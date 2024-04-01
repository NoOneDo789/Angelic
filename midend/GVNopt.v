Require Import Classical.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Events.
Require Import Registers.
Require Import Floats.
Require Import Utils.
Require Import SSA. 
Require Import SSAutils. 
Require Import Utilsvalidproof.
Require Import DomCompute.
Require Import Axioms.
Require Import KildallComp.
Require Import OrderedType.
Require Import Ordered.
Require Import FSets.
Require FSetAVL.
Require Import Opt.
Require Import OptInv.
Require Import DLib.

(** Common Subexpression Elimination based on Global Value Numbering *)

(** * Validation algorithm *)
Section Checker.
  
  Variable f : function.
  
  Notation code := (fn_code f).
  Notation phicode := (fn_phicode f).

  Definition certif := PTree.t ssa_def.
  Variable certificate : certif.
  
  Definition ssa_def_to_node (d:ssa_def) : node :=
    match d with
      | SDIop pc => pc
      | SDPhi pc _ => pc
    end.
  
  Definition top_set l : PTree.t unit :=
    fold_left (fun p s => PTree.set s tt p) l (PTree.empty _).
  
  Lemma in_top_set : forall l x, In x l -> PTree.get x (top_set l) = Some tt.
  Proof.
    assert (forall l s x,
              s ! x = Some tt ->
              (fold_left (fun (p : PTree.t unit) (s : PTree.elt) => PTree.set s tt p)
                         l s) ! x = Some tt).
    induction l; simpl; intros; go.
    apply IHl.
    rewrite PTree.gsspec; flatten.
    assert (forall l s x,
              In x l ->
              (fold_left (fun (p : PTree.t unit) (s : PTree.elt) => PTree.set s tt p)
                         l s) ! x = Some tt).
    induction l; simpl; intros; go.
    destruct H0; auto.
    apply H.
    subst; rewrite PTree.gss; auto.
    intros; apply H0; auto.
  Qed.
  
  Definition test_param_no_repr (s:PTree.t unit) : bool :=
    forall_ptree (fun r d =>
                     match get_ssa_eq f d with
                       | None => false
                       | Some e =>
                         let dst := ssa_eq_to_dst e in
                         match PTree.get dst s with
                           | Some _ => false
                           | None =>
                             match certificate ! dst with
                               | None => true
                               | Some _ => false
                             end
                         end
                     end) certificate.

  Definition make_repr (l:list reg) : reg -> (reg * node) :=
    let s := top_set l in
    if test_param_no_repr s then
      let map := PTree.map (fun r d => match get_ssa_eq f d with
                                          | None => (r, xH)
                                          | Some e => (ssa_eq_to_dst e, ssa_def_to_node d)
                                        end) certificate in
      (fun r => match PTree.get r map with
                | Some r' => r'
                | None => (r, xH)
                end)
    else (fun r => (r,xH)).

  Lemma make_repr_not_id : forall l r r',
    In r l ->  fst (make_repr l r') = r -> r = r'.
  Proof.
    unfold make_repr; intros r r' Hi.
    flatten; simpl; auto.
    destruct p as (r0 & n0); intro; subst; simpl in *.
    unfold test_param_no_repr in Eq.
    rewrite PTree.gmap in Eq0.
    unfold option_map in Eq0.
    flatten Eq0.
    exploit ptree_forall; eauto.
    simpl.
    flatten.
    exploit in_top_set; eauto.
    congruence.
  Qed.

  Lemma test_itempotent s :
    test_param_no_repr s = true ->
    let map := PTree.map (fun r d => match get_ssa_eq f d with
                                        | None => (r, xH)
                                        | Some e => (ssa_eq_to_dst e, ssa_def_to_node d)
                                      end) certificate in
    forall r r', PTree.get r map = Some r' -> PTree.get (fst r') map = None.
  Proof.
    unfold test_param_no_repr; intros.
    rewrite PTree.gmap in H0.
    rewrite PTree.gmap.
    destruct (certificate ! r) eqn:E; inv H0.
    exploit ptree_forall; eauto; clear H.
    simpl.
    flatten; simpl.
    rewrite Eq1; auto.
  Qed.

  Lemma make_repr_itempotent : forall l r,
    fst (make_repr l (fst (make_repr l r))) = fst (make_repr l r).
  Proof.
    intros l r.
    unfold make_repr.
    destruct (test_param_no_repr (top_set l)) eqn:E1; simpl; auto.
    set (map := PTree.map (fun r d => match get_ssa_eq f d with
                                        | None => (r, xH)
                                        | Some e => (ssa_eq_to_dst e, ssa_def_to_node d)
                                      end) certificate).
    destruct (map ! r) eqn:E2; simpl; auto.
    - exploit test_itempotent; eauto.
      intros; assert (T : map ! (fst p) = None) by auto.
      rewrite T; auto.
    - rewrite E2; auto.
  Qed.
  
  Definition op_eq (x y:operation) : bool :=
    if eq_operation x y then true else false.

  Lemma op_eq_true_iff : forall x y,
    op_eq x y = true <-> x = y.
  Proof.
    unfold op_eq; intros; destruct eq_operation; intuition congruence.
  Qed.

  
  Definition check_GVN_instr (f:function)
             (repr:reg-> (reg*node))
             (pc:node) (ins:instruction) : bool :=
    match ins with
      | Iop op args dst _ =>
        let dst' := fst (repr dst) in
        (peq dst dst')
          ||
          (match PTree.get dst certificate with
             | None => false
             | Some (SDIop pc') =>
               match get_ssa_eq f (SDIop pc') with
                 | Some (EqIop op' args' dst0') =>
                   (peq dst' dst0') &&
                   (op_eq op op') &&
                   (fn_dom_test f pc' pc) &&
                   (negb (op_depends_on_memory op)) &&
                   (forall_list2 (fun x y => peq (fst (repr x)) (fst (repr y))) args args')
                 | _ => false
               end
             | Some _ => false
           end)
      | _ => true
    end.

  Definition check_GVN_phiblock (f:function)
             (repr:reg-> (reg*node)) (pc:node) (phib:phiblock) : bool :=
        forallb
          (fun (phi:phiinstruction) =>
             let (args,dst) := phi in
             let dst' := fst (repr dst) in
             (peq dst dst')
               ||
               (match PTree.get dst certificate with
                  | None => false
                  | Some (SDPhi pc' idx) =>
                    (peq pc pc')
                      &&
                      (match get_ssa_eq f (SDPhi pc' idx) with
                         | Some (EqPhi dst0' args') =>
                           (peq dst' dst0')
                           &&
                           (forall_list2 (fun x y => peq (fst (repr x)) (fst (repr y))) args args')
                         | _ => false
                       end)
                  | Some _ => false
                end))
          phib.

  Definition dst_at_top l (m:PTree.t instruction) : list reg :=
    PTree.fold (fun l oc ins =>
                  match ins with
                    | Iload _ _ _ r _
                    | Icall _ _ _ r _ => r :: l
                    | Ibuiltin _ _ (BR r) _ => r :: l
                    | _ => l
                  end) m l.

  Lemma dst_at_top_prop1 : forall m l pc,
    match m!pc with
      | Some (Iload _ _ _ r _)
      | Some (Icall _ _ _ r _) => In r (dst_at_top l m)
      | Some (Ibuiltin _ _ (BR r) _) => In r (dst_at_top l m)
      | _ => True
    end.
  Proof.
    intros m l pc.
    unfold dst_at_top.
    apply PTree_Properties.fold_rec; intros.
    - rewrite <- H; flatten; auto.
    - rewrite PTree.gempty; auto.
    - rewrite PTree.gsspec.
      flatten; auto.
  Qed.

  Lemma dst_at_top_prop0 : forall m l,
    forall r, In r l -> In r (dst_at_top l m).
  Proof.
    intros m l.
    unfold dst_at_top.
    apply PTree_Properties.fold_rec; intros; auto.
    flatten; auto.
  Qed.

  Definition check_GVN : option (reg-> (reg * node)) :=
    let top_list := dst_at_top (fn_ext_params f) (fn_code f) in
    let repr := make_repr top_list in
    let check_params := forallb (fun r => peq (fst (repr r)) r) top_list in
    let check_instr := forall_ptree (check_GVN_instr f repr) (fn_code f) in
    let check_phiblock := forall_ptree (check_GVN_phiblock f repr) (fn_phicode f) in
    if check_params && check_instr && check_phiblock
    then Some repr
    else None.

End Checker.

(** * CSE optimisation based on GVN *)

Axiom extern_gvn: function -> certif.

(* Definition get_repr (f:function) (c:certif):= *)
(*   match check_GVN f c with *)
(*     | Some repr => repr *)
(*     | None => (fun x => (x,xH)) *)
(*   end. *)

(* Definition get_extern_gvn (f:function): (reg -> (reg* node)) := *)
(*   get_repr f (extern_gvn f). *)

(* Definition analysis (f: function) := ((get_extern_gvn f, f),P2Map.init true). *)

(* Definition res := ((reg -> reg*node)  (* repr(x) = (r, r_def) *) *)
(*                     * function        (* function *)                            *)
(*                    )%type. *)

(* Definition check_def (code:code) (pc:node) (x:reg) : bool := *)
(*   match code!pc with *)
(*     | Some (Iop op args dst succ) => if peq x dst then true else false *)
(*     | Some (Iload chunk addr args dst succ) => if peq x dst then true else false *)
(*     | Some (Icall sig fn args dst succ) => if peq x dst then true else false *)
(*     | Some (Ibuiltin fn args (BR dst) succ) => if peq x dst then true else false *)
(*     | _ => false *)
(*   end. *)


Definition find_mv_instr (result: option (reg*reg)) (pc: node) ins : option (reg * reg) :=
  match result with
  | None => match ins with
            | Iop Omove (src :: nil) dst _ => Some (dst,src)
            | _ => result
            end
  | _ => result
  end.

Definition find_mv_code (c: code) : option (reg * reg) :=
  PTree.fold find_mv_instr c None.

Definition remove_mv_instr (d: reg) (instr: instruction) :=
  match instr with
  | Iop Omove _ dst pc' =>
      if Pos.eqb dst d then Inop pc' else instr
  | _ => instr
  end.

Definition rename_reg (d s: reg) (r: reg) : reg :=
  if (Pos.eqb r d) then s else r.

Definition rename_fn (d s: reg) (fn: reg + ident) : reg + ident :=
  match fn with inl r => inl (rename_reg d s r) | _ => fn end.

Fixpoint rename_barg (d s: reg) (b: builtin_arg reg) : builtin_arg reg :=
  match b with
  | BA r => BA (rename_reg d s r)
  | BA_splitlong b1 b2 => BA_splitlong (rename_barg d s b1) (rename_barg d s b2)
  | BA_addptr b1 b2 => BA_addptr (rename_barg d s b1) (rename_barg d s b2)
  | _ => b
  end.

Fixpoint rename_bres (d s: reg) (b: builtin_res reg) : builtin_res reg :=
  match b with
  | BR r => BR (rename_reg d s r)
  | BR_splitlong b1 b2 => BR_splitlong (rename_bres d s b1) (rename_bres d s b2)
  | _ => b
  end.  

Definition subst_instr (d s: reg) (instr: instruction) :=
  let rn := rename_reg d s in
  let rnf := rename_fn d s in
  let rnba := rename_barg d s in
  let rnbr := rename_bres d s in
  match instr with
  | Inop pc' => Inop pc'
  | Iop op args dst pc' => Iop op (map rn args) (rn dst) pc'
  | Iload chunk addr args dst pc' => Iload chunk addr (map rn args) (rn dst) pc'
  | Istore chunk addr args src pc' => Istore chunk addr (map rn args) (rn src) pc'
  | Icall sig fn args dst pc' => Icall sig (rnf fn) (map rn args) (rn dst) pc'
  | Itailcall sig fn args => Itailcall sig (rnf fn) (map rn args)
  | Ibuiltin ef args dst pc' => Ibuiltin ef (map rnba args) (rnbr dst) pc'
  | Icond cond args ifso ifnot => Icond cond (map rn args) ifso ifnot
  | Ijumptable arg tbl => Ijumptable (rn arg) tbl
  | Ireturn ret => Ireturn (option_map rn ret)
  end.

Definition elim_mv_code (d s: reg) (c: code) : code :=
  PTree.map (fun pc instr => subst_instr d s (remove_mv_instr d instr)) c.

Fixpoint find_mv_phiblock (blk: phiblock) : option (reg * reg) :=
  match blk with
  | nil => None
  | (Iphi (src::args) dst) :: blk' =>
      if forallb (Pos.eqb src) args
      then Some (dst,src)
      else find_mv_phiblock blk'
  | _ :: blk' => find_mv_phiblock blk'
  end.

Definition _find_mv_phiblock result (pc: node) blk : option (reg * reg) :=
  match result with
  | None => find_mv_phiblock blk
  | _ => result
  end.

Definition find_mv_phicode (p: phicode) : option (reg * reg) :=
  PTree.fold _find_mv_phiblock p None.

Fixpoint remove_mv_phiblock (d: reg) (blk: phiblock) :=
  match blk with
  | nil => nil  
  | (Iphi args dst) :: blk' =>
      if Pos.eqb dst d
      then remove_mv_phiblock d blk'
      else (Iphi args dst) :: remove_mv_phiblock d blk'
  end.

Definition subst_phi (d s: reg) (pins: phiinstruction) :=
  match pins with
  | Iphi args dst => Iphi (map (rename_reg d s) args) (rename_reg d s dst)
  end.

Definition elim_mv_phicode (d s: reg) (p: phicode) : phicode :=
  PTree.map (fun pc blk => map (subst_phi d s) (remove_mv_phiblock d blk)) p.

Fixpoint simplify_mv (fuel: nat) (c: code) (p: phicode) : code * phicode :=
  match fuel with
  | 0 => (c, p)
  | S fuel' =>
      match find_mv_code c with
      | Some (d, s) =>
          simplify_mv fuel' (elim_mv_code d s c) (elim_mv_phicode d s p)
      | None => match find_mv_phicode p with
                | Some (d, s) =>
                    simplify_mv fuel' (elim_mv_code d s c) (elim_mv_phicode d s p)
                | None => (c,p)
                end
      end
  end.

Definition transf_function (f: function) : function :=
  let fuel :=
    PTree.fold (fun m _ blk => length blk + m) f.(fn_phicode)
    (PTree.fold (fun m _ _ => 1+m) f.(fn_code) 1%nat) in
  let '(code', phicode') := simplify_mv fuel f.(fn_code) f.(fn_phicode) in
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    code'
    phicode'
    f.(fn_entrypoint)
    f.(fn_ext_params)
    f.(fn_dom_test).

Definition transf_fundef (f: fundef) : fundef :=
  AST.transf_fundef transf_function f.

Definition transf_program (p: program) : program :=
  AST.transform_program transf_fundef p.
