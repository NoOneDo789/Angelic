Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import Utils.
Require Import Integers.
Require Import Floats.
Require Import Classical.
Require Import Lattice.
Require Import Iteration.
Require Import DLib.
Require Import Kildall.
Require Import KildallComp.
Require Import SSA.
Require Import SSAutils.
Require Import Utilsvalidproof.
Require Opt.
Require Import Dsd.
Require Import ValueDomainSSA ValueAOpSSA.

(** Sparse Conditional Constant Propagation *)

(** * Dataflow solver over DU chains *)
Module Type DATAFLOW_SOLVER.

  Module L := AVal. 
                
  Definition lattice_values := PMap.t L.t.
  Definition exec_state := P2Map.t bool.
  
  Definition not_defined (f: function)
             (absint: instruction -> lattice_values -> option (reg * L.t)) (r: reg) :=
    (forall lv r' nv i pc, (fn_code f) ! pc = Some i ->  absint i lv = Some (r',nv) -> r <> r')
    /\ (forall pc pb l r', (fn_phicode f) ! pc = Some pb -> In (Iphi l r') pb -> r <> r').
  
  Definition executable_node (f : function) (pc' : node) (es : exec_state) :=
    pc' = fn_entrypoint f
    \/ (exists pc, es !!2 (pc, pc') = true /\ cfg f pc pc').

  Parameter fixpoint : forall
      (f: function)
      (absint: instruction -> lattice_values -> option (reg * L.t))
      (init: lattice_values),
      PMap.t L.t * exec_state.

  Axiom defined_nowhere_stays_top: forall f absint init r lv,
      not_defined f absint r ->
      init # r = L.top ->
      lv = fst (fixpoint f absint init) ->
      lv # r = L.top.

  Axiom defined_nowhere_becomes_top: forall f absint init r,
      not_defined f absint r ->
      init # r = L.bot ->
      (fst (fixpoint f absint init)) # r = L.top.

  Definition exec_flags_sound (f : function) (lv : Regmap.t L.t) (es : exec_state) := 
    forall pc pc' i, 
      cfg f pc pc' ->
      es !!2 (pc, pc') = false ->
      (fn_code f) ! pc' = Some i ->
      ~ executable_node f pc es \/
      match (fn_code f) ! pc with
      | Some (Icond cond args ifso ifnot) =>
        (ifso = pc' -> eval_static_condition cond lv ## args = Just false) /\
        (ifnot = pc' -> eval_static_condition cond lv ## args = Just true)
      | Some (Ijumptable arg tbl) =>
        exists n : int, lv # arg = I n /\ list_nth_z tbl (Int.unsigned n) <> Some pc'
      | _ => False
      end.

  Definition code_post_fixpoint (f : function)
                   (absint: instruction -> lattice_values -> option (reg * L.t))
                   (lv : lattice_values) (es : exec_state) :=
    forall pc i r v, 
      (fn_code f) ! pc = Some i ->
      executable_node f pc es ->
      absint i lv = Some (r, v) ->
      L.ge lv # r v.
  
  Definition phicode_post_fixpoint (f : function)
             (lv : Regmap.t L.t) (es : exec_state) :=
    forall pc pb r l xi pc' k,
      (fn_phicode f) ! pc' = Some pb ->
      In (Iphi l r) pb ->
      index_pred (make_predecessors (fn_code f) successors_instr) pc pc' = Some k ->
      es !!2 (pc, pc') = true ->
      nth_error l k = Some xi ->
      L.ge (lv # r) (lv # xi).
  
  Axiom post_fixpoint : forall f absint init lv es,
      fixpoint f absint init = (lv, es) ->
      code_post_fixpoint f absint lv es
      /\ phicode_post_fixpoint f lv es
      /\ exec_flags_sound f lv es.

End DATAFLOW_SOLVER.


Module DataflowSolver: DATAFLOW_SOLVER.

  Module L := AVal.

  Section CDS.

  Definition lattice_values := PMap.t L.t.
  Definition exec_state := P2Map.t bool.

  Definition instr_workset := (list reg * list reg)%type.
  Definition edge := (node * node)%type.

  Definition state := (list edge * instr_workset * lattice_values * exec_state)%type.

  (** * Def-Use Chains *)
  Definition ssainstruction := (node * (instruction + phiinstruction))%type.
  Definition du_chain := PMap.t (list ssainstruction).

  Record const_state := mkConstantState {
     cs_duc: du_chain;
     cs_preds: PTree.t (list node)
  }.

  Variable f: function.
  Variable absint : instruction -> lattice_values -> option (reg * L.t).
  Variable initial_values : lattice_values.

  Definition bge (x y : L.t) : bool := L.beq (L.lub x y) x.

  Remark bge_correct: forall x y, bge x y = true -> L.ge x y.
  Proof.
    intros. unfold bge in H. apply L.beq_correct in H. eapply L.ge_trans.
    apply L.ge_refl. apply L.eq_sym. apply H. apply L.ge_lub_right.
  Qed.

  (** Determining whether a given node is executable, in current dataflow solver *)
  Definition preds_of cs pc := match (cs_preds cs) ! pc with
                              | None => nil
                              | Some l => l
                            end.

  Fixpoint node_is_executable_rec (es: exec_state) preds pc' :=
    match preds with
      | nil => false
      | pc :: pcs =>
        if es #2 (pc, pc') then true else node_is_executable_rec es pcs pc'
    end.

  Definition node_is_executable cs (st:state) pc' :=
    match st with
        (cfgwl, iws, lv, es) => node_is_executable_rec es (preds_of cs pc') pc'
    end.

  (* Unconditionally set an edge as executable when there is only one child *)
  Definition single_succ (pc: node) (i: instruction) : option edge :=
   match i with
   | Inop s => Some (pc, s)
   | Iop op args res s => Some (pc, s)
   | Iload chunk addr args dst s => Some (pc, s)
   | Istore chunk addr args src s => Some (pc, s)
   | Icall sig ros args res s => Some (pc, s)
   | Itailcall sig ros args => None
   | Ibuiltin ef args res s => Some (pc, s)
   | Icond cond args ifso ifnot => None
   | Ijumptable arg tbl => None
   | Ireturn optarg => None
   end.

  (** Picks a register from the worklist, from the top list if possible *)
  Fixpoint pick_instr_rec vl (iws_t: list reg) (iws_nt: list reg) : (option reg * instr_workset) :=
    match iws_t, iws_nt with
      | x::xs, ys => (Some x, (xs, ys))
      | nil, y::ys => if L.beq L.top vl# y then pick_instr_rec vl nil ys else (Some y, (nil, ys))
      | nil, nil => (None, (nil, nil))
    end.

  Definition pick_instr vl (iws: instr_workset) : option reg * instr_workset:=
    match iws with
        (ts, nts) => pick_instr_rec vl ts nts
    end.

  (** Updates the state with the new value [nv] of [r], and adds it
   to the workset if necessary *)
  Definition add_instr_aux (r: reg) (v: L.t) (iws: instr_workset) :=
    let (top, ntop) := iws in
    if L.beq v L.top then (r :: top, ntop) else (top, r :: ntop).

  Definition update_vals lv iws r nv :=
    let ov := lv # r in
    if bge ov nv
    then (lv, iws)
    else (lv # r <- (L.lub nv ov), add_instr_aux r (L.lub nv ov) iws).


  (** Static evaluation of a phi-block *)
   Fixpoint visit_phi_rec (lv: lattice_values) (es: exec_state) pc' args preds x :=
     if L.beq L.top x then Some L.top else
     match args, preds with
       | y::ys, pc::pcs =>
         let a := if es #2 (pc, pc') then lv # y else L.bot in
         visit_phi_rec lv es pc' ys pcs (L.lub x a)
       | nil, nil => Some x
       | _, _ => None
     end.

   Definition visit_phi cs (st_in: state) pc' r_used pi : state :=
     match st_in with (cfgwl, iws, lv, es) =>
     match pi with Iphi args r =>
       if L.beq L.top lv # r then (cfgwl, iws, lv, es) else
       match visit_phi_rec lv es pc' args (preds_of cs pc') r_used with
         | Some x => let (lv', iws') := update_vals lv iws r x in
                     (cfgwl, iws', lv', es)
         | None => (cfgwl, iws, lv, es)
       end
     end
     end.

   Definition visit_phibloc cs st r_used pc :=
     match (fn_phicode f) ! pc with
       | None => st
       | Some pb => fold_left (fun acc pi => visit_phi cs acc pc r_used pi) pb st
     end.

   Definition visit_instr (st_in : state) pc instr :=
     match st_in with (cfgwl, iws, lv, es) =>
     match instr with
       | Icond cond args ifso ifnot =>
         match eval_static_condition cond lv ## args with
           | Just true => ((pc, ifso)::cfgwl, iws, lv, es)
           | Just false => ((pc, ifnot)::cfgwl, iws, lv, es)
           | _ => ((pc, ifso) :: (pc, ifnot) :: cfgwl, iws, lv, es)
         end
       | Ijumptable arg tbl =>
         match lv # arg with
           | I k => match list_nth_z tbl (Int.unsigned k) with
                         | None => (map (fun x:node => (pc, x)) tbl ++ cfgwl, iws, lv, es)
                         | Some pc' => ((pc, pc')::cfgwl, iws, lv, es)
                       end
           | x => (map (fun x:node => (pc, x)) tbl ++ cfgwl, iws, lv, es)
         end
       | _ => match absint instr lv with
                | Some (r, x) =>
                  let (lv', iws') := update_vals lv iws r x in
                  (cfgwl, iws', lv', es)
                | None => (cfgwl, iws, lv, es)
              end
     end
     end.

   (** The register defined by an instruction *)
   Definition def_reg i :=
     match i with
       | Iop _ _ r _ | Iload _ _ _ r _  | Istore _ _ _ r _
       | Icall _ _ _ r _ | Ibuiltin _ _ (BR r) _  => Some r
     | _ => None
   end.

   Definition visit_ssainstr cs st r_used (ssai : ssainstruction) :=
     match st with (_, _, lv, _) =>
     match ssai with
       | (pc, inr pi) =>
         visit_phi cs st pc r_used pi
       | (pc, inl instr) =>
         match def_reg instr with
           | Some r => if L.beq L.top lv # r (* Optim: nothing to do if at top *)
                       then st
                       else match node_is_executable cs st pc with
                              | false => st
                              | true => visit_instr st pc instr
                            end
           | None =>  match node_is_executable cs st pc with (* Mostly conditionals*)
                              | false => st
                              | true => visit_instr st pc instr
                      end
         end
     end
     end.

   Definition step (ms : const_state * state) : (option (lattice_values * exec_state))
                                                + (const_state * state) :=
     let (cs, st) := ms in
     match st with (cfgwl, iws, lv, es) =>
     match cfgwl with
       | (pc0, pc) :: cfgwl' =>
         match es #2 (pc0, pc) with
           | true => inr _ (cs, (cfgwl', iws, lv, es))
           | false =>
             let es' := es #2 (pc0, pc) <- true in
             let st2 := visit_phibloc cs (cfgwl', iws, lv ,es') L.bot pc in
             match (fn_code f) ! pc with
               | None => inl _ None
               | Some instr =>
                 match visit_instr st2 pc instr with
                   | (cfgwl'', iws'', lv'', es'') =>
                     match single_succ pc instr with
                       | None => inr _ (cs, (cfgwl'', iws'', lv'', es''))
                       | Some (x, y) => inr _ (cs, (if es' #2 (x,y)
                                                    then cfgwl''
                                                    else (x,y)::cfgwl'', iws'', lv'', es''))
                     end
                 end
             end
         end
       | nil =>
         match pick_instr lv iws with
           | (Some r, iws') => (* Fold over all uses of [r] *)
             inr _ (cs, (fold_left (fun st_in ssai => visit_ssainstr cs st_in lv # r ssai)
                                   (cs_duc cs) # r
                                   (cfgwl, iws', lv, es)))
           | _ => inl _ (Some (lv, es))
         end
     end

     end.

   Definition initial_state : option state :=
     let start i := match single_succ (fn_entrypoint f) i with
                      | None => nil
                      | Some x => x :: nil
                    end in
     match (fn_code f) ! (fn_entrypoint f) with
       | None => None
       | Some i => Some (start i, (nil, nil), initial_values, P2Map.init false)
     end.

  (** * Post-fixpoint checker *)
  Definition executable_node (pc': node) (es: exec_state) :=
    pc' = fn_entrypoint f \/ exists pc, es #2 (pc, pc') = true /\ SSA.cfg f pc pc'.

  Definition bexecutable_node (pc': node) (preds: PTree.t (list node)) (es: exec_state) :=
    if Pos.eq_dec pc' (fn_entrypoint f) then true else
      existsb (fun pc => es #2 (pc, pc')) preds !!! pc'.

  Definition check_code lv preds es :=
    forall_ptree (fun pc i => match bexecutable_node pc preds es with
                                | false => true
                                | true => match absint i lv with
                                            | None => true
                                            | Some (r, nv) => bge (lv # r) nv
                                          end
                              end) (fn_code f).

  Fixpoint check_phiinstruction lv es r rs preds pc' :=
    match rs, preds with
      | nil, nil => true
      | x::xs, pc::pcs => match es #2 (pc, pc') with
                            | false => check_phiinstruction lv es r xs pcs pc'
                            | true => bge (lv # r) (lv # x) &&
                                          check_phiinstruction lv es r xs pcs pc'
                          end
      | _, _ => false
    end.

  Definition check_phicode_g lv es preds (pc: node) pb :=
    forallb (fun pi => match pi with
                         | Iphi rs r => check_phiinstruction lv es r rs (preds !!! pc)  pc
                       end) pb.

  Definition check_phicode lv es preds :=
    forall_ptree (check_phicode_g lv es preds) (fn_phicode f).

  Definition check_non_exec_edge lv pc pc' :=
    match (fn_code f) ! pc with
      | Some (Icond cond args ifso ifnot) =>
        match Pos.eq_dec pc' ifso with
          | left _ => match eval_static_condition cond lv ## args with
                      | Just false => match Pos.eq_dec pc' ifnot with
                                        | right _ => true
                                        | left _ => match eval_static_condition cond lv ## args with
                                                      | Just true => true
                                                      | _ => false
                                                    end
                                      end
                      | _ => false
                      end
          | right _ => match Pos.eq_dec pc' ifnot with
                       | right _ => false
                       | left _ => match eval_static_condition cond lv ## args with
                                   | Just true => true
                                   | _ => false
                                   end
                       end
        end
      | Some (Ijumptable arg tbl) =>
        match lv # arg with
          | I n => match list_nth_z tbl (Int.unsigned n) with
                        | Some p => if Pos.eq_dec p pc' then false else true
                        | None => true (* ???? *)
                      end
          | _ => false
        end
      | Some i => false
      | None => false
    end.

  Definition check_executable_flags lv es preds :=
    forall_ptree
      (fun pc' _ => forallb (fun pc => match bexecutable_node pc preds es with
                                         | true => if bool_dec es #2 (pc, pc') false
                                                   then check_non_exec_edge lv pc pc'
                                                   else true
                                         | false => true
                                       end) (preds !!! pc')) (fn_code f).

  Definition check lv es preds :=
    (check_phicode lv es preds)
      && (check_code lv preds es)
      && (check_executable_flags lv es preds).

  (** Fixpoint *)
  
  (** ** Construction *)
  Definition regs_used_by (i : instruction) : list reg :=
    match i with
    | Iop _ l _ _ => l
    | Iload _ _ l _ _ => l
    | Istore _ _ l _ _ => l
    | Icall _ ros l _ _
    | Itailcall _ ros l =>
      match ros with
      | inl r => r :: l
      | inr _ => l
      end
    | Ibuiltin _ l _ _ => (params_of_builtin_args l)
    | Icond _ l _ _ => l
    | Ijumptable r _ => r :: nil
    | Ireturn (Some r) => r :: nil
    | _ => nil
    end.

  Definition handle_reg_list (duc: du_chain) (ssai: ssainstruction) (rs: list reg) :=
    List.fold_left (fun u r => PMap.set r (ssai :: u # r) u) rs duc.

  Definition def_use_1 duc c :=
    PTree.fold (fun u pc i => handle_reg_list u (pc, inl _ i) (regs_used_by i)) c duc.

  Definition handle_phi_block (duc : du_chain) pc (pb : phiblock) :=
    List.fold_left
      (fun u pi => match pi with
                     Iphi args _ => handle_reg_list u (pc, inr _ pi) args end)
      pb duc.

  Definition def_use_2 duc phic :=
    PTree.fold (fun u pc pb => handle_phi_block u pc pb) phic duc.

  Definition make_du_chain f : du_chain :=
    let u := def_use_1 (PMap.init nil) (fn_code f) in
    def_use_2 u (fn_phicode f).

  
  Definition fixpoint :=
    let failed := (PMap.init L.top, P2Map.init true) in
    let preds :=  make_predecessors (fn_code f) successors_instr in
    let cs := mkConstantState (make_du_chain f) preds in
    match initial_state with
    | Some is =>
      match PrimIter.iterate _ _ step (cs, is) with
      | Some (Some (lv, es)) =>
        let lv' := PMap.map (fun v => if L.beq v L.bot then L.top else v) lv in
        if check lv' es preds then (lv', es) else failed
      | _ => failed
      end
    | None => failed
    end.

  (** ** Proof of the checker *)
   Remark bexecutable_node_correct: forall es pc',
     bexecutable_node pc' (make_predecessors (fn_code f) successors_instr) es = true <->
     executable_node pc' es.
   Proof.
     intros es pc'. split. unfold executable_node, bexecutable_node in *.
     intros H.
     destruct (Pos.eq_dec pc' (fn_entrypoint f)). auto. right.
     apply existsb_exists in H as [pc [H1 H2]].
     exists pc. intuition.
     assert (exists i : instruction, (fn_code f) ! pc = Some i).
     unfold "!!!" in *. flatten H1.
     eapply make_predecessors_some in Eq; eauto.
     unfold In in *. contradiction.
     destruct H as [i H].
     assert (In pc' (successors_instr i)).
     eapply make_predecessors_correct2; eauto.
     econstructor; eauto.

     intros H. unfold bexecutable_node.
     destruct (Pos.eq_dec pc' (fn_entrypoint f)). auto.
     apply existsb_exists. unfold executable_node in *.
     destruct H as [H | [pc H]].
     contradiction.
     exists pc.
     intuition.
     invh SSA.cfg.
     eapply make_predecessors_correct_1; eauto.
   Qed.

   Definition code_post_fixpoint lv es :=
     forall pc i r v,
     (fn_code f) ! pc = Some i ->
     executable_node pc es ->
     absint i lv = Some (r, v) ->
     L.ge lv # r v.

   Remark check_code_correct: forall lv es,
     check_code lv (make_predecessors (fn_code f) successors_instr) es = true ->
     code_post_fixpoint lv es.
   Proof.
     intros lv es H. unfold check_code, code_post_fixpoint in *.
     intros. eapply forall_ptree_true in H; eauto.
     apply bexecutable_node_correct in H1.
     flatten H.
     apply bge_correct; auto.
   Qed.

   Definition phicode_post_fixpoint lv es := forall pc pb r l xi pc' k,
    (fn_phicode f) ! pc' = Some pb ->
    In (Iphi l r) pb ->
    index_pred (make_predecessors (fn_code f) successors_instr) pc pc' = Some k ->
    es #2 (pc, pc') = true ->
    nth_error l k = Some xi ->
    L.ge (lv # r) (lv # xi).

   Hint Resolve bge_correct: core.
   
   Remark check_phiinstruction_correct: forall lv es pb r l pc' preds,
     (fn_phicode f) ! pc' = Some pb ->
     check_phiinstruction lv es r l preds  pc' = true->
     forall pc xi k,
     (k < length preds)%nat ->
     Utils.get_index preds pc = Some k ->
     es #2 (pc, pc') = true ->
     nth_error l k = Some xi ->
     L.ge (lv # r) (lv # xi).
   Proof.
     intros.
     generalize dependent l.
     induction preds.
     + simpl in *. intros. lia.
     + simpl in *. intros.
       destruct l.
       simpl in *. congruence.

       assert (check_phiinstruction lv es r l preds pc' = true).
       simpl in *.
       flatten H0; apply andb_true_iff in H0; intuition.

       destruct (eq_nat_dec k O).
       - subst. unfold nth_error in H4. inv H4.
         assert (a = pc).
         apply get_index_nth_error in H2.
         unfold nth_error in *. simpl in *. inv H2. reflexivity.
         subst. simpl in *. flatten H0.
         apply bge_correct. apply andb_true_iff in H0. intuition.
       - assert (exists k0, k = Datatypes.S k0) as [k0 Hk].
           destruct (O_or_S k). inv s. exists x. auto.
           congruence.
         subst.
         eapply IHpreds with (k := k0) (l := l); eauto.
         * lia.
         * eapply get_index_cons_succ; eauto.
   Qed.

   Remark check_phicode_correct: forall lv es,
     check_phicode lv es (make_predecessors (fn_code f) successors_instr) = true ->
     phicode_post_fixpoint lv es.
   Proof.
     intros lv es H.
     unfold phicode_post_fixpoint, check_phicode in *.
     intros pc pb r l xi pc' k H1 H2 H3 H4.
     eapply forall_ptree_true in H; eauto.
     unfold check_phicode_g in *. eapply forallb_forall in H; eauto.
     flatten H.
     eapply check_phiinstruction_correct; eauto.
     eapply index_pred_some; eauto.
   Qed.

   Definition exec_flags_sound lv es :=
     forall pc pc' i
            (EX_CFG: SSA.cfg f pc pc')
            (EX_NOTEXEC: es #2 (pc, pc') = false)
            (EX_INS: (fn_code f) ! pc' = Some i),
       ~executable_node pc es \/
       match (fn_code f) ! pc with
         | Some (Icond cond args ifso ifnot) =>
           (ifso  = pc' -> eval_static_condition cond lv ## args = Just false) /\
           (ifnot = pc' -> eval_static_condition cond lv ## args = Just true)
         | Some (Ijumptable arg tbl) =>
           exists n, (lv # arg = I n /\ list_nth_z tbl (Int.unsigned n) <> Some pc')
         | _ => False
       end.

   Remark check_executable_flags_correct: forall es lv,
     check_executable_flags lv es (make_predecessors (fn_code f) successors_instr) = true ->
     exec_flags_sound lv es.
   Proof.
     intros.
     unfold exec_flags_sound, check_executable_flags in *. intros.
     match goal with
       | H: forall_ptree ?f ?code = true |- _ =>
         assert (forall pp x, code ! pp = Some x -> f pp x = true) as H0
     end.
     apply forall_ptree_true; auto.
     destruct (classic (executable_node pc es)); intuition.
     destruct ((fn_code f) ! pc) eqn:eq.
     + specialize (H0 pc' i EX_INS).
       eapply forallb_forall with (x := pc) in H0; eauto.
       flatten H0; eauto.
       - unfold check_non_exec_edge in H0. rewrite eq in H0.
         flatten H0; right; intuition.
         * exists n. intuition. 
         * exists n. intuition. 
       - left. intro contra; apply bexecutable_node_correct in contra. congruence.
       - invh cfg. eapply make_predecessors_correct_1; eauto.
     + invh cfg. unfold fn_code in *. rewrite eq in HCFG_ins. congruence.
   Qed.

   Remark top_is_post_fixpoint:
    code_post_fixpoint (PMap.init L.top) (P2Map.init true)
    /\ phicode_post_fixpoint (PMap.init L.top) (P2Map.init true)
    /\ exec_flags_sound (PMap.init L.top) (P2Map.init true).
  Proof.
    unfold code_post_fixpoint. split. intros.
    rewrite PMap.gi. apply L.ge_top. split.
    unfold phicode_post_fixpoint. intros. rewrite PMap.gi. apply L.ge_top.
    unfold exec_flags_sound. intros. rewrite P2Map.gi in *. discriminate.
  Qed.

  Remark check_correct: forall lv es,
    check lv es (make_predecessors (fn_code f) successors_instr) = true ->
    code_post_fixpoint lv es /\ phicode_post_fixpoint lv es /\ exec_flags_sound lv es.
  Proof.
    intros. unfold check in H. apply andb_prop in H. destruct H as [H1 H2].
    apply andb_prop in H1. destruct H1 as [H1 H3].
    split.
      apply check_code_correct; assumption. split.
      apply check_phicode_correct; assumption.
      apply check_executable_flags_correct; assumption.
  Qed.

  (** ** Correctness of du_chains *)
  Definition ssai_in_function ssai f :=
    match ssai with
    | (pc, inl i)  => (fn_code f) ! pc = Some i
    | (pc, inr pi) => exists pb, (fn_phicode f) ! pc = Some pb /\ In pi pb
    end.

  Definition maps_into_function f m := forall r ssai,
      In ssai (m # r) -> ssai_in_function ssai f.

  Hint Unfold maps_into_function ssai_in_function: core.

  Lemma duc_maps_into_function_handle_reg_list: forall f duc ssai rs,
      maps_into_function f duc ->
      ssai_in_function ssai f ->
      maps_into_function f (handle_reg_list duc ssai rs).
  Proof.
    intros. generalize dependent duc.
    induction rs.
    tauto.
    intros.
    simpl in *. eapply IHrs; eauto.
    unfold maps_into_function in *. intros.
    destruct (peq a r).
    + subst.
      rewrite PMap.gss in *.
      inv H1; eauto.
    + rewrite PMap.gso in *; auto. eauto.
  Qed.

  Lemma duc_maps_into_function_code: forall f duc,
      maps_into_function f duc ->
      maps_into_function f (def_use_1 duc (fn_code f)).
  Proof.
    intros.
    unfold def_use_1.
    apply PTree_Properties.fold_rec; auto.
    intros.
    apply duc_maps_into_function_handle_reg_list; auto.
  Qed.

  Lemma duc_maps_into_function_phibloc: forall f duc pc pb l,
      maps_into_function f duc ->
      (fn_phicode f) ! pc = Some pb ->
      (exists pref, pref ++ l = pb) ->
      maps_into_function f (handle_phi_block duc pc l).
  Proof.
    intros.
    generalize dependent duc. induction l; auto.
    destruct a.
    unfold maps_into_function; intros.
    simpl in *; flatten H2.

    eapply IHl with (duc := (handle_reg_list duc (pc, inr (Iphi l0 r)) l0)); eauto.
    { invh ex. exists (x ++ Iphi l0 r :: nil). rewrite <- app_assoc. reflexivity. }
    eapply duc_maps_into_function_handle_reg_list; eauto.
    simpl. exists pb. intuition. invh ex.
    { assert (In (Iphi l0 r) (Iphi l0 r :: l)). auto. apply in_app. auto. }
  Qed.

  Lemma duc_maps_into_function_phicode: forall f duc,
      maps_into_function f duc ->
      maps_into_function f (def_use_2 duc (fn_phicode f)).
  Proof.
    intros.
    unfold def_use_2.
    apply PTree_Properties.fold_rec; auto.
    intros.
    eapply duc_maps_into_function_phibloc; eauto.
    exists nil; reflexivity.
  Qed.

  Lemma duc_maps_into_function: forall f,
      maps_into_function f (make_du_chain f).
  Proof.
    unfold make_du_chain. intros.
    eapply duc_maps_into_function_phicode; eauto.
    eapply duc_maps_into_function_code; eauto.
    unfold maps_into_function. intros.
    rewrite PMap.gi in H.
    contradiction.
  Qed.

  (* Proof that uninitialized values stay at bot *)
  Definition get_lv (st: state) :=
    match st with
        (_, _, lv, _) => lv
    end.

  Definition not_defined r := (forall lv r' nv i pc,
    (fn_code f) ! pc = Some i -> absint i lv = Some (r', nv) -> r <> r') /\
    (forall pc pb l r', (fn_phicode f) ! pc = Some pb -> In (Iphi l r') pb -> r <> r').

  Remark defined_nowhere_stationary_aux_update_val:
    forall lv b r t lv',
      fst (update_vals lv b r t) = lv' ->
      (forall r', r' <> r -> lv' # r' = lv # r').
  Proof.
    intros.
    unfold update_vals in *.
    flatten H; simpl in *; try congruence.
    subst. rewrite PMap.gso; auto.
  Qed.

  Remark defined_nowhere_stationary_aux_visit_instr: forall st r pc i,
    not_defined r ->
    (fn_code f) ! pc = Some i ->
    (get_lv (visit_instr st pc i)) # r = (get_lv st) # r.
  Proof.
    intros.
    unfold not_defined in *.
    unfold visit_instr in *.
    destruct H as [Ha Hb].
    flatten; simpl in *; try (reflexivity); subst;
      try match goal with
          [H: (absint _ _ = Some (?r0, _)),
           H1: update_vals ?l ?i0 ?r1 ?t = (?t0, ?i1)  |- (_ = ?l !! r) ]=>
           assert (r <> r0);
             [intro contra; subst; eapply Ha; eauto |
              eapply (defined_nowhere_stationary_aux_update_val l i0 r0 t) ; eauto];
             rewrite H1; simpl; auto
      end.
  Qed.

  Remark defined_nowhere_stationary_aux_visit_phi: forall st cs r pc r_used pi pb,
    not_defined r ->
    (fn_phicode f) ! pc = Some pb -> In pi pb ->
    (get_lv (visit_phi cs st pc r_used pi)) # r = (get_lv st) # r.
  Proof.
    intros.
    unfold visit_phi in *.
    flatten.
    assert (r <> r0) by ( destruct H as [Ha Hb]; eapply Hb; eauto).
    subst.
    assert (fst (update_vals l i r0 t) = t0) by (rewrite Eq5; simpl; auto).
    eapply defined_nowhere_stationary_aux_update_val; go.
  Qed.

  Remark defined_nowhere_stationary_aux_visit_phibloc_rec:
    forall st st' cs r pc r_used pb,
    not_defined r ->
    (fn_phicode f) ! pc = Some pb ->
    (forall l, (exists l', l' ++ l = pb) ->
               fold_left (fun acc pi => visit_phi cs acc pc r_used pi)
                         l
                         st = st' ->
               (get_lv st') # r = (get_lv st) # r).
  Proof.
    intros.
    generalize dependent st.
    induction l.
    + intros. simpl in *. unfold get_lv. flatten.
    + intros.
      simpl in *.
      assert ((get_lv st') !! r = (get_lv (visit_phi cs st pc r_used a)) !! r).
      eapply IHl with (st := visit_phi cs st pc r_used a); eauto.
      invh ex.
      exists (x ++ a :: nil). {
        rewrite <- app_assoc.
        simpl.
        apply eq_refl.
      }
      assert ((get_lv (visit_phi cs st pc r_used a)) !! r = (get_lv st) !! r).
      eapply defined_nowhere_stationary_aux_visit_phi; eauto.
      invh ex. {
        assert (In a (a::l)). apply in_eq.
        apply in_app.
        auto.
      }
      congruence.
  Qed.

  Remark defined_nowhere_stationary_aux_visit_phibloc: forall st st' cs r pc r_used,
    not_defined r ->
    visit_phibloc cs st r_used pc = st' ->
    (get_lv (visit_phibloc cs st r_used pc)) !! r = (get_lv st) !! r.
  Proof.
    intros.
    unfold visit_phibloc in *.
    destruct ((fn_phicode f) ! pc) as [pb |] eqn:eq.
    eapply defined_nowhere_stationary_aux_visit_phibloc_rec
      with (l := pb) (cs := cs) (r_used := r_used) (st := st); eauto.
    exists nil. reflexivity.
    subst. reflexivity.
  Qed.

  Remark defined_nowhere_stationary_aux_rec_helper: forall r m (x : ssainstruction) l',
    maps_into_function f m ->
    (exists pref, pref ++ x :: l' = m # r) ->
    ssai_in_function x f.
  Proof.
    intros.
    destruct H0 as [prefs H0].
    assert (In x m # r).
    rewrite <- H0.
    assert (In x (x::l')); auto.
    apply in_app. auto.
    eapply H; eauto.
  Qed.

  Remark defined_nowhere_stationary_aux: forall st st' r cs cs',
    not_defined r -> step (cs, st) = inr (cs', st') ->
    maps_into_function f (cs_duc cs) ->
    (get_lv st) # r = (get_lv st') # r.
  Proof.
    intros.
    remember st as St.
    destruct st as [[[a b] lv] c].
    unfold step in *.
    rewrite HeqSt in *.
    flatten H0; try (flatten H0; reflexivity); simpl;
    try (match goal with
        [ h: context[ visit_phibloc ?cs ?stin ?bot ?n0 ] |- _ ] =>
        assert ((get_lv (visit_phibloc cs stin bot n0)) !! r = lv !! r);
          [eapply defined_nowhere_stationary_aux_visit_phibloc; eauto |
           assert ( (get_lv (visit_instr
                               (visit_phibloc cs stin bot n0) n0 i)) !! r =
                    (get_lv (visit_phibloc cs stin bot n0)) !! r);
                  [eapply defined_nowhere_stationary_aux_visit_instr; eauto |
                    assert ((get_lv
                               (visit_instr
                                  (visit_phibloc cs stin bot n0) n0 i)) = t)]
          ]
      end; [

      match goal with
          [ H: visit_instr _ _ _ = _ |- _ ] => rewrite H; reflexivity
      end |
      congruence]).

    match goal with
        [ |- context [ fold_left ?fn_ ?l_ ?acc0 ] ]=>
        set (fn := fn_); set (l := l_)
    end.
    assert (forall l' acc,
              (exists pref, pref ++ l' = l) ->
              (get_lv (fold_left fn l' acc)) !! r = (get_lv acc) !! r) as Hbi.
    + induction l'; intros; simpl in *.
      - tauto.
      - assert ((get_lv (fn acc a)) # r = (get_lv acc) # r) as Hsame.
        * unfold fn. unfold visit_ssainstr.
          flatten;
          try (unfold l in *; subst;
               assert (ssai_in_function (n, inl i1) f);
               [eapply defined_nowhere_stationary_aux_rec_helper; eauto |
                eapply defined_nowhere_stationary_aux_visit_instr; eauto]).
          assert (ssai_in_function (n, inr p1) f).
          eapply defined_nowhere_stationary_aux_rec_helper; eauto.
          unfold ssai_in_function in *.
          destruct H2 as [pb [Hphib Hin]].
          eapply defined_nowhere_stationary_aux_visit_phi; eauto.
        * rewrite <- Hsame.
          eapply IHl'.
          invh ex.
          exists (x ++ a::nil). rewrite <- app_assoc. auto.
    + rewrite Hbi; auto.
      exists nil; auto.
  Qed.

  Remark cs_constant: forall cs cs' st st',
    step (cs, st) = inr (cs', st') -> cs = cs'.
  Proof.
    intros.
    unfold step in *. flatten H.
  Qed.


  Remark defined_nowhere_stationary: forall r lv es is ,
    not_defined r -> initial_state = Some is ->
    PrimIter.iterate
      _ _ step (mkConstantState (make_du_chain f)
                                (make_predecessors (fn_code f) successors_instr), is) = Some (Some (lv, es)) ->
     lv # r = initial_values # r.
  Proof.
    intros.
    set (P (s:const_state*state) :=
           forall cs st, s = (cs, st) ->
                         ((get_lv st) # r = initial_values # r)
                         /\ (maps_into_function f (cs_duc cs))).
    set (Q (o: option (lattice_values * exec_state)) :=
           forall v es', o = Some (v, es') -> v # r = initial_values # r).
    assert (Q (Some (lv, es))).
    {
      eapply PrimIter.iterate_prop with (step := step) (P := P) ; unfold P, Q.
      + intro. destruct (step a) eqn:eq.
        unfold step in eq. intros. subst.
        flatten eq.
        assert ((get_lv ((nil, i, v, es'):state)) # r =  v # r) by reflexivity.
        destruct (H2 c (nil, i, v, es')) as [Hlv Hduc]; auto.

        intros. subst. destruct a as (cs0, st0).
        destruct (H2 cs0 st0) as [Hlv Hduc]; auto.
        split. rewrite <- Hlv. apply eq_sym.
        eapply defined_nowhere_stationary_aux; eauto.
        eapply cs_constant in eq. subst. assumption.

      + eapply H1.
      + intros. unfold initial_state in *.
        flatten H0. split; [auto | apply duc_maps_into_function].
                    split; [auto | apply duc_maps_into_function].
      }

      unfold Q in *. apply H2 with es. apply eq_refl.
  Qed.
  
  Lemma defined_nowhere_becomes_top: forall r,
    not_defined r -> initial_values # r = L.bot -> (fst fixpoint) # r = L.top.
  Proof.
    intros.
    unfold fixpoint in *.
    flatten; subst; simpl; try (rewrite PMap.gi; eauto).
    assert (l # r = initial_values # r)
    by (eapply defined_nowhere_stationary with (3:= Eq0); eauto).
    rewrite PMap.gmap.
    rewrite H1. rewrite H0. auto.
  Qed.

  Lemma defined_nowhere_stays_top: forall r lv,
    not_defined r -> initial_values # r = L.top -> lv = fst fixpoint -> lv # r = L.top.
  Proof.
    intros; unfold fixpoint in *.
    flatten H1 ; subst; try (simpl ; rewrite PMap.gi;  eauto).
    simpl. rewrite PMap.gmap.
    assert (l !! r = initial_values !! r)
      by (eapply defined_nowhere_stationary; eauto).
    rewrite H0 in *.
    rewrite H1.
    auto. 
  Qed.

  (** * Correctness lemma *)
  Lemma post_fixpoint: forall lv es,
    fixpoint = (lv, es) ->
    code_post_fixpoint lv es
    /\ phicode_post_fixpoint lv es
    /\ exec_flags_sound lv es.
  Proof.
    intros. unfold fixpoint in H.
    destruct (initial_state).
    match goal with
        H: context [ PrimIter.iterate ?x ?y ?z ?t ] |- _ =>
        destruct (PrimIter.iterate x y z t)
    end.
     + destruct o. destruct p.
       - flatten H.
         apply check_correct in Eq. assumption.
         apply top_is_post_fixpoint.
       - inv H. apply top_is_post_fixpoint.
     + inv H. apply top_is_post_fixpoint.
     + inv H. apply top_is_post_fixpoint.
  Qed.

  End CDS.
  
End DataflowSolver.


(** * SCCP optimization, as an instantiation of the generic analysis.  *)
Section Opt.

  (** ** Definition *)
  Definition handle_instr (i: instruction) res : option (reg * AVal.t) :=
    match i with
    | Iop op regs r _ =>
      let vs := List.map (fun r => (PMap.get r res)) regs in
      Some (r,  eval_static_operation op vs)
    | Iload _ _ _ r _ | Icall _ _ _ r _ | Ibuiltin _ _ (BR r) _ => Some (r, AVal.top)
    | _ => None
    end.

  Definition initial f :=
    List.fold_left
      (fun vals r => PMap.set r AVal.top vals)
      (fn_params f)
      (PMap.init AVal.bot).

  Definition fixpoint f:=
    let fp := (DataflowSolver.fixpoint f handle_instr (initial f)) in
    ((fun r => PMap.get r (fst fp)),snd fp).

  Definition const_for_result (a: aval) : option operation :=
    match a with
    | I n => Some(Ointconst n)
    | F n => if Compopts.generate_float_constants tt then Some(Ofloatconst n) else None
    | FS n => if Compopts.generate_float_constants tt then Some(Osingleconst n) else None
    | _ => None
    end.
  
  Definition transf_instr (approx: reg -> AVal.t) (n: node) i :=
    match i with
    | Iop op args res s =>
      match const_for_result (eval_static_operation op (map approx args)) with
      | Some cop => Iop cop nil res s
      | _ => i
      end
    | _ => i
    end.

  Definition transf_function (f: function) := 
    @Opt.transf_function _ fixpoint transf_instr f. 
  
  Definition transf_fundef (f: fundef) : fundef :=
    AST.transf_fundef transf_function f.

  Definition transf_program (p: program) : program :=
    AST.transform_program transf_fundef p.

End Opt.

