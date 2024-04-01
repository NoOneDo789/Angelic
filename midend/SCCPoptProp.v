Require Import Coqlib.
Require Import Maps.
Require Import Maps2.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import Utils.
Require Import Classical.
Require Import Lattice.
Require Import Iteration.
Require Import DLib.
Require Import Integers.
Require Import Kildall.
Require Import KildallComp.
Require Import SSA.
Require Import SSAutils.
Require Import Utilsvalidproof.
Require Values.
Require Import SCCPopt.
Require Opt.
Require Import Dsd.
Unset Allow StrictProp.

(** * Proof obligations from [OptInv] *)
Module DS := DataflowSolver.
Require Import OptInv ValueDomainSSA ValueAOpSSA.
Require Import Globalenvs.

Section DSD_ANALYSIS.

  Notation A := fixpoint.
  Notation A_r f := (fst (A f)).
  Notation A_e f := (snd (A f)).

  (* Minimal block classification for analyzing operators *)
  Program Definition bctop (ge:genv): block_classification :=
    BC (fun b =>
          if (plt b (Genv.genv_next ge)) then
            match Genv.invert_symbol ge b with
            | None => BCother
            | Some id => BCglob id end
          else BCother) _ _.
  Next Obligation.
    flatten H.
  Qed.
  Next Obligation.
    flatten H. 
    eapply Genv.invert_find_symbol in Eq0.
    eapply Genv.invert_find_symbol in Eq.
    congruence.
  Qed.
  
  Definition G (ge: genv) (sp: Values.val) (rs: regset) := fun av v => (vmatch (bctop ge) v av).
  
  Hint Unfold G: core.
  Definition result := reg -> AVal.t.
  Definition is_at_Top (res: result) (r: reg) : Prop := res r = AVal.top.

  Lemma G_increasing: forall ge sp rs x y z,
                        vge x y -> G ge sp rs y z -> G ge sp rs x z.
  Proof.
    intros.
    unfold G in *.
    eapply vmatch_ge; eauto.
  Qed.

  Lemma G_top : forall f r ge sp rs, is_at_Top (A_r f) r -> G ge sp rs (A_r f r) (rs# r).
  Proof.
    intros. invh is_at_Top.
    unfold G. simpl. rewrite H1. unfold AVal.top.
    destruct (rs !! r) ; try solve [eapply vmatch_top ; eauto; go].
    case_eq (bctop ge b); intros.
    - simpl in H; flatten H.
    - simpl in H; flatten H.
      eapply vmatch_top; eauto.
      econstructor; eauto.
      econstructor; eauto.
      simpl. flatten. eauto.
    - simpl in H; flatten H.
    - simpl in H; flatten H;
      try solve [(econstructor; eauto);
                 (econstructor; eauto);
                 (simpl; flatten)].
    Unshelve.
    go. go.
  Qed.

 Lemma is_at_Top_eq_is_at_Top : forall f dst x,
   is_at_Top (A_r f) dst -> A_r f x = A_r f dst -> is_at_Top (A_r f) x.
  Proof.
    unfold is_at_Top; intros. congruence.
  Qed.

  Remark ext_params_not_defined: forall (f:function) x,
      wf_ssa_function f ->
      ext_params f x ->
      DS.not_defined f handle_instr x.
  Proof.
    intros.
    Ltac ssa_params :=
      match goal with
          HH : In _ (fn_params _) |- _ => apply fn_ssa_params in HH
      end.

    unfold DS.not_defined. split.
    + intros lv r' nv i pc H1. 
      unfold handle_instr in *.
      intro contra; subst.
      flatten H1; assert (assigned_code_spec (fn_code f) pc r'); eauto;
      try (invh ext_params; [ ssa_params ; [intro; subst; intuition; eauto | eauto]
                  | intro; subst; unfold not in *; eauto]).
    + intros. 
      intro contra; subst.
      assert (assigned_phi_spec (fn_phicode f) pc r'); try (econstructor; eauto).
      invh ext_params.
      - ssa_params. intuition; eauto. assumption.
      - intuition; eauto.
  Qed.

  Remark params_at_top_aux: forall f,
                            forall r inilv res,
    fold_left (fun lv r => PMap.set r AVal.top lv) (fn_params f)  inilv = res ->
    ((In r (fn_params f) -> res # r = AVal.top)
     /\ ((~In r (fn_params f)) -> res # r = inilv # r)).
  Proof.
    intros. subst. generalize dependent inilv.
    unfold initial.
    induction (fn_params f).
    + intros. simpl in *. intuition.
    + intros. simpl in *. specialize (IHl (inilv # a <- AVal.top)).
      destruct IHl.
      split.
    - intros. inv H1. 
      destruct (in_dec peq r l); intuition;
      match goal with
          H: ?t = ?t' |- _ => rewrite H
      end; apply PMap.gss; intuition. intuition.
    - intros H1. intuition.
      rewrite H1.
      apply PMap.gso; eauto.
  Qed.

  Lemma params_at_top: forall f,
      forall r,
        In r (fn_params f) -> (initial f) # r = AVal.top.
  Proof.
    intros.
    set (lv := initial f). unfold initial in *.
    set (HH := params_at_top_aux f).
    specialize (HH r (PMap.init AVal.bot) lv).
    intuition.
  Qed.

  Lemma ext_param_at_top: forall (f:function) r,
      wf_ssa_function f ->
      ext_params f r -> is_at_Top (A_r f) r.
  Proof.
    intros.
    destruct (in_dec peq r (fn_params f)).
    + assert ((initial f) # r = AVal.top) by (apply params_at_top; auto).
      exploit ext_params_not_defined; eauto. intros NDEF.
      eapply DS.defined_nowhere_stays_top; eauto.
    + set (ini := initial f). unfold initial in *.
      set (HH := params_at_top_aux f).
      specialize (HH r (PMap.init AVal.bot) ini).
      rewrite PMap.gi in *.
      assert (ini # r = AVal.bot) by intuition.
      exploit ext_params_not_defined; eauto.  intros NDEF.
      eapply DS.defined_nowhere_becomes_top; eauto.
  Qed.

  Definition exec f pc := DS.executable_node f pc (A_e f).

  Lemma exec_fn_entrypoint : forall f, exec f (fn_entrypoint f).
  Proof.
    go.
  Qed.

(** Instantiating the [DsdAnalysis] record *)
  Definition SCCP := (OptInv.Build_DsdAnalysis AVal.t G is_at_Top A
                                               exec exec_fn_entrypoint
                                               is_at_Top_eq_is_at_Top
                                               ext_param_at_top G_top).
End DSD_ANALYSIS.


(** * Some more auxiliary lemmas to retrieve soundness invariant of the analysis *)

Section AuxResults.

Variant single_succ_instr f : node -> Prop :=
| SSnop: forall pc s,
   (fn_code f) !pc = Some (Inop s) -> single_succ_instr f pc
| SSop: forall pc op args dst s,
   (fn_code f) !pc = Some (Iop op args dst s) -> single_succ_instr f pc
| SSload: forall pc chk adr args dst s,
   (fn_code f) !pc = Some (Iload chk adr args dst s) -> single_succ_instr f pc
| SSbuiltin: forall pc ef args dst s,
   (fn_code f) !pc = Some (Ibuiltin ef args dst s) -> single_succ_instr f pc
| SSstore: forall pc chk adr args src s,
   (fn_code f) !pc = Some (Istore chk adr args src s) -> single_succ_instr f pc
| SScall: forall pc sig fn args dst s,
   (fn_code f) !pc = Some (Icall sig fn args dst s) -> single_succ_instr f pc.

Lemma exec_single_succ: forall (f:function) lv es pc pc' i,
  wf_ssa_function f ->
  DataflowSolver.fixpoint f handle_instr (initial f) = (lv, es) ->
  (fn_code f) ! pc = Some i ->
  single_succ_instr f pc ->
  successors_instr i = pc'::nil ->
  exec f pc ->
  es #2 (pc, pc') = true.
Proof.
  intros f lv es pc pc' i WF FIX H H0 H1 H2.
  generalize FIX ; intro FIX'.
  apply DS.post_fixpoint in FIX as [_ [_ He]].
  unfold DS.exec_flags_sound in *.
  destruct (classic (es !!2 (pc, pc') = true)) as [Hc | Hc].
  + assumption.
  + apply not_true_iff_false in Hc.
    assert (exists i', (fn_code f) ! pc' = Some i') as [i' Hex].
    { eapply fn_code_closed; eauto. rewrite H1. auto. }
    assert (Hcfg: cfg f pc pc').
    { econstructor; eauto. rewrite H1. auto. }
    specialize (He pc pc' i' Hcfg Hc Hex).
    inv He.
  - inv H2. eelim H3; go.
    destruct H4 as [pc0 [Htrue HHcfg]]. 
    unfold fixpoint in *. simpl in *.
    rewrite FIX' in *. simpl in Htrue.
    eelim H3. econstructor 2; eauto; go.
  - destruct ((fn_code f) ! pc) eqn:eq.
    destruct i0; try contradiction.
    inv H. simpl in *. inv H1.
    inv H. inv H0; congruence.
    contradiction.
Qed.

Lemma exec_node_single_succ: forall (f:function) lv es pc pc' i,
   wf_ssa_function f ->
   DS.fixpoint f handle_instr (initial f) = (lv, es) ->
   (fn_code f) ! pc = Some i ->
   single_succ_instr f pc ->
   successors_instr i = pc'::nil ->
   exec f pc ->
   exec f pc'.
Proof.
  intros.
  assert (es #2 (pc, pc') = true).
  eapply exec_single_succ; eauto.
  right.
  exists pc. split.
  - unfold fixpoint. simpl. rewrite H0. simpl. intuition.
  - econstructor; eauto.
    assert (In pc' (pc'::nil)). auto. congruence.
Qed.

Hint Unfold successors_instr: core.

Lemma step_phi_aux: forall (f:function) ge pc pc' phib k sp rs,
   wf_ssa_function f ->
   reached f pc ->
   exec f pc ->

   (fn_code f) ! pc = Some (Inop pc') ->
   (fn_phicode f) ! pc' = Some phib ->
   index_pred (Kildall.make_predecessors (fn_code f) successors_instr) pc pc' = Some k ->

   gamma SCCP f ge sp pc rs ->
   gamma SCCP f ge sp pc' (phi_store k phib rs).
Proof.
  intros f ge pc pc' phib k sp rs WF HH H H0 H1 H2 H3.
  intros r Hr Hexr.
  destruct (classic (assigned_phi_spec (fn_phicode f) pc' r)) as [H6 | H6].
  + invh assigned_phi_spec. invh ex.
    allinv.
    destruct (nth_error x k) eqn:eq.
    * erewrite phi_store_copy2; eauto.
      assert (AVal.ge (A_r SCCP f r) (A_r SCCP f r0)).
      { case_eq (DataflowSolver.fixpoint f handle_instr (initial f)). intros lv es Hfp.
        exploit DS.post_fixpoint; eauto.
        intros [Hc [Hp He]].
        exploit Hp; eauto.
        eapply exec_single_succ with (lv:= lv); eauto; intuition.
        econstructor; eauto.
        intros.
        unfold SCCP, A_r ; simpl.
        rewrite Hfp. simpl. auto.
      }

      exploit dsd_pred_jpn'; eauto.
      { intros [Hcase1 | Hcase2].
        - destruct Hcase1. eapply G_increasing; eauto.
           eapply H3; eauto.
        - destruct Hcase2. eapply G_increasing; eauto.
          exploit ext_param_at_top ; eauto. intros Htop.
          replace (A_r SCCP f r0) with (fst (fixpoint f) r0) by reflexivity.
          eapply (G_top); eauto.
      }

    * unfold phi_store.
      assert (exists arg : reg, nth_error x k = Some arg).
      eapply fn_phiargs; eauto. invh ex. congruence.
  + destruct (peq pc (fn_entrypoint f)).
    * subst.
      exploit dsd_entry_ext_param; eauto. intros.
      replace (A_r SCCP f r) with (fst (fixpoint f) r) by reflexivity.
      eapply G_top; eauto.
      eapply ext_param_at_top with (r:= r) ; eauto.
    * erewrite phi_store_notin_preserved; eauto.
      replace (A_r SCCP f r) with (fst (fixpoint f) r) by reflexivity.
      exploit (dsd_pred_njp f WF pc pc' r) ; eauto. go.
      { intros [Hcase1 | [Hcase2 | Hcase3]]; intuition auto.
        - exploit H3; eauto.
        - exploit (H3 r); eauto.
          invh def; try congruence.
          unfold fn_code in *.
          invh assigned_code_spec; try congruence.
      }
Qed.

Lemma exec_exec_helper : forall f pc es,
 exec f pc ->
 es = (A_e SCCP f) ->
 DS.executable_node f pc es.
Proof.
  unfold SCCP, A_e ; simpl in *.
  intros. rewrite H0.
  inv H. go.
  destruct H1 as [pc0 [Hsnd Hcfg]].
  go. 
Qed.

Lemma same_fn_code1 : forall (f:function) pc res,
  forall (WF : wf_ssa_function f),
    (forall op args res pc', (fn_code f) ! pc <> Some (Iop op args res pc')) ->
    exec f pc ->
    assigned_code_spec (fn_code f) pc res ->
    is_at_Top (A_r SCCP f) res.
Proof.
  intros.
  case_eq (DS.fixpoint f handle_instr (initial f)); intros lv es FIX.
  generalize FIX; intros FIX'.
  eapply DS.post_fixpoint in FIX as [Hc [Hp _]].
  unfold DS.code_post_fixpoint in *.
  assert (AVal.ge lv !! res AVal.top).
  { inv H1; eapply Hc; eauto; try eapply exec_exec_helper; go;
    (unfold SCCP, A_e; simpl; try rewrite FIX';auto); try congruence.
  }
  unfold SCCP, A_r ; simpl.
  rewrite FIX'. simpl.
  unfold is_at_Top.
  invh AVal.ge; auto; intuition auto.
  invh pge; auto.
Qed.

Lemma G_list_val_list_match_approx : forall f ge sp lv es args rs,
  G_list SCCP ge sp rs (map (A_r SCCP f) args) rs ## args ->
  DS.fixpoint f handle_instr (initial f) = (lv, es) ->
  list_forall2 (vmatch (bctop ge)) rs ## args lv ## args.
Proof.
  induction args ; intros; go.
  simpl in *. inv H.
  econstructor; eauto.
  unfold G, SCCP, A_r in * ; simpl in * ; rewrite H0 in * ; simpl in *.
  apply H4; auto.
Qed.

Import SSAinv.
Import Utils.
  
Lemma Iop_correct : forall (f:function) pc sf op args res pc' v rs
                           (ge: Globalenvs.Genv.t fundef unit) sp m x,
                    forall (WFF: wf_ssa_function f)
                           (SINV: s_inv ge (State sf f (Values.Vptr sp Ptrofs.zero) pc rs m)),
    (fn_code f) ! pc = Some (Iop op args res pc') ->
    eval_operation ge (Values.Vptr sp Ptrofs.zero) op (rs ## args) m = Some v ->
    gamma SCCP f ge (Values.Vptr sp Ptrofs.zero) pc rs ->
    exec f pc ->
    dsd f x pc' ->
    G ge (Values.Vptr sp Ptrofs.zero) (rs # res <- v) (A_r SCCP f x) (rs # res <- v) !! x.
Proof.
  intros until x; intros WFF SINV CODE EVAL GAMMA EXE DSD.
  destruct (peq x res).
  - subst.
    rewrite PMap.gss.
    case_eq (DS.fixpoint f handle_instr (initial f)).
    intros lv es FIX.
    assert (AVal.ge (lv !! res) (eval_static_operation op lv ## args)).
    { generalize FIX ; intros FIX'.
      apply DS.post_fixpoint in FIX as [Hc _].
      unfold DS.code_post_fixpoint in Hc.
      eapply Hc; eauto.
      unfold SCCP, A_e in * ; simpl in *; auto.
      unfold exec in EXE; simpl in *.
      rewrite FIX' in EXE. simpl in *. auto.
    }
    assert (vmatch (bctop ge) v (eval_static_operation op lv ## args)).
    { exploit (all_used_approx SCCP ge f pc (Values.Vptr sp Ptrofs.zero) rs args); eauto.
      induction args; go. intros HG_list. 
      eapply eval_static_operation_sound; eauto.
      - constructor; auto.
        + intros. split; intros.
          * simpl. flatten; try solve [unfold Genv.find_symbol in *;
                                       apply Genv.genv_symb_range in H0; intuition].
            -- apply Genv.find_invert_symbol in H0; congruence.
            -- apply Genv.find_invert_symbol in H0; congruence.
          * simpl in H0; flatten H0.
            apply Genv.invert_find_symbol. auto.
        + intros. simpl. flatten.
          * split; congruence.
          * split; congruence. 
      - simpl. flatten.
      - eapply G_list_val_list_match_approx; eauto.
    }
    eapply G_increasing; eauto.
    replace (A_r SCCP f res) with ((fst (fixpoint f)) res) by reflexivity.
    unfold fixpoint ; simpl; rewrite FIX; auto.
  - exploit (dsd_pred_not_join_point f WFF pc pc' x); eauto.
    go. 
    intro contra. eapply fn_normalized with (pc := pc) in contra; go.
    + unfold successors, Kildall.successors_list.
      rewrite PTree.gmap1. unfold option_map.
      unfold fn_code in *.
      rewrite CODE. simpl. auto.
    + intros [Hcase1 | [ Hcase2 | Hcase3]]; intuition auto.
      * exploit ext_param_at_top; go.
        intros HTOP.
        replace (A_r SCCP f x) with ((fst (fixpoint f)) x) in * by reflexivity.
        eapply G_top; eauto.
      * rewrite PMap.gso; eauto.
        exploit GAMMA; eauto.
      * unfold fn_code in *.
        invh assigned_code_spec; try congruence.
Qed.

Import Dom.
Hint Resolve sdom_dom_pred fn_code_reached fn_entry_pred fn_phicode_inv
             list_nth_z_in: core.
Hint Unfold reached: core.
Hint Constructors SSA.step: core.

Lemma exec_step : forall prog0 ,
                  forall ge0  t sf sp pc rs m (f0:function) s',
   wf_ssa_function f0 ->
   sfg_inv SCCP prog0 sf ->
   gamma SCCP f0 ge0 sp pc rs ->
   OptInv.exec SCCP f0 pc ->
   step ge0 (State sf f0 sp pc rs m) t s' ->
   match s' with
   | State _ f1 _ pc' _ _ => OptInv.exec SCCP f1 pc'
   | Callstate nil _ _ _ => True
   | Callstate (Stackframe _ f2 _ pc' _ :: _) _ _ _ => OptInv.exec SCCP f2 pc'
   | Returnstate _ _ _ => True
   end.
Proof.
 intros.
    case_eq (DS.fixpoint f0 handle_instr (initial f0)); intros lv es FIX.
    generalize H3 ; intros STEP.
    inv H3; try solve [exploit exec_node_single_succ; go]; auto.
    + destruct sf; auto.
      destruct s. inv H0; go.
    + assert (es #2 (pc, ifso) = true).
      { generalize FIX ; intros FIX'.
        apply DS.post_fixpoint in FIX as [_ [_ Hes]].
        unfold DS.exec_flags_sound in *.
        assert (Hcfg: cfg f0 pc ifso) by go.
        destruct (classic (es !!2 (pc, ifso) = true)) as [Hcl | Hcl]; auto.
        apply not_true_iff_false in Hcl.
        assert (exists i, (fn_code f0) ! ifso = Some i)
          as [i Hpc'] by (eapply fn_code_closed; go).
        specialize (Hes pc ifso i Hcfg Hcl Hpc').
        destruct Hes.
        + eelim H3; eapply exec_exec_helper; eauto.
          unfold SCCP, A_e ; simpl ; rewrite FIX'; go.
        + flatten H12. destruct H3 as [Hso _].
          specialize (Hso (eq_refl _)).
          exploit (eval_static_condition_sound (bctop ge0) cond (rs## args) m (lv## args)); eauto. 
          eapply G_list_val_list_match_approx; eauto.
          eapply all_used_approx; eauto.
          induction args; go.
          intros.
          rewrite Hso in H3 at 1. inv H3; try congruence. 
      }
      right. exists pc ; split; go.
      unfold fixpoint ; rewrite FIX; simpl; auto.
    + assert (es #2 (pc, ifnot) = true).
      { generalize FIX ; intros FIX'.
        apply DS.post_fixpoint in FIX as [_ [_ Hes]].
        unfold DS.exec_flags_sound in *.
        assert (Hcfg: cfg f0 pc ifnot) by go.
        destruct (classic (es !!2 (pc, ifnot) = true)) as [Hcl | Hcl]; auto.
        apply not_true_iff_false in Hcl.
        assert (exists i, (fn_code f0) ! ifnot = Some i)
          as [i Hpc'] by (eapply fn_code_closed; go).
        specialize (Hes pc ifnot i Hcfg Hcl Hpc').
        destruct Hes.
        + eelim H3; eapply exec_exec_helper; eauto.
          unfold SCCP, A_e ; simpl ; rewrite FIX'; go.
        + flatten H12. destruct H3 as [_ Hifnot].
          specialize (Hifnot (eq_refl _)).
          exploit (eval_static_condition_sound (bctop ge0) cond (rs## args) m (lv## args)); eauto.
          eapply G_list_val_list_match_approx; eauto.
          eapply all_used_approx; eauto.
          induction args; go.
          intros. rewrite Hifnot in H3 at 1. inv H3; try congruence. 
      }
      right. exists pc ; split; go.
      unfold fixpoint ; rewrite FIX; simpl; auto.
    + assert (es #2 (pc, pc') = true).
      { generalize FIX ; intros FIX'.
        apply DS.post_fixpoint in FIX as [_ [_ Hes]].
        unfold DS.exec_flags_sound in *.
        assert (Hcfg: cfg f0 pc pc') by go.
        destruct (classic (es !!2 (pc, pc') = true)) as [Hcl | Hcl]; auto.
        apply not_true_iff_false in Hcl.
        assert (exists i, (fn_code f0) ! pc' = Some i)
          as [i Hpc'] by (eapply fn_code_closed; go).
        specialize (Hes pc pc' i Hcfg Hcl Hpc').
        destruct Hes.
        + eelim H3; eapply exec_exec_helper; eauto.
          unfold SCCP, A_e ; simpl ; rewrite FIX'; go.
        + flatten H12. destruct H3 as [n0 [Hlv Hlistnth]].
          assert (n0 = n).
          {
            assert (vmatch (bctop ge0) rs !! arg  lv !! arg).
            exploit used_match_approx; eauto.
            econstructor 10; eauto. intros.
            unfold G, SCCP, A_r in * ; simpl in *; auto.
            rewrite FIX' in *. simpl in *. go.
            rewrite Hlv in H3 at 1.
            rewrite H13 in H3 at 1.
            inv H3. auto. 
          }
          subst.
          congruence.
      }
      right. exists pc ; split; go.
      unfold fixpoint ; rewrite FIX; simpl; auto.
Unshelve.
all: go. 
Qed.

(** * Structural properties. Helpers *)

Lemma new_code_same_or_Iop :
  forall (f:function) (Hwf: wf_ssa_function f) pc ins,
    (fn_code f) ! pc = Some ins ->
    transf_instr (fst (fixpoint f)) pc ins = ins
    \/ match ins with
       | Iop _ _ dst pc'
       | Iload _ _ _ dst pc'
       | Icall _ _ _ dst pc'
       | Ibuiltin _ _ (BR dst) pc' =>
         exists op' args',
         transf_instr (fst (fixpoint f)) pc ins = Iop op' args' dst pc'
         /\ forall x, In x args' -> exists d : node, def f x d /\ SSA.sdom f d pc
       | _ => False
       end.
Proof.
  destruct ins; simpl; flatten; eauto; right.
  exists o0; exists nil;
    split; auto;
      intros x Hin; inv Hin.
Qed.

Lemma join_point_transf_function :
  forall (f:function) (Hwf: wf_ssa_function f) j,
    join_point j (transf_function f) <-> join_point j f.
Proof.
  intros.
  eapply Opt.join_point_transf_function; eauto.
  eapply new_code_same_or_Iop; eauto.
Qed.

Lemma make_predecessors_transf_function: forall (f:function) (Hwf: wf_ssa_function f),
  (Kildall.make_predecessors (fn_code (transf_function f)) successors_instr) =
  (Kildall.make_predecessors (fn_code f) successors_instr).
Proof.
  intros.
  eapply Opt.make_predecessors_transf_function; eauto.
  eapply new_code_same_or_Iop; eauto.
Qed.

End AuxResults.
