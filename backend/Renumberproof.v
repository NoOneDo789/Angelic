(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Postorder renumbering of RTL control-flow graphs. *)

Require Import Coqlib Maps Postorder.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL Renumber.
Require Import Simulation sflib Classical.
From Paco Require Import paco.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (Genv.find_funct_transf TRANSL).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (Genv.find_symbol_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; reflexivity.
Qed.

Lemma find_function_translated:
  forall ros rs fd,
  find_function ge ros rs = Some fd ->
  find_function tge ros rs = Some (transf_fundef fd).
Proof.
  unfold find_function; intros. destruct ros as [r|id].
  eapply functions_translated; eauto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
  eapply function_ptr_translated; eauto.
Qed.

(** Effect of an injective renaming of nodes on a CFG. *)

Section RENUMBER.

Variable f: PTree.t positive.

Hypothesis f_inj: forall x1 x2 y, f!x1 = Some y -> f!x2 = Some y -> x1 = x2.

Lemma renum_cfg_nodes:
  forall c x y i,
  c!x = Some i -> f!x = Some y -> (renum_cfg f c)!y = Some(renum_instr f i).
Proof.
  set (P := fun (c c': code) =>
              forall x y i, c!x = Some i -> f!x = Some y -> c'!y = Some(renum_instr f i)).
  intros c0. change (P c0 (renum_cfg f c0)). unfold renum_cfg.
  apply PTree_Properties.fold_rec; unfold P; intros.
  (* extensionality *)
  eapply H0; eauto. rewrite H; auto.
  (* base *)
  rewrite PTree.gempty in H; congruence.
  (* induction *)
  rewrite PTree.gsspec in H2. unfold renum_node. destruct (peq x k).
  inv H2. rewrite H3. apply PTree.gss.
  destruct f!k as [y'|] eqn:?.
  rewrite PTree.gso. eauto. red; intros; subst y'. elim n. eapply f_inj; eauto.
  eauto.
Qed.

End RENUMBER.

Definition pnum (f: function) := postorder (successors_map f) f.(fn_entrypoint).

Definition reach (f: function) (pc: node) := reachable (successors_map f) f.(fn_entrypoint) pc.

Lemma transf_function_at:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  reach f pc ->
  (transf_function f).(fn_code)!(renum_pc (pnum f) pc) = Some(renum_instr (pnum f) i).
Proof.
  intros.
  destruct (postorder_correct (successors_map f) f.(fn_entrypoint)) as [A B].
  fold (pnum f) in *.
  unfold renum_pc. destruct (pnum f)! pc as [pc'|] eqn:?.
  simpl. eapply renum_cfg_nodes; eauto.
  elim (B pc); auto. unfold successors_map. rewrite PTree.gmap1. rewrite H. simpl. congruence.
Qed.

Ltac TR_AT :=
  match goal with
  | [ A: (fn_code _)!_ = Some _ , B: reach _ _ |- _ ] =>
        generalize (transf_function_at _ _ _ A B); simpl renum_instr; intros
  end.

Lemma reach_succ:
  forall f pc i s,
  f.(fn_code)!pc = Some i -> In s (successors_instr i) ->
  reach f pc -> reach f s.
Proof.
  unfold reach; intros. econstructor; eauto.
  unfold successors_map. rewrite PTree.gmap1. rewrite H. auto.
Qed.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs
        (REACH: reach f pc),
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res (transf_function f) sp (renum_pc (pnum f) pc) rs).

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk'
        (STACKS: list_forall2 match_frames stk stk')
        (REACH: reach f pc),
      match_states (State stk f sp pc rs m)
                   (State stk' (transf_function f) sp (renum_pc (pnum f) pc) rs m)
  | match_callstates: forall stk f args m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk f args m)
                   (Callstate stk' (transf_fundef f) args m)
  | match_returnstates: forall stk v m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m)
                   (Returnstate stk' v m).

Lemma step_simulation:
  forall S1 t S2 (INT: ~ is_external ge S1), RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 2; intros S1' MS; inv MS; try TR_AT.
(* nop *)
  econstructor; split. eapply exec_Inop; eauto.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* op *)
  econstructor; split.
  eapply exec_Iop; eauto.
  instantiate (1 := v). rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* itop *)
  econs; split.
  eapply exec_Iop_itop; eauto.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* load *)
  econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = Some a).
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eapply exec_Iload; eauto.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* store *)
  econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = Some a).
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eapply exec_Istore; eauto.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* call *)
  econstructor; split.
  eapply exec_Icall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  constructor. constructor; auto. constructor. eapply reach_succ; eauto. simpl; auto.
(* tailcall *)
  econstructor; split.
  eapply exec_Itailcall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  constructor. auto.
(* builtin *)
  ss. des_ifs.
  (* exploit eval_builtin_args_preserved. exact symbols_preserved. eauto. i. *)
  (* exploit external_call_symbols_preserved; eauto. apply senv_preserved. i. des. *)
  (* econstructor; split. *)
  (* eapply exec_Ibuiltin; try eapply DSTEPTGT; eauto. *)
  (* { rr. i. erewrite <- USB in H5, H6. eapply SINGLE; eauto. } *)
  (* { erewrite USB in H2. eauto. } *)
  (*   (* eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved. *) *)
  (*   (* exploit external_call_symbols_preserved; eauto. apply senv_preserved. *) *)
  (*   (* i. des.  *) *)
  (* constructor; auto. eapply reach_succ; eauto. simpl; auto. *)
(* cond *)
  econstructor; split.
  eapply exec_Icond; eauto.
  replace (if b then renum_pc (pnum f) ifso else renum_pc (pnum f) ifnot)
     with (renum_pc (pnum f) (if b then ifso else ifnot)).
  constructor; auto. eapply reach_succ; eauto. simpl. destruct b; auto.
  destruct b; auto.
(* jumptbl *)
  econstructor; split.
  eapply exec_Ijumptable; eauto. rewrite list_nth_z_map. rewrite H1. simpl; eauto.
  constructor; auto. eapply reach_succ; eauto. simpl. eapply list_nth_z_in; eauto.
(* return *)
  econstructor; split.
  eapply exec_Ireturn; eauto.
  constructor; auto.
(* internal function *)
  simpl. econstructor; split.
  eapply exec_function_internal; eauto.
  constructor; auto. unfold reach. constructor.
(* external function *)
  ss.
  (* econstructor; split. *)
  (* exploit external_call_symbols_preserved; eauto. apply senv_preserved. i. des. *)
  (* eapply exec_function_external; try eapply DSTEPTGT; eauto. *)
  (* { rr. i. erewrite <- USB in H1, H2. eapply SINGLE; eauto. } *)
  (* { rewrite USB in H0. eauto. } *)
  (* (* eapply external_call_symbols_preserved; eauto. apply senv_preserved. *) *)
  (* constructor; auto. *)
(* return *)
  inv STACKS. inv H1.
  econstructor; split.
  eapply exec_return; eauto.
  constructor; auto.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inv H. econstructor; split.
  econstructor.
    eapply (Genv.init_mem_transf TRANSL); eauto.
    rewrite symbols_preserved. rewrite (match_program_main TRANSL). eauto.
    eapply function_ptr_translated; eauto.
    rewrite <- H3; apply sig_preserved.
  constructor. constructor.
Qed.

Lemma deterministic_initial_state:
  forall st0 st1, RTL.initial_state tprog st0 -> RTL.initial_state tprog st1 -> st0 = st1.
Proof. ii. inv H; inv H0; ss. clarify. subst ge0 ge1. clarify. Qed.

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor.
Qed.

Lemma match_states_gsim
      st_src0 st_tgt0
      (MATCH: match_states st_src0 st_tgt0)
  :
    gsim (RTL.gsemantics prog) (RTL.gsemantics tprog) false false None (inl st_src0) (inl st_tgt0).
Proof.
  generalize dependent st_src0. generalize dependent st_tgt0.
  pcofix CIH. i. pfold.
  destruct (final_state (RTL.gsemantics tprog) st_tgt0) eqn:FINAL.
  { assert (final_state (RTL.gsemantics prog) st_src0 = Some i).
    { inv MATCH; ss. des_ifs. inv STACKS. }
    eapply gsim_final; eauto. }
  destruct (classic (RTL.is_external ge st_src0)); cycle 1.
  (* not external *)
  - eapply gsim_dstep_tgt; eauto. i.
    assert (FINALSRC: final_state (RTL.gsemantics prog) st_src0 = None).
    { inv MATCH; ss. des_ifs. inv STACKS. }
    eapply gsim_dstep_src; eauto.
    { instantiate (1:=(fun t st_src1 => RTL.step ge st_src0 t st_src1 /\ t = E0)).
      econs; eauto. }
    eapply gsim_astep_src; eauto. i. ss. des. subst.
    exploit step_simulation; eauto. i. des. inv DTGT; cycle 1.
    { inv MATCH; ss; des_ifs; try TR_AT; ss; clarify. inv ASRC; clarify. }
    eapply gsim_astep_tgt; eauto.
    { ss. esplits; eauto. }
    eapply gsim_coind; eauto.
  (* external *)
  - eapply gsim_dstep_tgt; eauto. i.
    inv DTGT; clarify.
    { inv MATCH; ss; des_ifs; try TR_AT; ss; clarify. }
    inv STEP.
    + unfold RTL.is_external in H. destruct st_src0; ss; inversion MATCH; subst.
      destruct ((fn_code f0) ! pc0) eqn:BLTIN; ss. destruct i; ss.
      TR_AT. ss. clarify.
      exploit eval_builtin_args_preserved.
      { symmetry. eapply symbols_preserved. }
      { eauto. }
      i. exploit external_call_symbols_preserved.
      { symmetry. eapply senv_preserved. }
      { eauto. }
      i. des.
      set (S_src1:= (fun tr st => match st with
                               | State s1 f1 sp1 pc1 rs1 m1 =>
                                   s1 = stack /\ f1 = f0 /\ sp1 = sp /\ pc1 = n /\
                                     exists v, S_ext tr v m1 /\ rs1 = (regmap_setres res v rs)
                                     (* (match res with *)
                                     (*  | BR r => exists v, (S_ext tr v m1) /\ rs1 = (regmap_setres res v rs) *)
                                     (*  | _ => exists v, S_ext tr v m1 /\ rs1 = (regmap_setres res v rs) *)
                                     (*  end) *)
                               | _ => False
                               end)).
      eapply gsim_dstep_src; eauto.
      { instantiate (1:= S_src1).
        econs 2; ss. des_ifs. econs; eauto. ii. subst S_src1. ss. esplits; eauto.
        rewrite USB; eauto. }
      eapply gsim_astep_src; eauto. i.
      subst S_src1. ss. des_ifs. des. subst.
      eapply gsim_astep_tgt; eauto. 
      eapply gsim_coind; eauto.
      right. eapply CIH; eauto.
      econs 1; eauto. eapply reach_succ; eauto. simpl; auto.
    + unfold RTL.is_external in H.
      destruct st_src0; ss; des_ifs; inversion MATCH; subst.
      exploit external_call_symbols_preserved.
      { symmetry. eapply senv_preserved. }
      { eauto. }
      i. des.
      set (S_src1:= (fun tr st => match st with
                               | Returnstate s1 vres1 m1 => s1 = stack /\ S_ext tr vres1 m1
                               | _ => False
                               end)).
      eapply gsim_dstep_src; eauto.
      { econs 2; ss. econs; eauto. ii.
        instantiate (1:= S_src1). ss. esplits; eauto.
        erewrite USB; eauto. }
      eapply gsim_astep_src; eauto. i.
      subst S_src1. ss. des_ifs. des. subst.
      eapply gsim_astep_tgt; eauto. 
      eapply gsim_coind; eauto.
      right. eapply CIH; eauto.
      econs; eauto.
Qed.

Theorem transf_program_correct:
  general_simulation (RTL.gsemantics prog) (RTL.gsemantics tprog).
Proof.
  econs. econs.
  destruct (classic (exists st_src, initial_state (RTL.gsemantics prog) st_src)).
  2:{ econs; eauto. }
  des. econs 2; eauto.
  { exploit transf_initial_states; eauto. i. des. eauto. }
  i. exploit transf_initial_states; eauto. i. des.
  exploit (deterministic_initial_state st_tgt S2); eauto. i. subst.
  esplits; eauto. eapply match_states_gsim. eauto.
Qed.

End PRESERVATION.







