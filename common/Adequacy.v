Require Import Coqlib.
Require Import sflib.
Require Import Events.
Require Import Simulation.
Require Import Behaviors2.
(* Require Import Classical. *)
From Paco Require Import paco.
(* From Ordinal Require Import Ordinal. *)

Set Implicit Arguments.


Hint Constructors _gsim: core.

Section Adequacy.
  
Variable L1 L2: gsemantics.

Definition get_tr (otr: option trace): trace :=
  match otr with
  | None => E0
  | Some tr => tr
  end.

Lemma adequacy_spin_step
  bt otr st_src0 gst_tgt0
  (SIM: gsim L1 L2 false bt otr (inl st_src0) gst_tgt0)
  (BEH: BSem.state_div L2 gst_tgt0):
  exists S_src0 (bt1:bool) gst_tgt1,
     <<BEH: GStep L1 st_src0 S_src0>>
  /\ <<TR: forall tr1 st_src1 (IN: S_src0 tr1 st_src1), tr1 = E0>>
  /\ <<DIV: BSem.state_div L2 gst_tgt1>>
  /\ <<BT: bt -> bt1>> /\ <<TR: get_tr otr = E0>>
  /\ <<SIM: gsim L1 L2 false bt1 None (inr S_src0) gst_tgt1>>
.
Proof.
  remember false as bs.
  remember (inl st_src0) as gst_src0.
  punfold SIM. ginduction SIM; ss; i; clarify; eauto.
  - punfold BEH. inv BEH.
    des. exfalso. eapply final_nostep; cycle 1; eauto.
  - ss. punfold BEH. inv BEH. des. pclearbot.
    exploit H; pclearbot; eauto.
  - esplits; eauto; i.
    inv SIM; ss; clarify; eauto.
    exploit STEP; eauto. i. des.
    inv H; ss. clarify.
    punfold BEH. inv BEH. exploit DIV; eauto. i. des; eauto.
  - exploit IHSIM; eauto.
    { punfold BEH. inv BEH. exploit DIV; eauto. i. des; pclearbot; eauto. }
    i. des; ss. eexists. exists bt1. esplits; eauto.
    punfold BEH. inv BEH. exploit DIV0; eauto. i. des; pclearbot; subst; eauto.
Qed.

Lemma adequacy_spin_aux
  bs bt otr gst_src0 gst_tgt0
  (SIM: gsim L1 L2 bs bt otr gst_src0 gst_tgt0)
  (BEH: BSem.state_div L2 gst_tgt0):
  <<BEH: BSem.state_div L1 gst_src0>>.
Proof.
  revert_until bs. revert bs. pcofix CIH. i.
  cut (paco1 (BSem._state_div L1) r gst_src0 /\ (get_tr otr = E0)); try by (i; des; eauto).
  punfold SIM. revert_until CIH.
  induction 1; ss; i; clarify.
  - punfold BEH. inv BEH.
    des. exfalso. eapply final_nostep; cycle 1; eauto.
  - pclearbot. exploit adequacy_spin_step; eauto. i. des; ss.
    split; eauto.
    pstep. econs. esplits; eauto.
    right. eapply CIH; eauto.
  - punfold BEH. inv BEH. pclearbot.
    exploit H; eauto.
  - exploit IHSIM; eauto. i. des; ss.
    split; eauto.
  - split; eauto.
    pstep. econs 2. i. exploit H; eauto. i. des; ss; clarify.
    splits; eauto.
  - punfold BEH. inv BEH. exploit DIV; eauto. i. des; ss; clarify.
    pclearbot. exploit IHSIM; eauto.
Qed.

Lemma adequacy_spin
  bs bt tr gst_src0 gst_tgt0
  (SIM: gsim L1 L2 bs bt tr gst_src0 gst_tgt0)
  (BEH: BSem.of_state L2 gst_tgt0 Beh.spin)
  :
  BSem.of_state L1 gst_src0 Beh.spin.
Proof.
  eapply BSem.div_to_spin, adequacy_spin_aux, BSem.spin_to_div; eauto.
Qed.

Lemma beh_oom_dec (beh: Beh.t):
  beh = Beh.oom \/ beh <> Beh.oom.
Proof.
  destruct beh; eauto; ii; right; ss.
Qed.

Lemma adequacy_aux
  bs bt otr gst_src0 st_tgt0 beh
  (NOTOOM: beh <> Beh.oom)
  (SIM: gsim L1 L2 bs bt otr gst_src0 (inl st_tgt0))
  (BEH: BSem.of_state L2 (inl st_tgt0) (Beh.app (get_tr otr) beh))
  :
  <<BEH: BSem.of_state L1 gst_src0 beh>>.
Proof.
  revert_until bs. revert bs. pcofix CIH. i.

  remember (Beh.app (get_tr otr) beh) as beh0.
  move BEH before CIH. revert_until BEH. punfold BEH.
  pattern (inl st_tgt0: gstate _), beh0. revert_until CIH.
  apply BSem._of_state_ind_gen; i.
  - destruct otr as [[]|], beh; ss.
  - remember (inl st0) as gst_tgt0.
    pstep. move SIM before __CASE__. revert_until SIM.
    punfold SIM. induction SIM; i; ss; clarify; subst; eauto.
    + ss. subst. eauto.
    + remember false as bs in GSIM at 1. clear Heqbs.
      remember false as bt in GSIM at 1.
      remember None as tr in GSIM.
      assert(Htr: get_tr tr = E0) by (subst; eauto). clear Heqtr.
      remember (inl st_src0 : gstate _) as gst_src0. clear Heqgst_src0 st_src0.
      remember (inl st0) as gst_tgt0.
      destruct GSIM as [GSIM|]; ss. move GSIM before __CASE__0. revert_until GSIM.
      punfold GSIM. induction GSIM; i; ss; clarify; eauto.
      eapply BSem.sb_astep; i; subst; eauto.
      exploit STEP; eauto. i. inv H2; ss.
    + eapply BSem.sb_astep; i; subst; eauto.
      exploit STEP; eauto. i. inv H2; ss.
  - destruct beh; try by (destruct otr as [[]|]; ss).
    eapply paco2_mon_bot; eauto. eapply adequacy_spin; eauto.
  - subst. remember (inl st0) as gst_tgt0.
    pstep. move SIM before __CASE__. revert_until SIM.
    punfold SIM. induction SIM; i; ss; clarify.
    + exfalso. eapply final_nostep; cycle 1; eauto.
    + remember false as bs in GSIM at 1. clear Heqbs.
      remember false as bt in GSIM at 1.
      remember None as tr in GSIM.
      assert(Htr: get_tr tr = E0) by (subst; eauto). clear Heqtr.
      remember (inl st_src0 : gstate _) as gst_src0. clear Heqgst_src0 st_src0.
      remember (inl st0) as gst_tgt0.
      pclearbot. move GSIM before __CASE__0. revert_until GSIM.
      punfold GSIM. induction GSIM; i; ss; clarify; eauto.
      * exfalso. eapply final_nostep; cycle 1; eauto.
      * clear H. exploit STEP; eauto. i. inv H; ss; clarify.
        inv BSIM; ss; clarify.
        eapply BSem.sb_dstep; eauto.
        eapply BSem.sb_astep; i.
        { exploit STEP0; eauto. subst. i. inv H; ss; clarify.
          exploit IH; eauto. i. punfold H. }
        exploit STEP0; eauto. i. inv H0; ss; clarify.
        exploit OFST2; eauto. i. des. pclearbot.
        esplits; cycle 1; eauto.
        destruct (beh_oom_dec es1'); subst; eauto.
        right. eapply CIH; eauto.
      * eapply BSem.sb_astep; i; subst; eauto.
        exploit STEP; eauto. i. inv H1; ss.
    + clear H. exploit STEP; eauto. i. inv H; ss; clarify.
      inv BSIM; ss; clarify.
      eapply BSem.sb_dstep; eauto.
      eapply BSem.sb_astep; i.
      { exploit STEP0; eauto. subst. i. inv H; ss; clarify.
        exploit IH; eauto. i. punfold H. }
      exploit STEP0; eauto. i. inv H0; ss; clarify.
      exploit OFST2; eauto. i. des. pclearbot.
      esplits; cycle 1; eauto.
      destruct (beh_oom_dec es1'); subst; eauto.
      right. eapply CIH; eauto.
    + exploit IHSIM; eauto.
    + eapply BSem.sb_astep; i; subst; eauto.
      exploit STEP; eauto. i. inv H1; ss.
Qed.

Lemma adequacy
  st_src0 st_tgt0
  (SIM: gsim L1 L2 false false None (inl st_src0) (inl st_tgt0)) :
  <<IMPR: BSem.improves (BSem.of_state L1 (inl st_src0)) (BSem.of_state L2 (inl st_tgt0))>>.
Proof.
  ii. destruct (beh_oom_dec x0); subst; eauto.
  eapply adequacy_aux; eauto.
Qed.

Lemma adequacy_init
  (SIM: general_simulation L1 L2):
  <<IMPR: BSem.improves (BSem.of_program L1) (BSem.of_program L2)>>.
Proof.
  ii. inv PR.
  - inv SIM. inv props. inv gsim_initial_states_sim.
    { econs 2; eauto. }
    des. exploit INITSIM; try eapply H; eauto. i. des.
    econs; eauto. eapply adequacy; eauto.
  - inv SIM. inv props. inv gsim_initial_states_sim.
    { econs 2; eauto. }
    des. exfalso. eapply H. eauto.
Qed.

End Adequacy.
