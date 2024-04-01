Require Import Values.
Require Import Globalenvs.
(* Require Import Memory. *)
Require Import Integers.
Require Import Events.
(* Require Import AST. *)
From Paco Require Import paco.
Require Import Coqlib.
Require Import sflib.
Require Import Axioms.
Require Import Relations.
Require Import Wellfounded.
Require Import Smallstep.
Require Import Program.Equality.

Set Implicit Arguments.

Section GENSTEP.

Variable genv: Type.
Variable state: Type.

(* Variable rstep: genv -> state -> (trace -> state -> Prop) -> Prop. *)

Definition genstep := state -> (trace -> state -> Prop) -> Prop.

Definition nogenstep (s: state) (r: genstep) : Prop :=
  forall S, ~ (r s S).

Definition genstep_compose (r0 r1: genstep): genstep :=
  fun st0 S2 =>
    exists S0 (DSTEP0: r0 st0 S0),
      (forall st1 tr1 (ASTEP0: S0 tr1 st1),
          (exists S1 (DSTEP1: r1 st1 S1),
              (forall st2 tr2 (ASTEP1: S1 tr2 st2),
                  S2 (tr1 ++ tr2) st2))).

Inductive genstep_star (r: genstep): genstep :=
| genstep_star_refl
    s (S: trace -> state -> Prop)
    (IN: S [] s)
  :
  genstep_star r s S
| genstep_star_step
    s S
    (IN: genstep_compose r (genstep_star r) s S)
  :
  genstep_star r s S
.

Inductive genstep_plus (r: genstep): genstep :=
| genstep_left
    S s
    (IN: genstep_compose r (genstep_star r) s S)
  :
  genstep_plus r s S
.

End GENSTEP.

Record gsemantics : Type := GSemantics_gen {
  state: Type;
  genvtype: Type;
  gstep : genvtype -> state -> (trace -> state -> Prop) -> Prop;
  initial_state: state -> Prop;
  final_state: state -> option int;
  (* is_external: genvtype -> state -> Prop;                               *)
  globalenv: genvtype;
  symbolenv: Senv.t;
  final_nostep: forall s vi, final_state s = (Some vi) -> nogenstep s (gstep globalenv)                           
}.

(* Definition GSemantics {state funtype vartype: Type} *)
(*                       (genstep: state -> (trace -> state -> Prop) -> Prop) *)
(*                       (initial_state: state -> Prop) *)
(*                       (final_state: state -> int -> Prop) *)
(*                       (is_external: Genv.t funtype vartype -> state -> Prop) *)
(*                       (globalenv: Genv.t funtype vartype) : gsemantics := *)
(*   {| state := state; *)
(*      genvtype := Genv.t funtype vartype; *)
(*      gstep := fun genv: Genv.t funtype vartype => genstep; *)
(*      initial_state := initial_state; *)
(*      final_state := final_state; *)
(*      (* is_external := is_external; *) *)
(*      globalenv := globalenv; *)
(*      symbolenv := Genv.to_senv globalenv |}. *)

Definition GStep (L: gsemantics) :=
  (gstep L (globalenv L)).
Definition GStar (L: gsemantics) :=
  (genstep_star (GStep L)).
Definition GPlus (L: gsemantics) :=
  (genstep_plus (GStep L)).
Definition NoGStep (L: gsemantics) :=
  (nogenstep (GStep L)).

(* Definition deterministic_angelic (L: gsemantics) : Prop := *)
(*   forall st St (STEP: GStep L st St), (~ exists tr st0, St tr st0) \/ (exists tr st0, St tr st0). *)

Lemma genplus_one
  L s S
  (STEP: GStep L s S)
  :
  <<PLUS: GPlus L s S>>.
Proof.
  rr. econs. unfold genstep_compose.
  esplits; eauto. ii.
  exists (fun t s => t = E0 /\ s = st1).
  esplits.
  { econs; eauto. }
  ii. des; subst. rewrite E0_right; eauto.
Qed.

Definition non_empty (L: gsemantics) (S: trace -> state L -> Prop) : Prop :=
  exists t st, S t st.
(* Lemma gstar_nonempty *)
(*   L s S *)
(*   (STAR: GStar L s S): *)
  
Section GENERAL_SIM.

Variables L1 L2: gsemantics.

Definition get_trace (ot: option trace) : trace :=
  match ot with
  | None => E0
  | Some tr => tr
  end.

Definition add_trace (t: trace) (ot: option trace) : option trace :=
  match ot with
  | None => Some t
  | Some t' => Some (t ++ t')
  end.

Definition gstate (S: Type) : Type := (S + (trace -> S -> Prop))%type.

Inductive _gsim (gsim: bool -> bool -> option trace -> gstate L1.(state) -> gstate L2.(state) -> Prop) :
  bool -> bool -> option trace -> gstate L1.(state) -> gstate L2.(state) -> Prop :=
| gsim_final (__CASE__ := "GSIM Final")
    (gst_src0: gstate L1.(state)) (gst_tgt0: gstate L2.(state))
    st_src0 st_tgt0 (GSSRC: gst_src0 = inl st_src0) (GSTGT: gst_tgt0 = inl st_tgt0)
    bs bt
    otr (TR: otr = None)
    retv
    (FINALTGT: final_state L2 st_tgt0 = Some retv)
    (FINALSRC: final_state L1 st_src0 = Some retv):
  _gsim gsim bs bt otr gst_src0 gst_tgt0

| gsim_coind (__CASE__ := "GSIM Coind")
    (gst_src0: gstate L1.(state)) (gst_tgt0: gstate L2.(state))
    st_src0 st_tgt0 (GSSRC: gst_src0 = inl st_src0) (GSTGT: gst_tgt0 = inl st_tgt0)
    bs bt (BS: bs = true) (BT: bt = true)
    otr (TR: otr = None)
    (GSIM: gsim false false otr gst_src0 gst_tgt0):
  _gsim gsim bs bt otr gst_src0 gst_tgt0

| gsim_dstep_tgt (__CASE__ := "GSIM Dstep Tgt")
    (gst_src0: gstate L1.(state)) (gst_tgt0: gstate L2.(state))
    st_src0 st_tgt0 (GSSRC: gst_src0 = inl st_src0) (GSTGT: gst_tgt0 = inl st_tgt0)
    (NOTFINAL: final_state L2 st_tgt0 = None) (* without this condition final state of L2 matches every states of L1  *)
    bs bt
    otr (TR: otr = None)
    (STEP: forall S_tgt1
             (DTGT: GStep L2 st_tgt0 S_tgt1),
             <<BSIM: _gsim gsim bs bt otr gst_src0 (inr S_tgt1)>>):
  _gsim gsim bs bt otr gst_src0 gst_tgt0

| gsim_dstep_src (__CASE__ := "GSIM Dstep Src")
    (gst_src0: gstate L1.(state)) (gst_tgt0: gstate L2.(state))
    st_src0 (GSSRC: gst_src0 = inl st_src0)
    bs bt
    otr (TR: otr = None)
            S_src1
            (DSRC: GStep L1 st_src0 S_src1)
            (BSIM: _gsim gsim bs bt otr (inr S_src1) gst_tgt0):
  _gsim gsim bs bt otr gst_src0 gst_tgt0

| gsim_astep_src (__CASE__ := "GSIM Astep Src")
    (gst_src0: gstate L1.(state)) (gst_tgt0: gstate L2.(state))
    S_src0 (GSSRC: gst_src0 = inr S_src0)
    bs bt
    otr (TR: otr = None)
    (STEP: forall tr' st_src1
             (ASRC: S_src0 tr' st_src1),
             <<BSIM: _gsim gsim true bt (Some tr') (inl st_src1) gst_tgt0>>):
  _gsim gsim bs bt otr gst_src0 gst_tgt0

| gsim_astep_tgt (__CASE__ := "GSIM Astep Tgt")
    (gst_src0: gstate L1.(state)) (gst_tgt0: gstate L2.(state))
    st_src0 S_tgt0 (GSSRC: gst_src0 = inl st_src0) (GSTGT: gst_tgt0 = inr S_tgt0)
    bs bt
    tr otr (TR: otr = Some tr)
             st_tgt1
             (ATGT: S_tgt0 tr st_tgt1)
             (BSIM: _gsim gsim bs true None gst_src0 (inl st_tgt1)):
  _gsim gsim bs bt otr gst_src0 gst_tgt0
.

(* Inductive _gsim (gsim: option trace -> option trace -> gstate L1.(state) -> gstate L2.(state) -> Prop) : *)
(*   option trace -> option trace -> gstate L1.(state) -> gstate L2.(state) -> Prop := *)
(* | gsim_final *)
(*     tr_src tr_tgt (gst_src0: gstate L1.(state)) (gst_tgt0: gstate L2.(state)) *)
(*     st_src0 st_tgt0 (GSSRC: gst_src0 = inl st_src0) (GSTGT: gst_tgt0 = inl st_tgt0) *)
(*     retv *)
(*     (SAME: get_trace tr_src = get_trace tr_tgt) *)
(*     (FINALTGT: final_state L2 st_tgt0 retv) *)
(*     (FINALSRC: final_state L1 st_src0 retv): *)
(*   _gsim gsim tr_src tr_tgt gst_src0 gst_tgt0 *)
(* | gsim_coind *)
(*     tr_src tr_tgt (gst_src0: gstate L1.(state)) (gst_tgt0: gstate L2.(state)) *)
(*     st_src0 st_tgt0 (GSSRC: gst_src0 = inl st_src0) (GSTGT: gst_tgt0 = inl st_tgt0) *)
(*     tr *)
(*     (TRSRC: tr_src = Some tr) (TRTGT: tr_tgt = Some tr) *)
(*     (GSIM: gsim None None gst_src0 gst_tgt0): *)
(*   _gsim gsim tr_src tr_tgt gst_src0 gst_tgt0 *)
(* | gsim_dstep_tgt *)
(*     tr_src tr_tgt (gst_src0: gstate L1.(state)) (gst_tgt0: gstate L2.(state)) *)
(*     st_src0 st_tgt0 (GSSRC: gst_src0 = inl st_src0) (GSTGT: gst_tgt0 = inl st_tgt0) *)
(*     (STEP: forall S_tgt1 *)
(*              (DTGT: GStep L2 st_tgt0 S_tgt1), *)
(*              <<BSIM: _gsim gsim tr_src tr_tgt gst_src0 (inr S_tgt1)>>): *)
(*   _gsim gsim tr_src tr_tgt gst_src0 gst_tgt0 *)
(* | gsim_dstep_src *)
(*     tr_src tr_tgt (gst_src0: gstate L1.(state)) (gst_tgt0: gstate L2.(state)) *)
(*     st_src0 (GSSRC: gst_src0 = inl st_src0) *)
(*             S_src1 *)
(*             (DSRC: GStep L1 st_src0 S_src1) *)
(*             (BSIM: _gsim gsim tr_src tr_tgt (inr S_src1) gst_tgt0): *)
(*   _gsim gsim tr_src tr_tgt gst_src0 gst_tgt0 *)
(* | gsim_astep_src *)
(*     tr_src tr_tgt (gst_src0: gstate L1.(state)) (gst_tgt0: gstate L2.(state)) *)
(*     S_src0 (GSSRC: gst_src0 = inr S_src0) *)
(*     (STEP: forall tr st_src1 *)
(*              (ASRC: S_src0 tr st_src1), *)
(*              <<BSIM: _gsim gsim (add_trace tr tr_src) tr_tgt (inl st_src1) gst_tgt0>>): *)
(*   _gsim gsim tr_src tr_tgt gst_src0 gst_tgt0 *)
(* | gsim_astep_tgt *)
(*     tr_src tr_tgt (gst_src0: gstate L1.(state)) (gst_tgt0: gstate L2.(state)) *)
(*     st_src0 S_tgt0 (GSSRC: gst_src0 = inl st_src0) (GSTGT: gst_tgt0 = inr S_tgt0) *)
(*              tr st_tgt1 *)
(*              (ATGT: S_tgt0 tr st_tgt1) *)
(*              (BSIM: _gsim gsim tr_src (add_trace tr tr_tgt) gst_src0 (inl st_tgt1)): *)
(*   _gsim gsim tr_src tr_tgt gst_src0 gst_tgt0 *)
(* . *)

Definition gsim: _ -> _ -> _ -> _ -> _ -> Prop := paco5 _gsim bot5.

(* Lemma _gsim_ind2 *)
(*   forall (r P: _ -> _ -> _ -> _ -> Prop), *)
(*   (forall tr1 tr2 st1 st2,  *)
(*   (P: -> Prop) *)
(*   ( *)

Lemma gsim_mon: monotone5 _gsim.
Proof.
  ii. ginduction IN. i.
  - econs; eauto.
  - econs 2; eauto.
  - econs 3; eauto.
  - econs 4; eauto.
  - i. econs 5; eauto.
  - i. econs 6; eauto.
Qed.

Hint Unfold gsim.
Hint Resolve gsim_mon: paco.
Hint Resolve cpn5_wcompat: paco.

(* Lemma gsim_ind (P: index -> L0.(state) -> L1.(state) -> Prop) *)
(*   (FIN: forall *)
(*       i_src0 i_tgt0 st_src0 st_tgt0 *)
(*             retv *)
(*             (SRT: _.(state_sort) st_src0 = final retv) *)
(*             (SRT: _.(state_sort) st_tgt0 = final retv), *)
(*             P i_src0 i_tgt0 st_src0 st_tgt0) *)
(*         (VIS: forall *)
(*             i_src0 i_tgt0 st_src0 st_tgt0 *)
(*             (SRT: _.(state_sort) st_src0 = vis) *)
(*             (SRT: _.(state_sort) st_tgt0 = vis) *)
(*             (SIM: forall ev st_tgt1 *)
(*                          (STEP: _.(step) st_tgt0 (Some ev) st_tgt1) *)
(*               , *)
(*                 exists st_src1 (STEP: _.(step) st_src0 (Some ev) st_src1), *)
(*                   <<SIM: sim true true st_src1 st_tgt1>>), *)
(*             P i_src0 i_tgt0 st_src0 st_tgt0) *)
(*         (VISSTUCK: forall *)
(*             i_src0 i_tgt0 st_src0 st_tgt0 *)
(*             (SRT: _.(state_sort) st_tgt0 = vis) *)
(*             (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1)), *)
(*             P i_src0 i_tgt0 st_src0 st_tgt0) *)
(*         (DMSRC: forall *)
(*             i_src0 i_tgt0 st_src0 st_tgt0 *)
(*             (SRT: _.(state_sort) st_src0 = demonic) *)
(*             (SIM: exists st_src1 *)
(*                          (STEP: _.(step) st_src0 None st_src1) *)
(*               , *)
(*                 <<SIM: sim true i_tgt0 st_src1 st_tgt0>> /\ <<IH: P true i_tgt0 st_src1 st_tgt0>>), *)
(*             P i_src0 i_tgt0 st_src0 st_tgt0) *)
(*         (DMTGT: forall *)
(*             i_src0 i_tgt0 st_src0 st_tgt0 *)
(*             (SRT: _.(state_sort) st_tgt0 = demonic) *)
(*             (SIM: forall st_tgt1 *)
(*                          (STEP: _.(step) st_tgt0 None st_tgt1) *)
(*               , *)
(*                 <<SIM: sim i_src0 true st_src0 st_tgt1>> /\ <<IH: P i_src0 true st_src0 st_tgt1>>), *)
(*             P i_src0 i_tgt0 st_src0 st_tgt0) *)
(*         (ANSRC: forall *)
(*             i_src0 i_tgt0 st_src0 st_tgt0 *)
(*             (SRT: _.(state_sort) st_src0 = angelic) *)
(*             (SIM: forall st_src1 *)
(*                          (STEP: _.(step) st_src0 None st_src1) *)
(*               , *)
(*                 <<SIM: sim true i_tgt0 st_src1 st_tgt0>> /\ <<IH: P true i_tgt0 st_src1 st_tgt0>>), *)
(*             P i_src0 i_tgt0 st_src0 st_tgt0) *)
(*         (ANTGT: forall *)
(*             i_src0 i_tgt0 st_src0 st_tgt0 *)
(*             (SRT: _.(state_sort) st_tgt0 = angelic) *)
(*             (SIM: exists st_tgt1 *)
(*                          (STEP: _.(step) st_tgt0 None st_tgt1) *)
(*               , *)
(*                 <<SIM: sim i_src0 true st_src0 st_tgt1>> /\ <<IH: P i_src0 true st_src0 st_tgt1>>), *)
(*             P i_src0 i_tgt0 st_src0 st_tgt0) *)
(*         (PROGRESS: *)
(*            forall *)
(*              i_src0 i_tgt0 st_src0 st_tgt0 *)
(*              (SIM: sim false false st_src0 st_tgt0) *)
(*              (SRC: i_src0 = true) *)
(*              (TGT: i_tgt0 = true), *)
(*              P i_src0 i_tgt0 st_src0 st_tgt0) *)
(*     : *)
(*       forall i_src0 i_tgt0 st_src0 st_tgt0 *)
(*              (SIM: sim i_src0 i_tgt0 st_src0 st_tgt0), *)
(*         P i_src0 i_tgt0 st_src0 st_tgt0. *)
(*   Proof. *)
(*     i. eapply (@_sim_ind2 sim P); eauto. *)
(*     { i. eapply DMSRC; eauto. des. esplits; eauto. *)
(*       pfold. eapply sim_mon; eauto. *)
(*     } *)
(*     { i. eapply DMTGT; eauto. i. hexploit SIM0; eauto. i. des. esplits; eauto. *)
(*       pfold. eapply sim_mon; eauto. *)
(*     } *)
(*     { i. eapply ANSRC; eauto. i. hexploit SIM0; eauto. i. des. esplits; eauto. *)
(*       pfold. eapply sim_mon; eauto. *)
(*     } *)
(*     { i. eapply ANTGT; eauto. des. esplits; eauto. *)
(*       pfold. eapply sim_mon; eauto. *)
(*     } *)
(*     { punfold SIM. eapply sim_mon; eauto. i. pclearbot. auto. } *)
(*   Qed. *)

End GENERAL_SIM.

Variant gsim_init_sim (L1 L2: gsemantics) : Prop :=
  | gsim_init_src_ub
      (SRCUB: ~ exists st_src, initial_state L1 st_src)
  | gsim_init
      (TGTEXISTS: exists st_tgt, <<INITTGT: initial_state L2 st_tgt>>)
      (INITSIM: forall st_tgt
                  (INITTGT: initial_state L2 st_tgt),
        exists st_src,
          (<<INITSRC: initial_state L1 st_src>>) /\
          (<<GSIM: gsim L1 L2 false false None (inl st_src) (inl st_tgt)>>)).

(* Variant gsim_init_sim (L1 L2: gsemantics) (* (index: Type) (order: index -> index -> Prop) *): Prop := *)
(* (* | gsim_init_forward *) *)
(* (*     (INITSIM: forall st_init_src *) *)
(* (*         (INITSRC: initial_state L1 st_init_src), *) *)
(* (*         exists st_init_tgt, *) *)
(* (*           (<<INITTGT: initial_state L2 st_init_tgt>>) /\ *) *)
(* (*           (<<GSIM: gsim L1 L2 None None st_init_src st_init_tgt>>)) *) *)
(* | gsim_init_backward *)
(*     (INITEXISTS: forall st_init_src *)
(*         (INITSRC: initial_state L1 st_init_src), *)
(*         exists st_init_tgt, <<INITTGT: initial_state L2 st_init_tgt>>) *)
(*     (INITSIM: forall st_init_src_ *)
(*         (INITSRC: initial_state L1 st_init_src_) *)
(*         st_init_tgt *)
(*         (INITTGT: initial_state L2 st_init_tgt), *)
(*         exists st_init_src, *)
(*           (<<INITSRC: initial_state L1 st_init_src>>) /\ *)
(*           (<<GSIM: gsim L1 L2 None None st_init_src st_init_tgt>>)). *)

Record gsim_properties (L1 L2: gsemantics)(*  (index: Type) *)
                       (* (order: index -> index -> Prop) *): Type := {
    (* gsim_order_wf: <<WF: well_founded order>>; *)
    gsim_initial_states_sim: <<INIT: gsim_init_sim L1 L2>>;
}.

Arguments gsim_properties: clear implicits.

Inductive general_simulation (L1 L2: gsemantics) : Prop :=
  General_simulation(*  (index: Type) *)
                   (* (order: index -> index -> Prop) *)
                   (props: gsim_properties L1 L2).

Arguments General_simulation {L1 L2} props.

Section TOGEN.

Variable state: Type.
Variable genv: Type.

(* Variable L: semantics. *)

Variable intstep: genv -> state -> trace -> state -> Prop.
Variable extstep: genv -> state -> (trace -> state -> Prop) -> Prop.

Variable is_ext: genv -> state -> Prop.
Variable final_state: genv -> state -> option int.

Inductive step_gen (ge: genv) (st1: state) : (trace -> state -> Prop) -> Prop :=
| step_gen_internal_intro
  (NOTFINAL: final_state ge st1 = None)
  (INT: ~ is_ext ge st1)
  :
  step_gen ge st1 (fun t st2 => intstep ge st1 t st2 /\ t = E0)
| step_gen_external_intro
  (S: trace -> state -> Prop)
  (EXT: is_ext ge st1)
  (STEP: extstep ge st1 S)
  :
  step_gen ge st1 S
.

End TOGEN.

Hint Unfold gsim.
Hint Resolve gsim_mon: paco.
Hint Resolve cpn5_wcompat: paco.

