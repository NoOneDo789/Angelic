(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Whole-program behaviors *)

(* Require Import Classical. *)
(* Require Import ClassicalEpsilon. *)
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Simulation.
Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Relations.Relation_Operators.

Set Implicit Arguments.
Set Asymmetric Patterns.


(* Trace & Behavior from CCR *)

Module Beh.

  (* reacts: Trace without basecase *)
  CoInductive t: Type :=
  | oom
  | done (retv: int)
  | spin
  (* | ub *)
  | cons (hd: event) (tl: t)
  .

  Infix "##" := cons (at level 60, right associativity).

  Fixpoint app (pre: list event) (bh: t): t :=
    match pre with
    | [] => bh
    | hd :: tl => cons hd (app tl bh)
    end
  .
  Lemma fold_app
        s pre tl
    :
      (cons s (app pre tl)) = app (s :: pre) tl
  .
  Proof. reflexivity. Qed.

  Definition prefix (pre: list event) (bh: t): Prop :=
    exists tl, <<APP: app pre tl = bh>>
  .
  (* | done (retv: int) *)
  (* | spin *)
  (* | ub *)
  (* | oom *)
  (* | cons (hd: event) (tl: t) *)

  Inductive beh_spin : t -> Prop :=
  (* | beh_spin_done retv: beh_spin (done retv) *)
  | beh_spin_spin : beh_spin spin
  (* | beh_spin_ub : beh_spin beh_ub *)
  (* | beh_spin_oom : beh_spin beh_oom *)
  | beh_spin_cons hd tl (SPIN: beh_spin tl) : beh_spin (cons hd tl).

  Variant _beh_nospin (beh_nospin: t -> Prop) : t -> Prop :=
  | beh_nospin_done retv: _beh_nospin beh_nospin (done retv)
  (* | beh_nospin_ub : _beh_nospin beh_nospin ub *)
  | beh_nospin_oom : _beh_nospin beh_nospin oom
  | beh_nospin_cons hd tl (SPIN: beh_nospin tl) : _beh_nospin beh_nospin (cons hd tl).

  Definition beh_nospin: _ -> Prop := paco1 _beh_nospin bot1.

  Lemma beh_nospin_mon: monotone1 _beh_nospin.
  Proof. ii. inv IN; try (by econs; eauto). Qed.

  Hint Constructors _beh_nospin.
  Hint Unfold beh_nospin.
  Hint Resolve beh_nospin_mon: paco.

End Beh.

Module BSem.

Definition t: Type := Beh.t -> Prop.
Definition improves (src tgt: t): Prop := tgt <1= src.

Section BEHAVES.

Variable L: gsemantics.

Variant _state_div (state_div: gstate L.(state) -> Prop) :
  gstate L.(state) -> Prop :=
| state_div_left
    st0 S0
    (DSTEP: GStep L st0 S0)
    (DIV: state_div (inr S0)) :
  _state_div state_div (inl st0)
| state_div_right
    (S0: trace -> L.(state) -> Prop)
    (DIV: forall tr st1 (ASTEP: S0 tr st1), <<TR: tr = E0>> /\ <<TL: state_div (inl st1)>>)
  :
  _state_div state_div (inr S0)
.

Definition state_div: _ -> Prop := paco1 _state_div bot1.

(* Inductive _state_div (state_div: L.(state) -> Prop) *)
(*   (st0: L.(state)): Prop := *)
(* | state_div_nd *)
(*     (STEP: exists S0 (DSTEP: GStep L st0 S0), *)
(*              forall tr st1 (ASTEP: S0 tr st1), <<TR: tr = E0>> /\ <<TL: state_div st1>>) *)
(* . *)

(* Definition state_div: _ -> Prop := paco1 _state_div bot1. *)

Lemma state_div_mon: monotone1 _state_div.
Proof.
  ii. ginduction IN.
  - i. econs; eauto.
  - i. econs 2; eauto. i. exploit DIV; eauto. i. des. esplits; eauto.
Qed.

Hint Constructors _state_div.
Hint Unfold state_div.
Hint Resolve state_div_mon: paco.

(* Variant of_astate (of_state1 of_state2: L.(state) -> Beh.t -> Prop) (S0: trace -> L.(state) -> Prop) (evs: Beh.t) : Prop := *)
(* | sb_astep *)
(*     (OFST1: forall es1 st1 (ASTEP: S0 es1 st1), (es1 = E0 -> of_state1 st1 evs)) *)
(*     (OFST2: forall es1 st1 (ASTEP: S0 es1 st1), (es1 <> E0 -> exists es1', (of_state2 st1 es1' /\ (Beh.app es1 es1' = evs)))) *)
(* . *)
            
Inductive _of_state (of_state: gstate L.(state) -> Beh.t -> Prop): gstate L.(state) -> Beh.t -> Prop :=
| sb_oom (__CASE__ := "OfState OOM")
    st0
  :
    _of_state of_state (inl st0) (Beh.oom)
| sb_done (__CASE__ := "OfState Done")
    st0 retv
    (FINAL: final_state L st0 = Some retv)
  :
    _of_state of_state (inl st0) (Beh.done retv)
| sb_spin (__CASE__ := "OfState Spin")
    st0
    (DIVERGES: state_div (inl st0))
  :
    _of_state of_state (inl st0) (Beh.spin)
| sb_dstep (__CASE__ := "OfState Dstep")
    st0 S0 evs
    (DSTEP: GStep L st0 S0)
    (OFST: _of_state of_state (inr S0) evs)
  :
    _of_state of_state (inl st0) evs
| sb_astep (__CASE__ := "OfState Astep")
    (S0: trace -> L.(state) -> Prop) evs
    (OFST1: forall es1 st1 (ASTEP: S0 es1 st1), es1 = E0 -> _of_state of_state (inl st1) evs)
    (OFST2: forall es1 st1 (ASTEP: S0 es1 st1), es1 <> E0 -> exists es1', of_state (inl st1) es1' /\ Beh.app es1 es1' = evs)
  :
    _of_state of_state (inr S0) evs
.

Definition of_state: _ -> _ -> Prop := paco2 _of_state bot2.

(* Theorem of_state_ind : *)
(* forall (r P: _ -> _ -> Prop), *)
(* (forall st0 retv, final_state L st0 retv -> P st0 (Beh.done retv)) -> *)
(* (forall st0, state_div (inl st0) -> P st0 Beh.spin) -> *)
(* (forall st0, P st0 Beh.oom) -> *)
(* (forall st0 evs *)
(*    (STEP: exists S0 (DSTEP: GStep L st0 S0), *)
(*           forall es1 st1 (ASTEP: S0 es1 st1), *)
(*           (es1 = E0 -> <<TL: _of_state r st1 evs>> /\ <<IH: P st1 evs>>) /\ *)
(*           (es1 <> E0 -> exists es1', <<TL: r st1 es1'>> /\ <<EVS: Beh.app es1 es1' = evs>>) *)
(*    ) *)
(*   , *)
(*     P st0 evs) -> *)
(* forall s t, _of_state r s t -> P s t. *)
(* Proof. *)
(*   fix IH 9. i. *)
(*   inv H3; eauto. des. *)
(*   eapply H2. esplits; eauto. ii. hexploit STEP; eauto. i. des. esplits; [|auto]. *)
(*   i. hexploit H3; auto. i. des. subst. esplits; eauto. *)
(*   eapply IH; eauto. *)
(* Qed. *)

Lemma of_state_mon: monotone2 _of_state.
Proof.
  ii. ginduction IN.
  - econs 1; eauto.
  - econs 2; eauto.
  - econs 3; eauto.
  - econs 4; eauto.
  - econs 5; eauto. i. exploit OFST2; eauto. i. des.
    esplits; eauto.
Qed.

Hint Constructors _of_state.
Hint Unfold of_state.
Hint Resolve of_state_mon: paco.

Lemma _of_state_ind_gen: forall (of_state P : gstate L.(state) -> Beh.t -> Prop)
    (COOM : let __CASE__ := "OfState OOM" in forall (st0 : state L), P (inl st0) Beh.oom)
    (CDONE: let __CASE__ := "OfState Done" in forall (st0 : state L) (retv : int), final_state L st0 = Some retv -> P (inl st0) (Beh.done retv))
    (CSPIN: let __CASE__ := "OfState Spin" in forall st0 : state L, state_div (inl st0) -> P (inl st0) Beh.spin)
    (CSTEP: let __CASE__ := "OfState Step" in forall (st0 : state L) (S0 : trace -> state L -> Prop) (evs : Beh.t)
              (DSTEP: GStep L st0 S0)
              (IH: forall (es1 : trace) (st1 : state L), S0 es1 st1 -> es1 = E0 -> P (inl st1) evs)
              (OFST1: forall (es1 : trace) (st1 : state L), S0 es1 st1 -> es1 = E0 -> _of_state of_state (inl st1) evs)
              (OFST2: forall (es1 : trace) (st1 : state L),
                        S0 es1 st1 -> es1 <> E0 -> exists es1' : Beh.t, of_state (inl st1) es1' /\ Beh.app es1 es1' = evs),
                      P (inl st0) evs),
  forall (s : state L) (t : Beh.t), _of_state of_state (inl s) t -> P (inl s) t.
Proof.
  intros. remember (inl s) as gs0 in H. revert_until CSTEP.
  fix self 5; i.
  destruct H eqn: Hcase; inversion Heqgs0; subst.
  - apply COOM.
  - apply CDONE. assumption.
  - apply CSPIN. assumption.
  - eapply CSTEP; try eassumption; i; inversion _o; subst.
    + eapply self; try reflexivity.
      hexploit OFST1; i; try eassumption; try reflexivity.
    + hexploit OFST1; i; try eassumption; try reflexivity.
    + hexploit OFST2; i; try eassumption; try reflexivity.
Qed.

Lemma spin_to_div 
  gst0
  (BEH: of_state gst0 Beh.spin) :
  <<BEH: (state_div gst0)>>.
Proof.
  i. punfold BEH.
  remember (Beh.spin) as beh.
  revert_until gst0. revert gst0.
  induction 2; i; clarify.
  - r. pfold. econs; eauto. left.
    eapply IHBEH; eauto.
  - r. pfold. econs; eauto. i.
    destruct tr eqn:TR.
    + esplits; eauto with paco. left.
      eapply H; eauto.
    + exfalso. exploit OFST2; eauto; ss. i. des.
      inv H1.
Qed.

Lemma div_to_spin
  gst0
  (BEH: state_div gst0) :
  <<BEH: of_state gst0 Beh.spin>>.
Proof.
  pfold. destruct gst0; ss.
  { eapply sb_spin; eauto. }
  eapply sb_astep.
  - i. subst. 
    punfold BEH. inv BEH. ss. exploit DIV; eauto. i. des.
    pclearbot. eauto.
  - i. punfold BEH. inv BEH. ss. exploit DIV; eauto. i. des.
    subst; clarify.
Qed.

Inductive of_program: Beh.t -> Prop :=
  | program_runs: forall s beh,
      initial_state L s -> of_state (inl s) beh ->
      of_program beh
  | program_goes_initially_wrong beh:
      (forall s, ~initial_state L s) ->
      of_program beh
.

(**********************************************************)
(*********************** properties ***********************)
(**********************************************************)

Lemma oom_bottom
      st0
  :
    <<OOM: of_state (inl st0) Beh.oom>>
.
Proof. eauto with paco. Qed.

(* Lemma ub_top *)
(*       st0 *)
(*       (UB: of_state st0 Beh.ub) *)
(*   : *)
(*     forall beh, of_state st0 beh *)
(* . *)
(* Proof. *)
(*   revert_until L. pfold. i. punfold UB. *)
(*   remember Beh.ub as tmp. revert Heqtmp. *)
(*   induction UB using of_state_ind; ii; ss; clarify. *)
(*   des. econs; eauto. esplits; eauto. ii. exploit STEP; eauto. ii. des. *)
(*   split. *)
(*   - ii. exploit H; eauto. i. des. clarify. exploit IH; eauto. *)
(*   - ii. exploit H0; eauto. i. des. destruct es1; ss. *)
(* Qed. *)

(* Lemma GStep_behav *)
(*   (STEP: GStep L s S) *)
(*   (BEH: of_state s beh) *)

End BEHAVES.

End BSem.
Hint Constructors BSem._state_div.
Hint Unfold BSem.state_div.
Hint Resolve BSem.state_div_mon: paco.

Hint Constructors BSem._of_state.
Hint Unfold BSem.of_state.
Hint Resolve BSem.of_state_mon: paco.

Hint Unfold BSem.improves.
Hint Constructors BSem._state_div.
Hint Unfold BSem.state_div.
Hint Resolve BSem.state_div_mon: paco.
Hint Constructors BSem._of_state.
Hint Unfold BSem.of_state.
Hint Resolve BSem.of_state_mon: paco.


