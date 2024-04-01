(** Correctness proof for the RTL normalization phase. *)
Require Import DLib. 
Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import Smallstep.
Require Import RTL.
Require Import RTLnorm.
Require Import RTLnormspec.
Require Import Kildall.
Require Import Conventions.
Require Import Utils.
Require Import Events.
Require Import Linking.
Unset Allow StrictProp.

Section PRESERVATION.

  Definition match_prog (p tp: RTL.program) :=
  match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

  Lemma transf_program_match:
    forall p tp, transl_program p = Errors.OK tp -> match_prog p tp.
  Proof.
    intros. apply match_transform_partial_program; auto.
  Qed.

  Section CORRECTNESS.
    
    Variable prog: RTL.program.
    Variable tprog: RTL.program.
    Hypothesis TRANSF_PROG: match_prog prog tprog.

    Let ge := Genv.globalenv prog.
    Let tge := Genv.globalenv tprog.
  
    Lemma symbols_preserved:
      forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
    Proof.
      eapply Genv.find_symbol_transf_partial; eauto.
    Qed.

    Lemma functions_translated:
      forall (v: val) (f: RTL.fundef),
        Genv.find_funct ge v = Some f ->
        exists tf, Genv.find_funct tge v = Some tf /\ transl_fundef f = Errors.OK tf.
    Proof.
      eapply Genv.find_funct_transf_partial; eauto.
    Qed.

    Lemma function_ptr_translated:
      forall (b: block) (f: RTL.fundef),
        Genv.find_funct_ptr ge b = Some f ->
        exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = Errors.OK tf.
    Proof.
      eapply Genv.find_funct_ptr_transf_partial ; eauto.
    Qed.

    Lemma senv_preserved:
      Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
    Proof.
      eapply Genv.senv_transf_partial; eauto.
    Qed.

    Lemma sig_fundef_translated:
      forall f tf,
        transl_fundef f = Errors.OK tf ->
        funsig tf = RTL.funsig f.
    Proof.
      intros f tf. intros.
      destruct f ; simpl in *. Errors.monadInv H.
      unfold transl_function in EQ;
        flatten EQ; boolInv; go.
      inv H. auto.
    Qed.

    Lemma sig_function_translated:
      forall f tf,
        transl_function f = Errors.OK tf ->
        fn_sig tf = RTL.fn_sig f.
    Proof.
      intros f tf. destruct f; simpl; intros EQ.
      unfold transl_function in EQ;
        flatten EQ; boolInv; go.
    Qed. 

    Lemma spec_ros_r_find_function:
      forall rs f r,
        RTL.find_function ge (inl _ r) rs = Some f ->
        exists tf,
          RTL.find_function tge (inl _ r) rs = Some tf
          /\ transl_fundef f = Errors.OK tf.
    Proof.
      intros.
      eapply functions_translated; eauto.
    Qed.

    Lemma spec_ros_id_find_function:
      forall rs f id,
        RTL.find_function ge (inr _ id) rs = Some f ->
        exists tf,
          RTL.find_function tge (inr _ id) rs = Some tf
          /\ transl_fundef f = Errors.OK tf.
    Proof.
      intros.
      simpl in *. 
      case_eq (Genv.find_symbol ge id) ; intros.
      rewrite H0 in H.
      rewrite symbols_preserved in * ; eauto ; rewrite H0 in *.
      exploit function_ptr_translated; eauto.
      rewrite H0 in H ; inv H.
    Qed.

    Lemma stacksize_preserved: forall f tf, 
        transl_function f = Errors.OK tf -> 
        fn_stacksize f = fn_stacksize tf.
    Proof.
      intros f tf EQ.
      unfold transl_function in EQ;
        flatten EQ; boolInv; go.
    Qed.

    Inductive match_stackframes : list stackframe -> list stackframe -> Prop :=
    | match_stackframes_nil: match_stackframes nil nil 
    | match_stackframes_cons1: 
        forall res f sp pc rs s tf ts 
               (STACK : (match_stackframes s ts))
               (SPEC: (transl_function f = Errors.OK tf)),
          match_stackframes
            ((Stackframe res f sp pc rs) :: s)
            ((Stackframe res tf sp pc rs) :: ts)
    | match_stackframes_cons2: 
        forall res f sp pc pc' rs s tf ts aux
               (STACK : (match_stackframes s ts))
               (SPEC: (transl_function f = Errors.OK tf))
               (NORM: reach_nops (fn_code tf) pc' pc aux),
          match_stackframes
            ((Stackframe res f sp pc rs) :: s)
            ((Stackframe res tf sp pc' rs) :: ts).

    Hint Constructors match_stackframes: core.
    Set Implicit Arguments.

    Variant match_states: RTL.state -> RTL.state -> Prop :=
    | match_states_intro:
        forall s ts sp pc rs m f tf
               (SPEC: transl_function f = Errors.OK tf)
               (STACK: match_stackframes s ts),
          match_states (State s f sp pc rs m) (State ts tf sp pc rs m)
    | match_states_call:
        forall s ts f tf args m
               (SPEC: transl_fundef f = Errors.OK tf)
               (STACK: match_stackframes s ts),
          match_states (Callstate s f args m) (Callstate ts tf args m)
    | match_states_return:
        forall s ts v m 
               (STACK: match_stackframes s ts),
          match_states (Returnstate s v m) (Returnstate ts v m).
    Hint Constructors match_states: core.
    
    Lemma transf_initial_states:
      forall st1, RTL.initial_state prog st1 ->
                  exists st2, RTL.initial_state tprog st2 /\ match_states st1 st2.
    Proof.
      intros. inversion H.
      exploit function_ptr_translated ; eauto. intros [tf [Hfind Htrans]].
      econstructor; split.
      - econstructor.
        assert (MEM: (Genv.init_mem tprog) = Some m0) by (eapply (Genv.init_mem_transf_partial TRANSF_PROG); eauto).
        + apply MEM ; auto.
        + replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
          symmetry; eapply match_program_main; eauto.
        + eauto.
        + rewrite <- H3. apply sig_fundef_translated; auto.
      - eapply match_states_call  ; eauto.
    Qed.

    Lemma transf_final_states:
      forall st1 st2 r,
        match_states st1 st2 -> RTL.final_state st1 r -> RTL.final_state st2 r.
    Proof.
      intros. inv H0. inv H. 
      inv STACK.
      constructor.
    Qed.

    Create HintDb valagree.
    Hint Resolve symbols_preserved : valagree.
    Hint Resolve eval_addressing_preserved : valagree.
    Hint Resolve eval_operation_preserved : valagree.
    Hint Resolve sig_function_translated : valagree.
    Hint Resolve sig_fundef_translated : valagree.
    Hint Resolve senv_preserved : valagree.
    Hint Resolve stacksize_preserved: valagree.

    Lemma reach_nop_star :  forall ts pt regs m aux x pcx pc,
        reach_nops (fn_code x) pcx pc aux ->
        star step tge (RTL.State ts x pt pcx regs m) E0 (RTL.State ts x pt pc regs m).
    Proof.
      induction aux; intros.
      - inv H.  eapply star_step ; eauto ; go. 
      - inv H.
        exploit IHaux ; eauto; go.
    Qed.  

    Ltac allinv := 
      repeat 
        match goal with 
        | [H: value ?s = Some ?s' |- _ ] => inv H
        | [ H1:   (fn_code ?tf) ! ?pc = Some _  ,
                  H2: (fn_code ?tf) ! ?pc = Some _ |- _ ] =>
          rewrite H1 in H2; inv H2
        | [ H1:   (RTL.fn_code ?tf) ! ?pc = Some _  ,
                  H2: (RTL.fn_code ?tf) ! ?pc = Some _ |- _ ] =>
          rewrite H1 in H2; inv H2
        | _ => idtac
        end.

    Variant ch_succ : instruction -> instruction -> Prop :=
    |cs_inop : forall s1 s2, ch_succ (Inop s1) (Inop s2)
    |cs_iop: forall s1 s2 op args dst, ch_succ (Iop op args dst s1) (Iop op args dst s2)
    |cs_iload: forall s1 s2 chunk addr args dst, ch_succ (Iload chunk addr args dst s1) (Iload chunk addr args dst s2)
    |cs_istore: forall s1 s2 chunk addr args src, ch_succ (Istore chunk addr args src s1) (Istore chunk addr args src s2)
    |cs_icall: forall s1 s2 sig fn args dst, ch_succ (Icall sig fn args dst s1) (Icall sig fn args dst s2)
    |cs_itailcall: forall sig fn args, ch_succ (Itailcall sig fn args) (Itailcall sig fn args)
    |cs_ibuiltin : forall s1 s2 ef args dst, ch_succ (Ibuiltin ef args dst s1) (Ibuiltin ef args dst s2)
    |cs_icond : forall cond args i1 i2 n1 n2, ch_succ (Icond cond args i1 n1) (Icond cond args i2 n2)
    |cs_ijump: forall arg tbl1 tbl2, List.length tbl1 = List.length tbl2 -> ch_succ (Ijumptable arg tbl1) (Ijumptable arg tbl2)
    |cs_iret : forall ret, ch_succ (Ireturn ret) (Ireturn ret).

    Lemma ch_succ_dec_spec : forall i1 i2, 
        ch_succ_dec i1 i2 = true -> ch_succ i1 i2.
    Proof.
      destruct i1, i2 ; simpl ; 
        intros; try boolInv ; go.
    Qed.

Ltac normalized := 
  match goal with 
    | id: context[norm _ _ _ ] |- _ =>
    (exploit id ; eauto; intros);
    (invh norm; allinv); 
    (exploit ch_succ_dec_spec ; eauto ; intros ; invh ch_succ)
  end.

Ltac succ n s := 
  match goal with 
    | id : forall (k : nat) (succ succ' : node), _ |- _ =>
       specialize (id n); simpl in *;
       exploit id; eauto; intros [HC1 | [nops HC2]]; subst;
       exists s ; (split ; go ; (econstructor ; eauto using reach_nop_star ; go))
  end.

Lemma transl_step_correct:
  forall s1 t s2,
    step ge s1 t s2 ->
    forall s1' (MS: match_states s1 s1'),
      exists s2', plus step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS; auto; 
  match goal with 
    | [H : transl_fundef (Internal ?f) = _ |- _ ] => idtac
    | [H : transl_fundef (External ?f) = _ |- _ ] => idtac
    | [  |- context [Returnstate ?ts ?vres ?m]] => idtac
    | _ => 
      ( (exploit transl_function_spec_ok ; eauto; intros))
  end ;
  match goal with 
    | [SPEC: transl_function_spec ?f ?tf |- _ ] => inv SPEC
    | _ => idtac
  end.
  
  - (* inop *)
    normalized.
    succ O (RTL.State ts tf sp pc' rs m). 

  - (* iop *)
    normalized. 
    succ O (RTL.State ts tf sp pc' (rs#res <- v) m).
    + econstructor 2 ; eauto.
      rewrite <- H0 ; eauto with valagree. 
    + auto. 
    + econstructor 2 ; eauto.
      rewrite <- H0 ; eauto with valagree. 
    + auto. 
  
  - (* iload *)
    normalized. 
    succ O (RTL.State ts tf sp pc' (rs#dst <- v) m);
      first [econstructor 3; eauto;
             rewrite <- H0 ; eauto with valagree
            |auto
            |econstructor 3 ; eauto;
             rewrite <- H0 ; eauto with valagree
            | auto].
    
  - (* istore *)
    normalized. 
    succ O (RTL.State ts tf sp pc' rs m');
    first [ econstructor 4 ; eauto;
            rewrite <- H0 ; eauto with valagree
          | auto
          | econstructor 4 ; eauto;
            rewrite <- H0 ; eauto with valagree
          | auto].
  
  - (* icall *)
    normalized.
    destruct ros; 
      [ exploit spec_ros_r_find_function ; eauto 
      | exploit spec_ros_id_find_function ; eauto] ; 
      (intros [tf' [Hfind OKtf']]).
    + specialize (H5 O) ; simpl in *.
      exploit H5 ; eauto ; intros [HC1 | [aux' HC2]]; subst.
      * exists (Callstate (Stackframe res tf sp pc' rs :: ts) tf' rs ## args m); split;
        [   (eapply plus_one ; eauto);
          (eapply exec_Icall  ; eauto); 
          (eauto with valagree)
          |
          (constructor ; auto);
            (econstructor ; eauto);
            (replace (fn_sig tf) with (fn_sig f); eauto); 
            (symmetry ; eauto with valagree)].
      * exists (Callstate (Stackframe res tf sp s2 rs :: ts) tf' rs ## args m); split.
        { (eapply plus_one ; eauto);
          (eapply exec_Icall  ; eauto); 
          (eauto with valagree). }
        { (constructor ; auto);
          (econstructor ; eauto);
          (replace (fn_sig tf) with (fn_sig f); eauto); 
          (symmetry ; eauto with valagree). } 

    + specialize (H5 O) ; simpl in *.
      exploit H5 ; eauto ; intros [HC1 | [aux' HC2]]; subst.
      * exists (Callstate (Stackframe res tf sp pc' rs :: ts) tf' rs ## args m); split;
        [   (eapply plus_one ; eauto);
          (eapply exec_Icall  ; eauto); 
          (eauto with valagree)
          |
          (constructor ; auto);
            (econstructor ; eauto);
            (replace (fn_sig tf) with (fn_sig f); eauto); 
            (symmetry ; eauto with valagree)]. 
      * exists (Callstate (Stackframe res tf sp s2 rs :: ts) tf' rs ## args m); split.
        { (eapply plus_one ; eauto);
          (eapply exec_Icall  ; eauto); 
          (eauto with valagree). }
        { (constructor ; auto);
          (econstructor ; eauto);
          (replace (fn_sig tf) with (fn_sig f); eauto); 
          (symmetry ; eauto with valagree). 
        }

  - (* itailcall *)
    normalized. 
    destruct ros;
    [exploit spec_ros_r_find_function ; eauto
      | exploit spec_ros_id_find_function ; eauto];
    (intros EQ; destruct EQ as [tf' [Hfind OKtf']]);
    (exploit (sig_function_translated f tf) ; eauto ; intros);
    
    ((exists (Callstate ts tf' rs##args m');  split);
      [  (eapply plus_one ; eauto); 
        (eapply exec_Itailcall ; eauto with valagree);
        (replace (fn_stacksize tf) with (fn_stacksize f); eauto with valagree)
        | ( (constructor; auto);
          (eapply match_stackframes_change_sig ;eauto with valagree))]);
    eapply tailcall_ok ; eauto.
    
  - (* ibuiltin *)
    normalized.
    succ O (RTL.State ts tf sp pc' (regmap_setres res vres rs) m').
    + econstructor; eauto.
      eapply eval_builtin_args_preserved with (ge1:= ge); eauto with valagree.
      eapply external_call_symbols_preserved; eauto with valagree.
    + rewrite E0_right; eauto. 
    + econstructor; eauto.
      eapply eval_builtin_args_preserved with (ge1:= ge); eauto with valagree.
      eapply external_call_symbols_preserved; eauto with valagree.
    + rewrite E0_right; eauto. 
    
  - (* ifso *)
    destruct b.
    + normalized.
      succ O (RTL.State ts tf sp ifso rs m).
    + normalized.
      succ (S 0) (RTL.State ts tf sp ifnot rs m).

  - (* ijump *)
    normalized. 
    exploit @list_nth_z_nth_error ; eauto; intros.  
    exploit @nth_error_some_same_length; eauto ; intros [e Hnth].
    (specialize (H6 (Z.to_nat (Int.unsigned n))); simpl in *).
    exploit H6; eauto; intros [HC1 | [nops HC2]]; subst.
    + exists (RTL.State ts tf sp pc' rs m); split ; eauto. 
      econstructor; eauto. 
      eapply exec_Ijumptable ; eauto.
      exploit @nth_error_list_nth_z ; eauto.
      eapply @list_nth_z_ge0 ; eauto.
      go. 
      auto. 
    + exists (RTL.State ts tf sp pc' rs m); split ; eauto. 
      econstructor; eauto. 
      eapply exec_Ijumptable ; eauto.
      exploit @nth_error_list_nth_z ; eauto.
      eapply @list_nth_z_ge0 ; eauto.
      eauto using reach_nop_star. 
      auto. 
  
  - (* ireturn *)
    (exploit transl_function_spec_ok ; eauto; intros SPEC').
    inv SPEC'.
    assert (Hpc := NORM pc). 
    exploit Hpc ; eauto ; intros Hnorm. 
    inv Hnorm; allinv; try congruence. 
    exploit ch_succ_dec_spec; eauto ; intros ; invh ch_succ.
    exists (Returnstate ts (regmap_optget or Vundef rs) m'); split ; eauto. 
    eapply plus_one ; eauto.
    eapply exec_Ireturn ; eauto.
    rewrite <- H0 ; eauto with valagree.
    rewrite stacksize_preserved with f tf ; eauto.

  - (* internal *)
    simpl in SPEC. Errors.monadInv SPEC.
    exists (RTL.State ts x (Vptr stk Ptrofs.zero) (fn_entrypoint f)
                          (init_regs args x.(fn_params))
                          m').
    split.
    + exploit transl_function_spec_ok; eauto. intros SPEC.
      inv SPEC.
      eapply plus_left with (s2:=(RTL.State ts x (Vptr stk Ptrofs.zero) (fn_entrypoint x) 
                                            (init_regs args (fn_params x)) m')) ; eauto. 
      eapply exec_function_internal; eauto.
      rewrite stacksize_preserved with f x in H ; auto.
      eapply reach_nop_star ; eauto.
      auto.
    + replace (RTL.fn_params f) with (fn_params x).
      econstructor ; eauto.
      unfold transl_function in EQ.
      flatten EQ; try congruence.
      auto.

  - (* external *)
    inv SPEC.
    exists (Returnstate ts res m'). split. 
    eapply plus_one ; eauto.
    eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto with valagree.
    econstructor ; eauto.
  
  - (* return state *)
    inv STACK. 
    exists (RTL.State ts0 tf sp pc (rs# res <- vres) m).
    split. eapply plus_one ; eauto. constructor ; eauto.
    constructor ; auto.
    
    exists (RTL.State ts0 tf sp pc (rs# res <- vres) m).
    split. 
    eapply plus_left with 
    (s2:= (RTL.State ts0 tf sp pc' (rs# res <- vres) m) )  ; eauto. 
    constructor ; eauto.
    eapply reach_nop_star; eauto. 
    auto. 
    constructor ; auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  eapply senv_preserved. 
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transl_step_correct. 
Qed.

     End CORRECTNESS.
     
End PRESERVATION.
