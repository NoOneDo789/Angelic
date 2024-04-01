Require Import Coqlib.
Require Import Maps.
Require Import Maps2.
Require Import AST.
Require Import Op.
Require Import Utils.
Require Import Integers.
Require Import Floats.
Require Import Classical.
Require Import Dom.
Require Import SSA.
Require Import SSAutils.
Require Import Smallstep.
Require Import Globalenvs.
Require Import Values.
Require Import Events.
Require Import SCCPopt.
Require Import ConstpropOp.
Require Import DLib.
Require Import Utilsvalidproof.
Require Import KildallComp.
Require Import Dsd.
Require Import Relations.
Require Import SSAinv.
Require Import OptInv.
Require Import SCCPopt.
Require Import SCCPoptProp.
Require Import Registers.
Require Import Linking.
Unset Allow StrictProp.

(** Correctness proof of the SCCP optimization *)

Section PRESERVATION.

  Definition match_prog (p: SSA.program) (tp: SSA.program) :=
    match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

  Lemma transf_program_match:
    forall p, match_prog p (transf_program p).
  Proof.
    intros; subst.
    eapply match_transform_program_contextual; auto.
  Qed.

  Section CORRECTNESS.
    
    Hint Unfold exec: core.
    
    Variable prog: program.
    Variable tprog: program.
    Hypothesis TRANSL: match_prog prog tprog.
    Hypothesis HWF: wf_ssa_program prog.

    Definition ge := Genv.globalenv prog.
    Definition tge := Genv.globalenv tprog.

    Lemma same_symbols: forall s,
        Genv.find_symbol tge s = Genv.find_symbol ge s.
    Proof.
      eapply Genv.find_symbol_transf; eauto.
    Qed.

    Lemma match_prog_wf_ssa : wf_ssa_program tprog.
    Proof.
      red. intros.
      red in  HWF.
      inv TRANSL.
      intuition. revert H0 H HWF.
      induction 1; intros.
      - inv H.
      - inv H1.      
        + inv H. inv H4.
          destruct f1 ; simpl in * ; try constructor; auto.
          eapply Opt.transf_function_preserve_wf_ssa_function; eauto.
          * eapply new_code_same_or_Iop; eauto.
          * exploit (HWF (Internal f) id); eauto.
            destruct a1, g; simpl in * ; try congruence. 
            left. inv H; simpl in *; auto. 
            intros. inv H4; auto.
        + eapply IHlist_forall2; eauto.
    Qed.

    Lemma funct_ptr_translated:
      forall (b: Values.block) (f: fundef),
        Genv.find_funct_ptr ge b = Some f ->
        Genv.find_funct_ptr tge b = Some (transf_fundef f).
    Proof.
      eapply Genv.find_funct_ptr_transf ; eauto. 
    Qed.

    Lemma functions_translated:
      forall (v: val) (f: fundef),
        Genv.find_funct ge v = Some f ->
        Genv.find_funct tge v = Some (transf_fundef f).
    Proof.
      eapply Genv.find_funct_transf ; eauto.
    Qed.

    Lemma sig_preserved:
      forall f, funsig (transf_fundef f) = funsig f.
    Proof.
      destruct f;  simpl ; try reflexivity.
    Qed.

    Lemma transf_ros_correct:
      forall ros rs f,
        find_function ge ros rs = Some f ->
        find_function tge ros rs = Some (transf_fundef f).
    Proof.
      intros.
      unfold find_function in *.
      destruct ros; simpl.
      exploit functions_translated; eauto.
      flatten; rewrite same_symbols in *;
        rewrite Eq in *; eauto using funct_ptr_translated.
      inv H.
    Qed.

    Lemma same_eval_addressing: forall sp addr rs args,
        eval_addressing tge sp addr rs ## args = eval_addressing ge sp addr rs ## args.
    Proof.
      intros.
      unfold eval_addressing;
        try (unfold eval_addressing32, eval_addressing64);
        unfold Genv.symbol_address.
      flatten; rewrite <- same_symbols in *; eauto; flatten.
    Qed.

    Hint Resolve same_symbols: core.

    Lemma same_eval: forall sp op rs args m,
        eval_operation tge sp op rs ## args m = eval_operation ge sp op rs ## args m.
    Proof.
      intros.
      unfold eval_operation;
        try unfold eval_addressing32, eval_addressing64;
        unfold Genv.symbol_address.
      flatten;
        match goal with
        | id: Genv.find_symbol _ _ = _ |- _ =>
          rewrite same_symbols in id ; try congruence
        end.
    Qed.

    Lemma senv_equiv : Senv.equiv ge tge.
    Proof.
      apply (Genv.senv_transf TRANSL).
    Qed.

    (** * Simulation relation *)
    Inductive match_stackframes : list stackframe -> list stackframe -> Prop :=
    | match_stackframes_nil: match_stackframes nil nil
    | match_stackframes_cons:
        forall res f sp pc rs s st b
               (SP: sp = (Vptr b Ptrofs.zero))
               (STACK: (match_stackframes s st))
               (WFF: wf_ssa_function f)
               (HG:forall v, gamma SCCP f ge sp pc (rs# res <- v))
               (EXE: exec f pc),
          match_stackframes
            ((Stackframe res f sp pc rs) :: s)
            ((Stackframe res (transf_function f) sp pc rs) :: st).

    Variant match_states: SSA.state -> SSA.state -> Prop :=
    | match_states_intro:
        forall s st sp pc rs m f b
               (SP: sp = (Vptr b Ptrofs.zero))
               (SINV:s_inv ge (State s f sp pc rs m))
               (HG:gamma SCCP f ge sp pc rs)
               (EXE: exec f pc)
               (STACK: match_stackframes s st),
          match_states (State s f sp pc rs m) (State st (transf_function f) sp pc rs m)
    | match_states_call:
        forall s st f args m
               (SINV:s_inv ge (Callstate s f args m))
               (STACK: match_stackframes s st),
          match_states (Callstate s f args m) (Callstate st (transf_fundef f) args m)
    | match_states_return:
        forall s st v m
               (SINV:s_inv ge (Returnstate s v m))
               (STACK: match_stackframes s st),
          match_states (Returnstate s v m) (Returnstate st v m).
    
    Hint Resolve sdom_dom_pred fn_code_reached fn_entry_pred
         fn_phicode_inv list_nth_z_in: core.
    Hint Constructors clos_refl_trans SSA.step: core.
    
    Lemma match_stackframes_sfg_inv : forall s st,
        match_stackframes s st ->
        sfg_inv SCCP prog s.
    Proof.
      induction 1 ; go.
    Qed.

    Lemma transf_initial_states:
      forall st1, SSA.initial_state prog st1 ->
                  exists st2, SSA.initial_state tprog st2 /\ match_states st1 st2.
    Proof.
      intros. inversion H.
      exploit @funct_ptr_translated ; eauto. intros. 
      econstructor; split.
      - econstructor.
        assert (MEM: (Genv.init_mem tprog) = Some m0) by (eapply (Genv.init_mem_transf TRANSL); eauto).
        + apply MEM ; auto.
        + replace (prog_main tprog) with (prog_main prog). rewrite same_symbols; eauto.
          symmetry; eapply match_program_main; eauto.
        + eauto.
        + rewrite <- H3. apply sig_preserved; auto.
      - eapply match_states_call  ; eauto.
        + constructor.
          eapply Genv.find_funct_ptr_prop ; eauto.
          constructor.
        + constructor.
    Qed.

    Lemma transf_final_states:
      forall st1 st2 r,
        match_states st1 st2 -> SSA.final_state st1 r -> SSA.final_state st2 r.
    Proof.
      intros. inv H0. inv H. 
      inv STACK.
      constructor.
    Qed.
    
    (** * Soundness invariant of the analysis *)
    Lemma subj_red_gamma : forall prog (WFP: wf_ssa_program prog),
        forall (f f':function) (HWF : wf_ssa_function f)
               t m m' rs rs' sp sp' pc pc' s s',
          gamma SCCP f (Genv.globalenv prog) (Vptr sp Ptrofs.zero) pc rs ->
          sfg_inv SCCP prog s ->
          exec f pc ->
          s_inv (Genv.globalenv prog) (State s f (Vptr sp Ptrofs.zero) pc rs m) ->
          SSA.step (Genv.globalenv prog) (State s f (Vptr sp Ptrofs.zero) pc rs m) t
                       (State s' f' (Vptr sp' Ptrofs.zero) pc' rs' m') ->
          gamma SCCP f' (Genv.globalenv prog) (Vptr sp' Ptrofs.zero) pc' rs'.
    Proof.
      intros. 
      eapply subj_red_gamma; eauto.
      - intros; eapply same_fn_code1; eauto.
      - intros; eapply Iop_correct; eauto.
      - intros; eapply step_phi_aux; eauto.
      - intros; eapply exec_step; eauto.
    Qed. 

    Hint Resolve match_stackframes_sfg_inv
         subj_red subj_red_gamma: core.
    
    Ltac match_go :=
      match goal with
      | id: SSA.step _ _ _ _ |- match_states _ _  =>
        econstructor; eauto ; [eapply SSAinv.subj_red; eauto
                              | eapply subj_red_gamma; eauto
                              | eapply exec_step in id; eauto]
      end.

    Ltac TransfInstr :=
      match goal with
      | f : function,
            id: (fn_code _)! ?pc = Some ?instr |- _ =>
        case_eq (DS.fixpoint f handle_instr (initial f)) ;
        intros lv es FIX;
        set (lv' := fun reg => PMap.get reg lv) in * ;
        try assert ((fn_code (transf_function f)) !pc = Some(transf_instr lv' pc instr))
          by (unfold transf_function, Opt.transf_function, fn_code;
              simpl; rewrite PTree.gmap; try rewrite FIX;
              unfold option_map; destruct f ; simpl in *;
              flatten ; reflexivity);
        simpl transf_instr in *
      end.

    Hint Extern 1 (wf_ssa_function _) => invh s_inv: core.
    
    Lemma transf_step_correct:
      forall s1 t s2,
        SSA.step ge s1 t s2 ->
        SSA.step ge s1 t s2 ->
        forall s1' (MS: match_states s1 s1'),
        exists s2', SSA.step tge s1' t s2' /\ match_states s2 s2'.
    Proof.
      intros s1 t s2.

      induction 1; intros; inv MS; auto.

      (* Inop *)
      - exists (State st (transf_function f) (Vptr b Ptrofs.zero) pc' rs m).
        split; try match_go.
        TransfInstr.
        eapply exec_Inop_njp; eauto.
        intro Hcont.
        erewrite join_point_transf_function in Hcont ; go.
          
      (* Inop phi *)
      - exists (State st (transf_function f) (Vptr b Ptrofs.zero) pc' (phi_store k phib rs) m).
        split; try match_go.
        TransfInstr.
        eapply exec_Inop_jp; eauto.
        erewrite join_point_transf_function; go.
        rewrite make_predecessors_transf_function; auto.
        
      (* Iop *)
      - exists (State st (transf_function f) (Vptr b Ptrofs.zero) pc' rs # res <- v m).
        split; try match_go.        
        TransfInstr.

        assert ((fn_code (transf_function f)) !pc = Some(transf_instr lv' pc (Iop op args res pc'))).
        { unfold transf_function, transf_instr, Opt.transf_function.
          simpl; rewrite PTree.gmap; try rewrite FIX. simpl.
          unfold option_map; unfold transf_instr ; destruct f ; simpl in *; flatten;
            (replace (lv## args) with (map lv' args)
              in Eq1 at 1 by (induction args; go));
            rewrite Eq1 in Eq2 at 1; congruence.
        }
        simpl transf_instr in *.
        flatten H2; try ( eapply exec_Iop; eauto; rewrite same_eval; auto).
        exploit (ValueAOpSSA.eval_static_operation_sound (bctop ge) ge); eauto.
        + constructor.
          * intros. split; intros.
            -- simpl. flatten; try solve [unfold Genv.find_symbol in *;
                                          apply Genv.genv_symb_range in H3  ; intuition].
               ++ apply Genv.find_invert_symbol in H3; congruence.
               ++ apply Genv.find_invert_symbol in H3; congruence.
            -- simpl in H3. flatten H3.
               apply Genv.invert_find_symbol. auto.
          * intros. simpl. flatten.
            -- split; congruence.
            -- split; congruence. 
        + simpl. flatten. 
        + eapply G_list_val_list_match_approx; eauto.
          eapply gamma_v_args; eauto.
        + intros.
          (replace (lv## args) with (map (fun r : reg => lv' r) args)
            in H3 at 1 by (induction args; go)).
          unfold const_for_result in *. flatten Eq; inv H3; auto.  
                                                              
      - exists (State st (transf_function f) (Vptr b Ptrofs.zero) pc' rs # dst <- v m).
        split; try match_go.
        TransfInstr.
        eapply exec_Iload; eauto;
        try (rewrite same_eval_addressing; auto).
        
      - exists (State st (transf_function f) (Vptr b Ptrofs.zero) pc' rs m').
        split; try match_go.
        TransfInstr.
        eapply exec_Istore; eauto;
          try (rewrite same_eval_addressing; auto).

      - exists (Callstate (Stackframe res (transf_function f) (Vptr b Ptrofs.zero) pc' rs::st)
                          (transf_fundef fd) rs ## args m); split.
        + TransfInstr; intros.
      eapply exec_Icall; eauto.
      rewrite transf_ros_correct with (f := fd); eauto.
      unfold funsig, transf_fundef.
      destruct fd; simpl; eauto.

      + econstructor; eauto.
        * eapply SSAinv.subj_red; eauto.
        * econstructor; eauto.
          -- intros v x Hyp1 Hyp2.
             destruct (peq x res).
             ++ subst. exploit (same_fn_code1 f pc); go.
                eapply G_top; eauto.
             ++ rewrite PMap.gso; auto.
                exploit (HG x); eauto.
                destruct dsd_pred_njp with f pc pc' x as
                    [[Dx Dx']|[[Dx [Dx' Dx'']]|[Dx Dx']]]; simplify_dsd; eauto.
                go.
                intro; subst; exploit fn_entry; eauto; intros (succ' & Hscucc); congruence.
                go.
                eelim ssa_not_Inop_not_phi; eauto; go.
          -- eapply exec_step in H2; eauto.

      - exists (Callstate st (transf_fundef fd) rs ## args m'); split; try match_go.
        + TransfInstr; intros.
      eapply exec_Itailcall; eauto.
      rewrite transf_ros_correct with (f := fd); eauto.
      unfold funsig, transf_fundef.
      destruct fd; simpl; eauto; unfold transf_function.

      + econstructor; eauto.
        eapply SSAinv.subj_red; eauto.

      - exists (State st (transf_function f) (Vptr b Ptrofs.zero) pc' (regmap_setres res vres rs) m').
        split; try match_go.
        TransfInstr.
        eapply exec_Ibuiltin with (vargs:= vargs); eauto.
        eapply eval_builtin_args_preserved; eauto.
        eapply external_call_symbols_preserved; eauto.
        apply senv_equiv.
        
      - exists (State st (transf_function f) (Vptr b Ptrofs.zero) ifso rs m).
        split; try match_go.
        TransfInstr. eapply exec_Icond_true; eauto.
        
      - exists (State st (transf_function f) (Vptr b Ptrofs.zero) ifnot rs m).
        split; try match_go.
        TransfInstr. eapply exec_Icond_false; eauto.

      - exists (State st (transf_function f) (Vptr b Ptrofs.zero) pc' rs m).
        split; try match_go.
        TransfInstr. eapply exec_Ijumptable; eauto.

      - exists (Returnstate st (regmap_optget or Vundef rs) m'); split; try match_go.
        + TransfInstr.
          econstructor; eauto.

        + econstructor; eauto.
          eapply SSAinv.subj_red; eauto.

      - exists (State st (transf_function f) (Vptr stk Ptrofs.zero)
                      (fn_entrypoint (transf_function f))
                      (init_regs args (fn_params (transf_function f))) m');
          split; try match_go.
        + econstructor; eauto.
        + replace (fn_entrypoint (transf_function f)) with (fn_entrypoint f);
            [|compute; reflexivity].
          replace (fn_params (transf_function f)) with (fn_params f);
            [|compute; reflexivity].
          econstructor; eauto.
          * eapply SSAinv.subj_red; eauto.
          * eapply gamma_entry; eauto.
            invh s_inv. invh wf_ssa_fundef; auto.
          * go.
          
      - exists (Returnstate st res m'); split.
        + econstructor; eauto.
          eapply external_call_symbols_preserved; eauto.
          apply senv_equiv.
        + econstructor; eauto.
          eapply SSAinv.subj_red; eauto.

      - inv STACK.
        exists (State st0 (transf_function f) (Vptr b Ptrofs.zero) pc rs # res <- vres m); split; go.
        econstructor; eauto.
        eapply SSAinv.subj_red; eauto.
    Qed.
    
    Theorem transf_program_correct:
      forward_simulation (SSA.semantics prog) (SSA.semantics tprog).
    Proof.
      eapply forward_simulation_step.
      eapply senv_equiv.
      eexact transf_initial_states.
      eexact transf_final_states.
      intros; eapply transf_step_correct; eauto.
    Qed.

  End CORRECTNESS.
        
End PRESERVATION.
