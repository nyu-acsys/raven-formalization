From stdpp Require Export binders strings.
From stdpp Require Import countable.
From stdpp Require Export namespaces.
From stdpp Require Import gmap list sets.

From iris Require Import options.
From iris.algebra Require Import ofe cmra agree auth gset gmap.
From iris.bi Require Import derived_laws.
From iris.bi.lib Require Import fixpoint_mono.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import ghost_map.
From iris.base_logic.lib Require Import invariants.

From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.

From raven_iris.simp_raven_lang Require Import lang lifting ghost_state.
From raven_iris.rich_raven_lang Require Import rrl_lang.
From raven_iris.rich_raven_lang Require Import trnsl.
Require Import Coq.Logic.FunctionalExtensionality.

Set Default Proof Using "All".

Section MainSoundness.
    Context {I : Type}.
    Context (Gs : I → cmra).
    Context {Σ : gFunctors}.
    Context `{!inGs Σ Gs}.
    Context `{!inG Σ (authR (gmap.gmapUR heap_addr (agreeR gnameO)))}.
    Context `{!simpLangG Σ}.
    Context {RProg : Program}.
    Context {G : GhostConfig}.
    Context {Γ : Γ_type Gs}.
    Context `{!invTokenG Σ}.

    Local Notation proc_set := (RProg.(prog_proc_set)).
    Local Notation pred_set := (RProg.(prog_pred_set)).
    Local Notation inv_set := (RProg.(prog_inv_set)).
    Local Notation fld_set := (RProg.(prog_fld_set)).
    Local Notation proc_map := (RProg.(prog_proc_map)).
    Local Notation inv_map := (RProg.(prog_inv_map)).
    Local Notation pred_map := (RProg.(prog_pred_map)).
    Local Notation ghost_heap_name := (G.(gc_ghost_heap_name)).
    Local Notation ghost_heap_namespace := (G.(gc_ghost_heap_namespace)).
    Local Notation inv_namespace_map := (G.(gc_inv_namespace_map)).
    Local Notation ProgramWF := (@ProgramWF Σ invTokenG0 RProg G).
    Local Notation RavenHoareTriple := (@RavenHoareTriple RProg).
    Local Notation stmt_well_defined := (@stmt_well_defined RProg).
    Local Notation alloc_stmt_well_defined := (@alloc_stmt_well_defined RProg).
    Local Notation fresh_proc_entry_lvars := (@fresh_proc_entry_lvars G).
    Local Notation proc_bodies_translate := (@proc_bodies_translate RProg).
    Local Notation StackFree := (@StackFree RProg).
    Local Notation typeOf_val_has_typ := (@typeOf_val_has_typ G).
    Local Notation trnsl_assertion := (@trnsl_assertion I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation entails := (@entails I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation inv_body_bridge := (@inv_body_bridge I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation Wghost := (@Wghost Σ inG0 simpLangG0 G).
    Local Notation Wghost_alloc := (@Wghost_alloc I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ).
    Local Notation Winv := (@Winv I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation Winv_alloc := (@Winv_alloc I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation Winv_open := (@Winv_open I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation stack_free_assertion_trnsl := (@stack_free_assertion_trnsl I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_and := (@trnsl_assertion_and I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_exists := (@trnsl_assertion_exists I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_LInv_some := (@trnsl_assertion_LInv_some I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_mp_irrelevant := (@trnsl_assertion_mp_irrelevant I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_mp_irrelevant_reserved :=
      (@trnsl_assertion_mp_irrelevant_reserved I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_subst_congr := (@trnsl_assertion_subst_congr I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_unfold := (@trnsl_assertion_unfold I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_w_lexpr_subst := (@trnsl_assertion_w_lexpr_subst I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_inv_validity' := (@trnsl_inv_validity' I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_pred_validity' := (@trnsl_pred_validity' I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_w_lexpr_subst_r := (@trnsl_assertion_w_lexpr_subst_r I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation entails_intro := (@entails_intro I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation entails_refl := (@entails_refl I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation entails_trans := (@entails_trans I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation entails_and_stack_exists_swap := (@entails_and_stack_exists_swap I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation entails_exists_and_swap := (@entails_exists_and_swap I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation entails_exists_intro := (@entails_exists_intro I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_subst_lv := (@trnsl_assertion_subst_lv I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_subst_lvar := (@trnsl_assertion_subst_lvar I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_forall := (@trnsl_assertion_forall I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_ite := (@trnsl_assertion_ite I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_impl := (@trnsl_assertion_impl I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation RAPack_fpuValid := (@RAPack_fpuValid I Gs Σ inGs0 inG0 simpLangG0 RProg G).
    Local Notation trnsl_assertion_pre := (@trnsl_assertion_pre I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation fresh_lvar_not_in_lexpr_map_fvars_zip := (@fresh_lvar_not_in_lexpr_map_fvars_zip I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation hstab_lexpr_subst_fwd := (@hstab_lexpr_subst_fwd I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation hstab_lexpr_subst_r := (@hstab_lexpr_subst_r I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation stack_free_assertion_subst := (@stack_free_assertion_subst I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation transport_cmra_update := (@transport_cmra_update I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation inv_set_to_namespace := (@inv_set_to_namespace G).
    Local Notation trnsl_mask := (@trnsl_mask G).
    Local Notation inv_set_to_namespace_subseteq_trnsl_mask := (@inv_set_to_namespace_subseteq_trnsl_mask I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation ghost_heap_namespace_subseteq_trnsl_mask := (@ghost_heap_namespace_subseteq_trnsl_mask I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation inv_map_subseteq := (@inv_map_subseteq I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation inv_map_set_minus_subseteq := (@inv_map_set_minus_subseteq I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_expr_interp_lexpr_compatibility := (@trnsl_expr_interp_lexpr_compatibility I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_expr_interp_lexpr_compatibility2 := (@trnsl_expr_interp_lexpr_compatibility2 I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_hoare_triple := (@trnsl_hoare_triple I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation all_inv_worlds := (@all_inv_worlds I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation all_inv_worlds_elem := (@all_inv_worlds_elem I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation Wghost_world := (@Wghost_world Σ inG0 simpLangG0 G).
    Local Notation all_proc_tbl_chunks := (@all_proc_tbl_chunks Σ simpLangG0 RProg).
    Local Notation all_proc_tbl_chunks_elem := (@all_proc_tbl_chunks_elem I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation fresh_var_trnsl_expr_invariant := (@fresh_var_trnsl_expr_invariant I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation lexpr_holds_interp_compat := (@lexpr_holds_interp_compat I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation val_beq_refl := (@val_beq_refl I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation val_beq_eq := (@val_beq_eq I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation val_beq_neq := (@val_beq_neq I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation expr_interp_well_defined := (@expr_interp_well_defined I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation args_interp_values := (@args_interp_values I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation fresh_mp_rewrite_LExpr_holds := (@fresh_mp_rewrite_LExpr_holds I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation fresh_mp_rewrite_symb_stk_to_stk_frm_compat := (@fresh_mp_rewrite_symb_stk_to_stk_frm_compat I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation all_proc_specs_valid_iris := (@all_proc_specs_valid_iris I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation all_proc_specs_valid_raven := (@all_proc_specs_valid_raven RProg).
    Local Notation lexpr_list_fresh_lvar := (@lexpr_list_fresh_lvar I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation lexpr_map_fvars_zip_bound := (@lexpr_map_fvars_zip_bound I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation lexpr_map_fvars_zip_no_reserved := (@lexpr_map_fvars_zip_no_reserved I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation subst_map_avoids_reserved_of_lexprs := (@subst_map_avoids_reserved_of_lexprs I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation ret_val_not_reserved := (@ret_val_not_reserved I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation dom_insert_not_reserved := (@dom_insert_not_reserved I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation subst_map_avoids_reserved_insert := (@subst_map_avoids_reserved_insert I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation lval_list_no_reserved := (@lval_list_no_reserved I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation lvar_list_no_reserved := (@lvar_list_no_reserved I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation forall2_interp_stable := (@forall2_interp_stable I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).
    Local Notation trnsl_assertion_subst_lv_stable := (@trnsl_assertion_subst_lv_stable I Gs Σ inGs0 inG0 simpLangG0 RProg G Γ invTokenG0).


  Lemma assertion_entails_sound σ A B : assertion_entails σ A B -> entails σ A B.
  Proof.
    induction 1.
    - (* AE_Refl *) apply entails_refl.
    - (* AE_Trans *) eapply entails_trans; eassumption.
    - (* AE_And_Mono *)
      apply entails_intro. intros stk mp Henv.
      destruct (IHassertion_entails1 stk mp Henv) as [Pp [Pp' [<- [<- H1']]]].
      destruct (IHassertion_entails2 stk mp Henv) as [Qp [Qp' [<- [<- H2']]]].
      rewrite !trnsl_assertion_and. iIntros "[HP HQ]". iSplitL "HP".
      + iApply (H1' with "HP").
      + iApply (H2' with "HQ").
    - (* AE_And_Comm *)
      apply entails_intro. intros stk mp Henv. rewrite !trnsl_assertion_and. iIntros "[$ $]".
    - (* AE_And_Assoc_R *)
      apply entails_intro. intros stk mp Henv. rewrite !trnsl_assertion_and. iIntros "[[$ $] $]".
    - (* AE_And_Assoc_L *)
      apply entails_intro. intros stk mp Henv. rewrite !trnsl_assertion_and. iIntros "[$ [$ $]]".
    - (* AE_And_Elim_L *)
      apply entails_intro. intros stk mp Henv. rewrite trnsl_assertion_and. iIntros "[$ _]".
    - (* AE_And_Elim_R *)
      apply entails_intro. intros stk mp Henv. rewrite trnsl_assertion_and. iIntros "[_ $]".
    - (* AE_And_True_Intro *)
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and (trnsl_assertion_unfold (LPure True)) /trnsl_assertion_pre /=.
      iIntros "H". iFrame.
    - (* AE_And_True_Elim *)
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and (trnsl_assertion_unfold (LPure True)) /trnsl_assertion_pre /=.
      iIntros "[$ _]".
    - (* AE_True_Intro *)
      apply entails_intro. intros stk mp Henv.
      rewrite (trnsl_assertion_unfold (LPure True)) /trnsl_assertion_pre /=.
      iIntros "_". done.
    - (* AE_Pure *)
      apply entails_intro. intros stk mp Henv.
      rewrite (trnsl_assertion_unfold (LPure p)) (trnsl_assertion_unfold (LPure q))
        /trnsl_assertion_pre /=.
      iIntros "%Hp". iPureIntro. auto.
    - (* AE_Exists_Mono *)
      rename H into Hty.
      apply entails_intro. intros stk mp Henv.
      rewrite !trnsl_assertion_exists.
      iIntros "[%v' [%Htyp HA]]". iExists v'. iSplitR; [done|].
      have Henv' : env_typ_well_defined σ (fun y => if (y =? lv)%string then v' else mp y).
      { apply env_typ_well_defined_update; [exact Henv | rewrite Hty; exact Htyp]. }
      destruct (IHassertion_entails stk (fun y => if (y =? lv)%string then v' else mp y) Henv')
        as [Ap [Bp [<- [<- Hent]]]].
      iApply (Hent with "HA").
    - (* AE_Exists_Intro *) exact (entails_exists_intro σ lv t X H).
    - (* AE_Exists_ValIntro *)
      rename H into Hty, H0 into Htv, H1 into Hqf.
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_exists.
      rewrite (trnsl_assertion_subst_lv A lv w stk mp Hqf).
      iIntros "H". iExists w. iSplitR; [done|]. iExact "H".
    - (* AE_Exists_Elim *)
      rename H into Hty, H0 into Hfresh.
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_exists.
      iIntros "[%v' [%Htyp HP]]".
      have Henv' : env_typ_well_defined σ (fun y => if (y =? lv)%string then v' else mp y).
      { apply env_typ_well_defined_update; [exact Henv | rewrite Hty; exact Htyp]. }
      destruct (IHassertion_entails stk (fun y => if (y =? lv)%string then v' else mp y) Henv')
        as [Pp [Qp [<- [<- Hent]]]].
      iDestruct (Hent with "HP") as "HQ".
      iEval (rewrite (trnsl_assertion_mp_irrelevant lv Q v' stk mp Hfresh)) in "HQ".
      iExact "HQ".
    - (* AE_Exists_And_Swap_R *) exact (entails_exists_and_swap σ lv t body p H).
    - (* AE_And_Exists_Swap_L *)
      rename H into Hfresh.
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and trnsl_assertion_exists trnsl_assertion_exists.
      iIntros "[Hc [%v' [%Htyp Hbody]]]".
      iExists v'. iSplitR; [done|].
      rewrite trnsl_assertion_and.
      rewrite (trnsl_assertion_mp_irrelevant lv c v' stk mp Hfresh).
      iFrame.
    - (* AE_Ite_True *)
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and (trnsl_assertion_ite cond A B stk mp)
        (trnsl_assertion_unfold (LExprA cond)) /trnsl_assertion_pre /=.
      iIntros "[Hite %Hc]".
      iDestruct "Hite" as "[Hthen _]". iApply "Hthen". iPureIntro. exact Hc.
    - (* AE_Ite_False *)
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and (trnsl_assertion_ite cond A B stk mp)
        (trnsl_assertion_unfold (LExprA (LUnOp NotBoolOp cond))) /trnsl_assertion_pre /=.
      iIntros "[Hite %Hnc]".
      have Hcond_false : interp_lexpr cond mp = Some (LitBool false).
      { unfold LExpr_holds in Hnc. simpl in Hnc.
        destruct (interp_lexpr cond mp) as [[bv|zv| |lv0|[rv xv]]|] eqn:Hcond;
          simpl in Hnc; try (exfalso; exact Hnc).
        destruct bv; [discriminate Hnc | reflexivity]. }
      iDestruct "Hite" as "[_ Helse]". iApply "Helse". iPureIntro.
      unfold LExpr_holds. rewrite Hcond_false. intros [=].
    - (* AE_Ite_Bool_True *)
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and.
      rewrite (trnsl_assertion_ite cond (LAnd A (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
        (LAnd B (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false))))) stk mp).
      rewrite (trnsl_assertion_unfold (LExprA (LVar lv))) /trnsl_assertion_pre /=.
      iIntros "[Hite %Hlv]".
      unfold LExpr_holds in Hlv. simpl in Hlv.
      destruct (interp_lexpr cond mp) as [vc|] eqn:Hcond.
      + destruct (val_beq vc (LitBool true)) eqn:Hvc.
        * unfold val_beq in Hvc. apply bool_decide_eq_true_1 in Hvc. subst vc.
          iDestruct "Hite" as "[Hthen _]".
          iDestruct ("Hthen" with "[]") as "HA".
          { iPureIntro. unfold LExpr_holds. rewrite Hcond. done. }
          iEval (rewrite trnsl_assertion_and) in "HA". iDestruct "HA" as "[HA _]".
          rewrite trnsl_assertion_and (trnsl_assertion_unfold (LExprA cond)) /trnsl_assertion_pre /=.
          iFrame "HA". iPureIntro. unfold LExpr_holds. rewrite Hcond. done.
        * iDestruct "Hite" as "[_ Helse]".
          iDestruct ("Helse" with "[]") as "HB".
          { iPureIntro. unfold LExpr_holds. rewrite Hcond. intros ->.
            unfold val_beq in Hvc. apply bool_decide_eq_false_1 in Hvc. apply Hvc. reflexivity. }
          iEval (rewrite trnsl_assertion_and
            (trnsl_assertion_unfold (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false)))))
            /trnsl_assertion_pre /=) in "HB".
          iDestruct "HB" as "[_ %Hf]".
          unfold LExpr_holds in Hf. cbn [interp_lexpr] in Hf.
          assert (Hcomp : val_beq (LitBool true) (LitBool false) = false).
          { destruct (val_beq (LitBool true) (LitBool false)) eqn:Heq0; [|reflexivity].
            exfalso. apply internal_val_dec_bl in Heq0. discriminate. }
          congruence.
      + iDestruct "Hite" as "[_ Helse]".
        iDestruct ("Helse" with "[]") as "HB".
        { iPureIntro. unfold LExpr_holds. rewrite Hcond. intros []. }
        iEval (rewrite trnsl_assertion_and
          (trnsl_assertion_unfold (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false)))))
          /trnsl_assertion_pre /=) in "HB".
        iDestruct "HB" as "[_ %Hf]".
        unfold LExpr_holds in Hf. cbn [interp_lexpr] in Hf.
        assert (Hcomp : val_beq (LitBool true) (LitBool false) = false).
        { destruct (val_beq (LitBool true) (LitBool false)) eqn:Heq0; [|reflexivity].
          exfalso. apply internal_val_dec_bl in Heq0. discriminate. }
        congruence.
    - (* AE_Ite_Bool_False *)
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and.
      rewrite (trnsl_assertion_ite cond (LAnd A (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
        (LAnd B (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false))))) stk mp).
      rewrite (trnsl_assertion_unfold (LExprA (LUnOp NotBoolOp (LVar lv)))) /trnsl_assertion_pre /=.
      iIntros "[Hite %Hlv]".
      unfold LExpr_holds in Hlv. simpl in Hlv.
      destruct (mp lv) as [b| |i|l|ra] eqn:Hmplv; simpl in Hlv; try contradiction.
      injection Hlv as Hlv. apply negb_true_iff in Hlv. subst b.
      destruct (interp_lexpr cond mp) as [vc|] eqn:Hcond.
      + destruct (val_beq vc (LitBool true)) eqn:Hvc.
        * unfold val_beq in Hvc. apply bool_decide_eq_true_1 in Hvc. subst vc.
          iDestruct "Hite" as "[Hthen _]".
          iDestruct ("Hthen" with "[]") as "HA".
          { iPureIntro. unfold LExpr_holds. rewrite Hcond. done. }
          iEval (rewrite trnsl_assertion_and
            (trnsl_assertion_unfold (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
            /trnsl_assertion_pre /=) in "HA".
          iDestruct "HA" as "[_ %Ht]".
          unfold LExpr_holds in Ht. cbn [interp_lexpr] in Ht.
          assert (Hcomp : val_beq (LitBool false) (LitBool true) = false).
          { destruct (val_beq (LitBool false) (LitBool true)) eqn:Heq0; [|reflexivity].
            exfalso. apply internal_val_dec_bl in Heq0. discriminate. }
          congruence.
        * iDestruct "Hite" as "[_ Helse]".
          iDestruct ("Helse" with "[]") as "HB".
          { iPureIntro. unfold LExpr_holds. rewrite Hcond. intros ->.
            unfold val_beq in Hvc. apply bool_decide_eq_false_1 in Hvc. apply Hvc. reflexivity. }
          iEval (rewrite trnsl_assertion_and) in "HB". iDestruct "HB" as "[$ _]".
      + iDestruct "Hite" as "[_ Helse]".
        iDestruct ("Helse" with "[]") as "HB".
        { iPureIntro. unfold LExpr_holds. rewrite Hcond. intros []. }
        iEval (rewrite trnsl_assertion_and) in "HB". iDestruct "HB" as "[$ _]".
    - (* AE_LExpr_Subst_Eq_Congr *)
      rename H into Hqf.
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and (trnsl_assertion_unfold (LExprA (LBinOp EqOp (LVar lv) (LVar lv2))))
        /trnsl_assertion_pre /=.
      iIntros "[%Heq H]".
      unfold LExpr_holds in Heq. simpl in Heq. injection Heq as Heq.
      apply bool_decide_eq_true in Heq.
      rewrite (trnsl_assertion_subst_lvar A lv lv2 stk mp Hqf).
      have Hself : (fun y => if (y =? lv)%string then mp lv2 else mp y) = mp.
      { apply functional_extensionality. intros y.
        destruct (String.eqb_spec y lv) as [-> | _]; [exact (eq_sym Heq) | reflexivity]. }
      rewrite Hself. iExact "H".
    - (* AE_Exists_Rename_Intro *)
      rename H into Hty, H0 into Hty2, H1 into Hqf.
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_exists.
      rewrite (trnsl_assertion_subst_lvar A lv lv2 stk mp Hqf).
      iIntros "H". iExists (mp lv2). iSplitR.
      + iPureIntro. specialize (Henv lv2). rewrite Hty2 in Henv.
        destruct (σ lv2), (mp lv2); simpl in *; try done.
      + iExact "H".
    - (* AE_LExprA_Impl *)
      rename H into Himpl.
      apply entails_intro. intros stk mp Henv.
      rewrite (trnsl_assertion_unfold (LExprA e1)) (trnsl_assertion_unfold (LExprA e2)) /trnsl_assertion_pre /=.
      iIntros "%He1". iPureIntro. exact (Himpl mp He1).
    - (* AE_LExprA_True *)
      rename H into Htrue.
      apply entails_intro. intros stk mp Henv.
      rewrite (trnsl_assertion_unfold (LPure True)) (trnsl_assertion_unfold (LExprA e)) /trnsl_assertion_pre /=.
      iIntros "_". iPureIntro. exact (Htrue mp).
    - (* AE_GhostOwn_Chunk_Eq *)
      rename H into Heq.
      apply entails_intro. intros stk mp Henv.
      rewrite !trnsl_assertion_unfold /trnsl_assertion_pre /=.
      destruct (Γ r) as [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ].
      + unfold LExpr_holds. rewrite (Heq mp). done.
      + done.
  Qed.


    (* mp is quantified here, inside the entailment (Iris-level ∀), rather
       than as a Rocq-level forall wrapping the whole theorem: RavenHoareTriple
       itself never mentions mp (it's a purely symbolic calculus), and pinning
       one mp for the entire derivation tree before induction even starts
       forces every fresh lvar introduced anywhere in the derivation to agree
       with that single, externally-fixed valuation -- which SequenceRule's
       own soundness case needs to violate (chaining into a second statement
       whose precondition needs the *specific* witness the first statement's
       own postcondition existential just produced, not the one true mp
       decided in advance). Keeping ∀mp inside the iProp lets iInduction's
       own per-case IH each carry an independent ∀mp', instantiable at
       whatever extension of the ambient mp a given case's witness needs. *)


    Theorem rrl_validity ρ σ stk_id p msk cmd q
      (Hwf : ProgramWF) (Hpbt : proc_bodies_translate) :
      stmt_well_defined ρ cmd ->
      msk ⊆ inv_set ->
       □ all_inv_worlds ∗ □ Wghost_world ∗ □ all_proc_tbl_chunks ∗ ▷ (all_proc_specs_valid_iris σ) ∗ ⌜RavenHoareTriple ρ σ p cmd msk q⌝
      ⊢  (∀ mp, ⌜env_typ_well_defined σ mp⌝ -∗ trnsl_hoare_triple stk_id p msk cmd q mp).
    Proof.
      iIntros (Hwelldef Hmask_sub) "[#Hworlds [#Hgworld [#HprocTbl [#Calls %H]]]]".
      iInduction H as
      [ ρ σ stk mask v lv e lexpr t Htrnsl Hinf Hfresh Hstkcompat |
      ρ σ stk mask x e rdchunk fld lexpr_e lvar_x t Htrnsl Htyp Hfresh Hnotin Hstkcompat
      | ρ σ stk mask v fld e old_chunk lv lexpr Hatm HLexpr1 Hwd
      | ρ σ stk mask x fld_vals ghost_fld_vals lvar_x
        Hfresh HNoDupFV HNoDupGFV HgfvFsNe HgfvValid Hstkcompat
      | | |
      | ρ σ stk stk' mask invr args stmt inv_record p q lv0 t0 lexprs Hargs Hinv_mask Hinv_record Hinv_len Hlexprs_res Hstk_tp subst Hlvfresh Hlv0_res Hbody IHHbody
      | ρ σ stk mask invr args inv_record p lexprs Hargs Hinv_mask Hinv_record Hinv_len Hlexprs_res Hstk_tp subst
      | | | | | |
      | ρ σ stk mask v e1 fld e2 e3 lvar_v lexpr1 lexpr2 lexpr3 old_chunk Hfresh Hinf Hwd2 Hwd3 Hnotin Htrnsl1 Htrnsl2 Htrnsl3 Hstkcompat
      | ρ σ mask v t body c q Hsigma Hqfresh
      | ρ σ stk mask e p lexpr Htrnsl Hinf Hstkcompat ] "IH";
      iIntros (mp) "%Henv".
      3: { 
        (* FIELD WRITE *)
        unfold trnsl_hoare_triple.
        simpl.
        destruct (trnsl_stmt (FldWr v fld e)) eqn:Ht. 2: done.
        { inversion Ht. } 

        inversion Ht. simpl. 
        - iIntros (Φ). iModIntro.
          setoid_rewrite trnsl_assertion_unfold.
          iIntros "[Hstk1 Hstk2] HΦ".
          simpl.
          iDestruct "Hstk2" as (l old_chunk0) "[%Hlexpr1 [%Hold Hlfld]]".
          destruct Hwd as [tp Htp].
          assert (inf_lexpr σ lexpr = Some tp) as Hlexpr_tp.
          { apply (lexpr_expr_typ_compat ρ _ stk e); try done. }
          assert (∃ val, interp_lexpr lexpr mp = Some val) as [new_chunk Hinterp_new].
          { apply (lexpr_typcheck_well_defined σ _ _ tp); try done. }
          pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ HLexpr1 Hinterp_new) as Hexpr_step_e.

          iApply (wp_heap_wr stk_id (symb_stk_to_stk_frm stk mp) _ _ _ l _ _ _ with "[Hstk1 Hlfld]").

        {
          iFrame.
          iSplit.
          { iPureIntro. simpl. rewrite lookup_fmap.
            rewrite Hatm. simpl. unfold LExpr_holds in Hlexpr1. simpl in Hlexpr1. injection Hlexpr1 as Hlv.
            destruct (val_beq (mp lv) (LitLoc l)) eqn:Hlv'.
            - apply f_equal.
            apply internal_val_dec_bl in Hlv'.
            rewrite Hlv'. simpl. apply f_equal.

            destruct l. simpl. done.
            - inversion Hlv.
          }


          { iPureIntro. exact Hexpr_step_e. }
        }

        {
          iModIntro. iIntros "[HstkO [Hlpt _]]".
          iApply "HΦ". iFrame.
          iPureIntro. split; [exact Hlexpr1 | exact Hinterp_new].
        }

      }

      7: {
        (* INV ACCESS BLOCK *)
        unfold trnsl_hoare_triple.

        inversion Hwelldef as [ | | | | | | | | | | | | | rho' inv' args' stmt' HInvSet HargsWellDef HBodywelldef | | | ];
          subst stmt' args'.
        have Hsub : ↑(inv_namespace_map invr) ⊆ trnsl_mask mask.
        { etrans; [| apply inv_set_to_namespace_subseteq_trnsl_mask]. apply inv_map_subseteq; done. }
        have HInvs : trnsl_mask (mask ∖ {[invr]}) = trnsl_mask mask ∖ ↑inv_namespace_map invr.
        { rewrite /trnsl_mask.
          have HInvs' : inv_set_to_namespace (mask ∖ {[invr]})
                      = inv_set_to_namespace mask ∖ ↑inv_namespace_map invr.
          { apply (inv_map_set_minus_subseteq Hwf); done. }
          have Hdisj := Hwf.(pwf_ghost_heap_namespace_disjoint_inv) invr HInvSet.
          rewrite HInvs'. set_solver. }
        iDestruct (all_inv_worlds_elem invr HInvSet with "Hworlds") as "#Hiw".

        destruct (trnsl_stmt (InvAccessBlock invr args stmt)) eqn:Ht.
        2: { done. }

        { (* the block performs no physical step: a pure ghost update *)
          assert (Hnone : trnsl_stmt stmt = None').
          { apply trnsl_stmt_trnsl_atomic_block_none. simpl in Ht. exact Ht. }
          iEval (rewrite Hnone) in "IH".
          iIntros "Hpre".
          iEval (rewrite !trnsl_assertion_and) in "Hpre".
          iEval (rewrite (trnsl_assertion_LInv_some invr inv_record lexprs stk_id mp Hinv_record)) in "Hpre".
          iDestruct "Hpre" as "[Hstk [HTok Hu]]".
          iDestruct "HTok" as (vs) "[%HF2 #Hfrag]".
          have Hlenvs : length vs = length inv_record.(inv_args).
          { rewrite <- Hinv_len. symmetry. exact (Forall2_length _ _ _ HF2). }
          iMod (Winv_open Hwf _ invr inv_record vs Hinv_record Hlenvs Hsub
                 with "Hiw Hfrag") as "[Hbody Hclose]".
          have Hbridge := inv_body_bridge Hwf invr inv_record lexprs vs stk_id mp
            (lexpr_map_fvars_zip_no_reserved inv_record.(inv_args) lexprs Hlexprs_res)
            Hinv_record Hinv_len HF2.
          iEval (rewrite <- Hbridge) in "Hbody".
          iPoseProof ("IH" with "[%] [%]") as "IH1".
          { done. }
          { set_solver. }
          iPoseProof ("IH1" $! mp with "[%] [Hstk Hbody Hu]") as "IH2".
          { done. }
          { iEval (rewrite !trnsl_assertion_and). iFrame. }
          iEval (rewrite HInvs) in "IH2".
          iMod "IH2" as "IH2".
          iEval (rewrite trnsl_assertion_exists) in "IH2".
          iDestruct "IH2" as (v') "[%Htyp IH2]".
          iEval (rewrite !trnsl_assertion_and) in "IH2".
          iDestruct "IH2" as "[Hstk [Hbody' Hq]]".
          have Hdom_sm : dom subst = list_to_set inv_record.(inv_args).
          { apply dom_list_to_map_zip. lia. }
          have Hfv_sm : assertion_true_fvars (inv_body inv_record) ⊆ dom subst.
          { rewrite Hdom_sm. exact (Hwf.(pwf_inv_fvars_closed) invr inv_record Hinv_record). }
          have Hlv_lexprs : Forall (fun le => lv0 ∉ lexpr_fvars le) lexprs.
          { exact (lexpr_list_fresh_lvar stk args lexprs lv0 Hargs Hlvfresh). }
          have Hlv_sm : lv0 ∉ lexpr_map_fvars subst.
          { exact (lexpr_map_fvars_zip_bound inv_record.(inv_args) lexprs lv0 Hlv_lexprs). }
          have Hmr_sm : subst_map_avoids_reserved subst.
          { apply subst_map_avoids_reserved_of_lexprs.
            - exact (Hwf.(pwf_inv_args_not_reserved) invr inv_record Hinv_record).
            - exact Hlexprs_res. }
          have Hbind_sm : assertion_exists_binders (inv_body inv_record) ##
            (dom subst ∪ lexpr_map_fvars subst).
          { apply reserved_disjoint_dom.
            - exact (Hwf.(pwf_inv_binders_reserved) invr inv_record Hinv_record).
            - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
                [exact (proj1 Hmr_sm v Hv) | exact (proj2 Hmr_sm v Hv)]. }
          iEval (rewrite (trnsl_assertion_subst_lv_stable Hwf (inv_body inv_record) subst lv0 v' stk_id mp
            (Hwf.(pwf_inv_body_stack_free) invr inv_record Hinv_record)
            Hbind_sm
            Hfv_sm Hmr_sm Hlv_sm)) in "Hbody'".
          iEval (rewrite Hbridge) in "Hbody'".
          iMod ("Hclose" with "Hbody'") as "_".
          iModIntro.
          iEval (rewrite trnsl_assertion_exists).
          iExists v'. iSplitR; [done|].
          iEval (rewrite !trnsl_assertion_and).
          iEval (rewrite (trnsl_assertion_LInv_some invr inv_record lexprs stk_id
            (fun y => if (y =? lv0)%string then v' else mp y) Hinv_record)).
          iFrame "Hstk Hq".
          iExists vs. iSplit; [iPureIntro; exact (forall2_interp_stable lexprs vs mp lv0 v' Hlv_lexprs HF2) | iExact "Hfrag"].
        }

        { (* the block performs one atomic physical step *)
          assert (Hsome : trnsl_stmt stmt = Some' s).
          { apply trnsl_stmt_trnsl_atomic_block_some. simpl in Ht. exact Ht. }
          have Hatomic : Atomic WeaklyAtomic (to_rtstmt stk_id s).
          { simpl in Ht. apply (trnsl_atomic_block_atomicity stmt); done. }
          iEval (rewrite Hsome) in "IH".
          iIntros (Φ) "!> Hpre HΦ".
          iEval (rewrite !trnsl_assertion_and) in "Hpre".
          iEval (rewrite (trnsl_assertion_LInv_some invr inv_record lexprs stk_id mp Hinv_record)) in "Hpre".
          iDestruct "Hpre" as "[Hstk [HTok Hu]]".
          iDestruct "HTok" as (vs) "[%HF2 #Hfrag]".
          have Hlenvs : length vs = length inv_record.(inv_args).
          { rewrite <- Hinv_len. symmetry. exact (Forall2_length _ _ _ HF2). }
          iMod (Winv_open Hwf _ invr inv_record vs Hinv_record Hlenvs Hsub
                 with "Hiw Hfrag") as "[Hbody Hclose]".
          have Hbridge := inv_body_bridge Hwf invr inv_record lexprs vs stk_id mp
            (lexpr_map_fvars_zip_no_reserved inv_record.(inv_args) lexprs Hlexprs_res)
            Hinv_record Hinv_len HF2.
          iEval (rewrite <- Hbridge) in "Hbody".
          rewrite <- HInvs.
          iPoseProof ("IH" with "[%] [%]") as "IH1".
          { done. }
          { set_solver. }
          iApply ("IH1" $! mp with "[%] [Hstk Hbody Hu]").
          { done. }
          { iEval (rewrite !trnsl_assertion_and). iFrame. }
          iNext. iIntros "Hpost".
          iEval (rewrite trnsl_assertion_exists) in "Hpost".
          iDestruct "Hpost" as (v') "[%Htyp Hpost]".
          iEval (rewrite !trnsl_assertion_and) in "Hpost".
          iDestruct "Hpost" as "[Hstk [Hbody' Hq]]".
          have Hdom_sm : dom subst = list_to_set inv_record.(inv_args).
          { apply dom_list_to_map_zip. lia. }
          have Hfv_sm : assertion_true_fvars (inv_body inv_record) ⊆ dom subst.
          { rewrite Hdom_sm. exact (Hwf.(pwf_inv_fvars_closed) invr inv_record Hinv_record). }
          have Hlv_lexprs : Forall (fun le => lv0 ∉ lexpr_fvars le) lexprs.
          { exact (lexpr_list_fresh_lvar stk args lexprs lv0 Hargs Hlvfresh). }
          have Hlv_sm : lv0 ∉ lexpr_map_fvars subst.
          { exact (lexpr_map_fvars_zip_bound inv_record.(inv_args) lexprs lv0 Hlv_lexprs). }
          have Hmr_sm : subst_map_avoids_reserved subst.
          { apply subst_map_avoids_reserved_of_lexprs.
            - exact (Hwf.(pwf_inv_args_not_reserved) invr inv_record Hinv_record).
            - exact Hlexprs_res. }
          have Hbind_sm : assertion_exists_binders (inv_body inv_record) ##
            (dom subst ∪ lexpr_map_fvars subst).
          { apply reserved_disjoint_dom.
            - exact (Hwf.(pwf_inv_binders_reserved) invr inv_record Hinv_record).
            - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
                [exact (proj1 Hmr_sm v Hv) | exact (proj2 Hmr_sm v Hv)]. }
          iEval (rewrite (trnsl_assertion_subst_lv_stable Hwf (inv_body inv_record) subst lv0 v' stk_id mp
            (Hwf.(pwf_inv_body_stack_free) invr inv_record Hinv_record)
            Hbind_sm
            Hfv_sm Hmr_sm Hlv_sm)) in "Hbody'".
          iEval (rewrite Hbridge) in "Hbody'".
          rewrite HInvs.
          iMod ("Hclose" with "Hbody'") as "_".
          iModIntro. iApply "HΦ".
          iEval (rewrite trnsl_assertion_exists).
          iExists v'. iSplitR; [done|].
          iEval (rewrite !trnsl_assertion_and).
          iEval (rewrite (trnsl_assertion_LInv_some invr inv_record lexprs stk_id
            (fun y => if (y =? lv0)%string then v' else mp y) Hinv_record)).
          iFrame "Hstk Hq".
          iExists vs. iSplit; [iPureIntro; exact (forall2_interp_stable lexprs vs mp lv0 v' Hlv_lexprs HF2) | iExact "Hfrag"].
        }
      }

      7: {
        (* INV ALLOC (FoldInv) *)
        unfold trnsl_hoare_triple. simpl.
        inversion Hwelldef as [ | | | | | | | | | | | | | | rho' inv' args' HInvSet HargsWellDef | | ];
          subst args'.
        have Hsub : ↑(inv_namespace_map invr) ⊆ trnsl_mask mask.
        { etrans; [| apply inv_set_to_namespace_subseteq_trnsl_mask]. apply inv_map_subseteq; done. }
        iDestruct (all_inv_worlds_elem invr HInvSet with "Hworlds") as "Hiw".
        destruct (args_interp_values ρ σ stk mp args lexprs Hstk_tp Henv HargsWellDef Hargs)
          as [vs HF2].
        have Hlenvs : length vs = length inv_record.(inv_args).
        { rewrite <- Hinv_len. symmetry. exact (Forall2_length _ _ _ HF2). }
        rewrite !trnsl_assertion_and.
        rewrite (trnsl_assertion_LInv_some invr inv_record lexprs stk_id mp Hinv_record).
        iIntros "[Hstk [Hbody Hu]]".
        have Hbridge := inv_body_bridge Hwf invr inv_record lexprs vs stk_id mp
          (lexpr_map_fvars_zip_no_reserved inv_record.(inv_args) lexprs Hlexprs_res)
          Hinv_record Hinv_len HF2.
        rewrite Hbridge.
        iMod (Winv_alloc Hwf _ invr inv_record vs Hinv_record Hlenvs Hsub
               with "Hiw Hbody") as "#Hfrag".
        iModIntro. iFrame. iExists vs. by iFrame "#".
      }

      1 : {
        (* ASSIGN *)
        unfold trnsl_hoare_triple. simpl.

        iIntros (Φ).
        iModIntro.
        iIntros "Hstk HΦ".

        destruct (interp_lexpr lexpr mp) eqn: Hlexpr.

        { iApply (wp_assign stk_id (symb_stk_to_stk_frm stk mp) v (trnsl_lval v0) e with "[Hstk]").

          {
            setoid_rewrite trnsl_assertion_unfold.
            iFrame.
            iPureIntro.
            apply (trnsl_expr_interp_lexpr_compatibility _ _ lexpr). { done. } 
            done. 
          }
          
          iNext.
          iIntros "[Hstk _]".
          iApply "HΦ".
          setoid_rewrite trnsl_assertion_unfold.
          iExists (v0).
          iSplitR.
          { iPureIntro.
            exact (interp_lexpr_well_typed_match σ lexpr t v0 mp Henv
              (lexpr_expr_typ_compat ρ σ stk e lexpr t Hstkcompat Htrnsl Hinf) Hlexpr). }
          iSplitL.
          {
            (* simpl. *)
            (unfold rrl_lang.symb_stk_to_stk_frm). simpl. unfold fresh_lvar in Hfresh.
            assert (<[v:=trnsl_lval v0]> ((λ v1 : lvar, trnsl_lval (mp v1)) <$> stk)
                =
              (λ v1 : lvar, trnsl_lval (if (v1 =? lv)%string then v0 else mp v1)) <$>
                <[v:=lv]> stk) as Hmapeq.
              {
                apply map_eq.
                intros i.
                destruct (String.eqb i v) eqn:Hi.
                - apply String.eqb_eq in Hi; subst i.
                  simpl. rewrite lookup_insert. rewrite lookup_fmap. rewrite lookup_insert. simpl. rewrite String.eqb_refl. reflexivity.
                - apply String.eqb_neq in Hi.
                  rewrite lookup_insert_ne. 2:{ done. }
                  rewrite lookup_fmap.
                  rewrite lookup_fmap.
                  rewrite lookup_insert_ne; [|done].
                  destruct (stk !! i) as [x|] eqn:HstkI;  simpl; auto.
                  + assert (x ≠ lv) as Hxlv. { specialize (Hfresh i). rewrite HstkI in Hfresh. intros Heq. subst x. contradiction.
                  } simpl.
                  rewrite HstkI. simpl. f_equal. rewrite <- String.eqb_neq in Hxlv. rewrite Hxlv. auto.

                  + rewrite HstkI. simpl. done.
              } rewrite Hmapeq. done.

          }
          iPureIntro.

          apply (fresh_mp_rewrite_LExpr_holds stk lv e lexpr mp v0 Hfresh Htrnsl Hlexpr).
        }

        assert (Hstk_compat: stk_type_compat ρ σ stk) by assumption.
        pose proof (expr_interp_well_defined ρ σ stk e mp lexpr Hstk_compat Henv Htrnsl Hlexpr).
        inversion Hwelldef.
        contradiction.
      }

      9 : {
        (* FRAME RULE *)
        iPoseProof ("IH" with  "[%]") as "IH2". { done. }
        iClear "IH".

        unfold trnsl_hoare_triple. simpl.
        destruct (trnsl_stmt s) eqn:Htrnsl; try done.
        { simpl.
          setoid_rewrite trnsl_assertion_unfold.

          iIntros "[Hu Hu1]".
          iPoseProof ("IH2" with "[%] [%] [Hu]") as ">IH3"; try iFrame; try done.

        }

        {
          iIntros (Φ).
          setoid_rewrite trnsl_assertion_unfold.
          iModIntro. iIntros "[Hu Hu1] HΦ".
          iApply ("IH2" with "[%] [%] [Hu]"); try iFrame; try done.
          iNext. iIntros "Hu0". iApply "HΦ". iFrame.
        }
      }

      1 : {
        (* FIELD READ *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ). setoid_rewrite trnsl_assertion_unfold. iModIntro. iIntros "[Hstk Hl] HΦ".
        iDestruct "Hl" as (l val) "[%HLe_h [%Hchunk H_l_hp]]".

        destruct (interp_lexpr lexpr_e mp) eqn: Hinterp.

        2 : { assert (Hstk_compat: stk_type_compat ρ σ stk) by assumption.
          apply (expr_interp_well_defined ρ σ stk e mp lexpr_e Hstk_compat Henv Htrnsl) in Hinterp.
          inversion Hwelldef. contradiction.
        }

        pose proof (lexpr_holds_interp_compat _ _ _ _ HLe_h Hinterp). subst v.

        iApply (wp_heap_rd stk_id (rrl_lang.symb_stk_to_stk_frm stk mp) fld e (trnsl_lval val) l x _ 1%Qp with "[Hstk H_l_hp]").

        {
          pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ Htrnsl Hinterp) as Hstep.
          iFrame.
          iPureIntro.
          simpl in Hstep.
          assert (l = {| loc_car := loc_car l |}) as Hloc.
          { destruct l. simpl. done.  }
          rewrite Hloc. done.
        }

        {
          iNext.
          iIntros "[Hstk [Hhp _]]".
          iApply "HΦ". iFrame.
          iExists val.
          iSplitR.
          { iPureIntro. exact (interp_lexpr_well_typed_match σ rdchunk t val mp Henv Htyp Hchunk). }

          iSplitL "Hstk".
          - pose proof (fresh_mp_rewrite_symb_stk_to_stk_frm_compat stk lvar_x x mp val Hfresh) as HstkOwnDone.
            rewrite HstkOwnDone. iFrame.

          - iSplitL.
            + iPureIntro.
              pose proof (fresh_var_trnsl_expr_invariant stk lvar_x e _ mp val Hfresh Htrnsl) as Hfvi.
              unfold LExpr_holds.
              simpl. rewrite <- Hfvi.
              rewrite (interp_lexpr_stable rdchunk mp lvar_x val Hnotin).
              split; [apply HLe_h | rewrite Hchunk; done].

            + iPureIntro. unfold LExpr_holds. simpl.
              rewrite (interp_lexpr_stable rdchunk mp lvar_x val Hnotin). rewrite Hchunk.
              rewrite String.eqb_refl. rewrite val_beq_refl. done.
        }
      }

      1 : {
        (* ALLOC *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ).
        iModIntro.
        iIntros "Hstack HΦ".
        iApply wp_fupd.
        iApply (wp_alloc _ _ fld_vals ghost_fld_vals.*1 _ _ with "[Hstack]") .
        - exact HNoDupFV.
        - exact HNoDupGFV.
        - intro Hne. apply HgfvFsNe. intro Heq. apply Hne. rewrite Heq. done.
        - setoid_rewrite trnsl_assertion_unfold. iFrame.
        - iNext.
          iIntros "Hpost".
          iDestruct "Hpost" as (l) "[Hstk [Hhp [Hgfrag _]]]".
          set (mp' := (λ x0 : lvar, if (x0 =? lvar_x)%string then LitLoc l else mp x0)).

          (* Ghost fields: mint a fresh ghost cell per (fld, r, x) triple,
             consuming Hgfrag's reservation for that key one at a time,
             mirroring the real-field induction below but via Wghost_alloc
             (a fancy update -- hence wp_fupd above) instead of a bare
             field_list_to_iprop fact. *)
          iAssert (|={trnsl_mask mask}=> trnsl_assertion (field_list_to_ghost_assertion (LVar lvar_x) ghost_fld_vals) stk_id mp')%I
            with "[Hgfrag]" as "Hghost".
          { iInduction ghost_fld_vals as [ | [gfld [r gx]] gfvs'] "IHg".
            - iModIntro. setoid_rewrite trnsl_assertion_unfold. done.
            - simpl.
              inversion HNoDupGFV as [| ? ? HgNotIn HgNoDup'].
              have Hgcons_ne : (gfld, existT r gx) :: gfvs' ≠ ([] : list (fld_name * ra_elem)).
              { discriminate. }
              have Hfvne : fld_vals ≠ [] := HgfvFsNe Hgcons_ne.
              iPoseProof ("IHg" $! HgNoDup' (λ _, Hfvne) (Forall_inv_tail HgfvValid)) as "IHg2".
              iClear "IHg".
              rewrite (ghost_dom_frag_insert (heap_addr_constr l gfld)
                (list_to_set (map (heap_addr_constr l) gfvs'.*1))); [ | set_solver].
              iDestruct "Hgfrag" as "[Hgfrag1 Hgfragr]".
              iMod ("IHg2" with "Hgfragr") as "Hrest".
              destruct (Γ r) as [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ] eqn:HΓeq.
              + pose proof (Wghost_alloc (trnsl_mask mask) r l gfld gx (Forall_inv HgfvValid)
                  (existT i (exist _ U (conj Hdis (exist _ Heq_car (conj Heq_cmra (conj Hop Hvalid))))))
                  HΓeq) as HWalloc.
                specialize (HWalloc (ghost_heap_namespace_subseteq_trnsl_mask mask)).
                iMod (HWalloc with "Hgworld Hgfrag1") as (γ) "[Hmap Hown]".
                iModIntro.
                setoid_rewrite trnsl_assertion_unfold.
                simpl.
                rewrite HΓeq.
                iSplitL "Hmap Hown".
                * iExists l, gx, γ.
                  iSplitR; [| iSplitR; [done | iFrame]].
                  iPureIntro. unfold LExpr_holds. simpl.
                  subst mp'. simpl. rewrite String.eqb_refl val_beq_refl. done.
                * iExact "Hrest".
              + iModIntro.
                setoid_rewrite trnsl_assertion_unfold.
                simpl.
                rewrite HΓeq.
                iSplitR; [done | iExact "Hrest"].
          }
          iMod "Hghost" as "Hghost".

          iApply "HΦ". iModIntro. iFrame.
          setoid_rewrite trnsl_assertion_unfold.
          iExists (LitLoc l).
          iSplitR; [done|].
          simpl.
          iFrame "Hghost".

          clear HgfvFsNe HNoDupGFV HgfvValid.
          iInduction fld_vals as [ | ] "IH".

          + simpl. iFrame. rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done.
          unfold symb_stk_to_stk_frm. simpl.
          assert (lang.LitLoc l = lang.LitLoc {| loc_car := loc_car l |}) as H1'.
          {  destruct l. simpl. done. }
          rewrite <- H1'. iFrame.

          + simpl. destruct a as [fld val].
          assert (stmt_well_defined ρ (Alloc x fld_vals)) as Hwell_def'. { apply (alloc_stmt_well_defined _ _ fld val). exact Hwelldef. }

            * simpl.
              iPoseProof ("IH" with "[%]") as "IH2"; try done.
              iClear "IH".
              iDestruct "Hhp" as "[Hhpl Hhpfvs]".
              inversion HNoDupFV as [| ? ? Hnotin_fv Hnodup_fv_tail].
              iPoseProof ("IH2" $! Hnodup_fv_tail with "Hstk Hhpfvs") as "[IH3 IH3']".
              iFrame. iExists l, (trnsl_val val).
              assert (trnsl_lval (trnsl_val val) = val) as H1'. { apply trnsl_lval_trnsl_val_inverse. }
              rewrite H1'. iFrame.
              iPureIntro.
              unfold LExpr_holds.
              simpl.
              split; [ | reflexivity].
              subst mp'. simpl. rewrite String.eqb_refl. rewrite val_beq_refl. done.
      }

      4 : {
        (* UNFOLD PRED: no later left to strip -- LPred denotes its body
           directly, so unfolding is a definitional step. *)
        unfold trnsl_hoare_triple.
        simpl.
        pose proof (trnsl_pred_validity' pred lexprs stk_id mp) as HPredTrnsl.
        rewrite H0 in HPredTrnsl. unfold subst_map in HPredTrnsl. simpl in HPredTrnsl.
        rewrite !trnsl_assertion_and.
        rewrite <- HPredTrnsl.
        iIntros "H". iModIntro. iExact "H".
      }

      4 : {
        (* FOLD PRED *)
        unfold trnsl_hoare_triple.
        simpl.
        pose proof (trnsl_pred_validity' pred lexprs stk_id mp) as HPredTrnsl.
        rewrite H1 in HPredTrnsl. unfold subst_map in HPredTrnsl. simpl in HPredTrnsl.
        rewrite !trnsl_assertion_and.
        rewrite <- HPredTrnsl.
        iIntros "H". iModIntro. iExact "H".
      }

      2 : {
        (* SEQ *)
        inversion Hwelldef.
        iPoseProof ("IH" with "[%] [%]") as "IH'"; try done.
        iPoseProof ("IH1" with "[%] [%]") as "IH1'"; try done.
        iSpecialize ("IH'" $! mp). iSpecialize ("IH1'" $! mp).
        iClear "IH IH1".

        unfold trnsl_hoare_triple.
        simpl.
        - destruct (trnsl_stmt c1) eqn:Hc1, (trnsl_stmt c2) eqn:Hc2; try done.
          +  iIntros "Hu0".
          iPoseProof ("IH'" with "[%] Hu0") as ">IHH"; try done.
           iApply ("IH1'" with "[%]"); try done.

          + iIntros (Φ). iModIntro. iIntros "Hu0 HΦ".
            iPoseProof ("IH'" with "[%] Hu0") as ">IHH"; try done.
            iApply ("IH1'" with "[%] IHH"); try done.

          + iIntros (Φ) "!> Hu0 HΦ".
            iApply wp_fupd.
            iApply ("IH'" $! Henv with "Hu0").
            iNext. iIntros "Hmid".
            iPoseProof ("IH1'" $! Henv with "Hmid") as "Hpost".
            iMod "Hpost". iModIntro. iApply "HΦ". iFrame.

          + simpl.
            iApply wp_seq.
              { iApply ("IH'" with "[%]"); try done. }
              { iApply ("IH1'" with "[%]"); try done. }
      }

      5 : {
        (* SKIP *)
        unfold trnsl_hoare_triple. simpl.
        iIntros (Φ). iModIntro. iIntros "Hp HΦ".
        iApply (wp_skip with "Hp").
        iNext. setoid_rewrite trnsl_assertion_unfold. iIntros "[[Hstk Hu] _]". iApply "HΦ". iFrame.
      }

      5: {
        (* CAS: a single rule covering both outcomes. The
           outcome (chunk = lexpr2, at the pre-CAS map mp) is decided once,
           right after establishing lexpr1/lexpr2's evaluatedness, shared by
           both branches; the branch itself then picks which side of the
           postcondition's LIte to discharge, closing the other side
           vacuously by deriving False from its own antecedent. *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ). iModIntro. setoid_rewrite trnsl_assertion_unfold. iIntros "[Hstk He1] HΦ".
        iDestruct "He1" as (l chunk) "[%He1 [%Hold Hl]]".
        unfold LExpr_holds in He1. simpl in He1.
        destruct (interp_lexpr lexpr1 mp) eqn:Hlexpr1.
        2 : {
            (* Make sure interp_lexpr lexpr1 is not None *)
            assert (inf_lexpr σ lexpr1 = Some TpLoc) as Hlexpr_tp.  { apply (lexpr_expr_typ_compat ρ _ stk e1); try done. }
            assert (∃ val, interp_lexpr lexpr1 mp = Some val) as Hlexpr_interp. { apply (lexpr_typcheck_well_defined σ _ _ TpLoc); try done. }
            destruct Hlexpr_interp as [val0 Hlexpr_inter].
            rewrite Hlexpr_inter in Hlexpr1. discriminate.
        }

        injection He1 as He1.
        destruct (val_beq v0 (LitLoc l)) eqn:Hv0_l; try done.
        apply val_beq_eq in Hv0_l. rewrite Hv0_l in Hlexpr1.

        pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ Htrnsl1 Hlexpr1) as Hexpr_step_e1.

        destruct Hwd2 as [tp2 Htp2].
        assert (inf_lexpr σ lexpr2 = Some tp2) as Hlexpr2_tp.
        { apply (lexpr_expr_typ_compat ρ _ stk e2); try done. }
        assert (∃ val, interp_lexpr lexpr2 mp = Some val) as [old_val2 Hl2].
        { apply (lexpr_typcheck_well_defined σ _ _ tp2); try done. }
        pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ Htrnsl2 Hl2) as Hexpr_step_e2.

        destruct (val_beq chunk old_val2) eqn:Hbeq.

        - (* CAS succeeds: chunk = old_val2 *)
          apply val_beq_eq in Hbeq. subst old_val2.

          destruct Hwd3 as [tp3 Htp3].
          assert (inf_lexpr σ lexpr3 = Some tp3) as Hlexpr3_tp.
          { apply (lexpr_expr_typ_compat ρ _ stk e3); try done. }
          assert (∃ val, interp_lexpr lexpr3 mp = Some val) as [new_val Hinterp_new].
          { apply (lexpr_typcheck_well_defined σ _ _ tp3); try done. }
          pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ Htrnsl3 Hinterp_new) as Hexpr_step_e3.

          iApply (wp_cas_succ v e1 fld e2 e3 stk_id (symb_stk_to_stk_frm stk mp) l (trnsl_lval chunk) (trnsl_lval new_val) with "[Hstk Hl]"); try done.

          { assert (trnsl_lval (LitLoc l) = (lang.LitLoc l)) as Hloc_eq.
          - simpl. destruct l. simpl. done.
          - rewrite -> Hloc_eq in *. done. }

          { iFrame. }

          iNext. iIntros "[Hstk [Hl _]]".
          iApply "HΦ". iFrame.
          iExists (LitBool true).
          iSplitR; [done|].
          iSplitL "Hstk".
          + rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done.

          + iSplit.
            * iIntros "_".
              iSplitL.
              {
                iFrame.
                iPureIntro. split.
                { unfold LExpr_holds. simpl.
                  rewrite <- (fresh_var_trnsl_expr_invariant stk lvar_v e1 lexpr1 mp (LitBool true)); try done.
                  rewrite Hlexpr1. rewrite val_beq_refl. done. }
                { rewrite <- (fresh_var_trnsl_expr_invariant stk lvar_v e3 lexpr3 mp (LitBool true) Hfresh Htrnsl3). exact Hinterp_new. }
              }
              iPureIntro.
              unfold LExpr_holds. simpl. rewrite String.eqb_refl. rewrite val_beq_refl. done.

            * iIntros "%Hcontra". exfalso. apply Hcontra.
              unfold LExpr_holds. simpl.
              rewrite (interp_lexpr_stable old_chunk mp lvar_v (LitBool true) Hnotin).
              rewrite <- (fresh_var_trnsl_expr_invariant stk lvar_v e2 lexpr2 mp (LitBool true) Hfresh Htrnsl2).
              rewrite Hold Hl2. rewrite val_beq_refl. done.

        - (* CAS fails: chunk ≠ old_val2 *)
          apply val_beq_neq in Hbeq.

          iApply (wp_cas_fail v e1 fld e2 e3 stk_id (symb_stk_to_stk_frm stk mp) l (trnsl_lval old_val2) (trnsl_lval chunk) _ with "[Hstk Hl]"); try done.

          + assert (trnsl_lval (LitLoc l) = (lang.LitLoc l)) as Hloc_eq. { simpl. destruct l. simpl. done. }
          { rewrite -> Hloc_eq in *. done. }

          + assert (trnsl_lval chunk ≠ trnsl_lval old_val2) as Hneq2.
            { intros Heq. apply Hbeq. apply (trnsl_lval_injective _ _ Heq). }
            done.

          + iFrame.

          + iNext. iIntros "[Hstk [Hl _]]".
            iApply "HΦ".
            iFrame.
            iExists (LitBool false).
            iSplitR; [done|].
            iSplitL "Hstk".

            { rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done. }

            iSplit.
            * iIntros "%Hc". exfalso.
              unfold LExpr_holds in Hc. simpl in Hc.
              rewrite (interp_lexpr_stable old_chunk mp lvar_v (LitBool false) Hnotin) in Hc.
              rewrite <- (fresh_var_trnsl_expr_invariant stk lvar_v e2 lexpr2 mp (LitBool false) Hfresh Htrnsl2) in Hc.
              rewrite Hold Hl2 in Hc.
              injection Hc as Hc.
              apply val_beq_eq in Hc. apply Hbeq. exact Hc.

            * iIntros "_".
              iSplitL.
              {
                iFrame.
                iPureIntro. split.
                { unfold LExpr_holds. simpl.
                  rewrite <- (fresh_var_trnsl_expr_invariant stk lvar_v e1 lexpr1 mp (LitBool false)); try done.
                  rewrite Hlexpr1. rewrite val_beq_refl. done. }
                { rewrite (interp_lexpr_stable old_chunk mp lvar_v (LitBool false) Hnotin). exact Hold. }
              }
              iPureIntro. unfold LExpr_holds; simpl.
              apply f_equal. rewrite String.eqb_refl. rewrite val_beq_refl. done.
      }

      4 : {
        (* WEAKENING *)
        apply assertion_entails_sound in H0, H1.
        unfold entails in *.
        unfold trnsl_hoare_triple. simpl.
        specialize H0 with stk_id mp. specialize (H0 Henv).
        destruct H0 as [P' [P [HP' [HP HP_ent_P']]]].

        specialize H1 with stk_id mp. specialize (H1 Henv).
        destruct H1 as [Q [Q' [HQ [HQ' HQ_ent_Q']]]].
        rewrite HP' HQ'.

        destruct (trnsl_stmt c) eqn:HtrnslStmt; try done.

        -
        iPoseProof ("IH" with "[%] [%]") as "IH1"; try done.
        iSpecialize ("IH1" $! mp).
        iEval (unfold trnsl_hoare_triple) in "IH1".
        rewrite HP HQ.
        iIntros "HP'".
        iPoseProof ("IH1" with "[%] [HP']") as "HII"; try iFrame; try done.
        { iApply HP_ent_P'. iFrame. }
        iDestruct  "HII" as ">HQ" . iModIntro.
        iApply HQ_ent_Q'.
        iFrame.

        -
        iPoseProof ("IH" with "[%] [%]") as "IH1"; try done.
        iSpecialize ("IH1" $! mp).
        iEval (unfold trnsl_hoare_triple) in "IH1".
        rewrite HP HQ.
        iIntros (Φ). iModIntro. iIntros "HP' HΦ".
        iApply ("IH1" with "[%] [HP']"); try iFrame; try done.
          + iApply HP_ent_P'. iFrame.
          + iNext. iIntros "HQ". iApply "HΦ". iApply HQ_ent_Q'. iFrame.
      }

      2 : {
        (* IF *)
        inversion Hwelldef; subst e0 s0 s3.
        iPoseProof ("IH" with "[%]") as "IH'"; try done.
        iPoseProof ("IH1" with "[%]") as "IH1'"; try done.
        iClear "IH IH1".
        unfold trnsl_hoare_triple. simpl.

        pose proof (lexpr_expr_typ_compat _ _ _ _ _ _ H1 H H0) as Hlexpr_type_inf.
          pose proof (lexpr_typcheck_well_defined _ _ _ _ Henv Hlexpr_type_inf) as Hinterp_lexpr.
          destruct Hinterp_lexpr as [val0 Hinterp_lexpr].
          pose proof (interp_lexpr_typ_compat _ _ _ _ _ Henv Hlexpr_type_inf Hinterp_lexpr) as Hle_typ.
          unfold typeOf in Hle_typ. destruct (trnsl_lval val0) as [ | | | |[]] eqn:Hle_val; try done.
          unfold trnsl_lval in Hle_val. destruct (val0) eqn: Hle_val'; try done.

        destruct (trnsl_stmt s1) eqn:Hs1, (trnsl_stmt s2) eqn:Hs2; try done.

        - destruct b0.

          + setoid_rewrite trnsl_assertion_unfold. iIntros "[Hstk Hu]".
            iPoseProof ("IH'" with "[%] [%] [Hstk Hu]") as "Hpost".
            { done. }
            { done. }
            { iFrame. iPureIntro. unfold LExpr_holds. rewrite Hinterp_lexpr. done. }
            iMod "Hpost" as "HQ". iModIntro. iFrame.

          + setoid_rewrite trnsl_assertion_unfold. iIntros "[Hstk Hu]".
            iPoseProof ("IH1'" with "[%] [%] [Hstk Hu]") as "Hpost".
            { done. }
            { done. }
            { iFrame. iPureIntro. unfold LExpr_holds. simpl. rewrite Hinterp_lexpr. done. }
            iMod "Hpost" as "HQ". iModIntro. iFrame.
        - iIntros (Φ). iModIntro. setoid_rewrite trnsl_assertion_unfold. iIntros "[Hstk Hu] HΦ".
          destruct b0.
          + iApply (wp_if_t e (RTSkipS stk_id) (to_rtstmt stk_id s) stk_id (symb_stk_to_stk_frm stk1 mp) (trnsl_assertion p stk_id mp) (trnsl_assertion Q stk_id mp) (lang.LitUnit) (trnsl_mask mask) with "[IH'] [IH' Hstk Hu] [HΦ]"); try iFrame.
            *  apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool true) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk Hu] HΦ'".
            setoid_rewrite trnsl_assertion_unfold.
            iPoseProof ("IH'" with "[%] [%] [Hstk Hu]") as "HQ".
            { done. }
            { done. }
            { iFrame. iPureIntro. unfold LExpr_holds. rewrite Hinterp_lexpr. done.  }
            iMod "HQ" as "HQ". iEval (rewrite <- (trnsl_assertion_unfold Q stk_id mp)) in "HQ".
            iApply (wp_skip (trnsl_assertion Q stk_id mp) with "HQ").
            iNext. iIntros "[HQ Hcred]". iApply "HΦ'".
            iEval (rewrite (trnsl_assertion_unfold Q stk_id mp)) in "HQ". iExact "HQ".

            * setoid_rewrite trnsl_assertion_unfold. iFrame.

            * iNext. iIntros "HQ". iApply "HΦ".
              iEval (rewrite (trnsl_assertion_unfold Q stk_id mp)) in "HQ". iFrame.

          + iApply (wp_if_f e (RTSkipS stk_id) (to_rtstmt stk_id s) stk_id (symb_stk_to_stk_frm stk1 mp) (trnsl_assertion p stk_id mp) (trnsl_assertion Q stk_id mp) (lang.LitUnit) (trnsl_mask mask) with "[IH'] [IH' Hstk Hu] [HΦ]"); try iFrame.
            * apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool false) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk Hu] HΦ'".
            setoid_rewrite trnsl_assertion_unfold.
            iPoseProof ("IH1'" with "[%] [%] [Hstk Hu]") as "HQ".
            { done. }
            { done. }
            { iFrame. iPureIntro. unfold LExpr_holds. simpl. rewrite Hinterp_lexpr. done.  }
            iApply "HQ". iNext.
            iIntros "HQ". iApply "HΦ'". iFrame.

            * setoid_rewrite trnsl_assertion_unfold. iFrame.

            * iNext. iIntros "HQ". iApply "HΦ".
              iEval (rewrite (trnsl_assertion_unfold Q stk_id mp)) in "HQ". iFrame.

        - iIntros (Φ). iModIntro. setoid_rewrite trnsl_assertion_unfold. iIntros "[Hstk Hu] HΦ".
          destruct b0.
          + iApply (wp_if_t e (to_rtstmt stk_id s) (RTSkipS stk_id) stk_id (symb_stk_to_stk_frm stk1 mp) (trnsl_assertion p stk_id mp) (trnsl_assertion Q stk_id mp) (lang.LitUnit) (trnsl_mask mask) with "[IH'] [IH' Hstk Hu] [HΦ]"); try iFrame.
            *  apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool true) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk Hu] HΦ'".
            setoid_rewrite trnsl_assertion_unfold.
            iPoseProof ("IH'" with "[%] [%] [Hstk Hu]") as "HQ".
            { done. }
            { done. }
            { iFrame. iPureIntro. unfold LExpr_holds. rewrite Hinterp_lexpr. done.  }
            iApply "HQ". iNext. iIntros "HQ". iApply "HΦ'". iFrame.

            * setoid_rewrite trnsl_assertion_unfold. iFrame.

            * iNext. iIntros "HQ". iApply "HΦ".
              iEval (rewrite (trnsl_assertion_unfold Q stk_id mp)) in "HQ". iFrame.

          + iApply (wp_if_f e (to_rtstmt stk_id s) (RTSkipS stk_id) stk_id (symb_stk_to_stk_frm stk1 mp) (trnsl_assertion p stk_id mp) (trnsl_assertion Q stk_id mp) (lang.LitUnit) (trnsl_mask mask) with "[IH'] [IH' Hstk Hu] [HΦ]"); try iFrame.
            * apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool false) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk Hu] HΦ'".
            setoid_rewrite trnsl_assertion_unfold.
            iPoseProof ("IH1'" with "[%] [%] [Hstk Hu]") as "HQ".
            { done. }
            { done. }
            { iFrame. iPureIntro. unfold LExpr_holds. simpl. rewrite Hinterp_lexpr. done. }

            iMod "HQ" as "HQ". iEval (rewrite <- (trnsl_assertion_unfold Q stk_id mp)) in "HQ".
            iApply (wp_skip (trnsl_assertion Q stk_id mp) with "HQ").
            iNext. iIntros "[HQ Hcred]". iApply "HΦ'".
            iEval (rewrite (trnsl_assertion_unfold Q stk_id mp)) in "HQ". iExact "HQ".

            * setoid_rewrite trnsl_assertion_unfold. iFrame.
            * iNext. iIntros "HQ". iApply "HΦ".
              iEval (rewrite (trnsl_assertion_unfold Q stk_id mp)) in "HQ". iFrame.

        - iIntros (Φ). iModIntro. setoid_rewrite trnsl_assertion_unfold. iIntros "[Hstk Hu] HΦ".
          destruct b0.
          + iApply (wp_if_t e (to_rtstmt stk_id s) (to_rtstmt stk_id s0) stk_id (symb_stk_to_stk_frm stk1 mp) (trnsl_assertion p stk_id mp) (trnsl_assertion Q stk_id mp) (lang.LitUnit) (trnsl_mask mask) with "[IH'] [IH' Hstk Hu] [HΦ]"); try iFrame.
            *  apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool true) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk Hu] HΦ'".
            setoid_rewrite trnsl_assertion_unfold.
            iPoseProof ("IH'" with "[%] [%] [Hstk Hu]") as "HQ".
            { done. }
            { done. }
            { iFrame. iPureIntro. unfold LExpr_holds. rewrite Hinterp_lexpr. done.  }
            iApply "HQ". iNext. iIntros "HQ". iApply "HΦ'". iFrame.

            * setoid_rewrite trnsl_assertion_unfold. iFrame.

            * iNext. iIntros "HQ". iApply "HΦ".
              iEval (rewrite (trnsl_assertion_unfold Q stk_id mp)) in "HQ". iFrame.

          + iApply (wp_if_f e (to_rtstmt stk_id s) (to_rtstmt stk_id s0) stk_id (symb_stk_to_stk_frm stk1 mp) (trnsl_assertion p stk_id mp) (trnsl_assertion Q stk_id mp) (lang.LitUnit) (trnsl_mask mask) with "[IH'] [IH' Hstk Hu] [HΦ]"); try iFrame.
            * apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool false) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk Hu] HΦ'".
            setoid_rewrite trnsl_assertion_unfold.
            iPoseProof ("IH1'" with "[%] [%] [Hstk Hu]") as "HQ".
            { done. }
            { done. }
            { iFrame. iPureIntro. unfold LExpr_holds. simpl. rewrite Hinterp_lexpr. done. }
            iApply "HQ". iNext. iIntros "HQ". iApply "HΦ'". iFrame.

            * setoid_rewrite trnsl_assertion_unfold. iFrame.

            * iNext. iIntros "HQ". iApply "HΦ".
              iEval (rewrite (trnsl_assertion_unfold Q stk_id mp)) in "HQ". iFrame.

      }
      
      1 : {
        (* CALL *)
        unfold trnsl_hoare_triple. simpl (trnsl_stmt (Call x proc_name args)). case_match; try discriminate.
        pose proof H0 as H0'.
        apply Hwf.(pwf_proc_args_unique) in H0'.
        pose proof H0 as H0_rv_fresh.
        apply Hwf.(pwf_proc_ret_val_fresh) in H0_rv_fresh.
        pose proof H0 as H0_locals_unique.
        apply Hwf.(pwf_proc_locals_unique) in H0_locals_unique.
        pose proof H0 as H0_args_locals_disjoint.
        apply Hwf.(pwf_proc_args_locals_disjoint) in H0_args_locals_disjoint.
        pose proof H0 as H0_rv_declared.
        apply Hwf.(pwf_proc_ret_val_declared) in H0_rv_declared.
        pose proof H0 as Hspec_StackFree.
        apply Hwf.(pwf_proc_stack_free) in Hspec_StackFree.
        pose proof (stmt_well_defined_call_ret_typed ρ x proc_name args proc_record Hwelldef H0) as Hret_wt.

        inversion Hwelldef; subst ρ0 v proc args0.

        assert (exists arg_vals, Forall2 (fun e v => expr_step e (symb_stk_to_stk_frm stk mp) (Val v)) args arg_vals) as Harg_vals.

        {
          (* Save stk_type_compat before clearing *)
          assert (Hstk_compat: stk_type_compat ρ σ stk) by assumption.
          (* Prove existence of arg_vals *)
          clear Hwelldef H1 H6 H15 H16.
          clear subst_map.
          clear H5.
          clear H12.
          revert lexprs H2 H14.
          induction args as [| a args IH]; intros lexprs H2 H12.
          - simpl in H2. destruct lexprs; [ | discriminate ]. exists nil. constructor.
          - simpl in H2. destruct lexprs as [| l lexprs']; [ discriminate | ].
            (* heads must match and tails must match *)
            simpl in H2. injection H2 as Hhd Htl.
            inversion H12 as [| a' args' Hwd H12']. clear H12; subst.
            (* interp_lexpr either yields a value or None *)
            destruct (interp_lexpr l mp) as [v | ] eqn:He.
            + (* Some v: build the head step and recurse for the tail *)
              specialize (IH lexprs' Htl H12') as [arg_vals' Hforall'].
              exists ((trnsl_lval v) :: arg_vals').
              apply Forall2_cons. split.
              * apply trnsl_expr_interp_lexpr_compatibility with (lexpr:=l); try assumption.
              * exact Hforall'.
            + (* None: contradict well-definedness using expr_interp_well_defined *)
              eapply (expr_interp_well_defined ρ σ stk a mp l Hstk_compat Henv) in Hhd; [ | exact He ].
              contradiction.
        }

        destruct Harg_vals as [arg_vals Harg_vals].

        assert (Forall2 (λ expr val, interp_lexpr expr mp = Some (trnsl_val val)) lexprs arg_vals) as Hlexprs_arg_vals.
          {
            clear Hwelldef H1 H5 H6 H12 H14 H15 H16 subst_map.
            revert args arg_vals H2 Harg_vals.
            induction lexprs as [| le lexprs IH]; intros args arg_vals H2 Harg_vals.
            - destruct args; [| discriminate]. inversion Harg_vals. constructor.

            - destruct args; [discriminate |]. simpl in H2. injection H2 as Hhd Htl.
              inversion Harg_vals as [ | x0 y l l' HhdExprStep HtlExprStep ]; subst.
              specialize (IH args l' Htl HtlExprStep).
              apply Forall2_cons. split.
              + apply (trnsl_expr_interp_lexpr_compatibility2 stk e); try simpl; try done. rewrite trnsl_lval_trnsl_val_inverse. done.

              + done.
          }

        simpl in *.
        destruct proc_record as [proc_args proc_locals proc_pre proc_post proc_body] eqn:Hproc_record.

        assert (proc_entry = Proc proc_args proc_locals proc_pre proc_post proc_body) as Hpe.
        { rewrite H0 in H11. injection H11 as <-. done. }
        rewrite Hpe in H15.

        assert (Forall2 (λ arg_decl val, typeOf val = snd arg_decl)
                  (proc_args_of (Proc proc_args proc_locals proc_pre proc_post proc_body)) arg_vals)
          as Harg_vals_typed.
        { apply (proc_call_args_typed_result ρ σ stk mp args lexprs arg_vals
            (Proc proc_args proc_locals proc_pre proc_post proc_body) H3 Henv H15 H2 Hlexprs_arg_vals). }

        set (trnsl_assertion (subst proc_pre subst_map) stk_id mp) as u1.

        assert (trnsl_assertion (subst proc_pre subst_map) stk_id mp ≡ u1) as Hproc_pre.
            { subst u1; reflexivity. }

        destruct (trnsl_stmt (proc_body)) eqn:Hproc_body;  try discriminate.

        
        {
          (* proc_body = Skip *)
        inversion H6; subst s.
        iIntros (Φ). iModIntro. setoid_rewrite trnsl_assertion_unfold.

        iIntros "[Hstk Hu1] HΦ".

        set (subst_map' := @list_to_map var LExpr (gmap var LExpr) _ _ (zip (proc_args).*1 (map (λ val, LVal (trnsl_val val)) arg_vals))).

          set ((trnsl_assertion (subst proc_pre subst_map') stk_id mp)) as proc_frame_pre.
          set (fun ret_val => trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id mp) as proc_frame_post.
          (* Threads the type fact all_proc_specs_valid_iris's WP conclusion
             promises for "#ret_val" (see proc_ret_typ_opt's own comment)
             through wp_call's own operational return boundary -- keeping it
             separate from proc_frame_post itself (rather than baking it in)
             so trnsl_assertion_w_lexpr_subst_r's bridge below stays exactly
             as it always was. *)
          set (fun ret_val => proc_frame_post ret_val ∗
            ⌜proc_ret_typ_opt proc_record = Some (typeOf ret_val)⌝)%I as proc_frame_post_typed.

        iApply (wp_call _ _ _ _ _ _ (lang.Proc proc_name proc_args proc_locals _) _ u1 proc_frame_post_typed with "[] [Hstk Hu1]"); try iFrame; try done.

          {
            (* Showing procedure contract holds, via the ambient (Löb-guarded) Calls fact *)
            iNext.
            iIntros (stk_id' stk_frm') "%HlocalsDef". destruct HlocalsDef as [HlocalsDef [Hrv_val Hdom_val]]. simpl in *.

            iPoseProof ("Calls" $! proc_name (Proc proc_args proc_locals proc_pre proc_post proc_body) arg_vals with "[%]") as "Calls'".
            { done. }
            iPoseProof ("Calls'" with "[%]") as "Hproc".
            { exact H0. }

            iSpecialize ("Hproc" $! proc_frame_pre proc_frame_post_typed stk_id' stk_frm' mp lang.SkipS mask).

            iSpecialize ("Hproc" with "[%]"). { exact Henv. }

            iSpecialize ("Hproc" with "[%]"). { exact Hmask_sub. }

            iSpecialize ("Hproc" with "[%]"). { exact (proj2 H5). }

            assert ((∀ v : var * typ, v ∈ proc_args_of (Proc proc_args proc_locals proc_pre proc_post proc_body) → is_Some (locals stk_frm' !! v.1))) as HIsSome.

            {
              intros v Hin. apply elem_of_list_lookup_1 in Hin as [i Hi].
              assert (proc_args.*1 !! i = Some v.1) as Hi'.
              { rewrite list_lookup_fmap. rewrite Hi. done.   }
              simpl in HlocalsDef.
              eapply (Forall2_lookup_l _ proc_args.*1 arg_vals i v.1 HlocalsDef) in Hi' as [val [Hval Hlookup]]. by eexists.
            }

          iSpecialize ("Hproc" with "[%]"). { exact HIsSome. }

          simpl in HlocalsDef.
          iSpecialize ("Hproc" with "[%]"). { exact HlocalsDef. }

          simpl in Hrv_val. simpl in Hdom_val.
          iSpecialize ("Hproc" with "[%]").
          { intros v tp Hin. destruct (Hrv_val v tp Hin) as [val [Hlk Hty]].
            exists val. split; [exact Hlk |]. apply typeOf_val_has_typ. exact Hty. }
          iSpecialize ("Hproc" with "[%]"). { exact Hdom_val. }

          assert (trnsl_assertion (subst proc_pre subst_map') stk_id mp ≡ proc_frame_pre) as Hproc_frame_pre.
          { subst proc_frame_pre. reflexivity. }

          have Hmr_dom' : ∀ v, v ∈ dom subst_map' → ¬ is_reserved v.
          { intros v Hv. apply elem_of_dom in Hv as [e He].
            apply elem_of_list_to_map_2 in He. apply elem_of_zip_l in He.
            exact (proj1 (Forall_forall _ _)
                     (Hwf.(pwf_proc_args_not_reserved) proc_name
                        (Proc proc_args proc_locals proc_pre proc_post proc_body) H0) v He). }

          have Hproc_frame_pre' : trnsl_assertion (subst proc_pre subst_map') stk_id' mp ≡ proc_frame_pre.
          { etransitivity.
            - symmetry. apply (stack_free_assertion_trnsl _ stk_id stk_id' mp).
              apply (stack_free_assertion_subst Hwf _ _ Hmr_dom').
              destruct Hspec_StackFree; done.
            - exact Hproc_frame_pre. }

          iSpecialize ("Hproc" with "[%]"). { exact Harg_vals_typed. }

          iSpecialize ("Hproc" with "[%]"). { exact Hproc_frame_pre'. }

          have Hproc_frame_post_all : ∀ ret_val,
              (trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id' mp ∗
               ⌜proc_ret_typ_opt (Proc proc_args proc_locals proc_pre proc_post proc_body) = Some (typeOf ret_val)⌝)%I ≡ proc_frame_post_typed ret_val.
          { intros ret_val. rewrite -Hproc_record. rewrite /proc_frame_post_typed /proc_frame_post. f_equiv. etransitivity.
            - symmetry. apply (stack_free_assertion_trnsl _ stk_id stk_id' mp).
              apply (stack_free_assertion_subst Hwf _ _
                       (dom_insert_not_reserved subst_map' "#ret_val" (LVal (trnsl_val ret_val))
                          ret_val_not_reserved Hmr_dom')).
              destruct Hspec_StackFree; done.
            - reflexivity. }

          iSpecialize ("Hproc" with "[%]"). { exact Hproc_frame_post_all. }

          assert (trnsl_stmt proc_body = Some' lang.SkipS
            ∨ trnsl_stmt proc_body = None' ∧ lang.SkipS = lang.SkipS) as Hproc_body'. { right. split; try done. }

          iSpecialize ("Hproc" with "[%]"). { exact Hproc_body'. }

          iIntros (Φ'). iModIntro.
          iIntros "[Hstk Hu1] HΦ".

          iApply ("Hproc" with "[Hstk Hu1]").

          {
            iFrame.

            have Hmr1 : subst_map_avoids_reserved (list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr).
            { apply subst_map_avoids_reserved_of_lexprs.
              - exact (Hwf.(pwf_proc_args_not_reserved) proc_name
                         (Proc proc_args proc_locals proc_pre proc_post proc_body) H0).
              - exact (proj1 H5). }
            have Hmr2 : subst_map_avoids_reserved
              (list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr).
            { apply subst_map_avoids_reserved_of_lexprs.
              - exact (Hwf.(pwf_proc_args_not_reserved) proc_name
                         (Proc proc_args proc_locals proc_pre proc_post proc_body) H0).
              - exact (lval_list_no_reserved arg_vals trnsl_val). }
            have HbA_M1 : assertion_exists_binders proc_pre ##
              (dom (list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr) ∪
               lexpr_map_fvars (list_to_map (zip proc_args.*1 lexprs))).
            { apply reserved_disjoint_dom.
              - exact (proj1 (Hwf.(pwf_proc_binders_reserved) proc_name _ H0)).
              - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
                  [exact (proj1 Hmr1 v Hv) | exact (proj2 Hmr1 v Hv)]. }
            have HbA_M2 : assertion_exists_binders proc_pre ##
              (dom (list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr) ∪
               lexpr_map_fvars (list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)))).
            { apply reserved_disjoint_dom.
              - exact (proj1 (Hwf.(pwf_proc_binders_reserved) proc_name _ H0)).
              - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
                  [exact (proj1 Hmr2 v Hv) | exact (proj2 Hmr2 v Hv)]. }
            have HfvA : ∀ v, v ∈ assertion_lexpr_fvars proc_pre →
              v ∈ dom (list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr) ∨ is_reserved v.
            { have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ HlocalsDef. have := Forall2_length _ _ _ Hlexprs_arg_vals. lia. }
              intros v Hv.
              destruct (proj1 (Hwf.(pwf_proc_fvars_bounded) proc_name _ H0) v Hv) as [Hin | Hin].
              - left. rewrite dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). exact Hin.
              - right. exact (proj1 (Hwf.(pwf_proc_binders_reserved) proc_name _ H0) v Hin). }
            have HdomEq : dom (list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr) = dom (list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr).
            { have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ HlocalsDef. have := Forall2_length _ _ _ Hlexprs_arg_vals. lia. }
              have Hlen2 : length proc_args.*1 ≤ length (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals). { rewrite map_length. have := Forall2_length _ _ _ HlocalsDef. lia. }
              rewrite !dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). rewrite (fst_zip _ _ Hlen2). reflexivity. }
            pose proof (trnsl_assertion_w_lexpr_subst proc_pre lexprs proc_args.*1 arg_vals stk_id mp u1 proc_frame_pre
              Hwf (proj1 Hspec_StackFree)
              HbA_M1 HbA_M2
              HfvA HdomEq Hmr1 Hmr2
              Hlexprs_arg_vals Hproc_pre Hproc_frame_pre) as Himpl.
            iApply Himpl. iFrame.
          }


          iNext. iExact "HΦ".
          }

          { iDestruct (all_proc_tbl_chunks_elem proc_name (Proc proc_args proc_locals proc_pre proc_post proc_body) H0 with "HprocTbl") as "Hproc_tbl".
            iEval (simpl; rewrite Hproc_body) in "Hproc_tbl".
            iFrame "Hproc_tbl". setoid_rewrite <- trnsl_assertion_unfold. iFrame. }

          {
            iNext. iIntros "[%ret_val [Hstk [[Hq %Htyp2] _]]]".

            have Hproc_frame_post : trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id mp ≡ proc_frame_post ret_val.
            { reflexivity. }

            have Hret_typ_match : typ_val_match (ρ x) (trnsl_val ret_val).
            { apply typeOf_trnsl_val_match.
              unfold proc_call_ret_well_typed in Hret_wt.
              rewrite Hproc_record in Htyp2.
              rewrite Htyp2 in Hret_wt.
              exact (eq_sym Hret_wt). }

            iApply "HΦ". iFrame. iExists (trnsl_val ret_val).
            iSplitR; [iPureIntro; exact Hret_typ_match|].

            set (trnsl_assertion (subst proc_post (<["#ret_val":=LVar lvar_x]> subst_map)) stk_id
            (λ x0 : lvar, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0)) as u.

            assert ((trnsl_assertion (subst proc_post (<["#ret_val":=LVar lvar_x]> subst_map)) stk_id
            (λ x0 : lvar, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0)) ≡ u) as Hpost.
            { subst u; reflexivity. }


            iSplitR "Hq".
            { rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done. rewrite trnsl_lval_trnsl_val_inverse. iFrame. }

            { have Hmr1_base : subst_map_avoids_reserved (list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr).
              { apply subst_map_avoids_reserved_of_lexprs.
                - exact (Hwf.(pwf_proc_args_not_reserved) proc_name
                           (Proc proc_args proc_locals proc_pre proc_post proc_body) H0).
                - exact (proj1 H5). }
              have Hmr2_base : subst_map_avoids_reserved
                (list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr).
              { apply subst_map_avoids_reserved_of_lexprs.
                - exact (Hwf.(pwf_proc_args_not_reserved) proc_name
                           (Proc proc_args proc_locals proc_pre proc_post proc_body) H0).
                - exact (lval_list_no_reserved arg_vals trnsl_val). }
              have Hlvar_x_ok : ¬ is_reserved lvar_x := H4.
              have Hargs_ok : Forall (λ a, ¬ is_reserved a) proc_args.*1 :=
                Hwf.(pwf_proc_args_not_reserved) proc_name
                  (Proc proc_args proc_locals proc_pre proc_post proc_body) H0.
              have Hmr1 : subst_map_avoids_reserved (<["#ret_val":=LVar lvar_x]>(list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr)).
              { apply subst_map_avoids_reserved_insert.
                - exact ret_val_not_reserved.
                - intros v Hv. simpl in Hv. apply elem_of_singleton in Hv as ->. exact Hlvar_x_ok.
                - exact Hmr1_base. }
              have Hmr2 : subst_map_avoids_reserved (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr)).
              { apply subst_map_avoids_reserved_insert.
                - exact ret_val_not_reserved.
                - intros v Hv. simpl in Hv. set_solver.
                - exact Hmr2_base. }
              have HbA_M1 : assertion_exists_binders proc_post ##
                (dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr)) ∪
                 lexpr_map_fvars (<["#ret_val":=LVar lvar_x]>(list_to_map (zip proc_args.*1 lexprs)))).
              { apply reserved_disjoint_dom.
                - exact (proj2 (Hwf.(pwf_proc_binders_reserved) proc_name _ H0)).
                - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
                    [exact (proj1 Hmr1 v Hv) | exact (proj2 Hmr1 v Hv)]. }
              have HbA_M2 : assertion_exists_binders proc_post ##
                (dom (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr)) ∪
                 lexpr_map_fvars (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))))).
              { apply reserved_disjoint_dom.
                - exact (proj2 (Hwf.(pwf_proc_binders_reserved) proc_name _ H0)).
                - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
                    [exact (proj1 Hmr2 v Hv) | exact (proj2 Hmr2 v Hv)]. }
              have HfvA : ∀ v, v ∈ assertion_lexpr_fvars proc_post →
                v ∈ dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr)) ∨ is_reserved v.
              { have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ Hlexprs_arg_vals. have := Forall2_length _ _ _ Harg_vals. have := @length_fmap _ _ fst proc_args. simpl in *. lia. }
                intros v Hv.
                destruct (proj2 (Hwf.(pwf_proc_fvars_bounded) proc_name _ H0) v Hv) as [Hin | Hin].
                - left. rewrite dom_insert_L. rewrite dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). exact Hin.
                - right. exact (proj2 (Hwf.(pwf_proc_binders_reserved) proc_name _ H0) v Hin). }
              have HdomEq : dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr)) = dom (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr)).
              { have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ Hlexprs_arg_vals. have := Forall2_length _ _ _ Harg_vals. have := @length_fmap _ _ fst proc_args. simpl in *. lia. }
                have Hlen2 : length proc_args.*1 ≤ length (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals). { rewrite map_length. have := Forall2_length _ _ _ Harg_vals. have := @length_fmap _ _ fst proc_args. simpl in *. lia. }
                rewrite !dom_insert_L. rewrite !dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). rewrite (fst_zip _ _ Hlen2). reflexivity. }
              pose proof (trnsl_assertion_w_lexpr_subst_r proc_post lexprs proc_args.*1 arg_vals lvar_x ret_val stk stk_id mp u (proc_frame_post ret_val)
                Hwf (proj2 Hspec_StackFree)
                HbA_M1 HbA_M2
                HfvA HdomEq Hmr1 Hmr2
                (fresh_lvar_not_in_lexpr_map_fvars_zip stk args lexprs proc_args.*1 lvar_x H2 H)
                Hlvar_x_ok Hargs_ok
                H Hlexprs_arg_vals Hpost Hproc_frame_post) as Himpl.
              setoid_rewrite <- trnsl_assertion_unfold. iApply Himpl. iFrame. }
          }
        }

        { (* proc body is not well-formed: ruled out by proc_bodies_translate,
             since a registered procedure's body always translates. *)
          exfalso. exact (Hpbt proc_name
            (Proc proc_args proc_locals proc_pre proc_post proc_body) H0 Hproc_body).
        }

        {
          (* proc_body != Skip *)
        inversion H6; subst s.
        iIntros (Φ). iModIntro.
        setoid_rewrite trnsl_assertion_unfold.

        iIntros "[Hstk Hu1] HΦ".

        set (subst_map' := @list_to_map var LExpr (gmap var LExpr) _ _ (zip (proc_args).*1 (map (λ val, LVal (trnsl_val val)) arg_vals))).

          set (trnsl_assertion (subst proc_pre subst_map') stk_id mp) as proc_frame_pre.
          assert ((trnsl_assertion (subst proc_pre subst_map') stk_id mp) ≡ proc_frame_pre) as Hproc_frame_pre. { subst proc_frame_pre; reflexivity. }

          set (fun ret_val => trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id mp) as proc_frame_post.
          set (fun ret_val => proc_frame_post ret_val ∗
            ⌜proc_ret_typ_opt proc_record = Some (typeOf ret_val)⌝)%I as proc_frame_post_typed.

        iApply (wp_call _ _ _ _ _ _ (lang.Proc proc_name proc_args proc_locals _) _ u1 proc_frame_post_typed with "[] [Hstk Hu1]"); try iFrame; try done.

          {
            (* Showing procedure contract holds, via the ambient (Löb-guarded) Calls fact *)
            iNext.
            iIntros (stk_id' stk_frm') "%HlocalsDef". destruct HlocalsDef as [HlocalsDef [Hrv_val Hdom_val]]. simpl in *.

            iPoseProof ("Calls" $! proc_name (Proc proc_args proc_locals proc_pre proc_post proc_body) arg_vals with "[%]") as "Calls'".
            { done. }
            iPoseProof ("Calls'" with "[%]") as "Hproc".
            { exact H0. }

            iSpecialize ("Hproc" $! proc_frame_pre proc_frame_post_typed stk_id' stk_frm' mp s0 mask).

            iSpecialize ("Hproc" with "[%]"). { exact Henv. }

            iSpecialize ("Hproc" with "[%]"). { exact Hmask_sub. }

            iSpecialize ("Hproc" with "[%]"). { exact (proj2 H5). }

            assert ((∀ v : var * typ, v ∈ proc_args_of (Proc proc_args proc_locals proc_pre proc_post proc_body) → is_Some (locals stk_frm' !! v.1))) as HIsSome.

            {
              intros v Hin. apply elem_of_list_lookup_1 in Hin as [i Hi].
              assert (proc_args.*1 !! i = Some v.1) as Hi'.
              { rewrite list_lookup_fmap. rewrite Hi. done.   }
              simpl in HlocalsDef.
              eapply (Forall2_lookup_l _ proc_args.*1 arg_vals i v.1 HlocalsDef) in Hi' as [val [Hval Hlookup]]. by eexists.
            }

          iSpecialize ("Hproc" with "[%]"). { exact HIsSome. }

          simpl in HlocalsDef.
          iSpecialize ("Hproc" with "[%]"). { exact HlocalsDef. }

          simpl in Hrv_val. simpl in Hdom_val.
          iSpecialize ("Hproc" with "[%]").
          { intros v tp Hin. destruct (Hrv_val v tp Hin) as [val [Hlk Hty]].
            exists val. split; [exact Hlk |]. apply typeOf_val_has_typ. exact Hty. }
          iSpecialize ("Hproc" with "[%]"). { exact Hdom_val. }

          have Hmr_dom' : ∀ v, v ∈ dom subst_map' → ¬ is_reserved v.
          { intros v Hv. apply elem_of_dom in Hv as [e He].
            apply elem_of_list_to_map_2 in He. apply elem_of_zip_l in He.
            exact (proj1 (Forall_forall _ _)
                     (Hwf.(pwf_proc_args_not_reserved) proc_name
                        (Proc proc_args proc_locals proc_pre proc_post proc_body) H0) v He). }

          have Hproc_frame_pre' : trnsl_assertion (subst proc_pre subst_map') stk_id' mp ≡ proc_frame_pre.
          { etransitivity.
            - symmetry. apply (stack_free_assertion_trnsl _ stk_id stk_id' mp).
              apply (stack_free_assertion_subst Hwf _ _ Hmr_dom').
              destruct Hspec_StackFree; done.
            - exact Hproc_frame_pre. }

          iSpecialize ("Hproc" with "[%]"). { exact Harg_vals_typed. }

          iSpecialize ("Hproc" with "[%]"). { exact Hproc_frame_pre'. }

          have Hproc_frame_post_all : ∀ ret_val,
              (trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id' mp ∗
               ⌜proc_ret_typ_opt (Proc proc_args proc_locals proc_pre proc_post proc_body) = Some (typeOf ret_val)⌝)%I ≡ proc_frame_post_typed ret_val.
          { intros ret_val. rewrite -Hproc_record. rewrite /proc_frame_post_typed /proc_frame_post. f_equiv. etransitivity.
            - symmetry. apply (stack_free_assertion_trnsl _ stk_id stk_id' mp).
              apply (stack_free_assertion_subst Hwf _ _
                       (dom_insert_not_reserved subst_map' "#ret_val" (LVal (trnsl_val ret_val))
                          ret_val_not_reserved Hmr_dom')).
              destruct Hspec_StackFree; done.
            - reflexivity. }

          iSpecialize ("Hproc" with "[%]"). { exact Hproc_frame_post_all. }

          assert (trnsl_stmt proc_body = Some' s0
            ∨ trnsl_stmt proc_body = None' ∧ s0 = lang.SkipS) as Hproc_body'. { left. try done. }

          iSpecialize ("Hproc" with "[%]"). { exact Hproc_body'. }

          iIntros (Φ'). iModIntro.
          iIntros "[Hstk Hu1] HΦ".

          iApply ("Hproc" with "[Hstk Hu1]").

          {
            iFrame.
            have Hmr1 : subst_map_avoids_reserved (list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr).
            { apply subst_map_avoids_reserved_of_lexprs.
              - exact (Hwf.(pwf_proc_args_not_reserved) proc_name
                         (Proc proc_args proc_locals proc_pre proc_post proc_body) H0).
              - exact (proj1 H5). }
            have Hmr2 : subst_map_avoids_reserved
              (list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr).
            { apply subst_map_avoids_reserved_of_lexprs.
              - exact (Hwf.(pwf_proc_args_not_reserved) proc_name
                         (Proc proc_args proc_locals proc_pre proc_post proc_body) H0).
              - exact (lval_list_no_reserved arg_vals trnsl_val). }
            have HbA_M1 : assertion_exists_binders proc_pre ##
              (dom (list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr) ∪
               lexpr_map_fvars (list_to_map (zip proc_args.*1 lexprs))).
            { apply reserved_disjoint_dom.
              - exact (proj1 (Hwf.(pwf_proc_binders_reserved) proc_name _ H0)).
              - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
                  [exact (proj1 Hmr1 v Hv) | exact (proj2 Hmr1 v Hv)]. }
            have HbA_M2 : assertion_exists_binders proc_pre ##
              (dom (list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr) ∪
               lexpr_map_fvars (list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)))).
            { apply reserved_disjoint_dom.
              - exact (proj1 (Hwf.(pwf_proc_binders_reserved) proc_name _ H0)).
              - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
                  [exact (proj1 Hmr2 v Hv) | exact (proj2 Hmr2 v Hv)]. }
            have HfvA : ∀ v, v ∈ assertion_lexpr_fvars proc_pre →
              v ∈ dom (list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr) ∨ is_reserved v.
            { have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ HlocalsDef. have := Forall2_length _ _ _ Hlexprs_arg_vals. lia. }
              intros v Hv.
              destruct (proj1 (Hwf.(pwf_proc_fvars_bounded) proc_name _ H0) v Hv) as [Hin | Hin].
              - left. rewrite dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). exact Hin.
              - right. exact (proj1 (Hwf.(pwf_proc_binders_reserved) proc_name _ H0) v Hin). }
            have HdomEq : dom (list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr) = dom (list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr).
            { have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ HlocalsDef. have := Forall2_length _ _ _ Hlexprs_arg_vals. lia. }
              have Hlen2 : length proc_args.*1 ≤ length (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals). { rewrite map_length. have := Forall2_length _ _ _ HlocalsDef. lia. }
              rewrite !dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). rewrite (fst_zip _ _ Hlen2). reflexivity. }
            pose proof (trnsl_assertion_w_lexpr_subst proc_pre lexprs proc_args.*1 arg_vals stk_id mp u1 proc_frame_pre
              Hwf (proj1 Hspec_StackFree)
              HbA_M1 HbA_M2
              HfvA HdomEq Hmr1 Hmr2
              Hlexprs_arg_vals Hproc_pre Hproc_frame_pre) as Himpl.
            iApply Himpl. iFrame.
          }


          iNext. iExact "HΦ".

          }

          { iDestruct (all_proc_tbl_chunks_elem proc_name (Proc proc_args proc_locals proc_pre proc_post proc_body) H0 with "HprocTbl") as "Hproc_tbl".
            iEval (simpl; rewrite Hproc_body) in "Hproc_tbl".
            iFrame "Hproc_tbl". setoid_rewrite <- trnsl_assertion_unfold. iFrame. }

          {
            iNext. iIntros "[%ret_val [Hstk [[Hq %Htyp2] _]]]".

            have Hproc_frame_post : trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id mp ≡ proc_frame_post ret_val.
            { reflexivity. }

            have Hret_typ_match : typ_val_match (ρ x) (trnsl_val ret_val).
            { apply typeOf_trnsl_val_match.
              unfold proc_call_ret_well_typed in Hret_wt.
              rewrite Hproc_record in Htyp2.
              rewrite Htyp2 in Hret_wt.
              exact (eq_sym Hret_wt). }

            iApply "HΦ". iFrame. iExists (trnsl_val ret_val).
            iSplitR; [iPureIntro; exact Hret_typ_match|].

            set (trnsl_assertion (subst proc_post (<["#ret_val":=LVar lvar_x]> subst_map)) stk_id
            (λ x0 : lvar, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0)) as u.
            assert ((trnsl_assertion (subst proc_post (<["#ret_val":=LVar lvar_x]> subst_map)) stk_id
            (λ x0 : lvar, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0)) ≡ u) as Hpost. { subst u; reflexivity. }

            iSplitR "Hq".
            { rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done. rewrite trnsl_lval_trnsl_val_inverse. iFrame. }

            { have Hmr1_base : subst_map_avoids_reserved (list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr).
              { apply subst_map_avoids_reserved_of_lexprs.
                - exact (Hwf.(pwf_proc_args_not_reserved) proc_name
                           (Proc proc_args proc_locals proc_pre proc_post proc_body) H0).
                - exact (proj1 H5). }
              have Hmr2_base : subst_map_avoids_reserved
                (list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr).
              { apply subst_map_avoids_reserved_of_lexprs.
                - exact (Hwf.(pwf_proc_args_not_reserved) proc_name
                           (Proc proc_args proc_locals proc_pre proc_post proc_body) H0).
                - exact (lval_list_no_reserved arg_vals trnsl_val). }
              have Hlvar_x_ok : ¬ is_reserved lvar_x := H4.
              have Hargs_ok : Forall (λ a, ¬ is_reserved a) proc_args.*1 :=
                Hwf.(pwf_proc_args_not_reserved) proc_name
                  (Proc proc_args proc_locals proc_pre proc_post proc_body) H0.
              have Hmr1 : subst_map_avoids_reserved (<["#ret_val":=LVar lvar_x]>(list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr)).
              { apply subst_map_avoids_reserved_insert.
                - exact ret_val_not_reserved.
                - intros v Hv. simpl in Hv. apply elem_of_singleton in Hv as ->. exact Hlvar_x_ok.
                - exact Hmr1_base. }
              have Hmr2 : subst_map_avoids_reserved (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr)).
              { apply subst_map_avoids_reserved_insert.
                - exact ret_val_not_reserved.
                - intros v Hv. simpl in Hv. set_solver.
                - exact Hmr2_base. }
              have HbA_M1 : assertion_exists_binders proc_post ##
                (dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr)) ∪
                 lexpr_map_fvars (<["#ret_val":=LVar lvar_x]>(list_to_map (zip proc_args.*1 lexprs)))).
              { apply reserved_disjoint_dom.
                - exact (proj2 (Hwf.(pwf_proc_binders_reserved) proc_name _ H0)).
                - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
                    [exact (proj1 Hmr1 v Hv) | exact (proj2 Hmr1 v Hv)]. }
              have HbA_M2 : assertion_exists_binders proc_post ##
                (dom (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr)) ∪
                 lexpr_map_fvars (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))))).
              { apply reserved_disjoint_dom.
                - exact (proj2 (Hwf.(pwf_proc_binders_reserved) proc_name _ H0)).
                - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
                    [exact (proj1 Hmr2 v Hv) | exact (proj2 Hmr2 v Hv)]. }
              have HfvA : ∀ v, v ∈ assertion_lexpr_fvars proc_post →
                v ∈ dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr)) ∨ is_reserved v.
              { have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ Hlexprs_arg_vals. have := Forall2_length _ _ _ Harg_vals. have := @length_fmap _ _ fst proc_args. simpl in *. lia. }
                intros v Hv.
                destruct (proj2 (Hwf.(pwf_proc_fvars_bounded) proc_name _ H0) v Hv) as [Hin | Hin].
                - left. rewrite dom_insert_L. rewrite dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). exact Hin.
                - right. exact (proj2 (Hwf.(pwf_proc_binders_reserved) proc_name _ H0) v Hin). }
              have HdomEq : dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr)) = dom (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr)).
              { have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ Hlexprs_arg_vals. have := Forall2_length _ _ _ Harg_vals. have := @length_fmap _ _ fst proc_args. simpl in *. lia. }
                have Hlen2 : length proc_args.*1 ≤ length (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals). { rewrite map_length. have := Forall2_length _ _ _ Harg_vals. have := @length_fmap _ _ fst proc_args. simpl in *. lia. }
                rewrite !dom_insert_L. rewrite !dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). rewrite (fst_zip _ _ Hlen2). reflexivity. }
              pose proof (trnsl_assertion_w_lexpr_subst_r proc_post lexprs proc_args.*1 arg_vals lvar_x ret_val stk stk_id mp u (proc_frame_post ret_val)
                Hwf (proj2 Hspec_StackFree)
                HbA_M1 HbA_M2
                HfvA HdomEq Hmr1 Hmr2
                (fresh_lvar_not_in_lexpr_map_fvars_zip stk args lexprs proc_args.*1 lvar_x H2 H)
                Hlvar_x_ok Hargs_ok
                H Hlexprs_arg_vals Hpost Hproc_frame_post) as Himpl.
              setoid_rewrite <- trnsl_assertion_unfold. iApply Himpl. iFrame. }
          }

        }

      }

      1 : {
        (* FPU *)
        unfold trnsl_hoare_triple; simpl.
        setoid_rewrite trnsl_assertion_unfold.
        iIntros "[Hstack [Hown %Hfpv]]".
        destruct (Γ r) as [[i [U [Hdisc [Heq_car [Hindx [Hcomp Hval]]]]]] | ] eqn:H_RA_Pack.
        - pose proof (RAPack_fpuValid Γ r
            (existT i (exist _ U (conj Hdisc (exist _ Heq_car (conj Hindx (conj Hcomp Hval))))))
            H_RA_Pack) as HRA_fpu.
          iDestruct "Hown" as (l chunk_old γ) "[%Heq [%Hown_eval [Hmap Hown]]]".
          destruct (interp_lexpr_ra_fpuvalid_inv r chunk_old lexpr_old lexpr_new mp Hown_eval Hfpv)
            as [chunk_new [Hnew_eval Hfpu]].

          iFrame.

          apply (HRA_fpu chunk_old chunk_new) in Hfpu.

          iMod (own_update _
            (transport (f_equal cmra_car Hindx) ((transport Heq_car chunk_old)))
            (transport (f_equal cmra_car Hindx) ((transport Heq_car chunk_new)))
         with "Hown") as "Hown".

         { apply transport_cmra_update. exact Hfpu.  }

         iModIntro. rewrite H_RA_Pack. iExists l, chunk_new, γ. iFrame.
         iPureIntro. split; [exact Heq | exact Hnew_eval].

        - (* r ∉ ra_set: LGhostOwn is vacuously True on both sides *)
          iModIntro.
          simpl.
          rewrite H_RA_Pack.
          iFrame.

      }

      1 : {
        (* EXISTS ELIM *)
        iPoseProof ("IH" with "[%] [%]") as "IH1"; try done.
        unfold trnsl_hoare_triple. simpl.
        destruct (trnsl_stmt c) eqn:Htrnsl; try done.
        { (* None' branch: ghost-only step *)
          rewrite (trnsl_assertion_exists v t body stk_id mp).
          iIntros "[%v' [%Htyp Hebody]]".
          have Htyp' : typ_val_match (σ v) v'. { rewrite Hsigma. exact Htyp. }
          pose proof (env_typ_well_defined_update σ mp v v' Henv Htyp') as Henv'.
          iPoseProof ("IH1" $! (fun y => if (y =? v)%string then v' else mp y) with "[%]") as "IH2"; [done|].
          iEval (unfold trnsl_hoare_triple) in "IH2".
          iMod ("IH2" with "Hebody") as "Hq".
          iEval (rewrite (trnsl_assertion_mp_irrelevant v q v' stk_id mp Hqfresh)) in "Hq".
          iModIntro. iFrame.
        }
        { (* Some' branch: real WP triple *)
          iIntros (Φ).
          rewrite (trnsl_assertion_exists v t body stk_id mp).
          iModIntro. iIntros "[%v' [%Htyp Hebody]] HΦ".
          have Htyp' : typ_val_match (σ v) v'. { rewrite Hsigma. exact Htyp. }
          pose proof (env_typ_well_defined_update σ mp v v' Henv Htyp') as Henv'.
          iPoseProof ("IH1" $! (fun y => if (y =? v)%string then v' else mp y) with "[%]") as "IH2"; [done|].
          iEval (unfold trnsl_hoare_triple) in "IH2".
          iApply ("IH2" with "Hebody").
          iNext. iIntros "Hq". iApply "HΦ".
          iEval (rewrite (trnsl_assertion_mp_irrelevant v q v' stk_id mp Hqfresh)) in "Hq".
          iFrame.
        }
      }

      1: {
        (* ASSERT: ghost-only, no physical step, and no change to the
           assertion state -- trnsl_hoare_triple for a None'-producing stmt
           unfolds to a bare update between identical pre/post, so this is
           just returning the hypothesis unchanged (mirrors FPU's own case
           shape, but without any own_update at all, since there's no
           ghost-state change here). *)
        unfold trnsl_hoare_triple; simpl.
        setoid_rewrite trnsl_assertion_unfold.
        iIntros "H". iModIntro. iFrame.
      }
    Qed.

    (* The central bootstrap theorem: if every procedure's own body is
       provably correct against its own contract (via RavenHoareTriple, run
       from a symbolic entry stack synthesized from its formal args and
       locals), then all_proc_specs_valid_iris holds unconditionally -- with no
       ▷ all_proc_specs_valid_iris hypothesis of its own. The recursive/mutually-
       recursive call sites inside procedure bodies are discharged via Löb
       induction, mirroring rrl_validity's own use of "Calls".

       raven_soundness_core is an internal building block: Theorem
       raven_soundness, below (after Section MainTranslation closes), is
       the adequacy wrapper that picks a concrete Sigma/Gamma/invTokenG,
       allocates ghost_heap_name/invtoken_names, discharges
       Hworlds/Hgworlds/Hwtbl, and calls this lemma directly rather than
       allocating internally itself. *)
    Lemma raven_soundness_core σ
      (Hwf : ProgramWF)
      (* σ has enough distinct lvars of any given type, avoiding any finite
         exclusion set -- lets every procedure synthesize its own entry stack
         out of genuinely fresh lvars, rather than reusing formal-argument or
         local-variable names as lvar names (which would force every
         procedure sharing such a name to agree on its type under a single
         global σ). *)
      (Hσ_rich : ∀ (t : typ) (excl : gset lvar), ∃ lv, lv ∉ excl ∧ ¬ is_reserved lv ∧ σ lv = t)
      (Hpbt : proc_bodies_translate)
      (* "#ret_val" is itself a stack variable, so by the time the body
         returns it may have been reassigned (fresh lvar per
         VarAssignmentRule) away from its initial binding; lv_final is
         whatever lvar it now points to, and the postcondition's own
         "#ret_val" occurrences must be read through that renaming --
         mirroring exactly how ProcCallRuleRet's own conclusion substitutes
         "#ret_val" with the call's fresh result lvar. *)
      (Hbodies : all_proc_specs_valid_raven σ) :
      (* The per-invariant shared worlds, the ghost heap's own world, and
         every procedure's table registration are object-level (-∗)
         antecedents, not Coq-level "⊢ P" premises: own_alloc/inv_alloc
         (the only way to ever produce them) only ever yield a
         |==>/={E}=∗-wrapped fact, never a bare unconditional "⊢ P" -- so a
         caller building them via allocation (see raven_soundness, the
         adequacy wrapper below) needs to be able to *frame them in*,
         not hand over a closed proof term. The calculus itself has no rule
         that could produce any of the three (an [LInv] fact is only ever
         *traded for* by [InvAllocRule], never conjured; proc_tbl_chunk is
         consumed by ProcCallRuleRet's soundness case but never produced by
         any rule either), so they record how the ghost state/program were
         set up -- as resources, not as external axioms. *)
      all_inv_worlds -∗ Wghost_world -∗ all_proc_tbl_chunks -∗
      all_proc_specs_valid_iris σ.
    Proof.
      iIntros "#Hworlds #Hgworlds #Hwtbl".
      iLöb as "IH".
      rewrite /all_proc_specs_valid_iris.
      iModIntro.
      iIntros (proc proc_record stk_vals) "%Hproc_in_set %Hproc_map".
      iIntros (precond postcond stk_id stk_frm mp stmt msk)
        "%Henv %Hmsk_sub %Hmask_req %Hargs_present %Harg_vals %Hlocals_typed %Hdom_val %Harg_vals_typed %Hprecond_eq %Hpostcond_eq %Hstmt_shape".

      (* Matches all_proc_specs_valid_raven's own internal "let ρ := ..." --
         Hbodies proc proc_record Hproc_map below is already stated in
         terms of exactly this, so ρ needs no external parameter here. *)
      set (ρ := proc_pvar_typs proc_record).

      pose proof (Hwf.(pwf_proc_args_unique) proc proc_record Hproc_map) as Hargs_nodup.
      pose proof (Hwf.(pwf_proc_locals_unique) proc proc_record Hproc_map) as Hlocals_nodup.
      pose proof (Hwf.(pwf_proc_args_locals_disjoint) proc proc_record Hproc_map) as Hargs_locals_disjoint.
      pose proof (Hwf.(pwf_proc_stack_free) proc proc_record Hproc_map) as [Hpre_free Hpost_free].

      destruct (fresh_proc_entry_lvars σ Hσ_rich proc_record) as (dll & _).
      set (args_lvs := dll_args dll).
      set (locals_lvs := dll_locals dll).
      have Hargs_lvs_len : length args_lvs = length (proc_args_of proc_record) := dll_args_len dll.
      have Hlocals_lvs_len : length locals_lvs = length (proc_locals_of proc_record) := dll_locals_len dll.
      have Hargs_lvs_typed : Forall2 (fun decl lv => σ lv = snd decl) (proc_args_of proc_record) args_lvs
        := dll_args_typed dll.
      have Hlocals_lvs_typed : Forall2 (fun decl lv => σ lv = snd decl) (proc_locals_of proc_record) locals_lvs
        := dll_locals_typed dll.
      have Hargs_lvs_nodup : NoDup args_lvs := dll_args_nodup dll.
      have Hlocals_lvs_nodup : NoDup locals_lvs := dll_locals_nodup dll.
      have Hargs_locals_lvs_disjoint : ∀ lv, lv ∈ args_lvs → lv ∉ locals_lvs := dll_disjoint dll.

      destruct (Hbodies proc proc_record Hproc_map) as [Hwelldef Hbody_msk].
      destruct (Hbody_msk msk Hmask_req Hmsk_sub dll) as (stk0' & lv_final & Hrv_final & Hlv_final_res & Hlv_final_typ & HRHT).

      set (args := (proc_args_of proc_record).*1).
      set (loc_names := (proc_locals_of proc_record).*1).
      set (names := (proc_args_of proc_record ++ proc_locals_of proc_record).*1).
      set (lvs := args_lvs ++ locals_lvs).

      have Hargs_len2 : length args = length stk_vals := Forall2_length _ _ _ Harg_vals.
      destruct (extract_present_vals (proc_locals_of proc_record) stk_frm.(locals) Hlocals_typed)
        as (local_vals & Hlocal_vals_F2 & Hlocal_vals_typed).
      set (vals := stk_vals ++ local_vals).

      have Hargs_len_lvs : length args = length args_lvs.
      { unfold args. rewrite map_length. exact (eq_sym Hargs_lvs_len). }
      have Hlocals_len_lvs : length loc_names = length locals_lvs.
      { unfold loc_names. rewrite map_length. exact (eq_sym Hlocals_lvs_len). }
      have Hlocals_len2 : length loc_names = length local_vals.
      { unfold loc_names. rewrite map_length. exact (Forall2_length _ _ _ Hlocal_vals_F2). }

      have Hnames_eq : names = args ++ loc_names.
      { unfold names, args, loc_names. apply fmap_app. }

      have Hnodup_names : NoDup names.
      { rewrite Hnames_eq. apply NoDup_app. repeat split.
        - exact Hargs_nodup.
        - intros x Hx1 Hx2. exact (Hargs_locals_disjoint x Hx1 Hx2).
        - exact Hlocals_nodup. }

      have Hnodup_lvs : NoDup lvs.
      { unfold lvs. apply NoDup_app. repeat split.
        - exact Hargs_lvs_nodup.
        - exact Hargs_locals_lvs_disjoint.
        - exact Hlocals_lvs_nodup. }

      have Hlen1 : length names = length lvs.
      { rewrite Hnames_eq. unfold lvs. rewrite !app_length. f_equal; [exact Hargs_len_lvs | exact Hlocals_len_lvs]. }
      have Hlen2 : length names = length vals.
      { rewrite Hnames_eq. unfold vals. rewrite !app_length. f_equal; [exact Hargs_len2 | exact Hlocals_len2]. }

      set (mp0 := fun lv0 => match (list_to_map (zip lvs vals) : gmap lvar lang.val) !! lv0 with
                              | Some v => trnsl_val v | None => mp lv0 end).

      have Hargs_typed_σ : Forall2 (λ lv val, typeOf val = σ lv) args_lvs stk_vals.
      { eapply Forall2_combine; [| exact Hargs_lvs_typed | exact Harg_vals_typed].
        intros decl lv val Hp1 Hp2. rewrite Hp2. exact (eq_sym Hp1). }
      have Hlocals_typed_σ : Forall2 (λ lv val, typeOf val = σ lv) locals_lvs local_vals.
      { eapply Forall2_combine; [| exact Hlocals_lvs_typed | exact Hlocal_vals_typed].
        intros decl lv val Hp1 Hp2. rewrite Hp2. exact (eq_sym Hp1). }
      have Hnames_typed : Forall2 (λ lv0 val0, typeOf val0 = σ lv0) lvs vals.
      { unfold lvs, vals. apply Forall2_app; [exact Hargs_typed_σ | exact Hlocals_typed_σ]. }

      have Henv0 : env_typ_well_defined σ mp0.
      { unfold mp0. exact (env_typ_well_defined_override σ mp lvs vals Hnames_typed Henv). }

      have Hnodup_names_vals : NoDup (zip names vals).*1.
      { rewrite (fst_zip _ _ (Nat.eq_le_incl _ _ Hlen2)). exact Hnodup_names. }
      have Hzip_names_vals_eq : zip names vals = zip args stk_vals ++ zip loc_names local_vals.
      { rewrite Hnames_eq. unfold vals. exact (zip_with_app pair args loc_names stk_vals local_vals Hargs_len2). }

      have Hframe_eq : stk_frm.(locals) = list_to_map (zip names vals).
      { apply map_eq. intro v.
        destruct (decide (v ∈ names)) as [Hin | Hnotin].
        - rewrite Hnames_eq elem_of_app in Hin.
          destruct Hin as [Hin_args | Hin_locals].
          + apply elem_of_list_lookup_1 in Hin_args as [i Hi].
            pose proof (Forall2_lookup_l _ args stk_vals i v Harg_vals Hi) as [val [Hval Hlk]].
            have Hzip_lookup : zip args stk_vals !! i = Some (v, val).
            { apply lookup_zip_with_Some. exists v, val. done. }
            have Hzip_in : (v, val) ∈ zip args stk_vals := elem_of_list_lookup_2 _ i _ Hzip_lookup.
            rewrite Hlk. symmetry.
            apply elem_of_list_to_map_1; [exact Hnodup_names_vals |].
            rewrite Hzip_names_vals_eq. apply elem_of_app. left. exact Hzip_in.
          + apply elem_of_list_lookup_1 in Hin_locals as [i Hi].
            unfold loc_names in Hi. rewrite list_lookup_fmap in Hi.
            destruct (proc_locals_of proc_record !! i) as [[v0 tp0]|] eqn:Hdecl_i; [| discriminate].
            simpl in Hi. injection Hi as Hi_eq. subst v0.
            pose proof (Forall2_lookup_l _ (proc_locals_of proc_record) local_vals i (v, tp0) Hlocal_vals_F2 Hdecl_i)
              as [val [Hval Hlk]].
            simpl in Hlk.
            have Hi : loc_names !! i = Some v.
            { unfold loc_names. rewrite list_lookup_fmap Hdecl_i. done. }
            have Hzip_lookup : zip loc_names local_vals !! i = Some (v, val).
            { apply lookup_zip_with_Some. exists v, val. done. }
            have Hzip_in : (v, val) ∈ zip loc_names local_vals := elem_of_list_lookup_2 _ i _ Hzip_lookup.
            rewrite Hlk. symmetry.
            apply elem_of_list_to_map_1; [exact Hnodup_names_vals |].
            rewrite Hzip_names_vals_eq. apply elem_of_app. right. exact Hzip_in.
        - have Hn1 : stk_frm.(locals) !! v = None.
          { apply not_elem_of_dom. rewrite Hdom_val.
            intro Hc. apply Hnotin. rewrite Hnames_eq.
            rewrite <- list_to_set_app_L in Hc. rewrite elem_of_list_to_set in Hc. exact Hc. }
          have Hn2 : (list_to_map (zip names vals) : gmap var lang.val) !! v = None.
          { apply not_elem_of_list_to_map_1. rewrite (fst_zip _ _ (Nat.eq_le_incl _ _ Hlen2)). exact Hnotin. }
          rewrite Hn1 Hn2. done. }

      have Hstk0_eq : symb_stk_to_stk_frm (list_to_map (zip names lvs)) mp0 = stk_frm.
      { unfold mp0.
        rewrite (symb_stk_to_stk_frm_general names lvs vals mp Hnodup_names Hnodup_lvs Hlen1 Hlen2).
        unfold assoc_map. rewrite <- Hframe_eq. destruct stk_frm. reflexivity. }

      have Hargs_len2' : length args ≤ length (map (λ val, LVal (trnsl_val val)) stk_vals).
      { rewrite map_length. rewrite Hargs_len2. apply Nat.le_refl. }
      have Hargs_len_lvs' : length args ≤ length (map LVar args_lvs).
      { rewrite map_length. rewrite Hargs_len_lvs. apply Nat.le_refl. }

      (* mp0 only ever overrides mp at lvs = args_lvs ++ locals_lvs, all of
         which are non-reserved (dll_args_not_reserved/dll_locals_not_reserved)
         -- so it agrees with mp at every reserved name, the fact both
         Hprecond_bridge/Hpostcond_bridge's own widened Hbase need to cover
         the "is_reserved" disjunct trnsl_assertion_subst_congr's Hbase
         premise carries. *)
      have Hreserved_mp0 : ∀ x, is_reserved x → mp0 x = mp x.
      { intros x Hx.
        have Hx_lvs : x ∉ lvs.
        { intro Hin. unfold lvs in Hin. apply elem_of_app in Hin as [Hin|Hin].
          - exact (proj1 (Forall_forall _ _) (dll_args_not_reserved dll) x Hin Hx).
          - exact (proj1 (Forall_forall _ _) (dll_locals_not_reserved dll) x Hin Hx). }
        unfold mp0.
        have Hnone : (list_to_map (zip lvs vals) : gmap lvar lang.val) !! x = None.
        { apply not_elem_of_dom.
          rewrite dom_list_to_map_L (fst_zip _ _ (Nat.eq_le_incl _ _ (eq_trans (eq_sym Hlen1) Hlen2))).
          rewrite elem_of_list_to_set. exact Hx_lvs. }
        rewrite Hnone. reflexivity. }

      have Hprecond_bridge :
        trnsl_assertion (subst (proc_precond_of proc_record) (list_to_map (zip args (map LVar args_lvs)))) stk_id mp0
        ≡ precond.
      { set (M1 := list_to_map (zip args (map LVar args_lvs)) : gmap var LExpr).
        set (M2 := list_to_map (zip args (map (λ val, LVal (trnsl_val val)) stk_vals)) : gmap var LExpr).
        have Hmr1 : subst_map_avoids_reserved M1.
        { unfold M1. apply subst_map_avoids_reserved_of_lexprs.
          - exact (Hwf.(pwf_proc_args_not_reserved) proc proc_record Hproc_map).
          - exact (lvar_list_no_reserved args_lvs (dll_args_not_reserved dll)). }
        have Hmr2 : subst_map_avoids_reserved M2.
        { unfold M2. apply subst_map_avoids_reserved_of_lexprs.
          - exact (Hwf.(pwf_proc_args_not_reserved) proc proc_record Hproc_map).
          - exact (lval_list_no_reserved stk_vals trnsl_val). }
        have HbA_M1 : assertion_exists_binders (proc_precond_of proc_record) ##
          (dom M1 ∪ lexpr_map_fvars M1).
        { apply reserved_disjoint_dom.
          - exact (proj1 (Hwf.(pwf_proc_binders_reserved) proc proc_record Hproc_map)).
          - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
              [exact (proj1 Hmr1 v Hv) | exact (proj2 Hmr1 v Hv)]. }
        have HbA_M2 : assertion_exists_binders (proc_precond_of proc_record) ##
          (dom M2 ∪ lexpr_map_fvars M2).
        { apply reserved_disjoint_dom.
          - exact (proj1 (Hwf.(pwf_proc_binders_reserved) proc proc_record Hproc_map)).
          - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
              [exact (proj1 Hmr2 v Hv) | exact (proj2 Hmr2 v Hv)]. }
        have Hfv := proj1 (Hwf.(pwf_proc_fvars_bounded) proc proc_record Hproc_map).
        have HfvA : ∀ v, v ∈ assertion_lexpr_fvars (proc_precond_of proc_record) → v ∈ dom M1 ∨ is_reserved v.
        { intros v Hv. destruct (Hfv v Hv) as [Hin | Hin].
          - left. unfold M1. rewrite dom_list_to_map_L (fst_zip _ _ Hargs_len_lvs'). exact Hin.
          - right. exact (proj1 (Hwf.(pwf_proc_binders_reserved) proc proc_record Hproc_map) v Hin). }
        have HdomEq : dom M1 = dom M2.
        { unfold M1, M2. rewrite !dom_list_to_map_L (fst_zip _ _ Hargs_len_lvs') (fst_zip _ _ Hargs_len2'). reflexivity. }
        have Hstab := hstab_lexpr_subst_fwd args (map LVar args_lvs) stk_vals HdomEq.
        have Hbase : ∀ x, x ∈ dom M1 → eval_lvar M1 mp0 x = eval_lvar M2 mp x.
        { intros x Hx.
          have Hx_args : x ∈ args.
          { unfold M1 in Hx. rewrite dom_list_to_map_L (fst_zip _ _ Hargs_len_lvs') in Hx.
            rewrite elem_of_list_to_set in Hx. exact Hx. }
          pose proof Hx_args as Hx_args'.
          apply elem_of_list_lookup_1 in Hx_args' as [i Hi].
          have Hlv_ex : is_Some (args_lvs !! i).
          { apply lookup_lt_is_Some_2. rewrite <- Hargs_len_lvs. eapply lookup_lt_Some. exact Hi. }
          destruct Hlv_ex as [lv Hlv].
          pose proof (Forall2_lookup_l _ args stk_vals i x Harg_vals Hi) as [val [Hval Hlk]].
          have Hzip_lvs_in : (x, lv) ∈ zip args args_lvs.
          { apply (elem_of_list_lookup_2 _ i). apply lookup_zip_with_Some. exists x, lv. done. }
          have Hzip_vals_in : (x, val) ∈ zip args stk_vals.
          { apply (elem_of_list_lookup_2 _ i). apply lookup_zip_with_Some. exists x, val. done. }
          unfold eval_lvar, M1, M2.
          rewrite (zip_wrap_map_lookup_arg args args_lvs LVar x lv Hargs_nodup Hzip_lvs_in).
          rewrite (zip_wrap_map_lookup_arg args stk_vals (λ val0, LVal (trnsl_val val0)) x val Hargs_nodup Hzip_vals_in).
          simpl. unfold mp0.
          have Hzip_lvs_full : (lv, val) ∈ zip lvs vals.
          { unfold lvs, vals. rewrite (zip_with_app pair args_lvs locals_lvs stk_vals local_vals (eq_trans (eq_sym Hargs_len_lvs) Hargs_len2)).
            apply elem_of_app. left.
            apply (elem_of_list_lookup_2 _ i). apply lookup_zip_with_Some. exists lv, val.
            split; [done |]. split.
            - apply elem_of_list_lookup_1 in Hzip_lvs_in as [i' Hi'].
              rewrite lookup_zip_with in Hi'.
              destruct (args !! i') eqn:Ha; [| discriminate]. destruct (args_lvs !! i') eqn:Hb; [| discriminate].
              simpl in Hi'. injection Hi' as Heqa Heqb. subst v. subst l.
              have Hii' : i = i'. { apply (NoDup_lookup args i i' x Hargs_nodup Hi Ha). }
              subst i'. exact Hb.
            - apply elem_of_list_lookup_1 in Hzip_vals_in as [i' Hi'].
              rewrite lookup_zip_with in Hi'.
              destruct (args !! i') eqn:Ha; [| discriminate]. destruct (stk_vals !! i') eqn:Hb; [| discriminate].
              simpl in Hi'. injection Hi' as Heqa Heqb. subst v. subst v0.
              have Hii' : i = i'. { apply (NoDup_lookup args i i' x Hargs_nodup Hi Ha). }
              subst i'. exact Hb. }
          have Hmp0_lv : (list_to_map (zip lvs vals) : gmap lvar lang.val) !! lv = Some val.
          { apply elem_of_list_to_map_1; [rewrite (fst_zip _ _ (Nat.eq_le_incl _ _ (eq_trans (eq_sym Hlen1) Hlen2))); exact Hnodup_lvs | exact Hzip_lvs_full]. }
          rewrite Hmp0_lv. done. }
        have Hbase' : ∀ x, x ∈ dom M1 ∨ is_reserved x → eval_lvar M1 mp0 x = eval_lvar M2 mp x.
        { intros x [Hx | Hx]; [exact (Hbase x Hx) |].
          unfold eval_lvar.
          have Hn1 : M1 !! x = None. { apply not_elem_of_dom. intro Hin. exact (proj1 Hmr1 x Hin Hx). }
          have Hn2 : M2 !! x = None. { apply not_elem_of_dom. intro Hin. exact (proj1 Hmr2 x Hin Hx). }
          rewrite Hn1 Hn2. f_equal. exact (Hreserved_mp0 x Hx). }
        have Heq := trnsl_assertion_subst_congr Hwf (proc_precond_of proc_record) M1 M2 stk_id mp0 mp
          Hpre_free HbA_M1 HbA_M2
          HfvA HdomEq Hmr1 Hmr2 Hstab Hbase'.
        rewrite Heq. exact Hprecond_eq. }

      set (ret_val := trnsl_lval (mp0 lv_final)).

      have Hpostcond_bridge :
        (trnsl_assertion
          (subst (proc_postcond_of proc_record)
             (<["#ret_val" := LVar lv_final]> (list_to_map (zip args (map LVar args_lvs)))))
          stk_id mp0 ∗
         ⌜proc_ret_typ_opt proc_record = Some (typeOf ret_val)⌝)%I
        ≡ postcond ret_val.
      { set (M1 := <["#ret_val" := LVar lv_final]> (list_to_map (zip args (map LVar args_lvs))) : gmap var LExpr).
        set (M2 := <["#ret_val" := LVal (trnsl_val ret_val)]>
                     (list_to_map (zip args (map (λ val, LVal (trnsl_val val)) stk_vals))) : gmap var LExpr).
        have Hmr1_base : subst_map_avoids_reserved (list_to_map (zip args (map LVar args_lvs)) : gmap var LExpr).
        { apply subst_map_avoids_reserved_of_lexprs.
          - exact (Hwf.(pwf_proc_args_not_reserved) proc proc_record Hproc_map).
          - exact (lvar_list_no_reserved args_lvs (dll_args_not_reserved dll)). }
        have Hmr2_base : subst_map_avoids_reserved
          (list_to_map (zip args (map (λ val, LVal (trnsl_val val)) stk_vals)) : gmap var LExpr).
        { apply subst_map_avoids_reserved_of_lexprs.
          - exact (Hwf.(pwf_proc_args_not_reserved) proc proc_record Hproc_map).
          - exact (lval_list_no_reserved stk_vals trnsl_val). }
        have Hmr1 : subst_map_avoids_reserved M1.
        { unfold M1. apply subst_map_avoids_reserved_insert.
          - exact ret_val_not_reserved.
          - intros v Hv. simpl in Hv. apply elem_of_singleton in Hv as ->. exact Hlv_final_res.
          - exact Hmr1_base. }
        have Hmr2 : subst_map_avoids_reserved M2.
        { unfold M2. apply subst_map_avoids_reserved_insert.
          - exact ret_val_not_reserved.
          - intros v Hv. simpl in Hv. set_solver.
          - exact Hmr2_base. }
        have HbA_M1 : assertion_exists_binders (proc_postcond_of proc_record) ##
          (dom M1 ∪ lexpr_map_fvars M1).
        { apply reserved_disjoint_dom.
          - exact (proj2 (Hwf.(pwf_proc_binders_reserved) proc proc_record Hproc_map)).
          - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
              [exact (proj1 Hmr1 v Hv) | exact (proj2 Hmr1 v Hv)]. }
        have HbA_M2 : assertion_exists_binders (proc_postcond_of proc_record) ##
          (dom M2 ∪ lexpr_map_fvars M2).
        { apply reserved_disjoint_dom.
          - exact (proj2 (Hwf.(pwf_proc_binders_reserved) proc proc_record Hproc_map)).
          - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
              [exact (proj1 Hmr2 v Hv) | exact (proj2 Hmr2 v Hv)]. }
        have Hfv := proj2 (Hwf.(pwf_proc_fvars_bounded) proc proc_record Hproc_map).
        have HdomEq0 : dom (list_to_map (zip args (map LVar args_lvs)) : gmap var LExpr)
                     = dom (list_to_map (zip args (map (λ val, LVal (trnsl_val val)) stk_vals)) : gmap var LExpr).
        { rewrite !dom_list_to_map_L (fst_zip _ _ Hargs_len_lvs') (fst_zip _ _ Hargs_len2'). reflexivity. }
        have HfvA : ∀ v, v ∈ assertion_lexpr_fvars (proc_postcond_of proc_record) → v ∈ dom M1 ∨ is_reserved v.
        { intros v Hv. destruct (Hfv v Hv) as [Hin | Hin].
          - left. unfold M1. rewrite dom_insert_L dom_list_to_map_L (fst_zip _ _ Hargs_len_lvs'). exact Hin.
          - right. exact (proj2 (Hwf.(pwf_proc_binders_reserved) proc proc_record Hproc_map) v Hin). }
        have HdomEq : dom M1 = dom M2.
        { unfold M1, M2. rewrite !dom_insert_L. rewrite HdomEq0. reflexivity. }
        have Hstab := hstab_lexpr_subst_r args (map LVar args_lvs) stk_vals lv_final ret_val HdomEq.
        have Hbase : ∀ x, x ∈ dom M1 → eval_lvar M1 mp0 x = eval_lvar M2 mp x.
        { intros x Hx.
          destruct (decide (x = "#ret_val")) as [-> | Hne].
          - unfold eval_lvar, M1, M2. rewrite !lookup_insert. simpl.
            unfold ret_val. rewrite trnsl_val_trnsl_lval_inverse. reflexivity.
          - have Hx_args : x ∈ args.
            { unfold M1 in Hx. rewrite dom_insert_L elem_of_union in Hx.
              destruct Hx as [Hx1 | Hx2].
              - exfalso. apply Hne. rewrite elem_of_singleton in Hx1. exact Hx1.
              - rewrite dom_list_to_map_L (fst_zip _ _ Hargs_len_lvs') in Hx2.
                rewrite elem_of_list_to_set in Hx2. exact Hx2. }
            unfold eval_lvar, M1, M2.
            rewrite lookup_insert_ne; [| intro Heq'; apply Hne; exact (eq_sym Heq')].
            rewrite lookup_insert_ne; [| intro Heq'; apply Hne; exact (eq_sym Heq')].
            pose proof Hx_args as Hx_args'.
            apply elem_of_list_lookup_1 in Hx_args' as [i Hi].
            have Hlv_ex : is_Some (args_lvs !! i).
            { apply lookup_lt_is_Some_2. rewrite <- Hargs_len_lvs. eapply lookup_lt_Some. exact Hi. }
            destruct Hlv_ex as [lv Hlv].
            pose proof (Forall2_lookup_l _ args stk_vals i x Harg_vals Hi) as [val [Hval Hlk]].
            have Hzip_lvs_in : (x, lv) ∈ zip args args_lvs.
            { apply (elem_of_list_lookup_2 _ i). apply lookup_zip_with_Some. exists x, lv. done. }
            have Hzip_vals_in : (x, val) ∈ zip args stk_vals.
            { apply (elem_of_list_lookup_2 _ i). apply lookup_zip_with_Some. exists x, val. done. }
            rewrite (zip_wrap_map_lookup_arg args args_lvs LVar x lv Hargs_nodup Hzip_lvs_in).
            rewrite (zip_wrap_map_lookup_arg args stk_vals (λ val0, LVal (trnsl_val val0)) x val Hargs_nodup Hzip_vals_in).
            simpl. unfold mp0.
            have Hzip_lvs_full : (lv, val) ∈ zip lvs vals.
            { unfold lvs, vals. rewrite (zip_with_app pair args_lvs locals_lvs stk_vals local_vals (eq_trans (eq_sym Hargs_len_lvs) Hargs_len2)).
              apply elem_of_app. left.
              apply (elem_of_list_lookup_2 _ i). apply lookup_zip_with_Some. exists lv, val.
              split; [done |]. split.
              - apply elem_of_list_lookup_1 in Hzip_lvs_in as [i' Hi'].
                rewrite lookup_zip_with in Hi'.
                destruct (args !! i') eqn:Ha; [| discriminate]. destruct (args_lvs !! i') eqn:Hb; [| discriminate].
                simpl in Hi'. injection Hi' as Heqa Heqb. subst v. subst l.
                have Hii' : i = i'. { apply (NoDup_lookup args i i' x Hargs_nodup Hi Ha). }
                subst i'. exact Hb.
              - apply elem_of_list_lookup_1 in Hzip_vals_in as [i' Hi'].
                rewrite lookup_zip_with in Hi'.
                destruct (args !! i') eqn:Ha; [| discriminate]. destruct (stk_vals !! i') eqn:Hb; [| discriminate].
                simpl in Hi'. injection Hi' as Heqa Heqb. subst v. subst v0.
                have Hii' : i = i'. { apply (NoDup_lookup args i i' x Hargs_nodup Hi Ha). }
                subst i'. exact Hb. }
            have Hmp0_lv : (list_to_map (zip lvs vals) : gmap lvar lang.val) !! lv = Some val.
          { apply elem_of_list_to_map_1; [rewrite (fst_zip _ _ (Nat.eq_le_incl _ _ (eq_trans (eq_sym Hlen1) Hlen2))); exact Hnodup_lvs | exact Hzip_lvs_full]. }
          rewrite Hmp0_lv. done. }
        have Hbase' : ∀ x, x ∈ dom M1 ∨ is_reserved x → eval_lvar M1 mp0 x = eval_lvar M2 mp x.
        { intros x [Hx | Hx]; [exact (Hbase x Hx) |].
          unfold eval_lvar.
          have Hn1 : M1 !! x = None. { apply not_elem_of_dom. intro Hin. exact (proj1 Hmr1 x Hin Hx). }
          have Hn2 : M2 !! x = None. { apply not_elem_of_dom. intro Hin. exact (proj1 Hmr2 x Hin Hx). }
          rewrite Hn1 Hn2. f_equal. exact (Hreserved_mp0 x Hx). }
        have Heq := trnsl_assertion_subst_congr Hwf (proc_postcond_of proc_record) M1 M2 stk_id mp0 mp
          Hpost_free HbA_M1 HbA_M2
          HfvA HdomEq Hmr1 Hmr2 Hstab Hbase'.
        rewrite Heq. exact (Hpostcond_eq ret_val). }

      iPoseProof (rrl_validity ρ σ stk_id
        (LAnd (LStack (list_to_map (zip names lvs)))
           (subst (proc_precond_of proc_record) (list_to_map (zip args (map LVar args_lvs)))))
        msk (proc_body_of proc_record)
        (LAnd (LStack stk0')
           (subst (proc_postcond_of proc_record)
              (<["#ret_val" := LVar lv_final]> (list_to_map (zip args (map LVar args_lvs))))))
        Hwf Hpbt Hwelldef Hmsk_sub with "[]") as "Htriple".
      { iSplitR.
        { iModIntro. iApply "Hworlds". }
        iSplitR.
        { iModIntro. iApply "Hgworlds". }
        iSplitR.
        { iModIntro. iApply "Hwtbl". }
        iSplitR.
        { iApply "IH". }
        iPureIntro. exact HRHT. }
      iSpecialize ("Htriple" $! mp0 Henv0).

      destruct Hstmt_shape as [Hstmt_shape | [Hstmt_shape ->]];
        iEval (rewrite /trnsl_hoare_triple Hstmt_shape) in "Htriple".

      - (* proc_body_of proc_record translates to a real statement *)
        iEval (setoid_rewrite trnsl_assertion_unfold; simpl) in "Htriple".
        have Hprecond_bridge' := Hprecond_bridge.
        rewrite trnsl_assertion_unfold in Hprecond_bridge'.
        have Hpostcond_bridge' := Hpostcond_bridge.
        rewrite trnsl_assertion_unfold in Hpostcond_bridge'.
        iIntros (Φ). iModIntro.
        iIntros "[Hstk Hpre] HΦ'".
        iApply ("Htriple" with "[Hstk Hpre]").
        { rewrite Hstk0_eq.
          iSplitL "Hstk"; [iFrame |]. iEval (rewrite Hprecond_bridge'). iFrame. }
        iNext. iIntros "[Hpost_stk Hpost_pred]".
        iApply "HΦ'".
        iExists ret_val, (symb_stk_to_stk_frm stk0' mp0).
        iFrame "Hpost_stk".
        iSplitR.
        + iPureIntro. simpl. rewrite lookup_fmap Hrv_final. reflexivity.
        + iAssert (trnsl_assertion
              (subst (proc_postcond_of proc_record)
                 (<["#ret_val" := LVar lv_final]> (list_to_map (zip args (map LVar args_lvs)))))
              stk_id mp0 ∗
            ⌜proc_ret_typ_opt proc_record = Some (typeOf ret_val)⌝)%I
            with "[Hpost_pred]" as "Hpost_pred2".
          { iSplitL "Hpost_pred".
            - iEval (rewrite trnsl_assertion_unfold). iExact "Hpost_pred".
            - iPureIntro. unfold ret_val.
              rewrite (interp_lexpr_typ_compat σ (LVar lv_final) (σ lv_final) (mp0 lv_final) mp0 Henv0 eq_refl eq_refl).
              exact Hlv_final_typ. }
          iEval (rewrite Hpostcond_bridge) in "Hpost_pred2". iFrame.

      - (* trnsl_stmt (proc_body_of proc_record) = None': body is ghost-only, runs as Skip *)
        have Hprecond_bridge' := Hprecond_bridge.
        rewrite trnsl_assertion_unfold in Hprecond_bridge'.
        have Hpostcond_bridge' := Hpostcond_bridge.
        rewrite trnsl_assertion_unfold in Hpostcond_bridge'.
        iEval (setoid_rewrite trnsl_assertion_unfold; simpl) in "Htriple".
        iIntros (Φ). iModIntro.
        iIntros "[Hstk Hpre] HΦ'".
        iMod ("Htriple" with "[Hstk Hpre]") as "[Hpost_stk Hpost_pred]".
        { rewrite Hstk0_eq.
          iSplitL "Hstk"; [iFrame |]. iEval (rewrite Hprecond_bridge'). iFrame. }
        iApply (wp_skip
          (∃ ret_val0 stk_frm'', stack_own[stk_id, stk_frm''] ∗
             ⌜locals stk_frm'' !! "#ret_val" = Some ret_val0⌝ ∗ postcond ret_val0)%I
          (trnsl_mask msk) stk_id with "[Hpost_stk Hpost_pred]").
        { iExists ret_val, (symb_stk_to_stk_frm stk0' mp0). iFrame "Hpost_stk".
          iSplitR.
          - iPureIntro. simpl. rewrite lookup_fmap Hrv_final. reflexivity.
          - iAssert (trnsl_assertion
                (subst (proc_postcond_of proc_record)
                   (<["#ret_val" := LVar lv_final]> (list_to_map (zip args (map LVar args_lvs)))))
                stk_id mp0 ∗
              ⌜proc_ret_typ_opt proc_record = Some (typeOf ret_val)⌝)%I
              with "[Hpost_pred]" as "Hpost_pred2".
            { iSplitL "Hpost_pred".
              - iEval (rewrite trnsl_assertion_unfold). iExact "Hpost_pred".
              - iPureIntro. unfold ret_val.
                rewrite (interp_lexpr_typ_compat σ (LVar lv_final) (σ lv_final) (mp0 lv_final) mp0 Henv0 eq_refl eq_refl).
                exact Hlv_final_typ. }
            iEval (rewrite Hpostcond_bridge) in "Hpost_pred2". iFrame. }
        iNext. iIntros "[Hpost _]".
        iApply "HΦ'". iFrame "Hpost".
    Qed.

  End MainSoundness.

(* Adequacy wrapper: builds a concrete Gamma (single-RA), GhostConfig and
   invTokenG instance, and
   discharges all_inv_worlds/Wghost_world internally via own_alloc +
   inv_alloc at the empty index -- the whole point of moving
   raven_soundness_core's Hworlds/Hgworlds/Hwtbl from Coq-level "⊢ P"
   premises to object-level (-∗) antecedents above: own_alloc/inv_alloc
   only ever produce a |==>/={E}=∗-wrapped fact, so this wrapper genuinely
   needs to *apply* raven_soundness_core to freshly-allocated resources
   inside its own fancy update, which a bare "⊢ P" argument could never
   accept.

   Scoped to a single RA and a single invariant, parametric over which ones
   -- not generic over an arbitrary finite ra_set/inv_set, which would need
   a fold/induction over finite sets no caller in this project needs
   (counter_monotonic.v uses exactly one RA, h_ra, and one invariant,
   "counterInv"). Establishing Winv/Wghost "from nothing" (at the empty
   index) doesn't depend on the RA/invariant's own content, so this
   restriction only affects how all_inv_worlds is *stated* (a singleton
   big_sepS), not how it is proved.

   all_proc_tbl_chunks stays an external (-∗) antecedent: it depends on
   simpLangG's own heap_proctbl_name, which this wrapper doesn't control
   (simpLangG is taken as a given instance, not allocated here -- only a
   full wp_adequacy-style derivation for a specific execution can produce
   one, which is separate, later, unscoped work). Hwf is phrased uniformly
   over the eventual gname choice: ProgramWF's own fields never inspect
   *which* gname own_alloc hands back, only namespace disjointness and
   invtoken_names's injectivity on inv_set (trivial for a singleton
   inv_set), so proving it for one arbitrary (γg, γi) pair proves it for
   the pair this wrapper actually picks. *)
Section AdequacyWrapper.
  Context {Σ : gFunctors}.
  Context {I : Type} (Gs : I → cmra) `{!inGs Σ Gs}.
  Context `{!inG Σ (authR (gmap.gmapUR heap_addr (agreeR gnameO)))}.
  Context `{!simpLangG Σ}.
  Context `{!invTokenGpreS Σ}.
  Context (RProg : Program).
  Context (r0 : ra_name) (w0 : Γ_witness Gs r0).
  Context (iname0 : inv_name) (Hinv_set : prog_inv_set RProg = {[iname0]}).
  Context (ghost_heap_ns inv_ns : namespace) (Hns_disj : ghost_heap_ns ## inv_ns).

  Definition Γ0 : Γ_type Gs := λ r,
    match decide (r = r0) with
    | left Heq => Γ_found Gs r (eq_rect_r (Γ_witness Gs) w0 Heq)
    | right _ => Γ_absent Gs r
    end.

  Definition mkGhostConfig (γg : gname) : GhostConfig := {|
    gc_ghost_heap_name := γg;
    gc_ghost_heap_namespace := ghost_heap_ns;
    gc_inv_namespace_map := λ _, inv_ns;
  |}.

  Definition mkInvTokenG (γi : gname) : invTokenG Σ :=
    InvTokenG Σ _ (λ _, γi).

  Theorem raven_soundness (σ : lvar_typs)
    (Hwf : ∀ γg γi, ProgramWF (P:=RProg) (G:=mkGhostConfig γg) (invTokenG0:=mkInvTokenG γi))
    (Hσ_rich : ∀ (t : typ) (excl : gset lvar), ∃ lv, lv ∉ excl ∧ ¬ is_reserved lv ∧ σ lv = t)
    (Hpbt : proc_bodies_translate (P:=RProg))
    (Hbodies : all_proc_specs_valid_raven (RProg:=RProg) σ) :
    all_proc_tbl_chunks (RProg:=RProg) -∗
    |={⊤}=> ∃ γg γi,
      all_proc_specs_valid_iris Gs σ (RProg:=RProg) (G:=mkGhostConfig γg)
        (Γ:=Γ0) (invTokenG0:=mkInvTokenG γi).
  Proof.
    iIntros "Hwtbl".
    iMod (own_alloc (● (∅ : gmap.gmapUR heap_addr (agreeR gnameO))))
      as (γg) "Hgh"; first by apply auth_auth_valid.
    iMod (own_alloc (● (∅ : inv_argsUR))) as (γi) "Hin"; first by apply auth_auth_valid.
    iExists γg, γi.
    pose proof (Hwf γg γi) as Hwf0.
    iAssert (▷ Wghost (G:=mkGhostConfig γg))%I with "[Hgh]" as "Hwg".
    { iNext. iExists ∅. rewrite fmap_empty big_sepS_empty. iFrame. }
    iMod (inv_alloc ghost_heap_ns ⊤ (Wghost (G:=mkGhostConfig γg)) with "Hwg") as "#Hgworlds".
    iAssert (▷ Winv Gs iname0 (RProg:=RProg) (G:=mkGhostConfig γg) (invTokenG0:=mkInvTokenG γi) (Γ:=Γ0))%I
      with "[Hin]" as "Hwi".
    { iNext. iExists ∅. rewrite big_sepS_empty. unfold mkInvTokenG. simpl. iFrame. }
    iMod (inv_alloc inv_ns ⊤
      (Winv Gs iname0 (RProg:=RProg) (G:=mkGhostConfig γg) (invTokenG0:=mkInvTokenG γi) (Γ:=Γ0))
      with "Hwi") as "#Hworlds_inv".
    iAssert (all_inv_worlds Gs (RProg:=RProg) (G:=mkGhostConfig γg) (invTokenG0:=mkInvTokenG γi) (Γ:=Γ0))
      as "Hworlds".
    { rewrite /all_inv_worlds Hinv_set big_sepS_singleton. iExact "Hworlds_inv". }
    iModIntro.
    iApply (raven_soundness_core Gs σ Hwf0 Hσ_rich Hpbt Hbodies with "Hworlds Hgworlds Hwtbl").
  Qed.

End AdequacyWrapper.
