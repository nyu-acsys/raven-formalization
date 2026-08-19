From stdpp Require Export binders strings.
From stdpp Require Import countable.
From stdpp Require Export namespaces.
From stdpp Require Import gmap list sets.

From iris Require Import options.
From iris.algebra Require Import cmra.
From iris.bi Require Import derived_laws.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import ghost_map.
From iris.base_logic.lib Require Import invariants.

From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.

From raven_iris.simp_raven_lang Require Import lang lifting ghost_state.
From raven_iris.rich_raven_lang Require Import rrl_lang.

Require Import iris.base_logic.lib.later_credits.

Section MainTranslation.
    Definition inv_set_to_namespace (s : gset inv_name) : coPset :=
      set_fold (λ inv acc, acc ∪ ↑(inv_namespace_map inv)) ∅ s.

    Lemma inv_map_subseteq invr mask:
      invr ∈ mask -> ↑(inv_namespace_map invr) ⊆ inv_set_to_namespace mask.
    Proof.
      revert mask.
      unfold inv_set_to_namespace.
      apply (set_fold_ind (λ acc s, invr ∈ s → ↑inv_namespace_map invr ⊆ acc)).
    - solve_proper.
    - intros Hcontra. set_solver.
    - intros x s' acc Hnotin IH Hin'.
      destruct (decide (x = invr)) as [->|Hneq].
      + set_solver.
      + set_solver.
    Qed.

    Lemma inv_map_set_minus_subseteq (Hwf : ProgramWF) mask invr:
      invr ∈ mask ->
      invr ∈ inv_set ->
        (inv_set_to_namespace (mask ∖ {[invr]})) = inv_set_to_namespace mask ∖ ↑inv_namespace_map invr.
    Proof.
      intros Hin Hinvset.
      unfold inv_set_to_namespace.
      set (f := λ inv (acc : coPset), acc ∪ ↑inv_namespace_map inv).
      (* pwf_inv_namespace_disjoint has no inv1 ≠ inv2 guard, so applying
         it with invr = invr gives ↑inv_namespace_map invr ## ↑inv_namespace_map invr,
         which implies ↑inv_namespace_map invr = ∅. *)
      have H_self_disj : (↑inv_namespace_map invr : coPset) ## ↑inv_namespace_map invr.
      { exact (Hwf.(pwf_inv_namespace_disjoint) invr invr Hinvset Hinvset). }
      have H_empty : (↑inv_namespace_map invr : coPset) = ∅.
      { apply elem_of_equiv_empty_L. intros x Hx.
        exact (proj1 (elem_of_disjoint (↑inv_namespace_map invr) (↑inv_namespace_map invr)) H_self_disj x Hx Hx). }
      have Hcomm_acc : forall (S : gset inv_name) (b : coPset),
          set_fold f b S = set_fold f ∅ S ∪ b.
      {
        intros S b.
        pose proof (@set_fold_comm_acc inv_name (gset inv_name) _ _ _ _ _ _ _ _ _ coPset f (fun c => c ∪ b) ∅ S) as Hca.
        simpl in Hca.
        rewrite <- Hca.
        - f_equal. set_solver.
        - intros y c. subst f. simpl. set_solver.
      }
      have Hstep : forall (x : inv_name) (Y : gset inv_name),
          x ∉ Y ->
          set_fold f ∅ ({[x]} ∪ Y) = set_fold f ∅ Y ∪ ↑inv_namespace_map x.
      {
        intros x Y Hx.
        assert (Hdisj : ({[x]} : gset inv_name) ## Y) by set_solver.
        have H1 : set_fold f ∅ ({[x]} ∪ Y) = set_fold f (set_fold f ∅ ({[x]} : gset inv_name)) Y.
        { apply (@set_fold_disj_union_strong inv_name (gset inv_name) _ _ _ _ _ _ _ _ _ coPset eq _ f ∅ {[x]} Y).
          - intros y. solve_proper.
          - intros x1 x2 b' _ _ _. subst f. simpl. set_solver.
          - exact Hdisj.
        }
        rewrite H1.
        rewrite (@set_fold_singleton inv_name (gset inv_name) _ _ _ _ _ _ _ _ _ coPset f ∅ x).
        rewrite Hcomm_acc.
        subst f. simpl. set_solver.
      }
      pose proof (union_difference_singleton_L invr mask Hin) as Hmask_split.
      have Hmask_eq : set_fold f ∅ mask = set_fold f ∅ (mask ∖ {[invr]}).
      {
        transitivity (set_fold f ∅ ({[invr]} ∪ (mask ∖ {[invr]}))).
        - f_equal. exact Hmask_split.
        - rewrite Hstep.
          + rewrite H_empty. set_solver.
          + intro Hc. apply elem_of_difference in Hc.
            destruct Hc as [_ Hne]. apply Hne. apply elem_of_singleton_2. reflexivity.
      }
      rewrite Hmask_eq. rewrite H_empty. set_solver.
    Qed.

    Lemma trnsl_expr_interp_lexpr_compatibility stk e lexpr lv mp :
      trnsl_expr_lExpr stk e = Some (lexpr) ->
      interp_lexpr lexpr mp = Some lv ->
      expr_step e (symb_stk_to_stk_frm stk mp) (Val (trnsl_lval lv)).
    Proof.
      revert lexpr lv.
      induction e; intros lexpr lv Htrnsl Hinterp; simpl in Htrnsl.
      - (* Var x *)
        destruct (stk !! x) as [lv_name|] eqn:Hlookup; [|discriminate].
        injection Htrnsl as <-. simpl in Hinterp. injection Hinterp as <-.
        apply VarStep. unfold symb_stk_to_stk_frm. simpl.
        rewrite lookup_fmap. rewrite Hlookup. simpl. done.
      - (* Val v *)
        injection Htrnsl as <-. simpl in Hinterp. injection Hinterp as <-.
        rewrite trnsl_lval_trnsl_val_inverse. apply ExprRefl.
      - (* UnOp op e *)
        destruct (trnsl_expr_lExpr stk e) as [le1|] eqn:Hle1; [|discriminate].
        injection Htrnsl as <-.
        destruct op; simpl in Hinterp.
        + (* NotBoolOp *)
          destruct (interp_lexpr le1 mp) as [[b|n| |l]|] eqn:Hv1; try discriminate.
          injection Hinterp as <-.
          apply UnOpStep with (v := lang.LitBool b).
          * exact (IHe le1 (LitBool b) eq_refl Hv1).
          * simpl. done.
        + (* NegOp *)
          destruct (interp_lexpr le1 mp) as [[b|i| |l]|] eqn:Hv1; try discriminate.
          injection Hinterp as <-.
          apply UnOpStep with (v := lang.LitInt i).
          * exact (IHe le1 (LitInt i) eq_refl Hv1).
          * simpl. done.
      - (* BinOp op e1 e2 *)
        destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [|discriminate].
        destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [|discriminate].
        injection Htrnsl as <-.
        destruct op; simpl in Hinterp;
          (* Integer arithmetic ops: AddOp, SubOp, MulOp, DivOp, ModOp *)
          try (destruct (interp_lexpr le1 mp) as [[b1|i1| |l1]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|i2| |l2]|] eqn:Hv2; try discriminate;
               injection Hinterp as <-;
               apply BinOpStep with (v1 := lang.LitInt i1) (v2 := lang.LitInt i2);
               [ exact (IHe1 le1 (LitInt i1) eq_refl Hv1)
               | exact (IHe2 le2 (LitInt i2) eq_refl Hv2)
               | simpl; done ]);
          (* Comparison ops: LtOp, GtOp, LeOp, GeOp — result is LitBool *)
          try (destruct (interp_lexpr le1 mp) as [[b1|i1| |l1]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|i2| |l2]|] eqn:Hv2; try discriminate;
               injection Hinterp as <-;
               apply BinOpStep with (v1 := lang.LitInt i1) (v2 := lang.LitInt i2);
               [ exact (IHe1 le1 (LitInt i1) eq_refl Hv1)
               | exact (IHe2 le2 (LitInt i2) eq_refl Hv2)
               | simpl; done ]);
          (* EqOp *)
          try (destruct (interp_lexpr le1 mp) as [v1|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [v2|] eqn:Hv2; try discriminate;
               injection Hinterp as <-;
               apply BinOpStep with (v1 := trnsl_lval v1) (v2 := trnsl_lval v2);
               [ exact (IHe1 le1 v1 eq_refl Hv1)
               | exact (IHe2 le2 v2 eq_refl Hv2)
               | simpl; rewrite <- val_beq_bool_decide; done ]);
          (* NeOp *)
          try (destruct (interp_lexpr le1 mp) as [v1|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [v2|] eqn:Hv2; try discriminate;
               injection Hinterp as <-;
               apply BinOpStep with (v1 := trnsl_lval v1) (v2 := trnsl_lval v2);
               [ exact (IHe1 le1 v1 eq_refl Hv1)
               | exact (IHe2 le2 v2 eq_refl Hv2)
               | simpl; rewrite bool_decide_not; rewrite <- val_beq_bool_decide; done ]);
          (* Boolean ops: AndOp, OrOp *)
          try (destruct (interp_lexpr le1 mp) as [[b1|n1| |l1]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|n2| |l2]|] eqn:Hv2; try discriminate;
               injection Hinterp as <-;
               apply BinOpStep with (v1 := lang.LitBool b1) (v2 := lang.LitBool b2);
               [ exact (IHe1 le1 (LitBool b1) eq_refl Hv1)
               | exact (IHe2 le2 (LitBool b2) eq_refl Hv2)
               | simpl; done ]).
      - (* IfE e1 e2 e3 *)
        destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [|discriminate].
        destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [|discriminate].
        destruct (trnsl_expr_lExpr stk e3) as [le3|] eqn:Hle3; [|discriminate].
        injection Htrnsl as <-.
        simpl in Hinterp.
        destruct (interp_lexpr le1 mp) as [[b|n| |l]|] eqn:Hcond; try discriminate.
        (* only LitBool b remains; now case split on the boolean *)
        destruct b; simpl in Hinterp.
        + (* condition = true *)
          apply IfETrueEvalStep.
          * exact (IHe1 le1 (LitBool true) eq_refl Hcond).
          * exact (IHe2 le2 lv eq_refl Hinterp).
        + (* condition = false *)
          apply IfEFalseEvalStep.
          * exact (IHe1 le1 (LitBool false) eq_refl Hcond).
          * exact (IHe3 le3 lv eq_refl Hinterp).
      - (* StuckE *)
        injection Htrnsl as <-. simpl in Hinterp. discriminate.
    Qed.

    Lemma trnsl_expr_interp_lexpr_compatibility2 stk e lexpr lv mp :
      trnsl_expr_lExpr stk e = Some (lexpr) ->
      expr_step e (symb_stk_to_stk_frm stk mp) (Val (trnsl_lval lv)) ->
      interp_lexpr lexpr mp = Some lv.
    Proof.
      revert lexpr lv.
      induction e; intros lexpr lv Htrnsl Hstep; simpl in Htrnsl.
      - (* Var x *)
        destruct (stk !! x) as [lv_name|] eqn:Hlookup; [|discriminate].
        injection Htrnsl as <-. simpl.
        inversion Hstep; subst.
        unfold symb_stk_to_stk_frm in H2. simpl in H2.
        rewrite lookup_fmap in H2. rewrite Hlookup in H2. simpl in H2.
        injection H2 as H2. f_equal. exact (trnsl_lval_injective _ _ H2).
      - (* Val v *)
        injection Htrnsl as <-. simpl.
        inversion Hstep; subst.
        f_equal. exact (trnsl_val_trnsl_lval_inverse lv).
      - (* UnOp op e *)
        destruct (trnsl_expr_lExpr stk e) as [le1|] eqn:Hle1; [|discriminate].
        injection Htrnsl as <-.
        inversion Hstep; subst.
        destruct op; simpl.
        + (* NotBoolOp *)
          simpl in H4. destruct v; try discriminate.
          injection H4 as H4.
          pose proof (IHe le1 (LitBool b) eq_refl H3) as Hle.
          rewrite Hle. simpl. f_equal. exact (trnsl_lval_injective (LitBool (negb b)) lv H4).
        + (* NegOp *)
          simpl in H4. destruct v; try discriminate.
          injection H4 as H4.
          pose proof (IHe le1 (LitInt i) eq_refl H3) as Hle.
          rewrite Hle. simpl. f_equal. exact (trnsl_lval_injective (LitInt (-i)) lv H4).
      - (* BinOp op e1 e2 *)
        destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [|discriminate].
        destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [|discriminate].
        injection Htrnsl as <-.
        inversion Hstep; subst.
        rewrite <- (trnsl_lval_trnsl_val_inverse v1) in H4.
        rewrite <- (trnsl_lval_trnsl_val_inverse v2) in H5.
        pose proof (IHe1 le1 (trnsl_val v1) eq_refl H4) as Hle1'.
        pose proof (IHe2 le2 (trnsl_val v2) eq_refl H5) as Hle2'.
        destruct op; simpl in *;
          (* Group 1: arithmetic, comparison, bool ops *)
          try (destruct v1; try discriminate; destruct v2; try discriminate;
               injection H6 as H6;
               symmetry in H6; apply (f_equal trnsl_val) in H6;
               rewrite trnsl_val_trnsl_lval_inverse in H6; simpl in H6; subst lv;
               simpl in Hle1', Hle2'; rewrite Hle1' Hle2'; simpl; done);
          (* EqOp *)
          try (injection H6 as H6;
               symmetry in H6; apply (f_equal trnsl_val) in H6;
               rewrite trnsl_val_trnsl_lval_inverse in H6; simpl in H6; subst lv;
               rewrite Hle1' Hle2'; simpl; f_equal; f_equal;
               rewrite val_beq_bool_decide;
               rewrite trnsl_lval_trnsl_val_inverse; rewrite trnsl_lval_trnsl_val_inverse;
               destruct (bool_decide (v1 = v2)); done);
          (* NeOp *)
          try (injection H6 as H6;
               symmetry in H6; apply (f_equal trnsl_val) in H6;
               rewrite trnsl_val_trnsl_lval_inverse in H6; simpl in H6; subst lv;
               rewrite Hle1' Hle2'; simpl; f_equal; f_equal;
               rewrite bool_decide_not; f_equal;
               rewrite val_beq_bool_decide;
               rewrite trnsl_lval_trnsl_val_inverse; rewrite trnsl_lval_trnsl_val_inverse;
               destruct (bool_decide (v1 = v2)); done).
      - (* IfE e1 e2 e3 *)
        destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [|discriminate].
        destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [|discriminate].
        destruct (trnsl_expr_lExpr stk e3) as [le3|] eqn:Hle3; [|discriminate].
        injection Htrnsl as <-.
        simpl.
        inversion Hstep; subst.
        + (* IfETrueStep: e1 = Val (LitBool true), true branch = Val (trnsl_lval lv) *)
          specialize (IHe1 le1 (LitBool true) eq_refl). specialize (IHe2 le2 lv eq_refl).
          simpl in IHe1, IHe2.
          pose proof (IHe1 (ExprRefl _ _)) as Hcond.
          pose proof (IHe2 (ExprRefl _ _)) as Hbranch.
          rewrite Hcond. exact Hbranch.
        + (* IfEFalseStep: e1 = Val (LitBool false), false branch = Val (trnsl_lval lv) *)
          specialize (IHe1 le1 (LitBool false) eq_refl). specialize (IHe3 le3 lv eq_refl).
          simpl in IHe1, IHe3.
          pose proof (IHe1 (ExprRefl _ _)) as Hcond.
          pose proof (IHe3 (ExprRefl _ _)) as Hbranch.
          rewrite Hcond. exact Hbranch.
        + (* IfETrueEvalStep: eval e1 → LitBool true, eval e2 → lv *)
          pose proof (IHe1 le1 (LitBool true) eq_refl H3) as Hcond.
          pose proof (IHe2 le2 lv eq_refl H5) as Hbranch.
          rewrite Hcond. exact Hbranch.
        + (* IfEFalseEvalStep: eval e1 → LitBool false, eval e3 → lv *)
          pose proof (IHe1 le1 (LitBool false) eq_refl H3) as Hcond.
          pose proof (IHe3 le3 lv eq_refl H5) as Hbranch.
          rewrite Hcond. exact Hbranch.
      - (* StuckE *)
        injection Htrnsl as <-. simpl. inversion Hstep.
    Qed.

    Definition trnsl_hoare_triple (stk_id: stack_id) (p : assertion) (ι1: nat) (msk : maskAnnot) (cmd : stmt) (q : assertion) (ι2: nat) (mp : symb_map) : iProp rrl_lang.Σ :=
        match (trnsl_stmt cmd) with 
        | Error => True
        | None' =>
          match (trnsl_assertion p stk_id mp), 
                (trnsl_assertion q stk_id mp) with
          | p', q' =>
            p' ∗ £ ι1 ={inv_set_to_namespace msk}=∗ q' ∗ £ ι2 
          end
        
        | Some' s =>
          match (trnsl_assertion p stk_id mp), 
                (trnsl_assertion q stk_id mp) with
          | p', q' => 
            {{{ p' ∗ £ ι1 }}}  
              to_rtstmt stk_id s @ (inv_set_to_namespace msk)
            {{{ RET lang.LitUnit; q' ∗ £ ι2}}}
          end
        end
    .

    Lemma fresh_var_trnsl_expr_invariant stk lv e lexpr mp v0:
      fresh_lvar stk lv ->
      trnsl_expr_lExpr stk e = Some lexpr ->
       interp_lexpr lexpr mp = interp_lexpr lexpr (λ x : lvar, if (x =? lv)%string then v0 else mp x).
    Proof.
      intros Hfresh Htrnsl.
      revert lexpr Htrnsl.
      induction e; intros lexpr Htrnsl; simpl in Htrnsl.
      - (* Var x: lexpr = LVar (stk !! x) *)
        destruct (stk !! x) as [lv_name|] eqn:Hlookup; [|discriminate].
        injection Htrnsl as <-. simpl.
        (* lv_name ≠ lv because fresh_lvar stk lv *)
        assert (lv_name ≠ lv) as Hneq.
        { intro Heq. subst lv_name. exact (Hfresh x Hlookup). }
        rewrite <- String.eqb_neq in Hneq. rewrite Hneq. done.
      - (* Val v: lexpr = LVal (trnsl_val v) *)
        injection Htrnsl as <-. simpl. done.
      - (* UnOp op e *)
        destruct (trnsl_expr_lExpr stk e) as [le1|] eqn:Hle1; [|discriminate].
        injection Htrnsl as <-. simpl.
        rewrite (IHe le1 eq_refl). done.
      - (* BinOp op e1 e2 *)
        destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [|discriminate].
        destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [|discriminate].
        injection Htrnsl as <-. simpl.
        rewrite (IHe1 le1 eq_refl) (IHe2 le2 eq_refl). done.
      - (* IfE e1 e2 e3 *)
        destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [|discriminate].
        destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [|discriminate].
        destruct (trnsl_expr_lExpr stk e3) as [le3|] eqn:Hle3; [|discriminate].
        injection Htrnsl as <-. simpl.
        rewrite (IHe1 le1 eq_refl) (IHe2 le2 eq_refl) (IHe3 le3 eq_refl). done.
      - (* StuckE *)
        injection Htrnsl as <-. simpl. done.
    Qed.

    Lemma lexpr_holds_interp_compat lexpr v1 mp v:
      LExpr_holds (LBinOp EqOp lexpr (LVal v1)) mp ->
      interp_lexpr lexpr mp = Some v ->
      v = v1.
    Proof.
      intros H1 H2.
      unfold LExpr_holds in H1.
      simpl in H1. rewrite H2 in H1. injection H1 as H1.
      destruct (val_beq v v1) eqn:Hvb.
      - apply internal_val_dec_bl in Hvb. done.
      - inversion H1.
    Qed.

    (* The four lemmas below exploit the correctness lemmas that
       [Scheme Equality for val] generates:
         internal_val_dec_lb : v1 = v2  → val_beq v1 v2 = true
         internal_val_dec_bl : val_beq v1 v2 = true → v1 = v2
       For [internal_loc_beq_refl], note that [val_beq (LitLoc l) (LitLoc l)]
       reduces definitionally to [internal_loc_beq l l], so the witness
       produced by [internal_val_dec_lb] can be used directly. *)

    Lemma internal_loc_beq_refl l :
      internal_loc_beq l l = true.
    Proof.
      (* val_beq (LitLoc l) (LitLoc l)  ≡  internal_loc_beq l l  by reduction.
         internal_val_dec_lb gives val_beq (LitLoc l) (LitLoc l) = true, which
         Coq accepts as a proof of internal_loc_beq l l = true by δ-equality. *)
      exact (internal_val_dec_lb (LitLoc l) (LitLoc l) eq_refl).
    Qed.

    Lemma val_beq_refl (v : val) : val_beq v v = true.
    Proof.
      (* Straight application of the Scheme-generated "= → beq" direction. *)
      apply internal_val_dec_lb. reflexivity.
    Qed.

    Lemma val_beq_eq (v1 : val) (v2 : val) : val_beq v1 v2 = true -> v1 = v2.
    Proof.
      (* Straight application of the Scheme-generated "beq → =" direction. *)
      apply internal_val_dec_bl.
    Qed.

    Lemma val_beq_neq v1 v2 : val_beq v1 v2 = false -> v1 ≠ v2.
    Proof.
      (* Contrapositive: if v1 = v2 then val_beq v1 v2 = true (val_beq_refl),
         contradicting the hypothesis val_beq v1 v2 = false. *)
      intros Hfalse ->.
      rewrite val_beq_refl in Hfalse. discriminate.
    Qed.

    Lemma expr_interp_well_defined ρ σ stk e mp lexpr:
      stk_type_compat ρ σ stk ->
      env_typ_well_defined σ mp ->
      trnsl_expr_lExpr stk e = Some lexpr ->
      interp_lexpr lexpr mp = None ->
      not (expr_well_defined ρ e).
    Proof.
      intros Hstk Henv Htrnsl Hnone [tp Htp].
      pose proof (lexpr_expr_typ_compat ρ σ stk e lexpr tp Hstk Htrnsl Htp) as Hinf_le.
      pose proof (lexpr_typcheck_well_defined σ mp lexpr tp Henv Hinf_le) as [val Hval].
      rewrite Hnone in Hval. discriminate.
    Qed.

    Lemma fresh_mp_rewrite_LExpr_holds stk lv e lexpr mp v0 : 
      fresh_lvar stk lv -> 
      trnsl_expr_lExpr stk e = Some lexpr -> 
      interp_lexpr lexpr mp = Some v0 -> 
      LExpr_holds (LBinOp EqOp (LVar lv) lexpr)
        (λ x : lvar, if (x =? lv)%string then v0 else mp x).
    Proof. intros Hfresh Htrnsl Hinterp.
      set (mp' := (λ x : lvar, if (x =? lv)%string then v0 else mp x)).
      (* assert (interp_lexpr (LVar lv)) *)
      unfold LExpr_holds. simpl. 
      assert (mp' lv = v0). { subst mp'. simpl. rewrite String.eqb_refl. reflexivity. }
      rewrite H.
      rewrite (fresh_var_trnsl_expr_invariant _ _ _ _ _ v0 Hfresh Htrnsl) in Hinterp.
      rewrite Hinterp. 

      assert (val_beq v0 v0 = true) as Hbeq. { apply val_beq_refl. }
      rewrite Hbeq.
      reflexivity.
    Qed.

    Lemma fresh_mp_rewrite_symb_stk_to_stk_frm_compat stk lvar_x x mp val:
      fresh_lvar stk lvar_x ->
        symb_stk_to_stk_frm (<[x:=lvar_x]> stk)
          (λ x0 : lvar, if (x0 =? lvar_x)%string then val else mp x0) =

          {| locals := <[x:=trnsl_lval val]> (locals (symb_stk_to_stk_frm stk mp))|} .
    Proof. intros Hfresh.
      unfold symb_stk_to_stk_frm. apply f_equal.
      apply map_eq.
      intros i.
      destruct (stk !! i) eqn:HstkI.
      - rewrite lookup_fmap. 
        destruct (String.eqb i x) eqn:H_i_x.
        + apply String.eqb_eq in H_i_x. subst i. simpl.
        rewrite lookup_insert. rewrite lookup_insert. simpl. rewrite String.eqb_refl. done.

        + assert (not (i = x)). { apply String.eqb_neq in H_i_x. done. }

        rewrite lookup_insert_ne. 
          2 : { intro Heq; subst i; contradiction. }

        rewrite lookup_insert_ne. 
          2 : { intro Heq; subst i; contradiction. }
        simpl. rewrite HstkI. simpl. rewrite lookup_fmap. rewrite HstkI. simpl. apply f_equal. apply f_equal.
        assert ((l =? lvar_x)%string = false).
          { unfold fresh_lvar in Hfresh.
        specialize (Hfresh i). rewrite HstkI in Hfresh. apply String.eqb_neq. intro H2. subst lvar_x. contradiction. }
        rewrite H0. done.

      - destruct (String.eqb i x) eqn:H_i_x.
        + apply String.eqb_eq in H_i_x. subst i.
        rewrite lookup_fmap. rewrite lookup_insert.
        rewrite lookup_insert. simpl. rewrite String.eqb_refl. done.
        + apply String.eqb_neq in H_i_x.
          simpl.
          rewrite lookup_fmap. rewrite lookup_insert_ne.
          2 : { intro Heq; subst i; contradiction. }
          rewrite lookup_fmap. rewrite HstkI. simpl.
          rewrite lookup_insert_ne.
          2 : { intro Heq; subst i; contradiction. }
          rewrite HstkI. simpl. done.
    Qed.

    (* Native-Iris restatement of the former [proc_specs_valid] axiom: the operational
       Hoare triple for every procedure in [proc_map] holds. Persistent (□) so it can be
       freely duplicated into every nested call frame; guarded uses of this fact (behind a
       later, via Löb induction) are how [raven_soundness] below discharges it
       without assuming it outright. *)
    (* Parameterized by [σ], the same lvar-typing environment used throughout the
       whole program's verification (matching rrl_validity's own σ parameter) — not
       re-quantified internally, so every use of [all_proc_specs_valid_iris σ] and every
       rrl_validity invocation are talking about the same σ. *)
    Definition all_proc_specs_valid_iris (σ : lvar_typs) : iProp rrl_lang.Σ :=
      □ ∀ proc proc_record stk_vals,
      ⌜proc ∈ proc_set⌝ -∗
      ⌜proc_map !! proc = Some proc_record⌝ -∗

      ∀ precond (postcond : lang.val -> iProp rrl_lang.Σ) stk_id stk_frm mp stmt (msk : maskAnnot),

      (* mp must be well-typed against σ, mirroring the requirement rrl_validity itself needs. *)
      ⌜env_typ_well_defined σ mp⌝ -∗

      ⌜forall v, v ∈ (proc_args_of proc_record) -> is_Some (stk_frm.(locals) !! v.1)⌝ -∗

      ⌜Forall2 (λ var val, stk_frm.(locals) !! var = Some val) (proc_args_of proc_record).*1 stk_vals⌝ -∗

      (* stk_frm is exactly the frame a fresh call/spawn produces (see lang.v's
         RTCallStep/SpawnStep): every declared local (including "#ret_val")
         is present, holding a non-deterministically chosen value of its
         declared type, and nothing else. Needed so a synthesized LStack for
         the procedure's own entry scope can reconstruct stk_frm exactly. *)
      ⌜∀ v tp, (v, tp) ∈ proc_locals_of proc_record ->
          ∃ val, stk_frm.(locals) !! v = Some val ∧ typeOf val = tp⌝ -∗
      ⌜dom stk_frm.(locals) = list_to_set (proc_args_of proc_record).*1 ∪ list_to_set (proc_locals_of proc_record).*1⌝ -∗

      (* the argument values are well-typed against the procedure's own declared
         parameter types, mirroring the static proc_call_args_well_typed check. *)
      ⌜Forall2 (λ arg_decl val, typeOf val = snd arg_decl) (proc_args_of proc_record) stk_vals⌝ -∗

      let subst_map' := val_subst_map (proc_args_of proc_record).*1 stk_vals in

      ⌜trnsl_assertion (subst (proc_precond_of proc_record) subst_map') stk_id mp ≡ precond⌝ -∗
      ⌜∀ ret_val, trnsl_assertion (subst (proc_postcond_of proc_record) (<["#ret_val" := LVal (trnsl_val (ret_val))]> subst_map')) stk_id mp ≡ postcond ret_val⌝ -∗

      ⌜(trnsl_stmt (proc_body_of proc_record) = Some' stmt) \/ (trnsl_stmt (proc_body_of proc_record) = None' /\ stmt = lang.SkipS)⌝ -∗
      {{{ stack_own[stk_id, stk_frm] ∗ precond }}} (to_rtstmt stk_id stmt) @ (inv_set_to_namespace msk)
        {{{ RET lang.LitUnit; ∃ ret_val stk_frm'', stack_own[stk_id, stk_frm''] ∗ ⌜ (locals stk_frm'' !! "#ret_val") = Some ret_val ⌝ ∗ postcond ret_val }}}.

    (* Raven counterpart of all_proc_specs_valid_iris: every procedure's own
       body is provably correct against its own contract via RavenHoareTriple,
       run from a symbolic entry stack synthesized (via a fresh
       proc_entry_lvars) out of its formal args and locals. A plain Prop,
       not an iProp -- raven_soundness below is exactly the bridge from this
       Raven-level statement to the Iris-level all_proc_specs_valid_iris. *)
    Definition all_proc_specs_valid_raven (ρ : pvar_typs) (σ : lvar_typs) : Prop :=
      ∀ proc_name proc_record, proc_map !! proc_name = Some proc_record →
        stmt_well_defined ρ (proc_body_of proc_record) ∧
        ∀ msk (dll : proc_entry_lvars σ proc_record),
          ∃ ι2 stk0' lv_final,
            stk0' !! "#ret_val" = Some lv_final ∧
            RavenHoareTriple ρ σ
              (LAnd (LStack (assoc_map (proc_args_of proc_record ++ proc_locals_of proc_record).*1
                                        (dll_args dll ++ dll_locals dll)))
                 (subst (proc_precond_of proc_record)
                    (lvar_subst_map (proc_args_of proc_record).*1 (dll_args dll))))
              0 (proc_body_of proc_record) msk
              (LAnd (LStack stk0')
                 (subst (proc_postcond_of proc_record)
                    (<["#ret_val" := LVar lv_final]>
                       (lvar_subst_map (proc_args_of proc_record).*1 (dll_args dll)))))
              ι2.

    Theorem rrl_validity ρ σ ι1 ι2 stk_id p msk cmd q
      (Hwf : ProgramWF) :
      stmt_well_defined ρ cmd ->
      forall mp, (env_typ_well_defined σ mp) ->
       ▷ (all_proc_specs_valid_iris σ) ∗ ⌜RavenHoareTriple ρ σ p ι1 cmd msk q ι2⌝
      ⊢  (trnsl_hoare_triple stk_id p ι1 msk cmd q ι2 mp).
    Proof.
      iIntros (Hwelldef mp Henv) "[#Calls %H]".
      iInduction H as
      [ | 
      | ρ σ ι stk mask v fld e old_val new_val lv Hatm HLexpr1 
      | | | | 
      | ρ σ ι1 ι2 stk mask invr args stmt inv_record p q lexprs Hargs Hinv_mask Hinv_record Hstk_tp Hcred subst Hbody IHHbody
      | | | | | | | | ] "IH".
      3: { 
        (* FIELD WRITE *)
        unfold trnsl_hoare_triple.
        simpl.
        destruct (trnsl_stmt (FldWr v fld e)) eqn:Ht. 2: done.
        { inversion Ht. } 

        inversion Ht. simpl. 
        - iIntros (Φ). iModIntro.
          setoid_rewrite trnsl_assertion_unfold.
          iIntros "[[Hstk1 Hstk2] Hcred] HΦ".
          simpl.
          iDestruct "Hstk2" as "[%l [%Hlexpr1 Hlfld]]".
          
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


          { iPureIntro. apply (trnsl_expr_interp_lexpr_compatibility _ _ (LVal new_val)). { done. } done. }
        }

        {
          iModIntro. iIntros "[HstkO [Hlpt Hcred']]".
          iApply "HΦ". iCombine "Hcred" "Hcred'" as "Hcred". rewrite Nat.add_1_r. iFrame.
          iPureIntro. done.
        }

      }

      7: {
        (* INV ACCESS BLOCK *)
        unfold trnsl_hoare_triple.

        pose proof (trnsl_inv_validity' invr lexprs stk_id mp) as Htrnsl_inv_valid.
        rewrite Hinv_record in Htrnsl_inv_valid. simpl in Htrnsl_inv_valid.
        
        destruct (trnsl_stmt (InvAccessBlock invr args stmt)) eqn:Ht. 
        2: { done. }

        
        { 
          destruct (trnsl_assertion (LStack stk) stk_id mp) eqn:Hstack.

          simpl.
          setoid_rewrite trnsl_assertion_unfold. simpl.
          iIntros "[Hpre Hcr]".
          iDestruct "Hpre" as "[Hstk Hrest]".
          rewrite Hinv_record.
          iDestruct "Hrest" as "[#H Hu]".
           
           assert (trnsl_stmt stmt = None'). {
            apply trnsl_stmt_trnsl_atomic_block_none. simpl in Ht. exact Ht. }
           iEval (rewrite H) in "IH".

          iInv "H" as "Hinv".
          { 
            (* inv_namespace mask *)
            apply inv_map_subseteq; try done.
          }

          assert (ι1 = (ι1-1 + 1)) as Hiota. { rewrite Nat.sub_add; [ reflexivity | ]. lia. }
          apply (f_equal lc) in Hiota.
          iEval (rewrite Hiota) in "Hcr".
          iPoseProof ((lc_split (ι1 - 1) 1) with "Hcr") as "[Hcr1 Hcr2]".

          iDestruct (lc_fupd_elim_later with "Hcr2 Hinv") as ">Hinv".

          iCombine "Hstk Hinv Hu" as "Hcomb".
          inversion Hwelldef as [ | | | | | | | | | | | | | inv args' stmt' HInvSet HargsWellDef HBodywelldef | ]; subst stmt' args'.

          
          
          iPoseProof ("IH" with  "[%] [%] [Hcomb Hcr1]") as "IH2"; try iFrame; try done.
          { setoid_rewrite trnsl_assertion_unfold. iFrame.  }
          assert ((inv_set_to_namespace (mask ∖ {[invr]})) = inv_set_to_namespace mask ∖ ↑inv_namespace_map invr) as HInvs. { apply (inv_map_set_minus_subseteq Hwf); try done. }
          rewrite HInvs.
          iDestruct "IH2" as ">IH2".
          setoid_rewrite trnsl_assertion_unfold.
          iDestruct "IH2" as "[[IHs [IHH1 IHH] ] Hcr]".
          iModIntro.
          iFrame "# ∗". done.
        }
        
        { 
          assert (trnsl_stmt stmt = Some' s). {
            apply trnsl_stmt_trnsl_atomic_block_some. simpl in Ht. exact Ht. }
          simpl.
          iIntros (Φ).
          iModIntro.
          setoid_rewrite trnsl_assertion_unfold.
          iIntros "[[Hstk [#HInv Hu]] Hcr] HΦ".

          assert (ι1 = (ι1-1 + 1)) as Hiota. { rewrite Nat.sub_add; [ reflexivity | ]. lia. }
          apply (f_equal lc) in Hiota.
          iEval (rewrite Hiota) in "Hcr".

          iPoseProof ((lc_split (ι1 - 1) 1) with "Hcr") as "[Hcr1 Hcr2]".
          rewrite Hinv_record.
          iInv "HInv" as "HInvBody".
          { 
            (* inv_namespace mask *)
            apply inv_map_subseteq; try done.
          }

          {
            (* atomicity *)
            simpl in Ht.
            apply (trnsl_atomic_block_atomicity stmt); try done. 
          }

          iDestruct (lc_fupd_elim_later with "Hcr2 HInvBody") as ">HInvBody".

          iCombine "Hstk HInvBody Hu" as "Hcomb".
          (* iCombine "Hcomb1"  as "Hcomb2". *)

          assert (HInvSet0 : invr ∈ inv_set) by (inversion Hwelldef; done).
          assert (inv_set_to_namespace (mask ∖ {[invr]}) = inv_set_to_namespace mask ∖ ↑inv_namespace_map invr) as H0. { apply inv_map_set_minus_subseteq; try done. }
          rewrite H0; destruct H0.

          inversion Hwelldef as [ | | | | | | | | | | | | | inv args' stmt' HInvSet HargsWellDef HBodywelldef | ]; subst stmt' args'.
          iEval (rewrite H) in "IH".
          iApply ("IH" with "[%] [%] [Hcomb Hcr1]"); try iFrame; try done.
          { rewrite Htrnsl_inv_valid. setoid_rewrite trnsl_assertion_unfold. iFrame. }
          iNext.
          setoid_rewrite trnsl_assertion_unfold.
          iIntros "[[Hstk [Hu Hu1]] Hcr]".
          iModIntro.
          iFrame.
          iApply "HΦ".
          iFrame "# ∗".
          rewrite Hinv_record.
          setoid_rewrite trnsl_assertion_unfold. iExact "HInv".
        }
      }

      1 : {
        (* ASSIGN *)
        unfold trnsl_hoare_triple. simpl.

        iIntros (Φ).
        iModIntro.
        iIntros "[Hstk Hcr] HΦ".

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
          iIntros "[Hstk Hcr1]".
          iApply "HΦ".
          iCombine "Hcr" "Hcr1" as "Hcr". rewrite Nat.add_1_r. iFrame.
          setoid_rewrite trnsl_assertion_unfold.
          iExists (v0).
          iSplitL.
          {
            (* simpl. *)
            (unfold rrl_lang.symb_stk_to_stk_frm). simpl. unfold fresh_lvar in H0.
            assert (<[v:=trnsl_lval v0]> ((λ v1 : lvar, trnsl_lval (mp v1)) <$> stk)
                =
              (λ v1 : lvar, trnsl_lval (if (v1 =? lv)%string then v0 else mp v1)) <$>
                <[v:=lv]> stk).
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
                  + assert (x ≠ lv). { specialize (H0 i). rewrite HstkI in H0. intros Heq. subst x. contradiction.
                  } simpl.
                  rewrite HstkI. simpl. f_equal. rewrite <- String.eqb_neq in H2. rewrite H2. auto.

                  + rewrite HstkI. simpl. done.
              } rewrite H2. done.

          }
          iPureIntro.

          apply (fresh_mp_rewrite_LExpr_holds stk lv e lexpr mp v0 H0 H Hlexpr).
        }

        assert (Hstk_compat: stk_type_compat ρ σ stk) by assumption.
        pose proof (expr_interp_well_defined ρ σ stk e mp lexpr Hstk_compat Henv H Hlexpr).
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

          iIntros "[[Hu Hu1] Hcr]".
          iPoseProof ("IH2" with "[%] [Hu Hcr]") as ">[IH3 Hcr']"; try iFrame; try done.

        }

        {
          iIntros (Φ).
          setoid_rewrite trnsl_assertion_unfold.
          iModIntro. iIntros "[[Hu Hu1] Hcr] HΦ".
          iApply ("IH2" with "[%] [Hu Hcr]"); try iFrame; try done.
          iNext. iIntros "[Hu0 Hcr']". iApply "HΦ". iFrame.
        }
      }

      1 : {
        (* FIELD READ *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ). setoid_rewrite trnsl_assertion_unfold. iModIntro. iIntros "[[Hstk Hl] Hcr] HΦ".
        iDestruct "Hl" as (l) "[%HLe_h H_l_hp]".

        destruct (interp_lexpr lexpr_e mp) eqn: Hinterp.

        2 : { assert (Hstk_compat: stk_type_compat ρ σ stk) by assumption.
          apply (expr_interp_well_defined ρ σ stk e mp lexpr_e Hstk_compat Henv H) in Hinterp.
          inversion Hwelldef. contradiction.
        }

        pose proof (lexpr_holds_interp_compat _ _ _ _ HLe_h Hinterp). subst v.

        iApply (wp_heap_rd stk_id (rrl_lang.symb_stk_to_stk_frm stk mp) fld e (trnsl_lval val) l x _ 1%Qp with "[Hstk H_l_hp]").

        {
          pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H Hinterp).
          iFrame.
          iPureIntro. 
          simpl in H1.
          assert (l = {| loc_car := loc_car l |}).
          { destruct l. simpl. done.  }
          rewrite H3. done. 
        }

        {
          iNext.
          iIntros "[Hstk [Hhp Hcr']]".
          iApply "HΦ". iCombine "Hcr" "Hcr'" as "Hcr". rewrite Nat.add_1_r. iFrame.
          iExists val.

          iSplitL "Hstk".
          - pose proof (fresh_mp_rewrite_symb_stk_to_stk_frm_compat stk lvar_x x mp val H0) as HstkOwnDone.
            rewrite HstkOwnDone. iFrame.

          - iSplitL.
            + iPureIntro.
              pose proof (fresh_var_trnsl_expr_invariant stk lvar_x e _ mp val H0 H).
              unfold LExpr_holds.
              simpl. rewrite <- H2. apply HLe_h.
          
            + iPureIntro. unfold LExpr_holds. simpl. rewrite String.eqb_refl. rewrite val_beq_refl. done.
        }
      }

      1 : {
        (* ALLOC *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ).
        iModIntro.
        iIntros "[Hstack Hcr] HΦ".
        iApply (wp_alloc with "[Hstack]") .
        - done.
        - setoid_rewrite trnsl_assertion_unfold. iFrame.
        - iNext.
          iIntros "Hpost".
          iDestruct "Hpost" as (l) "[Hstk [Hhp Hcr']]".
          iApply "HΦ". iCombine "Hcr" "Hcr'" as "Hcr". rewrite Nat.add_1_r. iFrame.
          setoid_rewrite trnsl_assertion_unfold.
          iExists (LitLoc l).
          set (mp' := (λ x0 : lvar, if (x0 =? lvar_x)%string then LitLoc l else mp x0)).

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
              inversion H0.
              iPoseProof ("IH2" $! H5 with "Hstk Hhpfvs") as "[IH3 IH3']". 
              iFrame. iExists l. 
              assert (trnsl_lval (trnsl_val val) = val) as H1'. { apply trnsl_lval_trnsl_val_inverse. } 
              rewrite H1'. iFrame.
              iPureIntro. 
              unfold LExpr_holds.
              simpl.
              subst mp'. simpl. rewrite String.eqb_refl. rewrite val_beq_refl. done.
      }

      4 : {
        (* UNFOLD PRED *)
        unfold trnsl_hoare_triple.
        simpl.
        pose proof (trnsl_pred_validity' pred lexprs stk_id mp) as HPredTrnsl. rewrite H0 in HPredTrnsl. unfold subst_map in HPredTrnsl. setoid_rewrite trnsl_assertion_unfold in HPredTrnsl. 
        setoid_rewrite trnsl_assertion_unfold.
        simpl.
        rewrite <- HPredTrnsl.
        iIntros "[[Hstk Hpred] Hcr]".
        iPoseProof ((lc_split ι 1) with "Hcr") as "[Hcr1 Hcr2]".

        iDestruct (lc_fupd_elim_later with "Hcr2 Hpred") as ">Hpred".
        iFrame. done.

      }

      4 : {
        (* FOLD PRED *)
        unfold trnsl_hoare_triple.
        simpl.
        pose proof (trnsl_pred_validity' pred lexprs stk_id mp) as HPredTrnsl. rewrite H1 in HPredTrnsl. unfold subst_map in HPredTrnsl. setoid_rewrite trnsl_assertion_unfold. simpl. rewrite H1. rewrite HPredTrnsl.
        iIntros "[[Hstk HPred] Hcr]". iModIntro. rewrite <- HPredTrnsl. iFrame. iNext. setoid_rewrite trnsl_assertion_unfold. iFrame.
      }

      2 : {
        (* SEQ *)
        inversion Hwelldef.
        iPoseProof ("IH" with "[%]") as "IH'"; try done.
        iPoseProof ("IH1" with "[%]") as "IH1'"; try done.
        iClear "IH IH1".

        unfold trnsl_hoare_triple. 
        simpl.
        - destruct (trnsl_stmt c1) eqn:Hc1, (trnsl_stmt c2) eqn:Hc2; try done.
          +  iIntros "Hu0".
          iPoseProof ("IH'" with "[%] Hu0") as ">IHH"; try done.
           iApply "IH1'"; try done.

          + iIntros (Φ). iModIntro. iIntros "Hu0 HΦ".
            iPoseProof ("IH'" with "[%] Hu0") as ">IHH"; try done.
            iApply ("IH1'" with "[%] IHH"); try done.

          + iIntros (Φ) "!> [Hu0 Hcr] HΦ".
            iApply wp_fupd.
            iApply ("IH'" $! Henv with "[$Hu0 $Hcr]").
            iNext. iIntros "Hmid".
            iPoseProof ("IH1'" $! Henv with "Hmid") as "Hpost".
            iMod "Hpost". iModIntro. iApply "HΦ". iFrame.

          + simpl.
            iApply wp_seq.
              { iApply "IH'"; try done. }
              { iApply "IH1'"; try done. }
      }

      5 : {
        (* SKIP *)
        unfold trnsl_hoare_triple. simpl.
        iIntros (Φ). iModIntro. iIntros "[Hp Hcr] HΦ".
        iApply (wp_skip with "Hp"). 
        iNext. setoid_rewrite trnsl_assertion_unfold. iIntros "[[Hstk Hu] Hcr']". iApply "HΦ". iCombine "Hcr" "Hcr'" as "Hcr". iFrame.
      }

      5: {
        (* CAS SUCC *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ). iModIntro. setoid_rewrite trnsl_assertion_unfold. iIntros "[[Hstk He1] Hcr] HΦ".
        iDestruct "He1" as (l) "[%He1 Hl]".
        assert (interp_lexpr (LVal old_val) mp = Some old_val) as Hinterp_old; try done.
        assert (interp_lexpr (LVal new_val) mp = Some new_val) as Hinterp_new; try done.
        pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H2 Hinterp_old) as Hexpr_step_e2.
        pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H3 Hinterp_new) as Hexpr_step_e3.
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
        
        pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H1 Hlexpr1) as Hexpr_step_e1.

        iApply (wp_cas_succ v e1 fld e2 e3 stk_id (symb_stk_to_stk_frm stk mp) l (trnsl_lval old_val) (trnsl_lval new_val) with "[Hstk Hl]"); try done.
        
        { assert (trnsl_lval (LitLoc l) = (lang.LitLoc l)).
        - simpl. destruct l. simpl. done.
        - rewrite -> H5 in *. done. }

        { iFrame. }

        iNext. iIntros "[Hstk [Hl Hcr']]".
        iApply "HΦ". iCombine "Hcr" "Hcr'" as "Hcr". rewrite Nat.add_1_r. iFrame.
        iExists (LitBool true).
        iSplitL "Hstk".
        - rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done.

        - iSplitL.
        { 
          iPureIntro. apply EqOp_refl. 
          unfold LExpr_holds. simpl. 
          rewrite <- (fresh_var_trnsl_expr_invariant stk lvar_v e1 lexpr1 mp (LitBool true)); try done. rewrite Hlexpr1. 
          assert (internal_loc_beq l l = true) as H_l_l. { apply internal_loc_beq_refl. } 
          rewrite H_l_l. done.
        }

         iPureIntro.
         unfold LExpr_holds. simpl. rewrite String.eqb_refl. rewrite val_beq_refl. done.
      }

      5 : {
        (* CAS FAIL *)
        unfold trnsl_hoare_triple; simpl.
        iIntros (Φ). iModIntro. setoid_rewrite trnsl_assertion_unfold. iIntros "[[Hstk [He1 %Hneq]] Hcr] HΦ".
        iDestruct "He1" as (l) "[%He1 Hl]".
        assert (interp_lexpr (LVal old_val2) mp = Some old_val2) as Hinterp_old; try done.
        pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H2 Hinterp_old) as Hexpr_step_e2.
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
        
        pose proof (trnsl_expr_interp_lexpr_compatibility _ _ _ _ _ H1 Hlexpr1) as Hexpr_step_e1.

        iApply (wp_cas_fail v e1 fld e2 e3 stk_id (symb_stk_to_stk_frm stk mp) l (trnsl_lval old_val2) (trnsl_lval old_val) _ with "[Hstk Hl]"); try done.
        
        - assert (trnsl_lval (LitLoc l) = (lang.LitLoc l)) as H4. { simpl. destruct l. simpl. done. }
        { rewrite -> H4 in *. done. }

        - unfold LExpr_holds in Hneq.
          simpl in Hneq. injection Hneq as Hneq.

          assert (val_beq old_val old_val2 = false) as Hbeq.
          { simpl in Hneq.
          move: Hneq. by case (val_beq old_val old_val2). }

          apply val_beq_neq in Hbeq.
          assert (trnsl_lval old_val ≠ trnsl_lval old_val2) as Hneq2.
          { intros Heq. apply Hbeq. apply (trnsl_lval_injective _ _ Heq). }
          done.

        - iFrame.

        - iNext. iIntros "[Hstk [Hl Hcr']]".
          iApply "HΦ".
          iCombine "Hcr" "Hcr'" as "Hcr". rewrite Nat.add_1_r. iFrame.
          iExists (LitBool false).
          iSplitL "Hstk".

          { rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done. }
          
          iSplitL.
          { 
            iPureIntro. unfold LExpr_holds. simpl. 
            rewrite <- (fresh_var_trnsl_expr_invariant stk lvar_v e1 lexpr1 mp (LitBool false)); try done. rewrite Hlexpr1. rewrite val_beq_refl.
            done.
          }

          { 
            iPureIntro. unfold LExpr_holds; simpl.
            apply f_equal. rewrite String.eqb_refl. rewrite val_beq_refl. done.
          }
      }

      4 : {
        (* WEAKENING *)
        unfold entails in *.
        unfold trnsl_hoare_triple. simpl.
        specialize H0 with stk_id mp.
        destruct H0 as [P' [P [HP' [HP HP_ent_P']]]].
        
        specialize H1 with stk_id mp.
        destruct H1 as [Q [Q' [HQ [HQ' HQ_ent_Q']]]].
        rewrite HP HP' HQ HQ'.

        destruct (trnsl_stmt c) eqn:HtrnslStmt; try done.

        - 
        iPoseProof ("IH" with "[%]") as "IH2"; try done.
        iIntros "[HP' Hcr]".
        iPoseProof ("IH2" with "[%] [HP' Hcr]") as "HII"; try iFrame; try done.
        { iApply HP_ent_P'. iFrame. }
        iDestruct  "HII" as ">[HQ Hcr]" . iModIntro. iFrame.
        iApply HQ_ent_Q'.
        iFrame.

        -
        iPoseProof ("IH" with "[%]") as "IH2"; try done.
        iIntros (Φ). iModIntro. iIntros "[HP' Hcr] HΦ".
        iApply ("IH2" with "[%] [HP' Hcr]"); try iFrame; try done.
          + iApply HP_ent_P'. iFrame.
          + iNext. iIntros "[HQ Hcr]". iApply "HΦ". iFrame. iApply HQ_ent_Q'. iFrame.
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
          unfold typeOf in Hle_typ. destruct (trnsl_lval val0) eqn:Hle_val; try done.
          unfold trnsl_lval in Hle_val. destruct (val0) eqn: Hle_val'; try done.

        destruct (trnsl_stmt s1) eqn:Hs1, (trnsl_stmt s2) eqn:Hs2; try done.

        - destruct b0.

          + setoid_rewrite trnsl_assertion_unfold. iIntros "[[Hstk Hu] Hcr]".

          iPoseProof ("IH'" with "[%] [Hstk Hu Hcr]") as "Hpost"; try iFrame; try done.
          { unfold LExpr_holds. rewrite Hinterp_lexpr. done. }

          iDestruct "Hpost" as ">[[Hstk Hu0] Hcr2]".

          assert (ι2 = ι2 `min` ι3 + (ι2 - ι2 `min` ι3)) as Hiota. { lia.  }
          apply (f_equal lc) in Hiota.
          iEval (rewrite Hiota) in "Hcr2".

          iDestruct (lc_split (ι2 `min` ι3) (ι2 - (ι2 `min` ι3)) with "Hcr2") as "[Hcr2 Hcr2']".

          iFrame. iModIntro. done.
          
          + setoid_rewrite trnsl_assertion_unfold. iIntros "[[Hstk Hu] Hcr]".

          iPoseProof ("IH1'" with "[%] [Hstk Hu Hcr]") as "Hpost"; try iFrame; try done.
          { unfold LExpr_holds. simpl.  rewrite Hinterp_lexpr. done. }

          iDestruct "Hpost" as ">[[Hstk Hu0] Hcr2]".

          assert (ι3 = ι2 `min` ι3 + (ι3 - ι2 `min` ι3)) as Hiota. { lia.  }
          apply (f_equal lc) in Hiota.
          iEval (rewrite Hiota) in "Hcr2".

          iDestruct (lc_split (ι2 `min` ι3) (ι3 - (ι2 `min` ι3)) with "Hcr2") as "[Hcr2 Hcr2']".
          iFrame.
          done.
        - iIntros (Φ). iModIntro. setoid_rewrite trnsl_assertion_unfold. iIntros "[[Hstk Hu] Hcr] HΦ".
          destruct b0.
          + iApply (wp_if_t e (RTSkipS stk_id) (to_rtstmt stk_id s) stk_id (symb_stk_to_stk_frm stk1 mp) ((trnsl_assertion p stk_id mp) ∗ £ι1) (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ (trnsl_assertion q stk_id mp) ∗ £ι2) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu Hcr] [HΦ]"); try iFrame.
            *  apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool true) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk [Hu Hcr]] HΦ'".
            setoid_rewrite trnsl_assertion_unfold.
            iPoseProof ("IH'" with "[%] [Hstk Hu Hcr]" ) as "HQ"; try done; try iFrame.
            { iPureIntro. unfold LExpr_holds. rewrite Hinterp_lexpr. done.  }
            simpl.
            iDestruct "HQ" as ">[[Hstk Hu] Hcr]". iApply (wp_skip (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ (trnsl_assertion q stk_id mp)) with "[Hstk Hu]"); iFrame.
            { setoid_rewrite trnsl_assertion_unfold. iFrame. }
            iNext. iIntros "[[Hstk Hu] Hcr']". iApply "HΦ'". setoid_rewrite trnsl_assertion_unfold. iFrame.
            
            * setoid_rewrite trnsl_assertion_unfold. iFrame.


            * iNext. iIntros "[Hstk [Hu Hcr]]". iApply "HΦ". iFrame.

            assert (ι2 = ι2 `min` ι3 + (ι2 - ι2 `min` ι3)) as Hiota. { lia.  }
            apply (f_equal lc) in Hiota.
            iEval (rewrite Hiota) in "Hcr".
            iDestruct (lc_split (ι2 `min` ι3) (ι2 - (ι2 `min` ι3)) with "Hcr") as "[Hcr2 Hcr2']". setoid_rewrite trnsl_assertion_unfold. iFrame.
          
          + iApply (wp_if_f e (RTSkipS stk_id) (to_rtstmt stk_id s) stk_id (symb_stk_to_stk_frm stk1 mp) ((trnsl_assertion p stk_id mp) ∗ £ι1) (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ (trnsl_assertion q stk_id mp) ∗ £ι3) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu Hcr] [HΦ]"); try iFrame.
            * apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool false) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk [Hu Hcr]] HΦ'".
            setoid_rewrite trnsl_assertion_unfold.
            iPoseProof ("IH1'" with "[%] [Hstk Hu Hcr]" ) as "HQ"; try done; try iFrame.
            { iPureIntro. unfold LExpr_holds. simpl. rewrite Hinterp_lexpr. done.  }
            iApply "HQ"; iFrame. iNext.
            iIntros "[[Hstk Hu] Hcr]". iApply "HΦ'". iFrame.

            * setoid_rewrite trnsl_assertion_unfold. iFrame.

            * iNext. iIntros "[Hstk [Hu Hcr]]". iApply "HΦ". iFrame.

            assert (ι3 = ι2 `min` ι3 + (ι3 - ι2 `min` ι3)) as Hiota. { lia. }
            apply (f_equal lc) in Hiota.
            iEval (rewrite Hiota) in "Hcr".
            iDestruct (lc_split (ι2 `min` ι3) (ι3 - (ι2 `min` ι3)) with "Hcr") as "[Hcr2 Hcr2']". setoid_rewrite trnsl_assertion_unfold. iFrame.

        - iIntros (Φ). iModIntro. setoid_rewrite trnsl_assertion_unfold. iIntros "[[Hstk Hu] Hcr] HΦ".
          destruct b0.
          + iApply (wp_if_t e (to_rtstmt stk_id s) (RTSkipS stk_id) stk_id (symb_stk_to_stk_frm stk1 mp) ((trnsl_assertion p stk_id mp) ∗ £ι1) (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ (trnsl_assertion q stk_id mp) ∗ £ι2) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu Hcr] [HΦ]"); try iFrame.
            *  apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool true) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk [Hu Hcr]] HΦ'".
            setoid_rewrite trnsl_assertion_unfold.
            iPoseProof ("IH'" with "[%] [Hstk Hu Hcr]" ) as "HQ"; try done; try iFrame.
            { iPureIntro. unfold LExpr_holds. rewrite Hinterp_lexpr. done.  }
            iApply "HQ"; iFrame. iNext. iIntros "[[Hstk Hu] Hcr]". iApply "HΦ'". iFrame.

            * setoid_rewrite trnsl_assertion_unfold. iFrame.

            * iNext. iIntros "[Hstk [Hu Hcr]]". iApply "HΦ". iFrame.
            assert (ι2 = ι2 `min` ι3 + (ι2 - ι2 `min` ι3)) as Hiota. { lia. }
            apply (f_equal lc) in Hiota.
            iEval (rewrite Hiota) in "Hcr".
            iDestruct (lc_split (ι2 `min` ι3) (ι2 - (ι2 `min` ι3)) with "Hcr") as "[Hcr2 Hcr2']". setoid_rewrite trnsl_assertion_unfold. iFrame.

          
          + iApply (wp_if_f e (to_rtstmt stk_id s) (RTSkipS stk_id) stk_id (symb_stk_to_stk_frm stk1 mp) ((trnsl_assertion p stk_id mp) ∗ £ι1) (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ (trnsl_assertion q stk_id mp) ∗ £ι3) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu Hcr] [HΦ]"); try iFrame.
            * apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool false) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk [Hu Hcr]] HΦ'".
            setoid_rewrite trnsl_assertion_unfold.
            iPoseProof ("IH1'" with "[%] [Hstk Hu Hcr]" ) as "HQ"; try done; try iFrame.
            { iPureIntro. unfold LExpr_holds. simpl. rewrite Hinterp_lexpr. done. }
            
            iDestruct "HQ" as ">[[Hstk Hu] Hcr]". iApply (wp_skip (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ (trnsl_assertion q stk_id mp)) with "[Hstk Hu]"); iFrame.
            { setoid_rewrite trnsl_assertion_unfold. iFrame. }
            iNext. iIntros "[[Hstk Hu] Hcr']". iApply "HΦ'". setoid_rewrite trnsl_assertion_unfold. iFrame.

            * setoid_rewrite trnsl_assertion_unfold. iFrame.
            * iNext. iIntros "[Hstk [Hu Hcr]]". iApply "HΦ". iFrame.
            
            assert (ι3 = ι2 `min` ι3 + (ι3 - ι2 `min` ι3)) as Hiota. { lia. }
            apply (f_equal lc) in Hiota.
            iEval (rewrite Hiota) in "Hcr".
            iDestruct (lc_split (ι2 `min` ι3) (ι3 - (ι2 `min` ι3)) with "Hcr") as "[Hcr2 Hcr2']". setoid_rewrite trnsl_assertion_unfold. iFrame.

        - iIntros (Φ). iModIntro. setoid_rewrite trnsl_assertion_unfold. iIntros "[[Hstk Hu] Hcr] HΦ".
          destruct b0.
          + iApply (wp_if_t e (to_rtstmt stk_id s) (to_rtstmt stk_id s0) stk_id (symb_stk_to_stk_frm stk1 mp) ((trnsl_assertion p stk_id mp) ∗ £ι1) (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ (trnsl_assertion q stk_id mp) ∗ £ι2) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu Hcr] [HΦ]"); try iFrame.
            *  apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool true) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk [Hu Hcr]] HΦ'".
            setoid_rewrite trnsl_assertion_unfold.
            iPoseProof ("IH'" with "[%] [Hstk Hu Hcr]" ) as "HQ"; try done; try iFrame.
            { iPureIntro. unfold LExpr_holds. rewrite Hinterp_lexpr. done.  }
            iApply "HQ"; iFrame. iNext. iIntros "[[Hstk Hu] Hcr]". iApply "HΦ'". iFrame.

            * setoid_rewrite trnsl_assertion_unfold. iFrame.

            * iNext. iIntros "[Hstk [Hu Hcr]]". iApply "HΦ". iFrame.
            assert (ι2 = ι2 `min` ι3 + (ι2 - ι2 `min` ι3)) as Hiota. { lia.  }
            apply (f_equal lc) in Hiota.
            iEval (rewrite Hiota) in "Hcr".
            iDestruct (lc_split (ι2 `min` ι3) (ι2 - (ι2 `min` ι3)) with "Hcr") as "[Hcr2 Hcr2']". setoid_rewrite trnsl_assertion_unfold. iFrame.
            
          + iApply (wp_if_f e (to_rtstmt stk_id s) (to_rtstmt stk_id s0) stk_id (symb_stk_to_stk_frm stk1 mp) ((trnsl_assertion p stk_id mp) ∗ £ι1) (stack_own[ stk_id, symb_stk_to_stk_frm stk2 mp] ∗ (trnsl_assertion q stk_id mp) ∗ £ι3) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu Hcr] [HΦ]"); try iFrame.
            * apply (trnsl_expr_interp_lexpr_compatibility _ e lexpr (LitBool false) mp); try done.

            * iIntros (Φ'). iModIntro. iIntros "[Hstk [Hu Hcr]] HΦ'".
            setoid_rewrite trnsl_assertion_unfold.
            iPoseProof ("IH1'" with "[%] [Hstk Hu Hcr]" ) as "HQ"; try done; try iFrame.
            { iPureIntro. unfold LExpr_holds. simpl. rewrite Hinterp_lexpr. done. }
            iApply "HQ"; iFrame. iNext. iIntros "[[Hstk Hu] Hcr]". iApply "HΦ'". iFrame.

            * setoid_rewrite trnsl_assertion_unfold. iFrame.

            * iNext. iIntros "[Hstk [Hu Hcr]]". iApply "HΦ". iFrame.

            assert (ι3 = ι2 `min` ι3 + (ι3 - ι2 `min` ι3)) as Hiota. { lia.  }
            apply (f_equal lc) in Hiota.
            iEval (rewrite Hiota) in "Hcr".
            iDestruct (lc_split (ι2 `min` ι3) (ι3 - (ι2 `min` ι3)) with "Hcr") as "[Hcr2 Hcr2']". setoid_rewrite trnsl_assertion_unfold. iFrame.

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

        inversion Hwelldef; subst ρ0 v proc args0.

        assert (exists arg_vals, Forall2 (fun e v => expr_step e (symb_stk_to_stk_frm stk mp) (Val v)) args arg_vals) as Harg_vals.

        {
          (* Save stk_type_compat before clearing *)
          assert (Hstk_compat: stk_type_compat ρ σ stk) by assumption.
          (* Prove existence of arg_vals *)
          clear Hwelldef H1 H4 H11 H13.
          clear subst_map.
          revert lexprs H2 H12.
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
            clear Hwelldef H1 H4 H11 H12 H13 subst_map.
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
        { rewrite H0 in H9. injection H9 as <-. done. }
        rewrite Hpe in H13.

        assert (Forall2 (λ arg_decl val, typeOf val = snd arg_decl)
                  (proc_args_of (Proc proc_args proc_locals proc_pre proc_post proc_body)) arg_vals)
          as Harg_vals_typed.
        { apply (proc_call_args_typed_result ρ σ stk mp args lexprs arg_vals
            (Proc proc_args proc_locals proc_pre proc_post proc_body) H3 Henv H13 H2 Hlexprs_arg_vals). }

        set (trnsl_assertion (subst proc_pre subst_map) stk_id mp) as u1.

        assert (trnsl_assertion (subst proc_pre subst_map) stk_id mp ≡ u1) as Hproc_pre.
            { subst u1; reflexivity. }

        destruct (trnsl_stmt (proc_body)) eqn:Hproc_body;  try discriminate.

        
        {
          (* proc_body = Skip *)
        inversion H4; subst s.
        iIntros (Φ). iModIntro. setoid_rewrite trnsl_assertion_unfold.

        iIntros "[[Hstk [Hproc_tbl Hu1]] Hcr] HΦ".

        set (subst_map' := @list_to_map var LExpr (gmap var LExpr) _ _ (zip (proc_args).*1 (map (λ val, LVal (trnsl_val val)) arg_vals))).

          set ((trnsl_assertion (subst proc_pre subst_map') stk_id mp)) as proc_frame_pre.
          set (fun ret_val => trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id mp) as proc_frame_post.

        iApply (wp_call _ _ _ _ _ _ (lang.Proc proc_name proc_args proc_locals _) _ u1 proc_frame_post with "[] [Hstk Hproc_tbl Hu1]"); try iFrame; try done.

          {
            (* Showing procedure contract holds, via the ambient (Löb-guarded) Calls fact *)
            iNext.
            iIntros (stk_id' stk_frm') "%HlocalsDef". destruct HlocalsDef as [HlocalsDef [Hrv_val Hdom_val]]. simpl in *.

            iPoseProof ("Calls" $! proc_name (Proc proc_args proc_locals proc_pre proc_post proc_body) arg_vals with "[%]") as "Calls'".
            { done. }
            iPoseProof ("Calls'" with "[%]") as "Hproc".
            { exact H0. }

            iSpecialize ("Hproc" $! proc_frame_pre proc_frame_post stk_id' stk_frm' mp lang.SkipS mask).

            iSpecialize ("Hproc" with "[%]"). { exact Henv. }

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

          have Hproc_frame_pre' : trnsl_assertion (subst proc_pre subst_map') stk_id' mp ≡ proc_frame_pre.
          { etransitivity.
            - symmetry. apply (stack_free_assertion_trnsl _ stk_id stk_id' mp).
              apply (stack_free_assertion_subst Hwf). destruct Hspec_StackFree; done.
            - exact Hproc_frame_pre. }

          iSpecialize ("Hproc" with "[%]"). { exact Harg_vals_typed. }

          iSpecialize ("Hproc" with "[%]"). { exact Hproc_frame_pre'. }

          have Hproc_frame_post_all : ∀ ret_val,
              trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id' mp ≡ proc_frame_post ret_val.
          { intros ret_val. etransitivity.
            - symmetry. apply (stack_free_assertion_trnsl _ stk_id stk_id' mp).
              apply (stack_free_assertion_subst Hwf). destruct Hspec_StackFree; done.
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

            have HfvA : assertion_lexpr_fvars proc_pre ⊆ dom (list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr).
            { have Hfv := proj1 (Hwf.(pwf_proc_fvars_bounded) proc_name _ H0).
              have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ HlocalsDef. have := Forall2_length _ _ _ Hlexprs_arg_vals. lia. }
              rewrite dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). exact Hfv. }
            have HdomEq : dom (list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr) = dom (list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr).
            { have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ HlocalsDef. have := Forall2_length _ _ _ Hlexprs_arg_vals. lia. }
              have Hlen2 : length proc_args.*1 ≤ length (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals). { rewrite map_length. have := Forall2_length _ _ _ HlocalsDef. lia. }
              rewrite !dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). rewrite (fst_zip _ _ Hlen2). reflexivity. }
            pose proof (trnsl_assertion_w_lexpr_subst proc_pre lexprs proc_args.*1 arg_vals stk_id mp u1 proc_frame_pre
              Hwf (proj1 Hspec_StackFree)
              (proj1 (Hwf.(pwf_proc_binders_fresh) proc_name _ _ H0))
              (proj1 (Hwf.(pwf_proc_binders_fresh) proc_name _ _ H0))
              HfvA HdomEq
              Hlexprs_arg_vals Hproc_pre Hproc_frame_pre) as Himpl.
            iApply Himpl. iFrame.
          }


          iNext. iExact "HΦ".
          }

          { rewrite Hproc_body. iFrame. setoid_rewrite <- trnsl_assertion_unfold. iFrame. }

          {
            iNext. iIntros "[%ret_val [Hstk [Hq Hcr']]]".

            have Hproc_frame_post : trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id mp ≡ proc_frame_post ret_val.
            { reflexivity. }

            iApply "HΦ". iCombine "Hcr Hcr'" as "Hcr". rewrite Nat.add_1_r. iFrame. iExists (trnsl_val ret_val).

            set (trnsl_assertion (subst proc_post (<["#ret_val":=LVar lvar_x]> subst_map)) stk_id
            (λ x0 : lvar, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0)) as u.

            assert ((trnsl_assertion (subst proc_post (<["#ret_val":=LVar lvar_x]> subst_map)) stk_id
            (λ x0 : lvar, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0)) ≡ u) as Hpost.
            { subst u; reflexivity. }


            iSplitR "Hq".
            { rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done. rewrite trnsl_lval_trnsl_val_inverse. iFrame. }

            { have HfvA : assertion_lexpr_fvars proc_post ⊆ dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr)).
              { have Hfv := proj2 (Hwf.(pwf_proc_fvars_bounded) proc_name _ H0).
                have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ Hlexprs_arg_vals. have := Forall2_length _ _ _ Harg_vals. have := @length_fmap _ _ fst proc_args. simpl in *. lia. }
                rewrite dom_insert_L. rewrite dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). exact Hfv. }
              have HdomEq : dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr)) = dom (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr)).
              { have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ Hlexprs_arg_vals. have := Forall2_length _ _ _ Harg_vals. have := @length_fmap _ _ fst proc_args. simpl in *. lia. }
                have Hlen2 : length proc_args.*1 ≤ length (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals). { rewrite map_length. have := Forall2_length _ _ _ Harg_vals. have := @length_fmap _ _ fst proc_args. simpl in *. lia. }
                rewrite !dom_insert_L. rewrite !dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). rewrite (fst_zip _ _ Hlen2). reflexivity. }
              pose proof (trnsl_assertion_w_lexpr_subst_r proc_post lexprs proc_args.*1 arg_vals lvar_x ret_val stk stk_id mp u (proc_frame_post ret_val)
                Hwf (proj2 Hspec_StackFree)
                (proj2 (Hwf.(pwf_proc_binders_fresh) proc_name _ _ H0))
                (proj2 (Hwf.(pwf_proc_binders_fresh) proc_name _ _ H0))
                HfvA HdomEq (fresh_lvar_not_in_lexpr_map_fvars_zip stk args lexprs proc_args.*1 lvar_x H2 H)
                H Hlexprs_arg_vals Hpost Hproc_frame_post) as Himpl.
              setoid_rewrite <- trnsl_assertion_unfold. iApply Himpl. iFrame. }
          }
        }

        { (* proc body is not well-formed *)

          inversion H4; subst s. 
          setoid_rewrite trnsl_assertion_unfold.
          iIntros (Φ) "!> [[Hstk [Hfalse Hu]] Hcr]". rewrite Hproc_body. done. 
        }

        {
          (* proc_body != Skip *)
        inversion H4; subst s.
        iIntros (Φ). iModIntro.
        setoid_rewrite trnsl_assertion_unfold.

        iIntros "[[Hstk [Hproc_tbl Hu1]] Hcr] HΦ".

        set (subst_map' := @list_to_map var LExpr (gmap var LExpr) _ _ (zip (proc_args).*1 (map (λ val, LVal (trnsl_val val)) arg_vals))).

          set (trnsl_assertion (subst proc_pre subst_map') stk_id mp) as proc_frame_pre.
          assert ((trnsl_assertion (subst proc_pre subst_map') stk_id mp) ≡ proc_frame_pre) as Hproc_frame_pre. { subst proc_frame_pre; reflexivity. }

          set (fun ret_val => trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id mp) as proc_frame_post.

        iApply (wp_call _ _ _ _ _ _ (lang.Proc proc_name proc_args proc_locals _) _ u1 proc_frame_post with "[] [Hstk Hproc_tbl Hu1]"); try iFrame; try done.

          {
            (* Showing procedure contract holds, via the ambient (Löb-guarded) Calls fact *)
            iNext.
            iIntros (stk_id' stk_frm') "%HlocalsDef". destruct HlocalsDef as [HlocalsDef [Hrv_val Hdom_val]]. simpl in *.

            iPoseProof ("Calls" $! proc_name (Proc proc_args proc_locals proc_pre proc_post proc_body) arg_vals with "[%]") as "Calls'".
            { done. }
            iPoseProof ("Calls'" with "[%]") as "Hproc".
            { exact H0. }

            iSpecialize ("Hproc" $! proc_frame_pre proc_frame_post stk_id' stk_frm' mp s0 mask).

            iSpecialize ("Hproc" with "[%]"). { exact Henv. }

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

          have Hproc_frame_pre' : trnsl_assertion (subst proc_pre subst_map') stk_id' mp ≡ proc_frame_pre.
          { etransitivity.
            - symmetry. apply (stack_free_assertion_trnsl _ stk_id stk_id' mp).
              apply (stack_free_assertion_subst Hwf). destruct Hspec_StackFree; done.
            - exact Hproc_frame_pre. }

          iSpecialize ("Hproc" with "[%]"). { exact Harg_vals_typed. }

          iSpecialize ("Hproc" with "[%]"). { exact Hproc_frame_pre'. }

          have Hproc_frame_post_all : ∀ ret_val,
              trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id' mp ≡ proc_frame_post ret_val.
          { intros ret_val. etransitivity.
            - symmetry. apply (stack_free_assertion_trnsl _ stk_id stk_id' mp).
              apply (stack_free_assertion_subst Hwf). destruct Hspec_StackFree; done.
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
            have HfvA : assertion_lexpr_fvars proc_pre ⊆ dom (list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr).
            { have Hfv := proj1 (Hwf.(pwf_proc_fvars_bounded) proc_name _ H0).
              have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ HlocalsDef. have := Forall2_length _ _ _ Hlexprs_arg_vals. lia. }
              rewrite dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). exact Hfv. }
            have HdomEq : dom (list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr) = dom (list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr).
            { have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ HlocalsDef. have := Forall2_length _ _ _ Hlexprs_arg_vals. lia. }
              have Hlen2 : length proc_args.*1 ≤ length (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals). { rewrite map_length. have := Forall2_length _ _ _ HlocalsDef. lia. }
              rewrite !dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). rewrite (fst_zip _ _ Hlen2). reflexivity. }
            pose proof (trnsl_assertion_w_lexpr_subst proc_pre lexprs proc_args.*1 arg_vals stk_id mp u1 proc_frame_pre
              Hwf (proj1 Hspec_StackFree)
              (proj1 (Hwf.(pwf_proc_binders_fresh) proc_name _ _ H0))
              (proj1 (Hwf.(pwf_proc_binders_fresh) proc_name _ _ H0))
              HfvA HdomEq
              Hlexprs_arg_vals Hproc_pre Hproc_frame_pre) as Himpl.
            iApply Himpl. iFrame.
          }


          iNext. iExact "HΦ".

          }

          { rewrite Hproc_body. iFrame. setoid_rewrite <- trnsl_assertion_unfold. iFrame. }

          {
            iNext. iIntros "[%ret_val [Hstk [Hq Hcr']]]".

            have Hproc_frame_post : trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id mp ≡ proc_frame_post ret_val.
            { reflexivity. }

            iApply "HΦ". iCombine "Hcr" "Hcr'" as "Hcr". rewrite Nat.add_1_r. iFrame. iExists (trnsl_val ret_val).

            set (trnsl_assertion (subst proc_post (<["#ret_val":=LVar lvar_x]> subst_map)) stk_id
            (λ x0 : lvar, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0)) as u.
            assert ((trnsl_assertion (subst proc_post (<["#ret_val":=LVar lvar_x]> subst_map)) stk_id
            (λ x0 : lvar, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0)) ≡ u) as Hpost. { subst u; reflexivity. }

            iSplitR "Hq".
            { rewrite fresh_mp_rewrite_symb_stk_to_stk_frm_compat; try done. rewrite trnsl_lval_trnsl_val_inverse. iFrame. }

            { have HfvA : assertion_lexpr_fvars proc_post ⊆ dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr)).
              { have Hfv := proj2 (Hwf.(pwf_proc_fvars_bounded) proc_name _ H0).
                have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ Hlexprs_arg_vals. have := Forall2_length _ _ _ Harg_vals. have := @length_fmap _ _ fst proc_args. simpl in *. lia. }
                rewrite dom_insert_L. rewrite dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). exact Hfv. }
              have HdomEq : dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip proc_args.*1 lexprs) : gmap lvar LExpr)) = dom (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip proc_args.*1 (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr)).
              { have Hlen : length proc_args.*1 ≤ length lexprs. { have := Forall2_length _ _ _ Hlexprs_arg_vals. have := Forall2_length _ _ _ Harg_vals. have := @length_fmap _ _ fst proc_args. simpl in *. lia. }
                have Hlen2 : length proc_args.*1 ≤ length (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals). { rewrite map_length. have := Forall2_length _ _ _ Harg_vals. have := @length_fmap _ _ fst proc_args. simpl in *. lia. }
                rewrite !dom_insert_L. rewrite !dom_list_to_map_L. rewrite (fst_zip _ _ Hlen). rewrite (fst_zip _ _ Hlen2). reflexivity. }
              pose proof (trnsl_assertion_w_lexpr_subst_r proc_post lexprs proc_args.*1 arg_vals lvar_x ret_val stk stk_id mp u (proc_frame_post ret_val)
                Hwf (proj2 Hspec_StackFree)
                (proj2 (Hwf.(pwf_proc_binders_fresh) proc_name _ _ H0))
                (proj2 (Hwf.(pwf_proc_binders_fresh) proc_name _ _ H0))
                HfvA HdomEq (fresh_lvar_not_in_lexpr_map_fvars_zip stk args lexprs proc_args.*1 lvar_x H2 H)
                H Hlexprs_arg_vals Hpost Hproc_frame_post) as Himpl.
              setoid_rewrite <- trnsl_assertion_unfold. iApply Himpl. iFrame. }
          }

        }

      }

      1 : {
        (* FPU *)
        unfold trnsl_hoare_triple; simpl.
        setoid_rewrite trnsl_assertion_unfold.
        specialize (RAPack_fpuValid Γ RAPack old_val new_val) as HRA_fpu.
        
        iIntros "[[Hstack Hown] Hcr]".
        destruct (Γ RAPack) as [i [U [Hdisc [Heq_car [Hindx [Hcomp Hval]]]]]] eqn:H_RA_Pack.
        iDestruct "Hown" as (l) "[%Heq Hown]".

        iFrame.

        apply (HRA_fpu) in H0.

        iMod (own_update _ 
          (transport (f_equal cmra_car Hindx) ((transport Heq_car old_val))) 
          (transport (f_equal cmra_car Hindx) ((transport Heq_car new_val)))
       with "Hown") as "Hown".

       { apply transport_cmra_update. exact H0.  }

       iModIntro. rewrite H_RA_Pack. iExists l. iFrame. iPureIntro. exact Heq.

      }

    Qed.

    (* The central bootstrap theorem: if every procedure's own body is
       provably correct against its own contract (via RavenHoareTriple, run
       from a symbolic entry stack synthesized from its formal args and
       locals), then all_proc_specs_valid_iris holds unconditionally -- with no
       ▷ all_proc_specs_valid_iris hypothesis of its own. The recursive/mutually-
       recursive call sites inside procedure bodies are discharged via Löb
       induction, mirroring rrl_validity's own use of "Calls". *)
    Theorem raven_soundness ρ σ
      (Hwf : ProgramWF)
      (* σ has enough distinct lvars of any given type, avoiding any finite
         exclusion set -- lets every procedure synthesize its own entry stack
         out of genuinely fresh lvars, rather than reusing formal-argument or
         local-variable names as lvar names (which would force every
         procedure sharing such a name to agree on its type under a single
         global σ). *)
      (Hσ_rich : ∀ (t : typ) (excl : gset lvar), ∃ lv, lv ∉ excl ∧ σ lv = t)
      (* Every procedure call starts a fresh sub-execution: wp_call discards
         whatever later-credits the caller has accumulated (never threads
         them into the callee), so a procedure body's own derivation must be
         able to start at credit-index 0 -- exactly like the top-level
         "main" program itself must.
         "#ret_val" is itself a stack variable, so by the time the body
         returns it may have been reassigned (fresh lvar per
         VarAssignmentRule) away from its initial binding; lv_final is
         whatever lvar it now points to, and the postcondition's own
         "#ret_val" occurrences must be read through that renaming --
         mirroring exactly how ProcCallRuleRet's own conclusion substitutes
         "#ret_val" with the call's fresh result lvar. *)
      (Hbodies : all_proc_specs_valid_raven ρ σ) :
      ⊢ all_proc_specs_valid_iris σ.
    Proof.
      iLöb as "IH".
      rewrite /all_proc_specs_valid_iris.
      iModIntro.
      iIntros (proc proc_record stk_vals) "%Hproc_in_set %Hproc_map".
      iIntros (precond postcond stk_id stk_frm mp stmt msk)
        "%Henv %Hargs_present %Harg_vals %Hlocals_typed %Hdom_val %Harg_vals_typed %Hprecond_eq %Hpostcond_eq %Hstmt_shape".

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
      destruct (Hbody_msk msk dll) as (ι2 & stk0' & lv_final & Hrv_final & HRHT).

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

      have Hprecond_bridge :
        trnsl_assertion (subst (proc_precond_of proc_record) (list_to_map (zip args (map LVar args_lvs)))) stk_id mp0
        ≡ precond.
      { set (M1 := list_to_map (zip args (map LVar args_lvs)) : gmap var LExpr).
        set (M2 := list_to_map (zip args (map (λ val, LVal (trnsl_val val)) stk_vals)) : gmap var LExpr).
        have Hfv := proj1 (Hwf.(pwf_proc_fvars_bounded) proc proc_record Hproc_map).
        have HfvA : assertion_lexpr_fvars (proc_precond_of proc_record) ⊆ dom M1.
        { unfold M1. rewrite dom_list_to_map_L (fst_zip _ _ Hargs_len_lvs'). exact Hfv. }
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
        have Heq := trnsl_assertion_subst_congr Hwf (proc_precond_of proc_record) M1 M2 stk_id mp0 mp
          Hpre_free (proj1 (Hwf.(pwf_proc_binders_fresh) proc proc_record M1 Hproc_map))
          (proj1 (Hwf.(pwf_proc_binders_fresh) proc proc_record M2 Hproc_map))
          HfvA HdomEq Hstab Hbase.
        rewrite Heq. exact Hprecond_eq. }

      set (ret_val := trnsl_lval (mp0 lv_final)).

      have Hpostcond_bridge :
        trnsl_assertion
          (subst (proc_postcond_of proc_record)
             (<["#ret_val" := LVar lv_final]> (list_to_map (zip args (map LVar args_lvs)))))
          stk_id mp0
        ≡ postcond ret_val.
      { set (M1 := <["#ret_val" := LVar lv_final]> (list_to_map (zip args (map LVar args_lvs))) : gmap var LExpr).
        set (M2 := <["#ret_val" := LVal (trnsl_val ret_val)]>
                     (list_to_map (zip args (map (λ val, LVal (trnsl_val val)) stk_vals))) : gmap var LExpr).
        have Hfv := proj2 (Hwf.(pwf_proc_fvars_bounded) proc proc_record Hproc_map).
        have HdomEq0 : dom (list_to_map (zip args (map LVar args_lvs)) : gmap var LExpr)
                     = dom (list_to_map (zip args (map (λ val, LVal (trnsl_val val)) stk_vals)) : gmap var LExpr).
        { rewrite !dom_list_to_map_L (fst_zip _ _ Hargs_len_lvs') (fst_zip _ _ Hargs_len2'). reflexivity. }
        have HfvA : assertion_lexpr_fvars (proc_postcond_of proc_record) ⊆ dom M1.
        { unfold M1. rewrite dom_insert_L dom_list_to_map_L (fst_zip _ _ Hargs_len_lvs'). exact Hfv. }
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
        have Heq := trnsl_assertion_subst_congr Hwf (proc_postcond_of proc_record) M1 M2 stk_id mp0 mp
          Hpost_free (proj2 (Hwf.(pwf_proc_binders_fresh) proc proc_record M1 Hproc_map))
          (proj2 (Hwf.(pwf_proc_binders_fresh) proc proc_record M2 Hproc_map))
          HfvA HdomEq Hstab Hbase.
        rewrite Heq. exact (Hpostcond_eq ret_val). }

      iPoseProof (rrl_validity ρ σ 0 ι2 stk_id
        (LAnd (LStack (list_to_map (zip names lvs)))
           (subst (proc_precond_of proc_record) (list_to_map (zip args (map LVar args_lvs)))))
        msk (proc_body_of proc_record)
        (LAnd (LStack stk0')
           (subst (proc_postcond_of proc_record)
              (<["#ret_val" := LVar lv_final]> (list_to_map (zip args (map LVar args_lvs))))))
        Hwf Hwelldef mp0 Henv0 with "[$IH]") as "Htriple".
      { iPureIntro. exact HRHT. }

      destruct Hstmt_shape as [Hstmt_shape | [Hstmt_shape ->]];
        iEval (rewrite /trnsl_hoare_triple Hstmt_shape) in "Htriple".

      - (* proc_body_of proc_record translates to a real statement *)
        iEval (setoid_rewrite trnsl_assertion_unfold; simpl) in "Htriple".
        have Hprecond_bridge' := Hprecond_bridge.
        unfold trnsl_assertion in Hprecond_bridge'.
        rewrite trnsl_assertion_unfold in Hprecond_bridge'.
        have Hpostcond_bridge' := Hpostcond_bridge.
        unfold trnsl_assertion in Hpostcond_bridge'.
        rewrite trnsl_assertion_unfold in Hpostcond_bridge'.
        iIntros (Φ). iModIntro.
        iMod lc_zero as "Hlc0".
        iIntros "[Hstk Hpre] HΦ'".
        iApply ("Htriple" with "[Hstk Hpre Hlc0]").
        { rewrite Hstk0_eq.
          iSplitL "Hstk Hpre".
          - iSplitL "Hstk"; [iFrame |]. iEval (rewrite Hprecond_bridge'). iFrame.
          - iFrame. }
        iNext. iIntros "[[Hpost_stk Hpost_pred] Hcr2]".
        iApply "HΦ'".
        iExists ret_val, (symb_stk_to_stk_frm stk0' mp0).
        iFrame "Hpost_stk".
        iSplitR.
        + iPureIntro. simpl. rewrite lookup_fmap Hrv_final. reflexivity.
        + iEval (rewrite Hpostcond_bridge') in "Hpost_pred". iFrame.

      - (* trnsl_stmt (proc_body_of proc_record) = None': body is ghost-only, runs as Skip *)
        have Hprecond_bridge' := Hprecond_bridge.
        unfold trnsl_assertion in Hprecond_bridge'.
        rewrite trnsl_assertion_unfold in Hprecond_bridge'.
        have Hpostcond_bridge' := Hpostcond_bridge.
        unfold trnsl_assertion in Hpostcond_bridge'.
        rewrite trnsl_assertion_unfold in Hpostcond_bridge'.
        iEval (setoid_rewrite trnsl_assertion_unfold; simpl) in "Htriple".
        iIntros (Φ). iModIntro.
        iMod lc_zero as "Hlc0".
        iIntros "[Hstk Hpre] HΦ'".
        iMod ("Htriple" with "[Hstk Hpre Hlc0]") as "[[Hpost_stk Hpost_pred] Hcr2]".
        { rewrite Hstk0_eq.
          iSplitL "Hstk Hpre".
          - iSplitL "Hstk"; [iFrame |]. iEval (rewrite Hprecond_bridge'). iFrame.
          - iFrame. }
        iApply (wp_skip
          (∃ ret_val0 stk_frm'', stack_own[stk_id, stk_frm''] ∗
             ⌜locals stk_frm'' !! "#ret_val" = Some ret_val0⌝ ∗ postcond ret_val0)%I
          (inv_set_to_namespace msk) stk_id with "[Hpost_stk Hpost_pred]").
        { iExists ret_val, (symb_stk_to_stk_frm stk0' mp0). iFrame "Hpost_stk".
          iSplitR.
          - iPureIntro. simpl. rewrite lookup_fmap Hrv_final. reflexivity.
          - iEval (rewrite Hpostcond_bridge') in "Hpost_pred". iFrame. }
        iNext. iIntros "[Hpost Hcr1]".
        iApply "HΦ'". iFrame "Hpost".
    Qed.

  End MainTranslation.
