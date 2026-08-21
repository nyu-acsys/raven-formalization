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

    (* [mask ⊆ inv_set] is genuinely needed: an invariant name outside [inv_set]
       carries no disjointness guarantee, so its namespace could overlap invr's
       and the equality would fail. *)
    Lemma inv_map_set_minus_subseteq (Hwf : ProgramWF) mask invr:
      invr ∈ mask ->
      invr ∈ inv_set ->
      mask ⊆ inv_set ->
        (inv_set_to_namespace (mask ∖ {[invr]})) = inv_set_to_namespace mask ∖ ↑inv_namespace_map invr.
    Proof.
      intros Hin Hinvset Hmask_sub.
      unfold inv_set_to_namespace.
      set (f := λ inv (acc : coPset), acc ∪ ↑inv_namespace_map inv).
      (* Every *other* invariant of the mask is in inv_set and differs from invr,
         so pwf_inv_namespace_disjoint applies to it. *)
      have Hrest_disj : set_fold f ∅ (mask ∖ {[invr]}) ## (↑inv_namespace_map invr : coPset).
      {
        have Hrest : ∀ i, i ∈ mask ∖ {[invr]} → i ∈ inv_set ∧ i ≠ invr.
        { intros i Hi. apply elem_of_difference in Hi as [Hi1 Hi2].
          split; [exact (Hmask_sub i Hi1) |].
          intros ->. apply Hi2. apply elem_of_singleton_2. reflexivity. }
        revert Hrest.
        apply (set_fold_ind
                 (λ acc s, (∀ i, i ∈ s → i ∈ inv_set ∧ i ≠ invr) →
                           acc ## (↑inv_namespace_map invr : coPset))).
        - solve_proper.
        - intros _. set_solver.
        - intros x s' acc Hnotin IH Hall.
          destruct (Hall x ltac:(set_solver)) as [Hxset Hxne].
          have Hxdisj := Hwf.(pwf_inv_namespace_disjoint) x invr Hxset Hinvset Hxne.
          have Hacc : acc ## (↑inv_namespace_map invr : coPset).
          { apply IH. intros i Hi. apply Hall. set_solver. }
          subst f. simpl. set_solver.
      }
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
      have Hmask_eq : set_fold f ∅ mask
                    = set_fold f ∅ (mask ∖ {[invr]}) ∪ ↑inv_namespace_map invr.
      {
        transitivity (set_fold f ∅ ({[invr]} ∪ (mask ∖ {[invr]}))).
        - f_equal. exact Hmask_split.
        - apply Hstep.
          intro Hc. apply elem_of_difference in Hc.
          destruct Hc as [_ Hne]. apply Hne. apply elem_of_singleton_2. reflexivity.
      }
      rewrite Hmask_eq. set_solver.
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
          destruct (interp_lexpr le1 mp) as [[b|n| |l|p]|] eqn:Hv1; try discriminate.
          injection Hinterp as <-.
          apply UnOpStep with (v := lang.LitBool b).
          * exact (IHe le1 (LitBool b) eq_refl Hv1).
          * simpl. done.
        + (* NegOp *)
          destruct (interp_lexpr le1 mp) as [[b|i| |l|p]|] eqn:Hv1; try discriminate.
          injection Hinterp as <-.
          apply UnOpStep with (v := lang.LitInt i).
          * exact (IHe le1 (LitInt i) eq_refl Hv1).
          * simpl. done.
        + (* RAValidOp *)
          destruct (interp_lexpr le1 mp) as [[b|n| |l|[r x]]|] eqn:Hv1; try discriminate.
          injection Hinterp as <-.
          apply UnOpStep with (v := lang.LitRAElem (existT r x)).
          * exact (IHe le1 (LitRAElem (existT r x)) eq_refl Hv1).
          * simpl. done.
        + (* RAOfIntOp *)
          destruct (interp_lexpr le1 mp) as [[b|z| |l|p]|] eqn:Hv1; try discriminate.
          simpl in Hinterp.
          injection Hinterp as <-.
          apply UnOpStep with (v := lang.LitInt z).
          * exact (IHe le1 (LitInt z) eq_refl Hv1).
          * simpl. reflexivity.
      - (* BinOp op e1 e2 *)
        destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [|discriminate].
        destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [|discriminate].
        injection Htrnsl as <-.
        destruct op; simpl in Hinterp;
          (* Integer arithmetic ops: AddOp, SubOp, MulOp, DivOp, ModOp *)
          try (destruct (interp_lexpr le1 mp) as [[b1|i1| |l1|p1]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|i2| |l2|p2]|] eqn:Hv2; try discriminate;
               injection Hinterp as <-;
               apply BinOpStep with (v1 := lang.LitInt i1) (v2 := lang.LitInt i2);
               [ exact (IHe1 le1 (LitInt i1) eq_refl Hv1)
               | exact (IHe2 le2 (LitInt i2) eq_refl Hv2)
               | simpl; done ]);
          (* Comparison ops: LtOp, GtOp, LeOp, GeOp — result is LitBool *)
          try (destruct (interp_lexpr le1 mp) as [[b1|i1| |l1|p1]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|i2| |l2|p2]|] eqn:Hv2; try discriminate;
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
          try (destruct (interp_lexpr le1 mp) as [[b1|n1| |l1|p1]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|n2| |l2|p2]|] eqn:Hv2; try discriminate;
               injection Hinterp as <-;
               apply BinOpStep with (v1 := lang.LitBool b1) (v2 := lang.LitBool b2);
               [ exact (IHe1 le1 (LitBool b1) eq_refl Hv1)
               | exact (IHe2 le2 (LitBool b2) eq_refl Hv2)
               | simpl; done ]);
          (* RACompOp *)
          try (destruct (interp_lexpr le1 mp) as [[b1|i1| |l1|[r1 x1]]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|i2| |l2|[r2 x2]]|] eqn:Hv2; try discriminate;
               destruct (decide (r1 = r2)) as [<-|Hne]; [ | discriminate Hinterp ];
               injection Hinterp as <-;
               apply BinOpStep with (v1 := lang.LitRAElem (existT r1 x1)) (v2 := lang.LitRAElem (existT r1 x2));
               [ exact (IHe1 le1 (LitRAElem (existT r1 x1)) eq_refl Hv1)
               | exact (IHe2 le2 (LitRAElem (existT r1 x2)) eq_refl Hv2)
               | apply bin_op_eval_ra_comp ]);
          (* RAFrameOp *)
          try (destruct (interp_lexpr le1 mp) as [[b1|i1| |l1|[r1 x1]]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|i2| |l2|[r2 x2]]|] eqn:Hv2; try discriminate;
               destruct (decide (r1 = r2)) as [<-|Hne]; [ | discriminate Hinterp ];
               injection Hinterp as <-;
               apply BinOpStep with (v1 := lang.LitRAElem (existT r1 x1)) (v2 := lang.LitRAElem (existT r1 x2));
               [ exact (IHe1 le1 (LitRAElem (existT r1 x1)) eq_refl Hv1)
               | exact (IHe2 le2 (LitRAElem (existT r1 x2)) eq_refl Hv2)
               | apply bin_op_eval_ra_frame ]);
          (* RAFpuValidOp *)
          try (destruct (interp_lexpr le1 mp) as [[b1|i1| |l1|[r1 x1]]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|i2| |l2|[r2 x2]]|] eqn:Hv2; try discriminate;
               destruct (decide (r1 = r2)) as [<-|Hne]; [ | discriminate Hinterp ];
               injection Hinterp as <-;
               apply BinOpStep with (v1 := lang.LitRAElem (existT r1 x1)) (v2 := lang.LitRAElem (existT r1 x2));
               [ exact (IHe1 le1 (LitRAElem (existT r1 x1)) eq_refl Hv1)
               | exact (IHe2 le2 (LitRAElem (existT r1 x2)) eq_refl Hv2)
               | apply bin_op_eval_ra_fpuvalid ]).
      - (* IfE e1 e2 e3 *)
        destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [|discriminate].
        destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [|discriminate].
        destruct (trnsl_expr_lExpr stk e3) as [le3|] eqn:Hle3; [|discriminate].
        injection Htrnsl as <-.
        simpl in Hinterp.
        destruct (interp_lexpr le1 mp) as [[b|n| |l|p]|] eqn:Hcond; try discriminate.
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
        + (* RAValidOp *)
          simpl in H4. destruct v as [ | | | |[r x]]; try discriminate.
          injection H4 as H4.
          pose proof (IHe le1 (LitRAElem (existT r x)) eq_refl H3) as Hle.
          rewrite Hle. simpl. f_equal. exact (trnsl_lval_injective (LitBool (bool_decide (valid x))) lv H4).
        + (* RAOfIntOp *)
          simpl in H4. destruct v as [ | z | | | ]; try discriminate.
          injection H4 as H4.
          pose proof (IHe le1 (LitInt z) eq_refl H3) as Hle.
          rewrite Hle. simpl. f_equal.
          exact (trnsl_lval_injective (LitRAElem (existT r (ra_of_int z))) lv H4).
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
               destruct (bool_decide (v1 = v2)); done);
          (* RACompOp *)
          try (destruct v1 as [ | | | |[r1 x1]]; try discriminate;
               destruct v2 as [ | | | |[r2 x2]]; try discriminate;
               destruct (decide (r1 = r2)) as [<-|Hne]; [ | discriminate H6 ];
               injection H6 as H6;
               symmetry in H6; apply (f_equal trnsl_val) in H6;
               rewrite trnsl_val_trnsl_lval_inverse in H6; simpl in H6; subst lv;
               simpl in Hle1', Hle2';
               exact (interp_lexpr_ra_comp r1 x1 x2 le1 le2 mp Hle1' Hle2'));
          (* RAFrameOp *)
          try (destruct v1 as [ | | | |[r1 x1]]; try discriminate;
               destruct v2 as [ | | | |[r2 x2]]; try discriminate;
               destruct (decide (r1 = r2)) as [<-|Hne]; [ | discriminate H6 ];
               injection H6 as H6;
               symmetry in H6; apply (f_equal trnsl_val) in H6;
               rewrite trnsl_val_trnsl_lval_inverse in H6; simpl in H6; subst lv;
               simpl in Hle1', Hle2';
               exact (interp_lexpr_ra_frame r1 x1 x2 le1 le2 mp Hle1' Hle2'));
          (* RAFpuValidOp *)
          try (destruct v1 as [ | | | |[r1 x1]]; try discriminate;
               destruct v2 as [ | | | |[r2 x2]]; try discriminate;
               destruct (decide (r1 = r2)) as [<-|Hne]; [ | discriminate H6 ];
               injection H6 as H6;
               symmetry in H6; apply (f_equal trnsl_val) in H6;
               rewrite trnsl_val_trnsl_lval_inverse in H6; simpl in H6; subst lv;
               simpl in Hle1', Hle2';
               exact (interp_lexpr_ra_fpuvalid r1 x1 x2 le1 le2 mp Hle1' Hle2')).
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

    Definition trnsl_hoare_triple (stk_id: stack_id) (p : assertion) (msk : maskAnnot) (cmd : stmt) (q : assertion) (mp : symb_map) : iProp rrl_lang.Σ :=
        match (trnsl_stmt cmd) with
        | Error => True
        | None' =>
          match (trnsl_assertion p stk_id mp),
                (trnsl_assertion q stk_id mp) with
          | p', q' =>
            p' ={inv_set_to_namespace msk}=∗ q'
          end

        | Some' s =>
          match (trnsl_assertion p stk_id mp),
                (trnsl_assertion q stk_id mp) with
          | p', q' =>
            {{{ p' }}}
              to_rtstmt stk_id s @ (inv_set_to_namespace msk)
            {{{ RET lang.LitUnit; q'}}}
          end
        end
    .

    (* The per-invariant shared worlds.  Persistent, and an explicit premise of
       [raven_soundness]: the calculus has no rule that could establish it, so
       it records how the ghost state must have been set up. *)
    Definition all_inv_worlds : iProp rrl_lang.Σ :=
      ([∗ set] inv' ∈ inv_set, inv (inv_namespace_map inv') (Winv inv'))%I.

    Lemma all_inv_worlds_elem (inv' : inv_name) :
      inv' ∈ inv_set →
      all_inv_worlds -∗ inv (inv_namespace_map inv') (Winv inv').
    Proof.
      intros Hin. rewrite /all_inv_worlds.
      iIntros "H". by iApply (big_sepS_elem_of with "H").
    Qed.

    (* The proc-table registration for every procedure, mirroring
       all_inv_worlds's own role: the calculus has no rule that could
       establish proc_tbl_chunk (it's a persistent fact about how the ghost
       state was set up, never allocated by any rule -- see
       ProcCallRuleRet's soundness case, the only consumer), so it's an
       explicit premise of raven_soundness instead. *)
    Definition all_proc_tbl_chunks : iProp rrl_lang.Σ :=
      ([∗ map] proc_name ↦ proc_record ∈ proc_map,
        proc_tbl_chunk proc_name
          (lang.Proc proc_name (proc_args_of proc_record) (proc_locals_of proc_record)
             match trnsl_stmt (proc_body_of proc_record) with
             | Some' s => s
             | _ => lang.SkipS
             end))%I.

    Lemma all_proc_tbl_chunks_elem (proc_name : proc_name) (proc_record : ProcRecord) :
      proc_map !! proc_name = Some proc_record ->
      all_proc_tbl_chunks -∗
      proc_tbl_chunk proc_name
        (lang.Proc proc_name (proc_args_of proc_record) (proc_locals_of proc_record)
           match trnsl_stmt (proc_body_of proc_record) with
           | Some' s => s
           | _ => lang.SkipS
           end).
    Proof.
      intros Hin. rewrite /all_proc_tbl_chunks.
      iIntros "H". by iApply (big_sepM_lookup with "H").
    Qed.

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

    (* Well-typed argument expressions all denote a value under mp, so an
       argument list has a value vector. *)
    Lemma args_interp_values ρ σ stk mp (args : list lang.expr) (lexprs : list LExpr) :
      stk_type_compat ρ σ stk →
      env_typ_well_defined σ mp →
      Forall (fun arg => expr_well_defined ρ arg) args →
      map (fun arg => trnsl_expr_lExpr stk arg) args = map (fun le => Some le) lexprs →
      ∃ vs : list val, Forall2 (λ le v, interp_lexpr le mp = Some v) lexprs vs.
    Proof.
      intros Hstk Henv Hwd. revert lexprs.
      induction args as [| a args IH]; intros lexprs Hmap.
      - destruct lexprs; [| discriminate]. exists []. constructor.
      - destruct lexprs as [| le lexprs]; [discriminate |].
        simpl in Hmap. injection Hmap as Hle Hmap'.
        inversion Hwd as [| a' args' Hwda Hwdargs]; subst.
        destruct (IH Hwdargs lexprs Hmap') as [vs Hvs].
        destruct (interp_lexpr le mp) as [v |] eqn:Hinterp.
        + exists (v :: vs). by constructor.
        + exfalso.
          exact (expr_interp_well_defined ρ σ stk a mp le Hstk Henv Hle Hinterp Hwda).
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

      (* The mask only ever mentions invariants of the program, mirroring the
         requirement rrl_validity itself needs to reason about mask narrowing. *)
      ⌜msk ⊆ inv_set⌝ -∗

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
        ∀ msk, msk ⊆ inv_set →
        ∀ (dll : proc_entry_lvars σ proc_record),
          ∃ stk0' lv_final,
            stk0' !! "#ret_val" = Some lv_final ∧
            RavenHoareTriple ρ σ
              (LAnd (LStack (assoc_map (proc_args_of proc_record ++ proc_locals_of proc_record).*1
                                        (dll_args dll ++ dll_locals dll)))
                 (subst (proc_precond_of proc_record)
                    (lvar_subst_map (proc_args_of proc_record).*1 (dll_args dll))))
              (proc_body_of proc_record) msk
              (LAnd (LStack stk0')
                 (subst (proc_postcond_of proc_record)
                    (<["#ret_val" := LVar lv_final]>
                       (lvar_subst_map (proc_args_of proc_record).*1 (dll_args dll))))).

    (* Combines two separately-held translated assertions into one LAnd fact
       -- used by ExistsElimRule's soundness case to reassemble the pieces of
       a precondition after they've been destructured. *)
    Lemma trnsl_assertion_and_intro P1 P2 stk_id mp :
      trnsl_assertion P1 stk_id mp -∗ trnsl_assertion P2 stk_id mp -∗
      trnsl_assertion (LAnd P1 P2) stk_id mp.
    Proof. rewrite trnsl_assertion_and. iIntros "$ $". Qed.

    (* eval_lvar at any x ∈ dom M is stable under an mp-update at a var not
       mentioned by any of M's values -- the two facts InvAccessBlockRule's
       soundness case needs to bridge subst inv_body subst_map's truth
       across the mp-update the block's own postcondition existential
       (LExists lv) introduces for the wrapped stmt's fresh result lvar. *)
    Lemma eval_lvar_base_stable (M : gmap lvar LExpr) (q : symb_map) (lv : lvar) (v' : val) (x : lvar) :
      lv ∉ lexpr_map_fvars M -> x ∈ dom M ->
      eval_lvar M (fun y => if (y =? lv)%string then v' else q y) x = eval_lvar M q x.
    Proof.
      intros Hlv Hx. destruct (proj1 (elem_of_dom (D := gset lvar) M x) Hx) as [e HMx].
      unfold eval_lvar. rewrite HMx.
      apply interp_lexpr_stable. exact (proj1 (lexpr_map_fvars_spec M lv) Hlv x e HMx).
    Qed.

    Lemma eval_lvar_stab_generic (M : gmap lvar LExpr) (q1 q2 : symb_map) :
      (forall x, x ∈ dom M -> eval_lvar M q1 x = eval_lvar M q2 x) ->
      forall (v : lvar), v ∉ lexpr_map_fvars M ->
      forall (v' : val) (x : lvar), x ∈ dom M ->
      eval_lvar M (fun y => if (y =? v)%string then v' else q1 y) x =
      eval_lvar M (fun y => if (y =? v)%string then v' else q2 y) x.
    Proof.
      intros Hbase v Hv v' x Hx.
      rewrite (eval_lvar_base_stable M q1 v v' x Hv Hx) (eval_lvar_base_stable M q2 v v' x Hv Hx).
      exact (Hbase x Hx).
    Qed.

    (* Every lexpr InvAccessBlockRule's own call-site args translate to is
       fvar-disjoint from a stk-fresh lvar -- lifts
       trnsl_expr_lExpr_fresh_lvar (single expr) across the whole args/
       lexprs list via the rule's own Hargs map-equality premise. *)
    Lemma lexpr_list_fresh_lvar (stk : stack) (args : list lang.expr) (lexprs : list LExpr) (lv : lvar) :
      map (trnsl_expr_lExpr stk) args = map Some lexprs ->
      fresh_lvar stk lv ->
      Forall (fun le => lv ∉ lexpr_fvars le) lexprs.
    Proof.
      revert lexprs. induction args as [| a args' IH]; intros lexprs Heq Hfresh;
        destruct lexprs as [| le lexprs']; try discriminate Heq; [constructor |].
      simpl in Heq. injection Heq as Heq1 Heq2.
      constructor.
      - exact (trnsl_expr_lExpr_fresh_lvar stk a le lv Heq1 Hfresh).
      - exact (IH lexprs' Heq2 Hfresh).
    Qed.

    (* lexpr_map_fvars of a zip-built substitution map is bounded by the
       fvars of its values. *)
    Lemma lexpr_map_fvars_zip_bound (ks : list var) (vs : list LExpr) (v : lvar) :
      Forall (fun e => v ∉ lexpr_fvars e) vs ->
      v ∉ lexpr_map_fvars (list_to_map (zip ks vs) : gmap var LExpr).
    Proof.
      intros Hfa. apply (lexpr_map_fvars_spec _ v). intros k e Hke.
      apply elem_of_list_to_map_2, elem_of_zip_r in Hke.
      rewrite List.Forall_forall in Hfa. apply Hfa.
      apply elem_of_list_In. exact Hke.
    Qed.

    (* Forall2's own interp_lexpr equations are stable under an mp-update at
       a var none of the lexprs mention. *)
    Lemma forall2_interp_stable (lexprs : list LExpr) (vs : list val) (mp : symb_map) (lv : lvar) (v' : val) :
      Forall (fun le => lv ∉ lexpr_fvars le) lexprs ->
      Forall2 (fun le v => interp_lexpr le mp = Some v) lexprs vs ->
      Forall2 (fun le v => interp_lexpr le (fun y => if (y =? lv)%string then v' else mp y) = Some v) lexprs vs.
    Proof.
      intros Hfa Hf2. induction Hf2 as [| le v0 lexprs' vs' Hhd Htl IH]; inversion Hfa as [| ? ? Hh Ht]; subst.
      - constructor.
      - constructor; [rewrite (interp_lexpr_stable le mp lv v' Hh); exact Hhd | exact (IH Ht)].
    Qed.

    (* subst inv_body subst_map's own translated truth doesn't change under
       an mp-update at a var lv not mentioned by subst_map's own values (see
       InvAccessBlockRule's lv-freshness premise). *)
    Lemma trnsl_assertion_subst_lv_stable (Hwf : ProgramWF) (a : assertion) (M : gmap lvar LExpr)
        (lv : lvar) (v' : val) stk_id mp :
      StackFree a ->
      assertion_exists_binders a ## lexpr_map_fvars M ->
      assertion_lexpr_fvars a ⊆ dom M ->
      lv ∉ lexpr_map_fvars M ->
      trnsl_assertion (subst a M) stk_id (fun y => if (y =? lv)%string then v' else mp y)
      ≡ trnsl_assertion (subst a M) stk_id mp.
    Proof.
      intros Hsf Hbind Hfv Hlv.
      apply (trnsl_assertion_subst_congr Hwf a M M stk_id
               (fun y => if (y =? lv)%string then v' else mp y) mp); try done.
      - intros q1 q2 Hag v0 Hv1 Hv2 v'' x Hx. exact (eval_lvar_stab_generic M q1 q2 Hag v0 Hv1 v'' x Hx).
      - intros x Hx. exact (eval_lvar_base_stable M mp lv v' x Hlv Hx).
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

    (* ProcCallRuleRet's own fresh lvar (holding the call's return value) is
       now typed by the caller's own ρ x (x being the call's LHS pvar) --
       Raven's own type-checker already guarantees a call's LHS and the
       callee's return value agree in type, but that discipline isn't
       tracked anywhere in this untyped-assertion calculus (no field/return
       -type environment threads through LOwn/proc contracts the way
       inf_lexpr does for HeapReadRule's chunk). Assumed here, in the same
       spirit as Γ/proc_map/inv_map being Global Parameters representing
       externally-guaranteed setup, rather than built out -- ProcCallRuleRet
       isn't exercised by the counter_monotonic.v example this file's
       soundness proof is checked against. *)
    Axiom call_ret_val_well_typed : forall (ρ : pvar_typs) (x : var) (ret_val : lang.val),
      typ_val_match (ρ x) (trnsl_val ret_val).

    Theorem rrl_validity ρ σ stk_id p msk cmd q
      (Hwf : ProgramWF) (Hpbt : proc_bodies_translate) :
      stmt_well_defined ρ cmd ->
      msk ⊆ inv_set ->
       □ all_inv_worlds ∗ □ all_proc_tbl_chunks ∗ ▷ (all_proc_specs_valid_iris σ) ∗ ⌜RavenHoareTriple ρ σ p cmd msk q⌝
      ⊢  (∀ mp, ⌜env_typ_well_defined σ mp⌝ -∗ trnsl_hoare_triple stk_id p msk cmd q mp).
    Proof.
      iIntros (Hwelldef Hmask_sub) "[#Hworlds [#HprocTbl [#Calls %H]]]".
      iInduction H as
      [ ρ σ stk mask v lv e lexpr t Htrnsl Hinf Hfresh Hstkcompat |
      ρ σ stk mask x e rdchunk fld lexpr_e lvar_x t Htrnsl Htyp Hfresh Hnotin Hstkcompat
      | ρ σ stk mask v fld e old_chunk lv lexpr Hatm HLexpr1 Hwd
      | | | |
      | ρ σ stk stk' mask invr args stmt inv_record p q lv0 t0 lexprs Hargs Hinv_mask Hinv_record Hinv_len Hstk_tp subst Hlvfresh Hbody IHHbody
      | ρ σ stk mask invr args inv_record p lexprs Hargs Hinv_mask Hinv_record Hinv_len Hstk_tp subst
      | | | | | |
      | ρ σ stk mask v e1 fld e2 e3 lvar_v lexpr1 lexpr2 lexpr3 old_chunk Hfresh Hinf Hwd2 Hwd3 Hnotin Htrnsl1 Htrnsl2 Htrnsl3 Hstkcompat
      | ρ σ mask v t body c q Hsigma Hqfresh ] "IH";
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

        inversion Hwelldef as [ | | | | | | | | | | | | | rho' inv' args' stmt' HInvSet HargsWellDef HBodywelldef | | ];
          subst stmt' args'.
        have Hsub : ↑(inv_namespace_map invr) ⊆ inv_set_to_namespace mask.
        { apply inv_map_subseteq; done. }
        have HInvs : inv_set_to_namespace (mask ∖ {[invr]})
                   = inv_set_to_namespace mask ∖ ↑inv_namespace_map invr.
        { apply (inv_map_set_minus_subseteq Hwf); done. }
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
          have Hfv_sm : assertion_lexpr_fvars (inv_body inv_record) ⊆ dom subst.
          { rewrite Hdom_sm. exact (Hwf.(pwf_inv_fvars_scoped) invr inv_record Hinv_record). }
          have Hlv_lexprs : Forall (fun le => lv0 ∉ lexpr_fvars le) lexprs.
          { exact (lexpr_list_fresh_lvar stk args lexprs lv0 Hargs Hlvfresh). }
          have Hlv_sm : lv0 ∉ lexpr_map_fvars subst.
          { exact (lexpr_map_fvars_zip_bound inv_record.(inv_args) lexprs lv0 Hlv_lexprs). }
          iEval (rewrite (trnsl_assertion_subst_lv_stable Hwf (inv_body inv_record) subst lv0 v' stk_id mp
            (Hwf.(pwf_inv_body_stack_free) invr inv_record Hinv_record)
            (Hwf.(pwf_inv_binders_fresh) invr inv_record subst Hinv_record)
            Hfv_sm Hlv_sm)) in "Hbody'".
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
          have Hfv_sm : assertion_lexpr_fvars (inv_body inv_record) ⊆ dom subst.
          { rewrite Hdom_sm. exact (Hwf.(pwf_inv_fvars_scoped) invr inv_record Hinv_record). }
          have Hlv_lexprs : Forall (fun le => lv0 ∉ lexpr_fvars le) lexprs.
          { exact (lexpr_list_fresh_lvar stk args lexprs lv0 Hargs Hlvfresh). }
          have Hlv_sm : lv0 ∉ lexpr_map_fvars subst.
          { exact (lexpr_map_fvars_zip_bound inv_record.(inv_args) lexprs lv0 Hlv_lexprs). }
          iEval (rewrite (trnsl_assertion_subst_lv_stable Hwf (inv_body inv_record) subst lv0 v' stk_id mp
            (Hwf.(pwf_inv_body_stack_free) invr inv_record Hinv_record)
            (Hwf.(pwf_inv_binders_fresh) invr inv_record subst Hinv_record)
            Hfv_sm Hlv_sm)) in "Hbody'".
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
        inversion Hwelldef as [ | | | | | | | | | | | | | | rho' inv' args' HInvSet HargsWellDef | ];
          subst args'.
        have Hsub : ↑(inv_namespace_map invr) ⊆ inv_set_to_namespace mask.
        { apply inv_map_subseteq; done. }
        iDestruct (all_inv_worlds_elem invr HInvSet with "Hworlds") as "Hiw".
        destruct (args_interp_values ρ σ stk mp args lexprs Hstk_tp Henv HargsWellDef Hargs)
          as [vs HF2].
        have Hlenvs : length vs = length inv_record.(inv_args).
        { rewrite <- Hinv_len. symmetry. exact (Forall2_length _ _ _ HF2). }
        rewrite !trnsl_assertion_and.
        rewrite (trnsl_assertion_LInv_some invr inv_record lexprs stk_id mp Hinv_record).
        iIntros "[Hstk [Hbody Hu]]".
        have Hbridge := inv_body_bridge Hwf invr inv_record lexprs vs stk_id mp
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
        iApply (wp_alloc with "[Hstack]") .
        - done.
        - setoid_rewrite trnsl_assertion_unfold. iFrame.
        - iNext.
          iIntros "Hpost".
          iDestruct "Hpost" as (l) "[Hstk [Hhp _]]".
          iApply "HΦ". iFrame.
          setoid_rewrite trnsl_assertion_unfold.
          iExists (LitLoc l).
          iSplitR; [done|].
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
        (* UNFOLD PRED: no later left to strip -- LPred now denotes its body
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
        (* CAS: consolidated CASSuccRule/CASFailRule (see git history). The
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
          + iApply (wp_if_t e (RTSkipS stk_id) (to_rtstmt stk_id s) stk_id (symb_stk_to_stk_frm stk1 mp) (trnsl_assertion p stk_id mp) (trnsl_assertion Q stk_id mp) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu] [HΦ]"); try iFrame.
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

          + iApply (wp_if_f e (RTSkipS stk_id) (to_rtstmt stk_id s) stk_id (symb_stk_to_stk_frm stk1 mp) (trnsl_assertion p stk_id mp) (trnsl_assertion Q stk_id mp) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu] [HΦ]"); try iFrame.
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
          + iApply (wp_if_t e (to_rtstmt stk_id s) (RTSkipS stk_id) stk_id (symb_stk_to_stk_frm stk1 mp) (trnsl_assertion p stk_id mp) (trnsl_assertion Q stk_id mp) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu] [HΦ]"); try iFrame.
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

          + iApply (wp_if_f e (to_rtstmt stk_id s) (RTSkipS stk_id) stk_id (symb_stk_to_stk_frm stk1 mp) (trnsl_assertion p stk_id mp) (trnsl_assertion Q stk_id mp) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu] [HΦ]"); try iFrame.
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
          + iApply (wp_if_t e (to_rtstmt stk_id s) (to_rtstmt stk_id s0) stk_id (symb_stk_to_stk_frm stk1 mp) (trnsl_assertion p stk_id mp) (trnsl_assertion Q stk_id mp) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu] [HΦ]"); try iFrame.
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

          + iApply (wp_if_f e (to_rtstmt stk_id s) (to_rtstmt stk_id s0) stk_id (symb_stk_to_stk_frm stk1 mp) (trnsl_assertion p stk_id mp) (trnsl_assertion Q stk_id mp) (lang.LitUnit) (inv_set_to_namespace mask) with "[IH'] [IH' Hstk Hu] [HΦ]"); try iFrame.
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

        iIntros "[Hstk Hu1] HΦ".

        set (subst_map' := @list_to_map var LExpr (gmap var LExpr) _ _ (zip (proc_args).*1 (map (λ val, LVal (trnsl_val val)) arg_vals))).

          set ((trnsl_assertion (subst proc_pre subst_map') stk_id mp)) as proc_frame_pre.
          set (fun ret_val => trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id mp) as proc_frame_post.

        iApply (wp_call _ _ _ _ _ _ (lang.Proc proc_name proc_args proc_locals _) _ u1 proc_frame_post with "[] [Hstk Hu1]"); try iFrame; try done.

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

            iSpecialize ("Hproc" with "[%]"). { exact Hmask_sub. }

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

          { iDestruct (all_proc_tbl_chunks_elem proc_name (Proc proc_args proc_locals proc_pre proc_post proc_body) H0 with "HprocTbl") as "Hproc_tbl".
            iEval (simpl; rewrite Hproc_body) in "Hproc_tbl".
            iFrame "Hproc_tbl". setoid_rewrite <- trnsl_assertion_unfold. iFrame. }

          {
            iNext. iIntros "[%ret_val [Hstk [Hq _]]]".

            have Hproc_frame_post : trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id mp ≡ proc_frame_post ret_val.
            { reflexivity. }

            iApply "HΦ". iFrame. iExists (trnsl_val ret_val).
            iSplitR; [iPureIntro; exact (call_ret_val_well_typed ρ x ret_val)|].

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

        { (* proc body is not well-formed: ruled out by proc_bodies_translate,
             since a registered procedure's body always translates. *)
          exfalso. exact (Hpbt proc_name
            (Proc proc_args proc_locals proc_pre proc_post proc_body) H0 Hproc_body).
        }

        {
          (* proc_body != Skip *)
        inversion H4; subst s.
        iIntros (Φ). iModIntro.
        setoid_rewrite trnsl_assertion_unfold.

        iIntros "[Hstk Hu1] HΦ".

        set (subst_map' := @list_to_map var LExpr (gmap var LExpr) _ _ (zip (proc_args).*1 (map (λ val, LVal (trnsl_val val)) arg_vals))).

          set (trnsl_assertion (subst proc_pre subst_map') stk_id mp) as proc_frame_pre.
          assert ((trnsl_assertion (subst proc_pre subst_map') stk_id mp) ≡ proc_frame_pre) as Hproc_frame_pre. { subst proc_frame_pre; reflexivity. }

          set (fun ret_val => trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id mp) as proc_frame_post.

        iApply (wp_call _ _ _ _ _ _ (lang.Proc proc_name proc_args proc_locals _) _ u1 proc_frame_post with "[] [Hstk Hu1]"); try iFrame; try done.

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

            iSpecialize ("Hproc" with "[%]"). { exact Hmask_sub. }

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

          { iDestruct (all_proc_tbl_chunks_elem proc_name (Proc proc_args proc_locals proc_pre proc_post proc_body) H0 with "HprocTbl") as "Hproc_tbl".
            iEval (simpl; rewrite Hproc_body) in "Hproc_tbl".
            iFrame "Hproc_tbl". setoid_rewrite <- trnsl_assertion_unfold. iFrame. }

          {
            iNext. iIntros "[%ret_val [Hstk [Hq _]]]".

            have Hproc_frame_post : trnsl_assertion (subst proc_post (<["#ret_val":=LVal (trnsl_val ret_val)]> subst_map')) stk_id mp ≡ proc_frame_post ret_val.
            { reflexivity. }

            iApply "HΦ". iFrame. iExists (trnsl_val ret_val).
            iSplitR; [iPureIntro; exact (call_ret_val_well_typed ρ x ret_val)|].

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
        iIntros "[Hstack [Hown %Hfpv]]".
        pose proof (RAPack_fpuValid Γ (ra_map r)) as HRA_fpu.
        destruct (Γ (ra_map r)) as [i [U [Hdisc [Heq_car [Hindx [Hcomp Hval]]]]]] eqn:H_RA_Pack.
        iDestruct "Hown" as (l chunk_old) "[%Heq [%Hown_eval Hown]]".
        destruct (interp_lexpr_ra_fpuvalid_inv r chunk_old lexpr_old lexpr_new mp Hown_eval Hfpv)
          as [chunk_new [Hnew_eval Hfpu]].

        iFrame.

        apply (HRA_fpu chunk_old chunk_new) in Hfpu.

        iMod (own_update _
          (transport (f_equal cmra_car Hindx) ((transport Heq_car chunk_old)))
          (transport (f_equal cmra_car Hindx) ((transport Heq_car chunk_new)))
       with "Hown") as "Hown".

       { apply transport_cmra_update. exact Hfpu.  }

       iModIntro. rewrite H_RA_Pack. iExists l, chunk_new. iFrame.
       iPureIntro. split; [exact Heq | exact Hnew_eval].

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
      (* The per-invariant shared worlds are established.  The calculus has no
         rule that could produce this -- an [LInv] fact is only ever *traded
         for* by [InvAllocRule], never conjured -- so it is an explicit
         premise recording how the ghost state was set up, exactly as
         [Hbodies] records that every procedure body was verified. *)
      (Hworlds : ⊢ all_inv_worlds)
      (* Every procedure's own registration is established, and its body
         actually compiles -- same status as Hworlds: no rule ever produces
         proc_tbl_chunk (ProcCallRuleRet needs it purely to satisfy wp_call's
         operational precondition, not as part of the Hoare-logic contract
         itself), so both are explicit premises recording how the ghost
         state/program were set up. *)
      (Hwtbl : ⊢ all_proc_tbl_chunks)
      (Hpbt : proc_bodies_translate)
      (* "#ret_val" is itself a stack variable, so by the time the body
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
        "%Henv %Hmsk_sub %Hargs_present %Harg_vals %Hlocals_typed %Hdom_val %Harg_vals_typed %Hprecond_eq %Hpostcond_eq %Hstmt_shape".

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
      destruct (Hbody_msk msk Hmsk_sub dll) as (stk0' & lv_final & Hrv_final & HRHT).

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

      iPoseProof (rrl_validity ρ σ stk_id
        (LAnd (LStack (list_to_map (zip names lvs)))
           (subst (proc_precond_of proc_record) (list_to_map (zip args (map LVar args_lvs)))))
        msk (proc_body_of proc_record)
        (LAnd (LStack stk0')
           (subst (proc_postcond_of proc_record)
              (<["#ret_val" := LVar lv_final]> (list_to_map (zip args (map LVar args_lvs))))))
        Hwf Hpbt Hwelldef Hmsk_sub with "[]") as "Htriple".
      { iSplitR.
        { iModIntro. iApply Hworlds. }
        iSplitR.
        { iModIntro. iApply Hwtbl. }
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
        + iEval (rewrite Hpostcond_bridge') in "Hpost_pred". iFrame.

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
          (inv_set_to_namespace msk) stk_id with "[Hpost_stk Hpost_pred]").
        { iExists ret_val, (symb_stk_to_stk_frm stk0' mp0). iFrame "Hpost_stk".
          iSplitR.
          - iPureIntro. simpl. rewrite lookup_fmap Hrv_final. reflexivity.
          - iEval (rewrite Hpostcond_bridge') in "Hpost_pred". iFrame. }
        iNext. iIntros "[Hpost _]".
        iApply "HΦ'". iFrame "Hpost".
    Qed.

  End MainTranslation.
