From Coq Require Import ClassicalEpsilon FunctionalExtensionality Lia
  Program.Equality.
From stdpp Require Import gmap sets.

From raven_iris.rich_raven_lang Require Import
  typed_core typed_analysis_view typed_assertion typed_ir typed_runtime.

(** Certified source-to-source normalization for typed Raven programs. *)
Module TypedNormalizationBase.

Module Make (LegacyRAs : ra_base.RA_CONFIG)
    (Logic : TypedAssertion.LOGIC_SIGNATURE).
Module Runtime := TypedRuntime.Make LegacyRAs Logic.
Module Hoare := Runtime.Validation.Hoare.
Module Assertions := Runtime.Translation.Assertions.
Module Core := Runtime.Core.
Module IR := Runtime.IR.
Module GenericRegions := Runtime.GenericRegions.
Module StructuredCertificates := Runtime.StructuredCertificates.
Import TypedCore TypedIR Runtime IR Core Runtime.Translation.
Import StructuredCertificates.

Notation pexpr_dependencies :=
  Hoare.ResourceHoare.pexpr_dependencies.
Notation pexpr_list_dependencies :=
  Hoare.ResourceHoare.pexpr_list_dependencies.
Notation statement_writes := Hoare.ResourceHoare.statement_writes.

(** Proof-facing certificate that the invariant instance named at a closing
    fold is the one named when the access was opened.  The baseline
    normalizer obtains this from syntactic stability.  A future preprocessing
    pass may instead snapshot the arguments in proof-only ghost variables and
    prove the same interface after replacing both annotations by the snapshot.
    Nothing below depends on how the certificate was obtained. *)
Record access_argument_stability {Γ F Δ invariant}
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (opening_store closing_store : symbolic_store Γ F Δ) : Prop := {
  stable_symbolized_arguments :
    IR.symbolize_expr_list closing_store arguments =
      IR.symbolize_expr_list opening_store arguments;
}.

(** General boundary relation used by the traversal.  Opening and closing
    annotations need not be the same source syntax; only their symbolized
    invariant arguments must agree.  The future ghost-snapshot preprocessing
    pass targets exactly this interface. *)
Record access_argument_compatibility {Γ F Δ invariant}
    (opening_arguments closing_arguments :
      pexpr_list Γ (Logic.invariant_args invariant))
    (opening_store closing_store : symbolic_store Γ F Δ) : Prop := {
  compatible_symbolized_arguments :
    IR.symbolize_expr_list closing_store closing_arguments =
      IR.symbolize_expr_list opening_store opening_arguments;
}.

Definition access_argument_compatibility_of_stability {Γ F Δ invariant}
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (opening_store closing_store : symbolic_store Γ F Δ)
    (stable : access_argument_stability arguments opening_store closing_store) :
    access_argument_compatibility arguments arguments opening_store
      closing_store.
Proof.
  destruct stable as [Hstable].
  exact {| compatible_symbolized_arguments := Hstable |}.
Defined.

Definition access_argument_stability_of_equality {Γ F Δ invariant}
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (opening_store closing_store : symbolic_store Γ F Δ)
    (Heq : IR.symbolize_expr_list closing_store arguments =
      IR.symbolize_expr_list opening_store arguments) :
    access_argument_stability arguments opening_store closing_store :=
  {| stable_symbolized_arguments := Heq |}.

Definition syntactic_access_argument_stability {Γ F Δ invariant}
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (store : symbolic_store Γ F Δ) :
    access_argument_stability arguments store store :=
  {| stable_symbolized_arguments := eq_refl |}.

Fixpoint unfold_free {Γ} (statement : stmt Γ) : Prop :=
  match statement with
  | TUnfold _ _ _ => False
  | TInvAccess _ _ body | TAtomic _ body => unfold_free body
  | TIf _ _ then_branch else_branch =>
      unfold_free then_branch /\ unfold_free else_branch
  | TSeq _ first second => unfold_free first /\ unfold_free second
  | _ => True
  end.

Fixpoint access_neutral {Γ} (statement : stmt Γ) : Prop :=
  match statement with
  | TUnfold _ _ _ | TFold _ _ _ => False
  | TInvAccess _ _ body | TAtomic _ body => access_neutral body
  | TIf _ _ then_branch else_branch =>
      access_neutral then_branch /\ access_neutral else_branch
  | TSeq _ first second => access_neutral first /\ access_neutral second
  | _ => True
  end.

(** Syntactic acceptance certificate for the first end-to-end normalizer.
    It records only the deliberately supported source layouts; it is not an
    execution semantics or a second interpretation of statements.  The
    analyzer certificate remains responsible for all LIFO and atomic-step
    facts, while assertion alignment recovers invariant instances. *)
Inductive baseline_normalizable {Γ} : stmt Γ -> Type :=
| BaselineUnfoldFree statement :
    unfold_free statement -> baseline_normalizable statement
| BaselineSequence node first second :
    access_neutral first ->
    baseline_normalizable second ->
    baseline_normalizable (TSeq node first second)
| BaselineBalancedSequence node first second :
    baseline_normalizable first ->
    baseline_normalizable second ->
    baseline_normalizable (TSeq node first second)
| BaselineConditional node condition then_branch else_branch :
    baseline_normalizable then_branch ->
    baseline_normalizable else_branch ->
    baseline_normalizable (TIf node condition then_branch else_branch)
| BaselineTerminalAccess outer_node unfold_node body_sequence_node fold_node
    invariant opening_arguments closing_arguments body :
    access_neutral body ->
    opening_arguments = closing_arguments ->
    pexpr_list_dependencies opening_arguments ## statement_writes body ->
    baseline_normalizable
      (TSeq outer_node (TUnfold unfold_node invariant opening_arguments)
        (TSeq body_sequence_node body
          (TFold fold_node invariant closing_arguments)))
| BaselineAccessThen outer_node unfold_node body_sequence_node
    fold_sequence_node fold_node invariant opening_arguments closing_arguments
    body work :
    access_neutral body ->
    opening_arguments = closing_arguments ->
    pexpr_list_dependencies opening_arguments ## statement_writes body ->
    baseline_normalizable work ->
    baseline_normalizable
      (TSeq outer_node (TUnfold unfold_node invariant opening_arguments)
        (TSeq body_sequence_node body
          (TSeq fold_sequence_node
            (TFold fold_node invariant closing_arguments) work))).

(** Executable recognizers for the source-shape portion of the restricted
    analysis.  Argument stability and write effects are intentionally not
    decided here: Step 3 enriches the access stack with precisely that
    information. *)
Fixpoint unfold_freeb {Γ} (statement : stmt Γ) : bool :=
  match statement with
  | TUnfold _ _ _ => false
  | TInvAccess _ _ body | TAtomic _ body => unfold_freeb body
  | TIf _ _ then_branch else_branch =>
      unfold_freeb then_branch && unfold_freeb else_branch
  | TSeq _ first second => unfold_freeb first && unfold_freeb second
  | _ => true
  end.

Fixpoint access_neutralb {Γ} (statement : stmt Γ) : bool :=
  match statement with
  | TUnfold _ _ _ | TFold _ _ _ => false
  | TInvAccess _ _ body | TAtomic _ body => access_neutralb body
  | TIf _ _ then_branch else_branch =>
      access_neutralb then_branch && access_neutralb else_branch
  | TSeq _ first second => access_neutralb first && access_neutralb second
  | _ => true
  end.

(** Conservative executable check for the source layouts handled by the
    baseline normalizer.  A raw unfold is accepted only when its enclosing
    sequence exposes the matching fold and an access-neutral body.  The
    equality test is only for invariant identities; argument compatibility
    is deliberately deferred to the effect-aware pass. *)
Fixpoint restricted_fragment_shape_check {Γ} (statement : stmt Γ) : bool :=
  match statement with
  | TUnfold _ _ _ => false
  | TInvAccess _ _ body | TAtomic _ body => unfold_freeb body
  | TIf _ _ then_branch else_branch =>
      restricted_fragment_shape_check then_branch &&
        restricted_fragment_shape_check else_branch
  | TSeq _ first second =>
      match first, second with
      | TUnfold _ opening_invariant _,
          TSeq _ body (TFold _ closing_invariant _) =>
          bool_decide (opening_invariant = closing_invariant) &&
            access_neutralb body
      | TUnfold _ opening_invariant _,
          TSeq _ body (TSeq _ (TFold _ closing_invariant _) work) =>
          bool_decide (opening_invariant = closing_invariant) &&
            access_neutralb body && restricted_fragment_shape_check work
      | _, _ =>
          restricted_fragment_shape_check first &&
            restricted_fragment_shape_check second
      end
  | _ => true
  end.

Definition restricted_fragment_shape {Γ} (statement : stmt Γ) : Prop :=
  restricted_fragment_shape_check statement = true.

(** Executable key for the first conservative argument fragment.  Requiring
    every invariant argument to be a stack variable makes equality reduce to
    ordinary list equality and avoids proof-generated dependent transports.
    Literal and compound keys can be added later without changing callers. *)
Fixpoint restricted_argument_variable_indices {Γ ts}
    (expressions : pexpr_list Γ ts) : option (list nat) :=
  match expressions with
  | PENil => Some []
  | PECons expression tail =>
      match expression, restricted_argument_variable_indices tail with
      | PEVar variable, Some indices =>
          Some (member_index variable :: indices)
      | _, _ => None
      end
  end.

Definition restricted_pexpr_list_eqb {Γ ts}
    (left right : pexpr_list Γ ts) : bool :=
  match restricted_argument_variable_indices left,
      restricted_argument_variable_indices right with
  | Some left_indices, Some right_indices =>
      bool_decide (left_indices = right_indices)
  | _, _ => false
  end.

Lemma member_index_injective {Γ t} (left right : member Γ t) :
  member_index left = member_index right -> left = right.
Proof.
  induction left; dependent destruction right; cbn; intro Hindex;
    try discriminate.
  - reflexivity.
  - f_equal. apply IHleft. now injection Hindex.
Qed.

Lemma normalization_update_store_here {F Δ head_type tail_context}
    (head : value_ref F Δ head_type)
    (tail : symbolic_store tail_context F Δ) :
  IR.update_store_with_bound (StoreCons head tail) MHere =
    StoreCons (RefBound MHere) (Assertions.weaken_store tail).
Proof.
  unfold IR.update_store_with_bound, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl). reflexivity.
Qed.

Lemma normalization_update_store_there {F Δ head_type tail_context t}
    (head : value_ref F Δ head_type)
    (tail : symbolic_store tail_context F Δ)
    (target : pvar tail_context t) :
  IR.update_store_with_bound (StoreCons head tail) (MThere target) =
    StoreCons (Assertions.weaken_ref head)
      (IR.update_store_with_bound tail target).
Proof.
  unfold IR.update_store_with_bound, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl). reflexivity.
Qed.

Lemma normalization_lookup_store_here {F Δ head_type tail_context}
    (head : value_ref F Δ head_type)
    (tail : symbolic_store tail_context F Δ) :
  lookup_store (StoreCons head tail) _ MHere = head.
Proof.
  unfold lookup_store, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl). reflexivity.
Qed.

Lemma normalization_lookup_store_there {F Δ head_type tail_context t}
    (head : value_ref F Δ head_type)
    (tail : symbolic_store tail_context F Δ)
    (variable : pvar tail_context t) :
  lookup_store (StoreCons head tail) _ (MThere variable) =
    lookup_store tail _ variable.
Proof.
  unfold lookup_store, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl). reflexivity.
Qed.

Lemma normalization_lookup_weaken_store {Γ F Δ t u}
    (store : symbolic_store Γ F Δ) (variable : pvar Γ t) :
  lookup_store (@Assertions.weaken_store Γ F Δ u store) t variable =
    @Assertions.weaken_ref F Δ t u (lookup_store store t variable).
Proof.
  induction store; dependent destruction variable.
  - cbn [Assertions.weaken_store].
    rewrite !normalization_lookup_store_here. reflexivity.
  - cbn [Assertions.weaken_store].
    rewrite !normalization_lookup_store_there. apply IHstore.
Qed.

Lemma lookup_update_store_with_bound_neq {Γ F Δ t u}
    (store : symbolic_store Γ F Δ) (target : pvar Γ t)
    (variable : pvar Γ u) :
  member_index variable <> member_index target ->
  lookup_store (IR.update_store_with_bound store target) u variable =
    Assertions.weaken_ref (lookup_store store u variable).
Proof.
  induction store; dependent destruction target; dependent destruction variable;
    intro Hneq.
  - exfalso. apply Hneq. reflexivity.
  - rewrite normalization_update_store_here,
      normalization_lookup_store_there,
      normalization_lookup_weaken_store,
      normalization_lookup_store_there. reflexivity.
  - rewrite normalization_update_store_there,
      !normalization_lookup_store_here. reflexivity.
  - rewrite normalization_update_store_there,
      !normalization_lookup_store_there.
    apply IHstore. intro Heq. apply Hneq. cbn. now f_equal.
Qed.

Lemma symbolize_expr_update_store_with_bound_neq {Γ F Δ t u}
    (store : symbolic_store Γ F Δ) (target : pvar Γ t)
    (expression : pexpr Γ u) :
  member_index target ∉ pexpr_dependencies expression ->
  IR.symbolize_expr (IR.update_store_with_bound store target)
      expression =
    Assertions.weaken_expr (IR.symbolize_expr store expression).
Proof.
  induction expression; cbn [pexpr_dependencies IR.symbolize_expr
    Assertions.weaken_expr]; intro Hnot.
  - f_equal. apply lookup_update_store_with_bound_neq.
    intro Heq. apply Hnot. apply elem_of_singleton_2. exact (eq_sym Heq).
  - reflexivity.
  - f_equal. apply IHexpression. exact Hnot.
  - apply not_elem_of_union in Hnot as [Hleft Hright].
    f_equal; auto.
Qed.

Lemma symbolize_expr_list_update_store_with_bound_neq {Γ F Δ t ts}
    (store : symbolic_store Γ F Δ) (target : pvar Γ t)
    (expressions : pexpr_list Γ ts) :
  member_index target ∉ pexpr_list_dependencies expressions ->
  IR.symbolize_expr_list (IR.update_store_with_bound store target)
      expressions =
    Assertions.weaken_expr_list (IR.symbolize_expr_list store expressions).
Proof.
  induction expressions; cbn [pexpr_list_dependencies
    IR.symbolize_expr_list Assertions.weaken_expr_list]; intro Hnot.
  - reflexivity.
  - apply not_elem_of_union in Hnot as [Hhead Htail].
    f_equal.
    + now apply symbolize_expr_update_store_with_bound_neq.
    + now apply IHexpressions.
Qed.

(** Every syntactic stack owner in an assertion agrees on the symbolic
    interpretation of a fixed source-level argument vector.  The expected
    vector is weakened when a logical binder is crossed; this is assertion
    structure only, not another interpretation of Raven statements. *)
Fixpoint stack_arguments_agree {Γ F Δ ts}
    (arguments : pexpr_list Γ ts) (expected : Assertions.expr_list F Δ ts)
    (formula : Assertions.assertion Γ F Δ) : Prop :=
  match formula with
  | Assertions.AStack store =>
      IR.symbolize_expr_list store arguments = expected
  | Assertions.AExists _ body | Assertions.AForall _ body =>
      stack_arguments_agree arguments
        (Assertions.weaken_expr_list expected) body
  | Assertions.AIte _ then_branch else_branch =>
      stack_arguments_agree arguments expected then_branch /\
      stack_arguments_agree arguments expected else_branch
  | Assertions.AAnd left_formula right_formula =>
      stack_arguments_agree arguments expected left_formula /\
      stack_arguments_agree arguments expected right_formula
  | _ => True
  end.

(** Agreement after eliminating logical binders by a proof-facing
    substitution.  Existentials admit either the old parametric/fresh mode or
    a concrete witness in the target context.  The second mode is what makes
    current-witness existential introduction visible without attempting to
    substitute through [AStack] itself. *)
Definition extend_bound_subst {F Δ Δ' u}
    (substitution : Assertions.bound_subst F Δ Δ')
    (witness : Core.expr F Δ' u) :
    Assertions.bound_subst F (u :: Δ) Δ' :=
  fun t variable =>
    match view_member variable with
    | MVHere => witness
    | MVThere variable' => substitution _ variable'
    end.

Definition identity_bound_subst {F Δ} :
    Assertions.bound_subst F Δ Δ :=
  fun t variable => Core.ERef (Core.RefBound variable).

Fixpoint stack_arguments_agree_under {Γ F Δ Δ' ts}
    (substitution : Assertions.bound_subst F Δ Δ')
    (arguments : pexpr_list Γ ts)
    (expected : Assertions.expr_list F Δ' ts)
    (formula : Assertions.assertion Γ F Δ) : Prop :=
  match formula with
  | Assertions.AStack store =>
      Assertions.subst_bound_expr_list substitution
        (IR.symbolize_expr_list store arguments) = expected
  | Assertions.AExists u body =>
      stack_arguments_agree_under
        (Assertions.lift_bound_subst substitution) arguments
        (Assertions.weaken_expr_list expected) body \/
      exists witness : Core.expr F Δ' u,
        stack_arguments_agree_under
          (extend_bound_subst substitution witness) arguments expected body
  | Assertions.AForall _ body =>
      stack_arguments_agree_under
        (Assertions.lift_bound_subst substitution) arguments
        (Assertions.weaken_expr_list expected) body
  | Assertions.AIte _ then_branch else_branch =>
      stack_arguments_agree_under substitution arguments expected then_branch /\
      stack_arguments_agree_under substitution arguments expected else_branch
  | Assertions.AAnd left_formula right_formula =>
      stack_arguments_agree_under substitution arguments expected left_formula /\
      stack_arguments_agree_under substitution arguments expected right_formula
  | _ => True
  end.

Definition witness_aware_stack_arguments_agree {Γ F Δ ts}
    (arguments : pexpr_list Γ ts) (expected : Assertions.expr_list F Δ ts)
    (formula : Assertions.assertion Γ F Δ) : Prop :=
  stack_arguments_agree_under identity_bound_subst arguments expected formula.

Lemma subst_bound_expr_identity_ext {F Δ t}
    (substitution : Assertions.bound_subst F Δ Δ)
    (Hidentity : forall u (variable : bvar Δ u),
      substitution u variable = Core.ERef (Core.RefBound variable))
    (expression : Core.expr F Δ t) :
  Assertions.subst_bound_expr substitution expression = expression.
Proof.
  induction expression; cbn [Assertions.subst_bound_expr
    Assertions.subst_bound_ref].
  - destruct reference; try reflexivity. apply Hidentity.
  - reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma subst_bound_expr_list_identity_ext {F Δ ts}
    (substitution : Assertions.bound_subst F Δ Δ)
    (Hidentity : forall u (variable : bvar Δ u),
      substitution u variable = Core.ERef (Core.RefBound variable))
    (expressions : Assertions.expr_list F Δ ts) :
  Assertions.subst_bound_expr_list substitution expressions = expressions.
Proof.
  induction expressions as [|u us head tail IH];
    cbn [Assertions.subst_bound_expr_list].
  - reflexivity.
  - rewrite (subst_bound_expr_identity_ext substitution Hidentity head).
    rewrite IH. reflexivity.
Qed.

Lemma stack_arguments_agree_under_identity {Γ F Δ ts}
    (substitution : Assertions.bound_subst F Δ Δ)
    (Hidentity : forall u (variable : bvar Δ u),
      substitution u variable = Core.ERef (Core.RefBound variable))
    (arguments : pexpr_list Γ ts) (expected : Assertions.expr_list F Δ ts)
    (formula : Assertions.assertion Γ F Δ) :
  stack_arguments_agree arguments expected formula ->
  stack_arguments_agree_under substitution arguments expected formula.
Proof.
  revert substitution Hidentity expected.
  induction formula; intros substitution Hidentity expected Hagree;
    cbn [stack_arguments_agree stack_arguments_agree_under] in Hagree |- *;
    try tauto.
  - rewrite (subst_bound_expr_list_identity_ext substitution Hidentity).
    exact Hagree.
  - left. apply IHformula; [|exact Hagree].
    intros u variable. dependent destruction variable.
    + unfold Assertions.lift_bound_subst. rewrite view_member_here. reflexivity.
    + unfold Assertions.lift_bound_subst. rewrite view_member_there.
      rewrite Hidentity. reflexivity.
  - apply IHformula; [|exact Hagree].
    intros u variable. dependent destruction variable.
    + unfold Assertions.lift_bound_subst. rewrite view_member_here. reflexivity.
    + unfold Assertions.lift_bound_subst. rewrite view_member_there.
      rewrite Hidentity. reflexivity.
  - split; [apply IHformula1 | apply IHformula2]; tauto.
  - split; [apply IHformula1 | apply IHformula2]; tauto.
Qed.

Lemma stack_arguments_agree_witness_aware {Γ F Δ ts}
    (arguments : pexpr_list Γ ts) (expected : Assertions.expr_list F Δ ts)
    (formula : Assertions.assertion Γ F Δ) :
  stack_arguments_agree arguments expected formula ->
  witness_aware_stack_arguments_agree arguments expected formula.
Proof.
  apply stack_arguments_agree_under_identity.
  intros. reflexivity.
Qed.

Lemma subst_bound_expr_after_rename {F Δ Δr Θ t}
    (renaming : Assertions.bound_renaming Δ Δr)
    (source_subst : Assertions.bound_subst F Δ Θ)
    (target_subst : Assertions.bound_subst F Δr Θ)
    (Hcompatible : forall u (variable : bvar Δ u),
      target_subst u (renaming u variable) = source_subst u variable)
    (expression : Core.expr F Δ t) :
  Assertions.subst_bound_expr target_subst
      (Assertions.rename_bound_expr renaming expression) =
    Assertions.subst_bound_expr source_subst expression.
Proof.
  induction expression; cbn [Assertions.subst_bound_expr
    Assertions.subst_bound_ref Assertions.rename_bound_expr
    Assertions.rename_bound_ref].
  - destruct reference; try reflexivity. apply Hcompatible.
  - reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma subst_bound_expr_list_after_rename {F Δ Δr Θ ts}
    (renaming : Assertions.bound_renaming Δ Δr)
    (source_subst : Assertions.bound_subst F Δ Θ)
    (target_subst : Assertions.bound_subst F Δr Θ)
    (Hcompatible : forall u (variable : bvar Δ u),
      target_subst u (renaming u variable) = source_subst u variable)
    (expressions : Assertions.expr_list F Δ ts) :
  Assertions.subst_bound_expr_list target_subst
      (Assertions.rename_bound_expr_list renaming expressions) =
    Assertions.subst_bound_expr_list source_subst expressions.
Proof.
  induction expressions as [|u us head tail IH];
    cbn [Assertions.subst_bound_expr_list
      Assertions.rename_bound_expr_list].
  - reflexivity.
  - rewrite (subst_bound_expr_after_rename renaming source_subst target_subst
      Hcompatible head), IH. reflexivity.
Qed.

Lemma subst_bound_assertion_after_rename_stack_free
    {Γ F Δ Δr Θ}
    (renaming : Assertions.bound_renaming Δ Δr)
    (source_subst : Assertions.bound_subst F Δ Θ)
    (target_subst : Assertions.bound_subst F Δr Θ)
    (Hcompatible : forall u (variable : bvar Δ u),
      target_subst u (renaming u variable) = source_subst u variable)
    (formula : Assertions.assertion Γ F Δ) :
  Assertions.stack_free formula ->
  Assertions.subst_bound_assertion target_subst
      (Assertions.rename_bound_assertion renaming formula) =
    Assertions.subst_bound_assertion source_subst formula.
Proof.
  intro Hfree. revert Δr Θ renaming source_subst target_subst Hcompatible.
  induction Hfree; intros Δr Θ renaming source_subst target_subst Hcompatible;
    cbn [Assertions.subst_bound_assertion Assertions.rename_bound_assertion].
  - rewrite (subst_bound_expr_after_rename renaming source_subst target_subst
      Hcompatible). reflexivity.
  - reflexivity.
  - rewrite !(subst_bound_expr_after_rename renaming source_subst target_subst
      Hcompatible). reflexivity.
  - rewrite !(subst_bound_expr_after_rename renaming source_subst target_subst
      Hcompatible). reflexivity.
  - rewrite !(subst_bound_expr_after_rename renaming source_subst target_subst
      Hcompatible). reflexivity.
  - rewrite (subst_bound_expr_after_rename renaming source_subst target_subst
      Hcompatible). reflexivity.
  - rewrite (IHHfree (t :: Δr) (t :: Θ)
      (Assertions.lift_bound_renaming renaming)
      (Assertions.lift_bound_subst source_subst)
      (Assertions.lift_bound_subst target_subst)).
    + destruct (Assertions.subst_bound_assertion
        (Assertions.lift_bound_subst source_subst) body); reflexivity.
    + intros u variable. dependent destruction variable.
      * unfold Assertions.lift_bound_renaming, Assertions.lift_bound_subst.
        rewrite !view_member_here. reflexivity.
      * unfold Assertions.lift_bound_renaming, Assertions.lift_bound_subst.
        rewrite !view_member_there. rewrite Hcompatible. reflexivity.
  - rewrite (IHHfree (t :: Δr) (t :: Θ)
      (Assertions.lift_bound_renaming renaming)
      (Assertions.lift_bound_subst source_subst)
      (Assertions.lift_bound_subst target_subst)).
    + destruct (Assertions.subst_bound_assertion
        (Assertions.lift_bound_subst source_subst) body); reflexivity.
    + intros u variable. dependent destruction variable.
      * unfold Assertions.lift_bound_renaming, Assertions.lift_bound_subst.
        rewrite !view_member_here. reflexivity.
      * unfold Assertions.lift_bound_renaming, Assertions.lift_bound_subst.
        rewrite !view_member_there. rewrite Hcompatible. reflexivity.
  - rewrite (subst_bound_expr_after_rename renaming source_subst target_subst
      Hcompatible).
    rewrite (IHHfree1 _ _ renaming source_subst target_subst Hcompatible).
    rewrite (IHHfree2 _ _ renaming source_subst target_subst Hcompatible).
    destruct (Assertions.subst_bound_assertion source_subst then_branch);
      destruct (Assertions.subst_bound_assertion source_subst else_branch);
      reflexivity.
  - rewrite (subst_bound_expr_list_after_rename renaming source_subst
      target_subst Hcompatible). reflexivity.
  - rewrite (subst_bound_expr_list_after_rename renaming source_subst
      target_subst Hcompatible). reflexivity.
  - rewrite (IHHfree1 _ _ renaming source_subst target_subst Hcompatible).
    rewrite (IHHfree2 _ _ renaming source_subst target_subst Hcompatible).
    destruct (Assertions.subst_bound_assertion source_subst left);
      destruct (Assertions.subst_bound_assertion source_subst right);
      reflexivity.
Qed.

Lemma subst_bound_assertion_identity_stack_free {Γ F Δ}
    (substitution : Assertions.bound_subst F Δ Δ)
    (Hidentity : forall u (variable : bvar Δ u),
      substitution u variable = Core.ERef (Core.RefBound variable))
    (formula : Assertions.assertion Γ F Δ) :
  Assertions.stack_free formula ->
  Assertions.subst_bound_assertion substitution formula = Some formula.
Proof.
  intro Hfree. revert substitution Hidentity.
  induction Hfree; intros substitution Hidentity;
    cbn [Assertions.subst_bound_assertion].
  - rewrite (subst_bound_expr_identity_ext substitution Hidentity). reflexivity.
  - reflexivity.
  - rewrite !(subst_bound_expr_identity_ext substitution Hidentity). reflexivity.
  - rewrite !(subst_bound_expr_identity_ext substitution Hidentity). reflexivity.
  - rewrite !(subst_bound_expr_identity_ext substitution Hidentity). reflexivity.
  - rewrite (subst_bound_expr_identity_ext substitution Hidentity). reflexivity.
  - rewrite (IHHfree (Assertions.lift_bound_subst substitution)); [reflexivity|].
    intros u variable. dependent destruction variable.
    + unfold Assertions.lift_bound_subst. rewrite view_member_here. reflexivity.
    + unfold Assertions.lift_bound_subst. rewrite view_member_there.
      rewrite Hidentity. reflexivity.
  - rewrite (IHHfree (Assertions.lift_bound_subst substitution)); [reflexivity|].
    intros u variable. dependent destruction variable.
    + unfold Assertions.lift_bound_subst. rewrite view_member_here. reflexivity.
    + unfold Assertions.lift_bound_subst. rewrite view_member_there.
      rewrite Hidentity. reflexivity.
  - rewrite (subst_bound_expr_identity_ext substitution Hidentity).
    rewrite (IHHfree1 substitution Hidentity),
      (IHHfree2 substitution Hidentity). reflexivity.
  - rewrite (subst_bound_expr_list_identity_ext substitution Hidentity).
    reflexivity.
  - rewrite (subst_bound_expr_list_identity_ext substitution Hidentity).
    reflexivity.
  - rewrite (IHHfree1 substitution Hidentity),
      (IHHfree2 substitution Hidentity). reflexivity.
Qed.

Lemma stack_arguments_agree_under_rename {Γ F Δ Δr Θ ts}
    (renaming : Assertions.bound_renaming Δ Δr)
    (source_subst : Assertions.bound_subst F Δ Θ)
    (target_subst : Assertions.bound_subst F Δr Θ)
    (Hcompatible : forall u (variable : bvar Δ u),
      target_subst u (renaming u variable) = source_subst u variable)
    (arguments : pexpr_list Γ ts) (expected : Assertions.expr_list F Θ ts)
    (formula : Assertions.assertion Γ F Δ) :
  stack_arguments_agree_under source_subst arguments expected formula ->
  stack_arguments_agree_under target_subst arguments expected
    (Assertions.rename_bound_assertion renaming formula).
Proof.
  revert Δr Θ renaming source_subst target_subst Hcompatible expected.
  induction formula; intros Δr Θ renaming source_subst target_subst
      Hcompatible expected Hagree;
    cbn [stack_arguments_agree_under Assertions.rename_bound_assertion]
      in Hagree |- *; try tauto.
  - rewrite IR.symbolize_expr_list_rename_bound_store.
    rewrite (subst_bound_expr_list_after_rename renaming source_subst
      target_subst Hcompatible). exact Hagree.
  - destruct Hagree as [Hfresh | [witness Hwitness]].
    + left. eapply IHformula; [|exact Hfresh].
      intros u variable. dependent destruction variable.
      * unfold Assertions.lift_bound_renaming,
          Assertions.lift_bound_subst. rewrite !view_member_here. reflexivity.
      * unfold Assertions.lift_bound_renaming,
          Assertions.lift_bound_subst. rewrite !view_member_there.
        rewrite Hcompatible. reflexivity.
    + right. exists witness. eapply IHformula; [|exact Hwitness].
      intros u variable. dependent destruction variable.
      * rewrite Assertions.lift_bound_renaming_here.
        unfold extend_bound_subst. rewrite !view_member_here. reflexivity.
      * rewrite Assertions.lift_bound_renaming_there.
        unfold extend_bound_subst. rewrite !view_member_there.
        apply Hcompatible.
  - eapply (IHformula (t :: Δr) (t :: Θ)
      (Assertions.lift_bound_renaming renaming)
      (Assertions.lift_bound_subst source_subst)
      (Assertions.lift_bound_subst target_subst)); [|exact Hagree].
    intros u variable. dependent destruction variable.
    + unfold Assertions.lift_bound_renaming,
        Assertions.lift_bound_subst. rewrite !view_member_here. reflexivity.
    + unfold Assertions.lift_bound_renaming,
        Assertions.lift_bound_subst. rewrite !view_member_there.
      f_equal. apply Hcompatible.
  - split.
    + eapply IHformula1; [exact Hcompatible|exact (proj1 Hagree)].
    + eapply IHformula2; [exact Hcompatible|exact (proj2 Hagree)].
  - split.
    + eapply IHformula1; [exact Hcompatible|exact (proj1 Hagree)].
    + eapply IHformula2; [exact Hcompatible|exact (proj2 Hagree)].
Qed.

(** Reflection along a renaming when the proof-facing substitutions agree on
    its image.  Unlike the older strict agreement reflection lemma below,
    this does not require the renaming to be injective: the equality after
    applying the two substitutions is precisely the relevant invariant. *)
Lemma stack_arguments_agree_under_rename_reflect {Γ F Δ Δr Θ ts}
    (renaming : Assertions.bound_renaming Δ Δr)
    (source_subst : Assertions.bound_subst F Δ Θ)
    (target_subst : Assertions.bound_subst F Δr Θ)
    (Hcompatible : forall u (variable : bvar Δ u),
      target_subst u (renaming u variable) = source_subst u variable)
    (arguments : pexpr_list Γ ts) (expected : Assertions.expr_list F Θ ts)
    (formula : Assertions.assertion Γ F Δ) :
  stack_arguments_agree_under target_subst arguments expected
    (Assertions.rename_bound_assertion renaming formula) ->
  stack_arguments_agree_under source_subst arguments expected formula.
Proof.
  revert Δr Θ renaming source_subst target_subst Hcompatible expected.
  induction formula; intros Δr Θ renaming source_subst target_subst
      Hcompatible expected Hagree;
    cbn [stack_arguments_agree_under Assertions.rename_bound_assertion]
      in Hagree |- *; try tauto.
  - rewrite IR.symbolize_expr_list_rename_bound_store in Hagree.
    rewrite (subst_bound_expr_list_after_rename renaming source_subst
      target_subst Hcompatible) in Hagree.
    exact Hagree.
  - destruct Hagree as [Hfresh | [witness Hwitness]].
    + left. eapply IHformula; [|exact Hfresh].
      intros u variable. dependent destruction variable.
      * unfold Assertions.lift_bound_renaming,
          Assertions.lift_bound_subst. rewrite !view_member_here. reflexivity.
      * unfold Assertions.lift_bound_renaming,
          Assertions.lift_bound_subst. rewrite !view_member_there.
        f_equal. apply Hcompatible.
    + right. exists witness. eapply IHformula; [|exact Hwitness].
      intros u variable. dependent destruction variable.
      * rewrite Assertions.lift_bound_renaming_here.
        unfold extend_bound_subst. rewrite !view_member_here. reflexivity.
      * rewrite Assertions.lift_bound_renaming_there.
        unfold extend_bound_subst. rewrite !view_member_there.
        apply Hcompatible.
  - eapply IHformula; [|exact Hagree].
    intros u variable. dependent destruction variable.
    + unfold Assertions.lift_bound_renaming,
        Assertions.lift_bound_subst. rewrite !view_member_here. reflexivity.
    + unfold Assertions.lift_bound_renaming,
        Assertions.lift_bound_subst. rewrite !view_member_there.
      f_equal. apply Hcompatible.
  - split.
    + eapply IHformula1; [exact Hcompatible|exact (proj1 Hagree)].
    + eapply IHformula2; [exact Hcompatible|exact (proj2 Hagree)].
  - split.
    + eapply IHformula1; [exact Hcompatible|exact (proj1 Hagree)].
    + eapply IHformula2; [exact Hcompatible|exact (proj2 Hagree)].
Qed.

(** A chosen existential witness does not interfere with agreement for a
    formula merely weakened across that existential.  This is the transport
    needed by the chosen-witness branch of [EntailsExistsElim]. *)
Lemma stack_arguments_agree_under_weaken_reflect_chosen
    {Γ F Δ Θ ts u}
    (substitution : Assertions.bound_subst F Δ Θ)
    (witness : Core.expr F Θ u)
    (arguments : pexpr_list Γ ts) (expected : Assertions.expr_list F Θ ts)
    (formula : Assertions.assertion Γ F Δ) :
  stack_arguments_agree_under (extend_bound_subst substitution witness)
    arguments expected (@Assertions.weaken_assertion Γ F Δ u formula) ->
  stack_arguments_agree_under substitution arguments expected formula.
Proof.
  intro Hagree.
  unfold Assertions.weaken_assertion.
  eapply stack_arguments_agree_under_rename_reflect with
    (renaming := @Assertions.weaken_bound_renaming Δ u); [|exact Hagree].
  intros t variable.
    unfold extend_bound_subst, Assertions.weaken_bound_renaming.
    rewrite !view_member_there. reflexivity.
Qed.

(** Introducing an existential with an already-bound witness is compatible
    with the witness-aware agreement invariant: record that variable as the
    substitution for the freshly introduced existential.  This is a local
    normalization transport, not an unrestricted source-entailment rule. *)
Lemma stack_arguments_agree_under_exists_bound_intro
    {Γ F Δ Θ ts t}
    (substitution : Assertions.bound_subst F Δ Θ)
    (arguments : pexpr_list Γ ts) (expected : Assertions.expr_list F Θ ts)
    (body : Assertions.assertion Γ F (t :: Δ)) (witness : bvar Δ t) :
  stack_arguments_agree_under substitution arguments expected
    (Assertions.rename_bound_assertion
      (Assertions.head_bound_renaming witness) body) ->
  stack_arguments_agree_under substitution arguments expected
    (Assertions.AExists t body).
Proof.
  intro Hagree. cbn [stack_arguments_agree_under].
  right. exists (substitution _ witness).
  eapply stack_arguments_agree_under_rename_reflect with
    (renaming := Assertions.head_bound_renaming witness)
    (target_subst := substitution); [|exact Hagree].
  intros u variable.
  unfold extend_bound_subst, Assertions.head_bound_renaming.
  dependent destruction variable.
  - rewrite !view_member_here. reflexivity.
  - rewrite !view_member_there. reflexivity.
Qed.

Lemma witness_aware_stack_arguments_agree_current_exists {Γ F Δ ts t}
    (arguments : pexpr_list Γ ts)
    (expected : Assertions.expr_list F (t :: Δ) ts)
    (body : Assertions.assertion Γ F (t :: Δ)) :
  witness_aware_stack_arguments_agree arguments expected body ->
  witness_aware_stack_arguments_agree arguments expected
    (@Assertions.weaken_assertion Γ F Δ t
      (Assertions.AExists t body)).
Proof.
  intros Hagree.
  unfold witness_aware_stack_arguments_agree in Hagree |- *.
  unfold Assertions.weaken_assertion.
  cbn [Assertions.rename_bound_assertion stack_arguments_agree_under].
  right. exists (Core.ERef (Core.RefBound MHere)).
  eapply stack_arguments_agree_under_rename with
    (renaming := Assertions.lift_bound_renaming
      (@Assertions.weaken_bound_renaming Δ t))
    (source_subst := @identity_bound_subst F (t :: Δ)); [|exact Hagree].
  intros u variable. dependent destruction variable.
  - rewrite Assertions.lift_bound_renaming_here.
    unfold extend_bound_subst, identity_bound_subst.
    rewrite !view_member_here. reflexivity.
  - rewrite Assertions.lift_bound_renaming_there.
    unfold Assertions.weaken_bound_renaming, extend_bound_subst,
      identity_bound_subst.
    rewrite !view_member_there. reflexivity.
Qed.

Lemma symbolize_expr_weaken_store {Γ F Δ t u}
    (store : symbolic_store Γ F Δ) (expression : pexpr Γ t) :
  IR.symbolize_expr (@Assertions.weaken_store Γ F Δ u store) expression =
    Assertions.weaken_expr (IR.symbolize_expr store expression).
Proof.
  induction expression; cbn [IR.symbolize_expr Assertions.weaken_expr].
  - f_equal. apply normalization_lookup_weaken_store.
  - reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma symbolize_expr_list_weaken_store {Γ F Δ ts u}
    (store : symbolic_store Γ F Δ) (expressions : pexpr_list Γ ts) :
  IR.symbolize_expr_list (@Assertions.weaken_store Γ F Δ u store)
    expressions =
    Assertions.weaken_expr_list (IR.symbolize_expr_list store expressions).
Proof.
  induction expressions; cbn [IR.symbolize_expr_list
    Assertions.weaken_expr_list].
  - reflexivity.
  - f_equal; auto using symbolize_expr_weaken_store.
Qed.

Lemma normalization_lookup_rename_bound_store {Γ F Δ Δ' t}
    (renaming : Assertions.bound_renaming Δ Δ')
    (store : symbolic_store Γ F Δ) (variable : pvar Γ t) :
  lookup_store (Assertions.rename_bound_store renaming store) t variable =
    Assertions.rename_bound_ref renaming (lookup_store store t variable).
Proof.
  induction store; dependent destruction variable; cbn
    [Assertions.rename_bound_store].
  - rewrite !normalization_lookup_store_here. reflexivity.
  - rewrite !normalization_lookup_store_there. exact (IHstore _).
Qed.

Lemma symbolize_expr_rename_bound_store {Γ F Δ Δ' t}
    (renaming : Assertions.bound_renaming Δ Δ')
    (store : symbolic_store Γ F Δ) (expression : pexpr Γ t) :
  IR.symbolize_expr (Assertions.rename_bound_store renaming store)
    expression =
    Assertions.rename_bound_expr renaming
      (IR.symbolize_expr store expression).
Proof.
  induction expression; cbn [IR.symbolize_expr
    Assertions.rename_bound_expr].
  - f_equal. apply normalization_lookup_rename_bound_store.
  - reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma symbolize_expr_list_rename_bound_store {Γ F Δ Δ' ts}
    (renaming : Assertions.bound_renaming Δ Δ')
    (store : symbolic_store Γ F Δ) (expressions : pexpr_list Γ ts) :
  IR.symbolize_expr_list (Assertions.rename_bound_store renaming store)
    expressions =
    Assertions.rename_bound_expr_list renaming
      (IR.symbolize_expr_list store expressions).
Proof.
  induction expressions; cbn [IR.symbolize_expr_list
    Assertions.rename_bound_expr_list].
  - reflexivity.
  - f_equal; auto using symbolize_expr_rename_bound_store.
Qed.

Lemma rename_bound_expr_lift_weaken {F Δ Δ' t u}
    (renaming : Assertions.bound_renaming Δ Δ')
    (expression : Core.expr F Δ t) :
  Assertions.rename_bound_expr
    (Assertions.lift_bound_renaming renaming)
    (Assertions.weaken_expr (u := u) expression) =
  Assertions.weaken_expr
    (Assertions.rename_bound_expr renaming expression).
Proof.
  induction expression; cbn [Assertions.rename_bound_expr
    Assertions.weaken_expr Assertions.rename_bound_ref
    Assertions.weaken_ref Assertions.lift_bound_renaming].
  - destruct reference; cbn [Assertions.rename_bound_ref
      Assertions.weaken_ref]; try reflexivity.
    unfold Assertions.lift_bound_renaming.
    rewrite view_member_there. reflexivity.
  - reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma rename_bound_expr_list_lift_weaken {F Δ Δ' ts u}
    (renaming : Assertions.bound_renaming Δ Δ')
    (expressions : Assertions.expr_list F Δ ts) :
  Assertions.rename_bound_expr_list
    (Assertions.lift_bound_renaming renaming)
    (Assertions.weaken_expr_list (u := u) expressions) =
  Assertions.weaken_expr_list
    (Assertions.rename_bound_expr_list renaming expressions).
Proof.
  induction expressions; cbn [Assertions.rename_bound_expr_list
    Assertions.weaken_expr_list].
  - reflexivity.
  - f_equal; auto using rename_bound_expr_lift_weaken.
Qed.

Lemma weaken_ref_injective {F Δ t u}
    (left right : value_ref F Δ t) :
  Assertions.weaken_ref (u := u) left =
    Assertions.weaken_ref (u := u) right -> left = right.
Proof.
  destruct left; dependent destruction right; cbn;
    intro Hequal; try discriminate.
  all: inversion Hequal; try reflexivity.
  all: dependent destruction H0; reflexivity.
Qed.

Lemma weaken_expr_injective {F Δ t u}
    (left right : Core.expr F Δ t) :
  Assertions.weaken_expr (u := u) left =
    Assertions.weaken_expr (u := u) right -> left = right.
Proof.
  revert right.
  induction left; intros other Hequal; dependent destruction other;
    cbn [Assertions.weaken_expr] in Hequal; try discriminate.
  all: dependent destruction Hequal; try reflexivity;
    f_equal; eauto using weaken_ref_injective.
Qed.

Lemma weaken_expr_list_injective {F Δ ts u}
    (left right : Assertions.expr_list F Δ ts) :
  Assertions.weaken_expr_list (u := u) left =
    Assertions.weaken_expr_list (u := u) right -> left = right.
Proof.
  revert right.
  induction left; intros other Hequal; dependent destruction other;
    cbn [Assertions.weaken_expr_list] in Hequal; try discriminate.
  all: dependent destruction Hequal; try reflexivity;
    f_equal; eauto using weaken_expr_injective.
Qed.

Lemma stack_free_stack_arguments_agree {Γ F Δ ts}
    (arguments : pexpr_list Γ ts)
    (expected : Assertions.expr_list F Δ ts)
    (formula : Assertions.assertion Γ F Δ) :
  Assertions.stack_free formula ->
  stack_arguments_agree arguments expected formula.
Proof.
  intro Hfree. revert expected.
  induction Hfree; intros expected; cbn; try tauto; eauto.
Qed.

Lemma stack_free_stack_arguments_agree_under {Γ F Δ ts}
    (arguments : pexpr_list Γ ts) (formula : Assertions.assertion Γ F Δ) :
  Assertions.stack_free formula ->
  forall Δ' (substitution : Assertions.bound_subst F Δ Δ')
      (expected : Assertions.expr_list F Δ' ts),
    stack_arguments_agree_under substitution arguments expected formula.
Proof.
  intro Hfree. induction Hfree; intros Δ' substitution expected;
    cbn [stack_arguments_agree_under]; try tauto.
  - left. apply IHHfree.
  - apply IHHfree.
  - split; [apply IHHfree1 | apply IHHfree2].
  - split; [apply IHHfree1 | apply IHHfree2].
Qed.

Lemma stack_arguments_agree_rename {Γ F Δ Δ' ts}
    (renaming : Assertions.bound_renaming Δ Δ')
    (arguments : pexpr_list Γ ts) (expected : Assertions.expr_list F Δ ts)
    (formula : Assertions.assertion Γ F Δ) :
  stack_arguments_agree arguments expected formula ->
  stack_arguments_agree arguments
    (Assertions.rename_bound_expr_list renaming expected)
    (Assertions.rename_bound_assertion renaming formula).
Proof.
  revert Δ' renaming expected.
  induction formula; intros Δ' renaming expected Hagree;
    cbn [stack_arguments_agree Assertions.rename_bound_assertion]
      in Hagree |- *;
    try tauto.
  - rewrite symbolize_expr_list_rename_bound_store.
    exact (f_equal (Assertions.rename_bound_expr_list renaming) Hagree).
  - rewrite <- rename_bound_expr_list_lift_weaken.
    apply IHformula. exact Hagree.
  - rewrite <- rename_bound_expr_list_lift_weaken.
    apply IHformula. exact Hagree.
  - split; [apply IHformula1 | apply IHformula2]; tauto.
  - split; [apply IHformula1 | apply IHformula2]; tauto.
Qed.

Lemma rename_bound_expr_weaken {F Δ t u}
    (expression : Core.expr F Δ t) :
  Assertions.rename_bound_expr Assertions.weaken_bound_renaming expression =
  Assertions.weaken_expr (u := u) expression.
Proof.
  induction expression; cbn [Assertions.rename_bound_expr
    Assertions.rename_bound_ref Assertions.weaken_expr
    Assertions.weaken_ref Assertions.weaken_bound_renaming].
  - destruct reference; reflexivity.
  - reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma rename_bound_expr_exchange_double_weaken {F Δ t u result}
    (expression : Core.expr F Δ result) :
  Assertions.rename_bound_expr (@Assertions.exchange_bound_renaming Δ u t)
    (Assertions.weaken_expr (u := u)
      (Assertions.weaken_expr (u := t) expression)) =
  Assertions.weaken_expr (u := t)
    (Assertions.weaken_expr (u := u) expression).
Proof.
  induction expression; cbn [Assertions.rename_bound_expr
    Assertions.rename_bound_ref Assertions.weaken_expr
    Assertions.weaken_ref Assertions.weaken_bound_renaming].
  - destruct reference; cbn [Assertions.exchange_bound_renaming].
    + reflexivity.
    + unfold Assertions.weaken_ref, Assertions.rename_bound_ref,
        Assertions.weaken_bound_renaming.
      rewrite Assertions.exchange_bound_renaming_there_there. reflexivity.
    + reflexivity.
  - reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma rename_bound_expr_list_exchange_double_weaken {F Δ ts t u}
    (expressions : Assertions.expr_list F Δ ts) :
  Assertions.rename_bound_expr_list
    (@Assertions.exchange_bound_renaming Δ u t)
    (Assertions.weaken_expr_list (u := u)
      (Assertions.weaken_expr_list (u := t) expressions)) =
  Assertions.weaken_expr_list (u := t)
    (Assertions.weaken_expr_list (u := u) expressions).
Proof.
  induction expressions; cbn [Assertions.rename_bound_expr_list
    Assertions.weaken_expr_list].
  - reflexivity.
  - f_equal; [apply rename_bound_expr_exchange_double_weaken|exact IHexpressions].
Qed.

Lemma rename_bound_expr_list_weaken {F Δ ts u}
    (expressions : Assertions.expr_list F Δ ts) :
  Assertions.rename_bound_expr_list Assertions.weaken_bound_renaming
    expressions =
  Assertions.weaken_expr_list (u := u) expressions.
Proof.
  induction expressions; cbn [Assertions.rename_bound_expr_list
    Assertions.weaken_expr_list].
  - reflexivity.
  - f_equal.
    + apply rename_bound_expr_weaken.
    + exact IHexpressions.
Qed.

Lemma stack_arguments_agree_weaken {Γ F Δ ts u}
    (arguments : pexpr_list Γ ts) (expected : Assertions.expr_list F Δ ts)
    (formula : Assertions.assertion Γ F Δ) :
  stack_arguments_agree arguments expected formula ->
  stack_arguments_agree arguments
    (@Assertions.weaken_expr_list F Δ ts u expected)
    (@Assertions.weaken_assertion Γ F Δ u formula).
Proof.
  intro Hagree.
  unfold Assertions.weaken_assertion.
  rewrite <- rename_bound_expr_list_weaken.
  eapply stack_arguments_agree_rename; eauto.
Qed.

Definition bound_renaming_injective {Δ Δ'}
    (renaming : Assertions.bound_renaming Δ Δ') : Prop :=
  forall t (left right : bvar Δ t),
    renaming t left = renaming t right -> left = right.

Lemma weaken_bound_renaming_injective {Δ u} :
  bound_renaming_injective (@Assertions.weaken_bound_renaming Δ u).
Proof.
  intros t left right Hequal.
  unfold Assertions.weaken_bound_renaming in Hequal.
  dependent destruction Hequal. reflexivity.
Qed.

Lemma lift_bound_renaming_injective {Δ Δ' u}
    (renaming : Assertions.bound_renaming Δ Δ') :
  bound_renaming_injective renaming ->
  bound_renaming_injective (Assertions.lift_bound_renaming (u := u) renaming).
Proof.
  intro Hinjective. intros t left right Hequal.
  dependent destruction left; dependent destruction right;
    unfold Assertions.lift_bound_renaming in Hequal;
    rewrite ?view_member_here, ?view_member_there in Hequal;
    try discriminate; try reflexivity.
  injection Hequal as Hrenamed. f_equal.
  apply Hinjective. dependent destruction Hrenamed.
  match goal with H : renaming _ _ = renaming _ _ |- _ => exact H end.
Qed.

Lemma rename_bound_ref_injective {F Δ Δ' t}
    (renaming : Assertions.bound_renaming Δ Δ') :
  bound_renaming_injective renaming ->
  forall (left right : value_ref F Δ t),
    Assertions.rename_bound_ref renaming left =
      Assertions.rename_bound_ref renaming right -> left = right.
Proof.
  intro Hinjective. intros left right Hequal.
  destruct left; dependent destruction right; cbn
    [Assertions.rename_bound_ref] in Hequal; try discriminate.
  - dependent destruction Hequal. reflexivity.
  - injection Hequal as Hbound. f_equal.
    apply Hinjective. exact Hbound.
  - dependent destruction Hequal. reflexivity.
Qed.

Lemma rename_bound_expr_injective {F Δ Δ' t}
    (renaming : Assertions.bound_renaming Δ Δ') :
  bound_renaming_injective renaming ->
  forall (left right : Core.expr F Δ t),
    Assertions.rename_bound_expr renaming left =
      Assertions.rename_bound_expr renaming right ->
    left = right.
Proof.
  intro Hinjective. intros left.
  induction left; intros other Hequal; dependent destruction other;
    cbn [Assertions.rename_bound_expr] in Hequal; try discriminate.
  all: dependent destruction Hequal; try reflexivity;
    f_equal; eauto using rename_bound_ref_injective.
Qed.

Lemma rename_bound_expr_list_injective {F Δ Δ' ts}
    (renaming : Assertions.bound_renaming Δ Δ') :
  bound_renaming_injective renaming ->
  forall (left right : Assertions.expr_list F Δ ts),
    Assertions.rename_bound_expr_list renaming left =
      Assertions.rename_bound_expr_list renaming right ->
    left = right.
Proof.
  intro Hinjective. intros left.
  induction left; intros other Hequal; dependent destruction other;
    cbn [Assertions.rename_bound_expr_list] in Hequal; try discriminate.
  - reflexivity.
  - dependent destruction Hequal. f_equal.
    + eapply rename_bound_expr_injective; eauto.
    + eauto.
Qed.

Lemma stack_arguments_agree_rename_reflect {Γ F Δ Δ' ts}
    (renaming : Assertions.bound_renaming Δ Δ')
    (arguments : pexpr_list Γ ts) (expected : Assertions.expr_list F Δ ts)
    (formula : Assertions.assertion Γ F Δ) :
  bound_renaming_injective renaming ->
  stack_arguments_agree arguments
    (Assertions.rename_bound_expr_list renaming expected)
    (Assertions.rename_bound_assertion renaming formula) ->
  stack_arguments_agree arguments expected formula.
Proof.
  intros Hinjective. revert Δ' renaming expected Hinjective.
  induction formula; intros Δ' renaming expected Hinjective Hagree;
    cbn [stack_arguments_agree Assertions.rename_bound_assertion]
      in Hagree |- *; try tauto.
  - rewrite symbolize_expr_list_rename_bound_store in Hagree.
    eapply rename_bound_expr_list_injective; eauto.
  - rewrite <- rename_bound_expr_list_lift_weaken in Hagree.
    eapply IHformula; eauto using lift_bound_renaming_injective.
  - rewrite <- rename_bound_expr_list_lift_weaken in Hagree.
    eapply IHformula; eauto using lift_bound_renaming_injective.
  - split; [eapply IHformula1 | eapply IHformula2]; eauto; tauto.
  - split; [eapply IHformula1 | eapply IHformula2]; eauto; tauto.
Qed.

Lemma stack_arguments_agree_weaken_reflect {Γ F Δ ts u}
    (arguments : pexpr_list Γ ts) (expected : Assertions.expr_list F Δ ts)
    (formula : Assertions.assertion Γ F Δ) :
  stack_arguments_agree arguments
    (@Assertions.weaken_expr_list F Δ ts u expected)
    (@Assertions.weaken_assertion Γ F Δ u formula) ->
  stack_arguments_agree arguments expected formula.
Proof.
  unfold Assertions.weaken_assertion.
  rewrite <- rename_bound_expr_list_weaken.
  eapply stack_arguments_agree_rename_reflect.
  apply weaken_bound_renaming_injective.
Qed.

Lemma entailment_step_stack_arguments_agree {Γ F Δ ts}
    (arguments : pexpr_list Γ ts)
    (expected : Assertions.expr_list F Δ ts)
    (left right : Assertions.assertion Γ F Δ) :
  Assertions.entailment_step left right ->
  stack_arguments_agree arguments expected left ->
  stack_arguments_agree arguments expected right.
Proof.
  intro Hstep.
  induction Hstep; cbn; intro Hagree; try tauto.
  - split.
    + exact (proj1 Hagree).
    + apply stack_free_stack_arguments_agree. exact H.
  - split.
    + apply stack_free_stack_arguments_agree. exact H.
    + exact (proj1 Hagree).
Qed.

(** A successful binder substitution cannot have crossed a stack owner:
    substitutions deliberately reject [AStack].  This is the only special
    fact needed for existential-introduction entailments. *)
Lemma subst_bound_assertion_some_stack_free {Γ F Δ Δ'}
    (substitution : Assertions.bound_subst F Δ Δ')
    (formula : Assertions.assertion Γ F Δ)
    (target : Assertions.assertion Γ F Δ') :
  Assertions.subst_bound_assertion substitution formula = Some target ->
  Assertions.stack_free formula.
Proof.
  revert Δ' substitution target.
  induction formula; intros Δ' substitution target Hresult;
    cbn [Assertions.subst_bound_assertion] in Hresult.
  - discriminate.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct (Assertions.subst_bound_assertion
      (Assertions.lift_bound_subst substitution) formula) as [body'|]
      eqn:Hbody; [|discriminate].
    inversion Hresult; subst target. constructor.
    eapply IHformula; eauto.
  - destruct (Assertions.subst_bound_assertion
      (Assertions.lift_bound_subst substitution) formula) as [body'|]
      eqn:Hbody; [|discriminate].
    inversion Hresult; subst target. constructor.
    eapply IHformula; eauto.
  - destruct (Assertions.subst_bound_assertion substitution formula1)
      as [then_branch'|] eqn:Hthen; [|discriminate].
    destruct (Assertions.subst_bound_assertion substitution formula2)
      as [else_branch'|] eqn:Helse; [|discriminate].
    inversion Hresult; subst target. constructor.
    + eapply IHformula1; eauto.
    + eapply IHformula2; eauto.
  - constructor.
  - constructor.
  - destruct (Assertions.subst_bound_assertion substitution formula1)
      as [left'|] eqn:Hleft; [|discriminate].
    destruct (Assertions.subst_bound_assertion substitution formula2)
      as [right'|] eqn:Hright; [|discriminate].
    inversion Hresult; subst target. constructor.
    + eapply IHformula1; eauto.
    + eapply IHformula2; eauto.
Qed.

Lemma assertion_entails_stack_arguments_agree {Γ F Δ ts}
    (arguments : pexpr_list Γ ts) (expected : Assertions.expr_list F Δ ts)
    (left right : Assertions.assertion Γ F Δ) :
  Assertions.assertion_entails left right ->
  stack_arguments_agree arguments expected left ->
  stack_arguments_agree arguments expected right.
Proof.
  intro Hentails. induction Hentails; intro Hagree; cbn in Hagree |- *.
  - tauto.
  - eapply entailment_step_stack_arguments_agree; eauto.
  - apply IHHentails2. now apply IHHentails1.
  - split; [apply IHHentails1 | apply IHHentails2]; tauto.
  - apply IHHentails. exact Hagree.
  - apply stack_free_stack_arguments_agree.
    eapply subst_bound_assertion_some_stack_free; eauto.
  - apply (stack_arguments_agree_weaken_reflect (u := t)).
    apply IHHentails. exact Hagree.
  - split.
    + exact (proj1 Hagree).
    + apply stack_arguments_agree_weaken. exact (proj2 Hagree).
  - split.
    + exact (proj1 Hagree).
    + apply (stack_arguments_agree_weaken_reflect (u := t)).
      exact (proj2 Hagree).
  - split.
    + apply stack_arguments_agree_weaken. exact (proj1 Hagree).
    + exact (proj2 Hagree).
  - split; [apply IHHentails1 | apply IHHentails2]; tauto.
  - apply stack_arguments_agree_weaken. exact Hagree.
  - exact Hagree.
  - exact Hagree.
  - pose proof (stack_arguments_agree_rename
      (@Assertions.exchange_bound_renaming Δ u t) arguments
      (Assertions.weaken_expr_list (Assertions.weaken_expr_list expected))
      body Hagree) as Hrenamed.
    rewrite rename_bound_expr_list_exchange_double_weaken in Hrenamed.
    exact Hrenamed.
  - apply IHHentails. exact Hagree.
Qed.

Lemma restricted_argument_variable_indices_injective {Γ ts}
    (left right : pexpr_list Γ ts) indices :
  restricted_argument_variable_indices left = Some indices ->
  restricted_argument_variable_indices right = Some indices ->
  left = right.
Proof.
  revert right indices.
  induction left; intros right indices Hleft Hright;
    dependent destruction right.
  - cbn in Hleft, Hright. congruence.
  - cbn in Hleft, Hright.
    destruct p; try discriminate.
    destruct p0; try discriminate.
    destruct (restricted_argument_variable_indices left) as [left_indices|]
      eqn:Hleft_indices; try discriminate.
    destruct (restricted_argument_variable_indices right) as [right_indices|]
      eqn:Hright_indices; try discriminate.
    inversion Hleft; inversion Hright; subst.
    f_equal.
    + f_equal. apply member_index_injective. congruence.
    + eapply IHleft; [reflexivity|].
      rewrite Hright_indices. f_equal. congruence.
Qed.

Lemma restricted_pexpr_list_eqb_sound {Γ ts}
    (left right : pexpr_list Γ ts) :
  restricted_pexpr_list_eqb left right = true -> left = right.
Proof.
  unfold restricted_pexpr_list_eqb.
  destruct (restricted_argument_variable_indices left) as [left_indices|]
    eqn:Hleft; try discriminate.
  destruct (restricted_argument_variable_indices right) as [right_indices|]
    eqn:Hright; try discriminate.
  intro Hequal. apply bool_decide_eq_true in Hequal. subst right_indices.
  eapply restricted_argument_variable_indices_injective; eauto.
Qed.

Definition restricted_access_boundary_check {Γ invariant}
    (opening_arguments closing_arguments :
      pexpr_list Γ (Logic.invariant_args invariant))
    (body : stmt Γ) : bool :=
  restricted_pexpr_list_eqb opening_arguments closing_arguments &&
    bool_decide (pexpr_list_dependencies opening_arguments ##
      statement_writes body).

Lemma restricted_access_boundary_check_sound {Γ invariant}
    (opening_arguments closing_arguments :
      pexpr_list Γ (Logic.invariant_args invariant)) body :
  restricted_access_boundary_check opening_arguments closing_arguments body =
    true ->
  opening_arguments = closing_arguments /\
  pexpr_list_dependencies opening_arguments ## statement_writes body.
Proof.
  unfold restricted_access_boundary_check.
  rewrite Bool.andb_true_iff. intros [Harguments Hwrites].
  split.
  - now apply restricted_pexpr_list_eqb_sound.
  - now apply bool_decide_eq_true in Hwrites.
Qed.

(** Effect-only component of the restricted pass.  Structural admissibility
    remains the independent executable decision above. *)
Fixpoint restricted_access_effect_check {Γ} (statement : stmt Γ) : bool :=
  match statement with
  | TInvAccess _ _ body | TAtomic _ body => restricted_access_effect_check body
  | TIf _ _ then_branch else_branch =>
      restricted_access_effect_check then_branch &&
        restricted_access_effect_check else_branch
  | TSeq _ first second =>
      match first, second with
      | TUnfold _ opening_invariant opening_arguments,
          TSeq _ body (TFold _ closing_invariant closing_arguments) =>
          match decide (opening_invariant = closing_invariant) with
          | left Heq =>
              restricted_access_boundary_check opening_arguments
                (eq_rect _ (fun invariant =>
                  pexpr_list Γ (Logic.invariant_args invariant))
                  closing_arguments _ (eq_sym Heq)) body
          | right _ => false
          end
      | TUnfold _ opening_invariant opening_arguments,
          TSeq _ body
            (TSeq _ (TFold _ closing_invariant closing_arguments) work) =>
          match decide (opening_invariant = closing_invariant) with
          | left Heq =>
              restricted_access_boundary_check opening_arguments
                (eq_rect _ (fun invariant =>
                  pexpr_list Γ (Logic.invariant_args invariant))
                  closing_arguments _ (eq_sym Heq)) body &&
                restricted_access_effect_check work
          | right _ => false
          end
      | _, _ =>
          restricted_access_effect_check first &&
            restricted_access_effect_check second
      end
  | _ => true
  end.

Definition restricted_fragment_check {Γ} (statement : stmt Γ) : bool :=
  restricted_fragment_shape_check statement &&
    restricted_access_effect_check statement.

Definition restricted_fragment_accepted {Γ} (statement : stmt Γ) : Prop :=
  restricted_fragment_check statement = true.

Fixpoint normalization_statement_size {Γ} (statement : stmt Γ) : nat :=
  match statement with
  | TInvAccess _ _ body | TAtomic _ body =>
      S (normalization_statement_size body)
  | TIf _ _ then_branch else_branch | TSeq _ then_branch else_branch =>
      S (normalization_statement_size then_branch +
        normalization_statement_size else_branch)
  | _ => 1
  end.

(** Proof-irrelevant source-to-source worker.  Its private budget is only a
    termination device for the nested [AccessThen] continuation and never
    appears in an analysis certificate or theorem interface. *)
Fixpoint restricted_normalize_statement_fuel {Γ} (fuel : nat)
    (statement : stmt Γ) : option (stmt Γ) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match statement with
      | TUnfold _ _ _ => None
      | TInvAccess invariant arguments body =>
          match restricted_normalize_statement_fuel fuel' body with
          | Some normalized_body =>
              Some (TInvAccess invariant arguments normalized_body)
          | None => None
          end
      | TAtomic node body =>
          match restricted_normalize_statement_fuel fuel' body with
          | Some normalized_body => Some (TAtomic node normalized_body)
          | None => None
          end
      | TIf node condition then_branch else_branch =>
          match restricted_normalize_statement_fuel fuel' then_branch,
              restricted_normalize_statement_fuel fuel' else_branch with
          | Some normalized_then, Some normalized_else =>
              Some (TIf node condition normalized_then normalized_else)
          | _, _ => None
          end
      | TSeq outer_node first second =>
          match first, second with
          | TUnfold _ opening_invariant opening_arguments,
              TSeq _ body (TFold _ closing_invariant closing_arguments) =>
              match decide (opening_invariant = closing_invariant) with
              | left Heq =>
                  if restricted_access_boundary_check opening_arguments
                    (eq_rect _ (fun invariant =>
                      pexpr_list Γ (Logic.invariant_args invariant))
                      closing_arguments _ (eq_sym Heq)) body
                  then Some (TInvAccess opening_invariant opening_arguments body)
                  else None
              | right _ => None
              end
          | TUnfold _ opening_invariant opening_arguments,
              TSeq _ body
                (TSeq _ (TFold _ closing_invariant closing_arguments) work) =>
              match decide (opening_invariant = closing_invariant) with
              | left Heq =>
                  if restricted_access_boundary_check opening_arguments
                    (eq_rect _ (fun invariant =>
                      pexpr_list Γ (Logic.invariant_args invariant))
                      closing_arguments _ (eq_sym Heq)) body
                  then
                    match restricted_normalize_statement_fuel fuel' work with
                    | Some normalized_work =>
                        Some (TSeq outer_node
                          (TInvAccess opening_invariant opening_arguments body)
                          normalized_work)
                    | None => None
                    end
                  else None
              | right _ => None
              end
          | _, _ =>
              match restricted_normalize_statement_fuel fuel' first,
                  restricted_normalize_statement_fuel fuel' second with
              | Some normalized_first, Some normalized_second =>
                  Some (TSeq outer_node normalized_first normalized_second)
              | _, _ => None
              end
          end
      | _ => Some statement
      end
  end.

Definition restricted_analyze_and_normalize {Γ}
    (statement : stmt Γ) : option (stmt Γ) :=
  if restricted_fragment_check statement
  then restricted_normalize_statement_fuel
    (S (normalization_statement_size statement)) statement
  else None.

Lemma unfold_freeb_spec {Γ} (statement : stmt Γ) :
  unfold_freeb statement = true <-> unfold_free statement.
Proof.
  induction statement; cbn;
    rewrite ?Bool.andb_true_iff, ?IHstatement, ?IHstatement1, ?IHstatement2;
    intuition congruence.
Qed.

Lemma access_neutralb_spec {Γ} (statement : stmt Γ) :
  access_neutralb statement = true <-> access_neutral statement.
Proof.
  induction statement; cbn;
    rewrite ?Bool.andb_true_iff, ?IHstatement, ?IHstatement1, ?IHstatement2;
    intuition congruence.
Qed.

Lemma restricted_fragment_check_refines_shape {Γ} (statement : stmt Γ) :
  restricted_fragment_accepted statement -> restricted_fragment_shape statement.
Proof.
  unfold restricted_fragment_accepted, restricted_fragment_check,
    restricted_fragment_shape.
  rewrite Bool.andb_true_iff. tauto.
Qed.

(** The executable shape check is sound for the existing proof-producing
    baseline grammar.  Thus later strengthening it with effects can only
    reject programs; it cannot admit a source layout unsupported by the
    normalization theorem. *)
Lemma restricted_fragment_shape_check_sound {Γ} (statement : stmt Γ) :
  restricted_fragment_shape statement ->
  restricted_access_effect_check statement = true ->
  baseline_normalizable statement.
Proof.
  refine (well_founded_induction_type
    (well_founded_ltof _ (@normalization_statement_size Γ))
    (fun current => restricted_fragment_shape current ->
      restricted_access_effect_check current = true ->
      baseline_normalizable current) _ statement).
  intros current IH Hcheck Heffects.
  destruct current; cbn [restricted_fragment_shape
    restricted_fragment_shape_check] in Hcheck |- *;
    try (apply BaselineUnfoldFree; cbn; done).
  - apply BaselineUnfoldFree. cbn.
    apply unfold_freeb_spec. exact Hcheck.
  - apply Bool.andb_true_iff in Hcheck as [Hthen Helse].
    apply Bool.andb_true_iff in Heffects as [Hthen_effects Helse_effects].
    apply BaselineConditional.
    + apply IH; [unfold ltof; cbn; lia | exact Hthen | exact Hthen_effects].
    + apply IH; [unfold ltof; cbn; lia | exact Helse | exact Helse_effects].
  - destruct current1; unfold restricted_fragment_shape in Hcheck;
      cbn in Hcheck, Heffects.
    all: try (apply Bool.andb_true_iff in Heffects as
      [Hfirst_effects Hsecond_effects]).
    all: try (apply BaselineSequence;
      [cbn; tauto | apply IH;
        [unfold ltof; cbn; lia | exact Hcheck |
         first [exact Hsecond_effects | exact Heffects]]]).
    2: apply BaselineBalancedSequence;
      [apply BaselineUnfoldFree; cbn; exact I |
       apply IH; [unfold ltof; cbn; lia | exact Hcheck |
         first [exact Hsecond_effects | exact Heffects]]].
    all: try (apply Bool.andb_true_iff in Hcheck as [Hfirst Hsecond]).
    2: apply BaselineBalancedSequence.
    2: apply BaselineUnfoldFree; cbn; apply unfold_freeb_spec; exact Hfirst.
    2: apply IH; [unfold ltof; cbn; lia | exact Hsecond |
      first [exact Hsecond_effects | exact Heffects]].
    2: apply Bool.andb_true_iff in Hfirst as [Hthen Helse].
    2: apply Bool.andb_true_iff in Hfirst_effects as
      [Hthen_effects Helse_effects].
    2: apply BaselineBalancedSequence.
    2: apply BaselineConditional.
    2: apply IH; [unfold ltof; cbn; lia | exact Hthen | exact Hthen_effects].
    2: apply IH; [unfold ltof; cbn; lia | exact Helse | exact Helse_effects].
    2: apply IH; [unfold ltof; cbn; lia | exact Hsecond |
      first [exact Hsecond_effects | exact Heffects]].
    2: apply BaselineBalancedSequence.
    2: apply IH; [unfold ltof; cbn; lia | exact Hfirst | exact Hfirst_effects].
    2: apply IH; [unfold ltof; cbn; lia | exact Hsecond |
      first [exact Hsecond_effects | exact Heffects]].
    2: apply BaselineBalancedSequence.
    2: apply BaselineUnfoldFree; cbn; apply unfold_freeb_spec; exact Hfirst.
    2: apply IH; [unfold ltof; cbn; lia | exact Hsecond |
      first [exact Hsecond_effects | exact Heffects]].
    destruct current2; cbn in Hcheck; try discriminate.
    destruct current2_2; cbn in Hcheck; try discriminate.
    1: apply Bool.andb_true_iff in Hcheck as [Hinvariant Hbody];
      apply bool_decide_eq_true in Hinvariant. subst invariant0.
      apply access_neutralb_spec in Hbody.
      destruct (decide (invariant = invariant) : Decision (invariant = invariant))
        as [Heq|Hneq]; last contradiction.
      replace Heq with (@eq_refl inv_id invariant) in Heffects
        by apply proof_irrelevance.
      cbn in Heffects.
      apply restricted_access_boundary_check_sound in Heffects as
        [Harguments Hdisjoint].
      apply BaselineTerminalAccess; assumption.
    destruct current2_2_1; cbn in Hcheck; try discriminate.
    apply Bool.andb_true_iff in Hcheck as [Hprefix Hwork].
    apply Bool.andb_true_iff in Hprefix as [Hinvariant Hbody].
    apply bool_decide_eq_true in Hinvariant. subst invariant0.
    apply access_neutralb_spec in Hbody.
    destruct (decide (invariant = invariant) : Decision (invariant = invariant))
      as [Heq|Hneq]; last contradiction.
    replace Heq with (@eq_refl inv_id invariant) in Heffects
      by apply proof_irrelevance.
    cbn in Heffects.
    apply Bool.andb_true_iff in Heffects as [Hboundary Hwork_effects].
    apply restricted_access_boundary_check_sound in Hboundary as
      [Harguments Hdisjoint].
    apply BaselineAccessThen; [exact Hbody | exact Harguments | exact Hdisjoint |].
    apply IH; [unfold ltof; cbn; lia | exact Hwork | exact Hwork_effects].
  - apply BaselineUnfoldFree. cbn.
    apply unfold_freeb_spec. exact Hcheck.
Qed.

Corollary restricted_fragment_check_sound {Γ} (statement : stmt Γ) :
  restricted_fragment_accepted statement -> baseline_normalizable statement.
Proof.
  intro Haccepted.
  unfold restricted_fragment_accepted, restricted_fragment_check in Haccepted.
  apply Bool.andb_true_iff in Haccepted as [Hshape Heffects].
  eapply restricted_fragment_shape_check_sound; eauto.
Qed.

Lemma restricted_access_neutral_unfold_free {Γ} (statement : stmt Γ) :
  access_neutral statement -> unfold_free statement.
Proof.
  induction statement; cbn; intuition.
Qed.

Lemma unfold_free_normalize_statement_succeeds_with_fuel {Γ}
    (statement : stmt Γ) fuel :
  unfold_free statement ->
  normalization_statement_size statement < fuel ->
  exists normalized,
    restricted_normalize_statement_fuel fuel statement = Some normalized.
Proof.
  revert fuel.
  induction statement; intros fuel Hfree Hfuel.
  all: destruct fuel as [|fuel].
  all: try (cbn in Hfuel; lia).
  all: cbn [unfold_free normalization_statement_size
    restricted_normalize_statement_fuel] in Hfree, Hfuel |- *.
  all: try contradiction.
  all: try (eexists; reflexivity).
  - destruct (IHstatement fuel Hfree ltac:(lia)) as
      [normalized Hnormalized].
    rewrite Hnormalized. eexists; reflexivity.
  - destruct Hfree as [Hfree1 Hfree2].
    destruct (IHstatement1 fuel Hfree1 ltac:(lia)) as
      [normalized1 Hnormalized1].
    destruct (IHstatement2 fuel Hfree2 ltac:(lia)) as
      [normalized2 Hnormalized2].
    rewrite Hnormalized1, Hnormalized2. eexists; reflexivity.
  - destruct Hfree as [Hfree1 Hfree2].
    destruct (IHstatement1 fuel Hfree1 ltac:(lia)) as
      [normalized1 Hnormalized1].
    destruct (IHstatement2 fuel Hfree2 ltac:(lia)) as
      [normalized2 Hnormalized2].
    destruct statement1; cbn [unfold_free] in Hfree1;
      try contradiction;
      cbn [restricted_normalize_statement_fuel] in Hnormalized1 |- *;
      rewrite Hnormalized1, Hnormalized2;
      eexists; reflexivity.
  - destruct (IHstatement fuel Hfree ltac:(lia)) as
      [normalized Hnormalized].
    rewrite Hnormalized. eexists; reflexivity.
Qed.

Corollary unfold_free_normalize_statement_succeeds {Γ}
    (statement : stmt Γ) :
  unfold_free statement ->
  exists normalized,
    restricted_normalize_statement_fuel
      (S (normalization_statement_size statement)) statement =
      Some normalized.
Proof.
  intro Hfree.
  eapply unfold_free_normalize_statement_succeeds_with_fuel; [exact Hfree|lia].
Qed.

Lemma unfold_free_normalize_statement_identity {Γ} (statement : stmt Γ)
    fuel normalized :
  unfold_free statement ->
  restricted_normalize_statement_fuel fuel statement = Some normalized ->
  normalized = statement.
Proof.
  revert fuel normalized.
  induction statement; intros fuel normalized Hfree Hworker;
    destruct fuel; cbn [unfold_free restricted_normalize_statement_fuel]
      in Hfree, Hworker; try contradiction; try congruence.
  - destruct (restricted_normalize_statement_fuel fuel statement) eqn:Hbody;
      try discriminate.
    inversion Hworker; subst. f_equal. eapply IHstatement; eauto.
  - destruct Hfree as [Hthen Helse].
    destruct (restricted_normalize_statement_fuel fuel statement1)
      eqn:Hworker1; try discriminate.
    destruct (restricted_normalize_statement_fuel fuel statement2)
      eqn:Hworker2; try discriminate.
    inversion Hworker; subst. f_equal; eauto.
  - destruct Hfree as [Hfirst Hsecond].
    remember (restricted_normalize_statement_fuel fuel statement1)
      as first_result eqn:Hfirst_result.
    remember (restricted_normalize_statement_fuel fuel statement2)
      as second_result eqn:Hsecond_result.
    destruct statement1; cbn [unfold_free] in Hfirst; try contradiction;
      cbn [restricted_normalize_statement_fuel] in Hworker.
    all: destruct first_result; try discriminate;
      destruct second_result; try discriminate;
      inversion Hworker; subst; f_equal;
      eauto using eq_sym.
  - destruct (restricted_normalize_statement_fuel fuel statement) eqn:Hbody;
      try discriminate.
    inversion Hworker; subst. f_equal. eapply IHstatement; eauto.
Qed.

Lemma restricted_normalize_terminal_access {Γ} fuel outer_node unfold_node
    body_sequence_node fold_node invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (body : stmt Γ) :
  restricted_access_boundary_check arguments arguments body = true ->
  restricted_normalize_statement_fuel (S fuel)
    (TSeq outer_node (TUnfold unfold_node invariant arguments)
      (TSeq body_sequence_node body (TFold fold_node invariant arguments))) =
    Some (TInvAccess invariant arguments body).
Proof.
  intro Hboundary. cbn [restricted_normalize_statement_fuel].
  destruct (decide (invariant = invariant)) as [Heq | Hneq];
    [| contradiction].
  replace Heq with (@eq_refl inv_id invariant) by apply proof_irrelevance.
  cbn. now rewrite Hboundary.
Qed.

Lemma restricted_normalize_continued_access {Γ} fuel outer_node unfold_node
    body_sequence_node fold_sequence_node fold_node invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (body work normalized_work : stmt Γ) :
  restricted_access_boundary_check arguments arguments body = true ->
  restricted_normalize_statement_fuel fuel work = Some normalized_work ->
  restricted_normalize_statement_fuel (S fuel)
    (TSeq outer_node (TUnfold unfold_node invariant arguments)
      (TSeq body_sequence_node body
        (TSeq fold_sequence_node (TFold fold_node invariant arguments)
          work))) =
    Some (TSeq outer_node (TInvAccess invariant arguments body)
      normalized_work).
Proof.
  intros Hboundary Hwork. cbn [restricted_normalize_statement_fuel].
  destruct (decide (invariant = invariant)) as [Heq | Hneq];
    [| contradiction].
  replace Heq with (@eq_refl inv_id invariant) by apply proof_irrelevance.
  cbn. now rewrite Hboundary, Hwork.
Qed.

Lemma restricted_terminal_access_accepted_inv {Γ} outer_node unfold_node
    body_sequence_node fold_node invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (body : stmt Γ) :
  restricted_fragment_accepted
    (TSeq outer_node (TUnfold unfold_node invariant arguments)
      (TSeq body_sequence_node body (TFold fold_node invariant arguments))) ->
  access_neutral body /\
    restricted_access_boundary_check arguments arguments body = true.
Proof.
  unfold restricted_fragment_accepted, restricted_fragment_check.
  cbn [restricted_fragment_shape_check restricted_access_effect_check].
  destruct (decide (invariant = invariant)) as [Heq | Hneq];
    [| contradiction].
  replace Heq with (@eq_refl inv_id invariant) by apply proof_irrelevance.
  rewrite bool_decide_true; [| reflexivity].
  cbn. rewrite !Bool.andb_true_iff.
  intros [Hneutral Hboundary]. split.
  - now apply access_neutralb_spec.
  - exact Hboundary.
Qed.

Lemma restricted_continued_access_accepted_inv {Γ} outer_node unfold_node
    body_sequence_node fold_sequence_node fold_node invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (body work : stmt Γ) :
  restricted_fragment_accepted
    (TSeq outer_node (TUnfold unfold_node invariant arguments)
      (TSeq body_sequence_node body
        (TSeq fold_sequence_node (TFold fold_node invariant arguments)
          work))) ->
  access_neutral body /\
    restricted_access_boundary_check arguments arguments body = true /\
    restricted_fragment_accepted work.
Proof.
  unfold restricted_fragment_accepted, restricted_fragment_check.
  cbn [restricted_fragment_shape_check restricted_access_effect_check].
  destruct (decide (invariant = invariant)) as [Heq | Hneq];
    [| contradiction].
  replace Heq with (@eq_refl inv_id invariant) by apply proof_irrelevance.
  cbn. rewrite !Bool.andb_true_iff.
  intros [[[_ Hneutral] Hwork_shape] [Hboundary Hwork_effect]].
  split; [now apply access_neutralb_spec|].
  split; [exact Hboundary|].
  split; assumption.
Qed.

Lemma access_neutral_effect_check {Γ} (statement : stmt Γ) :
  access_neutral statement ->
  restricted_access_effect_check statement = true.
Proof.
  induction statement; cbn [access_neutral restricted_access_effect_check];
    intros Hneutral; try contradiction; try reflexivity.
  - now rewrite IHstatement.
  - destruct Hneutral as [Hthen Helse].
    now rewrite IHstatement1, IHstatement2.
  - destruct Hneutral as [Hfirst Hsecond].
    pose proof (IHstatement1 Hfirst) as Hcheck1.
    pose proof (IHstatement2 Hsecond) as Hcheck2.
    destruct statement1; cbn [access_neutral] in Hfirst.
    all: try contradiction.
    all: try (cbn [restricted_access_effect_check] in Hcheck1 |- *;
      rewrite Hcheck1, Hcheck2; reflexivity).
    all: rewrite Hcheck2; exact Hcheck1.
  - now rewrite IHstatement.
Qed.

Lemma access_neutral_sequence_effect_check {Γ} node
    (first second : stmt Γ) :
  access_neutral first ->
  restricted_access_effect_check (TSeq node first second) =
    (restricted_access_effect_check first &&
      restricted_access_effect_check second).
Proof.
  intro Hneutral.
  destruct first; cbn [access_neutral] in Hneutral;
    try contradiction;
    reflexivity.
Qed.

(** Successful admission is sufficient for the proof-irrelevant normalizer
    to produce a target at its private size bound.  This is the first local
    correctness fact for the combined pass: later certificate construction
    may consume the returned statement without evaluating Hoare or alignment
    evidence. *)
Lemma restricted_normalize_statement_succeeds_with_fuel {Γ}
    (statement : stmt Γ) fuel :
  restricted_fragment_accepted statement ->
  normalization_statement_size statement < fuel ->
  exists normalized,
    restricted_normalize_statement_fuel fuel statement = Some normalized.
Proof.
  revert fuel.
  refine (well_founded_induction_type
    (well_founded_ltof _ (@normalization_statement_size Γ))
    (fun current => forall fuel,
      restricted_fragment_accepted current ->
      normalization_statement_size current < fuel ->
      exists normalized,
        restricted_normalize_statement_fuel fuel current = Some normalized)
    _ statement).
  intros current IH fuel Haccepted Hfuel.
  destruct fuel as [|fuel]; [cbn in Hfuel; lia|].
  unfold restricted_fragment_accepted, restricted_fragment_check in Haccepted.
  apply Bool.andb_true_iff in Haccepted as [Hshape Heffect].
  destruct current.
  all: cbn [restricted_fragment_shape_check
    restricted_access_effect_check normalization_statement_size]
    in Hshape, Heffect, Hfuel.
  all: try discriminate.
  all: try (eexists; reflexivity).
  - apply unfold_freeb_spec in Hshape.
    destruct (unfold_free_normalize_statement_succeeds_with_fuel current fuel
      Hshape ltac:(lia)) as [normalized Hnormalized].
    change (exists normalized0,
      match restricted_normalize_statement_fuel fuel current with
      | Some normalized_body =>
          Some (TInvAccess invariant arguments normalized_body)
      | None => None
      end = Some normalized0).
    rewrite Hnormalized. eexists; reflexivity.
  - apply Bool.andb_true_iff in Hshape as [Hshape1 Hshape2].
    apply Bool.andb_true_iff in Heffect as [Heffect1 Heffect2].
    destruct (IH current1 ltac:(unfold ltof; cbn; lia) fuel
      ltac:(unfold restricted_fragment_accepted, restricted_fragment_check;
        apply Bool.andb_true_iff; auto) ltac:(lia)) as
      [normalized1 Hnormalized1].
    destruct (IH current2 ltac:(unfold ltof; cbn; lia) fuel
      ltac:(unfold restricted_fragment_accepted, restricted_fragment_check;
        apply Bool.andb_true_iff; auto) ltac:(lia)) as
      [normalized2 Hnormalized2].
    change (exists normalized,
      match restricted_normalize_statement_fuel fuel current1 with
      | Some normalized_then =>
          match restricted_normalize_statement_fuel fuel current2 with
          | Some normalized_else =>
              Some (TIf node condition normalized_then normalized_else)
          | None => None
          end
      | None => None
      end = Some normalized).
    rewrite Hnormalized1, Hnormalized2. eexists; reflexivity.
  - destruct current1.
    all: try (apply Bool.andb_true_iff in Hshape as [Hshape1 Hshape2];
      apply Bool.andb_true_iff in Heffect as [Heffect1 Heffect2];
      match goal with
      | |- context [TSeq ?seq_node ?first ?second] =>
          destruct (IH first ltac:(unfold ltof; cbn; lia) fuel
            ltac:(unfold restricted_fragment_accepted,
              restricted_fragment_check;
              apply Bool.andb_true_iff; auto) ltac:(lia)) as
            [normalized1 Hnormalized1];
          destruct (IH second ltac:(unfold ltof; cbn; lia) fuel
            ltac:(unfold restricted_fragment_accepted,
              restricted_fragment_check;
              apply Bool.andb_true_iff; auto) ltac:(lia)) as
            [normalized2 Hnormalized2];
          cbn [restricted_normalize_statement_fuel];
          rewrite Hnormalized1, Hnormalized2;
          eexists; reflexivity
      end).
    destruct current2; cbn [restricted_fragment_shape_check
      restricted_access_effect_check] in Hshape, Heffect |- *;
      try discriminate.
    destruct current2_2; cbn [restricted_fragment_shape_check
      restricted_access_effect_check] in Hshape, Heffect |- *;
      try discriminate.
    + apply Bool.andb_true_iff in Hshape as [Hinvariant _].
      apply bool_decide_eq_true in Hinvariant. subst invariant0.
      destruct (decide (invariant = invariant)) as [Heq | Hneq];
        [|contradiction].
      replace Heq with (@eq_refl inv_id invariant) in Heffect |- *
        by apply proof_irrelevance.
      cbn in Heffect |- *.
      destruct (decide (invariant = invariant)) as [Heq0 | Hneq];
        [|contradiction].
      replace Heq0 with Heq by apply proof_irrelevance.
      rewrite Heffect. eexists; reflexivity.
    + destruct current2_2_1; cbn [restricted_fragment_shape_check
        restricted_access_effect_check] in Hshape, Heffect |- *;
        try discriminate.
      apply Bool.andb_true_iff in Hshape as [Hprefix Hwork_shape].
      apply Bool.andb_true_iff in Hprefix as [Hinvariant _].
      apply bool_decide_eq_true in Hinvariant. subst invariant0.
      destruct (decide (invariant = invariant)) as [Heq | Hneq];
        [|contradiction].
      replace Heq with (@eq_refl inv_id invariant) in Heffect
        by apply proof_irrelevance.
      cbn in Heffect.
      apply Bool.andb_true_iff in Heffect as [Hboundary Hwork_effect].
      assert (Hwork_accepted :
        restricted_fragment_accepted current2_2_2).
      { unfold restricted_fragment_accepted, restricted_fragment_check.
        apply Bool.andb_true_iff. split; assumption. }
      assert (Hwork_smaller : ltof (stmt Γ) normalization_statement_size
        current2_2_2
        (TSeq node (TUnfold node0 invariant arguments)
          (TSeq node1 current2_1
            (TSeq node2 (TFold node3 invariant arguments0)
              current2_2_2)))).
      { unfold ltof. cbn. lia. }
      assert (Hwork_fuel :
        normalization_statement_size current2_2_2 < fuel).
      { cbn in Hfuel. lia. }
      destruct (IH current2_2_2 Hwork_smaller fuel Hwork_accepted Hwork_fuel)
        as [normalized_work Hwork].
      cbn [restricted_normalize_statement_fuel].
      destruct (decide (invariant = invariant)) as [Heq0 | Hneq];
        [|contradiction].
      replace Heq0 with Heq by apply proof_irrelevance.
      replace Heq with (@eq_refl inv_id invariant) by apply proof_irrelevance.
      cbn. rewrite Hboundary, Hwork. eexists; reflexivity.
  - apply unfold_freeb_spec in Hshape.
    destruct (unfold_free_normalize_statement_succeeds_with_fuel current fuel
      Hshape ltac:(lia)) as [normalized Hnormalized].
    change (exists normalized0,
      match restricted_normalize_statement_fuel fuel current with
      | Some normalized_body => Some (TAtomic node normalized_body)
      | None => None
      end = Some normalized0).
    rewrite Hnormalized. eexists; reflexivity.
Qed.

Corollary restricted_normalize_statement_succeeds {Γ} (statement : stmt Γ) :
  restricted_fragment_accepted statement ->
  exists normalized,
    restricted_normalize_statement_fuel
      (S (normalization_statement_size statement)) statement =
      Some normalized.
Proof.
  intro Haccepted.
  eapply restricted_normalize_statement_succeeds_with_fuel;
    [exact Haccepted|lia].
Qed.

Corollary restricted_analyze_and_normalize_succeeds {Γ}
    (statement : stmt Γ) :
  restricted_fragment_accepted statement ->
  exists normalized,
    restricted_analyze_and_normalize statement = Some normalized.
Proof.
  intro Haccepted.
  unfold restricted_analyze_and_normalize.
  rewrite Haccepted.
  now apply restricted_normalize_statement_succeeds.
Qed.

Lemma access_neutral_unfold_free {Γ} (statement : stmt Γ) :
  access_neutral statement -> unfold_free statement.
Proof.
  induction statement; simpl; intuition.
Qed.

(** Access-neutral statements cannot change the auxiliary LIFO stack.  This
    is particularly useful for trusted atomic bodies: their analyzer
    certificates may remain opaque while their lack of invariant operations
    determines the stack behavior completely. *)
Lemma access_neutral_lifo {cost Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ entry statement exit) stack :
  access_neutral statement ->
  GenericRegions.Atomicity.lifo_certificate certificate stack stack.
Proof.
  revert stack.
  induction certificate; intros stack Hneutral; simpl in *.
  - reflexivity.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hneutral. contradiction.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hneutral. contradiction.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    destruct Hneutral as [Hfirst Hsecond].
    exists stack. split; [apply IHcertificate1 | apply IHcertificate2];
      assumption.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    destruct Hneutral as [Hthen Helse]. split.
    + apply IHcertificate1. exact Hthen.
    + apply IHcertificate2. exact Helse.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    split; [apply IHcertificate | reflexivity]. exact Hneutral.
Qed.

Lemma access_neutral_preserves_open {cost Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ entry statement exit) :
  access_neutral statement ->
  GenericRegions.Atomicity.analysis_open exit =
    GenericRegions.Atomicity.analysis_open entry.
Proof.
  induction certificate; intros Hneutral.
  - eapply GenericRegions.Atomicity.take_step_preserves_open; eauto.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hneutral. contradiction.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hneutral. contradiction.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hneutral. destruct Hneutral as [Hfirst Hsecond].
    rewrite (IHcertificate2 Hsecond), (IHcertificate1 Hfirst). reflexivity.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hneutral. destruct Hneutral as [Hthen _].
    exact (IHcertificate1 Hthen).
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    eapply eq_trans; [exact e1|].
    eapply GenericRegions.Atomicity.take_step_preserves_open; eauto.
Qed.

(** An unfold-free analyzed region entered with no open invariant is LIFO
    balanced.  Raw folds are deliberately allowed here: at a closed entry
    they are invariant allocation, hence leave both the analyzer open set
    and the auxiliary access stack unchanged. *)
Lemma unfold_free_closed_lifo {cost Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ entry statement exit) :
  unfold_free statement ->
  GenericRegions.Atomicity.analysis_open entry = ∅ ->
  GenericRegions.Atomicity.lifo_certificate certificate [] [] /\
    GenericRegions.Atomicity.analysis_open exit = ∅.
Proof.
  induction certificate; intros Hfree Hclosed; simpl in *.
  - split; [reflexivity|].
    rewrite <- Hclosed.
    eapply GenericRegions.Atomicity.take_step_preserves_open; eauto.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hfree. contradiction.
  - split.
    + right. split; [reflexivity|]. rewrite Hclosed. apply not_elem_of_empty.
    + destruct (GenericRegions.Atomicity.fold_fresh_invariant invariant state)
        as [_ Hopen].
      * rewrite Hclosed. apply not_elem_of_empty.
      * now rewrite Hopen, Hclosed.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    destruct Hfree as [Hfirst Hsecond].
    destruct (IHcertificate1 Hfirst Hclosed) as [Hlifo1 Hmiddle].
    destruct (IHcertificate2 Hsecond Hmiddle) as [Hlifo2 Hexit].
    split; [eexists; split; eassumption|exact Hexit].
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    destruct Hfree as [Hthen Helse].
    destruct (IHcertificate1 Hthen Hclosed) as [Hlifo1 Hthen_closed].
    destruct (IHcertificate2 Helse Hclosed) as [Hlifo2 Helse_closed].
    split; [split; assumption|exact Hthen_closed].
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    pose proof (GenericRegions.Atomicity.take_step_preserves_open _ _ _ e0)
      as Houter.
    rewrite Hclosed in Houter.
    destruct (IHcertificate Hfree Houter) as [Hlifo Hinner].
    split; [split; [exact Hlifo|reflexivity]|exact Hinner].
Qed.

Lemma structured_certificate_unfold_free {cost Γ entry statement exit}
    (certificate : structured_certificate cost Γ entry statement exit) :
    unfold_free statement.
Proof.
  induction certificate; simpl; intuition.
  destruct statement; cbn in e |- *; try discriminate; exact I.
Qed.

(** Safety condition needed by the Iris interpretation: invariant-access
    regions may contain trusted atomic blocks, but may not themselves occur
    inside one. *)
Fixpoint structured_accesses_outside_atomic
    {cost Γ entry statement exit}
    (certificate : structured_certificate cost Γ entry statement exit) : Prop :=
  match certificate with
  | StructuredSequence _ _ _ _ _ _ _ _ first second =>
      structured_accesses_outside_atomic first /\
      structured_accesses_outside_atomic second
  | StructuredConditional _ _ _ _ _ _ _ _ _ then_branch else_branch _ _ =>
      structured_accesses_outside_atomic then_branch /\
      structured_accesses_outside_atomic else_branch
  | StructuredAtomic _ _ _ _ _ _ _ _ body _ =>
      structured_accesses_outside_atomic body
  | StructuredInvAccess _ _ access_entry _ _ _ _ _ _ body _ =>
      GenericRegions.Atomicity.analysis_in_atomic access_entry = false /\
      structured_accesses_outside_atomic body
  | _ => True
  end.

(** Without an unfold, the LIFO machine can only preserve or pop its input
    stack.  These two small facts let the focused normalizer recognize an
    ordinary, stack-preserving prefix without reconstructing an access trace. *)
Lemma unfold_free_lifo_length_le {cost Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ entry statement exit) stack_in stack_out :
  unfold_free statement ->
  GenericRegions.Atomicity.lifo_certificate certificate stack_in stack_out ->
  length stack_out <= length stack_in.
Proof.
  revert stack_in stack_out.
  induction certificate; intros stack_in stack_out Hfree Hlifo; simpl in *.
  - subst stack_out. lia.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hfree. contradiction.
  - destruct Hlifo as [(outer & -> & _)|[-> _]]; simpl; lia.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree. destruct Hfree as [Hfirst_free Hsecond_free].
    destruct Hlifo as (stack_middle & Hfirst & Hsecond).
    specialize (IHcertificate1 _ _ Hfirst_free Hfirst).
    specialize (IHcertificate2 _ _ Hsecond_free Hsecond). lia.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree. destruct Hfree as [Hthen_free Helse_free].
    destruct Hlifo as [Hthen _]. eauto.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree. destruct Hlifo as [Hbody ->]. eauto.
Qed.

Lemma unfold_free_lifo_same_length {cost Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ entry statement exit) stack_in stack_out :
  unfold_free statement ->
  GenericRegions.Atomicity.lifo_certificate certificate stack_in stack_out ->
  length stack_out = length stack_in ->
  stack_out = stack_in.
Proof.
  revert stack_in stack_out.
  induction certificate; intros stack_in stack_out Hfree Hlifo Hlength;
    simpl in *.
  - exact Hlifo.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hfree. contradiction.
  - destruct Hlifo as [(outer & -> & _)|[-> _]]; [simpl in Hlength; lia|reflexivity].
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree. destruct Hfree as [Hfirst_free Hsecond_free].
    destruct Hlifo as (stack_middle & Hfirst & Hsecond).
    pose proof (unfold_free_lifo_length_le certificate1 _ _
      Hfirst_free Hfirst) as Hfirst_le.
    pose proof (unfold_free_lifo_length_le certificate2 _ _
      Hsecond_free Hsecond) as Hsecond_le.
    assert (length stack_middle = length stack_in) by lia.
    pose proof (IHcertificate1 _ _ Hfirst_free Hfirst ltac:(assumption))
      as Hmiddle. subst stack_middle.
    apply IHcertificate2; assumption.
  - destruct statement; cbn in e; try discriminate; inversion e; subst; clear e.
    cbn in Hfree. destruct Hfree as [Hthen_free _]. destruct Hlifo as [Hthen _].
    eauto.
  - destruct statement; cbn in e; try discriminate; inversion e; subst; clear e.
    destruct Hlifo as [Hbody ->]. reflexivity.
Qed.

Definition choose_lifo_sequence_middle
    {cost Γ entry statement first middle second exit view
      first_certificate second_certificate stack_in stack_out}
    (Hlifo : GenericRegions.Atomicity.lifo_certificate
      (GenericRegions.Atomicity.CertSequence cost Γ entry statement first
        middle second exit view first_certificate second_certificate)
      stack_in stack_out) :
  { stack_middle : list GenericRegions.Atomicity.access_marker |
    GenericRegions.Atomicity.lifo_certificate first_certificate stack_in
      stack_middle /\
    GenericRegions.Atomicity.lifo_certificate second_certificate stack_middle
      stack_out }.
Proof.
  apply constructive_indefinite_description. exact Hlifo.
Defined.

(** Every accepted baseline region is balanced when entered with no pending
    access marker.  This is the compositional boundary needed to normalize
    two adjacent accepted regions independently: the parent sequence's
    existential LIFO midpoint is forced back to [[]]. *)
Lemma baseline_normalizable_empty_output {Γ} (statement : stmt Γ)
    (Hbaseline : baseline_normalizable statement) :
  forall cost entry exit
    (certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry statement exit) stack_out,
    GenericRegions.Atomicity.lifo_certificate certificate [] stack_out ->
    stack_out = [].
Proof.
  induction Hbaseline; intros cost entry exit certificate stack_out Hlifo.
  - pose proof (unfold_free_lifo_length_le certificate [] stack_out u Hlifo)
      as Hlength.
    destruct stack_out; [reflexivity|simpl in Hlength; lia].
  - dependent destruction certificate; try discriminate.
    cbn in e. inversion e; subst.
    destruct Hlifo as (middle_stack & Hfirst & Hsecond).
    assert (Hfirst_closed : GenericRegions.Atomicity.lifo_certificate
      certificate1 [] []).
    { apply access_neutral_lifo. exact a. }
    assert (Hmiddle : middle_stack = []).
    { eapply GenericRegions.Atomicity.lifo_certificate_functional;
        eassumption. }
    subst middle_stack.
    eapply IHHbaseline. exact Hsecond.
  - dependent destruction certificate; try discriminate.
    cbn in e. inversion e; subst.
    destruct Hlifo as (middle_stack & Hfirst & Hsecond).
    assert (Hmiddle : middle_stack = []) by eauto.
    subst middle_stack.
    eauto.
  - dependent destruction certificate; try discriminate.
    cbn in e. inversion e; subst.
    destruct Hlifo as [Hthen _]. eauto.
  - dependent destruction certificate; try discriminate.
    match goal with Hview : RegionSyntax.view (TSeq _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate1; try discriminate.
    match goal with Hview : RegionSyntax.view (TUnfold _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2; try discriminate.
    match goal with Hview : RegionSyntax.view (TSeq _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2_2; try discriminate.
    match goal with Hview : RegionSyntax.view (TFold _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    destruct Hlifo as (opened_stack & Hopen & Htail).
    destruct Htail as (body_stack & Hbody & Hfold).
    assert (Hbody_same : GenericRegions.Atomicity.lifo_certificate
      certificate2_1 opened_stack opened_stack).
    { apply access_neutral_lifo. exact a. }
    assert (Hbody_stack : body_stack = opened_stack).
    { eapply GenericRegions.Atomicity.lifo_certificate_functional;
        eassumption. }
    subst body_stack.
    unfold GenericRegions.Atomicity.lifo_certificate in Hfold.
    destruct Hfold as [(outer_open & Hstack & _)|[Hsame Hclosed]].
    + cbn in Hopen. congruence.
    + exfalso. apply Hclosed.
      match goal with
      | Htransition : GenericRegions.Atomicity.open_invariant ?opened_invariant
          ?opening_state = inr ?opened_state |- _ =>
          pose proof (GenericRegions.Atomicity.open_invariant_success
            opened_invariant opening_state opened_state Htransition) as
            (_ & _ & _ & Hopened);
          rewrite (access_neutral_preserves_open certificate2_1 a), Hopened;
          apply elem_of_union_l; apply elem_of_singleton_2; reflexivity
      end.
  - dependent destruction certificate; try discriminate.
    match goal with Hview : RegionSyntax.view (TSeq _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate1; try discriminate.
    match goal with Hview : RegionSyntax.view (TUnfold _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2; try discriminate.
    match goal with Hview : RegionSyntax.view (TSeq _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2_2; try discriminate.
    match goal with Hview : RegionSyntax.view (TSeq _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    match goal with
    | Hfold_certificate : GenericRegions.Atomicity.analysis_certificate
        _ _ _ (TFold _ _ _) _ |- _ =>
        dependent destruction Hfold_certificate
    end; try discriminate.
    match goal with Hview : RegionSyntax.view (TFold _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    destruct Hlifo as (opened_stack & Hopen & Htail).
    destruct Htail as (body_stack & Hbody & Hfold_work).
    assert (Hbody_same : GenericRegions.Atomicity.lifo_certificate
      certificate2_1 opened_stack opened_stack).
    { apply access_neutral_lifo. exact a. }
    assert (Hbody_stack : body_stack = opened_stack).
    { eapply GenericRegions.Atomicity.lifo_certificate_functional;
        eassumption. }
    subst body_stack.
    destruct Hfold_work as (closed_stack & Hfold & Hwork).
    unfold GenericRegions.Atomicity.lifo_certificate in Hfold.
    destruct Hfold as [(outer_open & Hstack & _)|[Hsame Hclosed]].
    + cbn in Hopen. subst opened_stack.
      inversion Hstack; subst outer_open closed_stack.
      eapply IHHbaseline. exact Hwork.
    + exfalso. apply Hclosed.
      match goal with
      | Htransition : GenericRegions.Atomicity.open_invariant ?opened_invariant
          ?opening_state = inr ?opened_state |- _ =>
          pose proof (GenericRegions.Atomicity.open_invariant_success
            opened_invariant opening_state opened_state Htransition) as
            (_ & _ & _ & Hopened);
          rewrite (access_neutral_preserves_open certificate2_1 a), Hopened;
          apply elem_of_union_l; apply elem_of_singleton_2; reflexivity
      end.
Qed.

(** Accepted source regions are balanced at a closed procedure boundary.
    Unlike the purely syntactic statement, this uses the analyzer entry
    state so that an unmatched raw fold is correctly treated as allocation. *)
Lemma baseline_normalizable_closed_lifo {Γ} (statement : stmt Γ)
    (Hbaseline : baseline_normalizable statement) :
  forall cost entry exit
    (certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry statement exit),
    GenericRegions.Atomicity.analysis_open entry = ∅ ->
    GenericRegions.Atomicity.lifo_certificate certificate [] [] /\
      GenericRegions.Atomicity.analysis_open exit = ∅.
Proof.
  induction Hbaseline; intros cost entry exit certificate Hentry.
  - now apply unfold_free_closed_lifo.
  - dependent destruction certificate; try discriminate.
    cbn in e. inversion e; subst.
    assert (Hfirst_lifo : GenericRegions.Atomicity.lifo_certificate
      certificate1 [] []).
    { apply access_neutral_lifo. exact a. }
    assert (Hmiddle : GenericRegions.Atomicity.analysis_open middle = ∅).
    { rewrite (access_neutral_preserves_open certificate1 a). exact Hentry. }
    destruct (IHHbaseline _ _ _ certificate2 Hmiddle) as [Hsecond Hexit].
    split; [eexists; split; eassumption|exact Hexit].
  - dependent destruction certificate; try discriminate.
    cbn in e. inversion e; subst.
    destruct (IHHbaseline1 _ _ _ certificate1 Hentry) as [Hfirst Hmiddle].
    destruct (IHHbaseline2 _ _ _ certificate2 Hmiddle) as [Hsecond Hexit].
    split; [eexists; split; eassumption|exact Hexit].
  - dependent destruction certificate; try discriminate.
    cbn in e. inversion e; subst.
    destruct (IHHbaseline1 _ _ _ certificate1 Hentry) as [Hthen Hthen_exit].
    destruct (IHHbaseline2 _ _ _ certificate2 Hentry) as [Helse Helse_exit].
    split; [split; assumption|exact Hthen_exit].
  - dependent destruction certificate; try discriminate.
    match goal with Hview : RegionSyntax.view (TSeq _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate1; try discriminate.
    match goal with Hview : RegionSyntax.view (TUnfold _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2; try discriminate.
    match goal with Hview : RegionSyntax.view (TSeq _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2_2; try discriminate.
    match goal with Hview : RegionSyntax.view (TFold _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    pose proof (GenericRegions.Atomicity.open_invariant_success _ _ _ e0)
      as (Hfresh & _ & _ & Hopened).
    assert (Hbody : GenericRegions.Atomicity.lifo_certificate
      certificate2_1 [(invariant, GenericRegions.Atomicity.analysis_open state)]
      [(invariant, GenericRegions.Atomicity.analysis_open state)]).
    { apply access_neutral_lifo. exact a. }
    assert (Hbody_open : GenericRegions.Atomicity.analysis_open state1 =
      {[invariant]} ∪ GenericRegions.Atomicity.analysis_open state).
    { rewrite (access_neutral_preserves_open certificate2_1 a). exact Hopened. }
    assert (Hfold : GenericRegions.Atomicity.lifo_certificate
      (GenericRegions.Atomicity.CertFold cost Γ state1
        (TFold fold_node invariant closing_arguments) invariant e3)
      [(invariant, GenericRegions.Atomicity.analysis_open state)] []).
    { left. exists (GenericRegions.Atomicity.analysis_open state).
      repeat split; try reflexivity.
      - rewrite Hbody_open. apply elem_of_union_l, elem_of_singleton_2.
        reflexivity.
      - exact Hfresh.
      - exact Hbody_open. }
    split.
    + eexists. split; [reflexivity|]. eexists. split; [exact Hbody|exact Hfold].
    + destruct (GenericRegions.Atomicity.fold_open_invariant invariant state1)
        as [_ Hclosed].
      * rewrite Hbody_open. apply elem_of_union_l, elem_of_singleton_2.
        reflexivity.
      * rewrite Hclosed, Hbody_open, Hentry.
        set_solver.
  - dependent destruction certificate; try discriminate.
    match goal with Hview : RegionSyntax.view (TSeq _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate1; try discriminate.
    match goal with Hview : RegionSyntax.view (TUnfold _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2; try discriminate.
    match goal with Hview : RegionSyntax.view (TSeq _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2_2; try discriminate.
    match goal with Hview : RegionSyntax.view (TSeq _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    match goal with
    | Hfold_certificate : GenericRegions.Atomicity.analysis_certificate
        _ _ _ (TFold _ _ _) _ |- _ =>
        dependent destruction Hfold_certificate
    end; try discriminate.
    match goal with Hview : RegionSyntax.view (TFold _ _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    pose proof (GenericRegions.Atomicity.open_invariant_success _ _ _ e0)
      as (Hfresh & _ & _ & Hopened).
    assert (Hbody : GenericRegions.Atomicity.lifo_certificate
      certificate2_1 [(invariant, GenericRegions.Atomicity.analysis_open state)]
      [(invariant, GenericRegions.Atomicity.analysis_open state)]).
    { apply access_neutral_lifo. exact a. }
    assert (Hbody_open : GenericRegions.Atomicity.analysis_open state1 =
      {[invariant]} ∪ GenericRegions.Atomicity.analysis_open state).
    { rewrite (access_neutral_preserves_open certificate2_1 a). exact Hopened. }
    assert (Hfold : GenericRegions.Atomicity.lifo_certificate
      (GenericRegions.Atomicity.CertFold cost Γ state1
        (TFold fold_node invariant closing_arguments) invariant e3)
      [(invariant, GenericRegions.Atomicity.analysis_open state)] []).
    { left. exists (GenericRegions.Atomicity.analysis_open state).
      repeat split; try reflexivity.
      - rewrite Hbody_open. apply elem_of_union_l, elem_of_singleton_2.
        reflexivity.
      - exact Hfresh.
      - exact Hbody_open. }
    assert (Hclosed_middle : GenericRegions.Atomicity.analysis_open
      (GenericRegions.Atomicity.fold_invariant invariant state1) = ∅).
    { destruct (GenericRegions.Atomicity.fold_open_invariant invariant state1)
        as [_ Hclosed].
      - rewrite Hbody_open. apply elem_of_union_l, elem_of_singleton_2.
        reflexivity.
      - rewrite Hclosed, Hbody_open, Hentry. set_solver. }
    destruct (IHHbaseline _ _ _ certificate2_2_2 Hclosed_middle)
      as [Hwork Hexit].
    split.
    + eexists. split; [reflexivity|]. eexists. split; [exact Hbody|].
      eexists. split; [exact Hfold|exact Hwork].
    + exact Hexit.
Qed.

(** In the focused one-marker traversal, an unfold-free sequence has only
    two possible handoff points: either its first child preserves the focused
    marker, or that child consumes it.  This is the structural dichotomy used
    by the recursive normalizer; in particular, callers never inspect the
    implementation of [lifo_certificate] or redo its length arithmetic. *)
Lemma unfold_free_lifo_sequence_middle_boundary
    {cost Γ entry first middle second exit marker tail stack_middle}
    (first_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry first middle)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      middle second exit)
    (Hfirst_free : unfold_free first)
    (Hsecond_free : unfold_free second)
    (Hfirst : GenericRegions.Atomicity.lifo_certificate first_certificate
      (marker :: tail) stack_middle)
    (Hsecond : GenericRegions.Atomicity.lifo_certificate second_certificate
      stack_middle tail) :
  stack_middle = marker :: tail \/ stack_middle = tail.
Proof.
  pose proof (unfold_free_lifo_length_le first_certificate _ _
    Hfirst_free Hfirst) as Hfirst_length.
  pose proof (unfold_free_lifo_length_le second_certificate _ _
    Hsecond_free Hsecond) as Hsecond_length.
  destruct (Nat.eq_dec (length stack_middle) (S (length tail))) as
    [Hpreserved | Hnot_preserved].
  - left. apply unfold_free_lifo_same_length with first_certificate;
      assumption.
  - right.
    simpl in Hfirst_length.
    assert (Hclosed : length tail = length stack_middle) by lia.
    symmetry. apply unfold_free_lifo_same_length with second_certificate;
      assumption.
Qed.

(** A fold that shortens the focused stack is necessarily the matching fold,
    not the fresh-invariant-allocation alternative of the analyzer rule. *)
Lemma lifo_fold_consumes_focused_marker
    {cost Γ state node invariant arguments}
    {focused : inv_id} {outer_open : gset inv_id}
    {tail : list GenericRegions.Atomicity.access_marker}
    (Hlifo : GenericRegions.Atomicity.lifo_certificate
      (GenericRegions.Atomicity.CertFold cost Γ state
        (TFold node invariant arguments) invariant eq_refl)
      ((focused, outer_open) :: tail) tail) :
  invariant = focused.
Proof.
  simpl in Hlifo.
  destruct Hlifo as
    [(observed_outer & Hstack & _)|[Hstack _]].
  - congruence.
  - apply (f_equal (@length _)) in Hstack. simpl in Hstack. lia.
Qed.

Lemma unfold_free_balanced_structured {cost Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ entry statement exit) stack :
  unfold_free statement ->
  GenericRegions.Atomicity.lifo_certificate certificate stack stack ->
  structured_certificate cost Γ entry statement exit.
Proof.
  revert stack.
  induction certificate; intros stack Hfree Hlifo; simpl in *.
  - econstructor; eauto.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hfree. contradiction.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    destruct (decide
      (invariant ∈ GenericRegions.Atomicity.analysis_open state)) as
      [Hmember|Hfresh].
    + exfalso. destruct Hlifo as
        [(outer & Hcons & _)|[_ Hnot_member]].
      * apply (f_equal (@length _)) in Hcons. simpl in Hcons. lia.
      * exact (Hnot_member Hmember).
    + apply StructuredFreshFold. exact Hfresh.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree. destruct Hfree as [Hfirst_free Hsecond_free].
    destruct (constructive_indefinite_description _ Hlifo) as
      (stack_middle & Hfirst & Hsecond).
    pose proof (unfold_free_lifo_length_le certificate1 _ _
      Hfirst_free Hfirst) as Hfirst_le.
    pose proof (unfold_free_lifo_length_le certificate2 _ _
      Hsecond_free Hsecond) as Hsecond_le.
    assert (Hmiddle_length : length stack_middle = length stack) by lia.
    pose proof (unfold_free_lifo_same_length certificate1 _ _
      Hfirst_free Hfirst Hmiddle_length) as Hmiddle.
    subst stack_middle. eapply StructuredSequence.
    + apply (IHcertificate1 stack); assumption.
    + apply (IHcertificate2 stack); assumption.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree. destruct Hfree as [Hthen_free Helse_free].
    eapply StructuredConditional; eauto using (proj1 Hlifo), (proj2 Hlifo).
  - destruct statement; cbn in e; try discriminate; inversion e; subst; clear e.
    cbn in Hfree. eapply StructuredAtomic; eauto using (proj1 Hlifo).
Qed.

(** Footprint-preserving form used by the public dispatcher.  The older
    projection above remains useful to low-level callers that need only a
    structured certificate. *)
Record balanced_structured_result {cost Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ entry statement exit) : Type := {
  balanced_structured_certificate :
    structured_certificate cost Γ entry statement exit;
  balanced_structured_footprint :
    structured_certificate_footprint balanced_structured_certificate ⊆
    GenericRegions.Atomicity.certificate_footprint certificate;
  balanced_structured_safe :
    structured_accesses_outside_atomic balanced_structured_certificate;
}.

Arguments balanced_structured_certificate {_ _ _ _ _ _} _.
Arguments balanced_structured_footprint {_ _ _ _ _ _} _ _ _.
Arguments balanced_structured_safe {_ _ _ _ _ _} _.

Lemma unfold_free_balanced_structured_result
    {cost Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ entry statement exit) stack :
  unfold_free statement ->
  GenericRegions.Atomicity.lifo_certificate certificate stack stack ->
  balanced_structured_result certificate.
Proof.
  revert stack.
  induction certificate; intros stack Hfree Hlifo; simpl in *.
  - refine {| balanced_structured_certificate := StructuredLeaf cost Γ state
        statement exit e e0 |}.
    intros invariant Hmember. exact Hmember.
    exact I.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hfree. contradiction.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    destruct (decide
      (invariant ∈ GenericRegions.Atomicity.analysis_open state)) as
      [Hmember|Hfresh].
    + exfalso. destruct Hlifo as
        [(outer & Hcons & _)|[_ Hnot_member]].
      * apply (f_equal (@length _)) in Hcons. simpl in Hcons. lia.
      * exact (Hnot_member Hmember).
    + refine {| balanced_structured_certificate :=
          StructuredFreshFold cost Γ state _ invariant arguments Hfresh |}.
      intros candidate Hcandidate. exact Hcandidate.
      exact I.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree. destruct Hfree as [Hfirst_free Hsecond_free].
    destruct (constructive_indefinite_description _ Hlifo) as
      (stack_middle & Hfirst & Hsecond).
    pose proof (unfold_free_lifo_length_le certificate1 _ _
      Hfirst_free Hfirst) as Hfirst_le.
    pose proof (unfold_free_lifo_length_le certificate2 _ _
      Hsecond_free Hsecond) as Hsecond_le.
    assert (Hmiddle_length : length stack_middle = length stack) by lia.
    pose proof (unfold_free_lifo_same_length certificate1 _ _
      Hfirst_free Hfirst Hmiddle_length) as Hmiddle.
    subst stack_middle.
    pose (first_result := IHcertificate1 stack Hfirst_free Hfirst).
    pose (second_result := IHcertificate2 stack Hsecond_free Hsecond).
    refine {| balanced_structured_certificate :=
        StructuredSequence cost Γ state _ first middle second exit
          first_result.(balanced_structured_certificate)
          second_result.(balanced_structured_certificate) |}.
    intros invariant Hmember.
    simpl in Hmember |- *.
    repeat rewrite elem_of_union in Hmember |- *.
    pose proof (first_result.(balanced_structured_footprint) invariant) as
      Hfirst_subset.
    pose proof (second_result.(balanced_structured_footprint) invariant) as
      Hsecond_subset.
    tauto.
    split; [exact first_result.(balanced_structured_safe) |
      exact second_result.(balanced_structured_safe)].
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree. destruct Hfree as [Hthen_free Helse_free].
    pose (then_result := IHcertificate1 stack Hthen_free (proj1 Hlifo)).
    pose (else_result := IHcertificate2 stack Helse_free (proj2 Hlifo)).
    refine {| balanced_structured_certificate :=
        StructuredConditional cost Γ state _ condition then_branch else_branch
          then_exit else_exit then_result.(balanced_structured_certificate)
          else_result.(balanced_structured_certificate) e0 e1 |}.
    intros invariant Hmember.
    simpl in Hmember |- *.
    repeat rewrite elem_of_union in Hmember |- *.
    pose proof (then_result.(balanced_structured_footprint) invariant) as
      Hthen_subset.
    pose proof (else_result.(balanced_structured_footprint) invariant) as
      Helse_subset.
    tauto.
    split; [exact then_result.(balanced_structured_safe) |
      exact else_result.(balanced_structured_safe)].
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree.
    pose (body_result := IHcertificate stack Hfree (proj1 Hlifo)).
    refine {| balanced_structured_certificate :=
        StructuredAtomic cost Γ state _ body outer inner e0
          body_result.(balanced_structured_certificate) e1 |}.
    intros invariant Hmember.
    simpl in Hmember |- *.
    repeat rewrite elem_of_union in Hmember |- *.
    pose proof (body_result.(balanced_structured_footprint) invariant) as
      Hbody_subset.
    destruct Hmember as
      [[[[Hentry_mask | Hentry_open] | Hexit_mask] | Hexit_open] | Hbody].
    + simpl. repeat rewrite elem_of_union. tauto.
    + simpl. repeat rewrite elem_of_union. tauto.
    + simpl. repeat rewrite elem_of_union. tauto.
    + simpl. repeat rewrite elem_of_union. tauto.
    + specialize (Hbody_subset Hbody). simpl. tauto.
    + exact body_result.(balanced_structured_safe).
Defined.

End Make.
End TypedNormalizationBase.
