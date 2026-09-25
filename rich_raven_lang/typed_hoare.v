From Coq Require Import List Program.Equality ZArith Lia
  Logic.ProofIrrelevance Logic.FunctionalExtensionality.
From stdpp Require Import gmap sets.

From raven_iris.rich_raven_lang Require Import
  typed_core typed_assertion typed_ir typed_resource_hoare.

Import ListNotations.
Open Scope list_scope.

(** The typed Raven Hoare calculus.  This module contains only
    syntax-directed proof rules; their semantic validation is a separate
    concern. *)
Module TypedHoare.

Import TypedCore TypedIR.

Module Make (RAs : RA_VALUE_CONFIG) (Logic : TypedAssertion.LOGIC_SIGNATURE).
(** Project the substrate from the resource calculus, which is applied
    once, so both calculi share a single instance while they coexist. *)
Module ResourceHoare := TypedResourceHoare.Make RAs Logic.
Module IR := ResourceHoare.IR.
Module Core := IR.Core.
Module Assertions := IR.Assertions.
Module Resource := IR.Resource.
Import Core Assertions IR.

Definition mask := gset inv_id.


Fixpoint allocated_physical_fields_assertion {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
    assertion Γ F (TRef :: Δ) :=
  match fields with
  | [] => APure True
  | FieldInit field value :: fields' =>
      AAnd (AOwn field (ERef (RefBound MHere))
        (weaken_expr (symbolize_expr store value)))
        (allocated_physical_fields_assertion store fields')
  end.

Fixpoint allocated_ghost_fields_assertion {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) :
    assertion Γ F (TRef :: Δ) :=
  match fields with
  | [] => APure True
  | GhostFieldInit resource field Hfield value :: fields' =>
      AAnd
        (AGhostOwn field (ERef (RefBound MHere))
          (eq_rect (TRA resource) (expr F (TRef :: Δ))
            (weaken_expr (symbolize_expr store value))
            (Logic.field_type field) (eq_sym Hfield)))
        (allocated_ghost_fields_assertion store fields')
  end.

Definition allocated_fields_assertion {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
  assertion Γ F (TRef :: Δ) :=
  AAnd
    (allocated_physical_fields_assertion store
      (physical_field_initializers fields))
    (allocated_ghost_fields_assertion store (ghost_field_initializers fields)).

Fixpoint ghost_initializers_valid_assertion {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) :
    assertion Γ F Δ :=
  match fields with
  | [] => APure True
  | GhostFieldInit resource _ _ value :: fields' =>
      AAnd (ARAValid (TRA resource) (symbolize_expr store value))
        (ghost_initializers_valid_assertion store fields')
  end.

Lemma allocated_physical_fields_assertion_stack_free {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
  stack_free (allocated_physical_fields_assertion store fields).
Proof.
  induction fields as [|[field value] fields IH]; cbn.
  - constructor.
  - constructor; [constructor|exact IH].
Qed.

Lemma allocated_ghost_fields_assertion_stack_free {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) :
  stack_free (allocated_ghost_fields_assertion store fields).
Proof.
  induction fields as [|[resource field Hfield value] fields IH]; cbn.
  - constructor.
  - constructor; [constructor|exact IH].
Qed.

Lemma allocated_fields_assertion_stack_free {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
  stack_free (allocated_fields_assertion store fields).
Proof.
  unfold allocated_fields_assertion.
  constructor.
  - apply allocated_physical_fields_assertion_stack_free.
  - apply allocated_ghost_fields_assertion_stack_free.
Qed.

Lemma ghost_initializers_valid_assertion_stack_free {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) :
  stack_free (ghost_initializers_valid_assertion store fields).
Proof.
  induction fields as [|[resource field Hfield value] fields IH]; cbn.
  - constructor.
  - constructor; [constructor|exact IH].
Qed.

Lemma allocated_physical_fields_assertion_stack_count {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
  assertion_stack_count (allocated_physical_fields_assertion store fields) = 0.
Proof.
  apply stack_free_assertion_stack_count.
  apply allocated_physical_fields_assertion_stack_free.
Qed.

Lemma allocated_ghost_fields_assertion_stack_count {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) :
  assertion_stack_count (allocated_ghost_fields_assertion store fields) = 0.
Proof.
  apply stack_free_assertion_stack_count.
  apply allocated_ghost_fields_assertion_stack_free.
Qed.

Lemma ghost_initializers_valid_assertion_stack_count {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) :
  assertion_stack_count (ghost_initializers_valid_assertion store fields) = 0.
Proof.
  apply stack_free_assertion_stack_count.
  apply ghost_initializers_valid_assertion_stack_free.
Qed.


(** One-step entailments contain only semantic/structural primitives.
    Reflexivity, transitivity, and congruence are factored into the closure
    below instead of repeated as domain-specific constructors. *)

(** Proof-relevant identity of one invariant instance.  The declaration ID
    remains separate because today's executable mask analysis is ID-based;
    the argument vector is retained so a future per-instance analysis can use
    the complete key without changing normalization or semantic rule
    interfaces. *)
Record invariant_instance_key {F Δ} (invariant : inv_id) : Type := {
  invariant_instance_arguments :
    expr_list F Δ (Logic.invariant_args invariant);
}.

(** Equality certificate generated by the combined atomicity/Hoare
    certification pass.  Equality is conditional on an ordinary Raven
    assertion, exactly matching the frontend's stability-assertion scheme.
    A ghost-snapshot extension changes only [condition] and the expressions
    stored in the keys. *)
Record invariant_instance_equality {F Δ} (invariant : inv_id)
    (opening closing : invariant_instance_key invariant) : Type := {
  invariant_instance_equality_condition : expr F Δ TBool;
  invariant_instance_equal_assuming :
    expr_list_equal_assuming invariant_instance_equality_condition _
      (invariant_instance_arguments invariant closing)
      (invariant_instance_arguments invariant opening);
}.

Definition invariant_instance_key_of_arguments {F Δ invariant}
    (arguments : expr_list F Δ (Logic.invariant_args invariant)) :
    @invariant_instance_key F Δ invariant :=
  {| invariant_instance_arguments := arguments |}.

(** Store-indexed boundary evidence consumed by normalization.  Source
    annotations and symbolic stores are retained independently: explicit
    equality assertions may justify different expressions, and a future
    snapshot pass may replace either side without changing this interface. *)
Record invariant_access_boundary_equality {Γ F Δ} (invariant : inv_id)
    (opening_arguments closing_arguments :
      pexpr_list Γ (Logic.invariant_args invariant))
    (opening_store closing_store : symbolic_store Γ F Δ) : Type := {
  invariant_boundary_instance_equality :
    invariant_instance_equality invariant
      (invariant_instance_key_of_arguments
        (symbolize_expr_list opening_store opening_arguments))
      (invariant_instance_key_of_arguments
        (symbolize_expr_list closing_store closing_arguments));
}.

Lemma entailment_step_stack_count {Γ F Δ}
    (left right : assertion Γ F Δ) :
  entailment_step left right ->
  assertion_stack_count right <= assertion_stack_count left.
Proof.
  intro Hstep.
  induction Hstep; cbn; try lia.
  - rewrite (stack_free_assertion_stack_count _ H), Nat.max_0_r.
    lia.
  - rewrite (stack_free_assertion_stack_count _ H), Nat.max_0_l.
    lia.
Qed.

Lemma assertion_entails_stack_count {Γ F Δ}
    (left right : assertion Γ F Δ) :
  assertion_entails left right ->
  assertion_stack_count right <= assertion_stack_count left.
Proof.
  intro Hentails.
  induction Hentails; cbn.
  - reflexivity.
  - apply entailment_step_stack_count. exact H.
  - eapply Nat.le_trans; eauto.
  - lia.
  - exact IHHentails.
  - rewrite (subst_bound_assertion_stack_count _ _ _ H). reflexivity.
  - rewrite <- (weaken_assertion_stack_count (u := t) conclusion).
    exact IHHentails.
  - rewrite (weaken_assertion_stack_count (u := t) frame). reflexivity.
  - rewrite (weaken_assertion_stack_count (u := t) frame). reflexivity.
  - rewrite (weaken_assertion_stack_count (u := t) frame). reflexivity.
  - lia.
  - rewrite (weaken_assertion_stack_count (u := t) formula). reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite rename_bound_assertion_stack_count. reflexivity.
  - exact IHHentails.
Qed.

Lemma entails_exists_and_left_out {Γ F Δ t}
    (frame : assertion Γ F Δ) (body : assertion Γ F (t :: Δ)) :
  assertion_entails
    (AExists t (AAnd (weaken_assertion frame) body))
    (AAnd frame (AExists t body)).
Proof.
  eapply EntailsTrans.
  - apply EntailsExistsMono. apply EntailsStep. apply ESAndComm.
  - eapply EntailsTrans.
    + apply EntailsExistsAndRightOut.
    + apply EntailsStep. apply ESAndComm.
Qed.

Lemma existential_prenex_and_right_entails {Γ F Δ}
    (left : assertion Γ F Δ) (right : existential_prenex Γ F Δ) :
  assertion_entails (AAnd left (interp_existential_prenex right))
    (interp_existential_prenex
      (existential_prenex_and_right left right)).
Proof.
  revert left. induction right; intro left; cbn.
  - apply EntailsRefl.
  - eapply EntailsTrans.
    + apply EntailsAndExistsLeft.
    + apply EntailsExistsMono. apply IHright.
Qed.

Lemma existential_prenex_and_right_entails_back {Γ F Δ}
    (left : assertion Γ F Δ) (right : existential_prenex Γ F Δ) :
  assertion_entails
    (interp_existential_prenex
      (existential_prenex_and_right left right))
    (AAnd left (interp_existential_prenex right)).
Proof.
  revert left. induction right; intro left; cbn.
  - apply EntailsRefl.
  - eapply EntailsTrans.
    + apply EntailsExistsMono. apply IHright.
    + apply entails_exists_and_left_out.
Qed.

Lemma existential_prenex_and_entails {Γ F Δ}
    (left right : existential_prenex Γ F Δ) :
  assertion_entails
    (AAnd (interp_existential_prenex left)
      (interp_existential_prenex right))
    (interp_existential_prenex (existential_prenex_and left right)).
Proof.
  revert right. induction left; intro right; cbn.
  - apply existential_prenex_and_right_entails.
  - eapply EntailsTrans.
    + apply EntailsExistsAndRight.
    + apply EntailsExistsMono.
      pose proof (IHleft (weaken_existential_prenex right)) as Hinduction.
      unfold weaken_existential_prenex in Hinduction.
      rewrite interp_rename_bound_existential_prenex in Hinduction.
      exact Hinduction.
Qed.

Lemma existential_prenex_and_entails_back {Γ F Δ}
    (left right : existential_prenex Γ F Δ) :
  assertion_entails
    (interp_existential_prenex (existential_prenex_and left right))
    (AAnd (interp_existential_prenex left)
      (interp_existential_prenex right)).
Proof.
  revert right. induction left; intro right; cbn.
  - apply existential_prenex_and_right_entails_back.
  - eapply EntailsTrans.
    + apply EntailsExistsMono.
      pose proof (IHleft (weaken_existential_prenex right)) as Hinduction.
      unfold weaken_existential_prenex in Hinduction.
      rewrite interp_rename_bound_existential_prenex in Hinduction.
      exact Hinduction.
    + apply EntailsExistsAndRightOut.
Qed.

Lemma entails_exists_vacuous_out {Γ F Δ t}
    (formula : assertion Γ F Δ) :
  assertion_entails (AExists t (weaken_assertion formula)) formula.
Proof.
  apply EntailsExistsElim. apply EntailsRefl.
Qed.

Lemma existential_prenex_ite_else_entails {Γ F Δ}
    (condition : expr F Δ TBool) (then_branch : assertion Γ F Δ)
    (else_branch : existential_prenex Γ F Δ) :
  assertion_entails
    (AIte condition then_branch
      (interp_existential_prenex else_branch))
    (interp_existential_prenex
      (existential_prenex_ite_else condition then_branch else_branch)).
Proof.
  revert condition then_branch.
  induction else_branch; intros condition then_branch; cbn.
  - apply EntailsRefl.
  - eapply EntailsTrans.
    + apply EntailsIteMono.
      * apply EntailsExistsVacuousIntro.
      * apply EntailsRefl.
    + eapply EntailsTrans.
      * apply EntailsIteExistsIn.
      * apply EntailsExistsMono. apply IHelse_branch.
Qed.

Lemma existential_prenex_ite_else_entails_back {Γ F Δ}
    (condition : expr F Δ TBool) (then_branch : assertion Γ F Δ)
    (else_branch : existential_prenex Γ F Δ) :
  assertion_entails
    (interp_existential_prenex
      (existential_prenex_ite_else condition then_branch else_branch))
    (AIte condition then_branch
      (interp_existential_prenex else_branch)).
Proof.
  revert condition then_branch.
  induction else_branch; intros condition then_branch; cbn.
  - apply EntailsRefl.
  - eapply EntailsTrans.
    + apply EntailsExistsMono. apply IHelse_branch.
    + eapply EntailsTrans.
      * apply EntailsExistsIteOut.
      * apply EntailsIteMono.
        -- apply entails_exists_vacuous_out.
        -- apply EntailsRefl.
Qed.

Lemma existential_prenex_ite_entails {Γ F Δ}
    (condition : expr F Δ TBool)
    (then_branch else_branch : existential_prenex Γ F Δ) :
  assertion_entails
    (AIte condition (interp_existential_prenex then_branch)
      (interp_existential_prenex else_branch))
    (interp_existential_prenex
      (existential_prenex_ite condition then_branch else_branch)).
Proof.
  revert condition else_branch.
  induction then_branch; intros condition else_branch; cbn.
  - apply existential_prenex_ite_else_entails.
  - eapply EntailsTrans.
    + apply EntailsIteMono.
      * apply EntailsRefl.
      * apply EntailsExistsVacuousIntro.
    + eapply EntailsTrans.
      * apply EntailsIteExistsIn.
      * apply EntailsExistsMono.
        pose proof (IHthen_branch (weaken_expr condition)
          (weaken_existential_prenex else_branch)) as Hinduction.
        unfold weaken_existential_prenex in Hinduction.
        rewrite interp_rename_bound_existential_prenex in Hinduction.
        exact Hinduction.
Qed.

Lemma existential_prenex_ite_entails_back {Γ F Δ}
    (condition : expr F Δ TBool)
    (then_branch else_branch : existential_prenex Γ F Δ) :
  assertion_entails
    (interp_existential_prenex
      (existential_prenex_ite condition then_branch else_branch))
    (AIte condition (interp_existential_prenex then_branch)
      (interp_existential_prenex else_branch)).
Proof.
  revert condition else_branch.
  induction then_branch; intros condition else_branch; cbn.
  - apply existential_prenex_ite_else_entails_back.
  - eapply EntailsTrans.
    + apply EntailsExistsMono.
      pose proof (IHthen_branch (weaken_expr condition)
        (weaken_existential_prenex else_branch)) as Hinduction.
      unfold weaken_existential_prenex in Hinduction.
      rewrite interp_rename_bound_existential_prenex in Hinduction.
      exact Hinduction.
    + eapply EntailsTrans.
      * apply EntailsExistsIteOut.
      * apply EntailsIteMono.
        -- apply EntailsRefl.
        -- apply entails_exists_vacuous_out.
Qed.

Theorem normalize_existential_prenex_entails {Γ F Δ}
    (formula : assertion Γ F Δ) :
  assertion_entails formula
    (interp_existential_prenex (normalize_existential_prenex formula)).
Proof.
  induction formula; cbn; try apply EntailsRefl.
  - apply EntailsExistsMono. exact IHformula.
  - apply EntailsForallMono. exact IHformula.
  - eapply EntailsTrans.
    + apply EntailsIteMono; eassumption.
    + apply existential_prenex_ite_entails.
  - eapply EntailsTrans.
    + apply EntailsAndMono; eassumption.
    + apply existential_prenex_and_entails.
Qed.

Theorem normalize_existential_prenex_entails_back {Γ F Δ}
    (formula : assertion Γ F Δ) :
  assertion_entails
    (interp_existential_prenex (normalize_existential_prenex formula))
    formula.
Proof.
  induction formula; cbn; try apply EntailsRefl.
  - apply EntailsExistsMono. exact IHformula.
  - apply EntailsForallMono. exact IHformula.
  - eapply EntailsTrans.
    + apply existential_prenex_ite_entails_back.
    + apply EntailsIteMono; eassumption.
  - eapply EntailsTrans.
    + apply existential_prenex_and_entails_back.
    + apply EntailsAndMono; eassumption.
Qed.

(** The tail of a binder environment is the environment seen by an assertion
    before it is weakened under a fresh outer binder.  Keeping this explicit
    avoids having to choose a value for the fresh binder when transporting
    semantic entailment certificates. *)
Definition tail_binder_env {Δ u} (binders : binder_env (u :: Δ)) :
    binder_env Δ :=
  fun t variable => binders t (weaken_bound_renaming t variable).


Lemma weaken_bound_renaming_injective {Δ u} :
  bound_renaming_injective (@weaken_bound_renaming Δ u).
Proof.
  intros t left right Hequal.
  unfold weaken_bound_renaming in Hequal.
  dependent destruction Hequal. reflexivity.
Qed.

Lemma lift_bound_renaming_injective {Δ Δ' u}
    (renaming : bound_renaming Δ Δ') :
  bound_renaming_injective renaming ->
  bound_renaming_injective (lift_bound_renaming (u := u) renaming).
Proof.
  intro Hinjective. intros t left right Hequal.
  dependent destruction left; dependent destruction right;
    unfold lift_bound_renaming in Hequal;
    rewrite ?view_member_here, ?view_member_there in Hequal;
    try discriminate; try reflexivity.
  injection Hequal as Hrenamed. f_equal.
  apply Hinjective. dependent destruction Hrenamed.
  match goal with H : renaming _ _ = renaming _ _ |- _ => exact H end.
Qed.

Lemma rename_bound_expr_weaken_local {F Δ t u}
    (expression : expr F Δ t) :
  rename_bound_expr (@weaken_bound_renaming Δ u) expression =
    weaken_expr (u := u) expression.
Proof.
  induction expression; cbn [rename_bound_expr rename_bound_ref
    weaken_expr weaken_ref weaken_bound_renaming]; try reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma interp_weaken_expr_tail {F Δ t u}
    (formals : formal_env F) (binders : binder_env (u :: Δ))
    (atoms : atom_env) (expression : expr F Δ t) :
  interp_expr formals binders atoms (weaken_expr (u := u) expression) =
    interp_expr formals (tail_binder_env binders) atoms expression.
Proof.
  rewrite <- rename_bound_expr_weaken_local.
  apply interp_rename_bound_expr.
  intros v variable. reflexivity.
Qed.

Lemma expr_list_equal_assuming_weaken {F Δ ts u}
    (condition : expr F Δ TBool)
    (left right : expr_list F Δ ts) :
  expr_list_equal_assuming condition ts left right ->
  expr_list_equal_assuming (weaken_expr (u := u) condition) ts
    (weaken_expr_list (u := u) left) (weaken_expr_list (u := u) right).
Proof.
  intro Hequal. induction Hequal.
  - apply ExprListEqualNil.
  - cbn [weaken_expr_list]. apply ExprListEqualCons.
    + intros formals binders atoms Hcondition.
      rewrite interp_weaken_expr_tail in Hcondition.
      rewrite interp_weaken_expr_tail.
      rewrite interp_weaken_expr_tail.
      eapply H; exact Hcondition.
    + exact IHHequal.
Qed.

Definition pullback_binder_env {Δ Δ'}
    (renaming : bound_renaming Δ Δ') (binders : binder_env Δ') :
    binder_env Δ :=
  fun t variable => binders t (renaming t variable).

Lemma interp_rename_bound_expr_pullback {F Δ Δ' t}
    (renaming : bound_renaming Δ Δ') (formals : formal_env F)
    (binders : binder_env Δ') (atoms : atom_env) (expression : expr F Δ t) :
  interp_expr formals binders atoms (rename_bound_expr renaming expression) =
    interp_expr formals (pullback_binder_env renaming binders) atoms expression.
Proof.
  apply interp_rename_bound_expr.
  intros. reflexivity.
Qed.

Lemma expr_list_equal_assuming_rename {F Δ Δ' ts}
    (renaming : bound_renaming Δ Δ')
    (condition : expr F Δ TBool)
    (left right : expr_list F Δ ts) :
  expr_list_equal_assuming condition ts left right ->
  expr_list_equal_assuming (rename_bound_expr renaming condition) ts
    (rename_bound_expr_list renaming left)
    (rename_bound_expr_list renaming right).
Proof.
  intro Hequal. induction Hequal; cbn [rename_bound_expr_list].
  - constructor.
  - constructor.
    + intros formals binders atoms Hcondition.
      repeat rewrite interp_rename_bound_expr_pullback in *.
      eapply H; exact Hcondition.
    + exact IHHequal.
Qed.

Lemma entailment_step_rename {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ') (left right : assertion Γ F Δ) :
  entailment_step left right ->
  entailment_step (rename_bound_assertion renaming left)
    (rename_bound_assertion renaming right).
Proof.
  intro Hstep.
  induction Hstep; cbn [rename_bound_assertion]; try constructor; eauto.
  all: try (apply Assertions.stack_free_rename_bound_assertion; assumption).
  all: try (intros; repeat rewrite interp_rename_bound_expr_pullback in *;
    eauto).
  all: try (apply expr_list_equal_assuming_rename; assumption).
Qed.

Lemma entailment_step_weaken {Γ F Δ u}
    (left right : assertion Γ F Δ) :
  entailment_step left right ->
  entailment_step (weaken_assertion (u := u) left)
    (weaken_assertion (u := u) right).
Proof.
  intro Hstep.
  induction Hstep; cbn [weaken_assertion]; try constructor; eauto.
  all: try (apply Assertions.stack_free_rename_bound_assertion; assumption).
  all: try (intros; repeat rewrite rename_bound_expr_weaken_local in *;
    repeat rewrite interp_weaken_expr_tail in *; eauto).
  all: try (apply expr_list_equal_assuming_weaken; assumption).
  all: induction H; cbn [weaken_expr_list rename_bound_expr_list];
    constructor; eauto.
  all: intros; repeat rewrite rename_bound_expr_weaken_local in *;
    repeat rewrite interp_weaken_expr_tail in *; eauto.
Qed.

Lemma entails_and_true_elim {Γ F Δ} (formula : assertion Γ F Δ) :
  assertion_entails (AAnd formula (APure True)) formula.
Proof. apply EntailsStep. apply ESAndElimL. Qed.

Lemma entails_and_comm {Γ F Δ} (left right : assertion Γ F Δ) :
  assertion_entails (AAnd left right) (AAnd right left).
Proof. apply EntailsStep. apply ESAndComm. Qed.

Lemma entails_and_assoc_r {Γ F Δ}
    (first second third : assertion Γ F Δ) :
  assertion_entails (AAnd (AAnd first second) third)
    (AAnd first (AAnd second third)).
Proof. apply EntailsStep. apply ESAndAssocR. Qed.

Lemma entails_and_assoc_l {Γ F Δ}
    (first second third : assertion Γ F Δ) :
  assertion_entails (AAnd first (AAnd second third))
    (AAnd (AAnd first second) third).
Proof. apply EntailsStep. apply ESAndAssocL. Qed.

Lemma entails_stack_exclusive {Γ F Δ}
    (left right : symbolic_store Γ F Δ) :
  assertion_entails (AAnd (AStack left) (AStack right)) (APure False).
Proof. apply EntailsStep. apply ESStackExclusive. Qed.

Lemma entails_and_swap_middle {Γ F Δ}
    (first second third fourth : assertion Γ F Δ) :
  assertion_entails
    (AAnd (AAnd first second) (AAnd third fourth))
    (AAnd (AAnd first third) (AAnd second fourth)).
Proof.
  eapply EntailsTrans.
  - apply entails_and_assoc_r.
  - eapply EntailsTrans.
    + apply EntailsAndMono; [apply EntailsRefl|].
      eapply EntailsTrans; [apply entails_and_assoc_l|].
      eapply EntailsTrans.
      * apply EntailsAndMono; [apply entails_and_comm|apply EntailsRefl].
      * apply entails_and_assoc_r.
    + apply entails_and_assoc_l.
Qed.

(** Generic renaming / substitution algebra, independent of procedure and
    resource contracts. *)
Module RenamingFacts.

(** Formal substitution commutes with a change of the ambient binder
    context.  These small syntactic facts are kept here, next to contract
    instantiation, since they are needed when an invariant instance is
    carried under an additional logical binder. *)
Definition rename_formal_subst {F F' Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (substitution : formal_subst F F' Δ) : formal_subst F F' Δ' :=
  fun t variable => rename_bound_expr renaming (substitution t variable).

Lemma rename_bound_expr_lift_weaken {F Δ Δ' t u}
    (renaming : bound_renaming Δ Δ')
    (expression : expr F Δ t) :
  rename_bound_expr (lift_bound_renaming renaming)
      (weaken_expr (u := u) expression) =
    weaken_expr (rename_bound_expr renaming expression).
Proof.
  induction expression; cbn [rename_bound_expr weaken_expr
    rename_bound_ref weaken_ref lift_bound_renaming].
  - destruct reference; cbn [rename_bound_ref weaken_ref]; try reflexivity.
    unfold lift_bound_renaming. rewrite view_member_there. reflexivity.
  - reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma rename_bound_expr_list_lift_weaken {F Δ Δ' ts u}
    (renaming : bound_renaming Δ Δ')
    (expressions : expr_list F Δ ts) :
  rename_bound_expr_list (lift_bound_renaming renaming)
      (weaken_expr_list (u := u) expressions) =
    weaken_expr_list (rename_bound_expr_list renaming expressions).
Proof.
  induction expressions; cbn [rename_bound_expr_list weaken_expr_list].
  - reflexivity.
  - f_equal; auto using rename_bound_expr_lift_weaken.
Qed.

Lemma rename_formal_subst_lift {F F' Δ Δ'} (u : typ)
    (renaming : bound_renaming Δ Δ')
    (substitution : formal_subst F F' Δ) :
  rename_formal_subst (lift_bound_renaming (u := u) renaming)
      (lift_formal_subst substitution) =
    lift_formal_subst (u := u) (rename_formal_subst renaming substitution).
Proof.
  apply functional_extensionality_dep; intro result_type.
  apply functional_extensionality; intro variable.
  apply rename_bound_expr_lift_weaken.
Qed.

Lemma subst_formals_expr_rename {F F' Δ Δ' t}
    (renaming : bound_renaming Δ Δ')
    (substitution : formal_subst F F' Δ)
    (expression : expr F Δ t) :
  subst_formals_expr (rename_formal_subst renaming substitution)
      (rename_bound_expr renaming expression) =
    rename_bound_expr renaming (subst_formals_expr substitution expression).
Proof.
  induction expression; cbn [subst_formals_expr subst_formals_ref
    rename_bound_expr rename_bound_ref]; try reflexivity.
  - destruct reference; cbn; try reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma subst_formals_expr_list_rename {F F' Δ Δ' ts}
    (renaming : bound_renaming Δ Δ')
    (substitution : formal_subst F F' Δ)
    (expressions : expr_list F Δ ts) :
  subst_formals_expr_list (rename_formal_subst renaming substitution)
      (rename_bound_expr_list renaming expressions) =
    rename_bound_expr_list renaming
      (subst_formals_expr_list substitution expressions).
Proof.
  induction expressions; cbn [subst_formals_expr_list rename_bound_expr_list].
  - reflexivity.
  - f_equal; [apply subst_formals_expr_rename|exact IHexpressions].
Qed.

Lemma subst_formals_assertion_rename {Γ F F' Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (substitution : formal_subst F F' Δ)
    (formula : assertion Γ F Δ) :
  forall target,
    subst_formals_assertion substitution formula = Some target ->
    subst_formals_assertion (rename_formal_subst renaming substitution)
      (rename_bound_assertion renaming formula) =
    Some (rename_bound_assertion renaming target).
Proof.
  revert Δ' renaming substitution.
  induction formula as [store | condition | proposition | field location chunk
    | field location chunk | r old_chunk new_chunk | t chunk
    | t body IHbody | t body IHbody | condition then_branch else_branch
      IHthen IHelse | invariant args | predicate args
    | left right IHleft IHright]; intros Δ' renaming substitution target Hresult;
    cbn in Hresult |- *.
  - discriminate.
  - inversion Hresult; subst target. cbn.
    rewrite subst_formals_expr_rename. reflexivity.
  - inversion Hresult; reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_formals_expr_rename renaming substitution chunk).
    rewrite (subst_formals_expr_rename renaming substitution chunk0). reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_formals_expr_rename renaming substitution chunk).
    rewrite (subst_formals_expr_rename renaming substitution chunk0). reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_formals_expr_rename renaming substitution new_chunk).
    rewrite (subst_formals_expr_rename renaming substitution new_chunk0). reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_formals_expr_rename renaming substitution chunk0). reflexivity.
  - destruct (subst_formals_assertion (lift_formal_subst substitution) IHbody)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target.
    rewrite <- rename_formal_subst_lift.
    rewrite (IHIHbody (body :: Δ')
      (lift_bound_renaming (u := body) renaming)
      (lift_formal_subst substitution) body' Hbody). reflexivity.
  - destruct (subst_formals_assertion (lift_formal_subst substitution) IHbody)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target.
    rewrite <- rename_formal_subst_lift.
    rewrite (IHIHbody (body :: Δ')
      (lift_bound_renaming (u := body) renaming)
      (lift_formal_subst substitution) body' Hbody). reflexivity.
  - destruct (subst_formals_assertion substitution else_branch)
      as [formula1'|] eqn:Hfirst; [|discriminate].
    destruct (subst_formals_assertion substitution IHelse)
      as [formula2'|] eqn:Hsecond; [|discriminate].
    inversion Hresult; subst target.
    cbn.
    rewrite (subst_formals_expr_rename renaming substitution then_branch).
    rewrite (IHthen Δ' renaming substitution formula1' Hfirst),
      (IHIHelse Δ' renaming substitution formula2' Hsecond). reflexivity.
  - rewrite subst_formals_expr_list_rename. inversion Hresult. reflexivity.
  - rewrite subst_formals_expr_list_rename. inversion Hresult. reflexivity.
  - destruct (subst_formals_assertion substitution right)
      as [formula1'|] eqn:Hfirst; [|discriminate].
    destruct (subst_formals_assertion substitution IHright)
      as [formula2'|] eqn:Hsecond; [|discriminate].
    inversion Hresult; subst target.
    rewrite (IHleft Δ' renaming substitution formula1' Hfirst),
      (IHIHright Δ' renaming substitution formula2' Hsecond). reflexivity.
Qed.

(** The corresponding operation for a bound substitution changes only its
    target binder context; the source context of the assertion is unchanged. *)
Definition rename_bound_subst {F Δ Δ' Δ''}
    (renaming : bound_renaming Δ' Δ'')
    (substitution : bound_subst F Δ Δ') : bound_subst F Δ Δ'' :=
  fun t variable => rename_bound_expr renaming (substitution t variable).

Lemma rename_bound_subst_lift {F Δ Δ' Δ''} (u : typ)
    (renaming : bound_renaming Δ' Δ'')
    (substitution : bound_subst F Δ Δ') :
  rename_bound_subst (lift_bound_renaming (u := u) renaming)
      (lift_bound_subst substitution) =
    lift_bound_subst (u := u) (rename_bound_subst renaming substitution).
Proof.
  apply functional_extensionality_dep; intro result_type.
  apply functional_extensionality; intro variable.
  dependent destruction variable.
  - unfold rename_bound_subst, lift_bound_subst.
    rewrite view_member_here.
    cbn [rename_bound_expr rename_bound_ref].
    unfold lift_bound_renaming. rewrite view_member_here. reflexivity.
  - unfold rename_bound_subst, lift_bound_subst.
    rewrite view_member_there.
    apply rename_bound_expr_lift_weaken.
Qed.

Lemma subst_bound_expr_rename {F Δ Δ' Δ'' t}
    (renaming : bound_renaming Δ' Δ'')
    (substitution : bound_subst F Δ Δ')
    (expression : expr F Δ t) :
  subst_bound_expr (rename_bound_subst renaming substitution) expression =
    rename_bound_expr renaming (subst_bound_expr substitution expression).
Proof.
  induction expression; cbn [subst_bound_expr subst_bound_ref
    rename_bound_expr rename_bound_ref]; try reflexivity.
  - destruct reference; cbn; try reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma subst_bound_expr_list_rename {F Δ Δ' Δ'' ts}
    (renaming : bound_renaming Δ' Δ'')
    (substitution : bound_subst F Δ Δ')
    (expressions : expr_list F Δ ts) :
  subst_bound_expr_list (rename_bound_subst renaming substitution) expressions =
    rename_bound_expr_list renaming
      (subst_bound_expr_list substitution expressions).
Proof.
  induction expressions; cbn [subst_bound_expr_list rename_bound_expr_list].
  - reflexivity.
  - f_equal; [apply subst_bound_expr_rename|exact IHexpressions].
Qed.

Lemma subst_bound_assertion_rename {Γ F Δ Δ' Δ''}
    (renaming : bound_renaming Δ' Δ'')
    (substitution : bound_subst F Δ Δ')
    (formula : assertion Γ F Δ) :
  forall target,
    subst_bound_assertion substitution formula = Some target ->
    subst_bound_assertion (rename_bound_subst renaming substitution) formula =
    Some (rename_bound_assertion renaming target).
Proof.
  revert Δ' Δ'' renaming substitution.
  induction formula as [store | condition | proposition | field location chunk
    | field location chunk | r old_chunk new_chunk | t chunk
    | t body IHbody | t body IHbody | condition then_branch else_branch
      IHthen IHelse | invariant args | predicate args
    | left right IHleft IHright]; intros Δ' Δ'' renaming substitution target Hresult;
    cbn in Hresult |- *.
  - discriminate.
  - inversion Hresult; subst target. cbn.
    rewrite subst_bound_expr_rename. reflexivity.
  - inversion Hresult; reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_bound_expr_rename renaming substitution chunk).
    rewrite (subst_bound_expr_rename renaming substitution chunk0). reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_bound_expr_rename renaming substitution chunk).
    rewrite (subst_bound_expr_rename renaming substitution chunk0). reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_bound_expr_rename renaming substitution new_chunk).
    rewrite (subst_bound_expr_rename renaming substitution new_chunk0). reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_bound_expr_rename renaming substitution chunk0). reflexivity.
  - destruct (subst_bound_assertion (lift_bound_subst substitution) IHbody)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target.
    rewrite <- rename_bound_subst_lift.
    rewrite (IHIHbody (body :: Δ') (body :: Δ'')
      (lift_bound_renaming (u := body) renaming)
      (lift_bound_subst substitution) body' Hbody). reflexivity.
  - destruct (subst_bound_assertion (lift_bound_subst substitution) IHbody)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target.
    rewrite <- rename_bound_subst_lift.
    rewrite (IHIHbody (body :: Δ') (body :: Δ'')
      (lift_bound_renaming (u := body) renaming)
      (lift_bound_subst substitution) body' Hbody). reflexivity.
  - destruct (subst_bound_assertion substitution else_branch)
      as [formula1'|] eqn:Hfirst; [|discriminate].
    destruct (subst_bound_assertion substitution IHelse)
      as [formula2'|] eqn:Hsecond; [|discriminate].
    inversion Hresult; subst target.
    rewrite (subst_bound_expr_rename renaming substitution then_branch).
    rewrite (IHthen Δ' Δ'' renaming substitution formula1' Hfirst),
      (IHIHelse Δ' Δ'' renaming substitution formula2' Hsecond). reflexivity.
  - rewrite subst_bound_expr_list_rename. inversion Hresult. reflexivity.
  - rewrite subst_bound_expr_list_rename. inversion Hresult. reflexivity.
  - destruct (subst_bound_assertion substitution right)
      as [formula1'|] eqn:Hfirst; [|discriminate].
    destruct (subst_bound_assertion substitution IHright)
      as [formula2'|] eqn:Hsecond; [|discriminate].
    inversion Hresult; subst target.
    rewrite (IHleft Δ' Δ'' renaming substitution formula1' Hfirst),
      (IHIHright Δ' Δ'' renaming substitution formula2' Hsecond). reflexivity.
Qed.

Lemma reindex_stack_context_rename {F Δ Δ' Γ Γ'}
    (renaming : bound_renaming Δ Δ')
    (source : assertion Γ F Δ) (target : assertion Γ' F Δ) :
  reindex_stack_context source target ->
  reindex_stack_context (rename_bound_assertion renaming source)
    (rename_bound_assertion renaming target).
Proof.
  intro Hreindex.
  revert Δ' renaming.
  induction Hreindex; intros Δ' renaming;
    cbn [rename_bound_assertion]; try constructor; eauto.
Qed.

Lemma rename_empty_bound_subst {F Δ u} :
  rename_bound_subst (@weaken_bound_renaming Δ u)
      (@empty_bound_subst F Δ) =
    @empty_bound_subst F (u :: Δ).
Proof.
  apply functional_extensionality_dep; intro result_type.
  apply functional_extensionality; intro variable.
  dependent destruction variable.
Qed.

Lemma rename_empty_bound_subst_general {F Δ Δ'}
    (renaming : bound_renaming Δ Δ') :
  rename_bound_subst renaming (@empty_bound_subst F Δ) =
    @empty_bound_subst F Δ'.
Proof.
  apply functional_extensionality_dep; intro result_type.
  apply functional_extensionality; intro variable.
  dependent destruction variable.
Qed.

Lemma lookup_expr_list_there {F Δ t ts u}
    (expression : expr F Δ t) (expressions : expr_list F Δ ts)
    (variable : member ts u) :
  lookup_expr_list (ExprCons expression expressions) (MThere variable) =
    lookup_expr_list expressions variable.
Proof.
  unfold lookup_expr_list, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl).
  reflexivity.
Qed.

Lemma rename_formal_subst_expr_list {F Δ Δ' ts}
    (renaming : bound_renaming Δ Δ')
    (arguments : expr_list F Δ ts) :
  rename_formal_subst renaming (expr_list_formal_subst arguments) =
    expr_list_formal_subst (rename_bound_expr_list renaming arguments).
Proof.
  apply functional_extensionality_dep; intro result_type.
  apply functional_extensionality; intro variable.
  induction arguments as [|head_type tail head arguments IH].
  - dependent destruction variable.
  - dependent destruction variable.
    + unfold rename_formal_subst, expr_list_formal_subst.
      rewrite lookup_expr_list_here.
      cbn [rename_bound_expr_list].
      rewrite lookup_expr_list_here. reflexivity.
    + unfold rename_formal_subst, expr_list_formal_subst.
      rewrite lookup_expr_list_there.
      cbn [rename_bound_expr_list].
      rewrite lookup_expr_list_there. apply IH.
Qed.

Lemma rename_bound_expr_weaken {F Δ t u}
    (expression : expr F Δ t) :
  rename_bound_expr (@weaken_bound_renaming Δ u) expression =
    weaken_expr (u := u) expression.
Proof.
  induction expression; cbn [rename_bound_expr rename_bound_ref
    weaken_expr weaken_ref weaken_bound_renaming]; try reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma rename_bound_expr_list_weaken {F Δ ts u}
    (expressions : expr_list F Δ ts) :
  rename_bound_expr_list (@weaken_bound_renaming Δ u) expressions =
    weaken_expr_list (u := u) expressions.
Proof.
  induction expressions; cbn [rename_bound_expr_list weaken_expr_list].
  - reflexivity.
  - f_equal; [apply rename_bound_expr_weaken | exact IHexpressions].
Qed.
Lemma rename_bound_assertion_compose {Γ F Δ Δ' Δ''}
    (first : bound_renaming Δ Δ') (second : bound_renaming Δ' Δ'')
    (formula : assertion Γ F Δ) :
  rename_bound_assertion second (rename_bound_assertion first formula) =
    rename_bound_assertion (compose_bound_renaming first second) formula.
Proof.
  revert Δ' Δ'' first second.
  induction formula; intros; cbn [rename_bound_assertion];
    try (f_equal; eauto using rename_bound_expr_compose,
      rename_bound_expr_list_compose, rename_bound_store_compose).
  all: rewrite <- lift_bound_renaming_compose; apply IHformula.
Qed.

(** Renaming the caller's binder context leaves the callee's return-binder
    injection unchanged: [return_bound_renaming] targets binder zero, and
    [lift_bound_renaming] fixes binder zero.  Needed by a CONTRACT_ENV
    implementation to discharge [instantiated_post_value_rename]. *)
Lemma compose_return_bound_renaming {Δ Δ' t} (renaming : bound_renaming Δ Δ') :
  compose_bound_renaming (@return_bound_renaming Δ t)
    (lift_bound_renaming renaming) = @return_bound_renaming Δ' t.
Proof.
  apply functional_extensionality_dep; intro u.
  apply functional_extensionality; intro variable.
  unfold compose_bound_renaming, return_bound_renaming.
  dependent destruction variable.
  - rewrite view_member_here. apply lift_bound_renaming_here.
  - dependent destruction variable.
Qed.

(** The identity renaming is useful when a bound variable is temporarily
    exposed as an existential witness and then reintroduced at the head of
    the surrounding context. *)
Lemma compose_exchange_bound_renaming {Δ t u} :
  compose_bound_renaming
    (@exchange_bound_renaming Δ t u)
    (@exchange_bound_renaming Δ u t) =
  (@identity_bound_renaming (t :: u :: Δ)).
Proof.
  apply functional_extensionality_dep. intro result.
  apply functional_extensionality. intro variable.
  dependent destruction variable.
  - unfold compose_bound_renaming, identity_bound_renaming.
    rewrite exchange_bound_renaming_here,
      exchange_bound_renaming_there_here. reflexivity.
  - dependent destruction variable.
    + unfold compose_bound_renaming, identity_bound_renaming.
      rewrite exchange_bound_renaming_there_here,
        exchange_bound_renaming_here. reflexivity.
    + unfold compose_bound_renaming, identity_bound_renaming.
      rewrite !exchange_bound_renaming_there_there. reflexivity.
Qed.

Lemma exchange_bound_renaming_injective {Δ t u} :
  bound_renaming_injective (@exchange_bound_renaming Δ t u).
Proof.
  intros result left right Hequal.
  pose proof (f_equal
    (@exchange_bound_renaming Δ u t result) Hequal) as Hinverse.
  change
    (compose_bound_renaming (@exchange_bound_renaming Δ t u)
      (@exchange_bound_renaming Δ u t) result left =
     compose_bound_renaming (@exchange_bound_renaming Δ t u)
      (@exchange_bound_renaming Δ u t) result right) in Hinverse.
  rewrite compose_exchange_bound_renaming in Hinverse. exact Hinverse.
Qed.

Lemma exchange_bound_renaming_natural {Δ Θ t u}
    (renaming : bound_renaming Δ Θ) :
  compose_bound_renaming (@exchange_bound_renaming Δ u t)
    (lift_bound_renaming (u := t)
      (lift_bound_renaming (u := u) renaming)) =
  compose_bound_renaming
    (lift_bound_renaming (u := u)
      (lift_bound_renaming (u := t) renaming))
    (@exchange_bound_renaming Θ u t).
Proof.
  apply functional_extensionality_dep. intro result.
  apply functional_extensionality. intro variable.
  dependent destruction variable.
  - unfold compose_bound_renaming.
    rewrite exchange_bound_renaming_here.
    rewrite !lift_bound_renaming_there, !lift_bound_renaming_here.
    rewrite exchange_bound_renaming_here. reflexivity.
  - dependent destruction variable.
    + unfold compose_bound_renaming.
      rewrite exchange_bound_renaming_there_here.
      rewrite !lift_bound_renaming_here, !lift_bound_renaming_there.
      rewrite lift_bound_renaming_here.
      rewrite exchange_bound_renaming_there_here. reflexivity.
    + unfold compose_bound_renaming.
      rewrite exchange_bound_renaming_there_there.
      rewrite !lift_bound_renaming_there.
      rewrite exchange_bound_renaming_there_there. reflexivity.
Qed.

Lemma rename_bound_assertion_exchange_natural {Γ F Δ Θ t u}
    (renaming : bound_renaming Δ Θ)
    (body : assertion Γ F (u :: t :: Δ)) :
  rename_bound_assertion
    (lift_bound_renaming (u := t)
      (lift_bound_renaming (u := u) renaming))
    (rename_bound_assertion (@exchange_bound_renaming Δ u t) body) =
  rename_bound_assertion (@exchange_bound_renaming Θ u t)
    (rename_bound_assertion
      (lift_bound_renaming (u := u)
        (lift_bound_renaming (u := t) renaming)) body).
Proof.
  rewrite !rename_bound_assertion_compose.
  rewrite exchange_bound_renaming_natural. reflexivity.
Qed.

Lemma rename_bound_assertion_identity {Γ F Δ}
    (formula : assertion Γ F Δ) :
  rename_bound_assertion identity_bound_renaming formula = formula.
Proof.
  induction formula; cbn [rename_bound_assertion identity_bound_renaming];
    try reflexivity.
  - rewrite rename_bound_store_identity. reflexivity.
  - rewrite rename_bound_expr_identity. reflexivity.
  - rewrite rename_bound_expr_identity, rename_bound_expr_identity. reflexivity.
  - rewrite rename_bound_expr_identity, rename_bound_expr_identity. reflexivity.
  - rewrite rename_bound_expr_identity, rename_bound_expr_identity. reflexivity.
  - rewrite rename_bound_expr_identity. reflexivity.
  - rewrite lift_identity_bound_renaming, IHformula. reflexivity.
  - rewrite lift_identity_bound_renaming, IHformula. reflexivity.
  - rewrite rename_bound_expr_identity, IHformula1, IHformula2. reflexivity.
  - rewrite rename_bound_expr_list_identity. reflexivity.
  - rewrite rename_bound_expr_list_identity. reflexivity.
  - rewrite IHformula1, IHformula2. reflexivity.
Qed.

Lemma rename_bound_assertion_exchange_involutive {Γ F Δ t u}
    (formula : assertion Γ F (t :: u :: Δ)) :
  rename_bound_assertion (@exchange_bound_renaming Δ u t)
    (rename_bound_assertion (@exchange_bound_renaming Δ t u) formula) =
  formula.
Proof.
  rewrite rename_bound_assertion_compose,
    compose_exchange_bound_renaming.
  apply rename_bound_assertion_identity.
Qed.

Lemma entails_exists_swap_back {Γ F Δ t u}
    (body : assertion Γ F (u :: t :: Δ)) :
  assertion_entails
    (AExists u (AExists t
      (rename_bound_assertion (@exchange_bound_renaming Δ u t) body)))
    (AExists t (AExists u body)).
Proof.
  rewrite <- (rename_bound_assertion_exchange_involutive body) at 2.
  apply EntailsExistsSwap.
Qed.

Lemma compose_bound_renaming_lift_weaken_head_current {Δ t} :
    compose_bound_renaming
      (lift_bound_renaming (@weaken_bound_renaming Δ t))
      (head_bound_renaming MHere) =
    (@identity_bound_renaming (t :: Δ)).
Proof.
  apply functional_extensionality_dep. intros u.
  apply functional_extensionality. intro variable.
  dependent destruction variable.
  - unfold compose_bound_renaming, lift_bound_renaming,
      weaken_bound_renaming, head_bound_renaming,
      identity_bound_renaming.
    rewrite !view_member_here. reflexivity.
  - unfold compose_bound_renaming, lift_bound_renaming,
      weaken_bound_renaming, head_bound_renaming,
      identity_bound_renaming.
    rewrite !view_member_there. reflexivity.
Qed.

Lemma rename_bound_assertion_lift_weaken_head_current {Γ F Δ t}
    (body : assertion Γ F (t :: Δ)) :
  rename_bound_assertion (head_bound_renaming MHere)
      (rename_bound_assertion
        (lift_bound_renaming (@weaken_bound_renaming Δ t)) body) = body.
Proof.
  rewrite rename_bound_assertion_compose.
  rewrite compose_bound_renaming_lift_weaken_head_current.
  apply rename_bound_assertion_identity.
Qed.

Lemma rename_bound_store_weaken {Γ F Δ u}
    (store : symbolic_store Γ F Δ) :
  rename_bound_store (@weaken_bound_renaming Δ u) store =
    weaken_store (u := u) store.
Proof.
  induction store; cbn [rename_bound_store weaken_store]; f_equal; auto.
Qed.

Lemma rename_bound_assertion_lift_weaken {Γ F Δ Δ' u}
    (renaming : bound_renaming Δ Δ') (formula : assertion Γ F Δ) :
  rename_bound_assertion (lift_bound_renaming (u := u) renaming)
      (weaken_assertion (u := u) formula) =
    weaken_assertion (u := u) (rename_bound_assertion renaming formula).
Proof.
  unfold weaken_assertion.
  rewrite rename_bound_assertion_compose.
  rewrite rename_bound_assertion_compose.
  f_equal.
  apply functional_extensionality_dep; intro t.
  apply functional_extensionality; intro variable.
  unfold compose_bound_renaming, lift_bound_renaming,
    weaken_bound_renaming.
  rewrite view_member_there. reflexivity.
Qed.

Lemma allocated_physical_fields_assertion_rename {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (store : symbolic_store Γ F Δ) fields :
  rename_bound_assertion (lift_bound_renaming renaming)
      (allocated_physical_fields_assertion store fields) =
    allocated_physical_fields_assertion
      (rename_bound_store renaming store) fields.
Proof.
  induction fields as [|[field value] fields IH]; cbn.
  - reflexivity.
  - unfold lift_bound_renaming at 1. rewrite view_member_here.
    rewrite symbolize_expr_rename_bound_store.
    rewrite rename_bound_expr_lift_weaken.
    rewrite IH. reflexivity.
Qed.

Lemma allocated_ghost_fields_assertion_rename {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (store : symbolic_store Γ F Δ) fields :
  rename_bound_assertion (lift_bound_renaming renaming)
      (allocated_ghost_fields_assertion store fields) =
    allocated_ghost_fields_assertion
      (rename_bound_store renaming store) fields.
Proof.
  induction fields as [|[resource field Hfield value] fields IH]; cbn.
  - reflexivity.
  - unfold lift_bound_renaming at 1. rewrite view_member_here.
    rewrite symbolize_expr_rename_bound_store.
    destruct Hfield.
    cbn.
    rewrite rename_bound_expr_lift_weaken.
    rewrite IH. reflexivity.
Qed.

Lemma allocated_fields_assertion_rename {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (store : symbolic_store Γ F Δ) fields :
  rename_bound_assertion (lift_bound_renaming renaming)
      (allocated_fields_assertion store fields) =
    allocated_fields_assertion (rename_bound_store renaming store) fields.
Proof.
  unfold allocated_fields_assertion. cbn.
  rewrite allocated_physical_fields_assertion_rename.
  rewrite allocated_ghost_fields_assertion_rename. reflexivity.
Qed.

Lemma ghost_initializers_valid_assertion_rename {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (store : symbolic_store Γ F Δ) fields :
  rename_bound_assertion renaming
      (ghost_initializers_valid_assertion store fields) =
    ghost_initializers_valid_assertion
      (rename_bound_store renaming store) fields.
Proof.
  induction fields as [|[resource field Hfield value] fields IH]; cbn.
  - reflexivity.
  - rewrite symbolize_expr_rename_bound_store.
    rewrite IH. reflexivity.
Qed.

Lemma subst_bound_expr_rename_both
    {F Δ Δ' Θ Θ' t}
    (source_renaming : bound_renaming Δ Δ')
    (target_renaming : bound_renaming Θ Θ')
    (substitution : bound_subst F Δ Θ)
    (renamed_substitution : bound_subst F Δ' Θ')
    (Hsubst : forall u (variable : bvar Δ u),
      renamed_substitution u (source_renaming u variable) =
      rename_bound_expr target_renaming (substitution u variable))
    (expression : expr F Δ t) :
  subst_bound_expr renamed_substitution
      (rename_bound_expr source_renaming expression) =
  rename_bound_expr target_renaming
      (subst_bound_expr substitution expression).
Proof.
  induction expression;
    cbn [subst_bound_expr subst_bound_ref rename_bound_expr rename_bound_ref];
    try reflexivity.
  - destruct reference; cbn; try reflexivity. apply Hsubst.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma subst_bound_expr_list_rename_both
    {F Δ Δ' Θ Θ' ts}
    (source_renaming : bound_renaming Δ Δ')
    (target_renaming : bound_renaming Θ Θ')
    (substitution : bound_subst F Δ Θ)
    (renamed_substitution : bound_subst F Δ' Θ')
    (Hsubst : forall u (variable : bvar Δ u),
      renamed_substitution u (source_renaming u variable) =
      rename_bound_expr target_renaming (substitution u variable))
    (expressions : expr_list F Δ ts) :
  subst_bound_expr_list renamed_substitution
      (rename_bound_expr_list source_renaming expressions) =
  rename_bound_expr_list target_renaming
      (subst_bound_expr_list substitution expressions).
Proof.
  induction expressions; cbn [subst_bound_expr_list rename_bound_expr_list].
  - reflexivity.
  - f_equal.
    + apply subst_bound_expr_rename_both; assumption.
    + apply IHexpressions.
Qed.

Lemma subst_bound_assertion_rename_both
    {Γ F Δ Δ' Θ Θ'}
    (source_renaming : bound_renaming Δ Δ')
    (target_renaming : bound_renaming Θ Θ')
    (substitution : bound_subst F Δ Θ)
    (renamed_substitution : bound_subst F Δ' Θ')
    (formula : assertion Γ F Δ) :
  (forall u (variable : bvar Δ u),
    renamed_substitution u (source_renaming u variable) =
    rename_bound_expr target_renaming (substitution u variable)) ->
  subst_bound_assertion renamed_substitution
      (rename_bound_assertion source_renaming formula) =
  match subst_bound_assertion substitution formula with
  | Some result => Some (rename_bound_assertion target_renaming result)
  | None => None
  end.
Proof.
  revert Θ Δ' Θ' source_renaming target_renaming substitution
    renamed_substitution.
  induction formula; intros Θ Δ' Θ' source_renaming target_renaming
      substitution renamed_substitution Hsubst;
    cbn [rename_bound_assertion subst_bound_assertion].
  - reflexivity.
  - rewrite (subst_bound_expr_rename_both source_renaming target_renaming
      substitution renamed_substitution Hsubst condition). reflexivity.
  - reflexivity.
  - rewrite (subst_bound_expr_rename_both source_renaming target_renaming
      substitution renamed_substitution Hsubst location).
    rewrite (subst_bound_expr_rename_both source_renaming target_renaming
      substitution renamed_substitution Hsubst chunk). reflexivity.
  - rewrite (subst_bound_expr_rename_both source_renaming target_renaming
      substitution renamed_substitution Hsubst location).
    rewrite (subst_bound_expr_rename_both source_renaming target_renaming
      substitution renamed_substitution Hsubst chunk). reflexivity.
  - rewrite (subst_bound_expr_rename_both source_renaming target_renaming
      substitution renamed_substitution Hsubst old_chunk).
    rewrite (subst_bound_expr_rename_both source_renaming target_renaming
      substitution renamed_substitution Hsubst new_chunk). reflexivity.
  - rewrite (subst_bound_expr_rename_both source_renaming target_renaming
      substitution renamed_substitution Hsubst chunk). reflexivity.
  - rewrite (IHformula (t :: Θ) (t :: Δ') (t :: Θ')
      (lift_bound_renaming source_renaming)
      (lift_bound_renaming target_renaming)
      (lift_bound_subst substitution)
      (lift_bound_subst renamed_substitution)).
    + destruct (subst_bound_assertion (lift_bound_subst substitution) formula);
        reflexivity.
    + intros u variable. dependent destruction variable.
      * unfold lift_bound_renaming, lift_bound_subst.
        rewrite !view_member_here. cbn [rename_bound_expr rename_bound_ref].
        unfold lift_bound_renaming. rewrite view_member_here. reflexivity.
      * rewrite lift_bound_renaming_there.
        unfold lift_bound_subst. rewrite !view_member_there.
        rewrite rename_bound_expr_lift_weaken, Hsubst. reflexivity.
  - rewrite (IHformula (t :: Θ) (t :: Δ') (t :: Θ')
      (lift_bound_renaming source_renaming)
      (lift_bound_renaming target_renaming)
      (lift_bound_subst substitution)
      (lift_bound_subst renamed_substitution)).
    + destruct (subst_bound_assertion (lift_bound_subst substitution) formula);
        reflexivity.
    + intros u variable. dependent destruction variable.
      * unfold lift_bound_renaming, lift_bound_subst.
        rewrite !view_member_here. cbn [rename_bound_expr rename_bound_ref].
        unfold lift_bound_renaming. rewrite view_member_here. reflexivity.
      * rewrite lift_bound_renaming_there.
        unfold lift_bound_subst. rewrite !view_member_there.
        rewrite rename_bound_expr_lift_weaken, Hsubst. reflexivity.
  - rewrite (subst_bound_expr_rename_both source_renaming target_renaming
      substitution renamed_substitution Hsubst condition).
    rewrite (IHformula1 Θ Δ' Θ' source_renaming target_renaming
      substitution renamed_substitution Hsubst).
    rewrite (IHformula2 Θ Δ' Θ' source_renaming target_renaming
      substitution renamed_substitution Hsubst).
    destruct (subst_bound_assertion substitution formula1);
      destruct (subst_bound_assertion substitution formula2); reflexivity.
  - rewrite (subst_bound_expr_list_rename_both source_renaming target_renaming
      substitution renamed_substitution Hsubst args). reflexivity.
  - rewrite (subst_bound_expr_list_rename_both source_renaming target_renaming
      substitution renamed_substitution Hsubst args). reflexivity.
  - rewrite (IHformula1 Θ Δ' Θ' source_renaming target_renaming
      substitution renamed_substitution Hsubst).
    rewrite (IHformula2 Θ Δ' Θ' source_renaming target_renaming
      substitution renamed_substitution Hsubst).
    destruct (subst_bound_assertion substitution formula1);
      destruct (subst_bound_assertion substitution formula2); reflexivity.
Qed.

Lemma instantiate_bound_assertion_rename
    {Γ F Δ Δ' t}
    (renaming : bound_renaming Δ Δ')
    (witness : expr F Δ t)
    (body : assertion Γ F (t :: Δ)) :
  instantiate_bound_assertion (rename_bound_expr renaming witness)
      (rename_bound_assertion (lift_bound_renaming renaming) body) =
  match instantiate_bound_assertion witness body with
  | Some result => Some (rename_bound_assertion renaming result)
  | None => None
  end.
Proof.
  unfold instantiate_bound_assertion.
  apply subst_bound_assertion_rename_both.
  intros u variable. dependent destruction variable.
  - rewrite lift_bound_renaming_here.
    unfold head_bound_subst. rewrite !view_member_here. reflexivity.
  - rewrite lift_bound_renaming_there.
    unfold head_bound_subst. rewrite !view_member_there.
    cbn [rename_bound_expr rename_bound_ref]. reflexivity.
Qed.

Lemma assertion_entails_rename {Γ F Δ Θ}
    (target_renaming : bound_renaming Δ Θ)
    (left right : assertion Γ F Δ) :
  assertion_entails left right ->
  assertion_entails (rename_bound_assertion target_renaming left)
    (rename_bound_assertion target_renaming right).
Proof.
  intro Hentails. revert Θ target_renaming.
  induction Hentails; intros Θ target_renaming;
    cbn [rename_bound_assertion].
  - apply EntailsRefl.
  - apply EntailsStep. now apply entailment_step_rename.
  - eapply EntailsTrans; eauto.
  - apply EntailsAndMono; eauto.
  - apply EntailsExistsMono. apply IHHentails.
  - eapply EntailsExistsIntro with
      (witness := rename_bound_expr target_renaming witness).
    rewrite instantiate_bound_assertion_rename, H. reflexivity.
  - apply EntailsExistsElim.
    rewrite <- rename_bound_assertion_lift_weaken. apply IHHentails.
  - rewrite rename_bound_assertion_lift_weaken.
    apply EntailsExistsAndRight.
  - rewrite rename_bound_assertion_lift_weaken.
    apply EntailsExistsAndRightOut.
  - rewrite rename_bound_assertion_lift_weaken.
    apply EntailsAndExistsLeft.
  - apply EntailsIteMono; [apply IHHentails1|apply IHHentails2].
  - rewrite rename_bound_assertion_lift_weaken.
    apply EntailsExistsVacuousIntro.
  - rewrite rename_bound_expr_lift_weaken.
    apply EntailsExistsIteOut.
  - rewrite rename_bound_expr_lift_weaken.
    apply EntailsIteExistsIn.
  - rewrite rename_bound_assertion_exchange_natural.
    apply EntailsExistsSwap.
  - apply EntailsForallMono. apply IHHentails.
Qed.
Lemma reindex_stack_context_stack_free {F Δ Γ Γ'}
    (source : assertion Γ F Δ) (target : assertion Γ' F Δ) :
  reindex_stack_context source target ->
  stack_free source ->
  stack_free target.
Proof.
  intro Hreindex.
  induction Hreindex; intro Hfree;
    dependent destruction Hfree; try constructor; eauto.
Qed.
(** Renaming algebra for the resource core.  Contract-independent, and
    needed both by the erasure and by concrete contract environments. *)
Lemma subst_formals_core_rename {F F' Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (substitution : formal_subst F F' Δ) (formula : Resource.core_assertion F Δ) :
  Resource.subst_formals_core (rename_formal_subst renaming substitution)
      (Resource.rename_bound_core renaming formula) =
    Resource.rename_bound_core renaming (Resource.subst_formals_core substitution formula).
Proof.
  revert F' Δ' renaming substitution.
  induction formula; intros F' Δ' renaming substitution;
    cbn [Resource.subst_formals_core Resource.rename_bound_core];
    rewrite ?subst_formals_expr_rename,
            ?subst_formals_expr_list_rename;
    try reflexivity.
  all: f_equal.
  all: try (rewrite <- rename_formal_subst_lift; apply IHformula).
  all: eauto.
Qed.

Lemma subst_bound_core_rename {F Δ Δ' Δ''}
    (renaming : bound_renaming Δ' Δ'')
    (substitution : bound_subst F Δ Δ') (formula : Resource.core_assertion F Δ) :
  Resource.subst_bound_core (rename_bound_subst renaming substitution)
      formula =
    Resource.rename_bound_core renaming (Resource.subst_bound_core substitution formula).
Proof.
  revert Δ' Δ'' renaming substitution.
  induction formula; intros Δ' Δ'' renaming substitution;
    cbn [Resource.subst_bound_core Resource.rename_bound_core];
    rewrite ?subst_bound_expr_rename,
            ?subst_bound_expr_list_rename;
    try reflexivity.
  all: f_equal.
  all: try (rewrite <- rename_bound_subst_lift; apply IHformula).
  all: eauto.
Qed.

(** Lifting a closed body into a binder context is renaming-invariant:
    there are no bound variables to rename. *)
Lemma weaken_core_to_rename {F Δ Δ'} (renaming : bound_renaming Δ Δ')
    (formula : Resource.core_assertion F []) :
  Resource.rename_bound_core renaming (Resource.weaken_core_to Δ formula) =
    Resource.weaken_core_to Δ' formula.
Proof.
  unfold Resource.weaken_core_to. rewrite <- subst_bound_core_rename.
  apply Resource.subst_bound_core_ext. intros t variable.
  dependent destruction variable.
Qed.

End RenamingFacts.

(** Canonical instantiation of a selected procedure contract in the caller's
    logical context. *)
Definition procedure_pre_instantiation {callee_variables identity}
    (procedure : typed_procedure callee_variables identity)
    {F Δ}
    (arguments : expr_list F Δ (Logic.procedure_args identity)) :
    Resource.core_assertion F Δ :=
  Resource.subst_formals_core (expr_list_formal_subst arguments)
    (Resource.weaken_core_to Δ (procedure_precondition _ _ procedure)).

(** Close every ambient logical binder existentially. *)
Fixpoint existentially_close_assertion {Γ F Δ}
    (formula : assertion Γ F Δ) : assertion Γ F [] :=
  match Δ as Δ0 return assertion Γ F Δ0 -> assertion Γ F [] with
  | [] => fun formula => formula
  | t :: tail => fun formula =>
      @existentially_close_assertion Γ F tail (AExists t formula)
  end formula.

Fixpoint existentially_close_prenex_at {Γ F} (Δ : context)
    (prenex : Resource.resource_prenex Γ F Δ) :
    Resource.resource_prenex Γ F [] :=
  match Δ as Δ0 return Resource.resource_prenex Γ F Δ0 ->
      Resource.resource_prenex Γ F [] with
  | [] => fun prenex => prenex
  | t :: tail => fun prenex =>
      existentially_close_prenex_at tail (Resource.ResourceExists t prenex)
  end prenex.

Definition existentially_close_prenex {Γ F Δ}
    (prenex : Resource.resource_prenex Γ F Δ) :
    Resource.resource_prenex Γ F [] :=
  existentially_close_prenex_at Δ prenex.

(** Canonical resource assertions at a procedure boundary. *)
Definition procedure_body_pre {Γ identity}
    (procedure : typed_procedure Γ identity) :
    Resource.resource_prenex Γ (Logic.procedure_args identity) [] :=
  Resource.RState (procedure_entry_store _ _ procedure)
    (procedure_precondition _ _ procedure).

Definition procedure_body_post {Γ identity Δ}
    (procedure : typed_procedure Γ identity)
    (exit_store : symbolic_store Γ (Logic.procedure_args identity) Δ)
    (return_reference : value_ref (Logic.procedure_args identity) Δ
      (Logic.procedure_return identity)) :
    Resource.resource_prenex Γ (Logic.procedure_args identity) [] :=
  existentially_close_prenex
    (Resource.RState exit_store
      (Resource.subst_bound_core
        (singleton_bound_subst return_reference)
        (procedure_postcondition _ _ procedure))).

(** Coherence between the authoritative resource-contract environment and
    the typed procedure table.  The environment identifies the logical
    contract and analyzer-visible masks of each procedure; this interface
    connects those declarations to the concrete typed procedure selected by
    the executable table. *)
Module Type PROCEDURE_CONTRACT_COHERENCE
    (RC : ResourceHoare.RESOURCE_CONTRACT_ENV_BASE).
  Parameter procedures : typed_procedure_environment.
  Parameter declared_required_mask : packed_typed_procedure -> mask.
  Parameter declared_granted_mask : packed_typed_procedure -> mask.

  (** Every procedure admitted by the contract environment has a typed
      declaration in the executable table.  The dependent witness can be
      obtained by the computable lookup [lookup_typed_procedure_at]. *)
  Parameter procedure_selects : forall identity,
    RC.procedure_verified identity ->
    { callee_variables : context &
      { procedure : typed_procedure callee_variables identity |
        lookup_typed_procedure procedures identity =
          Some (pack_typed_procedure procedure) } }.

  Parameter required_mask_coherent : forall identity procedure,
    lookup_typed_procedure procedures identity = Some procedure ->
    RC.required_mask identity = declared_required_mask procedure.
  Parameter granted_mask_coherent : forall identity procedure,
    lookup_typed_procedure procedures identity = Some procedure ->
    RC.granted_mask identity = declared_granted_mask procedure.

  (** The declared contract *is* the callee's contract.  Both are core
      assertions at the same indices, so these are equations. *)
  Parameter contract_pre_coherent : forall callee_variables identity
      (procedure : typed_procedure callee_variables identity),
    lookup_typed_procedure procedures identity =
      Some (pack_typed_procedure procedure) ->
    RC.contract_pre identity = procedure_precondition _ _ procedure.
  Parameter contract_post_coherent : forall callee_variables identity
      (procedure : typed_procedure callee_variables identity),
    lookup_typed_procedure procedures identity =
      Some (pack_typed_procedure procedure) ->
    RC.contract_post identity = procedure_postcondition _ _ procedure.
End PROCEDURE_CONTRACT_COHERENCE.

End Make.
End TypedHoare.
