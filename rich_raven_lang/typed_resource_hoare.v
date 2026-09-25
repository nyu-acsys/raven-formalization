From Coq Require Import List PArith Program.Equality ProofIrrelevance
  Logic.FunctionalExtensionality String ZArith Lia.
From stdpp Require Import gmap sets.

From raven_iris.rich_raven_lang Require Import typed_core typed_assertion
  typed_resource typed_ir.

Import ListNotations.
Open Scope list_scope.

(** * The resource Hoare calculus

    Statement rules inspect and update an explicit [resource_stack]; frame
    and ordinary consequence accept only a [core_assertion]; resource
    binders live in a telescope rather than under an [AExists] wrapped
    around a stack.

    What is absent, by typing rather than by proof:

      - no [assertion_stack_count] or [<= 1] linearity hypothesis;
      - no [stack_free] side condition on any frame, invariant body,
        contract or allocation resource;
      - no [ESStackExclusive]: two stacks in one assertion is unstatable,
        so the rule that derived [False] from it has nothing to fire on;
      - no store-join operation.  The baseline conditional requires one
        common output resource assertion, and the monotonic counter needs
        no join (measured: zero cases).

    This module sits between [typed_ir] and [typed_hoare] in the chain, so
    the old and new calculi share one instance of the substrate while both
    exist. *)

Module TypedResourceHoare.

Module Make (RAs : TypedCore.RA_VALUE_CONFIG)
    (Logic : TypedAssertion.LOGIC_SIGNATURE).
Module IR := TypedIR.Make RAs Logic.
Module Resource := IR.Resource.
Module Assertions := IR.Assertions.
Module Core := IR.Core.
Import TypedCore Core Assertions Resource IR.

(** Argument stability belongs to the resource rule's interface.  The
    normalizer and analyzer reuse these definitions rather than maintaining a
    second, potentially divergent write-footprint computation. *)
Fixpoint pexpr_dependencies {Γ t} (expression : pexpr Γ t) : gset nat :=
  match expression with
  | PEVar variable => {[member_index variable]}
  | PEVal _ => ∅
  | PEUnOp _ operand => pexpr_dependencies operand
  | PEBinOp _ operand1 operand2 =>
      pexpr_dependencies operand1 ∪ pexpr_dependencies operand2
  end.

Fixpoint pexpr_list_dependencies {Γ ts}
    (expressions : pexpr_list Γ ts) : gset nat :=
  match expressions with
  | PENil => ∅
  | PECons expression tail =>
      pexpr_dependencies expression ∪ pexpr_list_dependencies tail
  end.

Lemma pexpr_list_dependencies_append {Γ left_types right_types}
    (left : pexpr_list Γ left_types) (right : pexpr_list Γ right_types) :
  pexpr_list_dependencies (IR.pexpr_list_append left right) =
    pexpr_list_dependencies left ∪ pexpr_list_dependencies right.
Proof.
  induction left as [|t ts expression tail IH]; simpl.
  - apply set_eq. intros slot. rewrite elem_of_union.
    split.
    + intro Hslot. right. exact Hslot.
    + intros [Hempty | Hslot].
      * rewrite elem_of_empty in Hempty. contradiction.
      * exact Hslot.
  - rewrite IH. apply set_eq. intros slot.
    repeat rewrite elem_of_union. tauto.
Qed.

Fixpoint statement_writes {Γ} (statement : stmt Γ) : gset nat :=
  match statement with
  | TAssign _ target _ | TFieldRead _ _ target _ | TAlloc _ target _ =>
      {[member_index target]}
  | TCall _ _ _ (CTStore target) => {[member_index target]}
  | TInvAccess _ _ body | TAtomic _ body => statement_writes body
  | TIf _ _ then_branch else_branch | TSeq _ then_branch else_branch =>
      statement_writes then_branch ∪ statement_writes else_branch
  | _ => ∅
  end.

(* ------------------------------------------------------------------ *)
(** ** 1. Core entailment

    The rules of [TypedHoare.entailment_step] / [assertion_entails] minus
    [ESStackExclusive], and with the [Γ] index gone.  [CEntailsExistsIntro]
    also loses its [= Some _] premise, because instantiation is total on
    core assertions. *)

Inductive core_entailment_step {F Δ} :
    core_assertion F Δ -> core_assertion F Δ -> Prop :=
| CESAndComm left right :
    core_entailment_step (CAnd left right) (CAnd right left)
| CESAndAssocR first second third :
    core_entailment_step (CAnd (CAnd first second) third)
      (CAnd first (CAnd second third))
| CESAndAssocL first second third :
    core_entailment_step (CAnd first (CAnd second third))
      (CAnd (CAnd first second) third)
| CESAndElimL left right : core_entailment_step (CAnd left right) left
| CESAndElimR left right : core_entailment_step (CAnd left right) right
| CESAndTrueIntro formula :
    core_entailment_step formula (CAnd formula (CPure True))
| CESTrueIntro formula : core_entailment_step formula (CPure True)
| CESPure (left right : Prop) :
    (left -> right) -> core_entailment_step (CPure left) (CPure right)
| CESIteTrue condition then_branch else_branch :
    core_entailment_step (CAnd (CIte condition then_branch else_branch)
      (CExpr condition)) then_branch
| CESIteFalse condition then_branch else_branch :
    core_entailment_step
      (CAnd (CIte condition then_branch else_branch)
        (CExpr (EUnOp UNot condition))) else_branch
| CESIteIntroTrue condition then_branch else_branch :
    core_entailment_step (CAnd then_branch (CExpr condition))
      (CIte condition then_branch else_branch)
| CESIteIntroFalse condition then_branch else_branch :
    core_entailment_step
      (CAnd else_branch (CExpr (EUnOp UNot condition)))
      (CIte condition then_branch else_branch)
| CESIteBoolTrue condition then_branch else_branch indicator :
    core_entailment_step
      (CAnd
        (CIte condition
          (CAnd then_branch
            (CExpr (EBinOp (BEq TBool) indicator (EVal (VBool true)))))
          (CAnd else_branch
            (CExpr (EBinOp (BEq TBool) indicator (EVal (VBool false))))))
        (CExpr indicator))
      (CAnd then_branch (CExpr condition))
| CESIteBoolFalse condition then_branch else_branch indicator :
    core_entailment_step
      (CAnd
        (CIte condition
          (CAnd then_branch
            (CExpr (EBinOp (BEq TBool) indicator (EVal (VBool true)))))
          (CAnd else_branch
            (CExpr (EBinOp (BEq TBool) indicator (EVal (VBool false))))))
        (CExpr (EUnOp UNot indicator)))
      else_branch
| CESExprImpl (left right : expr F Δ TBool) :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms left = Some (VBool true) ->
      interp_expr formals binders atoms right = Some (VBool true)) ->
    core_entailment_step (CExpr left) (CExpr right)
| CESExprTrue (expression : expr F Δ TBool) :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms expression = Some (VBool true)) ->
    core_entailment_step (CPure True) (CExpr expression)
| CESRAValidTrue t (expression : expr F Δ t) :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env) value,
      interp_expr formals binders atoms expression = Some value ->
      tval_ra_valid value) ->
    core_entailment_step (CPure True) (CRAValid t expression)
| CESFpuAllowedTrue t (old_expression new_expression : expr F Δ t) :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env) old_value new_value,
      interp_expr formals binders atoms old_expression = Some old_value ->
      interp_expr formals binders atoms new_expression = Some new_value ->
      tval_fpu_allowed old_value new_value) ->
    core_entailment_step (CPure True)
      (CFpuAllowed t old_expression new_expression)
| CESOwnChunkEq field location left_chunk right_chunk :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms left_chunk =
        interp_expr formals binders atoms right_chunk) ->
    core_entailment_step (COwn field location left_chunk)
      (COwn field location right_chunk)
| CESGhostOwnChunkEq field location left_chunk right_chunk :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms left_chunk =
        interp_expr formals binders atoms right_chunk) ->
    core_entailment_step (CGhostOwn field location left_chunk)
      (CGhostOwn field location right_chunk)
| CESOwnChunkEqAssume field location left_chunk right_chunk condition :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms condition = Some (VBool true) ->
      interp_expr formals binders atoms left_chunk =
        interp_expr formals binders atoms right_chunk) ->
    core_entailment_step
      (CAnd (COwn field location left_chunk) (CExpr condition))
      (COwn field location right_chunk)
| CESGhostOwnChunkEqAssume field location left_chunk right_chunk condition :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms condition = Some (VBool true) ->
      interp_expr formals binders atoms left_chunk =
        interp_expr formals binders atoms right_chunk) ->
    core_entailment_step
      (CAnd (CGhostOwn field location left_chunk) (CExpr condition))
      (CGhostOwn field location right_chunk)
| CESInvariantArgumentsEqAssume invariant
    (left_arguments right_arguments :
      expr_list F Δ (Logic.invariant_args invariant))
    (condition : expr F Δ TBool) :
    expr_list_equal_assuming condition _ left_arguments right_arguments ->
    core_entailment_step
      (CAnd (CInvariant invariant left_arguments) (CExpr condition))
      (CInvariant invariant right_arguments)
| CESPredicateArgumentsEqAssume predicate
    (left_arguments right_arguments :
      expr_list F Δ (Logic.predicate_args predicate))
    (condition : expr F Δ TBool) :
    expr_list_equal_assuming condition _ left_arguments right_arguments ->
    core_entailment_step
      (CAnd (CPredicate predicate left_arguments) (CExpr condition))
      (CPredicate predicate right_arguments).

Inductive core_entails {F} : forall {Δ},
    core_assertion F Δ -> core_assertion F Δ -> Prop :=
| CEntailsRefl {Δ : context} (formula : core_assertion F Δ) :
    core_entails formula formula
| CEntailsStep {Δ : context} (left right : core_assertion F Δ) :
    core_entailment_step left right ->
    core_entails left right
| CEntailsTrans {Δ : context}
    (first second third : core_assertion F Δ) :
    core_entails first second -> core_entails second third ->
    core_entails first third
| CEntailsAndMono {Δ : context}
    (left left' right right' : core_assertion F Δ) :
    core_entails left left' -> core_entails right right' ->
    core_entails (CAnd left right) (CAnd left' right')
| CEntailsExistsMono {Δ : context} t (body body' : core_assertion F (t :: Δ)) :
    core_entails body body' ->
    core_entails (CExists t body) (CExists t body')
| CEntailsExistsIntro {Δ : context} t
    (body : core_assertion F (t :: Δ)) witness :
    (* no [= Some _] premise: instantiation is total on core assertions *)
    core_entails (Resource.instantiate_bound_core witness body)
      (CExists t body)
| CEntailsExistsElim {Δ : context} t
    (body : core_assertion F (t :: Δ))
    (conclusion : core_assertion F Δ) :
    core_entails body (Resource.weaken_core conclusion) ->
    core_entails (CExists t body) conclusion
| CEntailsExistsAndRight {Δ : context} t
    (body : core_assertion F (t :: Δ)) (frame : core_assertion F Δ) :
    core_entails
      (CAnd (CExists t body) frame)
      (CExists t (CAnd body (Resource.weaken_core frame)))
| CEntailsExistsAndRightOut {Δ : context} t
    (body : core_assertion F (t :: Δ)) (frame : core_assertion F Δ) :
    core_entails
      (CExists t (CAnd body (Resource.weaken_core frame)))
      (CAnd (CExists t body) frame)
| CEntailsAndExistsLeft {Δ : context} t (frame : core_assertion F Δ)
    (body : core_assertion F (t :: Δ)) :
    core_entails
      (CAnd frame (CExists t body))
      (CExists t (CAnd (Resource.weaken_core frame) body))
| CEntailsIteMono {Δ : context} (condition : expr F Δ TBool)
    (then_branch then_branch' else_branch else_branch' : core_assertion F Δ) :
    core_entails then_branch then_branch' ->
    core_entails else_branch else_branch' ->
    core_entails (CIte condition then_branch else_branch)
      (CIte condition then_branch' else_branch')
| CEntailsExistsVacuousIntro {Δ : context} t
    (formula : core_assertion F Δ) :
    core_entails formula (CExists t (Resource.weaken_core formula))
| CEntailsExistsIteOut {Δ : context} t (condition : expr F Δ TBool)
    (then_branch else_branch : core_assertion F (t :: Δ)) :
    core_entails
      (CExists t
        (CIte (weaken_expr condition) then_branch else_branch))
      (CIte condition (CExists t then_branch) (CExists t else_branch))
| CEntailsIteExistsIn {Δ : context} t (condition : expr F Δ TBool)
    (then_branch else_branch : core_assertion F (t :: Δ)) :
    core_entails
      (CIte condition (CExists t then_branch) (CExists t else_branch))
      (CExists t
        (CIte (weaken_expr condition) then_branch else_branch))
| CEntailsExistsSwap {Δ : context} t u
    (body : core_assertion F (u :: t :: Δ)) :
    core_entails
      (CExists t (CExists u body))
      (CExists u (CExists t
        (Resource.rename_bound_core
          (@exchange_bound_renaming Δ u t) body)))
| CEntailsForallMono {Δ : context} t
    (body body' : core_assertion F (t :: Δ)) :
    core_entails body body' ->
    core_entails (CForall t body) (CForall t body').

Lemma core_entails_exists_and_left_out {F Δ t}
    (frame : core_assertion F Δ) (body : core_assertion F (t :: Δ)) :
  core_entails
    (CExists t (CAnd (Resource.weaken_core frame) body))
    (CAnd frame (CExists t body)).
Proof.
  eapply CEntailsTrans.
  - apply CEntailsExistsMono, CEntailsStep, CESAndComm.
  - eapply CEntailsTrans.
    + apply CEntailsExistsAndRightOut.
    + apply CEntailsStep, CESAndComm.
Qed.

Lemma core_existential_prenex_and_right_entails {F Δ}
    (left : core_assertion F Δ)
    (right : Resource.core_existential_prenex F Δ) :
  core_entails
    (CAnd left (Resource.interp_core_existential_prenex right))
    (Resource.interp_core_existential_prenex
      (Resource.core_existential_prenex_and_right left right)).
Proof.
  revert left. induction right; intro left; cbn.
  - apply CEntailsRefl.
  - eapply CEntailsTrans.
    + apply CEntailsAndExistsLeft.
    + apply CEntailsExistsMono, IHright.
Qed.

Lemma core_existential_prenex_and_right_entails_back {F Δ}
    (left : core_assertion F Δ)
    (right : Resource.core_existential_prenex F Δ) :
  core_entails
    (Resource.interp_core_existential_prenex
      (Resource.core_existential_prenex_and_right left right))
    (CAnd left (Resource.interp_core_existential_prenex right)).
Proof.
  revert left. induction right; intro left; cbn.
  - apply CEntailsRefl.
  - eapply CEntailsTrans.
    + apply CEntailsExistsMono, IHright.
    + apply core_entails_exists_and_left_out.
Qed.

Lemma core_existential_prenex_and_entails {F Δ}
    (left right : Resource.core_existential_prenex F Δ) :
  core_entails
    (CAnd (Resource.interp_core_existential_prenex left)
      (Resource.interp_core_existential_prenex right))
    (Resource.interp_core_existential_prenex
      (Resource.core_existential_prenex_and left right)).
Proof.
  revert right. induction left; intro right; cbn.
  - apply core_existential_prenex_and_right_entails.
  - eapply CEntailsTrans.
    + apply CEntailsExistsAndRight.
    + apply CEntailsExistsMono.
      pose proof (IHleft
        (Resource.weaken_core_existential_prenex right)) as Hinduction.
      unfold Resource.weaken_core_existential_prenex in Hinduction.
      rewrite Resource.interp_rename_core_existential_prenex in Hinduction.
      exact Hinduction.
Qed.

Lemma core_existential_prenex_and_entails_back {F Δ}
    (left right : Resource.core_existential_prenex F Δ) :
  core_entails
    (Resource.interp_core_existential_prenex
      (Resource.core_existential_prenex_and left right))
    (CAnd (Resource.interp_core_existential_prenex left)
      (Resource.interp_core_existential_prenex right)).
Proof.
  revert right. induction left; intro right; cbn.
  - apply core_existential_prenex_and_right_entails_back.
  - eapply CEntailsTrans.
    + apply CEntailsExistsMono.
      pose proof (IHleft
        (Resource.weaken_core_existential_prenex right)) as Hinduction.
      unfold Resource.weaken_core_existential_prenex in Hinduction.
      rewrite Resource.interp_rename_core_existential_prenex in Hinduction.
      exact Hinduction.
    + apply CEntailsExistsAndRightOut.
Qed.

Lemma core_entails_exists_vacuous_out {F Δ t}
    (formula : core_assertion F Δ) :
  core_entails (CExists t (Resource.weaken_core formula)) formula.
Proof.
  apply CEntailsExistsElim, CEntailsRefl.
Qed.

Lemma core_existential_prenex_ite_else_entails {F Δ}
    (condition : expr F Δ TBool) (then_branch : core_assertion F Δ)
    (else_branch : Resource.core_existential_prenex F Δ) :
  core_entails
    (CIte condition then_branch
      (Resource.interp_core_existential_prenex else_branch))
    (Resource.interp_core_existential_prenex
      (Resource.core_existential_prenex_ite_else condition then_branch
        else_branch)).
Proof.
  revert condition then_branch.
  induction else_branch; intros condition then_branch; cbn.
  - apply CEntailsRefl.
  - eapply CEntailsTrans.
    + apply CEntailsIteMono.
      * apply CEntailsExistsVacuousIntro.
      * apply CEntailsRefl.
    + eapply CEntailsTrans.
      * apply CEntailsIteExistsIn.
      * apply CEntailsExistsMono, IHelse_branch.
Qed.

Lemma core_existential_prenex_ite_else_entails_back {F Δ}
    (condition : expr F Δ TBool) (then_branch : core_assertion F Δ)
    (else_branch : Resource.core_existential_prenex F Δ) :
  core_entails
    (Resource.interp_core_existential_prenex
      (Resource.core_existential_prenex_ite_else condition then_branch
        else_branch))
    (CIte condition then_branch
      (Resource.interp_core_existential_prenex else_branch)).
Proof.
  revert condition then_branch.
  induction else_branch; intros condition then_branch; cbn.
  - apply CEntailsRefl.
  - eapply CEntailsTrans.
    + apply CEntailsExistsMono, IHelse_branch.
    + eapply CEntailsTrans.
      * apply CEntailsExistsIteOut.
      * apply CEntailsIteMono.
        -- apply core_entails_exists_vacuous_out.
        -- apply CEntailsRefl.
Qed.

Lemma core_existential_prenex_ite_entails {F Δ}
    (condition : expr F Δ TBool)
    (then_branch else_branch : Resource.core_existential_prenex F Δ) :
  core_entails
    (CIte condition
      (Resource.interp_core_existential_prenex then_branch)
      (Resource.interp_core_existential_prenex else_branch))
    (Resource.interp_core_existential_prenex
      (Resource.core_existential_prenex_ite condition then_branch
        else_branch)).
Proof.
  revert condition else_branch.
  induction then_branch; intros condition else_branch; cbn.
  - apply core_existential_prenex_ite_else_entails.
  - eapply CEntailsTrans.
    + apply CEntailsIteMono.
      * apply CEntailsRefl.
      * apply CEntailsExistsVacuousIntro.
    + eapply CEntailsTrans.
      * apply CEntailsIteExistsIn.
      * apply CEntailsExistsMono.
        pose proof (IHthen_branch (weaken_expr condition)
          (Resource.weaken_core_existential_prenex else_branch))
          as Hinduction.
        unfold Resource.weaken_core_existential_prenex in Hinduction.
        rewrite Resource.interp_rename_core_existential_prenex in Hinduction.
        exact Hinduction.
Qed.

Lemma core_existential_prenex_ite_entails_back {F Δ}
    (condition : expr F Δ TBool)
    (then_branch else_branch : Resource.core_existential_prenex F Δ) :
  core_entails
    (Resource.interp_core_existential_prenex
      (Resource.core_existential_prenex_ite condition then_branch
        else_branch))
    (CIte condition
      (Resource.interp_core_existential_prenex then_branch)
      (Resource.interp_core_existential_prenex else_branch)).
Proof.
  revert condition else_branch.
  induction then_branch; intros condition else_branch; cbn.
  - apply core_existential_prenex_ite_else_entails_back.
  - eapply CEntailsTrans.
    + apply CEntailsExistsMono.
      pose proof (IHthen_branch (weaken_expr condition)
        (Resource.weaken_core_existential_prenex else_branch))
        as Hinduction.
      unfold Resource.weaken_core_existential_prenex in Hinduction.
      rewrite Resource.interp_rename_core_existential_prenex in Hinduction.
      exact Hinduction.
    + eapply CEntailsTrans.
      * apply CEntailsExistsIteOut.
      * apply CEntailsIteMono.
        -- apply CEntailsRefl.
        -- apply core_entails_exists_vacuous_out.
Qed.

Theorem normalize_core_existential_prenex_entails {F Δ}
    (formula : core_assertion F Δ) :
  core_entails formula
    (Resource.interp_core_existential_prenex
      (Resource.normalize_core_existential_prenex formula)).
Proof.
  induction formula; cbn; try apply CEntailsRefl.
  - apply CEntailsExistsMono. exact IHformula.
  - apply CEntailsForallMono. exact IHformula.
  - eapply CEntailsTrans.
    + apply CEntailsIteMono; eassumption.
    + apply core_existential_prenex_ite_entails.
  - eapply CEntailsTrans.
    + apply CEntailsAndMono; eassumption.
    + apply core_existential_prenex_and_entails.
Qed.

Theorem normalize_core_existential_prenex_entails_back {F Δ}
    (formula : core_assertion F Δ) :
  core_entails
    (Resource.interp_core_existential_prenex
      (Resource.normalize_core_existential_prenex formula)) formula.
Proof.
  induction formula; cbn; try apply CEntailsRefl.
  - apply CEntailsExistsMono. exact IHformula.
  - apply CEntailsForallMono. exact IHformula.
  - eapply CEntailsTrans.
    + apply core_existential_prenex_ite_entails_back.
    + apply CEntailsIteMono; eassumption.
  - eapply CEntailsTrans.
    + apply core_existential_prenex_and_entails_back.
    + apply CEntailsAndMono; eassumption.
Qed.
(** *** Erasure into the old entailment

    Each core rule is the corresponding assertion rule on the embedded
    image.  This is what lets the validity slice reuse
    [TypedValidity.assertion_entails_valid] — a 260-line semantic theorem —
    instead of reproving entailment soundness for the core grammar. *)

Lemma core_entailment_step_erases {F Δ} (left right : core_assertion F Δ) :
  core_entailment_step left right ->
  forall Γ, entailment_step (@core_to_assertion Γ F Δ left)
    (core_to_assertion right).
Proof.
  intro Hstep; induction Hstep; intro Γ; cbn [core_to_assertion];
    econstructor; eauto using core_to_assertion_stack_free.
Qed.

Lemma core_entails_erases {F Δ} (left right : core_assertion F Δ) :
  core_entails left right ->
  forall Γ, assertion_entails (@core_to_assertion Γ F Δ left)
    (core_to_assertion right).
Proof.
  intro Hentails; induction Hentails; intro Γ; cbn [core_to_assertion];
    rewrite ?core_to_assertion_weaken, ?core_to_assertion_rename in *.
  all: try (econstructor;
    eauto using core_entailment_step_erases, core_to_assertion_stack_free;
    fail).
  - eapply EntailsExistsIntro. apply instantiate_bound_core_to_assertion.
  - apply EntailsExistsElim. rewrite <- core_to_assertion_weaken.
    apply IHHentails.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 2. The resource entailment boundary

    Ordinary consequence preserves the explicit stack and uses core
    entailment for the remainder.  A change of symbolic store is a
    separate structural rule, never an assertion entailment. *)

Definition resource_entails {Γ F Δ}
    (left right : resource_assertion Γ F Δ) : Prop :=
  resource_stack left = resource_stack right /\
  core_entails (resource_body left) (resource_body right).

Inductive resource_prenex_entails {Γ F} : forall {Δ},
    resource_prenex Γ F Δ -> resource_prenex Γ F Δ -> Prop :=
| RPEBody {Δ} (left right : resource_assertion Γ F Δ) :
    resource_entails left right ->
    resource_prenex_entails (ResourceBody left) (ResourceBody right)
| RPEMono {Δ} t (left right : resource_prenex Γ F (t :: Δ)) :
    resource_prenex_entails left right ->
    resource_prenex_entails (ResourceExists t left) (ResourceExists t right)
(** A resource binder may be instantiated only at a witness a
    symbolic-store slot can hold, i.e. a [value_ref].  Stated at the
    innermost binder; [RPEMono] composes to reach any binder.  The rejected
    unrestricted current-witness rule is not recoverable from this. *)
| RPEIntro {Δ} t (witness : value_ref F Δ t)
    (state : resource_assertion Γ F (t :: Δ)) :
    resource_prenex_entails
      (ResourceBody (subst_bound_resource
        (head_bound_ref_subst witness) state))
      (ResourceExists t (ResourceBody state))
(** Moving a *core* existential into the telescope.

    Separating the stack from the assertion body leaves a gap the mixed
    grammar did not have: an invariant body is a [core_assertion], so
    unfolding one yields [RState store (CExists t body)], while every
    rule that works under a binder -- and [RTPrenexElim] itself --
    requires the binder to sit in the telescope.  Nothing else bridges
    the two: [RPEIntro] is existential *introduction* at a witness, and
    [RTConsequence] weakens a precondition only through [core_entails],
    which cannot cross the [RState] boundary.

    Semantically this is [∗] distributing over [∃]:

      stack(store) ∗ (∃ x, body x)  ⊢  ∃ x, stack(weaken_store store) ∗ body x

    and it needs no witness and no inhabitation assumption, because the
    witness comes from the core existential already present.  Weakening
    the store is what makes it sound: the store cannot mention the new
    binder, which is exactly the invariant the split representation
    maintains.  Stack exclusivity is untouched -- there is still exactly
    one [RState] under every telescope branch.

    The framed shape is covered without a second constructor:
    [CEntailsExistsAndRight] turns [CAnd (CExists t body) frame] into
    [CExists t (CAnd body (weaken_core frame))] first.

    [RPECloseCoreExists] provides the converse.  It was not needed by the
    first operational examples, but the derivation preprocessing pass needs
    genuine equivalence when it canonicalizes both sides of every sequence
    boundary. *)
| RPEOpenCoreExists {Δ} t (store : symbolic_store Γ F Δ)
    (body : core_assertion F (t :: Δ)) :
    resource_prenex_entails
      (RState store (CExists t body))
      (ResourceExists t (RState (weaken_store store) body))
| RPECloseCoreExists {Δ} t (store : symbolic_store Γ F Δ)
    (body : core_assertion F (t :: Δ)) :
    resource_prenex_entails
      (ResourceExists t (RState (weaken_store store) body))
      (RState store (CExists t body))
| RPEVacuous {Δ} t (body : resource_prenex Γ F Δ) :
    resource_prenex_entails
      (ResourceExists t (weaken_resource_prenex body)) body
| RPETrans {Δ} (first second third : resource_prenex Γ F Δ) :
    resource_prenex_entails first second ->
    resource_prenex_entails second third ->
    resource_prenex_entails first third
| RPERename {Δ Δ'} (renaming : bound_renaming Δ Δ')
    (left right : resource_prenex Γ F Δ) :
    resource_prenex_entails left right ->
    resource_prenex_entails
      (Resource.rename_resource_prenex left Δ' renaming)
      (Resource.rename_resource_prenex right Δ' renaming)
| RPEUnderExists {Δ} t (body : resource_prenex Γ F (t :: Δ))
    (target : resource_prenex Γ F Δ) :
    resource_prenex_entails (ResourceExists t body) target ->
    resource_prenex_entails body (Resource.weaken_resource_prenex target).

Lemma resource_entails_refl {Γ F Δ} (state : resource_assertion Γ F Δ) :
  resource_entails state state.
Proof. split; [reflexivity | apply CEntailsRefl]. Qed.

Lemma resource_prenex_entails_refl {Γ F Δ} (prenex : resource_prenex Γ F Δ) :
  resource_prenex_entails prenex prenex.
Proof.
  induction prenex as [Δ state | Δ t rest IH].
  - apply RPEBody, resource_entails_refl.
  - apply RPEMono, IH.
Qed.

Lemma resource_prenex_entails_frame_true_intro {Γ F Δ}
    (prenex : resource_prenex Γ F Δ) :
  resource_prenex_entails prenex (Resource.prenex_and prenex CTrue).
Proof.
  induction prenex; cbn [Resource.prenex_and].
  - apply RPEBody. split; [reflexivity |].
    apply CEntailsStep, CESAndTrueIntro.
  - apply RPEMono. exact IHprenex.
Qed.

Lemma resource_prenex_entails_frame_true_elim {Γ F Δ}
    (prenex : resource_prenex Γ F Δ) :
  resource_prenex_entails (Resource.prenex_and prenex CTrue) prenex.
Proof.
  induction prenex; cbn [Resource.prenex_and].
  - apply RPEBody. split; [reflexivity |].
    apply CEntailsStep, CESAndElimL.
  - apply RPEMono. exact IHprenex.
Qed.

Lemma resource_prenex_entails_frame_assoc {Γ F Δ}
    (prenex : resource_prenex Γ F Δ) (first second : core_assertion F Δ) :
  resource_prenex_entails
    (Resource.prenex_and (Resource.prenex_and prenex first) second)
    (Resource.prenex_and prenex (CAnd first second)).
Proof.
  revert first second. induction prenex; intros first second;
    cbn [Resource.prenex_and].
  - apply RPEBody. split; [reflexivity |].
    apply CEntailsStep, CESAndAssocR.
  - apply RPEMono. apply IHprenex.
Qed.

Lemma resource_prenex_entails_frame_assoc_back {Γ F Δ}
    (prenex : resource_prenex Γ F Δ) (first second : core_assertion F Δ) :
  resource_prenex_entails
    (Resource.prenex_and prenex (CAnd first second))
    (Resource.prenex_and (Resource.prenex_and prenex first) second).
Proof.
  revert first second. induction prenex; intros first second;
    cbn [Resource.prenex_and].
  - apply RPEBody. split; [reflexivity |].
    apply CEntailsStep, CESAndAssocL.
  - apply RPEMono. apply IHprenex.
Qed.

Lemma resource_prenex_entails_weaken {Γ F Δ u}
    (left right : resource_prenex Γ F Δ) :
  resource_prenex_entails left right ->
  resource_prenex_entails (Resource.weaken_resource_prenex (u := u) left)
    (Resource.weaken_resource_prenex (u := u) right).
Proof.
  apply RPERename.
Qed.

Lemma resource_of_core_existential_prenex_entails {Γ F Δ}
    (store : symbolic_store Γ F Δ)
    (prenex : Resource.core_existential_prenex F Δ) :
  resource_prenex_entails
    (RState store (Resource.interp_core_existential_prenex prenex))
    (Resource.resource_of_core_existential_prenex store prenex).
Proof.
  revert store. induction prenex; intro store; cbn.
  - apply RPEBody, resource_entails_refl.
  - eapply RPETrans.
    + apply RPEOpenCoreExists.
    + apply RPEMono, IHprenex.
Qed.

Lemma resource_of_core_existential_prenex_entails_back {Γ F Δ}
    (store : symbolic_store Γ F Δ)
    (prenex : Resource.core_existential_prenex F Δ) :
  resource_prenex_entails
    (Resource.resource_of_core_existential_prenex store prenex)
    (RState store (Resource.interp_core_existential_prenex prenex)).
Proof.
  revert store. induction prenex; intro store; cbn.
  - apply RPEBody, resource_entails_refl.
  - eapply RPETrans.
    + apply RPEMono, IHprenex.
    + apply RPECloseCoreExists.
Qed.

Theorem normalize_resource_prenex_entails {Γ F Δ}
    (prenex : resource_prenex Γ F Δ) :
  resource_prenex_entails prenex (Resource.normalize_resource_prenex prenex).
Proof.
  induction prenex as [Δ [store body] | Δ t rest IH]; cbn.
  - eapply RPETrans with (second := RState store
      (Resource.interp_core_existential_prenex
        (Resource.normalize_core_existential_prenex body))).
    + apply RPEBody. split; [reflexivity |].
      apply normalize_core_existential_prenex_entails.
    + apply resource_of_core_existential_prenex_entails.
  - apply RPEMono, IH.
Qed.

Theorem normalize_resource_prenex_entails_back {Γ F Δ}
    (prenex : resource_prenex Γ F Δ) :
  resource_prenex_entails (Resource.normalize_resource_prenex prenex) prenex.
Proof.
  induction prenex as [Δ [store body] | Δ t rest IH]; cbn.
  - eapply RPETrans with (second := RState store
      (Resource.interp_core_existential_prenex
        (Resource.normalize_core_existential_prenex body))).
    + apply resource_of_core_existential_prenex_entails_back.
    + apply RPEBody. split; [reflexivity |].
      apply normalize_core_existential_prenex_entails_back.
  - apply RPEMono, IH.
Qed.

Lemma normalize_weaken_resource_prenex_entails {Γ F Δ u}
    (prenex : resource_prenex Γ F Δ) :
  resource_prenex_entails
    (Resource.normalize_resource_prenex
      (Resource.weaken_resource_prenex (u := u) prenex))
    (Resource.weaken_resource_prenex
      (Resource.normalize_resource_prenex prenex)).
Proof.
  eapply RPETrans.
  - apply normalize_resource_prenex_entails_back.
  - apply resource_prenex_entails_weaken,
      normalize_resource_prenex_entails.
Qed.

Lemma normalize_weaken_resource_prenex_entails_back {Γ F Δ u}
    (prenex : resource_prenex Γ F Δ) :
  resource_prenex_entails
    (Resource.weaken_resource_prenex
      (Resource.normalize_resource_prenex prenex))
    (Resource.normalize_resource_prenex
      (Resource.weaken_resource_prenex (u := u) prenex)).
Proof.
  eapply RPETrans.
  - apply resource_prenex_entails_weaken,
      normalize_resource_prenex_entails_back.
  - apply normalize_resource_prenex_entails.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 3. Auxiliary core assertions

    Each of these has a [_stack_free] and a [_stack_count] lemma attached
    to its counterpart in [TypedHoare]; here both are unstatable. *)

Fixpoint allocated_physical_fields_core {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
    core_assertion F (TRef :: Δ) :=
  match fields with
  | [] => CPure True
  | FieldInit field value :: fields' =>
      CAnd (COwn field (ERef (RefBound MHere))
        (weaken_expr (symbolize_expr store value)))
        (allocated_physical_fields_core store fields')
  end.

Fixpoint allocated_ghost_fields_core {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) :
    core_assertion F (TRef :: Δ) :=
  match fields with
  | [] => CPure True
  | GhostFieldInit resource field Hfield value :: fields' =>
      CAnd
        (CGhostOwn field (ERef (RefBound MHere))
          (eq_rect (TRA resource) (expr F (TRef :: Δ))
            (weaken_expr (symbolize_expr store value))
            (Logic.field_type field) (eq_sym Hfield)))
        (allocated_ghost_fields_core store fields')
  end.

Definition allocated_fields_core {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
  core_assertion F (TRef :: Δ) :=
  CAnd
    (allocated_physical_fields_core store
      (physical_field_initializers fields))
    (allocated_ghost_fields_core store (ghost_field_initializers fields)).

Fixpoint ghost_initializers_valid_core {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) :
    core_assertion F Δ :=
  match fields with
  | [] => CPure True
  | GhostFieldInit resource _ _ value :: fields' =>
      CAnd (CRAValid (TRA resource) (symbolize_expr store value))
        (ghost_initializers_valid_core store fields')
  end.

(** A change of symbolic store must be justified structurally, slot by
    slot, rather than by an assertion entailment.  This replaces the
    recursive [stack_arguments_agree] search over logical assertion
    syntax. *)
Inductive store_equal_under {F Δ} (body : core_assertion F Δ) :
    forall Γ, symbolic_store Γ F Δ -> symbolic_store Γ F Δ -> Prop :=
| StoreEqualNil : store_equal_under body [] StoreNil StoreNil
| StoreEqualCons t Γ (left right : value_ref F Δ t)
    (left_tail right_tail : symbolic_store Γ F Δ) :
    core_entails body
      (CExpr (EBinOp (BEq t) (ERef left) (ERef right))) ->
    store_equal_under body Γ left_tail right_tail ->
    store_equal_under body (t :: Γ)
      (StoreCons left left_tail) (StoreCons right right_tail).

Lemma store_equal_under_frame {Γ F Δ}
    (body frame : core_assertion F Δ)
    (left right : symbolic_store Γ F Δ) :
  store_equal_under body Γ left right ->
  store_equal_under (CAnd body frame) Γ left right.
Proof.
  intro Hstore. induction Hstore.
  - apply StoreEqualNil.
  - apply StoreEqualCons.
    + eapply CEntailsTrans.
      * apply CEntailsStep, CESAndElimL.
      * exact H.
    + exact IHHstore.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 4. Procedure contracts

    Instantiation is a total function, not the three-clause relation
    [CONTRACT_ENV.instantiated_definition].  Gone with it:
    [predicate_body_stack_free], [invariant_body_stack_free],
    [instantiated_pre_stack_free], [instantiated_post_value_stack_free],
    the two [_rename] parameters (now provable, being a composition of
    total functions), and [reindex_stack_context]. *)

Module Type RESOURCE_CONTRACT_ENV_BASE.
  (** Masks are analysis state rather than logical contract data, but the analyzer still reads a procedure's declared masks off
      its contract, so they belong to the authoritative environment.
      Keeping them here gives the analyzer and resource calculus one
      authoritative source for procedure effects. *)
  Parameter required_mask : proc_id -> gset inv_id.
  Parameter granted_mask : proc_id -> gset inv_id.
  Parameter predicate_body : forall predicate,
    core_assertion (Logic.predicate_args predicate) [].
  Parameter predicate_body_entry_free : forall predicate,
    core_entry_free (predicate_body predicate).
  Parameter invariant_body : forall invariant,
    core_assertion (Logic.invariant_args invariant) [].
  Parameter invariant_body_entry_free : forall invariant,
    core_entry_free (invariant_body invariant).
  Parameter contract_pre : forall procedure,
    core_assertion (Logic.procedure_args procedure) [].
  Parameter contract_post : forall procedure,
    core_assertion (Logic.procedure_args procedure)
      (return_context (Logic.procedure_return procedure)).
  (** The callee has a declaration with a verified body.  In [CONTRACT_ENV]
      this is smuggled through the existential inside [instantiated_pre]
      and extracted by [instantiated_pre_selects]; as a premise there is
      nothing to extract. *)
  Parameter procedure_verified : proc_id -> Prop.
End RESOURCE_CONTRACT_ENV_BASE.


Module ContractInstances (Contracts : RESOURCE_CONTRACT_ENV_BASE).

  Definition instantiated_invariant {F Δ} (invariant : inv_id)
      (arguments : expr_list F Δ (Logic.invariant_args invariant)) :
      core_assertion F Δ :=
    subst_formals_core (expr_list_formal_subst arguments)
      (weaken_core_to Δ (Contracts.invariant_body invariant)).

  Definition instantiated_predicate {F Δ} (predicate : pred_id)
      (arguments : expr_list F Δ (Logic.predicate_args predicate)) :
      core_assertion F Δ :=
    subst_formals_core (expr_list_formal_subst arguments)
      (weaken_core_to Δ (Contracts.predicate_body predicate)).

  Definition instantiated_pre {F Δ} (procedure : proc_id)
      (arguments : expr_list F Δ (Logic.procedure_args procedure)) :
      core_assertion F Δ :=
    subst_formals_core (expr_list_formal_subst arguments)
      (weaken_core_to Δ (Contracts.contract_pre procedure)).

  (** The callee's return binder becomes binder zero of the caller. *)
  Definition instantiated_post {F Δ} (procedure : proc_id)
      (arguments : expr_list F (Logic.procedure_return procedure :: Δ)
        (Logic.procedure_args procedure)) :
      core_assertion F (Logic.procedure_return procedure :: Δ) :=
    subst_formals_core (expr_list_formal_subst arguments)
      (rename_bound_core return_bound_renaming
        (Contracts.contract_post procedure)).

End ContractInstances.

(* ------------------------------------------------------------------ *)
(** ** 5. The calculus *)

Module ResourceRules (Contracts : RESOURCE_CONTRACT_ENV_BASE).
Module Instances := ContractInstances Contracts.
Import Instances.

(** Structured invariant access, over resource telescopes.  Compare
    [TypedHoare.invariant_access_closure]: the [AAnd (AStack store) _]
    shape becomes the record, the frame is a [core_assertion] so it cannot
    hide a second stack, and [invariant_access_closure_stack_count] — whose
    only job was to show the closure neither loses nor duplicates the
    distinguished stack — has nothing left to prove. *)
Inductive resource_access_closure {Γ F} (invariant : inv_id) :
    forall Δ (arguments : expr_list F Δ (Logic.invariant_args invariant)),
      core_assertion F Δ ->
      resource_prenex Γ F Δ -> resource_prenex Γ F Δ -> Prop :=
| ResourceAccessBase Δ arguments invariant_body store remainder :
    resource_access_closure invariant Δ arguments invariant_body
      (RState store (CAnd invariant_body remainder))
      (RState store (CAnd (CInvariant invariant arguments) remainder))
| ResourceAccessExists Δ t arguments invariant_body opened closed :
    resource_access_closure invariant (t :: Δ)
      (weaken_expr_list arguments) (weaken_core invariant_body)
      opened closed ->
    resource_access_closure invariant Δ arguments invariant_body
      (ResourceExists t opened) (ResourceExists t closed)
| ResourceAccessEquality Δ
    (opening_arguments closing_arguments :
      expr_list F Δ (Logic.invariant_args invariant))
    opening_body store remainder condition :
    expr_list_equal_assuming condition _ closing_arguments opening_arguments ->
    resource_access_closure invariant Δ opening_arguments opening_body
      (RState store
        (CAnd (instantiated_invariant invariant closing_arguments)
          (CAnd remainder (CExpr condition))))
      (RState store
        (CAnd (CInvariant invariant opening_arguments)
          (CAnd remainder (CExpr condition))))
| ResourceAccessFrame Δ arguments invariant_body opened closed frame :
    resource_access_closure invariant Δ arguments invariant_body
      opened closed ->
    resource_access_closure invariant Δ arguments invariant_body
      (prenex_and opened frame) (prenex_and closed frame)
| ResourceAccessConsequence Δ arguments invariant_body
    opened opened' closed closed' :
    resource_prenex_entails opened' opened ->
    resource_access_closure invariant Δ arguments invariant_body
      opened closed ->
    resource_prenex_entails closed closed' ->
    resource_access_closure invariant Δ arguments invariant_body
      opened' closed'
| ResourceAccessStackRewrite Δ arguments invariant_body
    store store' body closed :
    resource_access_closure invariant Δ arguments invariant_body
      (RState store body) closed ->
    store_equal_under body Γ store' store ->
    resource_access_closure invariant Δ arguments invariant_body
      (RState store' body) closed
| ResourceAccessArgumentStoreRewrite Δ
    (program_arguments : pexpr_list Γ (Logic.invariant_args invariant))
    opening_store closing_store body closed :
    resource_access_closure invariant Δ
      (symbolize_expr_list closing_store program_arguments)
      (instantiated_invariant invariant
        (symbolize_expr_list closing_store program_arguments))
      (RState closing_store body) closed ->
    store_equal_under body Γ opening_store closing_store ->
    resource_access_closure invariant Δ
      (symbolize_expr_list opening_store program_arguments)
      (instantiated_invariant invariant
        (symbolize_expr_list opening_store program_arguments))
      (RState opening_store body) closed
| ResourceAccessRename Δ Δ' (renaming : bound_renaming Δ Δ')
    arguments invariant_body opened closed :
    bound_renaming_injective renaming ->
    resource_access_closure invariant Δ arguments invariant_body
      opened closed ->
    resource_access_closure invariant Δ'
      (rename_bound_expr_list renaming arguments)
      (rename_bound_core renaming invariant_body)
      (rename_resource_prenex opened _ renaming)
      (rename_resource_prenex closed _ renaming).

(** Canonical closure extracted from a bare fold rule.  The primitive access
    closure carries an explicit core frame; choosing [CTrue] and eliminating
    it by consequence recovers the exact pre/postconditions of
    [RTFoldInvariant]. *)
Lemma resource_access_closure_fold_base {Γ F Δ} invariant
    (arguments : expr_list F Δ (Logic.invariant_args invariant))
    (store : symbolic_store Γ F Δ) :
  resource_access_closure invariant Δ arguments
    (Instances.instantiated_invariant invariant arguments)
    (RState store (Instances.instantiated_invariant invariant arguments))
    (RState store (CInvariant invariant arguments)).
Proof.
  eapply ResourceAccessConsequence with
    (opened := RState store
      (CAnd (Instances.instantiated_invariant invariant arguments) CTrue))
    (closed := RState store
      (CAnd (CInvariant invariant arguments) CTrue)).
  - apply RPEBody. split; [reflexivity |].
    apply CEntailsStep. apply CESAndTrueIntro.
  - apply ResourceAccessBase.
  - apply RPEBody. split; [reflexivity |].
    apply CEntailsStep. apply CESAndElimL.
Qed.

(** A fold surrounded by ordinary consequence still exposes the same access
    boundary.  This is the fold-side inversion principle used by the
    normalizer: the rule's precondition entailment strengthens the opened
    resources and its postcondition entailment weakens the closed result. *)
Lemma resource_access_closure_fold_consequence {Γ F Δ} invariant
    (arguments : expr_list F Δ (Logic.invariant_args invariant))
    (store : symbolic_store Γ F Δ) (pre_body : core_assertion F Δ)
    (post : resource_prenex Γ F Δ) :
  core_entails pre_body
    (Instances.instantiated_invariant invariant arguments) ->
  resource_prenex_entails
    (RState store (CInvariant invariant arguments)) post ->
  resource_access_closure invariant Δ arguments
    (Instances.instantiated_invariant invariant arguments)
    (RState store pre_body) post.
Proof.
  intros Hpre Hpost. eapply ResourceAccessConsequence with
    (opened := RState store
      (Instances.instantiated_invariant invariant arguments))
    (closed := RState store (CInvariant invariant arguments)).
  - apply RPEBody. split; [reflexivity | exact Hpre].
  - apply resource_access_closure_fold_base.
  - exact Hpost.
Qed.

(** The canonical fold leaf when its symbolic store has been rewritten after
    the access body.  The inner fold closes the invariant at the closing
    store; [ResourceAccessArgumentStoreRewrite] transports both stack
    ownership and the symbolized argument vector back to the opening store. *)
Lemma resource_access_closure_fold_store_rewrite {Γ F Δ} invariant
    (program_arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (opening_store closing_store : symbolic_store Γ F Δ)
    (fold_pre : core_assertion F Δ) (post : resource_prenex Γ F Δ) :
  core_entails fold_pre
    (Instances.instantiated_invariant invariant
      (symbolize_expr_list closing_store program_arguments)) ->
  resource_prenex_entails
    (RState closing_store
      (CInvariant invariant
        (symbolize_expr_list closing_store program_arguments))) post ->
  store_equal_under fold_pre Γ opening_store closing_store ->
  resource_access_closure invariant Δ
    (symbolize_expr_list opening_store program_arguments)
    (Instances.instantiated_invariant invariant
      (symbolize_expr_list opening_store program_arguments))
    (RState opening_store fold_pre) post.
Proof.
  intros Hfold_pre Hfold_post Hstore.
  eapply ResourceAccessArgumentStoreRewrite.
  - eapply resource_access_closure_fold_consequence; eassumption.
  - exact Hstore.
Qed.

(** Eliminate a vacuous focused binder after closing an access.  This is the
    closure-side counterpart of [RTPrenexElim]: lift the inner closure through
    the existential, then discard the weakened closed result by consequence. *)
Lemma resource_access_closure_exists_elim {Γ F Δ} invariant t
    (arguments : expr_list F Δ (Logic.invariant_args invariant))
    (invariant_body : core_assertion F Δ)
    (opened : resource_prenex Γ F (t :: Δ))
    (closed : resource_prenex Γ F Δ) :
  resource_access_closure invariant (t :: Δ)
    (weaken_expr_list arguments) (weaken_core invariant_body)
    opened (weaken_resource_prenex closed) ->
  resource_access_closure invariant Δ arguments invariant_body
    (ResourceExists t opened) closed.
Proof.
  intro Hclosure. eapply ResourceAccessConsequence.
  - apply resource_prenex_entails_refl.
  - apply ResourceAccessExists. exact Hclosure.
  - apply RPEVacuous.
Qed.

(** The identity shared by the two sides of an invariant access.  It records
    the canonical unfold and its telescope path, but deliberately carries no
    assertion endpoints: opening and closing may use different structural
    wrappers around the same scoped access. *)
Inductive resource_access_focus {Γ F} (invariant : inv_id)
    (program_arguments : pexpr_list Γ (Logic.invariant_args invariant)) :
    context -> Type :=
| ResourceAccessFocusBase Δ
    (focus_arguments : expr_list F Δ (Logic.invariant_args invariant)) :
    resource_access_focus invariant program_arguments Δ
| ResourceAccessFocusPreserve Δ t :
    resource_access_focus invariant program_arguments (t :: Δ) ->
    resource_access_focus invariant program_arguments Δ
| ResourceAccessFocusBoundWeaken Δ t :
    resource_access_focus invariant program_arguments Δ ->
    resource_access_focus invariant program_arguments (t :: Δ)
| ResourceAccessFocusElim Δ t :
    resource_access_focus invariant program_arguments (t :: Δ) ->
    resource_access_focus invariant program_arguments Δ.

Inductive resource_access_opening {Γ F} (invariant : inv_id)
    (program_arguments : pexpr_list Γ (Logic.invariant_args invariant)) :
    forall {Δ}, resource_access_focus invariant program_arguments Δ ->
      resource_prenex Γ F Δ -> resource_prenex Γ F Δ -> Prop :=
| ResourceAccessOpeningBase Δ (store : symbolic_store Γ F Δ) :
    resource_access_opening invariant program_arguments
      (@ResourceAccessFocusBase Γ F invariant program_arguments Δ
        (symbolize_expr_list store program_arguments))
      (RState store
        (CInvariant invariant (symbolize_expr_list store program_arguments)))
      (RState store
        (instantiated_invariant invariant
          (symbolize_expr_list store program_arguments)))
| ResourceAccessOpeningPreserve Δ t focus external body_pre :
    resource_access_opening invariant program_arguments
      (Δ := t :: Δ) focus external body_pre ->
    resource_access_opening invariant program_arguments
      (@ResourceAccessFocusPreserve Γ F invariant program_arguments Δ t focus)
      (ResourceExists t external) (ResourceExists t body_pre)
| ResourceAccessOpeningBoundWeaken Δ t focus external body_pre :
    resource_access_opening invariant program_arguments
      (Δ := Δ) focus external body_pre ->
    resource_access_opening invariant program_arguments
      (@ResourceAccessFocusBoundWeaken Γ F invariant program_arguments
        Δ t focus)
      (weaken_resource_prenex external) (weaken_resource_prenex body_pre)
| ResourceAccessOpeningElim Δ t focus external body_pre :
    resource_access_opening invariant program_arguments
      (Δ := t :: Δ) focus external (weaken_resource_prenex body_pre) ->
    resource_access_opening invariant program_arguments
      (@ResourceAccessFocusElim Γ F invariant program_arguments Δ t focus)
      (ResourceExists t external) body_pre
| ResourceAccessOpeningPrenexConsequence Δ focus
    external external' body_pre body_pre' :
    resource_access_opening invariant program_arguments
      (Δ := Δ) focus external body_pre ->
    resource_prenex_entails external' external ->
    resource_prenex_entails body_pre body_pre' ->
    resource_access_opening invariant program_arguments focus
      external' body_pre'
| ResourceAccessOpeningFrame Δ focus (store : symbolic_store Γ F Δ)
    pre_body frame body_pre :
    resource_access_opening invariant program_arguments focus
      (RState store pre_body) body_pre ->
    resource_access_opening invariant program_arguments focus
      (RState store (CAnd pre_body frame)) (prenex_and body_pre frame)
| ResourceAccessOpeningConsequence Δ focus (store : symbolic_store Γ F Δ)
    pre_body pre_body' body_pre body_pre' :
    resource_access_opening invariant program_arguments focus
      (RState store pre_body) body_pre ->
    core_entails pre_body' pre_body ->
    resource_prenex_entails body_pre body_pre' ->
    resource_access_opening invariant program_arguments focus
      (RState store pre_body') body_pre'
| ResourceAccessOpeningStackRewrite Δ focus
    (store store' : symbolic_store Γ F Δ) pre_body body_pre :
    resource_access_opening invariant program_arguments focus
      (RState store pre_body) body_pre ->
    store_equal_under pre_body Γ store' store ->
    resource_access_opening invariant program_arguments focus
      (RState store' pre_body) body_pre.

Inductive resource_access_closing {Γ F} (invariant : inv_id)
    (program_arguments : pexpr_list Γ (Logic.invariant_args invariant)) :
    forall {Δ}, resource_access_focus invariant program_arguments Δ ->
      resource_prenex Γ F Δ -> resource_prenex Γ F Δ -> Prop :=
| ResourceAccessClosingBase Δ (store : symbolic_store Γ F Δ) :
    resource_access_closing invariant program_arguments
      (@ResourceAccessFocusBase Γ F invariant program_arguments Δ
        (symbolize_expr_list store program_arguments))
      (RState store
        (instantiated_invariant invariant
          (symbolize_expr_list store program_arguments)))
      (RState store
        (CInvariant invariant
          (symbolize_expr_list store program_arguments)))
| ResourceAccessClosingPreserve Δ t focus body_post external_post :
    resource_access_closing invariant program_arguments
      (Δ := t :: Δ) focus body_post external_post ->
    resource_access_closing invariant program_arguments
      (@ResourceAccessFocusPreserve Γ F invariant program_arguments Δ t focus)
      (ResourceExists t body_post) (ResourceExists t external_post)
| ResourceAccessClosingBoundWeaken Δ t focus body_post external_post :
    resource_access_closing invariant program_arguments
      (Δ := Δ) focus body_post external_post ->
    resource_access_closing invariant program_arguments
      (@ResourceAccessFocusBoundWeaken Γ F invariant program_arguments
        Δ t focus)
      (weaken_resource_prenex body_post)
      (weaken_resource_prenex external_post)
| ResourceAccessClosingElim Δ t focus body_post external_post :
    resource_access_closing invariant program_arguments
      (Δ := t :: Δ) focus body_post (weaken_resource_prenex external_post) ->
    resource_access_closing invariant program_arguments
      (@ResourceAccessFocusElim Γ F invariant program_arguments Δ t focus)
      (ResourceExists t body_post) external_post
| ResourceAccessClosingConsequence Δ focus
    body_post body_post' external_post external_post' :
    resource_prenex_entails body_post' body_post ->
    resource_access_closing invariant program_arguments
      (Δ := Δ) focus body_post external_post ->
    resource_prenex_entails external_post external_post' ->
    resource_access_closing invariant program_arguments focus
      body_post' external_post'
| ResourceAccessClosingFrame Δ focus body_post external_post frame :
    resource_access_closing invariant program_arguments
      (Δ := Δ) focus body_post external_post ->
    resource_access_closing invariant program_arguments focus
      (prenex_and body_post frame) (prenex_and external_post frame)
| ResourceAccessClosingStackRewrite Δ focus
    (store store' : symbolic_store Γ F Δ) body external_post :
    resource_access_closing invariant program_arguments focus
      (RState store body) external_post ->
    store_equal_under body Γ store' store ->
    resource_access_closing invariant program_arguments focus
      (RState store' body) external_post.

(** A non-dependent view of an opening whose shared focus is canonical.
    Keeping this small inversion view in the resource layer prevents the
    runtime soundness file from expanding a large dependent-induction proof
    term merely to eliminate impossible binder-focus constructors. *)
Inductive resource_access_base_opening {Γ F Δ} (invariant : inv_id)
    (program_arguments : pexpr_list Γ (Logic.invariant_args invariant)) :
    expr_list F Δ (Logic.invariant_args invariant) ->
      resource_prenex Γ F Δ -> resource_prenex Γ F Δ -> Prop :=
| ResourceAccessBaseOpening (store : symbolic_store Γ F Δ) :
    resource_access_base_opening invariant program_arguments
      (symbolize_expr_list store program_arguments)
      (RState store
        (CInvariant invariant
          (symbolize_expr_list store program_arguments)))
      (RState store
        (instantiated_invariant invariant
          (symbolize_expr_list store program_arguments)))
| ResourceAccessBaseOpeningPrenexConsequence
    focus_arguments external external' body_pre body_pre' :
    resource_access_base_opening invariant program_arguments focus_arguments
      external body_pre ->
    resource_prenex_entails external' external ->
    resource_prenex_entails body_pre body_pre' ->
    resource_access_base_opening invariant program_arguments focus_arguments
      external' body_pre'
| ResourceAccessBaseOpeningFrame focus_arguments
    (store : symbolic_store Γ F Δ)
    pre_body frame body_pre :
    resource_access_base_opening invariant program_arguments focus_arguments
      (RState store pre_body) body_pre ->
    resource_access_base_opening invariant program_arguments focus_arguments
      (RState store (CAnd pre_body frame)) (prenex_and body_pre frame)
| ResourceAccessBaseOpeningConsequence
    focus_arguments (store : symbolic_store Γ F Δ)
    pre_body pre_body' body_pre body_pre' :
    resource_access_base_opening invariant program_arguments focus_arguments
      (RState store pre_body) body_pre ->
    core_entails pre_body' pre_body ->
    resource_prenex_entails body_pre body_pre' ->
    resource_access_base_opening invariant program_arguments focus_arguments
      (RState store pre_body') body_pre'
| ResourceAccessBaseOpeningStackRewrite
    focus_arguments (store store' : symbolic_store Γ F Δ)
    pre_body body_pre :
    resource_access_base_opening invariant program_arguments focus_arguments
      (RState store pre_body) body_pre ->
    store_equal_under pre_body Γ store' store ->
    resource_access_base_opening invariant program_arguments focus_arguments
      (RState store' pre_body) body_pre.

Lemma resource_access_opening_base_view {Γ F Δ} invariant
    (program_arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (focus_arguments : expr_list F Δ (Logic.invariant_args invariant))
    (external body_pre : resource_prenex Γ F Δ) :
  resource_access_opening invariant program_arguments
    (@ResourceAccessFocusBase Γ F invariant program_arguments Δ
      focus_arguments)
    external body_pre ->
  resource_access_base_opening invariant program_arguments focus_arguments
    external body_pre.
Proof.
  intro Hopening. dependent induction Hopening.
  - apply ResourceAccessBaseOpening.
  - eapply ResourceAccessBaseOpeningPrenexConsequence.
    { apply (IHHopening focus_arguments eq_refl). }
    { exact H. }
    { exact H0. }
  - apply ResourceAccessBaseOpeningFrame.
    apply (IHHopening focus_arguments eq_refl).
  - eapply ResourceAccessBaseOpeningConsequence.
    + apply (IHHopening focus_arguments eq_refl).
    + exact H.
    + exact H0.
  - eapply ResourceAccessBaseOpeningStackRewrite.
    + apply (IHHopening focus_arguments eq_refl).
    + exact H.
Qed.

Inductive resource_access_boundary {Γ F} (invariant : inv_id)
    (program_arguments : pexpr_list Γ (Logic.invariant_args invariant)) :
    forall {Δ}, resource_prenex Γ F Δ -> resource_prenex Γ F Δ ->
      resource_prenex Γ F Δ -> resource_prenex Γ F Δ -> Prop :=
| ResourceAccessBoundaryBase Δ (store : symbolic_store Γ F Δ)
    (frame : core_assertion F Δ) body_post external_post :
    resource_access_closure invariant Δ
      (symbolize_expr_list store program_arguments)
      (instantiated_invariant invariant
        (symbolize_expr_list store program_arguments))
      body_post external_post ->
    resource_access_boundary invariant program_arguments
      (RState store
        (CAnd (CInvariant invariant
          (symbolize_expr_list store program_arguments)) frame))
      (RState store
        (CAnd (instantiated_invariant invariant
          (symbolize_expr_list store program_arguments)) frame))
      body_post external_post
| ResourceAccessBoundaryOpeningPrenexConsequence Δ external external'
    body_pre body_pre' body_post external_post :
    resource_access_boundary invariant program_arguments (Δ := Δ)
      external body_pre body_post external_post ->
    resource_prenex_entails external' external ->
    resource_prenex_entails body_pre body_pre' ->
    resource_access_boundary invariant program_arguments
      external' body_pre' body_post external_post
| ResourceAccessBoundaryOpeningFrame Δ (store : symbolic_store Γ F Δ)
    pre_body frame body_pre body_post external_post :
    resource_access_boundary invariant program_arguments
      (RState store pre_body) body_pre body_post external_post ->
    resource_access_boundary invariant program_arguments
      (RState store (CAnd pre_body frame)) (prenex_and body_pre frame)
      body_post external_post
| ResourceAccessBoundaryOpeningConsequence Δ
    (store : symbolic_store Γ F Δ) pre_body pre_body' body_pre body_pre'
    body_post external_post :
    resource_access_boundary invariant program_arguments
      (RState store pre_body) body_pre body_post external_post ->
    core_entails pre_body' pre_body ->
    resource_prenex_entails body_pre body_pre' ->
    resource_access_boundary invariant program_arguments
      (RState store pre_body') body_pre' body_post external_post
| ResourceAccessBoundaryOpeningStackRewrite Δ
    (store store' : symbolic_store Γ F Δ) pre_body body_pre body_post
    external_post :
    resource_access_boundary invariant program_arguments
      (RState store pre_body) body_pre body_post external_post ->
    store_equal_under pre_body Γ store' store ->
    resource_access_boundary invariant program_arguments
      (RState store' pre_body) body_pre body_post external_post
| ResourceAccessBoundaryClosingConsequence Δ external_pre body_pre
    body_post body_post' external_post external_post' :
    resource_prenex_entails body_post' body_post ->
    resource_access_boundary invariant program_arguments (Δ := Δ)
      external_pre body_pre body_post external_post ->
    resource_prenex_entails external_post external_post' ->
    resource_access_boundary invariant program_arguments
      external_pre body_pre body_post' external_post'
| ResourceAccessBoundaryClosingFrame Δ external_pre body_pre body_post
    external_post frame :
    resource_access_boundary invariant program_arguments (Δ := Δ)
      external_pre body_pre body_post external_post ->
    resource_access_boundary invariant program_arguments
      external_pre body_pre (prenex_and body_post frame)
      (prenex_and external_post frame).

Lemma resource_access_boundary_base {Γ F Δ} invariant
    (program_arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (store : symbolic_store Γ F Δ) (frame : core_assertion F Δ)
    (body_post external_post : resource_prenex Γ F Δ) :
  resource_access_closure invariant Δ
    (symbolize_expr_list store program_arguments)
    (instantiated_invariant invariant
      (symbolize_expr_list store program_arguments))
    body_post external_post ->
  resource_access_boundary invariant program_arguments
    (RState store
      (CAnd (CInvariant invariant
        (symbolize_expr_list store program_arguments)) frame))
    (RState store
      (CAnd (instantiated_invariant invariant
        (symbolize_expr_list store program_arguments)) frame))
    body_post external_post.
Proof.
  apply ResourceAccessBoundaryBase.
Qed.

Lemma resource_access_boundary_consequence {Γ F Δ} invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (external_pre external_pre' body_pre body_post
      external_post external_post' : resource_prenex Γ F Δ) :
  resource_prenex_entails external_pre' external_pre ->
  resource_access_boundary invariant arguments
    external_pre body_pre body_post external_post ->
  resource_prenex_entails external_post external_post' ->
  resource_access_boundary invariant arguments
    external_pre' body_pre body_post external_post'.
Proof.
  intros Hpre Hboundary Hpost.
  eapply ResourceAccessBoundaryClosingConsequence.
  - apply resource_prenex_entails_refl.
  - eapply ResourceAccessBoundaryOpeningPrenexConsequence.
    + exact Hboundary.
    + exact Hpre.
    + apply resource_prenex_entails_refl.
  - exact Hpost.
Qed.

Lemma resource_access_boundary_base_view {Γ F Δ} invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (external_pre body_pre body_post external_post :
      resource_prenex Γ F Δ) :
  resource_access_boundary invariant arguments
    external_pre body_pre body_post external_post ->
  exists focus_arguments : expr_list F Δ
      (Logic.invariant_args invariant),
    resource_access_opening invariant arguments
      (@ResourceAccessFocusBase Γ F invariant arguments Δ focus_arguments)
      external_pre body_pre /\
    resource_access_closure invariant Δ focus_arguments
      (instantiated_invariant invariant focus_arguments)
      body_post external_post.
Proof.
  intro Hboundary. induction Hboundary.
  - exists (symbolize_expr_list store arguments). split.
    + change (resource_access_opening invariant arguments
        (ResourceAccessFocusBase invariant arguments Δ
          (symbolize_expr_list store arguments))
        (RState store
          (CAnd (CInvariant invariant
            (symbolize_expr_list store arguments)) frame))
        (prenex_and
          (RState store
            (instantiated_invariant invariant
              (symbolize_expr_list store arguments))) frame)).
      apply ResourceAccessOpeningFrame. apply ResourceAccessOpeningBase.
    + exact H.
  - destruct IHHboundary as (focus_arguments & Hopening & Hclosing).
    exists focus_arguments. split; [|exact Hclosing].
    eapply ResourceAccessOpeningPrenexConsequence; eassumption.
  - destruct IHHboundary as (focus_arguments & Hopening & Hclosing).
    exists focus_arguments. split; [|exact Hclosing].
    apply ResourceAccessOpeningFrame. exact Hopening.
  - destruct IHHboundary as (focus_arguments & Hopening & Hclosing).
    exists focus_arguments. split; [|exact Hclosing].
    eapply ResourceAccessOpeningConsequence; eassumption.
  - destruct IHHboundary as (focus_arguments & Hopening & Hclosing).
    exists focus_arguments. split; [|exact Hclosing].
    eapply ResourceAccessOpeningStackRewrite; eassumption.
  - destruct IHHboundary as (focus_arguments & Hopening & Hclosing).
    exists focus_arguments. split; [exact Hopening |].
    eapply ResourceAccessConsequence; eassumption.
  - destruct IHHboundary as (focus_arguments & Hopening & Hclosing).
    exists focus_arguments. split; [exact Hopening |].
    apply ResourceAccessFrame. exact Hclosing.
Qed.

Inductive RavenResourceTriple {Γ F} : forall {Δ},
    resource_prenex Γ F Δ -> stmt Γ -> resource_prenex Γ F Δ -> Prop :=

(** *** Telescope rules.  These replace [ResourceExistsElimRule] and
    [ResourceExistsPreserveRule], which had to reach inside an [AExists]
    wrapped around a stack. *)
| RTPrenexPreserve {Δ} t statement
    (pre post : resource_prenex Γ F (t :: Δ)) :
    RavenResourceTriple pre statement post ->
    RavenResourceTriple (ResourceExists t pre) statement (ResourceExists t post)
| RTBoundWeaken {Δ} t statement
    (pre post : resource_prenex Γ F Δ) :
    RavenResourceTriple pre statement post ->
    RavenResourceTriple (weaken_resource_prenex (u := t) pre) statement
      (weaken_resource_prenex (u := t) post)
| RTPrenexElim {Δ} t statement
    (pre : resource_prenex Γ F (t :: Δ)) (post : resource_prenex Γ F Δ) :
    RavenResourceTriple pre statement (weaken_resource_prenex post) ->
    RavenResourceTriple (ResourceExists t pre) statement post

(** General consequence at the telescope boundary.  Unlike ordinary
    [RTConsequence], this rule may move a core existential into the prenex;
    stack safety is still enforced by [resource_prenex_entails]. *)
| RTPrenexConsequence {Δ} statement
    (pre pre' post post' : resource_prenex Γ F Δ) :
    RavenResourceTriple pre statement post ->
    resource_prenex_entails pre' pre ->
    resource_prenex_entails post post' ->
    RavenResourceTriple pre' statement post'

(** *** Structural rules.  Frame takes a [core_assertion]; ordinary
    consequence keeps the stack fixed; a change of store is the separate
    structural [RTStackRewrite].  Together they replace
    [ResourceStackConsequenceRule]. *)
| RTFrame {Δ} statement (store : symbolic_store Γ F Δ)
    (pre_body frame : core_assertion F Δ) (post : resource_prenex Γ F Δ) :
    RavenResourceTriple (RState store pre_body) statement post ->
    RavenResourceTriple (RState store (CAnd pre_body frame)) statement
      (prenex_and post frame)
| RTConsequence {Δ} statement (store : symbolic_store Γ F Δ)
    (pre_body pre_body' : core_assertion F Δ)
    (post post' : resource_prenex Γ F Δ) :
    RavenResourceTriple (RState store pre_body) statement post ->
    core_entails pre_body' pre_body ->
    resource_prenex_entails post post' ->
    RavenResourceTriple (RState store pre_body') statement post'
| RTStackRewrite {Δ} statement (store store' : symbolic_store Γ F Δ)
    (body : core_assertion F Δ) (post : resource_prenex Γ F Δ) :
    RavenResourceTriple (RState store body) statement post ->
    store_equal_under body Γ store' store ->
    RavenResourceTriple (RState store' body) statement post

(** *** Statement rules.  None carries a frame parameter: the core body of
    a resource state is already arbitrary. *)
(* The empty continuation is the identity on every prenex, not only on a
   single resource state: it neither reads nor changes the store, and binds
   nothing. *)
| RTDone {Δ} node (P : resource_prenex Γ F Δ) :
    RavenResourceTriple P (TDone node) P
| RTAssert {Δ} node (store : symbolic_store Γ F Δ)
    (body : core_assertion F Δ) condition :
    RavenResourceTriple
      (RState store (CAnd body (CExpr (symbolize_expr store condition))))
      (TAssert node condition)
      (RState store (CAnd body (CExpr (symbolize_expr store condition))))
| RTAssign {Δ} t node (store : symbolic_store Γ F Δ) target value :
    RavenResourceTriple
      (RState store CTrue)
      (TAssign node target value)
      (ResourceExists t
        (RState (update_store_with_bound store target)
          (CExpr (EBinOp (BEq t) (ERef (RefBound MHere))
            (weaken_expr (symbolize_expr store value))))))
| RTFieldRead {Δ} node (store : symbolic_store Γ F Δ) field
    (target : pvar Γ (Logic.field_type field)) base chunk :
    RavenResourceTriple
      (RState store (COwn field (symbolize_expr store base) chunk))
      (TFieldRead node field target base)
      (ResourceExists (Logic.field_type field)
        (RState (update_store_with_bound store target)
          (CAnd
            (COwn field (weaken_expr (symbolize_expr store base))
              (weaken_expr chunk))
            (CExpr (EBinOp (BEq (Logic.field_type field))
              (ERef (RefBound MHere)) (weaken_expr chunk))))))
| RTFieldWrite {Δ} node (store : symbolic_store Γ F Δ) field base
    (value : pexpr Γ (Logic.field_type field)) old_chunk :
    RavenResourceTriple
      (RState store (COwn field (symbolize_expr store base) old_chunk))
      (TFieldWrite node field base value)
      (RState store
        (COwn field (symbolize_expr store base)
          (symbolize_expr store value)))
| RTAlloc {Δ} node (store : symbolic_store Γ F Δ) target fields :
    NoDup (map field_init_id fields) ->
    NoDup (map ghost_field_init_id (ghost_field_initializers fields)) ->
    ghost_initializers_require_physical fields ->
    RavenResourceTriple
      (RState store
        (ghost_initializers_valid_core store
          (ghost_field_initializers fields)))
      (TAlloc node target fields)
      (ResourceExists TRef
        (RState (update_store_with_bound store target)
          (allocated_fields_core store fields)))
| RTGhostUpdate {Δ} node (store : symbolic_store Γ F Δ)
    field base old_value new_value :
    RavenResourceTriple
      (RState store
        (CAnd
          (CGhostOwn field (symbolize_expr store base)
            (symbolize_expr store old_value))
          (CFpuAllowed (Logic.field_type field)
            (symbolize_expr store old_value)
            (symbolize_expr store new_value))))
      (TGhostUpdate node field base old_value new_value)
      (RState store
        (CGhostOwn field (symbolize_expr store base)
          (symbolize_expr store new_value)))
| RTSeq {Δ} node (pre middle post : resource_prenex Γ F Δ) first second :
    RavenResourceTriple pre first middle ->
    RavenResourceTriple middle second post ->
    RavenResourceTriple pre (TSeq node first second) post

(** Baseline conditional: both branches establish the same output resource
    assertion, store included.  No join operation. *)
| RTIf {Δ} node (store : symbolic_store Γ F Δ) (body : core_assertion F Δ)
    condition then_branch else_branch (post : resource_prenex Γ F Δ) :
    RavenResourceTriple
      (RState store (CAnd body (CExpr (symbolize_expr store condition))))
      then_branch post ->
    RavenResourceTriple
      (RState store
        (CAnd body (CExpr (EUnOp UNot (symbolize_expr store condition)))))
      else_branch post ->
    RavenResourceTriple (RState store body)
      (TIf node condition then_branch else_branch) post

(** *** Fold / unfold.  The store is threaded unchanged. *)
| RTUnfoldInvariant {Δ} node invariant (store : symbolic_store Γ F Δ) arguments :
    RavenResourceTriple
      (RState store
        (CInvariant invariant (symbolize_expr_list store arguments)))
      (TUnfold node invariant arguments)
      (RState store
        (instantiated_invariant invariant
          (symbolize_expr_list store arguments)))
| RTFoldInvariant {Δ} node invariant (store : symbolic_store Γ F Δ) arguments :
    RavenResourceTriple
      (RState store
        (instantiated_invariant invariant
          (symbolize_expr_list store arguments)))
      (TFold node invariant arguments)
      (RState store
        (CInvariant invariant (symbolize_expr_list store arguments)))
| RTUnfoldPredicate {Δ} node predicate (store : symbolic_store Γ F Δ) arguments :
    RavenResourceTriple
      (RState store
        (CPredicate predicate (symbolize_expr_list store arguments)))
      (TPredicateUnfold node predicate arguments)
      (RState store
        (instantiated_predicate predicate
          (symbolize_expr_list store arguments)))
| RTFoldPredicate {Δ} node predicate (store : symbolic_store Γ F Δ) arguments :
    RavenResourceTriple
      (RState store
        (instantiated_predicate predicate
          (symbolize_expr_list store arguments)))
      (TPredicateFold node predicate arguments)
      (RState store
        (CPredicate predicate (symbolize_expr_list store arguments)))

| RTInvAccess {Δ} invariant arguments body
    (external_pre body_pre body_post external_post : resource_prenex Γ F Δ) :
    resource_access_boundary invariant arguments
      external_pre body_pre body_post external_post ->
    RavenResourceTriple body_pre body body_post ->
    RavenResourceTriple external_pre
      (TInvAccess invariant arguments body) external_post
(** General matched access.  The opening and closing prenex spines are
    intentionally independent: existential witnesses exposed while opening
    the invariant are local to the body proof, and the closing spine consumes
    whatever witnesses that proof produces.  Only the program-level invariant
    arguments are shared. *)
| RTInvAccessIndependent {Δ} invariant arguments body
    (external_pre body_pre body_post external_post : resource_prenex Γ F Δ)
    (opening_focus closing_focus :
      resource_access_focus invariant arguments Δ) :
    pexpr_list_dependencies arguments ## statement_writes body ->
    resource_access_opening invariant arguments opening_focus
      external_pre body_pre ->
    RavenResourceTriple body_pre body body_post ->
    resource_access_closing invariant arguments closing_focus
      body_post external_post ->
    RavenResourceTriple external_pre
      (TInvAccess invariant arguments body) external_post
| RTAtomicBlock {Δ} node (pre post : resource_prenex Γ F Δ) body :
    RavenResourceTriple pre body post ->
    RavenResourceTriple pre (TAtomic node body) post

(** *** Calls and spawn.  The result binder lands in the telescope; the
    "callee is declared and verified" guard is an explicit premise. *)
| RTCallDiscard {Δ} node procedure (store : symbolic_store Γ F Δ)
    (typed_arguments : pexpr_list Γ (Logic.procedure_args procedure)) :
    Contracts.procedure_verified procedure ->
    RavenResourceTriple
      (RState store
        (instantiated_pre procedure
          (symbolize_expr_list store typed_arguments)))
      (TCall node procedure typed_arguments
        (@CTDiscard Γ (Logic.procedure_return procedure)))
      (ResourceExists (Logic.procedure_return procedure)
        (RState (weaken_store store)
          (instantiated_post procedure
            (weaken_expr_list
              (symbolize_expr_list store typed_arguments)))))
| RTCallStore {Δ} node procedure (store : symbolic_store Γ F Δ)
    (typed_arguments : pexpr_list Γ (Logic.procedure_args procedure))
    (target : pvar Γ (Logic.procedure_return procedure)) :
    Contracts.procedure_verified procedure ->
    RavenResourceTriple
      (RState store
        (instantiated_pre procedure
          (symbolize_expr_list store typed_arguments)))
      (TCall node procedure typed_arguments (CTStore target))
      (ResourceExists (Logic.procedure_return procedure)
        (RState (update_store_with_bound store target)
          (instantiated_post procedure
            (weaken_expr_list
              (symbolize_expr_list store typed_arguments)))))
| RTSpawn {Δ} node procedure (store : symbolic_store Γ F Δ)
    (typed_arguments : pexpr_list Γ (Logic.procedure_args procedure)) :
    Contracts.procedure_verified procedure ->
    RavenResourceTriple
      (RState store
        (instantiated_pre procedure
          (symbolize_expr_list store typed_arguments)))
      (TSpawn node procedure typed_arguments)
      (RState store CTrue).

(** Telescope transport is deliberately stated over the completed access,
    not over [resource_access_boundary].  These are the three outcomes used
    by the joint body/fold cut: preservation retains the witness, elimination
    discharges it around the whole access, and weakening runs an access that
    is independent of the fresh binder. *)
Lemma RTInvAccessPrenexPreserve {Γ F Δ} t invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant)) body
    (pre post : resource_prenex Γ F (t :: Δ)) :
  RavenResourceTriple pre (TInvAccess invariant arguments body) post ->
  RavenResourceTriple (ResourceExists t pre)
    (TInvAccess invariant arguments body) (ResourceExists t post).
Proof. apply RTPrenexPreserve. Qed.

Lemma RTInvAccessPrenexElim {Γ F Δ} t invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant)) body
    (pre : resource_prenex Γ F (t :: Δ))
    (post : resource_prenex Γ F Δ) :
  RavenResourceTriple pre (TInvAccess invariant arguments body)
    (weaken_resource_prenex post) ->
  RavenResourceTriple (ResourceExists t pre)
    (TInvAccess invariant arguments body) post.
Proof. apply RTPrenexElim. Qed.

Lemma RTInvAccessBoundWeaken {Γ F Δ} t invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant)) body
    (pre post : resource_prenex Γ F Δ) :
  RavenResourceTriple pre (TInvAccess invariant arguments body) post ->
  RavenResourceTriple (weaken_resource_prenex (u := t) pre)
    (TInvAccess invariant arguments body)
    (weaken_resource_prenex (u := t) post).
Proof. apply RTBoundWeaken. Qed.

Lemma resource_access_opening_triple {Γ F Δ node invariant}
    (program_arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (focus : resource_access_focus invariant program_arguments Δ)
    (external body_pre : resource_prenex Γ F Δ) :
  resource_access_opening invariant program_arguments focus
    external body_pre ->
  RavenResourceTriple external
    (TUnfold node invariant program_arguments) body_pre.
Proof.
  intro Hopening. induction Hopening.
  - apply RTUnfoldInvariant.
  - apply RTPrenexPreserve. exact IHHopening.
  - apply RTBoundWeaken. exact IHHopening.
  - apply RTPrenexElim. exact IHHopening.
  - eapply RTPrenexConsequence; eassumption.
  - apply RTFrame. exact IHHopening.
  - eapply RTConsequence; eassumption.
  - eapply RTStackRewrite; eassumption.
Qed.

Lemma resource_access_opening_complete {Γ F Δ node invariant}
    (program_arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (external body_pre : resource_prenex Γ F Δ)
    (derivation : RavenResourceTriple external
      (TUnfold node invariant program_arguments) body_pre) :
  exists (focus : resource_access_focus invariant program_arguments Δ),
    resource_access_opening invariant program_arguments focus
      external body_pre.
Proof.
  dependent induction derivation.
  - destruct (IHderivation node invariant program_arguments eq_refl)
      as (focus & Hopening).
    exists (@ResourceAccessFocusPreserve Γ F invariant program_arguments
      Δ t focus).
    exact (@ResourceAccessOpeningPreserve Γ F invariant program_arguments
      Δ t focus pre post Hopening).
  - destruct (IHderivation node invariant program_arguments eq_refl)
      as (focus & Hopening).
    exists (@ResourceAccessFocusBoundWeaken Γ F invariant program_arguments
      Δ t focus).
    exact (@ResourceAccessOpeningBoundWeaken Γ F invariant program_arguments
      Δ t focus pre post Hopening).
  - destruct (IHderivation node invariant program_arguments eq_refl)
      as (focus & Hopening).
    exists (@ResourceAccessFocusElim Γ F invariant program_arguments
      Δ t focus).
    exact (@ResourceAccessOpeningElim Γ F invariant program_arguments
      Δ t focus pre post Hopening).
  - destruct (IHderivation node invariant program_arguments eq_refl)
      as (focus & Hopening). exists focus.
    eapply ResourceAccessOpeningPrenexConsequence; eassumption.
  - destruct (IHderivation node invariant program_arguments eq_refl)
      as (focus & Hopening). exists focus.
    apply ResourceAccessOpeningFrame. exact Hopening.
  - destruct (IHderivation node invariant program_arguments eq_refl)
      as (focus & Hopening). exists focus.
    eapply ResourceAccessOpeningConsequence; eassumption.
  - destruct (IHderivation node invariant program_arguments eq_refl)
      as (focus & Hopening). exists focus.
    eapply ResourceAccessOpeningStackRewrite; eassumption.
  - exists (@ResourceAccessFocusBase Γ F invariant program_arguments Δ
      (symbolize_expr_list store program_arguments)).
    apply ResourceAccessOpeningBase.
Qed.

(** Fold-side counterpart of [resource_access_opening_complete].  The focus
    records the telescope path and canonical argument vector selected by the fold
    derivation; the joint access cut later reconciles it with the opening
    focus through the body derivation. *)
Lemma resource_access_closing_complete {Γ F Δ node invariant}
    (program_arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (body_post external_post : resource_prenex Γ F Δ)
    (derivation : RavenResourceTriple body_post
      (TFold node invariant program_arguments) external_post) :
  exists (focus : resource_access_focus invariant program_arguments Δ),
    resource_access_closing invariant program_arguments focus
      body_post external_post.
Proof.
  dependent induction derivation.
  - destruct (IHderivation node invariant program_arguments eq_refl)
      as (focus & Hclosing).
    exists (@ResourceAccessFocusPreserve Γ F invariant program_arguments
      Δ t focus). apply ResourceAccessClosingPreserve. exact Hclosing.
  - destruct (IHderivation node invariant program_arguments eq_refl)
      as (focus & Hclosing).
    exists (@ResourceAccessFocusBoundWeaken Γ F invariant program_arguments
      Δ t focus). apply ResourceAccessClosingBoundWeaken. exact Hclosing.
  - destruct (IHderivation node invariant program_arguments eq_refl)
      as (focus & Hclosing).
    exists (@ResourceAccessFocusElim Γ F invariant program_arguments
      Δ t focus). apply ResourceAccessClosingElim. exact Hclosing.
  - destruct (IHderivation node invariant program_arguments eq_refl)
      as (focus & Hclosing). exists focus.
    eapply ResourceAccessClosingConsequence; eassumption.
  - destruct (IHderivation node invariant program_arguments eq_refl)
      as (focus & Hclosing). exists focus.
    change (resource_access_closing invariant program_arguments focus
      (prenex_and (RState store pre_body) frame) (prenex_and post frame)).
    apply ResourceAccessClosingFrame. exact Hclosing.
  - destruct (IHderivation node invariant program_arguments eq_refl)
      as (focus & Hclosing). exists focus.
    eapply ResourceAccessClosingConsequence with
      (body_post := RState store pre_body) (external_post := post).
    + apply RPEBody. split; [reflexivity|exact H].
    + exact Hclosing.
    + exact H0.
  - destruct (IHderivation node invariant program_arguments eq_refl)
      as (focus & Hclosing). exists focus.
    eapply ResourceAccessClosingStackRewrite; eassumption.
  - exists (@ResourceAccessFocusBase Γ F invariant program_arguments Δ
      (symbolize_expr_list store program_arguments)).
    apply ResourceAccessClosingBase.
Qed.

(** Canonical surface rule, now derived from the four-ended boundary rather
    than built into the calculus. *)
Lemma RTInvAccessBase {Γ F Δ} invariant
    (store : symbolic_store Γ F Δ)
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (frame : core_assertion F Δ) body
    (opened_post closed_post : resource_prenex Γ F Δ) :
  RavenResourceTriple
    (RState store
      (CAnd (instantiated_invariant invariant
        (symbolize_expr_list store arguments)) frame))
    body opened_post ->
  resource_access_closure invariant Δ
    (symbolize_expr_list store arguments)
    (instantiated_invariant invariant
      (symbolize_expr_list store arguments))
    opened_post closed_post ->
  RavenResourceTriple
    (RState store
      (CAnd (CInvariant invariant (symbolize_expr_list store arguments))
        frame))
    (TInvAccess invariant arguments body) closed_post.
Proof.
  intros Hbody Hclosure. eapply RTInvAccess.
  - apply resource_access_boundary_base. exact Hclosure.
  - exact Hbody.
Qed.

(** Normalize the two visible resource boundaries without changing the
    statement.  The recursive derivation preprocessor uses this operation at
    every constructor, so both children of a sequence choose the identical
    normal form for their shared assertion. *)
Lemma RavenResourceTriple_normalize_endpoints {Γ F Δ}
    (pre post : resource_prenex Γ F Δ) statement :
  RavenResourceTriple pre statement post ->
  RavenResourceTriple (Resource.normalize_resource_prenex pre) statement
    (Resource.normalize_resource_prenex post).
Proof.
  intro derivation.
  eapply RTPrenexConsequence.
  - exact derivation.
  - apply normalize_resource_prenex_entails_back.
  - apply normalize_resource_prenex_entails.
Qed.

Lemma RavenResourceTriple_denormalize_endpoints {Γ F Δ}
    (pre post : resource_prenex Γ F Δ) statement :
  RavenResourceTriple (Resource.normalize_resource_prenex pre) statement
    (Resource.normalize_resource_prenex post) ->
  RavenResourceTriple pre statement post.
Proof.
  intro derivation.
  eapply RTPrenexConsequence.
  - exact derivation.
  - apply normalize_resource_prenex_entails.
  - apply normalize_resource_prenex_entails_back.
Qed.

Lemma RavenResourceTriple_denormalize_pre {Γ F Δ}
    (pre post : resource_prenex Γ F Δ) statement :
  RavenResourceTriple (Resource.normalize_resource_prenex pre) statement post ->
  RavenResourceTriple pre statement post.
Proof.
  intro derivation. eapply RTPrenexConsequence.
  - exact derivation.
  - apply normalize_resource_prenex_entails.
  - apply resource_prenex_entails_refl.
Qed.

Lemma RavenResourceTriple_denormalize_post {Γ F Δ}
    (pre post : resource_prenex Γ F Δ) statement :
  RavenResourceTriple pre statement
    (Resource.normalize_resource_prenex post) ->
  RavenResourceTriple pre statement post.
Proof.
  intro derivation. eapply RTPrenexConsequence.
  - exact derivation.
  - apply resource_prenex_entails_refl.
  - apply normalize_resource_prenex_entails_back.
Qed.

(** Canonicalize every internal sequence cut.  This is proof preprocessing:
    the Raven statement is unchanged. *)
Fixpoint RavenResourceTriple_normalize_boundaries {Γ F Δ}
    (pre post : resource_prenex Γ F Δ) statement
    (derivation : RavenResourceTriple pre statement post)
    {struct derivation} :
  RavenResourceTriple (Resource.normalize_resource_prenex pre) statement
    (Resource.normalize_resource_prenex post).
Proof.
  destruct derivation.
  all: apply RavenResourceTriple_normalize_endpoints.
  - apply RTPrenexPreserve.
    apply RavenResourceTriple_denormalize_endpoints.
    apply RavenResourceTriple_normalize_boundaries. exact derivation.
  - apply RTBoundWeaken.
    apply RavenResourceTriple_denormalize_endpoints.
    apply RavenResourceTriple_normalize_boundaries. exact derivation.
  - apply RTPrenexElim.
    apply RavenResourceTriple_denormalize_endpoints.
    apply RavenResourceTriple_normalize_boundaries. exact derivation.
  - eapply RTPrenexConsequence.
    + apply RavenResourceTriple_denormalize_endpoints.
      apply RavenResourceTriple_normalize_boundaries. exact derivation.
    + exact H.
    + exact H0.
  - apply RTFrame.
    apply RavenResourceTriple_denormalize_endpoints.
    apply RavenResourceTriple_normalize_boundaries. exact derivation.
  - eapply RTConsequence.
    + apply RavenResourceTriple_denormalize_endpoints.
      apply RavenResourceTriple_normalize_boundaries. exact derivation.
    + exact H.
    + exact H0.
  - eapply RTStackRewrite.
    + apply RavenResourceTriple_denormalize_endpoints.
      apply RavenResourceTriple_normalize_boundaries. exact derivation.
    + exact H.
  - apply RTDone.
  - apply RTAssert.
  - apply RTAssign.
  - apply RTFieldRead.
  - apply RTFieldWrite.
  - apply RTAlloc; assumption.
  - apply RTGhostUpdate.
  - eapply RTSeq with (middle := Resource.normalize_resource_prenex middle).
    + apply RavenResourceTriple_denormalize_pre.
      apply RavenResourceTriple_normalize_boundaries. exact derivation1.
    + apply RavenResourceTriple_denormalize_post.
      apply RavenResourceTriple_normalize_boundaries. exact derivation2.
  - eapply RTIf.
    + apply RavenResourceTriple_denormalize_endpoints.
      apply RavenResourceTriple_normalize_boundaries. exact derivation1.
    + apply RavenResourceTriple_denormalize_endpoints.
      apply RavenResourceTriple_normalize_boundaries. exact derivation2.
  - apply RTUnfoldInvariant.
  - apply RTFoldInvariant.
  - apply RTUnfoldPredicate.
  - apply RTFoldPredicate.
  - eapply RTInvAccess; eassumption.
  - eapply RTInvAccessIndependent; eassumption.
  - apply RTAtomicBlock.
    apply RavenResourceTriple_denormalize_endpoints.
    apply RavenResourceTriple_normalize_boundaries. exact derivation.
  - apply RTCallDiscard. assumption.
  - apply RTCallStore. assumption.
  - apply RTSpawn. assumption.
Defined.

(** *** Derived rule: move a postcondition's core existential into the
    telescope.

    This is the operational face of [RPEOpenCoreExists].  A statement
    whose post is an [RState] with a top-level core existential -- the
    shape [RTUnfoldInvariant] produces for an existentially quantified
    invariant body -- is retyped so the binder sits in the prenex, where
    [RTPrenexPreserve] can derive under it and [RTPrenexElim] can discard
    it.  Composed with [RTSeq], this is also what supplies a
    binder-carrying *precondition* to the continuation: the resource
    calculus has no precondition-weakening rule at the prenex level, so
    the binder has to be moved on the producing side. *)
Lemma RTPostOpenCoreExists {Γ F Δ} t statement
    (store : symbolic_store Γ F Δ) (pre : core_assertion F Δ)
    (post_store : symbolic_store Γ F Δ) (post : core_assertion F (t :: Δ)) :
  RavenResourceTriple (RState store pre) statement
    (RState post_store (CExists t post)) ->
  RavenResourceTriple (RState store pre) statement
    (ResourceExists t (RState (weaken_store post_store) post)).
Proof.
  intro derivation.
  eapply RTConsequence.
  - exact derivation.
  - apply CEntailsRefl.
  - apply RPEOpenCoreExists.
Qed.

(** The two canonical sequence outcomes used by telescope focusing.  Keeping
    these as derived rules makes the consumer cut an induction over logical
    structure, rather than a continuation semantics. *)
Lemma RTSeqPrenexPreserve {Γ F Δ} t node
    (pre middle post : resource_prenex Γ F (t :: Δ)) first second :
  RavenResourceTriple pre first middle ->
  RavenResourceTriple middle second post ->
  RavenResourceTriple (ResourceExists t pre) (TSeq node first second)
    (ResourceExists t post).
Proof.
  intros Hfirst Hsecond. apply RTPrenexPreserve.
  eapply RTSeq; eassumption.
Qed.

Lemma RTSeqPrenexElim {Γ F Δ} t node
    (pre middle : resource_prenex Γ F (t :: Δ))
    (post : resource_prenex Γ F Δ) first second :
  RavenResourceTriple pre first middle ->
  RavenResourceTriple middle second (weaken_resource_prenex post) ->
  RavenResourceTriple (ResourceExists t pre) (TSeq node first second) post.
Proof.
  intros Hfirst Hsecond. apply RTPrenexElim.
  eapply RTSeq; eassumption.
Qed.

(** Once a focused binder has ceased to affect the intermediate assertion,
    an ordinary continuation can run below it by [RTBoundWeaken], after which
    the one outer elimination closes the complete sequence. *)
Lemma RTSeqPrenexElimClosedContinuation {Γ F Δ} t node
    (pre : resource_prenex Γ F (t :: Δ))
    (middle post : resource_prenex Γ F Δ) first second :
  RavenResourceTriple pre first (weaken_resource_prenex middle) ->
  RavenResourceTriple middle second post ->
  RavenResourceTriple (ResourceExists t pre) (TSeq node first second) post.
Proof.
  intros Hfirst Hsecond. apply RTPrenexElim.
  eapply RTSeq; [exact Hfirst |].
  apply RTBoundWeaken. exact Hsecond.
Qed.

(** A consumer of one distinguished outer binder has exactly two canonical
    outcomes.  It either eliminates the binder, in which case its inner
    derivation ends in a weakened outer postcondition, or preserves it and
    returns another outer existential.  A final prenex entailment records
    proof-only postcondition reshaping without obscuring the outcome. *)
Inductive existential_consumer_normal_form {Γ F Δ} (t : typ)
    (pre : resource_prenex Γ F (t :: Δ)) (statement : stmt Γ) :
    resource_prenex Γ F Δ -> Prop :=
| ExistentialConsumerEliminates
    (canonical_post : resource_prenex Γ F Δ) :
    RavenResourceTriple pre statement
      (weaken_resource_prenex canonical_post) ->
    forall requested_post,
      resource_prenex_entails canonical_post requested_post ->
      existential_consumer_normal_form t pre statement requested_post
| ExistentialConsumerPreserves
    (inner_post : resource_prenex Γ F (t :: Δ)) :
    RavenResourceTriple pre statement inner_post ->
    forall requested_post,
      resource_prenex_entails (ResourceExists t inner_post) requested_post ->
      existential_consumer_normal_form t pre statement requested_post.

Lemma existential_consumer_normal_form_rewrap {Γ F Δ t}
    {pre : resource_prenex Γ F (t :: Δ)} {statement : stmt Γ}
    {post : resource_prenex Γ F Δ} :
  existential_consumer_normal_form t pre statement post ->
  RavenResourceTriple (ResourceExists t pre) statement post.
Proof.
  intros Hnormal. destruct Hnormal.
  - eapply RTPrenexConsequence.
    + apply RTPrenexElim. exact H.
    + apply resource_prenex_entails_refl.
    + exact H0.
  - eapply RTPrenexConsequence.
    + apply RTPrenexPreserve. exact H.
    + apply resource_prenex_entails_refl.
    + exact H0.
Qed.

Lemma existential_consumer_normal_form_post_consequence {Γ F Δ t}
    {pre : resource_prenex Γ F (t :: Δ)} {statement : stmt Γ}
    {post post' : resource_prenex Γ F Δ} :
  existential_consumer_normal_form t pre statement post ->
  resource_prenex_entails post post' ->
  existential_consumer_normal_form t pre statement post'.
Proof.
  intros Hnormal Hpost. destruct Hnormal.
  - econstructor 1; [exact H |]. eapply RPETrans; eassumption.
  - econstructor 2; [exact H |]. eapply RPETrans; eassumption.
Qed.

(** Sequence composition after the first component has eliminated the
    binder.  Its accumulated post-entailment becomes the pre-consequence of
    the ordinary continuation, which is then weakened below the binder. *)
Lemma existential_consumer_normal_form_sequence_eliminated {Γ F Δ t}
    node {pre : resource_prenex Γ F (t :: Δ)}
    {middle post : resource_prenex Γ F Δ} {first second : stmt Γ}
    {inner_post : resource_prenex Γ F Δ}
    (Hfirst : RavenResourceTriple pre first
      (weaken_resource_prenex inner_post))
    (Hmiddle : resource_prenex_entails inner_post middle)
    (Hsecond : RavenResourceTriple middle second post) :
  existential_consumer_normal_form t pre (TSeq node first second) post.
Proof.
  econstructor 1.
  - eapply RTSeq; [exact Hfirst |].
    apply RTBoundWeaken. eapply RTPrenexConsequence.
    + exact Hsecond.
    + exact Hmiddle.
    + apply resource_prenex_entails_refl.
  - apply resource_prenex_entails_refl.
Qed.

(** If the first component preserves the binder, composition is entirely
    below it.  The caller supplies the recursively normalized second
    component, after using the first outcome's accumulated entailment as its
    source cut. *)
Lemma existential_consumer_normal_form_sequence_preserved {Γ F Δ t}
    node {pre middle : resource_prenex Γ F (t :: Δ)}
    {post : resource_prenex Γ F Δ} {first second : stmt Γ} :
  RavenResourceTriple pre first middle ->
  existential_consumer_normal_form t middle second post ->
  existential_consumer_normal_form t pre (TSeq node first second) post.
Proof.
  intros Hfirst Hsecond. destruct Hsecond.
  - econstructor 1; [| exact H0]. eapply RTSeq; eassumption.
  - econstructor 2; [| exact H0]. eapply RTSeq; eassumption.
Qed.

(** Logical half of the consumer cut.  Starting from a distinguished outer
    existential, an entailment either discharges that binder or preserves it
    as the outer binder of the target. *)
Inductive existential_source_cut {Γ F Δ} (t : typ)
    (body : resource_prenex Γ F (t :: Δ)) :
    resource_prenex Γ F Δ -> Prop :=
| ExistentialSourceEliminated (target : resource_prenex Γ F Δ) :
    resource_prenex_entails body (weaken_resource_prenex target) ->
    existential_source_cut t body target
| ExistentialSourcePreserved
    (focused : resource_prenex Γ F (t :: Δ)) :
    resource_prenex_entails body focused ->
    existential_source_cut t body (ResourceExists t focused).

Lemma existential_source_cut_entails {Γ F Δ t}
    {body : resource_prenex Γ F (t :: Δ)}
    {target : resource_prenex Γ F Δ} :
  existential_source_cut t body target ->
  resource_prenex_entails (ResourceExists t body) target.
Proof.
  intros Hcut. destruct Hcut.
  - eapply RPETrans.
    + apply RPEMono. exact H.
    + apply RPEVacuous.
  - apply RPEMono. exact H.
Qed.

(** The two telescope constructors after recursive boundary normalization.
    The elimination case uses logical equivalence rather than requiring
    normalization to commute with weakening by definitional equality. *)
Lemma normalize_prenex_preserve_consumer {Γ F Δ t statement}
    (pre post : resource_prenex Γ F (t :: Δ))
    (derivation : RavenResourceTriple pre statement post) :
  existential_consumer_normal_form t
    (Resource.normalize_resource_prenex pre) statement
    (Resource.normalize_resource_prenex (ResourceExists t post)).
Proof.
  cbn [Resource.normalize_resource_prenex].
  econstructor 2.
  - apply RavenResourceTriple_normalize_boundaries. exact derivation.
  - apply resource_prenex_entails_refl.
Qed.

Lemma normalize_prenex_elim_consumer {Γ F Δ t statement}
    (pre : resource_prenex Γ F (t :: Δ))
    (post : resource_prenex Γ F Δ)
    (derivation : RavenResourceTriple pre statement
      (Resource.weaken_resource_prenex post)) :
  existential_consumer_normal_form t
    (Resource.normalize_resource_prenex pre) statement
    (Resource.normalize_resource_prenex post).
Proof.
  econstructor 1.
  - eapply RTPrenexConsequence.
    + apply RavenResourceTriple_normalize_boundaries. exact derivation.
    + apply resource_prenex_entails_refl.
    + apply normalize_weaken_resource_prenex_entails.
  - apply resource_prenex_entails_refl.
Qed.

(** Complete consumer cut for the split resource grammar.  The current
    logical binder is a valid witness for the source existential, while the
    symbolic stack is merely weakened and is never substituted.  Therefore
    an arbitrary consumer can be run below the binder and the binder can be
    eliminated around the complete statement. *)
Lemma existential_consumer_normal_form_complete {Γ F Δ t statement}
    (body : resource_prenex Γ F (t :: Δ))
    (consumer_pre consumer_post : resource_prenex Γ F Δ)
    (source_entails : resource_prenex_entails
      (ResourceExists t body) consumer_pre)
    (consumer : RavenResourceTriple consumer_pre statement consumer_post) :
  existential_consumer_normal_form t body statement consumer_post.
Proof.
  econstructor 1.
  - eapply RTPrenexConsequence.
    + apply RTBoundWeaken. exact consumer.
    + apply RPEUnderExists. exact source_entails.
    + apply resource_prenex_entails_refl.
  - apply resource_prenex_entails_refl.
Qed.

Lemma RavenResourceTriple_under_exists {Γ F Δ t statement}
    (body : resource_prenex Γ F (t :: Δ))
    (consumer_pre consumer_post : resource_prenex Γ F Δ) :
  resource_prenex_entails (ResourceExists t body) consumer_pre ->
  RavenResourceTriple consumer_pre statement consumer_post ->
  RavenResourceTriple body statement
    (Resource.weaken_resource_prenex consumer_post).
Proof.
  intros Hsource Hconsumer. eapply RTPrenexConsequence.
  - apply RTBoundWeaken. exact Hconsumer.
  - apply RPEUnderExists. exact Hsource.
  - apply resource_prenex_entails_refl.
Qed.

(** Framing extends from a single resource state to an arbitrary resource
    telescope.  At an existential, run the original derivation below the
    binder, frame there with the weakened core assertion, and eliminate the
    binder around the complete statement. *)
Lemma RavenResourceTriple_prenex_frame {Γ F Δ statement}
    (pre post : resource_prenex Γ F Δ) (frame : core_assertion F Δ) :
  RavenResourceTriple pre statement post ->
  RavenResourceTriple (prenex_and pre frame) statement
    (prenex_and post frame).
Proof.
  revert post frame.
  induction pre as [Δ state | Δ t body IH]; intros post frame Htriple.
  - destruct state as [store pre_body]. apply RTFrame. exact Htriple.
  - apply RTPrenexElim.
    rewrite <- prenex_and_weaken.
    apply IH.
    eapply RavenResourceTriple_under_exists.
    + apply resource_prenex_entails_refl.
    + exact Htriple.
Qed.

(** Structural inversion for sequencing.  Proof-only wrappers are pushed to
    the appropriate side of the cut, so the returned intermediate assertion
    is a genuine resource telescope rather than a derivation-side artifact. *)
Lemma RavenResourceTriple_sequence_decompose {Γ F Δ node first second}
    (pre post : resource_prenex Γ F Δ) :
  RavenResourceTriple pre (TSeq node first second) post ->
  exists middle : resource_prenex Γ F Δ,
    RavenResourceTriple pre first middle /\
    RavenResourceTriple middle second post.
Proof.
  intro derivation. dependent induction derivation.
  - destruct (IHderivation node first second eq_refl) as (middle & Hfirst & Hsecond).
    exists (ResourceExists t middle). split.
    + apply RTPrenexPreserve. exact Hfirst.
    + apply RTPrenexPreserve. exact Hsecond.
  - destruct (IHderivation node first second eq_refl) as (middle & Hfirst & Hsecond).
    exists (weaken_resource_prenex middle). split.
    + apply RTBoundWeaken. exact Hfirst.
    + apply RTBoundWeaken. exact Hsecond.
  - destruct (IHderivation node first second eq_refl) as (middle & Hfirst & Hsecond).
    exists (ResourceExists t middle). split.
    + apply RTPrenexPreserve. exact Hfirst.
    + apply RTPrenexElim. exact Hsecond.
  - destruct (IHderivation node first second eq_refl) as (middle & Hfirst & Hsecond).
    exists middle. split.
    + eapply RTPrenexConsequence; [exact Hfirst|exact H|apply resource_prenex_entails_refl].
    + eapply RTPrenexConsequence; [exact Hsecond|apply resource_prenex_entails_refl|exact H0].
  - destruct (IHderivation node first second eq_refl) as (middle & Hfirst & Hsecond).
    exists (prenex_and middle frame). split.
    + apply RTFrame. exact Hfirst.
    + apply RavenResourceTriple_prenex_frame. exact Hsecond.
  - destruct (IHderivation node first second eq_refl) as (middle & Hfirst & Hsecond).
    exists middle. split.
    + eapply RTConsequence; [exact Hfirst|exact H|apply resource_prenex_entails_refl].
    + eapply RTPrenexConsequence; [exact Hsecond|apply resource_prenex_entails_refl|exact H0].
  - destruct (IHderivation node first second eq_refl) as (middle & Hfirst & Hsecond).
    exists middle. split.
    + eapply RTStackRewrite; eassumption.
    + exact Hsecond.
  - exists middle. split; assumption.
Qed.

(** The syntactic spine selected by the restricted normalizer can therefore
    be exposed without inspecting the proof term's outer structural rules. *)
Lemma RavenResourceTriple_unfold_body_fold_decompose {Γ F Δ}
    outer_node unfold_node body_sequence_node fold_node invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant)) body
    (pre post : resource_prenex Γ F Δ) :
  RavenResourceTriple pre
    (TSeq outer_node (TUnfold unfold_node invariant arguments)
      (TSeq body_sequence_node body
        (TFold fold_node invariant arguments))) post ->
  exists opened opened_post : resource_prenex Γ F Δ,
    RavenResourceTriple pre (TUnfold unfold_node invariant arguments) opened /\
    RavenResourceTriple opened body opened_post /\
    RavenResourceTriple opened_post
      (TFold fold_node invariant arguments) post.
Proof.
  intro derivation.
  destruct (RavenResourceTriple_sequence_decompose _ _ derivation)
    as (opened & Hunfold & Htail).
  destruct (RavenResourceTriple_sequence_decompose _ _ Htail)
    as (opened_post & Hbody & Hfold).
  exists opened, opened_post. repeat split; assumption.
Qed.

(** Complete proof-side exposure of a raw matched-access spine.  The two
    focus witnesses are kept separate here on purpose: reconciling them is
    precisely the remaining joint body/fold argument, whereas syntactic
    sequence inversion and wrapper extraction are now fully discharged. *)
Lemma RavenResourceTriple_unfold_body_fold_spines {Γ F Δ}
    outer_node unfold_node body_sequence_node fold_node invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant)) body
    (pre post : resource_prenex Γ F Δ) :
  RavenResourceTriple pre
    (TSeq outer_node (TUnfold unfold_node invariant arguments)
      (TSeq body_sequence_node body
        (TFold fold_node invariant arguments))) post ->
  exists opened opened_post : resource_prenex Γ F Δ,
    exists opening_focus closing_focus :
      resource_access_focus invariant arguments Δ,
    resource_access_opening invariant arguments opening_focus pre opened /\
    RavenResourceTriple opened body opened_post /\
    resource_access_closing invariant arguments closing_focus
      opened_post post.
Proof.
  intro derivation.
  destruct (RavenResourceTriple_unfold_body_fold_decompose
    outer_node unfold_node body_sequence_node fold_node invariant arguments
    body pre post derivation)
    as (opened & opened_post & Hunfold & Hbody & Hfold).
  destruct (resource_access_opening_complete arguments pre opened
    Hunfold) as (opening_focus & Hopening).
  destruct (resource_access_closing_complete arguments opened_post
    post Hfold) as (closing_focus & Hclosing).
  exists opened, opened_post, opening_focus, closing_focus.
  repeat split; assumption.
Qed.

(** Cut a binder-preserving prefix against an arbitrary outer consumer.
    The entailment is the logical fold boundary: it identifies the
    existentially closed result of [first] with the precondition expected by
    [second].  [RavenResourceTriple_under_exists] moves the consumer below the
    binder, so the complete sequence can be derived there and eliminated only
    once, around both statements. *)
Lemma RTSeqPrenexConsumerCut {Γ F Δ t} node
    (body middle : resource_prenex Γ F (t :: Δ))
    (consumer_pre consumer_post : resource_prenex Γ F Δ)
    (first second : stmt Γ) :
  RavenResourceTriple body first middle ->
  resource_prenex_entails (ResourceExists t middle) consumer_pre ->
  RavenResourceTriple consumer_pre second consumer_post ->
  RavenResourceTriple (ResourceExists t body)
    (TSeq node first second) consumer_post.
Proof.
  intros Hfirst Hcut Hsecond. apply RTPrenexElim.
  eapply RTSeq; [exact Hfirst |].
  eapply RavenResourceTriple_under_exists; eassumption.
Qed.

(** Assemble a matched invariant access with an arbitrary continuation once
    the fold-side closure has been exposed.  The closed access postcondition
    need only entail the continuation precondition; telescope binders may
    already occur inside [opened_post] and [closed_post]. *)
Lemma RTInvAccessThen {Γ F Δ} node invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (store : symbolic_store Γ F Δ) (frame : core_assertion F Δ) body
    (opened_post closed_post consumer_pre consumer_post :
      resource_prenex Γ F Δ) work :
  RavenResourceTriple
    (RState store
      (CAnd
        (instantiated_invariant invariant
          (symbolize_expr_list store arguments)) frame))
    body opened_post ->
  resource_access_closure invariant Δ
    (symbolize_expr_list store arguments)
    (instantiated_invariant invariant
      (symbolize_expr_list store arguments))
    opened_post closed_post ->
  resource_prenex_entails closed_post consumer_pre ->
  RavenResourceTriple consumer_pre work consumer_post ->
  RavenResourceTriple
    (RState store
      (CAnd
        (CInvariant invariant (symbolize_expr_list store arguments)) frame))
    (TSeq node (TInvAccess invariant arguments body) work) consumer_post.
Proof.
  intros Hbody Hclosure Hcut Hwork. eapply RTSeq.
  - eapply RTInvAccess.
    + apply resource_access_boundary_base. exact Hclosure.
    + exact Hbody.
  - eapply RTPrenexConsequence; [exact Hwork | exact Hcut |].
    apply resource_prenex_entails_refl.
Qed.

(** Canonical matched-boundary leaf.  The body may change the symbolic
    store, but the fold arguments are already expressed in the body's exit
    context.  Ordinary fold consequence supplies both the strengthened fold
    precondition and the cut into the following statement. *)
Lemma RTInvAccessThenFoldConsequence {Γ F Δ} node invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (input_store fold_store : symbolic_store Γ F Δ)
    (frame pre_body : core_assertion F Δ) body
    (consumer_pre consumer_post : resource_prenex Γ F Δ) work :
  RavenResourceTriple
    (RState input_store
      (CAnd
        (instantiated_invariant invariant
          (symbolize_expr_list input_store arguments)) frame))
    body (RState fold_store pre_body) ->
  core_entails pre_body
    (instantiated_invariant invariant
      (symbolize_expr_list input_store arguments)) ->
  resource_prenex_entails
    (RState fold_store
      (CInvariant invariant
        (symbolize_expr_list input_store arguments))) consumer_pre ->
  RavenResourceTriple consumer_pre work consumer_post ->
  RavenResourceTriple
    (RState input_store
      (CAnd
        (CInvariant invariant
          (symbolize_expr_list input_store arguments)) frame))
    (TSeq node (TInvAccess invariant arguments body) work) consumer_post.
Proof.
  intros Hbody Hfold_pre Hcut Hwork.
  eapply RTInvAccessThen with
    (opened_post := RState fold_store pre_body)
    (closed_post := RState fold_store
      (CInvariant invariant (symbolize_expr_list input_store arguments)))
    (consumer_pre := consumer_pre).
  - exact Hbody.
  - apply resource_access_closure_fold_consequence.
    + exact Hfold_pre.
    + apply resource_prenex_entails_refl.
  - exact Hcut.
  - exact Hwork.
Qed.

(** Complete access-plus-continuation leaf when the fold is performed after a
    proof-only symbolic-store rewrite. *)
Lemma RTInvAccessThenFoldStoreRewrite {Γ F Δ} node invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (input_store closing_store : symbolic_store Γ F Δ)
    (frame fold_pre : core_assertion F Δ) body
    (consumer_pre consumer_post : resource_prenex Γ F Δ) work :
  RavenResourceTriple
    (RState input_store
      (CAnd
        (instantiated_invariant invariant
          (symbolize_expr_list input_store arguments)) frame))
    body (RState input_store fold_pre) ->
  core_entails fold_pre
    (instantiated_invariant invariant
      (symbolize_expr_list closing_store arguments)) ->
  resource_prenex_entails
    (RState closing_store
      (CInvariant invariant
        (symbolize_expr_list closing_store arguments))) consumer_pre ->
  store_equal_under fold_pre Γ input_store closing_store ->
  RavenResourceTriple consumer_pre work consumer_post ->
  RavenResourceTriple
    (RState input_store
      (CAnd
        (CInvariant invariant
          (symbolize_expr_list input_store arguments)) frame))
    (TSeq node (TInvAccess invariant arguments body) work) consumer_post.
Proof.
  intros Hbody Hfold_pre Hfold_post Hstore Hwork.
  eapply RTInvAccessThen with
    (opened_post := RState input_store fold_pre)
    (closed_post := consumer_pre) (consumer_pre := consumer_pre).
  - exact Hbody.
  - eapply resource_access_closure_fold_store_rewrite; eassumption.
  - apply resource_prenex_entails_refl.
  - exact Hwork.
Qed.

(** Terminal form of [RTInvAccessThenFoldStoreRewrite]. *)
Lemma RTInvAccessFoldStoreRewrite {Γ F Δ} invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (input_store closing_store : symbolic_store Γ F Δ)
    (frame fold_pre : core_assertion F Δ) body
    (post : resource_prenex Γ F Δ) :
  RavenResourceTriple
    (RState input_store
      (CAnd
        (instantiated_invariant invariant
          (symbolize_expr_list input_store arguments)) frame))
    body (RState input_store fold_pre) ->
  core_entails fold_pre
    (instantiated_invariant invariant
      (symbolize_expr_list closing_store arguments)) ->
  resource_prenex_entails
    (RState closing_store
      (CInvariant invariant
        (symbolize_expr_list closing_store arguments))) post ->
  store_equal_under fold_pre Γ input_store closing_store ->
  RavenResourceTriple
    (RState input_store
      (CAnd
        (CInvariant invariant
          (symbolize_expr_list input_store arguments)) frame))
    (TInvAccess invariant arguments body) post.
Proof.
  intros Hbody Hfold_pre Hfold_post Hstore.
  eapply RTInvAccess.
  - apply resource_access_boundary_base.
    eapply resource_access_closure_fold_store_rewrite; eassumption.
  - exact Hbody.
Qed.

(** The fold-boundary instance used by continued matched-access
    normalization.  The access is proved while the focused logical binder is
    in scope; its closed result is then related to the outer continuation.
    Applying this lemma once per outer [ResourceExists] moves an arbitrary
    telescope of result binders around the complete access-plus-continuation
    segment. *)
Lemma RTInvAccessThenConsumerCut {Γ F Δ t} node invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (store : symbolic_store Γ F (t :: Δ))
    (frame : core_assertion F (t :: Δ)) body
    (opened_post closed_post : resource_prenex Γ F (t :: Δ))
    (consumer_pre consumer_post : resource_prenex Γ F Δ) work :
  RavenResourceTriple
    (RState store
      (CAnd
        (instantiated_invariant invariant
          (symbolize_expr_list store arguments)) frame))
    body opened_post ->
  resource_access_closure invariant (t :: Δ)
    (symbolize_expr_list store arguments)
    (instantiated_invariant invariant
      (symbolize_expr_list store arguments))
    opened_post closed_post ->
  resource_prenex_entails (ResourceExists t closed_post) consumer_pre ->
  RavenResourceTriple consumer_pre work consumer_post ->
  RavenResourceTriple
    (ResourceExists t
      (RState store
        (CAnd
          (CInvariant invariant (symbolize_expr_list store arguments))
          frame)))
    (TSeq node (TInvAccess invariant arguments body) work) consumer_post.
Proof.
  intros Hbody Hclosure Hcut Hwork.
  eapply RTSeqPrenexConsumerCut; [| exact Hcut | exact Hwork].
  eapply RTInvAccess.
  - apply resource_access_boundary_base. exact Hclosure.
  - exact Hbody.
Qed.

(** One telescope layer around the canonical consequence-wrapped fold.
    Repeated application handles any result telescope produced by the access
    body before the continuation resumes in the outer context. *)
Lemma RTInvAccessThenFoldConsequenceConsumerCut {Γ F Δ t} node invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (input_store fold_store : symbolic_store Γ F (t :: Δ))
    (frame fold_pre : core_assertion F (t :: Δ)) body
    (consumer_pre consumer_post : resource_prenex Γ F Δ) work :
  RavenResourceTriple
    (RState input_store
      (CAnd
        (instantiated_invariant invariant
          (symbolize_expr_list input_store arguments)) frame))
    body (RState fold_store fold_pre) ->
  core_entails fold_pre
    (instantiated_invariant invariant
      (symbolize_expr_list input_store arguments)) ->
  resource_prenex_entails
    (ResourceExists t
      (RState fold_store
        (CInvariant invariant
          (symbolize_expr_list input_store arguments)))) consumer_pre ->
  RavenResourceTriple consumer_pre work consumer_post ->
  RavenResourceTriple
    (ResourceExists t
      (RState input_store
        (CAnd
          (CInvariant invariant
            (symbolize_expr_list input_store arguments)) frame)))
    (TSeq node (TInvAccess invariant arguments body) work) consumer_post.
Proof.
  intros Hbody Hfold_pre Hcut Hwork.
  eapply RTInvAccessThenConsumerCut with
    (opened_post := RState fold_store fold_pre)
    (closed_post := RState fold_store
      (CInvariant invariant (symbolize_expr_list input_store arguments)))
    (consumer_pre := consumer_pre).
  - exact Hbody.
  - apply resource_access_closure_fold_consequence.
    + exact Hfold_pre.
    + apply resource_prenex_entails_refl.
  - exact Hcut.
  - exact Hwork.
Qed.

Corollary existential_consumer_normal_form_of_triple {Γ F Δ t statement}
    (body : resource_prenex Γ F (t :: Δ))
    (post : resource_prenex Γ F Δ) :
  RavenResourceTriple (ResourceExists t body) statement post ->
  existential_consumer_normal_form t body statement post.
Proof.
  apply existential_consumer_normal_form_complete.
  apply resource_prenex_entails_refl.
Qed.

End ResourceRules.

End Make.
End TypedResourceHoare.
