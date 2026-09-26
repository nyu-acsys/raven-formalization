From Coq Require Import Classical FunctionalExtensionality Program.Equality.
From iris.proofmode Require Import tactics.

From raven Require Import verification.expressions verification.assertions verification.ir verification.procedures soundness.interpretation.

(** Semantic validity of the typed entailment and Hoare calculi. *)
Module TypedValidity.

Import TypedCore TypedIR.

Module Make (RAs : RA_VALUE_CONFIG) (Logic : TypedAssertion.LOGIC_SIGNATURE).
Module Translation := TypedTranslation.Make RAs Logic.
Module Hoare := Translation.Hoare.
Module IR := Translation.IR.
Module Core := Translation.Core.
Module Assertions := Translation.Assertions.
Module Resource := Translation.Resource.
Import Core Assertions IR Hoare Translation.

(** Validity over a semantic model supplied as a term, so adequacy may
    construct [Model] after allocating Iris ghost names. *)
Module TermSemantics.
Section WithModel.
Context {PROP : bi} (Model : Translation.semantic_config_data PROP).
Let term_bi_affine : BiAffine PROP :=
  @Translation.data_bi_affine PROP Model.
Local Existing Instance term_bi_affine.
Local Notation iProp := (bi_car PROP).
Local Notation interp_assertion :=
  (Translation.TermSemantics.interp_assertion Model).
Local Notation interp_core :=
  (Translation.TermSemantics.interp_core Model).
Local Notation interp_resource :=
  (Translation.TermSemantics.interp_resource Model).
Local Notation interp_resource_prenex :=
  (Translation.TermSemantics.interp_resource_prenex Model).

Definition predicate_semantics := forall predicate,
  Translation.tval_list (Logic.predicate_args predicate) -> iProp.

Section EntailmentValidity.
Context (predicates : predicate_semantics).

Definition semantically_entails {Γ F Δ}
    (left right : assertion Γ F Δ) : Prop :=
  forall (runtime : Translation.data_stack_context Model Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env),
    interp_assertion predicates runtime formals binders atoms left ⊢
    interp_assertion predicates runtime formals binders atoms right.

Lemma entailment_step_valid {Γ F Δ}
    (left right : assertion Γ F Δ) :
  entailment_step left right -> semantically_entails left right.
Proof.
  intros Hstep runtime formals binders atoms.
  destruct Hstep; cbn [Translation.TermSemantics.interp_assertion].
  - iIntros "[Hleft Hright]". iFrame.
  - iIntros "[[Hfirst Hsecond] Hthird]". iFrame.
  - iIntros "[Hfirst [Hsecond Hthird]]". iFrame.
  - iIntros "[Hleft _]". iExact "Hleft".
  - iIntros "[_ Hright]". iExact "Hright".
  - iIntros "H". iFrame.
  - iIntros "_". done.
  - iIntros "%Hleft". iPureIntro. exact (H Hleft).
  - iIntros "[Hite %Hcondition]".
    iDestruct "Hite" as "[Hthen _]". iApply "Hthen". done.
  - iIntros "[Hite %Hcondition]".
    iDestruct "Hite" as "[_ Helse]". iApply "Helse".
    iPureIntro. intro Htrue. simpl in Hcondition.
    rewrite Htrue in Hcondition. discriminate.
  - iIntros "[Hthen %Hcondition]". iSplit.
    + iIntros "_". iExact "Hthen".
    + iIntros "%Hfalse". exfalso. exact (Hfalse Hcondition).
  - iIntros "[Helse %Hcondition]". iSplit.
    + iIntros "%Htrue". exfalso. simpl in Hcondition.
      rewrite Htrue in Hcondition. discriminate.
    + iIntros "_". iExact "Helse".
  - iIntros "H". iDestruct "H" as "[Hite Hindicator]".
    iDestruct "Hindicator" as %Hindicator.
    destruct (interp_expr formals binders atoms condition) as [value|]
      eqn:Hcondition.
    + dependent destruction value. destruct b.
      * iDestruct "Hite" as "[Hthen _]".
        iDestruct ("Hthen" with "[]") as "[Hbranch _]"; first done.
        iFrame. done.
      * iDestruct "Hite" as "[_ Helse]".
        iDestruct ("Helse" with "[]") as "[_ %Heq]".
        { iPureIntro. congruence. }
        cbn [interp_expr interp_binop] in Heq.
        rewrite Hindicator in Heq. discriminate.
    + iDestruct "Hite" as "[_ Helse]".
      iDestruct ("Helse" with "[]") as "[_ %Heq]".
      { iPureIntro. congruence. }
      cbn [interp_expr interp_binop] in Heq.
      rewrite Hindicator in Heq. discriminate.
  - iIntros "H". iDestruct "H" as "[Hite Hindicator]".
    iDestruct "Hindicator" as %Hindicator.
    assert (Hindicator_false :
      interp_expr formals binders atoms indicator = Some (VBool false)).
    { cbn [interp_expr] in Hindicator.
      destruct (interp_expr formals binders atoms indicator) as [value|]
        eqn:Hvalue; [|discriminate].
      dependent destruction value. destruct b; inversion Hindicator. reflexivity. }
    destruct (interp_expr formals binders atoms condition) as [value|]
      eqn:Hcondition.
    + dependent destruction value. destruct b.
      * iDestruct "Hite" as "[Hthen _]".
        iDestruct ("Hthen" with "[]") as "[_ %Heq]"; first done.
        cbn [interp_expr interp_binop] in Heq.
        rewrite Hindicator_false in Heq. discriminate.
      * iDestruct "Hite" as "[_ Helse]".
        iDestruct ("Helse" with "[]") as "[Hbranch _]".
        { iPureIntro. congruence. }
        iExact "Hbranch".
    + iDestruct "Hite" as "[_ Helse]".
      iDestruct ("Helse" with "[]") as "[Hbranch _]".
      { iPureIntro. congruence. }
      iExact "Hbranch".
  - iIntros "%Hleft". iPureIntro. exact (H formals binders atoms Hleft).
  - iIntros "_". iPureIntro. exact (H formals binders atoms).
  - iIntros "_".
    destruct (interp_expr_total formals binders atoms expression) as [value Hvalue].
    iPureIntro. exists value. split; [exact Hvalue|].
    eapply H. exact Hvalue.
  - iIntros "_".
    destruct (interp_expr_total formals binders atoms old_expression)
      as [old_value Hold].
    destruct (interp_expr_total formals binders atoms new_expression)
      as [new_value Hnew].
    iPureIntro. exists old_value, new_value. repeat split; try assumption.
    eapply H; eassumption.
  - iIntros "Hown". iDestruct "Hown" as (concrete_location concrete_chunk)
      "(%Hlocation & %Hchunk & Hown)".
    iExists concrete_location, concrete_chunk. iSplit; first done.
    iSplit; last iExact "Hown". iPureIntro.
    rewrite <- Hchunk, <- (H formals binders atoms). reflexivity.
  - iIntros "Hown". iDestruct "Hown" as (concrete_location concrete_chunk)
      "(%Hlocation & %Hchunk & Hown)".
    iExists concrete_location, concrete_chunk. iSplit; first done.
    iSplit; last iExact "Hown". iPureIntro.
    rewrite <- Hchunk, <- (H formals binders atoms). reflexivity.
  - iIntros "[Hown %Hcondition]".
    iDestruct "Hown" as (concrete_location concrete_chunk)
      "(%Hlocation & %Hchunk & Hown)".
    iExists concrete_location, concrete_chunk. iSplit; first done.
    iSplit; last iExact "Hown". iPureIntro.
    rewrite <- Hchunk, <- (H formals binders atoms Hcondition). reflexivity.
  - iIntros "[Hown %Hcondition]".
    iDestruct "Hown" as (concrete_location concrete_chunk)
      "(%Hlocation & %Hchunk & Hown)".
    iExists concrete_location, concrete_chunk. iSplit; first done.
    iSplit; last iExact "Hown". iPureIntro.
    rewrite <- Hchunk, <- (H formals binders atoms Hcondition). reflexivity.
  - iIntros "[Hinv %Hcondition]".
    iDestruct "Hinv" as (values) "[%Harguments Hinv]".
    iExists values. iFrame. iPureIntro.
    rewrite <- Harguments. symmetry.
    apply Translation.interp_expr_list_equal_assuming with
      (condition := condition); assumption.
  - iIntros "[Hpredicate %Hcondition]".
    iDestruct "Hpredicate" as (values) "[%Harguments Hpredicate]".
    iExists values. iFrame. iPureIntro.
    rewrite <- Harguments. symmetry.
    apply Translation.interp_expr_list_equal_assuming with
      (condition := condition); assumption.
  - apply Translation.data_stack_own_exclusive.
Qed.

Theorem assertion_entails_valid {Γ F Δ}
    (left right : assertion Γ F Δ) :
  assertion_entails left right -> semantically_entails left right.
Proof.
  intros Hentails. induction Hentails;
    intros runtime formals binders atoms.
  - reflexivity.
  - apply entailment_step_valid. exact H.
  - etrans; [apply IHHentails1 | apply IHHentails2].
  - cbn [Translation.TermSemantics.interp_assertion].
    iIntros "[Hleft Hright]". iSplitL "Hleft".
    + iApply IHHentails1. iExact "Hleft".
    + iApply IHHentails2. iExact "Hright".
  - cbn [Translation.TermSemantics.interp_assertion]. iIntros "H".
    iDestruct "H" as (value) "Hbody". iExists value.
    iApply IHHentails. iExact "Hbody".
  - cbn [Translation.TermSemantics.interp_assertion].
    iIntros "Hinstantiated".
    destruct (interp_expr_total formals binders atoms witness)
      as [value Hvalue].
    iExists value.
    erewrite <- (Translation.TermSemantics.interp_instantiate_bound_assertion
      Model predicates); [|exact Hvalue|exact H].
    iExact "Hinstantiated".
  - cbn [Translation.TermSemantics.interp_assertion]. iIntros "H".
    iDestruct "H" as (value) "Hbody".
    iPoseProof (IHHentails runtime formals (binder_cons value binders) atoms
      with "Hbody") as "Hresult".
    iEval (rewrite Translation.TermSemantics.interp_weaken_assertion) in
      "Hresult". iExact "Hresult".
  - cbn [Translation.TermSemantics.interp_assertion].
    iIntros "[Hbody Hframe]".
    iDestruct "Hbody" as (value) "Hbody". iExists value.
    iFrame "Hbody".
    rewrite Translation.TermSemantics.interp_weaken_assertion.
    iExact "Hframe".
  - cbn [Translation.TermSemantics.interp_assertion]. iIntros "H".
    iDestruct "H" as (value) "[Hbody Hframe]". iSplitL "Hbody".
    + iExists value. iExact "Hbody".
    + iEval (rewrite Translation.TermSemantics.interp_weaken_assertion) in
        "Hframe". iExact "Hframe".
  - cbn [Translation.TermSemantics.interp_assertion].
    iIntros "[Hframe Hbody]".
    iDestruct "Hbody" as (value) "Hbody". iExists value.
    rewrite Translation.TermSemantics.interp_weaken_assertion. iFrame.
  - cbn [Translation.TermSemantics.interp_assertion]. iIntros "H".
    iSplit.
    + iDestruct "H" as "[Hthen _]".
      iIntros "%Hcondition". iApply IHHentails1.
      iApply "Hthen". iPureIntro. exact Hcondition.
    + iDestruct "H" as "[_ Helse]".
      iIntros "%Hcondition". iApply IHHentails2.
      iApply "Helse". iPureIntro. exact Hcondition.
  - cbn [Translation.TermSemantics.interp_assertion]. iIntros "H".
    iExists (Core.default_tval t).
    rewrite Translation.TermSemantics.interp_weaken_assertion. iExact "H".
  - cbn [Translation.TermSemantics.interp_assertion]. iIntros "H".
    iSplit.
    + iDestruct "H" as (value) "[Hthen _]".
      iIntros "%Hcondition". iExists value. iApply "Hthen".
      rewrite Translation.interp_weaken_expr.
      iPureIntro. exact Hcondition.
    + iDestruct "H" as (value) "[_ Helse]".
      iIntros "%Hcondition". iExists value. iApply "Helse".
      rewrite Translation.interp_weaken_expr.
      iPureIntro. exact Hcondition.
  - cbn [Translation.TermSemantics.interp_assertion]. iIntros "H".
    destruct (classic
      (Core.interp_expr formals binders atoms condition =
        Some (Core.VBool true))) as [Hcondition|Hcondition].
    + iDestruct "H" as "[Hthen _]".
      iPoseProof ("Hthen" $! Hcondition) as "Hthen".
      iDestruct "Hthen" as (value) "Hbody". iExists value. iSplit.
      * iIntros "_". iExact "Hbody".
      * iIntros "%Hfalse".
        rewrite Translation.interp_weaken_expr in Hfalse. contradiction.
    + iDestruct "H" as "[_ Helse]".
      iPoseProof ("Helse" $! Hcondition) as "Helse".
      iDestruct "Helse" as (value) "Hbody". iExists value. iSplit.
      * iIntros "%Hfalse".
        rewrite Translation.interp_weaken_expr in Hfalse. contradiction.
      * iIntros "_". iExact "Hbody".
  - cbn [Translation.TermSemantics.interp_assertion]. iIntros "H".
    iDestruct "H" as (t_value) "H".
    iDestruct "H" as (u_value) "H".
    iExists u_value, t_value.
    rewrite (Translation.TermSemantics.interp_rename_bound_assertion
      Model predicates (@exchange_bound_renaming Δ u t) formals
      (binder_cons u_value (binder_cons t_value binders))
      (binder_cons t_value (binder_cons u_value binders)) atoms runtime
      (binder_cons_exchange t_value u_value binders) body).
    iExact "H".
  - cbn [Translation.TermSemantics.interp_assertion]. iIntros "H" (value).
    iApply (IHHentails runtime formals (binder_cons value binders) atoms).
    iApply ("H" $! value).
Qed.

(** *** Soundness of the resource core's entailment

    Proved directly over [interp_core]; nothing here routes through the
    assertion grammar.  The argument is the one behind
    [entailment_step_valid]/[assertion_entails_valid] above, one case
    shorter: [ESStackExclusive] has no core counterpart, because a core
    assertion cannot mention the symbolic store at all. *)
Definition core_semantically_entails {F Δ}
    (left right : Resource.core_assertion F Δ) : Prop :=
  forall (formals : formal_env F) (binders : binder_env Δ)
    (atoms : atom_env),
    interp_core predicates formals binders atoms left ⊢
    interp_core predicates formals binders atoms right.

Lemma core_entailment_step_valid {F Δ}
    (left right : Resource.core_assertion F Δ) :
  Hoare.ResourceHoare.core_entailment_step left right -> core_semantically_entails left right.
Proof.
  intros Hstep formals binders atoms.
  destruct Hstep; cbn [Translation.TermSemantics.interp_core].
  - iIntros "[Hleft Hright]". iFrame.
  - iIntros "[[Hfirst Hsecond] Hthird]". iFrame.
  - iIntros "[Hfirst [Hsecond Hthird]]". iFrame.
  - iIntros "[Hleft _]". iExact "Hleft".
  - iIntros "[_ Hright]". iExact "Hright".
  - iIntros "H". iFrame.
  - iIntros "_". done.
  - iIntros "%Hleft". iPureIntro. exact (H Hleft).
  - iIntros "[Hite %Hcondition]".
    iDestruct "Hite" as "[Hthen _]". iApply "Hthen". done.
  - iIntros "[Hite %Hcondition]".
    iDestruct "Hite" as "[_ Helse]". iApply "Helse".
    iPureIntro. intro Htrue. simpl in Hcondition.
    rewrite Htrue in Hcondition. discriminate.
  - iIntros "[Hthen %Hcondition]". iSplit.
    + iIntros "_". iExact "Hthen".
    + iIntros "%Hfalse". exfalso. exact (Hfalse Hcondition).
  - iIntros "[Helse %Hcondition]". iSplit.
    + iIntros "%Htrue". exfalso. simpl in Hcondition.
      rewrite Htrue in Hcondition. discriminate.
    + iIntros "_". iExact "Helse".
  - iIntros "H". iDestruct "H" as "[Hite Hindicator]".
    iDestruct "Hindicator" as %Hindicator.
    destruct (interp_expr formals binders atoms condition) as [value|]
      eqn:Hcondition.
    + dependent destruction value. destruct b.
      * iDestruct "Hite" as "[Hthen _]".
        iDestruct ("Hthen" with "[]") as "[Hbranch _]"; first done.
        iFrame. done.
      * iDestruct "Hite" as "[_ Helse]".
        iDestruct ("Helse" with "[]") as "[_ %Heq]".
        { iPureIntro. congruence. }
        cbn [interp_expr interp_binop] in Heq.
        rewrite Hindicator in Heq. discriminate.
    + iDestruct "Hite" as "[_ Helse]".
      iDestruct ("Helse" with "[]") as "[_ %Heq]".
      { iPureIntro. congruence. }
      cbn [interp_expr interp_binop] in Heq.
      rewrite Hindicator in Heq. discriminate.
  - iIntros "H". iDestruct "H" as "[Hite Hindicator]".
    iDestruct "Hindicator" as %Hindicator.
    assert (Hindicator_false :
      interp_expr formals binders atoms indicator = Some (VBool false)).
    { cbn [interp_expr] in Hindicator.
      destruct (interp_expr formals binders atoms indicator) as [value|]
        eqn:Hvalue; [|discriminate].
      dependent destruction value. destruct b; inversion Hindicator. reflexivity. }
    destruct (interp_expr formals binders atoms condition) as [value|]
      eqn:Hcondition.
    + dependent destruction value. destruct b.
      * iDestruct "Hite" as "[Hthen _]".
        iDestruct ("Hthen" with "[]") as "[_ %Heq]"; first done.
        cbn [interp_expr interp_binop] in Heq.
        rewrite Hindicator_false in Heq. discriminate.
      * iDestruct "Hite" as "[_ Helse]".
        iDestruct ("Helse" with "[]") as "[Hbranch _]".
        { iPureIntro. congruence. }
        iExact "Hbranch".
    + iDestruct "Hite" as "[_ Helse]".
      iDestruct ("Helse" with "[]") as "[Hbranch _]".
      { iPureIntro. congruence. }
      iExact "Hbranch".
  - iIntros "%Hleft". iPureIntro. exact (H formals binders atoms Hleft).
  - iIntros "_". iPureIntro. exact (H formals binders atoms).
  - iIntros "_".
    destruct (interp_expr_total formals binders atoms expression) as [value Hvalue].
    iPureIntro. exists value. split; [exact Hvalue|].
    eapply H. exact Hvalue.
  - iIntros "_".
    destruct (interp_expr_total formals binders atoms old_expression)
      as [old_value Hold].
    destruct (interp_expr_total formals binders atoms new_expression)
      as [new_value Hnew].
    iPureIntro. exists old_value, new_value. repeat split; try assumption.
    eapply H; eassumption.
  - iIntros "Hown". iDestruct "Hown" as (concrete_location concrete_chunk)
      "(%Hlocation & %Hchunk & Hown)".
    iExists concrete_location, concrete_chunk. iSplit; first done.
    iSplit; last iExact "Hown". iPureIntro.
    rewrite <- Hchunk, <- (H formals binders atoms). reflexivity.
  - iIntros "Hown". iDestruct "Hown" as (concrete_location concrete_chunk)
      "(%Hlocation & %Hchunk & Hown)".
    iExists concrete_location, concrete_chunk. iSplit; first done.
    iSplit; last iExact "Hown". iPureIntro.
    rewrite <- Hchunk, <- (H formals binders atoms). reflexivity.
  - iIntros "[Hown %Hcondition]".
    iDestruct "Hown" as (concrete_location concrete_chunk)
      "(%Hlocation & %Hchunk & Hown)".
    iExists concrete_location, concrete_chunk. iSplit; first done.
    iSplit; last iExact "Hown". iPureIntro.
    rewrite <- Hchunk, <- (H formals binders atoms Hcondition). reflexivity.
  - iIntros "[Hown %Hcondition]".
    iDestruct "Hown" as (concrete_location concrete_chunk)
      "(%Hlocation & %Hchunk & Hown)".
    iExists concrete_location, concrete_chunk. iSplit; first done.
    iSplit; last iExact "Hown". iPureIntro.
    rewrite <- Hchunk, <- (H formals binders atoms Hcondition). reflexivity.
  - iIntros "[Hinv %Hcondition]".
    iDestruct "Hinv" as (values) "[%Harguments Hinv]".
    iExists values. iFrame. iPureIntro.
    rewrite <- Harguments. symmetry.
    apply Translation.interp_expr_list_equal_assuming with
      (condition := condition); assumption.
  - iIntros "[Hpredicate %Hcondition]".
    iDestruct "Hpredicate" as (values) "[%Harguments Hpredicate]".
    iExists values. iFrame. iPureIntro.
    rewrite <- Harguments. symmetry.
    apply Translation.interp_expr_list_equal_assuming with
      (condition := condition); assumption.
Qed.

Theorem core_entails_valid {F Δ}
    (left right : Resource.core_assertion F Δ) :
  Hoare.ResourceHoare.core_entails left right -> core_semantically_entails left right.
Proof.
  intros Hentails. induction Hentails;
    intros formals binders atoms.
  - reflexivity.
  - apply core_entailment_step_valid. exact H.
  - etrans; [apply IHHentails1 | apply IHHentails2].
  - cbn [Translation.TermSemantics.interp_core].
    iIntros "[Hleft Hright]". iSplitL "Hleft".
    + iApply IHHentails1. iExact "Hleft".
    + iApply IHHentails2. iExact "Hright".
  - cbn [Translation.TermSemantics.interp_core]. iIntros "H".
    iDestruct "H" as (value) "Hbody". iExists value.
    iApply IHHentails. iExact "Hbody".
  - cbn [Translation.TermSemantics.interp_core].
    iIntros "Hinstantiated".
    destruct (interp_expr_total formals binders atoms witness)
      as [value Hvalue].
    iExists value.
    erewrite <- (Translation.TermSemantics.interp_instantiate_bound_core
      Model predicates); [|exact Hvalue].
    iExact "Hinstantiated".
  - cbn [Translation.TermSemantics.interp_core]. iIntros "H".
    iDestruct "H" as (value) "Hbody".
    iPoseProof (IHHentails formals (binder_cons value binders) atoms
      with "Hbody") as "Hresult".
    iEval (rewrite Translation.TermSemantics.interp_weaken_core) in
      "Hresult". iExact "Hresult".
  - cbn [Translation.TermSemantics.interp_core].
    iIntros "[Hbody Hframe]".
    iDestruct "Hbody" as (value) "Hbody". iExists value.
    iFrame "Hbody".
    rewrite Translation.TermSemantics.interp_weaken_core.
    iExact "Hframe".
  - cbn [Translation.TermSemantics.interp_core]. iIntros "H".
    iDestruct "H" as (value) "[Hbody Hframe]". iSplitL "Hbody".
    + iExists value. iExact "Hbody".
    + iEval (rewrite Translation.TermSemantics.interp_weaken_core) in
        "Hframe". iExact "Hframe".
  - cbn [Translation.TermSemantics.interp_core].
    iIntros "[Hframe Hbody]".
    iDestruct "Hbody" as (value) "Hbody". iExists value.
    rewrite Translation.TermSemantics.interp_weaken_core. iFrame.
  - cbn [Translation.TermSemantics.interp_core]. iIntros "H".
    iSplit.
    + iDestruct "H" as "[Hthen _]".
      iIntros "%Hcondition". iApply IHHentails1.
      iApply "Hthen". iPureIntro. exact Hcondition.
    + iDestruct "H" as "[_ Helse]".
      iIntros "%Hcondition". iApply IHHentails2.
      iApply "Helse". iPureIntro. exact Hcondition.
  - cbn [Translation.TermSemantics.interp_core]. iIntros "H".
    iExists (Core.default_tval t).
    rewrite Translation.TermSemantics.interp_weaken_core. iExact "H".
  - cbn [Translation.TermSemantics.interp_core]. iIntros "H".
    iSplit.
    + iDestruct "H" as (value) "[Hthen _]".
      iIntros "%Hcondition". iExists value. iApply "Hthen".
      rewrite Translation.interp_weaken_expr.
      iPureIntro. exact Hcondition.
    + iDestruct "H" as (value) "[_ Helse]".
      iIntros "%Hcondition". iExists value. iApply "Helse".
      rewrite Translation.interp_weaken_expr.
      iPureIntro. exact Hcondition.
  - cbn [Translation.TermSemantics.interp_core]. iIntros "H".
    destruct (classic
      (Core.interp_expr formals binders atoms condition =
        Some (Core.VBool true))) as [Hcondition|Hcondition].
    + iDestruct "H" as "[Hthen _]".
      iPoseProof ("Hthen" $! Hcondition) as "Hthen".
      iDestruct "Hthen" as (value) "Hbody". iExists value. iSplit.
      * iIntros "_". iExact "Hbody".
      * iIntros "%Hfalse".
        rewrite Translation.interp_weaken_expr in Hfalse. contradiction.
    + iDestruct "H" as "[_ Helse]".
      iPoseProof ("Helse" $! Hcondition) as "Helse".
      iDestruct "Helse" as (value) "Hbody". iExists value. iSplit.
      * iIntros "%Hfalse".
        rewrite Translation.interp_weaken_expr in Hfalse. contradiction.
      * iIntros "_". iExact "Hbody".
  - cbn [Translation.TermSemantics.interp_core]. iIntros "H".
    iDestruct "H" as (t_value) "H".
    iDestruct "H" as (u_value) "H".
    iExists u_value, t_value.
    rewrite (Translation.TermSemantics.interp_rename_bound_core
      Model predicates (@exchange_bound_renaming Δ u t) formals
      (binder_cons u_value (binder_cons t_value binders))
      (binder_cons t_value (binder_cons u_value binders)) atoms
      (binder_cons_exchange t_value u_value binders) body).
    iExact "H".
  - cbn [Translation.TermSemantics.interp_core]. iIntros "H" (value).
    iApply (IHHentails formals (binder_cons value binders) atoms).
    iApply ("H" $! value).
Qed.

(** [RPEIntro] substitutes a reference witness into the symbolic store.
    It used to be carried as a hypothesis of the slice; it is now proved
    once, from the interpretation of reference substitution, by
    [rpe_intro_holds] just below.  The definition is kept because the
    slice lemmas quantify over it, but nothing has to supply it. *)
Definition rpe_intro_valid (Γ F : context) : Prop :=
  forall Δ t (witness : Core.value_ref F Δ t)
    (state : Resource.resource_assertion Γ F (t :: Δ))
    (runtime : Translation.data_stack_context Model Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env),
  interp_resource predicates runtime formals binders atoms
    (Resource.subst_bound_resource
      (Resource.head_bound_ref_subst witness) state) ⊢
  (∃ value : tval t,
    interp_resource predicates runtime formals
      (binder_cons value binders) atoms state)%I.

(** Proved, not assumed.  Instantiating a resource binder is a
    substitution of a [value_ref] into both halves of the state: into the
    symbolic store, where [interp_subst_bound_store] turns it into a
    binder-environment extension, and into the core, where
    [interp_subst_bound_core] does the same.  Nothing about the concrete
    stack-ownership predicate is needed, so this belongs here rather than
    at the runtime layer. *)
Theorem rpe_intro_holds (Γ F : context) : rpe_intro_valid Γ F.
Proof.
  intros Δ t witness state runtime formals binders atoms.
  destruct state as [store body].
  unfold Translation.TermSemantics.interp_resource,
    Resource.subst_bound_resource.
  cbn [Resource.resource_stack Resource.resource_body].
  iIntros "H".
  iExists (Core.interp_ref formals binders atoms witness).
  rewrite (Translation.interp_subst_bound_store
    (Resource.head_bound_ref_subst witness) formals _ binders atoms
    (Translation.interp_head_bound_ref_subst witness formals binders atoms)
    store).
  rewrite (Translation.TermSemantics.interp_subst_bound_core Model
    predicates
    (Resource.bound_subst_of_refs (Resource.head_bound_ref_subst witness))
    formals _ binders atoms
    (fun u variable =>
      f_equal Some
        (Translation.interp_head_bound_ref_subst witness formals binders
          atoms u variable))
    body).
  iExact "H".
Qed.

Lemma resource_prenex_entails_valid {Γ F}
    {Δ} (left right : Resource.resource_prenex Γ F Δ) :
  Hoare.ResourceHoare.resource_prenex_entails left right ->
  forall (runtime : Translation.data_stack_context Model Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env),
  interp_resource_prenex predicates runtime formals binders atoms
    left ⊢
  interp_resource_prenex predicates runtime formals binders atoms
    right.
Proof.
  intro Hentails; induction Hentails;
    intros runtime formals binders atoms;
    cbn [Translation.TermSemantics.interp_resource_prenex].
  - destruct H as [Hstack Hcore].
    destruct left as [lstore lbody]; destruct right as [rstore rbody].
    cbn [Resource.resource_stack Resource.resource_body] in *. subst rstore.
    unfold Translation.TermSemantics.interp_resource.
    cbn [Resource.resource_stack Resource.resource_body].
    apply bi.sep_mono;
      [done
      | exact (core_entails_valid lbody rbody Hcore formals binders atoms)].
  - apply bi.exist_mono; intro value. apply IHHentails.
  - apply rpe_intro_holds.
  - (* RPEOpenCoreExists: unconditional.  The core existential and the
       telescope binder interpret to the same Iris existential; the
       symbolic store is insensitive to the extra binder. *)
    unfold Resource.RState.
    cbn [Translation.TermSemantics.interp_resource_prenex].
    unfold Translation.TermSemantics.interp_resource.
    cbn [Resource.resource_stack Resource.resource_body
      Translation.TermSemantics.interp_core].
    iIntros "[Hstack Hbody]".
    iDestruct "Hbody" as (value) "Hbody".
    iExists value.
    rewrite Translation.interp_weaken_store.
    iFrame.
  - (* RPECloseCoreExists: the reverse distribution law. *)
    unfold Resource.RState.
    cbn [Translation.TermSemantics.interp_resource_prenex].
    unfold Translation.TermSemantics.interp_resource.
    cbn [Resource.resource_stack Resource.resource_body
      Translation.TermSemantics.interp_core].
    iIntros "H".
    iDestruct "H" as (value) "[Hstack Hbody]".
    rewrite <- (Translation.interp_weaken_store
      formals binders atoms value store).
    iFrame.
  - apply bi.exist_elim; intro value.
    apply bi.equiv_entails_1_1,
      (Translation.TermSemantics.interp_weaken_resource_prenex Model).
  - etrans; [apply IHHentails1 | apply IHHentails2].
  - pose (source_binders := fun t (variable : bvar Δ t) =>
      binders t (renaming t variable)).
    have Hrenaming : forall t (variable : bvar Δ t),
        binders t (renaming t variable) = source_binders t variable.
    { intros. reflexivity. }
    rewrite (Translation.TermSemantics.interp_rename_resource_prenex Model
      predicates left _ renaming formals source_binders binders atoms runtime
      Hrenaming).
    rewrite (Translation.TermSemantics.interp_rename_resource_prenex Model
      predicates right _ renaming formals source_binders binders atoms runtime
      Hrenaming).
    apply IHHentails.
  - pose (tail := fun u (variable : bvar Δ u) =>
      binders u (MThere variable)).
    have Heta : binder_cons (binders t MHere) tail = binders :=
      binder_cons_eta binders.
    iIntros "Hbody".
    iPoseProof (IHHentails runtime formals tail atoms with "[Hbody]")
      as "Htarget".
    { iExists (binders t MHere). rewrite Heta. iExact "Hbody". }
    rewrite <- Heta.
    rewrite (Translation.TermSemantics.interp_weaken_resource_prenex Model).
    iExact "Htarget".
Qed.

End EntailmentValidity.

End WithModel.

End TermSemantics.

End Make.
End TypedValidity.
