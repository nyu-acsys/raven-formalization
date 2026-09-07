From Coq Require Import Program.Equality.
From iris.proofmode Require Import tactics.

From raven_iris.rich_raven_lang Require Import
  typed_core typed_assertion typed_ir typed_hoare typed_translation.

(** Semantic validity of the typed entailment and Hoare calculi. *)
Module TypedValidity.

Import TypedCore TypedIR.

Module Make (RAs : RA_VALUE_CONFIG) (Logic : TypedAssertion.LOGIC_SIGNATURE).
Module Translation := TypedTranslation.Make RAs Logic.
Module Hoare := Translation.Hoare.
Module IR := Translation.IR.
Module Core := Translation.Core.
Module Assertions := Translation.Assertions.
Import Core Assertions IR Hoare Translation.

Module Semantics (Model : Translation.SEMANTIC_CONFIG).
Module S := Translation.Semantics Model.
Import S.
Existing Instance Model.bi_affine.
Local Notation iProp := (bi_car Model.PROP).

Section EntailmentValidity.
Context (predicates : predicate_semantics).

Definition semantically_entails {Γ F Δ}
    (left right : assertion Γ F Δ) : Prop :=
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env),
    interp_assertion predicates runtime formals binders atoms left ⊢
    interp_assertion predicates runtime formals binders atoms right.

Lemma entailment_step_valid {Γ F Δ}
    (left right : assertion Γ F Δ) :
  entailment_step left right -> semantically_entails left right.
Proof.
  intros Hstep runtime formals binders atoms.
  destruct Hstep; cbn [interp_assertion].
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
  - iIntros "Hown". iDestruct "Hown" as (concrete_location concrete_chunk)
      "(%Hlocation & %Hchunk & Hown)".
    iExists concrete_location, concrete_chunk. iSplit; first done.
    iSplit; last iExact "Hown". iPureIntro.
    rewrite <- Hchunk, <- (H formals binders atoms). reflexivity.
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
  - cbn [interp_assertion]. iIntros "[Hleft Hright]". iSplitL "Hleft".
    + iApply IHHentails1. iExact "Hleft".
    + iApply IHHentails2. iExact "Hright".
  - cbn [interp_assertion]. iIntros "H".
    iDestruct "H" as (value) "Hbody". iExists value.
    iApply IHHentails. iExact "Hbody".
  - cbn [interp_assertion]. iIntros "Hinstantiated".
    destruct (interp_expr_total formals binders atoms witness)
      as [value Hvalue].
    iExists value.
    erewrite <- (interp_instantiate_bound_assertion predicates);
      [|exact Hvalue|exact H].
    iExact "Hinstantiated".
  - cbn [interp_assertion]. iIntros "H".
    iDestruct "H" as (value) "Hbody".
    iPoseProof (IHHentails runtime formals (binder_cons value binders) atoms
      with "Hbody") as "Hresult".
    iEval (rewrite interp_weaken_assertion) in "Hresult". iExact "Hresult".
  - cbn [interp_assertion]. iIntros "[Hbody Hframe]".
    iDestruct "Hbody" as (value) "Hbody". iExists value.
    iFrame "Hbody". rewrite interp_weaken_assertion. iExact "Hframe".
  - cbn [interp_assertion]. iIntros "[Hframe Hbody]".
    iDestruct "Hbody" as (value) "Hbody". iExists value.
    rewrite interp_weaken_assertion. iFrame.
  - cbn [interp_assertion]. iIntros "H" (value).
    iApply (IHHentails runtime formals (binder_cons value binders) atoms).
    iApply ("H" $! value).
Qed.

End EntailmentValidity.

Module Type STATEMENT_WP.
  Parameter statement_wp : forall Γ, Model.stack_context Γ -> stmt Γ ->
    Hoare.mask -> Hoare.mask -> iProp -> iProp.

  Parameter statement_wp_mono : forall Γ runtime statement mask_pre mask_post
      (left right : iProp),
    (left ⊢ right) ->
    statement_wp Γ runtime statement mask_pre mask_post left ⊢
      statement_wp Γ runtime statement mask_pre mask_post right.

  Parameter skip_wp : forall Γ runtime node current_mask (post : iProp),
    post ⊢ statement_wp Γ runtime (TSkip node)
      current_mask current_mask post.

  Parameter assert_wp : forall Γ runtime node condition current_mask
      (post : iProp),
    post ⊢ statement_wp Γ runtime (TAssert node condition)
      current_mask current_mask post.

  Parameter sequence_wp : forall Γ runtime node first second mask1 mask2 mask3
      (post : iProp),
    statement_wp Γ runtime first mask1 mask2
      (statement_wp Γ runtime second mask2 mask3 post) ⊢
    statement_wp Γ runtime (TSeq node first second) mask1 mask3 post.

  Parameter frame_wp : forall Γ runtime statement mask_pre mask_post
      (post frame : iProp),
    statement_wp Γ runtime statement mask_pre mask_post post ∗ frame ⊢
    statement_wp Γ runtime statement mask_pre mask_post (post ∗ frame).

  Parameter conditional_wp : forall Γ F Δ runtime
      (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
      node (store : symbolic_store Γ F Δ) (frame : iProp) condition
      then_branch else_branch mask_pre mask_post (post : iProp),
    (Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗
       frame ∗
       ⌜interp_expr formals binders atoms (Hoare.symbolize_expr store condition) =
         Some (VBool true)⌝ ⊢
       statement_wp Γ runtime then_branch mask_pre mask_post post) ->
    (Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗
       frame ∗
       ⌜interp_expr formals binders atoms (Hoare.symbolize_expr store condition) <>
         Some (VBool true)⌝ ⊢
       statement_wp Γ runtime else_branch mask_pre mask_post post) ->
    Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗
      frame ⊢
    statement_wp Γ runtime (TIf node condition then_branch else_branch)
      mask_pre mask_post post.
End STATEMENT_WP.

Module StructuralValidity (Contracts : Hoare.CONTRACT_ENV)
    (Execution : STATEMENT_WP).
Module Rules := Hoare.LogicRules Contracts.
Import Rules.
Section WithPredicates.
Context (predicates : atom_env -> predicate_semantics).

Definition semantically_valid {Γ F Δ} (pre : assertion Γ F Δ)
    (statement : stmt Γ) mask_pre mask_post (post : assertion Γ F Δ) : Prop :=
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env),
    interp_assertion (predicates atoms) runtime formals binders atoms pre ⊢
    Execution.statement_wp Γ runtime statement mask_pre mask_post
      (interp_assertion (predicates atoms) runtime formals binders atoms post).

Lemma skip_rule_valid {Γ F Δ} node (store : symbolic_store Γ F Δ) frame mask :
  semantically_valid (AAnd (AStack store) frame) (TSkip node) mask mask
    (AAnd (AStack store) frame).
Proof.
  intros runtime formals binders atoms. apply Execution.skip_wp.
Qed.

Lemma assert_rule_valid {Γ F Δ} node (store : symbolic_store Γ F Δ) frame
    condition mask :
  semantically_valid
    (AAnd (AStack store)
      (AAnd frame (AExpr (Hoare.symbolize_expr store condition))))
    (TAssert node condition) mask mask
    (AAnd (AStack store)
      (AAnd frame (AExpr (Hoare.symbolize_expr store condition)))).
Proof.
  intros runtime formals binders atoms. apply Execution.assert_wp.
Qed.

Lemma sequence_rule_valid {Γ F Δ} node
    (pre middle post : assertion Γ F Δ) (first second : stmt Γ)
    mask1 mask2 mask3 :
  semantically_valid pre first mask1 mask2 middle ->
  semantically_valid middle second mask2 mask3 post ->
  semantically_valid pre (TSeq node first second) mask1 mask3 post.
Proof.
  intros Hfirst Hsecond runtime formals binders atoms.
  iIntros "Hpre".
  iPoseProof (Hfirst runtime formals binders atoms with "Hpre") as "Hfirst".
  iApply Execution.sequence_wp.
  iApply (Execution.statement_wp_mono with "Hfirst").
  iIntros "Hmiddle".
  iApply (Hsecond runtime formals binders atoms with "Hmiddle").
Qed.

Lemma conditional_rule_valid {Γ F Δ} node (store : symbolic_store Γ F Δ)
    (frame : assertion Γ F Δ) condition (then_branch else_branch : stmt Γ)
    (post : assertion Γ F Δ) mask_pre mask_post :
  semantically_valid
    (AAnd (AStack store)
      (AAnd frame (AExpr (Hoare.symbolize_expr store condition))))
    then_branch mask_pre mask_post post ->
  semantically_valid
    (AAnd (AStack store)
      (AAnd frame (AExpr (EUnOp UNot
        (Hoare.symbolize_expr store condition)))))
    else_branch mask_pre mask_post post ->
  semantically_valid (AAnd (AStack store) frame)
    (TIf node condition then_branch else_branch) mask_pre mask_post post.
Proof.
  intros Hthen Helse runtime formals binders atoms.
  apply Execution.conditional_wp.
  - iIntros "(Hstack & Hframe & %Hcondition)".
    iApply (Hthen runtime formals binders atoms). iFrame. done.
  - iIntros "(Hstack & Hframe & %Hcondition)".
    iApply (Helse runtime formals binders atoms). iFrame.
    iPureIntro. simpl. destruct (interp_expr formals binders atoms
      (Hoare.symbolize_expr store condition)) as [value|] eqn:Hvalue.
    + dependent destruction value. destruct b; simpl; congruence.
    + exfalso. destruct (interp_expr_total formals binders atoms
        (Hoare.symbolize_expr store condition)) as [value Htotal].
      congruence.
Qed.

Lemma frame_rule_valid {Γ F Δ} (pre post frame : assertion Γ F Δ)
    (statement : stmt Γ) mask_pre mask_post :
  semantically_valid pre statement mask_pre mask_post post ->
  semantically_valid (AAnd pre frame) statement mask_pre mask_post
    (AAnd post frame).
Proof.
  intros Htriple runtime formals binders atoms.
  iIntros "[Hpre Hframe]".
  iPoseProof (Htriple runtime formals binders atoms with "Hpre") as "Hwp".
  iApply Execution.frame_wp. iFrame.
Qed.

Lemma consequence_rule_valid {Γ F Δ}
    (pre pre' post post' : assertion Γ F Δ) (statement : stmt Γ)
    mask_pre mask_post :
  semantically_valid pre statement mask_pre mask_post post ->
  assertion_entails pre' pre -> assertion_entails post post' ->
  semantically_valid pre' statement mask_pre mask_post post'.
Proof.
  intros Htriple Hpre Hpost runtime formals binders atoms.
  iIntros "Hpre".
  iPoseProof (assertion_entails_valid (predicates atoms) _ _ Hpre runtime formals
    binders atoms with "Hpre") as "Hpre".
  iPoseProof (Htriple runtime formals binders atoms with "Hpre") as "Hwp".
  iApply (Execution.statement_wp_mono with "Hwp").
  iApply (assertion_entails_valid (predicates atoms) _ _ Hpost).
Qed.

Lemma exists_elim_rule_valid {Γ F Δ t} (body : assertion Γ F (t :: Δ))
    (post : assertion Γ F Δ) (statement : stmt Γ) mask_pre mask_post :
  semantically_valid body statement mask_pre mask_post
    (weaken_assertion post) ->
  semantically_valid (AExists t body) statement mask_pre mask_post post.
Proof.
  intros Htriple runtime formals binders atoms. iIntros "Hpre".
  iDestruct "Hpre" as (value) "Hbody".
  iPoseProof (Htriple runtime formals (binder_cons value binders) atoms
    with "Hbody") as "Hwp".
  iApply (Execution.statement_wp_mono with "Hwp").
  rewrite interp_weaken_assertion. done.
Qed.

Lemma exists_preserve_rule_valid {Γ F Δ t}
    (body post : assertion Γ F (t :: Δ)) (statement : stmt Γ)
    mask_pre mask_post :
  semantically_valid body statement mask_pre mask_post post ->
  semantically_valid (AExists t body) statement mask_pre mask_post
    (AExists t post).
Proof.
  intros Htriple runtime formals binders atoms. iIntros "Hpre".
  iDestruct "Hpre" as (value) "Hbody".
  iPoseProof (Htriple runtime formals (binder_cons value binders) atoms
    with "Hbody") as "Hwp".
  iApply (Execution.statement_wp_mono with "Hwp").
  iIntros "Hpost". iExists value. iExact "Hpost".
Qed.

End WithPredicates.
End StructuralValidity.

(** Primitive boundary for the continuation-based statement translation.
    Leaves include physical and contract-backed operations.  Conditionals are
    separate because their runtime step selects one of two recursively
    translated continuations. *)
Module Type CONTINUATION_PRIMITIVES.
  Parameter leaf_wp : forall Γ, Model.stack_context Γ -> stmt Γ ->
    Hoare.mask -> Hoare.mask -> iProp -> iProp.
  Parameter branch_wp : forall Γ, Model.stack_context Γ -> pexpr Γ TBool ->
    Hoare.mask -> iProp -> iProp -> iProp.
  Parameter atomic_wp : forall Γ, Model.stack_context Γ -> stmt Γ ->
    Hoare.mask -> Hoare.mask -> iProp -> iProp.

  Parameter leaf_mono : forall Γ runtime statement mask_pre mask_post P Q,
    (P ⊢ Q) -> leaf_wp Γ runtime statement mask_pre mask_post P ⊢
      leaf_wp Γ runtime statement mask_pre mask_post Q.
  Parameter leaf_frame : forall Γ runtime statement mask_pre mask_post P R,
    leaf_wp Γ runtime statement mask_pre mask_post P ∗ R ⊢
      leaf_wp Γ runtime statement mask_pre mask_post (P ∗ R).
  Parameter leaf_skip : forall Γ runtime node mask P,
    P ⊢ leaf_wp Γ runtime (TSkip node) mask mask P.
  Parameter leaf_assert : forall Γ runtime node condition mask P,
    P ⊢ leaf_wp Γ runtime (TAssert node condition) mask mask P.

  Parameter atomic_mono : forall Γ runtime body mask_pre mask_post P Q,
    (P ⊢ Q) -> atomic_wp Γ runtime body mask_pre mask_post P ⊢
      atomic_wp Γ runtime body mask_pre mask_post Q.
  Parameter atomic_frame : forall Γ runtime body mask_pre mask_post P R,
    atomic_wp Γ runtime body mask_pre mask_post P ∗ R ⊢
      atomic_wp Γ runtime body mask_pre mask_post (P ∗ R).

  Parameter branch_mono : forall Γ runtime condition mask P P' Q Q',
    (P ⊢ P') -> (Q ⊢ Q') ->
    branch_wp Γ runtime condition mask P Q ⊢
      branch_wp Γ runtime condition mask P' Q'.
  Parameter branch_frame : forall Γ runtime condition mask P Q R,
    branch_wp Γ runtime condition mask P Q ∗ R ⊢
      branch_wp Γ runtime condition mask (P ∗ R) (Q ∗ R).
  Parameter branch_select : forall Γ F Δ runtime
      (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
      (store : symbolic_store Γ F Δ) (frame : iProp) condition mask P Q,
    (Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗
       frame ∗
       ⌜interp_expr formals binders atoms (Hoare.symbolize_expr store condition) =
         Some (VBool true)⌝ ⊢ P) ->
    (Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗
       frame ∗
       ⌜interp_expr formals binders atoms (Hoare.symbolize_expr store condition) <>
         Some (VBool true)⌝ ⊢ Q) ->
    Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗
      frame ⊢ branch_wp Γ runtime condition mask P Q.
End CONTINUATION_PRIMITIVES.

Module ContinuationExecution (Primitives : CONTINUATION_PRIMITIVES).

Fixpoint statement_wp {Γ} (runtime : Model.stack_context Γ)
    (statement : stmt Γ) (mask_pre mask_post : Hoare.mask)
    (post : iProp) : iProp :=
  match statement with
  | TSeq _ first second =>
      (∃ middle : Hoare.mask,
        statement_wp runtime first mask_pre middle
          (statement_wp runtime second middle mask_post post))%I
  | TIf _ condition then_branch else_branch =>
      Primitives.branch_wp Γ runtime condition mask_pre
         (statement_wp runtime then_branch mask_pre mask_post post)
         (statement_wp runtime else_branch mask_pre mask_post post)
  | TAtomic _ body =>
      Primitives.atomic_wp Γ runtime body mask_pre mask_post
        (statement_wp runtime body mask_pre mask_post post)
  | _ => Primitives.leaf_wp Γ runtime statement mask_pre mask_post post
  end.

Lemma statement_wp_mono {Γ} runtime (statement : stmt Γ) mask_pre mask_post P Q :
  (P ⊢ Q) ->
  statement_wp runtime statement mask_pre mask_post P ⊢
    statement_wp runtime statement mask_pre mask_post Q.
Proof.
  revert mask_pre mask_post P Q.
  induction statement; intros mask_pre mask_post P Q HPQ; simpl;
    try (apply Primitives.leaf_mono; exact HPQ).
  - iIntros "Hbranch".
    pose proof (IHstatement1 mask_pre mask_post P Q HPQ) as Hthen.
    pose proof (IHstatement2 mask_pre mask_post P Q HPQ) as Helse.
    iApply (@Primitives.branch_mono Γ runtime condition mask_pre
      (statement_wp runtime statement1 mask_pre mask_post P)
      (statement_wp runtime statement1 mask_pre mask_post Q)
      (statement_wp runtime statement2 mask_pre mask_post P)
      (statement_wp runtime statement2 mask_pre mask_post Q)
      Hthen Helse with "Hbranch").
  - iIntros "H". iDestruct "H" as (middle) "H". iExists middle.
    pose proof (IHstatement2 middle mask_post P Q HPQ) as Hsecond.
    iApply (IHstatement1 mask_pre middle _ _ Hsecond with "H").
  - apply Primitives.atomic_mono.
    apply IHstatement. exact HPQ.
Qed.

Lemma statement_wp_frame {Γ} runtime (statement : stmt Γ) mask_pre mask_post P R :
  statement_wp runtime statement mask_pre mask_post P ∗ R ⊢
    statement_wp runtime statement mask_pre mask_post (P ∗ R).
Proof.
  revert mask_pre mask_post P R.
  induction statement; intros mask_pre mask_post P R;
    simpl; try apply Primitives.leaf_frame.
  - iIntros "[Hbranch R]".
    iPoseProof (@Primitives.branch_frame Γ runtime condition mask_pre
      (statement_wp runtime statement1 mask_pre mask_post P)
      (statement_wp runtime statement2 mask_pre mask_post P) R
      with "[$Hbranch $R]") as "Hbranch".
    pose proof (IHstatement1 mask_pre mask_post P R) as Hthen.
    pose proof (IHstatement2 mask_pre mask_post P R) as Helse.
    iApply (@Primitives.branch_mono Γ runtime condition mask_pre _ _ _ _
      Hthen Helse with "Hbranch").
  - iIntros "[H R]". iDestruct "H" as (middle) "H". iExists middle.
    iPoseProof (IHstatement1 mask_pre middle
      (statement_wp runtime statement2 middle mask_post P) R
      with "[$H $R]") as "Hfirst".
    iApply (statement_wp_mono with "Hfirst").
    exact (IHstatement2 middle mask_post P R).
  - iIntros "[Hatomic HR]".
    iPoseProof (Primitives.atomic_frame Γ runtime statement mask_pre mask_post
      (statement_wp runtime statement mask_pre mask_post P) R
      with "[$Hatomic $HR]") as "Hatomic".
    iApply (Primitives.atomic_mono with "Hatomic").
    exact (IHstatement mask_pre mask_post P R).
Qed.

Module Interface <: STATEMENT_WP.
  Definition statement_wp := @statement_wp.
  Definition statement_wp_mono := @statement_wp_mono.
  Definition skip_wp := Primitives.leaf_skip.
  Definition assert_wp := Primitives.leaf_assert.
  Lemma sequence_wp Γ runtime node first second mask1 mask2 mask3 post :
    statement_wp Γ runtime first mask1 mask2
      (statement_wp Γ runtime second mask2 mask3 post) ⊢
    statement_wp Γ runtime (TSeq node first second) mask1 mask3 post.
  Proof. iIntros "H". iExists mask2. iExact "H". Qed.
  Definition frame_wp := @statement_wp_frame.
  Lemma conditional_wp (Γ F Δ : context) (runtime : Model.stack_context Γ)
      (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
      node (store : symbolic_store Γ F Δ) (frame : iProp) condition
      (then_branch else_branch : stmt Γ) mask_pre mask_post (post : iProp) :
    (Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗
       frame ∗ ⌜interp_expr formals binders atoms
         (Hoare.symbolize_expr store condition) = Some (VBool true)⌝ ⊢
       statement_wp Γ runtime then_branch mask_pre mask_post post) ->
    (Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗
       frame ∗ ⌜interp_expr formals binders atoms
         (Hoare.symbolize_expr store condition) <> Some (VBool true)⌝ ⊢
       statement_wp Γ runtime else_branch mask_pre mask_post post) ->
    Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗
      frame ⊢ statement_wp Γ runtime
        (TIf node condition then_branch else_branch) mask_pre mask_post post.
  Proof.
    intros Hthen Helse. simpl. iIntros "H".
    iApply (Primitives.branch_select with "H"); assumption.
  Qed.
End Interface.

End ContinuationExecution.

End Semantics.
End Make.
End TypedValidity.
