From Coq Require Import List String ZArith Program.Equality Lia Logic.ProofIrrelevance.
From stdpp Require Import countable gmap namespaces sets.

From iris.algebra Require Import auth gset.
From iris.base_logic Require Import fancy_updates.
From iris.base_logic.lib Require Import own invariants.

From raven_iris.simp_raven_lang Require Import lang ghost_state.
From raven_iris.rich_raven_lang Require Import
  rrl_lang typed_core typed_analysis_view typed_assertion typed_ir
  typed_translation typed_validity typed_region.

Import ListNotations.
Import weakestpre.
Open Scope list_scope.

(** Concrete connection between the typed assertion semantics and Raven's
    existing Iris ghost state. *)
Module TypedRuntime.

Module Make (LegacyRAs : ra_base.RA_CONFIG)
    (Logic : TypedAssertion.LOGIC_SIGNATURE).

Module Legacy := rrl_lang.Make LegacyRAs.
Module LegacyLifting := Legacy.lifting.
Module LegacyGhost := LegacyLifting.ghost_state.
Module LegacyLang := LegacyLifting.lang.

Module TypedRAs <: TypedCore.RA_VALUE_CONFIG.
  Definition ra_carrier name :=
    ra_base.RA_carrier (LegacyRAs.ra_map name).

  Definition ra_eqb name
      (left right : ra_carrier name) : bool := bool_decide (left = right).

  Lemma ra_eqb_eq name (left right : ra_carrier name) :
    ra_eqb name left right = true <-> left = right.
  Proof. apply bool_decide_eq_true. Qed.
End TypedRAs.

Module Validation := TypedValidity.Make TypedRAs Logic.
Module Translation := Validation.Translation.
Module IR := Translation.IR.
Module Core := Translation.Core.
Import TypedCore TypedIR Core IR Translation.

Module RegionSyntax <: TypedAnalysisView.ANALYSIS_SYNTAX.
  Definition statement := IR.stmt.
  Definition view {Γ} (statement : statement Γ) :=
    match statement with
    | TUnfold _ invariant _ => TypedAnalysisView.ViewUnfold invariant
    | TFold _ invariant _ => TypedAnalysisView.ViewFold invariant
    | TSeq _ first second => TypedAnalysisView.ViewSequence first second
    | TIf _ _ then_branch else_branch =>
        TypedAnalysisView.ViewConditional then_branch else_branch
    | TAtomic _ body => TypedAnalysisView.ViewAtomic body
    | _ => TypedAnalysisView.ViewLeaf
    end.
  Fixpoint size {Γ} (statement : statement Γ) : nat :=
    match statement with
    | TSeq _ first second | TIf _ _ first second => S (size first + size second)
    | TAtomic _ body => S (size body)
    | _ => 1
    end.
  Lemma size_positive Γ (statement : statement Γ) : 0 < size statement.
  Proof. induction statement; simpl; lia. Qed.
  Lemma sequence_children_smaller (Γ : context)
      (statement first second : statement Γ) :
    view statement = TypedAnalysisView.ViewSequence first second ->
    size first < size statement /\ size second < size statement.
  Proof. destruct statement; cbn; intros Hview; try discriminate.
    inversion Hview; subst. lia. Qed.
  Lemma conditional_children_smaller (Γ : context)
      (statement then_branch else_branch : statement Γ) :
    view statement = TypedAnalysisView.ViewConditional then_branch else_branch ->
    size then_branch < size statement /\ size else_branch < size statement.
  Proof. destruct statement; cbn; intros Hview; try discriminate.
    inversion Hview; subst. lia. Qed.
  Lemma atomic_body_smaller (Γ : context) (statement body : statement Γ) :
    view statement = TypedAnalysisView.ViewAtomic body ->
    size body < size statement.
  Proof. destruct statement; cbn; intros Hview; try discriminate.
    inversion Hview; subst. lia. Qed.
End RegionSyntax.

Module GenericRegions := TypedRegion.Generic RegionSyntax.

(** Canonical pairing used by certified-region soundness.  Unlike the legacy
    pairing in [typed_region], every component below refers to this runtime's
    single non-generative IR instance.  The explicit LIFO boundary stacks let
    the semantic induction split sequences without losing an accessor that
    was opened by the first component and is closed by the second. *)
Module CertifiedRegions (Contracts : Hoare.CONTRACT_ENV).
Module Rules := Hoare.LogicRules Contracts.
Module Atomicity := GenericRegions.Atomicity.

(** The analyzer-selected effect of procedure leaves agrees with the contract
    environment used by the Hoare and runtime layers. *)
Definition procedure_cost_model_sound (cost : Atomicity.cost_model) : Prop :=
  forall Γ (statement : stmt Γ),
  match statement with
  | TCall _ procedure _ _ =>
      cost Γ statement = Atomicity.ProcedureCallStep
        (Contracts.required_mask procedure)
        (Contracts.granted_mask procedure)
  | TSpawn _ procedure _ =>
      cost Γ statement =
        Atomicity.ProcedureSpawnStep (Contracts.required_mask procedure)
  | _ =>
      match cost Γ statement with
      | Atomicity.ProcedureCallStep _ _
      | Atomicity.ProcedureSpawnStep _ => False
      | _ => True
      end
  end.

Lemma certified_call_step_effect cost
    (Hcost : procedure_cost_model_sound cost)
    Γ args return_type node procedure (arguments : pexpr_list Γ args)
    (target : call_target Γ return_type) entry exit :
  Atomicity.take_step
      (cost Γ (@TCall Γ args return_type node procedure arguments target))
      entry = inr exit ->
  Contracts.required_mask procedure ⊆ Atomicity.analysis_mask entry /\
  Contracts.granted_mask procedure ## Atomicity.analysis_open entry /\
  Atomicity.analysis_mask exit = Atomicity.analysis_mask entry ∪
    Contracts.granted_mask procedure /\
  Atomicity.analysis_open exit = Atomicity.analysis_open entry.
Proof.
  intros Hstep. specialize (Hcost Γ
    (@TCall Γ args return_type node procedure arguments target)).
  simpl in Hcost. rewrite Hcost in Hstep.
  exact (Atomicity.procedure_call_step_success _ _ _ _ Hstep).
Qed.

Lemma certified_spawn_step_effect cost
    (Hcost : procedure_cost_model_sound cost)
    Γ args node procedure (arguments : pexpr_list Γ args) entry exit :
  Atomicity.take_step
      (cost Γ (@TSpawn Γ args node procedure arguments)) entry = inr exit ->
  Contracts.required_mask procedure ⊆ Atomicity.analysis_mask entry /\
  Atomicity.analysis_mask exit = Atomicity.analysis_mask entry /\
  Atomicity.analysis_open exit = Atomicity.analysis_open entry.
Proof.
  intros Hstep. specialize (Hcost Γ
    (@TSpawn Γ args node procedure arguments)).
  simpl in Hcost. rewrite Hcost in Hstep.
  exact (Atomicity.procedure_spawn_step_success _ _ _ Hstep).
Qed.

(** A small dependent transport API keeps the alignment witness below about
    proof structure rather than about the incidental normal form chosen for
    finite-set unions. *)
Definition hoare_mask_transport {Γ F Δ}
    {pre post : Translation.Assertions.assertion Γ F Δ} {statement}
    {source_pre source_post target_pre target_post}
    (derivation : @Rules.RavenHoareTriple Γ F Δ pre statement
      source_pre source_post post)
    (pre_equal : source_pre = target_pre)
    (post_equal : source_post = target_post) :
    @Rules.RavenHoareTriple Γ F Δ pre statement target_pre target_post post.
Proof.
  subst target_pre target_post. exact derivation.
Defined.

Lemma unfold_analysis_mask {Γ : context} {entry : Atomicity.analysis_state}
    {node : node_id} {invariant : inv_id}
    {arguments : pexpr_list Γ (Logic.invariant_args invariant)}
    {exit : Atomicity.analysis_state}
    (view : RegionSyntax.view (TUnfold node invariant arguments) =
      TypedAnalysisView.ViewUnfold invariant)
    (step : Atomicity.open_invariant invariant entry = inr exit) :
  Atomicity.analysis_mask exit =
    Atomicity.analysis_mask entry ∖ {[invariant]}.
Proof.
  intros. apply Atomicity.open_invariant_success in step as
    (_ & _ & Hmask & _). exact Hmask.
Qed.

Lemma fold_analysis_mask (invariant : inv_id) (entry : Atomicity.analysis_state) :
  Atomicity.analysis_mask (Atomicity.fold_invariant invariant entry) =
    Atomicity.analysis_mask entry ∪ {[invariant]}.
Proof.
  unfold Atomicity.fold_invariant.
  destruct (bool_decide (invariant ∈ Atomicity.analysis_open entry));
    simpl; set_solver.
Qed.

Lemma step_analysis_mask (entry exit : Atomicity.analysis_state) :
  Atomicity.take_step Atomicity.AtomicStep entry = inr exit ->
  Atomicity.analysis_mask exit = Atomicity.analysis_mask entry.
Proof.
  intro Hstep. apply Atomicity.atomic_step_preserves_sets in Hstep as
    [Hmask _]. exact Hmask.
Qed.

Lemma conditional_analysis_mask (state then_exit else_exit : Atomicity.analysis_state)
    branch_mask
    (then_mask : Atomicity.analysis_mask then_exit =
      branch_mask)
    (else_mask : Atomicity.analysis_mask else_exit =
      branch_mask) :
  branch_mask = Atomicity.analysis_mask
    (Atomicity.AnalysisState
      (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
      (Atomicity.analysis_open then_exit)
      (Atomicity.analysis_step_taken then_exit ||
        Atomicity.analysis_step_taken else_exit)
      (Atomicity.analysis_in_atomic then_exit)).
Proof.
  simpl. rewrite then_mask else_mask. set_solver.
Qed.

(** This witness pairs every control-producing Hoare rule with the same
    analysis-certificate node.  Assertion-only wrappers retain the very same
    certificate, while sequences, branches, and atomic blocks expose aligned
    children at their actual intermediate analysis states. *)
Inductive certificate_hoare_aligned (cost : Atomicity.cost_model) :
    forall {Γ F Δ fuel} {entry : Atomicity.analysis_state}
      {statement : stmt Γ} {exit : Atomicity.analysis_state}
      {pre post : Translation.Assertions.assertion Γ F Δ},
      Atomicity.analysis_certificate cost Γ fuel entry statement exit ->
      @Rules.RavenHoareTriple Γ F Δ pre statement
        (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit) post ->
      Type :=
| AlignedOrdinaryLeaf : forall Γ F Δ fuel entry statement exit pre post view step
    (derivation : @Rules.RavenHoareTriple Γ F Δ pre statement
      (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit) post),
    certificate_hoare_aligned cost
      (Atomicity.CertLeaf cost Γ fuel entry statement exit view step)
      derivation
| AlignedUnfold : forall Γ F Δ fuel entry node invariant arguments exit
    store body
    (view : RegionSyntax.view (TUnfold node invariant arguments) =
      TypedAnalysisView.ViewUnfold invariant)
    (step : Atomicity.open_invariant invariant entry = inr exit)
    (available : invariant ∈ Atomicity.analysis_mask entry)
    (instantiated : Contracts.instantiated_invariant Γ F Δ
      (Logic.invariant_args invariant) invariant
      (Hoare.symbolize_expr_list store arguments) body),
    certificate_hoare_aligned cost
      (Atomicity.CertUnfold cost Γ fuel entry
        (TUnfold node invariant arguments) invariant exit view step)
      (hoare_mask_transport
        (Rules.UnfoldInvariantRule node invariant arguments store body
          (Atomicity.analysis_mask entry) available instantiated)
        eq_refl (eq_sym (unfold_analysis_mask view step)))
| AlignedFold : forall Γ F Δ fuel entry node invariant arguments
    store body
    (view : RegionSyntax.view (TFold node invariant arguments) =
      TypedAnalysisView.ViewFold invariant)
    (instantiated : Contracts.instantiated_invariant Γ F Δ
      (Logic.invariant_args invariant) invariant
      (Hoare.symbolize_expr_list store arguments) body),
    certificate_hoare_aligned cost
      (Atomicity.CertFold cost Γ fuel entry
        (TFold node invariant arguments) invariant view)
      (hoare_mask_transport
        (Rules.FoldInvariantRule node invariant arguments store body
          (Atomicity.analysis_mask entry) instantiated)
        eq_refl (eq_sym (fold_analysis_mask invariant entry)))
| AlignedSequence : forall Γ F Δ fuel state node first middle second exit
    pre middle_assertion post view first_certificate second_certificate
    (first_derivation : @Rules.RavenHoareTriple Γ F Δ pre first
      (Atomicity.analysis_mask state) (Atomicity.analysis_mask middle)
      middle_assertion)
    (second_derivation : @Rules.RavenHoareTriple Γ F Δ middle_assertion second
      (Atomicity.analysis_mask middle) (Atomicity.analysis_mask exit) post),
    certificate_hoare_aligned cost first_certificate first_derivation ->
    certificate_hoare_aligned cost second_certificate second_derivation ->
    certificate_hoare_aligned cost
      (Atomicity.CertSequence cost Γ fuel state (TSeq node first second)
        first middle second exit
        view first_certificate second_certificate)
      (Rules.SequenceRule node pre middle_assertion post first second
        (Atomicity.analysis_mask state) (Atomicity.analysis_mask middle)
        (Atomicity.analysis_mask exit) first_derivation second_derivation)
| AlignedConditional : forall Γ F Δ fuel state node store frame condition
    then_branch else_branch then_exit else_exit post view then_certificate
    else_certificate open_equal atomic_equal branch_mask
    (then_derivation : @Rules.RavenHoareTriple Γ F Δ
      (Translation.Assertions.AAnd (Translation.Assertions.AStack store)
        (Translation.Assertions.AAnd frame
          (Translation.Assertions.AExpr (Hoare.symbolize_expr store condition))))
      then_branch (Atomicity.analysis_mask state) branch_mask
      post)
    (else_derivation : @Rules.RavenHoareTriple Γ F Δ
      (Translation.Assertions.AAnd (Translation.Assertions.AStack store)
        (Translation.Assertions.AAnd frame
          (Translation.Assertions.AExpr (EUnOp UNot
            (Hoare.symbolize_expr store condition)))))
      else_branch (Atomicity.analysis_mask state) branch_mask
      post)
    (then_mask : Atomicity.analysis_mask then_exit =
      branch_mask)
    (else_mask : Atomicity.analysis_mask else_exit =
      branch_mask),
    certificate_hoare_aligned cost then_certificate
      (hoare_mask_transport then_derivation eq_refl (eq_sym then_mask)) ->
    certificate_hoare_aligned cost else_certificate
      (hoare_mask_transport else_derivation eq_refl (eq_sym else_mask)) ->
    certificate_hoare_aligned cost
      (Atomicity.CertConditional cost Γ fuel state
        (TIf node condition then_branch else_branch) then_branch else_branch
        then_exit else_exit view then_certificate else_certificate
        open_equal atomic_equal)
      (hoare_mask_transport
        (Rules.ConditionalRule node store frame condition then_branch else_branch
          post (Atomicity.analysis_mask state) branch_mask then_derivation
          else_derivation)
        eq_refl
        (conditional_analysis_mask state then_exit else_exit branch_mask
          then_mask else_mask))
| AlignedAtomic : forall Γ F Δ fuel state node body outer inner pre post
    (view : RegionSyntax.view (TAtomic node body) =
      TypedAnalysisView.ViewAtomic body)
    (step : Atomicity.take_step Atomicity.AtomicStep state = inr outer)
    (body_certificate : Atomicity.analysis_certificate cost Γ fuel
      (Atomicity.AnalysisState (Atomicity.analysis_mask outer)
        (Atomicity.analysis_open outer) (Atomicity.analysis_step_taken outer) true)
      body inner)
    (open_equal : Atomicity.analysis_open inner = Atomicity.analysis_open outer)
    (trusted : Contracts.trusted_atomic Γ body)
    (body_derivation : @Rules.RavenHoareTriple Γ F Δ pre body
      (Atomicity.analysis_mask state) (Atomicity.analysis_mask inner) post),
    certificate_hoare_aligned cost body_certificate
      (hoare_mask_transport body_derivation
        (eq_sym (step_analysis_mask state outer step))
        eq_refl) ->
    certificate_hoare_aligned cost
      (Atomicity.CertAtomic cost Γ fuel state (TAtomic node body) body outer inner
        view step body_certificate open_equal)
      (Rules.AtomicBlockRule node pre post body
        (Atomicity.analysis_mask state) (Atomicity.analysis_mask inner)
        trusted body_derivation)
| AlignedFrame : forall (Γ F Δ : context) (fuel : nat)
    (entry exit : Atomicity.analysis_state) (statement : stmt Γ)
    (pre post frame : Translation.Assertions.assertion Γ F Δ)
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement exit)
    (derivation : @Rules.RavenHoareTriple Γ F Δ pre statement
      (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit) post),
    certificate_hoare_aligned cost certificate derivation ->
    certificate_hoare_aligned cost certificate
      (Rules.FrameRule pre post frame statement
        (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit)
        derivation)
| AlignedConsequence : forall (Γ F Δ : context) (fuel : nat)
    (entry exit : Atomicity.analysis_state) (statement : stmt Γ)
    (pre pre' post post' : Translation.Assertions.assertion Γ F Δ)
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement exit)
    (derivation : @Rules.RavenHoareTriple Γ F Δ pre statement
      (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit) post)
    (pre_entails : Hoare.assertion_entails pre' pre)
    (post_entails : Hoare.assertion_entails post post'),
    certificate_hoare_aligned cost certificate derivation ->
    certificate_hoare_aligned cost certificate
      (Rules.ConsequenceRule pre pre' post post' statement
        (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit)
        derivation pre_entails post_entails)
| AlignedExistsElim : forall (Γ F Δ : context) t (fuel : nat)
    (entry exit : Atomicity.analysis_state) (statement : stmt Γ)
    (body : Translation.Assertions.assertion Γ F (t :: Δ))
    (post : Translation.Assertions.assertion Γ F Δ)
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement exit)
    (derivation : @Rules.RavenHoareTriple Γ F (t :: Δ) body statement
      (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit)
      (Translation.Assertions.weaken_assertion post)),
    certificate_hoare_aligned cost certificate derivation ->
    certificate_hoare_aligned cost certificate
      (Rules.ExistsElimRule t body post statement
        (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit)
        derivation)
| AlignedExistsPreserve : forall (Γ F Δ : context) t (fuel : nat)
    (entry exit : Atomicity.analysis_state) (statement : stmt Γ)
    (body post : Translation.Assertions.assertion Γ F (t :: Δ))
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement exit)
    (derivation : @Rules.RavenHoareTriple Γ F (t :: Δ) body statement
      (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit) post),
    certificate_hoare_aligned cost certificate derivation ->
    certificate_hoare_aligned cost certificate
      (Rules.ExistsPreserveRule t body post statement
        (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit)
        derivation).

(** Resource-only counterpart to [certificate_hoare_aligned].  The analysis
    certificate owns all mask bookkeeping; this pairing records just the
    matching resource proof structure. *)
Inductive resource_certificate_hoare_aligned (cost : Atomicity.cost_model) :
    forall {Γ F Δ fuel} {entry : Atomicity.analysis_state}
      {statement : stmt Γ} {exit : Atomicity.analysis_state}
      {pre post : Translation.Assertions.assertion Γ F Δ},
      Atomicity.analysis_certificate cost Γ fuel entry statement exit ->
      @Rules.RavenResourceTriple Γ F Δ pre statement post ->
      Type :=
| ResourceAlignedOrdinaryLeaf : forall Γ F Δ fuel entry statement exit pre post
    view step
    (derivation : @Rules.RavenResourceTriple Γ F Δ pre statement post),
    resource_certificate_hoare_aligned cost
      (Atomicity.CertLeaf cost Γ fuel entry statement exit view step)
      derivation
| ResourceAlignedUnfold : forall Γ F Δ fuel entry node invariant arguments exit
    store body
    (view : RegionSyntax.view (TUnfold node invariant arguments) =
      TypedAnalysisView.ViewUnfold invariant)
    (step : Atomicity.open_invariant invariant entry = inr exit)
    (instantiated : Contracts.instantiated_invariant Γ F Δ
      (Logic.invariant_args invariant) invariant
      (Hoare.symbolize_expr_list store arguments) body),
    resource_certificate_hoare_aligned cost
      (Atomicity.CertUnfold cost Γ fuel entry
        (TUnfold node invariant arguments) invariant exit view step)
      (Rules.ResourceUnfoldInvariantRule node invariant arguments store body
        instantiated)
| ResourceAlignedFold : forall Γ F Δ fuel entry node invariant arguments
    store body
    (view : RegionSyntax.view (TFold node invariant arguments) =
      TypedAnalysisView.ViewFold invariant)
    (instantiated : Contracts.instantiated_invariant Γ F Δ
      (Logic.invariant_args invariant) invariant
      (Hoare.symbolize_expr_list store arguments) body),
    resource_certificate_hoare_aligned cost
      (Atomicity.CertFold cost Γ fuel entry
        (TFold node invariant arguments) invariant view)
      (Rules.ResourceFoldInvariantRule node invariant arguments store body
        instantiated)
| ResourceAlignedSequence : forall Γ F Δ fuel state node first middle second exit
    pre middle_assertion post view first_certificate second_certificate
    (first_derivation : @Rules.RavenResourceTriple Γ F Δ pre first
      middle_assertion)
    (second_derivation : @Rules.RavenResourceTriple Γ F Δ middle_assertion second
      post),
    resource_certificate_hoare_aligned cost first_certificate first_derivation ->
    resource_certificate_hoare_aligned cost second_certificate second_derivation ->
    resource_certificate_hoare_aligned cost
      (Atomicity.CertSequence cost Γ fuel state (TSeq node first second)
        first middle second exit view first_certificate second_certificate)
      (Rules.ResourceSequenceRule node pre middle_assertion post first second
        first_derivation second_derivation)
| ResourceAlignedConditional : forall Γ F Δ fuel state node store frame condition
    then_branch else_branch then_exit else_exit post view then_certificate
    else_certificate open_equal atomic_equal
    (then_derivation : @Rules.RavenResourceTriple Γ F Δ
      (Translation.Assertions.AAnd (Translation.Assertions.AStack store)
        (Translation.Assertions.AAnd frame
          (Translation.Assertions.AExpr (Hoare.symbolize_expr store condition))))
      then_branch post)
    (else_derivation : @Rules.RavenResourceTriple Γ F Δ
      (Translation.Assertions.AAnd (Translation.Assertions.AStack store)
        (Translation.Assertions.AAnd frame
          (Translation.Assertions.AExpr (EUnOp UNot
            (Hoare.symbolize_expr store condition)))))
      else_branch post),
    resource_certificate_hoare_aligned cost then_certificate then_derivation ->
    resource_certificate_hoare_aligned cost else_certificate else_derivation ->
    resource_certificate_hoare_aligned cost
      (Atomicity.CertConditional cost Γ fuel state
        (TIf node condition then_branch else_branch) then_branch else_branch
        then_exit else_exit view then_certificate else_certificate
        open_equal atomic_equal)
      (Rules.ResourceConditionalRule node store frame condition
        then_branch else_branch post then_derivation else_derivation)
| ResourceAlignedAtomic : forall Γ F Δ fuel state node body outer inner pre post
    (view : RegionSyntax.view (TAtomic node body) =
      TypedAnalysisView.ViewAtomic body)
    (step : Atomicity.take_step Atomicity.AtomicStep state = inr outer)
    (body_certificate : Atomicity.analysis_certificate cost Γ fuel
      (Atomicity.AnalysisState (Atomicity.analysis_mask outer)
        (Atomicity.analysis_open outer) (Atomicity.analysis_step_taken outer) true)
      body inner)
    (open_equal : Atomicity.analysis_open inner = Atomicity.analysis_open outer)
    (trusted : Contracts.trusted_atomic Γ body)
    (body_derivation : @Rules.RavenResourceTriple Γ F Δ pre body post),
    resource_certificate_hoare_aligned cost body_certificate body_derivation ->
    resource_certificate_hoare_aligned cost
      (Atomicity.CertAtomic cost Γ fuel state (TAtomic node body) body outer inner
        view step body_certificate open_equal)
      (Rules.ResourceAtomicBlockRule node pre post body trusted body_derivation)
| ResourceAlignedFrame : forall (Γ F Δ : context) (fuel : nat)
    (entry exit : Atomicity.analysis_state) (statement : stmt Γ)
    (pre post frame : Translation.Assertions.assertion Γ F Δ)
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement exit)
    (derivation : @Rules.RavenResourceTriple Γ F Δ pre statement post),
    resource_certificate_hoare_aligned cost certificate derivation ->
    resource_certificate_hoare_aligned cost certificate
      (Rules.ResourceFrameRule pre post frame statement derivation)
| ResourceAlignedConsequence : forall (Γ F Δ : context) (fuel : nat)
    (entry exit : Atomicity.analysis_state) (statement : stmt Γ)
    (pre pre' post post' : Translation.Assertions.assertion Γ F Δ)
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement exit)
    (derivation : @Rules.RavenResourceTriple Γ F Δ pre statement post)
    (pre_entails : Hoare.assertion_entails pre' pre)
    (post_entails : Hoare.assertion_entails post post'),
    resource_certificate_hoare_aligned cost certificate derivation ->
    resource_certificate_hoare_aligned cost certificate
      (Rules.ResourceConsequenceRule pre pre' post post' statement
        derivation pre_entails post_entails)
| ResourceAlignedExistsElim : forall (Γ F Δ : context) t (fuel : nat)
    (entry exit : Atomicity.analysis_state) (statement : stmt Γ)
    (body : Translation.Assertions.assertion Γ F (t :: Δ))
    (post : Translation.Assertions.assertion Γ F Δ)
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement exit)
    (derivation : @Rules.RavenResourceTriple Γ F (t :: Δ) body statement
      (Translation.Assertions.weaken_assertion post)),
    resource_certificate_hoare_aligned cost certificate derivation ->
    resource_certificate_hoare_aligned cost certificate
      (Rules.ResourceExistsElimRule t body post statement derivation)
| ResourceAlignedExistsPreserve : forall (Γ F Δ : context) t (fuel : nat)
    (entry exit : Atomicity.analysis_state) (statement : stmt Γ)
    (body post : Translation.Assertions.assertion Γ F (t :: Δ))
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement exit)
    (derivation : @Rules.RavenResourceTriple Γ F (t :: Δ) body statement post),
    resource_certificate_hoare_aligned cost certificate derivation ->
    resource_certificate_hoare_aligned cost certificate
      (Rules.ResourceExistsPreserveRule t body post statement derivation).

Lemma resource_alignment_proof_irrelevance
    {cost Γ F Δ fuel entry statement exit pre post}
    (certificate : Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    (source target : @Rules.RavenResourceTriple Γ F Δ pre statement post) :
  source = target ->
  resource_certificate_hoare_aligned cost certificate source ->
  resource_certificate_hoare_aligned cost certificate target.
Proof.
  intros -> Haligned.
  exact Haligned.
Qed.

Theorem certificate_hoare_aligned_erases_resource
    {cost Γ F Δ fuel entry statement exit pre post}
    (certificate : Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    (derivation : @Rules.RavenHoareTriple Γ F Δ pre statement
      (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit) post) :
  certificate_hoare_aligned cost certificate derivation ->
  resource_certificate_hoare_aligned cost certificate
    (Rules.RavenHoareTriple_erases_resource pre statement
      (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit) post
      derivation).
Proof.
  intro Haligned.
  induction Haligned.
  - apply ResourceAlignedOrdinaryLeaf.
  - eapply resource_alignment_proof_irrelevance.
    + apply proof_irrelevance.
    + apply ResourceAlignedUnfold.
  - eapply resource_alignment_proof_irrelevance.
    + apply proof_irrelevance.
    + apply ResourceAlignedFold.
  - eapply resource_alignment_proof_irrelevance.
    + apply proof_irrelevance.
    + eapply ResourceAlignedSequence; eauto.
  - eapply resource_alignment_proof_irrelevance.
    + apply proof_irrelevance.
    + eapply ResourceAlignedConditional; eauto.
  - eapply resource_alignment_proof_irrelevance.
    + apply proof_irrelevance.
    + eapply ResourceAlignedAtomic; eauto.
  - eapply resource_alignment_proof_irrelevance.
    + apply proof_irrelevance.
    + eapply ResourceAlignedFrame; eauto.
  - eapply resource_alignment_proof_irrelevance.
    + apply proof_irrelevance.
    + eapply ResourceAlignedConsequence; eauto.
  - eapply resource_alignment_proof_irrelevance.
    + apply proof_irrelevance.
    + eapply ResourceAlignedExistsElim; eauto.
  - eapply resource_alignment_proof_irrelevance.
    + apply proof_irrelevance.
    + eapply ResourceAlignedExistsPreserve; eauto.
  Unshelve.
  all: eauto.
Qed.

(** Hoare alignment rules out branch-local mask declarations which disappear
    at a conditional join.  Consequently every namespace mentioned by an
    aligned analysis certificate is available again either in its final Raven
    mask or among its final open invariants.  This is a statement about
    Raven-level masks only; [Model.runtime_mask] is applied to this bound at
    the Iris boundary. *)
Lemma aligned_certificate_footprint_subset_exit_resources
    {cost Γ F Δ fuel entry statement exit pre post}
    (certificate : Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    (derivation : @Rules.RavenHoareTriple Γ F Δ pre statement
      (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit) post) :
  certificate_hoare_aligned cost certificate derivation ->
  Atomicity.certificate_footprint certificate ⊆
    Atomicity.analysis_mask exit ∪ Atomicity.analysis_open exit.
Proof.
  intro Haligned.
  induction Haligned; simpl.
  - have Hstart := Atomicity.take_step_resources_monotone _ _ _ step.
    intros other Hmember.
    specialize (Hstart other).
    rewrite !elem_of_union in Hmember, Hstart |- *.
    rewrite elem_of_empty in Hmember.
    tauto.
  - apply Atomicity.open_invariant_success in step as
      (Hfresh & Havailable & Hmask & Hopen).
    rewrite Hmask. rewrite Hopen.
    intros other Hmember.
    rewrite !elem_of_union in Hmember |- *.
    rewrite !elem_of_difference in Hmember |- *.
    rewrite !elem_of_singleton in Hmember |- *.
    rewrite elem_of_empty in Hmember.
    destruct (decide (other = invariant)) as [->|Hneq]; tauto.
  - unfold Atomicity.fold_invariant.
    destruct (bool_decide (invariant ∈ Atomicity.analysis_open entry)); simpl;
      intros other Hmember;
      rewrite !elem_of_union in Hmember |- *;
      rewrite ?elem_of_difference in Hmember |- *;
      rewrite ?elem_of_singleton in Hmember |- *;
      rewrite elem_of_empty in Hmember;
      destruct (decide (other = invariant)) as [->|Hneq]; tauto.
  - have Hmiddle : Atomicity.analysis_mask middle ∪
      Atomicity.analysis_open middle ⊆
      Atomicity.analysis_mask exit ∪ Atomicity.analysis_open exit.
    { etrans.
      - intros invariant Hmember.
        rewrite elem_of_union in Hmember.
        destruct Hmember as [Hmask|Hopen].
        + apply (Atomicity.certificate_entry_subset_footprint
            second_certificate).
          exact Hmask.
        + apply (Atomicity.certificate_entry_open_subset_footprint
            second_certificate).
          exact Hopen.
      - exact IHHaligned2. }
    have Hstart : Atomicity.analysis_mask state ∪
        Atomicity.analysis_open state ⊆
        Atomicity.analysis_mask middle ∪ Atomicity.analysis_open middle.
    { etrans.
      - intros invariant Hmember.
        rewrite elem_of_union in Hmember.
        destruct Hmember as [Hmask|Hopen].
        + apply (Atomicity.certificate_entry_subset_footprint
            first_certificate). exact Hmask.
        + apply (Atomicity.certificate_entry_open_subset_footprint
            first_certificate). exact Hopen.
      - exact IHHaligned1. }
    intros other Hmember.
    specialize (IHHaligned1 other).
    specialize (IHHaligned2 other).
    specialize (Hmiddle other).
    specialize (Hstart other).
    rewrite !elem_of_union in Hmember, IHHaligned1, IHHaligned2, Hmiddle,
      Hstart |- *.
    tauto.
  - rewrite then_mask. rewrite else_mask.
    have Hmask_idem : branch_mask ∩ branch_mask = branch_mask.
    { apply set_eq. intros invariant.
      rewrite elem_of_intersection. tauto. }
    rewrite Hmask_idem.
    rewrite then_mask in IHHaligned1.
    rewrite else_mask in IHHaligned2.
    rewrite <- open_equal in IHHaligned2.
    have Hstart : Atomicity.analysis_mask state ∪
        Atomicity.analysis_open state ⊆
        branch_mask ∪ Atomicity.analysis_open then_exit.
    { etrans.
      - intros invariant Hmember.
        rewrite elem_of_union in Hmember.
        destruct Hmember as [Hmask|Hopen].
        + apply (Atomicity.certificate_entry_subset_footprint
            then_certificate). exact Hmask.
        + apply (Atomicity.certificate_entry_open_subset_footprint
            then_certificate). exact Hopen.
      - exact IHHaligned1. }
    intros other Hmember.
    specialize (IHHaligned1 other).
    specialize (IHHaligned2 other).
    specialize (Hstart other).
    rewrite !elem_of_union in Hmember, IHHaligned1, IHHaligned2, Hstart |- *.
    destruct Hmember as [[[[Hentry_mask | Hentry_open] | Hexit_mask] |
      Hexit_open] | [Hthen | Helse]].
    + exact (Hstart (or_introl Hentry_mask)).
    + exact (Hstart (or_intror Hentry_open)).
    + left. exact Hexit_mask.
    + right. exact Hexit_open.
    + apply IHHaligned1. exact Hthen.
    + apply IHHaligned2. exact Helse.
  - have Hsets := Atomicity.atomic_step_preserves_sets _ _ step.
    destruct Hsets as [Hmask Hopen].
    have Hentry : Atomicity.analysis_mask state ∪
      Atomicity.analysis_open state ⊆
      Atomicity.analysis_mask inner ∪ Atomicity.analysis_open inner.
    { rewrite <- Hmask, <- Hopen.
      etrans.
      - intros invariant Hmember.
        rewrite elem_of_union in Hmember.
        destruct Hmember as [Hmask'|Hopen'].
        + apply (Atomicity.certificate_entry_subset_footprint
            body_certificate).
          exact Hmask'.
        + apply (Atomicity.certificate_entry_open_subset_footprint
            body_certificate).
          exact Hopen'.
      - exact IHHaligned. }
    intros other Hmember.
    specialize (IHHaligned other).
    specialize (Hentry other).
    rewrite !elem_of_union in Hmember, IHHaligned, Hentry |- *.
    destruct Hmember as [[[[Hentry_mask | Hentry_open] | Hexit_mask] |
      Hexit_open] | Hbody].
    + exact (Hentry (or_introl Hentry_mask)).
    + exact (Hentry (or_intror Hentry_open)).
    + left. exact Hexit_mask.
    + right. exact Hexit_open.
    + apply IHHaligned. exact Hbody.
  - exact IHHaligned.
  - exact IHHaligned.
  - exact IHHaligned.
  - exact IHHaligned.
Qed.

Record CertifiedRavenHoareTriple (cost : Atomicity.cost_model)
    {Γ F Δ fuel}
    (stack_in stack_out : list GenericRegions.Atomicity.access_marker)
    (pre : Translation.Assertions.assertion Γ F Δ) (statement : stmt Γ)
    (entry exit : Atomicity.analysis_state)
    (post : Translation.Assertions.assertion Γ F Δ) : Type := {
  certified_analysis :
    Atomicity.analysis_certificate cost Γ fuel entry statement exit;
  certified_lifo :
    Atomicity.lifo_certificate certified_analysis stack_in stack_out;
  certified_hoare :
    @Rules.RavenHoareTriple Γ F Δ pre statement
      (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit) post;
  certified_alignment :
    certificate_hoare_aligned cost certified_analysis certified_hoare;
}.

Definition ClosedCertifiedRavenHoareTriple cost {Γ F Δ fuel}
    (pre : Translation.Assertions.assertion Γ F Δ) (statement : stmt Γ)
    (entry exit : Atomicity.analysis_state)
    (post : Translation.Assertions.assertion Γ F Δ) : Type :=
  @CertifiedRavenHoareTriple cost Γ F Δ fuel [] []
    pre statement entry exit post.

(** New proof-facing certified judgment.  Raven resources are proved without
    exposing analyzer masks; the paired certificate and coherent cost model
    own all control-state obligations. *)
Record CertifiedRavenResourceTriple (cost : Atomicity.cost_model)
    {Γ F Δ fuel}
    (stack_in stack_out : list GenericRegions.Atomicity.access_marker)
    (pre : Translation.Assertions.assertion Γ F Δ) (statement : stmt Γ)
    (entry exit : Atomicity.analysis_state)
    (post : Translation.Assertions.assertion Γ F Δ) : Type := {
  certified_resource_analysis :
    Atomicity.analysis_certificate cost Γ fuel entry statement exit;
  certified_resource_lifo :
    Atomicity.lifo_certificate certified_resource_analysis stack_in stack_out;
  certified_resource_cost_sound : procedure_cost_model_sound cost;
  certified_resource_hoare :
    @Rules.RavenResourceTriple Γ F Δ pre statement post;
  certified_resource_alignment :
    resource_certificate_hoare_aligned cost certified_resource_analysis
      certified_resource_hoare;
}.

Definition ClosedCertifiedRavenResourceTriple cost {Γ F Δ fuel}
    (pre : Translation.Assertions.assertion Γ F Δ) (statement : stmt Γ)
    (entry exit : Atomicity.analysis_state)
    (post : Translation.Assertions.assertion Γ F Δ) : Type :=
  @CertifiedRavenResourceTriple cost Γ F Δ fuel [] []
    pre statement entry exit post.

Lemma certified_hoare_erases_resource cost {Γ F Δ fuel}
    stack_in stack_out pre (statement : stmt Γ) entry exit post :
  procedure_cost_model_sound cost ->
  @CertifiedRavenHoareTriple cost Γ F Δ fuel stack_in stack_out
    pre statement entry exit post ->
  @CertifiedRavenResourceTriple cost Γ F Δ fuel stack_in stack_out
    pre statement entry exit post.
Proof.
  intros Hcost certified.
  destruct certified as [certificate lifo derivation alignment].
  refine {| certified_resource_analysis := certificate;
    certified_resource_lifo := lifo;
    certified_resource_cost_sound := Hcost;
    certified_resource_hoare :=
      Rules.RavenHoareTriple_erases_resource pre statement
        (Atomicity.analysis_mask entry) (Atomicity.analysis_mask exit) post
        derivation |}.
  exact (certificate_hoare_aligned_erases_resource certificate derivation
    alignment).
Qed.

Lemma certified_exit_wf cost {Γ F Δ fuel} stack_in stack_out pre
    (statement : stmt Γ) entry exit post :
  Atomicity.state_wf entry ->
  @CertifiedRavenHoareTriple cost Γ F Δ fuel stack_in stack_out
    pre statement entry exit post ->
  Atomicity.state_wf exit.
Proof.
  intros Hwf certified. destruct certified as [certificate lifo hoare alignment].
  eapply Atomicity.certificate_preserves_wf; eauto.
Qed.

End CertifiedRegions.

(** A body certificate is mask-parametric in exactly the same way as the call
    rule: any caller mask containing the declaration's required mask may run
    the body, and the declaration's granted mask is available on return. *)
Module CertifiedProcedureBodies (Contracts : Hoare.CONTRACT_ENV).
Module Certified := CertifiedRegions Contracts.

Record body_certificate {Γ F} (procedure : typed_procedure Γ F)
    (current_mask : Hoare.mask) : Type := BodyCertificate {
  body_fuel : nat;
  body_cost : GenericRegions.Atomicity.cost_model;
  body_entry : GenericRegions.Atomicity.analysis_state;
  body_exit : GenericRegions.Atomicity.analysis_state;
  body_exit_store : symbolic_store Γ F [];
  body_post : Translation.Assertions.assertion Γ F [];
  (** Procedure bodies start outside every dynamically opened invariant.
      Recording these facts in the certificate keeps the recursive body
      proof independent of the caller's control-flow proof state. *)
  body_entry_wf : GenericRegions.Atomicity.state_wf body_entry;
  body_entry_closed : GenericRegions.Atomicity.analysis_open body_entry = ∅;
  body_entry_mask : GenericRegions.Atomicity.analysis_mask body_entry = current_mask;
  body_exit_mask : GenericRegions.Atomicity.analysis_mask body_exit =
    current_mask ∪ Contracts.granted_mask
      (procedure_identity _ _ procedure);
  body_post_canonical :
    Hoare.procedure_body_post procedure body_exit_store = Some body_post;
  body_derivation :
    @Certified.ClosedCertifiedRavenHoareTriple
      body_cost Γ F [] body_fuel
      (Hoare.procedure_body_pre procedure) (procedure_body _ _ procedure)
      body_entry body_exit body_post;
  body_operational_footprint :
    GenericRegions.Atomicity.certificate_operational_footprint
      (@Certified.certified_analysis body_cost Γ F [] body_fuel [] []
        (Hoare.procedure_body_pre procedure) (procedure_body _ _ procedure)
        body_entry body_exit body_post body_derivation) ⊆ current_mask;
}.

Definition body_valid {Γ F} (procedure : typed_procedure Γ F) : Type :=
  forall current_mask,
    Contracts.required_mask (procedure_identity _ _ procedure) ⊆ current_mask ->
    body_certificate procedure current_mask.

Definition packed_body_valid (packed : packed_typed_procedure) : Type :=
  match packed with
  | existT Γ (existT F procedure) => @body_valid Γ F procedure
  end.
End CertifiedProcedureBodies.

Module Type RUNTIME_RESOURCES.
  Parameter Σ : gFunctors.
  Parameter simpLangG0 : LegacyLifting.simpLangG Σ.
  Parameter invTokenG0 : Legacy.invTokenG Σ.

  Parameter field_name : field_id -> LegacyLang.fld_name.
  Parameter field_name_injective : Inj (=) (=) field_name.
  Parameter invariant_name : inv_id -> Legacy.inv_name.
  Parameter invariant_name_injective : Inj (=) (=) invariant_name.
  Parameter invariant_namespace : inv_id -> namespace.
  Parameter invariant_namespaces_disjoint : forall left right,
    left ≠ right ->
    (↑(invariant_namespace left) : coPset) ## ↑(invariant_namespace right).
  Parameter ghost_heap_namespace : namespace.
  Parameter invariant_ghost_namespace_disjoint : forall invariant,
    (↑(invariant_namespace invariant) : coPset) ## ↑ghost_heap_namespace.
  Parameter procedure_name : proc_id -> LegacyLang.proc_name.
  Parameter procedure_name_injective : Inj (=) (=) procedure_name.
End RUNTIME_RESOURCES.

Module ConcreteModel (Resources : RUNTIME_RESOURCES).

Existing Instance Resources.invTokenG0.
Existing Instance Resources.simpLangG0.
Local Instance concrete_heapG : LegacyGhost.heapG Resources.Σ :=
  LegacyLifting.simpLangG_gen_heapG.
Local Instance concrete_irisG : irisGS LegacyLang.simp_lang Resources.Σ :=
  LegacyLifting.simpLang_irisG.
Local Existing Instance weakestpre.wp'.

Local Instance concrete_invtoken_inG :
    inG Resources.Σ (authR Legacy.inv_argsUR) :=
  @Legacy.invtoken_inG Resources.Σ Resources.invTokenG0.

Definition PROP : bi := iPropI Resources.Σ.

(** The fixed Iris mask envelope in which a certified region executes. *)
Definition ambient_mask : Type := coPset.

Definition bi_affine : BiAffine PROP := _.

Definition tval_to_val {t} (value : tval t) : LegacyLang.val :=
  match value with
  | VBool boolean => LegacyLang.LitBool boolean
  | VInt integer => LegacyLang.LitInt integer
  | VRef location => LegacyLang.LitLoc (LegacyLang.Loc location)
  | VUnit => LegacyLang.LitUnit
  | VRA resource => LegacyLang.LitRAElem
      (@existT string
        (fun name => ra_base.RA_carrier (LegacyRAs.ra_map name))
        _ resource)
  end.

Definition runtime_type (t : TypedCore.typ) : LegacyLang.typ :=
  match t with
  | TBool => LegacyLang.TpBool
  | TInt => LegacyLang.TpInt
  | TRef => LegacyLang.TpLoc
  | TUnit => LegacyLang.TpUnit
  | TRA resource => LegacyLang.TpRA resource
  end.

Fixpoint runtime_variables {Γ} (names : named_context Γ) :
    list LegacyLang.var :=
  match names with
  | NCNil => []
  | NCCons source_name _ tail => source_name :: runtime_variables tail
  end.

Definition runtime_variable {Γ t} (names : named_context Γ)
    (variable : pvar Γ t) : LegacyLang.var :=
  default "" (runtime_variables names !! member_index variable).

(** Runtime procedure frames reserve the legacy return name, but the slot is
    still the procedure's distinguished typed variable.  Rename that one
    decoration in the naming context so body translation and frame ownership
    use exactly the same key as the legacy call machinery. *)
Fixpoint rename_named_context_at {Γ} (names : named_context Γ)
    (replacement : string) (index : nat) : named_context Γ :=
  match names with
  | NCNil => NCNil
  | NCCons name u tail =>
      match index with
      | 0 => NCCons replacement u tail
      | S tail_index =>
          NCCons name u (rename_named_context_at tail replacement tail_index)
      end
  end.

Definition runtime_procedure_names {Γ F}
    (procedure : typed_procedure Γ F) : named_context Γ :=
  rename_named_context_at (procedure_variables _ _ procedure) "#ret_val"
    (member_index (procedure_return_variable _ _ procedure)).

Lemma runtime_variables_rename_named_context_at_member {Γ}
    (names : named_context Γ) replacement index name :
  In name (runtime_variables
    (rename_named_context_at names replacement index)) ->
  name = replacement \/ In name (runtime_variables names).
Proof.
  revert index. induction names; intros [|index]; simpl.
  - tauto.
  - tauto.
  - intros [-> | Hin]; [left; reflexivity | right; now right].
  - intros [-> | Hin].
    + right. now left.
    + destruct (IHnames index Hin); [now left | right; now right].
Qed.

Lemma runtime_variables_rename_named_context_at_lookup {Γ}
    (names : named_context Γ) replacement index :
  index < length (runtime_variables names) ->
  runtime_variables (rename_named_context_at names replacement index) !! index =
    Some replacement.
Proof.
  revert index. induction names; intros [|index] Hindex; simpl in *.
  - lia.
  - lia.
  - reflexivity.
  - apply IHnames. lia.
Qed.

Lemma runtime_variables_rename_named_context_at_nodup {Γ}
    (names : named_context Γ) replacement index :
  NoDup (runtime_variables names) ->
  ~ In replacement (runtime_variables names) ->
  NoDup (runtime_variables
    (rename_named_context_at names replacement index)).
Proof.
  revert index. induction names; intros [|index] Hnames Hfresh; simpl in *.
  - constructor.
  - constructor.
  - inversion Hnames as [|? ? Hhead Htail]. constructor.
    + intros Hin. apply elem_of_list_In in Hin.
      apply Hfresh. right; exact Hin.
    + exact Htail.
  - inversion Hnames as [|? ? Hhead Htail]. constructor.
    + intros Hin.
      apply elem_of_list_In in Hin.
      destruct (runtime_variables_rename_named_context_at_member
        names replacement index name Hin) as [Heq | Hin'].
      * apply Hfresh. left. exact Heq.
      * apply Hhead. apply elem_of_list_In. exact Hin'.
    + apply IHnames; [exact Htail|].
      intros Hin. apply Hfresh. right.
      exact Hin.
Qed.

Lemma runtime_procedure_names_nodup {Γ F}
    (procedure : typed_procedure Γ F) :
  procedure_wf procedure ->
  ~ List.In "#ret_val"
      (named_context_names (procedure_variables _ _ procedure)) ->
  NoDup (runtime_variables (runtime_procedure_names procedure)).
Proof.
  intros Hwf Hfresh. apply runtime_variables_rename_named_context_at_nodup.
  - change (NoDup
      (named_context_names (procedure_variables _ _ procedure))).
    apply NoDup_ListNoDup. exact (procedure_variable_names_unique _ Hwf).
  - change (~ List.In "#ret_val"
      (named_context_names (procedure_variables _ _ procedure))).
    exact Hfresh.
Qed.

(** The legacy procedure record uses untyped declaration lists.  These
    projections are nevertheless generated from the intrinsic frame layout,
    so an argument declaration always names a body slot of the same type. *)
Fixpoint runtime_formal_declarations {Γ F} (names : named_context Γ)
    (variables : pvar_list Γ F) : list (LegacyLang.var * LegacyLang.typ) :=
  match variables with
  | PVNil => []
  | @PVCons _ tail t variable variables' =>
      (runtime_variable names variable, runtime_type t) ::
        runtime_formal_declarations names variables'
  end.

Fixpoint runtime_local_declarations_from {Γ} (names : named_context Γ)
    (formal_indices : list nat) (return_index index : nat) :
    list (LegacyLang.var * LegacyLang.typ) :=
  match names with
  | NCNil => []
  | NCCons name t tail =>
      let tail_declarations := runtime_local_declarations_from tail
        formal_indices return_index (S index) in
      if existsb (Nat.eqb index) formal_indices then tail_declarations
      else
        let runtime_name :=
          if Nat.eqb index return_index then "#ret_val" else name in
        (runtime_name, runtime_type t) :: tail_declarations
  end.

Definition procedure_return_index {Γ F} (procedure : typed_procedure Γ F) :
    nat :=
  member_index (procedure_return_variable _ _ procedure).

Definition runtime_procedure_arguments {Γ F}
    (procedure : typed_procedure Γ F) :
    list (LegacyLang.var * LegacyLang.typ) :=
  runtime_formal_declarations (procedure_variables _ _ procedure)
    (procedure_formal_variables _ _ procedure).

Definition runtime_procedure_locals {Γ F}
    (procedure : typed_procedure Γ F) :
    list (LegacyLang.var * LegacyLang.typ) :=
  runtime_local_declarations_from
    (procedure_variables _ _ procedure)
    (pvar_list_indices (procedure_formal_variables _ _ procedure))
    (procedure_return_index procedure) 0.

Lemma runtime_formal_declarations_length {Γ F} (names : named_context Γ)
    (variables : pvar_list Γ F) :
  length (runtime_formal_declarations names variables) = length F.
Proof. induction variables; simpl; congruence. Qed.

Lemma runtime_procedure_arguments_length {Γ F}
    (procedure : typed_procedure Γ F) :
  length (runtime_procedure_arguments procedure) = length F.
Proof. apply runtime_formal_declarations_length. Qed.

Lemma runtime_variables_length {Γ} (names : named_context Γ) :
  length (runtime_variables names) = length Γ.
Proof. induction names; simpl; congruence. Qed.

Lemma member_index_lt {Γ t} (variable : pvar Γ t) :
  member_index variable < length Γ.
Proof. induction variable; simpl; lia. Qed.

Lemma runtime_procedure_return_name {Γ F}
    (procedure : typed_procedure Γ F) :
  runtime_variable (runtime_procedure_names procedure)
    (procedure_return_variable _ _ procedure) = "#ret_val".
Proof.
  unfold runtime_variable, runtime_procedure_names.
  rewrite runtime_variables_rename_named_context_at_lookup.
  - reflexivity.
  - rewrite runtime_variables_length. apply member_index_lt.
Qed.

Lemma runtime_variable_member {Γ} (names : named_context Γ) t
    (variable : pvar Γ t) :
  runtime_variable names variable ∈ runtime_variables names.
Proof.
  unfold runtime_variable.
  have Hlookup : is_Some (runtime_variables names !! member_index variable).
  { apply lookup_lt_is_Some_2. rewrite runtime_variables_length.
    apply member_index_lt. }
  destruct (runtime_variables names !! member_index variable) as [name|]
    eqn:Hname.
  - simpl. apply elem_of_list_lookup. exists (member_index variable). exact Hname.
  - destruct Hlookup as [name Hsome]. congruence.
Qed.

Lemma runtime_variables_are_names {Γ} (names : named_context Γ) :
  runtime_variables names = named_context_names names.
Proof. induction names; simpl; [reflexivity | f_equal; assumption]. Qed.

Lemma runtime_variable_lookup {Γ t} (names : named_context Γ)
    (variable : pvar Γ t) :
  runtime_variables names !! member_index variable =
    Some (runtime_variable names variable).
Proof.
  unfold runtime_variable.
  destruct (runtime_variables names !! member_index variable) as [name|]
    eqn:Hlookup; [reflexivity |].
  exfalso. apply lookup_ge_None_1 in Hlookup.
  rewrite runtime_variables_length in Hlookup.
  pose proof (member_index_lt variable). lia.
Qed.

Lemma runtime_variable_injective {Γ t u} (names : named_context Γ)
    (left : pvar Γ t) (right : pvar Γ u) :
  List.NoDup (named_context_names names) ->
  runtime_variable names left = runtime_variable names right ->
  member_index left = member_index right.
Proof.
  intros Hnames Heq.
  rewrite <- runtime_variables_are_names in Hnames.
  eapply NoDup_lookup;
    [apply NoDup_ListNoDup; exact Hnames | apply runtime_variable_lookup |].
  rewrite Heq. apply runtime_variable_lookup.
Qed.

Lemma runtime_formal_name_index {Γ F} (names : named_context Γ)
    (variables : pvar_list Γ F) name :
  List.In name (runtime_formal_declarations names variables).*1 ->
  exists index, List.In index (pvar_list_indices variables) /\
    runtime_variables names !! index = Some name.
Proof.
  induction variables as [| F t variable variables IH]; simpl.
  - intros Hin. inversion Hin.
  - intros [Heq | Hin].
    + subst name. exists (member_index variable). split; [left; reflexivity |].
      apply runtime_variable_lookup.
    + destruct (IH Hin) as (index & Hindex & Hlookup).
      exists index. split; [right; exact Hindex | exact Hlookup].
Qed.

Lemma runtime_formal_names_nodup {Γ F} (names : named_context Γ)
    (variables : pvar_list Γ F) :
  List.NoDup (named_context_names names) ->
  List.NoDup (pvar_list_indices variables) ->
  List.NoDup (runtime_formal_declarations names variables).*1.
Proof.
  intros Hnames Hindices. induction variables as [| F t variable variables IH];
    simpl in *; [constructor |].
  inversion Hindices as [| index indices Hfresh Htail]. constructor.
  - intros Hin. destruct (runtime_formal_name_index names variables _ Hin)
      as (other & Hother & Hlookup).
    apply Hfresh. enough (member_index variable = other) by congruence.
    rewrite <- runtime_variables_are_names in Hnames.
    eapply NoDup_lookup;
      [apply NoDup_ListNoDup; exact Hnames | apply runtime_variable_lookup |].
    exact Hlookup.
  - apply IH; assumption.
Qed.

Lemma runtime_procedure_argument_names_nodup {Γ F}
    (procedure : typed_procedure Γ F) :
  procedure_wf procedure ->
  List.NoDup (runtime_procedure_arguments procedure).*1.
Proof.
  intros Hwf. apply runtime_formal_names_nodup.
  - exact (procedure_variable_names_unique _ Hwf).
  - exact (procedure_formal_slots_unique _ Hwf).
Qed.

Lemma runtime_local_declarations_from_source_index {Γ}
    (names : named_context Γ) (formal_indices : list nat)
    (return_index index : nat) name :
  In name (runtime_local_declarations_from names formal_indices return_index
    index).*1 ->
  name = "#ret_val" \/
  exists local_index,
    runtime_variables names !! local_index = Some name /\
    ~ In (index + local_index) formal_indices.
Proof.
  revert index.
  induction names as [| Γ name0 t names IH]; intros index; simpl.
  - intros Hin. inversion Hin.
  - destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
    + intros Hin. destruct (IH (S index) Hin) as [Hret | Hsource].
      * left; exact Hret.
      * right. destruct Hsource as (local_index & Hlookup & Hnot).
        exists (S local_index). split.
        { rewrite lookup_cons. simpl. exact Hlookup. }
        { replace (index + S local_index) with (S index + local_index)
            by lia. exact Hnot. }
    + intros Hin. destruct (Nat.eqb index return_index) eqn:Hsame.
      * simpl in Hin. destruct Hin as [Hin | Hin].
        -- left. symmetry. exact Hin.
        -- destruct (IH (S index) Hin) as [Hret | Hsource].
           ++ left; exact Hret.
           ++ right. destruct Hsource as (local_index & Hlookup & Hnot).
              exists (S local_index). split.
              { rewrite lookup_cons. simpl. exact Hlookup. }
              { replace (index + S local_index) with
                  (S index + local_index) by lia. exact Hnot. }
      * simpl in Hin. destruct Hin as [Hin | Hin].
        -- subst name. right. exists 0. split; [simpl; reflexivity|].
           intro Hinformal.
           rewrite Nat.add_0_r in Hinformal.
           have Htrue : existsb (Nat.eqb index) formal_indices = true.
           { apply (proj2 (existsb_exists (Nat.eqb index)
                 formal_indices)).
             exists index. split; [exact Hinformal|apply Nat.eqb_refl]. }
           congruence.
        -- destruct (IH (S index) Hin) as [Hret | Hsource].
           ++ left; exact Hret.
           ++ right. destruct Hsource as (local_index & Hlookup & Hnot).
              exists (S local_index). split.
              { rewrite lookup_cons. simpl. exact Hlookup. }
              { replace (index + S local_index) with
                  (S index + local_index) by lia. exact Hnot. }
Qed.

Lemma runtime_local_declarations_from_no_return_name {Γ}
    (names : named_context Γ) (formal_indices : list nat)
    (return_index index : nat) :
  ~ List.In "#ret_val" (named_context_names names) ->
  return_index < index ->
  ~ List.In "#ret_val"
    (runtime_local_declarations_from names formal_indices return_index index).*1.
Proof.
  revert index.
  induction names as [| Γ name t names IH]; intros index; simpl.
  - intros _ _ Hin. inversion Hin.
  - intros Hfresh Hbound.
    have Hhead : ~ "#ret_val" = name.
    { intros Heq. subst name. apply Hfresh. simpl. now left. }
    have Htail : ~ List.In "#ret_val" (named_context_names names).
    { intros Hin. apply Hfresh. simpl. now right. }
    destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
    + apply IH; [exact Htail|lia].
    + destruct (Nat.eqb index return_index) eqn:Hsame.
      * apply Nat.eqb_eq in Hsame. subst return_index. lia.
      * intros Hin. simpl in Hin. destruct Hin as [Hin | Hin].
        -- apply Hhead. symmetry. exact Hin.
        -- apply (IH (S index) Htail); [lia|exact Hin].
Qed.

Lemma runtime_local_declarations_from_nodup {Γ}
    (names : named_context Γ) (formal_indices : list nat)
    (return_index index : nat) :
  List.NoDup (named_context_names names) ->
  ~ List.In "#ret_val" (named_context_names names) ->
  NoDup
    (runtime_local_declarations_from names formal_indices return_index index).*1.
Proof.
  revert index.
  induction names as [| Γ name t names IH]; intros index; simpl.
  - constructor.
  - intros Hnames Hfresh.
    inversion Hnames as [| ? ? Hhead Htail].
    have Hfresh_tail : ~ List.In "#ret_val" (named_context_names names).
    { intros Hin. apply Hfresh. simpl. now right. }
    destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
    + apply IH; [exact Htail|exact Hfresh_tail].
    + constructor.
      * intros Hin. destruct (Nat.eqb index return_index) eqn:Hsame.
        -- apply Nat.eqb_eq in Hsame. subst return_index.
           apply (runtime_local_declarations_from_no_return_name names
              formal_indices index (S index) Hfresh_tail); [lia|].
           apply elem_of_list_In. exact Hin.
        -- simpl in Hin. destruct (runtime_local_declarations_from_source_index
             names formal_indices return_index (S index) name
             (ltac:(apply elem_of_list_In; exact Hin)))
             as [Hret | Hsource].
           ++ apply Hfresh. left. exact Hret.
           ++ destruct Hsource as (local_index & Hlookup & Hnot).
              apply Hhead. rewrite <- runtime_variables_are_names.
              apply elem_of_list_In. apply elem_of_list_lookup. exists local_index.
              exact Hlookup.
      * apply IH; [exact Htail|exact Hfresh_tail].
Qed.

Lemma runtime_local_declarations_from_contains_return {Γ}
    (names : named_context Γ) (formal_indices : list nat)
    (result index : nat) :
  index <= result -> result < index + length (runtime_variables names) ->
  ~ In result formal_indices ->
  "#ret_val" ∈
    (runtime_local_declarations_from names formal_indices result index).*1.
Proof.
  revert index.
  induction names as [| Γ name t names IH]; intros index; simpl.
  - intros Hle Hlt _. change (result < index + 0) in Hlt. lia.
  - intros Hle Hlt Hnot.
    destruct (Nat.eqb index result) eqn:Hsame.
    + apply Nat.eqb_eq in Hsame; subst result.
      destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
      * exfalso. apply Hnot.
        apply existsb_exists in Hformal.
        destruct Hformal as (candidate & Hin & Heq).
        apply Nat.eqb_eq in Heq. subst candidate. exact Hin.
      * simpl. apply elem_of_cons. left. reflexivity.
    + apply Nat.eqb_neq in Hsame.
      assert (Hlt_index : index < result) by lia.
      destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
      * apply IH; [lia|lia|exact Hnot].
      * simpl. right. apply IH; [lia|lia|exact Hnot].
Qed.

Lemma runtime_procedure_locals_nodup {Γ F} (procedure : typed_procedure Γ F) :
  procedure_wf procedure ->
  ~ List.In "#ret_val"
      (named_context_names (procedure_variables _ _ procedure)) ->
  NoDup (runtime_procedure_locals procedure).*1.
Proof.
  intros Hwf Hfresh.
  unfold runtime_procedure_locals.
  apply runtime_local_declarations_from_nodup.
  - exact (procedure_variable_names_unique _ Hwf).
  - exact Hfresh.
Qed.

Lemma runtime_procedure_local_source_index {Γ F}
    (procedure : typed_procedure Γ F) name :
  In name (runtime_procedure_locals procedure).*1 ->
  name = "#ret_val" \/
  exists local_index,
    runtime_variables (procedure_variables _ _ procedure) !! local_index =
      Some name /\
    ~ In local_index (pvar_list_indices (procedure_formal_variables _ _ procedure)).
Proof.
  unfold runtime_procedure_locals.
  intros Hin. apply runtime_local_declarations_from_source_index in Hin.
  destruct Hin as [Hret | (local_index & Hlookup & Hnot)].
  - left; exact Hret.
  - right. exists local_index. split; [exact Hlookup|].
    simpl in Hnot. exact Hnot.
Qed.

Lemma runtime_procedure_return_local {Γ F} (procedure : typed_procedure Γ F) :
  procedure_wf procedure ->
  ~ List.In "#ret_val"
      (named_context_names (procedure_variables _ _ procedure)) ->
  "#ret_val" ∈ (runtime_procedure_locals procedure).*1.
Proof.
  intros Hwf Hfresh. apply runtime_local_declarations_from_contains_return.
  - lia.
  - rewrite runtime_variables_length. apply member_index_lt.
  - exact (procedure_return_slot_local _ Hwf).
Qed.

Lemma runtime_procedure_arguments_locals_disjoint {Γ F}
    (procedure : typed_procedure Γ F) :
  procedure_wf procedure ->
  ~ List.In "#ret_val"
      (named_context_names (procedure_variables _ _ procedure)) ->
  (runtime_procedure_arguments procedure).*1 ##
    (runtime_procedure_locals procedure).*1.
Proof.
  intros Hwf Hfresh name Hargument Hlocal.
  apply elem_of_list_In in Hargument.
  apply elem_of_list_In in Hlocal.
  destruct (runtime_formal_name_index
      (procedure_variables _ _ procedure)
      (procedure_formal_variables _ _ procedure) name Hargument)
    as (formal_index & Hformal_index & Hformal_lookup).
  destruct (runtime_procedure_local_source_index procedure name Hlocal)
    as [Hreturn | (local_index & Hlocal_lookup & Hlocal_not_formal)].
  - subst name. apply Hfresh. rewrite <- runtime_variables_are_names.
    apply elem_of_list_In. apply elem_of_list_lookup.
    exists formal_index. exact Hformal_lookup.
  - have Hindices : formal_index = local_index.
    { have Hnames := procedure_variable_names_unique _ Hwf.
      rewrite <- runtime_variables_are_names in Hnames.
      eapply NoDup_lookup;
        [apply NoDup_ListNoDup; exact Hnames | exact Hformal_lookup |].
      exact Hlocal_lookup. }
    apply Hlocal_not_formal. rewrite <- Hindices. exact Hformal_index.
Qed.

Definition runtime_unop {input output} (op : unop input output) :
    un_op :=
  match op with
  | UNot => NotBoolOp
  | UNeg => NegOp
  end.

Definition runtime_binop {left right output}
    (op : binop left right output) : bin_op :=
  match op with
  | BAdd => AddOp | BSub => SubOp
  | BMul => MulOp | BDiv => DivOp
  | BMod => ModOp | BLt => LtOp
  | BLe => LeOp | BGt => GtOp
  | BGe => GeOp | BEq _ => EqOp
  | BNe _ => NeOp | BAnd => AndOp
  | BOr => OrOp
  end.

Lemma tval_to_val_injective t : Inj (=) (=) (@tval_to_val t).
Proof.
  intros left right Heq.
  destruct t; dependent destruction left; dependent destruction right;
    simpl in Heq; inversion Heq; try reflexivity.
  apply (Eqdep_dec.inj_pair2_eq_dec string String.string_dec) in H0.
  subst. reflexivity.
Qed.

Lemma runtime_unop_sound {input output} (op : unop input output)
    (value : tval input) :
  LegacyLang.un_op_eval (runtime_unop op) (tval_to_val value) =
    Some (tval_to_val (interp_unop op value)).
Proof. destruct op; dependent destruction value; reflexivity. Qed.

Lemma runtime_eqb_sound t (left right : tval t) :
  bool_decide (tval_to_val left = tval_to_val right) =
    tval_eqb t left right.
Proof.
  destruct (bool_decide (tval_to_val left = tval_to_val right)) eqn:Hlegacy,
    (tval_eqb t left right) eqn:Htyped; try reflexivity.
  - apply bool_decide_eq_true in Hlegacy.
    apply tval_to_val_injective in Hlegacy. subst.
    assert (tval_eqb t right right = true) as Heq.
    { apply Core.tval_eqb_eq. reflexivity. }
    congruence.
  - apply Core.tval_eqb_eq in Htyped. subst.
    assert (bool_decide (tval_to_val right = tval_to_val right) = true) as Heq.
    { apply bool_decide_eq_true. reflexivity. }
    congruence.
Qed.

Lemma runtime_neqb_sound t (left right : tval t) :
  bool_decide (not (tval_to_val left = tval_to_val right)) =
    negb (tval_eqb t left right).
Proof.
  destruct (tval_eqb t left right) eqn:Htyped.
  - apply Core.tval_eqb_eq in Htyped. subst. simpl.
    apply bool_decide_eq_false. intros Hneq. apply Hneq. reflexivity.
  - simpl. apply bool_decide_eq_true. intros Heq.
    apply tval_to_val_injective in Heq. subst.
    assert (tval_eqb t right right = true) as Hrefl.
    { apply Core.tval_eqb_eq. reflexivity. }
    congruence.
Qed.

Lemma runtime_binop_sound {left right output}
    (op : binop left right output) (value1 : tval left)
    (value2 : tval right) (result : tval output) :
  interp_binop op value1 value2 = Some result ->
  LegacyLang.bin_op_eval (runtime_binop op)
    (tval_to_val value1) (tval_to_val value2) = Some (tval_to_val result).
Proof.
  destruct op.
  all: try solve [simpl; rewrite runtime_eqb_sound;
    intros Heq; inversion Heq; reflexivity].
  all: try solve [simpl; rewrite runtime_neqb_sound;
    intros Heq; inversion Heq; reflexivity].
  all: dependent destruction value1; dependent destruction value2;
    simpl; intros Heq; inversion Heq; subst; reflexivity.
Qed.

Fixpoint runtime_expr {Γ t} (names : named_context Γ)
    (expression : pexpr Γ t) : LegacyLang.expr :=
  match expression with
  | PEVar variable => LegacyLang.Var (runtime_variable names variable)
  | PEVal value => LegacyLang.Val (tval_to_val value)
  | PEUnOp op operand =>
      LegacyLang.UnOp (runtime_unop op) (runtime_expr names operand)
  | PEBinOp op operand1 operand2 =>
      LegacyLang.BinOp (runtime_binop op)
        (runtime_expr names operand1) (runtime_expr names operand2)
  end.

(** A legacy stack frame represents a symbolic typed store when each typed
    program variable is bound to the interpretation of its symbolic value.
    Keeping this relation extensional avoids dependent transports in the
    operational simulation proofs. *)
Definition stack_corresponds {Γ F Δ}
    (names : named_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (frame : LegacyLang.stack_frame) : Prop :=
  forall t (variable : pvar Γ t),
    frame.(LegacyLang.locals) !! runtime_variable names variable =
      Some (tval_to_val
        (interp_ref formals binders atoms (lookup_store store t variable))).

Lemma runtime_expr_sound {Γ F Δ t} (names : named_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (frame : LegacyLang.stack_frame)
    (expression : pexpr Γ t) (value : tval t) :
  stack_corresponds names formals binders atoms store frame ->
  interp_program_expr formals binders atoms store expression = Some value ->
  LegacyLang.expr_step (runtime_expr names expression) frame
    (LegacyLang.Val (tval_to_val value)).
Proof.
  intros Hstack. unfold interp_program_expr. induction expression; simpl.
  - intros Heq. inversion Heq. subst. apply LegacyLang.VarStep.
    apply Hstack.
  - intros Heq. inversion Heq. subst. apply LegacyLang.ExprRefl.
  - destruct (interp_expr formals binders atoms
        (Hoare.symbolize_expr store expression))
      as [operand_value|] eqn:Hoperand; simpl; [|discriminate].
    intros Heq. inversion Heq. subst. eapply LegacyLang.UnOpStep.
    + apply IHexpression. reflexivity.
    + apply runtime_unop_sound.
  - destruct (interp_expr formals binders atoms
        (Hoare.symbolize_expr store expression1))
      as [value1|] eqn:Hvalue1; simpl; [|discriminate].
    destruct (interp_expr formals binders atoms
        (Hoare.symbolize_expr store expression2))
      as [value2|] eqn:Hvalue2; simpl; [|discriminate].
    intros Heq. eapply LegacyLang.BinOpStep.
    + apply IHexpression1. reflexivity.
    + apply IHexpression2. reflexivity.
    + eapply runtime_binop_sound. exact Heq.
Qed.

Fixpoint runtime_expr_list {Γ ts} (names : named_context Γ)
    (expressions : pexpr_list Γ ts) : list LegacyLang.expr :=
  match expressions with
  | PENil => []
  | PECons expression expressions' =>
      runtime_expr names expression :: runtime_expr_list names expressions'
  end.

Lemma runtime_expr_list_length {Γ ts} (names : named_context Γ)
    (expressions : pexpr_list Γ ts) :
  length (runtime_expr_list names expressions) = length ts.
Proof. induction expressions; simpl; congruence. Qed.

Fixpoint runtime_field_initializers {Γ} (names : named_context Γ)
    (fields : list (field_init Γ)) :
    list (LegacyLang.fld_name * LegacyLang.expr) :=
  match fields with
  | [] => []
  | FieldInit field value :: fields' =>
      (Resources.field_name field, runtime_expr names value) ::
      runtime_field_initializers names fields'
  end.

Definition runtime_noop : LegacyLang.runtime_stmt :=
  LegacyLang.RTVal LegacyLang.LitUnit.

Definition combine_runtime_statements
    (first second : option LegacyLang.runtime_stmt) :
    option LegacyLang.runtime_stmt :=
  match first, second with
  | None, None => None
  | Some statement, None | None, Some statement => Some statement
  | Some first', Some second' => Some (LegacyLang.RTSeq first' second')
  end.

Fixpoint runtime_stmt {Γ} (names : named_context Γ)
    (stack : LegacyLang.stack_id) (statement : stmt Γ) :
    option LegacyLang.runtime_stmt :=
  match statement with
  | TSkip _ => None
  | TAssert _ _ => None
  | TAssign _ target value =>
      Some (LegacyLang.RTAssign (runtime_variable names target)
        (runtime_expr names value) stack)
  | TFieldRead _ field target base =>
      Some (LegacyLang.RTFldRd (runtime_variable names target)
        (runtime_expr names base) (Resources.field_name field) stack)
  | TFieldWrite _ field base value =>
      Some (LegacyLang.RTFldWr (runtime_expr names base)
        (Resources.field_name field) (runtime_expr names value) stack)
  | TAlloc _ target fields =>
      Some (LegacyLang.RTAlloc (runtime_variable names target)
        (runtime_field_initializers names fields) stack)
  | TGhostUpdate _ _ _ _ _ => None
  | TCall _ procedure arguments target =>
      match target with
      | CTStore target' =>
          Some (LegacyLang.RTCall (runtime_variable names target')
            (Resources.procedure_name procedure)
            (runtime_expr_list names arguments) stack)
      | CTDiscard =>
          Some (LegacyLang.RTCallNoStore
            (Resources.procedure_name procedure)
            (runtime_expr_list names arguments) stack)
      end
  | TSpawn _ procedure arguments =>
      Some (LegacyLang.RTSpawn (Resources.procedure_name procedure)
        (runtime_expr_list names arguments) stack)
  | TUnfold _ _ _ | TFold _ _ _
  | TPredicateUnfold _ _ _ | TPredicateFold _ _ _ => None
  | TIf _ condition then_branch else_branch =>
      match runtime_stmt names stack then_branch,
            runtime_stmt names stack else_branch with
      | None, None => None
      | then_runtime, else_runtime =>
          Some (LegacyLang.RTIfS (runtime_expr names condition)
            (default runtime_noop then_runtime)
            (default runtime_noop else_runtime) stack)
      end
  | TSeq _ first second =>
      combine_runtime_statements
        (runtime_stmt names stack first) (runtime_stmt names stack second)
  | TAtomic _ body => runtime_stmt names stack body
  end.

(** Proof-only statements may be distributed across a conditional without
    changing the generated runtime program.  The operational refinement uses
    this equality for an invariant unfold/fold pair: branch selection happens
    first, and only the selected arm enters the Iris invariant. *)
Lemma runtime_stmt_distribute_erased_around_if {Γ}
    (names : named_context Γ) stack
    unfold_node inner_node conditional_node
    (before after : stmt Γ) condition (then_branch else_branch : stmt Γ) :
  runtime_stmt names stack before = None ->
  runtime_stmt names stack after = None ->
  runtime_stmt names stack
    (TSeq unfold_node before
      (TSeq inner_node
        (TIf conditional_node condition then_branch else_branch) after)) =
  runtime_stmt names stack
    (TIf conditional_node condition
      (TSeq unfold_node before
        (TSeq inner_node then_branch after))
      (TSeq unfold_node before
        (TSeq inner_node else_branch after))).
Proof.
  intros Hbefore Hafter. simpl. rewrite Hbefore Hafter.
  destruct (runtime_stmt names stack then_branch),
    (runtime_stmt names stack else_branch); reflexivity.
Qed.

Corollary runtime_stmt_distribute_unfold_fold_if {Γ}
    (names : named_context Γ) stack
    unfold_node inner_node conditional_node fold_node
    invariant unfold_arguments fold_arguments condition
    (then_branch else_branch : stmt Γ) :
  runtime_stmt names stack
    (TSeq unfold_node (TUnfold unfold_node invariant unfold_arguments)
      (TSeq inner_node
        (TIf conditional_node condition then_branch else_branch)
        (TFold fold_node invariant fold_arguments))) =
  runtime_stmt names stack
    (TIf conditional_node condition
      (TSeq unfold_node (TUnfold unfold_node invariant unfold_arguments)
        (TSeq inner_node then_branch
          (TFold fold_node invariant fold_arguments)))
      (TSeq unfold_node (TUnfold unfold_node invariant unfold_arguments)
        (TSeq inner_node else_branch
          (TFold fold_node invariant fold_arguments)))).
Proof.
  apply runtime_stmt_distribute_erased_around_if; reflexivity.
Qed.

(** Soundness condition for the user-selected atomicity cost model at the
    concrete runtime boundary.  Proof-only leaves must not emit code; a leaf
    classified as one atomic step must translate to an Iris-atomic runtime
    statement.  Non-atomic leaves need no additional witness because the
    analysis already rejects them while an invariant is open.  Trusted
    [TAtomic] blocks are structural certificates rather than leaves and are
    handled by their separate module refinement assumption. *)
Definition runtime_cost_model_sound
    (cost : GenericRegions.Atomicity.cost_model) : Prop :=
  forall Γ (names : named_context Γ) stack (statement : stmt Γ) physical,
    RegionSyntax.view statement = TypedAnalysisView.ViewLeaf ->
    runtime_stmt names stack statement = Some physical ->
    match cost Γ statement with
    | GenericRegions.Atomicity.NoStep => False
    | GenericRegions.Atomicity.AtomicStep =>
        @Atomic LegacyLang.simp_lang WeaklyAtomic physical
    | GenericRegions.Atomicity.NonAtomicStep
    | GenericRegions.Atomicity.ProcedureCallStep _ _
    | GenericRegions.Atomicity.ProcedureSpawnStep _ => True
    end.

(** A typed declaration and a legacy procedure-table entry denote the same
    executable procedure when their frame layouts agree and translating the
    typed body yields the registered legacy body at every fresh stack id.
    The universal stack-id equation is the small-step execution boundary used
    by [wp_call], [wp_call_nostore], and [wp_spawn]. *)
Record runtime_procedure_registration {Γ F}
    (procedure : typed_procedure Γ F) (entry : LegacyLang.proc) : Prop := {
  registered_procedure_name :
    LegacyLang.proc_name_val entry =
      Resources.procedure_name (procedure_identity _ _ procedure);
  registered_procedure_arguments :
    LegacyLang.proc_args entry = runtime_procedure_arguments procedure;
  registered_procedure_locals :
    LegacyLang.proc_local_vars entry = runtime_procedure_locals procedure;
  registered_arguments_nodup :
    NoDup (LegacyLang.proc_args entry).*1;
  registered_locals_nodup :
    NoDup (LegacyLang.proc_local_vars entry).*1;
  registered_arguments_locals_disjoint :
    (LegacyLang.proc_args entry).*1 ## (LegacyLang.proc_local_vars entry).*1;
  registered_return_local :
    "#ret_val" ∈ (LegacyLang.proc_local_vars entry).*1;
  registered_procedure_body : forall stack,
    runtime_stmt (runtime_procedure_names procedure) stack
      (procedure_body _ _ procedure) =
    Some (LegacyLang.to_rtstmt stack (LegacyLang.proc_stmt entry));
}.

Definition packed_runtime_procedure_registration
    (procedure : packed_typed_procedure) (entry : LegacyLang.proc) : Prop :=
  match procedure with
  | existT Γ (existT F typed) =>
      @runtime_procedure_registration Γ F typed entry
  end.

Fixpoint tval_list_to_list {ts} (values : tval_list ts) :
    list LegacyLang.val :=
  match values with
  | TVNil => []
  | TVCons head tail => tval_to_val head :: tval_list_to_list tail
  end.

Lemma runtime_expr_list_sound {Γ F Δ ts} (names : named_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (frame : LegacyLang.stack_frame)
    (expressions : pexpr_list Γ ts) (values : tval_list ts) :
  stack_corresponds names formals binders atoms store frame ->
  interp_expr_list formals binders atoms
    (Hoare.symbolize_expr_list store expressions) = Some values ->
  Forall2 (fun expression value =>
    LegacyLang.expr_step expression frame (LegacyLang.Val value))
    (runtime_expr_list names expressions) (tval_list_to_list values).
Proof.
  intros Hstack. revert values.
  induction expressions; intros values Hvalues; dependent destruction values;
    simpl in Hvalues.
  - constructor.
  - destruct (interp_expr formals binders atoms
      (Hoare.symbolize_expr store p)) eqn:Hhead; [|discriminate].
    destruct (interp_expr_list formals binders atoms
      (Hoare.symbolize_expr_list store expressions)) eqn:Htail;
      [|discriminate].
    inversion Hvalues; subst. constructor.
    + eapply runtime_expr_sound; eauto.
    + eapply IHexpressions; eauto.
      dependent destruction H1. reflexivity.
Qed.

Definition tval_to_rich_val {t} (value : tval t) : Legacy.val :=
  match value with
  | VBool boolean => Legacy.LitBool boolean
  | VInt integer => Legacy.LitInt integer
  | VRef location => Legacy.LitLoc (LegacyLang.Loc location)
  | VUnit => Legacy.LitUnit
  | VRA resource => Legacy.LitRAElem
      (@existT string
        (fun name => ra_base.RA_carrier (LegacyRAs.ra_map name))
        _ resource)
  end.

Fixpoint tval_list_to_rich_list {ts} (values : tval_list ts) :
    list Legacy.val :=
  match values with
  | TVNil => []
  | TVCons head tail =>
      tval_to_rich_val head :: tval_list_to_rich_list tail
  end.

Lemma tval_to_rich_val_injective t :
  Inj (=) (=) (@tval_to_rich_val t).
Proof.
  intros left right Heq. destruct t; dependent destruction left;
    dependent destruction right; simpl in Heq; inversion Heq; try reflexivity.
  apply (Eqdep_dec.inj_pair2_eq_dec string String.string_dec) in H0.
  subst. reflexivity.
Qed.

Lemma tval_list_to_rich_list_injective ts :
  Inj (=) (=) (@tval_list_to_rich_list ts).
Proof.
  intros left. induction left as [|t ts head tail IH]; intros right Heq.
  - dependent destruction right. reflexivity.
  - dependent destruction right. simpl in Heq. injection Heq as Hhead Htail.
    apply tval_to_rich_val_injective in Hhead. subst.
    apply IH in Htail. subst. reflexivity.
Qed.

Fixpoint concrete_locals_by_store {Γ} (store : concrete_store Γ) :
    named_context Γ -> gmap LegacyLang.var LegacyLang.val.
Proof.
  destruct store as [|head_type tail_context value tail].
  - intros names. dependent destruction names. exact ∅.
  - intros names.
    dependent destruction names.
    exact (<[name := tval_to_val value]>
      (@concrete_locals_by_store tail_context tail names)).
Defined.

Definition concrete_locals {Γ} (names : named_context Γ)
    (store : concrete_store Γ) : gmap LegacyLang.var LegacyLang.val :=
  concrete_locals_by_store store names.

Lemma concrete_locals_interp_lookup {Γ F Δ} (names : named_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) :
  NoDup (runtime_variables names) ->
  forall t (variable : pvar Γ t),
    concrete_locals names (interp_store formals binders atoms store) !!
        runtime_variable names variable =
      Some (tval_to_val
        (interp_ref formals binders atoms (lookup_store store t variable))).
Proof.
  induction names; intros Hnames u variable.
  - dependent destruction variable.
  - dependent destruction store. dependent destruction variable.
    + unfold concrete_locals. cbn. unfold simplification_heq.
      rewrite (Eqdep_dec.UIP_dec
        (fun left right : context => decide (left = right))
        (@JMeq_eq context (t :: Γ) (t :: Γ) JMeq_refl) eq_refl).
      cbn. apply lookup_insert.
    + inversion Hnames as [|? ? Hfresh Htail].
      unfold concrete_locals. cbn. unfold simplification_heq.
      rewrite (Eqdep_dec.UIP_dec
        (fun left right : context => decide (left = right))
        (@JMeq_eq context (t :: Γ) (t :: Γ) JMeq_refl) eq_refl).
      cbn. rewrite lookup_insert_ne.
      * apply IHnames; assumption.
      * intros Heq. apply Hfresh. rewrite Heq.
        apply runtime_variable_member.
Qed.

Lemma concrete_procedure_return_lookup {Γ F Δ}
    (procedure : typed_procedure Γ F) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) :
  NoDup (runtime_variables (runtime_procedure_names procedure)) ->
  concrete_locals (runtime_procedure_names procedure)
      (interp_store formals binders atoms store) !! "#ret_val" =
    Some (tval_to_val (interp_ref formals binders atoms
      (lookup_store store _ (procedure_return_variable _ _ procedure)))).
Proof.
  intros Hnames. rewrite <- (runtime_procedure_return_name procedure).
  apply concrete_locals_interp_lookup. exact Hnames.
Qed.

Lemma runtime_name_has_variable {Γ} (names : named_context Γ) name :
  List.In name (runtime_variables names) ->
  exists t (variable : pvar Γ t), runtime_variable names variable = name.
Proof.
  induction names as [|Γ head t names IH]; simpl.
  - tauto.
  - intros [<- | Hin].
    + exists t, MHere. reflexivity.
    + destruct (IH Hin) as (u & variable & Hvariable).
      exists u, (MThere variable). exact Hvariable.
Qed.

Lemma concrete_locals_lookup_none {Γ} (names : named_context Γ)
    (store : concrete_store Γ) name :
  ~ List.In name (runtime_variables names) ->
  concrete_locals names store !! name = None.
Proof.
  induction names as [|Γ head t names IH]; intros Hfresh.
  - dependent destruction store. apply lookup_empty.
  - dependent destruction store. unfold concrete_locals. cbn.
    unfold simplification_heq.
    rewrite (Eqdep_dec.UIP_dec
      (fun left right : context => decide (left = right))
      (@JMeq_eq context (t :: Γ) (t :: Γ) JMeq_refl) eq_refl).
    cbn. rewrite lookup_insert_ne.
    + apply IH. intros Hin. apply Hfresh. now right.
    + intros Heq. apply Hfresh. left. exact Heq.
Qed.

Lemma stack_corresponds_canonical_frame_eq {Γ F Δ}
    (names : named_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (frame : LegacyLang.stack_frame) :
  NoDup (runtime_variables names) ->
  stack_corresponds names formals binders atoms store frame ->
  dom frame.(LegacyLang.locals) = list_to_set (runtime_variables names) ->
  frame = LegacyLang.StackFrame
    (concrete_locals names (interp_store formals binders atoms store)).
Proof.
  intros Hnames Hcorresponds Hdom. destruct frame as [locals]. simpl in *.
  f_equal. apply map_eq. intros name.
  destruct (in_dec String.string_dec name (runtime_variables names))
    as [Hin | Hnot].
  - destruct (runtime_name_has_variable names name Hin)
      as (t & variable & Hvariable).
    rewrite <- Hvariable.
    rewrite Hcorresponds.
    symmetry. apply concrete_locals_interp_lookup. exact Hnames.
  - have Hleft : locals !! name = None.
    { apply not_elem_of_dom. rewrite Hdom.
      rewrite elem_of_list_to_set. intros Hin.
      apply elem_of_list_In in Hin. exact (Hnot Hin). }
    rewrite Hleft. symmetry.
    apply concrete_locals_lookup_none. exact Hnot.
Qed.

Lemma concrete_locals_update_store {Γ F Δ t} (names : named_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (target : pvar Γ t)
    (value : tval t) :
  NoDup (runtime_variables names) ->
  concrete_locals names
      (interp_store formals (binder_cons value binders) atoms
        (Hoare.update_store_with_bound store target)) =
    <[runtime_variable names target := tval_to_val value]>
      (concrete_locals names (interp_store formals binders atoms store)).
Proof.
  induction names; intros Hnames.
  - dependent destruction target.
  - dependent destruction store. dependent destruction target.
    + unfold concrete_locals. cbn. unfold simplification_heq.
      rewrite (Eqdep_dec.UIP_dec
        (fun left right : context => decide (left = right))
        (@JMeq_eq context (t0 :: Γ) (t0 :: Γ) JMeq_refl) eq_refl).
      cbn. unfold simplification_heq.
      rewrite (Eqdep_dec.UIP_dec
        (fun left right : context => decide (left = right))
        (@JMeq_eq context (t0 :: Γ) (t0 :: Γ) JMeq_refl) eq_refl).
      cbn. rewrite interp_weaken_store.
      unfold binder_cons. rewrite view_member_here. rewrite insert_insert.
      reflexivity.
    + inversion Hnames as [|? ? Hfresh Htail].
      unfold concrete_locals. cbn. unfold simplification_heq.
      rewrite (Eqdep_dec.UIP_dec
        (fun left right : context => decide (left = right))
        (@JMeq_eq context (t0 :: Γ) (t0 :: Γ) JMeq_refl) eq_refl).
      cbn. unfold simplification_heq.
      rewrite (Eqdep_dec.UIP_dec
        (fun left right : context => decide (left = right))
        (@JMeq_eq context (t0 :: Γ) (t0 :: Γ) JMeq_refl) eq_refl).
      cbn. rewrite interp_weaken_ref. unfold concrete_locals in IHnames.
      rewrite IHnames; [|exact Htail].
      apply insert_commute. intros Heq. apply Hfresh. rewrite Heq.
      apply runtime_variable_member.
Qed.

Lemma concrete_stack_corresponds {Γ F Δ} (names : named_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) :
  NoDup (runtime_variables names) ->
  stack_corresponds names formals binders atoms store
    (LegacyLang.StackFrame
      (concrete_locals names (interp_store formals binders atoms store))).
Proof.
  intros Hnames t variable.
  apply concrete_locals_interp_lookup. exact Hnames.
Qed.

Record stack_context_data (Γ : context) := StackContext {
  runtime_stack_id : LegacyLang.stack_id;
  runtime_names : named_context Γ;
  runtime_names_nodup : NoDup (runtime_variables runtime_names);
}.

Definition stack_context : context -> Type := stack_context_data.

Definition empty_stack_context : stack_context [].
Proof. refine (StackContext [] 0%Z NCNil _). constructor. Defined.

Definition stack_own Γ (runtime : stack_context Γ)
    (store : concrete_store Γ) : bi_car PROP :=
  LegacyGhost.stack_frame_own (runtime_stack_id _ runtime)
    (LegacyLang.StackFrame (concrete_locals (runtime_names _ runtime) store)).

Lemma runtime_stack_frame_corresponds {Γ F Δ}
    (runtime : stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) :
  stack_corresponds (runtime_names _ runtime) formals binders atoms store
    (LegacyLang.StackFrame
      (concrete_locals (runtime_names _ runtime)
        (interp_store formals binders atoms store))).
Proof.
  intros t variable. apply concrete_locals_interp_lookup.
  apply runtime_names_nodup.
Qed.

Definition field_own field
    (location : tval TRef) (chunk : tval (Logic.field_type field)) :
    bi_car PROP :=
  match location with
  | VRef address =>
      LegacyGhost.heap_maps_to (LegacyLang.Loc address)
        (Resources.field_name field) 1 (tval_to_val chunk)
  end.

Definition invariant_own invariant
    (values : tval_list (Logic.invariant_args invariant)) : bi_car PROP :=
  @own Resources.Σ (authR Legacy.inv_argsUR) concrete_invtoken_inG
    (Legacy.invtoken_names (Resources.invariant_name invariant))
    (◯ ({[tval_list_to_rich_list values]} : gset (list Legacy.val))).

Definition runtime_wp (mask : coPset) (statement : LegacyLang.runtime_stmt)
    (post : LegacyLang.val -> iProp Resources.Σ) : iProp Resources.Σ :=
  @wp _ _ _ _
    (@weakestpre.wp' HasLc LegacyLang.simp_lang Resources.Σ concrete_irisG)
    NotStuck mask statement post.

Definition invariant_mask (mask : Hoare.mask) : coPset :=
  set_fold (fun invariant result =>
    result ∪ ↑(Resources.invariant_namespace invariant)) ∅ mask.

Definition runtime_mask (mask : Hoare.mask) : coPset :=
  invariant_mask mask ∪ ↑Resources.ghost_heap_namespace.

(** The physical Iris mask at a certificate state.  Raven masks record
    logical permissions; only invariants recorded as open are disabled in
    the fixed ambient envelope. *)
Definition enabled_runtime_mask (ambient : coPset) (open : gset inv_id) : coPset :=
  ambient ∖ invariant_mask open.

Definition active_runtime_mask (ambient : coPset)
    (state : GenericRegions.Atomicity.analysis_state) : coPset :=
  enabled_runtime_mask ambient (GenericRegions.Atomicity.analysis_open state).

Lemma invariant_mask_empty : invariant_mask (∅ : Hoare.mask) = ∅.
Proof. apply set_fold_empty. Qed.

Lemma invariant_mask_union_singleton invariant (mask : Hoare.mask) :
  invariant_mask ({[invariant]} ∪ mask) =
    ↑(Resources.invariant_namespace invariant) ∪ invariant_mask mask.
Proof.
  unfold invariant_mask.
  rewrite (set_fold_union_strong (=)
    (fun invariant result =>
      result ∪ ↑(Resources.invariant_namespace invariant)) ∅
    ({[invariant]} : Hoare.mask) mask).
  - rewrite set_fold_singleton.
    replace (∅ ∪ ↑Resources.invariant_namespace invariant) with
      ((fun result : coPset =>
          ↑Resources.invariant_namespace invariant ∪ result) ∅)
      by set_solver.
    rewrite (set_fold_comm_acc
      (fun invariant' result =>
        result ∪ ↑(Resources.invariant_namespace invariant'))
      (fun result => ↑Resources.invariant_namespace invariant ∪ result)
      ∅ mask); last (intros; set_solver).
    reflexivity.
  - intros invariant' result _. set_solver.
  - intros left right result _ _ _. set_solver.
Qed.

Lemma active_runtime_mask_open ambient invariant outer state :
  GenericRegions.Atomicity.analysis_open state = {[invariant]} ∪ outer ->
  active_runtime_mask ambient state =
    active_runtime_mask ambient
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask state) outer
        (GenericRegions.Atomicity.analysis_step_taken state)
        (GenericRegions.Atomicity.analysis_in_atomic state)) ∖
      ↑(Resources.invariant_namespace invariant).
Proof.
  intros Hopen. unfold active_runtime_mask, enabled_runtime_mask. simpl. rewrite Hopen.
  rewrite invariant_mask_union_singleton. set_solver.
Qed.

Lemma active_runtime_mask_same_open ambient left right :
  GenericRegions.Atomicity.analysis_open left =
    GenericRegions.Atomicity.analysis_open right ->
  active_runtime_mask ambient left = active_runtime_mask ambient right.
Proof. intros Hopen. unfold active_runtime_mask. now rewrite Hopen. Qed.

Lemma active_runtime_mask_closed ambient state :
  GenericRegions.Atomicity.analysis_open state = ∅ ->
  active_runtime_mask ambient state = ambient.
Proof.
  intros Hclosed. unfold active_runtime_mask, enabled_runtime_mask.
  rewrite Hclosed invariant_mask_empty. set_solver.
Qed.

Lemma invariant_mask_disjoint invariant (mask : Hoare.mask) :
  invariant ∉ mask ->
  (↑(Resources.invariant_namespace invariant) : coPset) ##
    invariant_mask mask.
Proof.
  induction mask using set_ind_L.
  - rewrite invariant_mask_empty. set_solver.
  - intros Hnotin. rewrite invariant_mask_union_singleton.
    have Hneq : invariant ≠ x by set_solver.
    have Hleft : (↑Resources.invariant_namespace invariant : coPset) ##
        ↑Resources.invariant_namespace x :=
      Resources.invariant_namespaces_disjoint invariant x Hneq.
    have Hright := IHmask ltac:(set_solver).
    exact (proj2 (disjoint_union_r _ _ _) (conj Hleft Hright)).
Qed.

Lemma invariant_namespace_subset_runtime_mask invariant (mask : Hoare.mask) :
  invariant ∈ mask ->
  ↑(Resources.invariant_namespace invariant) ⊆ runtime_mask mask.
Proof.
  intros Hmember.
  have Hmask : mask = {[invariant]} ∪ (mask ∖ {[invariant]}).
  { apply set_eq. intros other. rewrite elem_of_union elem_of_singleton
      elem_of_difference elem_of_singleton. split.
    - intros Hother. destruct (decide (other = invariant)) as [->|Hneq].
      + left. reflexivity.
      + right. split; assumption.
    - intros [->|[Hother _]]; assumption. }
  rewrite Hmask. unfold runtime_mask. rewrite invariant_mask_union_singleton.
  set_solver.
Qed.

Lemma invariant_masks_disjoint (left right : Hoare.mask) :
  left ## right -> invariant_mask left ## invariant_mask right.
Proof.
  revert right. induction left using set_ind_L; intros right Hdisjoint.
  - rewrite invariant_mask_empty. apply disjoint_empty_l.
  - rewrite invariant_mask_union_singleton.
    apply disjoint_union_l. split.
    + apply invariant_mask_disjoint. set_solver.
    + apply IHleft. set_solver.
Qed.

Lemma ghost_namespace_disjoint_invariant_mask (mask : Hoare.mask) :
  (↑Resources.ghost_heap_namespace : coPset) ## invariant_mask mask.
Proof.
  induction mask using set_ind_L.
  - rewrite invariant_mask_empty. apply disjoint_empty_r.
  - rewrite invariant_mask_union_singleton. apply disjoint_union_r. split.
    + symmetry. apply Resources.invariant_ghost_namespace_disjoint.
    + exact IHmask.
Qed.

Lemma runtime_mask_subset_active ambient (state :
    GenericRegions.Atomicity.analysis_state) :
  GenericRegions.Atomicity.state_wf state ->
  runtime_mask (GenericRegions.Atomicity.analysis_mask state) ⊆ ambient ->
  runtime_mask (GenericRegions.Atomicity.analysis_mask state) ⊆
    active_runtime_mask ambient state.
Proof.
  intros Hwf Henvelope.
  have Hinvariants : invariant_mask
      (GenericRegions.Atomicity.analysis_mask state) ##
      invariant_mask (GenericRegions.Atomicity.analysis_open state).
  { apply invariant_masks_disjoint. symmetry. exact Hwf. }
  have Hghost : (↑Resources.ghost_heap_namespace : coPset) ##
      invariant_mask (GenericRegions.Atomicity.analysis_open state).
  { apply ghost_namespace_disjoint_invariant_mask. }
  unfold runtime_mask in Henvelope |-*.
  unfold active_runtime_mask, enabled_runtime_mask.
  set_solver.
Qed.

Lemma runtime_mask_delete invariant (mask : Hoare.mask) :
  invariant ∈ mask ->
  runtime_mask (mask ∖ {[invariant]}) =
    runtime_mask mask ∖
      ↑(Resources.invariant_namespace invariant).
Proof.
  intros Hin. unfold runtime_mask.
  have Hmask : mask = {[invariant]} ∪ (mask ∖ {[invariant]}).
  { apply set_eq. intros other.
    rewrite elem_of_union elem_of_singleton elem_of_difference
      elem_of_singleton. split.
    - intros Hother. destruct (decide (other = invariant)); [left|right]; done.
    - intros [->|[Hother _]]; assumption. }
  have Hfold : invariant_mask mask =
      ↑(Resources.invariant_namespace invariant) ∪
        invariant_mask (mask ∖ {[invariant]}).
  { exact (eq_trans (f_equal invariant_mask Hmask)
      (invariant_mask_union_singleton invariant
        (mask ∖ {[invariant]}))). }
  rewrite Hfold.
  have Hinv := invariant_mask_disjoint invariant (mask ∖ {[invariant]})
    ltac:(set_solver).
  have Hghost := Resources.invariant_ghost_namespace_disjoint invariant.
  rewrite !difference_union_distr_l_L difference_diag_L.
  rewrite (difference_disjoint_L (invariant_mask (mask ∖ {[invariant]}))
    (↑(Resources.invariant_namespace invariant) : coPset)); last by symmetry.
  rewrite (difference_disjoint_L
    (↑Resources.ghost_heap_namespace : coPset)
    (↑(Resources.invariant_namespace invariant) : coPset));
    last by symmetry.
  rewrite (left_id_L _ _). reflexivity.
Qed.

Lemma runtime_mask_insert invariant (mask : Hoare.mask) :
  runtime_mask (mask ∪ {[invariant]}) =
    runtime_mask mask ∪
      ↑(Resources.invariant_namespace invariant).
Proof.
  unfold runtime_mask.
  have Hcomm : mask ∪ {[invariant]} = {[invariant]} ∪ mask.
  { apply set_eq. intros other. rewrite !elem_of_union !elem_of_singleton.
    tauto. }
  have Hfold : invariant_mask (mask ∪ {[invariant]}) =
      ↑(Resources.invariant_namespace invariant) ∪ invariant_mask mask.
  { exact (eq_trans (f_equal invariant_mask Hcomm)
      (invariant_mask_union_singleton invariant mask)). }
  rewrite Hfold. apply set_eq. intros name. rewrite !elem_of_union. tauto.
Qed.

Lemma invariant_namespace_disjoint_runtime_mask invariant (mask : Hoare.mask) :
  invariant ∉ mask ->
  (↑(Resources.invariant_namespace invariant) : coPset) ## runtime_mask mask.
Proof.
  intros Hnotin. unfold runtime_mask.
  apply disjoint_union_r. split.
  - apply invariant_mask_disjoint. exact Hnotin.
  - apply Resources.invariant_ghost_namespace_disjoint.
Qed.

Lemma runtime_mask_mono (left right : Hoare.mask) :
  left ⊆ right -> runtime_mask left ⊆ runtime_mask right.
Proof.
  revert right. induction left using set_ind_L; intros right Hsubset.
  - unfold runtime_mask. rewrite invariant_mask_empty. set_solver.
  - have Hx : x ∈ right by set_solver.
    have Hrest : X ⊆ right by set_solver.
    have IH := IHleft right Hrest.
    have Hnamespace := invariant_namespace_subset_runtime_mask x right Hx.
    rewrite (union_comm_L ({[x]} : Hoare.mask) X).
    rewrite runtime_mask_insert. set_solver.
Qed.

Lemma runtime_assignment_wp {Γ F Δ t} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (target : pvar Γ t)
    (expression : pexpr Γ t) (mask : coPset) :
  stack_own Γ runtime (interp_store formals binders atoms store) ⊢
  runtime_wp mask
    (LegacyLang.RTAssign
      (runtime_variable (runtime_names _ runtime) target)
      (runtime_expr (runtime_names _ runtime) expression)
      (runtime_stack_id _ runtime))
    (fun result =>
      (⌜result = LegacyLang.LitUnit⌝ ∗
       ∃ value,
         ⌜interp_program_expr formals binders atoms store expression =
           Some value⌝ ∗
         stack_own Γ runtime
           (interp_store formals (binder_cons value binders) atoms
             (Hoare.update_store_with_bound store target)))%I).
Proof.
  iIntros "Hstack". unfold runtime_wp.
  iEval (unfold stack_own) in "Hstack".
  destruct (interp_expr_total formals binders atoms
    (Hoare.symbolize_expr store expression)) as [value Hvalue].
  iApply (LegacyLifting.wp_assign
    (runtime_stack_id _ runtime)
    (LegacyLang.StackFrame
      (concrete_locals (runtime_names _ runtime)
        (interp_store formals binders atoms store)))
    (runtime_variable (runtime_names _ runtime) target)
    (tval_to_val value) (runtime_expr (runtime_names _ runtime) expression)
    mask with "[Hstack]").
  { iSplitL "Hstack"; first iExact "Hstack". iPureIntro.
    eapply runtime_expr_sound.
    - apply runtime_stack_frame_corresponds.
    - exact Hvalue. }
  iNext. iIntros "[Hstack Hcredit]". iSplit; first done. iExists value.
  iSplit; first done.
  unfold stack_own. simpl. rewrite concrete_locals_update_store.
  iExact "Hstack". apply runtime_names_nodup.
Qed.

Lemma runtime_field_write_wp {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) field (base : pexpr Γ TRef)
    (expression : pexpr Γ (Logic.field_type field))
    (location : tval TRef) (old_value : tval (Logic.field_type field))
    (mask : coPset) :
  interp_program_expr formals binders atoms store base = Some location ->
  stack_own Γ runtime (interp_store formals binders atoms store) ∗
    field_own field location old_value ⊢
  runtime_wp mask
    (LegacyLang.RTFldWr (runtime_expr (runtime_names _ runtime) base)
      (Resources.field_name field)
      (runtime_expr (runtime_names _ runtime) expression)
      (runtime_stack_id _ runtime))
    (fun result =>
      (⌜result = LegacyLang.LitUnit⌝ ∗
       ∃ new_value,
         ⌜interp_program_expr formals binders atoms store expression =
           Some new_value⌝ ∗
         stack_own Γ runtime (interp_store formals binders atoms store) ∗
         field_own field location new_value)%I).
Proof.
  intros Hlocation. iIntros "[Hstack Hfield]". unfold runtime_wp.
  iEval (unfold stack_own) in "Hstack".
  destruct (interp_program_expr formals binders atoms store expression)
    as [new_value|] eqn:Hvalue.
  2: exfalso; destruct (interp_expr_total formals binders atoms
        (Hoare.symbolize_expr store expression)) as [new_value Htotal];
      unfold interp_program_expr in Hvalue; congruence.
  dependent destruction location. iEval (unfold field_own) in "Hfield".
  iApply (LegacyLifting.wp_heap_wr_expr
    (runtime_stack_id _ runtime)
    (LegacyLang.StackFrame
      (concrete_locals (runtime_names _ runtime)
        (interp_store formals binders atoms store)))
    (runtime_expr (runtime_names _ runtime) base)
    (runtime_expr (runtime_names _ runtime) expression)
    (tval_to_val new_value) (LegacyLang.Loc location)
    (Resources.field_name field) (tval_to_val old_value) mask
    with "[Hstack Hfield]").
  { iFrame. iPureIntro. split.
    - exact (runtime_expr_sound (runtime_names _ runtime) formals binders atoms
        store _ base (VRef location)
        (runtime_stack_frame_corresponds runtime formals binders atoms store)
        Hlocation).
    - exact (runtime_expr_sound (runtime_names _ runtime) formals binders atoms
        store _ expression new_value
        (runtime_stack_frame_corresponds runtime formals binders atoms store)
        Hvalue). }
  iNext. iIntros "[Hstack [Hfield Hcredit]]". iSplit; first done.
  iExists new_value. iSplit; first done.
  unfold stack_own, field_own. simpl. iFrame.
Qed.

Lemma runtime_field_read_wp {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) field
    (target : pvar Γ (Logic.field_type field)) (base : pexpr Γ TRef)
    (location : tval TRef) (chunk : tval (Logic.field_type field))
    (mask : coPset) :
  interp_program_expr formals binders atoms store base = Some location ->
  stack_own Γ runtime (interp_store formals binders atoms store) ∗
    field_own field location chunk ⊢
  runtime_wp mask
    (LegacyLang.RTFldRd
      (runtime_variable (runtime_names _ runtime) target)
      (runtime_expr (runtime_names _ runtime) base)
      (Resources.field_name field) (runtime_stack_id _ runtime))
    (fun result =>
      (⌜result = LegacyLang.LitUnit⌝ ∗
       ∃ value,
         ⌜value = chunk⌝ ∗
         stack_own Γ runtime
           (interp_store formals (binder_cons value binders) atoms
             (Hoare.update_store_with_bound store target)) ∗
         field_own field location chunk)%I).
Proof.
  intros Hlocation. iIntros "[Hstack Hfield]". unfold runtime_wp.
  iEval (unfold stack_own) in "Hstack".
  dependent destruction location. iEval (unfold field_own) in "Hfield".
  iApply (LegacyLifting.wp_heap_rd
    (runtime_stack_id _ runtime)
    (LegacyLang.StackFrame
      (concrete_locals (runtime_names _ runtime)
        (interp_store formals binders atoms store)))
    (Resources.field_name field)
    (runtime_expr (runtime_names _ runtime) base)
    (tval_to_val chunk) (LegacyLang.Loc location)
    (runtime_variable (runtime_names _ runtime) target) mask 1%Qp
    with "[Hstack Hfield]").
  { iFrame. iPureIntro.
    exact (runtime_expr_sound (runtime_names _ runtime) formals binders atoms
      store _ base (VRef location)
      (runtime_stack_frame_corresponds runtime formals binders atoms store)
      Hlocation). }
  iNext. iIntros "[Hstack [Hfield Hcredit]]". iSplit; first done.
  iExists chunk. iSplit; first done. unfold stack_own, field_own. simpl.
  rewrite concrete_locals_update_store.
  iFrame. apply runtime_names_nodup.
Qed.

Fixpoint allocated_fields_own {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (location : tval TRef)
    (fields : list (field_init Γ)) : iProp Resources.Σ :=
  match fields with
  | [] => True%I
  | FieldInit field expression :: fields' =>
      (∃ value,
        ⌜interp_program_expr formals binders atoms store expression =
          Some value⌝ ∗
        field_own field location value ∗
        allocated_fields_own runtime formals binders atoms store location
          fields')%I
  end.

Inductive field_values_match {Γ F Δ}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) :
    list (field_init Γ) -> list (LegacyLang.fld_name * LegacyLang.val) -> Prop :=
| FieldValuesNil : field_values_match formals binders atoms store [] []
| FieldValuesCons field expression fields value values :
    interp_program_expr formals binders atoms store expression = Some value ->
    field_values_match formals binders atoms store fields values ->
    field_values_match formals binders atoms store
      (FieldInit field expression :: fields)
      ((Resources.field_name field, tval_to_val value) :: values).

Lemma field_values_match_exists {Γ F Δ} (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
  exists values, field_values_match formals binders atoms store fields values.
Proof.
  induction fields as [|[field expression] fields IH].
  - exists []. constructor.
  - destruct IH as [values Hvalues].
    destruct (interp_expr_total formals binders atoms
      (Hoare.symbolize_expr store expression)) as [value Hvalue].
    exists ((Resources.field_name field, tval_to_val value) :: values).
    constructor; [exact Hvalue|exact Hvalues].
Qed.

Lemma field_values_match_steps {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) fields values :
  field_values_match formals binders atoms store fields values ->
  Forall2 (fun initializer field_value =>
    fst initializer = fst field_value /\
    LegacyLang.expr_step (snd initializer)
      (LegacyLang.StackFrame
        (concrete_locals (runtime_names _ runtime)
          (interp_store formals binders atoms store)))
      (LegacyLang.Val (snd field_value)))
    (runtime_field_initializers (runtime_names _ runtime) fields) values.
Proof.
  intros Hmatch. induction Hmatch; simpl; constructor; [|exact IHHmatch].
  split; first reflexivity.
  exact (runtime_expr_sound (runtime_names _ runtime) formals binders atoms
    store _ expression value
    (runtime_stack_frame_corresponds runtime formals binders atoms store) H).
Qed.

Lemma field_values_match_names {Γ F Δ} formals binders atoms
    (store : symbolic_store Γ F Δ) fields values :
  field_values_match formals binders atoms store fields values ->
  values.*1 = map (fun initialization =>
    Resources.field_name (field_init_id initialization)) fields.
Proof.
  intros Hmatch. induction Hmatch; simpl.
  - reflexivity.
  - f_equal. exact IHHmatch.
Qed.

Lemma runtime_field_names_nodup {Γ} (fields : list (field_init Γ)) :
  NoDup (map field_init_id fields) ->
  NoDup (map (fun initialization =>
    Resources.field_name (field_init_id initialization)) fields).
Proof.
  induction fields as [|initialization fields IH]; simpl; intros Hnodup.
  - constructor.
  - inversion Hnodup as [|? ? Hfresh Htail]. constructor.
    + intros Hmember. apply elem_of_list_fmap in Hmember.
      destruct Hmember as [other [Heq Hother]].
      apply Resources.field_name_injective in Heq. apply Hfresh.
      apply elem_of_list_fmap. exists other. split; assumption.
    + apply IH. exact Htail.
Qed.

Lemma field_values_match_own {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) fields values address :
  field_values_match formals binders atoms store fields values ->
  LegacyLifting.field_list_to_iprop (LegacyLang.Loc address) values ⊢
    allocated_fields_own runtime formals binders atoms store (VRef address)
      fields.
Proof.
  intros Hmatch. induction Hmatch; simpl.
  - iIntros "_". done.
  - iIntros "[Hfield Hfields]". iExists value. iSplit; first done.
    unfold field_own. iFrame. iApply IHHmatch. iExact "Hfields".
Qed.

Lemma runtime_allocation_wp {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (target : pvar Γ TRef)
    (fields : list (field_init Γ)) (mask : coPset) :
  NoDup (map field_init_id fields) ->
  stack_own Γ runtime (interp_store formals binders atoms store) ⊢
  runtime_wp mask
    (LegacyLang.RTAlloc (runtime_variable (runtime_names _ runtime) target)
      (runtime_field_initializers (runtime_names _ runtime) fields)
      (runtime_stack_id _ runtime))
    (fun result =>
      (⌜result = LegacyLang.LitUnit⌝ ∗
       ∃ address : Z,
         stack_own Γ runtime
           (interp_store formals (binder_cons (VRef address) binders) atoms
             (Hoare.update_store_with_bound store target)) ∗
         allocated_fields_own runtime formals binders atoms store
           (VRef address) fields)%I).
Proof.
  intros Hfields. iIntros "Hstack". unfold runtime_wp.
  iEval (unfold stack_own) in "Hstack".
  destruct (field_values_match_exists formals binders atoms store fields)
    as [values Hvalues].
  iApply (LegacyLifting.wp_alloc_expr
    (runtime_stack_id _ runtime)
    (LegacyLang.StackFrame
      (concrete_locals (runtime_names _ runtime)
        (interp_store formals binders atoms store)))
    (runtime_field_initializers (runtime_names _ runtime) fields)
    values [] (runtime_variable (runtime_names _ runtime) target) mask
    with "Hstack").
  - exact (field_values_match_steps runtime formals binders atoms store
      fields values Hvalues).
  - rewrite (field_values_match_names formals binders atoms store fields
      values Hvalues). apply runtime_field_names_nodup. exact Hfields.
  - constructor.
  - intros Hnil. contradiction.
  - iNext. iIntros "Hpost".
    iDestruct "Hpost" as (location) "[Hstack [Hfields [Hghost Hcredit]]]".
    destruct location as [address]. iSplit; first done. iExists address.
    iSplitL "Hstack".
    + unfold stack_own. simpl. rewrite concrete_locals_update_store.
      iExact "Hstack". apply runtime_names_nodup.
    + iApply (field_values_match_own runtime formals binders atoms store
        fields values address Hvalues). iExact "Hfields".
Qed.

Global Instance stack_own_timeless Γ runtime store :
  Timeless (stack_own Γ runtime store).
Proof. destruct runtime. unfold stack_own. simpl. apply _. Qed.

Global Instance field_own_timeless field location chunk :
  Timeless (field_own field location chunk).
Proof. dependent destruction location. unfold field_own. apply _. Qed.

Global Instance invariant_own_persistent invariant values :
  Persistent (invariant_own invariant values).
Proof. unfold invariant_own. apply _. Qed.

Global Instance invariant_own_timeless invariant values :
  Timeless (invariant_own invariant values).
Proof. unfold invariant_own. apply _. Qed.

End ConcreteModel.

(** High-level operation contracts consumed by the generic Hoare-validity
    induction.  They expose interpreted typed assertions, while the concrete
    ghost state and legacy lifting lemmas remain encapsulated in
    [ConcreteModel]. *)
Module ConcreteValidity (Resources : RUNTIME_RESOURCES).
Module Model := ConcreteModel Resources.
Module S := Translation.Semantics Model.
Module Assertions := Translation.Assertions.
Import Assertions S.

Lemma assignment_rule_wp (predicates : predicate_semantics) {Γ F Δ t}
    (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (target : pvar Γ t)
    (expression : pexpr Γ t) (mask : Hoare.mask) :
  interp_assertion predicates runtime formals binders atoms (AStack store) ⊢
  Model.runtime_wp (Model.runtime_mask mask)
    (LegacyLang.RTAssign
      (Model.runtime_variable (Model.runtime_names _ runtime) target)
      (Model.runtime_expr (Model.runtime_names _ runtime) expression)
      (Model.runtime_stack_id _ runtime))
    (fun result =>
      (⌜result = LegacyLang.LitUnit⌝ ∗
       interp_assertion predicates runtime formals binders atoms
         (AExists t
           (AAnd (AStack (Hoare.update_store_with_bound store target))
             (AExpr (EBinOp (BEq t) (ERef (RefBound MHere))
               (weaken_expr (Hoare.symbolize_expr store expression)))))))%I).
Proof.
  iIntros "Hstack".
  iPoseProof (Model.runtime_assignment_wp runtime formals binders atoms store
    target expression (Model.runtime_mask mask) with "Hstack") as "Hwp".
  iEval (unfold Model.runtime_wp) in "Hwp". unfold Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]".
  iSplit; first done. iDestruct "Hpost" as (value) "[%Hvalue Hstack]".
  iExists value. iFrame. iPureIntro. simpl.
  rewrite interp_weaken_expr. unfold interp_program_expr in Hvalue.
  rewrite Hvalue. simpl. unfold binder_cons. rewrite view_member_here.
  rewrite (proj2 (tval_eqb_eq t value value) eq_refl). reflexivity.
Qed.

Lemma field_write_rule_wp (predicates : predicate_semantics) {Γ F Δ}
    (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) field (base : pexpr Γ TRef)
    (expression : pexpr Γ (Logic.field_type field)) old_chunk
    (mask : Hoare.mask) :
  interp_assertion predicates runtime formals binders atoms
    (AAnd (AStack store)
      (AOwn field (Hoare.symbolize_expr store base) old_chunk)) ⊢
  Model.runtime_wp (Model.runtime_mask mask)
    (LegacyLang.RTFldWr
      (Model.runtime_expr (Model.runtime_names _ runtime) base)
      (Resources.field_name field)
      (Model.runtime_expr (Model.runtime_names _ runtime) expression)
      (Model.runtime_stack_id _ runtime))
    (fun result =>
      (⌜result = LegacyLang.LitUnit⌝ ∗
       interp_assertion predicates runtime formals binders atoms
         (AAnd (AStack store)
           (AOwn field (Hoare.symbolize_expr store base)
             (Hoare.symbolize_expr store expression))))%I).
Proof.
  iIntros "[Hstack Hown]".
  iDestruct "Hown" as (location old_value) "(%Hlocation & %Hold & Hown)".
  iPoseProof (Model.runtime_field_write_wp runtime formals binders atoms store
    field base expression location old_value (Model.runtime_mask mask) Hlocation
    with "[$Hstack $Hown]") as "Hwp".
  iEval (unfold Model.runtime_wp) in "Hwp". unfold Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iDestruct "Hpost" as (new_value) "(%Hvalue & Hstack & Hown)".
  iFrame "Hstack". iExists location, new_value.
  iSplit; first done. iSplit; last iExact "Hown". iPureIntro.
  exact Hvalue.
Qed.

Lemma field_read_rule_wp (predicates : predicate_semantics) {Γ F Δ}
    (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) field
    (target : pvar Γ (Logic.field_type field)) (base : pexpr Γ TRef)
    chunk (mask : Hoare.mask) :
  interp_assertion predicates runtime formals binders atoms
    (AAnd (AStack store)
      (AOwn field (Hoare.symbolize_expr store base) chunk)) ⊢
  Model.runtime_wp (Model.runtime_mask mask)
    (LegacyLang.RTFldRd
      (Model.runtime_variable (Model.runtime_names _ runtime) target)
      (Model.runtime_expr (Model.runtime_names _ runtime) base)
      (Resources.field_name field) (Model.runtime_stack_id _ runtime))
    (fun result =>
      (⌜result = LegacyLang.LitUnit⌝ ∗
       interp_assertion predicates runtime formals binders atoms
         (AExists (Logic.field_type field)
           (AAnd (AStack (Hoare.update_store_with_bound store target))
             (AAnd
               (AOwn field (weaken_expr (Hoare.symbolize_expr store base))
                 (weaken_expr chunk))
               (AExpr (EBinOp (BEq (Logic.field_type field))
                 (ERef (RefBound MHere)) (weaken_expr chunk)))))))%I).
Proof.
  iIntros "[Hstack Hown]".
  iDestruct "Hown" as (location value) "(%Hlocation & %Hchunk & Hown)".
  iPoseProof (Model.runtime_field_read_wp runtime formals binders atoms store
    field target base location value (Model.runtime_mask mask) Hlocation
    with "[$Hstack $Hown]") as "Hwp".
  iEval (unfold Model.runtime_wp) in "Hwp". unfold Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iDestruct "Hpost" as (read_value) "(%Hread & Hstack & Hown)".
  iExists read_value. iFrame "Hstack". iSplit.
  - iExists location, value. repeat iSplit; try iExact "Hown"; iPureIntro;
      rewrite interp_weaken_expr; assumption.
  - iPureIntro. simpl. unfold binder_cons. rewrite view_member_here.
    rewrite interp_weaken_expr. rewrite Hchunk. simpl.
    rewrite Hread. rewrite (proj2 (tval_eqb_eq _ value value) eq_refl).
    reflexivity.
Qed.

Lemma allocated_fields_rule_interp (predicates : predicate_semantics)
    {Γ F Δ} (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) address :
  Model.allocated_fields_own runtime formals binders atoms store
      (VRef address) fields ⊢
  interp_assertion predicates runtime formals
    (binder_cons (VRef address) binders) atoms
    (Hoare.allocated_fields_assertion store fields).
Proof.
  induction fields as [|[field expression] fields IH]; simpl.
  - iIntros "_". done.
  - iIntros "Hfields". iDestruct "Hfields" as (value)
      "(%Hvalue & Hown & Hfields)". iSplitL "Hown".
    + iExists (VRef address), value. iSplit.
      { iPureIntro. unfold binder_cons. rewrite view_member_here. reflexivity. }
      iSplit; last iExact "Hown". iPureIntro.
      rewrite interp_weaken_expr. exact Hvalue.
    + iApply IH. iExact "Hfields".
Qed.

Lemma allocation_rule_wp (predicates : predicate_semantics) {Γ F Δ}
    (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (target : pvar Γ TRef)
    (fields : list (field_init Γ)) (mask : Hoare.mask) :
  NoDup (map field_init_id fields) ->
  interp_assertion predicates runtime formals binders atoms (AStack store) ⊢
  Model.runtime_wp (Model.runtime_mask mask)
    (LegacyLang.RTAlloc
      (Model.runtime_variable (Model.runtime_names _ runtime) target)
      (Model.runtime_field_initializers (Model.runtime_names _ runtime) fields)
      (Model.runtime_stack_id _ runtime))
    (fun result =>
      (⌜result = LegacyLang.LitUnit⌝ ∗
       interp_assertion predicates runtime formals binders atoms
         (AExists TRef
           (AAnd (AStack (Hoare.update_store_with_bound store target))
             (Hoare.allocated_fields_assertion store fields))))%I).
Proof.
  intros Hnodup. iIntros "Hstack".
  iPoseProof (Model.runtime_allocation_wp runtime formals binders atoms store
    target fields (Model.runtime_mask mask) Hnodup with "Hstack") as "Hwp".
  iEval (unfold Model.runtime_wp) in "Hwp". unfold Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iDestruct "Hpost" as (address) "[Hstack Hfields]".
  iExists (VRef address). iFrame "Hstack".
  iApply (allocated_fields_rule_interp predicates runtime formals binders atoms
    store fields address with "Hfields").
Qed.

End ConcreteValidity.

Module Type CONTROL_OPERATIONS (Resources : RUNTIME_RESOURCES).
  Module Model := ConcreteModel Resources.
  Parameter operation_wp : forall Γ, Model.stack_context Γ -> stmt Γ ->
    Hoare.mask -> Hoare.mask -> iProp Resources.Σ -> iProp Resources.Σ.
  Parameter operation_mono : forall Γ runtime statement mask_pre mask_post P Q,
    (P ⊢ Q) -> operation_wp Γ runtime statement mask_pre mask_post P ⊢
      operation_wp Γ runtime statement mask_pre mask_post Q.
  Parameter operation_frame : forall Γ runtime statement mask_pre mask_post P R,
    operation_wp Γ runtime statement mask_pre mask_post P ∗ R ⊢
      operation_wp Γ runtime statement mask_pre mask_post (P ∗ R).
  (** Atomic blocks are continuation operators, not opaque leaves: the
      implementation must wrap the recursively translated body supplied by
      the statement transformer. *)
  Parameter atomic_wp : forall Γ, Model.stack_context Γ -> stmt Γ ->
    Hoare.mask -> Hoare.mask -> iProp Resources.Σ -> iProp Resources.Σ.
  Parameter atomic_mono : forall Γ runtime body mask_pre mask_post P Q,
    (P ⊢ Q) -> atomic_wp Γ runtime body mask_pre mask_post P ⊢
      atomic_wp Γ runtime body mask_pre mask_post Q.
  Parameter atomic_frame : forall Γ runtime body mask_pre mask_post P R,
    atomic_wp Γ runtime body mask_pre mask_post P ∗ R ⊢
      atomic_wp Γ runtime body mask_pre mask_post (P ∗ R).
  Parameter atomic_intro : forall Γ runtime body mask_pre mask_post P,
    P ⊢ atomic_wp Γ runtime body mask_pre mask_post P.
End CONTROL_OPERATIONS.

(** Procedure execution is the genuinely program-dependent part of control
    flow.  It is separated from invariant mask transitions and trusted atomic
    wrapping, whose Iris interpretation is fixed below. *)
Module Type PROCEDURE_OPERATIONS (Resources : RUNTIME_RESOURCES).
  Module Model := ConcreteModel Resources.
  Parameter procedure_wp : forall Γ, Model.stack_context Γ -> stmt Γ ->
    Hoare.mask -> Hoare.mask -> iProp Resources.Σ -> iProp Resources.Σ.
  Parameter procedure_mono : forall Γ runtime statement mask_pre mask_post P Q,
    (P ⊢ Q) -> procedure_wp Γ runtime statement mask_pre mask_post P ⊢
      procedure_wp Γ runtime statement mask_pre mask_post Q.
  Parameter procedure_frame : forall Γ runtime statement mask_pre mask_post P R,
    procedure_wp Γ runtime statement mask_pre mask_post P ∗ R ⊢
      procedure_wp Γ runtime statement mask_pre mask_post (P ∗ R).
End PROCEDURE_OPERATIONS.

(** Operational procedure semantics, independent of procedure contracts.
    Contract validity later proves that the required precondition entails
    this WP.  The explicit final fancy update is where a procedure's granted
    Raven mask becomes available to its continuation. *)
Module RuntimeProcedureOperations (Resources : RUNTIME_RESOURCES)
    <: PROCEDURE_OPERATIONS Resources.
Module Model := ConcreteModel Resources.
Local Notation iProp := (iProp Resources.Σ).
Local Existing Instance Model.concrete_irisG.

Definition procedure_wp {Γ} (runtime : Model.stack_context Γ)
    (statement : stmt Γ) (mask_pre mask_post : Hoare.mask)
    (post : iProp) : iProp :=
  match statement with
  | TCall _ _ _ _ | TSpawn _ _ _ =>
      match Model.runtime_stmt (Model.runtime_names _ runtime)
          (Model.runtime_stack_id _ runtime) statement with
      | Some runtime_statement =>
          Model.runtime_wp (Model.runtime_mask mask_pre) runtime_statement
            (fun result =>
              (⌜result = LegacyLang.LitUnit⌝ ∗
               |={Model.runtime_mask mask_pre,
                   Model.runtime_mask mask_post}=> post)%I)
      | None => False%I
      end
  | _ => False%I
  end.

Lemma procedure_mono Γ runtime statement mask_pre mask_post P Q :
  (P ⊢ Q) ->
  @procedure_wp Γ runtime statement mask_pre mask_post P ⊢
    @procedure_wp Γ runtime statement mask_pre mask_post Q.
Proof.
  intros HPQ. unfold procedure_wp. destruct statement; simpl; try reflexivity;
    try destruct target; simpl.
  all: unfold Model.runtime_wp; iIntros "Hwp"; iApply (wp_mono with "Hwp");
    iIntros (result) "[%Hresult Hpost]"; iSplit; first done;
    iMod "Hpost"; iModIntro; iApply HPQ; iExact "Hpost".
Qed.

Lemma procedure_frame Γ runtime statement mask_pre mask_post P R :
  @procedure_wp Γ runtime statement mask_pre mask_post P ∗ R ⊢
    @procedure_wp Γ runtime statement mask_pre mask_post (P ∗ R).
Proof.
  unfold procedure_wp. destruct statement; simpl;
    try (iIntros "[H _]"; done); try destruct target; simpl.
  all: unfold Model.runtime_wp; iIntros "[Hwp HR]";
    iPoseProof (@wp_frame_r HasLc LegacyLang.simp_lang Resources.Σ
      Model.concrete_irisG NotStuck (Model.runtime_mask mask_pre) _
      (fun result =>
        (⌜result = LegacyLang.LitUnit⌝ ∗
         |={Model.runtime_mask mask_pre, Model.runtime_mask mask_post}=> P)%I)
      R with "[$Hwp $HR]") as "Hwp";
    iApply (wp_mono with "Hwp");
    iIntros (result) "[[%Hresult Hpost] HR]"; iSplit; first done;
    iMod "Hpost"; iModIntro; iFrame.
Qed.
End RuntimeProcedureOperations.

(** The fixed continuation implementation of control operations.  Calls and
    spawn are supplied by the verified program module, and a trusted atomic
    block wraps the already recursively translated body rather than
    translating it a second time.

    The bare two-mask updates below are deliberately only the operation-level
    shape of [TUnfold]/[TFold].  They do not manufacture the linear closing
    continuation returned by [InvariantWorld.open_world].  The semantic
    control contract therefore remains abstract until the certified atomicity
    region threads that continuation from an unfold to every matching fold;
    see [local/binding-redesign.md]. *)
Module DirectControlOperations (Resources : RUNTIME_RESOURCES)
    (Procedures : PROCEDURE_OPERATIONS Resources)
    <: CONTROL_OPERATIONS Resources.
Module Model := Procedures.Model.
Local Notation iProp := (iProp Resources.Σ).
Local Existing Instance Model.concrete_irisG.

Definition operation_wp {Γ} (runtime : Model.stack_context Γ)
    (statement : stmt Γ) (mask_pre mask_post : Hoare.mask)
    (post : iProp) : iProp :=
  match statement with
  | TCall _ _ _ _ | TSpawn _ _ _ =>
      Procedures.procedure_wp Γ runtime statement mask_pre mask_post post
  | TUnfold _ _ _ | TFold _ _ _ =>
      (|={Model.runtime_mask mask_pre, Model.runtime_mask mask_post}=> post)%I
  | _ => False%I
  end.

Lemma operation_mono Γ runtime statement mask_pre mask_post P Q :
  (P ⊢ Q) -> @operation_wp Γ runtime statement mask_pre mask_post P ⊢
    @operation_wp Γ runtime statement mask_pre mask_post Q.
Proof.
  intros HPQ. unfold operation_wp. destruct statement; simpl;
    try (apply Procedures.procedure_mono; exact HPQ); try reflexivity.
  all: iIntros "HP"; iMod "HP"; iModIntro; iApply HPQ; iExact "HP".
Qed.

Lemma operation_frame Γ runtime statement mask_pre mask_post P R :
  @operation_wp Γ runtime statement mask_pre mask_post P ∗ R ⊢
    @operation_wp Γ runtime statement mask_pre mask_post (P ∗ R).
Proof.
  unfold operation_wp. destruct statement; simpl;
    try apply Procedures.procedure_frame; try (iIntros "[H _]"; done).
  all: iIntros "[HP HR]"; iMod "HP"; iModIntro; iFrame.
Qed.

Definition atomic_wp {Γ} (_ : Model.stack_context Γ) (_ : stmt Γ)
    (_ _ : Hoare.mask) (body_wp : iProp) : iProp := body_wp.

Lemma atomic_mono Γ runtime body mask_pre mask_post P Q :
  (P ⊢ Q) -> @atomic_wp Γ runtime body mask_pre mask_post P ⊢
    @atomic_wp Γ runtime body mask_pre mask_post Q.
Proof. exact (fun HPQ => HPQ). Qed.

Lemma atomic_frame Γ runtime body mask_pre mask_post P R :
  @atomic_wp Γ runtime body mask_pre mask_post P ∗ R ⊢
    @atomic_wp Γ runtime body mask_pre mask_post (P ∗ R).
Proof. reflexivity. Qed.

Lemma atomic_intro Γ runtime body mask_pre mask_post P :
  P ⊢ @atomic_wp Γ runtime body mask_pre mask_post P.
Proof. reflexivity. Qed.
End DirectControlOperations.

Module ConcreteControlOperations (Resources : RUNTIME_RESOURCES).
  Module Procedures := RuntimeProcedureOperations Resources.
  Include DirectControlOperations Resources Procedures.
End ConcreteControlOperations.

Module ConcreteExecution (Resources : RUNTIME_RESOURCES)
    (Operations : CONTROL_OPERATIONS Resources).
Module Model := Operations.Model.
Module VSemantics := Validation.Semantics Model.
Local Notation iProp := (iProp Resources.Σ).
Local Existing Instance Model.concrete_irisG.
Import Translation.Assertions.

Lemma interp_assertion_timeless
    (predicates : VSemantics.S.predicate_semantics)
    (Hpredicates : forall predicate values,
      Timeless (predicates predicate values))
    {Γ F Δ} (runtime : Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (formula : assertion Γ F Δ) :
  Timeless (VSemantics.S.interp_assertion predicates runtime formals binders
    atoms formula).
Proof.
  induction formula; simpl.
  - apply _.
  - apply _.
  - apply _.
  - apply _.
  - apply bi.exist_timeless. intros. apply IHformula.
  - apply bi.forall_timeless. intros. apply IHformula.
  - apply bi.and_timeless; apply bi.wand_timeless; apply IHformula1 ||
      apply IHformula2.
  - apply bi.exist_timeless. intros. apply bi.sep_timeless; [apply _|apply _].
  - apply bi.exist_timeless. intros. apply bi.sep_timeless; [apply _|].
    apply Hpredicates.
  - apply bi.sep_timeless; [apply IHformula1|apply IHformula2].
Qed.

Definition physical_leaf_wp {Γ} (runtime : Model.stack_context Γ)
    (statement : LegacyLang.runtime_stmt) (mask : Hoare.mask) (post : iProp) :
    iProp :=
  Model.runtime_wp (Model.runtime_mask mask) statement
    (fun result => (⌜result = LegacyLang.LitUnit⌝ ∗ post)%I).

Definition leaf_wp {Γ} (runtime : Model.stack_context Γ)
    (statement : stmt Γ) (mask_pre mask_post : Hoare.mask) (post : iProp) :
    iProp :=
  match statement with
  | TCall _ _ _ _ | TSpawn _ _ _ | TUnfold _ _ _ | TFold _ _ _ =>
      Operations.operation_wp Γ runtime statement mask_pre mask_post post
  | _ =>
    match decide (mask_pre = mask_post) with
    | left _ =>
      match statement with
      | TSkip _ | TAssert _ _ => post
      | TAssign _ target expression =>
          physical_leaf_wp runtime
            (LegacyLang.RTAssign
              (Model.runtime_variable (Model.runtime_names _ runtime) target)
              (Model.runtime_expr (Model.runtime_names _ runtime) expression)
              (Model.runtime_stack_id _ runtime)) mask_pre post
      | TFieldRead _ field target base =>
          physical_leaf_wp runtime
            (LegacyLang.RTFldRd
              (Model.runtime_variable (Model.runtime_names _ runtime) target)
              (Model.runtime_expr (Model.runtime_names _ runtime) base)
              (Resources.field_name field) (Model.runtime_stack_id _ runtime))
            mask_pre post
      | TFieldWrite _ field base expression =>
          physical_leaf_wp runtime
            (LegacyLang.RTFldWr
              (Model.runtime_expr (Model.runtime_names _ runtime) base)
              (Resources.field_name field)
              (Model.runtime_expr (Model.runtime_names _ runtime) expression)
              (Model.runtime_stack_id _ runtime)) mask_pre post
      | TAlloc _ target fields =>
          physical_leaf_wp runtime
            (LegacyLang.RTAlloc
              (Model.runtime_variable (Model.runtime_names _ runtime) target)
              (Model.runtime_field_initializers
                (Model.runtime_names _ runtime) fields)
              (Model.runtime_stack_id _ runtime)) mask_pre post
      | TGhostUpdate _ _ _ _ _ =>
          (|={Model.runtime_mask mask_pre}=> post)%I
      | TPredicateUnfold _ _ _ | TPredicateFold _ _ _ => post
      | _ => False%I
      end
    | right _ => False%I
    end
  end.

Definition branch_wp {Γ} (_ : Model.stack_context Γ) (_ : pexpr Γ TBool)
    (_ : Hoare.mask) (then_wp else_wp : iProp) : iProp :=
  (then_wp ∨ else_wp)%I.

Lemma physical_leaf_mono {Γ} runtime statement mask (P Q : iProp) :
  (P ⊢ Q) -> physical_leaf_wp (Γ := Γ) runtime statement mask P ⊢
    physical_leaf_wp runtime statement mask Q.
Proof.
  intros HPQ. unfold physical_leaf_wp, Model.runtime_wp.
  iIntros "Hwp". iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult HP]". iSplit; first done.
  iApply HPQ. iExact "HP".
Qed.

Lemma physical_leaf_frame {Γ} runtime statement mask (P R : iProp) :
  physical_leaf_wp (Γ := Γ) runtime statement mask P ∗ R ⊢
    physical_leaf_wp runtime statement mask (P ∗ R).
Proof.
  unfold physical_leaf_wp, Model.runtime_wp.
  iIntros "[Hwp HR]".
  iPoseProof (@wp_frame_r HasLc LegacyLang.simp_lang Resources.Σ
    Model.concrete_irisG NotStuck (Model.runtime_mask mask) statement
    (fun result => (⌜result = LegacyLang.LitUnit⌝ ∗ P)%I) R
    with "[$Hwp $HR]") as "Hwp".
  iApply (wp_mono with "Hwp").
  iIntros (result) "[[%Hresult HP] HR]". iSplit; first done. iFrame.
Qed.

Lemma ghost_leaf_mono (mask : Hoare.mask) (P Q : iProp) :
  (P ⊢ Q) ->
  (|={Model.runtime_mask mask}=> P) ⊢ |={Model.runtime_mask mask}=> Q.
Proof.
  intros HPQ. iIntros "HP". iMod "HP". iModIntro. iApply HPQ. iExact "HP".
Qed.

Lemma ghost_leaf_frame (mask : Hoare.mask) (P R : iProp) :
  (|={Model.runtime_mask mask}=> P) ∗ R ⊢
    |={Model.runtime_mask mask}=> P ∗ R.
Proof. iIntros "[HP HR]". iMod "HP". iModIntro. iFrame. Qed.

Module Primitives <: VSemantics.CONTINUATION_PRIMITIVES.
  Definition leaf_wp := @leaf_wp.
  Definition branch_wp := @branch_wp.
  Definition atomic_wp := @Operations.atomic_wp.

  Lemma leaf_mono Γ runtime statement mask_pre mask_post P Q :
    (P ⊢ Q) -> leaf_wp Γ runtime statement mask_pre mask_post P ⊢
      leaf_wp Γ runtime statement mask_pre mask_post Q.
  Proof.
    intros HPQ. change (ConcreteExecution.leaf_wp runtime statement mask_pre
      mask_post P ⊢ ConcreteExecution.leaf_wp runtime statement mask_pre
      mask_post Q). unfold ConcreteExecution.leaf_wp.
    destruct statement; simpl;
      try (apply Operations.operation_mono; exact HPQ);
      destruct (decide (mask_pre = mask_post)); simpl; try reflexivity;
      try exact HPQ; try (apply ghost_leaf_mono; exact HPQ);
      try (apply physical_leaf_mono; exact HPQ).
  Qed.

  Lemma leaf_frame Γ runtime statement mask_pre mask_post P R :
    leaf_wp Γ runtime statement mask_pre mask_post P ∗ R ⊢
      leaf_wp Γ runtime statement mask_pre mask_post (P ∗ R).
  Proof.
    change (ConcreteExecution.leaf_wp runtime statement mask_pre mask_post P ∗ R
      ⊢ ConcreteExecution.leaf_wp runtime statement mask_pre mask_post (P ∗ R)).
    unfold ConcreteExecution.leaf_wp. destruct statement; simpl;
      try apply Operations.operation_frame;
      destruct (decide (mask_pre = mask_post)); simpl; try reflexivity;
      try apply ghost_leaf_frame; try (iIntros "[H _]"; done);
      try apply physical_leaf_frame.
  Qed.

  Lemma leaf_skip Γ runtime node mask P :
    P ⊢ leaf_wp Γ runtime (TSkip node) mask mask P.
  Proof.
    change (P ⊢ ConcreteExecution.leaf_wp runtime (TSkip node) mask mask P).
    unfold ConcreteExecution.leaf_wp. destruct (decide (mask = mask));
      [reflexivity|contradiction].
  Qed.

  Lemma leaf_assert Γ runtime node condition mask P :
    P ⊢ leaf_wp Γ runtime (TAssert node condition) mask mask P.
  Proof.
    change (P ⊢ ConcreteExecution.leaf_wp runtime
      (TAssert node condition) mask mask P).
    unfold ConcreteExecution.leaf_wp. destruct (decide (mask = mask));
      [reflexivity|contradiction].
  Qed.

  Definition atomic_mono := @Operations.atomic_mono.
  Definition atomic_frame := @Operations.atomic_frame.

  Lemma branch_mono Γ runtime condition mask P P' Q Q' :
    (P ⊢ P') -> (Q ⊢ Q') ->
    branch_wp Γ runtime condition mask P Q ⊢
      branch_wp Γ runtime condition mask P' Q'.
  Proof.
    intros HP HQ. iIntros "[HP|HQ]".
    - iLeft. iApply HP. iExact "HP".
    - iRight. iApply HQ. iExact "HQ".
  Qed.

  Lemma branch_frame Γ runtime condition mask P Q R :
    branch_wp Γ runtime condition mask P Q ∗ R ⊢
      branch_wp Γ runtime condition mask (P ∗ R) (Q ∗ R).
  Proof. iIntros "[[HP|HQ] HR]"; [iLeft|iRight]; iFrame. Qed.

  Lemma branch_select (Γ F Δ : context) (runtime : Model.stack_context Γ)
      (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
      (store : symbolic_store Γ F Δ) (frame : iProp) condition mask P Q :
    (Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗
       frame ∗ ⌜interp_expr formals binders atoms
         (Hoare.symbolize_expr store condition) = Some (VBool true)⌝ ⊢ P) ->
    (Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗
       frame ∗ ⌜interp_expr formals binders atoms
         (Hoare.symbolize_expr store condition) ≠ Some (VBool true)⌝ ⊢ Q) ->
    Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗
      frame ⊢ branch_wp Γ runtime condition mask P Q.
  Proof.
    intros Hthen Helse.
    destruct (interp_expr formals binders atoms
      (Hoare.symbolize_expr store condition)) as [value|] eqn:Hvalue.
    - dependent destruction value. destruct b.
      + iIntros "[Hstack Hframe]". iLeft. iApply Hthen. iFrame.
        iPureIntro. reflexivity.
      + iIntros "[Hstack Hframe]". iRight. iApply Helse. iFrame.
        iPureIntro. congruence.
    - exfalso. destruct (interp_expr_total formals binders atoms
        (Hoare.symbolize_expr store condition)) as [value Htotal].
      congruence.
  Qed.
End Primitives.

Module StatementWP := VSemantics.ContinuationExecution Primitives.

Module StructuralValidity (Contracts : Hoare.CONTRACT_ENV) :=
  VSemantics.StructuralValidity Contracts StatementWP.Interface.

Module PhysicalValidity (Contracts : Hoare.CONTRACT_ENV).
Module Structural := StructuralValidity Contracts.
Module Assertions := Translation.Assertions.
Module CV := ConcreteValidity Resources.
Import Assertions.
Section WithPredicates.
Context (predicates : atom_env -> VSemantics.S.predicate_semantics).

Lemma assignment_rule_valid {Γ F Δ t} (node : node_id)
    (store : symbolic_store Γ F Δ) (target : pvar Γ t)
    (expression : pexpr Γ t) (current_mask : Hoare.mask) :
  Structural.semantically_valid predicates
    (AStack store) (TAssign node target expression)
    current_mask current_mask
    (AExists t
      (AAnd (AStack (Hoare.update_store_with_bound store target))
        (AExpr (EBinOp (BEq t) (ERef (RefBound MHere))
          (weaken_expr (Hoare.symbolize_expr store expression)))))).
Proof.
  intros runtime formals binders atoms.
  unfold StatementWP.Interface.statement_wp, StatementWP.statement_wp.
  simpl. unfold Primitives.leaf_wp, leaf_wp.
  rewrite decide_True; last reflexivity. simpl.
  fold (VSemantics.S.interp_assertion (predicates atoms) runtime formals binders atoms
    (AStack store)).
  fold (VSemantics.S.interp_assertion (predicates atoms) runtime formals binders atoms
    (AExists t
      (AAnd (AStack (Hoare.update_store_with_bound store target))
        (AExpr (EBinOp (BEq t) (ERef (RefBound MHere))
          (weaken_expr (Hoare.symbolize_expr store expression))))))).
  unfold physical_leaf_wp.
  iIntros "Hpre".
  iPoseProof (Model.runtime_assignment_wp runtime formals binders atoms store
    target expression (Model.runtime_mask current_mask) with "Hpre") as "Hwp".
  iEval (unfold Model.runtime_wp) in "Hwp". unfold Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iDestruct "Hpost" as (value) "[%Hvalue Hstack]".
  iExists value. iFrame. iPureIntro. rewrite interp_weaken_expr.
  unfold interp_program_expr in Hvalue. rewrite Hvalue. simpl.
  unfold binder_cons. rewrite view_member_here.
  rewrite (proj2 (tval_eqb_eq t value value) eq_refl). reflexivity.
Qed.

Lemma field_write_rule_valid {Γ F Δ} (node : node_id)
    (store : symbolic_store Γ F Δ) field (base : pexpr Γ TRef)
    (expression : pexpr Γ (Logic.field_type field)) old_chunk current_mask :
  Structural.semantically_valid predicates
    (AAnd (AStack store)
      (AOwn field (Hoare.symbolize_expr store base) old_chunk))
    (TFieldWrite node field base expression) current_mask current_mask
    (AAnd (AStack store)
      (AOwn field (Hoare.symbolize_expr store base)
        (Hoare.symbolize_expr store expression))).
Proof.
  intros runtime formals binders atoms.
  unfold StatementWP.Interface.statement_wp, StatementWP.statement_wp.
  simpl. unfold Primitives.leaf_wp, leaf_wp.
  rewrite decide_True; last reflexivity. simpl. unfold physical_leaf_wp.
  iIntros "[Hstack Hown]".
  iDestruct "Hown" as (location old_value) "(%Hlocation & %Hold & Hown)".
  iPoseProof (Model.runtime_field_write_wp runtime formals binders atoms store
    field base expression location old_value (Model.runtime_mask current_mask)
    Hlocation with "[$Hstack $Hown]") as "Hwp".
  iEval (unfold Model.runtime_wp) in "Hwp". unfold Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iDestruct "Hpost" as (new_value) "(%Hvalue & Hstack & Hown)".
  iFrame "Hstack". iExists location, new_value.
  iSplit; first done. iSplit; last iExact "Hown". iPureIntro. exact Hvalue.
Qed.

Lemma field_read_rule_valid {Γ F Δ} (node : node_id)
    (store : symbolic_store Γ F Δ) field
    (target : pvar Γ (Logic.field_type field)) (base : pexpr Γ TRef)
    chunk current_mask :
  Structural.semantically_valid predicates
    (AAnd (AStack store)
      (AOwn field (Hoare.symbolize_expr store base) chunk))
    (TFieldRead node field target base) current_mask current_mask
    (AExists (Logic.field_type field)
      (AAnd (AStack (Hoare.update_store_with_bound store target))
        (AAnd
          (AOwn field (weaken_expr (Hoare.symbolize_expr store base))
            (weaken_expr chunk))
          (AExpr (EBinOp (BEq (Logic.field_type field))
            (ERef (RefBound MHere)) (weaken_expr chunk)))))).
Proof.
  intros runtime formals binders atoms.
  unfold StatementWP.Interface.statement_wp, StatementWP.statement_wp.
  simpl. unfold Primitives.leaf_wp, leaf_wp.
  rewrite decide_True; last reflexivity. simpl. unfold physical_leaf_wp.
  iIntros "[Hstack Hown]".
  iDestruct "Hown" as (location value) "(%Hlocation & %Hchunk & Hown)".
  iPoseProof (Model.runtime_field_read_wp runtime formals binders atoms store
    field target base location value (Model.runtime_mask current_mask)
    Hlocation with "[$Hstack $Hown]") as "Hwp".
  iEval (unfold Model.runtime_wp) in "Hwp". unfold Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iDestruct "Hpost" as (read_value) "(%Hread & Hstack & Hown)".
  iExists read_value. iFrame "Hstack". iSplit.
  - iExists location, value. repeat iSplit; try iExact "Hown"; iPureIntro;
      rewrite interp_weaken_expr; assumption.
  - iPureIntro. simpl. unfold binder_cons. rewrite view_member_here.
    rewrite interp_weaken_expr. rewrite Hchunk. simpl. rewrite Hread.
    rewrite (proj2 (tval_eqb_eq _ value value) eq_refl). reflexivity.
Qed.

Lemma allocated_fields_rule_valid {Γ F Δ}
    (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) fields address :
  Model.allocated_fields_own runtime formals binders atoms store
      (VRef address) fields ⊢
  VSemantics.S.interp_assertion (predicates atoms) runtime formals
    (binder_cons (VRef address) binders) atoms
    (Hoare.allocated_fields_assertion store fields).
Proof.
  induction fields as [|[field expression] fields IH]; simpl.
  - iIntros "_". done.
  - iIntros "Hfields". iDestruct "Hfields" as (value)
      "(%Hvalue & Hown & Hfields)". iSplitL "Hown".
    + iExists (VRef address), value. iSplit.
      { iPureIntro. unfold binder_cons. rewrite view_member_here. reflexivity. }
      iSplit; last iExact "Hown". iPureIntro.
      rewrite interp_weaken_expr. exact Hvalue.
    + iApply IH. iExact "Hfields".
Qed.

Lemma allocation_rule_valid {Γ F Δ} (node : node_id)
    (store : symbolic_store Γ F Δ) (target : pvar Γ TRef)
    fields current_mask :
  NoDup (map field_init_id fields) ->
  Structural.semantically_valid predicates (AStack store)
    (TAlloc node target fields) current_mask current_mask
    (AExists TRef
      (AAnd (AStack (Hoare.update_store_with_bound store target))
        (Hoare.allocated_fields_assertion store fields))).
Proof.
  intros Hnodup runtime formals binders atoms.
  unfold StatementWP.Interface.statement_wp, StatementWP.statement_wp.
  simpl. unfold Primitives.leaf_wp, leaf_wp.
  rewrite decide_True; last reflexivity. simpl. unfold physical_leaf_wp.
  iIntros "Hstack".
  iPoseProof (Model.runtime_allocation_wp runtime formals binders atoms store
    target fields (Model.runtime_mask current_mask) Hnodup
    with "Hstack") as "Hwp".
  iEval (unfold Model.runtime_wp) in "Hwp". unfold Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iDestruct "Hpost" as (address) "[Hstack Hfields]".
  iExists (VRef address). iFrame "Hstack".
  iApply (allocated_fields_rule_valid runtime formals binders atoms store
    fields address with "Hfields").
Qed.

End WithPredicates.
End PhysicalValidity.

Import Translation.Assertions.

(** Canonical recursive predicate and invariant-body interpretation used by
    concrete module instantiations. *)
Module DefinitionSemantics (Defs : Translation.DEFINITION_ENV).
  Module Definitions := VSemantics.S.Definitions Defs.
  Definition predicates (atoms : atom_env) :
      VSemantics.S.predicate_semantics :=
    Definitions.predicate_interp atoms.
  Definition invariant_body (atoms : atom_env) invariant
      (values : tval_list (Logic.invariant_args invariant)) : iProp :=
    Definitions.invariant_body_interp atoms invariant values.
End DefinitionSemantics.

(** Recursive predicate interpretation needed by invariant bodies. *)
Module Type TIMELESS_PREDICATES.
  Parameter predicates : atom_env -> VSemantics.S.predicate_semantics.
  Parameter predicates_timeless : forall atoms predicate values,
    Timeless (predicates atoms predicate values).
End TIMELESS_PREDICATES.

Module InvariantWorld (Contracts : Hoare.CONTRACT_ENV)
    (Leaf : TIMELESS_PREDICATES)
    (Defs : Translation.DEFINITION_ENV).
Local Existing Instance Resources.invTokenG0.

Definition body_interp (atoms : atom_env) invariant
    (values : tval_list (Logic.invariant_args invariant)) : iProp :=
  VSemantics.S.interp_assertion (Leaf.predicates atoms)
    Model.empty_stack_context (formal_env_of_values values)
    empty_binder_env atoms (Defs.invariant_body invariant).

Definition body_at (atoms : atom_env) invariant
    (raw_values : list Legacy.val) : iProp :=
  (∃ values : tval_list (Logic.invariant_args invariant),
    ⌜Model.tval_list_to_rich_list values = raw_values⌝ ∗
    body_interp atoms invariant values)%I.

Definition world (atoms : atom_env) invariant : iProp :=
  (∃ established : gset (list Legacy.val),
    @own Resources.Σ (authR Legacy.inv_argsUR) Model.concrete_invtoken_inG
      (Legacy.invtoken_names (Resources.invariant_name invariant))
      (● (established : Legacy.inv_argsUR)) ∗
    [∗ set] raw_values ∈ established, body_at atoms invariant raw_values)%I.

Definition world_context (atoms : atom_env) : iProp :=
  (∀ invariant : inv_id,
    inv (Resources.invariant_namespace invariant) (world atoms invariant))%I.

Global Instance world_context_persistent atoms :
  Persistent (world_context atoms).
Proof. unfold world_context. apply bi.forall_persistent. intros invariant. apply _. Qed.

Global Instance body_interp_timeless atoms invariant values :
  Timeless (body_interp atoms invariant values).
Proof.
  unfold body_interp. apply interp_assertion_timeless.
  apply Leaf.predicates_timeless.
Qed.

Global Instance body_at_timeless atoms invariant raw_values :
  Timeless (body_at atoms invariant raw_values).
Proof.
  unfold body_at. apply bi.exist_timeless. intros values.
  apply bi.sep_timeless; apply _.
Qed.

Global Instance world_timeless atoms invariant :
  Timeless (world atoms invariant).
Proof.
  unfold world. apply bi.exist_timeless. intros established.
  apply bi.sep_timeless; first apply _.
  apply big_sepS_timeless. intros raw_values _. apply _.
Qed.

Lemma fragment_member invariant established values :
  @own Resources.Σ (authR Legacy.inv_argsUR) Model.concrete_invtoken_inG
      (Legacy.invtoken_names (Resources.invariant_name invariant))
      (● (established : Legacy.inv_argsUR)) -∗
  Model.invariant_own invariant values -∗
  ⌜Model.tval_list_to_rich_list values ∈ established⌝.
Proof.
  iIntros "Hauth Hfrag". unfold Model.invariant_own.
  iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
  apply auth_both_valid_discrete in Hvalid as [Hincluded _].
  apply gset_included in Hincluded. iPureIntro. set_solver.
Qed.

Lemma open_world atoms invariant values E :
  ↑(Resources.invariant_namespace invariant) ⊆ E ->
  inv (Resources.invariant_namespace invariant) (world atoms invariant) -∗
  Model.invariant_own invariant values
    ={E, E ∖ ↑(Resources.invariant_namespace invariant)}=∗
  body_interp atoms invariant values ∗
    (body_interp atoms invariant values
      ={E ∖ ↑(Resources.invariant_namespace invariant), E}=∗ True).
Proof.
  intros Hnamespace. iIntros "#Hworld Hfragment".
  iMod (inv_acc_timeless with "Hworld") as "[Hcontents Hclose]";
    first exact Hnamespace.
  iDestruct "Hcontents" as (established) "[Hauth Hbodies]".
  iDestruct (fragment_member with "Hauth Hfragment") as %Hmember.
  rewrite (big_sepS_delete _ established
    (Model.tval_list_to_rich_list values) Hmember).
  iDestruct "Hbodies" as "[Hbody_at Hbodies]".
  iDestruct "Hbody_at" as (stored_values) "[%Hstored Hbody]".
  apply Model.tval_list_to_rich_list_injective in Hstored. subst stored_values.
  iModIntro. iFrame "Hbody". iIntros "Hbody". iApply "Hclose".
  iExists established. iFrame "Hauth".
  rewrite (big_sepS_delete _ established
    (Model.tval_list_to_rich_list values) Hmember).
  iFrame "Hbodies". iExists values. iFrame. done.
Qed.

Lemma open_world_certificate atoms invariant values
    (entry exit : GenericRegions.Atomicity.analysis_state) :
  GenericRegions.Atomicity.open_invariant invariant entry = inr exit ->
  inv (Resources.invariant_namespace invariant) (world atoms invariant) -∗
  Model.invariant_own invariant values
    ={Model.runtime_mask (GenericRegions.Atomicity.analysis_mask entry),
       Model.runtime_mask (GenericRegions.Atomicity.analysis_mask exit)}=∗
  body_interp atoms invariant values ∗
    (body_interp atoms invariant values
      ={Model.runtime_mask (GenericRegions.Atomicity.analysis_mask exit),
         Model.runtime_mask (GenericRegions.Atomicity.analysis_mask entry)}=∗
      True).
Proof.
  intros Htransition.
  apply GenericRegions.Atomicity.open_invariant_success in Htransition as
    (_ & Hmember & Hmask & _).
  rewrite Hmask.
  rewrite (Model.runtime_mask_delete invariant
    (GenericRegions.Atomicity.analysis_mask entry) Hmember).
  apply open_world.
  apply Model.invariant_namespace_subset_runtime_mask. exact Hmember.
Qed.

(** Linear semantic state threaded only by certified-region validity.  The
    Raven assertion at an unfold receives [body_interp]; its matching stack
    frame retains the typed arguments and the closer.  Remembering the
    opening mask lets the fold proof frame that closer across mask grants
    acquired while the accessor is live. *)
Definition access_frame (atoms : atom_env) (ambient : coPset)
    (invariant : inv_id) (outer_open : gset inv_id) : iProp :=
  (∃ values : tval_list (Logic.invariant_args invariant),
    Model.invariant_own invariant values ∗
    (body_interp atoms invariant values
      ={Model.enabled_runtime_mask ambient ({[invariant]} ∪ outer_open),
         Model.enabled_runtime_mask ambient outer_open}=∗ True))%I.

Lemma open_world_access_frame atoms ambient invariant values outer_open :
  ↑(Resources.invariant_namespace invariant) ⊆
    Model.enabled_runtime_mask ambient outer_open ->
  inv (Resources.invariant_namespace invariant) (world atoms invariant) -∗
  Model.invariant_own invariant values
    ={Model.enabled_runtime_mask ambient outer_open,
       Model.enabled_runtime_mask ambient ({[invariant]} ∪ outer_open)}=∗
  body_interp atoms invariant values ∗
    access_frame atoms ambient invariant outer_open.
Proof.
  intros Hnamespace.
  have Hactive :
      Model.enabled_runtime_mask ambient outer_open ∖
        ↑(Resources.invariant_namespace invariant) =
      Model.enabled_runtime_mask ambient ({[invariant]} ∪ outer_open).
  { unfold Model.enabled_runtime_mask.
    rewrite Model.invariant_mask_union_singleton. set_solver. }
  iIntros "#Hworld #Hown".
  iMod (open_world atoms invariant values
    (Model.enabled_runtime_mask ambient outer_open) Hnamespace
    with "Hworld Hown") as "[Hbody Hclose]".
  rewrite Hactive.
  iModIntro. iFrame "Hbody". iExists values. iFrame. iExact "Hown".
Qed.

Lemma close_access_frame atoms ambient invariant values outer_open :
  (forall stored_values : tval_list (Logic.invariant_args invariant),
    stored_values = values) ->
  body_interp atoms invariant values ∗
    access_frame atoms ambient invariant outer_open ⊢
  |={Model.enabled_runtime_mask ambient ({[invariant]} ∪ outer_open),
      Model.enabled_runtime_mask ambient outer_open}=>
    Model.invariant_own invariant values.
Proof.
  intros Hunique. iIntros "[Hbody Hframe]".
  iDestruct "Hframe" as (stored_values) "[#Hown Hclose]".
  have -> := Hunique stored_values.
  iMod ("Hclose" with "Hbody"). iModIntro. iExact "Hown".
Qed.

Fixpoint access_stack_interp (atoms : atom_env) (ambient : coPset)
    (stack : list GenericRegions.Atomicity.access_marker) : iProp :=
  match stack with
  | [] => emp%I
  | (invariant, outer_open) :: rest =>
      (access_frame atoms ambient invariant outer_open ∗
       access_stack_interp atoms ambient rest)%I
  end.

Lemma access_stack_interp_nil atoms ambient :
  access_stack_interp atoms ambient [] ⊣⊢ emp.
Proof. reflexivity. Qed.

Lemma access_stack_interp_cons atoms ambient invariant outer_open rest :
  access_stack_interp atoms ambient ((invariant, outer_open) :: rest) ⊣⊢
    access_frame atoms ambient invariant outer_open ∗
    access_stack_interp atoms ambient rest.
Proof. reflexivity. Qed.

Lemma establish_world atoms invariant values E :
  ↑(Resources.invariant_namespace invariant) ⊆ E ->
  inv (Resources.invariant_namespace invariant) (world atoms invariant) -∗
  body_interp atoms invariant values ={E}=∗
  Model.invariant_own invariant values.
Proof.
  intros Hnamespace. iIntros "#Hworld Hbody".
  iMod (inv_acc_timeless with "Hworld") as "[Hcontents Hclose]";
    first exact Hnamespace.
  iDestruct "Hcontents" as (established) "[Hauth Hbodies]".
  set raw_values := Model.tval_list_to_rich_list values.
  iMod (own_update _ _
    (● ((established ∪ {[raw_values]}) : Legacy.inv_argsUR) ⋅
     ◯ ({[raw_values]} : Legacy.inv_argsUR)) with "Hauth")
    as "[Hauth Hfragment]".
  { etrans.
    - apply (auth_update_auth (established : Legacy.inv_argsUR)
        (established ∪ {[raw_values]}) (established ∪ {[raw_values]})).
      apply gset_local_update. set_solver.
    - apply auth_update_dfrac_alloc; [apply _|].
      apply gset_included. set_solver. }
  iMod ("Hclose" with "[-Hfragment]").
  { iExists (established ∪ {[raw_values]}). iFrame "Hauth".
    destruct (decide (raw_values ∈ established)) as [Hpresent|Hfresh].
    - have Heq : established ∪ {[raw_values]} = established.
      { apply set_eq. intros other. rewrite elem_of_union elem_of_singleton.
        split.
        - intros [Hother|Heq]; first exact Hother. subst. exact Hpresent.
        - intros Hother. left. exact Hother. }
      rewrite Heq. iFrame "Hbodies".
    - rewrite big_sepS_union; last set_solver.
      iFrame "Hbodies". rewrite big_sepS_singleton.
      iExists values. iFrame. done. }
  iModIntro. unfold Model.invariant_own.
  iExact "Hfragment".
Qed.

End InvariantWorld.

Module Type SEMANTIC_LEAF_CONTRACTS (Contracts : Hoare.CONTRACT_ENV).
  Include TIMELESS_PREDICATES.
  Parameter predicate_instantiation_valid : forall {Γ F Δ}
      (runtime : Model.stack_context Γ) (formals : formal_env F)
      (binders : binder_env Δ) (atoms : atom_env) predicate
      (expressions : expr_list F Δ (Logic.predicate_args predicate)) body,
    Contracts.instantiated_predicate Γ F Δ (Logic.predicate_args predicate)
      predicate expressions body ->
    VSemantics.S.interp_assertion (predicates atoms) runtime formals binders atoms body ≡
    VSemantics.S.interp_assertion (predicates atoms) runtime formals binders atoms
      (APredicate predicate expressions).
  Parameter ghost_update_valid : forall {F Δ} field
      (old_expression new_expression : expr F Δ (Logic.field_type field))
      (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
      old_value new_value location mask,
    Contracts.valid_ghost_update F Δ field old_expression new_expression ->
    interp_expr formals binders atoms old_expression = Some old_value ->
    interp_expr formals binders atoms new_expression = Some new_value ->
    Model.field_own field location old_value ⊢
      |={Model.runtime_mask mask}=> Model.field_own field location new_value.
End SEMANTIC_LEAF_CONTRACTS.

Module NonPhysicalValidity (Contracts : Hoare.CONTRACT_ENV)
    (Semantic : SEMANTIC_LEAF_CONTRACTS Contracts).
Module Structural := StructuralValidity Contracts.
Import Translation.Assertions.

Lemma predicate_unfold_rule_valid {Γ F Δ} (node : node_id) predicate arguments
    (store : symbolic_store Γ F Δ) body current_mask :
  Contracts.instantiated_predicate Γ F Δ (Logic.predicate_args predicate)
    predicate (Hoare.symbolize_expr_list store arguments) body ->
  Structural.semantically_valid Semantic.predicates
    (AAnd (AStack store)
      (APredicate predicate (Hoare.symbolize_expr_list store arguments)))
    (TPredicateUnfold node predicate arguments) current_mask current_mask
    (AAnd (AStack store) body).
Proof.
  intros Hinst runtime formals binders atoms.
  unfold StatementWP.Interface.statement_wp, StatementWP.statement_wp.
  simpl. unfold Primitives.leaf_wp, leaf_wp.
  rewrite decide_True; last reflexivity. simpl.
  iIntros "[Hstack Hpredicate]". iFrame "Hstack".
  rewrite (Semantic.predicate_instantiation_valid runtime formals binders atoms
    predicate (Hoare.symbolize_expr_list store arguments) body Hinst).
  iExact "Hpredicate".
Qed.

Lemma predicate_fold_rule_valid {Γ F Δ} (node : node_id) predicate arguments
    (store : symbolic_store Γ F Δ) body current_mask :
  Contracts.instantiated_predicate Γ F Δ (Logic.predicate_args predicate)
    predicate (Hoare.symbolize_expr_list store arguments) body ->
  Structural.semantically_valid Semantic.predicates
    (AAnd (AStack store) body)
    (TPredicateFold node predicate arguments) current_mask current_mask
    (AAnd (AStack store)
      (APredicate predicate (Hoare.symbolize_expr_list store arguments))).
Proof.
  intros Hinst runtime formals binders atoms.
  unfold StatementWP.Interface.statement_wp, StatementWP.statement_wp.
  simpl. unfold Primitives.leaf_wp, leaf_wp.
  rewrite decide_True; last reflexivity. simpl.
  iIntros "[Hstack Hbody]". iFrame "Hstack".
  fold (VSemantics.S.interp_assertion (Semantic.predicates atoms) runtime formals
    binders atoms
    (APredicate predicate (Hoare.symbolize_expr_list store arguments))).
  rewrite -(Semantic.predicate_instantiation_valid runtime formals binders atoms
    predicate (Hoare.symbolize_expr_list store arguments) body Hinst).
  iExact "Hbody".
Qed.

Lemma ghost_update_rule_valid {Γ F Δ} (node : node_id)
    (store : symbolic_store Γ F Δ) field base old_value new_value current_mask :
  Contracts.valid_ghost_update F Δ field
    (Hoare.symbolize_expr store old_value)
    (Hoare.symbolize_expr store new_value) ->
  Structural.semantically_valid Semantic.predicates
    (AAnd (AStack store)
      (AOwn field (Hoare.symbolize_expr store base)
        (Hoare.symbolize_expr store old_value)))
    (TGhostUpdate node field base old_value new_value) current_mask current_mask
    (AAnd (AStack store)
      (AOwn field (Hoare.symbolize_expr store base)
        (Hoare.symbolize_expr store new_value))).
Proof.
  intros Hvalid runtime formals binders atoms.
  unfold StatementWP.Interface.statement_wp, StatementWP.statement_wp.
  simpl. unfold Primitives.leaf_wp, leaf_wp.
  rewrite decide_True; last reflexivity. simpl.
  iIntros "[Hstack Hown]".
  iDestruct "Hown" as (location old_chunk) "(%Hlocation & %Hold & Hown)".
  destruct (interp_expr_total formals binders atoms
    (Hoare.symbolize_expr store new_value)) as [new_chunk Hnew].
  iMod (Semantic.ghost_update_valid field
    (Hoare.symbolize_expr store old_value)
    (Hoare.symbolize_expr store new_value) formals binders atoms old_chunk
    new_chunk location current_mask Hvalid Hold Hnew with "Hown") as "Hown".
  iModIntro. iFrame "Hstack". iExists location, new_chunk.
  iFrame. done.
Qed.

End NonPhysicalValidity.

Module Type SEMANTIC_CONTROL_CONTRACTS (Contracts : Hoare.CONTRACT_ENV)
    (Leaf : SEMANTIC_LEAF_CONTRACTS Contracts).
  Definition predicates : atom_env -> VSemantics.S.predicate_semantics :=
    Leaf.predicates.
  Parameter invariant_open_valid : forall {Γ F Δ}
      (runtime : Model.stack_context Γ) (formals : formal_env F)
      (binders : binder_env Δ) (atoms : atom_env) node invariant arguments
      (store : symbolic_store Γ F Δ) body current_mask,
    invariant ∈ current_mask ->
    Contracts.instantiated_invariant Γ F Δ (Logic.invariant_args invariant)
      invariant (Hoare.symbolize_expr_list store arguments) body ->
    VSemantics.S.interp_assertion (predicates atoms) runtime formals binders atoms
      (AAnd (AStack store)
        (AInvariant invariant (Hoare.symbolize_expr_list store arguments))) ⊢
    Operations.operation_wp Γ runtime (TUnfold node invariant arguments)
      current_mask (current_mask ∖ {[invariant]})
      (VSemantics.S.interp_assertion (predicates atoms) runtime formals binders atoms
        (AAnd (AStack store) body)).
  Parameter invariant_close_valid : forall {Γ F Δ}
      (runtime : Model.stack_context Γ) (formals : formal_env F)
      (binders : binder_env Δ) (atoms : atom_env) node invariant arguments
      (store : symbolic_store Γ F Δ) body current_mask,
    Contracts.instantiated_invariant Γ F Δ (Logic.invariant_args invariant)
      invariant (Hoare.symbolize_expr_list store arguments) body ->
    VSemantics.S.interp_assertion (predicates atoms) runtime formals binders atoms
      (AAnd (AStack store) body) ⊢
    Operations.operation_wp Γ runtime (TFold node invariant arguments)
      current_mask (current_mask ∪ {[invariant]})
      (VSemantics.S.interp_assertion (predicates atoms) runtime formals binders atoms
        (AAnd (AStack store)
          (AInvariant invariant
            (Hoare.symbolize_expr_list store arguments)))).
  Parameter call_discard_valid : forall {Γ F Δ args t}
      (runtime : Model.stack_context Γ) (formals : formal_env F)
      (binders : binder_env Δ) (atoms : atom_env) node procedure arguments
      (store : symbolic_store Γ F Δ) contract_pre
      (contract_post : assertion Γ F (t :: Δ)) current_mask,
    Contracts.instantiated_pre Γ F Δ args procedure
      (Hoare.symbolize_expr_list store arguments) contract_pre ->
    Contracts.instantiated_post_value Γ F (t :: Δ) args t procedure
      (weaken_expr_list (Hoare.symbolize_expr_list store arguments))
      (ERef (RefBound MHere)) contract_post ->
    Contracts.required_mask procedure ⊆ current_mask ->
    VSemantics.S.interp_assertion (predicates atoms) runtime formals binders atoms
      (AAnd (AStack store) contract_pre) ⊢
    Operations.operation_wp Γ runtime
      (TCall node procedure arguments (@CTDiscard Γ t)) current_mask
      (current_mask ∪ Contracts.granted_mask procedure)
      (VSemantics.S.interp_assertion (predicates atoms) runtime formals binders atoms
        (AExists t (AAnd (AStack (weaken_store store)) contract_post))).
  Parameter call_store_valid : forall {Γ F Δ args t}
      (runtime : Model.stack_context Γ) (formals : formal_env F)
      (binders : binder_env Δ) (atoms : atom_env) node procedure arguments
      (store : symbolic_store Γ F Δ) (target : pvar Γ t) contract_pre
      (contract_post : assertion Γ F (t :: Δ)) current_mask,
    Contracts.instantiated_pre Γ F Δ args procedure
      (Hoare.symbolize_expr_list store arguments) contract_pre ->
    Contracts.instantiated_post_value Γ F (t :: Δ) args t procedure
      (weaken_expr_list (Hoare.symbolize_expr_list store arguments))
      (ERef (RefBound MHere)) contract_post ->
    Contracts.required_mask procedure ⊆ current_mask ->
    VSemantics.S.interp_assertion (predicates atoms) runtime formals binders atoms
      (AAnd (AStack store) contract_pre) ⊢
    Operations.operation_wp Γ runtime
      (TCall node procedure arguments (CTStore target)) current_mask
      (current_mask ∪ Contracts.granted_mask procedure)
      (VSemantics.S.interp_assertion (predicates atoms) runtime formals binders atoms
        (AExists t
          (AAnd (AStack (Hoare.update_store_with_bound store target))
            contract_post))).
  Parameter spawn_valid : forall {Γ F Δ args}
      (runtime : Model.stack_context Γ) (formals : formal_env F)
      (binders : binder_env Δ) (atoms : atom_env) node procedure arguments
      (store : symbolic_store Γ F Δ) contract_pre current_mask,
    Contracts.instantiated_pre Γ F Δ args procedure
      (Hoare.symbolize_expr_list store arguments) contract_pre ->
    Contracts.required_mask procedure ⊆ current_mask ->
    VSemantics.S.interp_assertion (predicates atoms) runtime formals binders atoms
      (AAnd (AStack store) contract_pre) ⊢
    Operations.operation_wp Γ runtime (TSpawn node procedure arguments)
      current_mask current_mask
      (VSemantics.S.interp_assertion (predicates atoms) runtime formals binders atoms
        (AStack store)).
End SEMANTIC_CONTROL_CONTRACTS.

Module ControlValidity (Contracts : Hoare.CONTRACT_ENV)
    (Leaf : SEMANTIC_LEAF_CONTRACTS Contracts)
    (Semantic : SEMANTIC_CONTROL_CONTRACTS Contracts Leaf).
Module Structural := StructuralValidity Contracts.

Lemma atomic_rule_valid {Γ F Δ} (node : node_id)
    (pre post : assertion Γ F Δ) (body : stmt Γ) mask_pre mask_post :
  Contracts.trusted_atomic Γ body ->
  Structural.semantically_valid Semantic.predicates pre body
    mask_pre mask_post post ->
  Structural.semantically_valid Semantic.predicates pre (TAtomic node body)
    mask_pre mask_post post.
Proof.
  intros Htrusted Hbody runtime formals binders atoms. iIntros "Hpre".
  iPoseProof (Hbody runtime formals binders atoms with "Hpre") as "Hbody".
  unfold StatementWP.Interface.statement_wp, StatementWP.statement_wp.
  simpl. iApply (Operations.atomic_intro with "Hbody").
Qed.

Lemma invariant_unfold_rule_valid {Γ F Δ} (node : node_id) invariant arguments
    (store : symbolic_store Γ F Δ) body current_mask :
  invariant ∈ current_mask ->
  Contracts.instantiated_invariant Γ F Δ (Logic.invariant_args invariant)
    invariant (Hoare.symbolize_expr_list store arguments) body ->
  Structural.semantically_valid Semantic.predicates
    (AAnd (AStack store)
      (AInvariant invariant (Hoare.symbolize_expr_list store arguments)))
    (TUnfold node invariant arguments) current_mask
    (current_mask ∖ {[invariant]}) (AAnd (AStack store) body).
Proof.
  intros Hmember Hinst runtime formals binders atoms.
  unfold StatementWP.Interface.statement_wp, StatementWP.statement_wp.
  simpl. apply Semantic.invariant_open_valid; assumption.
Qed.

Lemma invariant_fold_rule_valid {Γ F Δ} (node : node_id) invariant arguments
    (store : symbolic_store Γ F Δ) body current_mask :
  Contracts.instantiated_invariant Γ F Δ (Logic.invariant_args invariant)
    invariant (Hoare.symbolize_expr_list store arguments) body ->
  Structural.semantically_valid Semantic.predicates
    (AAnd (AStack store) body) (TFold node invariant arguments)
    current_mask (current_mask ∪ {[invariant]})
    (AAnd (AStack store)
      (AInvariant invariant (Hoare.symbolize_expr_list store arguments))).
Proof.
  intros Hinst runtime formals binders atoms.
  unfold StatementWP.Interface.statement_wp, StatementWP.statement_wp.
  simpl. apply Semantic.invariant_close_valid. exact Hinst.
Qed.

Lemma call_discard_rule_valid {Γ F Δ args t} (node : node_id) procedure arguments
    (store : symbolic_store Γ F Δ) contract_pre
    (contract_post : assertion Γ F (t :: Δ)) current_mask :
  Contracts.instantiated_pre Γ F Δ args procedure
    (Hoare.symbolize_expr_list store arguments) contract_pre ->
  Contracts.instantiated_post_value Γ F (t :: Δ) args t procedure
    (weaken_expr_list (Hoare.symbolize_expr_list store arguments))
    (ERef (RefBound MHere)) contract_post ->
  Contracts.required_mask procedure ⊆ current_mask ->
  Structural.semantically_valid Semantic.predicates
    (AAnd (AStack store) contract_pre)
    (TCall node procedure arguments (@CTDiscard Γ t)) current_mask
    (current_mask ∪ Contracts.granted_mask procedure)
    (AExists t (AAnd (AStack (weaken_store store)) contract_post)).
Proof.
  intros Hpre Hpost Hmask runtime formals binders atoms.
  unfold StatementWP.Interface.statement_wp, StatementWP.statement_wp.
  simpl. apply Semantic.call_discard_valid; assumption.
Qed.

Lemma call_store_rule_valid {Γ F Δ args t} (node : node_id) procedure arguments
    (store : symbolic_store Γ F Δ) (target : pvar Γ t) contract_pre
    (contract_post : assertion Γ F (t :: Δ)) current_mask :
  Contracts.instantiated_pre Γ F Δ args procedure
    (Hoare.symbolize_expr_list store arguments) contract_pre ->
  Contracts.instantiated_post_value Γ F (t :: Δ) args t procedure
    (weaken_expr_list (Hoare.symbolize_expr_list store arguments))
    (ERef (RefBound MHere)) contract_post ->
  Contracts.required_mask procedure ⊆ current_mask ->
  Structural.semantically_valid Semantic.predicates
    (AAnd (AStack store) contract_pre)
    (TCall node procedure arguments (CTStore target)) current_mask
    (current_mask ∪ Contracts.granted_mask procedure)
    (AExists t
      (AAnd (AStack (Hoare.update_store_with_bound store target))
        contract_post)).
Proof.
  intros Hpre Hpost Hmask runtime formals binders atoms.
  unfold StatementWP.Interface.statement_wp, StatementWP.statement_wp.
  simpl. apply Semantic.call_store_valid; assumption.
Qed.

Lemma spawn_rule_valid {Γ F Δ args} (node : node_id) procedure arguments
    (store : symbolic_store Γ F Δ) contract_pre current_mask :
  Contracts.instantiated_pre Γ F Δ args procedure
    (Hoare.symbolize_expr_list store arguments) contract_pre ->
  Contracts.required_mask procedure ⊆ current_mask ->
  Structural.semantically_valid Semantic.predicates
    (AAnd (AStack store) contract_pre) (TSpawn node procedure arguments)
    current_mask current_mask (AStack store).
Proof.
  intros Hpre Hmask runtime formals binders atoms.
  unfold StatementWP.Interface.statement_wp, StatementWP.statement_wp.
  simpl. apply Semantic.spawn_valid; assumption.
Qed.

End ControlValidity.

Module FullValidity (Contracts : Hoare.CONTRACT_ENV)
    (Leaf : SEMANTIC_LEAF_CONTRACTS Contracts)
    (Control : SEMANTIC_CONTROL_CONTRACTS Contracts Leaf).
Module Rules := Hoare.LogicRules Contracts.
Module Structural := StructuralValidity Contracts.
Module Physical := PhysicalValidity Contracts.
Module Logical := NonPhysicalValidity Contracts Leaf.
Module Controlled := ControlValidity Contracts Leaf Control.

Theorem raven_hoare_triple_valid {Γ F Δ}
    (pre post : assertion Γ F Δ) statement mask_pre mask_post :
  Rules.RavenHoareTriple pre statement mask_pre mask_post post ->
  Structural.semantically_valid Leaf.predicates pre statement
    mask_pre mask_post post.
Proof.
  intro Htriple. induction Htriple;
    eauto using
      Structural.skip_rule_valid,
      Structural.assert_rule_valid,
      Structural.sequence_rule_valid,
      Structural.conditional_rule_valid,
      Structural.frame_rule_valid,
      Structural.consequence_rule_valid,
      Structural.exists_elim_rule_valid,
      Structural.exists_preserve_rule_valid.
  - apply (Physical.assignment_rule_valid Leaf.predicates).
  - apply (Physical.field_read_rule_valid Leaf.predicates).
  - apply (Physical.field_write_rule_valid Leaf.predicates).
  - apply (Physical.allocation_rule_valid Leaf.predicates). exact H.
  - apply Logical.ghost_update_rule_valid. exact H.
  - eapply Controlled.atomic_rule_valid; eauto.
  - eapply Controlled.call_discard_rule_valid; eauto.
  - eapply Controlled.call_store_rule_valid; eauto.
  - eapply Controlled.invariant_unfold_rule_valid; eauto.
  - eapply Controlled.invariant_fold_rule_valid; eauto.
  - eapply Logical.predicate_unfold_rule_valid; eauto.
  - eapply Logical.predicate_fold_rule_valid; eauto.
  - eapply Controlled.spawn_rule_valid; eauto.
Qed.

End FullValidity.

End ConcreteExecution.

Module Type GENERIC_INVARIANT_REGION_OPERATIONS
    (Resources : RUNTIME_RESOURCES)
    (Operations : CONTROL_OPERATIONS Resources).
  Module Model := Operations.Model.
  Module Atomicity := GenericRegions.Atomicity.
  Local Notation iProp := (iProp Resources.Σ).
  Parameter operation_wp : forall Γ, Model.stack_context Γ ->
    Model.ambient_mask -> Atomicity.analysis_state -> stmt Γ -> Atomicity.analysis_state ->
    iProp -> iProp.
  Parameter operation_mono : forall Γ runtime ambient entry statement exit P Q,
    (P ⊢ Q) -> operation_wp Γ runtime ambient entry statement exit P ⊢
      operation_wp Γ runtime ambient entry statement exit Q.
  Parameter operation_frame : forall Γ runtime ambient entry statement exit P R,
    operation_wp Γ runtime ambient entry statement exit P ∗ R ⊢
      operation_wp Γ runtime ambient entry statement exit (P ∗ R).
End GENERIC_INVARIANT_REGION_OPERATIONS.

Module FancyUpdateInvariantRegionOperations (Resources : RUNTIME_RESOURCES)
    (Operations : CONTROL_OPERATIONS Resources)
    <: GENERIC_INVARIANT_REGION_OPERATIONS Resources Operations.
Module Model := Operations.Model.
Module Atomicity := GenericRegions.Atomicity.
Local Notation iProp := (iProp Resources.Σ).
Local Existing Instance Model.concrete_irisG.

Definition operation_wp {Γ} (_ : Model.stack_context Γ) (ambient : Model.ambient_mask)
    (entry : Atomicity.analysis_state) (statement : stmt Γ)
    (exit : Atomicity.analysis_state) (post : iProp) : iProp :=
  match statement with
  | TUnfold _ _ _ | TFold _ _ _ =>
      (|={Model.active_runtime_mask ambient entry,
           Model.active_runtime_mask ambient exit}=> post)%I
  | _ => False%I
  end.

Lemma operation_mono Γ runtime ambient entry statement exit P Q :
  (P ⊢ Q) -> @operation_wp Γ runtime ambient entry statement exit P ⊢
    @operation_wp Γ runtime ambient entry statement exit Q.
Proof.
  intros HPQ. unfold operation_wp. destruct statement; simpl; try reflexivity.
  all: iIntros "HP"; iMod "HP"; iModIntro; iApply HPQ; iExact "HP".
Qed.

Lemma operation_frame Γ runtime ambient entry statement exit P R :
  @operation_wp Γ runtime ambient entry statement exit P ∗ R ⊢
    @operation_wp Γ runtime ambient entry statement exit (P ∗ R).
Proof.
  unfold operation_wp. destruct statement; simpl;
    try (iIntros "[H _]"; done).
  all: iIntros "[HP HR]"; iMod "HP"; iModIntro; iFrame.
Qed.
End FancyUpdateInvariantRegionOperations.

(** Concrete operational implementation of every generic region primitive
    except invariant access.  The latter is kept separate so it cannot be
    accidentally implemented by the old bare two-mask fancy update. *)
Module OperationalGenericRegionPrimitives (Resources : RUNTIME_RESOURCES)
    (Operations : CONTROL_OPERATIONS Resources)
    (InvariantOperations :
      GENERIC_INVARIANT_REGION_OPERATIONS Resources Operations).
Module Execution := ConcreteExecution Resources Operations.
Module Model := Operations.Model.
Module Atomicity := GenericRegions.Atomicity.
Module RegionSemantics := GenericRegions.Semantics Model.
Local Notation iProp := (iProp Resources.Σ).
Local Existing Instance Model.concrete_irisG.

Definition ambient_physical_leaf_wp {Γ} (runtime : Model.stack_context Γ)
    (ambient : coPset) (entry : Atomicity.analysis_state)
    (statement : LegacyLang.runtime_stmt) (post : iProp) : iProp :=
  Model.runtime_wp (Model.active_runtime_mask ambient entry) statement
    (fun result => (⌜result = LegacyLang.LitUnit⌝ ∗ post)%I).

(** Certified-region leaves use the physical mask determined by the ambient
    envelope and the currently open invariants.  Procedure grants only alter
    Raven's logical mask; they do not manufacture an Iris mask transition. *)
Definition ambient_leaf_wp {Γ} (runtime : Model.stack_context Γ)
    (ambient : coPset) (entry : Atomicity.analysis_state)
    (statement : stmt Γ) (post : iProp) : iProp :=
  match statement with
  | TCall _ _ _ _ | TSpawn _ _ _ =>
      match Model.runtime_stmt (Model.runtime_names _ runtime)
          (Model.runtime_stack_id _ runtime) statement with
      | Some runtime_statement =>
          ambient_physical_leaf_wp runtime ambient entry runtime_statement post
      | None => False%I
      end
  | TSkip _ | TAssert _ _ => post
  | TAssign _ target expression =>
      ambient_physical_leaf_wp runtime ambient entry
        (LegacyLang.RTAssign
          (Model.runtime_variable (Model.runtime_names _ runtime) target)
          (Model.runtime_expr (Model.runtime_names _ runtime) expression)
          (Model.runtime_stack_id _ runtime)) post
  | TFieldRead _ field target base =>
      ambient_physical_leaf_wp runtime ambient entry
        (LegacyLang.RTFldRd
          (Model.runtime_variable (Model.runtime_names _ runtime) target)
          (Model.runtime_expr (Model.runtime_names _ runtime) base)
          (Resources.field_name field) (Model.runtime_stack_id _ runtime)) post
  | TFieldWrite _ field base expression =>
      ambient_physical_leaf_wp runtime ambient entry
        (LegacyLang.RTFldWr
          (Model.runtime_expr (Model.runtime_names _ runtime) base)
          (Resources.field_name field)
          (Model.runtime_expr (Model.runtime_names _ runtime) expression)
          (Model.runtime_stack_id _ runtime)) post
  | TAlloc _ target fields =>
      ambient_physical_leaf_wp runtime ambient entry
        (LegacyLang.RTAlloc
          (Model.runtime_variable (Model.runtime_names _ runtime) target)
          (Model.runtime_field_initializers (Model.runtime_names _ runtime) fields)
          (Model.runtime_stack_id _ runtime)) post
  | TGhostUpdate _ _ _ _ _ =>
      (|={Model.active_runtime_mask ambient entry}=> post)%I
  | TPredicateUnfold _ _ _ | TPredicateFold _ _ _ => post
  | _ => False%I
  end.

Lemma ambient_physical_leaf_mono {Γ} runtime ambient entry statement P Q :
  (P ⊢ Q) ->
  ambient_physical_leaf_wp (Γ := Γ) runtime ambient entry statement P ⊢
    ambient_physical_leaf_wp runtime ambient entry statement Q.
Proof.
  intros HPQ. unfold ambient_physical_leaf_wp, Model.runtime_wp.
  iIntros "Hwp". iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult HP]". iSplit; first done.
  iApply HPQ. iExact "HP".
Qed.

Lemma ambient_physical_leaf_frame {Γ} runtime ambient entry statement P R :
  ambient_physical_leaf_wp (Γ := Γ) runtime ambient entry statement P ∗ R ⊢
    ambient_physical_leaf_wp runtime ambient entry statement (P ∗ R).
Proof.
  unfold ambient_physical_leaf_wp, Model.runtime_wp.
  iIntros "[Hwp HR]".
  iPoseProof (@wp_frame_r HasLc LegacyLang.simp_lang Resources.Σ
    Model.concrete_irisG NotStuck (Model.active_runtime_mask ambient entry)
    statement (fun result => (⌜result = LegacyLang.LitUnit⌝ ∗ P)%I) R
    with "[$Hwp $HR]") as "Hwp".
  iApply (wp_mono with "Hwp").
  iIntros (result) "[[%Hresult HP] HR]". iSplit; first done. iFrame.
Qed.

Lemma ambient_leaf_mono {Γ} runtime ambient entry statement P Q :
  (P ⊢ Q) ->
  ambient_leaf_wp (Γ := Γ) runtime ambient entry statement P ⊢
    ambient_leaf_wp runtime ambient entry statement Q.
Proof.
  intros HPQ. unfold ambient_leaf_wp. destruct statement; simpl;
    try destruct target; simpl; try exact HPQ; try reflexivity;
    try (apply ambient_physical_leaf_mono; exact HPQ).
  all: iIntros "HP"; iMod "HP"; iModIntro; iApply HPQ; iExact "HP".
Qed.

Lemma ambient_leaf_frame {Γ} runtime ambient entry statement P R :
  ambient_leaf_wp (Γ := Γ) runtime ambient entry statement P ∗ R ⊢
    ambient_leaf_wp runtime ambient entry statement (P ∗ R).
Proof.
  unfold ambient_leaf_wp. destruct statement; simpl;
    try destruct target; simpl; try reflexivity;
    try apply ambient_physical_leaf_frame; try (iIntros "[H _]"; done).
  all: iIntros "[HP HR]"; iMod "HP"; iModIntro; iFrame.
Qed.

Definition operation_wp {Γ} (runtime : Model.stack_context Γ) (ambient : Model.ambient_mask)
    (entry : Atomicity.analysis_state) (statement : stmt Γ)
    (exit : Atomicity.analysis_state) (post : iProp) : iProp :=
  match RegionSyntax.view statement with
  | TypedAnalysisView.ViewLeaf =>
      ambient_leaf_wp runtime ambient entry statement post
  | TypedAnalysisView.ViewUnfold _ | TypedAnalysisView.ViewFold _ =>
      InvariantOperations.operation_wp Γ runtime ambient entry statement exit post
  | TypedAnalysisView.ViewAtomic body =>
      Operations.atomic_wp Γ runtime body (Atomicity.analysis_mask entry)
        (Atomicity.analysis_mask exit) post
  | _ => False%I
  end.

Definition branch_wp {Γ} (runtime : Model.stack_context Γ) (_ambient : Model.ambient_mask)
    (entry : Atomicity.analysis_state) (statement : stmt Γ)
    (_ _ : Atomicity.analysis_state) (then_wp else_wp : iProp) : iProp :=
  match statement with
  | TIf _ condition _ _ =>
      Execution.branch_wp runtime condition (Atomicity.analysis_mask entry)
        then_wp else_wp
  | _ => False%I
  end.

Module Interface <: RegionSemantics.REGION_PRIMITIVES.
  Definition operation_wp := @operation_wp.
  Definition branch_wp := @branch_wp.

  Lemma operation_mono Γ runtime ambient entry statement exit P Q :
    (P ⊢ Q) -> operation_wp Γ runtime ambient entry statement exit P ⊢
      operation_wp Γ runtime ambient entry statement exit Q.
  Proof.
    intros HPQ. unfold operation_wp, RegionSyntax.view.
    destruct statement; simpl; try exact HPQ; try reflexivity;
      try (apply ambient_leaf_mono; exact HPQ);
      try (apply InvariantOperations.operation_mono; exact HPQ);
      try (apply Operations.atomic_mono; exact HPQ).
  Qed.

  Lemma operation_frame Γ runtime ambient entry statement exit P R :
    operation_wp Γ runtime ambient entry statement exit P ∗ R ⊢
      operation_wp Γ runtime ambient entry statement exit (P ∗ R).
  Proof.
    unfold operation_wp, RegionSyntax.view. destruct statement; simpl;
      try reflexivity; try apply ambient_leaf_frame;
      try apply InvariantOperations.operation_frame;
      try apply Operations.atomic_frame;
      try (iIntros "[H _]"; done).
  Qed.

  Lemma branch_mono Γ runtime ambient entry statement then_exit else_exit P P' Q Q' :
    (P ⊢ P') -> (Q ⊢ Q') ->
    branch_wp Γ runtime ambient entry statement then_exit else_exit P Q ⊢
      branch_wp Γ runtime ambient entry statement then_exit else_exit P' Q'.
  Proof.
    intros HP HQ. unfold branch_wp. destruct statement; simpl; try reflexivity.
    apply Execution.Primitives.branch_mono; assumption.
  Qed.

  Lemma branch_frame Γ runtime ambient entry statement then_exit else_exit P Q R :
    branch_wp Γ runtime ambient entry statement then_exit else_exit P Q ∗ R ⊢
      branch_wp Γ runtime ambient entry statement then_exit else_exit
        (P ∗ R) (Q ∗ R).
  Proof.
    unfold branch_wp. destruct statement; simpl; try (iIntros "[H _]"; done).
    apply Execution.Primitives.branch_frame.
  Qed.
End Interface.

Module Interpreter := RegionSemantics.Interpreter Interface.
End OperationalGenericRegionPrimitives.

Module ConcreteGenericRegionExecution (Resources : RUNTIME_RESOURCES).
  Module Operations := ConcreteControlOperations Resources.
  Module InvariantOperations :=
    FancyUpdateInvariantRegionOperations Resources Operations.
  Module Primitives := OperationalGenericRegionPrimitives Resources Operations
    InvariantOperations.
  Include Primitives.Interpreter.
End ConcreteGenericRegionExecution.

Module Type DEFAULT_SEMANTIC_LEAF_CONTRACTS
    (Resources : RUNTIME_RESOURCES) (Contracts : Hoare.CONTRACT_ENV).
  Module Operations := ConcreteControlOperations Resources.
  Module Execution := ConcreteExecution Resources Operations.
  Include Execution.SEMANTIC_LEAF_CONTRACTS Contracts.
End DEFAULT_SEMANTIC_LEAF_CONTRACTS.


(** Default executable typed semantics: clients proving semantic contracts no
    longer choose a control-operation interpretation. *)
Module ConcreteStatementExecution (Resources : RUNTIME_RESOURCES).
  Module Operations := ConcreteControlOperations Resources.
  Include ConcreteExecution Resources Operations.
End ConcreteStatementExecution.

End Make.
End TypedRuntime.
