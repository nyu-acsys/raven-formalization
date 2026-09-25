From Coq Require Import ClassicalEpsilon FunctionalExtensionality Lia
  Program.Equality.
From stdpp Require Import gmap sets.

From raven_iris.rich_raven_lang Require Import
  typed_normalization_base typed_core typed_analysis_view typed_assertion
  typed_ir typed_runtime.

Module TypedNormalizationConditional.

Module Make (LegacyRAs : ra_base.RA_CONFIG)
    (Logic : TypedAssertion.LOGIC_SIGNATURE).
Include TypedNormalizationBase.Make LegacyRAs Logic.
Import TypedCore TypedIR Runtime IR Core Runtime.Translation.
Import StructuredCertificates.
Module ConditionalNormalizationPrefix (Config : Runtime.RUNTIME_CONFIGURATION)
    (ResourceContracts : Hoare.ResourceHoare.RESOURCE_CONTRACT_ENV_BASE).
(* Only the (non-generative) erasure is needed here.  Applying the full
   [ConcreteModelCore] would mint a second copy of its generative
   records, independent of the runtime model on the soundness path. *)
Module Model := Runtime.RuntimeErasure Config.
Module Certified := Runtime.CertifiedRegions ResourceContracts.
Module Resource := Runtime.Translation.Resource.
(** The single application of the resource calculus's rule functor.  It
    contains inductive families, so it is generative: everything
    downstream projects from here rather than re-applying it. *)
Module ResourceRules :=
  Hoare.ResourceHoare.ResourceRules ResourceContracts.

(** The resource calculus has exactly one stack at every prenex leaf, so
    argument stability no longer needs the legacy recursive search through
    arbitrary assertion syntax. *)


Lemma runtime_stmt_linear_access {Γ} names stack outer_node unfold_node
    body_sequence_node fold_node invariant opening_arguments closing_arguments
    (body : stmt Γ) :
  Model.runtime_stmt names stack
      (TSeq outer_node (TUnfold unfold_node invariant opening_arguments)
        (TSeq body_sequence_node body
          (TFold fold_node invariant closing_arguments))) =
    Model.runtime_stmt names stack body.
Proof.
  simpl. rewrite Model.runtime_seq_noop_r. reflexivity.
Qed.

Lemma runtime_stmt_linear_access_then {Γ} names stack outer_node unfold_node
    body_sequence_node fold_sequence_node fold_node invariant
    opening_arguments closing_arguments (body work : stmt Γ) :
  Model.runtime_stmt names stack
      (TSeq outer_node (TUnfold unfold_node invariant opening_arguments)
        (TSeq body_sequence_node body
          (TSeq fold_sequence_node
            (TFold fold_node invariant closing_arguments) work))) =
    Model.runtime_seq
      (Model.runtime_stmt names stack body)
      (Model.runtime_stmt names stack work).
Proof. reflexivity. Qed.

(** A normalized statement together with the resource derivation and
    structured analyzer certificate that justify it. *)

(* ------------------------------------------------------------------ *)
(** ** The same judgment over resource telescopes

    [normalization_result] above is indexed by [assertion] pre- and
    post-conditions and by the *old* calculus's [RavenResourceTriple].
    This is the same record over [resource_prenex] and the new calculus.
    Three things change, all by typing rather than by side condition:

      - the pre- and post-conditions are telescopes, so a normalization
        step cannot lose, duplicate, or reorder the distinguished stack;
      - the derivations are [ResourceRules.RavenResourceTriple], which has
        no mask indices on the logical judgment;
      - the erasure obligation is unchanged, because normalization is a
        statement-level rewrite and never touches the assertion.

    The analyzer certificate and the runtime-erasure obligation are shared
    verbatim with the assertion-shaped record: normalization is about
    statements, and only the justification changes representation.

    *This record is internal.*  It is the payload the constructors
    compose and the type they are stated at; it carries no footprint or
    access-safety guarantee, so it is not what a producer hands out.
    The three-way division the normalization layer settles on is:

      - [resource_normalization_result] -- internal payload and
        constructor-composition type;
      - [footprinted_resource_normalization_result] -- the externally
        produced, certified result;
      - exactly one generic producer, the footprinted traversal.

    There is deliberately no way to inject an unfootprinted
    normalization from outside.  Such a path would bypass precisely the
    two obligations the procedure theorem consumes -- footprint
    domination and access safety -- which is why the hand-supply
    evidence layer was removed rather than kept as an extension point. *)
Record resource_normalization_result {Γ F Δ}
    (cost : GenericRegions.Atomicity.cost_model)
    (entry exit : GenericRegions.Atomicity.analysis_state)
    (pre post : Resource.resource_prenex Γ F Δ) (source : stmt Γ)
    (source_derivation : ResourceRules.RavenResourceTriple pre source post)
    (source_certificate :
      GenericRegions.Atomicity.analysis_certificate cost Γ entry source exit)
    : Type := {
  resource_normalized_statement : stmt Γ;
  resource_normalization_target_derivation :
    ResourceRules.RavenResourceTriple pre resource_normalized_statement post;
  resource_normalization_target_certificate :
    structured_certificate cost Γ entry resource_normalized_statement exit;
  resource_normalization_runtime_erasure : forall names stack,
    Model.runtime_stmt names stack source =
      Model.runtime_stmt names stack resource_normalized_statement;
}.

Arguments resource_normalized_statement {_ _ _} {_ _ _ _ _ _ _ _} _.
Arguments resource_normalization_target_derivation
  {_ _ _} {_ _ _ _ _ _ _ _} _.
Arguments resource_normalization_target_certificate
  {_ _ _} {_ _ _ _ _ _ _ _} _.
Arguments resource_normalization_runtime_erasure
  {_ _ _} {_ _ _ _ _ _ _ _} _ _ _.

(** The identity normalization: any source statement normalizes to itself
    once its analyzer certificate is already structured.  This is the base
    case every later constructor composes with, and it is what makes the
    record inhabited independently of the rewrite library. *)
Definition resource_normalization_identity {Γ F Δ}
    {cost entry exit} {pre post : Resource.resource_prenex Γ F Δ}
    {source : stmt Γ}
    (source_derivation : ResourceRules.RavenResourceTriple pre source post)
    (source_certificate :
      GenericRegions.Atomicity.analysis_certificate cost Γ entry source exit)
    (structured : structured_certificate cost Γ entry source exit) :
    resource_normalization_result cost entry exit pre post source
      source_derivation source_certificate :=
  {| resource_normalized_statement := source;
     resource_normalization_target_derivation := source_derivation;
     resource_normalization_target_certificate := structured;
     resource_normalization_runtime_erasure :=
       fun names stack => eq_refl |}.

(** Footprint- and atomicity-strengthened form, mirroring
    [footprinted_normalization_result].

    This is the *external* result type: the only thing the generic
    producer returns and the only thing the procedure boundary accepts.
    Its two extra fields are exactly what
    [term_resource_certified_body_source_valid] needs in order to
    discharge structured validity without a premise. *)
Record footprinted_resource_normalization_result {Γ F Δ}
    (cost : GenericRegions.Atomicity.cost_model)
    (entry exit : GenericRegions.Atomicity.analysis_state)
    (pre post : Resource.resource_prenex Γ F Δ) (source : stmt Γ)
    (source_derivation : ResourceRules.RavenResourceTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit) : Type := {
  footprinted_resource_normalization :
    @resource_normalization_result Γ F Δ cost entry exit pre post source
      source_derivation source_certificate;
  footprinted_resource_normalization_subset :
    structured_certificate_footprint
      footprinted_resource_normalization.(
        resource_normalization_target_certificate) ⊆
    GenericRegions.Atomicity.certificate_footprint source_certificate;
  footprinted_resource_normalization_safe :
    GenericRegions.Atomicity.analysis_in_atomic entry = false ->
    structured_accesses_outside_atomic
      footprinted_resource_normalization.(
        resource_normalization_target_certificate);
}.

Arguments footprinted_resource_normalization {_ _ _} {_ _ _ _ _ _ _ _} _.
Arguments footprinted_resource_normalization_subset {_ _ _}
  {_ _ _ _ _ _ _ _} _ _ _.
Arguments footprinted_resource_normalization_safe {_ _ _}
  {_ _ _ _ _ _ _ _} _ _.

(** Public restricted-normalization contract.  The executable worker chooses
    only the target syntax; the existence of its resource derivation and
    structured certificate is proved in [Prop].  Consequently successful
    analysis never has to reduce a Hoare derivation, alignment witness, or
    semantic proof. *)
Definition restricted_footprinted_resource_normalization_exists
    {Γ F Δ cost entry exit pre post source}
    (derivation : ResourceRules.RavenResourceTriple pre source post)
    (certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit) : Prop :=
  exists result : @footprinted_resource_normalization_result Γ F Δ cost
      entry exit pre post source derivation certificate,
    restricted_analyze_and_normalize source =
      Some (resource_normalized_statement
        result.(footprinted_resource_normalization)).


(** *** Producing a [resource_normalization_result]

    The source-to-target seam.  [resource_normalization_identity] only
    says the record is inhabited; this is the first constructor that
    actually normalizes, taking an explicit `unfold; body; fold` source
    together with its ordinary analyzer certificate and returning the
    matched [TInvAccess] target with a structured certificate.

    Compare [normalization_close_one_marker_with_results]: the
    [Contracts.instantiated_invariant … invariant_body] premise is gone,
    because [RTInvAccess] takes the opened body to *be*
    [instantiated_invariant] applied to the access arguments. *)
Definition resource_normalization_close_one_marker_target
    {Γ F Δ cost entry opened inner}
    {pre post : Resource.resource_prenex Γ F Δ} {source : stmt Γ}
    invariant (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (body : stmt Γ)
    (source_derivation : ResourceRules.RavenResourceTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source (GenericRegions.Atomicity.fold_invariant invariant inner))
    (Hopen : GenericRegions.Atomicity.open_invariant invariant entry =
      inr opened)
    (Hbody_certificate : structured_certificate cost Γ opened body inner)
    (Hopen_preserved : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open opened)
    (Htarget : ResourceRules.RavenResourceTriple pre
      (TInvAccess invariant arguments body) post)
    (Herasure : forall names stack,
      Model.runtime_stmt names stack source =
        Model.runtime_stmt names stack body) :
  @resource_normalization_result Γ F Δ cost entry
    (GenericRegions.Atomicity.fold_invariant invariant inner)
    pre post source source_derivation source_certificate :=
  {| resource_normalized_statement := TInvAccess invariant arguments body;
     resource_normalization_target_derivation := Htarget;
     resource_normalization_target_certificate :=
       StructuredInvAccess cost Γ entry invariant arguments body opened inner
         Hopen Hbody_certificate Hopen_preserved;
     resource_normalization_runtime_erasure := Herasure |}.

(** Continued form of the target-oriented matched-access constructor.  The
    derivation cut is performed entirely before this boundary: [Htarget]
    already contains every logical telescope and structural wrapper around
    the complete access-plus-continuation statement.  Consequently this
    constructor only assembles syntax, the structured certificate, and
    runtime erasure; it never inspects the derivation. *)
Definition resource_normalization_close_one_marker_target_then
    {Γ F Δ cost entry opened inner exit}
    {pre post : Resource.resource_prenex Γ F Δ}
    invariant (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    outer_node unfold_node body_sequence_node fold_sequence_node fold_node
    (body work normalized_work : stmt Γ)
    (source_derivation : ResourceRules.RavenResourceTriple pre
      (TSeq outer_node (TUnfold unfold_node invariant arguments)
        (TSeq body_sequence_node body
          (TSeq fold_sequence_node (TFold fold_node invariant arguments)
            work))) post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry
      (TSeq outer_node (TUnfold unfold_node invariant arguments)
        (TSeq body_sequence_node body
          (TSeq fold_sequence_node (TFold fold_node invariant arguments)
            work))) exit)
    (Hopen : GenericRegions.Atomicity.open_invariant invariant entry =
      inr opened)
    (Hbody_certificate : structured_certificate cost Γ opened body inner)
    (Hopen_preserved : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open opened)
    (Htarget : ResourceRules.RavenResourceTriple pre
      (TSeq outer_node (TInvAccess invariant arguments body) normalized_work)
      post)
    (Hwork_certificate : structured_certificate cost Γ
      (GenericRegions.Atomicity.fold_invariant invariant inner)
      normalized_work exit)
    (Hwork_erasure : forall names stack,
      Model.runtime_stmt names stack work =
        Model.runtime_stmt names stack normalized_work) :
  @resource_normalization_result Γ F Δ cost entry exit pre post
    (TSeq outer_node (TUnfold unfold_node invariant arguments)
      (TSeq body_sequence_node body
        (TSeq fold_sequence_node (TFold fold_node invariant arguments) work)))
    source_derivation source_certificate.
Proof.
  refine {| resource_normalized_statement :=
      TSeq outer_node (TInvAccess invariant arguments body) normalized_work;
    resource_normalization_target_derivation := Htarget;
    resource_normalization_target_certificate :=
      StructuredSequence cost Γ entry outer_node _
        (GenericRegions.Atomicity.fold_invariant invariant inner) _ exit
        (StructuredInvAccess cost Γ entry invariant arguments body opened inner
          Hopen Hbody_certificate Hopen_preserved)
        Hwork_certificate |}.
  intros names stack. rewrite runtime_stmt_linear_access_then.
  now rewrite Hwork_erasure.
Defined.

(** Raw analyzer certificate for the general continued-access source.  This
    is the non-atomic counterpart of the earlier baseline constructor: the
    body and continuation certificates are arbitrary analyzer results. *)
Definition resource_access_then_source_certificate
    {Γ cost entry opened inner exit} invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (outer_node unfold_node body_sequence_node fold_sequence_node fold_node :
      node_id)
    (body work : stmt Γ)
    (body_analysis : GenericRegions.Atomicity.analysis_certificate cost Γ
      opened body inner)
    (work_analysis : GenericRegions.Atomicity.analysis_certificate cost Γ
      (GenericRegions.Atomicity.fold_invariant invariant inner) work exit)
    (Hopen : GenericRegions.Atomicity.open_invariant invariant entry =
      inr opened) :
  GenericRegions.Atomicity.analysis_certificate cost Γ entry
    (TSeq outer_node (TUnfold unfold_node invariant arguments)
      (TSeq body_sequence_node body
        (TSeq fold_sequence_node (TFold fold_node invariant arguments) work)))
    exit :=
  GenericRegions.Atomicity.CertSequence cost Γ entry
    (TSeq outer_node (TUnfold unfold_node invariant arguments)
      (TSeq body_sequence_node body
        (TSeq fold_sequence_node (TFold fold_node invariant arguments) work)))
    (TUnfold unfold_node invariant arguments) opened
    (TSeq body_sequence_node body
      (TSeq fold_sequence_node (TFold fold_node invariant arguments) work))
    exit eq_refl
    (GenericRegions.Atomicity.CertUnfold cost Γ entry
      (TUnfold unfold_node invariant arguments) invariant opened eq_refl Hopen)
    (GenericRegions.Atomicity.CertSequence cost Γ opened
      (TSeq body_sequence_node body
        (TSeq fold_sequence_node (TFold fold_node invariant arguments) work))
      body inner
      (TSeq fold_sequence_node (TFold fold_node invariant arguments) work)
      exit eq_refl body_analysis
      (GenericRegions.Atomicity.CertSequence cost Γ inner
        (TSeq fold_sequence_node (TFold fold_node invariant arguments) work)
        (TFold fold_node invariant arguments)
        (GenericRegions.Atomicity.fold_invariant invariant inner) work exit
        eq_refl
        (GenericRegions.Atomicity.CertFold cost Γ inner
          (TFold fold_node invariant arguments) invariant eq_refl)
        work_analysis)).

(** Footprinted package for the general continued-access target.  Its
    premises are exactly the recursively available facts for the body and
    continuation; no fact about the Hoare proof is required. *)
Definition resource_normalization_close_one_marker_target_then_footprinted
    {Γ F Δ cost entry opened inner exit}
    {pre post : Resource.resource_prenex Γ F Δ}
    invariant (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    outer_node unfold_node body_sequence_node fold_sequence_node fold_node
    (body work normalized_work : stmt Γ)
    (body_analysis : GenericRegions.Atomicity.analysis_certificate cost Γ
      opened body inner)
    (work_analysis : GenericRegions.Atomicity.analysis_certificate cost Γ
      (GenericRegions.Atomicity.fold_invariant invariant inner) work exit)
    (Hopen : GenericRegions.Atomicity.open_invariant invariant entry =
      inr opened)
    (Hbody_certificate : structured_certificate cost Γ opened body inner)
    (Hopen_preserved : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open opened)
    (Htarget : ResourceRules.RavenResourceTriple pre
      (TSeq outer_node (TInvAccess invariant arguments body) normalized_work)
      post)
    (Hwork_certificate : structured_certificate cost Γ
      (GenericRegions.Atomicity.fold_invariant invariant inner)
      normalized_work exit)
    (Hwork_erasure : forall names stack,
      Model.runtime_stmt names stack work =
        Model.runtime_stmt names stack normalized_work)
    (Hbody_subset : structured_certificate_footprint Hbody_certificate ⊆
      GenericRegions.Atomicity.certificate_footprint body_analysis)
    (Hwork_subset : structured_certificate_footprint Hwork_certificate ⊆
      GenericRegions.Atomicity.certificate_footprint work_analysis)
    (Hbody_safe : GenericRegions.Atomicity.analysis_in_atomic opened = false ->
      structured_accesses_outside_atomic Hbody_certificate)
    (Hwork_safe : GenericRegions.Atomicity.analysis_in_atomic
        (GenericRegions.Atomicity.fold_invariant invariant inner) = false ->
      structured_accesses_outside_atomic Hwork_certificate)
    (source_derivation : ResourceRules.RavenResourceTriple pre
      (TSeq outer_node (TUnfold unfold_node invariant arguments)
        (TSeq body_sequence_node body
          (TSeq fold_sequence_node (TFold fold_node invariant arguments) work)))
      post) :
  let source_certificate := resource_access_then_source_certificate invariant
    arguments outer_node unfold_node body_sequence_node fold_sequence_node
    fold_node body work body_analysis work_analysis Hopen in
  @footprinted_resource_normalization_result Γ F Δ cost entry exit pre post
    (TSeq outer_node (TUnfold unfold_node invariant arguments)
      (TSeq body_sequence_node body
        (TSeq fold_sequence_node (TFold fold_node invariant arguments) work)))
    source_derivation source_certificate.
Proof.
  intros source_certificate.
  refine {| footprinted_resource_normalization :=
    resource_normalization_close_one_marker_target_then invariant arguments
      outer_node unfold_node body_sequence_node fold_sequence_node fold_node
      body work normalized_work source_derivation source_certificate Hopen
      Hbody_certificate Hopen_preserved Htarget Hwork_certificate
      Hwork_erasure |}.
  - intros marker Hmember.
    specialize (Hbody_subset marker). specialize (Hwork_subset marker).
    simpl in Hmember |- *.
    set_unfold.
    tauto.
  - intros Hentry. cbn [resource_normalization_close_one_marker_target_then
      structured_accesses_outside_atomic]. split.
    + split; [exact Hentry |]. apply Hbody_safe.
      rewrite (GenericRegions.Atomicity.open_invariant_preserves_in_atomic
        invariant entry opened Hopen). exact Hentry.
    + apply Hwork_safe.
      unfold GenericRegions.Atomicity.fold_invariant.
      destruct (bool_decide
        (invariant ∈ GenericRegions.Atomicity.analysis_open inner)); simpl.
      all: rewrite (GenericRegions.Atomicity.analysis_certificate_preserves_in_atomic
        body_analysis).
      all: rewrite (GenericRegions.Atomicity.open_invariant_preserves_in_atomic
        invariant entry opened Hopen); exact Hentry.
Defined.

(** Worker-indexed continued-access assembly for the completeness induction.
    The recursive continuation result is consumed at the exact fuel supplied
    by the parent run, avoiding any fuel-irrelevance side theorem. *)
Lemma footprinted_resource_normalization_continued_access_from_worker
    {Γ F Δ cost entry opened inner exit}
    {pre middle post : Resource.resource_prenex Γ F Δ}
    invariant (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    outer_node unfold_node body_sequence_node fold_sequence_node fold_node
    (body work normalized : stmt Γ)
    (body_analysis : GenericRegions.Atomicity.analysis_certificate cost Γ
      opened body inner)
    (work_derivation : ResourceRules.RavenResourceTriple middle work post)
    (work_analysis : GenericRegions.Atomicity.analysis_certificate cost Γ
      (GenericRegions.Atomicity.fold_invariant invariant inner) work exit)
    (work_result : @footprinted_resource_normalization_result Γ F Δ cost
      (GenericRegions.Atomicity.fold_invariant invariant inner) exit
      middle post work work_derivation work_analysis)
    (Hopen : GenericRegions.Atomicity.open_invariant invariant entry =
      inr opened)
    (Hbody_certificate : structured_certificate cost Γ opened body inner)
    (Hopen_preserved : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open opened)
    (Htarget : ResourceRules.RavenResourceTriple pre
      (TSeq outer_node (TInvAccess invariant arguments body)
        (resource_normalized_statement
          work_result.(footprinted_resource_normalization))) post)
    (Hbody_subset : structured_certificate_footprint Hbody_certificate ⊆
      GenericRegions.Atomicity.certificate_footprint body_analysis)
    (Hbody_safe : GenericRegions.Atomicity.analysis_in_atomic opened = false ->
      structured_accesses_outside_atomic Hbody_certificate)
    (source_derivation : ResourceRules.RavenResourceTriple pre
      (TSeq outer_node (TUnfold unfold_node invariant arguments)
        (TSeq body_sequence_node body
          (TSeq fold_sequence_node (TFold fold_node invariant arguments) work)))
      post)
    fuel
    (Hboundary : restricted_access_boundary_check arguments arguments body =
      true)
    (Hwork_worker : restricted_normalize_statement_fuel fuel work =
      Some (resource_normalized_statement
        work_result.(footprinted_resource_normalization)))
    (Hworker : restricted_normalize_statement_fuel (S fuel)
      (TSeq outer_node (TUnfold unfold_node invariant arguments)
        (TSeq body_sequence_node body
          (TSeq fold_sequence_node (TFold fold_node invariant arguments) work)))
      = Some normalized) :
  let source_certificate := resource_access_then_source_certificate invariant
    arguments outer_node unfold_node body_sequence_node fold_sequence_node
    fold_node body work body_analysis work_analysis Hopen in
  exists result : @footprinted_resource_normalization_result Γ F Δ cost
      entry exit pre post
      (TSeq outer_node (TUnfold unfold_node invariant arguments)
        (TSeq body_sequence_node body
          (TSeq fold_sequence_node (TFold fold_node invariant arguments) work)))
      source_derivation source_certificate,
    resource_normalized_statement
      result.(footprinted_resource_normalization) = normalized.
Proof.
  intros source_certificate.
  pose (result :=
    resource_normalization_close_one_marker_target_then_footprinted
      invariant arguments outer_node unfold_node body_sequence_node
      fold_sequence_node fold_node body work
      (resource_normalized_statement
        work_result.(footprinted_resource_normalization))
      body_analysis work_analysis Hopen Hbody_certificate Hopen_preserved
      Htarget
      (resource_normalization_target_certificate
        work_result.(footprinted_resource_normalization))
      (resource_normalization_runtime_erasure
        work_result.(footprinted_resource_normalization))
      Hbody_subset
      work_result.(footprinted_resource_normalization_subset)
      Hbody_safe work_result.(footprinted_resource_normalization_safe)
      source_derivation).
  exists result.
  pose proof (restricted_normalize_continued_access fuel outer_node unfold_node
    body_sequence_node fold_sequence_node fold_node invariant arguments body
    work _ Hboundary Hwork_worker) as Hnormalized.
  rewrite Hworker in Hnormalized. inversion Hnormalized. reflexivity.
Qed.


(** Complete base case for the continued matched-access cut.  All logical
    work at the fold is explicit in [Hclosure] and [Hcut]; this lemma builds
    the complete normalized target and immediately installs it in the
    footprinted worker result.  Structural wrappers around the source belong
    outside this seam and are transported by the existing normalization
    constructors. *)


(** Structural composition of two resource normalizations across a
    source sequence node.  Mirrors [normalization_sequence]; the source
    node is preserved and the two erasure equations compose. *)
Definition resource_normalization_sequence
    {Γ F Δ cost entry middle exit}
    {pre middle_prenex post : Resource.resource_prenex Γ F Δ}
    {first second : stmt Γ} node
    (first_derivation :
      ResourceRules.RavenResourceTriple pre first middle_prenex)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry first middle)
    (first_normalization : @resource_normalization_result Γ F Δ cost entry
      middle pre middle_prenex first first_derivation first_certificate)
    (second_derivation :
      ResourceRules.RavenResourceTriple middle_prenex second post)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      middle second exit)
    (second_normalization : @resource_normalization_result Γ F Δ cost middle
      exit middle_prenex post second second_derivation second_certificate)
    (view : RegionSyntax.view (TSeq node first second) =
      TypedAnalysisView.ViewSequence first second) :
  let source := TSeq node first second in
  let source_derivation := ResourceRules.RTSeq node pre middle_prenex post
    first second first_derivation second_derivation in
  let source_certificate := GenericRegions.Atomicity.CertSequence cost Γ
    entry source first middle second exit view first_certificate
      second_certificate in
  @resource_normalization_result Γ F Δ cost entry exit pre post source
    source_derivation source_certificate.
Proof.
  simpl.
  refine {| resource_normalized_statement := TSeq node
      first_normalization.(resource_normalized_statement)
      second_normalization.(resource_normalized_statement);
    resource_normalization_target_derivation :=
      ResourceRules.RTSeq node pre middle_prenex post _ _
        first_normalization.(resource_normalization_target_derivation)
        second_normalization.(resource_normalization_target_derivation);
    resource_normalization_target_certificate :=
      StructuredSequence cost Γ entry node _ middle _ exit
        first_normalization.(resource_normalization_target_certificate)
        second_normalization.(resource_normalization_target_certificate) |}.
  intros names stack. simpl.
  rewrite (first_normalization.(resource_normalization_runtime_erasure)
    names stack).
  rewrite (second_normalization.(resource_normalization_runtime_erasure)
    names stack).
  reflexivity.
Defined.

(** The baseline terminal pattern *with a continuation*.  The source is the flattened shape a real program
    produces -- `unfold; atomic body; fold; work`, right-nested -- and
    the target is `TSeq (TInvAccess … (TAtomic …)) work'`.

    The continuation is consumed as an already-normalized
    statement together with its erasure equation, so this constructor is
    composable with whatever normalizes the tail; the access half is
    unchanged from [resource_normalization_terminal_atomic_access].
    Runtime erasure is [runtime_stmt_linear_access_then]: both shapes run
    the atomic body and then the continuation. *)
Definition resource_normalization_terminal_atomic_access_then
    {Γ F Δ cost entry opened inner exit}
    {post : Resource.resource_prenex Γ F Δ}
    invariant
    (arguments closing_arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (input_store output_store : symbolic_store Γ F Δ)
    (frame remainder : Resource.core_assertion F Δ)
    (outer_node unfold_node body_sequence_node fold_sequence_node fold_node
      atomic_node target_node : node_id)
    (atomic_body work work_target : stmt Γ)
    (source_derivation : ResourceRules.RavenResourceTriple
      (Resource.RState input_store
        (Resource.CAnd
          (Resource.CInvariant invariant
            (IR.symbolize_expr_list input_store arguments)) frame))
      (TSeq outer_node (TUnfold unfold_node invariant arguments)
        (TSeq body_sequence_node (TAtomic atomic_node atomic_body)
          (TSeq fold_sequence_node
            (TFold fold_node invariant closing_arguments) work)))
      post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry
      (TSeq outer_node (TUnfold unfold_node invariant arguments)
        (TSeq body_sequence_node (TAtomic atomic_node atomic_body)
          (TSeq fold_sequence_node
            (TFold fold_node invariant closing_arguments) work)))
      exit)
    (Hopen : GenericRegions.Atomicity.open_invariant invariant entry =
      inr opened)
    (Hatomic_certificate : structured_certificate cost Γ opened
      (TAtomic atomic_node atomic_body) inner)
    (Hopen_preserved : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open opened)
    (Hbody : ResourceRules.RavenResourceTriple
      (Resource.RState input_store
        (Resource.CAnd
          (ResourceRules.Instances.instantiated_invariant invariant
            (IR.symbolize_expr_list input_store arguments)) frame))
      (TAtomic atomic_node atomic_body)
      (Resource.RState output_store
        (Resource.CAnd
          (ResourceRules.Instances.instantiated_invariant invariant
            (IR.symbolize_expr_list input_store arguments)) remainder)))
    (work_certificate : structured_certificate cost Γ
      (GenericRegions.Atomicity.fold_invariant invariant inner)
      work_target exit)
    (work_derivation : ResourceRules.RavenResourceTriple
      (Resource.RState output_store
        (Resource.CAnd
          (Resource.CInvariant invariant
            (IR.symbolize_expr_list input_store arguments)) remainder))
      work_target post)
    (Hwork_erasure : forall names stack,
      Model.runtime_stmt names stack work =
        Model.runtime_stmt names stack work_target) :
  @resource_normalization_result Γ F Δ cost entry exit
    (Resource.RState input_store
      (Resource.CAnd
        (Resource.CInvariant invariant
          (IR.symbolize_expr_list input_store arguments)) frame))
    post
    (TSeq outer_node (TUnfold unfold_node invariant arguments)
      (TSeq body_sequence_node (TAtomic atomic_node atomic_body)
        (TSeq fold_sequence_node
          (TFold fold_node invariant closing_arguments) work)))
    source_derivation source_certificate.
Proof.
  refine {| resource_normalized_statement :=
      TSeq target_node
        (TInvAccess invariant arguments (TAtomic atomic_node atomic_body))
        work_target;
    resource_normalization_target_derivation :=
      ResourceRules.RTSeq target_node _ _ _ _ _
        (ResourceRules.RTInvAccessBase invariant input_store arguments frame
          (TAtomic atomic_node atomic_body) _ _ Hbody
          (ResourceRules.ResourceAccessBase invariant Δ
            (IR.symbolize_expr_list input_store arguments)
            (ResourceRules.Instances.instantiated_invariant invariant
              (IR.symbolize_expr_list input_store arguments))
            output_store remainder))
        work_derivation;
    resource_normalization_target_certificate :=
      StructuredSequence cost Γ entry target_node _
        (GenericRegions.Atomicity.fold_invariant invariant inner) _ exit
        (StructuredInvAccess cost Γ entry invariant arguments
          (TAtomic atomic_node atomic_body) opened inner Hopen
          Hatomic_certificate Hopen_preserved)
        work_certificate |}.
  intros names stack.
  rewrite runtime_stmt_linear_access_then.
  rewrite (Hwork_erasure names stack).
  reflexivity.
Defined.

(** The analyzer certificate for the baseline source, assembled from the
    analyses of the atomic body and the continuation.  Naming it keeps
    the footprint obligations and the procedure-level statement
    readable. *)

(* ------------------------------------------------------------------ *)
(** ** Structural normalization constructors

    Proof-only Hoare wrappers: the normalized statement, its structured
    certificate and its erasure equation are untouched, and only the
    derivation is rewrapped.  Each is the resource counterpart of the
    correspondingly named legacy constructor.

    One legacy constructor has no counterpart.
    [normalization_stack_consequence] existed because
    [ResourceConsequenceRule] could not see inside
    [AAnd (AStack store) body] and so could not weaken the body under a
    fixed stack.  Here the store is a field of the resource state and
    [RTConsequence] *is* body-level consequence, so
    [resource_normalization_consequence] covers both; a genuine change of
    store is the separate [resource_normalization_stack_rewrite]. *)

Definition resource_normalization_frame
    {Γ F Δ cost entry exit}
    {store : symbolic_store Γ F Δ}
    {pre_body : Resource.core_assertion F Δ}
    {post : Resource.resource_prenex Γ F Δ} {source}
    (frame : Resource.core_assertion F Δ)
    (source_derivation : ResourceRules.RavenResourceTriple
      (Resource.RState store pre_body) source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit)
    (normalization : @resource_normalization_result Γ F Δ cost entry exit
      (Resource.RState store pre_body) post source source_derivation
      source_certificate) :
  @resource_normalization_result Γ F Δ cost entry exit
    (Resource.RState store (Resource.CAnd pre_body frame))
    (Resource.prenex_and post frame) source
    (ResourceRules.RTFrame source store pre_body frame post
      source_derivation)
    source_certificate :=
  {| resource_normalized_statement :=
       normalization.(resource_normalized_statement);
     resource_normalization_target_derivation :=
       ResourceRules.RTFrame _ store pre_body frame post
         normalization.(resource_normalization_target_derivation);
     resource_normalization_target_certificate :=
       normalization.(resource_normalization_target_certificate);
     resource_normalization_runtime_erasure :=
       normalization.(resource_normalization_runtime_erasure) |}.

Definition resource_normalization_consequence
    {Γ F Δ cost entry exit}
    {store : symbolic_store Γ F Δ}
    {pre_body pre_body' : Resource.core_assertion F Δ}
    {post post' : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : ResourceRules.RavenResourceTriple
      (Resource.RState store pre_body) source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit)
    (normalization : @resource_normalization_result Γ F Δ cost entry exit
      (Resource.RState store pre_body) post source source_derivation
      source_certificate)
    (Hpre : Hoare.ResourceHoare.core_entails pre_body' pre_body)
    (Hpost : Hoare.ResourceHoare.resource_prenex_entails post post') :
  @resource_normalization_result Γ F Δ cost entry exit
    (Resource.RState store pre_body') post' source
    (ResourceRules.RTConsequence source store pre_body pre_body' post post'
      source_derivation Hpre Hpost)
    source_certificate :=
  {| resource_normalized_statement :=
       normalization.(resource_normalized_statement);
     resource_normalization_target_derivation :=
       ResourceRules.RTConsequence _ store pre_body pre_body' post post'
         normalization.(resource_normalization_target_derivation) Hpre Hpost;
     resource_normalization_target_certificate :=
       normalization.(resource_normalization_target_certificate);
     resource_normalization_runtime_erasure :=
       normalization.(resource_normalization_runtime_erasure) |}.

Definition resource_normalization_stack_rewrite
    {Γ F Δ cost entry exit}
    {store store' : symbolic_store Γ F Δ}
    {body : Resource.core_assertion F Δ}
    {post : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : ResourceRules.RavenResourceTriple
      (Resource.RState store body) source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit)
    (normalization : @resource_normalization_result Γ F Δ cost entry exit
      (Resource.RState store body) post source source_derivation
      source_certificate)
    (Hstore : Hoare.ResourceHoare.store_equal_under body Γ store' store) :
  @resource_normalization_result Γ F Δ cost entry exit
    (Resource.RState store' body) post source
    (ResourceRules.RTStackRewrite source store store' body post
      source_derivation Hstore)
    source_certificate :=
  {| resource_normalized_statement :=
       normalization.(resource_normalized_statement);
     resource_normalization_target_derivation :=
       ResourceRules.RTStackRewrite _ store store' body post
         normalization.(resource_normalization_target_derivation) Hstore;
     resource_normalization_target_certificate :=
       normalization.(resource_normalization_target_certificate);
     resource_normalization_runtime_erasure :=
       normalization.(resource_normalization_runtime_erasure) |}.

Definition resource_normalization_prenex_elim
    {Γ F Δ t cost entry exit}
    {pre : Resource.resource_prenex Γ F (t :: Δ)}
    {post : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : ResourceRules.RavenResourceTriple
      pre source (Resource.weaken_resource_prenex post))
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit)
    (normalization : @resource_normalization_result Γ F (t :: Δ) cost entry
      exit pre (Resource.weaken_resource_prenex post) source
      source_derivation source_certificate) :
  @resource_normalization_result Γ F Δ cost entry exit
    (Resource.ResourceExists t pre) post source
    (ResourceRules.RTPrenexElim t source pre post source_derivation)
    source_certificate :=
  {| resource_normalized_statement :=
       normalization.(resource_normalized_statement);
     resource_normalization_target_derivation :=
       ResourceRules.RTPrenexElim t _ pre post
         normalization.(resource_normalization_target_derivation);
     resource_normalization_target_certificate :=
       normalization.(resource_normalization_target_certificate);
     resource_normalization_runtime_erasure :=
       normalization.(resource_normalization_runtime_erasure) |}.

Definition resource_normalization_prenex_preserve
    {Γ F Δ t cost entry exit}
    {pre post : Resource.resource_prenex Γ F (t :: Δ)} {source}
    (source_derivation : ResourceRules.RavenResourceTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit)
    (normalization : @resource_normalization_result Γ F (t :: Δ) cost entry
      exit pre post source source_derivation source_certificate) :
  @resource_normalization_result Γ F Δ cost entry exit
    (Resource.ResourceExists t pre) (Resource.ResourceExists t post) source
    (ResourceRules.RTPrenexPreserve t source pre post source_derivation)
    source_certificate :=
  {| resource_normalized_statement :=
       normalization.(resource_normalized_statement);
     resource_normalization_target_derivation :=
       ResourceRules.RTPrenexPreserve t _ pre post
         normalization.(resource_normalization_target_derivation);
     resource_normalization_target_certificate :=
       normalization.(resource_normalization_target_certificate);
     resource_normalization_runtime_erasure :=
       normalization.(resource_normalization_runtime_erasure) |}.

Definition resource_normalization_bound_weaken
    {Γ F Δ t cost entry exit}
    {pre post : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : ResourceRules.RavenResourceTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit)
    (normalization : @resource_normalization_result Γ F Δ cost entry exit
      pre post source source_derivation source_certificate) :
  @resource_normalization_result Γ F (t :: Δ) cost entry exit
    (Resource.weaken_resource_prenex pre)
    (Resource.weaken_resource_prenex post) source
    (ResourceRules.RTBoundWeaken t source pre post source_derivation)
    source_certificate :=
  {| resource_normalized_statement :=
       normalization.(resource_normalized_statement);
     resource_normalization_target_derivation :=
       ResourceRules.RTBoundWeaken t _ pre post
         normalization.(resource_normalization_target_derivation);
     resource_normalization_target_certificate :=
       normalization.(resource_normalization_target_certificate);
     resource_normalization_runtime_erasure :=
       normalization.(resource_normalization_runtime_erasure) |}.

Definition resource_normalization_prenex_consequence
    {Γ F Δ cost entry exit}
    {pre pre' post post' : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : ResourceRules.RavenResourceTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit)
    (normalization : @resource_normalization_result Γ F Δ cost entry exit
      pre post source source_derivation source_certificate)
    (Hpre : Hoare.ResourceHoare.resource_prenex_entails pre' pre)
    (Hpost : Hoare.ResourceHoare.resource_prenex_entails post post') :
  @resource_normalization_result Γ F Δ cost entry exit
    pre' post' source
    (ResourceRules.RTPrenexConsequence source pre pre' post post'
      source_derivation Hpre Hpost) source_certificate :=
  {| resource_normalized_statement :=
       normalization.(resource_normalized_statement);
     resource_normalization_target_derivation :=
       ResourceRules.RTPrenexConsequence _ pre pre' post post'
         normalization.(resource_normalization_target_derivation) Hpre Hpost;
     resource_normalization_target_certificate :=
       normalization.(resource_normalization_target_certificate);
     resource_normalization_runtime_erasure :=
       normalization.(resource_normalization_runtime_erasure) |}.

Definition resource_normalization_conditional
    {Γ F Δ cost entry then_exit else_exit}
    {store : symbolic_store Γ F Δ}
    {body : Resource.core_assertion F Δ}
    {condition then_branch else_branch}
    {post : Resource.resource_prenex Γ F Δ}
    node
    (then_derivation : ResourceRules.RavenResourceTriple
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (IR.symbolize_expr store condition))))
      then_branch post)
    (then_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry then_branch then_exit)
    (then_normalization : @resource_normalization_result Γ F Δ cost entry
      then_exit _ post then_branch then_derivation then_certificate)
    (else_derivation : ResourceRules.RavenResourceTriple
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (Core.EUnOp Core.UNot
            (IR.symbolize_expr store condition)))))
      else_branch post)
    (else_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry else_branch else_exit)
    (else_normalization : @resource_normalization_result Γ F Δ cost entry
      else_exit _ post else_branch else_derivation else_certificate)
    (Hopen_equal : GenericRegions.Atomicity.analysis_open then_exit =
      GenericRegions.Atomicity.analysis_open else_exit)
    (Hatomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (view : RegionSyntax.view (TIf node condition then_branch else_branch) =
      TypedAnalysisView.ViewConditional then_branch else_branch) :
  let source := TIf node condition then_branch else_branch in
  let joined := GenericRegions.Atomicity.AnalysisState
    (GenericRegions.Atomicity.analysis_mask then_exit ∩
      GenericRegions.Atomicity.analysis_mask else_exit)
    (GenericRegions.Atomicity.analysis_open then_exit)
    (GenericRegions.Atomicity.analysis_step_taken then_exit ||
      GenericRegions.Atomicity.analysis_step_taken else_exit)
    (GenericRegions.Atomicity.analysis_in_atomic then_exit) in
  let source_derivation := ResourceRules.RTIf node store body condition
    then_branch else_branch post then_derivation else_derivation in
  let source_certificate := GenericRegions.Atomicity.CertConditional cost Γ
    entry source then_branch else_branch then_exit else_exit view
      then_certificate else_certificate Hopen_equal Hatomic_equal in
  @resource_normalization_result Γ F Δ cost entry joined
    (Resource.RState store body) post source
    source_derivation source_certificate.
Proof.
  simpl.
  refine {| resource_normalized_statement := TIf node condition
      then_normalization.(resource_normalized_statement)
      else_normalization.(resource_normalized_statement);
    resource_normalization_target_derivation :=
      ResourceRules.RTIf node store body condition _ _ post
        then_normalization.(resource_normalization_target_derivation)
        else_normalization.(resource_normalization_target_derivation);
    resource_normalization_target_certificate :=
      StructuredConditional cost Γ entry node condition _ _ then_exit
        else_exit
        then_normalization.(resource_normalization_target_certificate)
        else_normalization.(resource_normalization_target_certificate)
        Hopen_equal Hatomic_equal |}.
  intros names stack. simpl.
  rewrite (then_normalization.(resource_normalization_runtime_erasure)
    names stack).
  rewrite (else_normalization.(resource_normalization_runtime_erasure)
    names stack).
  reflexivity.
Defined.

(** *** Footprint transport

    A proof-only Hoare wrapper leaves both the normalized syntax and its
    structured certificate unchanged, so the strengthened record's two
    fields transport with no set reasoning at all. *)
Definition footprinted_resource_normalization_frame
    {Γ F Δ cost entry exit}
    {store : symbolic_store Γ F Δ}
    {pre_body : Resource.core_assertion F Δ}
    {post : Resource.resource_prenex Γ F Δ} {source}
    (frame : Resource.core_assertion F Δ)
    (source_derivation : ResourceRules.RavenResourceTriple
      (Resource.RState store pre_body) source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit)
    (result : @footprinted_resource_normalization_result Γ F Δ cost entry exit
      (Resource.RState store pre_body) post source source_derivation
      source_certificate) :
  @footprinted_resource_normalization_result Γ F Δ cost entry exit
    (Resource.RState store (Resource.CAnd pre_body frame))
    (Resource.prenex_and post frame) source
    (ResourceRules.RTFrame source store pre_body frame post
      source_derivation)
    source_certificate :=
  {| footprinted_resource_normalization :=
       resource_normalization_frame frame source_derivation
         source_certificate result.(footprinted_resource_normalization);
     footprinted_resource_normalization_subset :=
       result.(footprinted_resource_normalization_subset);
     footprinted_resource_normalization_safe :=
       result.(footprinted_resource_normalization_safe) |}.

Definition footprinted_resource_normalization_consequence
    {Γ F Δ cost entry exit}
    {store : symbolic_store Γ F Δ}
    {pre_body pre_body' : Resource.core_assertion F Δ}
    {post post' : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : ResourceRules.RavenResourceTriple
      (Resource.RState store pre_body) source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit)
    (result : @footprinted_resource_normalization_result Γ F Δ cost entry exit
      (Resource.RState store pre_body) post source source_derivation
      source_certificate)
    (Hpre : Hoare.ResourceHoare.core_entails pre_body' pre_body)
    (Hpost : Hoare.ResourceHoare.resource_prenex_entails post post') :
  @footprinted_resource_normalization_result Γ F Δ cost entry exit
    (Resource.RState store pre_body') post' source
    (ResourceRules.RTConsequence source store pre_body pre_body' post post'
      source_derivation Hpre Hpost)
    source_certificate :=
  {| footprinted_resource_normalization :=
       resource_normalization_consequence source_derivation
         source_certificate result.(footprinted_resource_normalization)
         Hpre Hpost;
     footprinted_resource_normalization_subset :=
       result.(footprinted_resource_normalization_subset);
     footprinted_resource_normalization_safe :=
       result.(footprinted_resource_normalization_safe) |}.

Definition footprinted_resource_normalization_stack_rewrite
    {Γ F Δ cost entry exit}
    {store store' : symbolic_store Γ F Δ}
    {body : Resource.core_assertion F Δ}
    {post : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : ResourceRules.RavenResourceTriple
      (Resource.RState store body) source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit)
    (result : @footprinted_resource_normalization_result Γ F Δ cost entry exit
      (Resource.RState store body) post source source_derivation
      source_certificate)
    (Hstore : Hoare.ResourceHoare.store_equal_under body Γ store' store) :
  @footprinted_resource_normalization_result Γ F Δ cost entry exit
    (Resource.RState store' body) post source
    (ResourceRules.RTStackRewrite source store store' body post
      source_derivation Hstore)
    source_certificate :=
  {| footprinted_resource_normalization :=
       resource_normalization_stack_rewrite source_derivation
         source_certificate result.(footprinted_resource_normalization)
         Hstore;
     footprinted_resource_normalization_subset :=
       result.(footprinted_resource_normalization_subset);
     footprinted_resource_normalization_safe :=
       result.(footprinted_resource_normalization_safe) |}.

Definition footprinted_resource_normalization_prenex_elim
    {Γ F Δ t cost entry exit}
    {pre : Resource.resource_prenex Γ F (t :: Δ)}
    {post : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : ResourceRules.RavenResourceTriple
      pre source (Resource.weaken_resource_prenex post))
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit)
    (result : @footprinted_resource_normalization_result Γ F (t :: Δ) cost
      entry exit pre (Resource.weaken_resource_prenex post) source
      source_derivation source_certificate) :
  @footprinted_resource_normalization_result Γ F Δ cost entry exit
    (Resource.ResourceExists t pre) post source
    (ResourceRules.RTPrenexElim t source pre post source_derivation)
    source_certificate :=
  {| footprinted_resource_normalization :=
       resource_normalization_prenex_elim source_derivation
         source_certificate result.(footprinted_resource_normalization);
     footprinted_resource_normalization_subset :=
       result.(footprinted_resource_normalization_subset);
     footprinted_resource_normalization_safe :=
       result.(footprinted_resource_normalization_safe) |}.

Definition footprinted_resource_normalization_prenex_preserve
    {Γ F Δ t cost entry exit}
    {pre post : Resource.resource_prenex Γ F (t :: Δ)} {source}
    (source_derivation : ResourceRules.RavenResourceTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit)
    (result : @footprinted_resource_normalization_result Γ F (t :: Δ) cost
      entry exit pre post source source_derivation source_certificate) :
  @footprinted_resource_normalization_result Γ F Δ cost entry exit
    (Resource.ResourceExists t pre) (Resource.ResourceExists t post) source
    (ResourceRules.RTPrenexPreserve t source pre post source_derivation)
    source_certificate :=
  {| footprinted_resource_normalization :=
       resource_normalization_prenex_preserve source_derivation
         source_certificate result.(footprinted_resource_normalization);
     footprinted_resource_normalization_subset :=
       result.(footprinted_resource_normalization_subset);
     footprinted_resource_normalization_safe :=
       result.(footprinted_resource_normalization_safe) |}.

Definition footprinted_resource_normalization_bound_weaken
    {Γ F Δ t cost entry exit}
    {pre post : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : ResourceRules.RavenResourceTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit)
    (result : @footprinted_resource_normalization_result Γ F Δ cost entry exit
      pre post source source_derivation source_certificate) :
  @footprinted_resource_normalization_result Γ F (t :: Δ) cost entry exit
    (Resource.weaken_resource_prenex pre)
    (Resource.weaken_resource_prenex post) source
    (ResourceRules.RTBoundWeaken t source pre post source_derivation)
    source_certificate :=
  {| footprinted_resource_normalization :=
       resource_normalization_bound_weaken source_derivation
         source_certificate result.(footprinted_resource_normalization);
     footprinted_resource_normalization_subset :=
       result.(footprinted_resource_normalization_subset);
     footprinted_resource_normalization_safe :=
       result.(footprinted_resource_normalization_safe) |}.

Definition footprinted_resource_normalization_prenex_consequence
    {Γ F Δ cost entry exit}
    {pre pre' post post' : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : ResourceRules.RavenResourceTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit)
    (result : @footprinted_resource_normalization_result Γ F Δ cost entry exit
      pre post source source_derivation source_certificate)
    (Hpre : Hoare.ResourceHoare.resource_prenex_entails pre' pre)
    (Hpost : Hoare.ResourceHoare.resource_prenex_entails post post') :
  @footprinted_resource_normalization_result Γ F Δ cost entry exit
    pre' post' source
    (ResourceRules.RTPrenexConsequence source pre pre' post post'
      source_derivation Hpre Hpost) source_certificate :=
  {| footprinted_resource_normalization :=
       resource_normalization_prenex_consequence source_derivation
         source_certificate result.(footprinted_resource_normalization)
         Hpre Hpost;
     footprinted_resource_normalization_subset :=
       result.(footprinted_resource_normalization_subset);
     footprinted_resource_normalization_safe :=
       result.(footprinted_resource_normalization_safe) |}.

(** The public normalization contract is insensitive to proof-only Hoare
    wrappers.  These lemmas deliberately transport an existential result in
    [Prop]; the executable worker is unchanged because each wrapper leaves
    the source statement unchanged. *)


(* ------------------------------------------------------------------ *)
(** ** Alignment between an analyzer certificate and a resource derivation

    It records that a derivation's structural shape matches the certificate's,
    which lets the normalizer recurse on the source shape instead of inverting
    an arbitrary derivation.

    [ResourceAlignedStackConsequence] is gone for the same reason its
    normalization constructor is: [RTConsequence] is body-level
    consequence, so it subsumes the stack-fixed case.  A genuine change
    of store is [ResourceAlignedStackRewrite].

    The two fold/unfold cases also lose a premise: the legacy ones carry
    an [instantiated_invariant] witness, while [RTUnfoldInvariant] and
    [RTFoldInvariant] take the opened body to *be*
    [instantiated_invariant] applied to the access arguments. *)
Inductive resource_certificate_aligned (cost : GenericRegions.Atomicity.cost_model) :
    forall {Γ F Δ} {entry : GenericRegions.Atomicity.analysis_state}
      {statement : stmt Γ} {exit : GenericRegions.Atomicity.analysis_state}
      {pre post : Resource.resource_prenex Γ F Δ},
      GenericRegions.Atomicity.analysis_certificate cost Γ entry statement exit ->
      @ResourceRules.RavenResourceTriple Γ F Δ pre statement post ->
      Type :=
| ResourceAlignedOrdinaryLeaf : forall Γ F Δ entry statement exit pre post
    view step
    (derivation : @ResourceRules.RavenResourceTriple Γ F Δ pre statement post),
    resource_certificate_aligned cost
      (GenericRegions.Atomicity.CertLeaf cost Γ entry statement exit view step)
      derivation
| ResourceAlignedDone : forall Γ F Δ entry statement pre post view
    (derivation : @ResourceRules.RavenResourceTriple Γ F Δ pre statement post),
    resource_certificate_aligned cost
      (GenericRegions.Atomicity.CertDone cost Γ entry statement view)
      derivation
| ResourceAlignedUnfold : forall Γ F Δ entry node invariant arguments exit
    (store : symbolic_store Γ F Δ)
    (view : RegionSyntax.view (TUnfold node invariant arguments) =
      TypedAnalysisView.ViewUnfold invariant)
    (step : GenericRegions.Atomicity.open_invariant invariant entry = inr exit),
    resource_certificate_aligned cost
      (GenericRegions.Atomicity.CertUnfold cost Γ entry
        (TUnfold node invariant arguments) invariant exit view step)
      (ResourceRules.RTUnfoldInvariant node invariant store arguments)
| ResourceAlignedFold : forall Γ F Δ entry node invariant arguments
    (store : symbolic_store Γ F Δ)
    (view : RegionSyntax.view (TFold node invariant arguments) =
      TypedAnalysisView.ViewFold invariant),
    resource_certificate_aligned cost
      (GenericRegions.Atomicity.CertFold cost Γ entry
        (TFold node invariant arguments) invariant view)
      (ResourceRules.RTFoldInvariant node invariant store arguments)
| ResourceAlignedSequence : forall Γ F Δ state node first middle second exit
    (pre middle_prenex post : Resource.resource_prenex Γ F Δ)
    (view : RegionSyntax.view (TSeq node first second) =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      state first middle)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      middle second exit)
    (first_derivation :
      @ResourceRules.RavenResourceTriple Γ F Δ pre first middle_prenex)
    (second_derivation :
      @ResourceRules.RavenResourceTriple Γ F Δ middle_prenex second post),
    resource_certificate_aligned cost first_certificate first_derivation ->
    resource_certificate_aligned cost second_certificate second_derivation ->
    resource_certificate_aligned cost
      (GenericRegions.Atomicity.CertSequence cost Γ state
        (TSeq node first second) first middle second exit view
        first_certificate second_certificate)
      (ResourceRules.RTSeq node pre middle_prenex post first second
        first_derivation second_derivation)
| ResourceAlignedConditional : forall Γ F Δ state node
    (store : symbolic_store Γ F Δ) (body : Resource.core_assertion F Δ)
    condition then_branch else_branch then_exit else_exit
    (post : Resource.resource_prenex Γ F Δ)
    (view : RegionSyntax.view (TIf node condition then_branch else_branch) =
      TypedAnalysisView.ViewConditional then_branch else_branch)
    (then_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      state then_branch then_exit)
    (else_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      state else_branch else_exit)
    (open_equal : GenericRegions.Atomicity.analysis_open then_exit =
      GenericRegions.Atomicity.analysis_open else_exit)
    (atomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (then_derivation : @ResourceRules.RavenResourceTriple Γ F Δ
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (IR.symbolize_expr store condition))))
      then_branch post)
    (else_derivation : @ResourceRules.RavenResourceTriple Γ F Δ
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (Core.EUnOp Core.UNot
            (IR.symbolize_expr store condition)))))
      else_branch post),
    resource_certificate_aligned cost then_certificate then_derivation ->
    resource_certificate_aligned cost else_certificate else_derivation ->
    resource_certificate_aligned cost
      (GenericRegions.Atomicity.CertConditional cost Γ state
        (TIf node condition then_branch else_branch) then_branch else_branch
        then_exit else_exit view then_certificate else_certificate
        open_equal atomic_equal)
      (ResourceRules.RTIf node store body condition then_branch else_branch
        post then_derivation else_derivation)
| ResourceAlignedAtomic : forall Γ F Δ state node body outer inner
    (pre post : Resource.resource_prenex Γ F Δ)
    (view : RegionSyntax.view (TAtomic node body) =
      TypedAnalysisView.ViewAtomic body)
    (step : GenericRegions.Atomicity.take_step
      GenericRegions.Atomicity.AtomicStep state = inr outer)
    (body_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask outer)
        (GenericRegions.Atomicity.analysis_open outer)
        (GenericRegions.Atomicity.analysis_step_taken outer) true)
      body inner)
    (open_equal : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open outer)
    (body_derivation :
      @ResourceRules.RavenResourceTriple Γ F Δ pre body post),
    resource_certificate_aligned cost body_certificate body_derivation ->
    resource_certificate_aligned cost
      (GenericRegions.Atomicity.CertAtomic cost Γ state (TAtomic node body)
        body outer inner view step body_certificate open_equal)
      (ResourceRules.RTAtomicBlock node pre post body body_derivation)
| ResourceAlignedFrame : forall Γ F Δ entry exit statement
    (store : symbolic_store Γ F Δ)
    (pre_body frame : Resource.core_assertion F Δ)
    (post : Resource.resource_prenex Γ F Δ)
    (certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry statement exit)
    (derivation : @ResourceRules.RavenResourceTriple Γ F Δ
      (Resource.RState store pre_body) statement post),
    resource_certificate_aligned cost certificate derivation ->
    resource_certificate_aligned cost certificate
      (ResourceRules.RTFrame statement store pre_body frame post derivation)
| ResourceAlignedPrenexElim : forall Γ F Δ t entry exit statement
    (pre : Resource.resource_prenex Γ F (t :: Δ))
    (post : Resource.resource_prenex Γ F Δ)
    (certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry statement exit)
    (derivation : @ResourceRules.RavenResourceTriple Γ F (t :: Δ)
      pre statement (Resource.weaken_resource_prenex post)),
    resource_certificate_aligned cost certificate derivation ->
    resource_certificate_aligned cost certificate
      (ResourceRules.RTPrenexElim t statement pre post derivation)
| ResourceAlignedPrenexPreserve : forall Γ F Δ t entry exit statement
    (pre post : Resource.resource_prenex Γ F (t :: Δ))
    (certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry statement exit)
    (derivation :
      @ResourceRules.RavenResourceTriple Γ F (t :: Δ) pre statement post),
    resource_certificate_aligned cost certificate derivation ->
    resource_certificate_aligned cost certificate
      (ResourceRules.RTPrenexPreserve t statement pre post derivation)
| ResourceAlignedPrenexConsequence : forall Γ F Δ entry exit statement
    (pre pre' post post' : Resource.resource_prenex Γ F Δ)
    (certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry statement exit)
    (derivation : @ResourceRules.RavenResourceTriple Γ F Δ
      pre statement post)
    (pre_entails : Hoare.ResourceHoare.resource_prenex_entails pre' pre)
    (post_entails : Hoare.ResourceHoare.resource_prenex_entails post post'),
    resource_certificate_aligned cost certificate derivation ->
    resource_certificate_aligned cost certificate
      (ResourceRules.RTPrenexConsequence statement pre pre' post post'
        derivation pre_entails post_entails)
| ResourceAlignedConsequence : forall Γ F Δ entry exit statement
    (store : symbolic_store Γ F Δ)
    (pre_body pre_body' : Resource.core_assertion F Δ)
    (post post' : Resource.resource_prenex Γ F Δ)
    (certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry statement exit)
    (derivation : @ResourceRules.RavenResourceTriple Γ F Δ
      (Resource.RState store pre_body) statement post)
    (pre_entails : Hoare.ResourceHoare.core_entails pre_body' pre_body)
    (post_entails : Hoare.ResourceHoare.resource_prenex_entails post post'),
    resource_certificate_aligned cost certificate derivation ->
    resource_certificate_aligned cost certificate
      (ResourceRules.RTConsequence statement store pre_body pre_body'
        post post' derivation pre_entails post_entails)
| ResourceAlignedStackRewrite : forall Γ F Δ entry exit statement
    (store store' : symbolic_store Γ F Δ)
    (body : Resource.core_assertion F Δ)
    (post : Resource.resource_prenex Γ F Δ)
    (certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry statement exit)
    (derivation : @ResourceRules.RavenResourceTriple Γ F Δ
      (Resource.RState store body) statement post)
    (store_equal : Hoare.ResourceHoare.store_equal_under body Γ store' store),
    resource_certificate_aligned cost certificate derivation ->
    resource_certificate_aligned cost certificate
      (ResourceRules.RTStackRewrite statement store store' body post
        derivation store_equal)
| ResourceAlignedBoundWeaken : forall Γ F Δ t entry exit statement
    (pre post : Resource.resource_prenex Γ F Δ)
    (certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry statement exit)
    (derivation : @ResourceRules.RavenResourceTriple Γ F Δ
      pre statement post),
    resource_certificate_aligned cost certificate derivation ->
    resource_certificate_aligned cost certificate
      (ResourceRules.RTBoundWeaken t statement pre post derivation).

(** *** Alignment is complete

    For any resource derivation and any analyzer certificate of the same
    statement, an alignment exists.  A program pairs its Hoare proof with its
    analysis, and the alignment follows rather than being reconstructed by
    hand.

    The [RTInvAccess] case is vacuous.  [RegionSyntax.view] sends
    [TInvAccess] to [ViewStructuredAccess], and no
    [analysis_certificate] constructor accepts that view, so there is no
    certificate to align with -- the analyzer never sees a structured
    access in its *source*, only in a normalization's target. *)
Fixpoint resource_certificate_aligned_complete_exists {cost Γ F} Δ
    (pre post : Resource.resource_prenex Γ F Δ) (statement : stmt Γ)
    (derivation : @ResourceRules.RavenResourceTriple Γ F Δ pre statement post)
    {struct derivation} :
  forall entry exit
    (certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry statement exit),
    exists aligned : resource_certificate_aligned cost certificate derivation,
      True.
Proof.
  destruct derivation; intros entry exit certificate.
  (* The rules that leave the statement, and hence the certificate,
     alone. *)
  all: try (destruct (resource_certificate_aligned_complete_exists cost Γ F
              _ _ _ _ derivation entry exit certificate) as [A _];
            unshelve eexists;
              [ solve [ eapply ResourceAlignedPrenexPreserve; exact A
                      | eapply ResourceAlignedPrenexElim; exact A
                      | eapply ResourceAlignedBoundWeaken; exact A
                      | eapply ResourceAlignedFrame; exact A
                      | eapply ResourceAlignedConsequence; exact A
                      | eapply ResourceAlignedStackRewrite; exact A
                      | eapply ResourceAlignedPrenexConsequence; exact A ]
              | exact I ]).
  (* Every remaining rule fixes the statement's shape, so the certificate
     is determined up to the cases whose view premise is contradictory. *)
  all: dependent destruction certificate; try discriminate.
  (* The bare unfold and fold need their view equation resolved first:
     the certificate names an invariant of its own, and alignment
     requires it to be the derivation's. *)
  all: try lazymatch goal with
       | [ |- context [ResourceRules.RTUnfoldInvariant _ _ _ _] ] =>
           cbn in e; dependent destruction e
       | [ |- context [ResourceRules.RTFoldInvariant _ _ _ _] ] =>
           cbn in e; dependent destruction e
       end.
  (* Leaves, and the bare unfold and fold. *)
  all: try (unshelve eexists; [solve [constructor] | exact I]).
  (* Sequence, conditional and the trusted atomic block recurse. *)
  (* Sequence, conditional and the trusted atomic block recurse.  The
     cases are selected by the derivation's shape rather than by
     position, since [dependent destruction] chooses the sub-derivation
     names. *)
  all: lazymatch goal with
       | [ |- context [ResourceRules.RTSeq _ _ _ _ _ _ ?d1 ?d2] ] =>
           cbn in e; dependent destruction e;
           destruct (resource_certificate_aligned_complete_exists cost Γ F
             _ _ _ _ d1 _ _ certificate1) as [A1 _];
           destruct (resource_certificate_aligned_complete_exists cost Γ F
             _ _ _ _ d2 _ _ certificate2) as [A2 _];
           unshelve eexists;
             [eapply ResourceAlignedSequence; eassumption | exact I]
       | [ |- context [ResourceRules.RTIf _ _ _ _ _ _ _ ?d1 ?d2] ] =>
           cbn in e; dependent destruction e;
           destruct (resource_certificate_aligned_complete_exists cost Γ F
             _ _ _ _ d1 _ _ certificate1) as [Athen _];
           destruct (resource_certificate_aligned_complete_exists cost Γ F
             _ _ _ _ d2 _ _ certificate2) as [Aelse _];
           unshelve eexists;
             [eapply ResourceAlignedConditional; eassumption | exact I]
       | [ |- context [ResourceRules.RTAtomicBlock _ _ _ _ ?d] ] =>
           cbn in e; dependent destruction e;
           destruct (resource_certificate_aligned_complete_exists cost Γ F
             _ _ _ _ d _ _ certificate) as [Abody _];
           unshelve eexists;
             [eapply ResourceAlignedAtomic; eassumption | exact I]
       end.
Qed.

(** Alignment exists propositionally for every matching pair.  Executable
    normalization must nevertheless receive a constructor-built witness:
    eliminating this existential with choice would make the witness opaque,
    while the producer computes by inspecting its constructors. *)

(* ------------------------------------------------------------------ *)
(** ** The certified resource triple and normalization entry point

    Alignment pairs the resource derivation with its analysis certificate.
    It is not reconstructed from an arbitrary derivation: the normalization
    result records the matching witness supplied by the analyzer, making the
    dependency explicit without duplicating the analyzer's traversal. *)

(** Proof-irrelevant input to the normalization theorem.  This record contains
    no alignment and no executable proof evidence.  The restricted checker owns partiality;
    normalization soundness is the proposition
    [restricted_footprinted_resource_normalization_exists] below. *)
Record resource_analyzed_triple (cost : GenericRegions.Atomicity.cost_model)
    {Γ F Δ}
    (pre : Resource.resource_prenex Γ F Δ) (statement : stmt Γ)
    (entry exit : GenericRegions.Atomicity.analysis_state)
    (post : Resource.resource_prenex Γ F Δ) : Type := {
  resource_analyzed_certificate :
    GenericRegions.Atomicity.analysis_certificate cost Γ entry statement exit;
  resource_analyzed_cost_sound : Certified.procedure_cost_model_sound cost;
  resource_analyzed_hoare :
    @ResourceRules.RavenResourceTriple Γ F Δ pre statement post;
  resource_analyzed_restricted : restricted_fragment_accepted statement;
}.

Arguments resource_analyzed_certificate {_ _ _ _ _ _ _ _ _} _.
Arguments resource_analyzed_cost_sound {_ _ _ _ _ _ _ _ _} _.
Arguments resource_analyzed_hoare {_ _ _ _ _ _ _ _ _} _.
Arguments resource_analyzed_restricted {_ _ _ _ _ _ _ _ _} _.

Lemma resource_analyzed_worker_succeeds
    {cost Γ F Δ pre statement entry exit post}
    (analyzed : @resource_analyzed_triple cost Γ F Δ pre statement entry exit
      post) :
  exists normalized,
    restricted_analyze_and_normalize statement = Some normalized.
Proof.
  apply restricted_analyze_and_normalize_succeeds.
  exact (resource_analyzed_restricted analyzed).
Qed.

(** Legacy proof-indexed bundle.  It remains temporarily for the old
    producer below, but is not the interface of the redesigned pass:
    [resource_analyzed_triple] plus
    [restricted_footprinted_resource_normalization_exists] is the new
    boundary, and alignment is constructed only inside its proof. *)


Definition footprinted_resource_normalization_sequence
    {Γ F Δ cost entry middle exit}
    {pre middle_prenex post : Resource.resource_prenex Γ F Δ}
    {first second : stmt Γ} node
    (first_derivation :
      ResourceRules.RavenResourceTriple pre first middle_prenex)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry first middle)
    (first_result : @footprinted_resource_normalization_result Γ F Δ cost
      entry middle pre middle_prenex first first_derivation first_certificate)
    (second_derivation :
      ResourceRules.RavenResourceTriple middle_prenex second post)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      middle second exit)
    (second_result : @footprinted_resource_normalization_result Γ F Δ cost
      middle exit middle_prenex post second second_derivation
      second_certificate)
    (view : RegionSyntax.view (TSeq node first second) =
      TypedAnalysisView.ViewSequence first second) :
  let source := TSeq node first second in
  let source_derivation := ResourceRules.RTSeq node pre middle_prenex post
    first second first_derivation second_derivation in
  let source_certificate := GenericRegions.Atomicity.CertSequence cost Γ
    entry source first middle second exit view first_certificate
      second_certificate in
  @footprinted_resource_normalization_result Γ F Δ cost entry exit pre post
    source source_derivation source_certificate.
Proof.
  simpl.
  refine {| footprinted_resource_normalization :=
    resource_normalization_sequence node first_derivation first_certificate
      first_result.(footprinted_resource_normalization) second_derivation
      second_certificate second_result.(footprinted_resource_normalization)
      view |}.
  - intros marker Hmember.
    simpl in Hmember |- *.
    repeat rewrite elem_of_union in Hmember |- *.
    pose proof (first_result.(footprinted_resource_normalization_subset)
      marker) as Hfirst.
    pose proof (second_result.(footprinted_resource_normalization_subset)
      marker) as Hsecond.
    tauto.
  - intros Hentry. split.
    + exact (first_result.(footprinted_resource_normalization_safe) Hentry).
    + apply second_result.(footprinted_resource_normalization_safe).
      rewrite (GenericRegions.Atomicity.analysis_certificate_preserves_in_atomic
        first_certificate). exact Hentry.
Defined.

Lemma footprinted_resource_normalization_sequence_from_worker
    {Γ F Δ cost entry middle exit}
    {pre middle_prenex post : Resource.resource_prenex Γ F Δ}
    {first second normalized_first normalized_second normalized : stmt Γ}
    node
    (first_derivation :
      ResourceRules.RavenResourceTriple pre first middle_prenex)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry first middle)
    (first_result : @footprinted_resource_normalization_result Γ F Δ cost
      entry middle pre middle_prenex first first_derivation first_certificate)
    (Hfirst_result : resource_normalized_statement
      first_result.(footprinted_resource_normalization) = normalized_first)
    (second_derivation :
      ResourceRules.RavenResourceTriple middle_prenex second post)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      middle second exit)
    (second_result : @footprinted_resource_normalization_result Γ F Δ cost
      middle exit middle_prenex post second second_derivation
      second_certificate)
    (Hsecond_result : resource_normalized_statement
      second_result.(footprinted_resource_normalization) = normalized_second)
    (view : RegionSyntax.view (TSeq node first second) =
      TypedAnalysisView.ViewSequence first second)
    (Hnot_unfold : match RegionSyntax.view first with
      | TypedAnalysisView.ViewUnfold _ => False
      | _ => True
      end)
    fuel
    (Hfirst_worker : restricted_normalize_statement_fuel fuel first =
      Some normalized_first)
    (Hsecond_worker : restricted_normalize_statement_fuel fuel second =
      Some normalized_second)
    (Hworker : restricted_normalize_statement_fuel (S fuel)
      (TSeq node first second) = Some normalized) :
  exists result : @footprinted_resource_normalization_result Γ F Δ cost entry
      exit pre post (TSeq node first second)
      (ResourceRules.RTSeq node pre middle_prenex post first second
        first_derivation second_derivation)
      (GenericRegions.Atomicity.CertSequence cost Γ entry
        (TSeq node first second) first middle second exit view
        first_certificate second_certificate),
    resource_normalized_statement
      result.(footprinted_resource_normalization) = normalized.
Proof.
  destruct first; cbn in Hnot_unfold, Hworker;
    try contradiction;
    rewrite Hfirst_worker, Hsecond_worker in Hworker;
    inversion Hworker; subst.
  all: exists (footprinted_resource_normalization_sequence node
    first_derivation first_certificate first_result second_derivation
    second_certificate second_result view);
    cbn; reflexivity.
Qed.

Definition footprinted_resource_normalization_conditional
    {Γ F Δ cost entry then_exit else_exit}
    {store : symbolic_store Γ F Δ} {body : Resource.core_assertion F Δ}
    {post : Resource.resource_prenex Γ F Δ}
    {condition} {then_branch else_branch : stmt Γ} node
    (then_derivation : ResourceRules.RavenResourceTriple
      (Resource.RState store
        (Resource.CAnd body (Resource.CExpr (IR.symbolize_expr store condition))))
      then_branch post)
    (then_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry then_branch then_exit)
    (then_result : @footprinted_resource_normalization_result Γ F Δ cost entry
      then_exit _ post then_branch then_derivation then_certificate)
    (else_derivation : ResourceRules.RavenResourceTriple
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (Core.EUnOp Core.UNot
            (IR.symbolize_expr store condition)))))
      else_branch post)
    (else_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry else_branch else_exit)
    (else_result : @footprinted_resource_normalization_result Γ F Δ cost entry
      else_exit _ post else_branch else_derivation else_certificate)
    (open_equal : GenericRegions.Atomicity.analysis_open then_exit =
      GenericRegions.Atomicity.analysis_open else_exit)
    (atomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (view : RegionSyntax.view (TIf node condition then_branch else_branch) =
      TypedAnalysisView.ViewConditional then_branch else_branch) :
  let source := TIf node condition then_branch else_branch in
  let joined := GenericRegions.Atomicity.AnalysisState
    (GenericRegions.Atomicity.analysis_mask then_exit ∩
      GenericRegions.Atomicity.analysis_mask else_exit)
    (GenericRegions.Atomicity.analysis_open then_exit)
    (GenericRegions.Atomicity.analysis_step_taken then_exit ||
      GenericRegions.Atomicity.analysis_step_taken else_exit)
    (GenericRegions.Atomicity.analysis_in_atomic then_exit) in
  let source_derivation := ResourceRules.RTIf node store body condition
    then_branch else_branch post then_derivation else_derivation in
  let source_certificate := GenericRegions.Atomicity.CertConditional cost Γ
    entry source then_branch else_branch then_exit else_exit view
      then_certificate else_certificate open_equal atomic_equal in
  @footprinted_resource_normalization_result Γ F Δ cost entry joined
    (Resource.RState store body) post source source_derivation
    source_certificate.
Proof.
  simpl.
  refine {| footprinted_resource_normalization :=
    resource_normalization_conditional node then_derivation then_certificate
      then_result.(footprinted_resource_normalization) else_derivation
      else_certificate else_result.(footprinted_resource_normalization)
      open_equal atomic_equal view |}.
  - intros marker Hmember.
    simpl in Hmember |- *.
    repeat rewrite elem_of_union in Hmember |- *.
    pose proof (then_result.(footprinted_resource_normalization_subset)
      marker) as Hthen.
    pose proof (else_result.(footprinted_resource_normalization_subset)
      marker) as Helse.
    tauto.
  - intros Hentry. split.
    + exact (then_result.(footprinted_resource_normalization_safe) Hentry).
    + exact (else_result.(footprinted_resource_normalization_safe) Hentry).
Defined.


Lemma footprinted_resource_normalization_conditional_from_worker
    {Γ F Δ cost entry then_exit else_exit}
    {store : symbolic_store Γ F Δ} {body : Resource.core_assertion F Δ}
    {post : Resource.resource_prenex Γ F Δ}
    {condition} {then_branch else_branch normalized_then normalized_else
      normalized : stmt Γ} node
    (then_derivation : ResourceRules.RavenResourceTriple
      (Resource.RState store
        (Resource.CAnd body (Resource.CExpr (IR.symbolize_expr store condition))))
      then_branch post)
    (then_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry then_branch then_exit)
    (then_result : @footprinted_resource_normalization_result Γ F Δ cost entry
      then_exit _ post then_branch then_derivation then_certificate)
    (Hthen_result : resource_normalized_statement
      then_result.(footprinted_resource_normalization) = normalized_then)
    (else_derivation : ResourceRules.RavenResourceTriple
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (Core.EUnOp Core.UNot
            (IR.symbolize_expr store condition)))))
      else_branch post)
    (else_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry else_branch else_exit)
    (else_result : @footprinted_resource_normalization_result Γ F Δ cost entry
      else_exit _ post else_branch else_derivation else_certificate)
    (Helse_result : resource_normalized_statement
      else_result.(footprinted_resource_normalization) = normalized_else)
    (open_equal : GenericRegions.Atomicity.analysis_open then_exit =
      GenericRegions.Atomicity.analysis_open else_exit)
    (atomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (view : RegionSyntax.view (TIf node condition then_branch else_branch) =
      TypedAnalysisView.ViewConditional then_branch else_branch)
    fuel
    (Hthen_worker : restricted_normalize_statement_fuel fuel then_branch =
      Some normalized_then)
    (Helse_worker : restricted_normalize_statement_fuel fuel else_branch =
      Some normalized_else)
    (Hworker : restricted_normalize_statement_fuel (S fuel)
      (TIf node condition then_branch else_branch) = Some normalized) :
  exists result : @footprinted_resource_normalization_result Γ F Δ cost entry
      _ _ post (TIf node condition then_branch else_branch)
      (ResourceRules.RTIf node store body condition then_branch else_branch
        post then_derivation else_derivation)
      (GenericRegions.Atomicity.CertConditional cost Γ entry
        (TIf node condition then_branch else_branch) then_branch else_branch
        then_exit else_exit view then_certificate else_certificate
        open_equal atomic_equal),
    resource_normalized_statement
      result.(footprinted_resource_normalization) = normalized.
Proof.
  cbn [restricted_normalize_statement_fuel] in Hworker.
  rewrite Hthen_worker, Helse_worker in Hworker. inversion Hworker; subst.
  exists (footprinted_resource_normalization_conditional node
    then_derivation then_certificate then_result else_derivation
    else_certificate else_result open_equal atomic_equal view).
  reflexivity.
Qed.

(** The matched access, footprinted.  The two extra hypotheses are what
    the recognizer can supply and the packaging needs: the body's
    structured footprint is dominated by the *source* certificate's, and
    the body is access-safe whenever the opened state is outside an
    atomic block.  The access node's own boundary is dominated for free,
    since [certificate_footprint] always contains the masks and open sets
    at its two ends. *)
Definition footprinted_resource_normalization_close_one_marker_target
    {Γ F Δ cost entry opened inner}
    {pre post : Resource.resource_prenex Γ F Δ} {source : stmt Γ}
    invariant (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (body : stmt Γ)
    (source_derivation : ResourceRules.RavenResourceTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source (GenericRegions.Atomicity.fold_invariant invariant inner))
    (Hopen : GenericRegions.Atomicity.open_invariant invariant entry =
      inr opened)
    (Hbody_certificate : structured_certificate cost Γ opened body inner)
    (Hopen_preserved : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open opened)
    (Htarget : ResourceRules.RavenResourceTriple pre
      (TInvAccess invariant arguments body) post)
    (Herasure : forall names stack,
      Model.runtime_stmt names stack source =
        Model.runtime_stmt names stack body)
    (Hbody_subset : structured_certificate_footprint Hbody_certificate ⊆
      GenericRegions.Atomicity.certificate_footprint source_certificate)
    (Hbody_safe : GenericRegions.Atomicity.analysis_in_atomic opened = false ->
      structured_accesses_outside_atomic Hbody_certificate) :
  @footprinted_resource_normalization_result Γ F Δ cost entry
    (GenericRegions.Atomicity.fold_invariant invariant inner)
    pre post source source_derivation source_certificate.
Proof.
  refine {| footprinted_resource_normalization :=
    resource_normalization_close_one_marker_target invariant arguments body
      source_derivation source_certificate Hopen Hbody_certificate
      Hopen_preserved Htarget Herasure |}.
  - intros marker Hmember.
    simpl in Hmember.
    repeat rewrite elem_of_union in Hmember.
    destruct Hmember as [[[[Hmask | Hopened] | Hexit_mask] | Hexit_open]
      | Hbody_member].
    + exact (GenericRegions.Atomicity.certificate_entry_subset_footprint
        source_certificate marker Hmask).
    + exact (GenericRegions.Atomicity.certificate_entry_open_subset_footprint
        source_certificate marker Hopened).
    + exact (GenericRegions.Atomicity.certificate_exit_subset_footprint
        source_certificate marker Hexit_mask).
    + exact (GenericRegions.Atomicity.certificate_exit_open_subset_footprint
        source_certificate marker Hexit_open).
    + exact (Hbody_subset marker Hbody_member).
  - intros Hentry. simpl. split.
    + exact Hentry.
    + apply Hbody_safe.
      rewrite (GenericRegions.Atomicity.open_invariant_preserves_in_atomic
        invariant entry opened Hopen). exact Hentry.
Defined.


(** Proof-normalization cut for one raw matched access.  This statement is
    kept immediately beside its normalization consumer so the generic
    completeness induction depends on exactly one proof-theoretic seam. *)
Lemma resource_raw_access_target : forall
    {Γ F Δ}
    (invariant : inv_id)
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    outer_node unfold_node body_sequence_node fold_node
    (body : stmt Γ) (pre post : Resource.resource_prenex Γ F Δ),
  pexpr_list_dependencies arguments ## statement_writes body ->
  ResourceRules.RavenResourceTriple pre
    (TSeq outer_node (TUnfold unfold_node invariant arguments)
      (TSeq body_sequence_node body
        (TFold fold_node invariant arguments))) post ->
  ResourceRules.RavenResourceTriple pre
    (TInvAccess invariant arguments body) post.
Proof.
  intros Γ F Δ invariant arguments outer_node unfold_node body_sequence_node
    fold_node body pre post Hstable Hraw.
  destruct (ResourceRules.RavenResourceTriple_unfold_body_fold_spines
    outer_node unfold_node body_sequence_node fold_node invariant arguments
    body pre post Hraw)
    as (body_pre & body_post & opening_focus & closing_focus &
      Hopening & Hbody & Hclosing).
  eapply ResourceRules.RTInvAccessIndependent.
  - exact Hstable.
  - exact Hopening.
  - exact Hbody.
  - exact Hclosing.
Qed.


(** Inversion facts for the executable worker used by the completeness
    induction below.  These expose the recursive fuel and normalized shape
    without adding any proof-side structure to the worker. *)
Lemma restricted_normalize_access_neutral_sequence_inv {Γ} (fuel : nat)
    (node : node_id) (first second normalized : stmt Γ) :
  access_neutral first ->
  restricted_normalize_statement_fuel (S fuel) (TSeq node first second) =
    Some normalized ->
  exists normalized_second,
    restricted_normalize_statement_fuel fuel first = Some first /\
    restricted_normalize_statement_fuel fuel second = Some normalized_second /\
    normalized = TSeq node first normalized_second.
Proof.
  intros Hneutral Hworker.
  remember (restricted_normalize_statement_fuel fuel first) as first_result
    eqn:Hfirst.
  remember (restricted_normalize_statement_fuel fuel second) as second_result
    eqn:Hsecond.
  destruct first_result as [normalized_first|]; [|].
  2: { destruct first; cbn [access_neutral] in Hneutral; try contradiction;
      cbn [restricted_normalize_statement_fuel] in Hworker;
      rewrite <- Hfirst in Hworker; discriminate. }
  destruct second_result as [normalized_second|]; [|].
  2: { destruct first; cbn [access_neutral] in Hneutral; try contradiction;
      cbn [restricted_normalize_statement_fuel] in Hworker;
      rewrite <- Hfirst, <- Hsecond in Hworker; discriminate. }
  pose proof (unfold_free_normalize_statement_identity first fuel
    normalized_first (restricted_access_neutral_unfold_free first Hneutral)
    (eq_sym Hfirst)) as Hidentity.
  subst normalized_first.
  destruct first; cbn [access_neutral] in Hneutral; try contradiction;
    cbn [restricted_normalize_statement_fuel] in Hworker;
    rewrite <- Hfirst, <- Hsecond in Hworker;
    inversion Hworker; subst;
    exists normalized_second; repeat split; try reflexivity; eauto.
Qed.

Lemma baseline_normalizable_unfold_absurd {Γ} node invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant)) :
  baseline_normalizable (TUnfold node invariant arguments) -> False.
Proof. intro H. inversion H; cbn in *; contradiction. Qed.

Lemma restricted_normalize_baseline_sequence_inv {Γ} fuel node
    (first second normalized : stmt Γ) :
  baseline_normalizable first ->
  restricted_normalize_statement_fuel (S fuel) (TSeq node first second) =
    Some normalized ->
  exists normalized_first normalized_second,
    restricted_normalize_statement_fuel fuel first = Some normalized_first /\
    restricted_normalize_statement_fuel fuel second = Some normalized_second /\
    normalized = TSeq node normalized_first normalized_second.
Proof.
  intros Hbaseline Hworker.
  remember (restricted_normalize_statement_fuel fuel first) as first_result
    eqn:Hfirst.
  remember (restricted_normalize_statement_fuel fuel second) as second_result
    eqn:Hsecond.
  destruct first_result as [normalized_first|];
    destruct second_result as [normalized_second|].
  all: destruct first; cbn [restricted_normalize_statement_fuel] in Hworker;
    try (exfalso; eapply baseline_normalizable_unfold_absurd; exact Hbaseline);
    rewrite <- ?Hfirst, <- ?Hsecond in Hworker; try discriminate.
  all: inversion Hworker; subst;
    do 2 eexists; repeat split; eauto.
Qed.

Lemma restricted_normalize_terminal_access_inv {Γ} fuel outer_node unfold_node
    body_sequence_node fold_node invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (body normalized : stmt Γ) :
  restricted_normalize_statement_fuel fuel
    (TSeq outer_node (TUnfold unfold_node invariant arguments)
      (TSeq body_sequence_node body (TFold fold_node invariant arguments))) =
    Some normalized ->
  exists remaining,
    fuel = S remaining /\
    restricted_access_boundary_check arguments arguments body = true /\
    normalized = TInvAccess invariant arguments body.
Proof.
  destruct fuel as [|remaining]; cbn [restricted_normalize_statement_fuel];
    try discriminate.
  destruct (decide (invariant = invariant)) as [Heq|Hneq];
    [|contradiction].
  replace Heq with (@eq_refl inv_id invariant) by apply proof_irrelevance.
  cbn.
  remember (restricted_access_boundary_check arguments arguments body)
    as boundary eqn:Hboundary.
  destruct boundary; try discriminate.
  intro Hworker. inversion Hworker; subst.
  exists remaining. repeat split; auto.
Qed.

Lemma restricted_normalize_continued_access_inv {Γ} fuel outer_node
    unfold_node body_sequence_node fold_sequence_node fold_node invariant
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (body work normalized : stmt Γ) :
  restricted_normalize_statement_fuel fuel
    (TSeq outer_node (TUnfold unfold_node invariant arguments)
      (TSeq body_sequence_node body
        (TSeq fold_sequence_node (TFold fold_node invariant arguments) work))) =
    Some normalized ->
  exists remaining normalized_work,
    fuel = S remaining /\
    restricted_access_boundary_check arguments arguments body = true /\
    restricted_normalize_statement_fuel remaining work = Some normalized_work /\
    normalized = TSeq outer_node (TInvAccess invariant arguments body)
      normalized_work.
Proof.
  destruct fuel as [|remaining]; cbn [restricted_normalize_statement_fuel];
    try discriminate.
  destruct (decide (invariant = invariant)) as [Heq|Hneq];
    [|contradiction].
  replace Heq with (@eq_refl inv_id invariant) by apply proof_irrelevance.
  cbn.
  remember (restricted_access_boundary_check arguments arguments body)
    as boundary eqn:Hboundary.
  destruct boundary; try discriminate.
  remember (restricted_normalize_statement_fuel remaining work)
    as work_result eqn:Hwork.
  destruct work_result as [normalized_work|]; try discriminate.
  intro Hworker. inversion Hworker; subst.
  exists remaining, normalized_work. repeat split; auto.
Qed.

Lemma conditional_resource_normalization_complete_from_worker
    {Γ F Δ cost entry exit node condition then_branch else_branch}
    {pre post : Resource.resource_prenex Γ F Δ}
    (derivation : ResourceRules.RavenResourceTriple pre
      (TIf node condition then_branch else_branch) post)
    (certificate : GenericRegions.Atomicity.analysis_certificate cost Γ entry
      (TIf node condition then_branch else_branch) exit)
    (Hthen : forall F0 Δ0 then_exit
      (then_pre then_post : Resource.resource_prenex Γ F0 Δ0)
      (then_derivation : ResourceRules.RavenResourceTriple then_pre
        then_branch then_post)
      (then_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
        entry then_branch then_exit),
      GenericRegions.Atomicity.lifo_certificate then_certificate [] [] ->
      forall fuel normalized,
      restricted_normalize_statement_fuel fuel then_branch = Some normalized ->
      exists result : @footprinted_resource_normalization_result Γ F0 Δ0 cost
          entry then_exit then_pre then_post then_branch then_derivation
          then_certificate,
        resource_normalized_statement
          result.(footprinted_resource_normalization) = normalized)
    (Helse : forall F0 Δ0 else_exit
      (else_pre else_post : Resource.resource_prenex Γ F0 Δ0)
      (else_derivation : ResourceRules.RavenResourceTriple else_pre
        else_branch else_post)
      (else_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
        entry else_branch else_exit),
      GenericRegions.Atomicity.lifo_certificate else_certificate [] [] ->
      forall fuel normalized,
      restricted_normalize_statement_fuel fuel else_branch = Some normalized ->
      exists result : @footprinted_resource_normalization_result Γ F0 Δ0 cost
          entry else_exit else_pre else_post else_branch else_derivation
          else_certificate,
        resource_normalized_statement
          result.(footprinted_resource_normalization) = normalized) :
  GenericRegions.Atomicity.lifo_certificate certificate [] [] ->
  forall fuel normalized,
  restricted_normalize_statement_fuel fuel
    (TIf node condition then_branch else_branch) = Some normalized ->
  exists result : @footprinted_resource_normalization_result Γ F Δ cost
      entry exit pre post (TIf node condition then_branch else_branch)
      derivation certificate,
    resource_normalized_statement
      result.(footprinted_resource_normalization) = normalized.
Proof.
  destruct (resource_certificate_aligned_complete_exists Δ pre post
    (TIf node condition then_branch else_branch) derivation entry exit
    certificate) as (aligned & _).
  dependent induction aligned; try discriminate.
  all: intros Hlifo fuel normalized Hworker.
  - destruct Hlifo as [Hthen_lifo Helse_lifo].
    destruct fuel as [|fuel]; cbn [restricted_normalize_statement_fuel]
      in Hworker; try discriminate.
    remember (restricted_normalize_statement_fuel fuel then_branch)
      as then_result eqn:Hthen_worker.
    remember (restricted_normalize_statement_fuel fuel else_branch)
      as else_result eqn:Helse_worker.
    destruct then_result as [normalized_then|]; try discriminate.
    destruct else_result as [normalized_else|]; try discriminate.
    destruct (Hthen F Δ then_exit _ post then_derivation then_certificate
      Hthen_lifo fuel normalized_then (eq_sym Hthen_worker))
      as (then_result & Hthen_result).
    destruct (Helse F Δ else_exit _ post else_derivation else_certificate
      Helse_lifo fuel normalized_else (eq_sym Helse_worker))
      as (else_result & Helse_result).
    eapply footprinted_resource_normalization_conditional_from_worker
      with (then_result := then_result) (else_result := else_result)
      (fuel := fuel); try eassumption.
    + symmetry. exact Hthen_worker.
    + symmetry. exact Helse_worker.
    + cbn [restricted_normalize_statement_fuel].
      rewrite <- Hthen_worker, <- Helse_worker. exact Hworker.
  - destruct (IHaligned node condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hlifo
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_resource_normalization_frame frame derivation0
      certificate result). exact Hresult.
  - destruct (IHaligned node condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hlifo
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_resource_normalization_prenex_elim derivation0
      certificate result). exact Hresult.
  - destruct (IHaligned node condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hlifo
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_resource_normalization_prenex_preserve derivation0
      certificate result). exact Hresult.
  - destruct (IHaligned node condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hlifo
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_resource_normalization_prenex_consequence derivation0
      certificate result pre_entails post_entails). exact Hresult.
  - destruct (IHaligned node condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hlifo
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_resource_normalization_consequence derivation0
      certificate result pre_entails post_entails). exact Hresult.
  - destruct (IHaligned node condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hlifo
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_resource_normalization_stack_rewrite derivation0
      certificate result store_equal). exact Hresult.
  - destruct (IHaligned node condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hlifo
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_resource_normalization_bound_weaken derivation0
      certificate result). exact Hresult.
Qed.

(** Worker-indexed completeness.  The syntax witness supplies the induction
    principle; the Hoare derivation is decomposed extensionally, so its proof
    wrappers do not become a second executable normalizer. *)
Lemma baseline_resource_normalization_complete_from_worker
    {Γ} (source : stmt Γ) (Hbaseline : baseline_normalizable source) :
  forall F Δ cost entry exit
    (pre post : Resource.resource_prenex Γ F Δ)
    (derivation : ResourceRules.RavenResourceTriple pre source post)
    (certificate : GenericRegions.Atomicity.analysis_certificate cost Γ
      entry source exit),
  GenericRegions.Atomicity.lifo_certificate certificate [] [] ->
  forall fuel normalized,
  restricted_normalize_statement_fuel fuel source = Some normalized ->
  exists result : @footprinted_resource_normalization_result Γ F Δ cost
      entry exit pre post source derivation certificate,
    resource_normalized_statement
      result.(footprinted_resource_normalization) = normalized.
Proof.
  induction Hbaseline; intros F Δ cost entry exit pre post derivation
    certificate Hlifo fuel normalized Hworker.
  - pose (balanced := unfold_free_balanced_structured_result certificate []
      u Hlifo).
    pose (normalization := resource_normalization_identity derivation
      certificate balanced.(balanced_structured_certificate)).
    pose (result := {| footprinted_resource_normalization := normalization;
      footprinted_resource_normalization_subset :=
        balanced.(balanced_structured_footprint);
      footprinted_resource_normalization_safe :=
        fun _ => balanced.(balanced_structured_safe) |}).
    exists result.
    pose proof (unfold_free_normalize_statement_identity statement fuel normalized
      u Hworker) as Heq.
    cbn. symmetry. exact Heq.
  - dependent destruction certificate; try discriminate.
    cbn in e. inversion e; subst.
    destruct (ResourceRules.RavenResourceTriple_sequence_decompose _ _
      derivation) as (middle_assertion & Hfirst & Hsecond).
    destruct Hlifo as (middle_stack & Hfirst_lifo & Hsecond_lifo).
    assert (Hfirst_same : GenericRegions.Atomicity.lifo_certificate
      certificate1 [] []).
    { apply access_neutral_lifo. exact a. }
    assert (Hmiddle_stack : middle_stack = []).
    { eapply GenericRegions.Atomicity.lifo_certificate_functional;
        eassumption. }
    subst middle_stack.
    destruct fuel as [|fuel]; cbn [restricted_normalize_statement_fuel]
      in Hworker; try discriminate.
    destruct (restricted_normalize_access_neutral_sequence_inv fuel node
      first0 second0 normalized a Hworker)
      as (normalized_second & Hfirst_worker & Hsecond_worker & ->).
    pose (first_balanced := unfold_free_balanced_structured_result
      certificate1 [] (restricted_access_neutral_unfold_free first0 a)
      Hfirst_lifo).
    pose (first_normalization := resource_normalization_identity Hfirst
      certificate1 first_balanced.(balanced_structured_certificate)).
    pose (first_result :=
      {| footprinted_resource_normalization := first_normalization;
         footprinted_resource_normalization_subset :=
           first_balanced.(balanced_structured_footprint);
         footprinted_resource_normalization_safe :=
           fun _ => first_balanced.(balanced_structured_safe) |}).
    destruct (IHHbaseline F Δ cost middle exit middle_assertion post Hsecond
      certificate2 Hsecond_lifo fuel normalized_second Hsecond_worker)
      as (second_result & Hsecond_result).
    replace derivation with (ResourceRules.RTSeq node pre middle_assertion post
      first0 second0 Hfirst Hsecond) by apply proof_irrelevance.
    eapply footprinted_resource_normalization_sequence_from_worker
      with (first_result := first_result) (second_result := second_result);
      try eassumption.
    + reflexivity.
    + destruct first0; cbn in a |- *; try contradiction; exact I.
  - dependent destruction certificate; try discriminate.
    cbn in e. inversion e; subst.
    destruct (ResourceRules.RavenResourceTriple_sequence_decompose _ _
      derivation) as (middle_assertion & Hfirst & Hsecond).
    destruct Hlifo as (middle_stack & Hfirst_lifo & Hsecond_lifo).
    pose proof (baseline_normalizable_empty_output first0 Hbaseline1 cost
      state middle certificate1 middle_stack Hfirst_lifo) as Hmiddle_stack.
    subst middle_stack.
    destruct fuel as [|fuel]; cbn [restricted_normalize_statement_fuel]
      in Hworker; try discriminate.
    destruct (restricted_normalize_baseline_sequence_inv fuel node first0
      second0 normalized Hbaseline1 Hworker)
      as (normalized_first & normalized_second & Hfirst_worker &
        Hsecond_worker & ->).
    destruct (IHHbaseline1 F Δ cost state middle pre middle_assertion Hfirst
      certificate1 Hfirst_lifo fuel normalized_first Hfirst_worker)
      as (first_result & Hfirst_result).
    destruct (IHHbaseline2 F Δ cost middle exit middle_assertion post Hsecond
      certificate2 Hsecond_lifo fuel normalized_second Hsecond_worker)
      as (second_result & Hsecond_result).
    replace derivation with (ResourceRules.RTSeq node pre middle_assertion post
      first0 second0 Hfirst Hsecond) by apply proof_irrelevance.
    eapply footprinted_resource_normalization_sequence_from_worker
      with (first_result := first_result) (second_result := second_result);
      try eassumption.
    destruct first0; cbn; try exact I.
    exfalso. eapply baseline_normalizable_unfold_absurd. exact Hbaseline1.
  - eapply conditional_resource_normalization_complete_from_worker;
      try eassumption.
    + intros F0 Δ0 then_exit then_pre then_post then_derivation
        then_certificate Hthen_lifo fuel0 normalized0 Hthen_worker.
      eapply IHHbaseline1; eassumption.
    + intros F0 Δ0 else_exit else_pre else_post else_derivation
        else_certificate Helse_lifo fuel0 normalized0 Helse_worker.
      eapply IHHbaseline2; eassumption.
  - subst closing_arguments.
    dependent destruction certificate; try discriminate.
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
    destruct Hlifo as (opened_stack & _ & Htail).
    destruct Htail as (body_stack & Hbody_lifo & Hfold_lifo).
    assert (Hbody_same : GenericRegions.Atomicity.lifo_certificate
      certificate2_1 opened_stack opened_stack).
    { apply access_neutral_lifo. exact a. }
    assert (Hbody_stack : body_stack = opened_stack).
    { eapply GenericRegions.Atomicity.lifo_certificate_functional;
        eassumption. }
    subst body_stack.
    pose (balanced := unfold_free_balanced_structured_result certificate2_1
      opened_stack (restricted_access_neutral_unfold_free first a)
      Hbody_lifo).
    pose (target := resource_raw_access_target invariant opening_arguments
      outer_node unfold_node body_sequence_node fold_node first pre post d
      derivation).
    match goal with
    | |- exists _ : @footprinted_resource_normalization_result _ _ _ _ _ _
          _ _ _ _ ?sc, _ =>
        pose (source_certificate := sc)
    end.
    pose (result := footprinted_resource_normalization_close_one_marker_target
      invariant opening_arguments first derivation source_certificate
      e0 balanced.(balanced_structured_certificate)
      (access_neutral_preserves_open certificate2_1 a) target
      (fun names stack => runtime_stmt_linear_access names stack outer_node
        unfold_node body_sequence_node fold_node invariant opening_arguments
        opening_arguments first)
      ltac:(intros marker Hmember;
        pose proof (balanced.(balanced_structured_footprint) marker Hmember);
        cbn [source_certificate GenericRegions.Atomicity.certificate_footprint];
        set_solver)
      (fun _ => balanced.(balanced_structured_safe))).
    destruct (restricted_normalize_terminal_access_inv fuel outer_node
      unfold_node body_sequence_node fold_node invariant opening_arguments
      first normalized Hworker) as (remaining & -> & Hboundary & ->).
    exists result. cbn [result footprinted_resource_normalization_close_one_marker_target
      resource_normalization_close_one_marker_target]. reflexivity.
  - subst closing_arguments.
    dependent destruction certificate; try discriminate.
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
    destruct Hlifo as (opened_stack & Hopen_lifo & Htail).
    destruct Htail as (body_stack & Hbody_lifo & Hfold_work).
    assert (Hbody_same : GenericRegions.Atomicity.lifo_certificate
      certificate2_1 opened_stack opened_stack).
    { apply access_neutral_lifo. exact a. }
    assert (Hbody_stack : body_stack = opened_stack).
    { eapply GenericRegions.Atomicity.lifo_certificate_functional;
        eassumption. }
    subst body_stack.
    destruct Hfold_work as (closed_stack & Hfold_lifo & Hwork_lifo).
    unfold GenericRegions.Atomicity.lifo_certificate in Hfold_lifo.
    destruct Hfold_lifo as
      [(outer_open & Hstack & _)|[Hsame Hnot_open]].
    + cbn in Hopen_lifo. subst opened_stack.
      inversion Hstack; subst outer_open closed_stack.
      destruct (restricted_normalize_continued_access_inv fuel outer_node
        unfold_node body_sequence_node fold_sequence_node fold_node invariant
        opening_arguments first second normalized Hworker)
        as (remaining & normalized_work & -> & Hboundary & Hwork_worker & ->).
      destruct (ResourceRules.RavenResourceTriple_sequence_decompose _ _
        derivation) as (opened_assertion & Hunfold & Htail_derivation).
      destruct (ResourceRules.RavenResourceTriple_sequence_decompose _ _
        Htail_derivation) as (opened_post & Hbody & Hfold_work_derivation).
      destruct (ResourceRules.RavenResourceTriple_sequence_decompose _ _
        Hfold_work_derivation) as (closed_assertion & Hfold & Hwork).
      destruct (IHHbaseline F Δ cost
        (GenericRegions.Atomicity.fold_invariant invariant state1) exit
        closed_assertion post Hwork certificate2_2_2 Hwork_lifo remaining
        normalized_work Hwork_worker) as (work_result & Hwork_result).
      pose (terminal_derivation := ResourceRules.RTSeq outer_node pre
        opened_assertion closed_assertion _ _ Hunfold
        (ResourceRules.RTSeq body_sequence_node opened_assertion opened_post
          closed_assertion _ _ Hbody Hfold)).
      pose (access_derivation := resource_raw_access_target invariant
        opening_arguments outer_node unfold_node body_sequence_node fold_node
        first pre closed_assertion d terminal_derivation).
      pose (target_derivation := ResourceRules.RTSeq outer_node pre
        closed_assertion post _ _ access_derivation
        work_result.(footprinted_resource_normalization).(
          resource_normalization_target_derivation)).
      pose (balanced := unfold_free_balanced_structured_result certificate2_1
        [(invariant, GenericRegions.Atomicity.analysis_open state)]
        (restricted_access_neutral_unfold_free first a) Hbody_lifo).
      match goal with
      | |- exists _ : @footprinted_resource_normalization_result _ _ _ _ _ _
            _ _ _ _ ?sc, _ => pose (source_certificate := sc)
      end.
      subst normalized_work.
      change (exists result : @footprinted_resource_normalization_result
        Γ F Δ cost state exit pre post
        (TSeq outer_node (TUnfold unfold_node invariant opening_arguments)
          (TSeq body_sequence_node first
            (TSeq fold_sequence_node
              (TFold fold_node invariant opening_arguments) second)))
        derivation source_certificate,
        resource_normalized_statement
          result.(footprinted_resource_normalization) =
        TSeq outer_node (TInvAccess invariant opening_arguments first)
          (resource_normalized_statement
            work_result.(footprinted_resource_normalization))).
      replace source_certificate with
        (resource_access_then_source_certificate invariant opening_arguments
          outer_node unfold_node body_sequence_node fold_sequence_node
          fold_node first second certificate2_1 certificate2_2_2 e0)
        by apply Runtime.CertificateFacts.analysis_certificate_unique.
      eapply footprinted_resource_normalization_continued_access_from_worker
        with (body_analysis := certificate2_1)
          (work_result := work_result)
          (Hbody_certificate := balanced.(balanced_structured_certificate))
          (fuel := remaining);
        try eassumption.
      exact (access_neutral_preserves_open certificate2_1 a).
      exact balanced.(balanced_structured_footprint).
      exact (fun _ => balanced.(balanced_structured_safe)).
    + exfalso. apply Hnot_open.
      pose proof (GenericRegions.Atomicity.open_invariant_success
        invariant state state0 e0) as (_ & _ & _ & Hopened).
      rewrite (access_neutral_preserves_open certificate2_1 a), Hopened.
      apply elem_of_union_l, elem_of_singleton_2. reflexivity.
Qed.

(** Closed analyzer-facing completeness.  Successful restricted analysis
    supplies both the syntax induction witness and the worker result; the
    analyzer certificate supplies the balanced empty access stack. *)
Lemma resource_analyzed_normalization_exists
    {cost Γ F Δ pre source entry exit post}
    (analyzed : @resource_analyzed_triple cost Γ F Δ pre source entry exit
      post)
    (Hentry : GenericRegions.Atomicity.analysis_open entry = ∅) :
  restricted_footprinted_resource_normalization_exists
    (resource_analyzed_hoare analyzed)
    (resource_analyzed_certificate analyzed).
Proof.
  pose proof (restricted_fragment_check_sound source
    (resource_analyzed_restricted analyzed)) as Hbaseline.
  pose proof (proj1 (baseline_normalizable_closed_lifo source Hbaseline
    cost entry exit (resource_analyzed_certificate analyzed) Hentry)) as Hlifo.
  destruct (resource_analyzed_worker_succeeds analyzed)
    as (normalized & Hworker).
  unfold restricted_analyze_and_normalize in Hworker.
  rewrite (resource_analyzed_restricted analyzed) in Hworker.
  destruct (baseline_resource_normalization_complete_from_worker source
    Hbaseline F Δ cost entry exit pre post
    (resource_analyzed_hoare analyzed)
    (resource_analyzed_certificate analyzed) Hlifo
    (S (normalization_statement_size source)) normalized Hworker)
    as (result & Hresult).
  exists result. unfold restricted_analyze_and_normalize.
  rewrite (resource_analyzed_restricted analyzed), Hresult. exact Hworker.
Qed.

(** The alignment's node count, used as the traversal's budget.  Every
    recursive call descends at least one constructor, so this bounds the
    depth and the budget never decides anything. *)


End ConditionalNormalizationPrefix.
End Make.
End TypedNormalizationConditional.
