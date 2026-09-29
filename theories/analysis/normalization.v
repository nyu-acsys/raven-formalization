From Coq Require Import ClassicalEpsilon FunctionalExtensionality Lia
  Program.Equality.
From stdpp Require Import gmap sets.

From raven Require Import runtime.erasure analysis.structured_certificates analysis.normalization_base verification.expressions analysis.atomicity verification.assertions verification.ir soundness.runtime_model
  verification.access_layout verification.conditional_derivations
  runtime.conditional_erasure.

Module NormalizationConditional.

Import NormalizationBase.
Import Core IR Runtime IR Core Runtime.Translation.
Import StructuredCertificates.
Import ConditionalDerivations ConditionalErasure.
Import AccessLayout (canonical_branch).
Module ConditionalNormalizationPrefix.
(* Only the erasure is needed here, not the concrete model. *)
Module Erasure := RuntimeErasure.
Module Certified := Runtime.CertifiedRegions.
Module Resource := Runtime.Translation.Resource.
Module RavenHoareRules := Runtime.Validation.Hoare.ResourceHoare.

Section WithContracts.
Context {RAs : ra_base.RAConfig} {Logic : Assertion.LogicSignature}
  {Contracts : RavenHoareRules.ResourceContractEnv}.

(** The Hoare calculus has exactly one stack at every prenex leaf, so
    argument stability holds directly, without a recursive search
    through arbitrary syntax. *)


Lemma runtime_stmt_linear_access {Γ} names stack
    invariant opening_arguments closing_arguments
    (body : stmt Γ) :
  Erasure.runtime_stmt names stack
      (TSeq (TUnfold invariant opening_arguments)
        (TSeq body
          (TFold invariant closing_arguments))) =
    Erasure.runtime_stmt names stack body.
Proof.
  simpl. rewrite Erasure.runtime_seq_noop_r. reflexivity.
Qed.

Lemma runtime_stmt_linear_access_then {Γ} names stack
    invariant
    opening_arguments closing_arguments (body work : stmt Γ) :
  Erasure.runtime_stmt names stack
      (TSeq (TUnfold invariant opening_arguments)
        (TSeq body
          (TSeq
            (TFold invariant closing_arguments) work))) =
    Erasure.runtime_seq
      (Erasure.runtime_stmt names stack body)
      (Erasure.runtime_stmt names stack work).
Proof. reflexivity. Qed.

(** A normalized statement together with the resource derivation and
    structured analyzer certificate that justify it. *)

(* ------------------------------------------------------------------ *)
(** ** The normalization judgment, over resource telescopes

    [normalization_result] packages a source statement's resource
    derivation and structured analyzer certificate together with a
    normalized statement and matching evidence.  Three points matter,
    all enforced by typing rather than by side condition:

      - the pre- and post-conditions are telescopes, so a normalization
        step cannot lose, duplicate, or reorder the distinguished stack;
      - the derivations are [RavenHoareRules.RavenHoareTriple], which has
        no mask indices on the logical judgment;
      - the runtime-erasure obligation is a plain equality between
        erased statements, because normalization is a statement-level
        rewrite and never touches the resource formula.

    *This record is internal.*  It is the payload the constructors
    compose and the type they are stated at; it carries no footprint or
    access-safety guarantee, so it is not what a producer hands out.
    The three-way division the normalization layer settles on is:

      - [normalization_result] -- internal payload and
        constructor-composition type;
      - [footprinted_normalization_result] -- the externally
        produced, certified result;
      - exactly one generic producer, the footprinted traversal.

    There is deliberately no way to inject an unfootprinted
    normalization from outside.  Such a path would bypass precisely the
    two obligations the procedure theorem consumes -- footprint
    domination and access safety -- which is why the hand-supply
    evidence layer was removed rather than kept as an extension point. *)
Record normalization_result {Γ F Δ}
    (entry exit : GenericRegions.Atomicity.analysis_state)
    (pre post : Resource.resource_prenex Γ F Δ) (source : stmt Γ)
    (source_derivation : RavenHoareRules.RavenHoareTriple pre source post)
    (source_certificate :
      GenericRegions.Atomicity.analysis_certificate Γ entry source exit)
    : Type := {
  normalized_statement : stmt Γ;
  normalization_target_derivation :
    RavenHoareRules.RavenHoareTriple pre normalized_statement post;
  normalization_target_certificate :
    structured_certificate Γ entry normalized_statement exit;
  normalization_runtime_erasure : forall names stack,
    Erasure.runtime_stmt names stack source =
      Erasure.runtime_stmt names stack normalized_statement;
}.

#[global] Arguments normalized_statement {_ _ _} {_ _ _ _ _ _ _} _.
#[global] Arguments normalization_target_derivation
  {_ _ _} {_ _ _ _ _ _ _} _.
#[global] Arguments normalization_target_certificate
  {_ _ _} {_ _ _ _ _ _ _} _.
#[global] Arguments normalization_runtime_erasure
  {_ _ _} {_ _ _ _ _ _ _} _ _ _.

(** The identity normalization: any source statement normalizes to itself
    once its analyzer certificate is already structured.  This is the base
    case every later constructor composes with, and it is what makes the
    record inhabited independently of the rewrite library. *)
Definition normalization_identity {Γ F Δ}
    {entry exit} {pre post : Resource.resource_prenex Γ F Δ}
    {source : stmt Γ}
    (source_derivation : RavenHoareRules.RavenHoareTriple pre source post)
    (source_certificate :
      GenericRegions.Atomicity.analysis_certificate Γ entry source exit)
    (structured : structured_certificate Γ entry source exit) :
    normalization_result entry exit pre post source
      source_derivation source_certificate :=
  {| normalized_statement := source;
     normalization_target_derivation := source_derivation;
     normalization_target_certificate := structured;
     normalization_runtime_erasure :=
       fun names stack => eq_refl |}.

(** Footprint- and atomicity-strengthened form of [normalization_result].

    This is the *external* result type: the only thing the generic
    producer returns and the only thing the procedure boundary accepts.
    Its two extra fields are exactly what
    [term_certified_body_source_valid] needs in order to
    discharge structured validity without a premise. *)
Record footprinted_normalization_result {Γ F Δ}
    (entry exit : GenericRegions.Atomicity.analysis_state)
    (pre post : Resource.resource_prenex Γ F Δ) (source : stmt Γ)
    (source_derivation : RavenHoareRules.RavenHoareTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit) : Type := {
  footprinted_normalization :
    @normalization_result Γ F Δ entry exit pre post source
      source_derivation source_certificate;
  footprinted_normalization_subset :
    structured_certificate_footprint
      footprinted_normalization.(
        normalization_target_certificate) ⊆
    GenericRegions.Atomicity.certificate_footprint source_certificate;
  footprinted_normalization_safe :
    GenericRegions.Atomicity.analysis_in_atomic entry = false ->
    structured_accesses_outside_atomic
      footprinted_normalization.(
        normalization_target_certificate);
}.

#[global] Arguments footprinted_normalization {_ _ _} {_ _ _ _ _ _ _} _.
#[global] Arguments footprinted_normalization_subset {_ _ _}
  {_ _ _ _ _ _ _} _ _ _.
#[global] Arguments footprinted_normalization_safe {_ _ _}
  {_ _ _ _ _ _ _} _ _.

(** Public restricted-normalization contract.  The executable worker chooses
    only the target syntax; the existence of its resource derivation and
    structured certificate is proved in [Prop].  Consequently successful
    analysis never has to reduce a Hoare derivation, alignment witness, or
    semantic proof. *)
Definition restricted_footprinted_normalization_exists
    {Γ F Δ entry exit pre post source}
    (derivation : RavenHoareRules.RavenHoareTriple pre source post)
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit) : Prop :=
  exists result : @footprinted_normalization_result Γ F Δ
      entry exit pre post source derivation certificate,
    restricted_analyze_and_normalize source =
      Some (normalized_statement
        result.(footprinted_normalization)).


(** Structural composition of two resource normalizations across a
    source sequence: the two erasure equations compose. *)
Definition normalization_sequence
    {Γ F Δ entry middle exit}
    {pre middle_prenex post : Resource.resource_prenex Γ F Δ}
    {first second : stmt Γ}
    (first_derivation :
      RavenHoareRules.RavenHoareTriple pre first middle_prenex)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry first middle)
    (first_normalization : @normalization_result Γ F Δ entry
      middle pre middle_prenex first first_derivation first_certificate)
    (second_derivation :
      RavenHoareRules.RavenHoareTriple middle_prenex second post)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      middle second exit)
    (second_normalization : @normalization_result Γ F Δ middle
      exit middle_prenex post second second_derivation second_certificate)
    (view : RegionSyntax.view (TSeq first second) =
      AnalysisView.ViewSequence first second) :
  let source := TSeq first second in
  let source_derivation := RavenHoareRules.RTSeq pre middle_prenex post
    first second first_derivation second_derivation in
  let source_certificate := GenericRegions.Atomicity.CertSequence Γ
    entry source first middle second exit view first_certificate
      second_certificate in
  @normalization_result Γ F Δ entry exit pre post source
    source_derivation source_certificate.
Proof.
  simpl.
  refine {| normalized_statement := TSeq
      first_normalization.(normalized_statement)
      second_normalization.(normalized_statement);
    normalization_target_derivation :=
      RavenHoareRules.RTSeq pre middle_prenex post _ _
        first_normalization.(normalization_target_derivation)
        second_normalization.(normalization_target_derivation);
    normalization_target_certificate :=
      StructuredSequence Γ entry _ middle _ exit
        first_normalization.(normalization_target_certificate)
        second_normalization.(normalization_target_certificate) |}.
  intros names stack. simpl.
  rewrite (first_normalization.(normalization_runtime_erasure)
    names stack).
  rewrite (second_normalization.(normalization_runtime_erasure)
    names stack).
  reflexivity.
Defined.

(* ------------------------------------------------------------------ *)
(** ** Structural normalization constructors

    Proof-only Hoare wrappers: the normalized statement, its structured
    certificate and its erasure equation are untouched, and only the
    derivation is rewrapped.

    There is a single consequence constructor rather than a separate
    stack-consequence one: the store is a field of the resource state,
    and [RTConsequence] *is* body-level consequence, so
    [normalization_consequence] already covers weakening the body under
    a fixed stack.  A genuine change of store is the separate
    [normalization_stack_rewrite]. *)

Definition normalization_frame
    {Γ F Δ entry exit}
    {store : symbolic_store Γ F Δ}
    {pre_body : Resource.core_assertion F Δ}
    {post : Resource.resource_prenex Γ F Δ} {source}
    (frame : Resource.core_assertion F Δ)
    (source_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store pre_body) source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (normalization : @normalization_result Γ F Δ entry exit
      (Resource.RState store pre_body) post source source_derivation
      source_certificate) :
  @normalization_result Γ F Δ entry exit
    (Resource.RState store (Resource.CAnd pre_body frame))
    (Resource.prenex_and post frame) source
    (RavenHoareRules.RTFrame source store pre_body frame post
      source_derivation)
    source_certificate :=
  {| normalized_statement :=
       normalization.(normalized_statement);
     normalization_target_derivation :=
       RavenHoareRules.RTFrame _ store pre_body frame post
         normalization.(normalization_target_derivation);
     normalization_target_certificate :=
       normalization.(normalization_target_certificate);
     normalization_runtime_erasure :=
       normalization.(normalization_runtime_erasure) |}.

Definition normalization_consequence
    {Γ F Δ entry exit}
    {store : symbolic_store Γ F Δ}
    {pre_body pre_body' : Resource.core_assertion F Δ}
    {post post' : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store pre_body) source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (normalization : @normalization_result Γ F Δ entry exit
      (Resource.RState store pre_body) post source source_derivation
      source_certificate)
    (Hpre : Hoare.ResourceHoare.core_entails pre_body' pre_body)
    (Hpost : Hoare.ResourceHoare.resource_prenex_entails post post') :
  @normalization_result Γ F Δ entry exit
    (Resource.RState store pre_body') post' source
    (RavenHoareRules.RTConsequence source store pre_body pre_body' post post'
      source_derivation Hpre Hpost)
    source_certificate :=
  {| normalized_statement :=
       normalization.(normalized_statement);
     normalization_target_derivation :=
       RavenHoareRules.RTConsequence _ store pre_body pre_body' post post'
         normalization.(normalization_target_derivation) Hpre Hpost;
     normalization_target_certificate :=
       normalization.(normalization_target_certificate);
     normalization_runtime_erasure :=
       normalization.(normalization_runtime_erasure) |}.

Definition normalization_stack_rewrite
    {Γ F Δ entry exit}
    {store store' : symbolic_store Γ F Δ}
    {body : Resource.core_assertion F Δ}
    {post : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store body) source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (normalization : @normalization_result Γ F Δ entry exit
      (Resource.RState store body) post source source_derivation
      source_certificate)
    (Hstore : Hoare.ResourceHoare.store_equal_under body Γ store' store) :
  @normalization_result Γ F Δ entry exit
    (Resource.RState store' body) post source
    (RavenHoareRules.RTStackRewrite source store store' body post
      source_derivation Hstore)
    source_certificate :=
  {| normalized_statement :=
       normalization.(normalized_statement);
     normalization_target_derivation :=
       RavenHoareRules.RTStackRewrite _ store store' body post
         normalization.(normalization_target_derivation) Hstore;
     normalization_target_certificate :=
       normalization.(normalization_target_certificate);
     normalization_runtime_erasure :=
       normalization.(normalization_runtime_erasure) |}.

Definition normalization_prenex_elim
    {Γ F Δ t entry exit}
    {pre : Resource.resource_prenex Γ F (t :: Δ)}
    {post : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : RavenHoareRules.RavenHoareTriple
      pre source (Resource.weaken_resource_prenex post))
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (normalization : @normalization_result Γ F (t :: Δ) entry
      exit pre (Resource.weaken_resource_prenex post) source
      source_derivation source_certificate) :
  @normalization_result Γ F Δ entry exit
    (Resource.ResourceExists t pre) post source
    (RavenHoareRules.RTPrenexElim t source pre post source_derivation)
    source_certificate :=
  {| normalized_statement :=
       normalization.(normalized_statement);
     normalization_target_derivation :=
       RavenHoareRules.RTPrenexElim t _ pre post
         normalization.(normalization_target_derivation);
     normalization_target_certificate :=
       normalization.(normalization_target_certificate);
     normalization_runtime_erasure :=
       normalization.(normalization_runtime_erasure) |}.

Definition normalization_prenex_preserve
    {Γ F Δ t entry exit}
    {pre post : Resource.resource_prenex Γ F (t :: Δ)} {source}
    (source_derivation : RavenHoareRules.RavenHoareTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (normalization : @normalization_result Γ F (t :: Δ) entry
      exit pre post source source_derivation source_certificate) :
  @normalization_result Γ F Δ entry exit
    (Resource.ResourceExists t pre) (Resource.ResourceExists t post) source
    (RavenHoareRules.RTPrenexPreserve t source pre post source_derivation)
    source_certificate :=
  {| normalized_statement :=
       normalization.(normalized_statement);
     normalization_target_derivation :=
       RavenHoareRules.RTPrenexPreserve t _ pre post
         normalization.(normalization_target_derivation);
     normalization_target_certificate :=
       normalization.(normalization_target_certificate);
     normalization_runtime_erasure :=
       normalization.(normalization_runtime_erasure) |}.

Definition normalization_bound_weaken
    {Γ F Δ t entry exit}
    {pre post : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : RavenHoareRules.RavenHoareTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (normalization : @normalization_result Γ F Δ entry exit
      pre post source source_derivation source_certificate) :
  @normalization_result Γ F (t :: Δ) entry exit
    (Resource.weaken_resource_prenex pre)
    (Resource.weaken_resource_prenex post) source
    (RavenHoareRules.RTBoundWeaken t source pre post source_derivation)
    source_certificate :=
  {| normalized_statement :=
       normalization.(normalized_statement);
     normalization_target_derivation :=
       RavenHoareRules.RTBoundWeaken t _ pre post
         normalization.(normalization_target_derivation);
     normalization_target_certificate :=
       normalization.(normalization_target_certificate);
     normalization_runtime_erasure :=
       normalization.(normalization_runtime_erasure) |}.

Definition normalization_track
    {Γ F Δ entry exit}
    {pre post : Resource.resource_prenex Γ F Δ} {source}
    t (expression : gexpr Γ t) (value : Core.expr F Δ t)
    (stable : RavenHoareRules.pexpr_dependencies expression ##
      RavenHoareRules.statement_writes source)
    (source_derivation : RavenHoareRules.RavenHoareTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (normalization : @normalization_result Γ F Δ entry exit
      pre post source source_derivation source_certificate)
    (target_stable : RavenHoareRules.pexpr_dependencies expression ##
      RavenHoareRules.statement_writes normalization.(normalized_statement)) :
  @normalization_result Γ F Δ entry exit
    (RavenHoareRules.track_prenex expression pre value)
    (RavenHoareRules.track_prenex expression post value) source
    (RavenHoareRules.RTTrack t expression value source pre post stable
      source_derivation)
    source_certificate :=
  {| normalized_statement :=
       normalization.(normalized_statement);
     normalization_target_derivation :=
       RavenHoareRules.RTTrack t expression value _ pre post target_stable
         normalization.(normalization_target_derivation);
     normalization_target_certificate :=
       normalization.(normalization_target_certificate);
     normalization_runtime_erasure :=
       normalization.(normalization_runtime_erasure) |}.

Definition normalization_prenex_consequence
    {Γ F Δ entry exit}
    {pre pre' post post' : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : RavenHoareRules.RavenHoareTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (normalization : @normalization_result Γ F Δ entry exit
      pre post source source_derivation source_certificate)
    (Hpre : Hoare.ResourceHoare.resource_prenex_entails pre' pre)
    (Hpost : Hoare.ResourceHoare.resource_prenex_entails post post') :
  @normalization_result Γ F Δ entry exit
    pre' post' source
    (RavenHoareRules.RTPrenexConsequence source pre pre' post post'
      source_derivation Hpre Hpost) source_certificate :=
  {| normalized_statement :=
       normalization.(normalized_statement);
     normalization_target_derivation :=
       RavenHoareRules.RTPrenexConsequence _ pre pre' post post'
         normalization.(normalization_target_derivation) Hpre Hpost;
     normalization_target_certificate :=
       normalization.(normalization_target_certificate);
     normalization_runtime_erasure :=
       normalization.(normalization_runtime_erasure) |}.

Definition normalization_conditional
    {Γ F Δ entry then_exit else_exit}
    {store : symbolic_store Γ F Δ}
    {body : Resource.core_assertion F Δ}
    {condition then_branch else_branch}
    {post : Resource.resource_prenex Γ F Δ}
    (then_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (IR.symbolize_expr store condition))))
      then_branch post)
    (then_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry then_branch then_exit)
    (then_normalization : @normalization_result Γ F Δ entry
      then_exit _ post then_branch then_derivation then_certificate)
    (else_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (Core.EUnOp Core.UNot
            (IR.symbolize_expr store condition)))))
      else_branch post)
    (else_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry else_branch else_exit)
    (else_normalization : @normalization_result Γ F Δ entry
      else_exit _ post else_branch else_derivation else_certificate)
    (Hrecords_equal : GenericRegions.Atomicity.analysis_records then_exit =
      GenericRegions.Atomicity.analysis_records else_exit)
    (Hatomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (view : RegionSyntax.view (TIf condition then_branch else_branch) =
      AnalysisView.ViewConditional then_branch else_branch) :
  let source := TIf condition then_branch else_branch in
  let joined := GenericRegions.Atomicity.AnalysisState
    (GenericRegions.Atomicity.entries_meet
      (GenericRegions.Atomicity.analysis_entries then_exit)
      (GenericRegions.Atomicity.analysis_entries else_exit))
    (GenericRegions.Atomicity.analysis_records then_exit)
    (GenericRegions.Atomicity.analysis_step_taken then_exit ||
      GenericRegions.Atomicity.analysis_step_taken else_exit)
    (GenericRegions.Atomicity.analysis_in_atomic then_exit) in
  let source_derivation := RavenHoareRules.RTIf store body condition
    then_branch else_branch post then_derivation else_derivation in
  let source_certificate := GenericRegions.Atomicity.CertConditional Γ
    entry source then_branch else_branch then_exit else_exit view
      then_certificate else_certificate Hrecords_equal Hatomic_equal in
  @normalization_result Γ F Δ entry joined
    (Resource.RState store body) post source
    source_derivation source_certificate.
Proof.
  simpl.
  refine {| normalized_statement := TIf condition
      then_normalization.(normalized_statement)
      else_normalization.(normalized_statement);
    normalization_target_derivation :=
      RavenHoareRules.RTIf store body condition _ _ post
        then_normalization.(normalization_target_derivation)
        else_normalization.(normalization_target_derivation);
    normalization_target_certificate :=
      StructuredConditional Γ entry condition _ _ then_exit
        else_exit
        then_normalization.(normalization_target_certificate)
        else_normalization.(normalization_target_certificate)
        Hrecords_equal Hatomic_equal |}.
  intros names stack. simpl.
  rewrite (then_normalization.(normalization_runtime_erasure)
    names stack).
  rewrite (else_normalization.(normalization_runtime_erasure)
    names stack).
  reflexivity.
Defined.

(** A ghost value binder normalizes by normalizing its body. *)
Definition normalization_ghost_val
    {Γ F Δ entry exit}
    {store : symbolic_store Γ F Δ} {frame : Resource.core_assertion F Δ}
    {name t} {initializer : gexpr Γ t} {body : stmt (ghost_val t :: Γ)}
    {post : Resource.resource_prenex (ghost_val t :: Γ) F (t :: Δ)}
    (body_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState (StoreCons (d := ghost_val t) (RefBound MHere)
          (Assertions.weaken_store store))
        (Resource.CAnd (Resource.weaken_core frame)
          (Resource.CExpr (EBinOp (BEq t) (ERef (RefBound MHere))
            (Assertions.weaken_expr (IR.symbolize_expr store initializer))))))
      body post)
    (body_certificate : GenericRegions.Atomicity.analysis_certificate
      (ghost_val t :: Γ) entry body exit)
    (body_normalization : @normalization_result (ghost_val t :: Γ) F (t :: Δ)
      entry exit _ post body body_derivation body_certificate)
    (view : RegionSyntax.view (TGhostVal name t initializer body) =
      AnalysisView.ViewScope (ghost_val t) body)
    (admissible : GenericRegions.Atomicity.leave_scope_admissible
      (length Γ) exit = true) :
  @normalization_result Γ F Δ entry
    (GenericRegions.Atomicity.leave_scope (length Γ) entry exit)
    (Resource.RState store frame)
    (Resource.ResourceExists t (Resource.drop_head_prenex post))
    (TGhostVal name t initializer body)
    (RavenHoareRules.RTGhostVal name t initializer body store frame post
      body_derivation)
    (GenericRegions.Atomicity.CertScope Γ entry
      (TGhostVal name t initializer body) (ghost_val t) body exit view
      body_certificate admissible).
Proof.
  refine {| normalized_statement := TGhostVal name t initializer
      body_normalization.(normalized_statement);
    normalization_target_derivation :=
      RavenHoareRules.RTGhostVal name t initializer _ store frame post
        body_normalization.(normalization_target_derivation);
    normalization_target_certificate :=
      StructuredGhostVal Γ entry name t initializer _ exit
        body_normalization.(normalization_target_certificate) admissible |}.
  intros names stack. simpl.
  exact (body_normalization.(normalization_runtime_erasure)
    (NCCons name (ghost_val t) names) stack).
Defined.

(** *** Footprint transport

    A proof-only Hoare wrapper leaves both the normalized syntax and its
    structured certificate unchanged, so the strengthened record's two
    fields transport with no set reasoning at all. *)
Definition footprinted_normalization_frame
    {Γ F Δ entry exit}
    {store : symbolic_store Γ F Δ}
    {pre_body : Resource.core_assertion F Δ}
    {post : Resource.resource_prenex Γ F Δ} {source}
    (frame : Resource.core_assertion F Δ)
    (source_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store pre_body) source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (result : @footprinted_normalization_result Γ F Δ entry exit
      (Resource.RState store pre_body) post source source_derivation
      source_certificate) :
  @footprinted_normalization_result Γ F Δ entry exit
    (Resource.RState store (Resource.CAnd pre_body frame))
    (Resource.prenex_and post frame) source
    (RavenHoareRules.RTFrame source store pre_body frame post
      source_derivation)
    source_certificate :=
  {| footprinted_normalization :=
       normalization_frame frame source_derivation
         source_certificate result.(footprinted_normalization);
     footprinted_normalization_subset :=
       result.(footprinted_normalization_subset);
     footprinted_normalization_safe :=
       result.(footprinted_normalization_safe) |}.

Definition footprinted_normalization_consequence
    {Γ F Δ entry exit}
    {store : symbolic_store Γ F Δ}
    {pre_body pre_body' : Resource.core_assertion F Δ}
    {post post' : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store pre_body) source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (result : @footprinted_normalization_result Γ F Δ entry exit
      (Resource.RState store pre_body) post source source_derivation
      source_certificate)
    (Hpre : Hoare.ResourceHoare.core_entails pre_body' pre_body)
    (Hpost : Hoare.ResourceHoare.resource_prenex_entails post post') :
  @footprinted_normalization_result Γ F Δ entry exit
    (Resource.RState store pre_body') post' source
    (RavenHoareRules.RTConsequence source store pre_body pre_body' post post'
      source_derivation Hpre Hpost)
    source_certificate :=
  {| footprinted_normalization :=
       normalization_consequence source_derivation
         source_certificate result.(footprinted_normalization)
         Hpre Hpost;
     footprinted_normalization_subset :=
       result.(footprinted_normalization_subset);
     footprinted_normalization_safe :=
       result.(footprinted_normalization_safe) |}.

Definition footprinted_normalization_stack_rewrite
    {Γ F Δ entry exit}
    {store store' : symbolic_store Γ F Δ}
    {body : Resource.core_assertion F Δ}
    {post : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store body) source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (result : @footprinted_normalization_result Γ F Δ entry exit
      (Resource.RState store body) post source source_derivation
      source_certificate)
    (Hstore : Hoare.ResourceHoare.store_equal_under body Γ store' store) :
  @footprinted_normalization_result Γ F Δ entry exit
    (Resource.RState store' body) post source
    (RavenHoareRules.RTStackRewrite source store store' body post
      source_derivation Hstore)
    source_certificate :=
  {| footprinted_normalization :=
       normalization_stack_rewrite source_derivation
         source_certificate result.(footprinted_normalization)
         Hstore;
     footprinted_normalization_subset :=
       result.(footprinted_normalization_subset);
     footprinted_normalization_safe :=
       result.(footprinted_normalization_safe) |}.

Definition footprinted_normalization_prenex_elim
    {Γ F Δ t entry exit}
    {pre : Resource.resource_prenex Γ F (t :: Δ)}
    {post : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : RavenHoareRules.RavenHoareTriple
      pre source (Resource.weaken_resource_prenex post))
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (result : @footprinted_normalization_result Γ F (t :: Δ)
      entry exit pre (Resource.weaken_resource_prenex post) source
      source_derivation source_certificate) :
  @footprinted_normalization_result Γ F Δ entry exit
    (Resource.ResourceExists t pre) post source
    (RavenHoareRules.RTPrenexElim t source pre post source_derivation)
    source_certificate :=
  {| footprinted_normalization :=
       normalization_prenex_elim source_derivation
         source_certificate result.(footprinted_normalization);
     footprinted_normalization_subset :=
       result.(footprinted_normalization_subset);
     footprinted_normalization_safe :=
       result.(footprinted_normalization_safe) |}.

Definition footprinted_normalization_prenex_preserve
    {Γ F Δ t entry exit}
    {pre post : Resource.resource_prenex Γ F (t :: Δ)} {source}
    (source_derivation : RavenHoareRules.RavenHoareTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (result : @footprinted_normalization_result Γ F (t :: Δ)
      entry exit pre post source source_derivation source_certificate) :
  @footprinted_normalization_result Γ F Δ entry exit
    (Resource.ResourceExists t pre) (Resource.ResourceExists t post) source
    (RavenHoareRules.RTPrenexPreserve t source pre post source_derivation)
    source_certificate :=
  {| footprinted_normalization :=
       normalization_prenex_preserve source_derivation
         source_certificate result.(footprinted_normalization);
     footprinted_normalization_subset :=
       result.(footprinted_normalization_subset);
     footprinted_normalization_safe :=
       result.(footprinted_normalization_safe) |}.

Definition footprinted_normalization_bound_weaken
    {Γ F Δ t entry exit}
    {pre post : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : RavenHoareRules.RavenHoareTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (result : @footprinted_normalization_result Γ F Δ entry exit
      pre post source source_derivation source_certificate) :
  @footprinted_normalization_result Γ F (t :: Δ) entry exit
    (Resource.weaken_resource_prenex pre)
    (Resource.weaken_resource_prenex post) source
    (RavenHoareRules.RTBoundWeaken t source pre post source_derivation)
    source_certificate :=
  {| footprinted_normalization :=
       normalization_bound_weaken source_derivation
         source_certificate result.(footprinted_normalization);
     footprinted_normalization_subset :=
       result.(footprinted_normalization_subset);
     footprinted_normalization_safe :=
       result.(footprinted_normalization_safe) |}.

Definition footprinted_normalization_track
    {Γ F Δ entry exit}
    {pre post : Resource.resource_prenex Γ F Δ} {source}
    t (expression : gexpr Γ t) (value : Core.expr F Δ t)
    (stable : RavenHoareRules.pexpr_dependencies expression ##
      RavenHoareRules.statement_writes source)
    (source_derivation : RavenHoareRules.RavenHoareTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (result : @footprinted_normalization_result Γ F Δ entry exit
      pre post source source_derivation source_certificate)
    (target_stable : RavenHoareRules.pexpr_dependencies expression ##
      RavenHoareRules.statement_writes
        result.(footprinted_normalization).(normalized_statement)) :
  @footprinted_normalization_result Γ F Δ entry exit
    (RavenHoareRules.track_prenex expression pre value)
    (RavenHoareRules.track_prenex expression post value) source
    (RavenHoareRules.RTTrack t expression value source pre post stable
      source_derivation)
    source_certificate :=
  {| footprinted_normalization :=
       normalization_track t expression value stable source_derivation
         source_certificate result.(footprinted_normalization) target_stable;
     footprinted_normalization_subset :=
       result.(footprinted_normalization_subset);
     footprinted_normalization_safe :=
       result.(footprinted_normalization_safe) |}.

Definition footprinted_normalization_prenex_consequence
    {Γ F Δ entry exit}
    {pre pre' post post' : Resource.resource_prenex Γ F Δ} {source}
    (source_derivation : RavenHoareRules.RavenHoareTriple pre source post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (result : @footprinted_normalization_result Γ F Δ entry exit
      pre post source source_derivation source_certificate)
    (Hpre : Hoare.ResourceHoare.resource_prenex_entails pre' pre)
    (Hpost : Hoare.ResourceHoare.resource_prenex_entails post post') :
  @footprinted_normalization_result Γ F Δ entry exit
    pre' post' source
    (RavenHoareRules.RTPrenexConsequence source pre pre' post post'
      source_derivation Hpre Hpost) source_certificate :=
  {| footprinted_normalization :=
       normalization_prenex_consequence source_derivation
         source_certificate result.(footprinted_normalization)
         Hpre Hpost;
     footprinted_normalization_subset :=
       result.(footprinted_normalization_subset);
     footprinted_normalization_safe :=
       result.(footprinted_normalization_safe) |}.

(** The public normalization contract is insensitive to proof-only Hoare
    wrappers.  These lemmas deliberately transport an existential result in
    [Prop]; the executable worker is unchanged because each wrapper leaves
    the source statement unchanged. *)


(* ------------------------------------------------------------------ *)
(** ** Alignment between an analyzer certificate and a resource derivation

    It records that a derivation's structural shape matches the certificate's,
    which lets the normalizer recurse on the source shape instead of inverting
    an arbitrary derivation.

    [AlignedStackConsequence] is gone for the same reason its
    normalization constructor is: [RTConsequence] is body-level
    consequence, so it subsumes the stack-fixed case.  A genuine change
    of store is [AlignedStackRewrite].

    The two fold/unfold cases also carry no separate witness premise:
    [RTUnfoldInvariant] and [RTFoldInvariant] take the opened body to
    *be* [instantiated_invariant] applied to the access arguments. *)
Inductive certificate_aligned :
    forall {Γ F Δ} {entry : GenericRegions.Atomicity.analysis_state}
      {statement : stmt Γ} {exit : GenericRegions.Atomicity.analysis_state}
      {pre post : Resource.resource_prenex Γ F Δ},
      GenericRegions.Atomicity.analysis_certificate Γ entry statement exit ->
      @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ pre statement post ->
      Type :=
| AlignedOrdinaryLeaf : forall Γ F Δ entry statement exit pre post
    view step
    (derivation : @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ pre statement post),
    certificate_aligned
      (GenericRegions.Atomicity.CertLeaf Γ entry statement exit view step)
      derivation
| AlignedDone : forall Γ F Δ entry statement pre post view
    (derivation : @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ pre statement post),
    certificate_aligned
      (GenericRegions.Atomicity.CertDone Γ entry statement view)
      derivation
| AlignedUnfold : forall Γ F Δ entry invariant arguments exit
    (store : symbolic_store Γ F Δ)
    (view : RegionSyntax.view (TUnfold invariant arguments) =
      AnalysisView.ViewUnfold invariant (RegionSyntax.argument_key arguments))
    (step : GenericRegions.Atomicity.open_invariant invariant
      (RegionSyntax.argument_key arguments) entry = inr exit),
    certificate_aligned
      (GenericRegions.Atomicity.CertUnfold Γ entry
        (TUnfold invariant arguments) invariant
        (RegionSyntax.argument_key arguments) exit view step)
      (RavenHoareRules.RTUnfoldInvariant invariant store arguments)
| AlignedFold : forall Γ F Δ entry invariant arguments
    (store : symbolic_store Γ F Δ)
    (view : RegionSyntax.view (TFold invariant arguments) =
      AnalysisView.ViewFold invariant (RegionSyntax.argument_key arguments))
    (admissible : GenericRegions.Atomicity.fold_admissible invariant
      (RegionSyntax.argument_key arguments) entry = true),
    certificate_aligned
      (GenericRegions.Atomicity.CertFold Γ entry
        (TFold invariant arguments) invariant
        (RegionSyntax.argument_key arguments) view admissible)
      (RavenHoareRules.RTFoldInvariant invariant store arguments)
| AlignedSequence : forall Γ F Δ state first middle second exit
    (pre middle_prenex post : Resource.resource_prenex Γ F Δ)
    (view : RegionSyntax.view (TSeq first second) =
      AnalysisView.ViewSequence first second)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      state first middle)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      middle second exit)
    (first_derivation :
      @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ pre first middle_prenex)
    (second_derivation :
      @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ middle_prenex second post),
    certificate_aligned first_certificate first_derivation ->
    certificate_aligned second_certificate second_derivation ->
    certificate_aligned
      (GenericRegions.Atomicity.CertSequence Γ state
        (TSeq first second) first middle second exit view
        first_certificate second_certificate)
      (RavenHoareRules.RTSeq pre middle_prenex post first second
        first_derivation second_derivation)
| AlignedConditional : forall Γ F Δ state
    (store : symbolic_store Γ F Δ) (body : Resource.core_assertion F Δ)
    condition then_branch else_branch then_exit else_exit
    (post : Resource.resource_prenex Γ F Δ)
    (view : RegionSyntax.view (TIf condition then_branch else_branch) =
      AnalysisView.ViewConditional then_branch else_branch)
    (then_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      state then_branch then_exit)
    (else_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      state else_branch else_exit)
    (records_equal : GenericRegions.Atomicity.analysis_records then_exit =
      GenericRegions.Atomicity.analysis_records else_exit)
    (atomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (then_derivation : @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (IR.symbolize_expr store condition))))
      then_branch post)
    (else_derivation : @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (Core.EUnOp Core.UNot
            (IR.symbolize_expr store condition)))))
      else_branch post),
    certificate_aligned then_certificate then_derivation ->
    certificate_aligned else_certificate else_derivation ->
    certificate_aligned
      (GenericRegions.Atomicity.CertConditional Γ state
        (TIf condition then_branch else_branch) then_branch else_branch
        then_exit else_exit view then_certificate else_certificate
        records_equal atomic_equal)
      (RavenHoareRules.RTIf store body condition then_branch else_branch
        post then_derivation else_derivation)
| AlignedAtomic : forall Γ F Δ state body outer inner
    (pre post : Resource.resource_prenex Γ F Δ)
    (view : RegionSyntax.view (TAtomic body) =
      AnalysisView.ViewAtomic body)
    (step : GenericRegions.Atomicity.take_step
      GenericRegions.Atomicity.AtomicStep state = inr outer)
    (body_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_entries outer)
        (GenericRegions.Atomicity.analysis_records outer)
        (GenericRegions.Atomicity.analysis_step_taken outer) true)
      body inner)
    (records_equal : GenericRegions.Atomicity.analysis_records inner =
      GenericRegions.Atomicity.analysis_records outer)
    (body_derivation :
      @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ pre body post),
    certificate_aligned body_certificate body_derivation ->
    certificate_aligned
      (GenericRegions.Atomicity.CertAtomic Γ state (TAtomic body)
        body outer inner view step body_certificate records_equal)
      (RavenHoareRules.RTAtomicBlock pre post body body_derivation)
| AlignedGhostVal : forall Γ F Δ state name t initializer body exit
    (store : symbolic_store Γ F Δ) (frame : Resource.core_assertion F Δ)
    (post : Resource.resource_prenex (ghost_val t :: Γ) F (t :: Δ))
    (view : RegionSyntax.view (TGhostVal name t initializer body) =
      AnalysisView.ViewScope (ghost_val t) body)
    (body_certificate : GenericRegions.Atomicity.analysis_certificate
      (ghost_val t :: Γ) state body exit)
    (admissible : GenericRegions.Atomicity.leave_scope_admissible
      (length Γ) exit = true)
    body_derivation,
    certificate_aligned body_certificate body_derivation ->
    certificate_aligned
      (GenericRegions.Atomicity.CertScope Γ state
        (TGhostVal name t initializer body) (ghost_val t) body exit view
        body_certificate admissible)
      (RavenHoareRules.RTGhostVal name t initializer body store frame post
        body_derivation)
| AlignedFrame : forall Γ F Δ entry exit statement
    (store : symbolic_store Γ F Δ)
    (pre_body frame : Resource.core_assertion F Δ)
    (post : Resource.resource_prenex Γ F Δ)
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry statement exit)
    (derivation : @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ
      (Resource.RState store pre_body) statement post),
    certificate_aligned certificate derivation ->
    certificate_aligned certificate
      (RavenHoareRules.RTFrame statement store pre_body frame post derivation)
| AlignedPrenexElim : forall Γ F Δ t entry exit statement
    (pre : Resource.resource_prenex Γ F (t :: Δ))
    (post : Resource.resource_prenex Γ F Δ)
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry statement exit)
    (derivation : @RavenHoareRules.RavenHoareTriple _ _ _ Γ F (t :: Δ)
      pre statement (Resource.weaken_resource_prenex post)),
    certificate_aligned certificate derivation ->
    certificate_aligned certificate
      (RavenHoareRules.RTPrenexElim t statement pre post derivation)
| AlignedPrenexPreserve : forall Γ F Δ t entry exit statement
    (pre post : Resource.resource_prenex Γ F (t :: Δ))
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry statement exit)
    (derivation :
      @RavenHoareRules.RavenHoareTriple _ _ _ Γ F (t :: Δ) pre statement post),
    certificate_aligned certificate derivation ->
    certificate_aligned certificate
      (RavenHoareRules.RTPrenexPreserve t statement pre post derivation)
| AlignedPrenexConsequence : forall Γ F Δ entry exit statement
    (pre pre' post post' : Resource.resource_prenex Γ F Δ)
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry statement exit)
    (derivation : @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ
      pre statement post)
    (pre_entails : Hoare.ResourceHoare.resource_prenex_entails pre' pre)
    (post_entails : Hoare.ResourceHoare.resource_prenex_entails post post'),
    certificate_aligned certificate derivation ->
    certificate_aligned certificate
      (RavenHoareRules.RTPrenexConsequence statement pre pre' post post'
        derivation pre_entails post_entails)
| AlignedConsequence : forall Γ F Δ entry exit statement
    (store : symbolic_store Γ F Δ)
    (pre_body pre_body' : Resource.core_assertion F Δ)
    (post post' : Resource.resource_prenex Γ F Δ)
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry statement exit)
    (derivation : @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ
      (Resource.RState store pre_body) statement post)
    (pre_entails : Hoare.ResourceHoare.core_entails pre_body' pre_body)
    (post_entails : Hoare.ResourceHoare.resource_prenex_entails post post'),
    certificate_aligned certificate derivation ->
    certificate_aligned certificate
      (RavenHoareRules.RTConsequence statement store pre_body pre_body'
        post post' derivation pre_entails post_entails)
| AlignedStackRewrite : forall Γ F Δ entry exit statement
    (store store' : symbolic_store Γ F Δ)
    (body : Resource.core_assertion F Δ)
    (post : Resource.resource_prenex Γ F Δ)
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry statement exit)
    (derivation : @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ
      (Resource.RState store body) statement post)
    (store_equal : Hoare.ResourceHoare.store_equal_under body Γ store' store),
    certificate_aligned certificate derivation ->
    certificate_aligned certificate
      (RavenHoareRules.RTStackRewrite statement store store' body post
        derivation store_equal)
| AlignedBoundWeaken : forall Γ F Δ t entry exit statement
    (pre post : Resource.resource_prenex Γ F Δ)
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry statement exit)
    (derivation : @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ
      pre statement post),
    certificate_aligned certificate derivation ->
    certificate_aligned certificate
      (RavenHoareRules.RTBoundWeaken t statement pre post derivation)
| AlignedGhostConditional : forall Γ F Δ state
    (store : symbolic_store Γ F Δ) (body : Resource.core_assertion F Δ)
    condition then_branch else_branch then_exit else_exit
    (post : Resource.resource_prenex Γ F Δ)
    (view : RegionSyntax.view (TGhostIf condition then_branch else_branch) =
      AnalysisView.ViewConditional then_branch else_branch)
    (then_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      state then_branch then_exit)
    (else_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      state else_branch else_exit)
    (records_equal : GenericRegions.Atomicity.analysis_records then_exit =
      GenericRegions.Atomicity.analysis_records else_exit)
    (atomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (then_proof_only : proof_onlyb then_branch = true)
    (else_proof_only : proof_onlyb else_branch = true)
    (then_derivation : @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (IR.symbolize_expr store condition))))
      then_branch post)
    (else_derivation : @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (Core.EUnOp Core.UNot
            (IR.symbolize_expr store condition)))))
      else_branch post),
    certificate_aligned then_certificate then_derivation ->
    certificate_aligned else_certificate else_derivation ->
    certificate_aligned
      (GenericRegions.Atomicity.CertConditional Γ state
        (TGhostIf condition then_branch else_branch) then_branch else_branch
        then_exit else_exit view then_certificate else_certificate
        records_equal atomic_equal)
      (RavenHoareRules.RTGhostIf store body condition then_branch else_branch
        post then_proof_only else_proof_only then_derivation else_derivation)
| AlignedTrack : forall Γ F Δ t entry exit statement
    (expression : gexpr Γ t) (value : Core.expr F Δ t)
    (pre post : Resource.resource_prenex Γ F Δ)
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry statement exit)
    (stable : RavenHoareRules.pexpr_dependencies expression ##
      RavenHoareRules.statement_writes statement)
    (derivation : @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ
      pre statement post),
    certificate_aligned certificate derivation ->
    certificate_aligned certificate
      (RavenHoareRules.RTTrack t expression value statement pre post stable
        derivation).

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
Fixpoint certificate_aligned_complete_exists {Γ F} Δ
    (pre post : Resource.resource_prenex Γ F Δ) (statement : stmt Γ)
    (derivation : @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ pre statement post)
    {struct derivation} :
  forall entry exit
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry statement exit),
    exists aligned : certificate_aligned certificate derivation,
      True.
Proof.
  destruct derivation; intros entry exit certificate.
  (* The rules that leave the statement, and hence the certificate,
     alone. *)
  all: try (destruct (certificate_aligned_complete_exists Γ F
              _ _ _ _ derivation entry exit certificate) as [A _];
            unshelve eexists;
              [ solve [ eapply AlignedPrenexPreserve; exact A
                      | eapply AlignedPrenexElim; exact A
                      | eapply AlignedBoundWeaken; exact A
                      | eapply AlignedFrame; exact A
                      | eapply AlignedConsequence; exact A
                      | eapply AlignedStackRewrite; exact A
                      | eapply AlignedPrenexConsequence; exact A
                      | eapply AlignedTrack; exact A ]
              | exact I ]).
  (* Every remaining rule fixes the statement's shape, so the certificate
     is determined up to the cases whose view premise is contradictory. *)
  all: dependent destruction certificate; try discriminate.
  (* The bare unfold and fold need their view equation resolved first:
     the certificate names an invariant of its own, and alignment
     requires it to be the derivation's. *)
  all: try lazymatch goal with
       | [ |- context [RavenHoareRules.RTUnfoldInvariant _ _ _] ] =>
           cbn in e; dependent destruction e
       | [ |- context [RavenHoareRules.RTFoldInvariant _ _ _] ] =>
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
       | [ |- context [RavenHoareRules.RTSeq _ _ _ _ _ ?d1 ?d2] ] =>
           cbn in e; dependent destruction e;
           destruct (certificate_aligned_complete_exists Γ F
             _ _ _ _ d1 _ _ certificate1) as [A1 _];
           destruct (certificate_aligned_complete_exists Γ F
             _ _ _ _ d2 _ _ certificate2) as [A2 _];
           unshelve eexists;
             [eapply AlignedSequence; eassumption | exact I]
       | [ |- context [RavenHoareRules.RTIf _ _ _ _ _ _ ?d1 ?d2] ] =>
           cbn in e; dependent destruction e;
           destruct (certificate_aligned_complete_exists Γ F
             _ _ _ _ d1 _ _ certificate1) as [Athen _];
           destruct (certificate_aligned_complete_exists Γ F
             _ _ _ _ d2 _ _ certificate2) as [Aelse _];
           unshelve eexists;
             [eapply AlignedConditional; eassumption | exact I]
       | [ |- context [RavenHoareRules.RTGhostIf _ _ _ _ _ _ _ _ ?d1 ?d2] ] =>
           match goal with
           | Hview : RegionSyntax.view (TGhostIf _ _ _) = _ |- _ =>
               cbn in Hview; dependent destruction Hview
           end;
           destruct (certificate_aligned_complete_exists Γ F
             _ _ _ _ d1 _ _ certificate1) as [Athen _];
           destruct (certificate_aligned_complete_exists Γ F
             _ _ _ _ d2 _ _ certificate2) as [Aelse _];
           unshelve eexists;
             [eapply AlignedGhostConditional; eassumption | exact I]
       | [ |- context [RavenHoareRules.RTAtomicBlock _ _ _ ?d] ] =>
           cbn in e; dependent destruction e;
           destruct (certificate_aligned_complete_exists Γ F
             _ _ _ _ d _ _ certificate) as [Abody _];
           unshelve eexists;
             [eapply AlignedAtomic; eassumption | exact I]
       | [ |- context [RavenHoareRules.RTGhostVal _ _ _ _ _ _ _ ?d] ] =>
           cbn in e; injection e as Hd Hscope_body; subst;
           apply Eqdep.EqdepTheory.inj_pair2 in Hscope_body; subst;
           destruct (certificate_aligned_complete_exists _ F
             _ _ _ _ d _ _ certificate) as [Abody _];
           unshelve eexists;
             [eapply AlignedGhostVal; eassumption | exact I]
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
    [restricted_footprinted_normalization_exists] below. *)
Record analyzed_triple
    {Γ F Δ}
    (pre : Resource.resource_prenex Γ F Δ) (statement : stmt Γ)
    (entry exit : GenericRegions.Atomicity.analysis_state)
    (post : Resource.resource_prenex Γ F Δ) : Type := {
  analyzed_certificate :
    GenericRegions.Atomicity.analysis_certificate Γ entry statement exit;
  analyzed_hoare :
    @RavenHoareRules.RavenHoareTriple _ _ _ Γ F Δ pre statement post;
  analyzed_restricted : restricted_fragment_accepted statement;
}.

#[global] Arguments analyzed_certificate {_ _ _ _ _ _ _ _} _.
#[global] Arguments analyzed_hoare {_ _ _ _ _ _ _ _} _.
#[global] Arguments analyzed_restricted {_ _ _ _ _ _ _ _} _.

Lemma analyzed_worker_succeeds
    {Γ F Δ pre statement entry exit post}
    (analyzed : @analyzed_triple Γ F Δ pre statement entry exit
      post) :
  exists normalized,
    restricted_analyze_and_normalize statement = Some normalized.
Proof.
  apply restricted_analyze_and_normalize_succeeds.
  exact (analyzed_restricted analyzed).
Qed.

(** RuntimeModel proof-indexed bundle.  It remains temporarily for the old
    producer below, but is not the interface of the redesigned pass:
    [analyzed_triple] plus
    [restricted_footprinted_normalization_exists] is the new
    boundary, and alignment is constructed only inside its proof. *)


Definition footprinted_normalization_sequence
    {Γ F Δ entry middle exit}
    {pre middle_prenex post : Resource.resource_prenex Γ F Δ}
    {first second : stmt Γ}
    (first_derivation :
      RavenHoareRules.RavenHoareTriple pre first middle_prenex)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry first middle)
    (first_result : @footprinted_normalization_result Γ F Δ
      entry middle pre middle_prenex first first_derivation first_certificate)
    (second_derivation :
      RavenHoareRules.RavenHoareTriple middle_prenex second post)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      middle second exit)
    (second_result : @footprinted_normalization_result Γ F Δ
      middle exit middle_prenex post second second_derivation
      second_certificate)
    (view : RegionSyntax.view (TSeq first second) =
      AnalysisView.ViewSequence first second) :
  let source := TSeq first second in
  let source_derivation := RavenHoareRules.RTSeq pre middle_prenex post
    first second first_derivation second_derivation in
  let source_certificate := GenericRegions.Atomicity.CertSequence Γ
    entry source first middle second exit view first_certificate
      second_certificate in
  @footprinted_normalization_result Γ F Δ entry exit pre post
    source source_derivation source_certificate.
Proof.
  simpl.
  refine {| footprinted_normalization :=
    normalization_sequence first_derivation first_certificate
      first_result.(footprinted_normalization) second_derivation
      second_certificate second_result.(footprinted_normalization)
      view |}.
  - intros marker Hmember.
    simpl in Hmember |- *.
    repeat rewrite elem_of_union in Hmember |- *.
    pose proof (first_result.(footprinted_normalization_subset)
      marker) as Hfirst.
    pose proof (second_result.(footprinted_normalization_subset)
      marker) as Hsecond.
    tauto.
  - intros Hentry. split.
    + exact (first_result.(footprinted_normalization_safe) Hentry).
    + apply second_result.(footprinted_normalization_safe).
      rewrite (GenericRegions.Atomicity.analysis_certificate_preserves_in_atomic
        first_certificate). exact Hentry.
Defined.

Lemma footprinted_normalization_sequence_from_worker
    {Γ F Δ entry middle exit}
    {pre middle_prenex post : Resource.resource_prenex Γ F Δ}
    {first second normalized_first normalized_second normalized : stmt Γ}
    (first_derivation :
      RavenHoareRules.RavenHoareTriple pre first middle_prenex)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry first middle)
    (first_result : @footprinted_normalization_result Γ F Δ
      entry middle pre middle_prenex first first_derivation first_certificate)
    (Hfirst_result : normalized_statement
      first_result.(footprinted_normalization) = normalized_first)
    (second_derivation :
      RavenHoareRules.RavenHoareTriple middle_prenex second post)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      middle second exit)
    (second_result : @footprinted_normalization_result Γ F Δ
      middle exit middle_prenex post second second_derivation
      second_certificate)
    (Hsecond_result : normalized_statement
      second_result.(footprinted_normalization) = normalized_second)
    (view : RegionSyntax.view (TSeq first second) =
      AnalysisView.ViewSequence first second)
    (Hnot_unfold : match RegionSyntax.view first with
      | AnalysisView.ViewUnfold _ _ => False
      | _ => True
      end)
    fuel
    (Hfirst_worker : restricted_normalize_statement_fuel fuel first =
      Some normalized_first)
    (Hsecond_worker : restricted_normalize_statement_fuel fuel second =
      Some normalized_second)
    (Hworker : restricted_normalize_statement_fuel (S fuel)
      (TSeq first second) = Some normalized) :
  exists result : @footprinted_normalization_result Γ F Δ entry
      exit pre post (TSeq first second)
      (RavenHoareRules.RTSeq pre middle_prenex post first second
        first_derivation second_derivation)
      (GenericRegions.Atomicity.CertSequence Γ entry
        (TSeq first second) first middle second exit view
        first_certificate second_certificate),
    normalized_statement
      result.(footprinted_normalization) = normalized.
Proof.
  destruct first; cbn in Hnot_unfold, Hworker;
    try contradiction;
    rewrite Hfirst_worker, Hsecond_worker in Hworker;
    inversion Hworker; subst.
  all: exists (footprinted_normalization_sequence
    first_derivation first_certificate first_result second_derivation
    second_certificate second_result view);
    cbn; reflexivity.
Qed.

Definition footprinted_normalization_conditional
    {Γ F Δ entry then_exit else_exit}
    {store : symbolic_store Γ F Δ} {body : Resource.core_assertion F Δ}
    {post : Resource.resource_prenex Γ F Δ}
    {condition} {then_branch else_branch : stmt Γ}
    (then_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store
        (Resource.CAnd body (Resource.CExpr (IR.symbolize_expr store condition))))
      then_branch post)
    (then_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry then_branch then_exit)
    (then_result : @footprinted_normalization_result Γ F Δ entry
      then_exit _ post then_branch then_derivation then_certificate)
    (else_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (Core.EUnOp Core.UNot
            (IR.symbolize_expr store condition)))))
      else_branch post)
    (else_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry else_branch else_exit)
    (else_result : @footprinted_normalization_result Γ F Δ entry
      else_exit _ post else_branch else_derivation else_certificate)
    (records_equal : GenericRegions.Atomicity.analysis_records then_exit =
      GenericRegions.Atomicity.analysis_records else_exit)
    (atomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (view : RegionSyntax.view (TIf condition then_branch else_branch) =
      AnalysisView.ViewConditional then_branch else_branch) :
  let source := TIf condition then_branch else_branch in
  let joined := GenericRegions.Atomicity.AnalysisState
    (GenericRegions.Atomicity.entries_meet
      (GenericRegions.Atomicity.analysis_entries then_exit)
      (GenericRegions.Atomicity.analysis_entries else_exit))
    (GenericRegions.Atomicity.analysis_records then_exit)
    (GenericRegions.Atomicity.analysis_step_taken then_exit ||
      GenericRegions.Atomicity.analysis_step_taken else_exit)
    (GenericRegions.Atomicity.analysis_in_atomic then_exit) in
  let source_derivation := RavenHoareRules.RTIf store body condition
    then_branch else_branch post then_derivation else_derivation in
  let source_certificate := GenericRegions.Atomicity.CertConditional Γ
    entry source then_branch else_branch then_exit else_exit view
      then_certificate else_certificate records_equal atomic_equal in
  @footprinted_normalization_result Γ F Δ entry joined
    (Resource.RState store body) post source source_derivation
    source_certificate.
Proof.
  simpl.
  refine {| footprinted_normalization :=
    normalization_conditional then_derivation then_certificate
      then_result.(footprinted_normalization) else_derivation
      else_certificate else_result.(footprinted_normalization)
      records_equal atomic_equal view |}.
  - intros marker Hmember.
    simpl in Hmember |- *.
    repeat rewrite elem_of_union in Hmember |- *.
    pose proof (then_result.(footprinted_normalization_subset)
      marker) as Hthen.
    pose proof (else_result.(footprinted_normalization_subset)
      marker) as Helse.
    tauto.
  - intros Hentry. split.
    + exact (then_result.(footprinted_normalization_safe) Hentry).
    + exact (else_result.(footprinted_normalization_safe) Hentry).
Defined.


Lemma footprinted_normalization_conditional_from_worker
    {Γ F Δ entry then_exit else_exit}
    {store : symbolic_store Γ F Δ} {body : Resource.core_assertion F Δ}
    {post : Resource.resource_prenex Γ F Δ}
    {condition} {then_branch else_branch normalized_then normalized_else
      normalized : stmt Γ}
    (then_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store
        (Resource.CAnd body (Resource.CExpr (IR.symbolize_expr store condition))))
      then_branch post)
    (then_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry then_branch then_exit)
    (then_result : @footprinted_normalization_result Γ F Δ entry
      then_exit _ post then_branch then_derivation then_certificate)
    (Hthen_result : normalized_statement
      then_result.(footprinted_normalization) = normalized_then)
    (else_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (Core.EUnOp Core.UNot
            (IR.symbolize_expr store condition)))))
      else_branch post)
    (else_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry else_branch else_exit)
    (else_result : @footprinted_normalization_result Γ F Δ entry
      else_exit _ post else_branch else_derivation else_certificate)
    (Helse_result : normalized_statement
      else_result.(footprinted_normalization) = normalized_else)
    (records_equal : GenericRegions.Atomicity.analysis_records then_exit =
      GenericRegions.Atomicity.analysis_records else_exit)
    (atomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (view : RegionSyntax.view (TIf condition then_branch else_branch) =
      AnalysisView.ViewConditional then_branch else_branch)
    fuel
    (Hthen_worker : restricted_normalize_statement_fuel fuel then_branch =
      Some normalized_then)
    (Helse_worker : restricted_normalize_statement_fuel fuel else_branch =
      Some normalized_else)
    (Hworker : restricted_normalize_statement_fuel (S fuel)
      (TIf condition then_branch else_branch) = Some normalized) :
  exists result : @footprinted_normalization_result Γ F Δ entry
      _ _ post (TIf condition then_branch else_branch)
      (RavenHoareRules.RTIf store body condition then_branch else_branch
        post then_derivation else_derivation)
      (GenericRegions.Atomicity.CertConditional Γ entry
        (TIf condition then_branch else_branch) then_branch else_branch
        then_exit else_exit view then_certificate else_certificate
        records_equal atomic_equal),
    normalized_statement
      result.(footprinted_normalization) = normalized.
Proof.
  cbn [restricted_normalize_statement_fuel] in Hworker.
  rewrite Hthen_worker, Helse_worker in Hworker. inversion Hworker; subst.
  exists (footprinted_normalization_conditional
    then_derivation then_certificate then_result else_derivation
    else_certificate else_result records_equal atomic_equal view).
  reflexivity.
Qed.

Definition normalization_ghost_conditional
    {Γ F Δ entry then_exit else_exit}
    {store : symbolic_store Γ F Δ}
    {body : Resource.core_assertion F Δ}
    {condition then_branch else_branch}
    {post : Resource.resource_prenex Γ F Δ}
    (then_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (IR.symbolize_expr store condition))))
      then_branch post)
    (then_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry then_branch then_exit)
    (then_normalization : @normalization_result Γ F Δ entry
      then_exit _ post then_branch then_derivation then_certificate)
    (else_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (Core.EUnOp Core.UNot
            (IR.symbolize_expr store condition)))))
      else_branch post)
    (else_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry else_branch else_exit)
    (else_normalization : @normalization_result Γ F Δ entry
      else_exit _ post else_branch else_derivation else_certificate)
    (Hrecords_equal : GenericRegions.Atomicity.analysis_records then_exit =
      GenericRegions.Atomicity.analysis_records else_exit)
    (Hatomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (view : RegionSyntax.view (TGhostIf condition then_branch else_branch) =
      AnalysisView.ViewConditional then_branch else_branch)
    (then_proof_only : proof_onlyb then_branch = true)
    (else_proof_only : proof_onlyb else_branch = true)
    (normalized_then_proof_only :
      proof_onlyb then_normalization.(normalized_statement) = true)
    (normalized_else_proof_only :
      proof_onlyb else_normalization.(normalized_statement) = true) :
  let source := TGhostIf condition then_branch else_branch in
  let joined := GenericRegions.Atomicity.AnalysisState
    (GenericRegions.Atomicity.entries_meet
      (GenericRegions.Atomicity.analysis_entries then_exit)
      (GenericRegions.Atomicity.analysis_entries else_exit))
    (GenericRegions.Atomicity.analysis_records then_exit)
    (GenericRegions.Atomicity.analysis_step_taken then_exit ||
      GenericRegions.Atomicity.analysis_step_taken else_exit)
    (GenericRegions.Atomicity.analysis_in_atomic then_exit) in
  let source_derivation := RavenHoareRules.RTGhostIf store body condition
    then_branch else_branch post then_proof_only else_proof_only
    then_derivation else_derivation in
  let source_certificate := GenericRegions.Atomicity.CertConditional Γ
    entry source then_branch else_branch then_exit else_exit view
      then_certificate else_certificate Hrecords_equal Hatomic_equal in
  @normalization_result Γ F Δ entry joined
    (Resource.RState store body) post source
    source_derivation source_certificate.
Proof.
  simpl.
  refine {| normalized_statement := TGhostIf condition
      then_normalization.(normalized_statement)
      else_normalization.(normalized_statement);
    normalization_target_derivation :=
      RavenHoareRules.RTGhostIf store body condition _ _ post
        normalized_then_proof_only normalized_else_proof_only
        then_normalization.(normalization_target_derivation)
        else_normalization.(normalization_target_derivation);
    normalization_target_certificate :=
      StructuredGhostConditional Γ entry condition _ _ then_exit
        else_exit
        then_normalization.(normalization_target_certificate)
        else_normalization.(normalization_target_certificate)
        Hrecords_equal Hatomic_equal |}.
  intros names stack. reflexivity.
Defined.

Definition footprinted_normalization_ghost_conditional
    {Γ F Δ entry then_exit else_exit}
    {store : symbolic_store Γ F Δ} {body : Resource.core_assertion F Δ}
    {post : Resource.resource_prenex Γ F Δ}
    {condition} {then_branch else_branch : stmt Γ}
    (then_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store
        (Resource.CAnd body (Resource.CExpr (IR.symbolize_expr store condition))))
      then_branch post)
    (then_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry then_branch then_exit)
    (then_result : @footprinted_normalization_result Γ F Δ entry
      then_exit _ post then_branch then_derivation then_certificate)
    (else_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (Core.EUnOp Core.UNot
            (IR.symbolize_expr store condition)))))
      else_branch post)
    (else_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry else_branch else_exit)
    (else_result : @footprinted_normalization_result Γ F Δ entry
      else_exit _ post else_branch else_derivation else_certificate)
    (records_equal : GenericRegions.Atomicity.analysis_records then_exit =
      GenericRegions.Atomicity.analysis_records else_exit)
    (atomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (view : RegionSyntax.view (TGhostIf condition then_branch else_branch) =
      AnalysisView.ViewConditional then_branch else_branch)
    (then_proof_only : proof_onlyb then_branch = true)
    (else_proof_only : proof_onlyb else_branch = true)
    (normalized_then_proof_only : proof_onlyb
      then_result.(footprinted_normalization).(normalized_statement) = true)
    (normalized_else_proof_only : proof_onlyb
      else_result.(footprinted_normalization).(normalized_statement) = true) :
  let source := TGhostIf condition then_branch else_branch in
  let joined := GenericRegions.Atomicity.AnalysisState
    (GenericRegions.Atomicity.entries_meet
      (GenericRegions.Atomicity.analysis_entries then_exit)
      (GenericRegions.Atomicity.analysis_entries else_exit))
    (GenericRegions.Atomicity.analysis_records then_exit)
    (GenericRegions.Atomicity.analysis_step_taken then_exit ||
      GenericRegions.Atomicity.analysis_step_taken else_exit)
    (GenericRegions.Atomicity.analysis_in_atomic then_exit) in
  let source_derivation := RavenHoareRules.RTGhostIf store body condition
    then_branch else_branch post then_proof_only else_proof_only
    then_derivation else_derivation in
  let source_certificate := GenericRegions.Atomicity.CertConditional Γ
    entry source then_branch else_branch then_exit else_exit view
      then_certificate else_certificate records_equal atomic_equal in
  @footprinted_normalization_result Γ F Δ entry joined
    (Resource.RState store body) post source source_derivation
    source_certificate.
Proof.
  simpl.
  refine {| footprinted_normalization :=
    normalization_ghost_conditional then_derivation then_certificate
      then_result.(footprinted_normalization) else_derivation
      else_certificate else_result.(footprinted_normalization)
      records_equal atomic_equal view then_proof_only else_proof_only
      normalized_then_proof_only normalized_else_proof_only |}.
  - intros marker Hmember.
    simpl in Hmember |- *.
    repeat rewrite elem_of_union in Hmember |- *.
    pose proof (then_result.(footprinted_normalization_subset)
      marker) as Hthen.
    pose proof (else_result.(footprinted_normalization_subset)
      marker) as Helse.
    tauto.
  - intros Hentry. split.
    + exact (then_result.(footprinted_normalization_safe) Hentry).
    + exact (else_result.(footprinted_normalization_safe) Hentry).
Defined.

Lemma footprinted_normalization_ghost_conditional_from_worker
    {Γ F Δ entry then_exit else_exit}
    {store : symbolic_store Γ F Δ} {body : Resource.core_assertion F Δ}
    {post : Resource.resource_prenex Γ F Δ}
    {condition} {then_branch else_branch normalized_then normalized_else
      normalized : stmt Γ}
    (then_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store
        (Resource.CAnd body (Resource.CExpr (IR.symbolize_expr store condition))))
      then_branch post)
    (then_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry then_branch then_exit)
    (then_result : @footprinted_normalization_result Γ F Δ entry
      then_exit _ post then_branch then_derivation then_certificate)
    (Hthen_result : normalized_statement
      then_result.(footprinted_normalization) = normalized_then)
    (else_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState store
        (Resource.CAnd body
          (Resource.CExpr (Core.EUnOp Core.UNot
            (IR.symbolize_expr store condition)))))
      else_branch post)
    (else_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry else_branch else_exit)
    (else_result : @footprinted_normalization_result Γ F Δ entry
      else_exit _ post else_branch else_derivation else_certificate)
    (Helse_result : normalized_statement
      else_result.(footprinted_normalization) = normalized_else)
    (records_equal : GenericRegions.Atomicity.analysis_records then_exit =
      GenericRegions.Atomicity.analysis_records else_exit)
    (atomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (view : RegionSyntax.view (TGhostIf condition then_branch else_branch) =
      AnalysisView.ViewConditional then_branch else_branch)
    (then_proof_only : proof_onlyb then_branch = true)
    (else_proof_only : proof_onlyb else_branch = true)
    fuel
    (Hthen_worker : restricted_normalize_statement_fuel fuel then_branch =
      Some normalized_then)
    (Helse_worker : restricted_normalize_statement_fuel fuel else_branch =
      Some normalized_else)
    (Hworker : restricted_normalize_statement_fuel (S fuel)
      (TGhostIf condition then_branch else_branch) = Some normalized) :
  exists result : @footprinted_normalization_result Γ F Δ entry
      _ _ post (TGhostIf condition then_branch else_branch)
      (RavenHoareRules.RTGhostIf store body condition then_branch else_branch
        post then_proof_only else_proof_only then_derivation else_derivation)
      (GenericRegions.Atomicity.CertConditional Γ entry
        (TGhostIf condition then_branch else_branch) then_branch else_branch
        then_exit else_exit view then_certificate else_certificate
        records_equal atomic_equal),
    normalized_statement
      result.(footprinted_normalization) = normalized.
Proof.
  cbn [restricted_normalize_statement_fuel] in Hworker.
  rewrite Hthen_worker, Helse_worker in Hworker. inversion Hworker; subst.
  assert (Hthen_normalized : proof_onlyb
      then_result.(footprinted_normalization).(normalized_statement) = true).
  { rewrite (restricted_normalize_statement_proof_only _ _ _ Hthen_worker).
    exact then_proof_only. }
  assert (Helse_normalized : proof_onlyb
      else_result.(footprinted_normalization).(normalized_statement) = true).
  { rewrite (restricted_normalize_statement_proof_only _ _ _ Helse_worker).
    exact else_proof_only. }
  exists (footprinted_normalization_ghost_conditional
    then_derivation then_certificate then_result else_derivation
    else_certificate else_result records_equal atomic_equal view
    then_proof_only else_proof_only Hthen_normalized Helse_normalized).
  reflexivity.
Qed.

Definition footprinted_normalization_ghost_val
    {Γ F Δ entry exit}
    {store : symbolic_store Γ F Δ} {frame : Resource.core_assertion F Δ}
    {name t} {initializer : gexpr Γ t} {body : stmt (ghost_val t :: Γ)}
    {post : Resource.resource_prenex (ghost_val t :: Γ) F (t :: Δ)}
    (body_derivation : RavenHoareRules.RavenHoareTriple
      (Resource.RState (StoreCons (d := ghost_val t) (RefBound MHere)
          (Assertions.weaken_store store))
        (Resource.CAnd (Resource.weaken_core frame)
          (Resource.CExpr (EBinOp (BEq t) (ERef (RefBound MHere))
            (Assertions.weaken_expr (IR.symbolize_expr store initializer))))))
      body post)
    (body_certificate : GenericRegions.Atomicity.analysis_certificate
      (ghost_val t :: Γ) entry body exit)
    (body_result : @footprinted_normalization_result (ghost_val t :: Γ) F
      (t :: Δ) entry exit _ post body body_derivation body_certificate)
    (view : RegionSyntax.view (TGhostVal name t initializer body) =
      AnalysisView.ViewScope (ghost_val t) body)
    (admissible : GenericRegions.Atomicity.leave_scope_admissible
      (length Γ) exit = true) :
  @footprinted_normalization_result Γ F Δ entry
    (GenericRegions.Atomicity.leave_scope (length Γ) entry exit)
    (Resource.RState store frame)
    (Resource.ResourceExists t (Resource.drop_head_prenex post))
    (TGhostVal name t initializer body)
    (RavenHoareRules.RTGhostVal name t initializer body store frame post
      body_derivation)
    (GenericRegions.Atomicity.CertScope Γ entry
      (TGhostVal name t initializer body) (ghost_val t) body exit view
      body_certificate admissible).
Proof.
  refine {| footprinted_normalization :=
    normalization_ghost_val body_derivation body_certificate
      body_result.(footprinted_normalization) view admissible |}.
  - intros marker Hmember.
    simpl in Hmember |- *.
    repeat rewrite elem_of_union in Hmember |- *.
    pose proof (body_result.(footprinted_normalization_subset) marker)
      as Hbody.
    tauto.
  - exact body_result.(footprinted_normalization_safe).
Defined.

(** Inversion facts for the executable worker used by the completeness
    induction below.  These expose the recursive fuel and normalized shape
    without adding any proof-side structure to the worker. *)
Lemma restricted_normalize_access_neutral_sequence_inv {Γ} (fuel : nat)
    (first second normalized : stmt Γ) :
  access_neutral first ->
  restricted_normalize_statement_fuel (S fuel) (TSeq first second) =
    Some normalized ->
  exists normalized_second,
    restricted_normalize_statement_fuel fuel first = Some first /\
    restricted_normalize_statement_fuel fuel second = Some normalized_second /\
    normalized = TSeq first normalized_second.
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

Lemma baseline_normalizable_unfold_absurd {Γ} nested invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant)) :
  baseline_normalizable nested (TUnfold invariant arguments) -> False.
Proof.
  intro H. inversion H; subst; cbn in *; try contradiction.
  destruct nested; contradiction.
Qed.

Lemma restricted_normalize_baseline_sequence_inv {Γ} nested fuel
    (first second normalized : stmt Γ) :
  baseline_normalizable nested first ->
  restricted_normalize_statement_fuel (S fuel) (TSeq first second) =
    Some normalized ->
  exists normalized_first normalized_second,
    restricted_normalize_statement_fuel fuel first = Some normalized_first /\
    restricted_normalize_statement_fuel fuel second = Some normalized_second /\
    normalized = TSeq normalized_first normalized_second.
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

Lemma restricted_normalize_terminal_access_inv {Γ} fuel
    invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (body normalized : stmt Γ) :
  restricted_normalize_statement_fuel fuel
    (TSeq (TUnfold invariant arguments)
      (TSeq body (TFold invariant arguments))) =
    Some normalized ->
  exists remaining normalized_body,
    fuel = S remaining /\
    restricted_access_boundary_check arguments arguments body = true /\
    restricted_normalize_statement_fuel remaining body = Some normalized_body /\
    normalized = TInvAccess invariant arguments normalized_body.
Proof.
  destruct fuel as [|remaining]; cbn [restricted_normalize_statement_fuel];
    try discriminate.
  destruct (decide (invariant = invariant)) as [Heq|Hneq];
    [|contradiction].
  replace Heq with (@eq_refl inv_id invariant) by apply ProofIrrelevance.proof_irrelevance.
  cbn.
  destruct (restricted_access_boundary_check arguments arguments body)
    eqn:Hboundary; try discriminate.
  destruct (restricted_normalize_statement_fuel remaining body)
    as [normalized_body|] eqn:Hbody; try discriminate.
  intro Hworker. inversion Hworker; subst.
  exists remaining, normalized_body. repeat split; auto.
Qed.

Lemma restricted_normalize_continued_access_inv {Γ} fuel
    invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (body work normalized : stmt Γ) :
  restricted_normalize_statement_fuel fuel
    (TSeq (TUnfold invariant arguments)
      (TSeq body
        (TSeq (TFold invariant arguments) work))) =
    Some normalized ->
  exists remaining normalized_body normalized_work,
    fuel = S remaining /\
    restricted_access_boundary_check arguments arguments body = true /\
    restricted_normalize_statement_fuel remaining body = Some normalized_body /\
    restricted_normalize_statement_fuel remaining work = Some normalized_work /\
    normalized = TSeq (TInvAccess invariant arguments normalized_body)
      normalized_work.
Proof.
  destruct fuel as [|remaining]; cbn [restricted_normalize_statement_fuel];
    try discriminate.
  destruct (decide (invariant = invariant)) as [Heq|Hneq];
    [|contradiction].
  replace Heq with (@eq_refl inv_id invariant) by apply ProofIrrelevance.proof_irrelevance.
  cbn.
  destruct (restricted_access_boundary_check arguments arguments body)
    eqn:Hboundary; try discriminate.
  destruct (restricted_normalize_statement_fuel remaining body)
    as [normalized_body|] eqn:Hbody; try discriminate.
  destruct (restricted_normalize_statement_fuel remaining work)
    as [normalized_work|] eqn:Hwork; try discriminate.
  intro Hworker. inversion Hworker; subst.
  exists remaining, normalized_body, normalized_work. repeat split; auto.
Qed.

Lemma conditional_normalization_complete_from_worker
    {Γ F Δ entry exit condition then_branch else_branch}
    {pre post : Resource.resource_prenex Γ F Δ}
    (derivation : RavenHoareRules.RavenHoareTriple pre
      (TIf condition then_branch else_branch) post)
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ entry
      (TIf condition then_branch else_branch) exit)
    (Hthen : forall F0 Δ0 then_exit
      (then_pre then_post : Resource.resource_prenex Γ F0 Δ0)
      (then_derivation : RavenHoareRules.RavenHoareTriple then_pre
        then_branch then_post)
      (then_certificate : GenericRegions.Atomicity.analysis_certificate Γ
        entry then_branch then_exit),
      GenericRegions.Atomicity.analysis_records then_exit =
        GenericRegions.Atomicity.analysis_records entry ->
      forall fuel normalized,
      restricted_normalize_statement_fuel fuel then_branch = Some normalized ->
      exists result : @footprinted_normalization_result Γ F0 Δ0
          entry then_exit then_pre then_post then_branch then_derivation
          then_certificate,
        normalized_statement
          result.(footprinted_normalization) = normalized)
    (Helse : forall F0 Δ0 else_exit
      (else_pre else_post : Resource.resource_prenex Γ F0 Δ0)
      (else_derivation : RavenHoareRules.RavenHoareTriple else_pre
        else_branch else_post)
      (else_certificate : GenericRegions.Atomicity.analysis_certificate Γ
        entry else_branch else_exit),
      GenericRegions.Atomicity.analysis_records else_exit =
        GenericRegions.Atomicity.analysis_records entry ->
      forall fuel normalized,
      restricted_normalize_statement_fuel fuel else_branch = Some normalized ->
      exists result : @footprinted_normalization_result Γ F0 Δ0
          entry else_exit else_pre else_post else_branch else_derivation
          else_certificate,
        normalized_statement
          result.(footprinted_normalization) = normalized) :
  GenericRegions.Atomicity.analysis_records exit =
    GenericRegions.Atomicity.analysis_records entry ->
  forall fuel normalized,
  restricted_normalize_statement_fuel fuel
    (TIf condition then_branch else_branch) = Some normalized ->
  exists result : @footprinted_normalization_result Γ F Δ
      entry exit pre post (TIf condition then_branch else_branch)
      derivation certificate,
    normalized_statement
      result.(footprinted_normalization) = normalized.
Proof.
  destruct (certificate_aligned_complete_exists Δ pre post
    (TIf condition then_branch else_branch) derivation entry exit
    certificate) as (aligned & _).
  dependent induction aligned generalizing condition then_branch else_branch
    derivation certificate Hthen Helse; try discriminate.
  all: intros Hbalanced fuel normalized Hworker.
  - cbn [GenericRegions.Atomicity.analysis_records] in Hbalanced.
    pose proof Hbalanced as Hthen_balanced.
    pose proof (eq_trans (eq_sym records_equal) Hbalanced) as Helse_balanced.
    destruct fuel as [|fuel]; cbn [restricted_normalize_statement_fuel]
      in Hworker; try discriminate.
    remember (restricted_normalize_statement_fuel fuel then_branch)
      as then_result eqn:Hthen_worker.
    remember (restricted_normalize_statement_fuel fuel else_branch)
      as else_result eqn:Helse_worker.
    destruct then_result as [normalized_then|]; try discriminate.
    destruct else_result as [normalized_else|]; try discriminate.
    destruct (Hthen F Δ then_exit _ post then_derivation then_certificate
      Hthen_balanced fuel normalized_then (eq_sym Hthen_worker))
      as (then_result & Hthen_result).
    destruct (Helse F Δ else_exit _ post else_derivation else_certificate
      Helse_balanced fuel normalized_else (eq_sym Helse_worker))
      as (else_result & Helse_result).
    eapply footprinted_normalization_conditional_from_worker
      with (then_result := then_result) (else_result := else_result)
      (fuel := fuel); try eassumption.
    + symmetry. exact Hthen_worker.
    + symmetry. exact Helse_worker.
    + cbn [restricted_normalize_statement_fuel].
      rewrite <- Hthen_worker, <- Helse_worker. exact Hworker.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_frame frame derivation0
      certificate result). exact Hresult.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_prenex_elim derivation0
      certificate result). exact Hresult.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_prenex_preserve derivation0
      certificate result). exact Hresult.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_prenex_consequence derivation0
      certificate result pre_entails post_entails). exact Hresult.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_consequence derivation0
      certificate result pre_entails post_entails). exact Hresult.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_stack_rewrite derivation0
      certificate result store_equal). exact Hresult.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_bound_weaken derivation0
      certificate result). exact Hresult.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    assert (Htarget : RavenHoareRules.pexpr_dependencies expression ##
      RavenHoareRules.statement_writes
        result.(footprinted_normalization).(normalized_statement)).
    { rewrite Hresult, (restricted_normalize_statement_writes _ _ _ Hworker).
      exact stable. }
    exists (footprinted_normalization_track _ expression value stable
      derivation0 certificate result Htarget). exact Hresult.
Qed.

Lemma ghost_conditional_normalization_complete_from_worker
    {Γ F Δ entry exit condition then_branch else_branch}
    {pre post : Resource.resource_prenex Γ F Δ}
    (derivation : RavenHoareRules.RavenHoareTriple pre
      (TGhostIf condition then_branch else_branch) post)
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ entry
      (TGhostIf condition then_branch else_branch) exit)
    (Hthen : forall F0 Δ0 then_exit
      (then_pre then_post : Resource.resource_prenex Γ F0 Δ0)
      (then_derivation : RavenHoareRules.RavenHoareTriple then_pre
        then_branch then_post)
      (then_certificate : GenericRegions.Atomicity.analysis_certificate Γ
        entry then_branch then_exit),
      GenericRegions.Atomicity.analysis_records then_exit =
        GenericRegions.Atomicity.analysis_records entry ->
      forall fuel normalized,
      restricted_normalize_statement_fuel fuel then_branch = Some normalized ->
      exists result : @footprinted_normalization_result Γ F0 Δ0
          entry then_exit then_pre then_post then_branch then_derivation
          then_certificate,
        normalized_statement
          result.(footprinted_normalization) = normalized)
    (Helse : forall F0 Δ0 else_exit
      (else_pre else_post : Resource.resource_prenex Γ F0 Δ0)
      (else_derivation : RavenHoareRules.RavenHoareTriple else_pre
        else_branch else_post)
      (else_certificate : GenericRegions.Atomicity.analysis_certificate Γ
        entry else_branch else_exit),
      GenericRegions.Atomicity.analysis_records else_exit =
        GenericRegions.Atomicity.analysis_records entry ->
      forall fuel normalized,
      restricted_normalize_statement_fuel fuel else_branch = Some normalized ->
      exists result : @footprinted_normalization_result Γ F0 Δ0
          entry else_exit else_pre else_post else_branch else_derivation
          else_certificate,
        normalized_statement
          result.(footprinted_normalization) = normalized) :
  GenericRegions.Atomicity.analysis_records exit =
    GenericRegions.Atomicity.analysis_records entry ->
  forall fuel normalized,
  restricted_normalize_statement_fuel fuel
    (TGhostIf condition then_branch else_branch) = Some normalized ->
  exists result : @footprinted_normalization_result Γ F Δ
      entry exit pre post (TGhostIf condition then_branch else_branch)
      derivation certificate,
    normalized_statement
      result.(footprinted_normalization) = normalized.
Proof.
  destruct (certificate_aligned_complete_exists Δ pre post
    (TGhostIf condition then_branch else_branch) derivation entry exit
    certificate) as (aligned & _).
  dependent induction aligned generalizing condition then_branch else_branch
    derivation certificate Hthen Helse; try discriminate.
  all: intros Hbalanced fuel normalized Hworker.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_frame frame derivation0
      certificate result). exact Hresult.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_prenex_elim derivation0
      certificate result). exact Hresult.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_prenex_preserve derivation0
      certificate result). exact Hresult.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_prenex_consequence derivation0
      certificate result pre_entails post_entails). exact Hresult.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_consequence derivation0
      certificate result pre_entails post_entails). exact Hresult.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_stack_rewrite derivation0
      certificate result store_equal). exact Hresult.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_bound_weaken derivation0
      certificate result). exact Hresult.
  - cbn [GenericRegions.Atomicity.analysis_records] in Hbalanced.
    pose proof Hbalanced as Hthen_balanced.
    pose proof (eq_trans (eq_sym records_equal) Hbalanced) as Helse_balanced.
    destruct fuel as [|fuel]; cbn [restricted_normalize_statement_fuel]
      in Hworker; try discriminate.
    remember (restricted_normalize_statement_fuel fuel then_branch)
      as then_result eqn:Hthen_worker.
    remember (restricted_normalize_statement_fuel fuel else_branch)
      as else_result eqn:Helse_worker.
    destruct then_result as [normalized_then|]; try discriminate.
    destruct else_result as [normalized_else|]; try discriminate.
    destruct (Hthen F Δ then_exit _ post then_derivation then_certificate
      Hthen_balanced fuel normalized_then (eq_sym Hthen_worker))
      as (then_result & Hthen_result).
    destruct (Helse F Δ else_exit _ post else_derivation else_certificate
      Helse_balanced fuel normalized_else (eq_sym Helse_worker))
      as (else_result & Helse_result).
    eapply footprinted_normalization_ghost_conditional_from_worker
      with (then_result := then_result) (else_result := else_result)
      (fuel := fuel); try eassumption.
    + symmetry. exact Hthen_worker.
    + symmetry. exact Helse_worker.
    + cbn [restricted_normalize_statement_fuel].
      rewrite <- Hthen_worker, <- Helse_worker. exact Hworker.
  - destruct (IHaligned condition then_branch else_branch derivation0
      certificate Hthen Helse eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    assert (Htarget : RavenHoareRules.pexpr_dependencies expression ##
      RavenHoareRules.statement_writes
        result.(footprinted_normalization).(normalized_statement)).
    { rewrite Hresult, (restricted_normalize_statement_writes _ _ _ Hworker).
      exact stable. }
    exists (footprinted_normalization_track _ expression value stable
      derivation0 certificate result Htarget). exact Hresult.
Qed.

(** Completeness for a ghost value binder, given completeness for its body.
    Proof wrappers around the binder rule are transported unchanged. *)
Lemma ghost_val_normalization_complete_from_worker
    {Γ F Δ entry exit name t initializer body}
    {pre post : Resource.resource_prenex Γ F Δ}
    (derivation : RavenHoareRules.RavenHoareTriple pre
      (TGhostVal name t initializer body) post)
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ entry
      (TGhostVal name t initializer body) exit)
    (Hbody : forall F0 Δ0 body_exit
      (body_pre body_post : Resource.resource_prenex (ghost_val t :: Γ) F0 Δ0)
      (body_derivation : RavenHoareRules.RavenHoareTriple body_pre
        body body_post)
      (body_certificate : GenericRegions.Atomicity.analysis_certificate
        (ghost_val t :: Γ) entry body body_exit),
      GenericRegions.Atomicity.analysis_records body_exit =
        GenericRegions.Atomicity.analysis_records entry ->
      forall fuel normalized,
      restricted_normalize_statement_fuel fuel body = Some normalized ->
      exists result : @footprinted_normalization_result (ghost_val t :: Γ)
          F0 Δ0 entry body_exit body_pre body_post body body_derivation
          body_certificate,
        normalized_statement
          result.(footprinted_normalization) = normalized) :
  GenericRegions.Atomicity.analysis_records exit =
    GenericRegions.Atomicity.analysis_records entry ->
  forall fuel normalized,
  restricted_normalize_statement_fuel fuel
    (TGhostVal name t initializer body) = Some normalized ->
  exists result : @footprinted_normalization_result Γ F Δ
      entry exit pre post (TGhostVal name t initializer body)
      derivation certificate,
    normalized_statement
      result.(footprinted_normalization) = normalized.
Proof.
  destruct (certificate_aligned_complete_exists Δ pre post
    (TGhostVal name t initializer body) derivation entry exit
    certificate) as (aligned & _).
  dependent induction aligned generalizing name t initializer body
    derivation certificate Hbody; try discriminate.
  all: intros Hbalanced fuel normalized Hworker.
  - destruct fuel as [|fuel]; cbn [restricted_normalize_statement_fuel]
      in Hworker; try discriminate.
    remember (restricted_normalize_statement_fuel fuel body)
      as body_worker eqn:Hbody_worker.
    destruct body_worker as [normalized_body|]; try discriminate.
    injection Hworker as <-.
    destruct (Hbody F (t :: Δ) exit _ post body_derivation body_certificate
      Hbalanced fuel normalized_body (eq_sym Hbody_worker))
      as (body_result & Hbody_result).
    exists (footprinted_normalization_ghost_val body_derivation
      body_certificate body_result view admissible).
    change (TGhostVal name t initializer
      (normalized_statement (footprinted_normalization body_result)) =
      TGhostVal name t initializer normalized_body).
    rewrite Hbody_result. reflexivity.
  - destruct (IHaligned name t initializer body derivation0
      certificate Hbody eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_frame frame derivation0
      certificate result). exact Hresult.
  - destruct (IHaligned name t initializer body derivation0
      certificate Hbody eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_prenex_elim derivation0
      certificate result). exact Hresult.
  - destruct (IHaligned name t initializer body derivation0
      certificate Hbody eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_prenex_preserve derivation0
      certificate result). exact Hresult.
  - destruct (IHaligned name t initializer body derivation0
      certificate Hbody eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_prenex_consequence derivation0
      certificate result pre_entails post_entails). exact Hresult.
  - destruct (IHaligned name t initializer body derivation0
      certificate Hbody eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_consequence derivation0
      certificate result pre_entails post_entails). exact Hresult.
  - destruct (IHaligned name t initializer body derivation0
      certificate Hbody eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_stack_rewrite derivation0
      certificate result store_equal). exact Hresult.
  - destruct (IHaligned name t initializer body derivation0
      certificate Hbody eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    exists (footprinted_normalization_bound_weaken derivation0
      certificate result). exact Hresult.
  - destruct (IHaligned name t initializer body derivation0
      certificate Hbody eq_refl (JMeq_refl _) (JMeq_refl _) Hbalanced
      fuel normalized Hworker) as (result & Hresult).
    assert (Htarget : RavenHoareRules.pexpr_dependencies expression ##
      RavenHoareRules.statement_writes
        result.(footprinted_normalization).(normalized_statement)).
    { rewrite Hresult, (restricted_normalize_statement_writes _ _ _ Hworker).
      exact stable. }
    exists (footprinted_normalization_track _ expression value stable
      derivation0 certificate result Htarget). exact Hresult.
Qed.

(** Worker-indexed completeness.  The syntax witness supplies the induction
    principle; the Hoare derivation is decomposed extensionally, so its proof
    wrappers do not become a second executable normalizer. *)
(** ** Conditional accesses *)

(** [X ⊆ U] for a union [U] containing [X], or a superset of [X] recorded in
    a hypothesis. *)
Ltac subset_of_union :=
  match goal with
  | |- ∅ ⊆ _ => apply empty_subseteq
  | |- ?X ⊆ ?X => reflexivity
  | |- _ ∩ _ ⊆ _ =>
      etransitivity; [apply intersection_subseteq_l|]; subset_of_union
  | |- _ ⊆ _ ∪ _ =>
      first [apply union_subseteq_l'; subset_of_union
            | apply union_subseteq_r'; subset_of_union]
  | H : ?X ⊆ _ |- ?X ⊆ _ => etransitivity; [exact H|]; subset_of_union
  end.

Ltac view_inversion :=
  match goal with
  | Hview : @AnalysisView.syntax_view _ _ _ = _ |- _ =>
      cbn in Hview; inversion Hview; subst; try clear Hview
  end.

Ltac footprint_subset :=
  repeat apply union_least; subset_of_union.


Definition structured_guard_if {Γ entry} (guard : access_guard Γ)
    {then_branch else_branch : stmt Γ} {then_exit else_exit}
    (then_certificate : structured_certificate Γ entry then_branch then_exit)
    (else_certificate : structured_certificate Γ entry else_branch else_exit)
    (Hopen : Atom.analysis_records then_exit = Atom.analysis_records else_exit)
    (Hatomic : Atom.analysis_in_atomic then_exit =
      Atom.analysis_in_atomic else_exit) :
    structured_certificate Γ entry (guard_if guard then_branch else_branch)
      (Atom.AnalysisState
        (Atom.entries_meet (Atom.analysis_entries then_exit)
          (Atom.analysis_entries else_exit))
        (Atom.analysis_records then_exit)
        (Atom.analysis_step_taken then_exit || Atom.analysis_step_taken else_exit)
        (Atom.analysis_in_atomic then_exit)) :=
  match guard as guard0 return structured_certificate Γ entry
    (guard_if guard0 then_branch else_branch) _ with
  | GuardRuntime condition =>
      StructuredConditional Γ entry condition then_branch else_branch
        then_exit else_exit then_certificate else_certificate Hopen Hatomic
  | GuardGhost condition =>
      StructuredGhostConditional Γ entry condition then_branch else_branch
        then_exit else_exit then_certificate else_certificate Hopen Hatomic
  end.

Lemma structured_guard_if_footprint {Γ entry} (guard : access_guard Γ)
    {then_branch else_branch : stmt Γ} {then_exit else_exit}
    (then_certificate : structured_certificate Γ entry then_branch then_exit)
    (else_certificate : structured_certificate Γ entry else_branch else_exit)
    Hopen Hatomic :
  structured_certificate_footprint
    (structured_guard_if guard then_certificate else_certificate Hopen Hatomic) =
  Atom.analysis_mask entry ∪ Atom.analysis_open entry ∪
    Atom.analysis_mask (Atom.AnalysisState
      (Atom.entries_meet (Atom.analysis_entries then_exit)
        (Atom.analysis_entries else_exit))
      (Atom.analysis_records then_exit)
      (Atom.analysis_step_taken then_exit || Atom.analysis_step_taken else_exit)
      (Atom.analysis_in_atomic then_exit)) ∪
    Atom.analysis_open then_exit ∪
    (structured_certificate_footprint then_certificate ∪
      structured_certificate_footprint else_certificate).
Proof. destruct guard; reflexivity. Qed.

Lemma structured_guard_if_safe {Γ entry} (guard : access_guard Γ)
    {then_branch else_branch : stmt Γ} {then_exit else_exit}
    (then_certificate : structured_certificate Γ entry then_branch then_exit)
    (else_certificate : structured_certificate Γ entry else_branch else_exit)
    Hopen Hatomic :
  structured_accesses_outside_atomic then_certificate ->
  structured_accesses_outside_atomic else_certificate ->
  structured_accesses_outside_atomic
    (structured_guard_if guard then_certificate else_certificate Hopen Hatomic).
Proof. destruct guard; cbn; tauto. Qed.

Definition structured_cast {Γ entry statement exit exit'} (Hexit : exit = exit')
    (certificate : structured_certificate Γ entry statement exit) :
    structured_certificate Γ entry statement exit' :=
  eq_rect exit (structured_certificate Γ entry statement) certificate exit' Hexit.

Lemma structured_cast_footprint {Γ entry statement exit exit'}
    (Hexit : exit = exit')
    (certificate : structured_certificate Γ entry statement exit) :
  structured_certificate_footprint (structured_cast Hexit certificate) =
    structured_certificate_footprint certificate.
Proof. destruct Hexit. reflexivity. Qed.

Lemma structured_cast_safe {Γ entry statement exit exit'} (Hexit : exit = exit')
    (certificate : structured_certificate Γ entry statement exit) :
  structured_accesses_outside_atomic certificate ->
  structured_accesses_outside_atomic (structured_cast Hexit certificate).
Proof. destruct Hexit. auto. Qed.

Lemma entries_meet_self (entries : gset Atom.mask_entry) :
  Atom.entries_meet entries entries = entries.
Proof.
  unfold Atom.entries_meet, Atom.entry_covered. apply set_eq. intros entry.
  rewrite elem_of_filter, elem_of_union. tauto.
Qed.

Lemma analysis_state_join_self (state : Atom.analysis_state) :
  Atom.AnalysisState
    (Atom.entries_meet (Atom.analysis_entries state)
      (Atom.analysis_entries state))
    (Atom.analysis_records state)
    (Atom.analysis_step_taken state || Atom.analysis_step_taken state)
    (Atom.analysis_in_atomic state) = state.
Proof.
  destruct state as [entries records step atomic]. cbn.
  rewrite Bool.orb_diag, entries_meet_self. reflexivity.
Qed.

Lemma fold_invariant_in_atomic invariant key state :
  Atom.analysis_in_atomic (Atom.fold_invariant invariant key state) =
    Atom.analysis_in_atomic state.
Proof. apply Atom.fold_invariant_preserves_in_atomic. Qed.

(** Proof-only code leaves the analysis state unchanged. *)
Lemma proof_only_neutral_state {Γ entry statement exit}
    (certificate : Atom.analysis_certificate Γ entry statement exit) :
  proof_onlyb statement = true -> access_neutral statement -> exit = entry.
Proof.
  induction certificate; intros Hproof Hneutral.
  - rewrite (Certified.proof_only_leaf_cost Γ statement Hproof) in e0.
    unfold Atom.take_step, Atom.take_plain_step in e0.
    destruct (_ || _); injection e0 as <-; reflexivity.
  - reflexivity.
  - destruct statement; cbn in e; try discriminate. contradiction.
  - destruct statement; cbn in e; try discriminate. contradiction.
  - destruct statement; cbn in e; try discriminate. inversion e; subst.
    apply andb_prop in Hproof as [Hfirst Hsecond].
    destruct Hneutral as [Hfirst_neutral Hsecond_neutral].
    rewrite IHcertificate2, IHcertificate1; auto.
  - destruct statement; cbn in e; try discriminate; inversion e; subst;
      apply andb_prop in Hproof as [Hthen Helse];
      destruct Hneutral as [Hthen_neutral Helse_neutral];
      rewrite IHcertificate1, IHcertificate2 by assumption;
      apply analysis_state_join_self.
  - destruct statement; cbn in e; try discriminate.
  - destruct statement; cbn in e; try discriminate.
    injection e as Hd Hbody. subst.
    apply Eqdep.EqdepTheory.inj_pair2 in Hbody. subst.
    rewrite (IHcertificate Hproof Hneutral).
    destruct state as [entries records step atomic].
    unfold Atom.leave_scope. cbn. f_equal.
    apply set_eq. intros entry. rewrite elem_of_filter. tauto.
Qed.

(** Completeness of the worker for [statement], in any state that a
    statement of the given nesting may run in and that it keeps the open
    records of. *)
Definition normalization_complete {Γ} (nested : bool) (statement : stmt Γ) :
    Prop :=
  forall F Δ entry exit (pre post : Resource.resource_prenex Γ F Δ)
    (derivation : RavenHoareRules.RavenHoareTriple pre statement post)
    (certificate : Atom.analysis_certificate Γ entry statement exit),
  (if nested then True else Atom.analysis_records entry = []) ->
  Atom.analysis_records exit = Atom.analysis_records entry ->
  forall fuel normalized,
  restricted_normalize_statement_fuel fuel statement = Some normalized ->
  exists result : @footprinted_normalization_result Γ F Δ entry exit pre post
      statement derivation certificate,
    normalized_statement result.(footprinted_normalization) = normalized.

Lemma unfold_free_normalization_complete {Γ} nested (statement : stmt Γ) :
  unfold_free statement -> normalization_complete nested statement.
Proof.
  intros u F Δ entry exit pre post derivation certificate _ Hbalanced fuel
    normalized Hworker.
  pose (balanced := unfold_free_balanced_structured_result certificate
    u Hbalanced).
  pose (normalization := normalization_identity derivation
    certificate balanced.(balanced_structured_certificate)).
  exists {| footprinted_normalization := normalization;
    footprinted_normalization_subset :=
      balanced.(balanced_structured_footprint);
    footprinted_normalization_safe :=
      fun _ => balanced.(balanced_structured_safe) |}.
  pose proof (unfold_free_normalize_statement_identity statement fuel normalized
    u Hworker) as Heq.
  cbn. symmetry. exact Heq.
Qed.

(** What a normalized piece of a larger statement provides. *)
Lemma piece_normalization_facts {Γ} nested (statement normalized : stmt Γ)
    {entry exit} (certificate : Atom.analysis_certificate Γ entry statement exit)
    fuel F Δ (pre post : Resource.resource_prenex Γ F Δ) :
  normalization_complete nested statement ->
  RavenHoareRules.RavenHoareTriple pre statement post ->
  (if nested then True else Atom.analysis_records entry = []) ->
  Atom.analysis_records exit = Atom.analysis_records entry ->
  restricted_normalize_statement_fuel fuel statement = Some normalized ->
  exists target : structured_certificate Γ entry normalized exit,
    structured_certificate_footprint target ⊆
      Atom.certificate_footprint certificate /\
    (Atom.analysis_in_atomic entry = false ->
      structured_accesses_outside_atomic target) /\
    (forall names stack,
      Erasure.runtime_stmt names stack normalized =
        Erasure.runtime_stmt names stack statement) /\
    simulates statement normalized /\
    statement_writes normalized = statement_writes statement /\
    proof_onlyb normalized = proof_onlyb statement.
Proof.
  intros IH derivation Hclosed Hbalanced Hworker.
  destruct (IH F Δ _ _ pre post derivation certificate Hclosed Hbalanced fuel
    normalized Hworker) as (result & Hresult).
  pose proof (restricted_normalize_statement_writes _ _ _ Hworker).
  pose proof (restricted_normalize_statement_proof_only _ _ _ Hworker).
  subst normalized.
  exists (normalization_target_certificate (footprinted_normalization result)).
  repeat split; try assumption.
  - apply footprinted_normalization_subset.
  - apply footprinted_normalization_safe.
  - intros names stack'. symmetry. apply normalization_runtime_erasure.
  - intros F' Δ' P Q D.
    destruct (IH F' Δ' _ _ P Q D certificate Hclosed Hbalanced fuel _ Hworker)
      as (result' & Hresult').
    rewrite <- Hresult'.
    exact (normalization_target_derivation (footprinted_normalization result')).
Qed.

(** A linear access: its body is normalized with the access's record
    open. *)
Lemma terminal_access_normalization_complete_from_worker {Γ} nested invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (body : stmt Γ) :
  baseline_normalizable true body ->
  pexpr_list_dependencies arguments ## statement_writes body ->
  normalization_complete true body ->
  normalization_complete nested
    (TSeq (TUnfold invariant arguments)
      (TSeq body (TFold invariant arguments))).
Proof.
  intros Hbody_baseline Hstable IHbody F Δ entry exit pre post derivation
    certificate _ Hbalanced fuel normalized Hworker.
  destruct (restricted_normalize_terminal_access_inv _ _ _ _ _ Hworker)
    as (remaining & body' & -> & _ & Hbody_worker & ->).
  destruct (RavenHoareRules.RavenHoareTriple_sequence_decompose _ _ derivation)
    as (opened_pre & Hunfold & Htail).
  destruct (RavenHoareRules.RavenHoareTriple_sequence_decompose _ _ Htail)
    as (body_post & Hbody & Hfold).
  dependent destruction certificate; try discriminate. try view_inversion.
  dependent destruction certificate1; try discriminate. try view_inversion.
  dependent destruction certificate2; try discriminate. try view_inversion.
  dependent destruction certificate2_2; try discriminate. try view_inversion.
  rename e0 into Hopen, certificate2_1 into body_certificate.
  pose proof (baseline_nested_balanced _ _ Hbody_baseline eq_refl _ _
    body_certificate) as Hbody_open.
  destruct (IHbody F Δ _ _ _ _ Hbody body_certificate
    I Hbody_open remaining body'
    Hbody_worker) as (body_result & Hbody_result).
  subst body'.
  pose proof (restricted_normalize_statement_writes _ _ _ Hbody_worker)
    as Hbody_writes.
  pose proof (footprinted_normalization_subset body_result) as Hbody_subset.
  pose proof (footprinted_normalization_safe body_result) as Hbody_safe.
  set (body_normalization := footprinted_normalization body_result) in *.
  set (body' := normalized_statement body_normalization) in *.
  assert (Hderivation : RavenHoareRules.RavenHoareTriple pre
    (TInvAccess invariant arguments body') post).
  { apply RavenHoareTriple_access_of_raw; [rewrite Hbody_writes; exact Hstable|].
    eapply RavenHoareRules.RTSeq; [exact Hunfold|].
    eapply RavenHoareRules.RTSeq; [|exact Hfold].
    exact (normalization_target_derivation body_normalization). }
  pose (target := StructuredInvAccess Γ state invariant arguments body' state0
    state1 Hopen (normalization_target_certificate body_normalization)
    Hbody_open).
  unshelve eexists {| footprinted_normalization :=
    {| normalized_statement := TInvAccess invariant arguments body';
       normalization_target_derivation := Hderivation;
       normalization_target_certificate := target |} |}.
  - intros names stack'. rewrite runtime_stmt_linear_access. cbn.
    apply normalization_runtime_erasure.
  - cbn [target structured_certificate_footprint Atom.certificate_footprint].
    footprint_subset.
  - intros Hentry. cbn [target structured_accesses_outside_atomic].
    split; [exact Hentry|]. apply Hbody_safe.
    rewrite (Atom.open_invariant_preserves_in_atomic _ _ _ _ Hopen). exact Hentry.
  - reflexivity.
Qed.

Lemma continued_access_normalization_complete_from_worker {Γ} nested invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (body work : stmt Γ) :
  baseline_normalizable true body ->
  pexpr_list_dependencies arguments ## statement_writes body ->
  normalization_complete true body ->
  normalization_complete nested work ->
  normalization_complete nested
    (TSeq (TUnfold invariant arguments)
      (TSeq body (TSeq (TFold invariant arguments) work))).
Proof.
  intros Hbody_baseline Hstable IHbody IHwork F Δ entry exit pre post derivation
    certificate Hclosed Hbalanced fuel normalized Hworker.
  destruct (restricted_normalize_continued_access_inv _ _ _ _ _ _ Hworker)
    as (remaining & body' & work' & -> & _ & Hbody_worker & Hwork_worker & ->).
  destruct (RavenHoareRules.RavenHoareTriple_sequence_decompose _ _ derivation)
    as (opened_pre & Hunfold & Htail).
  destruct (RavenHoareRules.RavenHoareTriple_sequence_decompose _ _ Htail)
    as (body_post & Hbody & Hrest).
  destruct (RavenHoareRules.RavenHoareTriple_sequence_decompose _ _ Hrest)
    as (closed_pre & Hfold & Hwork).
  dependent destruction certificate; try discriminate. try view_inversion.
  dependent destruction certificate1; try discriminate. try view_inversion.
  dependent destruction certificate2; try discriminate. try view_inversion.
  dependent destruction certificate2_2; try discriminate. try view_inversion.
  dependent destruction certificate2_2_1; try discriminate. try view_inversion.
  rename e0 into Hopen, certificate2_1 into body_certificate,
    certificate2_2_2 into work_certificate.
  pose proof (baseline_nested_balanced _ _ Hbody_baseline eq_refl _ _
    body_certificate) as Hbody_open.
  pose proof (Atom.fold_after_open_records invariant _
    (RegionSyntax.argument_key arguments) _ _ _ Hopen Hbody_open)
    as Hwork_entry.
  assert (Hwork_closed : if nested then True else
      Atom.analysis_records (Atom.fold_invariant invariant
        (RegionSyntax.argument_key arguments) state1) = [])
    by (destruct nested; [exact I|]; rewrite Hwork_entry; exact Hclosed).
  destruct (IHbody F Δ _ _ _ _ Hbody body_certificate
    I Hbody_open remaining body'
    Hbody_worker) as (body_result & Hbody_result).
  destruct (IHwork F Δ _ _ _ _ Hwork work_certificate Hwork_closed
    (eq_trans Hbalanced (eq_sym Hwork_entry))
    remaining work' Hwork_worker) as (work_result & Hwork_result).
  subst body' work'.
  pose proof (restricted_normalize_statement_writes _ _ _ Hbody_worker)
    as Hbody_writes.
  pose proof (footprinted_normalization_subset body_result) as Hbody_subset.
  pose proof (footprinted_normalization_safe body_result) as Hbody_safe.
  pose proof (footprinted_normalization_subset work_result) as Hwork_subset.
  pose proof (footprinted_normalization_safe work_result) as Hwork_safe.
  set (body_normalization := footprinted_normalization body_result) in *.
  set (work_normalization := footprinted_normalization work_result) in *.
  set (body' := normalized_statement body_normalization) in *.
  set (work' := normalized_statement work_normalization) in *.
  assert (Hderivation : RavenHoareRules.RavenHoareTriple pre
    (TSeq (TInvAccess invariant arguments body') work') post).
  { eapply RavenHoareRules.RTSeq;
      [| exact (normalization_target_derivation work_normalization)].
    apply RavenHoareTriple_access_of_raw; [rewrite Hbody_writes; exact Hstable|].
    eapply RavenHoareRules.RTSeq; [exact Hunfold|].
    eapply RavenHoareRules.RTSeq; [|exact Hfold].
    exact (normalization_target_derivation body_normalization). }
  pose (target := StructuredSequence Γ state _ _ _ _
    (StructuredInvAccess Γ state invariant arguments body' state0 state1 Hopen
      (normalization_target_certificate body_normalization) Hbody_open)
    (normalization_target_certificate work_normalization)).
  unshelve eexists {| footprinted_normalization :=
    {| normalized_statement :=
         TSeq (TInvAccess invariant arguments body') work';
       normalization_target_derivation := Hderivation;
       normalization_target_certificate := target |} |}.
  - intros names stack'. rewrite runtime_stmt_linear_access_then. cbn.
    rewrite (normalization_runtime_erasure body_normalization),
      (normalization_runtime_erasure work_normalization).
    reflexivity.
  - cbn [target structured_certificate_footprint Atom.certificate_footprint].
    footprint_subset.
  - intros Hentry. cbn [target structured_accesses_outside_atomic].
    split; [split; [exact Hentry|]|].
    + apply Hbody_safe.
      rewrite (Atom.open_invariant_preserves_in_atomic _ _ _ _ Hopen). exact Hentry.
    + apply Hwork_safe. rewrite fold_invariant_in_atomic,
        (Atom.analysis_certificate_preserves_in_atomic body_certificate),
        (Atom.open_invariant_preserves_in_atomic _ _ _ _ Hopen).
      exact Hentry.
  - reflexivity.
Qed.

Lemma conditional_access_normalization_complete_from_worker {Γ} nested invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ) :
  baseline_normalizable true prefix ->
  baseline_normalizable true then_prefix ->
  baseline_normalizable true else_prefix ->
  (if proof_onlyb prefix
   then guard_proof_only guard
     (canonical_branch invariant arguments then_prefix then_continuation)
     (canonical_branch invariant arguments else_prefix else_continuation) = true
   else access_neutral then_prefix /\ access_neutral else_prefix /\
     proof_onlyb then_prefix = true /\ proof_onlyb else_prefix = true /\
     guard_proof_only guard then_continuation else_continuation = true) ->
  pexpr_list_dependencies arguments ##
    statement_writes (TSeq prefix (TSeq TDone then_prefix)) ->
  pexpr_list_dependencies arguments ##
    statement_writes (TSeq prefix (TSeq TDone else_prefix)) ->
  normalization_complete true prefix ->
  normalization_complete true then_prefix ->
  normalization_complete true else_prefix ->
  normalization_complete nested then_continuation ->
  normalization_complete nested else_continuation ->
  normalization_complete nested
    (conditional_access invariant arguments prefix guard then_prefix
      then_continuation else_prefix else_continuation).
Proof.
  intros Hq_base Htp_base Hep_base Hmode Hthen_stable Helse_stable
    IHq IHtp IHep IHtc IHec F Δ entry exit pre post derivation certificate
    Hclosed Hbalanced fuel normalized Hworker.
  destruct fuel as [|fuel]; [discriminate|].
  rewrite restricted_normalize_conditional_access_step in Hworker.
  destruct (restricted_normalize_conditional_access_inv _ _ _ _ _ _ _ _ _ _ _ _
    Hworker) as (q' & tp' & ep' & tc' & ec' & Hq_w & Htp_w & Hep_w & Htc_w &
      Hec_w & _ & _ & _ & ->).
  destruct (conditional_access_certificate_parts _ _ _ _ _ _ _ _ _ _
    certificate) as [opened joined then_closed then_exit else_closed else_exit
      Hopen cq ctp Hthen_admissible ctc cep Helse_admissible cec
      Hrecords_equal Hatomic_equal Hexit].
  subst exit.
  pose proof (Atom.analysis_certificate_unique certificate
    (conditional_access_certificate _ _ _ _ _ _ _ _ Hopen cq ctp
      Hthen_admissible ctc cep Helse_admissible cec Hrecords_equal
      Hatomic_equal)) as Hcertificate.
  subst certificate.
  pose proof (baseline_nested_balanced _ _ Hq_base eq_refl _ _ cq)
    as Hjoined_open.
  pose proof (baseline_nested_balanced _ _ Htp_base eq_refl _ _ ctp)
    as Htp_open.
  pose proof (baseline_nested_balanced _ _ Hep_base eq_refl _ _ cep)
    as Hep_open.
  pose proof (conditional_access_continuation_records _ _ _ _ Hopen cq ctp
    (baseline_nested_balanced _ _ Hq_base eq_refl)
    (baseline_nested_balanced _ _ Htp_base eq_refl)) as Hthen_entry.
  pose proof (conditional_access_continuation_records _ _ _ _ Hopen cq cep
    (baseline_nested_balanced _ _ Hq_base eq_refl)
    (baseline_nested_balanced _ _ Hep_base eq_refl)) as Helse_entry.
  cbn [Atom.analysis_records] in Hbalanced.
  pose proof (eq_trans Hbalanced (eq_sym Hthen_entry)) as Hthen_balanced.
  pose proof (eq_trans (eq_sym Hrecords_equal)
    (eq_trans Hbalanced (eq_sym Helse_entry))) as Helse_balanced.
  assert (Hthen_closed : if nested then True else
      Atom.analysis_records (Atom.fold_invariant invariant
        (RegionSyntax.argument_key arguments) then_closed) = [])
    by (destruct nested; [exact I|]; rewrite Hthen_entry; exact Hclosed).
  assert (Helse_closed : if nested then True else
      Atom.analysis_records (Atom.fold_invariant invariant
        (RegionSyntax.argument_key arguments) else_closed) = [])
    by (destruct nested; [exact I|]; rewrite Helse_entry; exact Hclosed).
  destruct (conditional_access_piece_derivations _ _ _ _ _ _ _ _ _ _
    derivation) as ((Pq & Qq & Dq) & (Ptp & Qtp & Dtp) & (Pep & Qep & Dep) &
      (Ptc & Qtc & Dtc) & (Pec & Qec & Dec)).
  destruct (piece_normalization_facts true _ _ cq fuel F Δ Pq Qq IHq Dq I
    Hjoined_open Hq_w) as (sq & Hsq_subset & Hsq_safe & Hq_erasure & Hq_sim &
      Hq_writes & Hq_proof').
  destruct (piece_normalization_facts true _ _ ctp fuel F Δ Ptp Qtp IHtp Dtp I
    Htp_open Htp_w) as (stp & Hstp_subset & Hstp_safe & Htp_erasure &
      Htp_sim & Htp_writes & Htp_proof').
  destruct (piece_normalization_facts true _ _ cep fuel F Δ Pep Qep IHep Dep I
    Hep_open Hep_w) as (sep & Hsep_subset & Hsep_safe & Hep_erasure &
      Hep_sim & Hep_writes & Hep_proof').
  destruct (piece_normalization_facts nested _ _ ctc fuel F Δ Ptc Qtc IHtc Dtc
    Hthen_closed Hthen_balanced Htc_w) as (stc & Hstc_subset & Hstc_safe &
      Htc_erasure & Htc_sim & Htc_writes & Htc_proof).
  destruct (piece_normalization_facts nested _ _ cec fuel F Δ Pec Qec IHec Dec
    Helse_closed Helse_balanced Hec_w) as (sec & Hsec_subset & Hsec_safe &
      Hec_erasure & Hec_sim & Hec_writes & Hec_proof).
  pose proof (Atom.open_invariant_preserves_in_atomic _ _ _ _ Hopen)
    as Hopened_atomic.
  pose proof (Atom.analysis_certificate_preserves_in_atomic cq)
    as Hjoined_atomic.
  destruct (proof_onlyb prefix) eqn:Hq_proof; cbv beta iota in Hmode.
  - (* Distributed: the access moves into both branches. *)
    assert (Hthen_open : Atom.analysis_records then_closed =
      Atom.analysis_records opened) by congruence.
    assert (Helse_open : Atom.analysis_records else_closed =
      Atom.analysis_records opened) by congruence.
    pose (branch := fun (branch_prefix : stmt Γ) closed
        (prefix_certificate : structured_certificate Γ joined branch_prefix
          closed) Hclosed_open =>
      StructuredInvAccess Γ entry invariant arguments
        (TSeq q' (TSeq TDone branch_prefix)) opened closed Hopen
        (StructuredSequence Γ opened q' joined (TSeq TDone branch_prefix)
          closed sq
          (StructuredSequence Γ joined TDone joined branch_prefix closed
            (StructuredDone Γ joined TDone eq_refl) prefix_certificate))
        Hclosed_open).
    pose (target := structured_guard_if guard
      (StructuredSequence Γ entry _ _ _ _
        (branch tp' then_closed stp Hthen_open) stc)
      (StructuredSequence Γ entry _ _ _ _
        (branch ep' else_closed sep Helse_open) sec)
      Hrecords_equal Hatomic_equal).
    assert (Hderivation : RavenHoareRules.RavenHoareTriple pre
      (distributed_access invariant arguments q' guard tp' tc' ep' ec') post).
    { eapply RavenHoareTriple_distributed_access;
        [exact Hq_proof | exact Hmode | | exact Hthen_stable | exact Helse_stable
        | exact Hq_sim | exact Htp_sim | exact Hep_sim | exact Htc_sim
        | exact Hec_sim | rewrite Hq_writes; set_solver
        | rewrite Htp_writes; set_solver | rewrite Hep_writes; set_solver
        | rewrite Htc_writes; set_solver | rewrite Hec_writes; set_solver
        | exact derivation].
      destruct guard; [reflexivity|].
      cbn [guard_proof_only canonical_branch proof_onlyb] in Hmode |- *.
      rewrite ?Hq_proof', ?Htp_proof', ?Hep_proof', ?Htc_proof, ?Hec_proof,
        ?Hq_proof.
      destruct (proof_onlyb then_prefix), (proof_onlyb else_prefix),
        (proof_onlyb then_continuation), (proof_onlyb else_continuation);
        cbn in *; congruence. }
    assert (Herasure : forall names stack,
      Erasure.runtime_stmt names stack
        (conditional_access invariant arguments prefix guard then_prefix
          then_continuation else_prefix else_continuation) =
      Erasure.runtime_stmt names stack
        (distributed_access invariant arguments q' guard tp' tc' ep' ec')).
    { intros names stack'. symmetry. apply distributed_access_erasure;
        [exact Hq_proof | apply Hq_erasure | apply Htp_erasure
        | apply Hep_erasure | apply Htc_erasure | apply Hec_erasure]. }
    assert (Hsubset : structured_certificate_footprint target ⊆
      Atom.certificate_footprint (conditional_access_certificate invariant arguments prefix
        guard then_prefix then_continuation else_prefix else_continuation Hopen
        cq ctp Hthen_admissible ctc cep Helse_admissible cec Hrecords_equal
        Hatomic_equal)).
    { unfold target. rewrite structured_guard_if_footprint.
      cbn [structured_certificate_footprint Atom.certificate_footprint
        conditional_access_certificate closing_branch_certificate branch].
      footprint_subset. }
    assert (Hsafe : Atom.analysis_in_atomic entry = false ->
      structured_accesses_outside_atomic target).
    { intros Hentry. unfold target.
      apply structured_guard_if_safe;
        cbn [structured_accesses_outside_atomic branch];
        (split; [split; [exact Hentry|]; split;
          [apply Hsq_safe; rewrite Hopened_atomic; exact Hentry|];
          split; [exact I|] |]).
      * apply Hstp_safe. rewrite Hjoined_atomic, Hopened_atomic. exact Hentry.
      * apply Hstc_safe. rewrite fold_invariant_in_atomic,
          (Atom.analysis_certificate_preserves_in_atomic ctp), Hjoined_atomic,
          Hopened_atomic. exact Hentry.
      * apply Hsep_safe. rewrite Hjoined_atomic, Hopened_atomic. exact Hentry.
      * apply Hsec_safe. rewrite fold_invariant_in_atomic,
          (Atom.analysis_certificate_preserves_in_atomic cep), Hjoined_atomic,
          Hopened_atomic. exact Hentry. }
    exists {| footprinted_normalization :=
      {| normalized_statement := distributed_access invariant arguments q' guard tp' tc'
           ep' ec';
         normalization_target_derivation := Hderivation;
         normalization_target_certificate := target;
         normalization_runtime_erasure := Herasure |};
      footprinted_normalization_subset := Hsubset;
      footprinted_normalization_safe := Hsafe |}.
    reflexivity.
  - (* Factored: the access closes through a ghost conditional. *)
    destruct Hmode as (Htp_neutral & Hep_neutral & Htp_proof & Hep_proof &
      Hguard).
    pose proof (unfold_free_normalize_statement_identity _ _ _
      (restricted_access_neutral_unfold_free _ Htp_neutral) Htp_w).
    pose proof (unfold_free_normalize_statement_identity _ _ _
      (restricted_access_neutral_unfold_free _ Hep_neutral) Hep_w).
    subst tp' ep'.
    pose proof (proof_only_neutral_state ctp Htp_proof Htp_neutral).
    pose proof (proof_only_neutral_state cep Hep_proof Hep_neutral).
    subst then_closed else_closed.
    pose (inner := structured_guard_if guard
      (StructuredSequence Γ joined then_prefix joined TDone joined stp
        (StructuredDone Γ joined TDone eq_refl))
      (StructuredSequence Γ joined else_prefix joined TDone joined sep
        (StructuredDone Γ joined TDone eq_refl))
      eq_refl eq_refl).
    pose (body := StructuredSequence Γ opened q' joined _ joined sq
      (StructuredSequence Γ joined TDone joined _ joined
        (StructuredDone Γ joined TDone eq_refl)
        (structured_cast (analysis_state_join_self joined) inner))).
    pose (target := StructuredSequence Γ entry _ _ _ _
      (StructuredInvAccess Γ entry invariant arguments _ opened joined Hopen
        body Hjoined_open)
      (structured_guard_if guard stc sec Hrecords_equal Hatomic_equal)).
    assert (Hderivation : RavenHoareRules.RavenHoareTriple pre
      (factored_access invariant arguments q' guard then_prefix tc'
        else_prefix ec') post).
    { eapply RavenHoareTriple_factored_access;
        [exact Htp_proof | exact Hep_proof | exact Hguard | |
        | exact Hq_sim | rewrite Hq_writes; set_solver | exact Htc_sim
        | exact Hec_sim | rewrite Htc_writes; set_solver
        | rewrite Hec_writes; set_solver | exact derivation].
      - destruct guard; [reflexivity|].
        cbn [guard_proof_only] in Hguard |- *.
        rewrite Htc_proof, Hec_proof. exact Hguard.
      - cbn [statement_writes] in Hthen_stable. set_solver. }
    assert (Herasure : forall names stack,
      Erasure.runtime_stmt names stack
        (conditional_access invariant arguments prefix guard then_prefix
          then_continuation else_prefix else_continuation) =
      Erasure.runtime_stmt names stack
        (factored_access invariant arguments q' guard then_prefix tc'
          else_prefix ec')).
    { intros names stack'. symmetry. apply factored_access_erasure;
        [exact Htp_proof | exact Hep_proof | apply Hq_erasure
        | apply Htc_erasure | apply Hec_erasure]. }
    assert (Hsubset : structured_certificate_footprint target ⊆
      Atom.certificate_footprint (conditional_access_certificate invariant arguments prefix
        guard then_prefix then_continuation else_prefix else_continuation Hopen
        cq ctp Hthen_admissible ctc cep Helse_admissible cec Hrecords_equal
        Hatomic_equal)).
    { unfold target, body.
      cbn [structured_certificate_footprint].
      rewrite structured_cast_footprint, structured_guard_if_footprint.
      unfold inner. rewrite structured_guard_if_footprint.
      cbn [structured_certificate_footprint Atom.certificate_footprint
        conditional_access_certificate closing_branch_certificate].
      rewrite analysis_state_join_self.
      footprint_subset. }
    assert (Hsafe : Atom.analysis_in_atomic entry = false ->
      structured_accesses_outside_atomic target).
    { intros Hentry. unfold target, body.
      cbn [structured_accesses_outside_atomic].
      split; [split; [exact Hentry|]; split;
        [apply Hsq_safe; rewrite Hopened_atomic; exact Hentry|]; split;
        [exact I|] |].
      * apply structured_cast_safe. unfold inner.
        apply structured_guard_if_safe; cbn; split; try exact I.
        -- apply Hstp_safe. rewrite Hjoined_atomic, Hopened_atomic. exact Hentry.
        -- apply Hsep_safe. rewrite Hjoined_atomic, Hopened_atomic. exact Hentry.
      * apply structured_guard_if_safe.
        -- apply Hstc_safe. rewrite fold_invariant_in_atomic, Hjoined_atomic,
             Hopened_atomic. exact Hentry.
        -- apply Hsec_safe. rewrite fold_invariant_in_atomic, Hjoined_atomic,
             Hopened_atomic. exact Hentry. }
    exists {| footprinted_normalization :=
      {| normalized_statement := factored_access invariant arguments q' guard then_prefix
           tc' else_prefix ec';
         normalization_target_derivation := Hderivation;
         normalization_target_certificate := target;
         normalization_runtime_erasure := Herasure |};
      footprinted_normalization_subset := Hsubset;
      footprinted_normalization_safe := Hsafe |}.
    reflexivity.
Qed.

Lemma baseline_normalization_complete_from_worker
    {Γ} nested (source : stmt Γ)
    (Hbaseline : baseline_normalizable nested source) :
  normalization_complete nested source.
Proof.
  induction Hbaseline.
  - apply unfold_free_normalization_complete.
    destruct nested; [apply restricted_access_neutral_unfold_free|]; exact y.
  - intros F Δ entry exit pre post derivation certificate Hclosed Hbalanced
      fuel normalized Hworker.
    dependent destruction certificate; try discriminate. try view_inversion.
    destruct (RavenHoareRules.RavenHoareTriple_sequence_decompose _ _
      derivation) as (middle_assertion & Hfirst & Hsecond).
    pose proof (access_neutral_records certificate1 a) as Hfirst_balanced.
    pose proof (eq_trans Hbalanced (eq_sym Hfirst_balanced)) as Hsecond_balanced.
    assert (Hsecond_closed : if nested then True else
        Atom.analysis_records middle = [])
      by (destruct nested; [exact I|]; rewrite Hfirst_balanced; exact Hclosed).
    destruct fuel as [|fuel]; cbn [restricted_normalize_statement_fuel]
      in Hworker; try discriminate.
    destruct (restricted_normalize_access_neutral_sequence_inv fuel
      first0 second0 normalized a Hworker)
      as (normalized_second & Hfirst_worker & Hsecond_worker & ->).
    destruct (unfold_free_normalization_complete true first0
      (restricted_access_neutral_unfold_free first0 a) F Δ _ _ _ _ Hfirst
      certificate1 I Hfirst_balanced fuel first0 Hfirst_worker)
      as (first_result & Hfirst_result).
    destruct (IHHbaseline F Δ _ _ _ _ Hsecond certificate2 Hsecond_closed
      Hsecond_balanced fuel normalized_second Hsecond_worker)
      as (second_result & Hsecond_result).
    replace derivation with (RavenHoareRules.RTSeq pre middle_assertion post
      first0 second0 Hfirst Hsecond) by apply ProofIrrelevance.proof_irrelevance.
    eapply footprinted_normalization_sequence_from_worker
      with (first_result := first_result) (second_result := second_result);
      try eassumption.
    all: first [reflexivity
      | destruct first0; cbn in a |- *; try contradiction; exact I].
  - intros F Δ entry exit pre post derivation certificate Hclosed Hbalanced
      fuel normalized Hworker.
    dependent destruction certificate; try discriminate. try view_inversion.
    destruct (RavenHoareRules.RavenHoareTriple_sequence_decompose _ _
      derivation) as (middle_assertion & Hfirst & Hsecond).
    assert (Hfirst_balanced : Atom.analysis_records middle =
        Atom.analysis_records state).
    { destruct nested.
      - exact (baseline_nested_balanced _ _ Hbaseline1 eq_refl _ _
          certificate1).
      - rewrite Hclosed.
        exact (baseline_normalizable_closed _ _ Hbaseline1 eq_refl _ _
          certificate1 Hclosed). }
    pose proof (eq_trans Hbalanced (eq_sym Hfirst_balanced)) as Hsecond_balanced.
    assert (Hsecond_closed : if nested then True else
        Atom.analysis_records middle = [])
      by (destruct nested; [exact I|]; rewrite Hfirst_balanced; exact Hclosed).
    destruct fuel as [|fuel]; cbn [restricted_normalize_statement_fuel]
      in Hworker; try discriminate.
    destruct (restricted_normalize_baseline_sequence_inv _ fuel first0
      second0 normalized Hbaseline1 Hworker)
      as (normalized_first & normalized_second & Hfirst_worker &
        Hsecond_worker & ->).
    destruct (IHHbaseline1 F Δ _ _ _ _ Hfirst certificate1 Hclosed
      Hfirst_balanced fuel normalized_first Hfirst_worker)
      as (first_result & Hfirst_result).
    destruct (IHHbaseline2 F Δ _ _ _ _ Hsecond certificate2 Hsecond_closed
      Hsecond_balanced fuel normalized_second Hsecond_worker)
      as (second_result & Hsecond_result).
    replace derivation with (RavenHoareRules.RTSeq pre middle_assertion post
      first0 second0 Hfirst Hsecond) by apply ProofIrrelevance.proof_irrelevance.
    eapply footprinted_normalization_sequence_from_worker
      with (first_result := first_result) (second_result := second_result);
      try eassumption.
    destruct first0; cbn; try exact I.
    exfalso. eapply baseline_normalizable_unfold_absurd. exact Hbaseline1.
  - intros F Δ entry exit pre post derivation certificate Hclosed Hbalanced
      fuel normalized Hworker.
    eapply conditional_normalization_complete_from_worker;
      try eassumption.
    + intros F0 Δ0 then_exit then_pre then_post then_derivation
        then_certificate Hthen_balanced fuel0 normalized0 Hthen_worker.
      eapply IHHbaseline1; eassumption.
    + intros F0 Δ0 else_exit else_pre else_post else_derivation
        else_certificate Helse_balanced fuel0 normalized0 Helse_worker.
      eapply IHHbaseline2; eassumption.
  - subst closing_arguments.
    apply terminal_access_normalization_complete_from_worker; assumption.
  - subst closing_arguments.
    apply continued_access_normalization_complete_from_worker; assumption.
  - intros F Δ entry exit pre post derivation certificate Hclosed Hbalanced
      fuel normalized Hworker.
    eapply ghost_val_normalization_complete_from_worker; try eassumption.
    intros F0 Δ0 body_exit body_pre body_post body_derivation
      body_certificate Hbody_balanced fuel0 normalized0 Hbody_worker.
    eapply IHHbaseline; eassumption.
  - intros F Δ entry exit pre post derivation certificate Hclosed Hbalanced
      fuel normalized Hworker.
    eapply ghost_conditional_normalization_complete_from_worker;
      try eassumption.
    + intros F0 Δ0 then_exit then_pre then_post then_derivation
        then_certificate Hthen_balanced fuel0 normalized0 Hthen_worker.
      eapply IHHbaseline1; eassumption.
    + intros F0 Δ0 else_exit else_pre else_post else_derivation
        else_certificate Helse_balanced fuel0 normalized0 Helse_worker.
      eapply IHHbaseline2; eassumption.
  - apply conditional_access_normalization_complete_from_worker;
      try assumption.
    rewrite e0. assumption.
  - apply conditional_access_normalization_complete_from_worker;
      try assumption.
    + apply BaselineUnfoldFree. exact a.
    + apply BaselineUnfoldFree. exact a0.
    + rewrite e0. repeat split; assumption.
    + apply unfold_free_normalization_complete.
      apply restricted_access_neutral_unfold_free. exact a.
    + apply unfold_free_normalization_complete.
      apply restricted_access_neutral_unfold_free. exact a0.
Qed.

(** Closed analyzer-facing completeness.  Successful restricted analysis
    supplies both the syntax induction witness and the worker result; the
    analyzer certificate closes every access it opens. *)
Lemma analyzed_normalization_exists
    {Γ F Δ pre source entry exit post}
    (analyzed : @analyzed_triple Γ F Δ pre source entry exit
      post)
    (Hentry : GenericRegions.Atomicity.analysis_open entry = ∅) :
  restricted_footprinted_normalization_exists
    (analyzed_hoare analyzed)
    (analyzed_certificate analyzed).
Proof.
  pose proof (restricted_fragment_check_sound source
    (analyzed_restricted analyzed)) as Hbaseline.
  apply Atom.analysis_open_empty in Hentry.
  pose proof (baseline_normalizable_closed _ source Hbaseline
    eq_refl entry exit (analyzed_certificate analyzed) Hentry) as Hexit.
  destruct (analyzed_worker_succeeds analyzed)
    as (normalized & Hworker).
  unfold restricted_analyze_and_normalize in Hworker.
  rewrite (analyzed_restricted analyzed) in Hworker.
  destruct (baseline_normalization_complete_from_worker _ source
    Hbaseline F Δ entry exit pre post
    (analyzed_hoare analyzed)
    (analyzed_certificate analyzed) Hentry (eq_trans Hexit (eq_sym Hentry))
    (S (normalization_statement_size source)) normalized Hworker)
    as (result & Hresult).
  exists result. unfold restricted_analyze_and_normalize.
  rewrite (analyzed_restricted analyzed), Hresult. exact Hworker.
Qed.

(** The alignment's node count, used as the traversal's budget.  Every
    recursive call descends at least one constructor, so this bounds the
    depth and the budget never decides anything. *)


End WithContracts.
End ConditionalNormalizationPrefix.
End NormalizationConditional.
