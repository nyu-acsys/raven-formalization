From Coq Require Import List String ZArith Program.Equality Lia ClassicalEpsilon.
From stdpp Require Import countable gmap namespaces sets.

From iris.algebra Require Import auth gset.
From iris.base_logic Require Import fancy_updates.
From iris.base_logic.lib Require Import own invariants.

From raven Require Import runtime.erasure analysis.structured_certificates runtime.lang runtime.ghost_state.
From raven Require Import verification.expressions analysis.atomicity verification.assertions verification.ir soundness.interpretation soundness.entailment_validity analysis.certificate_semantics soundness.runtime_model analysis.normalization_base analysis.normalization soundness.rule_validity soundness.procedure_validity.

Import ListNotations.
Import weakestpre.
Open Scope list_scope.

(** Adequacy: initialization of the runtime ghost state and the end-to-end
    library soundness theorem. *)
Module Adequacy.
Import RuleValidity ProcedureValidity.
Import Runtime RuntimeErasure.
Import Core IR Core IR Translation.
Import Translation.Assertions.

Section WithContracts.
Context {RAs : ra_base.RAConfig} {Logic : Assertion.LogicSignature}
  {Config : RuntimeConfiguration}
  {Contracts : Hoare.ResourceHoare.ResourceContractEnv}
  {Coherence : Hoare.ProcedureContractCoherence}.

Section InitializedCertifiedRuntime.
(** Dynamic semantic packages are functions of the freshly allocated
    [runtimeG].  This is the proof-relevant builder boundary needed to avoid
    choosing ghost names before [own_alloc]. *)
Definition initialized_leaf_builder {Σ : gFunctors} : Type :=
  forall RG : runtimeG Σ,
    @TermLeaf.semantic_leaf_contracts_data _ _ _ (iPropI Σ)
      (@semantic_data _ _ _ Σ RG).


(** Public syntax-only programs use the canonical operational package.
    There is no program-specific evidence at this boundary: explicit atomic
    blocks are trusted by the generic runtime semantics above. *)
Definition initialized_analyzed_program_builder {Σ : gFunctors}
    (Registration : certified_program_registration) : Type :=
  forall RG : runtimeG Σ,
    analyzed_program Registration.

End InitializedCertifiedRuntime.

(** End-to-end library boundary for the syntax-only analyzer interface.
    The only additional parameter is the single generic normalization
    completeness theorem; no procedure or example supplies a normalization
    witness. *)
Section InitializedResourceAnalyzedProgramAdequacy.
Context {Σ : gFunctors} `{!invGS Σ} `{!RuntimeGhost.heapGpreS Σ}
  `{!RuntimeModel.invTokenGpreS Σ}.
Context (Registration : certified_program_registration)
  (factory : runtime_ghost_resource_factory Σ ghost_heap_namespace)
  (build_leaf : @initialized_leaf_builder Σ)
  (Hcomplete : analyzed_normalization_complete)
  (build_program : @initialized_analyzed_program_builder Σ Registration).

Theorem initialized_analyzed_program_runtime
    (initial_state : RuntimeLang.state)
    (Hstate_wf : RuntimeGhost.state_wf initial_state)
    (Hprocedures : initial_state.(RuntimeLang.procs) =
      registered_runtime_procedure_map Registration)
    (atoms : atom_env) :
  (⊢ |={⊤}=> ∃ heap_name stack_name procedure_name ghost_domain_name
      (token_names : list gname),
    let heapG0 := Runtime.initialized_heapG heap_name stack_name procedure_name
      ghost_domain_name in
    let simpLangG0 := Runtime.initialized_simpLangG heap_name stack_name
      procedure_name ghost_domain_name in
    ∃ ghost_resource : runtime_ghost_resource _ _ factory simpLangG0,
    let invTokenG0 := registered_invTokenG Registration token_names in
    let runtimeG0 := runtimeG_with_ghost_resource simpLangG0 invTokenG0
      factory ghost_resource in
    let Leaf := build_leaf runtimeG0 in
    @RuntimeGhost.state_interp _ Σ heapG0 initial_state ∗
    @global_world_context _ _ _ _ _ Σ runtimeG0 Leaf Registration atoms)%I.
Proof.
  iMod (Runtime.initialized_runtime_resources_alloc initial_state Hstate_wf
    (length (registered_invariant_enumeration Registration)) factory)
    as (heap_name stack_name procedure_name ghost_domain_name token_names)
      "[%Htoken_facts Hresources]".
  destruct Htoken_facts as [Htokens_length Htokens_nodup].
  iDestruct "Hresources" as (ghost_resource)
    "[Hstate [#Hprocedures Htokens]]".
  iPoseProof (@registered_invtoken_authorities _ _ _ _ _ Σ _ Registration token_names
    Htokens_length with "Htokens") as "Htokens".
  set (heapG0 := Runtime.initialized_heapG heap_name stack_name procedure_name
    ghost_domain_name).
  set (simpLangG0 := Runtime.initialized_simpLangG heap_name stack_name
    procedure_name ghost_domain_name).
  set (invTokenG0 := registered_invTokenG Registration token_names).
  set (runtimeG0 := runtimeG_with_ghost_resource simpLangG0 invTokenG0
    factory ghost_resource).
  set (Leaf := build_leaf runtimeG0).
  set (program := build_program runtimeG0).
  iMod (@term_world_context_alloc _ _ _ _ _ Σ runtimeG0 Leaf Registration atoms
    with "[Htokens]") as "#Hworld".
  { iExact "Htokens". }
  iEval (rewrite Hprocedures) in "Hprocedures".
  iPoseProof (bi.equiv_entails_1_1 _ _
    (@runtime_procedure_map_chunks _ _ _ _ _ Σ runtimeG0 Registration )
    with "Hprocedures") as "#Hchunks".
  iPoseProof
    (@term_analyzed_configured_verified_procedure_specs_valid _ _ _ _ _ Σ
      runtimeG0 Leaf eq_refl Registration Hcomplete program
      with "Hchunks") as "#Hspecs".
  iModIntro.
  iExists heap_name, stack_name, procedure_name, ghost_domain_name,
    token_names, ghost_resource.
  simpl. iFrame "Hstate".
  rewrite /global_world_context. iFrame "Hworld Hchunks Hspecs".
Qed.

Theorem raven_analyzed_library_soundness
    (initial_state : RuntimeLang.state)
    (Hstate_wf : RuntimeGhost.state_wf initial_state)
    (Hprocedures : initial_state.(RuntimeLang.procs) =
      registered_runtime_procedure_map Registration)
    (atoms : atom_env) :
  (⊢ |={⊤}=> ∃ heap_name stack_name procedure_name ghost_domain_name
      (token_names : list gname),
    let heapG0 := Runtime.initialized_heapG heap_name stack_name procedure_name
      ghost_domain_name in
    let simpLangG0 := Runtime.initialized_simpLangG heap_name stack_name
      procedure_name ghost_domain_name in
    ∃ ghost_resource : runtime_ghost_resource _ _ factory simpLangG0,
    let invTokenG0 := registered_invTokenG Registration token_names in
    let runtimeG0 := runtimeG_with_ghost_resource simpLangG0 invTokenG0
      factory ghost_resource in
    let Leaf := build_leaf runtimeG0 in
    @RuntimeGhost.state_interp _ Σ heapG0 initial_state ∗
    @global_world_context _ _ _ _ _ Σ runtimeG0 Leaf Registration atoms)%I.
Proof.
  exact (initialized_analyzed_program_runtime initial_state Hstate_wf
    Hprocedures atoms).
Qed.

End InitializedResourceAnalyzedProgramAdequacy.
End WithContracts.
End Adequacy.
