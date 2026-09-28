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
    module soundness theorem. *)
Module Adequacy.
Import RuleValidity ProcedureValidity.
Import Runtime RuntimeErasure.
Import Core IR Core IR Translation.
Import Translation.Assertions.

(** The executable registration determined by a module. *)
Definition module_registration {RAs : ra_base.RAConfig}
    {Logic : Assertion.LogicSignature} (M : Hoare.module) :
    @certified_module_registration RAs Logic
      (Hoare.module_contracts M) (Hoare.module_coherence M) :=
  @canonical_registration RAs Logic
    (Hoare.module_contracts M) (Hoare.module_coherence M)
    (list_to_set (Hoare.module_invariants M)).

(** Analysis evidence indexed by the module.  Registry coverage is checked
    per procedure against the module declarations.  It deliberately ranges
    over the analyzed body footprint, rather than over the invariants exposed
    by the procedure contract: a body may allocate or use an invariant
    internally without exporting its capability to callers. *)
Definition packed_analyzed_body_exit_declared {RAs : ra_base.RAConfig}
    {Logic : Assertion.LogicSignature} (M : Hoare.module)
    (packed : packed_typed_procedure)
    (body : @packed_analyzed_body RAs Logic (Hoare.module_contracts M)
      packed) : Prop :=
  match packed as packed0 return
      @packed_analyzed_body RAs Logic (Hoare.module_contracts M) packed0 ->
      Prop with
  | existT Γ (existT identity procedure) => fun body0 =>
      GenericRegions.Atomicity.analysis_mask
        (analyzed_body_exit procedure
          (Certified.required_mask identity) body0) ⊆
      list_to_set (Hoare.module_invariants M)
  end body.

Record module_analysis {RAs : ra_base.RAConfig}
    {Logic : Assertion.LogicSignature} (M : Hoare.module) : Type :=
  ModuleAnalysis {
    module_analysis_bodies : forall packed
        (Hin : List.In packed
          (procedure_entries (Hoare.module_procedures M))),
      { body : @packed_analyzed_body RAs Logic (Hoare.module_contracts M)
          packed &
        packed_analyzed_body_exit_declared M packed body };
  }.

Section WithContracts.
Context {RAs : ra_base.RAConfig} {Logic : Assertion.LogicSignature}
  {Contracts : Hoare.ResourceHoare.ResourceContractEnv}
  {Coherence : Hoare.ProcedureContractCoherence}.

(** End-to-end module boundary for the syntax-only analyzer interface.
    Normalization completeness is discharged internally; no procedure or
    example supplies a normalization witness. *)
Section InitializedResourceAnalyzedModuleAdequacy.
Context {Σ : gFunctors} `{!invGS Σ} `{!RuntimeGhost.heapGpreS Σ}
  `{!RuntimeModel.invTokenGpreS Σ}.
Context (Registration : certified_module_registration)
  (factory : runtime_ghost_resource_factory Σ ghost_heap_namespace)
  (certificates : analyzed_module Registration).

Theorem initialized_analyzed_module_runtime
    (initial_state : RuntimeLang.state)
    (Hstate_wf : RuntimeGhost.state_wf initial_state)
    (Hprocedures : initial_state.(RuntimeLang.procs) =
      registered_runtime_procedure_map Registration)
    (valuation : symbol_valuation) :
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
    @RuntimeGhost.state_interp _ Σ heapG0 initial_state ∗
    @global_world_context _ _ _ _ Σ runtimeG0 Registration valuation)%I.
Proof.
  iMod (Runtime.initialized_runtime_resources_alloc initial_state Hstate_wf
    (length (registered_invariant_enumeration Registration)) factory)
    as (heap_name stack_name procedure_name ghost_domain_name token_names)
      "[%Htoken_facts Hresources]".
  destruct Htoken_facts as [Htokens_length Htokens_nodup].
  iDestruct "Hresources" as (ghost_resource)
    "[Hstate [#Hprocedures Htokens]]".
  iPoseProof (@registered_invtoken_authorities _ _ _ _ Σ _ Registration token_names
    Htokens_length with "Htokens") as "Htokens".
  set (heapG0 := Runtime.initialized_heapG heap_name stack_name procedure_name
    ghost_domain_name).
  set (simpLangG0 := Runtime.initialized_simpLangG heap_name stack_name
    procedure_name ghost_domain_name).
  set (invTokenG0 := registered_invTokenG Registration token_names).
  set (runtimeG0 := runtimeG_with_ghost_resource simpLangG0 invTokenG0
    factory ghost_resource).
  iMod (@term_world_context_alloc _ _ _ _ Σ runtimeG0 Registration valuation
    with "[Htokens]") as "#Hworld".
  { iExact "Htokens". }
  iEval (rewrite Hprocedures) in "Hprocedures".
  iPoseProof (bi.equiv_entails_1_1 _ _
    (@runtime_procedure_map_chunks _ _ _ _ Σ runtimeG0 Registration )
    with "Hprocedures") as "#Hchunks".
  iPoseProof
    (@term_analyzed_configured_verified_procedure_specs_valid _ _ _ _ Σ
      runtimeG0 eq_refl Registration
      analyzed_normalization_complete_from_raw_access_cut certificates
      with "Hchunks") as "#Hspecs".
  iModIntro.
  iExists heap_name, stack_name, procedure_name, ghost_domain_name,
    token_names, ghost_resource.
  simpl. iFrame "Hstate".
  rewrite /global_world_context. iFrame "Hworld Hchunks Hspecs".
Qed.

End InitializedResourceAnalyzedModuleAdequacy.
End WithContracts.

(** Module soundness: every procedure of the module meets its
    contract, for any caller.  The module's contract environment, the
    coherence of that environment with its procedure table, the semantics of
    its predicates, and its runtime registration are derived from the
    module, so they are not parameters. *)
Section ModuleSoundness.
Context {RAs : ra_base.RAConfig} {Logic : Assertion.LogicSignature}.
Context (M : Hoare.module).
#[local] Instance module_contracts_instance :
  Hoare.ResourceHoare.ResourceContractEnv := Hoare.module_contracts M.
#[local] Instance module_coherence_instance :
  Hoare.ProcedureContractCoherence := Hoare.module_coherence M.

Context {Σ : gFunctors} `{!invGS Σ} `{!RuntimeGhost.heapGpreS Σ}
  `{!RuntimeModel.invTokenGpreS Σ}.
Local Notation Registration :=
  (module_registration M).
Context (factory : runtime_ghost_resource_factory Σ ghost_heap_namespace)
  (certificates : module_analysis M).

Definition module_analyzed_certificates : analyzed_module Registration.
Proof.
  unshelve econstructor.
  - intros packed Hin.
    exact (projT1 (module_analysis_bodies M certificates packed Hin)).
  - intros Γ identity procedure Hin.
    set (selected := module_analysis_bodies M certificates
      (pack_typed_procedure procedure) Hin).
    etrans; last exact (projT2 selected).
    eapply GenericRegions.Atomicity.closed_coherent_certificate_footprint_subset_exit_mask.
    + exact (analyzed_body_conditionals _ _ (projT1 selected)).
    + exact (analyzed_body_exit_closed _ _ (projT1 selected)).
Defined.

Theorem raven_module_soundness
    (initial_state : RuntimeLang.state)
    (Hstate_wf : RuntimeGhost.state_wf initial_state)
    (Hprocedures : initial_state.(RuntimeLang.procs) =
      registered_runtime_procedure_map Registration)
    (valuation : symbol_valuation) :
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
    @RuntimeGhost.state_interp _ Σ heapG0 initial_state ∗
    @global_world_context _ _ _ _ Σ runtimeG0 Registration valuation)%I.
Proof.
  exact (initialized_analyzed_module_runtime Registration factory
    module_analyzed_certificates initial_state Hstate_wf Hprocedures valuation).
Qed.
End ModuleSoundness.
End Adequacy.
