From Coq Require Import List String ZArith Program.Equality Lia ClassicalEpsilon.
From stdpp Require Import countable gmap namespaces sets.

From iris.algebra Require Import auth gset.
From iris.base_logic Require Import fancy_updates.
From iris.base_logic.lib Require Import own invariants.

From raven Require Import runtime.erasure analysis.structured_certificates runtime.lang runtime.ghost_state.
From raven Require Import verification.expressions analysis.atomicity verification.assertions verification.ir soundness.interpretation soundness.entailment_validity analysis.certificate_semantics soundness.runtime_model analysis.normalization_base analysis.normalization soundness.rule_validity.

Import ListNotations.
Import weakestpre.
Open Scope list_scope.

(** Procedure validity: analyzed procedure bodies, the verified procedure
    table, and call/spawn closure over the rule validity theorem. *)
Module ProcedureValidity.
Import RuleValidity.
Import Runtime RuntimeErasure.
Import Core IR Core IR Translation.
Import Translation.Assertions.

Section WithContracts.
Context {RAs : ra_base.RAConfig} {Logic : Assertion.LogicSignature}
  {Config : RuntimeConfiguration}
  {Contracts : Hoare.ResourceHoare.ResourceContractEnv}
  {Coherence : Hoare.ProcedureContractCoherence}.

Section WithRuntime.
Context {Σ : gFunctors} `{RG : !runtimeG Σ}.
Local Existing Instances RuleValidity.core_simpLangG RuleValidity.core_invTokenG
  RuleValidity.core_heapG RuleValidity.core_irisG.
Local Existing Instance weakestpre.wp'.
Local Notation iProp := (bi_car (iPropI Σ)).

Context (Leaf : @TermLeaf.semantic_leaf_contracts_data _ _ _
  (iPropI Σ) semantic_data).
Context (Hruntime_ghost_namespace :
  @runtime_ghost_namespace _ _ Σ RG = ghost_heap_namespace).
Context (Registration : certified_program_registration).

Local Notation all_registered_procedure_chunks := (@RuleValidity.all_registered_procedure_chunks _ _ _ _ _ _ _ Registration).
Local Notation all_registered_procedure_chunks_lookup := (@RuleValidity.all_registered_procedure_chunks_lookup _ _ _ _ _ _ _ Registration).
Local Notation global_world_context := (@RuleValidity.global_world_context _ _ _ _ _ _ _ Leaf Registration).
Local Notation global_world_context_stable_atoms := (@RuleValidity.global_world_context_stable_atoms _ _ _ _ _ _ _ Leaf Registration).
Local Notation procedure_body_post_interp := (@RuleValidity.procedure_body_post_interp _ _ _ _ _ _ Leaf).
Local Notation procedure_post_instantiation_interp := (@RuleValidity.procedure_post_instantiation_interp _ _ _ _ _ _ _ Leaf).
Local Notation procedure_pre_instantiation_interp := (@RuleValidity.procedure_pre_instantiation_interp _ _ _ _ _ _ Leaf).
Local Notation registered_procedure_chunk := (@RuleValidity.registered_procedure_chunk _ _ _ _ _ _ _ Registration).
Local Notation runtime_procedure_entry := (@RuleValidity.runtime_procedure_entry _ _ _ _ _ Registration).
Local Notation runtime_procedure_entry_coherent := (@RuleValidity.runtime_procedure_entry_coherent _ _ _ _ _ Registration).
Local Notation runtime_procedure_map_chunks := (@RuleValidity.runtime_procedure_map_chunks _ _ _ _ _ _ _ Registration).
Local Notation term_interp_core := (@RuleValidity.term_interp_core _ _ _ _ _ _ Leaf).
Local Notation term_interp_core_stable_atoms := (@RuleValidity.term_interp_core_stable_atoms _ _ _ _ _ _ Leaf).
Local Notation term_interp_resource_prenex := (@RuleValidity.term_interp_resource_prenex _ _ _ _ _ _ Leaf).
Local Notation term_procedure_body_source_valid_footprinted := (@RuleValidity.term_procedure_body_source_valid_footprinted _ _ _ _ _ _ _ Leaf Registration).
Local Notation term_registered_invariants := (@RuleValidity.term_registered_invariants _ _ _ _ _ Registration).
Local Notation term_runtime_procedure_layout_configured := (@RuleValidity.term_runtime_procedure_layout_configured _ _ _ _ _ Registration).
Local Notation term_runtime_procedure_statement := (@RuleValidity.term_runtime_procedure_statement _ _ _ _ _ Registration).
Local Notation term_structured_certificate_resource_prenex_valid := (@RuleValidity.term_structured_certificate_resource_prenex_valid _ _ _ _ _ _ _ Leaf Hruntime_ghost_namespace Registration).
Local Notation term_structured_runtime_valid := (@RuleValidity.term_structured_runtime_valid _ _ _ _ _ _ _ Leaf Registration).
Local Notation term_world_context_alloc := (@RuleValidity.term_world_context_alloc _ _ _ _ _ _ _ Leaf Registration).
Local Notation verified_procedure_specs := (@RuleValidity.verified_procedure_specs _ _ _ _ _ _ _ Leaf Registration).
Local Notation verified_procedure_specs_valid := (@RuleValidity.verified_procedure_specs_valid _ _ _ _ _ _ _ Leaf Registration).

(* ------------------------------------------------------------------ *)
(** *** The resource-calculus procedure boundary

    This is the syntax-driven, proposition-valued input consumed by generic
    normalization.  Stable procedure facts and the analyzer certificate are
    recorded directly; alignment and normalization witnesses are derived by
    the generic completeness theorem rather than supplied by each program. *)
(** The canonical cost model is sound for the runtime: proof-only leaves
    erase to the terminal statement and the physical primitives are atomic
    runtime statements.  Together with
    [Certified.contract_cost_model_procedure_sound] this discharges both
    cost-model conditions once, for every program. *)
Lemma contract_cost_model_runtime_sound :
  RegionExecution.Primitives.Model.runtime_cost_model_sound
.
Proof.
  intros Γ names stack statement Hview.
  destruct statement; cbn in Hview; try discriminate;
    cbn [Certified.contract_cost_model].
  (* procedure calls and spawns need no witness *)
  all: try exact I.
  (* proof-only leaves erase to the terminal statement *)
  all: try reflexivity.
  all: cbn [RuntimeErasure.runtime_stmt].
  all: first
    [ apply RuntimeLang.atomic_assign
    | apply RuntimeLang.atomic_fld_rd
    | apply RuntimeLang.atomic_fld_wr
    | apply RuntimeLang.atomic_alloc ].
Qed.

Record analyzed_body_certificate {Γ identity}
    (procedure : typed_procedure Γ identity) (current_mask : Hoare.mask)
    : Type := AnalyzedBodyCertificate {
  analyzed_body_entry : GenericRegions.Atomicity.analysis_state;
  analyzed_body_exit : GenericRegions.Atomicity.analysis_state;
  analyzed_body_exit_context : context;
  analyzed_body_exit_store :
    symbolic_store Γ (Assertion.procedure_args identity)
      analyzed_body_exit_context;
  analyzed_body_return_reference :
    value_ref (Assertion.procedure_args identity)
      analyzed_body_exit_context
      (procedure_return_type _ _ procedure);
  analyzed_body_exit_return :
    lookup_store analyzed_body_exit_store _
      (procedure_return_variable _ _ procedure) =
        analyzed_body_return_reference;
  analyzed_body_entry_wf :
    GenericRegions.Atomicity.state_wf analyzed_body_entry;
  analyzed_body_entry_closed :
    GenericRegions.Atomicity.analysis_open analyzed_body_entry = ∅;
  analyzed_body_entry_outside_atomic :
    GenericRegions.Atomicity.analysis_in_atomic
      analyzed_body_entry = false;
  analyzed_body_exit_closed :
    GenericRegions.Atomicity.analysis_open analyzed_body_exit = ∅;
  analyzed_body_entry_mask :
    GenericRegions.Atomicity.analysis_mask analyzed_body_entry =
      current_mask;
  analyzed_body_exit_mask :
    GenericRegions.Atomicity.analysis_mask analyzed_body_exit =
      current_mask ∪ Certified.granted_mask
        (procedure_identity _ _ procedure);
  analyzed_body_triple :
    @CertifiedNormalization.analyzed_triple _ _ _
 Γ (Assertion.procedure_args identity)
      (@nil typ)
      (Hoare.procedure_body_pre procedure)
      (procedure_body _ _ procedure)
      analyzed_body_entry analyzed_body_exit
      (Hoare.procedure_body_post procedure
        analyzed_body_exit_store
        analyzed_body_return_reference);
  analyzed_body_conditionals :
    GenericRegions.Atomicity.conditional_masks_coherent
      (CertifiedNormalization.analyzed_certificate
        analyzed_body_triple);
}.

Arguments analyzed_body_triple {_ _} _ _ _.
Arguments analyzed_body_entry {_ _} _ _ _.
Arguments analyzed_body_exit {_ _} _ _ _.
Arguments analyzed_body_exit_store {_ _} _ _ _.
Arguments analyzed_body_return_reference {_ _} _ _ _.
Arguments analyzed_body_entry_wf {_ _} _ _ _.
Arguments analyzed_body_entry_outside_atomic {_ _} _ _ _.
Arguments analyzed_body_exit_return {_ _} _ _ _.
Arguments analyzed_body_entry_closed {_ _} _ _ _.
Arguments analyzed_body_exit_closed {_ _} _ _ _.
Arguments analyzed_body_exit_mask {_ _} _ _ _.
Arguments analyzed_body_conditionals {_ _} _ _ _.

Definition analyzed_body_normalization_exists {Γ identity}
    (procedure : typed_procedure Γ identity) (current_mask : Hoare.mask)
    (body : analyzed_body_certificate procedure current_mask) : Prop :=
  CertifiedNormalization.restricted_footprinted_normalization_exists
    (CertifiedNormalization.analyzed_hoare
      (analyzed_body_triple _ _ body))
    (CertifiedNormalization.analyzed_certificate
      (analyzed_body_triple _ _ body)).

(** Proof-level procedure bridge for the syntax-only analyzer.  The
    normalization witness stays existential: this theorem destructs it only
    while proving an Iris proposition, so neither programs nor executable
    analysis packages carry proof-relevant normalization data. *)
Theorem term_analyzed_body_source_valid
    {Γ identity} (procedure : typed_procedure Γ identity)
    (current_mask : Hoare.mask)
    (body : analyzed_body_certificate procedure current_mask)
    (Hnormalizes : analyzed_body_normalization_exists procedure
      current_mask body)
    (Hregistered : GenericRegions.Atomicity.certificate_footprint
      (CertifiedNormalization.analyzed_certificate
        (analyzed_body_triple _ _ body)) ⊆
      term_registered_invariants ) :
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env (Assertion.procedure_args identity))
    (atoms : atom_env) (ambient : coPset),
    RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint
        (CertifiedNormalization.analyzed_certificate
          (analyzed_body_triple _ _ body))) ⊆ ambient ->
    (global_world_context atoms ∗
     term_interp_resource_prenex runtime formals empty_binder_env atoms
       (Hoare.procedure_body_pre procedure)) ⊢
    translated_runtime_wp runtime ambient
      (analyzed_body_entry _ _ body)
      (analyzed_body_exit _ _ body)
      (procedure_body _ _ procedure)
      (global_world_context atoms ∗
       term_interp_resource_prenex runtime formals empty_binder_env atoms
         (Hoare.procedure_body_post procedure
           (analyzed_body_exit_store _ _ body)
           (analyzed_body_return_reference _ _ body))).
Proof.
  destruct Hnormalizes as [normalization Hworker].
  have Hvalid : term_structured_runtime_valid
      (CertifiedNormalization.normalization_target_certificate
        (CertifiedNormalization.footprinted_normalization
          normalization))
      (Hoare.procedure_body_pre procedure)
      (Hoare.procedure_body_post procedure
        (analyzed_body_exit_store _ _ body)
        (analyzed_body_return_reference _ _ body)).
  { exact (proj1 (term_structured_certificate_resource_prenex_valid
      (CertifiedNormalization.normalization_target_certificate
        (CertifiedNormalization.footprinted_normalization
          normalization))
      (CertifiedNormalization.normalization_target_derivation
        (CertifiedNormalization.footprinted_normalization
          normalization))
      (analyzed_body_entry_wf _ _ body)
      contract_cost_model_runtime_sound
      Certified.contract_cost_model_procedure_sound
      (fun invariant Hin => Hregistered invariant
        (CertifiedNormalization.footprinted_normalization_subset
          normalization invariant Hin))
      ((CertifiedNormalization.footprinted_normalization_safe
        normalization)
        (analyzed_body_entry_outside_atomic _ _ body)))). }
  exact (term_procedure_body_source_valid_footprinted
    procedure
    (analyzed_body_exit_store _ _ body)
    (analyzed_body_return_reference _ _ body)
    eq_refl eq_refl
    (CertifiedNormalization.analyzed_hoare
      (analyzed_body_triple _ _ body))
    (CertifiedNormalization.analyzed_certificate
      (analyzed_body_triple _ _ body))
    normalization eq_refl Hvalid).
Qed.

(** Exit-mask envelope used by recursive call/spawn closure. *)
Theorem term_analyzed_body_exit_mask_valid
    {Γ identity} (procedure : typed_procedure Γ identity)
    (current_mask : Hoare.mask)
    (body : analyzed_body_certificate procedure current_mask)
    (Hnormalizes : analyzed_body_normalization_exists procedure
      current_mask body)
    (Hregistered : GenericRegions.Atomicity.certificate_footprint
      (CertifiedNormalization.analyzed_certificate
        (analyzed_body_triple _ _ body)) ⊆
      term_registered_invariants ) :
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env (Assertion.procedure_args identity))
    (atoms : atom_env) (ambient : coPset),
    RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.analysis_mask
        (analyzed_body_exit _ _ body)) ⊆ ambient ->
    (global_world_context atoms ∗
     term_interp_resource_prenex runtime formals empty_binder_env atoms
       (Hoare.procedure_body_pre procedure)) ⊢
    translated_runtime_wp runtime ambient
      (analyzed_body_entry _ _ body)
      (analyzed_body_exit _ _ body)
      (procedure_body _ _ procedure)
      (global_world_context atoms ∗
       term_interp_resource_prenex runtime formals empty_binder_env atoms
         (Hoare.procedure_body_post procedure
           (analyzed_body_exit_store _ _ body)
           (analyzed_body_return_reference _ _ body))).
Proof.
  intros runtime formals atoms ambient Henvelope.
  destruct Hnormalizes as [normalization Hworker].
  have Hsource_envelope : RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint
        (CertifiedNormalization.analyzed_certificate
          (analyzed_body_triple _ _ body))) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    eapply GenericRegions.Atomicity.closed_coherent_certificate_footprint_subset_exit_mask.
    - exact (analyzed_body_conditionals _ _ body).
    - exact (analyzed_body_exit_closed _ _ body). }
  exact (term_analyzed_body_source_valid procedure
    current_mask body (ex_intro _ normalization Hworker) Hregistered
    runtime formals atoms ambient Hsource_envelope).
Qed.

Definition analyzed_body_valid {Γ identity}
    (procedure : typed_procedure Γ identity) : Type :=
  analyzed_body_certificate procedure
    (Certified.required_mask (procedure_identity _ _ procedure)).

Definition packed_analyzed_body
    (packed : packed_typed_procedure) : Type :=
  match packed with
  | existT Γ (existT identity procedure) =>
      @analyzed_body_valid Γ identity procedure
  end.

(** Program data for the syntax-only analysis path.  In particular this
    record contains no normalization witness and no alignment proof. *)
Record analyzed_program : Type := {
  analyzed_program_bodies : forall packed,
    List.In packed (procedure_entries Hoare.coherent_procedures) ->
    packed_analyzed_body packed;
  analyzed_program_registered : forall Γ identity
      (procedure : typed_procedure Γ identity)
      (Hin : List.In (pack_typed_procedure procedure)
        (procedure_entries Hoare.coherent_procedures)),
    GenericRegions.Atomicity.certificate_footprint
      (CertifiedNormalization.analyzed_certificate
        (analyzed_body_triple _ _
          (analyzed_program_bodies
            (pack_typed_procedure procedure) Hin))) ⊆
      term_registered_invariants ;
}.

Arguments analyzed_program_registered _ {_ _} _ _.

(** Generic producer completeness.  Successful restricted analysis and the
    closed procedure-entry state are sufficient; programs and examples carry
    no normalization or alignment witness. *)
Definition analyzed_normalization_complete : Prop :=
  forall Γ identity (procedure : typed_procedure Γ identity)
    (body : analyzed_body_valid procedure),
    analyzed_body_normalization_exists procedure
      (Certified.required_mask (procedure_identity _ _ procedure)) body.

(** This assembly is closed once the proof-theoretic raw-access cut in the
    normalization layer is discharged.  Its assumptions are intentionally
    kept visible in that layer until the analyzed access rule is validated. *)
Theorem analyzed_normalization_complete_from_raw_access_cut :
  analyzed_normalization_complete.
Proof.
  intros Γ identity procedure body.
  apply CertifiedNormalization.analyzed_normalization_exists.
  exact (analyzed_body_entry_closed _ _ body).
Qed.

(** Feeding the produced normalization to the procedure-level theorem.

    Structured validity of the *target* certificate is no longer a
    premise: it is derived here from
    [term_structured_certificate_resource_prenex_valid], the body
    certificate's [state_wf] and [entry_outside_atomic] fields, the
    analyzed body's cost-soundness proof, and the produced result's
    footprint-subset and safety fields.  The remaining environment facts are
    runtime cost-model soundness and registry coverage. *)


(** The recursive call/spawn closure needs only this semantic projection of an
    analyzed body.  It isolates the expensive Iris assembly proof from the
    syntax-directed normalization data. *)
Record term_registered_body_semantics {Γ F}
    (procedure : typed_procedure Γ F) : Type := {
  term_semantic_body_entry : GenericRegions.Atomicity.analysis_state;
  term_semantic_body_exit : GenericRegions.Atomicity.analysis_state;
  term_semantic_body_exit_context : context;
  term_semantic_body_exit_store :
    symbolic_store Γ (Assertion.procedure_args F) term_semantic_body_exit_context;
  term_semantic_body_return_reference :
    value_ref (Assertion.procedure_args F) term_semantic_body_exit_context
      (procedure_return_type _ _ procedure);
  term_semantic_body_exit_return :
    lookup_store term_semantic_body_exit_store _
      (procedure_return_variable _ _ procedure) =
        term_semantic_body_return_reference;
  term_semantic_body_entry_closed :
    GenericRegions.Atomicity.analysis_open term_semantic_body_entry = ∅;
  term_semantic_body_exit_closed :
    GenericRegions.Atomicity.analysis_open term_semantic_body_exit = ∅;
  term_semantic_body_exit_mask :
    GenericRegions.Atomicity.analysis_mask term_semantic_body_exit =
      Certified.required_mask (procedure_identity _ _ procedure) ∪
      Certified.granted_mask (procedure_identity _ _ procedure);
  term_semantic_body_source_valid : forall
      (runtime : RegionExecution.Primitives.Model.stack_context Γ)
      (formals : formal_env (Assertion.procedure_args F)) (atoms : atom_env) ambient,
    RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.analysis_mask term_semantic_body_exit) ⊆
      ambient ->
    (global_world_context atoms ∗
     term_interp_resource_prenex runtime formals empty_binder_env atoms
       (Hoare.procedure_body_pre procedure)) ⊢
    translated_runtime_wp runtime ambient term_semantic_body_entry
      term_semantic_body_exit (procedure_body _ _ procedure)
      (global_world_context atoms ∗
       term_interp_resource_prenex runtime formals empty_binder_env atoms
         (Hoare.procedure_body_post procedure term_semantic_body_exit_store
           term_semantic_body_return_reference));
}.

Record term_semantic_program_certificates : Type := {
  term_semantic_procedure_bodies : forall Γ F
      (procedure : typed_procedure Γ F),
    List.In (pack_typed_procedure procedure)
      (procedure_entries Hoare.coherent_procedures) ->
    term_registered_body_semantics procedure;
}.

(** Semantic projection of the syntax-only analyzer path.  Once the single
    generic normalization-completeness theorem is available, recursive
    call/spawn closure needs no proof-relevant producer data. *)
Definition term_analyzed_semantic_program
    (Hcomplete : analyzed_normalization_complete)
    (program : analyzed_program ) :
    term_semantic_program_certificates .
Proof.
  refine {| term_semantic_procedure_bodies := _ |}.
  intros Γ F procedure Hin.
  set (body := analyzed_program_bodies program
    (pack_typed_procedure procedure) Hin).
  refine {| term_semantic_body_entry :=
      analyzed_body_entry _ _ body;
    term_semantic_body_exit := analyzed_body_exit _ _ body;
    term_semantic_body_exit_context :=
      analyzed_body_exit_context _ _ body;
    term_semantic_body_exit_store :=
      analyzed_body_exit_store _ _ body;
    term_semantic_body_return_reference :=
      analyzed_body_return_reference _ _ body |}.
  - exact (analyzed_body_exit_return _ _ body).
  - exact (analyzed_body_entry_closed _ _ body).
  - exact (analyzed_body_exit_closed _ _ body).
  - exact (analyzed_body_exit_mask _ _ body).
  - intros runtime formals atoms ambient Henvelope.
    eapply term_analyzed_body_exit_mask_valid.
    + exact (Hcomplete Γ F procedure body).
    + exact (analyzed_program_registered program procedure Hin).
    + exact Henvelope.
Defined.

(** The assembly lemmas below use the executable runtime WP directly. *)
Local Instance term_assembly_wp :
    Wp iProp RuntimeLang.runtime_stmt RuntimeLang.val stuckness :=
  @weakestpre.wp' HasLc RuntimeLang.simp_lang Σ core_irisG.

(** Concrete execution boundary for a discarded procedure result in the
    certificate-indexed runtime.  The delayed premise is the body
    specification supplied by the certified-body theorem after choosing the
    canonical fresh frame. *)
Lemma term_procedure_discard_assembly
    {callee_variables callee_formals}
    (callee : typed_procedure callee_variables callee_formals)
    (caller_id : RuntimeLang.stack_id)
    (caller_frame : RuntimeLang.stack_frame)
    (arguments : list RuntimeLang.expr)
    (values : list RuntimeLang.val) (mask : coPset)
    (p : iProp) (q : RuntimeLang.val -> iProp)
    (Hin : List.In (pack_typed_procedure callee)
      (procedure_entries Hoare.coherent_procedures))
    (Hlength : length arguments = length (Assertion.procedure_args callee_formals))
    (Harguments : Forall2 (fun expression value =>
      RuntimeLang.expr_step expression caller_frame (RuntimeLang.Val value))
      arguments values) :
  let Hbody := (▷ (∀ stack_id frame,
      ⌜Forall2 (fun variable value => frame.(RuntimeLang.locals) !! variable =
          Some value)
          (RuntimeLang.proc_args
            (runtime_procedure_entry  (pack_typed_procedure callee))).*1 values /\
        (forall variable type,
          (variable, type) ∈ RuntimeLang.proc_local_vars
            (runtime_procedure_entry  (pack_typed_procedure callee)) ->
          exists value, frame.(RuntimeLang.locals) !! variable = Some value /\
            RuntimeLang.val_has_typ value type) /\
        dom frame.(RuntimeLang.locals) =
          list_to_set (RuntimeLang.proc_args
            (runtime_procedure_entry  (pack_typed_procedure callee))).*1 ∪
          list_to_set (RuntimeLang.proc_local_vars
            (runtime_procedure_entry  (pack_typed_procedure callee))).*1⌝ -∗
      {{{ RuntimeGhost.stack_frame_own stack_id frame ∗ p }}}
        RuntimeLang.to_rtstmt stack_id
          (RuntimeLang.proc_stmt
            (runtime_procedure_entry  (pack_typed_procedure callee))) @ mask
      {{{ RET RuntimeLang.LitUnit; ∃ return_value frame',
          RuntimeGhost.stack_frame_own stack_id frame' ∗
          ⌜frame'.(RuntimeLang.locals) !! "#ret_val" = Some return_value⌝ ∗
          q return_value }}}))%I in
  Hbody ∗ RuntimeGhost.stack_frame_own caller_id caller_frame ∗
    registered_procedure_chunk  (pack_typed_procedure callee) ∗ p ⊢
  @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG mask
    (RuntimeLang.RTCallNoStore
      (procedure_name (procedure_identity _ _ callee))
      arguments caller_id)
    (fun result => ⌜result = RuntimeLang.LitUnit⌝ ∗
      ∃ return_value,
        RuntimeGhost.stack_frame_own caller_id caller_frame ∗
        q return_value ∗ £ 1)%I.
Proof.
  cbn.
  pose proof (runtime_procedure_entry_coherent
    (pack_typed_procedure callee) Hin) as Hregistration.
  destruct Hregistration as [Hname Hargs Hlocals Hargs_nodup Hlocals_nodup
    Hdisjoint Hreturn_local Hregistered_body].
  assert (Hentry_length : length arguments =
      length (RuntimeLang.proc_args
        (runtime_procedure_entry  (pack_typed_procedure callee)))).
  { rewrite Hargs. rewrite RuntimeErasure.runtime_procedure_arguments_length.
    exact Hlength. }
  rewrite /registered_procedure_chunk.
  unfold RegionExecution.Primitives.Model.runtime_wp.
  iIntros "[#Hbody [Hcaller [Hchunk Hp]]]".
  iPoseProof (RuntimeLifting.wp_call_nostore
    caller_id caller_frame arguments values
    (procedure_name (procedure_identity _ _ callee))
    (runtime_procedure_entry  (pack_typed_procedure callee)) mask p q
    Hargs_nodup Hlocals_nodup Hdisjoint Hreturn_local Hentry_length Harguments
    with "Hbody") as "Hcall".
  iApply ("Hcall" with "[$Hcaller $Hchunk $Hp]").
  iNext. iIntros "Hresult".
  iSplit; first done.
  iExact "Hresult".
Qed.

(** Concrete execution boundary for a stored procedure result in the
    certificate-indexed runtime. *)
Lemma term_procedure_store_assembly
    {callee_variables callee_formals}
    (callee : typed_procedure callee_variables callee_formals)
    (caller_id : RuntimeLang.stack_id)
    (caller_frame : RuntimeLang.stack_frame)
    (arguments : list RuntimeLang.expr)
    (values : list RuntimeLang.val) (target : RuntimeLang.var) (mask : coPset)
    (p : iProp) (q : RuntimeLang.val -> iProp)
    (Hin : List.In (pack_typed_procedure callee)
      (procedure_entries Hoare.coherent_procedures))
    (Hlength : length arguments = length (Assertion.procedure_args callee_formals))
    (Harguments : Forall2 (fun expression value =>
      RuntimeLang.expr_step expression caller_frame (RuntimeLang.Val value))
      arguments values) :
  let Hbody := (▷ (∀ stack_id frame,
      ⌜Forall2 (fun variable value => frame.(RuntimeLang.locals) !! variable =
          Some value)
          (RuntimeLang.proc_args
            (runtime_procedure_entry  (pack_typed_procedure callee))).*1 values /\
        (forall variable type,
          (variable, type) ∈ RuntimeLang.proc_local_vars
            (runtime_procedure_entry  (pack_typed_procedure callee)) ->
          exists value, frame.(RuntimeLang.locals) !! variable = Some value /\
            RuntimeLang.val_has_typ value type) /\
        dom frame.(RuntimeLang.locals) =
          list_to_set (RuntimeLang.proc_args
            (runtime_procedure_entry  (pack_typed_procedure callee))).*1 ∪
          list_to_set (RuntimeLang.proc_local_vars
            (runtime_procedure_entry  (pack_typed_procedure callee))).*1⌝ -∗
      {{{ RuntimeGhost.stack_frame_own stack_id frame ∗ p }}}
        RuntimeLang.to_rtstmt stack_id
          (RuntimeLang.proc_stmt
            (runtime_procedure_entry  (pack_typed_procedure callee))) @ mask
      {{{ RET RuntimeLang.LitUnit; ∃ return_value frame',
          RuntimeGhost.stack_frame_own stack_id frame' ∗
          ⌜frame'.(RuntimeLang.locals) !! "#ret_val" = Some return_value⌝ ∗
          q return_value }}}))%I in
  Hbody ∗ RuntimeGhost.stack_frame_own caller_id caller_frame ∗
    registered_procedure_chunk  (pack_typed_procedure callee) ∗ p ⊢
  @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG mask
    (RuntimeLang.RTCall target
      (procedure_name (procedure_identity _ _ callee))
      arguments caller_id)
    (fun result => ⌜result = RuntimeLang.LitUnit⌝ ∗
      ∃ return_value,
        RuntimeGhost.stack_frame_own caller_id
          (RuntimeLang.StackFrame
            (<[target := return_value]> caller_frame.(RuntimeLang.locals))) ∗
        q return_value ∗ £ 1)%I.
Proof.
  cbn.
  pose proof (runtime_procedure_entry_coherent
    (pack_typed_procedure callee) Hin) as Hregistration.
  destruct Hregistration as [Hname Hargs Hlocals Hargs_nodup Hlocals_nodup
    Hdisjoint Hreturn_local Hregistered_body].
  assert (Hentry_length : length arguments =
      length (RuntimeLang.proc_args
        (runtime_procedure_entry  (pack_typed_procedure callee)))).
  { rewrite Hargs. rewrite RuntimeErasure.runtime_procedure_arguments_length.
    exact Hlength. }
  rewrite /registered_procedure_chunk.
  unfold RegionExecution.Primitives.Model.runtime_wp.
  iIntros "[#Hbody [Hcaller [Hchunk Hp]]]".
  iPoseProof (RuntimeLifting.wp_call
    caller_id caller_frame arguments values
    (procedure_name (procedure_identity _ _ callee)) target
    (runtime_procedure_entry  (pack_typed_procedure callee)) mask p q
    Hargs_nodup Hlocals_nodup Hdisjoint Hreturn_local Hentry_length Harguments
    with "Hbody") as "Hcall".
  iApply ("Hcall" with "[$Hcaller $Hchunk $Hp]").
  iNext. iIntros "Hresult".
  iSplit; first done.
  iExact "Hresult".
Qed.

(** Concrete execution boundary for a spawned procedure in the
    certificate-indexed runtime. *)
Lemma term_procedure_spawn_assembly
    {callee_variables callee_formals}
    (callee : typed_procedure callee_variables callee_formals)
    (caller_id : RuntimeLang.stack_id)
    (caller_frame : RuntimeLang.stack_frame)
    (arguments : list RuntimeLang.expr)
    (values : list RuntimeLang.val) (mask : coPset)
    (p : iProp)
    (Hin : List.In (pack_typed_procedure callee)
      (procedure_entries Hoare.coherent_procedures))
    (Hlength : length arguments = length (Assertion.procedure_args callee_formals))
    (Harguments : Forall2 (fun expression value =>
      RuntimeLang.expr_step expression caller_frame (RuntimeLang.Val value))
      arguments values) :
  let Hbody := (▷ (∀ stack_id frame,
      ⌜Forall2 (fun variable value => frame.(RuntimeLang.locals) !! variable =
          Some value)
          (RuntimeLang.proc_args
            (runtime_procedure_entry  (pack_typed_procedure callee))).*1 values /\
        (forall variable type,
          (variable, type) ∈ RuntimeLang.proc_local_vars
            (runtime_procedure_entry  (pack_typed_procedure callee)) ->
          exists value, frame.(RuntimeLang.locals) !! variable = Some value /\
            RuntimeLang.val_has_typ value type) /\
        dom frame.(RuntimeLang.locals) =
          list_to_set (RuntimeLang.proc_args
            (runtime_procedure_entry  (pack_typed_procedure callee))).*1 ∪
          list_to_set (RuntimeLang.proc_local_vars
            (runtime_procedure_entry  (pack_typed_procedure callee))).*1⌝ -∗
      {{{ RuntimeGhost.stack_frame_own stack_id frame ∗ p }}}
        RuntimeLang.to_rtstmt stack_id
          (RuntimeLang.proc_stmt
            (runtime_procedure_entry  (pack_typed_procedure callee))) @ ⊤
      {{{ RET RuntimeLang.LitUnit; True }}}))%I in
  Hbody ∗ RuntimeGhost.stack_frame_own caller_id caller_frame ∗
    registered_procedure_chunk  (pack_typed_procedure callee) ∗ p ⊢
  @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG mask
    (RuntimeLang.RTSpawn
      (procedure_name (procedure_identity _ _ callee))
      arguments caller_id)
    (fun result => ⌜result = RuntimeLang.LitUnit⌝ ∗
      RuntimeGhost.stack_frame_own caller_id caller_frame ∗ £ 1)%I.
Proof.
  cbn.
  pose proof (runtime_procedure_entry_coherent
    (pack_typed_procedure callee) Hin) as Hregistration.
  destruct Hregistration as [Hname Hargs Hlocals Hargs_nodup Hlocals_nodup
    Hdisjoint Hreturn_local Hregistered_body].
  assert (Hentry_length : length arguments =
      length (RuntimeLang.proc_args
        (runtime_procedure_entry  (pack_typed_procedure callee)))).
  { rewrite Hargs. rewrite RuntimeErasure.runtime_procedure_arguments_length.
    exact Hlength. }
  rewrite /registered_procedure_chunk.
  unfold RegionExecution.Primitives.Model.runtime_wp.
  iIntros "[#Hbody [Hcaller [Hchunk Hp]]]".
  iPoseProof (RuntimeLifting.wp_spawn
    caller_id caller_frame arguments values
    (procedure_name (procedure_identity _ _ callee))
    (runtime_procedure_entry  (pack_typed_procedure callee)) mask p
    Hargs_nodup Hlocals_nodup Hdisjoint Hreturn_local Hentry_length Harguments
    with "Hbody") as "Hspawn".
  iApply ("Hspawn" with "[$Hcaller $Hchunk $Hp]").
  iNext. iIntros "Hresult".
  iSplit; first done.
  iExact "Hresult".
Qed.

Theorem term_verified_procedure_bodies_guarded
    (program : term_semantic_program_certificates ) :
  all_registered_procedure_chunks  ∗ ▷ verified_procedure_specs  ⊢
    verified_procedure_specs .
Proof.
  unfold RuleValidity.verified_procedure_specs.
  iIntros "[#Hchunks #HIH]".
  iModIntro.
  iIntros (Γ F Δ pre post statement mask_pre mask_post entry exit
    runtime formals binders atoms ambient) "Hobligation Hmask #Hworld Hpre".
  iDestruct "Hmask" as %Hmask.
  iDestruct "Hobligation" as %Hobligation.
  destruct Hobligation.
  - rename H into Hpre_inst.
    rename H0 into Hpost_inst.
    rename H1 into Hrequired.
    iDestruct "Hpre" as "[Hstack Hcontract]".
    destruct (instantiated_pre_selects procedure
      (IR.symbolize_expr_list store arguments) contract_pre Hpre_inst)
      as [callee_variables [callee Hlookup]].
    (* [callee] is already at [procedure]: no identity transport, and no
       [subst] of the caller's identifier. *)
    have Hin : List.In (pack_typed_procedure callee)
      (procedure_entries Hoare.coherent_procedures).
    { apply lookup_typed_procedure_member with (identity := procedure).
      exact Hlookup. }
    have Hcallee_pre : contract_pre = Hoare.procedure_pre_instantiation callee
      (IR.symbolize_expr_list store arguments).
    { exact (instantiated_pre_coherent callee _ _ Hlookup Hpre_inst). }
    subst contract_pre.
    destruct (term_interpreted_expr_list_total formals binders atoms
      (IR.symbolize_expr_list store arguments)) as [values Hvalues].
    have Harguments : Forall2 (fun expression value =>
      RuntimeLang.expr_step expression
        (RuntimeLang.StackFrame
          (@RegionExecution.Primitives.Model.concrete_locals _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (interp_store formals binders atoms store)))
        (RuntimeLang.Val value))
      (@RuntimeErasure.runtime_expr_list _ Γ (Assertion.procedure_args procedure)
        (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments)
      (@RegionExecution.Primitives.Model.tval_list_to_list _ (Assertion.procedure_args procedure) values).
    { eapply (@RegionExecution.Primitives.Model.runtime_expr_list_sound _ Γ F Δ (Assertion.procedure_args procedure)
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        formals binders atoms store
        (RuntimeLang.StackFrame
          (@RegionExecution.Primitives.Model.concrete_locals _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (interp_store formals binders atoms store))) arguments values).
      - apply RegionExecution.Primitives.Model.runtime_stack_frame_corresponds.
      - exact Hvalues. }
    have Hlength : length (@RuntimeErasure.runtime_expr_list _ Γ (Assertion.procedure_args procedure)
      (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments) = length (Assertion.procedure_args procedure).
    { apply RuntimeErasure.runtime_expr_list_length. }
    unfold RegionExecution.Primitives.operation_wp,
      RegionExecution.Primitives.ambient_leaf_wp,
      RegionExecution.Primitives.ambient_physical_leaf_wp.
    simpl.
    iApply (wp_mono with "[-]").
    2: iApply (term_procedure_discard_assembly callee
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      (RuntimeLang.StackFrame (@RegionExecution.Primitives.Model.concrete_locals _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (interp_store formals binders atoms store)))
      (@RuntimeErasure.runtime_expr_list _ Γ (Assertion.procedure_args procedure) (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments)
      (@RegionExecution.Primitives.Model.tval_list_to_list _ (Assertion.procedure_args procedure) values)
      (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
      (term_interp_core formals binders atoms
        (Hoare.procedure_pre_instantiation callee
          (IR.symbolize_expr_list store arguments)))
      (fun raw => (∃ return_value : tval (Assertion.procedure_return procedure),
        ⌜raw = @RuntimeErasure.tval_to_val _ (Assertion.procedure_return procedure) return_value⌝ ∗
        term_interp_core formals (binder_cons return_value binders) atoms
          contract_post)%I)
      Hin Hlength Harguments).
    + iIntros (result) "[%Hunit Hpost]".
      iDestruct "Hpost" as (raw) "[Hcaller [Hq Hcredit]]".
      iDestruct "Hq" as (return_value) "[%Hraw Hpost]".
      subst raw.
      iClear "Hcredit".
      iSplit; first done.
      iExists return_value.
      iSplitL "Hcaller".
      { iEval (unfold RegionExecution.Primitives.Model.core_stack_own) in "Hcaller".
        rewrite interp_weaken_store.
        iExact "Hcaller". }
      iExact "Hpost".
    + iPoseProof (all_registered_procedure_chunks_lookup
        (pack_typed_procedure callee) Hin with "Hchunks") as "#Hchunk".
      iFrame "Hstack Hchunk Hcontract".
      iNext.
      iIntros (stack_id frame) "%Hframe".
      unfold RegionExecution.Primitives.Model.runtime_wp.
      iModIntro.
      iIntros (Φ) "Hpre HΦ".
      pose proof (term_runtime_procedure_layout_configured
        (pack_typed_procedure callee) Hin) as Hlayout.
      simpl in Hlayout.
      destruct Hlayout as [Hcallee_wf [Hcallee_fresh Hregistered]].
      have Hnames : NoDup (@RuntimeErasure.runtime_variables callee_variables
        (@RuntimeErasure.runtime_procedure_names _ _ callee_variables procedure callee)).
      { apply RuntimeErasure.runtime_procedure_names_nodup; assumption. }
      destruct Hframe as [Hframe_arguments [Hframe_locals Hframe_dom]].
      unfold RuleValidity.runtime_procedure_entry, registered_runtime_procedure_entry in
        Hframe_arguments, Hframe_locals, Hframe_dom.
      simpl in Hframe_arguments, Hframe_locals, Hframe_dom.
      destruct (@RegionExecution.Primitives.Model.procedure_entry_frame_corresponds _ _
        callee_variables procedure atoms callee values frame Hcallee_wf
        Hframe_arguments Hframe_locals Hframe_dom)
        as (callee_atoms & Hagree & Hcorresponds & Hdom).
      have Hframe_eq := @RegionExecution.Primitives.Model.stack_corresponds_canonical_frame_eq _ callee_variables (Assertion.procedure_args procedure) []
        (@RuntimeErasure.runtime_procedure_names _ _ callee_variables procedure callee)
        (formal_env_of_values values) empty_binder_env callee_atoms
        (procedure_entry_store _ _ callee) frame Hnames Hcorresponds Hdom.
      subst frame.
      set (callee_runtime := @RegionExecution.Primitives.make_stack_context
        callee_variables stack_id
        (@RuntimeErasure.runtime_procedure_names _ _
          callee_variables procedure callee) Hnames).
      iDestruct "Hpre" as "[Hcallee_frame Hcallee_contract]".
      iPoseProof (bi.equiv_entails_1_1 _ _
        (procedure_pre_instantiation_interp callee
          (IR.symbolize_expr_list store arguments)
          formals binders atoms values Hvalues)
        with "Hcallee_contract") as "Hcallee_contract".
      iPoseProof (bi.equiv_entails_1_1 _ _
        (term_interp_core_stable_atoms (formal_env_of_values values)
          empty_binder_env atoms callee_atoms
          (procedure_precondition _ _ callee) Hagree
          (procedure_precondition_entry_free _ Hcallee_wf))
        with "Hcallee_contract") as "Hcallee_contract".
      set (body := term_semantic_procedure_bodies program
        callee_variables procedure callee Hin).
      have Hexit_envelope : RegionExecution.Primitives.Model.runtime_mask
        (GenericRegions.Atomicity.analysis_mask
          (term_semantic_body_exit _ body)) ⊆
        RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
      { rewrite term_semantic_body_exit_mask.
        etrans; last exact Hmask.
        apply RegionExecution.Primitives.Model.runtime_mask_mono.
        intros invariant Hmember. rewrite !elem_of_union in Hmember |- *.
        destruct Hmember as [Hrequired_member | Hgranted];
          [left; exact (Hrequired _ Hrequired_member) | right; exact Hgranted]. }
      have Hentry_active : RegionExecution.Primitives.Model.active_runtime_mask
        (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
        (term_semantic_body_entry _ body) =
        RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
      { apply RegionExecution.Primitives.Model.active_runtime_mask_closed.
        exact (term_semantic_body_entry_closed _ body). }
      have Hexit_active : RegionExecution.Primitives.Model.active_runtime_mask
        (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
        (term_semantic_body_exit _ body) =
        RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
      { apply RegionExecution.Primitives.Model.active_runtime_mask_closed.
        exact (term_semantic_body_exit_closed _ body). }
      iAssert (global_world_context atoms) with "[Hworld Hchunks HIH]"
        as "#Hglobal".
      { rewrite /global_world_context.
        iFrame "Hworld Hchunks HIH". }
      iPoseProof (bi.equiv_entails_1_1 _ _
        (global_world_context_stable_atoms atoms callee_atoms Hagree)
        with "Hglobal") as "#Hcallee_global".
      iPoseProof (@term_semantic_body_source_valid callee_variables procedure
        callee body
        callee_runtime (formal_env_of_values values) callee_atoms
        (RegionExecution.Primitives.Model.active_runtime_mask ambient entry) Hexit_envelope) as "Hsource".
      iEval (unfold RuleValidity.translated_runtime_wp; rewrite Hregistered;
        rewrite Hentry_active Hexit_active) in "Hsource".
      iAssert (@RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
        (RuntimeLang.to_rtstmt stack_id
          (term_runtime_procedure_statement  (pack_typed_procedure callee)))
        (fun result =>
          (⌜result = RuntimeLang.LitUnit⌝ ∗
           |={RegionExecution.Primitives.Model.active_runtime_mask ambient entry}=>
             global_world_context callee_atoms ∗
             term_interp_resource_prenex
               callee_runtime (formal_env_of_values values) empty_binder_env
               callee_atoms (Hoare.procedure_body_post callee
                 (term_semantic_body_exit_store _ body)
                 (term_semantic_body_return_reference _ body)))%I))
        with "[Hsource Hcallee_global Hcallee_frame Hcallee_contract]" as "Hwp".
      { iApply ("Hsource" with
          "[$Hcallee_global $Hcallee_frame $Hcallee_contract]"). }
      have Hnotvalue : to_val
        ((RuntimeLang.to_rtstmt stack_id
          (term_runtime_procedure_statement  (pack_typed_procedure callee)) :
            language.expr RuntimeLang.simp_lang)) = None.
      { apply registered_runtime_procedure_nonvalue; exact Hin. }
      iAssert (@RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
        (RuntimeLang.to_rtstmt stack_id
          (RuntimeLang.proc_stmt
            (runtime_procedure_entry  (pack_typed_procedure callee)))) Φ)
        with "[Hwp HΦ]" as "Htarget".
      { iEval (unfold RegionExecution.Primitives.Model.runtime_wp) in "Hwp".
        iApply (wp_step_fupd _ _ (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
          _ _ with "[HΦ]").
        - rewrite Hnotvalue. constructor.
        - set_solver.
        - iApply (step_fupd_intro with "HΦ").
          set_solver.
        - iApply (wp_wand with "Hwp").
          iIntros (result) "[%Hunit Hout]".
          subst result.
          iIntros "HP".
          iMod "Hout" as "[_ Hbodypost]".
          iModIntro.
          iApply "HP".
          iPoseProof (bi.equiv_entails_1_1 _ _
            (procedure_body_post_interp callee
              (term_semantic_body_exit_store _ body)
              (term_semantic_body_return_reference _ body)
              callee_runtime (formal_env_of_values values) callee_atoms)
            with "[Hbodypost]") as (exit_values)
              "[Hexit_frame Hcallee_post]".
          { iExact "Hbodypost". }
          set (return_value := interp_ref (formal_env_of_values values)
            (formal_env_of_values exit_values) callee_atoms
            (term_semantic_body_return_reference _ body)).
          have Hreturn_lookup :
            @RegionExecution.Primitives.Model.concrete_locals _ callee_variables
              (@RuntimeErasure.runtime_procedure_names _ _
                callee_variables procedure callee)
              (interp_store (formal_env_of_values values)
                (formal_env_of_values exit_values) callee_atoms
                (term_semantic_body_exit_store _ body)) !! "#ret_val" =
            Some (@RuntimeErasure.tval_to_val _ _ return_value).
          { rewrite (@RegionExecution.Primitives.Model.concrete_procedure_return_lookup _ _
              callee_variables procedure _ callee (formal_env_of_values values)
              (formal_env_of_values exit_values) callee_atoms
              (term_semantic_body_exit_store _ body) Hnames).
            rewrite (term_semantic_body_exit_return _ body).
            reflexivity. }
          have Hvalues_weakened : interp_expr_list formals
            (binder_cons return_value binders) atoms
            (weaken_expr_list (IR.symbolize_expr_list store arguments)) =
            Some values.
          { rewrite interp_weaken_expr_list. exact Hvalues. }
          iPoseProof (bi.equiv_entails_1_2 _ _
            (term_interp_core_stable_atoms (formal_env_of_values values)
              (binder_cons return_value empty_binder_env) atoms callee_atoms
              (procedure_postcondition _ _ callee) Hagree
              (procedure_postcondition_entry_free _ Hcallee_wf))
            with "Hcallee_post") as "Hcallee_post".
          (* No [Hreturn] transport and no [UIP_refl]: the caller's result
             binder already has the declared return type. *)
          have Hpost_equiv := procedure_post_instantiation_interp callee
            (weaken_expr_list (IR.symbolize_expr_list store arguments))
            (ERef (RefBound MHere)) contract_post Hlookup Hpost_inst
            formals binders atoms values return_value
            Hvalues_weakened.
          iPoseProof (bi.equiv_entails_1_2 _ _ Hpost_equiv
            with "Hcallee_post") as "Hcaller_post".
          iExists (@RuntimeErasure.tval_to_val _ _ return_value),
            (RuntimeLang.StackFrame
         (@RegionExecution.Primitives.Model.concrete_locals _ callee_variables
           (@RuntimeErasure.runtime_procedure_names _ _
             callee_variables procedure callee)
                (interp_store (formal_env_of_values values)
                  (formal_env_of_values exit_values) callee_atoms
                  (term_semantic_body_exit_store _ body)))).
          iSplitL "Hexit_frame".
          { iEval (unfold RegionExecution.Primitives.Model.core_stack_own) in "Hexit_frame".
            iExact "Hexit_frame". }
          iSplit.
          { iPureIntro. exact Hreturn_lookup. }
          iExists return_value.
          iSplit; first done.
          iExact "Hcaller_post".
      }
      iExact "Htarget".
  - rename H into Hpre_inst.
    rename H0 into Hpost_inst.
    rename H1 into Hrequired.
    iDestruct "Hpre" as "[Hstack Hcontract]".
    destruct (instantiated_pre_selects procedure
      (IR.symbolize_expr_list store arguments) contract_pre Hpre_inst)
      as [callee_variables [callee Hlookup]].
    (* [callee] is already at [procedure]: no identity transport, and no
       [subst] of the caller's identifier. *)
    have Hin : List.In (pack_typed_procedure callee)
      (procedure_entries Hoare.coherent_procedures).
    { apply lookup_typed_procedure_member with (identity := procedure).
      exact Hlookup. }
    have Hcallee_pre : contract_pre = Hoare.procedure_pre_instantiation callee
      (IR.symbolize_expr_list store arguments).
    { exact (instantiated_pre_coherent callee _ _ Hlookup Hpre_inst). }
    subst contract_pre.
    destruct (term_interpreted_expr_list_total formals binders atoms
      (IR.symbolize_expr_list store arguments)) as [values Hvalues].
    have Harguments : Forall2 (fun expression value =>
      RuntimeLang.expr_step expression
        (RuntimeLang.StackFrame (@RegionExecution.Primitives.Model.concrete_locals _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (interp_store formals binders atoms store)))
        (RuntimeLang.Val value))
      (@RuntimeErasure.runtime_expr_list _ Γ (Assertion.procedure_args procedure) (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments)
      (@RegionExecution.Primitives.Model.tval_list_to_list _ (Assertion.procedure_args procedure) values).
    { eapply (@RegionExecution.Primitives.Model.runtime_expr_list_sound _ Γ F Δ (Assertion.procedure_args procedure) (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        formals binders atoms store
        (RuntimeLang.StackFrame (@RegionExecution.Primitives.Model.concrete_locals _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (interp_store formals binders atoms store))) arguments values).
      - apply RegionExecution.Primitives.Model.runtime_stack_frame_corresponds.
      - exact Hvalues. }
    have Hlength : length (@RuntimeErasure.runtime_expr_list _ Γ (Assertion.procedure_args procedure)
      (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments) = length (Assertion.procedure_args procedure).
    { apply RuntimeErasure.runtime_expr_list_length. }
    unfold RegionExecution.Primitives.operation_wp,
      RegionExecution.Primitives.ambient_leaf_wp,
      RegionExecution.Primitives.ambient_physical_leaf_wp.
    simpl.
    iApply (wp_mono with "[-]").
    2: iApply (term_procedure_store_assembly callee
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      (RuntimeLang.StackFrame (@RegionExecution.Primitives.Model.concrete_locals _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (interp_store formals binders atoms store)))
      (@RuntimeErasure.runtime_expr_list _ Γ (Assertion.procedure_args procedure) (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments)
      (@RegionExecution.Primitives.Model.tval_list_to_list _ (Assertion.procedure_args procedure) values)
      (@RuntimeErasure.runtime_variable Γ (Assertion.procedure_return procedure)
        (RegionExecution.Primitives.Model.runtime_names Γ runtime) target)
      (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
      (term_interp_core formals binders atoms
        (Hoare.procedure_pre_instantiation callee
          (IR.symbolize_expr_list store arguments)))
      (fun raw => (∃ return_value : tval (Assertion.procedure_return procedure),
        ⌜raw = @RuntimeErasure.tval_to_val _ (Assertion.procedure_return procedure) return_value⌝ ∗
        term_interp_core formals (binder_cons return_value binders) atoms
          contract_post)%I)
      Hin Hlength Harguments).
    + iIntros (result) "[%Hunit Hpost]".
      iDestruct "Hpost" as (raw) "[Hcaller [Hq Hcredit]]".
      iDestruct "Hq" as (return_value) "[%Hraw Hpost]".
      subst raw.
      iClear "Hcredit".
      iSplit; first done.
      iExists return_value.
      iSplitL "Hcaller".
      { iEval (unfold RegionExecution.Primitives.Model.core_stack_own) in "Hcaller".
        iApply (bi.equiv_entails_1_2 _ _
          (term_stack_own_update runtime formals binders atoms store target
            return_value)).
        iExact "Hcaller". }
      iExact "Hpost".
    + iPoseProof (all_registered_procedure_chunks_lookup
        (pack_typed_procedure callee) Hin with "Hchunks") as "#Hchunk".
      iFrame "Hstack Hchunk Hcontract".
      iNext.
      iIntros (stack_id frame) "%Hframe".
      unfold RegionExecution.Primitives.Model.runtime_wp.
      iModIntro.
      iIntros (Φ) "Hpre HΦ".
      pose proof (term_runtime_procedure_layout_configured
        (pack_typed_procedure callee) Hin) as Hlayout.
      simpl in Hlayout.
      destruct Hlayout as [Hcallee_wf [Hcallee_fresh Hregistered]].
      have Hnames : NoDup (@RuntimeErasure.runtime_variables callee_variables
        (@RuntimeErasure.runtime_procedure_names _ _ callee_variables procedure callee)).
      { apply RuntimeErasure.runtime_procedure_names_nodup; assumption. }
      destruct Hframe as [Hframe_arguments [Hframe_locals Hframe_dom]].
      unfold RuleValidity.runtime_procedure_entry, registered_runtime_procedure_entry in
        Hframe_arguments, Hframe_locals, Hframe_dom.
      simpl in Hframe_arguments, Hframe_locals, Hframe_dom.
      destruct (@RegionExecution.Primitives.Model.procedure_entry_frame_corresponds _ _
        callee_variables procedure atoms callee values frame Hcallee_wf
        Hframe_arguments Hframe_locals Hframe_dom)
        as (callee_atoms & Hagree & Hcorresponds & Hdom).
      have Hframe_eq := @RegionExecution.Primitives.Model.stack_corresponds_canonical_frame_eq _ callee_variables (Assertion.procedure_args procedure) []
        (@RuntimeErasure.runtime_procedure_names _ _ callee_variables procedure callee)
        (formal_env_of_values values) empty_binder_env callee_atoms
        (procedure_entry_store _ _ callee) frame Hnames Hcorresponds Hdom.
      subst frame.
      set (callee_runtime := @RegionExecution.Primitives.make_stack_context
        callee_variables stack_id
        (@RuntimeErasure.runtime_procedure_names _ _
          callee_variables procedure callee) Hnames).
      iDestruct "Hpre" as "[Hcallee_frame Hcallee_contract]".
      iPoseProof (bi.equiv_entails_1_1 _ _
        (procedure_pre_instantiation_interp callee
          (IR.symbolize_expr_list store arguments)
          formals binders atoms values Hvalues)
        with "Hcallee_contract") as "Hcallee_contract".
      iPoseProof (bi.equiv_entails_1_1 _ _
        (term_interp_core_stable_atoms (formal_env_of_values values)
          empty_binder_env atoms callee_atoms
          (procedure_precondition _ _ callee) Hagree
          (procedure_precondition_entry_free _ Hcallee_wf))
        with "Hcallee_contract") as "Hcallee_contract".
      set (body := term_semantic_procedure_bodies program
        callee_variables procedure callee Hin).
      have Hexit_envelope : RegionExecution.Primitives.Model.runtime_mask
        (GenericRegions.Atomicity.analysis_mask
          (term_semantic_body_exit _ body)) ⊆
        RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
      { rewrite term_semantic_body_exit_mask.
        etrans; last exact Hmask.
        apply RegionExecution.Primitives.Model.runtime_mask_mono.
        intros invariant Hmember. rewrite !elem_of_union in Hmember |- *.
        destruct Hmember as [Hrequired_member | Hgranted];
          [left; exact (Hrequired _ Hrequired_member) | right; exact Hgranted]. }
      have Hentry_active : RegionExecution.Primitives.Model.active_runtime_mask
        (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
        (term_semantic_body_entry _ body) =
        RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
      { apply RegionExecution.Primitives.Model.active_runtime_mask_closed.
        exact (term_semantic_body_entry_closed _ body). }
      have Hexit_active : RegionExecution.Primitives.Model.active_runtime_mask
        (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
        (term_semantic_body_exit _ body) =
        RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
      { apply RegionExecution.Primitives.Model.active_runtime_mask_closed.
        exact (term_semantic_body_exit_closed _ body). }
      iAssert (global_world_context atoms) with "[Hworld Hchunks HIH]"
        as "#Hglobal".
      { rewrite /global_world_context.
        iFrame "Hworld Hchunks HIH". }
      iPoseProof (bi.equiv_entails_1_1 _ _
        (global_world_context_stable_atoms atoms callee_atoms Hagree)
        with "Hglobal") as "#Hcallee_global".
      iPoseProof (@term_semantic_body_source_valid callee_variables procedure
        callee body
        callee_runtime (formal_env_of_values values) callee_atoms
        (RegionExecution.Primitives.Model.active_runtime_mask ambient entry) Hexit_envelope) as "Hsource".
      iEval (unfold RuleValidity.translated_runtime_wp; rewrite Hregistered;
        rewrite Hentry_active Hexit_active) in "Hsource".
      iAssert (@RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
        (RuntimeLang.to_rtstmt stack_id
          (term_runtime_procedure_statement  (pack_typed_procedure callee)))
        (fun result =>
          (⌜result = RuntimeLang.LitUnit⌝ ∗
           |={RegionExecution.Primitives.Model.active_runtime_mask ambient entry}=>
             global_world_context callee_atoms ∗
             term_interp_resource_prenex
               callee_runtime (formal_env_of_values values) empty_binder_env
               callee_atoms (Hoare.procedure_body_post callee
                 (term_semantic_body_exit_store _ body)
                 (term_semantic_body_return_reference _ body)))%I))
        with "[Hsource Hcallee_global Hcallee_frame Hcallee_contract]" as "Hwp".
      { iApply ("Hsource" with
          "[$Hcallee_global $Hcallee_frame $Hcallee_contract]"). }
      have Hnotvalue : to_val
        ((RuntimeLang.to_rtstmt stack_id
          (term_runtime_procedure_statement  (pack_typed_procedure callee)) :
            language.expr RuntimeLang.simp_lang)) = None.
      { apply registered_runtime_procedure_nonvalue; exact Hin. }
      iAssert (@RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
        (RuntimeLang.to_rtstmt stack_id
          (RuntimeLang.proc_stmt
            (runtime_procedure_entry  (pack_typed_procedure callee)))) Φ)
        with "[Hwp HΦ]" as "Htarget".
      { iEval (unfold RegionExecution.Primitives.Model.runtime_wp) in "Hwp".
        iApply (wp_step_fupd _ _ (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
          _ _ with "[HΦ]").
        - rewrite Hnotvalue. constructor.
        - set_solver.
        - iApply (step_fupd_intro with "HΦ").
          set_solver.
        - iApply (wp_wand with "Hwp").
          iIntros (result) "[%Hunit Hout]".
          subst result.
          iIntros "HP".
          iMod "Hout" as "[_ Hbodypost]".
          iModIntro.
          iApply "HP".
          iPoseProof (bi.equiv_entails_1_1 _ _
            (procedure_body_post_interp callee
              (term_semantic_body_exit_store _ body)
              (term_semantic_body_return_reference _ body)
              callee_runtime (formal_env_of_values values) callee_atoms)
            with "[Hbodypost]") as (exit_values)
              "[Hexit_frame Hcallee_post]".
          { iExact "Hbodypost". }
          set (return_value := interp_ref (formal_env_of_values values)
            (formal_env_of_values exit_values) callee_atoms
            (term_semantic_body_return_reference _ body)).
          have Hreturn_lookup :
            @RegionExecution.Primitives.Model.concrete_locals _ callee_variables
              (@RuntimeErasure.runtime_procedure_names _ _
                callee_variables procedure callee)
              (interp_store (formal_env_of_values values)
                (formal_env_of_values exit_values) callee_atoms
                (term_semantic_body_exit_store _ body)) !! "#ret_val" =
            Some (@RuntimeErasure.tval_to_val _ _ return_value).
          { rewrite (@RegionExecution.Primitives.Model.concrete_procedure_return_lookup _ _
              callee_variables procedure _ callee (formal_env_of_values values)
                    (formal_env_of_values exit_values) callee_atoms
              (term_semantic_body_exit_store _ body) Hnames).
            rewrite (term_semantic_body_exit_return _ body).
            reflexivity. }
          have Hvalues_weakened : interp_expr_list formals
            (binder_cons return_value binders) atoms
            (weaken_expr_list (IR.symbolize_expr_list store arguments))
            = Some values.
          { rewrite interp_weaken_expr_list. exact Hvalues. }
          iPoseProof (bi.equiv_entails_1_2 _ _
            (term_interp_core_stable_atoms (formal_env_of_values values)
              (binder_cons return_value empty_binder_env) atoms callee_atoms
              (procedure_postcondition _ _ callee) Hagree
              (procedure_postcondition_entry_free _ Hcallee_wf))
            with "Hcallee_post") as "Hcallee_post".
          (* No [Hreturn] transport and no [UIP_refl]: the caller's result
             binder already has the declared return type. *)
          have Hpost_equiv := procedure_post_instantiation_interp callee
            (weaken_expr_list (IR.symbolize_expr_list store arguments))
            (ERef (RefBound MHere)) contract_post Hlookup Hpost_inst
            formals binders atoms values return_value
            Hvalues_weakened.
          iPoseProof (bi.equiv_entails_1_2 _ _ Hpost_equiv
            with "Hcallee_post") as "Hcaller_post".
          iExists (@RuntimeErasure.tval_to_val _ _ return_value),
            (RuntimeLang.StackFrame
              (@RegionExecution.Primitives.Model.concrete_locals _ callee_variables
              (@RuntimeErasure.runtime_procedure_names _ _
                callee_variables procedure callee)
                (interp_store (formal_env_of_values values)
                  (formal_env_of_values exit_values) callee_atoms
                  (term_semantic_body_exit_store _ body)))).
          iSplitL "Hexit_frame".
          { iEval (unfold RegionExecution.Primitives.Model.core_stack_own) in "Hexit_frame".
            iExact "Hexit_frame". }
          iSplit.
          { iPureIntro. exact Hreturn_lookup. }
          iExists return_value.
          iSplit; first done.
          iExact "Hcaller_post".
      }
      iExact "Htarget".
  - rename H into Hpre_inst.
    rename H0 into Hrequired.
    iDestruct "Hpre" as "[Hstack Hcontract]".
    destruct (instantiated_pre_selects procedure
      (IR.symbolize_expr_list store arguments) contract_pre Hpre_inst)
      as [callee_variables [callee Hlookup]].
    (* [callee] is already at [procedure]: no identity transport, and no
       [subst] of the caller's identifier. *)
    have Hin : List.In (pack_typed_procedure callee)
      (procedure_entries Hoare.coherent_procedures).
    { apply lookup_typed_procedure_member with (identity := procedure).
      exact Hlookup. }
    have Hcallee_pre : contract_pre = Hoare.procedure_pre_instantiation callee
      (IR.symbolize_expr_list store arguments).
    { exact (instantiated_pre_coherent callee _ _ Hlookup Hpre_inst). }
    subst contract_pre.
    destruct (term_interpreted_expr_list_total formals binders atoms
      (IR.symbolize_expr_list store arguments)) as [values Hvalues].
    have Harguments : Forall2 (fun expression value =>
      RuntimeLang.expr_step expression
        (RuntimeLang.StackFrame (@RegionExecution.Primitives.Model.concrete_locals _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (interp_store formals binders atoms store)))
        (RuntimeLang.Val value))
      (@RuntimeErasure.runtime_expr_list _ Γ (Assertion.procedure_args procedure) (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments)
      (@RegionExecution.Primitives.Model.tval_list_to_list _ (Assertion.procedure_args procedure) values).
    { eapply (@RegionExecution.Primitives.Model.runtime_expr_list_sound _ Γ F Δ (Assertion.procedure_args procedure) (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        formals binders atoms store
        (RuntimeLang.StackFrame (@RegionExecution.Primitives.Model.concrete_locals _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (interp_store formals binders atoms store))) arguments values).
      - apply RegionExecution.Primitives.Model.runtime_stack_frame_corresponds.
      - exact Hvalues. }
    have Hlength : length (@RuntimeErasure.runtime_expr_list _ Γ (Assertion.procedure_args procedure)
      (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments) = length (Assertion.procedure_args procedure).
    { apply RuntimeErasure.runtime_expr_list_length. }
    unfold RegionExecution.Primitives.operation_wp,
      RegionExecution.Primitives.ambient_leaf_wp,
      RegionExecution.Primitives.ambient_physical_leaf_wp.
    simpl.
    iApply (wp_mono with "[-]").
    2: iApply (term_procedure_spawn_assembly callee
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      (RuntimeLang.StackFrame (@RegionExecution.Primitives.Model.concrete_locals _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (interp_store formals binders atoms store)))
      (@RuntimeErasure.runtime_expr_list _ Γ (Assertion.procedure_args procedure) (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments)
      (@RegionExecution.Primitives.Model.tval_list_to_list _ (Assertion.procedure_args procedure) values)
      (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
      (term_interp_core formals binders atoms
        (Hoare.procedure_pre_instantiation callee
          (IR.symbolize_expr_list store arguments)))
      Hin Hlength Harguments).
    + iIntros (result) "[%Hunit [Hcaller Hcredit]]".
      iClear "Hcredit".
      iSplit; first done.
      iEval (unfold RegionExecution.Primitives.Model.core_stack_own) in "Hcaller".
      iFrame "Hcaller".
    + iPoseProof (all_registered_procedure_chunks_lookup
        (pack_typed_procedure callee) Hin with "Hchunks") as "#Hchunk".
      iFrame "Hstack Hchunk Hcontract".
      iNext.
      iIntros (stack_id frame) "%Hframe".
      unfold RegionExecution.Primitives.Model.runtime_wp.
      iModIntro.
      iIntros (Φ) "Hpre HΦ".
      pose proof (term_runtime_procedure_layout_configured
        (pack_typed_procedure callee) Hin) as Hlayout.
      simpl in Hlayout.
      destruct Hlayout as [Hcallee_wf [Hcallee_fresh Hregistered]].
      have Hnames : NoDup (@RuntimeErasure.runtime_variables callee_variables
        (@RuntimeErasure.runtime_procedure_names _ _ callee_variables procedure callee)).
      { apply RuntimeErasure.runtime_procedure_names_nodup; assumption. }
      destruct Hframe as [Hframe_arguments [Hframe_locals Hframe_dom]].
      unfold RuleValidity.runtime_procedure_entry, registered_runtime_procedure_entry in
        Hframe_arguments, Hframe_locals, Hframe_dom.
      simpl in Hframe_arguments, Hframe_locals, Hframe_dom.
      destruct (@RegionExecution.Primitives.Model.procedure_entry_frame_corresponds _ _
        callee_variables procedure atoms callee values frame Hcallee_wf
        Hframe_arguments Hframe_locals Hframe_dom)
        as (callee_atoms & Hagree & Hcorresponds & Hdom).
      have Hframe_eq := @RegionExecution.Primitives.Model.stack_corresponds_canonical_frame_eq _ callee_variables (Assertion.procedure_args procedure) []
        (@RuntimeErasure.runtime_procedure_names _ _ callee_variables procedure callee)
        (formal_env_of_values values) empty_binder_env callee_atoms
        (procedure_entry_store _ _ callee) frame Hnames Hcorresponds Hdom.
      subst frame.
      set (callee_runtime := @RegionExecution.Primitives.make_stack_context
        callee_variables stack_id
        (@RuntimeErasure.runtime_procedure_names _ _
          callee_variables procedure callee) Hnames).
      iDestruct "Hpre" as "[Hcallee_frame Hcallee_contract]".
      iPoseProof (bi.equiv_entails_1_1 _ _
        (procedure_pre_instantiation_interp callee
          (IR.symbolize_expr_list store arguments)
          formals binders atoms values Hvalues)
        with "Hcallee_contract") as "Hcallee_contract".
      iPoseProof (bi.equiv_entails_1_1 _ _
        (term_interp_core_stable_atoms (formal_env_of_values values)
          empty_binder_env atoms callee_atoms
          (procedure_precondition _ _ callee) Hagree
          (procedure_precondition_entry_free _ Hcallee_wf))
        with "Hcallee_contract") as "Hcallee_contract".
      set (body := term_semantic_procedure_bodies program
        callee_variables procedure callee Hin).
      have Hexit_envelope : RegionExecution.Primitives.Model.runtime_mask
        (GenericRegions.Atomicity.analysis_mask
          (term_semantic_body_exit _ body)) ⊆ (⊤ : coPset).
      { set_solver. }
      have Hentry_active : RegionExecution.Primitives.Model.active_runtime_mask (⊤ : coPset)
        (term_semantic_body_entry _ body) = (⊤ : coPset).
      { apply RegionExecution.Primitives.Model.active_runtime_mask_closed.
        exact (term_semantic_body_entry_closed _ body). }
      have Hexit_active : RegionExecution.Primitives.Model.active_runtime_mask (⊤ : coPset)
        (term_semantic_body_exit _ body) = (⊤ : coPset).
      { apply RegionExecution.Primitives.Model.active_runtime_mask_closed.
        exact (term_semantic_body_exit_closed _ body). }
      iAssert (global_world_context atoms) with "[Hworld Hchunks HIH]"
        as "#Hglobal".
      { rewrite /global_world_context.
        iFrame "Hworld Hchunks HIH". }
      iPoseProof (bi.equiv_entails_1_1 _ _
        (global_world_context_stable_atoms atoms callee_atoms Hagree)
        with "Hglobal") as "#Hcallee_global".
      iPoseProof (@term_semantic_body_source_valid callee_variables procedure
        callee body
        callee_runtime (formal_env_of_values values) callee_atoms
        (⊤ : coPset) Hexit_envelope) as "Hsource".
      iEval (unfold RuleValidity.translated_runtime_wp; rewrite Hregistered;
        rewrite Hentry_active Hexit_active) in "Hsource".
      iAssert (@RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG (⊤ : coPset)
        (RuntimeLang.to_rtstmt stack_id
          (term_runtime_procedure_statement  (pack_typed_procedure callee)))
        (fun result =>
          (⌜result = RuntimeLang.LitUnit⌝ ∗
           |={⊤}=> global_world_context callee_atoms ∗
             term_interp_resource_prenex
               callee_runtime (formal_env_of_values values) empty_binder_env
               callee_atoms (Hoare.procedure_body_post callee
                 (term_semantic_body_exit_store _ body)
                 (term_semantic_body_return_reference _ body)))%I))
        with "[Hsource Hcallee_global Hcallee_frame Hcallee_contract]" as "Hwp".
      { iApply ("Hsource" with
          "[$Hcallee_global $Hcallee_frame $Hcallee_contract]"). }
      have Hnotvalue : to_val
        ((RuntimeLang.to_rtstmt stack_id
          (term_runtime_procedure_statement  (pack_typed_procedure callee)) :
            language.expr RuntimeLang.simp_lang)) = None.
      { apply registered_runtime_procedure_nonvalue; exact Hin. }
      iAssert (@RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG (⊤ : coPset)
        (RuntimeLang.to_rtstmt stack_id
          (RuntimeLang.proc_stmt
            (runtime_procedure_entry  (pack_typed_procedure callee)))) Φ)
        with "[Hwp HΦ]" as "Htarget".
      { iEval (unfold RegionExecution.Primitives.Model.runtime_wp) in "Hwp".
        iApply (wp_step_fupd _ _ (⊤ : coPset) _ _ with "[HΦ]").
        - rewrite Hnotvalue. constructor.
        - set_solver.
        - iApply (step_fupd_intro with "HΦ").
          set_solver.
        - iApply (wp_wand with "Hwp").
          iIntros (result) "[%Hunit Hout]".
          subst result.
          iIntros "HP".
          iMod "Hout" as "[Hglobal' Hbodypost']".
          iModIntro.
          iApply "HP".
          done.
      }
      iExact "Htarget".
Qed.

(** Public procedure-level soundness theorem.  Its only explicit input is the
    program's finite family of normalization proofs and certificates; the
    recursive specification environment is constructed and closed here. *)

(** Close the recursive procedure specification environment from the finite
    program certificate package. *)
Theorem term_analyzed_configured_verified_procedure_specs_valid
    (Hcomplete : analyzed_normalization_complete)
    (program : analyzed_program ) :
  all_registered_procedure_chunks  ⊢
    verified_procedure_specs .
Proof.
  apply verified_procedure_specs_valid.
  apply term_verified_procedure_bodies_guarded.
  exact (term_analyzed_semantic_program Hcomplete program).
Qed.

End WithRuntime.
End WithContracts.
End ProcedureValidity.
