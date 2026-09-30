From Coq Require Import List String ZArith Program.Equality Lia ClassicalEpsilon.
From stdpp Require Import countable gmap namespaces sets.

From iris.algebra Require Import auth gset.
From iris.base_logic Require Import fancy_updates.
From iris.base_logic.lib Require Import own invariants.

From raven Require Import runtime.erasure analysis.structured_certificates runtime.lang runtime.ghost_state.
From raven Require Import verification.expressions analysis.atomicity verification.assertions verification.ir soundness.interpretation soundness.entailment_validity soundness.runtime_model analysis.normalization_base analysis.normalization soundness.rule_validity.

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
  {Contracts : Hoare.ResourceHoare.ResourceContractEnv}
  {Coherence : Hoare.ProcedureContractCoherence}.

Section WithRuntime.
Context {Σ : gFunctors} `{RG : !runtimeG Σ}.
Local Existing Instances RuleValidity.core_simpLangG RuleValidity.core_invTokenG
  RuleValidity.core_heapG RuleValidity.core_irisG.
Local Existing Instance weakestpre.wp'.
Local Notation iProp := (bi_car (iPropI Σ)).

Context (Hruntime_ghost_namespace :
  @runtime_ghost_namespace _ _ Σ RG = ghost_heap_namespace).
Context (Registration : certified_module_registration).

Local Notation all_registered_procedure_chunks := (@RuleValidity.all_registered_procedure_chunks _ _ _ _ _ _ Registration).
Local Notation all_registered_procedure_chunks_lookup := (@RuleValidity.all_registered_procedure_chunks_lookup _ _ _ _ _ _ Registration).
Local Notation global_world_context := (@RuleValidity.global_world_context _ _ _ _ _ _ Registration).
Local Notation global_world_context_constant_symbols := (@RuleValidity.global_world_context_constant_symbols _ _ _ _ _ _ Registration).
Local Notation registered_procedure_chunk := (@RuleValidity.registered_procedure_chunk _ _ _ _ _ _ Registration).
Local Notation runtime_procedure_entry := (@RuleValidity.runtime_procedure_entry _ _ _ _ Registration).
Local Notation runtime_procedure_entry_coherent := (@RuleValidity.runtime_procedure_entry_coherent _ _ _ _ Registration).
Local Notation runtime_procedure_map_chunks := (@RuleValidity.runtime_procedure_map_chunks _ _ _ _ _ _ Registration).
Local Notation term_procedure_body_source_valid_footprinted := (@RuleValidity.term_procedure_body_source_valid_footprinted _ _ _ _ _ _ Registration).
Local Notation term_registered_invariants := (@RuleValidity.term_registered_invariants _ _ _ _ Registration).
Local Notation term_runtime_procedure_layout_configured := (@RuleValidity.term_runtime_procedure_layout_configured _ _ _ _ Registration).
Local Notation term_runtime_procedure_body :=
  (@RuleValidity.term_runtime_procedure_body _ _ _ _ Registration).
Local Notation term_structured_certificate_resource_prenex_valid := (@RuleValidity.term_structured_certificate_resource_prenex_valid _ _ _ _ _ _ Hruntime_ghost_namespace Registration).
Local Notation term_structured_runtime_valid := (@RuleValidity.term_structured_runtime_valid _ _ _ _ _ _ Registration).
Local Notation term_world_context_alloc := (@RuleValidity.term_world_context_alloc _ _ _ _ _ _ Registration).
Local Notation verified_procedure_specs := (@RuleValidity.verified_procedure_specs _ _ _ _ _ _ Registration).
Local Notation verified_procedure_specs_valid := (@RuleValidity.verified_procedure_specs_valid _ _ _ _ _ _ Registration).

(* ------------------------------------------------------------------ *)
(** *** The resource-calculus procedure boundary

    This is the syntax-driven, proposition-valued input consumed by generic
    normalization.  Stable procedure facts and the analyzer certificate are
    recorded directly; alignment and normalization witnesses are derived by
    the generic completeness theorem rather than supplied by each module. *)
(** The canonical cost model is sound for the runtime: proof-only leaves
    erase to the terminal statement and the physical primitives are atomic
    runtime statements.  Together with
    [Certified.contract_cost_model_procedure_sound] this discharges both
    cost-model conditions once, for every module. *)
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

(** A procedure body's canonical entry state: its required instances at its
    formal slots, with nothing open. *)
Definition procedure_entry_state {Γ identity}
    (procedure : typed_procedure Γ identity) :
    GenericRegions.Atomicity.analysis_state :=
  GenericRegions.Atomicity.closed_state
    (Certified.required_entries
      (RegionSyntax.variable_atoms (procedure_formal_variables _ _ procedure))
      identity).

Lemma procedure_entry_state_wf {Γ identity}
    (procedure : typed_procedure Γ identity) :
  GenericRegions.Atomicity.state_wf (procedure_entry_state procedure).
Proof. constructor. Qed.

Lemma procedure_entry_state_closed {Γ identity}
    (procedure : typed_procedure Γ identity) :
  GenericRegions.Atomicity.analysis_open (procedure_entry_state procedure) = ∅.
Proof. reflexivity. Qed.

Lemma procedure_entry_state_outside_atomic {Γ identity}
    (procedure : typed_procedure Γ identity) :
  GenericRegions.Atomicity.analysis_in_atomic
    (procedure_entry_state procedure) = false.
Proof. reflexivity. Qed.

(** The declarations available on entry are those the procedure
    requires. *)
Lemma procedure_entry_state_mask {Γ identity}
    (procedure : typed_procedure Γ identity) :
  GenericRegions.Atomicity.analysis_mask (procedure_entry_state procedure) =
    Certified.required_mask identity.
Proof.
  unfold GenericRegions.Atomicity.analysis_mask.
  rewrite procedure_entry_state_closed difference_empty_L.
  apply Certified.required_entries_declarations.
Qed.

(** An analyzed procedure body: its analysis starts from
    [procedure_entry_state]. *)
Record analyzed_body_certificate {Γ identity}
    (procedure : typed_procedure Γ identity)
    : Type := AnalyzedBodyCertificate {
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
  analyzed_body_exit_closed :
    GenericRegions.Atomicity.analysis_open analyzed_body_exit = ∅;
  analyzed_body_triple :
    @CertifiedNormalization.analyzed_triple _ _ _
 Γ (Assertion.procedure_args identity)
      (@nil typ)
      (Hoare.procedure_body_pre procedure)
      (procedure_body _ _ procedure)
      (procedure_entry_state procedure) analyzed_body_exit
      (Hoare.procedure_body_post procedure
        analyzed_body_exit_store
        analyzed_body_return_reference);
}.

Arguments analyzed_body_triple {_ _} _ _.
Arguments analyzed_body_exit {_ _} _ _.
Arguments analyzed_body_exit_context {_ _} _ _.
Arguments analyzed_body_exit_store {_ _} _ _.
Arguments analyzed_body_return_reference {_ _} _ _.
Arguments analyzed_body_exit_return {_ _} _ _.
Arguments analyzed_body_exit_closed {_ _} _ _.

Definition analyzed_body_normalization_exists {Γ identity}
    (procedure : typed_procedure Γ identity)
    (body : analyzed_body_certificate procedure) : Prop :=
  CertifiedNormalization.restricted_footprinted_normalization_exists
    (CertifiedNormalization.analyzed_hoare
      (analyzed_body_triple _ body))
    (CertifiedNormalization.analyzed_certificate
      (analyzed_body_triple _ body)).

(** Proof-level procedure bridge for the syntax-only analyzer.  The
    normalization witness stays existential: this theorem destructs it only
    while proving an Iris proposition, so neither modules nor executable
    analysis packages carry proof-relevant normalization data. *)
Theorem term_analyzed_body_source_valid
    {Γ identity} (procedure : typed_procedure Γ identity)
    (body : analyzed_body_certificate procedure)
    (Hnormalizes : analyzed_body_normalization_exists procedure body)
    (Hregistered : GenericRegions.Atomicity.certificate_footprint
      (CertifiedNormalization.analyzed_certificate
        (analyzed_body_triple _ body)) ⊆
      term_registered_invariants ) :
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env (Assertion.procedure_args identity))
    (valuation : symbol_valuation) (ambient : coPset),
    RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint
        (CertifiedNormalization.analyzed_certificate
          (analyzed_body_triple _ body)) ∪ term_registered_invariants) ⊆
      ambient ->
    (global_world_context valuation ∗
     term_interp_resource_prenex runtime formals empty_binder_env valuation
       (Hoare.procedure_body_pre procedure)) ⊢
    translated_runtime_wp runtime ambient
      (procedure_entry_state procedure)
      (analyzed_body_exit _ body)
      (procedure_body _ _ procedure)
      (global_world_context valuation ∗
       term_interp_resource_prenex runtime formals empty_binder_env valuation
         (Hoare.procedure_body_post procedure
           (analyzed_body_exit_store _ body)
           (analyzed_body_return_reference _ body))).
Proof.
  destruct Hnormalizes as [normalization Hworker].
  have Hvalid : term_structured_runtime_valid
      (CertifiedNormalization.normalization_target_certificate
        (CertifiedNormalization.footprinted_normalization
          normalization))
      (Hoare.procedure_body_pre procedure)
      (Hoare.procedure_body_post procedure
        (analyzed_body_exit_store _ body)
        (analyzed_body_return_reference _ body)).
  { exact (proj1 (term_structured_certificate_resource_prenex_valid
      (CertifiedNormalization.normalization_target_certificate
        (CertifiedNormalization.footprinted_normalization
          normalization))
      (CertifiedNormalization.normalization_target_derivation
        (CertifiedNormalization.footprinted_normalization
          normalization))
      (procedure_entry_state_wf procedure)
      contract_cost_model_runtime_sound
      Certified.contract_cost_model_procedure_sound
      (fun invariant Hin => Hregistered invariant
        (CertifiedNormalization.footprinted_normalization_subset
          normalization invariant Hin))
      ((CertifiedNormalization.footprinted_normalization_safe
        normalization)
        (procedure_entry_state_outside_atomic procedure)))). }
  exact (term_procedure_body_source_valid_footprinted
    procedure
    (analyzed_body_exit_store _ body)
    (analyzed_body_return_reference _ body)
    eq_refl eq_refl
    (CertifiedNormalization.analyzed_hoare
      (analyzed_body_triple _ body))
    (CertifiedNormalization.analyzed_certificate
      (analyzed_body_triple _ body))
    normalization eq_refl Hvalid).
Qed.

Definition analyzed_body_valid {Γ identity}
    (procedure : typed_procedure Γ identity) : Type :=
  analyzed_body_certificate procedure.

Definition packed_analyzed_body
    (packed : packed_typed_procedure) : Type :=
  match packed with
  | existT Γ (existT identity procedure) =>
      @analyzed_body_valid Γ identity procedure
  end.

(** Module-analysis data for the syntax-only path.  In particular this
    record contains no normalization witness and no alignment proof. *)
Record analyzed_module : Type := {
  analyzed_module_bodies : forall packed,
    List.In packed (procedure_entries Hoare.coherent_procedures) ->
    packed_analyzed_body packed;
  analyzed_module_registered : forall Γ identity
      (procedure : typed_procedure Γ identity)
      (Hin : List.In (pack_typed_procedure procedure)
        (procedure_entries Hoare.coherent_procedures)),
    GenericRegions.Atomicity.certificate_footprint
      (CertifiedNormalization.analyzed_certificate
        (analyzed_body_triple _
          (analyzed_module_bodies
            (pack_typed_procedure procedure) Hin))) ⊆
      term_registered_invariants ;
}.

Arguments analyzed_module_registered _ {_ _} _ _.

(** Generic producer completeness.  Successful restricted analysis and the
    closed procedure-entry state are sufficient; modules and examples carry
    no normalization or alignment witness. *)
Definition analyzed_normalization_complete : Prop :=
  forall Γ identity (procedure : typed_procedure Γ identity)
    (body : analyzed_body_valid procedure),
    analyzed_body_normalization_exists procedure body.

(** This assembly is closed once the proof-theoretic raw-access cut in the
    normalization layer is discharged.  Its assumptions are intentionally
    kept visible in that layer until the analyzed access rule is validated. *)
Theorem analyzed_normalization_complete_from_raw_access_cut :
  analyzed_normalization_complete.
Proof.
  intros Γ identity procedure body.
  apply CertifiedNormalization.analyzed_normalization_exists.
  exact (procedure_entry_state_closed procedure).
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
  term_semantic_body_source_valid : forall
      (runtime : RegionExecution.Primitives.Model.stack_context Γ)
      (formals : formal_env (Assertion.procedure_args F)) (valuation : symbol_valuation) ambient,
    RegionExecution.Primitives.Model.runtime_mask term_registered_invariants ⊆
      ambient ->
    (global_world_context valuation ∗
     term_interp_resource_prenex runtime formals empty_binder_env valuation
       (Hoare.procedure_body_pre procedure)) ⊢
    translated_runtime_wp runtime ambient term_semantic_body_entry
      term_semantic_body_exit (procedure_body _ _ procedure)
      (global_world_context valuation ∗
       term_interp_resource_prenex runtime formals empty_binder_env valuation
         (Hoare.procedure_body_post procedure term_semantic_body_exit_store
           term_semantic_body_return_reference));
}.

Record term_semantic_module_certificates : Type := {
  term_semantic_procedure_bodies : forall Γ F
      (procedure : typed_procedure Γ F),
    List.In (pack_typed_procedure procedure)
      (procedure_entries Hoare.coherent_procedures) ->
    term_registered_body_semantics procedure;
}.

(** Semantic projection of the syntax-only analyzer path.  Once the single
    generic normalization-completeness theorem is available, recursive
    call/spawn closure needs no proof-relevant producer data. *)
Definition term_analyzed_semantic_module
    (Hcomplete : analyzed_normalization_complete)
    (certificates : analyzed_module ) :
    term_semantic_module_certificates .
Proof.
  refine {| term_semantic_procedure_bodies := _ |}.
  intros Γ F procedure Hin.
  set (body := analyzed_module_bodies certificates
    (pack_typed_procedure procedure) Hin).
  refine {| term_semantic_body_entry := procedure_entry_state procedure;
    term_semantic_body_exit := analyzed_body_exit _ body;
    term_semantic_body_exit_context :=
      analyzed_body_exit_context _ body;
    term_semantic_body_exit_store :=
      analyzed_body_exit_store _ body;
    term_semantic_body_return_reference :=
      analyzed_body_return_reference _ body |}.
  - exact (analyzed_body_exit_return _ body).
  - exact (procedure_entry_state_closed procedure).
  - exact (analyzed_body_exit_closed _ body).
  - intros runtime formals valuation ambient Henvelope.
    eapply term_analyzed_body_source_valid.
    + exact (Hcomplete Γ F procedure body).
    + exact (analyzed_module_registered certificates procedure Hin).
    + etrans; last exact Henvelope.
      apply RegionExecution.Primitives.Model.runtime_mask_mono.
      intros invariant Hmember. apply elem_of_union in Hmember as [Hfootprint | Hregistered].
      * exact (analyzed_module_registered certificates procedure Hin _ Hfootprint).
      * exact Hregistered.
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
  let Hbody := (▷ □ (∀ stack_id frame,
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
      RuntimeGhost.stack_frame_own stack_id frame ∗ p -∗
      @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG mask
        (RuntimeLang.proc_stmt
          (runtime_procedure_entry  (pack_typed_procedure callee)) stack_id)
        (fun result => ⌜result = RuntimeLang.LitUnit⌝ ∗ ∃ return_value frame',
          RuntimeGhost.stack_frame_own stack_id frame' ∗
          ⌜frame'.(RuntimeLang.locals) !! "#ret_val" = Some return_value⌝ ∗
          q return_value)))%I in
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
  let Hbody := (▷ □ (∀ stack_id frame,
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
      RuntimeGhost.stack_frame_own stack_id frame ∗ p -∗
      @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG mask
        (RuntimeLang.proc_stmt
          (runtime_procedure_entry  (pack_typed_procedure callee)) stack_id)
        (fun result => ⌜result = RuntimeLang.LitUnit⌝ ∗ ∃ return_value frame',
          RuntimeGhost.stack_frame_own stack_id frame' ∗
          ⌜frame'.(RuntimeLang.locals) !! "#ret_val" = Some return_value⌝ ∗
          q return_value)))%I in
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
  let Hbody := (▷ □ (∀ stack_id frame,
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
      RuntimeGhost.stack_frame_own stack_id frame ∗ p -∗
      @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG ⊤
        (RuntimeLang.proc_stmt
          (runtime_procedure_entry  (pack_typed_procedure callee)) stack_id)
        (fun _ => True)))%I in
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
    (certificates : term_semantic_module_certificates ) :
  all_registered_procedure_chunks  ∗ ▷ verified_procedure_specs  ⊢
    verified_procedure_specs .
Proof.
  unfold RuleValidity.verified_procedure_specs.
  iIntros "[#Hchunks #HIH]".
  iModIntro.
  iIntros (Γ F Δ pre post statement mask_pre mask_post entry exit
    runtime formals binders valuation ambient)
    "Hobligation Hmask Hregistry #Hworld Hpre".
  iDestruct "Hmask" as %Hmask.
  iDestruct "Hregistry" as %Hregistry.
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
    destruct (term_interpreted_expr_list_total formals binders valuation
      (IR.symbolize_expr_list store arguments)) as [values Hvalues].
    have Harguments : Forall2 (fun expression value =>
      RuntimeLang.expr_step expression
        (RuntimeLang.StackFrame
          (@RegionExecution.Primitives.Model.concrete_locals _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (interp_store formals binders valuation store)))
        (RuntimeLang.Val value))
      (@RuntimeErasure.runtime_expr_list _ Γ _ (Assertion.procedure_args procedure)
        (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments)
      (@RegionExecution.Primitives.Model.tval_list_to_list _ (Assertion.procedure_args procedure) values).
    { eapply (@RegionExecution.Primitives.Model.runtime_expr_list_sound _ Γ F Δ (Assertion.procedure_args procedure)
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        formals binders valuation store
        (RuntimeLang.StackFrame
          (@RegionExecution.Primitives.Model.concrete_locals _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (interp_store formals binders valuation store))) arguments values).
      - apply RegionExecution.Primitives.Model.runtime_stack_frame_corresponds.
      - exact Hvalues. }
    have Hlength : length (@RuntimeErasure.runtime_expr_list _ Γ _ (Assertion.procedure_args procedure)
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
        (interp_store formals binders valuation store)))
      (@RuntimeErasure.runtime_expr_list _ Γ _ (Assertion.procedure_args procedure) (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments)
      (@RegionExecution.Primitives.Model.tval_list_to_list _ (Assertion.procedure_args procedure) values)
      (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
      (term_interp_core formals binders valuation
        (Hoare.procedure_pre_instantiation callee
          (IR.symbolize_expr_list store arguments)))
      (fun raw => (∃ return_value : tval (Assertion.procedure_return procedure),
        ⌜raw = @RuntimeErasure.tval_to_val _ (Assertion.procedure_return procedure) return_value⌝ ∗
        term_interp_core formals (binder_cons return_value binders) valuation
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
      iModIntro.
      iIntros (stack_id frame) "%Hframe [Hcallee_frame Hcallee_contract]".
      pose proof (term_runtime_procedure_layout_configured
        (pack_typed_procedure callee) Hin) as Hlayout.
      simpl in Hlayout.
      destruct Hlayout as [Hcallee_wf Hregistered].
      have Hnames : NoDup (@RuntimeErasure.runtime_frame_names callee_variables
        (@RuntimeErasure.runtime_procedure_names _ _ callee_variables procedure callee)).
      { apply RuntimeErasure.runtime_procedure_frame_names_nodup; assumption. }
      destruct Hframe as [Hframe_arguments [Hframe_locals Hframe_dom]].
      unfold RuleValidity.runtime_procedure_entry, registered_runtime_procedure_entry in
        Hframe_arguments, Hframe_locals, Hframe_dom.
      simpl in Hframe_arguments, Hframe_locals, Hframe_dom.
      destruct (@RegionExecution.Primitives.Model.procedure_entry_frame_corresponds _ _
        callee_variables procedure valuation callee values frame Hcallee_wf
        Hframe_arguments Hframe_locals Hframe_dom)
        as (callee_valuation & Hagree & Hcorresponds & Hdom).
      pose proof (@RegionExecution.Primitives.Model.stack_corresponds_canonical_frame_eq _ callee_variables (Assertion.procedure_args procedure) []
        (@RuntimeErasure.runtime_procedure_names _ _ callee_variables procedure callee)
        (formal_env_of_values values) empty_binder_env callee_valuation
        (procedure_entry_store _ _ callee) frame Hnames Hcorresponds Hdom) as Hframe_eq.
      subst frame.
      set (callee_runtime := @RegionExecution.Primitives.make_stack_context
        callee_variables stack_id
        (@RuntimeErasure.runtime_procedure_names _ _
          callee_variables procedure callee) Hnames).
      iPoseProof (bi.equiv_entails_1_1 _ _
        (procedure_pre_instantiation_interp callee
          (IR.symbolize_expr_list store arguments)
          formals binders valuation values Hvalues)
        with "Hcallee_contract") as "Hcallee_contract".
      iPoseProof (bi.equiv_entails_1_1 _ _
        (term_interp_core_constant_symbols (formal_env_of_values values)
          empty_binder_env valuation callee_valuation
          (procedure_precondition _ _ callee) Hagree
          (procedure_precondition_entry_free _ Hcallee_wf))
        with "Hcallee_contract") as "Hcallee_contract".
      set (body := term_semantic_procedure_bodies certificates
        callee_variables procedure callee Hin).
      have Hexit_envelope : RegionExecution.Primitives.Model.runtime_mask
          term_registered_invariants ⊆
        RegionExecution.Primitives.Model.active_runtime_mask ambient entry :=
        Hregistry.
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
      iAssert (global_world_context valuation) with "[Hworld Hchunks HIH]"
        as "#Hglobal".
      { rewrite /global_world_context.
        iFrame "Hworld Hchunks HIH". }
      iPoseProof (bi.equiv_entails_1_1 _ _
        (global_world_context_constant_symbols valuation callee_valuation Hagree)
        with "Hglobal") as "#Hcallee_global".
      iPoseProof (@term_semantic_body_source_valid callee_variables procedure
        callee body
        callee_runtime (formal_env_of_values values) callee_valuation
        (RegionExecution.Primitives.Model.active_runtime_mask ambient entry) Hexit_envelope) as "Hsource".
      iEval (unfold RuleValidity.translated_runtime_wp; rewrite Hregistered;
        rewrite Hentry_active Hexit_active) in "Hsource".
      iAssert (@RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
        (term_runtime_procedure_body (pack_typed_procedure callee) stack_id)
        (fun result =>
          (⌜result = RuntimeLang.LitUnit⌝ ∗
           |={RegionExecution.Primitives.Model.active_runtime_mask ambient entry}=>
             global_world_context callee_valuation ∗
             term_interp_resource_prenex
               callee_runtime (formal_env_of_values values) empty_binder_env
               callee_valuation (Hoare.procedure_body_post callee
                 (term_semantic_body_exit_store _ body)
                 (term_semantic_body_return_reference _ body)))%I))
        with "[Hsource Hcallee_global Hcallee_frame Hcallee_contract]" as "Hwp".
      { iApply ("Hsource" with
          "[$Hcallee_global $Hcallee_frame $Hcallee_contract]"). }
      iEval (unfold RegionExecution.Primitives.Model.runtime_wp) in "Hwp".
      unfold RegionExecution.Primitives.Model.runtime_wp.
      iApply wp_fupd.
      iApply (wp_wand with "Hwp").
          iIntros (result) "[%Hunit Hout]".
          subst result.
          iMod "Hout" as "[_ Hbodypost]".
          iModIntro.
          iSplit; first done.
          iPoseProof (bi.equiv_entails_1_1 _ _
            (procedure_body_post_interp callee
              (term_semantic_body_exit_store _ body)
              (term_semantic_body_return_reference _ body)
              callee_runtime (formal_env_of_values values) callee_valuation)
            with "[Hbodypost]") as (exit_values)
              "[Hexit_frame Hcallee_post]".
          { iExact "Hbodypost". }
          set (return_value := interp_ref (formal_env_of_values values)
            (formal_env_of_values exit_values) callee_valuation
            (term_semantic_body_return_reference _ body)).
          have Hreturn_lookup :
            @RegionExecution.Primitives.Model.concrete_locals _ callee_variables
              (@RuntimeErasure.runtime_procedure_names _ _
                callee_variables procedure callee)
              (interp_store (formal_env_of_values values)
                (formal_env_of_values exit_values) callee_valuation
                (term_semantic_body_exit_store _ body)) !! "#ret_val" =
            Some (@RuntimeErasure.tval_to_val _ _ return_value).
          { rewrite (@RegionExecution.Primitives.Model.concrete_procedure_return_lookup _ _
              callee_variables procedure _ callee (formal_env_of_values values)
              (formal_env_of_values exit_values) callee_valuation
              (term_semantic_body_exit_store _ body) Hcallee_wf Hnames).
            rewrite (term_semantic_body_exit_return _ body).
            reflexivity. }
          have Hvalues_weakened : interp_expr_list formals
            (binder_cons return_value binders) valuation
            (weaken_expr_list (IR.symbolize_expr_list store arguments)) =
            Some values.
          { rewrite interp_weaken_expr_list. exact Hvalues. }
          iPoseProof (bi.equiv_entails_1_2 _ _
            (term_interp_core_constant_symbols (formal_env_of_values values)
              (binder_cons return_value empty_binder_env) valuation callee_valuation
              (procedure_postcondition _ _ callee) Hagree
              (procedure_postcondition_entry_free _ Hcallee_wf))
            with "Hcallee_post") as "Hcallee_post".
          (* No [Hreturn] transport and no [UIP_refl]: the caller's result
             binder already has the declared return type. *)
          pose proof (procedure_post_instantiation_interp callee
            (weaken_expr_list (IR.symbolize_expr_list store arguments))
            (ERef (RefBound MHere)) contract_post Hlookup Hpost_inst
            formals binders valuation values return_value
            Hvalues_weakened) as Hpost_equiv.
          iPoseProof (bi.equiv_entails_1_2 _ _ Hpost_equiv
            with "Hcallee_post") as "Hcaller_post".
          iExists (@RuntimeErasure.tval_to_val _ _ return_value),
            (RuntimeLang.StackFrame
         (@RegionExecution.Primitives.Model.concrete_locals _ callee_variables
           (@RuntimeErasure.runtime_procedure_names _ _
             callee_variables procedure callee)
                (interp_store (formal_env_of_values values)
                  (formal_env_of_values exit_values) callee_valuation
                  (term_semantic_body_exit_store _ body)))).
          iSplitL "Hexit_frame".
          { iEval (unfold RegionExecution.Primitives.Model.core_stack_own) in "Hexit_frame".
            iExact "Hexit_frame". }
          iSplit.
          { iPureIntro. exact Hreturn_lookup. }
          iExists return_value.
          iSplit; first done.
          iExact "Hcaller_post".
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
    destruct (term_interpreted_expr_list_total formals binders valuation
      (IR.symbolize_expr_list store arguments)) as [values Hvalues].
    have Harguments : Forall2 (fun expression value =>
      RuntimeLang.expr_step expression
        (RuntimeLang.StackFrame (@RegionExecution.Primitives.Model.concrete_locals _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (interp_store formals binders valuation store)))
        (RuntimeLang.Val value))
      (@RuntimeErasure.runtime_expr_list _ Γ _ (Assertion.procedure_args procedure) (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments)
      (@RegionExecution.Primitives.Model.tval_list_to_list _ (Assertion.procedure_args procedure) values).
    { eapply (@RegionExecution.Primitives.Model.runtime_expr_list_sound _ Γ F Δ (Assertion.procedure_args procedure) (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        formals binders valuation store
        (RuntimeLang.StackFrame (@RegionExecution.Primitives.Model.concrete_locals _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (interp_store formals binders valuation store))) arguments values).
      - apply RegionExecution.Primitives.Model.runtime_stack_frame_corresponds.
      - exact Hvalues. }
    have Hlength : length (@RuntimeErasure.runtime_expr_list _ Γ _ (Assertion.procedure_args procedure)
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
        (interp_store formals binders valuation store)))
      (@RuntimeErasure.runtime_expr_list _ Γ _ (Assertion.procedure_args procedure) (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments)
      (@RegionExecution.Primitives.Model.tval_list_to_list _ (Assertion.procedure_args procedure) values)
      (@RuntimeErasure.runtime_variable Γ _ (Assertion.procedure_return procedure)
        (RegionExecution.Primitives.Model.runtime_names Γ runtime) target)
      (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
      (term_interp_core formals binders valuation
        (Hoare.procedure_pre_instantiation callee
          (IR.symbolize_expr_list store arguments)))
      (fun raw => (∃ return_value : tval (Assertion.procedure_return procedure),
        ⌜raw = @RuntimeErasure.tval_to_val _ (Assertion.procedure_return procedure) return_value⌝ ∗
        term_interp_core formals (binder_cons return_value binders) valuation
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
          (term_stack_own_update runtime formals binders valuation store target
            return_value)).
        iExact "Hcaller". }
      iExact "Hpost".
    + iPoseProof (all_registered_procedure_chunks_lookup
        (pack_typed_procedure callee) Hin with "Hchunks") as "#Hchunk".
      iFrame "Hstack Hchunk Hcontract".
      iNext.
      iModIntro.
      iIntros (stack_id frame) "%Hframe [Hcallee_frame Hcallee_contract]".
      pose proof (term_runtime_procedure_layout_configured
        (pack_typed_procedure callee) Hin) as Hlayout.
      simpl in Hlayout.
      destruct Hlayout as [Hcallee_wf Hregistered].
      have Hnames : NoDup (@RuntimeErasure.runtime_frame_names callee_variables
        (@RuntimeErasure.runtime_procedure_names _ _ callee_variables procedure callee)).
      { apply RuntimeErasure.runtime_procedure_frame_names_nodup; assumption. }
      destruct Hframe as [Hframe_arguments [Hframe_locals Hframe_dom]].
      unfold RuleValidity.runtime_procedure_entry, registered_runtime_procedure_entry in
        Hframe_arguments, Hframe_locals, Hframe_dom.
      simpl in Hframe_arguments, Hframe_locals, Hframe_dom.
      destruct (@RegionExecution.Primitives.Model.procedure_entry_frame_corresponds _ _
        callee_variables procedure valuation callee values frame Hcallee_wf
        Hframe_arguments Hframe_locals Hframe_dom)
        as (callee_valuation & Hagree & Hcorresponds & Hdom).
      pose proof (@RegionExecution.Primitives.Model.stack_corresponds_canonical_frame_eq _ callee_variables (Assertion.procedure_args procedure) []
        (@RuntimeErasure.runtime_procedure_names _ _ callee_variables procedure callee)
        (formal_env_of_values values) empty_binder_env callee_valuation
        (procedure_entry_store _ _ callee) frame Hnames Hcorresponds Hdom) as Hframe_eq.
      subst frame.
      set (callee_runtime := @RegionExecution.Primitives.make_stack_context
        callee_variables stack_id
        (@RuntimeErasure.runtime_procedure_names _ _
          callee_variables procedure callee) Hnames).
      iPoseProof (bi.equiv_entails_1_1 _ _
        (procedure_pre_instantiation_interp callee
          (IR.symbolize_expr_list store arguments)
          formals binders valuation values Hvalues)
        with "Hcallee_contract") as "Hcallee_contract".
      iPoseProof (bi.equiv_entails_1_1 _ _
        (term_interp_core_constant_symbols (formal_env_of_values values)
          empty_binder_env valuation callee_valuation
          (procedure_precondition _ _ callee) Hagree
          (procedure_precondition_entry_free _ Hcallee_wf))
        with "Hcallee_contract") as "Hcallee_contract".
      set (body := term_semantic_procedure_bodies certificates
        callee_variables procedure callee Hin).
      have Hexit_envelope : RegionExecution.Primitives.Model.runtime_mask
          term_registered_invariants ⊆
        RegionExecution.Primitives.Model.active_runtime_mask ambient entry :=
        Hregistry.
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
      iAssert (global_world_context valuation) with "[Hworld Hchunks HIH]"
        as "#Hglobal".
      { rewrite /global_world_context.
        iFrame "Hworld Hchunks HIH". }
      iPoseProof (bi.equiv_entails_1_1 _ _
        (global_world_context_constant_symbols valuation callee_valuation Hagree)
        with "Hglobal") as "#Hcallee_global".
      iPoseProof (@term_semantic_body_source_valid callee_variables procedure
        callee body
        callee_runtime (formal_env_of_values values) callee_valuation
        (RegionExecution.Primitives.Model.active_runtime_mask ambient entry) Hexit_envelope) as "Hsource".
      iEval (unfold RuleValidity.translated_runtime_wp; rewrite Hregistered;
        rewrite Hentry_active Hexit_active) in "Hsource".
      iAssert (@RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
        (term_runtime_procedure_body (pack_typed_procedure callee) stack_id)
        (fun result =>
          (⌜result = RuntimeLang.LitUnit⌝ ∗
           |={RegionExecution.Primitives.Model.active_runtime_mask ambient entry}=>
             global_world_context callee_valuation ∗
             term_interp_resource_prenex
               callee_runtime (formal_env_of_values values) empty_binder_env
               callee_valuation (Hoare.procedure_body_post callee
                 (term_semantic_body_exit_store _ body)
                 (term_semantic_body_return_reference _ body)))%I))
        with "[Hsource Hcallee_global Hcallee_frame Hcallee_contract]" as "Hwp".
      { iApply ("Hsource" with
          "[$Hcallee_global $Hcallee_frame $Hcallee_contract]"). }
      iEval (unfold RegionExecution.Primitives.Model.runtime_wp) in "Hwp".
      unfold RegionExecution.Primitives.Model.runtime_wp.
      iApply wp_fupd.
      iApply (wp_wand with "Hwp").
          iIntros (result) "[%Hunit Hout]".
          subst result.
          iMod "Hout" as "[_ Hbodypost]".
          iModIntro.
          iSplit; first done.
          iPoseProof (bi.equiv_entails_1_1 _ _
            (procedure_body_post_interp callee
              (term_semantic_body_exit_store _ body)
              (term_semantic_body_return_reference _ body)
              callee_runtime (formal_env_of_values values) callee_valuation)
            with "[Hbodypost]") as (exit_values)
              "[Hexit_frame Hcallee_post]".
          { iExact "Hbodypost". }
          set (return_value := interp_ref (formal_env_of_values values)
            (formal_env_of_values exit_values) callee_valuation
            (term_semantic_body_return_reference _ body)).
          have Hreturn_lookup :
            @RegionExecution.Primitives.Model.concrete_locals _ callee_variables
              (@RuntimeErasure.runtime_procedure_names _ _
                callee_variables procedure callee)
              (interp_store (formal_env_of_values values)
                (formal_env_of_values exit_values) callee_valuation
                (term_semantic_body_exit_store _ body)) !! "#ret_val" =
            Some (@RuntimeErasure.tval_to_val _ _ return_value).
          { rewrite (@RegionExecution.Primitives.Model.concrete_procedure_return_lookup _ _
              callee_variables procedure _ callee (formal_env_of_values values)
                    (formal_env_of_values exit_values) callee_valuation
              (term_semantic_body_exit_store _ body) Hcallee_wf Hnames).
            rewrite (term_semantic_body_exit_return _ body).
            reflexivity. }
          have Hvalues_weakened : interp_expr_list formals
            (binder_cons return_value binders) valuation
            (weaken_expr_list (IR.symbolize_expr_list store arguments))
            = Some values.
          { rewrite interp_weaken_expr_list. exact Hvalues. }
          iPoseProof (bi.equiv_entails_1_2 _ _
            (term_interp_core_constant_symbols (formal_env_of_values values)
              (binder_cons return_value empty_binder_env) valuation callee_valuation
              (procedure_postcondition _ _ callee) Hagree
              (procedure_postcondition_entry_free _ Hcallee_wf))
            with "Hcallee_post") as "Hcallee_post".
          (* No [Hreturn] transport and no [UIP_refl]: the caller's result
             binder already has the declared return type. *)
          pose proof (procedure_post_instantiation_interp callee
            (weaken_expr_list (IR.symbolize_expr_list store arguments))
            (ERef (RefBound MHere)) contract_post Hlookup Hpost_inst
            formals binders valuation values return_value
            Hvalues_weakened) as Hpost_equiv.
          iPoseProof (bi.equiv_entails_1_2 _ _ Hpost_equiv
            with "Hcallee_post") as "Hcaller_post".
          iExists (@RuntimeErasure.tval_to_val _ _ return_value),
            (RuntimeLang.StackFrame
              (@RegionExecution.Primitives.Model.concrete_locals _ callee_variables
              (@RuntimeErasure.runtime_procedure_names _ _
                callee_variables procedure callee)
                (interp_store (formal_env_of_values values)
                  (formal_env_of_values exit_values) callee_valuation
                  (term_semantic_body_exit_store _ body)))).
          iSplitL "Hexit_frame".
          { iEval (unfold RegionExecution.Primitives.Model.core_stack_own) in "Hexit_frame".
            iExact "Hexit_frame". }
          iSplit.
          { iPureIntro. exact Hreturn_lookup. }
          iExists return_value.
          iSplit; first done.
          iExact "Hcaller_post".
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
    destruct (term_interpreted_expr_list_total formals binders valuation
      (IR.symbolize_expr_list store arguments)) as [values Hvalues].
    have Harguments : Forall2 (fun expression value =>
      RuntimeLang.expr_step expression
        (RuntimeLang.StackFrame (@RegionExecution.Primitives.Model.concrete_locals _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (interp_store formals binders valuation store)))
        (RuntimeLang.Val value))
      (@RuntimeErasure.runtime_expr_list _ Γ _ (Assertion.procedure_args procedure) (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments)
      (@RegionExecution.Primitives.Model.tval_list_to_list _ (Assertion.procedure_args procedure) values).
    { eapply (@RegionExecution.Primitives.Model.runtime_expr_list_sound _ Γ F Δ (Assertion.procedure_args procedure) (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        formals binders valuation store
        (RuntimeLang.StackFrame (@RegionExecution.Primitives.Model.concrete_locals _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (interp_store formals binders valuation store))) arguments values).
      - apply RegionExecution.Primitives.Model.runtime_stack_frame_corresponds.
      - exact Hvalues. }
    have Hlength : length (@RuntimeErasure.runtime_expr_list _ Γ _ (Assertion.procedure_args procedure)
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
        (interp_store formals binders valuation store)))
      (@RuntimeErasure.runtime_expr_list _ Γ _ (Assertion.procedure_args procedure) (RegionExecution.Primitives.Model.runtime_names Γ runtime) arguments)
      (@RegionExecution.Primitives.Model.tval_list_to_list _ (Assertion.procedure_args procedure) values)
      (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
      (term_interp_core formals binders valuation
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
      iModIntro.
      iIntros (stack_id frame) "%Hframe [Hcallee_frame Hcallee_contract]".
      pose proof (term_runtime_procedure_layout_configured
        (pack_typed_procedure callee) Hin) as Hlayout.
      simpl in Hlayout.
      destruct Hlayout as [Hcallee_wf Hregistered].
      have Hnames : NoDup (@RuntimeErasure.runtime_frame_names callee_variables
        (@RuntimeErasure.runtime_procedure_names _ _ callee_variables procedure callee)).
      { apply RuntimeErasure.runtime_procedure_frame_names_nodup; assumption. }
      destruct Hframe as [Hframe_arguments [Hframe_locals Hframe_dom]].
      unfold RuleValidity.runtime_procedure_entry, registered_runtime_procedure_entry in
        Hframe_arguments, Hframe_locals, Hframe_dom.
      simpl in Hframe_arguments, Hframe_locals, Hframe_dom.
      destruct (@RegionExecution.Primitives.Model.procedure_entry_frame_corresponds _ _
        callee_variables procedure valuation callee values frame Hcallee_wf
        Hframe_arguments Hframe_locals Hframe_dom)
        as (callee_valuation & Hagree & Hcorresponds & Hdom).
      pose proof (@RegionExecution.Primitives.Model.stack_corresponds_canonical_frame_eq _ callee_variables (Assertion.procedure_args procedure) []
        (@RuntimeErasure.runtime_procedure_names _ _ callee_variables procedure callee)
        (formal_env_of_values values) empty_binder_env callee_valuation
        (procedure_entry_store _ _ callee) frame Hnames Hcorresponds Hdom) as Hframe_eq.
      subst frame.
      set (callee_runtime := @RegionExecution.Primitives.make_stack_context
        callee_variables stack_id
        (@RuntimeErasure.runtime_procedure_names _ _
          callee_variables procedure callee) Hnames).
      iPoseProof (bi.equiv_entails_1_1 _ _
        (procedure_pre_instantiation_interp callee
          (IR.symbolize_expr_list store arguments)
          formals binders valuation values Hvalues)
        with "Hcallee_contract") as "Hcallee_contract".
      iPoseProof (bi.equiv_entails_1_1 _ _
        (term_interp_core_constant_symbols (formal_env_of_values values)
          empty_binder_env valuation callee_valuation
          (procedure_precondition _ _ callee) Hagree
          (procedure_precondition_entry_free _ Hcallee_wf))
        with "Hcallee_contract") as "Hcallee_contract".
      set (body := term_semantic_procedure_bodies certificates
        callee_variables procedure callee Hin).
      have Hexit_envelope : RegionExecution.Primitives.Model.runtime_mask
          term_registered_invariants ⊆ (⊤ : coPset).
      { set_solver. }
      have Hentry_active : RegionExecution.Primitives.Model.active_runtime_mask (⊤ : coPset)
        (term_semantic_body_entry _ body) = (⊤ : coPset).
      { apply RegionExecution.Primitives.Model.active_runtime_mask_closed.
        exact (term_semantic_body_entry_closed _ body). }
      have Hexit_active : RegionExecution.Primitives.Model.active_runtime_mask (⊤ : coPset)
        (term_semantic_body_exit _ body) = (⊤ : coPset).
      { apply RegionExecution.Primitives.Model.active_runtime_mask_closed.
        exact (term_semantic_body_exit_closed _ body). }
      iAssert (global_world_context valuation) with "[Hworld Hchunks HIH]"
        as "#Hglobal".
      { rewrite /global_world_context.
        iFrame "Hworld Hchunks HIH". }
      iPoseProof (bi.equiv_entails_1_1 _ _
        (global_world_context_constant_symbols valuation callee_valuation Hagree)
        with "Hglobal") as "#Hcallee_global".
      iPoseProof (@term_semantic_body_source_valid callee_variables procedure
        callee body
        callee_runtime (formal_env_of_values values) callee_valuation
        (⊤ : coPset) Hexit_envelope) as "Hsource".
      iEval (unfold RuleValidity.translated_runtime_wp; rewrite Hregistered;
        rewrite Hentry_active Hexit_active) in "Hsource".
      iAssert (@RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG (⊤ : coPset)
        (term_runtime_procedure_body (pack_typed_procedure callee) stack_id)
        (fun result =>
          (⌜result = RuntimeLang.LitUnit⌝ ∗
           |={⊤}=> global_world_context callee_valuation ∗
             term_interp_resource_prenex
               callee_runtime (formal_env_of_values values) empty_binder_env
               callee_valuation (Hoare.procedure_body_post callee
                 (term_semantic_body_exit_store _ body)
                 (term_semantic_body_return_reference _ body)))%I))
        with "[Hsource Hcallee_global Hcallee_frame Hcallee_contract]" as "Hwp".
      { iApply ("Hsource" with
          "[$Hcallee_global $Hcallee_frame $Hcallee_contract]"). }
      iEval (unfold RegionExecution.Primitives.Model.runtime_wp) in "Hwp".
      unfold RegionExecution.Primitives.Model.runtime_wp.
      iApply wp_fupd.
      iApply (wp_wand with "Hwp").
      iIntros (result) "[%Hunit Hout]". subst result.
      iMod "Hout" as "[Hglobal' Hbodypost']".
      done.
Qed.

(** Public procedure-level soundness theorem.  Its only explicit input is the
    module's finite family of normalization proofs and certificates; the
    recursive specification environment is constructed and closed here. *)

(** Close the recursive procedure specification environment from the finite
    module certificate package. *)
Theorem term_analyzed_configured_verified_procedure_specs_valid
    (Hcomplete : analyzed_normalization_complete)
    (certificates : analyzed_module ) :
  all_registered_procedure_chunks  ⊢
    verified_procedure_specs .
Proof.
  apply verified_procedure_specs_valid.
  apply term_verified_procedure_bodies_guarded.
  exact (term_analyzed_semantic_module Hcomplete certificates).
Qed.

End WithRuntime.
End WithContracts.
End ProcedureValidity.
