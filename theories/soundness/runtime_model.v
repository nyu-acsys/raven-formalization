From Coq Require Import List String ZArith Program.Equality Lia
  Logic.ProofIrrelevance ClassicalEpsilon.
From stdpp Require Import countable gmap namespaces sets.

From iris.algebra Require Import auth gset.
From iris.base_logic Require Import fancy_updates.
From iris.base_logic.lib Require Import own invariants ghost_map.

From raven Require Import runtime.lang runtime.ghost_state runtime.invariant_tokens runtime.erasure.
From raven Require Import verification.expressions analysis.atomicity verification.assertions verification.ir soundness.interpretation soundness.entailment_validity analysis.certificate_semantics analysis.structured_certificates.

Import ListNotations.
Import weakestpre.
Open Scope list_scope.

(** Concrete connection between the typed assertion semantics and Raven's
    existing Iris ghost state. *)
Module Runtime.

Module RuntimeModel := InvTokens.
Module RuntimeLifting := RuntimeModel.lifting.
Module RuntimeGhost := RuntimeLifting.ghost_state.
Module RuntimeLang := RuntimeLifting.lang.
Import RuntimeErasure.

Module Validation := Validity.
Module Translation := Validation.Translation.
Module IR := Translation.IR.
Module Assertions := Translation.Assertions.
Module Core := Translation.Core.
Import Core IR Core IR Translation.

Module GenericRegions := Region.

(** Public projection of analyzer-certificate uniqueness for clients of this
    runtime module. *)
Module CertificateFacts.
Section WithSignature.
Context {RAs : RAConfig} {Logic : Assertion.LogicSignature}
  {Cost : AnalysisView.LeafCost}.
Lemma analysis_certificate_unique
    {Γ entry statement exit}
    (certificate1 certificate2 : GenericRegions.Atomicity.analysis_certificate
      Γ entry statement exit) :
  certificate1 = certificate2.
Proof.
  apply GenericRegions.Atomicity.analysis_certificate_unique.
Qed.
End WithSignature.
End CertificateFacts.

Section WithSignature.
Context {RAs : RAConfig} {Logic : Assertion.LogicSignature}
  {Cost : AnalysisView.LeafCost}.
Definition tval_ghost_valid {t} (value : tval t) : Prop.
Proof.
  exact (tval_ra_valid value).
Defined.

Definition ghost_chunk_valid (field : field_id)
    (value : tval (Assertion.field_type field)) : Prop :=
  tval_ghost_valid value.

End WithSignature.

(** Canonical pairing used by certified-region soundness.  Unlike the generic
    pairing in [certificate_semantics], every component below is stated over
    the runtime IR.  The explicit LIFO boundary stacks let
    the semantic induction split sequences without losing an accessor that
    was opened by the first component and is closed by the second. *)
Module CertifiedRegions.
Module Atomicity := GenericRegions.Atomicity.

Section WithContracts.
Context {RAs : RAConfig} {Logic : Assertion.LogicSignature}
  {Contracts : Hoare.ResourceHoare.ResourceContractEnv}.
(** Procedure masks, inferred from the contracts as in Raven: a procedure
    requires the invariants its precondition depends on and grants those its
    postcondition depends on in addition.  This is the only definition of
    the masks; everything else refers to it. *)
Definition required_mask (procedure : proc_id) : gset inv_id :=
  Hoare.ResourceHoare.contract_invariants Hoare.ResourceHoare.predicate_body
    Hoare.ResourceHoare.declared_predicates (Hoare.ResourceHoare.contract_pre procedure).

Definition granted_mask (procedure : proc_id) : gset inv_id :=
  Hoare.ResourceHoare.contract_invariants Hoare.ResourceHoare.predicate_body
    Hoare.ResourceHoare.declared_predicates (Hoare.ResourceHoare.contract_post procedure) ∖
  required_mask procedure.

(** The cost of every leaf is determined by the language and the contract
    environment, so each module uses the same derived cost model.
    Proof-only leaves
    take no step; the physical primitives are single atomic steps of the
    runtime language; calls and spawns take the effect declared by the
    callee's contract.  Structural statements are analyzed structurally and
    never consult this function. *)
Definition contract_cost_model : forall Γ, stmt Γ -> Atomicity.step_cost :=
  fun Γ statement =>
    match statement with
    | TAssign _ _ | TFieldRead _ _ _ | TFieldWrite _ _ _ | TAlloc _ _ =>
        Atomicity.AtomicStep
    | TCall procedure _ _ =>
        Atomicity.ProcedureCallStep (required_mask procedure)
          (granted_mask procedure)
    | TSpawn procedure _ =>
        Atomicity.ProcedureSpawnStep (required_mask procedure)
    | _ => Atomicity.NoStep
    end.

#[local] Instance leaf_costs : AnalysisView.LeafCost :=
  AnalysisView.LeafCostData contract_cost_model.

(** The analyzer-selected effect of procedure leaves agrees with the contract
    environment used by the Hoare and runtime layers. *)
Definition procedure_cost_model_sound : Prop :=
  forall Γ (statement : stmt Γ),
  match statement with
  | TCall procedure _ _ =>
      AnalysisView.leaf_cost Γ statement = Atomicity.ProcedureCallStep
        (required_mask procedure)
        (granted_mask procedure)
  | TSpawn procedure _ =>
      AnalysisView.leaf_cost Γ statement =
        Atomicity.ProcedureSpawnStep (required_mask procedure)
  | _ =>
      match AnalysisView.leaf_cost Γ statement with
      | Atomicity.ProcedureCallStep _ _
      | Atomicity.ProcedureSpawnStep _ => False
      | _ => True
      end
  end.

Lemma contract_cost_model_procedure_sound :
  procedure_cost_model_sound.
Proof. intros Γ statement. destruct statement; exact I || reflexivity. Qed.

Lemma certified_call_step_effect
    (Hcost : procedure_cost_model_sound)
    Γ procedure
    (arguments : pexpr_list Γ (Assertion.procedure_args procedure))
    (target : call_target Γ (Assertion.procedure_return procedure)) entry exit :
  Atomicity.take_step
      (AnalysisView.leaf_cost Γ (@TCall _ _ Γ procedure arguments target))
      entry = inr exit ->
  required_mask procedure ⊆ Atomicity.analysis_mask entry /\
  granted_mask procedure ## Atomicity.analysis_open entry /\
  Atomicity.analysis_mask exit = Atomicity.analysis_mask entry ∪
    granted_mask procedure /\
  Atomicity.analysis_open exit = Atomicity.analysis_open entry.
Proof.
  intros Hstep. exact (Atomicity.procedure_call_step_success _ _ _ _ Hstep).
Qed.

Lemma certified_spawn_step_effect
    (Hcost : procedure_cost_model_sound)
    Γ procedure
    (arguments : pexpr_list Γ (Assertion.procedure_args procedure)) entry exit :
  Atomicity.take_step
      (AnalysisView.leaf_cost Γ (@TSpawn _ _ Γ procedure arguments)) entry = inr exit ->
  required_mask procedure ⊆ Atomicity.analysis_mask entry /\
  Atomicity.analysis_mask exit = Atomicity.analysis_mask entry /\
  Atomicity.analysis_open exit = Atomicity.analysis_open entry.
Proof.
  intros Hstep. exact (Atomicity.procedure_spawn_step_success _ _ _ Hstep).
Qed.

Lemma unfold_analysis_mask {Γ : context} {entry : Atomicity.analysis_state}
    {invariant : inv_id}
    {arguments : pexpr_list Γ (Assertion.invariant_args invariant)}
    {exit : Atomicity.analysis_state}
    (view : RegionSyntax.view (TUnfold invariant arguments) =
      AnalysisView.ViewUnfold invariant)
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

End WithContracts.
End CertifiedRegions.
#[global] Existing Instance CertifiedRegions.leaf_costs.
#[global] Opaque CertifiedRegions.leaf_costs.

Section WithSignature.
Context {RAs : RAConfig} {Logic : Assertion.LogicSignature}
  {Cost : AnalysisView.LeafCost}.
Definition runtime_ghost_alloc_spec {Σ : gFunctors}
    (simpLangG0 : RuntimeLifting.simpLangG Σ) (ghost_namespace : namespace)
    (ghost_own : forall field,
      tval TRef -> tval (Assertion.field_type field) -> iProp Σ) : Prop :=
  forall E field resource_name field_name address chunk
    (Hfield : Assertion.field_type field = TRA resource_name),
    (↑ghost_namespace : coPset) ⊆ E ->
    @ra_base.valid _ (ra_base.RA_inst (RuntimeLang.ra_map resource_name)) chunk ->
    (⊢ @RuntimeGhost.ghost_dom_frag _ Σ
          (@RuntimeLifting.simpLangG_gen_heapG _ Σ simpLangG0)
          {[RuntimeLang.heap_addr_constr (RuntimeLang.Loc address) field_name]} -∗
        @fupd (iPropI Σ)
          (@bi_fupd_fupd _ (@uPred_bi_fupd HasLc Σ
            (@RuntimeLifting.simpLangG_invG _ Σ simpLangG0))) E E
          (ghost_own field (VRef address)
            (eq_rect (TRA resource_name) tval (VRA chunk)
              (Assertion.field_type field) (eq_sym Hfield))))%I.

Definition runtime_ghost_update_spec {Σ : gFunctors}
    (simpLangG0 : RuntimeLifting.simpLangG Σ)
    (ghost_own : forall field,
      tval TRef -> tval (Assertion.field_type field) -> iProp Σ) : Prop :=
  forall E field location old_chunk new_chunk,
    tval_fpu_allowed old_chunk new_chunk ->
    ghost_own field location old_chunk ⊢
      |={E}=> ghost_own field location new_chunk.

(** Term-level resources chosen by adequacy. A value of this class can be
    constructed with names returned by [own_alloc] inside an Iris
    initialization proof. *)
Class runtimeG (Σ : gFunctors) := RuntimeG {
  runtime_simpLangG : RuntimeLifting.simpLangG Σ;
  runtime_invTokenG : RuntimeModel.invTokenG Σ;
  runtime_ghost_namespace : namespace;
  runtime_ghost_own : forall field,
    tval TRef -> tval (Assertion.field_type field) -> iProp Σ;
  runtime_ghost_own_timeless : forall field location chunk,
    Timeless (runtime_ghost_own field location chunk);
  runtime_ghost_alloc : runtime_ghost_alloc_spec runtime_simpLangG
    runtime_ghost_namespace runtime_ghost_own;
  runtime_ghost_update : runtime_ghost_update_spec runtime_simpLangG
    runtime_ghost_own;
}.

(** Module-defined ghost ownership may itself require allocating an Iris
    invariant or authoritative camera before a [runtimeG] value can be
    assembled.  The implementation of that allocation belongs to the logic
    configuration, not to individual Raven modules. Its result is an
    opaque proof-time handle; any persistent infrastructure needed by the
    resulting ownership predicate is established internally by
    [runtime_ghost_resource_alloc]. *)
Record runtime_ghost_resource_factory (Σ : gFunctors) `{!FUpd (iPropI Σ)}
    (ghost_namespace : namespace) :=
  RuntimeGhostResourceFactory {
    runtime_ghost_resource : RuntimeLifting.simpLangG Σ -> Type;
    runtime_ghost_resource_own : forall simpLangG0,
      runtime_ghost_resource simpLangG0 -> forall field,
      tval TRef -> tval (Assertion.field_type field) -> iProp Σ;
    runtime_ghost_resource_own_timeless : forall simpLangG0 resource field
        location chunk,
      Timeless (runtime_ghost_resource_own simpLangG0 resource field location chunk);
    runtime_ghost_resource_alloc_cell : forall simpLangG0 resource,
      runtime_ghost_alloc_spec simpLangG0
        ghost_namespace (runtime_ghost_resource_own simpLangG0 resource);
    runtime_ghost_resource_update_cell : forall simpLangG0 resource,
      runtime_ghost_update_spec simpLangG0
        (runtime_ghost_resource_own simpLangG0 resource);
    runtime_ghost_resource_alloc : forall simpLangG0,
      (⊢ |={⊤}=> ∃ _ : runtime_ghost_resource simpLangG0, True)%I;
  }.

Definition runtimeG_with_ghost_resource {Σ : gFunctors}
    `{!FUpd (iPropI Σ)}
    (simpLangG0 : RuntimeLifting.simpLangG Σ)
    (invTokenG0 : RuntimeModel.invTokenG Σ)
    {ghost_namespace} (factory : runtime_ghost_resource_factory Σ ghost_namespace)
    (resource : runtime_ghost_resource _ _ factory simpLangG0) : runtimeG Σ := {|
  runtime_simpLangG := simpLangG0;
  runtime_invTokenG := invTokenG0;
  runtime_ghost_namespace := ghost_namespace;
  runtime_ghost_own := runtime_ghost_resource_own _ _ factory simpLangG0 resource;
  runtime_ghost_own_timeless :=
    runtime_ghost_resource_own_timeless _ _ factory simpLangG0 resource;
  runtime_ghost_alloc := runtime_ghost_resource_alloc_cell _ _ factory
    simpLangG0 resource;
  runtime_ghost_update := runtime_ghost_resource_update_cell _ _ factory
    simpLangG0 resource;
|}.

(** Constructors used by initialized adequacy after the corresponding names
    have been chosen by [own_alloc].  Keeping these as term definitions is
    essential: the finite invariant registry is inspected before [runtimeG]
    exists, and the resulting instances are assembled underneath the Iris
    allocation binders. *)
Section RuntimeInitialization.
Context {Σ : gFunctors} `{!invGS Σ} `{!RuntimeGhost.heapGpreS Σ}
  `{!RuntimeModel.invTokenGpreS Σ}.

Definition initialized_heapG
    (heap_name stack_name procedure_name ghost_domain_name : gname) :
    RuntimeGhost.heapG Σ := {|
  RuntimeGhost.heap_heap_inG := RuntimeGhost.heapGpreS_heap_inG;
  RuntimeGhost.heap_heap_name := heap_name;
  RuntimeGhost.heap_stack_inG := RuntimeGhost.heapGpreS_stack_inG;
  RuntimeGhost.heap_stack_name := stack_name;
  RuntimeGhost.heap_proctbl_inG := RuntimeGhost.heapGpreS_proctbl_inG;
  RuntimeGhost.heap_proctbl_name := procedure_name;
  RuntimeGhost.heap_ghostdom_inG := RuntimeGhost.heapGpreS_ghostdom_inG;
  RuntimeGhost.heap_ghostdom_name := ghost_domain_name;
|}.

Definition initialized_simpLangG
    (heap_name stack_name procedure_name ghost_domain_name : gname) :
    RuntimeLifting.simpLangG Σ :=
  RuntimeLifting.SimpLangG Σ invGS0
    (initialized_heapG heap_name stack_name procedure_name ghost_domain_name).

Definition initialized_invTokenG
    (names : RuntimeModel.inv_name -> gname) : RuntimeModel.invTokenG Σ :=
  RuntimeModel.InvTokenG Σ RuntimeModel.invtoken_pre_inG names.

(** Allocate a finite, pairwise-distinct family of empty invariant-token
    authorities. The list form is intentionally independent of the module's
    identifier type; initialized certified adequacy zips it with the finite
    registered-invariant enumeration. *)
Lemma allocate_invtoken_authority_names (count : nat) :
  (⊢ |={⊤}=> ∃ names : list gname,
    ⌜length names = count ∧ NoDup names⌝ ∗
    [∗ list] name ∈ names,
      @own Σ (authR RuntimeModel.inv_argsUR) RuntimeModel.invtoken_pre_inG name
        (● (∅ : RuntimeModel.inv_argsUR)))%I.
Proof.
  induction count as [|count IH].
  - iModIntro. iExists []. iSplit.
    { iPureIntro. split; constructor. }
    done.
  - iMod IH as (names) "[%Hnames Htokens]".
    iMod (own_alloc_cofinite (● (∅ : RuntimeModel.inv_argsUR))
      (list_to_set names)) as (name) "[%Hfresh Htoken]";
      first by apply auth_auth_valid.
    destruct Hnames as [Hlength Hnodup].
    iModIntro. iExists (name :: names). iSplit.
    { iPureIntro. split; simpl; first by rewrite Hlength.
      constructor; [by rewrite elem_of_list_to_set in Hfresh|exact Hnodup]. }
    iFrame.
Qed.

Lemma initialized_proc_table_fragments_persist
    (procedure_name : gname)
    (procedures : gmap RuntimeLang.proc_name RuntimeLang.proc) :
  (⊢ ([∗ map] name ↦ procedure ∈ procedures,
      @ghost_map_elem Σ RuntimeLang.proc_name RuntimeLang.proc _ _
        RuntimeGhost.heapGpreS_proctbl_inG procedure_name name (DfracOwn 1)
        procedure) ==∗
   ([∗ map] name ↦ procedure ∈ procedures,
      @ghost_map_elem Σ RuntimeLang.proc_name RuntimeLang.proc _ _
        RuntimeGhost.heapGpreS_proctbl_inG procedure_name name DfracDiscarded
        procedure))%I.
Proof.
  iIntros "Hfragments". iApply big_sepM_bupd.
  iApply (big_sepM_impl with "Hfragments").
  iIntros "!#" (name procedure) "_".
  iApply ghost_map_elem_persist.
Qed.

(** Allocate the complete simplified-language state interpretation together
    with the persistent fragments for its static procedure table. *)
Lemma initialized_state_resources_alloc
    (initial_state : RuntimeLang.state)
    (Hstate_wf : RuntimeGhost.state_wf initial_state) :
  (⊢ |={⊤}=> ∃ heap_name stack_name procedure_name ghost_domain_name,
    let heapG0 := initialized_heapG heap_name stack_name procedure_name
      ghost_domain_name in
    @RuntimeGhost.state_interp _ Σ heapG0 initial_state ∗
    ([∗ map] name ↦ procedure ∈ initial_state.(RuntimeLang.procs),
      @RuntimeGhost.proc_tbl_chunk _ Σ heapG0 name procedure))%I.
Proof.
  iMod (own_alloc (● RuntimeGhost.to_heapUR
    initial_state.(RuntimeLang.global_heap))) as (heap_name) "Hheap".
  { apply auth_auth_valid. intros address.
    rewrite /RuntimeGhost.to_heapUR lookup_fmap.
    destruct (initial_state.(RuntimeLang.global_heap) !! address) eqn:Haddress;
      try rewrite Haddress; simpl.
    - rewrite Some_valid pair_valid. split; [apply frac_valid_1|done].
    - exact I. }
  iMod (own_alloc (● RuntimeGhost.to_stackR initial_state.(RuntimeLang.stack)))
    as (stack_name) "Hstack".
  { apply auth_auth_valid. intros stack_id.
    rewrite /RuntimeGhost.to_stackR lookup_fmap.
    destruct (initial_state.(RuntimeLang.stack) !! stack_id); simpl; exact I. }
  iMod (ghost_map_alloc initial_state.(RuntimeLang.procs))
    as (procedure_name) "[Hprocedures Hfragments]".
  iMod (own_alloc (● (∅ : RuntimeGhost.ghost_domUR)))
    as (ghost_domain_name) "Hdomain"; first by apply auth_auth_valid.
  iMod (initialized_proc_table_fragments_persist procedure_name
    initial_state.(RuntimeLang.procs) with "Hfragments") as "#Hfragments".
  iModIntro. iExists heap_name, stack_name, procedure_name, ghost_domain_name.
  simpl. iFrame "Hfragments".
  rewrite /RuntimeGhost.state_interp /RuntimeGhost.heap_interp
    /RuntimeGhost.proc_tbl_interp /RuntimeGhost.stack_interp
    /RuntimeGhost.ghost_dom_interp.
  cbn [initialized_heapG].
  iSplitL "Hheap"; first iExact "Hheap".
  iSplitL "Hprocedures"; first iExact "Hprocedures".
  iSplitL "Hstack"; first iExact "Hstack".
  iSplit.
  - iExists ∅. rewrite gset_to_gmap_empty.
    iSplitL "Hdomain"; first iExact "Hdomain".
    iPureIntro. intros address Hmember.
    exfalso. exact (not_elem_of_empty address Hmember).
  - iPureIntro. exact Hstate_wf.
Qed.

(** One allocation transaction for all inputs used to construct the dynamic
    runtime bundle. Module initialization specializes [token_names] to its
    finite invariant enumeration and forms [runtimeG]. *)
Lemma initialized_runtime_resources_alloc
    (initial_state : RuntimeLang.state)
    (Hstate_wf : RuntimeGhost.state_wf initial_state)
    (token_count : nat) {ghost_namespace}
    (factory : runtime_ghost_resource_factory Σ ghost_namespace) :
  (⊢ |={⊤}=> ∃ heap_name stack_name procedure_name ghost_domain_name
      (token_names : list gname),
    ⌜length token_names = token_count ∧ NoDup token_names⌝ ∗
    let heapG0 := initialized_heapG heap_name stack_name procedure_name
      ghost_domain_name in
    let simpLangG0 := initialized_simpLangG heap_name stack_name procedure_name
      ghost_domain_name in
    ∃ ghost_resource : runtime_ghost_resource _ _ factory simpLangG0,
      @RuntimeGhost.state_interp _ Σ heapG0 initial_state ∗
      ([∗ map] name ↦ procedure ∈ initial_state.(RuntimeLang.procs),
        @RuntimeGhost.proc_tbl_chunk _ Σ heapG0 name procedure) ∗
      ([∗ list] token_name ∈ token_names,
        @own Σ (authR RuntimeModel.inv_argsUR) RuntimeModel.invtoken_pre_inG token_name
          (● (∅ : RuntimeModel.inv_argsUR))))%I.
Proof.
  iMod (initialized_state_resources_alloc initial_state Hstate_wf)
    as (heap_name stack_name procedure_name ghost_domain_name)
      "[Hstate #Hprocedures]".
  iMod (allocate_invtoken_authority_names token_count)
    as (token_names) "[%Htoken_names Htokens]".
  set (simpLangG0 := initialized_simpLangG heap_name stack_name procedure_name
    ghost_domain_name).
  iMod (runtime_ghost_resource_alloc _ _ factory simpLangG0)
    as (ghost_resource) "_".
  iModIntro.
  iExists heap_name, stack_name, procedure_name, ghost_domain_name, token_names.
  iSplit; first done. simpl. iExists ghost_resource. iFrame.
  iExact "Hprocedures".
Qed.

End RuntimeInitialization.

End WithSignature.

(** Iris resources are ordinary section variables, so the definitions below
    apply to a [runtimeG] value assembled after [own_alloc]. *)
Module ConcreteModelCore.
Import RuntimeErasure.

Section WithSignature.
Context {RAs : RAConfig} {Logic : Assertion.LogicSignature} {Cost : AnalysisView.LeafCost}.
(** Proof-only statements may be distributed across a conditional without
    changing the generated runtime statement. The operational refinement uses
    this equality for an invariant unfold/fold pair: branch selection happens
    first, and only the selected arm enters the Iris invariant. *)
Lemma runtime_stmt_distribute_erased_before_if {Γ}
    (names : named_context Γ) stack
    (before : stmt Γ) condition
    (then_branch else_branch : stmt Γ) :
  runtime_stmt names stack before = runtime_noop ->
  runtime_stmt names stack
    (TSeq before
      (TIf condition then_branch else_branch)) =
  runtime_stmt names stack
    (TIf condition
      (TSeq before then_branch)
      (TSeq before else_branch)).
Proof.
  intros Hbefore. simpl. rewrite Hbefore. reflexivity.
Qed.

Corollary runtime_stmt_distribute_unfold_before_if {Γ}
    (names : named_context Γ) stack
    invariant arguments condition
    (then_branch else_branch : stmt Γ) :
  runtime_stmt names stack
    (TSeq (TUnfold invariant arguments)
      (TIf condition then_branch else_branch)) =
  runtime_stmt names stack
    (TIf condition
      (TSeq (TUnfold invariant arguments)
        then_branch)
      (TSeq (TUnfold invariant arguments)
        else_branch)).
Proof.
  apply runtime_stmt_distribute_erased_before_if. reflexivity.
Qed.

Lemma runtime_stmt_distribute_erased_around_if {Γ}
    (names : named_context Γ) stack
    (before after : stmt Γ) condition (then_branch else_branch : stmt Γ) :
  runtime_stmt names stack before = runtime_noop ->
  runtime_stmt names stack after = runtime_noop ->
  runtime_stmt names stack
    (TSeq before
      (TSeq
        (TIf condition then_branch else_branch) after)) =
  runtime_stmt names stack
    (TIf condition
      (TSeq before
        (TSeq then_branch after))
      (TSeq before
        (TSeq else_branch after))).
Proof.
  intros Hbefore Hafter. simpl. rewrite Hbefore Hafter.
  rewrite !runtime_seq_noop_l !runtime_seq_noop_r. reflexivity.
Qed.

Corollary runtime_stmt_distribute_unfold_fold_if {Γ}
    (names : named_context Γ) stack
    invariant unfold_arguments fold_arguments condition
    (then_branch else_branch : stmt Γ) :
  runtime_stmt names stack
    (TSeq (TUnfold invariant unfold_arguments)
      (TSeq
        (TIf condition then_branch else_branch)
        (TFold invariant fold_arguments))) =
  runtime_stmt names stack
    (TIf condition
      (TSeq (TUnfold invariant unfold_arguments)
        (TSeq then_branch
          (TFold invariant fold_arguments)))
      (TSeq (TUnfold invariant unfold_arguments)
        (TSeq else_branch
          (TFold invariant fold_arguments)))).
Proof.
  apply runtime_stmt_distribute_erased_around_if; reflexivity.
Qed.

(** Soundness condition for the leaf costs at the concrete runtime
    boundary.  Proof-only leaves must erase to the terminal
    statement; a leaf classified as one atomic step must translate to an
    Iris-atomic runtime statement.  Non-atomic leaves need no additional witness because the
    analysis already rejects them while an invariant is open.  Trusted
    [TAtomic] blocks are structural certificates rather than leaves and are
    handled by the framework's trusted-atomic refinement assumption. *)
Definition runtime_cost_model_sound : Prop :=
  forall Γ (names : named_context Γ) stack (statement : stmt Γ),
    RegionSyntax.view statement = AnalysisView.ViewLeaf ->
    match AnalysisView.leaf_cost Γ statement with
    | GenericRegions.Atomicity.NoStep =>
        runtime_stmt names stack statement = runtime_noop
    | GenericRegions.Atomicity.AtomicStep =>
        @Atomic RuntimeLang.simp_lang WeaklyAtomic
          (runtime_stmt names stack statement)
    | GenericRegions.Atomicity.NonAtomicStep
    | GenericRegions.Atomicity.ProcedureCallStep _ _
    | GenericRegions.Atomicity.ProcedureSpawnStep _ => True
    end.

(** A typed declaration and a runtime procedure-table entry denote the same
    executable procedure when their frame layouts agree and translating the
    typed body yields the registered runtime body at every fresh stack id.
    The universal stack-id equation is the small-step execution boundary used
    by [wp_call], [wp_call_nostore], and [wp_spawn]. *)
Record runtime_procedure_registration {Γ F}
    (procedure : typed_procedure Γ F) (entry : RuntimeLang.proc) : Prop := {
  registered_procedure_name :
    RuntimeLang.proc_name_val entry =
      procedure_name (procedure_identity _ _ procedure);
  registered_procedure_arguments :
    RuntimeLang.proc_args entry = runtime_procedure_arguments procedure;
  registered_procedure_locals :
    RuntimeLang.proc_local_vars entry = runtime_procedure_locals procedure;
  registered_arguments_nodup :
    NoDup (RuntimeLang.proc_args entry).*1;
  registered_locals_nodup :
    NoDup (RuntimeLang.proc_local_vars entry).*1;
  registered_arguments_locals_disjoint :
    (RuntimeLang.proc_args entry).*1 ## (RuntimeLang.proc_local_vars entry).*1;
  registered_return_local :
    "#ret_val" ∈ (RuntimeLang.proc_local_vars entry).*1;
  registered_procedure_body : forall stack,
    runtime_stmt (runtime_procedure_names procedure) stack
      (procedure_body _ _ procedure) =
    RuntimeLang.proc_stmt entry stack;
}.

Definition packed_runtime_procedure_registration
    (procedure : packed_typed_procedure) (entry : RuntimeLang.proc) : Prop :=
  match procedure with
  | existT Γ (existT F typed) =>
      @runtime_procedure_registration Γ F typed entry
  end.

Fixpoint tval_list_to_list {ts} (values : tval_list ts) :
    list RuntimeLang.val :=
  match values with
  | TVNil => []
  | TVCons head tail => tval_to_val head :: tval_list_to_list tail
  end.

Lemma procedure_argument_frame_lookup {Γ F}
    (names : named_context Γ) (variables : pvar_list Γ F)
    (values : tval_list F) (frame : RuntimeLang.stack_frame) :
  Forall2 (fun variable value =>
    frame.(RuntimeLang.locals) !! variable = Some value)
    (runtime_formal_declarations names variables).*1
    (tval_list_to_list values) ->
  forall t (formal_variable : formal F t),
    frame.(RuntimeLang.locals) !!
      runtime_variable names (lookup_pvar_list variables formal_variable) =
    Some (tval_to_val (formal_env_of_values values t formal_variable)).
Proof.
  revert values. induction variables;
    intros values Hframe value_type formal_variable;
    dependent destruction values; dependent destruction formal_variable.
  all: inversion Hframe as [|? ? ? ? Hhead Htail]; subst.
  - rewrite lookup_pvar_list_here. rewrite formal_env_of_values_here.
    exact Hhead.
  - rewrite lookup_pvar_list_there. rewrite formal_env_of_values_there.
    apply IHvariables. exact Htail.
Qed.

Theorem procedure_entry_frame_corresponds {Γ F}
    (caller_valuation : symbol_valuation) (procedure : typed_procedure Γ F)
    (values : tval_list (Assertion.procedure_args F))
    (frame : RuntimeLang.stack_frame) :
  procedure_wf procedure ->
  Forall2 (fun variable value =>
    frame.(RuntimeLang.locals) !! variable = Some value)
    (runtime_procedure_arguments procedure).*1
    (tval_list_to_list values) ->
  (forall variable type,
    (variable, type) ∈ runtime_procedure_locals procedure ->
    exists value,
      frame.(RuntimeLang.locals) !! variable = Some value /\
      RuntimeLang.val_has_typ value type) ->
  dom frame.(RuntimeLang.locals) =
    list_to_set (runtime_procedure_arguments procedure).*1 ∪
      list_to_set (runtime_procedure_locals procedure).*1 ->
  exists callee_valuation : symbol_valuation,
    constant_symbols_agree caller_valuation callee_valuation /\
    stack_corresponds (runtime_procedure_names procedure)
      (formal_env_of_values values) empty_binder_env callee_valuation
      (procedure_entry_store _ _ procedure) frame /\
    dom frame.(RuntimeLang.locals) =
      list_to_set (runtime_variables (runtime_procedure_names procedure)).
Proof.
  intros Hwf Harguments Hlocals Hdom.
  destruct (procedure_frame_entry_symbol_valuation_exist caller_valuation procedure frame
    Hlocals) as (callee_valuation & Hagree & Hlocal).
  exists callee_valuation. split; [exact Hagree|]. split.
  - intros t variable.
    destruct (in_dec Nat.eq_dec (member_index variable)
      (pvar_list_indices (procedure_formal_variables _ _ procedure)))
    as [Hformal | Hnot].
    + destruct (pvar_list_index_member
      (procedure_formal_variables _ _ procedure) variable Hformal)
      as (formal_variable & Hvariable).
    subst variable.
    unfold procedure_entry_store, canonical_procedure_entry_store.
    rewrite lookup_canonical_entry_store_present.
      * cbn [interp_ref].
        apply procedure_argument_frame_lookup.
        unfold runtime_procedure_names.
        rewrite runtime_formal_declarations_rename_other;
          [exact Harguments | exact (procedure_return_slot_local _ Hwf)].
      * exact (procedure_formal_slots_unique _ Hwf).
    + unfold procedure_entry_store, canonical_procedure_entry_store.
      rewrite lookup_canonical_entry_store_absent; [|exact Hnot].
      cbn [interp_ref]. apply Hlocal. exact Hnot.
  - rewrite Hdom. apply runtime_procedure_declaration_names_cover. exact Hwf.
Qed.

Lemma runtime_expr_list_sound {Γ F Δ ts} (names : named_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (frame : RuntimeLang.stack_frame)
    (expressions : pexpr_list Γ ts) (values : tval_list ts) :
  stack_corresponds names formals binders valuation store frame ->
  interp_expr_list formals binders valuation
    (IR.symbolize_expr_list store expressions) = Some values ->
  Forall2 (fun expression value =>
    RuntimeLang.expr_step expression frame (RuntimeLang.Val value))
    (runtime_expr_list names expressions) (tval_list_to_list values).
Proof.
  intros Hstack. revert values.
  induction expressions; intros values Hvalues; dependent destruction values;
    simpl in Hvalues.
  - constructor.
  - destruct (interp_expr formals binders valuation
      (IR.symbolize_expr store p)) eqn:Hhead; [|discriminate].
    destruct (interp_expr_list formals binders valuation
      (IR.symbolize_expr_list store expressions)) eqn:Htail;
      [|discriminate].
    inversion Hvalues; subst. constructor.
    + eapply runtime_expr_sound; eauto.
    + eapply IHexpressions; eauto.
      dependent destruction H1. reflexivity.
Qed.

Definition tval_to_rich_val {t} (value : tval t) : RuntimeModel.val :=
  match value with
  | VBool boolean => RuntimeModel.LitBool boolean
  | VInt integer => RuntimeModel.LitInt integer
  | VRef location => RuntimeModel.LitLoc (RuntimeLang.Loc location)
  | VUnit => RuntimeModel.LitUnit
  | VRA resource => RuntimeModel.LitRAElem
      (@existT string
        (fun name => ra_base.RA_carrier (RuntimeLang.ra_map name))
        _ resource)
  end.

Fixpoint tval_list_to_rich_list {ts} (values : tval_list ts) :
    list RuntimeModel.val :=
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
    named_context Γ -> gmap RuntimeLang.var RuntimeLang.val.
Proof.
  destruct store as [|head_type tail_context value tail].
  - intros names. dependent destruction names. exact ∅.
  - intros names.
    dependent destruction names.
    exact (<[name := tval_to_val value]>
      (@concrete_locals_by_store tail_context tail names)).
Defined.

Definition concrete_locals {Γ} (names : named_context Γ)
    (store : concrete_store Γ) : gmap RuntimeLang.var RuntimeLang.val :=
  concrete_locals_by_store store names.

Lemma concrete_locals_interp_lookup {Γ F Δ} (names : named_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) :
  NoDup (runtime_variables names) ->
  forall t (variable : pvar Γ t),
    concrete_locals names (interp_store formals binders valuation store) !!
        runtime_variable names variable =
      Some (tval_to_val
        (interp_ref formals binders valuation (lookup_store store t variable))).
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
    (procedure : typed_procedure Γ F)
    (formals : formal_env (Assertion.procedure_args F))
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ (Assertion.procedure_args F) Δ) :
  NoDup (runtime_variables (runtime_procedure_names procedure)) ->
  concrete_locals (runtime_procedure_names procedure)
      (interp_store formals binders valuation store) !! "#ret_val" =
    Some (tval_to_val (interp_ref formals binders valuation
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
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (frame : RuntimeLang.stack_frame) :
  NoDup (runtime_variables names) ->
  stack_corresponds names formals binders valuation store frame ->
  dom frame.(RuntimeLang.locals) = list_to_set (runtime_variables names) ->
  frame = RuntimeLang.StackFrame
    (concrete_locals names (interp_store formals binders valuation store)).
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
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (target : pvar Γ t)
    (value : tval t) :
  NoDup (runtime_variables names) ->
  concrete_locals names
      (interp_store formals (binder_cons value binders) valuation
        (IR.update_store_with_bound store target)) =
    <[runtime_variable names target := tval_to_val value]>
      (concrete_locals names (interp_store formals binders valuation store)).
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
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) :
  NoDup (runtime_variables names) ->
  stack_corresponds names formals binders valuation store
    (RuntimeLang.StackFrame
      (concrete_locals names (interp_store formals binders valuation store))).
Proof.
  intros Hnames t variable.
  apply concrete_locals_interp_lookup. exact Hnames.
Qed.

Record stack_context_data (Γ : context) := StackContext {
  runtime_stack_id : RuntimeLang.stack_id;
  runtime_names : named_context Γ;
  runtime_names_nodup : NoDup (runtime_variables runtime_names);
}.

Definition stack_context : context -> Type := stack_context_data.

Definition empty_stack_context : stack_context [].
Proof. refine (StackContext [] 0%Z NCNil _). constructor. Defined.

Section WithRuntime.
Context {Σ : gFunctors} `{RG : !runtimeG Σ}.

Local Instance core_simpLangG : RuntimeLifting.simpLangG Σ :=
  runtime_simpLangG.
Local Instance core_invTokenG : RuntimeModel.invTokenG Σ :=
  runtime_invTokenG.
Local Instance core_heapG : RuntimeGhost.heapG Σ :=
  RuntimeLifting.simpLangG_gen_heapG.
Local Instance core_irisG : irisGS RuntimeLang.simp_lang Σ :=
  RuntimeLifting.simpLang_irisG.
Local Existing Instance weakestpre.wp'.
Local Instance core_invtoken_inG : inG Σ (authR RuntimeModel.inv_argsUR) :=
  @RuntimeModel.invtoken_inG _ Σ core_invTokenG.

Definition core_stack_own Γ (runtime : stack_context Γ)
    (store : concrete_store Γ) : iProp Σ :=
  RuntimeGhost.stack_frame_own (runtime_stack_id _ runtime)
    (RuntimeLang.StackFrame (concrete_locals (runtime_names _ runtime) store)).

Lemma core_stack_own_exclusive Γ (runtime : stack_context Γ)
    (left right : concrete_store Γ) :
  core_stack_own Γ runtime left ∗ core_stack_own Γ runtime right ⊢ False.
Proof.
  unfold core_stack_own.
  iIntros "[Hleft Hright]".
  iApply (RuntimeGhost.stack_frame_own_exclusive with "Hleft Hright").
Qed.

Local Notation stack_own := core_stack_own.
Local Notation concrete_heapG := core_heapG.
Local Notation concrete_irisG := core_irisG.
Local Notation concrete_invtoken_inG := core_invtoken_inG.

Lemma runtime_stack_frame_corresponds {Γ F Δ}
    (runtime : stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) :
  stack_corresponds (runtime_names _ runtime) formals binders valuation store
    (RuntimeLang.StackFrame
      (concrete_locals (runtime_names _ runtime)
        (interp_store formals binders valuation store))).
Proof.
  intros t variable. apply concrete_locals_interp_lookup.
  apply runtime_names_nodup.
Qed.

Definition core_field_own field
    (location : tval TRef) (chunk : tval (Assertion.field_type field)) :
    iProp Σ :=
  match location with
  | VRef address =>
      RuntimeGhost.heap_maps_to (RuntimeLang.Loc address)
        (field_name field) 1 (tval_to_val chunk)
  end.

Definition core_ghost_own field
    (location : tval TRef) (chunk : tval (Assertion.field_type field)) :
    iProp Σ :=
  runtime_ghost_own field location chunk.

Global Instance ghost_own_timeless field location chunk :
  Timeless (core_ghost_own field location chunk) :=
  runtime_ghost_own_timeless field location chunk.

Definition core_invariant_own invariant
    (values : tval_list (Assertion.invariant_args invariant)) : iProp Σ :=
  @own Σ (authR RuntimeModel.inv_argsUR) core_invtoken_inG
    (RuntimeModel.invtoken_names (invariant_name invariant))
    (◯ ({[tval_list_to_rich_list values]} : gset (list RuntimeModel.val))).

Local Notation field_own := core_field_own.
Local Notation ghost_own := core_ghost_own.
Local Notation invariant_own := core_invariant_own.

Definition runtime_wp (mask : coPset) (statement : RuntimeLang.runtime_stmt)
    (post : RuntimeLang.val -> iProp Σ) : iProp Σ :=
  @wp _ _ _ _
    (@weakestpre.wp' HasLc RuntimeLang.simp_lang Σ concrete_irisG)
    NotStuck mask statement post.

Definition invariant_mask (mask : Hoare.mask) : coPset :=
  set_fold (fun invariant result =>
    result ∪ ↑(invariant_namespace invariant)) ∅ mask.

Definition runtime_mask (mask : Hoare.mask) : coPset :=
  invariant_mask mask ∪ ↑ghost_heap_namespace.

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
    ↑(invariant_namespace invariant) ∪ invariant_mask mask.
Proof.
  unfold invariant_mask.
  rewrite (set_fold_union_strong (=)
    (fun invariant result =>
      result ∪ ↑(invariant_namespace invariant)) ∅
    ({[invariant]} : Hoare.mask) mask).
  - rewrite set_fold_singleton.
    replace (∅ ∪ ↑invariant_namespace invariant) with
      ((fun result : coPset =>
          ↑invariant_namespace invariant ∪ result) ∅)
      by set_solver.
    rewrite (set_fold_comm_acc
      (fun invariant' result =>
        result ∪ ↑(invariant_namespace invariant'))
      (fun result => ↑invariant_namespace invariant ∪ result)
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
      ↑(invariant_namespace invariant).
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
  (↑(invariant_namespace invariant) : coPset) ##
    invariant_mask mask.
Proof.
  induction mask using set_ind_L.
  - rewrite invariant_mask_empty. set_solver.
  - intros Hnotin. rewrite invariant_mask_union_singleton.
    have Hneq : invariant ≠ x by set_solver.
    pose proof (invariant_namespaces_disjoint invariant x Hneq) as Hleft.
    have Hright := IHmask ltac:(set_solver).
    exact (proj2 (disjoint_union_r _ _ _) (conj Hleft Hright)).
Qed.

Lemma invariant_namespace_subset_runtime_mask invariant (mask : Hoare.mask) :
  invariant ∈ mask ->
  ↑(invariant_namespace invariant) ⊆ runtime_mask mask.
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
  (↑ghost_heap_namespace : coPset) ## invariant_mask mask.
Proof.
  induction mask using set_ind_L.
  - rewrite invariant_mask_empty. apply disjoint_empty_r.
  - rewrite invariant_mask_union_singleton. apply disjoint_union_r. split.
    + symmetry. apply invariant_ghost_namespace_disjoint.
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
  have Hghost : (↑ghost_heap_namespace : coPset) ##
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
      ↑(invariant_namespace invariant).
Proof.
  intros Hin. unfold runtime_mask.
  have Hmask : mask = {[invariant]} ∪ (mask ∖ {[invariant]}).
  { apply set_eq. intros other.
    rewrite elem_of_union elem_of_singleton elem_of_difference
      elem_of_singleton. split.
    - intros Hother. destruct (decide (other = invariant)); [left|right]; done.
    - intros [->|[Hother _]]; assumption. }
  have Hfold : invariant_mask mask =
      ↑(invariant_namespace invariant) ∪
        invariant_mask (mask ∖ {[invariant]}).
  { exact (eq_trans (f_equal invariant_mask Hmask)
      (invariant_mask_union_singleton invariant
        (mask ∖ {[invariant]}))). }
  rewrite Hfold.
  have Hinv := invariant_mask_disjoint invariant (mask ∖ {[invariant]})
    ltac:(set_solver).
  have Hghost := invariant_ghost_namespace_disjoint invariant.
  rewrite !difference_union_distr_l_L difference_diag_L.
  rewrite (difference_disjoint_L (invariant_mask (mask ∖ {[invariant]}))
    (↑(invariant_namespace invariant) : coPset)); last by symmetry.
  rewrite (difference_disjoint_L
    (↑ghost_heap_namespace : coPset)
    (↑(invariant_namespace invariant) : coPset));
    last by symmetry.
  rewrite (left_id_L _ _). reflexivity.
Qed.

Lemma runtime_mask_insert invariant (mask : Hoare.mask) :
  runtime_mask (mask ∪ {[invariant]}) =
    runtime_mask mask ∪
      ↑(invariant_namespace invariant).
Proof.
  unfold runtime_mask.
  have Hcomm : mask ∪ {[invariant]} = {[invariant]} ∪ mask.
  { apply set_eq. intros other. rewrite !elem_of_union !elem_of_singleton.
    tauto. }
  have Hfold : invariant_mask (mask ∪ {[invariant]}) =
      ↑(invariant_namespace invariant) ∪ invariant_mask mask.
  { exact (eq_trans (f_equal invariant_mask Hcomm)
      (invariant_mask_union_singleton invariant mask)). }
  rewrite Hfold. apply set_eq. intros name. rewrite !elem_of_union. tauto.
Qed.

Lemma invariant_namespace_disjoint_runtime_mask invariant (mask : Hoare.mask) :
  invariant ∉ mask ->
  (↑(invariant_namespace invariant) : coPset) ## runtime_mask mask.
Proof.
  intros Hnotin. unfold runtime_mask.
  apply disjoint_union_r. split.
  - apply invariant_mask_disjoint. exact Hnotin.
  - apply invariant_ghost_namespace_disjoint.
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
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (target : pvar Γ t)
    (expression : pexpr Γ t) (mask : coPset) :
  stack_own Γ runtime (interp_store formals binders valuation store) ⊢
  runtime_wp mask
    (RuntimeLang.RTAssign
      (runtime_variable (runtime_names _ runtime) target)
      (runtime_expr (runtime_names _ runtime) expression)
      (runtime_stack_id _ runtime))
    (fun result =>
      (⌜result = RuntimeLang.LitUnit⌝ ∗
       ∃ value,
         ⌜interp_program_expr formals binders valuation store expression =
           Some value⌝ ∗
         stack_own Γ runtime
           (interp_store formals (binder_cons value binders) valuation
             (IR.update_store_with_bound store target)))%I).
Proof.
  iIntros "Hstack". unfold runtime_wp.
  iEval (unfold stack_own) in "Hstack".
  destruct (interp_expr_total formals binders valuation
    (IR.symbolize_expr store expression)) as [value Hvalue].
  iApply (RuntimeLifting.wp_assign
    (runtime_stack_id _ runtime)
    (RuntimeLang.StackFrame
      (concrete_locals (runtime_names _ runtime)
        (interp_store formals binders valuation store)))
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
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) field (base : pexpr Γ TRef)
    (expression : pexpr Γ (Assertion.field_type field))
    (location : tval TRef) (old_value : tval (Assertion.field_type field))
    (mask : coPset) :
  interp_program_expr formals binders valuation store base = Some location ->
  stack_own Γ runtime (interp_store formals binders valuation store) ∗
    field_own field location old_value ⊢
  runtime_wp mask
    (RuntimeLang.RTFldWr (runtime_expr (runtime_names _ runtime) base)
      (field_name field)
      (runtime_expr (runtime_names _ runtime) expression)
      (runtime_stack_id _ runtime))
    (fun result =>
      (⌜result = RuntimeLang.LitUnit⌝ ∗
       ∃ new_value,
         ⌜interp_program_expr formals binders valuation store expression =
           Some new_value⌝ ∗
         stack_own Γ runtime (interp_store formals binders valuation store) ∗
         field_own field location new_value)%I).
Proof.
  intros Hlocation. iIntros "[Hstack Hfield]". unfold runtime_wp.
  iEval (unfold stack_own) in "Hstack".
  destruct (interp_program_expr formals binders valuation store expression)
    as [new_value|] eqn:Hvalue.
  2: exfalso; destruct (interp_expr_total formals binders valuation
        (IR.symbolize_expr store expression)) as [new_value Htotal];
      unfold interp_program_expr in Hvalue; congruence.
  dependent destruction location. iEval (unfold field_own) in "Hfield".
  iApply (RuntimeLifting.wp_heap_wr_expr
    (runtime_stack_id _ runtime)
    (RuntimeLang.StackFrame
      (concrete_locals (runtime_names _ runtime)
        (interp_store formals binders valuation store)))
    (runtime_expr (runtime_names _ runtime) base)
    (runtime_expr (runtime_names _ runtime) expression)
    (tval_to_val new_value) (RuntimeLang.Loc location)
    (field_name field) (tval_to_val old_value) mask
    with "[Hstack Hfield]").
  { iFrame. iPureIntro. split.
    - exact (runtime_expr_sound (runtime_names _ runtime) formals binders valuation
        store _ base (VRef location)
        (runtime_stack_frame_corresponds runtime formals binders valuation store)
        Hlocation).
    - exact (runtime_expr_sound (runtime_names _ runtime) formals binders valuation
        store _ expression new_value
        (runtime_stack_frame_corresponds runtime formals binders valuation store)
        Hvalue). }
  iNext. iIntros "[Hstack [Hfield Hcredit]]". iSplit; first done.
  iExists new_value. iSplit; first done.
  unfold stack_own, field_own. simpl. iFrame.
Qed.

Lemma runtime_field_read_wp {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) field
    (target : pvar Γ (Assertion.field_type field)) (base : pexpr Γ TRef)
    (location : tval TRef) (chunk : tval (Assertion.field_type field))
    (mask : coPset) :
  interp_program_expr formals binders valuation store base = Some location ->
  stack_own Γ runtime (interp_store formals binders valuation store) ∗
    field_own field location chunk ⊢
  runtime_wp mask
    (RuntimeLang.RTFldRd
      (runtime_variable (runtime_names _ runtime) target)
      (runtime_expr (runtime_names _ runtime) base)
      (field_name field) (runtime_stack_id _ runtime))
    (fun result =>
      (⌜result = RuntimeLang.LitUnit⌝ ∗
       ∃ value,
         ⌜value = chunk⌝ ∗
         stack_own Γ runtime
           (interp_store formals (binder_cons value binders) valuation
             (IR.update_store_with_bound store target)) ∗
         field_own field location chunk)%I).
Proof.
  intros Hlocation. iIntros "[Hstack Hfield]". unfold runtime_wp.
  iEval (unfold stack_own) in "Hstack".
  dependent destruction location. iEval (unfold field_own) in "Hfield".
  iApply (RuntimeLifting.wp_heap_rd
    (runtime_stack_id _ runtime)
    (RuntimeLang.StackFrame
      (concrete_locals (runtime_names _ runtime)
        (interp_store formals binders valuation store)))
    (field_name field)
    (runtime_expr (runtime_names _ runtime) base)
    (tval_to_val chunk) (RuntimeLang.Loc location)
    (runtime_variable (runtime_names _ runtime) target) mask 1%Qp
    with "[Hstack Hfield]").
  { iFrame. iPureIntro.
    exact (runtime_expr_sound (runtime_names _ runtime) formals binders valuation
      store _ base (VRef location)
      (runtime_stack_frame_corresponds runtime formals binders valuation store)
      Hlocation). }
  iNext. iIntros "[Hstack [Hfield Hcredit]]". iSplit; first done.
  iExists chunk. iSplit; first done. unfold stack_own, field_own. simpl.
  rewrite concrete_locals_update_store.
  iFrame. apply runtime_names_nodup.
Qed.

Fixpoint allocated_physical_fields_own {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (location : tval TRef)
    (fields : list (field_init Γ)) : iProp Σ :=
  match fields with
  | [] => True%I
  | FieldInit field expression :: fields' =>
      (∃ value,
        ⌜interp_program_expr formals binders valuation store expression =
          Some value⌝ ∗
        field_own field location value ∗
        allocated_physical_fields_own runtime formals binders valuation store location
          fields')%I
  end.

Fixpoint allocated_ghost_fields_own {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (location : tval TRef)
    (fields : list (ghost_field_init Γ)) : iProp Σ :=
  match fields with
  | [] => True%I
  | GhostFieldInit resource field Hfield expression :: fields' =>
      (∃ value : RAValues.ra_carrier resource,
        ⌜interp_program_expr formals binders valuation store expression =
          Some (VRA value)⌝ ∗
        ghost_own field location
          (eq_rect (TRA resource) tval (VRA value)
            (Assertion.field_type field) (eq_sym Hfield)) ∗
        allocated_ghost_fields_own runtime formals binders valuation store location
          fields')%I
  end.

Definition allocated_fields_own {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (location : tval TRef)
    (fields : list (field_init Γ)) : iProp Σ :=
  (allocated_physical_fields_own runtime formals binders valuation store location
      (physical_field_initializers fields) ∗
   allocated_ghost_fields_own runtime formals binders valuation store location
      (ghost_field_initializers fields))%I.

Definition ghost_initializers_semantically_valid {Γ F Δ}
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) : Prop :=
  Forall (fun initialization =>
    match initialization with
    | GhostFieldInit resource _ _ expression => forall value,
        interp_program_expr formals binders valuation store expression =
          Some (VRA value) ->
        @ra_base.valid _ (ra_base.RA_inst (RuntimeLang.ra_map resource)) value
    end) fields.

Lemma ghost_dom_frag_names_cons address field names :
  field ∉ names ->
  RuntimeGhost.ghost_dom_frag (list_to_set (map
    (RuntimeLang.heap_addr_constr (RuntimeLang.Loc address)) (field :: names))) ⊣⊢
  RuntimeGhost.ghost_dom_frag
    {[RuntimeLang.heap_addr_constr (RuntimeLang.Loc address) field]} ∗
  RuntimeGhost.ghost_dom_frag (list_to_set (map
    (RuntimeLang.heap_addr_constr (RuntimeLang.Loc address)) names)).
Proof.
  intros Hfresh. simpl. rewrite RuntimeGhost.ghost_dom_frag_insert; first done.
  rewrite elem_of_list_to_set. intros Hmember.
  apply elem_of_list_fmap in Hmember as [other [Heq Hmember]].
  injection Heq as Heq. apply Hfresh. subst other. exact Hmember.
Qed.

Lemma allocated_ghost_fields_alloc {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) fields address E :
  NoDup (runtime_packed_ghost_field_names fields) ->
  ghost_initializers_semantically_valid formals binders valuation store fields ->
  (↑runtime_ghost_namespace : coPset) ⊆ E ->
  @RuntimeGhost.ghost_dom_frag _ Σ core_heapG
    (list_to_set (map (RuntimeLang.heap_addr_constr (RuntimeLang.Loc address))
      (runtime_packed_ghost_field_names fields))) -∗
  |={E}=> allocated_ghost_fields_own runtime formals binders valuation store
    (VRef address) fields.
Proof.
  intros Hnames Hvalid Hmask.
  induction fields as [|[resource field Hfield expression] fields IH].
  - iIntros "_". iModIntro. done.
  - inversion Hnames as [|? ? Hfresh Hnames']; subst.
    inversion Hvalid as [|? ? Hhead_valid Hvalid']; subst.
    simpl.
    destruct (interp_expr_total formals binders valuation
      (IR.symbolize_expr store expression)) as [value Hvalue].
    dependent destruction value.
    iIntros "Hdomain".
    iEval (rewrite (ghost_dom_frag_names_cons address (field_name field)
      (runtime_packed_ghost_field_names fields) Hfresh)) in "Hdomain".
    iDestruct "Hdomain" as "[Hone Htail]".
    iMod (IH Hnames' Hvalid' with "Htail") as "Htail".
    have Hchunk_valid : @ra_base.valid _
        (ra_base.RA_inst (RuntimeLang.ra_map resource)) value.
    { apply (Hhead_valid value). exact Hvalue. }
    iMod (runtime_ghost_alloc E field resource (field_name field)
      address value Hfield Hmask Hchunk_valid with "Hone") as "Hown".
    iModIntro. iExists value. iFrame. iPureIntro. exact Hvalue.
Qed.

Inductive field_values_match {Γ F Δ}
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) :
    list (field_init Γ) -> list (RuntimeLang.fld_name * RuntimeLang.val) -> Prop :=
| FieldValuesNil : field_values_match formals binders valuation store [] []
| FieldValuesCons field expression fields value values :
    interp_program_expr formals binders valuation store expression = Some value ->
    field_values_match formals binders valuation store fields values ->
    field_values_match formals binders valuation store
      (FieldInit field expression :: fields)
      ((field_name field, tval_to_val value) :: values).

Lemma field_values_match_exists {Γ F Δ} (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
  exists values, field_values_match formals binders valuation store fields values.
Proof.
  induction fields as [|[field expression] fields IH].
  - exists []. constructor.
  - destruct IH as [values Hvalues].
    destruct (interp_expr_total formals binders valuation
      (IR.symbolize_expr store expression)) as [value Hvalue].
    exists ((field_name field, tval_to_val value) :: values).
    constructor; [exact Hvalue|exact Hvalues].
Qed.

Lemma field_values_match_steps {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) fields values :
  field_values_match formals binders valuation store fields values ->
  Forall2 (fun initializer field_value =>
    fst initializer = fst field_value /\
    RuntimeLang.expr_step (snd initializer)
      (RuntimeLang.StackFrame
        (concrete_locals (runtime_names _ runtime)
          (interp_store formals binders valuation store)))
      (RuntimeLang.Val (snd field_value)))
    (runtime_field_initializers (runtime_names _ runtime) fields) values.
Proof.
  intros Hmatch. induction Hmatch; simpl; constructor; [|exact IHHmatch].
  split; first reflexivity.
  exact (runtime_expr_sound (runtime_names _ runtime) formals binders valuation
    store _ expression value
    (runtime_stack_frame_corresponds runtime formals binders valuation store) H).
Qed.

Lemma field_values_match_names {Γ F Δ} formals binders valuation
    (store : symbolic_store Γ F Δ) fields values :
  field_values_match formals binders valuation store fields values ->
  values.*1 = map (fun initialization =>
    field_name (field_init_id initialization)) fields.
Proof.
  intros Hmatch. induction Hmatch; simpl.
  - reflexivity.
  - f_equal. exact IHHmatch.
Qed.

Lemma runtime_field_names_nodup {Γ} (fields : list (field_init Γ)) :
  NoDup (map field_init_id fields) ->
  NoDup (map (fun initialization =>
    field_name (field_init_id initialization)) fields).
Proof.
  induction fields as [|initialization fields IH]; simpl; intros Hnodup.
  - constructor.
  - inversion Hnodup as [|? ? Hfresh Htail]. constructor.
    + intros Hmember. apply elem_of_list_fmap in Hmember.
      destruct Hmember as [other [Heq Hother]].
      apply field_name_injective in Heq. apply Hfresh.
      apply elem_of_list_fmap. exists other. split; assumption.
    + apply IH. exact Htail.
Qed.

Lemma runtime_physical_field_ids_nodup {Γ}
    (fields : list (field_init Γ)) :
  NoDup (map field_init_id fields) ->
  NoDup (map field_init_id (physical_field_initializers fields)).
Proof.
  induction fields as [|initialization fields IH]; simpl; intros Hnodup.
  - constructor.
  - inversion Hnodup as [|? ? Hfresh Htail]; subst.
    unfold physical_field_initializers. simpl.
    destruct (field_init_is_ghost initialization); simpl.
    + apply IH. exact Htail.
    + constructor; last (apply IH; exact Htail).
      intros Hmember. apply Hfresh.
      apply elem_of_list_fmap in Hmember as [other [Heq Hmember]].
      apply elem_of_list_fmap. exists other. split; [exact Heq |].
      rewrite elem_of_list_In in Hmember.
      apply List.filter_In in Hmember. destruct Hmember as [Hmember _].
      rewrite elem_of_list_In. exact Hmember.
Qed.

Lemma runtime_packed_ghost_field_names_nodup {Γ}
    (fields : list (ghost_field_init Γ)) :
  NoDup (map ghost_field_init_id fields) ->
  NoDup (runtime_packed_ghost_field_names fields).
Proof.
  induction fields as [|[resource field Hfield expression] fields IH];
    simpl; intros Hnodup.
  - constructor.
  - inversion Hnodup as [|? ? Hfresh Htail]; subst. constructor.
    + intros Hmember. apply elem_of_list_fmap in Hmember as
      [other [Heq Hother]].
      destruct other as [other_resource other_field other_type other_expression].
      simpl in Heq, Hother.
      apply field_name_injective in Heq. subst other_field. apply Hfresh.
      apply elem_of_list_fmap.
      exists (GhostFieldInit other_resource field other_type other_expression).
      split; [reflexivity | exact Hother].
    + apply IH. exact Htail.
Qed.

Lemma field_values_match_own {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) fields values address :
  field_values_match formals binders valuation store fields values ->
  RuntimeLifting.field_list_to_iprop (RuntimeLang.Loc address) values ⊢
    allocated_physical_fields_own runtime formals binders valuation store (VRef address)
      fields.
Proof.
  intros Hmatch. induction Hmatch; simpl.
  - iIntros "_". done.
  - iIntros "[Hfield Hfields]". iExists value. iSplit; first done.
    unfold field_own. iFrame. iApply IHHmatch. iExact "Hfields".
Qed.

Lemma runtime_allocation_wp {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (target : pvar Γ TRef)
    (fields : list (field_init Γ)) (mask : coPset) :
  NoDup (map field_init_id fields) ->
  NoDup (map ghost_field_init_id (ghost_field_initializers fields)) ->
  ghost_initializers_require_physical fields ->
  ghost_initializers_semantically_valid formals binders valuation store
    (ghost_field_initializers fields) ->
  (↑runtime_ghost_namespace : coPset) ⊆ mask ->
  stack_own Γ runtime (interp_store formals binders valuation store) ⊢
  runtime_wp mask
    (RuntimeLang.RTAlloc (runtime_variable (runtime_names _ runtime) target)
      (runtime_physical_field_initializers (runtime_names _ runtime) fields)
      (runtime_stack_id _ runtime))
    (fun result =>
      (⌜result = RuntimeLang.LitUnit⌝ ∗
       ∃ address : Z,
         stack_own Γ runtime
           (interp_store formals (binder_cons (VRef address) binders) valuation
             (IR.update_store_with_bound store target)) ∗
         allocated_fields_own runtime formals binders valuation store
           (VRef address) fields)%I).
Proof.
  intros Hfields Hghostfields Hphysical Hvalid Hmask.
  iIntros "Hstack". unfold runtime_wp.
  iApply wp_fupd.
  iEval (unfold stack_own) in "Hstack".
  destruct (field_values_match_exists formals binders valuation store
    (physical_field_initializers fields))
    as [values Hvalues].
  iApply (RuntimeLifting.wp_alloc_expr
    (runtime_stack_id _ runtime)
    (RuntimeLang.StackFrame
      (concrete_locals (runtime_names _ runtime)
        (interp_store formals binders valuation store)))
    (runtime_physical_field_initializers (runtime_names _ runtime) fields)
    values (runtime_ghost_field_names fields)
    (runtime_variable (runtime_names _ runtime) target) mask
    with "Hstack").
  - exact (field_values_match_steps runtime formals binders valuation store
      (physical_field_initializers fields) values Hvalues).
  - rewrite (field_values_match_names formals binders valuation store
      (physical_field_initializers fields) values Hvalues).
    apply runtime_field_names_nodup.
    exact (runtime_physical_field_ids_nodup fields Hfields).
  - unfold runtime_ghost_field_names.
    apply runtime_packed_ghost_field_names_nodup.
    exact Hghostfields.
  - intros Hghostnames.
    have Hghosts : not (ghost_field_initializers fields =
        (nil : list (ghost_field_init Γ))).
    { intros Hempty. apply Hghostnames.
      unfold runtime_ghost_field_names. rewrite Hempty. reflexivity. }
    have Hphysical_fields := Hphysical Hghosts.
    intros Hempty. subst values. inversion Hvalues; subst.
    apply Hphysical_fields. symmetry. exact H0.
  - iNext. iIntros "Hpost".
    iDestruct "Hpost" as (location) "[Hstack [Hfields [Hghost Hcredit]]]".
    destruct location as [address].
    iMod (allocated_ghost_fields_alloc runtime formals binders valuation store
      (ghost_field_initializers fields) address mask with "Hghost") as "Hghost".
    { apply runtime_packed_ghost_field_names_nodup. exact Hghostfields. }
    { exact Hvalid. }
    { exact Hmask. }
    iModIntro. iSplit; first done. iExists address.
    iSplitL "Hstack".
    + unfold stack_own. simpl. rewrite concrete_locals_update_store.
      iExact "Hstack". apply runtime_names_nodup.
    + iSplitL "Hfields".
      * iApply (field_values_match_own runtime formals binders valuation store
          (physical_field_initializers fields) values address Hvalues).
        iExact "Hfields".
      * iExact "Hghost".
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

(** Term-level view of the concrete assertion model.  This value can be
    formed from a [runtimeG] term whose names were allocated in an adequacy
    proof. *)
Definition core_semantic_data : Translation.semantic_config_data (iPropI Σ) := {|
  Translation.data_bi_affine := _;
  Translation.data_stack_context := stack_context;
  Translation.data_empty_stack_context := empty_stack_context;
  Translation.data_stack_own := core_stack_own;
  Translation.data_stack_own_exclusive := core_stack_own_exclusive;
  Translation.data_field_own := core_field_own;
  Translation.data_ghost_own := core_ghost_own;
  Translation.data_invariant_own := core_invariant_own;
|}.

End WithRuntime.
End WithSignature.
End ConcreteModelCore.

(** Term-level operation interfaces for an initialized runtime.  A proof may
    construct either record after choosing its [runtimeG] names. *)
Module TermControlOperations.
Section WithSignature.
Context {RAs : RAConfig} {Logic : Assertion.LogicSignature}
  {Cost : AnalysisView.LeafCost}.
Section WithModel.
Context {PROP : bi} (Model : Translation.semantic_config_data PROP).
Let term_bi_affine : BiAffine PROP :=
  @Translation.data_bi_affine _ _ PROP Model.
Local Existing Instance term_bi_affine.
Local Notation iProp := (bi_car PROP).

Record procedure_operations_data := ProcedureOperationsData {
  term_procedure_wp : forall Γ, Translation.data_stack_context Model Γ ->
    stmt Γ -> Hoare.mask -> Hoare.mask -> iProp -> iProp;
  term_procedure_mono : forall Γ runtime statement mask_pre mask_post P Q,
    (P ⊢ Q) -> term_procedure_wp Γ runtime statement mask_pre mask_post P ⊢
      term_procedure_wp Γ runtime statement mask_pre mask_post Q;
  term_procedure_frame : forall Γ runtime statement mask_pre mask_post P R,
    term_procedure_wp Γ runtime statement mask_pre mask_post P ∗ R ⊢
      term_procedure_wp Γ runtime statement mask_pre mask_post (P ∗ R)
}.

Record control_operations_data := ControlOperationsData {
  term_operation_wp : forall Γ, Translation.data_stack_context Model Γ ->
    stmt Γ -> Hoare.mask -> Hoare.mask -> iProp -> iProp;
  term_operation_mono : forall Γ runtime statement mask_pre mask_post P Q,
    (P ⊢ Q) -> term_operation_wp Γ runtime statement mask_pre mask_post P ⊢
      term_operation_wp Γ runtime statement mask_pre mask_post Q;
  term_operation_frame : forall Γ runtime statement mask_pre mask_post P R,
    term_operation_wp Γ runtime statement mask_pre mask_post P ∗ R ⊢
      term_operation_wp Γ runtime statement mask_pre mask_post (P ∗ R);
  term_atomic_wp : forall Γ, Translation.data_stack_context Model Γ ->
    stmt Γ -> Hoare.mask -> Hoare.mask -> iProp -> iProp;
  term_atomic_mono : forall Γ runtime body mask_pre mask_post P Q,
    (P ⊢ Q) -> term_atomic_wp Γ runtime body mask_pre mask_post P ⊢
      term_atomic_wp Γ runtime body mask_pre mask_post Q;
  term_atomic_frame : forall Γ runtime body mask_pre mask_post P R,
    term_atomic_wp Γ runtime body mask_pre mask_post P ∗ R ⊢
      term_atomic_wp Γ runtime body mask_pre mask_post (P ∗ R);
  term_atomic_intro : forall Γ runtime body mask_pre mask_post P,
    P ⊢ term_atomic_wp Γ runtime body mask_pre mask_post P
}.
End WithModel.
End WithSignature.
End TermControlOperations.

(** Concrete term-level operation model.  [RG] is an ordinary section
    variable, so [control_operations] can be formed after the
    adequacy proof has allocated all required ghost names. *)
Module ConcreteControlCore.
Module Model := ConcreteModelCore.
Section WithSignature.
Context {RAs : RAConfig} {Logic : Assertion.LogicSignature} {Cost : AnalysisView.LeafCost}.
Section WithRuntime.
Context {Σ : gFunctors} `{RG : !runtimeG Σ}.
Local Instance core_simpLangG : RuntimeLifting.simpLangG Σ :=
  runtime_simpLangG.
Local Instance core_invTokenG : RuntimeModel.invTokenG Σ := runtime_invTokenG.
Local Instance core_heapG : RuntimeGhost.heapG Σ :=
  RuntimeLifting.simpLangG_gen_heapG.
Local Instance core_irisG : irisGS RuntimeLang.simp_lang Σ :=
  @Model.core_irisG _ _ Σ RG.
Local Existing Instance weakestpre.wp'.
Local Notation iProp := (iProp Σ).

Definition semantic_data : Translation.semantic_config_data (iPropI Σ) :=
  @Model.core_semantic_data _ _ Σ RG.

Definition procedure_wp {Γ} (runtime : Model.stack_context Γ)
    (statement : stmt Γ) (mask_pre mask_post : Hoare.mask)
    (post : iProp) : iProp :=
  match statement with
  | TCall _ _ _ | TSpawn _ _ =>
      Model.runtime_wp (Model.runtime_mask mask_pre)
        (RuntimeErasure.runtime_stmt (Model.runtime_names _ runtime)
          (Model.runtime_stack_id _ runtime) statement)
        (fun result =>
          (⌜result = RuntimeLang.LitUnit⌝ ∗
           |={Model.runtime_mask mask_pre,
               Model.runtime_mask mask_post}=> post)%I)
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
    iPoseProof (@wp_frame_r HasLc RuntimeLang.simp_lang Σ core_irisG
      NotStuck (Model.runtime_mask mask_pre) _
      (fun result =>
        (⌜result = RuntimeLang.LitUnit⌝ ∗
         |={Model.runtime_mask mask_pre, Model.runtime_mask mask_post}=> P)%I)
      R with "[$Hwp $HR]") as "Hwp";
    iApply (wp_mono with "Hwp");
    iIntros (result) "[[%Hresult Hpost] HR]"; iSplit; first done;
    iMod "Hpost"; iModIntro; iFrame.
Qed.

Definition procedure_operations :
    @TermControlOperations.procedure_operations_data _ _ (iPropI Σ)
      semantic_data :=
  @TermControlOperations.ProcedureOperationsData _ _ (iPropI Σ) semantic_data
    (@procedure_wp) procedure_mono procedure_frame.

Definition operation_wp {Γ} (Procedures :
    @TermControlOperations.procedure_operations_data _ _ (iPropI Σ)
      semantic_data) (runtime : Model.stack_context Γ)
    (statement : stmt Γ) (mask_pre mask_post : Hoare.mask)
    (post : iProp) : iProp :=
  match statement with
  | TCall _ _ _ | TSpawn _ _ =>
      TermControlOperations.term_procedure_wp semantic_data Procedures Γ
        runtime statement mask_pre mask_post post
  | TUnfold _ _ | TFold _ _ =>
      (|={Model.runtime_mask mask_pre, Model.runtime_mask mask_post}=> post)%I
  | _ => False%I
  end.

Lemma operation_mono Procedures Γ runtime statement mask_pre mask_post P Q :
  (P ⊢ Q) ->
  @operation_wp Γ Procedures runtime statement mask_pre mask_post P ⊢
    @operation_wp Γ Procedures runtime statement mask_pre mask_post Q.
Proof.
  intros HPQ. unfold operation_wp. destruct statement; simpl;
    try (apply (TermControlOperations.term_procedure_mono semantic_data
      Procedures); exact HPQ); try reflexivity.
  all: iIntros "HP"; iMod "HP"; iModIntro; iApply HPQ; iExact "HP".
Qed.

Lemma operation_frame Procedures Γ runtime statement mask_pre mask_post P R :
  @operation_wp Γ Procedures runtime statement mask_pre mask_post P ∗ R ⊢
    @operation_wp Γ Procedures runtime statement mask_pre mask_post (P ∗ R).
Proof.
  unfold operation_wp. destruct statement; simpl;
    try apply (TermControlOperations.term_procedure_frame semantic_data
      Procedures); try (iIntros "[H _]"; done).
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

Definition control_operations (Procedures :
    @TermControlOperations.procedure_operations_data _ _ (iPropI Σ)
      semantic_data) :
    @TermControlOperations.control_operations_data _ _ (iPropI Σ)
      semantic_data :=
  @TermControlOperations.ControlOperationsData _ _ (iPropI Σ) semantic_data
    (fun Γ => @operation_wp Γ Procedures) (operation_mono Procedures)
    (operation_frame Procedures) (@atomic_wp) atomic_mono atomic_frame
    atomic_intro.

Definition concrete_control_operations :
    @TermControlOperations.control_operations_data _ _ (iPropI Σ)
      semantic_data := control_operations procedure_operations.
End WithRuntime.
End WithSignature.
End ConcreteControlCore.

Import Translation.Assertions.
Module TermSemanticLeafContracts.
Module RI := Hoare.ResourceHoare.
Section WithContracts.
Context {RAs : RAConfig} {Logic : Assertion.LogicSignature}
  {Contracts : Hoare.ResourceHoare.ResourceContractEnv}.
Section WithModel.
Context {PROP : bi} (Model : Translation.semantic_config_data PROP).
Context `{!FUpd PROP}.
Local Notation iProp := (bi_car PROP).

Record semantic_leaf_contracts_data := SemanticLeafContractsData {
  term_predicates : symbol_valuation ->
    Translation.TermSemantics.predicate_semantics;
  term_predicates_timeless : forall valuation predicate values,
    Timeless (term_predicates valuation predicate values);
  term_predicates_stable : forall left_valuation right_valuation,
    constant_symbols_agree left_valuation right_valuation ->
    forall predicate values,
      term_predicates left_valuation predicate values ≡
      term_predicates right_valuation predicate values;
  (** The instantiated predicate body agrees with the abstract predicate
      symbol.  Stated over the resource core: the instantiation is a total
      function of the arguments, so there is no relation to destruct and no
      reindexing step, and the obligation never mentions the assertion
      representation. *)
  term_predicate_instantiation_valid : forall {F Δ}
      (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
      predicate (expressions : expr_list F Δ (Assertion.predicate_args predicate)),
    Translation.TermSemantics.interp_core Model (term_predicates valuation)
      formals binders valuation
      (RI.instantiated_predicate predicate expressions) ≡
    Translation.TermSemantics.interp_core Model (term_predicates valuation)
      formals binders valuation
      (Translation.Resource.CPredicate predicate expressions);
}.
End WithModel.
End WithContracts.
End TermSemanticLeafContracts.

(** Term-level interface for the one region primitive whose implementation is
    specific to invariant transitions.  Keeping it separate lets adequacy
    construct it after allocating [runtimeG]. *)
Module TermInvariantRegionOperations.
Section WithSignature.
Context {RAs : RAConfig} {Logic : Assertion.LogicSignature}
  {Cost : AnalysisView.LeafCost}.
Section WithModel.
Context {PROP : bi} (Model : GenericRegions.region_model_data PROP).
Local Notation iProp := (bi_car PROP).

Record invariant_region_operations_data := InvariantRegionOperationsData {
  term_invariant_operation_wp : forall Γ,
    GenericRegions.term_region_stack_context Model Γ ->
    GenericRegions.term_region_ambient_mask Model ->
    GenericRegions.Atomicity.analysis_state -> stmt Γ ->
    GenericRegions.Atomicity.analysis_state -> iProp -> iProp;
  term_invariant_operation_mono : forall Γ runtime ambient entry statement exit P Q,
    (P ⊢ Q) ->
    term_invariant_operation_wp Γ runtime ambient entry statement exit P ⊢
      term_invariant_operation_wp Γ runtime ambient entry statement exit Q;
  term_invariant_operation_frame : forall Γ runtime ambient entry statement exit P R,
    term_invariant_operation_wp Γ runtime ambient entry statement exit P ∗ R ⊢
      term_invariant_operation_wp Γ runtime ambient entry statement exit (P ∗ R)
}.
End WithModel.
End WithSignature.
End TermInvariantRegionOperations.

(** Dynamic counterpart of [OperationalGenericRegionPrimitives].  It turns
    the term-level control and invariant-operation records into the generic
    certificate interpreter primitives. *)
Module OperationalGenericRegionPrimitivesCore.
Module Control := ConcreteControlCore.
Module Model := Control.Model.

Section WithSignature.
Context {RAs : RAConfig} {Logic : Assertion.LogicSignature} {Cost : AnalysisView.LeafCost}.
(** Construct a runtime stack context through the model's public alias, so
    clients need not rely on reduction through the nested [Control.Model]
    alias. *)
Definition make_stack_context {Γ} (stack_id : RuntimeLang.stack_id)
    (names : named_context Γ) (Hnames : NoDup (RuntimeErasure.runtime_variables names)) :
    Model.stack_context Γ :=
  @Model.StackContext Γ stack_id names Hnames.

Lemma active_runtime_mask_same_open ambient entry exit :
  GenericRegions.Atomicity.analysis_open entry =
    GenericRegions.Atomicity.analysis_open exit ->
  Model.active_runtime_mask ambient entry =
    Model.active_runtime_mask ambient exit.
Proof. apply Model.active_runtime_mask_same_open. Qed.

Lemma invariant_mask_union_singleton invariant mask :
  Model.invariant_mask ({[invariant]} ∪ mask) =
    ↑(invariant_namespace invariant) ∪ Model.invariant_mask mask.
Proof. apply Model.invariant_mask_union_singleton. Qed.

Lemma active_runtime_mask_access ambient entry invariant opened inner :
  GenericRegions.Atomicity.analysis_open opened =
    {[invariant]} ∪ GenericRegions.Atomicity.analysis_open entry ->
  GenericRegions.Atomicity.analysis_open inner =
    GenericRegions.Atomicity.analysis_open opened ->
  Model.active_runtime_mask ambient inner =
    Model.active_runtime_mask ambient entry ∖
      ↑(invariant_namespace invariant).
Proof.
  intros Hopened Hinner.
  rewrite (Model.active_runtime_mask_same_open ambient inner opened Hinner).
  apply Model.active_runtime_mask_open. exact Hopened.
Qed.

Section WithRuntime.
Context {Σ : gFunctors} `{RG : !runtimeG Σ}.
Local Instance core_simpLangG : RuntimeLifting.simpLangG Σ := runtime_simpLangG.
Local Instance core_invTokenG : RuntimeModel.invTokenG Σ := runtime_invTokenG.
Local Instance core_heapG : RuntimeGhost.heapG Σ :=
  RuntimeLifting.simpLangG_gen_heapG.
Local Instance core_irisG : irisGS RuntimeLang.simp_lang Σ :=
  @Model.core_irisG _ _ Σ RG.
Local Existing Instance weakestpre.wp'.
Local Notation iProp := (iProp Σ).

Definition semantic_data : Translation.semantic_config_data (iPropI Σ) :=
  @Control.semantic_data _ _ Σ RG.

Lemma semantic_stack_own_update {Γ F Δ t}
    (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (target : pvar Γ t) (value : tval t) :
  Translation.data_stack_own semantic_data runtime
      (interp_store formals (binder_cons value binders) valuation
        (IR.update_store_with_bound store target)) ⊣⊢
    RuntimeGhost.stack_frame_own (Model.runtime_stack_id _ runtime)
      (RuntimeLang.StackFrame
        (<[RuntimeErasure.runtime_variable (Model.runtime_names _ runtime) target :=
            RuntimeErasure.tval_to_val value]>
          (RuntimeLang.locals (RuntimeLang.StackFrame
            (Model.concrete_locals (Model.runtime_names _ runtime)
              (interp_store formals binders valuation store)))))).
Proof.
  unfold semantic_data, Control.semantic_data, Model.core_semantic_data.
  simpl. unfold Model.core_stack_own.
  rewrite Model.concrete_locals_update_store; [reflexivity|].
  apply Model.runtime_names_nodup.
Qed.
Definition region_model : GenericRegions.region_model_data (iPropI Σ) :=
  @GenericRegions.RegionModelData (iPropI Σ)
    (fun Γ => Model.stack_context Γ) RuntimeErasure.ambient_mask.

Lemma region_model_stack_context_eq Γ :
  GenericRegions.term_region_stack_context region_model Γ =
    Model.stack_context Γ.
Proof. reflexivity. Qed.

Lemma region_model_ambient_mask_eq :
  GenericRegions.term_region_ambient_mask region_model = RuntimeErasure.ambient_mask.
Proof. reflexivity. Qed.

Definition ambient_physical_leaf_wp {Γ} (runtime : Model.stack_context Γ)
    (ambient : coPset) (entry : GenericRegions.Atomicity.analysis_state)
    (statement : RuntimeLang.runtime_stmt) (post : iProp) : iProp :=
  Model.runtime_wp (Model.active_runtime_mask ambient entry) statement
    (fun result => (⌜result = RuntimeLang.LitUnit⌝ ∗ post)%I).

Definition ambient_leaf_wp {Γ} (runtime : Model.stack_context Γ)
    (ambient : coPset) (entry : GenericRegions.Atomicity.analysis_state)
    (statement : stmt Γ) (post : iProp) : iProp :=
  match statement with
  | TCall _ _ _ | TSpawn _ _ =>
      ambient_physical_leaf_wp runtime ambient entry
        (RuntimeErasure.runtime_stmt (Model.runtime_names _ runtime)
          (Model.runtime_stack_id _ runtime) statement) post
  | TDone | TAssert _ => post
  | TAssign target expression =>
      ambient_physical_leaf_wp runtime ambient entry
        (RuntimeLang.RTAssign
          (RuntimeErasure.runtime_variable (Model.runtime_names _ runtime) target)
          (RuntimeErasure.runtime_expr (Model.runtime_names _ runtime) expression)
          (Model.runtime_stack_id _ runtime)) post
  | TFieldRead field target base =>
      ambient_physical_leaf_wp runtime ambient entry
        (RuntimeLang.RTFldRd
          (RuntimeErasure.runtime_variable (Model.runtime_names _ runtime) target)
          (RuntimeErasure.runtime_expr (Model.runtime_names _ runtime) base)
          (field_name field) (Model.runtime_stack_id _ runtime)) post
  | TFieldWrite field base expression =>
      ambient_physical_leaf_wp runtime ambient entry
        (RuntimeLang.RTFldWr
          (RuntimeErasure.runtime_expr (Model.runtime_names _ runtime) base)
          (field_name field)
          (RuntimeErasure.runtime_expr (Model.runtime_names _ runtime) expression)
          (Model.runtime_stack_id _ runtime)) post
  | TAlloc target fields =>
      ambient_physical_leaf_wp runtime ambient entry
        (RuntimeLang.RTAlloc
          (RuntimeErasure.runtime_variable (Model.runtime_names _ runtime) target)
          (RuntimeErasure.runtime_physical_field_initializers
            (Model.runtime_names _ runtime) fields)
          (Model.runtime_stack_id _ runtime)) post
  | TGhostUpdate _ _ _ _ =>
      (|={Model.active_runtime_mask ambient entry}=> post)%I
  | TPredicateUnfold _ _ | TPredicateFold _ _ => post
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
  iPoseProof (@wp_frame_r HasLc RuntimeLang.simp_lang Σ core_irisG
    NotStuck (Model.active_runtime_mask ambient entry)
    statement (fun result => (⌜result = RuntimeLang.LitUnit⌝ ∗ P)%I) R
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

Definition operation_wp {Γ}
    (Operations : @TermControlOperations.control_operations_data _ _ (iPropI Σ)
      semantic_data)
    (InvariantOps :
      @TermInvariantRegionOperations.invariant_region_operations_data _ _ (iPropI Σ)
        region_model)
    (runtime : Model.stack_context Γ) (ambient : RuntimeErasure.ambient_mask)
    (entry : GenericRegions.Atomicity.analysis_state) (statement : stmt Γ)
    (exit : GenericRegions.Atomicity.analysis_state) (post : iProp) : iProp :=
  match RegionSyntax.view statement with
  | AnalysisView.ViewLeaf => ambient_leaf_wp runtime ambient entry statement post
  | AnalysisView.ViewUnfold _ | AnalysisView.ViewFold _ =>
      TermInvariantRegionOperations.term_invariant_operation_wp region_model
        InvariantOps Γ runtime ambient entry statement exit post
  | AnalysisView.ViewAtomic body =>
      TermControlOperations.term_atomic_wp semantic_data Operations Γ runtime body
        (GenericRegions.Atomicity.analysis_mask entry)
        (GenericRegions.Atomicity.analysis_mask exit) post
  | _ => False%I
  end.

Definition branch_wp {Γ}
    (runtime : Model.stack_context Γ) (_ : RuntimeErasure.ambient_mask)
    (entry : GenericRegions.Atomicity.analysis_state) (statement : stmt Γ)
    (_ _ : GenericRegions.Atomicity.analysis_state) (then_wp else_wp : iProp) : iProp :=
  match statement with
  | TIf _ _ _ => (then_wp ∨ else_wp)%I
  | _ => False%I
  end.

Lemma operation_mono Operations InvariantOps Γ runtime ambient entry statement exit P Q :
  (P ⊢ Q) ->
  @operation_wp Γ Operations InvariantOps runtime ambient entry statement exit P ⊢
    @operation_wp Γ Operations InvariantOps runtime ambient entry statement exit Q.
Proof.
  intros HPQ. unfold operation_wp, RegionSyntax.view.
  destruct statement; simpl; try exact HPQ; try reflexivity;
    try (apply ambient_leaf_mono; exact HPQ);
    try (apply (TermInvariantRegionOperations.term_invariant_operation_mono
      region_model InvariantOps); exact HPQ);
    try (apply (TermControlOperations.term_atomic_mono semantic_data Operations); exact HPQ).
  all: try (apply ambient_physical_leaf_mono; exact HPQ).
  all: try destruct target; simpl;
    try (apply ambient_physical_leaf_mono; exact HPQ).
  all: iIntros "HP"; iMod "HP"; iModIntro; iApply HPQ; iExact "HP".
Qed.

Lemma operation_frame Operations InvariantOps Γ runtime ambient entry statement exit P R :
  @operation_wp Γ Operations InvariantOps runtime ambient entry statement exit P ∗ R ⊢
    @operation_wp Γ Operations InvariantOps runtime ambient entry statement exit (P ∗ R).
Proof.
  unfold operation_wp, RegionSyntax.view. destruct statement; simpl;
    try reflexivity; try apply ambient_leaf_frame;
    try apply (TermInvariantRegionOperations.term_invariant_operation_frame
      region_model InvariantOps);
    try apply (TermControlOperations.term_atomic_frame semantic_data Operations);
    try (iIntros "[H _]"; done).
  all: try apply ambient_physical_leaf_frame.
  all: try destruct target; simpl; try apply ambient_physical_leaf_frame.
  all: iIntros "[HP HR]"; iMod "HP"; iModIntro; iFrame.
Qed.

Lemma branch_mono Γ runtime ambient entry statement then_exit else_exit P P' Q Q' :
  (P ⊢ P') -> (Q ⊢ Q') ->
  branch_wp (Γ := Γ) runtime ambient entry statement then_exit else_exit P Q ⊢
    branch_wp runtime ambient entry statement then_exit else_exit P' Q'.
Proof.
  intros HP HQ. unfold branch_wp. destruct statement; simpl; try reflexivity.
  iIntros "[HP|HQ]".
  - iLeft. iApply HP. iExact "HP".
  - iRight. iApply HQ. iExact "HQ".
Qed.

Lemma branch_frame Γ runtime ambient entry statement then_exit else_exit P Q R :
  branch_wp (Γ := Γ) runtime ambient entry statement then_exit else_exit P Q ∗ R ⊢
    branch_wp runtime ambient entry statement then_exit else_exit (P ∗ R) (Q ∗ R).
Proof.
  unfold branch_wp. destruct statement; simpl; try (iIntros "[H _]"; done).
  iIntros "[[HP|HQ] HR]"; [iLeft|iRight]; iFrame.
Qed.

Definition primitives (Operations :
    @TermControlOperations.control_operations_data _ _ (iPropI Σ) semantic_data)
    (InvariantOps :
      @TermInvariantRegionOperations.invariant_region_operations_data _ _ (iPropI Σ)
        region_model) :
    @GenericRegions.TermSemantics.region_primitives_data _ (iPropI Σ) region_model :=
  @GenericRegions.TermSemantics.RegionPrimitivesData _ (iPropI Σ) region_model
    (fun Γ => @operation_wp Γ Operations InvariantOps) (@branch_wp)
    (operation_mono Operations InvariantOps) (operation_frame Operations InvariantOps)
    branch_mono branch_frame.

(** The fancy-update record for invariant operations, stated against the
    interpreter's model. *)
Definition concrete_invariant_operation_wp {Γ} (_ : Model.stack_context Γ)
    (ambient : RuntimeErasure.ambient_mask) (entry : GenericRegions.Atomicity.analysis_state)
    (statement : stmt Γ) (exit : GenericRegions.Atomicity.analysis_state)
    (post : iProp) : iProp :=
  match statement with
  | TUnfold _ _ | TFold _ _ =>
      (|={Model.active_runtime_mask ambient entry,
           Model.active_runtime_mask ambient exit}=> post)%I
  | _ => False%I
  end.

Lemma concrete_invariant_operation_mono Γ runtime ambient entry statement exit P Q :
  (P ⊢ Q) ->
  @concrete_invariant_operation_wp Γ runtime ambient entry statement exit P ⊢
    @concrete_invariant_operation_wp Γ runtime ambient entry statement exit Q.
Proof.
  intros HPQ. unfold concrete_invariant_operation_wp.
  destruct statement; simpl; try reflexivity.
  all: iIntros "HP"; iMod "HP"; iModIntro; iApply HPQ; iExact "HP".
Qed.

Lemma concrete_invariant_operation_frame Γ runtime ambient entry statement exit P R :
  @concrete_invariant_operation_wp Γ runtime ambient entry statement exit P ∗ R ⊢
    @concrete_invariant_operation_wp Γ runtime ambient entry statement exit (P ∗ R).
Proof.
  unfold concrete_invariant_operation_wp. destruct statement; simpl;
    try (iIntros "[H _]"; done).
  all: iIntros "[HP HR]"; iMod "HP"; iModIntro; iFrame.
Qed.

Definition concrete_invariant_operations :
    @TermInvariantRegionOperations.invariant_region_operations_data _ _ (iPropI Σ)
      region_model :=
  @TermInvariantRegionOperations.InvariantRegionOperationsData _ _ (iPropI Σ)
    region_model (@concrete_invariant_operation_wp)
    concrete_invariant_operation_mono concrete_invariant_operation_frame.

Definition interpreter (Operations :
    @TermControlOperations.control_operations_data _ _ (iPropI Σ) semantic_data)
    (InvariantOps :
      @TermInvariantRegionOperations.invariant_region_operations_data _ _ (iPropI Σ)
        region_model) :
    @GenericRegions.TermSemantics.interpreter_data _ _ (iPropI Σ) region_model :=
  GenericRegions.TermSemantics.interpreter region_model
    (primitives Operations InvariantOps).
End WithRuntime.
End WithSignature.
End OperationalGenericRegionPrimitivesCore.

(** Fully concrete dynamic generic-region interpreter, suitable for a
    proof-time allocated [runtimeG] instance. *)
Module ConcreteGenericRegionExecutionCore.
Module Primitives := OperationalGenericRegionPrimitivesCore.
Module Control := Primitives.Control.
Section WithSignature.
Context {RAs : RAConfig} {Logic : Assertion.LogicSignature} {Cost : AnalysisView.LeafCost}.
Section WithRuntime.
Context {Σ : gFunctors} `{RG : !runtimeG Σ}.

Definition interpreter := @Primitives.interpreter _ _ _ Σ RG
  (@Control.concrete_control_operations _ _ Σ RG)
  (@Primitives.concrete_invariant_operations _ _ Σ RG).
End WithRuntime.
End WithSignature.
End ConcreteGenericRegionExecutionCore.

End Runtime.
