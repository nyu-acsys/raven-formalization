From Coq Require Import List String ZArith Program.Equality Lia
  Logic.ProofIrrelevance ClassicalEpsilon.
From stdpp Require Import countable gmap namespaces sets.

From iris.algebra Require Import auth gset.
From iris.base_logic Require Import fancy_updates.
From iris.base_logic.lib Require Import own invariants ghost_map.

From raven_iris.simp_raven_lang Require Import lang ghost_state inv_tokens.
From raven_iris.rich_raven_lang Require Import
  typed_core typed_analysis_view typed_assertion typed_ir
  typed_translation typed_validity typed_region.

Import ListNotations.
Import weakestpre.
Open Scope list_scope.

(** Concrete connection between the typed assertion semantics and Raven's
    existing Iris ghost state. *)
Module TypedRuntime.

Module Make (LegacyRAs : ra_base.RA_CONFIG)
    (Logic : TypedAssertion.LOGIC_SIGNATURE).

Module Legacy := InvTokens.Make LegacyRAs.
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

  Definition ra_id name : ra_carrier name :=
    @ra_base.ra_id (ra_base.RA_carrier (LegacyRAs.ra_map name))
      (ra_base.ra_inst_instance (LegacyRAs.ra_map name)).

  Definition ra_of_int name (value : Z) : ra_carrier name :=
    @ra_base.ra_of_int (ra_base.RA_carrier (LegacyRAs.ra_map name))
      (ra_base.ra_inst_instance (LegacyRAs.ra_map name)) value.

  Definition ra_valid name (value : ra_carrier name) : Prop :=
    @ra_base.valid _ (ra_base.ra_inst_instance (LegacyRAs.ra_map name)) value.

  Definition ra_fpu_allowed name (old_value new_value : ra_carrier name) : Prop :=
    @ra_base.fpuValid _ (ra_base.ra_inst_instance (LegacyRAs.ra_map name))
      old_value new_value.
End TypedRAs.

Module Validation := TypedValidity.Make TypedRAs Logic.
Module Translation := Validation.Translation.
Module IR := Translation.IR.
Module Assertions := Translation.Assertions.
Module Core := Translation.Core.
Import TypedCore TypedIR Core IR Translation.

(** Runtime representation of Raven's trusted atomic-block primitive.

    Atomic blocks are declarations about the modeled hardware substrate, not
    obligations attached to individual programs.  The framework therefore
    supplies their opaque transition uniformly.  Its semantic content is the
    global [term_trusted_atomic_runtime_refinement] assumption at the
    certified Iris boundary; examples neither define this relation nor prove
    a separate progress condition for it. *)
Axiom trusted_atomic_transition : forall {Γ},
  node_id -> stmt Γ -> LegacyLang.trusted_atomic_transition.

Module RegionSyntax <: TypedAnalysisView.ANALYSIS_SYNTAX.
  Definition statement := IR.stmt.
  Definition view {Γ} (statement : statement Γ) :=
    match statement with
    | TUnfold _ invariant _ => TypedAnalysisView.ViewUnfold invariant
    | TFold _ invariant _ => TypedAnalysisView.ViewFold invariant
    | TSeq _ first second => TypedAnalysisView.ViewSequence first second
    | TIf _ _ then_branch else_branch =>
        TypedAnalysisView.ViewConditional then_branch else_branch
    | TInvAccess invariant _ body =>
        TypedAnalysisView.ViewStructuredAccess invariant body
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

(** Public projection of analyzer-certificate uniqueness for clients of this
    instantiated runtime module. *)
Module CertificateFacts.
Lemma analysis_certificate_unique
    {Γ cost entry statement exit}
    (certificate1 certificate2 : GenericRegions.Atomicity.analysis_certificate
      cost Γ entry statement exit) :
  certificate1 = certificate2.
Proof.
  apply GenericRegions.analysis_certificate_unique.
Qed.
End CertificateFacts.

Definition tval_ghost_valid {t} (value : tval t) : Prop.
Proof.
  exact (tval_ra_valid value).
Defined.

Definition ghost_chunk_valid (field : field_id)
    (value : tval (Logic.field_type field)) : Prop :=
  tval_ghost_valid value.

(** Certificate for normalization output.  There is deliberately no raw
    unfold constructor.  A raw fold is admitted only when it allocates a
    fresh invariant; a fold that closes an open invariant must instead be
    represented by [StructuredInvAccess].  This is static evidence, not an
    operational or Iris interpretation.  The certificate lives in the
    shared runtime result so downstream modules use this runtime's single
    non-generative IR and analysis instances. *)
Module StructuredCertificates.

Inductive structured_certificate (cost : GenericRegions.Atomicity.cost_model) :
    forall Γ, GenericRegions.Atomicity.analysis_state -> stmt Γ ->
      GenericRegions.Atomicity.analysis_state -> Type :=
| StructuredLeaf Γ entry statement exit :
    RegionSyntax.view statement = TypedAnalysisView.ViewLeaf ->
    GenericRegions.Atomicity.take_step (cost Γ statement) entry = inr exit ->
    structured_certificate cost Γ entry statement exit
| StructuredFreshFold Γ entry node invariant arguments :
    invariant ∉ GenericRegions.Atomicity.analysis_open entry ->
    structured_certificate cost Γ entry (TFold node invariant arguments)
      (GenericRegions.Atomicity.fold_invariant invariant entry)
| StructuredSequence Γ entry node first middle second exit :
    structured_certificate cost Γ entry first middle ->
    structured_certificate cost Γ middle second exit ->
    structured_certificate cost Γ entry (TSeq node first second) exit
| StructuredConditional Γ entry node condition then_branch else_branch
    then_exit else_exit :
    structured_certificate cost Γ entry then_branch then_exit ->
    structured_certificate cost Γ entry else_branch else_exit ->
    GenericRegions.Atomicity.analysis_open then_exit =
      GenericRegions.Atomicity.analysis_open else_exit ->
    GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit ->
    structured_certificate cost Γ entry
      (TIf node condition then_branch else_branch)
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask then_exit ∩
          GenericRegions.Atomicity.analysis_mask else_exit)
        (GenericRegions.Atomicity.analysis_open then_exit)
        (GenericRegions.Atomicity.analysis_step_taken then_exit ||
          GenericRegions.Atomicity.analysis_step_taken else_exit)
        (GenericRegions.Atomicity.analysis_in_atomic then_exit))
| StructuredAtomic Γ entry node body outer inner :
    GenericRegions.Atomicity.take_step GenericRegions.Atomicity.AtomicStep entry =
      inr outer ->
    structured_certificate cost Γ
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask outer)
        (GenericRegions.Atomicity.analysis_open outer)
        (GenericRegions.Atomicity.analysis_step_taken outer) true)
      body inner ->
    GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open outer ->
    structured_certificate cost Γ entry (TAtomic node body)
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask inner)
        (GenericRegions.Atomicity.analysis_open inner)
        (GenericRegions.Atomicity.analysis_step_taken outer ||
          GenericRegions.Atomicity.analysis_step_taken inner)
        (GenericRegions.Atomicity.analysis_in_atomic outer))
| StructuredInvAccess Γ entry invariant arguments body opened inner :
    GenericRegions.Atomicity.open_invariant invariant entry = inr opened ->
    structured_certificate cost Γ opened body inner ->
    GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open opened ->
    structured_certificate cost Γ entry (TInvAccess invariant arguments body)
      (GenericRegions.Atomicity.fold_invariant invariant inner).

(** Logical Raven masks that may be needed while interpreting a structured
    certificate.  The footprint keeps both the masks and open sets at the
    certificate boundary, and exposes the footprints of every recursively
    certified child. *)
Fixpoint structured_certificate_footprint
    {cost Γ entry statement exit}
    (certificate : structured_certificate cost Γ entry statement exit) :
    gset inv_id :=
  GenericRegions.Atomicity.analysis_mask entry ∪
  GenericRegions.Atomicity.analysis_open entry ∪
  GenericRegions.Atomicity.analysis_mask exit ∪
  GenericRegions.Atomicity.analysis_open exit ∪
  match certificate with
  | StructuredSequence _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      structured_certificate_footprint first_certificate ∪
      structured_certificate_footprint second_certificate
  | StructuredConditional _ _ _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      structured_certificate_footprint then_certificate ∪
      structured_certificate_footprint else_certificate
  | StructuredAtomic _ _ _ _ _ _ _ _ body_certificate _ =>
      structured_certificate_footprint body_certificate
  | StructuredInvAccess _ _ _ _ _ _ _ _ _ body_certificate _ =>
      structured_certificate_footprint body_certificate
  | _ => ∅
  end.

Lemma structured_certificate_entry_subset_footprint
    {cost Γ entry statement exit}
    (certificate : structured_certificate cost Γ entry statement exit) :
  GenericRegions.Atomicity.analysis_mask entry ⊆
    structured_certificate_footprint certificate.
Proof.
  destruct certificate; simpl; intros candidate Hin.
  all: repeat rewrite elem_of_union; tauto.
Qed.

Lemma structured_certificate_exit_subset_footprint
    {cost Γ entry statement exit}
    (certificate : structured_certificate cost Γ entry statement exit) :
  GenericRegions.Atomicity.analysis_mask exit ⊆
    structured_certificate_footprint certificate.
Proof.
  destruct certificate; simpl; intros candidate Hin.
  all: repeat rewrite elem_of_union; tauto.
Qed.

End StructuredCertificates.

(** Canonical pairing used by certified-region soundness.  Unlike the legacy
    pairing in [typed_region], every component below refers to this runtime's
    single non-generative IR instance.  The explicit LIFO boundary stacks let
    the semantic induction split sequences without losing an accessor that
    was opened by the first component and is closed by the second. *)
Module CertifiedRegions
    (Contracts : Hoare.ResourceHoare.RESOURCE_CONTRACT_ENV_BASE).
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
    Γ node procedure
    (arguments : pexpr_list Γ (Logic.procedure_args procedure))
    (target : call_target Γ (Logic.procedure_return procedure)) entry exit :
  Atomicity.take_step
      (cost Γ (@TCall Γ node procedure arguments target))
      entry = inr exit ->
  Contracts.required_mask procedure ⊆ Atomicity.analysis_mask entry /\
  Contracts.granted_mask procedure ## Atomicity.analysis_open entry /\
  Atomicity.analysis_mask exit = Atomicity.analysis_mask entry ∪
    Contracts.granted_mask procedure /\
  Atomicity.analysis_open exit = Atomicity.analysis_open entry.
Proof.
  intros Hstep. specialize (Hcost Γ
    (@TCall Γ node procedure arguments target)).
  simpl in Hcost. rewrite Hcost in Hstep.
  exact (Atomicity.procedure_call_step_success _ _ _ _ Hstep).
Qed.

Lemma certified_spawn_step_effect cost
    (Hcost : procedure_cost_model_sound cost)
    Γ node procedure
    (arguments : pexpr_list Γ (Logic.procedure_args procedure)) entry exit :
  Atomicity.take_step
      (cost Γ (@TSpawn Γ node procedure arguments)) entry = inr exit ->
  Contracts.required_mask procedure ⊆ Atomicity.analysis_mask entry /\
  Atomicity.analysis_mask exit = Atomicity.analysis_mask entry /\
  Atomicity.analysis_open exit = Atomicity.analysis_open entry.
Proof.
  intros Hstep. specialize (Hcost Γ
    (@TSpawn Γ node procedure arguments)).
  simpl in Hcost. rewrite Hcost in Hstep.
  exact (Atomicity.procedure_spawn_step_success _ _ _ Hstep).
Qed.


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


End CertifiedRegions.

(** Resource-independent program configuration.  These choices are fixed by
    the Raven program and remain meaningful before Iris allocates any ghost
    names. *)
Module Type RUNTIME_CONFIGURATION.
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
End RUNTIME_CONFIGURATION.

Definition runtime_ghost_alloc_spec {Σ : gFunctors}
    (simpLangG0 : LegacyLifting.simpLangG Σ) (ghost_namespace : namespace)
    (ghost_own : forall field,
      tval TRef -> tval (Logic.field_type field) -> iProp Σ) : Prop :=
  forall E field resource_name field_name address chunk
    (Hfield : Logic.field_type field = TRA resource_name),
    (↑ghost_namespace : coPset) ⊆ E ->
    @ra_base.valid _ (ra_base.RA_inst (LegacyRAs.ra_map resource_name)) chunk ->
    (⊢ @LegacyGhost.ghost_dom_frag Σ
          (@LegacyLifting.simpLangG_gen_heapG Σ simpLangG0)
          {[LegacyLang.heap_addr_constr (LegacyLang.Loc address) field_name]} -∗
        @fupd (iPropI Σ)
          (@bi_fupd_fupd _ (@uPred_bi_fupd HasLc Σ
            (@LegacyLifting.simpLangG_invG Σ simpLangG0))) E E
          (ghost_own field (VRef address)
            (eq_rect (TRA resource_name) tval (VRA chunk)
              (Logic.field_type field) (eq_sym Hfield))))%I.

Definition runtime_ghost_update_spec {Σ : gFunctors}
    (simpLangG0 : LegacyLifting.simpLangG Σ)
    (ghost_own : forall field,
      tval TRef -> tval (Logic.field_type field) -> iProp Σ) : Prop :=
  forall E field location old_chunk new_chunk,
    tval_fpu_allowed old_chunk new_chunk ->
    ghost_own field location old_chunk ⊢
      |={E}=> ghost_own field location new_chunk.

(** Term-level resources chosen by adequacy.  In contrast to the old module
    interface, a value of this class can be constructed with names returned
    by [own_alloc] inside an Iris initialization proof. *)
Class runtimeG (Σ : gFunctors) := RuntimeG {
  runtime_simpLangG : LegacyLifting.simpLangG Σ;
  runtime_invTokenG : Legacy.invTokenG Σ;
  runtime_ghost_namespace : namespace;
  runtime_ghost_own : forall field,
    tval TRef -> tval (Logic.field_type field) -> iProp Σ;
  runtime_ghost_own_timeless : forall field location chunk,
    Timeless (runtime_ghost_own field location chunk);
  runtime_ghost_alloc : runtime_ghost_alloc_spec runtime_simpLangG
    runtime_ghost_namespace runtime_ghost_own;
  runtime_ghost_update : runtime_ghost_update_spec runtime_simpLangG
    runtime_ghost_own;
}.

(** Program-defined ghost ownership may itself require allocating an Iris
    invariant or authoritative camera before a [runtimeG] value can be
    assembled.  The implementation of that allocation belongs to the logic
    configuration, not to individual Raven programs.  Its result is an
    opaque proof-time handle; any persistent infrastructure needed by the
    resulting ownership predicate is established internally by
    [runtime_ghost_resource_alloc]. *)
Record runtime_ghost_resource_factory (Σ : gFunctors) `{!FUpd (iPropI Σ)}
    (ghost_namespace : namespace) :=
  RuntimeGhostResourceFactory {
    runtime_ghost_resource : LegacyLifting.simpLangG Σ -> Type;
    runtime_ghost_resource_own : forall simpLangG0,
      runtime_ghost_resource simpLangG0 -> forall field,
      tval TRef -> tval (Logic.field_type field) -> iProp Σ;
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
    (simpLangG0 : LegacyLifting.simpLangG Σ)
    (invTokenG0 : Legacy.invTokenG Σ)
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
Context {Σ : gFunctors} `{!invGS Σ} `{!LegacyGhost.heapGpreS Σ}
  `{!Legacy.invTokenGpreS Σ}.

Definition initialized_heapG
    (heap_name stack_name procedure_name ghost_domain_name : gname) :
    LegacyGhost.heapG Σ := {|
  LegacyGhost.heap_heap_inG := LegacyGhost.heapGpreS_heap_inG;
  LegacyGhost.heap_heap_name := heap_name;
  LegacyGhost.heap_stack_inG := LegacyGhost.heapGpreS_stack_inG;
  LegacyGhost.heap_stack_name := stack_name;
  LegacyGhost.heap_proctbl_inG := LegacyGhost.heapGpreS_proctbl_inG;
  LegacyGhost.heap_proctbl_name := procedure_name;
  LegacyGhost.heap_ghostdom_inG := LegacyGhost.heapGpreS_ghostdom_inG;
  LegacyGhost.heap_ghostdom_name := ghost_domain_name;
|}.

Definition initialized_simpLangG
    (heap_name stack_name procedure_name ghost_domain_name : gname) :
    LegacyLifting.simpLangG Σ :=
  LegacyLifting.SimpLangG Σ invGS0
    (initialized_heapG heap_name stack_name procedure_name ghost_domain_name).

Definition initialized_invTokenG
    (names : Legacy.inv_name -> gname) : Legacy.invTokenG Σ :=
  Legacy.InvTokenG Σ Legacy.invtoken_pre_inG names.

(** Allocate a finite, pairwise-distinct family of empty invariant-token
    authorities.  The list form is intentionally independent of the program's
    identifier type; initialized certified adequacy zips it with the finite
    registered-invariant enumeration. *)
Lemma allocate_invtoken_authority_names (count : nat) :
  (⊢ |={⊤}=> ∃ names : list gname,
    ⌜length names = count ∧ NoDup names⌝ ∗
    [∗ list] name ∈ names,
      @own Σ (authR Legacy.inv_argsUR) Legacy.invtoken_pre_inG name
        (● (∅ : Legacy.inv_argsUR)))%I.
Proof.
  induction count as [|count IH].
  - iModIntro. iExists []. iSplit.
    { iPureIntro. split; constructor. }
    done.
  - iMod IH as (names) "[%Hnames Htokens]".
    iMod (own_alloc_cofinite (● (∅ : Legacy.inv_argsUR))
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
    (procedures : gmap LegacyLang.proc_name LegacyLang.proc) :
  (⊢ ([∗ map] name ↦ procedure ∈ procedures,
      @ghost_map_elem Σ LegacyLang.proc_name LegacyLang.proc _ _
        LegacyGhost.heapGpreS_proctbl_inG procedure_name name (DfracOwn 1)
        procedure) ==∗
   ([∗ map] name ↦ procedure ∈ procedures,
      @ghost_map_elem Σ LegacyLang.proc_name LegacyLang.proc _ _
        LegacyGhost.heapGpreS_proctbl_inG procedure_name name DfracDiscarded
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
    (initial_state : LegacyLang.state)
    (Hstate_wf : LegacyGhost.state_wf initial_state) :
  (⊢ |={⊤}=> ∃ heap_name stack_name procedure_name ghost_domain_name,
    let heapG0 := initialized_heapG heap_name stack_name procedure_name
      ghost_domain_name in
    @LegacyGhost.state_interp Σ heapG0 initial_state ∗
    ([∗ map] name ↦ procedure ∈ initial_state.(LegacyLang.procs),
      @LegacyGhost.proc_tbl_chunk Σ heapG0 name procedure))%I.
Proof.
  iMod (own_alloc (● LegacyGhost.to_heapUR
    initial_state.(LegacyLang.global_heap))) as (heap_name) "Hheap".
  { apply auth_auth_valid. intros address.
    rewrite /LegacyGhost.to_heapUR lookup_fmap.
    destruct (initial_state.(LegacyLang.global_heap) !! address) eqn:Haddress;
      rewrite Haddress; simpl.
    - rewrite Some_valid pair_valid. split; [apply frac_valid_1|done].
    - exact I. }
  iMod (own_alloc (● LegacyGhost.to_stackR initial_state.(LegacyLang.stack)))
    as (stack_name) "Hstack".
  { apply auth_auth_valid. intros stack_id.
    rewrite /LegacyGhost.to_stackR lookup_fmap.
    destruct (initial_state.(LegacyLang.stack) !! stack_id); simpl; exact I. }
  iMod (ghost_map_alloc initial_state.(LegacyLang.procs))
    as (procedure_name) "[Hprocedures Hfragments]".
  iMod (own_alloc (● (∅ : LegacyGhost.ghost_domUR)))
    as (ghost_domain_name) "Hdomain"; first by apply auth_auth_valid.
  iMod (initialized_proc_table_fragments_persist procedure_name
    initial_state.(LegacyLang.procs) with "Hfragments") as "#Hfragments".
  iModIntro. iExists heap_name, stack_name, procedure_name, ghost_domain_name.
  simpl. iFrame "Hfragments".
  rewrite /LegacyGhost.state_interp /LegacyGhost.heap_interp
    /LegacyGhost.proc_tbl_interp /LegacyGhost.stack_interp
    /LegacyGhost.ghost_dom_interp.
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
    runtime bundle.  Program-specific initialization subsequently specializes
    [token_names] to its finite invariant enumeration and forms [runtimeG]. *)
Lemma initialized_runtime_resources_alloc
    (initial_state : LegacyLang.state)
    (Hstate_wf : LegacyGhost.state_wf initial_state)
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
      @LegacyGhost.state_interp Σ heapG0 initial_state ∗
      ([∗ map] name ↦ procedure ∈ initial_state.(LegacyLang.procs),
        @LegacyGhost.proc_tbl_chunk Σ heapG0 name procedure) ∗
      ([∗ list] token_name ∈ token_names,
        @own Σ (authR Legacy.inv_argsUR) Legacy.invtoken_pre_inG token_name
          (● (∅ : Legacy.inv_argsUR))))%I.
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

(** Compatibility interface during the staged migration.  New adequacy code
    targets [RUNTIME_CONFIGURATION] and [runtimeG]; existing semantic functors
    continue to accept this combined package until they have been generalized
    over the term-level class. *)
Module Type RUNTIME_RESOURCES.
  Include RUNTIME_CONFIGURATION.
  Parameter Σ : gFunctors.
  Parameter simpLangG0 : LegacyLifting.simpLangG Σ.
  Parameter invTokenG0 : Legacy.invTokenG Σ.
  Parameter ghost_own : forall field,
    tval TRef -> tval (Logic.field_type field) -> iProp Σ.
  Parameter ghost_own_timeless : forall field location chunk,
    Timeless (ghost_own field location chunk).
  Parameter ghost_alloc : runtime_ghost_alloc_spec simpLangG0
    ghost_heap_namespace ghost_own.
  Parameter ghost_update : runtime_ghost_update_spec simpLangG0 ghost_own.
End RUNTIME_RESOURCES.

Module StaticRuntimeConfiguration (Resources : RUNTIME_RESOURCES)
    <: RUNTIME_CONFIGURATION.
  Definition field_name := Resources.field_name.
  Definition field_name_injective := Resources.field_name_injective.
  Definition invariant_name := Resources.invariant_name.
  Definition invariant_name_injective := Resources.invariant_name_injective.
  Definition invariant_namespace := Resources.invariant_namespace.
  Definition invariant_namespaces_disjoint :=
    Resources.invariant_namespaces_disjoint.
  Definition ghost_heap_namespace := Resources.ghost_heap_namespace.
  Definition invariant_ghost_namespace_disjoint :=
    Resources.invariant_ghost_namespace_disjoint.
  Definition procedure_name := Resources.procedure_name.
  Definition procedure_name_injective := Resources.procedure_name_injective.
End StaticRuntimeConfiguration.

(** The implementation is parameterized only by the static program naming
    configuration.  Iris resources are ordinary Section parameters, so this
    module can be applied to a [runtimeG] value assembled after [own_alloc]. *)
(** *** The runtime erasure, extracted

    Everything from the typed program to the machine program it runs:
    expressions, field initializers, [runtime_stmt], and the total
    atomic-body erasure.  It is split out of [ConcreteModelCore] because
    that module is *generative* -- it declares records and an inductive --
    so a client that needs only the erasure cannot apply it a second time
    without creating incompatible copies of those types.  Nothing here
    declares a type, so this functor may be applied freely: a contract
    environment, which must be constructed before any semantic module,
    can reach [atomic_body_runtime] through it. *)
Module RuntimeErasure (Config : RUNTIME_CONFIGURATION).

(** The fixed Iris mask envelope in which a certified region executes. *)
Definition ambient_mask : Type := coPset.

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

(** Every dynamically typed runtime value has a typed representative.  This
    is the bridge used when a freshly-created procedure frame determines the
    interpretation of that invocation's canonical entry atoms. *)
Lemma val_has_typ_tval {t} (value : LegacyLang.val) :
  LegacyLang.val_has_typ value (runtime_type t) ->
  exists typed_value : tval t, tval_to_val typed_value = value.
Proof.
  destruct t; destruct value; simpl; intros Htype;
    try contradiction; try (destruct p; contradiction).
  - eexists (VBool _). reflexivity.
  - eexists (VInt _). reflexivity.
  - destruct l. eexists (VRef _). reflexivity.
  - eexists VUnit. reflexivity.
  - destruct p as [resource value]. simpl in Htype.
    subst resource.
    eexists (VRA value). reflexivity.
Qed.

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

Lemma runtime_variables_rename_named_context_at_lookup_other {Γ}
    (names : named_context Γ) replacement index query :
  not (query = index) ->
  runtime_variables (rename_named_context_at names replacement index) !! query =
    runtime_variables names !! query.
Proof.
  revert index query. induction names; intros [|index] [|query] Hother;
    simpl in *; try contradiction; try reflexivity.
  apply IHnames. lia.
Qed.

Lemma runtime_variable_rename_named_context_at_other {Γ t}
    (names : named_context Γ) replacement index (variable : pvar Γ t) :
  not (member_index variable = index) ->
  runtime_variable (rename_named_context_at names replacement index) variable =
    runtime_variable names variable.
Proof.
  revert names index. induction variable; intros names index Hother;
    dependent destruction names; destruct index;
    cbn [member_index rename_named_context_at runtime_variable] in *;
    try contradiction; try reflexivity.
  apply IHvariable. lia.
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

Lemma runtime_formal_declarations_rename_other {Γ F}
    (names : named_context Γ) (variables : pvar_list Γ F)
    replacement index :
  ~ In index (pvar_list_indices variables) ->
  runtime_formal_declarations
      (rename_named_context_at names replacement index) variables =
    runtime_formal_declarations names variables.
Proof.
  intros Hnot. induction variables; simpl in *; first reflexivity.
  f_equal.
  - rewrite runtime_variable_rename_named_context_at_other.
    + reflexivity.
    + intros Heq. apply Hnot. left. exact Heq.
  - apply IHvariables. intros Hin. apply Hnot. now right.
Qed.

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

Definition runtime_local_name {Γ t} (names : named_context Γ)
    (return_index index : nat) (variable : pvar Γ t) : LegacyLang.var :=
  if Nat.eqb (index + member_index variable) return_index then "#ret_val"
  else runtime_variable names variable.

Lemma runtime_local_declarations_from_variable {Γ}
    (names : named_context Γ) (formal_indices : list nat)
    (return_index index : nat) t (variable : pvar Γ t) :
  ~ In (index + member_index variable) formal_indices ->
  In (runtime_local_name names return_index index variable, runtime_type t)
    (runtime_local_declarations_from names formal_indices return_index index).
Proof.
  revert index names. induction variable; intros index names Hnot;
    dependent destruction names; cbn [runtime_local_name member_index] in *.
  - replace (index + 0) with index in Hnot by lia.
    destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
    + exfalso. apply Hnot. apply existsb_exists in Hformal.
      destruct Hformal as (candidate & Hin & Heq).
      apply Nat.eqb_eq in Heq. subst candidate.
      exact Hin.
    + cbn [runtime_local_declarations_from]. rewrite Hformal.
      unfold runtime_local_name.
      cbn [member_index runtime_variable].
      replace (index + 0) with index by lia.
      assert (Hhead : runtime_variable (NCCons name t names) MHere = name)
        by reflexivity.
      rewrite Hhead.
      destruct (Nat.eqb index return_index); apply in_eq.
  - destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
    + cbn [runtime_local_declarations_from]. rewrite Hformal.
      assert (Hname : runtime_local_name (NCCons name u names) return_index
          index (MThere variable) =
          runtime_local_name names return_index (S index) variable).
      { unfold runtime_local_name. cbn [member_index runtime_variable].
        replace (index + S (member_index variable)) with
          (S index + member_index variable) by lia. reflexivity. }
      rewrite Hname.
      apply IHvariable.
      replace (index + S (member_index variable)) with
        (S index + member_index variable) in Hnot by lia. exact Hnot.
    + cbn [runtime_local_declarations_from]. rewrite Hformal.
      assert (Hname : runtime_local_name (NCCons name u names) return_index
          index (MThere variable) =
          runtime_local_name names return_index (S index) variable).
      { unfold runtime_local_name. cbn [member_index runtime_variable].
        replace (index + S (member_index variable)) with
          (S index + member_index variable) by lia. reflexivity. }
      rewrite Hname.
      apply in_cons. apply IHvariable.
      replace (index + S (member_index variable)) with
        (S index + member_index variable) in Hnot by lia. exact Hnot.
Qed.

Lemma runtime_local_name_at_result {Γ t u} (names : named_context Γ)
    (result : pvar Γ u) (variable : pvar Γ t) :
  runtime_local_name names (member_index result) 0 variable =
  runtime_variable
    (rename_named_context_at names "#ret_val" (member_index result)) variable.
Proof.
  revert t variable u result.
  induction names as [| Γ name head_type names IH];
    intros value_type variable result_type result;
    dependent destruction variable; dependent destruction result;
    cbn [runtime_local_name rename_named_context_at runtime_variable].
  - unfold runtime_local_name, runtime_variable,
      Equality.simplification_heq.
    rewrite !member_index_here.
    reflexivity.
  - unfold runtime_local_name.
    rewrite member_index_here. rewrite member_index_there. reflexivity.
  - unfold runtime_local_name.
    rewrite member_index_there. rewrite member_index_here. reflexivity.
  - unfold runtime_local_name.
    rewrite !member_index_there. apply IH.
  all: try reflexivity.
Qed.

Lemma runtime_local_name_procedure {Γ F} (procedure : typed_procedure Γ F)
    t (variable : pvar Γ t) :
  runtime_local_name (procedure_variables _ _ procedure)
      (procedure_return_index procedure) 0 variable =
  runtime_variable (runtime_procedure_names procedure) variable.
Proof. apply runtime_local_name_at_result. Qed.

Lemma runtime_procedure_local_declaration {Γ F}
    (procedure : typed_procedure Γ F) t (variable : pvar Γ t) :
  ~ In (member_index variable)
      (pvar_list_indices (procedure_formal_variables _ _ procedure)) ->
  In (runtime_variable (runtime_procedure_names procedure) variable,
      runtime_type t) (runtime_procedure_locals procedure).
Proof.
  intros Hnot. unfold runtime_procedure_locals.
  rewrite <- runtime_local_name_procedure.
  apply runtime_local_declarations_from_variable.
  simpl. exact Hnot.
Qed.

Definition entry_atom_realizes {Γ} (identity : proc_id)
    (names : named_context Γ) (formal_indices : list nat)
    (frame : LegacyLang.stack_frame) {t} (symbolic : atom t)
    (value : tval t) : Prop :=
  forall variable : pvar Γ t,
    symbolic = ProcedureEntryAtom identity (member_index variable) ->
    ~ In (member_index variable) formal_indices ->
    frame.(LegacyLang.locals) !! runtime_variable names variable =
      Some (tval_to_val value).

Definition frame_entry_atoms {Γ} (caller_atoms : atom_env)
    (identity : proc_id) (names : named_context Γ)
    (formal_indices : list nat) (frame : LegacyLang.stack_frame)
    (Hrealizable : forall t (symbolic : atom t),
      exists value : tval t,
        entry_atom_realizes identity names formal_indices frame symbolic value)
    : atom_env :=
  fun t symbolic =>
    match symbolic as selected return tval _ with
    | Atom id => caller_atoms _ (Atom id)
    | ProcedureEntryAtom procedure slot =>
        epsilon (inhabits (default_tval t))
          (entry_atom_realizes identity names formal_indices frame
            (ProcedureEntryAtom procedure slot))
    end.

Lemma frame_entry_atoms_stable {Γ} (caller_atoms : atom_env)
    (identity : proc_id) (names : named_context Γ)
    (formal_indices : list nat) (frame : LegacyLang.stack_frame)
    Hrealizable :
  stable_atoms_agree caller_atoms
    (frame_entry_atoms caller_atoms identity names formal_indices frame
      Hrealizable).
Proof. intros t symbolic. destruct symbolic; simpl; reflexivity. Qed.

Lemma frame_entry_atoms_realize {Γ} (caller_atoms : atom_env)
    (identity : proc_id) (names : named_context Γ)
    (formal_indices : list nat) (frame : LegacyLang.stack_frame)
  Hrealizable t (symbolic : atom t) :
  entry_atom_realizes identity names formal_indices frame symbolic
    (frame_entry_atoms caller_atoms identity names formal_indices frame
      Hrealizable t symbolic).
Proof.
  destruct symbolic as [id | procedure slot].
  - intros variable Hbad _. discriminate Hbad.
  - unfold frame_entry_atoms. simpl. apply epsilon_spec. exact (Hrealizable _
      (ProcedureEntryAtom procedure slot)).
Qed.

Lemma frame_entry_atoms_exist {Γ} (caller_atoms : atom_env)
    (identity : proc_id) (names : named_context Γ)
    (formal_indices : list nat) (frame : LegacyLang.stack_frame) :
  (forall t (variable : pvar Γ t),
    ~ In (member_index variable) formal_indices ->
    exists value : tval t,
      frame.(LegacyLang.locals) !! runtime_variable names variable =
        Some (tval_to_val value)) ->
  exists callee_atoms : atom_env,
    stable_atoms_agree caller_atoms callee_atoms /\
    forall t (variable : pvar Γ t),
      ~ In (member_index variable) formal_indices ->
      frame.(LegacyLang.locals) !! runtime_variable names variable =
        Some (tval_to_val
          (callee_atoms t
            (ProcedureEntryAtom identity (member_index variable)))).
Proof.
  intros Htyped.
  assert (Hrealizable : forall t (symbolic : atom t),
      exists value : tval t,
        entry_atom_realizes identity names formal_indices frame symbolic value).
  { intros t symbolic.
    destruct (classic (exists variable : pvar Γ t,
      symbolic = ProcedureEntryAtom identity (member_index variable) /\
      ~ In (member_index variable) formal_indices)) as [Hexists | Hnone].
    - destruct Hexists as (variable & Hsymbolic & Hnot).
      destruct (Htyped t variable Hnot) as (value & Hvalue).
      exists value. intros other Hother Hother_not.
      have Hindices : member_index variable = member_index other.
      { rewrite Hsymbolic in Hother. inversion Hother. reflexivity. }
      have -> : other = variable.
      { apply member_index_injective. symmetry. exact Hindices. }
      exact Hvalue.
    - exists (default_tval t). intros variable Hsymbolic Hnot.
      exfalso. apply Hnone. exists variable. auto.
  }
  exists (frame_entry_atoms caller_atoms identity names formal_indices frame
    Hrealizable). split.
  - apply frame_entry_atoms_stable.
  - intros t variable Hnot.
    apply (frame_entry_atoms_realize caller_atoms identity names formal_indices
      frame Hrealizable t
      (ProcedureEntryAtom identity (member_index variable)) variable
      eq_refl Hnot).
Qed.

Lemma procedure_frame_entry_atoms_exist {Γ F}
    (caller_atoms : atom_env) (procedure : typed_procedure Γ F)
    (frame : LegacyLang.stack_frame) :
  (forall variable type,
    (variable, type) ∈ runtime_procedure_locals procedure ->
    exists value,
      frame.(LegacyLang.locals) !! variable = Some value /\
      LegacyLang.val_has_typ value type) ->
  exists callee_atoms : atom_env,
    stable_atoms_agree caller_atoms callee_atoms /\
    forall t (variable : pvar Γ t),
      ~ In (member_index variable)
        (pvar_list_indices (procedure_formal_variables _ _ procedure)) ->
      frame.(LegacyLang.locals) !!
          runtime_variable (runtime_procedure_names procedure) variable =
        Some (tval_to_val
          (callee_atoms t (ProcedureEntryAtom F (member_index variable)))).
Proof.
  intros Hlocals. apply frame_entry_atoms_exist.
  intros t variable Hnot.
  pose proof (runtime_procedure_local_declaration procedure t variable Hnot)
    as Hdeclaration.
  destruct (Hlocals
      (runtime_variable (runtime_procedure_names procedure) variable)
      (runtime_type t) (ltac:(apply elem_of_list_In; exact Hdeclaration)))
    as (raw & Hlookup & Htype).
  destruct (val_has_typ_tval raw Htype) as (value & <-).
  exists value. exact Hlookup.
Qed.

Lemma runtime_formal_declarations_length {Γ F} (names : named_context Γ)
    (variables : pvar_list Γ F) :
  length (runtime_formal_declarations names variables) = length F.
Proof. induction variables; simpl; congruence. Qed.

Lemma runtime_formal_declarations_lookup {Γ F}
    (names : named_context Γ) (variables : pvar_list Γ F) t
    (formal_variable : formal F t) :
  In (runtime_variable names (lookup_pvar_list variables formal_variable),
      runtime_type t) (runtime_formal_declarations names variables).
Proof.
  induction variables; dependent destruction formal_variable.
  - rewrite lookup_pvar_list_here. simpl. left. reflexivity.
  - rewrite lookup_pvar_list_there. simpl. right. apply IHvariables.
Qed.

Lemma runtime_procedure_arguments_length {Γ F}
    (procedure : typed_procedure Γ F) :
  length (runtime_procedure_arguments procedure) =
    length (Logic.procedure_args F).
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

Lemma runtime_variable_member_inv {Γ} (names : named_context Γ) name :
  In name (runtime_variables names) ->
  exists t (variable : pvar Γ t), runtime_variable names variable = name.
Proof.
  induction names; simpl; first tauto.
  intros [<- | Hin].
  - exists t, MHere. reflexivity.
  - destruct (IHnames Hin) as (u & variable & Hvariable).
    exists u, (MThere variable). exact Hvariable.
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
    ~ In (index + local_index) formal_indices /\
    not ((index + local_index)%nat = return_index).
Proof.
  revert index.
  induction names as [| Γ name0 t names IH]; intros index; simpl.
  - intros Hin. inversion Hin.
  - destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
    + intros Hin. destruct (IH (S index) Hin) as [Hret | Hsource].
      * left; exact Hret.
      * right. destruct Hsource as (local_index & Hlookup & Hnot & Hreturn).
        exists (S local_index). split.
        { rewrite lookup_cons. simpl. exact Hlookup. }
        split; replace (index + S local_index) with (S index + local_index)
          by lia; assumption.
    + intros Hin. destruct (Nat.eqb index return_index) eqn:Hsame.
      * simpl in Hin. destruct Hin as [Hin | Hin].
        -- left. symmetry. exact Hin.
        -- destruct (IH (S index) Hin) as [Hret | Hsource].
           ++ left; exact Hret.
           ++ right. destruct Hsource as
                (local_index & Hlookup & Hnot & Hreturn).
              exists (S local_index). split.
              { rewrite lookup_cons. simpl. exact Hlookup. }
              split; replace (index + S local_index) with
                (S index + local_index) by lia; assumption.
      * simpl in Hin. destruct Hin as [Hin | Hin].
        -- subst name. right. exists 0. split; [simpl; reflexivity|]. split.
           ++ intro Hinformal.
              rewrite Nat.add_0_r in Hinformal.
              have Htrue : existsb (Nat.eqb index) formal_indices = true.
              { apply (proj2 (existsb_exists (Nat.eqb index)
                    formal_indices)).
                exists index. split; [exact Hinformal|apply Nat.eqb_refl]. }
              congruence.
           ++ rewrite Nat.add_0_r. apply Nat.eqb_neq in Hsame. exact Hsame.
        -- destruct (IH (S index) Hin) as [Hret | Hsource].
           ++ left; exact Hret.
           ++ right. destruct Hsource as
                (local_index & Hlookup & Hnot & Hreturn).
              exists (S local_index). split.
              { rewrite lookup_cons. simpl. exact Hlookup. }
              split; replace (index + S local_index) with
                (S index + local_index) by lia; assumption.
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
           ++ destruct Hsource as (local_index & Hlookup & Hnot & Hreturn).
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
    ~ In local_index (pvar_list_indices (procedure_formal_variables _ _ procedure)) /\
    not (local_index = procedure_return_index procedure).
Proof.
  unfold runtime_procedure_locals.
  intros Hin. apply runtime_local_declarations_from_source_index in Hin.
  destruct Hin as [Hret | (local_index & Hlookup & Hnot & Hreturn)].
  - left; exact Hret.
  - right. exists local_index. split; [exact Hlookup|].
    split; simpl in *; assumption.
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
    as [Hreturn |
      (local_index & Hlocal_lookup & Hlocal_not_formal & Hlocal_not_return)].
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

Lemma runtime_procedure_declaration_names_cover {Γ F}
    (procedure : typed_procedure Γ F) :
  procedure_wf procedure ->
  (list_to_set (runtime_procedure_arguments procedure).*1 :
      gset LegacyLang.var) ∪
      (list_to_set (runtime_procedure_locals procedure).*1 :
        gset LegacyLang.var) =
    (list_to_set (runtime_variables (runtime_procedure_names procedure)) :
      gset LegacyLang.var).
Proof.
  intros Hwf. apply set_eq. intro name.
  rewrite elem_of_union. rewrite !elem_of_list_to_set.
  split.
  - intros [Hargument | Hlocal].
    + apply elem_of_list_In in Hargument.
      destruct (runtime_formal_name_index
        (procedure_variables _ _ procedure)
        (procedure_formal_variables _ _ procedure) name Hargument)
        as (index & Hformal & Hlookup).
      apply elem_of_list_lookup. exists index.
      unfold runtime_procedure_names.
      rewrite runtime_variables_rename_named_context_at_lookup_other.
      * exact Hlookup.
      * intros Heq. subst index.
        exact (procedure_return_slot_local _ Hwf Hformal).
    + apply elem_of_list_In in Hlocal.
      destruct (runtime_procedure_local_source_index procedure name Hlocal)
        as [-> | (index & Hlookup & Hnotformal & Hnotreturn)].
      * rewrite <- (runtime_procedure_return_name procedure).
        apply runtime_variable_member.
      * apply elem_of_list_lookup. exists index.
        unfold runtime_procedure_names.
        rewrite runtime_variables_rename_named_context_at_lookup_other;
          assumption.
  - intros Hname.
    apply elem_of_list_In in Hname.
    destruct (runtime_variable_member_inv
      (runtime_procedure_names procedure) name Hname)
      as (t & variable & <-).
    destruct (in_dec Nat.eq_dec (member_index variable)
      (pvar_list_indices (procedure_formal_variables _ _ procedure)))
      as [Hformal | Hlocal].
    + left. apply elem_of_list_In.
      destruct (pvar_list_index_member
        (procedure_formal_variables _ _ procedure) variable Hformal)
        as (formal_variable & Hvariable).
      subst variable. apply in_map_iff.
      exists (runtime_variable (procedure_variables _ _ procedure)
        (lookup_pvar_list (procedure_formal_variables _ _ procedure)
          formal_variable), runtime_type t). split.
      * simpl. unfold runtime_procedure_names.
        rewrite runtime_variable_rename_named_context_at_other; first reflexivity.
        intros Heq. apply (procedure_return_slot_local _ Hwf).
        rewrite <- Heq. exact Hformal.
      * apply runtime_formal_declarations_lookup.
    + right. apply elem_of_list_In. apply in_map_iff.
      exists (runtime_variable (runtime_procedure_names procedure) variable,
        runtime_type t). split; first reflexivity.
      apply runtime_procedure_local_declaration. exact Hlocal.
Qed.

Definition runtime_unop {input output} (op : unop input output) :
    un_op :=
  match op with
  | UNot => NotBoolOp
  | UNeg => NegOp
  | URAOfInt resource => RAOfIntOp resource
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
        (IR.symbolize_expr store expression))
      as [operand_value|] eqn:Hoperand; simpl; [|discriminate].
    intros Heq. inversion Heq. subst. eapply LegacyLang.UnOpStep.
    + apply IHexpression. reflexivity.
    + apply runtime_unop_sound.
  - destruct (interp_expr formals binders atoms
        (IR.symbolize_expr store expression1))
      as [value1|] eqn:Hvalue1; simpl; [|discriminate].
    destruct (interp_expr formals binders atoms
        (IR.symbolize_expr store expression2))
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
      (Config.field_name field, runtime_expr names value) ::
      runtime_field_initializers names fields'
  end.

Definition runtime_physical_field_initializers {Γ} (names : named_context Γ)
    (fields : list (field_init Γ)) :
    list (LegacyLang.fld_name * LegacyLang.expr) :=
  runtime_field_initializers names (physical_field_initializers fields).

Definition runtime_packed_ghost_field_names {Γ}
    (fields : list (ghost_field_init Γ)) : list LegacyLang.fld_name :=
  map (fun initialization => match initialization with
    | GhostFieldInit _ field _ _ => Config.field_name field
    end) fields.

Definition runtime_ghost_field_names {Γ} (fields : list (field_init Γ)) :
    list LegacyLang.fld_name :=
  runtime_packed_ghost_field_names (ghost_field_initializers fields).

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
        (runtime_expr names base) (Config.field_name field) stack)
  | TFieldWrite _ field base value =>
      Some (LegacyLang.RTFldWr (runtime_expr names base)
        (Config.field_name field) (runtime_expr names value) stack)
  | TAlloc _ target fields =>
      Some (LegacyLang.RTAlloc (runtime_variable names target)
        (runtime_field_initializers names
          (physical_field_initializers fields)) stack)
  | TGhostUpdate _ _ _ _ _ => None
  | TCall _ procedure arguments target =>
      match target with
      | CTStore target' =>
          Some (LegacyLang.RTCall (runtime_variable names target')
            (Config.procedure_name procedure)
            (runtime_expr_list names arguments) stack)
      | CTDiscard =>
          Some (LegacyLang.RTCallNoStore
            (Config.procedure_name procedure)
            (runtime_expr_list names arguments) stack)
      end
  | TSpawn _ procedure arguments =>
      Some (LegacyLang.RTSpawn (Config.procedure_name procedure)
        (runtime_expr_list names arguments) stack)
  | TUnfold _ _ _ | TFold _ _ _
  | TPredicateUnfold _ _ _ | TPredicateFold _ _ _ => None
  | TInvAccess _ _ body => runtime_stmt names stack body
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
  | TAtomic node body =>
      Some (LegacyLang.RTTrustedAtomic
        (trusted_atomic_transition node body) stack)
  end.

(** The total erasure of an atomic block's body: the program the machine
    runs for it, with a proof-only body erasing to [runtime_noop] rather
    than to nothing.  Totality is what lets the trusted transition take
    it as an argument. *)
Definition atomic_body_runtime {Γ} (names : named_context Γ)
    (stack : LegacyLang.stack_id) (body : stmt Γ) : LegacyLang.runtime_stmt :=
  default runtime_noop (runtime_stmt names stack body).

(** The trusted substrate observes an atomic block only through its runtime
    behavior.  Consequently, proof-only rewrites with identical erasure
    select the same opaque hardware transition.  Like the refinement law,
    this is a framework property, never a program-specific obligation. *)
Axiom trusted_atomic_transition_runtime_erasure : forall {Γ}
    (node : node_id) (body body' : stmt Γ),
  (forall (names : named_context Γ) (stack : LegacyLang.stack_id),
    runtime_stmt names stack body = runtime_stmt names stack body') ->
  trusted_atomic_transition node body = trusted_atomic_transition node body'.

Lemma runtime_stmt_atomic {Γ} (names : named_context Γ) stack node
    (body : stmt Γ) :
  runtime_stmt names stack (TAtomic node body) =
    Some (LegacyLang.RTTrustedAtomic
      (trusted_atomic_transition node body) stack).
Proof. reflexivity. Qed.

(** The point of the refactor: a proof-only rewrite of an atomic body
    cannot change the program.  No hypothesis about the transition is
    needed -- it simply cannot see the difference. *)
Lemma runtime_stmt_atomic_congruence {Γ} (names : named_context Γ) stack node
    (body body' : stmt Γ) :
  (forall (names : named_context Γ) (stack : LegacyLang.stack_id),
    runtime_stmt names stack body = runtime_stmt names stack body') ->
  runtime_stmt names stack (TAtomic node body) =
    runtime_stmt names stack (TAtomic node body').
Proof.
  intros Herasure.
  rewrite !runtime_stmt_atomic.
  rewrite (trusted_atomic_transition_runtime_erasure node body body' Herasure).
  reflexivity.
Qed.

End RuntimeErasure.

Module ConcreteModelCore (Config : RUNTIME_CONFIGURATION).
Include RuntimeErasure Config.


(** Proof-only statements may be distributed across a conditional without
    changing the generated runtime program.  The operational refinement uses
    this equality for an invariant unfold/fold pair: branch selection happens
    first, and only the selected arm enters the Iris invariant. *)
Lemma runtime_stmt_distribute_erased_before_if {Γ}
    (names : named_context Γ) stack before_node conditional_node
    then_seq_node else_seq_node (before : stmt Γ) condition
    (then_branch else_branch : stmt Γ) :
  runtime_stmt names stack before = None ->
  runtime_stmt names stack
    (TSeq before_node before
      (TIf conditional_node condition then_branch else_branch)) =
  runtime_stmt names stack
    (TIf conditional_node condition
      (TSeq then_seq_node before then_branch)
      (TSeq else_seq_node before else_branch)).
Proof.
  intros Hbefore. simpl. rewrite Hbefore.
  destruct (runtime_stmt names stack then_branch),
    (runtime_stmt names stack else_branch); reflexivity.
Qed.

Corollary runtime_stmt_distribute_unfold_before_if {Γ}
    (names : named_context Γ) stack unfold_node conditional_node
    then_seq_node else_seq_node invariant arguments condition
    (then_branch else_branch : stmt Γ) :
  runtime_stmt names stack
    (TSeq unfold_node (TUnfold unfold_node invariant arguments)
      (TIf conditional_node condition then_branch else_branch)) =
  runtime_stmt names stack
    (TIf conditional_node condition
      (TSeq then_seq_node (TUnfold unfold_node invariant arguments)
        then_branch)
      (TSeq else_seq_node (TUnfold unfold_node invariant arguments)
        else_branch)).
Proof.
  apply runtime_stmt_distribute_erased_before_if. reflexivity.
Qed.


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
      Config.procedure_name (procedure_identity _ _ procedure);
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

Lemma procedure_argument_frame_lookup {Γ F}
    (names : named_context Γ) (variables : pvar_list Γ F)
    (values : tval_list F) (frame : LegacyLang.stack_frame) :
  Forall2 (fun variable value =>
    frame.(LegacyLang.locals) !! variable = Some value)
    (runtime_formal_declarations names variables).*1
    (tval_list_to_list values) ->
  forall t (formal_variable : formal F t),
    frame.(LegacyLang.locals) !!
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
    (caller_atoms : atom_env) (procedure : typed_procedure Γ F)
    (values : tval_list (Logic.procedure_args F))
    (frame : LegacyLang.stack_frame) :
  procedure_wf procedure ->
  Forall2 (fun variable value =>
    frame.(LegacyLang.locals) !! variable = Some value)
    (runtime_procedure_arguments procedure).*1
    (tval_list_to_list values) ->
  (forall variable type,
    (variable, type) ∈ runtime_procedure_locals procedure ->
    exists value,
      frame.(LegacyLang.locals) !! variable = Some value /\
      LegacyLang.val_has_typ value type) ->
  dom frame.(LegacyLang.locals) =
    list_to_set (runtime_procedure_arguments procedure).*1 ∪
      list_to_set (runtime_procedure_locals procedure).*1 ->
  exists callee_atoms : atom_env,
    stable_atoms_agree caller_atoms callee_atoms /\
    stack_corresponds (runtime_procedure_names procedure)
      (formal_env_of_values values) empty_binder_env callee_atoms
      (procedure_entry_store _ _ procedure) frame /\
    dom frame.(LegacyLang.locals) =
      list_to_set (runtime_variables (runtime_procedure_names procedure)).
Proof.
  intros Hwf Harguments Hlocals Hdom.
  destruct (procedure_frame_entry_atoms_exist caller_atoms procedure frame
    Hlocals) as (callee_atoms & Hagree & Hlocal).
  exists callee_atoms. split; [exact Hagree|]. split.
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
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (frame : LegacyLang.stack_frame)
    (expressions : pexpr_list Γ ts) (values : tval_list ts) :
  stack_corresponds names formals binders atoms store frame ->
  interp_expr_list formals binders atoms
    (IR.symbolize_expr_list store expressions) = Some values ->
  Forall2 (fun expression value =>
    LegacyLang.expr_step expression frame (LegacyLang.Val value))
    (runtime_expr_list names expressions) (tval_list_to_list values).
Proof.
  intros Hstack. revert values.
  induction expressions; intros values Hvalues; dependent destruction values;
    simpl in Hvalues.
  - constructor.
  - destruct (interp_expr formals binders atoms
      (IR.symbolize_expr store p)) eqn:Hhead; [|discriminate].
    destruct (interp_expr_list formals binders atoms
      (IR.symbolize_expr_list store expressions)) eqn:Htail;
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
    (procedure : typed_procedure Γ F)
    (formals : formal_env (Logic.procedure_args F))
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ (Logic.procedure_args F) Δ) :
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
        (IR.update_store_with_bound store target)) =
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

Section WithRuntime.
Context {Σ : gFunctors} `{RG : runtimeG Σ}.

Local Instance core_simpLangG : LegacyLifting.simpLangG Σ :=
  runtime_simpLangG.
Local Instance core_invTokenG : Legacy.invTokenG Σ :=
  runtime_invTokenG.
Local Instance core_heapG : LegacyGhost.heapG Σ :=
  LegacyLifting.simpLangG_gen_heapG.
Local Instance core_irisG : irisGS LegacyLang.simp_lang Σ :=
  LegacyLifting.simpLang_irisG.
Local Existing Instance weakestpre.wp'.
Local Instance core_invtoken_inG : inG Σ (authR Legacy.inv_argsUR) :=
  @Legacy.invtoken_inG Σ core_invTokenG.

Definition core_stack_own Γ (runtime : stack_context Γ)
    (store : concrete_store Γ) : iProp Σ :=
  LegacyGhost.stack_frame_own (runtime_stack_id _ runtime)
    (LegacyLang.StackFrame (concrete_locals (runtime_names _ runtime) store)).

Lemma core_stack_own_exclusive Γ (runtime : stack_context Γ)
    (left right : concrete_store Γ) :
  core_stack_own Γ runtime left ∗ core_stack_own Γ runtime right ⊢ False.
Proof.
  unfold core_stack_own.
  iIntros "[Hleft Hright]".
  iApply (LegacyGhost.stack_frame_own_exclusive with "Hleft Hright").
Qed.

Local Notation stack_own := core_stack_own.
Local Notation concrete_heapG := core_heapG.
Local Notation concrete_irisG := core_irisG.
Local Notation concrete_invtoken_inG := core_invtoken_inG.

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

Definition core_field_own field
    (location : tval TRef) (chunk : tval (Logic.field_type field)) :
    iProp Σ :=
  match location with
  | VRef address =>
      LegacyGhost.heap_maps_to (LegacyLang.Loc address)
        (Config.field_name field) 1 (tval_to_val chunk)
  end.

Definition core_ghost_own field
    (location : tval TRef) (chunk : tval (Logic.field_type field)) :
    iProp Σ :=
  runtime_ghost_own field location chunk.

Global Instance ghost_own_timeless field location chunk :
  Timeless (core_ghost_own field location chunk) :=
  runtime_ghost_own_timeless field location chunk.

Definition core_invariant_own invariant
    (values : tval_list (Logic.invariant_args invariant)) : iProp Σ :=
  @own Σ (authR Legacy.inv_argsUR) core_invtoken_inG
    (Legacy.invtoken_names (Config.invariant_name invariant))
    (◯ ({[tval_list_to_rich_list values]} : gset (list Legacy.val))).

Local Notation field_own := core_field_own.
Local Notation ghost_own := core_ghost_own.
Local Notation invariant_own := core_invariant_own.

Definition runtime_wp (mask : coPset) (statement : LegacyLang.runtime_stmt)
    (post : LegacyLang.val -> iProp Σ) : iProp Σ :=
  @wp _ _ _ _
    (@weakestpre.wp' HasLc LegacyLang.simp_lang Σ concrete_irisG)
    NotStuck mask statement post.

Definition invariant_mask (mask : Hoare.mask) : coPset :=
  set_fold (fun invariant result =>
    result ∪ ↑(Config.invariant_namespace invariant)) ∅ mask.

Definition runtime_mask (mask : Hoare.mask) : coPset :=
  invariant_mask mask ∪ ↑Config.ghost_heap_namespace.

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
    ↑(Config.invariant_namespace invariant) ∪ invariant_mask mask.
Proof.
  unfold invariant_mask.
  rewrite (set_fold_union_strong (=)
    (fun invariant result =>
      result ∪ ↑(Config.invariant_namespace invariant)) ∅
    ({[invariant]} : Hoare.mask) mask).
  - rewrite set_fold_singleton.
    replace (∅ ∪ ↑Config.invariant_namespace invariant) with
      ((fun result : coPset =>
          ↑Config.invariant_namespace invariant ∪ result) ∅)
      by set_solver.
    rewrite (set_fold_comm_acc
      (fun invariant' result =>
        result ∪ ↑(Config.invariant_namespace invariant'))
      (fun result => ↑Config.invariant_namespace invariant ∪ result)
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
      ↑(Config.invariant_namespace invariant).
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
  (↑(Config.invariant_namespace invariant) : coPset) ##
    invariant_mask mask.
Proof.
  induction mask using set_ind_L.
  - rewrite invariant_mask_empty. set_solver.
  - intros Hnotin. rewrite invariant_mask_union_singleton.
    have Hneq : invariant ≠ x by set_solver.
    have Hleft : (↑Config.invariant_namespace invariant : coPset) ##
        ↑Config.invariant_namespace x :=
      Config.invariant_namespaces_disjoint invariant x Hneq.
    have Hright := IHmask ltac:(set_solver).
    exact (proj2 (disjoint_union_r _ _ _) (conj Hleft Hright)).
Qed.

Lemma invariant_namespace_subset_runtime_mask invariant (mask : Hoare.mask) :
  invariant ∈ mask ->
  ↑(Config.invariant_namespace invariant) ⊆ runtime_mask mask.
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
  (↑Config.ghost_heap_namespace : coPset) ## invariant_mask mask.
Proof.
  induction mask using set_ind_L.
  - rewrite invariant_mask_empty. apply disjoint_empty_r.
  - rewrite invariant_mask_union_singleton. apply disjoint_union_r. split.
    + symmetry. apply Config.invariant_ghost_namespace_disjoint.
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
  have Hghost : (↑Config.ghost_heap_namespace : coPset) ##
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
      ↑(Config.invariant_namespace invariant).
Proof.
  intros Hin. unfold runtime_mask.
  have Hmask : mask = {[invariant]} ∪ (mask ∖ {[invariant]}).
  { apply set_eq. intros other.
    rewrite elem_of_union elem_of_singleton elem_of_difference
      elem_of_singleton. split.
    - intros Hother. destruct (decide (other = invariant)); [left|right]; done.
    - intros [->|[Hother _]]; assumption. }
  have Hfold : invariant_mask mask =
      ↑(Config.invariant_namespace invariant) ∪
        invariant_mask (mask ∖ {[invariant]}).
  { exact (eq_trans (f_equal invariant_mask Hmask)
      (invariant_mask_union_singleton invariant
        (mask ∖ {[invariant]}))). }
  rewrite Hfold.
  have Hinv := invariant_mask_disjoint invariant (mask ∖ {[invariant]})
    ltac:(set_solver).
  have Hghost := Config.invariant_ghost_namespace_disjoint invariant.
  rewrite !difference_union_distr_l_L difference_diag_L.
  rewrite (difference_disjoint_L (invariant_mask (mask ∖ {[invariant]}))
    (↑(Config.invariant_namespace invariant) : coPset)); last by symmetry.
  rewrite (difference_disjoint_L
    (↑Config.ghost_heap_namespace : coPset)
    (↑(Config.invariant_namespace invariant) : coPset));
    last by symmetry.
  rewrite (left_id_L _ _). reflexivity.
Qed.

Lemma runtime_mask_insert invariant (mask : Hoare.mask) :
  runtime_mask (mask ∪ {[invariant]}) =
    runtime_mask mask ∪
      ↑(Config.invariant_namespace invariant).
Proof.
  unfold runtime_mask.
  have Hcomm : mask ∪ {[invariant]} = {[invariant]} ∪ mask.
  { apply set_eq. intros other. rewrite !elem_of_union !elem_of_singleton.
    tauto. }
  have Hfold : invariant_mask (mask ∪ {[invariant]}) =
      ↑(Config.invariant_namespace invariant) ∪ invariant_mask mask.
  { exact (eq_trans (f_equal invariant_mask Hcomm)
      (invariant_mask_union_singleton invariant mask)). }
  rewrite Hfold. apply set_eq. intros name. rewrite !elem_of_union. tauto.
Qed.

Lemma invariant_namespace_disjoint_runtime_mask invariant (mask : Hoare.mask) :
  invariant ∉ mask ->
  (↑(Config.invariant_namespace invariant) : coPset) ## runtime_mask mask.
Proof.
  intros Hnotin. unfold runtime_mask.
  apply disjoint_union_r. split.
  - apply invariant_mask_disjoint. exact Hnotin.
  - apply Config.invariant_ghost_namespace_disjoint.
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
             (IR.update_store_with_bound store target)))%I).
Proof.
  iIntros "Hstack". unfold runtime_wp.
  iEval (unfold stack_own) in "Hstack".
  destruct (interp_expr_total formals binders atoms
    (IR.symbolize_expr store expression)) as [value Hvalue].
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
      (Config.field_name field)
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
        (IR.symbolize_expr store expression)) as [new_value Htotal];
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
    (Config.field_name field) (tval_to_val old_value) mask
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
      (Config.field_name field) (runtime_stack_id _ runtime))
    (fun result =>
      (⌜result = LegacyLang.LitUnit⌝ ∗
       ∃ value,
         ⌜value = chunk⌝ ∗
         stack_own Γ runtime
           (interp_store formals (binder_cons value binders) atoms
             (IR.update_store_with_bound store target)) ∗
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
    (Config.field_name field)
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

Fixpoint allocated_physical_fields_own {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (location : tval TRef)
    (fields : list (field_init Γ)) : iProp Σ :=
  match fields with
  | [] => True%I
  | FieldInit field expression :: fields' =>
      (∃ value,
        ⌜interp_program_expr formals binders atoms store expression =
          Some value⌝ ∗
        field_own field location value ∗
        allocated_physical_fields_own runtime formals binders atoms store location
          fields')%I
  end.

Fixpoint allocated_ghost_fields_own {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (location : tval TRef)
    (fields : list (ghost_field_init Γ)) : iProp Σ :=
  match fields with
  | [] => True%I
  | GhostFieldInit resource field Hfield expression :: fields' =>
      (∃ value : TypedRAs.ra_carrier resource,
        ⌜interp_program_expr formals binders atoms store expression =
          Some (VRA value)⌝ ∗
        ghost_own field location
          (eq_rect (TRA resource) tval (VRA value)
            (Logic.field_type field) (eq_sym Hfield)) ∗
        allocated_ghost_fields_own runtime formals binders atoms store location
          fields')%I
  end.

Definition allocated_fields_own {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (location : tval TRef)
    (fields : list (field_init Γ)) : iProp Σ :=
  (allocated_physical_fields_own runtime formals binders atoms store location
      (physical_field_initializers fields) ∗
   allocated_ghost_fields_own runtime formals binders atoms store location
      (ghost_field_initializers fields))%I.

Definition ghost_initializers_semantically_valid {Γ F Δ}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) : Prop :=
  Forall (fun initialization =>
    match initialization with
    | GhostFieldInit resource _ _ expression => forall value,
        interp_program_expr formals binders atoms store expression =
          Some (VRA value) ->
        @ra_base.valid _ (ra_base.RA_inst (LegacyRAs.ra_map resource)) value
    end) fields.

Lemma ghost_dom_frag_names_cons address field names :
  field ∉ names ->
  LegacyGhost.ghost_dom_frag (list_to_set (map
    (LegacyLang.heap_addr_constr (LegacyLang.Loc address)) (field :: names))) ⊣⊢
  LegacyGhost.ghost_dom_frag
    {[LegacyLang.heap_addr_constr (LegacyLang.Loc address) field]} ∗
  LegacyGhost.ghost_dom_frag (list_to_set (map
    (LegacyLang.heap_addr_constr (LegacyLang.Loc address)) names)).
Proof.
  intros Hfresh. simpl. rewrite LegacyGhost.ghost_dom_frag_insert; first done.
  rewrite elem_of_list_to_set. intros Hmember.
  apply elem_of_list_fmap in Hmember as [other [Heq Hmember]].
  injection Heq as Heq. apply Hfresh. subst other. exact Hmember.
Qed.

Lemma allocated_ghost_fields_alloc {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) fields address E :
  NoDup (runtime_packed_ghost_field_names fields) ->
  ghost_initializers_semantically_valid formals binders atoms store fields ->
  (↑runtime_ghost_namespace : coPset) ⊆ E ->
  @LegacyGhost.ghost_dom_frag Σ core_heapG
    (list_to_set (map (LegacyLang.heap_addr_constr (LegacyLang.Loc address))
      (runtime_packed_ghost_field_names fields))) -∗
  |={E}=> allocated_ghost_fields_own runtime formals binders atoms store
    (VRef address) fields.
Proof.
  intros Hnames Hvalid Hmask.
  induction fields as [|[resource field Hfield expression] fields IH].
  - iIntros "_". iModIntro. done.
  - inversion Hnames as [|? ? Hfresh Hnames']; subst.
    inversion Hvalid as [|? ? Hhead_valid Hvalid']; subst.
    simpl.
    destruct (interp_expr_total formals binders atoms
      (IR.symbolize_expr store expression)) as [value Hvalue].
    dependent destruction value.
    iIntros "Hdomain".
    iEval (rewrite (ghost_dom_frag_names_cons address (Config.field_name field)
      (runtime_packed_ghost_field_names fields) Hfresh)) in "Hdomain".
    iDestruct "Hdomain" as "[Hone Htail]".
    iMod (IH Hnames' Hvalid' with "Htail") as "Htail".
    have Hchunk_valid : @ra_base.valid _
        (ra_base.RA_inst (LegacyRAs.ra_map resource)) value.
    { apply (Hhead_valid value). exact Hvalue. }
    iMod (runtime_ghost_alloc E field resource (Config.field_name field)
      address value Hfield Hmask Hchunk_valid with "Hone") as "Hown".
    iModIntro. iExists value. iFrame. iPureIntro. exact Hvalue.
Qed.

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
      ((Config.field_name field, tval_to_val value) :: values).

Lemma field_values_match_exists {Γ F Δ} (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
  exists values, field_values_match formals binders atoms store fields values.
Proof.
  induction fields as [|[field expression] fields IH].
  - exists []. constructor.
  - destruct IH as [values Hvalues].
    destruct (interp_expr_total formals binders atoms
      (IR.symbolize_expr store expression)) as [value Hvalue].
    exists ((Config.field_name field, tval_to_val value) :: values).
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
    Config.field_name (field_init_id initialization)) fields.
Proof.
  intros Hmatch. induction Hmatch; simpl.
  - reflexivity.
  - f_equal. exact IHHmatch.
Qed.

Lemma runtime_field_names_nodup {Γ} (fields : list (field_init Γ)) :
  NoDup (map field_init_id fields) ->
  NoDup (map (fun initialization =>
    Config.field_name (field_init_id initialization)) fields).
Proof.
  induction fields as [|initialization fields IH]; simpl; intros Hnodup.
  - constructor.
  - inversion Hnodup as [|? ? Hfresh Htail]. constructor.
    + intros Hmember. apply elem_of_list_fmap in Hmember.
      destruct Hmember as [other [Heq Hother]].
      apply Config.field_name_injective in Heq. apply Hfresh.
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
      apply Config.field_name_injective in Heq. subst other_field. apply Hfresh.
      apply elem_of_list_fmap.
      exists (GhostFieldInit other_resource field other_type other_expression).
      split; [reflexivity | exact Hother].
    + apply IH. exact Htail.
Qed.

Lemma field_values_match_own {Γ F Δ} (runtime : stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) fields values address :
  field_values_match formals binders atoms store fields values ->
  LegacyLifting.field_list_to_iprop (LegacyLang.Loc address) values ⊢
    allocated_physical_fields_own runtime formals binders atoms store (VRef address)
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
  NoDup (map ghost_field_init_id (ghost_field_initializers fields)) ->
  ghost_initializers_require_physical fields ->
  ghost_initializers_semantically_valid formals binders atoms store
    (ghost_field_initializers fields) ->
  (↑runtime_ghost_namespace : coPset) ⊆ mask ->
  stack_own Γ runtime (interp_store formals binders atoms store) ⊢
  runtime_wp mask
    (LegacyLang.RTAlloc (runtime_variable (runtime_names _ runtime) target)
      (runtime_physical_field_initializers (runtime_names _ runtime) fields)
      (runtime_stack_id _ runtime))
    (fun result =>
      (⌜result = LegacyLang.LitUnit⌝ ∗
       ∃ address : Z,
         stack_own Γ runtime
           (interp_store formals (binder_cons (VRef address) binders) atoms
             (IR.update_store_with_bound store target)) ∗
         allocated_fields_own runtime formals binders atoms store
           (VRef address) fields)%I).
Proof.
  intros Hfields Hghostfields Hphysical Hvalid Hmask.
  iIntros "Hstack". unfold runtime_wp.
  iApply wp_fupd.
  iEval (unfold stack_own) in "Hstack".
  destruct (field_values_match_exists formals binders atoms store
    (physical_field_initializers fields))
    as [values Hvalues].
  iApply (LegacyLifting.wp_alloc_expr
    (runtime_stack_id _ runtime)
    (LegacyLang.StackFrame
      (concrete_locals (runtime_names _ runtime)
        (interp_store formals binders atoms store)))
    (runtime_physical_field_initializers (runtime_names _ runtime) fields)
    values (runtime_ghost_field_names fields)
    (runtime_variable (runtime_names _ runtime) target) mask
    with "Hstack").
  - exact (field_values_match_steps runtime formals binders atoms store
      (physical_field_initializers fields) values Hvalues).
  - rewrite (field_values_match_names formals binders atoms store
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
    iMod (allocated_ghost_fields_alloc runtime formals binders atoms store
      (ghost_field_initializers fields) address mask with "Hghost") as "Hghost".
    { apply runtime_packed_ghost_field_names_nodup. exact Hghostfields. }
    { exact Hvalid. }
    { exact Hmask. }
    iModIntro. iSplit; first done. iExists address.
    iSplitL "Hstack".
    + unfold stack_own. simpl. rewrite concrete_locals_update_store.
      iExact "Hstack". apply runtime_names_nodup.
    + iSplitL "Hfields".
      * iApply (field_values_match_own runtime formals binders atoms store
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
End ConcreteModelCore.

(** Legacy module facade.  [Include] re-exports the static naming and runtime
    translation API from [ConcreteModelCore] without forwarding each of its
    declarations.  Only the semantic-module fields are specialized to the
    resource module, preserving the original [SEMANTIC_CONFIG] surface. *)
Module ConcreteModel (Resources : RUNTIME_RESOURCES).
Module Config := StaticRuntimeConfiguration Resources.
Include ConcreteModelCore Config.

Global Instance legacy_runtimeG : runtimeG Resources.Σ :=
  {| runtime_simpLangG := Resources.simpLangG0;
     runtime_invTokenG := Resources.invTokenG0;
     runtime_ghost_namespace := Resources.ghost_heap_namespace;
     runtime_ghost_own := Resources.ghost_own;
     runtime_ghost_own_timeless := Resources.ghost_own_timeless;
     runtime_ghost_alloc := Resources.ghost_alloc;
     runtime_ghost_update := Resources.ghost_update |}.

Definition PROP : bi := iPropI Resources.Σ.
Local Instance concrete_simpLangG : LegacyLifting.simpLangG Resources.Σ :=
  runtime_simpLangG.
Local Instance concrete_invTokenG : Legacy.invTokenG Resources.Σ :=
  runtime_invTokenG.
Local Instance concrete_heapG : LegacyGhost.heapG Resources.Σ :=
  @core_heapG Resources.Σ legacy_runtimeG.
Local Instance concrete_irisG : irisGS LegacyLang.simp_lang Resources.Σ :=
  @core_irisG Resources.Σ legacy_runtimeG.
Local Instance concrete_invtoken_inG : inG Resources.Σ (authR Legacy.inv_argsUR) :=
  @core_invtoken_inG Resources.Σ legacy_runtimeG.

Definition bi_affine : BiAffine PROP := _.

(** These four definitions deliberately retain their original bodies.  A
    number of legacy proofs unfold exactly one of these names before
    rewriting, so aliases to the generic core would be one delta step too
    opaque for that proof style. *)
Definition stack_own Γ (runtime : stack_context Γ)
    (store : concrete_store Γ) : bi_car PROP :=
  LegacyGhost.stack_frame_own (runtime_stack_id _ runtime)
    (LegacyLang.StackFrame (concrete_locals (runtime_names _ runtime) store)).

Lemma stack_own_exclusive Γ (runtime : stack_context Γ)
    (left right : concrete_store Γ) :
  stack_own Γ runtime left ∗ stack_own Γ runtime right ⊢ False.
Proof.
  unfold stack_own.
  iIntros "[Hleft Hright]".
  iApply (LegacyGhost.stack_frame_own_exclusive with "Hleft Hright").
Qed.

Definition field_own field
    (location : tval TRef) (chunk : tval (Logic.field_type field)) :
    bi_car PROP :=
  match location with
  | VRef address =>
      LegacyGhost.heap_maps_to (LegacyLang.Loc address)
        (Resources.field_name field) 1 (tval_to_val chunk)
  end.

Definition ghost_own field
    (location : tval TRef) (chunk : tval (Logic.field_type field)) :
    bi_car PROP :=
  Resources.ghost_own field location chunk.

Global Instance legacy_ghost_own_timeless field location chunk :
  Timeless (ghost_own field location chunk) :=
  Resources.ghost_own_timeless field location chunk.

Definition invariant_own invariant
    (values : tval_list (Logic.invariant_args invariant)) : bi_car PROP :=
  @own Resources.Σ (authR Legacy.inv_argsUR) concrete_invtoken_inG
    (Legacy.invtoken_names (Resources.invariant_name invariant))
    (◯ ({[tval_list_to_rich_list values]} : gset (list Legacy.val))).

Definition semantic_data : Translation.semantic_config_data PROP :=
  {| Translation.data_bi_affine := bi_affine;
     Translation.data_stack_context := stack_context;
     Translation.data_empty_stack_context := empty_stack_context;
     Translation.data_stack_own := stack_own;
     Translation.data_stack_own_exclusive := stack_own_exclusive;
     Translation.data_field_own := field_own;
     Translation.data_ghost_own := ghost_own;
     Translation.data_invariant_own := invariant_own |}.
End ConcreteModel.


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
    shape of [TUnfold]/[TFold]: they carry no linear closing continuation
    tying an unfold to its matching fold.  That pairing is established by the
    certified atomicity region, so the semantic control contract stays
    abstract here. *)
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

(** Term-level operation interfaces for an initialized runtime.  These are the
    dynamic counterparts of the two module types above: a proof may construct
    either record after choosing its [runtimeG] names. *)
Module TermControlOperations.
Section WithModel.
Context {PROP : bi} (Model : Translation.semantic_config_data PROP).
Let term_bi_affine : BiAffine PROP :=
  @Translation.data_bi_affine PROP Model.
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
End TermControlOperations.

(** Concrete term-level operation model.  [Config] is static while [RG] is an
    ordinary Section value, so [control_operations] can be formed after the
    adequacy proof has allocated all required ghost names. *)
Module ConcreteControlCore (Config : RUNTIME_CONFIGURATION).
Module Model := ConcreteModelCore Config.
Section WithRuntime.
Context {Σ : gFunctors} `{RG : runtimeG Σ}.
Local Instance core_simpLangG : LegacyLifting.simpLangG Σ :=
  runtime_simpLangG.
Local Instance core_invTokenG : Legacy.invTokenG Σ := runtime_invTokenG.
Local Instance core_heapG : LegacyGhost.heapG Σ :=
  LegacyLifting.simpLangG_gen_heapG.
Local Instance core_irisG : irisGS LegacyLang.simp_lang Σ :=
  @Model.core_irisG Σ RG.
Local Existing Instance weakestpre.wp'.
Local Notation iProp := (iProp Σ).

Definition semantic_data : Translation.semantic_config_data (iPropI Σ) :=
  @Model.core_semantic_data Σ RG.

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
    iPoseProof (@wp_frame_r HasLc LegacyLang.simp_lang Σ core_irisG
      NotStuck (Model.runtime_mask mask_pre) _
      (fun result =>
        (⌜result = LegacyLang.LitUnit⌝ ∗
         |={Model.runtime_mask mask_pre, Model.runtime_mask mask_post}=> P)%I)
      R with "[$Hwp $HR]") as "Hwp";
    iApply (wp_mono with "Hwp");
    iIntros (result) "[[%Hresult Hpost] HR]"; iSplit; first done;
    iMod "Hpost"; iModIntro; iFrame.
Qed.

Definition procedure_operations :
    @TermControlOperations.procedure_operations_data (iPropI Σ)
      semantic_data :=
  @TermControlOperations.ProcedureOperationsData (iPropI Σ) semantic_data
    (@procedure_wp) procedure_mono procedure_frame.

Definition operation_wp {Γ} (Procedures :
    @TermControlOperations.procedure_operations_data (iPropI Σ)
      semantic_data) (runtime : Model.stack_context Γ)
    (statement : stmt Γ) (mask_pre mask_post : Hoare.mask)
    (post : iProp) : iProp :=
  match statement with
  | TCall _ _ _ _ | TSpawn _ _ _ =>
      TermControlOperations.term_procedure_wp semantic_data Procedures Γ
        runtime statement mask_pre mask_post post
  | TUnfold _ _ _ | TFold _ _ _ =>
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
    @TermControlOperations.procedure_operations_data (iPropI Σ)
      semantic_data) :
    @TermControlOperations.control_operations_data (iPropI Σ)
      semantic_data :=
  @TermControlOperations.ControlOperationsData (iPropI Σ) semantic_data
    (fun Γ => @operation_wp Γ Procedures) (operation_mono Procedures)
    (operation_frame Procedures) (@atomic_wp) atomic_mono atomic_frame
    atomic_intro.

Definition concrete_control_operations :
    @TermControlOperations.control_operations_data (iPropI Σ)
      semantic_data := control_operations procedure_operations.
End WithRuntime.
End ConcreteControlCore.


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
              (Model.runtime_physical_field_initializers
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
         (IR.symbolize_expr store condition) = Some (VBool true)⌝ ⊢ P) ->
    (Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗
       frame ∗ ⌜interp_expr formals binders atoms
         (IR.symbolize_expr store condition) ≠ Some (VBool true)⌝ ⊢ Q) ->
    Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗
      frame ⊢ branch_wp Γ runtime condition mask P Q.
  Proof.
    intros Hthen Helse.
    destruct (interp_expr formals binders atoms
      (IR.symbolize_expr store condition)) as [value|] eqn:Hvalue.
    - dependent destruction value. destruct b.
      + iIntros "[Hstack Hframe]". iLeft. iApply Hthen. iFrame.
        iPureIntro. reflexivity.
      + iIntros "[Hstack Hframe]". iRight. iApply Helse. iFrame.
        iPureIntro. congruence.
    - exfalso. destruct (interp_expr_total formals binders atoms
        (IR.symbolize_expr store condition)) as [value Htotal].
      congruence.
  Qed.
End Primitives.

(** The same primitive implementation packaged for the term-level validity
    path.  No proof is duplicated: the fields reuse the verified legacy
    primitive lemmas above. *)
Definition term_primitives :
    @Validation.TermSemantics.continuation_primitives_data
      Model.PROP Model.semantic_data.
Proof.
  refine (@Validation.TermSemantics.ContinuationPrimitivesData
    Model.PROP Model.semantic_data
    (@leaf_wp) (@branch_wp) (@Operations.atomic_wp)
    Primitives.leaf_mono Primitives.leaf_frame Primitives.leaf_skip
    Primitives.leaf_assert Operations.atomic_mono Operations.atomic_frame
    Primitives.branch_mono Primitives.branch_frame Primitives.branch_select).
Defined.

Definition term_statement_interface :
    @Validation.TermSemantics.statement_wp_data
      Model.PROP Model.semantic_data :=
  Validation.TermSemantics.ContinuationExecution.interface
    Model.semantic_data term_primitives.

Module StatementWP := VSemantics.ContinuationExecution Primitives.


End ConcreteExecution.

Import Translation.Assertions.

Module TermSemanticLeafContracts
    (Contracts : Hoare.ResourceHoare.RESOURCE_CONTRACT_ENV_BASE).
Module RI := Hoare.ResourceHoare.ContractInstances Contracts.
Section WithModel.
Context {PROP : bi} (Model : Translation.semantic_config_data PROP).
Context `{!FUpd PROP}.
Local Notation iProp := (bi_car PROP).

Record semantic_leaf_contracts_data := SemanticLeafContractsData {
  term_predicates : atom_env ->
    Translation.TermSemantics.predicate_semantics;
  term_predicates_timeless : forall atoms predicate values,
    Timeless (term_predicates atoms predicate values);
  term_predicates_stable : forall left_atoms right_atoms,
    stable_atoms_agree left_atoms right_atoms ->
    forall predicate values,
      term_predicates left_atoms predicate values ≡
      term_predicates right_atoms predicate values;
  (** The instantiated predicate body agrees with the abstract predicate
      atom.  Stated over the resource core: the instantiation is a total
      function of the arguments, so there is no relation to destruct and no
      reindexing step, and the obligation never mentions the assertion
      representation. *)
  term_predicate_instantiation_valid : forall {F Δ}
      (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
      predicate (expressions : expr_list F Δ (Logic.predicate_args predicate)),
    Translation.TermSemantics.interp_core Model (term_predicates atoms)
      formals binders atoms
      (RI.instantiated_predicate predicate expressions) ≡
    Translation.TermSemantics.interp_core Model (term_predicates atoms)
      formals binders atoms
      (Translation.Resource.CPredicate predicate expressions);
}.
End WithModel.
End TermSemanticLeafContracts.

(** Term-level interface for the one region primitive whose implementation is
    specific to invariant transitions.  Keeping it separate lets adequacy
    construct it after allocating [runtimeG]. *)
Module TermInvariantRegionOperations.
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
End TermInvariantRegionOperations.

(** Dynamic counterpart of [FancyUpdateInvariantRegionOperations]. *)
Module ConcreteInvariantRegionOperationsCore (Config : RUNTIME_CONFIGURATION).
Module Control := ConcreteControlCore Config.
Module Model := Control.Model.
Section WithRuntime.
Context {Σ : gFunctors} `{RG : runtimeG Σ}.
Local Instance core_simpLangG : LegacyLifting.simpLangG Σ := runtime_simpLangG.
Local Instance core_invTokenG : Legacy.invTokenG Σ := runtime_invTokenG.
Local Instance core_irisG : irisGS LegacyLang.simp_lang Σ :=
  @Model.core_irisG Σ RG.
Local Existing Instance weakestpre.wp'.
Local Notation iProp := (iProp Σ).

Definition region_model : GenericRegions.region_model_data (iPropI Σ) :=
  @GenericRegions.RegionModelData (iPropI Σ)
    (fun Γ => Model.stack_context Γ) Model.ambient_mask.

(** Export the transparent components of the region-model record.  Clients
    outside this functor need these equalities to transport between the
    record projections expected by the generic interpreter and the concrete
    runtime types used by endpoint WPs. *)
Lemma region_model_stack_context_eq Γ :
  GenericRegions.term_region_stack_context region_model Γ =
    Model.stack_context Γ.
Proof. reflexivity. Qed.

Lemma region_model_ambient_mask_eq :
  GenericRegions.term_region_ambient_mask region_model = Model.ambient_mask.
Proof. reflexivity. Qed.

Definition operation_wp {Γ} (_ : Model.stack_context Γ) (ambient : Model.ambient_mask)
    (entry : GenericRegions.Atomicity.analysis_state) (statement : stmt Γ)
    (exit : GenericRegions.Atomicity.analysis_state) (post : iProp) : iProp :=
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

Definition operations :
    @TermInvariantRegionOperations.invariant_region_operations_data (iPropI Σ)
      region_model :=
  @TermInvariantRegionOperations.InvariantRegionOperationsData (iPropI Σ)
    region_model (@operation_wp) operation_mono operation_frame.
End WithRuntime.
End ConcreteInvariantRegionOperationsCore.

(** Dynamic counterpart of [OperationalGenericRegionPrimitives].  It turns
    the term-level control and invariant-operation records into the generic
    certificate interpreter primitives. *)
Module OperationalGenericRegionPrimitivesCore (Config : RUNTIME_CONFIGURATION).
Module Control := ConcreteControlCore Config.
Module Model := Control.Model.
Module InvariantOperations := ConcreteInvariantRegionOperationsCore Config.

(** Construct a runtime stack context through the model's public alias.  Keep
    this adapter at the functor boundary: clients must not rely on reduction
    through the nested [Control.Model] alias. *)
Definition make_stack_context {Γ} (stack_id : LegacyLang.stack_id)
    (names : named_context Γ) (Hnames : NoDup (Model.runtime_variables names)) :
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
    ↑(Config.invariant_namespace invariant) ∪ Model.invariant_mask mask.
Proof. apply Model.invariant_mask_union_singleton. Qed.

Lemma active_runtime_mask_access ambient entry invariant opened inner :
  GenericRegions.Atomicity.analysis_open opened =
    {[invariant]} ∪ GenericRegions.Atomicity.analysis_open entry ->
  GenericRegions.Atomicity.analysis_open inner =
    GenericRegions.Atomicity.analysis_open opened ->
  Model.active_runtime_mask ambient inner =
    Model.active_runtime_mask ambient entry ∖
      ↑(Config.invariant_namespace invariant).
Proof.
  intros Hopened Hinner.
  rewrite (Model.active_runtime_mask_same_open ambient inner opened Hinner).
  apply Model.active_runtime_mask_open. exact Hopened.
Qed.

Section WithRuntime.
Context {Σ : gFunctors} `{RG : runtimeG Σ}.
Local Instance core_simpLangG : LegacyLifting.simpLangG Σ := runtime_simpLangG.
Local Instance core_invTokenG : Legacy.invTokenG Σ := runtime_invTokenG.
Local Instance core_heapG : LegacyGhost.heapG Σ :=
  LegacyLifting.simpLangG_gen_heapG.
Local Instance core_irisG : irisGS LegacyLang.simp_lang Σ :=
  @Model.core_irisG Σ RG.
Local Existing Instance weakestpre.wp'.
Local Notation iProp := (iProp Σ).

Definition semantic_data : Translation.semantic_config_data (iPropI Σ) :=
  @Control.semantic_data Σ RG.

Lemma semantic_stack_own_update {Γ F Δ t}
    (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (target : pvar Γ t) (value : tval t) :
  Translation.data_stack_own semantic_data runtime
      (interp_store formals (binder_cons value binders) atoms
        (IR.update_store_with_bound store target)) ⊣⊢
    LegacyGhost.stack_frame_own (Model.runtime_stack_id _ runtime)
      (LegacyLang.StackFrame
        (<[Model.runtime_variable (Model.runtime_names _ runtime) target :=
            Model.tval_to_val value]>
          (LegacyLang.locals (LegacyLang.StackFrame
            (Model.concrete_locals (Model.runtime_names _ runtime)
              (interp_store formals binders atoms store)))))).
Proof.
  unfold semantic_data, Control.semantic_data, Model.core_semantic_data.
  simpl. unfold Model.core_stack_own.
  rewrite Model.concrete_locals_update_store; [reflexivity|].
  apply Model.runtime_names_nodup.
Qed.
Definition region_model : GenericRegions.region_model_data (iPropI Σ) :=
  @GenericRegions.RegionModelData (iPropI Σ)
    (fun Γ => Model.stack_context Γ) Model.ambient_mask.

Lemma region_model_stack_context_eq Γ :
  GenericRegions.term_region_stack_context region_model Γ =
    Model.stack_context Γ.
Proof. reflexivity. Qed.

Lemma region_model_ambient_mask_eq :
  GenericRegions.term_region_ambient_mask region_model = Model.ambient_mask.
Proof. reflexivity. Qed.

Definition ambient_physical_leaf_wp {Γ} (runtime : Model.stack_context Γ)
    (ambient : coPset) (entry : GenericRegions.Atomicity.analysis_state)
    (statement : LegacyLang.runtime_stmt) (post : iProp) : iProp :=
  Model.runtime_wp (Model.active_runtime_mask ambient entry) statement
    (fun result => (⌜result = LegacyLang.LitUnit⌝ ∗ post)%I).

Definition ambient_leaf_wp {Γ} (runtime : Model.stack_context Γ)
    (ambient : coPset) (entry : GenericRegions.Atomicity.analysis_state)
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
          (Config.field_name field) (Model.runtime_stack_id _ runtime)) post
  | TFieldWrite _ field base expression =>
      ambient_physical_leaf_wp runtime ambient entry
        (LegacyLang.RTFldWr
          (Model.runtime_expr (Model.runtime_names _ runtime) base)
          (Config.field_name field)
          (Model.runtime_expr (Model.runtime_names _ runtime) expression)
          (Model.runtime_stack_id _ runtime)) post
  | TAlloc _ target fields =>
      ambient_physical_leaf_wp runtime ambient entry
        (LegacyLang.RTAlloc
          (Model.runtime_variable (Model.runtime_names _ runtime) target)
          (Model.runtime_physical_field_initializers
            (Model.runtime_names _ runtime) fields)
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
  iPoseProof (@wp_frame_r HasLc LegacyLang.simp_lang Σ core_irisG
    NotStuck (Model.active_runtime_mask ambient entry)
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

Definition operation_wp {Γ}
    (Operations : @TermControlOperations.control_operations_data (iPropI Σ)
      semantic_data)
    (InvariantOps :
      @TermInvariantRegionOperations.invariant_region_operations_data (iPropI Σ)
        region_model)
    (runtime : Model.stack_context Γ) (ambient : Model.ambient_mask)
    (entry : GenericRegions.Atomicity.analysis_state) (statement : stmt Γ)
    (exit : GenericRegions.Atomicity.analysis_state) (post : iProp) : iProp :=
  match RegionSyntax.view statement with
  | TypedAnalysisView.ViewLeaf => ambient_leaf_wp runtime ambient entry statement post
  | TypedAnalysisView.ViewUnfold _ | TypedAnalysisView.ViewFold _ =>
      TermInvariantRegionOperations.term_invariant_operation_wp region_model
        InvariantOps Γ runtime ambient entry statement exit post
  | TypedAnalysisView.ViewAtomic body =>
      TermControlOperations.term_atomic_wp semantic_data Operations Γ runtime body
        (GenericRegions.Atomicity.analysis_mask entry)
        (GenericRegions.Atomicity.analysis_mask exit) post
  | _ => False%I
  end.

Definition branch_wp {Γ}
    (runtime : Model.stack_context Γ) (_ : Model.ambient_mask)
    (entry : GenericRegions.Atomicity.analysis_state) (statement : stmt Γ)
    (_ _ : GenericRegions.Atomicity.analysis_state) (then_wp else_wp : iProp) : iProp :=
  match statement with
  | TIf _ _ _ _ => (then_wp ∨ else_wp)%I
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
    @TermControlOperations.control_operations_data (iPropI Σ) semantic_data)
    (InvariantOps :
      @TermInvariantRegionOperations.invariant_region_operations_data (iPropI Σ)
        region_model) :
    @GenericRegions.TermSemantics.region_primitives_data (iPropI Σ) region_model :=
  @GenericRegions.TermSemantics.RegionPrimitivesData (iPropI Σ) region_model
    (fun Γ => @operation_wp Γ Operations InvariantOps) (@branch_wp)
    (operation_mono Operations InvariantOps) (operation_frame Operations InvariantOps)
    branch_mono branch_frame.

(** The combined interpreter owns a single instantiation of the model functor.
    Rebuild the small fancy-update record at that exact model identity; Rocq
    functor applications are generative, so the separately exported invariant
    core cannot be used definitionally here. *)
Definition concrete_invariant_operation_wp {Γ} (_ : Model.stack_context Γ)
    (ambient : Model.ambient_mask) (entry : GenericRegions.Atomicity.analysis_state)
    (statement : stmt Γ) (exit : GenericRegions.Atomicity.analysis_state)
    (post : iProp) : iProp :=
  match statement with
  | TUnfold _ _ _ | TFold _ _ _ =>
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
    @TermInvariantRegionOperations.invariant_region_operations_data (iPropI Σ)
      region_model :=
  @TermInvariantRegionOperations.InvariantRegionOperationsData (iPropI Σ)
    region_model (@concrete_invariant_operation_wp)
    concrete_invariant_operation_mono concrete_invariant_operation_frame.

Definition interpreter (Operations :
    @TermControlOperations.control_operations_data (iPropI Σ) semantic_data)
    (InvariantOps :
      @TermInvariantRegionOperations.invariant_region_operations_data (iPropI Σ)
        region_model) :
    @GenericRegions.TermSemantics.interpreter_data (iPropI Σ) region_model :=
  GenericRegions.TermSemantics.interpreter region_model
    (primitives Operations InvariantOps).
End WithRuntime.
End OperationalGenericRegionPrimitivesCore.

(** Fully concrete dynamic generic-region interpreter, suitable for a
    proof-time allocated [runtimeG] instance. *)
Module ConcreteGenericRegionExecutionCore (Config : RUNTIME_CONFIGURATION).
Module Primitives := OperationalGenericRegionPrimitivesCore Config.
Module Control := Primitives.Control.
Section WithRuntime.
Context {Σ : gFunctors} `{RG : runtimeG Σ}.

Definition interpreter := @Primitives.interpreter Σ RG
  (@Control.concrete_control_operations Σ RG)
  (@Primitives.concrete_invariant_operations Σ RG).
End WithRuntime.
End ConcreteGenericRegionExecutionCore.

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


End Make.
End TypedRuntime.
