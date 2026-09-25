From Coq Require Import List Program.Equality ClassicalEpsilon.
From stdpp Require Import sets.
From iris.base_logic.lib Require Import iprop invariants fancy_updates.
From iris.proofmode Require Import proofmode.
From raven_iris.rich_raven_lang Require Import typed_core
  typed_counter_monotonic.

Import ListNotations.
Open Scope list_scope.

(** Downstream normalization-readiness and final program-packaging layer for
    the typed monotonic-counter example.  The expensive runtime, normalization,
    and soundness functors are instantiated once by [typed_counter_monotonic]
    and are only imported here. *)
Module TypedCounterMonotonicPackaging.

Import TypedCounterMonotonic.
Import TypedCore TypedCounterMonotonic.IR TypedCounterMonotonic.IR.Core
  TypedCounterMonotonic.IR.Assertions.

Section CounterResourceProgramPackaging.
Context {Σ : iris.base_logic.lib.iprop.gFunctors}
  (RG : Runtime.runtimeG Σ).

Lemma counter_runtime_cost_model_sound :
  CounterSoundness.RegionExecution.Primitives.Model.runtime_cost_model_sound
    counter_cost_model.
Proof.
  intros Γ names stack statement physical Hview Hruntime.
  destruct statement; cbn in Hview; try discriminate;
    cbn [counter_cost_model].
  all: try exact I.
  - cbn [CounterSoundness.RegionExecution.Primitives.Model.runtime_stmt]
      in Hruntime.
    inversion Hruntime; subst. apply Runtime.LegacyLang.atomic_assign.
  - cbn [CounterSoundness.RegionExecution.Primitives.Model.runtime_stmt]
      in Hruntime.
    inversion Hruntime; subst. apply Runtime.LegacyLang.atomic_fld_rd.
  - cbn [CounterSoundness.RegionExecution.Primitives.Model.runtime_stmt]
      in Hruntime.
    inversion Hruntime; subst. apply Runtime.LegacyLang.atomic_fld_wr.
  - cbn [CounterSoundness.RegionExecution.Primitives.Model.runtime_stmt]
      in Hruntime.
    inversion Hruntime; subst. apply Runtime.LegacyLang.atomic_alloc.
Qed.

End CounterResourceProgramPackaging.

(* ================================================================== *)
(** * Instantiating the analyzed adequacy boundary

    [raven_analyzed_library_soundness] is parameterized over a
    registration, a ghost-resource factory, a leaf-contract builder, an
    operational-evidence builder and a program builder.  Nothing in the
    development had ever supplied any of them.  This section does, for
    the monotonic counter. *)

(** ** Leaf contracts

    The counter declares no predicates ([predicate_body _ := CPure
    False]), so the leaf interpretation is the constant [False] and the
    instantiation obligation is discharged from the shape of
    [instantiated_predicate] at a [CPure False] body. *)
Section CounterLeafContracts.
Context {Sigma : iris.base_logic.lib.iprop.gFunctors}.
Context `{!invGS Sigma}.

Definition counter_leaf (RG : Runtime.runtimeG Sigma) :
  @CounterSoundness.TermLeaf.semantic_leaf_contracts_data
    (iPropI Sigma) (@CounterSoundness.semantic_data Sigma RG).
Proof.
  unshelve econstructor.
  { exact (fun _ _ _ => False%I). }
  - abstract (intros; apply _).
  - abstract (intros; reflexivity).
  (* The resource-shaped obligation is a plain equivalence between the
     instantiated body and the predicate atom: the instantiation is a total
     function of the arguments, so there is no relation to destruct and no
     reindexing to discharge.  This example declares no predicate bodies, so
     both sides are [False]. *)
  - abstract (intros F Delta formals binders atoms predicate expressions;
    unfold CounterSoundness.TermLeaf.RI.instantiated_predicate;
    unfold CounterResourceContracts.predicate_body;
    cbn;
    iSplit; [iIntros "[]" | iIntros "H"; iDestruct "H" as (v) "[_ []]"]).
Defined.

(** ** The ghost-resource factory

    The factory interface is indexed by the concrete [simpLangG], so a
    faithful implementation may now connect the allocation rule's
    [ghost_dom_frag] witness to exclusive ownership of a ghost cell.  The
    present counter packaging still uses the smaller validity-only
    interpretation: its currently declared contracts are [CPure True], so
    the example does not yet rely on that exclusivity. *)
Definition counter_ghost_own
    (_ : Runtime.LegacyLifting.simpLangG Sigma) (_ : unit)
    (field : TypedCore.field_id)
    (location : Runtime.IR.Core.tval TypedCore.TRef)
    (chunk : Runtime.IR.Core.tval (CounterLogic.field_type field)) :
    iProp Sigma :=
  (⌜Runtime.IR.Core.tval_ra_valid chunk⌝)%I.

Definition counter_ghost_factory :
  Runtime.runtime_ghost_resource_factory Sigma
    RuntimeConfiguration.ghost_heap_namespace.
Proof.
  unshelve econstructor.
  { exact (fun _ => unit). }
  { exact counter_ghost_own. }
  - abstract (intros; unfold counter_ghost_own; apply _).
  - abstract (intros simpLangG0 resource E field resource_name field_name
      address chunk Hfield HE Hvalid;
    iIntros "_"; iModIntro; unfold counter_ghost_own; iPureIntro;
    set (t := CounterLogic.field_type field) in *; clearbody t;
    generalize (eq_sym Hfield); clear Hfield; intro Heq; destruct Heq;
    exact Hvalid).
  - abstract (intros simpLangG0 resource E field location old_chunk new_chunk
      Hfpu;
    unfold counter_ghost_own; iIntros "_"; iModIntro; iPureIntro;
    revert Hfpu;
    set (t := CounterLogic.field_type field) in *; clearbody t;
    destruct t; dependent destruction old_chunk;
      dependent destruction new_chunk; cbn; try contradiction;
    intro Hfpu;
    apply (proj1 (proj2 (mono_nat_ra.mn_fpuAxiom _ _ Hfpu)))).
  - abstract (intros simpLangG0; iModIntro; iExists tt; done).
Defined.

End CounterLeafContracts.

(* ================================================================== *)
(** * The analyzed program certificate, and the library boundary *)

(** Which body answers for which registered procedure.  The [Prop]-to-[Type]
    crossing is the same one the retired legacy dispatch used, but the
    cost model is carried *inside* the existential: the chosen body is
    otherwise opaque, and the program record's cost-soundness field has to
    see it. *)
Definition packed_analyzed_cost (packed : Runtime.IR.packed_typed_procedure) :
    CounterSoundness.packed_resource_analyzed_body packed ->
    Runtime.GenericRegions.Atomicity.cost_model :=
  match packed with
  | existT _ (existT _ procedure) =>
      fun body => CounterSoundness.resource_analyzed_body_cost procedure _ body
  end.

Definition counter_analyzed_dispatch :
  forall packed,
    List.In packed
      (procedure_entries CounterProcedureContracts.procedures) ->
    { body : CounterSoundness.packed_resource_analyzed_body packed |
      packed_analyzed_cost packed body = counter_cost_model }.
Proof.
  intros packed Hin.
  assert (Hexists : exists
      body : CounterSoundness.packed_resource_analyzed_body packed,
      packed_analyzed_cost packed body = counter_cost_model).
  { simpl in Hin.
    destruct Hin as [Hin | [Hin | [Hin | []]]].
    - dependent destruction Hin. exists read_analyzed_body. reflexivity.
    - dependent destruction Hin. exists incr_analyzed_body. reflexivity.
    - dependent destruction Hin. exists make_analyzed_body. reflexivity. }
  exact (constructive_indefinite_description _ Hexists).
Defined.

Definition counter_analyzed_bodies packed Hin :
    CounterSoundness.packed_resource_analyzed_body packed :=
  proj1_sig (counter_analyzed_dispatch packed Hin).

Lemma counter_analyzed_bodies_cost packed Hin :
  packed_analyzed_cost packed (counter_analyzed_bodies packed Hin) =
    counter_cost_model.
Proof. exact (proj2_sig (counter_analyzed_dispatch packed Hin)). Qed.

(** The same fact in unpacked form, which is the shape the program
    record's cost-soundness field presents. *)
Lemma counter_analyzed_body_cost {Gamma identity}
    (procedure : Runtime.IR.typed_procedure Gamma identity)
    (Hin : List.In (pack_typed_procedure procedure)
      (procedure_entries CounterProcedureContracts.procedures)) :
  CounterSoundness.resource_analyzed_body_cost procedure
      (CounterResourceContracts.required_mask
        (Runtime.IR.procedure_identity Gamma identity procedure))
      (counter_analyzed_bodies (pack_typed_procedure procedure) Hin) =
    counter_cost_model.
Proof. exact (counter_analyzed_bodies_cost (pack_typed_procedure procedure) Hin). Qed.

Section CounterAnalyzedProgram.
Context {Sigma : iris.base_logic.lib.iprop.gFunctors}.

(** Registry coverage, proved once for *any* body of this program rather
    than per procedure: the footprint is bounded by the body's own exit
    mask, and every counter procedure's exit mask is the union of a
    required and a granted mask, each of which is [counter_mask] or [∅]. *)
Lemma counter_analyzed_registered
    Gamma identity (procedure : IR.typed_procedure Gamma identity)
    (Hin : List.In (pack_typed_procedure procedure)
      (procedure_entries CounterProcedureContracts.procedures)) :
  Runtime.GenericRegions.Atomicity.certificate_footprint
    (CounterSoundness.CertifiedNormalization.resource_analyzed_certificate
      (CounterSoundness.resource_analyzed_body_triple _ _
        (counter_analyzed_bodies (pack_typed_procedure procedure) Hin)))
  ⊆ CounterSoundness.term_registered_invariants
      counter_program_registration .
Proof.
  set (body := counter_analyzed_bodies (pack_typed_procedure procedure) Hin).
  etrans.
  - eapply
      Runtime.GenericRegions.Atomicity.closed_coherent_certificate_footprint_subset_exit_mask.
    + exact (CounterSoundness.resource_analyzed_body_conditionals _ _ body).
    + exact (CounterSoundness.resource_analyzed_body_exit_closed _ _ body).
  - rewrite (CounterSoundness.resource_analyzed_body_exit_mask _ _ body).
    unfold CounterSoundness.term_registered_invariants,
      counter_program_registration. simpl.
    unfold CounterResourceContracts.required_mask,
      CounterResourceContracts.granted_mask,
      CounterResourceContracts.required_mask,
      CounterResourceContracts.granted_mask.
    destruct (Pos.eqb (Runtime.IR.procedure_identity Gamma identity procedure)
      make_procedure); unfold counter_mask; set_solver.
Qed.

Definition counter_analyzed_program (RG : Runtime.runtimeG Sigma) :
  CounterSoundness.resource_analyzed_program counter_program_registration.
Proof.
  unshelve econstructor.
  { exact counter_analyzed_bodies. }
  - intros Gamma identity procedure Hin.
    rewrite (counter_analyzed_body_cost procedure Hin).
    apply counter_runtime_cost_model_sound.
  - intros. apply counter_analyzed_registered.
Defined.

End CounterAnalyzedProgram.

(** ** The library boundary, instantiated

    Everything [raven_analyzed_library_soundness] is parameterized over is
    now supplied by this example: the registration, the ghost-resource
    factory, the leaf contracts, the generic producer-completeness theorem,
    and the analyzed program certificate. *)
Section CounterLibrarySoundness.
Context {Sigma : iris.base_logic.lib.iprop.gFunctors}.
Context `{!invGS Sigma}.
Context `{!Runtime.LegacyGhost.heapGpreS Sigma}.
Context `{!Runtime.Legacy.invTokenGpreS Sigma}.
Definition counter_library_soundness :=
  CounterSoundness.raven_analyzed_library_soundness
    counter_program_registration counter_ghost_factory counter_leaf
    CounterSoundness.resource_analyzed_normalization_complete_from_raw_access_cut
    counter_analyzed_program.

End CounterLibrarySoundness.

End TypedCounterMonotonicPackaging.
