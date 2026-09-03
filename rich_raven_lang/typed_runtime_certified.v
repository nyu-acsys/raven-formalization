From Coq Require Import List String ZArith Program.Equality Lia.
From stdpp Require Import countable gmap namespaces sets.

From iris.algebra Require Import auth gset.
From iris.base_logic Require Import fancy_updates.
From iris.base_logic.lib Require Import own invariants.

From raven_iris.simp_raven_lang Require Import lang ghost_state.
From raven_iris.rich_raven_lang Require Import
  typed_core typed_analysis_view typed_assertion typed_ir typed_translation
  typed_validity typed_region typed_runtime.

Import ListNotations.
Import weakestpre.
Open Scope list_scope.

(** Certificate-indexed runtime validity is kept separate from the executable
    typed runtime so that changes to the large structural proof do not force
    recompilation of the concrete semantic infrastructure. *)
Module TypedRuntimeCertified.

Module Make (LegacyRAs : ra_base.RA_CONFIG)
    (Logic : TypedAssertion.LOGIC_SIGNATURE).

Module Runtime := TypedRuntime.Make LegacyRAs Logic.
Include Runtime.
Module Hoare := Runtime.Validation.Hoare.
Import TypedCore TypedIR Core IR Translation.

Module CertifiedRegionValidity (Resources : RUNTIME_RESOURCES)
    (Contracts : Hoare.CONTRACT_ENV)
    (ProcedureContracts : Hoare.PROCEDURE_CONTRACT_COHERENCE Contracts)
    (Leaf : DEFAULT_SEMANTIC_LEAF_CONTRACTS Resources Contracts)
    (Defs : Translation.DEFINITION_ENV).
Module ProcedureBodies := CertifiedProcedureBodies Contracts.
(* Share the certificate module carried by procedure bodies.  Applying
   [CertifiedRegions] a second time here would create a generative copy whose
   dependent certificate records cannot cross the procedure boundary. *)
Module Certified := ProcedureBodies.Certified.
(* Reuse the operation module packaged with [Leaf].  This keeps the model
   carrying stack contexts definitionally identical to the one expected by
   [Leaf.predicate_instantiation_valid]; independently reapplying the
   concrete-operation functor would create a generative model copy. *)
Module InvariantOperations := FancyUpdateInvariantRegionOperations Resources
  Leaf.Operations.
Module ExecutionPrimitives := OperationalGenericRegionPrimitives Resources
  Leaf.Operations InvariantOperations.
Module Execution.
  Module Operations := Leaf.Operations.
  Module Primitives := ExecutionPrimitives.
  Include Primitives.Interpreter.
End Execution.
Module BaseExecution := ConcreteExecution Resources Leaf.Operations.
Module Model := BaseExecution.Model.
Module VSemantics := Leaf.Execution.VSemantics.
Module World := BaseExecution.InvariantWorld Contracts Leaf Defs.
Module Structural := BaseExecution.StructuralValidity Contracts.
Local Notation iProp := (iProp Resources.Σ).
Local Existing Instance Model.concrete_irisG.
Local Existing Instance Model.concrete_heapG.
Local Existing Instance weakestpre.wp'.
Local Instance concrete_wp :
    Wp iProp LegacyLang.runtime_stmt LegacyLang.val stuckness :=
  @weakestpre.wp' HasLc LegacyLang.simp_lang Resources.Σ
    Model.concrete_irisG.
Import Translation.Assertions.

(** Executable layout selected for each registered typed procedure.  Phase 7
    deliberately requires every table entry to have a physical body.  A
    declaration with no body denotes an assumed contract and is therefore not
    part of this verified runtime table; support for such assumptions can be
    added later as a separate specification environment. *)
Parameter runtime_procedure_statement :
  packed_typed_procedure -> LegacyLang.stmt.

Definition runtime_procedure_entry
    (packed : packed_typed_procedure) : LegacyLang.proc :=
  match packed with
  | existT Γ (existT F procedure) =>
      LegacyLang.Proc
        (Resources.procedure_name (procedure_identity Γ F procedure))
        (Model.runtime_procedure_arguments procedure)
        (Model.runtime_procedure_locals procedure)
        (runtime_procedure_statement packed)
  end.

Definition runtime_procedure_layout_configured : Prop :=
  forall (packed : packed_typed_procedure),
    List.In packed (procedure_entries ProcedureContracts.procedures) ->
    match packed with
    | existT Γ (existT F procedure) =>
        procedure_wf procedure /\
        ~ List.In "#ret_val" (named_context_names
          (procedure_variables Γ F procedure)) /\
        forall stack,
          Model.runtime_stmt (Model.runtime_procedure_names procedure) stack
            (procedure_body Γ F procedure) =
          Some (LegacyLang.to_rtstmt stack
            (runtime_procedure_statement packed))
    end.

Parameter configured_runtime_procedure_layout :
  runtime_procedure_layout_configured.

Lemma runtime_procedure_entry_coherent procedure :
  List.In procedure (procedure_entries ProcedureContracts.procedures) ->
  Model.packed_runtime_procedure_registration procedure
    (runtime_procedure_entry procedure).
Proof.
  intros Hin.
  pose proof (configured_runtime_procedure_layout procedure Hin) as Hlayout.
  destruct procedure as [Γ [F procedure]]. simpl in *.
  destruct Hlayout as (Hwf & Hfresh & Hbody).
  constructor; simpl; try reflexivity.
  - apply NoDup_ListNoDup.
    apply Model.runtime_procedure_argument_names_nodup. exact Hwf.
  - apply Model.runtime_procedure_locals_nodup; assumption.
  - apply Model.runtime_procedure_arguments_locals_disjoint; assumption.
  - apply Model.runtime_procedure_return_local; assumption.
  - exact Hbody.
Qed.

Definition registered_procedure_chunk
    (procedure : packed_typed_procedure) : iProp :=
  LegacyGhost.proc_tbl_chunk
    (Resources.procedure_name (packed_procedure_id procedure))
    (runtime_procedure_entry procedure).

Definition all_registered_procedure_chunks : iProp :=
  ([∗ list] procedure ∈ procedure_entries ProcedureContracts.procedures,
    registered_procedure_chunk procedure)%I.

Lemma registered_procedure_chunks_lookup procedures procedure :
  List.In procedure procedures ->
  ([∗ list] entry ∈ procedures, registered_procedure_chunk entry) ⊢
    registered_procedure_chunk procedure.
Proof.
  intros Hin.
  induction procedures as [|head tail IH].
  - inversion Hin.
  - simpl in Hin. destruct Hin as [<- | Hin].
    + rewrite big_sepL_cons. iIntros "[$ _]".
    + rewrite big_sepL_cons.
      iIntros "[_ Htail]".
      iApply (IH Hin). iExact "Htail".
Qed.

Lemma all_registered_procedure_chunks_lookup procedure :
  List.In procedure (procedure_entries ProcedureContracts.procedures) ->
  all_registered_procedure_chunks ⊢ registered_procedure_chunk procedure.
Proof. apply registered_procedure_chunks_lookup. Qed.

Parameter certified_procedure_bodies : forall procedure,
  List.In procedure (procedure_entries ProcedureContracts.procedures) ->
  ProcedureBodies.packed_body_valid procedure.

(** Static/runtime agreement for each selected body cost model.  This is
    semantic configuration evidence, not derivable from the Hoare
    certificate itself. *)
Parameter certified_procedure_body_cost_sound : forall Γ F
    (procedure : typed_procedure Γ F)
    (Hin : List.In (pack_typed_procedure procedure)
      (procedure_entries ProcedureContracts.procedures)) current_mask
    (Hmask : Contracts.required_mask (procedure_identity _ _ procedure) ⊆
      current_mask),
  Model.runtime_cost_model_sound
    (ProcedureBodies.body_cost _ _
      (certified_procedure_bodies (pack_typed_procedure procedure) Hin
        current_mask Hmask)).

(** The operational call rule constructs a fresh frame from evaluated actual
    arguments and canonical values for the registered locals.  This program
    interface states that the procedure's symbolic entry store denotes that
    frame under the shared atom environment.  It is deliberately narrower
    than a body-soundness assumption: it contains no Iris proposition and no
    claim about executing the body. *)
Definition procedure_entry_frames_compatible (atoms : atom_env) : Prop :=
  forall Γ F (procedure : typed_procedure Γ F) values frame,
    let packed : packed_typed_procedure := existT Γ (existT F procedure) in
    let entry := runtime_procedure_entry packed in
    Forall2 (fun variable value =>
      frame.(LegacyLang.locals) !! variable = Some value)
      entry.(LegacyLang.proc_args).*1 (Model.tval_list_to_list values) /\
    (forall variable type,
      (variable, type) ∈ entry.(LegacyLang.proc_local_vars) ->
      exists value,
        frame.(LegacyLang.locals) !! variable = Some value /\
        LegacyLang.val_has_typ value type) /\
    dom frame.(LegacyLang.locals) =
      list_to_set entry.(LegacyLang.proc_args).*1 ∪
      list_to_set entry.(LegacyLang.proc_local_vars).*1 ->
    Model.stack_corresponds (Model.runtime_procedure_names procedure)
      (formal_env_of_values values) empty_binder_env atoms
      (procedure_entry_store _ _ procedure) frame /\
    dom frame.(LegacyLang.locals) = list_to_set
      (Model.runtime_variables (Model.runtime_procedure_names procedure)).

Parameter configured_procedure_entry_frames : forall atoms,
  procedure_entry_frames_compatible atoms.

(** Interpretation-level form of canonical procedure-precondition
    instantiation.  Actual arguments are evaluated once in the caller and
    become the callee's formal environment; contract assertions contain no
    stack assertion, so their phantom program-variable context is reindexed
    independently. *)
Lemma procedure_pre_instantiation_interp
    {callee_variables callee_formals}
    (procedure : typed_procedure callee_variables callee_formals)
    {Γ F Δ} (arguments : expr_list F Δ callee_formals)
    (contract : assertion Γ F Δ)
    (Hinst : Hoare.procedure_pre_instantiation procedure arguments contract)
    (runtime : Model.stack_context Γ)
    (callee_runtime : Model.stack_context callee_variables)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (values : tval_list callee_formals)
    (Harguments : interp_expr_list formals binders atoms arguments =
      Some values) :
  VSemantics.S.interp_assertion (Leaf.predicates atoms)
      runtime formals binders atoms contract ⊣⊢
  VSemantics.S.interp_assertion (Leaf.predicates atoms)
      callee_runtime (formal_env_of_values values) empty_binder_env atoms
      (procedure_precondition _ _ procedure).
Proof.
  destruct Hinst as [after_binders [after_formals
    [Hbound [Hformal Hreindex]]]].
  have Hactuals := interp_expr_list_formal_subst_of_values arguments values
    formals binders atoms Harguments.
  pose proof (VSemantics.S.interp_subst_formals_assertion
    (Leaf.predicates atoms) (expr_list_formal_subst arguments)
    (formal_env_of_values values) formals binders atoms callee_runtime
    Hactuals after_binders after_formals Hformal) as Hformals.
  pose proof (VSemantics.S.interp_subst_bound_assertion
    (Leaf.predicates atoms) empty_bound_subst
    (formal_env_of_values values) empty_binder_env binders atoms callee_runtime
    (fun t variable => match variable with end)
    (procedure_precondition _ _ procedure) after_binders Hbound) as Hbounds.
  pose proof (VSemantics.S.interp_reindex_stack_context
    (Leaf.predicates atoms) after_formals contract Hreindex
    callee_runtime runtime formals binders atoms) as Hcontext.
  etrans; [symmetry; exact Hcontext|].
  etrans; [exact Hformals|].
  exact Hbounds.
Qed.

Lemma procedure_body_post_interp {Γ F}
    (procedure : typed_procedure Γ F) (exit_store : symbolic_store Γ F [])
    (body_post : assertion Γ F [])
    (Hpost : Hoare.procedure_body_post procedure exit_store = Some body_post)
    (runtime : Model.stack_context Γ) (formals : formal_env F)
    (atoms : atom_env) :
  VSemantics.S.interp_assertion (Leaf.predicates atoms)
      runtime formals empty_binder_env atoms body_post ⊣⊢
  (Model.stack_own Γ runtime
      (interp_store formals empty_binder_env atoms exit_store) ∗
   VSemantics.S.interp_assertion (Leaf.predicates atoms)
      runtime formals
      (binder_cons
        (interp_ref formals empty_binder_env atoms
          (lookup_store exit_store _
            (procedure_return_variable _ _ procedure)))
        empty_binder_env)
      atoms (procedure_postcondition _ _ procedure))%I.
Proof.
  unfold Hoare.procedure_body_post in Hpost.
  destruct (subst_bound_assertion
    (head_bound_subst
      (ERef (lookup_store exit_store _
        (procedure_return_variable _ _ procedure))))
    (procedure_postcondition _ _ procedure)) as [postcondition |]
      eqn:Hsubst; [|discriminate].
  inversion Hpost; subst body_post. simpl.
  apply bi.sep_proper; [reflexivity|].
  eapply VSemantics.S.interp_subst_bound_assertion.
  - apply (VSemantics.S.interp_head_bound_subst
      (ERef (lookup_store exit_store _
        (procedure_return_variable _ _ procedure)))
      (interp_ref formals empty_binder_env atoms
        (lookup_store exit_store _
          (procedure_return_variable _ _ procedure)))
      formals empty_binder_env atoms).
    reflexivity.
  - exact Hsubst.
Qed.

Lemma procedure_post_instantiation_interp
    {callee_variables callee_formals}
    (procedure : typed_procedure callee_variables callee_formals)
    {Γ F Δ t} (arguments : expr_list F (t :: Δ) callee_formals)
    (result : expr F (t :: Δ) t) (contract : assertion Γ F (t :: Δ))
    (Hlookup : lookup_typed_procedure ProcedureContracts.procedures
      (procedure_identity _ _ procedure) =
      Some (pack_typed_procedure procedure))
    (Hinst : Contracts.instantiated_post_value Γ F (t :: Δ)
      callee_formals t (procedure_identity _ _ procedure)
      arguments result contract)
    (runtime : Model.stack_context Γ)
    (callee_runtime : Model.stack_context callee_variables)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (values : tval_list callee_formals) (return_value : tval t)
    (Harguments : interp_expr_list formals
      (binder_cons return_value binders) atoms arguments = Some values) :
  exists (Hreturn : procedure_return_type _ _ procedure = t),
    VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals (binder_cons return_value binders) atoms contract ⊣⊢
    VSemantics.S.interp_assertion (Leaf.predicates atoms)
        callee_runtime (formal_env_of_values values)
        (binder_cons return_value empty_binder_env) atoms
        (eq_rect _ (fun result_type =>
          assertion callee_variables callee_formals
            (return_context result_type))
          (procedure_postcondition _ _ procedure) t Hreturn).
Proof.
  apply (proj1 (ProcedureContracts.instantiated_post_value_coherent
    _ _ procedure _ _ _ _ arguments result contract Hlookup)) in Hinst.
  destruct Hinst as (Hreturn & after_formals & Hformal & Hreindex).
  exists Hreturn.
  have Hactuals := interp_expr_list_formal_subst_of_values arguments values
    formals (binder_cons return_value binders) atoms Harguments.
  pose proof (VSemantics.S.interp_subst_formals_assertion
    (Leaf.predicates atoms) (expr_list_formal_subst arguments)
    (formal_env_of_values values) formals (binder_cons return_value binders)
    atoms callee_runtime Hactuals
    (rename_bound_assertion return_bound_renaming
      (eq_rect _ (fun result_type =>
        assertion callee_variables callee_formals
          (return_context result_type))
        (procedure_postcondition _ _ procedure) t Hreturn))
    after_formals Hformal) as Hformals.
  pose proof (VSemantics.S.interp_reindex_stack_context
    (Leaf.predicates atoms) after_formals contract Hreindex
    callee_runtime runtime formals (binder_cons return_value binders) atoms)
    as Hcontext.
  etrans; [symmetry; exact Hcontext|].
  etrans; [exact Hformals|].
  apply VSemantics.S.interp_rename_bound_assertion.
  apply binder_cons_return_bound_renaming.
Qed.

(** Concrete execution boundary for a discarded procedure result.  This
    lemma isolates the legacy call-frame protocol from the typed contract
    transports: its delayed premise is precisely the body specification that
    the certified-body theorem supplies after choosing the canonical fresh
    frame. *)
Lemma procedure_discard_legacy_assembly
    {callee_variables callee_formals}
    (callee : typed_procedure callee_variables callee_formals)
    (caller_id : LegacyLang.stack_id)
    (caller_frame : LegacyLang.stack_frame)
    (arguments : list LegacyLang.expr)
    (values : list LegacyLang.val) (mask : coPset)
    (p : iProp) (q : LegacyLang.val -> iProp)
    (Hin : List.In (pack_typed_procedure callee)
      (procedure_entries ProcedureContracts.procedures))
    (Hlength : length arguments = length callee_formals)
    (Harguments : Forall2 (fun expression value =>
      LegacyLang.expr_step expression caller_frame (LegacyLang.Val value))
      arguments values)
    (Hbody : (⊢ ▷ (∀ stack_id frame,
      ⌜Forall2 (fun variable value => frame.(LegacyLang.locals) !! variable =
          Some value)
          (LegacyLang.proc_args
            (runtime_procedure_entry (pack_typed_procedure callee))).*1 values /\
        (forall variable type,
          (variable, type) ∈ LegacyLang.proc_local_vars
            (runtime_procedure_entry (pack_typed_procedure callee)) ->
          exists value, frame.(LegacyLang.locals) !! variable = Some value /\
            LegacyLang.val_has_typ value type) /\
        dom frame.(LegacyLang.locals) =
          list_to_set (LegacyLang.proc_args
            (runtime_procedure_entry (pack_typed_procedure callee))).*1 ∪
          list_to_set (LegacyLang.proc_local_vars
            (runtime_procedure_entry (pack_typed_procedure callee))).*1⌝ -∗
      {{{ LegacyGhost.stack_frame_own stack_id frame ∗ p }}}
        LegacyLang.to_rtstmt stack_id
          (LegacyLang.proc_stmt
            (runtime_procedure_entry (pack_typed_procedure callee))) @ mask
      {{{ RET LegacyLang.LitUnit; ∃ return_value frame',
          LegacyGhost.stack_frame_own stack_id frame' ∗
          ⌜frame'.(LegacyLang.locals) !! "#ret_val" = Some return_value⌝ ∗
          q return_value }}}))%I) :
  LegacyGhost.stack_frame_own caller_id caller_frame ∗
    registered_procedure_chunk (pack_typed_procedure callee) ∗ p ⊢
  Model.runtime_wp mask
    (LegacyLang.RTCallNoStore
      (Resources.procedure_name (procedure_identity _ _ callee))
      arguments caller_id)
    (fun result => ⌜result = LegacyLang.LitUnit⌝ ∗
      ∃ return_value,
        LegacyGhost.stack_frame_own caller_id caller_frame ∗
        q return_value ∗ £ 1)%I.
Proof.
  iPoseProof Hbody as "#Hbody".
  pose proof (runtime_procedure_entry_coherent
    (pack_typed_procedure callee) Hin) as Hregistration.
  destruct Hregistration as [Hname Hargs Hlocals Hargs_nodup Hlocals_nodup
    Hdisjoint Hreturn_local Hregistered_body].
  assert (Hentry_length : length arguments =
      length (LegacyLang.proc_args
        (runtime_procedure_entry (pack_typed_procedure callee)))).
  { rewrite Hargs. rewrite Model.runtime_procedure_arguments_length.
    exact Hlength. }
  rewrite /registered_procedure_chunk.
  unfold Model.runtime_wp.
  iIntros "[Hcaller [Hchunk Hp]]".
  iPoseProof (LegacyLifting.wp_call_nostore
    caller_id caller_frame arguments values
    (Resources.procedure_name (procedure_identity _ _ callee))
    (runtime_procedure_entry (pack_typed_procedure callee)) mask p q
    Hargs_nodup Hlocals_nodup Hdisjoint Hreturn_local Hentry_length Harguments
    with "Hbody") as "Hcall".
  iApply ("Hcall" with "[$Hcaller $Hchunk $Hp]").
  iNext. iIntros "Hresult".
  iSplit; first done.
  iExact "Hresult".
Qed.

(** Runtime target of the aligned-certificate refinement.  A statement with
    no physical translation is exactly a mask-changing fancy update.  A
    physical translation runs at the entry active mask and performs the same
    entry-to-exit update before exposing the logical postcondition.  This
    generalized endpoint form is what lets sequence composition cross an
    unmatched unfold/fold without pretending that one fixed WP mask is active
    throughout the source region. *)
Definition translated_runtime_wp {Γ} (runtime : Model.stack_context Γ)
    (ambient : coPset) (entry exit : GenericRegions.Atomicity.analysis_state)
    (statement : stmt Γ) (post : iProp) : iProp :=
  match Model.runtime_stmt (Model.runtime_names _ runtime)
      (Model.runtime_stack_id _ runtime) statement with
  | None =>
      (|={Model.active_runtime_mask ambient entry,
           Model.active_runtime_mask ambient exit}=> post)%I
  | Some runtime_statement =>
      Model.runtime_wp (Model.active_runtime_mask ambient entry)
        runtime_statement
        (fun result =>
          (⌜result = LegacyLang.LitUnit⌝ ∗
           |={Model.active_runtime_mask ambient entry,
              Model.active_runtime_mask ambient exit}=> post)%I)
  end.

Lemma runtime_wp_atomic_mask_change
    (physical : LegacyLang.runtime_stmt) E1 E2
    (Phi : LegacyLang.val -> iProp)
    `{!@Atomic LegacyLang.simp_lang WeaklyAtomic physical} :
  (|={E1,E2}=> Model.runtime_wp E2 physical
      (fun value => |={E2,E1}=> Phi value)) ⊢
    Model.runtime_wp E1 physical Phi.
Proof.
  unfold Model.runtime_wp. iIntros "Hwp". iApply wp_atomic.
  iExact "Hwp".
Qed.

Lemma runtime_wp_sequence
    (first second : LegacyLang.runtime_stmt) E
    (Phi : LegacyLang.val -> iProp) :
  Model.runtime_wp E first
      (fun result =>
        ⌜result = LegacyLang.LitUnit⌝ ∗ Model.runtime_wp E second Phi) ⊢
    Model.runtime_wp E (LegacyLang.RTSeq first second) Phi.
Proof.
  unfold Model.runtime_wp. iIntros "Hfirst".
  iApply LegacyLifting.wp_seq_wp. iExact "Hfirst".
Qed.

(** Lift a translated atomic leaf through an enclosing logical mask change.
    This is the operational shape produced when an erased [TUnfold]/[TFold]
    pair surrounds the leaf: enter the invariant's smaller active mask, run
    the physical step there, and restore the enclosing mask before exposing
    the postcondition. *)
Lemma translated_atomic_leaf_mask_change {Γ}
    (runtime : Model.stack_context Γ) ambient entry exit statement physical
    E (post : iProp)
    (translated : Model.runtime_stmt (Model.runtime_names _ runtime)
      (Model.runtime_stack_id _ runtime) statement = Some physical)
    `{!@Atomic LegacyLang.simp_lang WeaklyAtomic physical} :
  (|={E, Model.active_runtime_mask ambient entry}=>
      translated_runtime_wp runtime ambient entry exit statement
        (|={Model.active_runtime_mask ambient exit, E}=> post)) ⊢
    Model.runtime_wp E physical
      (fun result => ⌜result = LegacyLang.LitUnit⌝ ∗ post).
Proof.
  unfold translated_runtime_wp. rewrite translated.
  iIntros "Hleaf". iApply runtime_wp_atomic_mask_change.
  iMod "Hleaf". iModIntro.
  iApply (wp_mono with "Hleaf").
  iIntros (result) "[%Hresult Hpost]".
  iMod "Hpost". iMod "Hpost". iModIntro.
  iSplit; first done. iExact "Hpost".
Qed.

(** Certificate-indexed operational CPS interpretation.  In contrast to
    [translated_runtime_wp], sequence nodes are not collapsed to their two
    endpoint masks: the second certificate remains the continuation of the
    first.  Consequently an erased unfold keeps the matching fold (and its
    linear access frame) in scope while the physical middle executes. *)
Fixpoint aligned_runtime_region_wp
    {Γ fuel entry statement exit} {cost : GenericRegions.Atomicity.cost_model}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit) :
    Model.stack_context Γ -> coPset -> iProp -> iProp :=
  match certificate in GenericRegions.Atomicity.analysis_certificate
      _ Γ' _ entry' statement' exit'
      return Model.stack_context Γ' -> coPset -> iProp -> iProp with
  | @GenericRegions.Atomicity.CertLeaf _ Γ' _ entry' statement' exit' _ _ =>
      fun runtime ambient post =>
        translated_runtime_wp runtime ambient entry' exit' statement' post
  | @GenericRegions.Atomicity.CertUnfold _ Γ' _ entry' statement' _ exit' _ _ =>
      fun runtime ambient post =>
        Execution.Primitives.operation_wp runtime ambient
          entry' statement' exit' post
  | @GenericRegions.Atomicity.CertFold _ Γ' _ entry' statement' invariant _ =>
      fun runtime ambient post =>
        Execution.Primitives.operation_wp runtime ambient entry' statement'
          (GenericRegions.Atomicity.fold_invariant invariant entry') post
  | @GenericRegions.Atomicity.CertSequence _ _ _ _ _ _ _ _ _ _
      first_certificate second_certificate =>
      fun runtime ambient post =>
        aligned_runtime_region_wp first_certificate runtime ambient
          (aligned_runtime_region_wp second_certificate runtime ambient post)
  | @GenericRegions.Atomicity.CertConditional _ Γ' _ entry' statement'
      _ _ then_exit else_exit _ _ _ _ _ =>
      fun runtime ambient post =>
        translated_runtime_wp runtime ambient entry'
          (GenericRegions.Atomicity.AnalysisState
            (GenericRegions.Atomicity.analysis_mask then_exit ∩
              GenericRegions.Atomicity.analysis_mask else_exit)
            (GenericRegions.Atomicity.analysis_open then_exit)
            (GenericRegions.Atomicity.analysis_step_taken then_exit ||
              GenericRegions.Atomicity.analysis_step_taken else_exit)
            (GenericRegions.Atomicity.analysis_in_atomic then_exit))
          statement' post
  | @GenericRegions.Atomicity.CertAtomic _ Γ' _ entry' statement'
      _ outer inner _ _ _ _ =>
      fun runtime ambient post =>
        translated_runtime_wp runtime ambient entry'
          (GenericRegions.Atomicity.AnalysisState
            (GenericRegions.Atomicity.analysis_mask inner)
            (GenericRegions.Atomicity.analysis_open inner)
            (GenericRegions.Atomicity.analysis_step_taken outer ||
              GenericRegions.Atomicity.analysis_step_taken inner)
            (GenericRegions.Atomicity.analysis_in_atomic outer))
          statement' post
  end.

(** A heterogeneous certificate zipper.  Consecutive certificates need not
    have the same fuel index; only their analysis states must connect.  This
    is the structural suffix needed when reassociating a nested sequence
    during operational reification. *)
Inductive operational_suffix (cost : GenericRegions.Atomicity.cost_model) Γ :
    GenericRegions.Atomicity.analysis_state ->
    GenericRegions.Atomicity.analysis_state -> Type :=
| OperationalDone state : operational_suffix cost Γ state state
| OperationalCons fuel entry statement middle exit
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement middle)
    (suffix : operational_suffix cost Γ middle exit) :
    operational_suffix cost Γ entry exit.

Arguments OperationalDone {_ _} _.
Arguments OperationalCons {_ _ _ _ _ _ _} _ _.

(** The proof-relevant zipper used by the final refinement.  Each entry keeps
    the Hoare derivation aligned with its certificate, so a conditional still
    exposes its symbolic guard and a trusted atomic block still exposes its
    module witness after sequence reassociation. *)
Inductive aligned_operational_suffix
    (cost : GenericRegions.Atomicity.cost_model) Γ F Δ :
    forall (entry : GenericRegions.Atomicity.analysis_state),
      assertion Γ F Δ -> list GenericRegions.Atomicity.access_marker ->
      GenericRegions.Atomicity.analysis_state -> assertion Γ F Δ ->
      list GenericRegions.Atomicity.access_marker -> Type :=
| AlignedOperationalDone state post stack :
    aligned_operational_suffix cost Γ F Δ
      state post stack state post stack
| AlignedOperationalCons fuel entry statement middle pre middle_assertion
    stack_in stack_middle
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement middle)
    (derivation : @Certified.Rules.RavenHoareTriple Γ F Δ pre statement
      (GenericRegions.Atomicity.analysis_mask entry)
      (GenericRegions.Atomicity.analysis_mask middle) middle_assertion)
    (aligned : Certified.certificate_hoare_aligned
      cost certificate derivation)
    (lifo : GenericRegions.Atomicity.lifo_certificate
      certificate stack_in stack_middle)
    final post stack_out
    (rest : aligned_operational_suffix cost Γ F Δ middle middle_assertion
      stack_middle final post stack_out) :
    aligned_operational_suffix cost Γ F Δ
      entry pre stack_in final post stack_out.

Arguments AlignedOperationalDone {_ _ _ _} _ _ _.

Fixpoint erase_aligned_operational_suffix
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (suffix : aligned_operational_suffix cost Γ F Δ
      entry pre stack_in exit post stack_out) :
    operational_suffix cost Γ entry exit :=
  match suffix with
  | AlignedOperationalDone state _ _ => OperationalDone state
  | @AlignedOperationalCons _ _ _ _ _ _ _ _ _ _ _ _ certificate _ _ _
      _ _ _ rest =>
      OperationalCons certificate (erase_aligned_operational_suffix rest)
  end.

(** Reassociate a sequence certificate into two adjacent aligned zipper
    entries.  This is deliberately proof-relevant: the two child Hoare
    derivations, their alignment witnesses, and their individual stack
    transitions remain available to a later focused reification proof. *)
Definition expand_aligned_sequence_suffix
    {cost Γ F Δ fuel state statement first middle second next final
      pre middle_assertion next_assertion post
      stack_in stack_middle stack_next stack_out}
    (view : RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel state first middle)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel middle second next)
    (first_derivation : @Certified.Rules.RavenHoareTriple Γ F Δ pre first
      (GenericRegions.Atomicity.analysis_mask state)
      (GenericRegions.Atomicity.analysis_mask middle) middle_assertion)
    (second_derivation : @Certified.Rules.RavenHoareTriple Γ F Δ
      middle_assertion second
      (GenericRegions.Atomicity.analysis_mask middle)
      (GenericRegions.Atomicity.analysis_mask next) next_assertion)
    (first_aligned : Certified.certificate_hoare_aligned cost
      first_certificate first_derivation)
    (second_aligned : Certified.certificate_hoare_aligned cost
      second_certificate second_derivation)
    (first_lifo : GenericRegions.Atomicity.lifo_certificate
      first_certificate stack_in stack_middle)
    (second_lifo : GenericRegions.Atomicity.lifo_certificate
      second_certificate stack_middle stack_next)
    (rest : aligned_operational_suffix cost Γ F Δ next next_assertion
      stack_next final post stack_out) :
    aligned_operational_suffix cost Γ F Δ state pre stack_in
      final post stack_out :=
  @AlignedOperationalCons cost Γ F Δ fuel state first middle pre
    middle_assertion stack_in stack_middle first_certificate first_derivation
    first_aligned first_lifo final post stack_out
    (@AlignedOperationalCons cost Γ F Δ fuel middle second next
      middle_assertion next_assertion stack_middle stack_next
      second_certificate second_derivation second_aligned second_lifo
      final post stack_out rest).

Lemma erase_expand_aligned_sequence_suffix
    {cost Γ F Δ fuel state statement first middle second next final
      pre middle_assertion next_assertion post
      stack_in stack_middle stack_next stack_out}
    (view : RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel state first middle)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel middle second next)
    (first_derivation : @Certified.Rules.RavenHoareTriple Γ F Δ pre first
      (GenericRegions.Atomicity.analysis_mask state)
      (GenericRegions.Atomicity.analysis_mask middle) middle_assertion)
    (second_derivation : @Certified.Rules.RavenHoareTriple Γ F Δ
      middle_assertion second
      (GenericRegions.Atomicity.analysis_mask middle)
      (GenericRegions.Atomicity.analysis_mask next) next_assertion)
    (first_aligned : Certified.certificate_hoare_aligned cost
      first_certificate first_derivation)
    (second_aligned : Certified.certificate_hoare_aligned cost
      second_certificate second_derivation)
    (first_lifo : GenericRegions.Atomicity.lifo_certificate
      first_certificate stack_in stack_middle)
    (second_lifo : GenericRegions.Atomicity.lifo_certificate
      second_certificate stack_middle stack_next)
    (rest : aligned_operational_suffix cost Γ F Δ next next_assertion
      stack_next final post stack_out) :
  erase_aligned_operational_suffix
    (expand_aligned_sequence_suffix view first_certificate second_certificate
      first_derivation second_derivation first_aligned second_aligned
      first_lifo second_lifo rest) =
  OperationalCons first_certificate
    (OperationalCons second_certificate
      (erase_aligned_operational_suffix rest)).
Proof. reflexivity. Qed.

Lemma aligned_operational_suffix_preserves_wf
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (suffix : aligned_operational_suffix cost Γ F Δ
      entry pre stack_in exit post stack_out) :
  GenericRegions.Atomicity.state_wf entry ->
  GenericRegions.Atomicity.state_wf exit.
Proof.
  induction suffix; intros Hwf; first exact Hwf.
  apply IHsuffix.
  eapply GenericRegions.Atomicity.certificate_preserves_wf; eauto.
Qed.

Fixpoint operational_suffix_wp {cost Γ entry exit}
    (suffix : operational_suffix cost Γ entry exit)
    (runtime : Model.stack_context Γ) ambient (post : iProp) : iProp :=
  match suffix with
  | OperationalDone _ => post
  | OperationalCons certificate rest =>
      aligned_runtime_region_wp certificate runtime ambient
        (operational_suffix_wp rest runtime ambient post)
  end.

Fixpoint operational_suffix_lifo {cost Γ entry exit}
    (suffix : operational_suffix cost Γ entry exit)
    (stack_in stack_out : list GenericRegions.Atomicity.access_marker) : Prop :=
  match suffix with
  | OperationalDone _ => stack_out = stack_in
  | OperationalCons certificate rest =>
      exists stack_middle,
        GenericRegions.Atomicity.lifo_certificate certificate
          stack_in stack_middle /\
      operational_suffix_lifo rest stack_middle stack_out
  end.

Lemma erase_aligned_operational_suffix_lifo
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (suffix : aligned_operational_suffix cost Γ F Δ
      entry pre stack_in exit post stack_out) :
  operational_suffix_lifo
    (erase_aligned_operational_suffix suffix) stack_in stack_out.
Proof.
  induction suffix; simpl.
  - reflexivity.
  - eexists. split; [exact lifo|exact IHsuffix].
Qed.

Lemma aligned_operational_suffix_preserves_stack_consistency
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (suffix : aligned_operational_suffix cost Γ F Δ
      entry pre stack_in exit post stack_out) :
  GenericRegions.Atomicity.state_wf entry ->
  GenericRegions.Atomicity.access_stack_consistent
    (GenericRegions.Atomicity.analysis_open entry) stack_in ->
  GenericRegions.Atomicity.access_stack_consistent
    (GenericRegions.Atomicity.analysis_open exit) stack_out.
Proof.
  induction suffix; intros Hwf Hstack; first exact Hstack.
  apply IHsuffix.
  - eapply GenericRegions.Atomicity.certificate_preserves_wf; eauto.
  - eapply GenericRegions.Atomicity.lifo_preserves_access_stack_consistency;
      eauto.
Qed.

Lemma aligned_balanced_suffix_open_equal
    {cost Γ F Δ entry pre stack exit post}
    (suffix : aligned_operational_suffix cost Γ F Δ
      entry pre stack exit post stack) :
  GenericRegions.Atomicity.state_wf entry ->
  GenericRegions.Atomicity.access_stack_consistent
    (GenericRegions.Atomicity.analysis_open entry) stack ->
  GenericRegions.Atomicity.analysis_open exit =
    GenericRegions.Atomicity.analysis_open entry.
Proof.
  intros Hwf Hstack.
  symmetry. eapply GenericRegions.Atomicity.access_stack_consistent_functional.
  - exact Hstack.
  - eapply aligned_operational_suffix_preserves_stack_consistency; eauto.
Qed.

Lemma aligned_balanced_suffix_active_mask_equal
    {cost Γ F Δ entry pre stack exit post}
    (suffix : aligned_operational_suffix cost Γ F Δ
      entry pre stack exit post stack) ambient :
  GenericRegions.Atomicity.state_wf entry ->
  GenericRegions.Atomicity.access_stack_consistent
    (GenericRegions.Atomicity.analysis_open entry) stack ->
  Model.active_runtime_mask ambient exit =
    Model.active_runtime_mask ambient entry.
Proof.
  intros Hwf Hstack. apply Model.active_runtime_mask_same_open.
  eapply aligned_balanced_suffix_open_equal; eauto.
Qed.

Definition aligned_singleton_suffix
    {cost Γ F Δ fuel entry statement exit pre post stack_in stack_out}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    (derivation : @Certified.Rules.RavenHoareTriple Γ F Δ pre statement
      (GenericRegions.Atomicity.analysis_mask entry)
      (GenericRegions.Atomicity.analysis_mask exit) post)
    (aligned : Certified.certificate_hoare_aligned
      cost certificate derivation)
    (lifo : GenericRegions.Atomicity.lifo_certificate
      certificate stack_in stack_out) :
  aligned_operational_suffix cost Γ F Δ
    entry pre stack_in exit post stack_out :=
  @AlignedOperationalCons cost Γ F Δ fuel entry statement exit pre post
    stack_in stack_out certificate derivation aligned lifo exit post stack_out
    (AlignedOperationalDone exit post stack_out).

Definition certificate_runtime_statement
    {cost Γ fuel entry statement exit}
    (_ : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    (runtime : Model.stack_context Γ) : option LegacyLang.runtime_stmt :=
  Model.runtime_stmt (Model.runtime_names _ runtime)
    (Model.runtime_stack_id _ runtime) statement.

Definition certificate_source_size
    {cost Γ fuel entry statement exit}
    (_ : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit) : nat :=
  RegionSyntax.size statement.

Fixpoint operational_suffix_runtime {cost Γ entry exit}
    (suffix : operational_suffix cost Γ entry exit)
    (runtime : Model.stack_context Γ) : option LegacyLang.runtime_stmt :=
  match suffix with
  | OperationalDone _ => None
  | OperationalCons certificate rest =>
      Model.combine_runtime_statements
        (certificate_runtime_statement certificate runtime)
        (operational_suffix_runtime rest runtime)
  end.

Fixpoint operational_suffix_measure {cost Γ entry exit}
    (suffix : operational_suffix cost Γ entry exit) : nat :=
  match suffix with
  | OperationalDone _ => 0
  | OperationalCons certificate rest =>
      certificate_source_size certificate + operational_suffix_measure rest
  end.

Fixpoint operational_suffix_footprint {cost Γ entry exit}
    (suffix : operational_suffix cost Γ entry exit) : gset inv_id :=
  match suffix with
  | OperationalDone _ => ∅
  | OperationalCons certificate rest =>
      GenericRegions.Atomicity.certificate_footprint certificate ∪
      operational_suffix_footprint rest
  end.

Definition aligned_operational_suffix_footprint
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (suffix : aligned_operational_suffix cost Γ F Δ
      entry pre stack_in exit post stack_out) : gset inv_id :=
  operational_suffix_footprint (erase_aligned_operational_suffix suffix).

Lemma operational_suffix_head_footprint_subset
    {cost Γ fuel entry statement middle exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement middle)
    (rest : operational_suffix cost Γ middle exit) :
  GenericRegions.Atomicity.certificate_footprint certificate ⊆
    operational_suffix_footprint (OperationalCons certificate rest).
Proof. simpl. set_solver. Qed.

Lemma operational_suffix_rest_footprint_subset
    {cost Γ fuel entry statement middle exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement middle)
    (rest : operational_suffix cost Γ middle exit) :
  operational_suffix_footprint rest ⊆
    operational_suffix_footprint (OperationalCons certificate rest).
Proof. simpl. set_solver. Qed.

Definition expand_sequence_suffix {cost Γ fuel state statement first middle
    second next final}
    (view : RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel state first middle)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel middle second next)
    (rest : operational_suffix cost Γ next final) :
    operational_suffix cost Γ state final :=
  OperationalCons first_certificate
    (OperationalCons second_certificate rest).

Lemma expand_sequence_suffix_wp {cost Γ fuel state statement first middle
    second next final}
    (view : RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel state first middle)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel middle second next)
    (rest : operational_suffix cost Γ next final)
    (runtime : Model.stack_context Γ) ambient post :
  operational_suffix_wp
      (OperationalCons
        (GenericRegions.Atomicity.CertSequence cost Γ fuel state statement
          first middle second next view first_certificate second_certificate)
        rest) runtime ambient post =
    operational_suffix_wp
      (expand_sequence_suffix view first_certificate second_certificate rest)
      runtime ambient post.
Proof. reflexivity. Qed.

Lemma expand_sequence_suffix_lifo {cost Γ fuel state statement first middle
    second next final}
    (view : RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel state first middle)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel middle second next)
    (rest : operational_suffix cost Γ next final) stack_in stack_out :
  operational_suffix_lifo
      (OperationalCons
        (GenericRegions.Atomicity.CertSequence cost Γ fuel state statement
          first middle second next view first_certificate second_certificate)
        rest) stack_in stack_out <->
    operational_suffix_lifo
      (expand_sequence_suffix view first_certificate second_certificate rest)
      stack_in stack_out.
Proof. simpl. firstorder. Qed.

Lemma expand_sequence_suffix_measure_decreases {cost Γ fuel state statement
    first middle second next final}
    (view : RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel state first middle)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel middle second next)
    (rest : operational_suffix cost Γ next final) :
  operational_suffix_measure
      (expand_sequence_suffix view first_certificate second_certificate rest) <
    operational_suffix_measure
      (OperationalCons
        (GenericRegions.Atomicity.CertSequence cost Γ fuel state statement
          first middle second next view first_certificate second_certificate)
        rest).
Proof.
  unfold expand_sequence_suffix. simpl. unfold certificate_source_size.
  destruct statement; simpl in view; try discriminate.
  inversion view; subst. simpl. lia.
Qed.

Definition packed_operational_suffix
    (cost : GenericRegions.Atomicity.cost_model) Γ : Type :=
  { entry : GenericRegions.Atomicity.analysis_state &
    { exit : GenericRegions.Atomicity.analysis_state &
      operational_suffix cost Γ entry exit }}.

Definition packed_operational_suffix_measure {cost Γ}
    (packed : packed_operational_suffix cost Γ) : nat :=
  match packed with
  | existT _ (existT _ suffix) => operational_suffix_measure suffix
  end.

Lemma operational_suffix_rest_measure_decreases
    {cost Γ fuel entry statement middle exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement middle)
    (rest : operational_suffix cost Γ middle exit) :
  operational_suffix_measure rest <
    operational_suffix_measure (OperationalCons certificate rest).
Proof.
  simpl. unfold certificate_source_size.
  have Hpositive := RegionSyntax.size_positive Γ statement. lia.
Qed.

Definition runtime_option_wp (entry_mask exit_mask : coPset)
    (physical : option LegacyLang.runtime_stmt) (post : iProp) : iProp :=
  match physical with
  | None => (|={entry_mask, exit_mask}=> post)%I
  | Some statement =>
      Model.runtime_wp entry_mask statement
        (fun result =>
          (⌜result = LegacyLang.LitUnit⌝ ∗
           |={entry_mask, exit_mask}=> post)%I)
  end.

Definition runtime_option_count
    (physical : option LegacyLang.runtime_stmt) : nat :=
  match physical with Some _ => 1 | None => 0 end.

Definition analysis_step_bit
    (state : GenericRegions.Atomicity.analysis_state) : nat :=
  if GenericRegions.Atomicity.analysis_step_taken state then 1 else 0.

Fixpoint certificate_open_continuous
    {cost Γ fuel entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit) : Prop :=
  GenericRegions.Atomicity.analysis_open entry ≠ ∅ /\
  GenericRegions.Atomicity.analysis_open exit ≠ ∅ /\
  match certificate with
  | GenericRegions.Atomicity.CertSequence _ _ _ _ _ _ _ _ _ _
      first_certificate second_certificate =>
      certificate_open_continuous first_certificate /\
      certificate_open_continuous second_certificate
  | GenericRegions.Atomicity.CertConditional _ _ _ _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      certificate_open_continuous then_certificate /\
      certificate_open_continuous else_certificate
  | _ => True
  end.

Fixpoint operational_suffix_chunk_count {cost Γ entry exit}
    (suffix : operational_suffix cost Γ entry exit)
    (runtime : Model.stack_context Γ) : nat :=
  match suffix with
  | OperationalDone _ => 0
  | OperationalCons certificate rest =>
      runtime_option_count (certificate_runtime_statement certificate runtime) +
      operational_suffix_chunk_count rest runtime
  end.

Lemma combine_runtime_statements_assoc_sparse first second third :
  runtime_option_count first + runtime_option_count second +
      runtime_option_count third <= 1 ->
  Model.combine_runtime_statements
      (Model.combine_runtime_statements first second) third =
    Model.combine_runtime_statements first
      (Model.combine_runtime_statements second third).
Proof.
  destruct first, second, third; simpl; intros Hcount;
    try reflexivity; lia.
Qed.

Lemma combine_runtime_statements_count_le first second :
  runtime_option_count
      (Model.combine_runtime_statements first second) <=
    runtime_option_count first + runtime_option_count second.
Proof. destruct first, second; simpl; lia. Qed.

Definition operational_suffix_translated_wp {cost Γ entry exit}
    (suffix : operational_suffix cost Γ entry exit)
    (runtime : Model.stack_context Γ) ambient (post : iProp) : iProp :=
  runtime_option_wp
    (Model.active_runtime_mask ambient entry)
    (Model.active_runtime_mask ambient exit)
    (operational_suffix_runtime suffix runtime) post.

(** A focused invariant bracket is reified at its enclosing mask [outer],
    while its certificate suffix itself runs between the smaller active masks
    recorded at its endpoints.  The closing update is part of the suffix
    continuation, so [wp_atomic] can encompass the unique physical step. *)
Definition legacy_masked_operational_suffix_wp {cost Γ entry exit}
    (suffix : operational_suffix cost Γ entry exit)
    (runtime : Model.stack_context Γ) ambient outer (post : iProp) : iProp :=
  (|={outer, Model.active_runtime_mask ambient entry}=>
    operational_suffix_wp suffix runtime ambient
      (|={Model.active_runtime_mask ambient exit, outer}=> post))%I.

Definition legacy_focused_operational_suffix_wp {cost Γ entry exit}
    (suffix : operational_suffix cost Γ entry exit)
    (runtime : Model.stack_context Γ) outer (post : iProp) : iProp :=
  runtime_option_wp outer outer (operational_suffix_runtime suffix runtime) post.

Lemma translated_runtime_wp_as_option {Γ}
    (runtime : Model.stack_context Γ) ambient entry exit statement post :
  translated_runtime_wp runtime ambient entry exit statement post ⊣⊢
    runtime_option_wp
      (Model.active_runtime_mask ambient entry)
      (Model.active_runtime_mask ambient exit)
      (Model.runtime_stmt (Model.runtime_names _ runtime)
        (Model.runtime_stack_id _ runtime) statement) post.
Proof. reflexivity. Qed.

Lemma runtime_option_wp_mono entry_mask exit_mask physical (P Q : iProp) :
  (P ⊢ Q) ->
  runtime_option_wp entry_mask exit_mask physical P ⊢
    runtime_option_wp entry_mask exit_mask physical Q.
Proof.
  intros HPQ. destruct physical as [statement|]; simpl.
  - iIntros "Hwp". iApply (wp_mono with "Hwp").
    iIntros (result) "[%Hresult Hpost]". iSplit; first done.
    iMod "Hpost". iModIntro. iApply HPQ. iExact "Hpost".
  - iIntros "Hpost". iMod "Hpost". iModIntro.
    iApply HPQ. iExact "Hpost".
Qed.

Lemma runtime_option_wp_sequence_same_mask mask first second (post : iProp) :
  runtime_option_wp mask mask first
      (runtime_option_wp mask mask second post) ⊢
    runtime_option_wp mask mask
      (Model.combine_runtime_statements first second) post.
Proof.
  destruct first as [first|], second as [second|]; simpl.
  - iIntros "Hfirst". iApply runtime_wp_sequence.
    iApply (wp_mono with "Hfirst").
    iIntros (result) "[%Hresult Hsecond]". iSplit; first done.
    iMod "Hsecond". iExact "Hsecond".
  - iIntros "Hfirst". iApply (wp_mono with "Hfirst").
    iIntros (result) "[%Hresult Hpost]". iSplit; first done.
    iMod "Hpost". iMod "Hpost". iModIntro. iExact "Hpost".
  - iIntros "Hsecond". iMod "Hsecond". iExact "Hsecond".
  - iIntros "Hpost". iMod "Hpost". iMod "Hpost".
    iModIntro. iExact "Hpost".
Qed.

(** Sequential composition only requires the exit mask of the first fragment
    to agree with the entry mask of the second one.  The final mask may be
    different; this is the form needed when an ordinary normalized chunk is
    prepended to a suffix that eventually closes or allocates an invariant. *)
Lemma runtime_option_wp_sequence entry_mask exit_mask first second
    (post : iProp) :
  runtime_option_wp entry_mask entry_mask first
      (runtime_option_wp entry_mask exit_mask second post) ⊢
    runtime_option_wp entry_mask exit_mask
      (Model.combine_runtime_statements first second) post.
Proof.
  destruct first as [first|], second as [second|]; simpl.
  - iIntros "Hfirst". iApply runtime_wp_sequence.
    iApply (wp_mono with "Hfirst").
    iIntros (result) "[%Hresult Hsecond]". iSplit; first done.
    iMod "Hsecond". iExact "Hsecond".
  - iIntros "Hfirst". iApply (wp_mono with "Hfirst").
    iIntros (result) "[%Hresult Hpost]". iSplit; first done.
    iMod "Hpost". iMod "Hpost". iModIntro. iExact "Hpost".
  - iIntros "Hsecond". iMod "Hsecond". iExact "Hsecond".
  - iIntros "Hpost". iMod "Hpost". iMod "Hpost".
    iModIntro. iExact "Hpost".
Qed.

(** Reify a proof-only mask bracket around an optional physical fragment.
    The only semantic premise is precisely Raven's atomicity obligation for
    the physical case; an erased fragment needs no such premise. *)
Lemma runtime_option_wp_atomic_mask_change outer inner physical (post : iProp) :
  (forall statement, physical = Some statement ->
    @Atomic LegacyLang.simp_lang WeaklyAtomic statement) ->
  (|={outer,inner}=>
    runtime_option_wp inner inner physical (|={inner,outer}=> post)) ⊢
  runtime_option_wp outer outer physical post.
Proof.
  intros Hatomic. destruct physical as [statement|] eqn:Hphysical; simpl.
  - pose proof (Hatomic statement eq_refl) as Hstatement_atomic.
    iIntros "Hbracket". iApply runtime_wp_atomic_mask_change.
    iMod "Hbracket". iModIntro.
    iApply (wp_mono with "Hbracket").
    iIntros (result) "[%Hresult Hpost]".
    iMod "Hpost". iMod "Hpost". iModIntro.
    iSplit; first done. iExact "Hpost".
  - iIntros "Hbracket". iMod "Hbracket".
    iMod "Hbracket". iMod "Hbracket". iModIntro.
    iExact "Hbracket".
Qed.

Lemma translated_runtime_wp_prepend_suffix
    {cost Γ fuel entry statement middle exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement middle)
    (rest : operational_suffix cost Γ middle exit)
    (runtime : Model.stack_context Γ) ambient (post : iProp)
    (Hopen : GenericRegions.Atomicity.analysis_open entry =
      GenericRegions.Atomicity.analysis_open middle) :
  translated_runtime_wp runtime ambient entry middle statement
      (operational_suffix_translated_wp rest runtime ambient post) ⊢
    operational_suffix_translated_wp
      (OperationalCons certificate rest) runtime ambient post.
Proof.
  unfold translated_runtime_wp, operational_suffix_translated_wp.
  unfold certificate_runtime_statement. simpl.
  unfold Model.active_runtime_mask. rewrite Hopen.
  apply runtime_option_wp_sequence.
Qed.

Lemma translated_runtime_wp_sequence {Γ}
    (runtime : Model.stack_context Γ) ambient entry middle exit node
    (first second : stmt Γ) (post : iProp)
    (Hopen : GenericRegions.Atomicity.analysis_open entry =
      GenericRegions.Atomicity.analysis_open middle) :
  translated_runtime_wp runtime ambient entry middle first
      (translated_runtime_wp runtime ambient middle exit second post) ⊢
    translated_runtime_wp runtime ambient entry exit
      (TSeq node first second) post.
Proof.
  unfold translated_runtime_wp. simpl.
  unfold Model.active_runtime_mask. rewrite Hopen.
  apply runtime_option_wp_sequence.
Qed.

Lemma operational_suffix_translated_wp_atomic_mask_change
    {cost Γ entry exit} (suffix : operational_suffix cost Γ entry exit)
    (runtime : Model.stack_context Γ) ambient outer (post : iProp)
    (Hopen : GenericRegions.Atomicity.analysis_open entry =
      GenericRegions.Atomicity.analysis_open exit) :
  (forall statement,
    operational_suffix_runtime suffix runtime = Some statement ->
    @Atomic LegacyLang.simp_lang WeaklyAtomic statement) ->
  (|={outer, Model.active_runtime_mask ambient entry}=>
    operational_suffix_translated_wp suffix runtime ambient
      (|={Model.active_runtime_mask ambient exit,outer}=> post)) ⊢
  legacy_focused_operational_suffix_wp suffix runtime outer post.
Proof.
  intros Hatomic.
  unfold operational_suffix_translated_wp,
    legacy_focused_operational_suffix_wp.
  have Hactive : Model.active_runtime_mask ambient entry =
      Model.active_runtime_mask ambient exit.
  { apply Model.active_runtime_mask_same_open. exact Hopen. }
  rewrite <- Hactive.
  apply runtime_option_wp_atomic_mask_change. exact Hatomic.
Qed.

Lemma operational_done_refines {cost Γ}
    (state : GenericRegions.Atomicity.analysis_state)
    (runtime : Model.stack_context Γ) ambient post :
  operational_suffix_wp (OperationalDone (cost := cost) (Γ := Γ) state)
      runtime ambient post ⊢
    operational_suffix_translated_wp
      (OperationalDone (cost := cost) (Γ := Γ) state)
      runtime ambient post.
Proof. simpl. iIntros "Hpost". iModIntro. iExact "Hpost". Qed.

Lemma legacy_masked_operational_done_refines {cost Γ}
    (state : GenericRegions.Atomicity.analysis_state)
    (runtime : Model.stack_context Γ) ambient outer post :
  legacy_masked_operational_suffix_wp
      (OperationalDone (cost := cost) (Γ := Γ) state)
      runtime ambient outer post ⊢
    legacy_focused_operational_suffix_wp
      (OperationalDone (cost := cost) (Γ := Γ) state)
      runtime outer post.
Proof.
  unfold legacy_masked_operational_suffix_wp,
    legacy_focused_operational_suffix_wp.
  simpl. iIntros "Hpost". iMod "Hpost". iMod "Hpost".
  iModIntro. iExact "Hpost".
Qed.

Lemma operational_leaf_done_refines {cost Γ fuel entry statement exit}
    (view : RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : GenericRegions.Atomicity.take_step (cost Γ statement) entry =
      inr exit)
    (runtime : Model.stack_context Γ) ambient post :
  operational_suffix_wp
      (OperationalCons
        (GenericRegions.Atomicity.CertLeaf cost Γ fuel entry statement exit
          view step)
        (OperationalDone exit)) runtime ambient post ⊢
    operational_suffix_translated_wp
      (OperationalCons
        (GenericRegions.Atomicity.CertLeaf cost Γ fuel entry statement exit
          view step)
        (OperationalDone exit)) runtime ambient post.
Proof.
  unfold operational_suffix_translated_wp. simpl.
  unfold certificate_runtime_statement, translated_runtime_wp,
    runtime_option_wp.
  destruct (Model.runtime_stmt (Model.runtime_names Γ runtime)
    (Model.runtime_stack_id Γ runtime) statement) eqn:Hruntime;
    simpl;
    iIntros "Hwp"; iExact "Hwp".
Qed.

Lemma translated_runtime_wp_runtime_stmt_ext {Γ}
    (runtime : Model.stack_context Γ) ambient entry exit
    (left right : stmt Γ) post :
  Model.runtime_stmt (Model.runtime_names _ runtime)
    (Model.runtime_stack_id _ runtime) left =
  Model.runtime_stmt (Model.runtime_names _ runtime)
    (Model.runtime_stack_id _ runtime) right ->
  translated_runtime_wp runtime ambient entry exit left post ⊣⊢
    translated_runtime_wp runtime ambient entry exit right post.
Proof.
  intros Hequal. unfold translated_runtime_wp. now rewrite Hequal.
Qed.

Lemma translated_runtime_wp_distribute_unfold_fold_if {Γ}
    (runtime : Model.stack_context Γ) ambient entry exit
    unfold_node inner_node conditional_node fold_node
    invariant unfold_arguments fold_arguments condition
    (then_branch else_branch : stmt Γ) post :
  translated_runtime_wp runtime ambient entry exit
    (TSeq unfold_node (TUnfold unfold_node invariant unfold_arguments)
      (TSeq inner_node
        (TIf conditional_node condition then_branch else_branch)
        (TFold fold_node invariant fold_arguments))) post ⊣⊢
  translated_runtime_wp runtime ambient entry exit
    (TIf conditional_node condition
      (TSeq unfold_node (TUnfold unfold_node invariant unfold_arguments)
        (TSeq inner_node then_branch
          (TFold fold_node invariant fold_arguments)))
      (TSeq unfold_node (TUnfold unfold_node invariant unfold_arguments)
        (TSeq inner_node else_branch
          (TFold fold_node invariant fold_arguments)))) post.
Proof.
  apply translated_runtime_wp_runtime_stmt_ext.
  apply Model.runtime_stmt_distribute_unfold_fold_if.
Qed.

(** Turn an erased arm into the value statement used by [RTIfS].  This lets
    the conditional proof treat physical and proof-only arms uniformly once
    branch selection has taken place. *)
Lemma translated_runtime_wp_default_arm {Γ}
    (runtime : Model.stack_context Γ) ambient entry exit
    (statement : stmt Γ) post :
  translated_runtime_wp runtime ambient entry exit statement post ⊢
  Model.runtime_wp (Model.active_runtime_mask ambient entry)
    (default Model.runtime_noop
      (Model.runtime_stmt (Model.runtime_names _ runtime)
        (Model.runtime_stack_id _ runtime) statement))
    (fun result =>
      (⌜result = LegacyLang.LitUnit⌝ ∗
       |={Model.active_runtime_mask ambient entry,
          Model.active_runtime_mask ambient exit}=> post)%I).
Proof.
  unfold translated_runtime_wp.
  destruct (Model.runtime_stmt (Model.runtime_names Γ runtime)
    (Model.runtime_stack_id Γ runtime) statement) as [physical|] eqn:Hphysical;
    first reflexivity.
  simpl. iIntros "Hpost". unfold Model.runtime_wp, Model.runtime_noop.
  iApply wp_value.
  - done.
  - iSplit; first done. iExact "Hpost".
Qed.

Lemma runtime_condition_step {Γ F Δ}
    (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) condition b :
  interp_expr formals binders atoms
    (Hoare.symbolize_expr store condition) = Some (VBool b) ->
  LegacyLang.expr_step
    (Model.runtime_expr (Model.runtime_names _ runtime) condition)
    (LegacyLang.StackFrame
      (Model.concrete_locals (Model.runtime_names _ runtime)
        (interp_store formals binders atoms store)))
    (LegacyLang.Val (Model.tval_to_val (VBool b))).
Proof.
  intros Hcondition. eapply Model.runtime_expr_sound.
  - apply Model.runtime_stack_frame_corresponds.
  - exact Hcondition.
Qed.

Lemma runtime_wp_if_true {Γ} (runtime : Model.stack_context Γ)
    frame (condition : pexpr Γ TBool) then_runtime else_runtime mask
    (P : iProp) (Phi : LegacyLang.val -> iProp) :
  LegacyLang.expr_step
    (Model.runtime_expr (Model.runtime_names _ runtime) condition) frame
    (LegacyLang.Val (LegacyLang.LitBool true)) ->
  (LegacyGhost.stack_frame_own (Model.runtime_stack_id _ runtime) frame ∗ P ⊢
    Model.runtime_wp mask then_runtime Phi) ->
  LegacyGhost.stack_frame_own (Model.runtime_stack_id _ runtime) frame ∗ P ⊢
    Model.runtime_wp mask
      (LegacyLang.RTIfS
        (Model.runtime_expr (Model.runtime_names _ runtime) condition)
        then_runtime else_runtime (Model.runtime_stack_id _ runtime)) Phi.
Proof.
  intros Hcondition Hthen. iIntros "Hresources". unfold Model.runtime_wp.
  iApply (LegacyLifting.wp_if_t_wp _ _ _ _ frame P Phi mask Hcondition
    with "[] Hresources").
  iIntros "Hresources". iPoseProof (Hthen with "Hresources") as "Hwp".
  iExact "Hwp".
Qed.

Lemma runtime_wp_if_false {Γ} (runtime : Model.stack_context Γ)
    frame (condition : pexpr Γ TBool) then_runtime else_runtime mask
    (P : iProp) (Phi : LegacyLang.val -> iProp) :
  LegacyLang.expr_step
    (Model.runtime_expr (Model.runtime_names _ runtime) condition) frame
    (LegacyLang.Val (LegacyLang.LitBool false)) ->
  (LegacyGhost.stack_frame_own (Model.runtime_stack_id _ runtime) frame ∗ P ⊢
    Model.runtime_wp mask else_runtime Phi) ->
  LegacyGhost.stack_frame_own (Model.runtime_stack_id _ runtime) frame ∗ P ⊢
    Model.runtime_wp mask
      (LegacyLang.RTIfS
        (Model.runtime_expr (Model.runtime_names _ runtime) condition)
        then_runtime else_runtime (Model.runtime_stack_id _ runtime)) Phi.
Proof.
  intros Hcondition Helse. iIntros "Hresources". unfold Model.runtime_wp.
  iApply (LegacyLifting.wp_if_f_wp _ _ _ _ frame P Phi mask Hcondition
    with "[] Hresources").
  iIntros "Hresources". iPoseProof (Helse with "Hresources") as "Hwp".
  iExact "Hwp".
Qed.

Lemma conditional_then_active_mask_join ambient then_exit else_exit :
  Model.active_runtime_mask ambient then_exit =
    Model.active_runtime_mask ambient
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask then_exit ∩
          GenericRegions.Atomicity.analysis_mask else_exit)
        (GenericRegions.Atomicity.analysis_open then_exit)
        (GenericRegions.Atomicity.analysis_step_taken then_exit ||
          GenericRegions.Atomicity.analysis_step_taken else_exit)
        (GenericRegions.Atomicity.analysis_in_atomic then_exit)).
Proof. apply Model.active_runtime_mask_same_open. reflexivity. Qed.

Lemma conditional_else_active_mask_join ambient then_exit else_exit :
  GenericRegions.Atomicity.analysis_open then_exit =
    GenericRegions.Atomicity.analysis_open else_exit ->
  Model.active_runtime_mask ambient else_exit =
    Model.active_runtime_mask ambient
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask then_exit ∩
          GenericRegions.Atomicity.analysis_mask else_exit)
        (GenericRegions.Atomicity.analysis_open then_exit)
        (GenericRegions.Atomicity.analysis_step_taken then_exit ||
          GenericRegions.Atomicity.analysis_step_taken else_exit)
        (GenericRegions.Atomicity.analysis_in_atomic then_exit)).
Proof.
  intros Hopen. apply Model.active_runtime_mask_same_open. simpl.
  symmetry. exact Hopen.
Qed.

Lemma translated_runtime_wp_if {Γ F Δ}
    (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) ambient entry exit node condition
    (then_branch else_branch : stmt Γ) post P b :
  interp_expr formals binders atoms
    (Hoare.symbolize_expr store condition) = Some (VBool b) ->
  (Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗ P ⊢
    translated_runtime_wp runtime ambient entry exit
      (if b then then_branch else else_branch) post) ->
  Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗ P ⊢
    translated_runtime_wp runtime ambient entry exit
      (TIf node condition then_branch else_branch) post.
Proof.
  intros Hcondition Hselected. destruct b.
  - destruct (Model.runtime_stmt (Model.runtime_names Γ runtime)
      (Model.runtime_stack_id Γ runtime) then_branch) as [then_runtime|]
        eqn:Hthen;
      destruct (Model.runtime_stmt (Model.runtime_names Γ runtime)
      (Model.runtime_stack_id Γ runtime) else_branch) as [else_runtime|]
        eqn:Helse.
    + have Hif : Model.runtime_stmt (Model.runtime_names Γ runtime)
          (Model.runtime_stack_id Γ runtime)
          (TIf node condition then_branch else_branch) =
        Some (LegacyLang.RTIfS
          (Model.runtime_expr (Model.runtime_names Γ runtime) condition)
          then_runtime else_runtime (Model.runtime_stack_id Γ runtime)).
      { simpl. rewrite Hthen Helse. reflexivity. }
      unfold translated_runtime_wp. rewrite Hif.
      eapply runtime_wp_if_true.
      * exact (runtime_condition_step runtime formals binders atoms store
          condition true Hcondition).
      * iIntros "Hresources".
        iPoseProof (Hselected with "Hresources") as "Hselected".
        iPoseProof (translated_runtime_wp_default_arm runtime ambient entry exit
          then_branch post with "Hselected") as "Harm".
        iEval (rewrite Hthen) in "Harm". iExact "Harm".
    + have Hif : Model.runtime_stmt (Model.runtime_names Γ runtime)
          (Model.runtime_stack_id Γ runtime)
          (TIf node condition then_branch else_branch) =
        Some (LegacyLang.RTIfS
          (Model.runtime_expr (Model.runtime_names Γ runtime) condition)
          then_runtime Model.runtime_noop (Model.runtime_stack_id Γ runtime)).
      { simpl. rewrite Hthen Helse. reflexivity. }
      unfold translated_runtime_wp. rewrite Hif.
      eapply runtime_wp_if_true.
      * exact (runtime_condition_step runtime formals binders atoms store
          condition true Hcondition).
      * iIntros "Hresources".
        iPoseProof (Hselected with "Hresources") as "Hselected".
        iPoseProof (translated_runtime_wp_default_arm runtime ambient entry exit
          then_branch post with "Hselected") as "Harm".
        iEval (rewrite Hthen) in "Harm". iExact "Harm".
    + have Hif : Model.runtime_stmt (Model.runtime_names Γ runtime)
          (Model.runtime_stack_id Γ runtime)
          (TIf node condition then_branch else_branch) =
        Some (LegacyLang.RTIfS
          (Model.runtime_expr (Model.runtime_names Γ runtime) condition)
          Model.runtime_noop else_runtime (Model.runtime_stack_id Γ runtime)).
      { simpl. rewrite Hthen Helse. reflexivity. }
      unfold translated_runtime_wp. rewrite Hif.
      eapply runtime_wp_if_true.
      * exact (runtime_condition_step runtime formals binders atoms store
          condition true Hcondition).
      * iIntros "Hresources".
        iPoseProof (Hselected with "Hresources") as "Hselected".
        iPoseProof (translated_runtime_wp_default_arm runtime ambient entry exit
          then_branch post with "Hselected") as "Harm".
        iEval (rewrite Hthen) in "Harm". iExact "Harm".
    + have Hif : Model.runtime_stmt (Model.runtime_names Γ runtime)
          (Model.runtime_stack_id Γ runtime)
          (TIf node condition then_branch else_branch) = None.
      { simpl. rewrite Hthen Helse. reflexivity. }
      unfold translated_runtime_wp. rewrite Hif. iIntros "Hresources".
      iPoseProof (Hselected with "Hresources") as "Hselected".
      iEval (unfold translated_runtime_wp; rewrite Hthen) in "Hselected".
      iExact "Hselected".
  - destruct (Model.runtime_stmt (Model.runtime_names Γ runtime)
      (Model.runtime_stack_id Γ runtime) then_branch) as [then_runtime|]
        eqn:Hthen;
      destruct (Model.runtime_stmt (Model.runtime_names Γ runtime)
      (Model.runtime_stack_id Γ runtime) else_branch) as [else_runtime|]
        eqn:Helse.
    + have Hif : Model.runtime_stmt (Model.runtime_names Γ runtime)
          (Model.runtime_stack_id Γ runtime)
          (TIf node condition then_branch else_branch) =
        Some (LegacyLang.RTIfS
          (Model.runtime_expr (Model.runtime_names Γ runtime) condition)
          then_runtime else_runtime (Model.runtime_stack_id Γ runtime)).
      { simpl. rewrite Hthen Helse. reflexivity. }
      unfold translated_runtime_wp. rewrite Hif.
      eapply runtime_wp_if_false.
      * exact (runtime_condition_step runtime formals binders atoms store
          condition false Hcondition).
      * iIntros "Hresources".
        iPoseProof (Hselected with "Hresources") as "Hselected".
        iPoseProof (translated_runtime_wp_default_arm runtime ambient entry exit
          else_branch post with "Hselected") as "Harm".
        iEval (rewrite Helse) in "Harm". iExact "Harm".
    + have Hif : Model.runtime_stmt (Model.runtime_names Γ runtime)
          (Model.runtime_stack_id Γ runtime)
          (TIf node condition then_branch else_branch) =
        Some (LegacyLang.RTIfS
          (Model.runtime_expr (Model.runtime_names Γ runtime) condition)
          then_runtime Model.runtime_noop (Model.runtime_stack_id Γ runtime)).
      { simpl. rewrite Hthen Helse. reflexivity. }
      unfold translated_runtime_wp. rewrite Hif.
      eapply runtime_wp_if_false.
      * exact (runtime_condition_step runtime formals binders atoms store
          condition false Hcondition).
      * iIntros "Hresources".
        iPoseProof (Hselected with "Hresources") as "Hselected".
        iPoseProof (translated_runtime_wp_default_arm runtime ambient entry exit
          else_branch post with "Hselected") as "Harm".
        iEval (rewrite Helse) in "Harm". iExact "Harm".
    + have Hif : Model.runtime_stmt (Model.runtime_names Γ runtime)
          (Model.runtime_stack_id Γ runtime)
          (TIf node condition then_branch else_branch) =
        Some (LegacyLang.RTIfS
          (Model.runtime_expr (Model.runtime_names Γ runtime) condition)
          Model.runtime_noop else_runtime (Model.runtime_stack_id Γ runtime)).
      { simpl. rewrite Hthen Helse. reflexivity. }
      unfold translated_runtime_wp. rewrite Hif.
      eapply runtime_wp_if_false.
      * exact (runtime_condition_step runtime formals binders atoms store
          condition false Hcondition).
      * iIntros "Hresources".
        iPoseProof (Hselected with "Hresources") as "Hselected".
        iPoseProof (translated_runtime_wp_default_arm runtime ambient entry exit
          else_branch post with "Hselected") as "Harm".
        iEval (rewrite Helse) in "Harm". iExact "Harm".
    + have Hif : Model.runtime_stmt (Model.runtime_names Γ runtime)
          (Model.runtime_stack_id Γ runtime)
          (TIf node condition then_branch else_branch) = None.
      { simpl. rewrite Hthen Helse. reflexivity. }
      unfold translated_runtime_wp. rewrite Hif. iIntros "Hresources".
      iPoseProof (Hselected with "Hresources") as "Hselected".
      iEval (unfold translated_runtime_wp; rewrite Helse) in "Hselected".
      iExact "Hselected".
Qed.

Corollary translated_runtime_wp_if_total {Γ F Δ}
    (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) ambient entry exit node condition
    (then_branch else_branch : stmt Γ) post P :
  (interp_expr formals binders atoms
      (Hoare.symbolize_expr store condition) = Some (VBool true) ->
    Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗ P ⊢
      translated_runtime_wp runtime ambient entry exit then_branch post) ->
  (interp_expr formals binders atoms
      (Hoare.symbolize_expr store condition) = Some (VBool false) ->
    Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗ P ⊢
      translated_runtime_wp runtime ambient entry exit else_branch post) ->
  Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗ P ⊢
    translated_runtime_wp runtime ambient entry exit
      (TIf node condition then_branch else_branch) post.
Proof.
  intros Hthen Helse.
  destruct (interp_expr_total formals binders atoms
    (Hoare.symbolize_expr store condition)) as [value Hvalue].
  dependent destruction value. destruct b.
  - eapply translated_runtime_wp_if; [exact Hvalue|apply Hthen; exact Hvalue].
  - eapply translated_runtime_wp_if; [exact Hvalue|apply Helse; exact Hvalue].
Qed.

(** Branch-local refinements may end at their actual analyzer exits.  The
    conditional itself continues from the join state; equality of branch
    open sets is exactly what is required to reuse one semantic continuation
    after either selected arm. *)
Lemma translated_runtime_wp_then_join_transport {Γ}
    (runtime : Model.stack_context Γ) ambient state then_exit else_exit
    statement post :
  translated_runtime_wp runtime ambient state then_exit statement post ⊣⊢
    translated_runtime_wp runtime ambient state
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask then_exit ∩
          GenericRegions.Atomicity.analysis_mask else_exit)
        (GenericRegions.Atomicity.analysis_open then_exit)
        (GenericRegions.Atomicity.analysis_step_taken then_exit ||
          GenericRegions.Atomicity.analysis_step_taken else_exit)
        (GenericRegions.Atomicity.analysis_in_atomic then_exit))
      statement post.
Proof.
  unfold translated_runtime_wp.
  rewrite (conditional_then_active_mask_join ambient then_exit else_exit).
  reflexivity.
Qed.

Lemma translated_runtime_wp_else_join_transport {Γ}
    (runtime : Model.stack_context Γ) ambient state then_exit else_exit
    statement post :
  GenericRegions.Atomicity.analysis_open then_exit =
    GenericRegions.Atomicity.analysis_open else_exit ->
  translated_runtime_wp runtime ambient state else_exit statement post ⊣⊢
    translated_runtime_wp runtime ambient state
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask then_exit ∩
          GenericRegions.Atomicity.analysis_mask else_exit)
        (GenericRegions.Atomicity.analysis_open then_exit)
        (GenericRegions.Atomicity.analysis_step_taken then_exit ||
          GenericRegions.Atomicity.analysis_step_taken else_exit)
        (GenericRegions.Atomicity.analysis_in_atomic then_exit))
      statement post.
Proof.
  intros Hopen. unfold translated_runtime_wp.
  rewrite (conditional_else_active_mask_join ambient then_exit else_exit Hopen).
  reflexivity.
Qed.

Lemma translated_runtime_wp_if_total_join {Γ F Δ}
    (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) ambient state node condition
    (then_branch else_branch : stmt Γ) then_exit else_exit post P
    (open_equal : GenericRegions.Atomicity.analysis_open then_exit =
      GenericRegions.Atomicity.analysis_open else_exit) :
  (interp_expr formals binders atoms
      (Hoare.symbolize_expr store condition) = Some (VBool true) ->
    Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗ P ⊢
      translated_runtime_wp runtime ambient state then_exit
        then_branch post) ->
  (interp_expr formals binders atoms
      (Hoare.symbolize_expr store condition) = Some (VBool false) ->
    Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗ P ⊢
      translated_runtime_wp runtime ambient state else_exit
        else_branch post) ->
  Model.stack_own Γ runtime (interp_store formals binders atoms store) ∗ P ⊢
    translated_runtime_wp runtime ambient state
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask then_exit ∩
          GenericRegions.Atomicity.analysis_mask else_exit)
        (GenericRegions.Atomicity.analysis_open then_exit)
        (GenericRegions.Atomicity.analysis_step_taken then_exit ||
          GenericRegions.Atomicity.analysis_step_taken else_exit)
        (GenericRegions.Atomicity.analysis_in_atomic then_exit))
      (TIf node condition then_branch else_branch) post.
Proof.
  intros Hthen Helse. eapply translated_runtime_wp_if_total.
  - intros Hcondition. rewrite <- translated_runtime_wp_then_join_transport.
    now apply Hthen.
  - intros Hcondition.
    rewrite <- (translated_runtime_wp_else_join_transport
      runtime ambient state then_exit else_exit else_branch post open_equal).
    now apply Helse.
Qed.

Lemma translated_runtime_wp_mono {Γ} (runtime : Model.stack_context Γ)
    ambient entry exit statement (P Q : iProp) :
  (P ⊢ Q) ->
  translated_runtime_wp runtime ambient entry exit statement P ⊢
    translated_runtime_wp runtime ambient entry exit statement Q.
Proof.
  intros HPQ. unfold translated_runtime_wp.
  destruct (Model.runtime_stmt (Model.runtime_names Γ runtime)
    (Model.runtime_stack_id Γ runtime) statement) as [physical|].
  - unfold Model.runtime_wp. iIntros "Hwp".
    iApply (wp_mono with "Hwp").
    iIntros (result) "[%Hresult Hpost]". iSplit; first done.
    iMod "Hpost". iModIntro. iApply HPQ. iExact "Hpost".
  - iIntros "Hpost". iMod "Hpost". iModIntro.
    iApply HPQ. iExact "Hpost".
Qed.

(** Framing for the translated runtime endpoint.  Both cases reduce to
    ordinary Iris framing: [wp_frame_r] for the physical leaf, and fancy-update
    framing for the erased case. *)
Lemma translated_runtime_wp_frame {Γ} (runtime : Model.stack_context Γ)
    ambient entry exit statement (post frame : iProp) :
  translated_runtime_wp runtime ambient entry exit statement post ∗ frame ⊢
    translated_runtime_wp runtime ambient entry exit statement (post ∗ frame).
Proof.
  unfold translated_runtime_wp.
  destruct (Model.runtime_stmt (Model.runtime_names Γ runtime)
    (Model.runtime_stack_id Γ runtime) statement) as [physical|].
  - unfold Model.runtime_wp. iIntros "[Hwp Hframe]".
    iPoseProof (@wp_frame_r HasLc LegacyLang.simp_lang Resources.Σ
      Model.concrete_irisG NotStuck (Model.active_runtime_mask ambient entry) _
      (fun result =>
        (⌜result = LegacyLang.LitUnit⌝ ∗
         |={Model.active_runtime_mask ambient entry,
            Model.active_runtime_mask ambient exit}=> post)%I)
      frame with "[$Hwp $Hframe]") as "Hwp".
    iApply (wp_mono with "Hwp").
    iIntros (result) "[[%Hresult Hpost] Hframe]". iSplit; first done.
    iMod "Hpost". iModIntro. iFrame.
  - iIntros "[Hpost Hframe]". iMod "Hpost". iModIntro. iFrame.
Qed.

Lemma translated_runtime_wp_active_masks_ext {Γ}
    (runtime : Model.stack_context Γ) ambient entry1 entry2 exit1 exit2
    statement post :
  Model.active_runtime_mask ambient entry1 =
    Model.active_runtime_mask ambient entry2 ->
  Model.active_runtime_mask ambient exit1 =
    Model.active_runtime_mask ambient exit2 ->
  translated_runtime_wp runtime ambient entry1 exit1 statement post ⊣⊢
    translated_runtime_wp runtime ambient entry2 exit2 statement post.
Proof.
  intros Hentry Hexit. unfold translated_runtime_wp.
  rewrite Hentry Hexit. reflexivity.
Qed.

Lemma translated_runtime_wp_then_to_conditional_join {Γ}
    (runtime : Model.stack_context Γ) ambient state then_exit else_exit
    statement post :
  translated_runtime_wp runtime ambient state then_exit statement post ⊣⊢
    translated_runtime_wp runtime ambient state
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask then_exit ∩
          GenericRegions.Atomicity.analysis_mask else_exit)
        (GenericRegions.Atomicity.analysis_open then_exit)
        (GenericRegions.Atomicity.analysis_step_taken then_exit ||
          GenericRegions.Atomicity.analysis_step_taken else_exit)
        (GenericRegions.Atomicity.analysis_in_atomic then_exit))
      statement post.
Proof.
  apply translated_runtime_wp_active_masks_ext; first reflexivity.
  apply conditional_then_active_mask_join.
Qed.

Lemma translated_runtime_wp_else_to_conditional_join {Γ}
    (runtime : Model.stack_context Γ) ambient state then_exit else_exit
    statement post :
  GenericRegions.Atomicity.analysis_open then_exit =
    GenericRegions.Atomicity.analysis_open else_exit ->
  translated_runtime_wp runtime ambient state else_exit statement post ⊣⊢
    translated_runtime_wp runtime ambient state
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask then_exit ∩
          GenericRegions.Atomicity.analysis_mask else_exit)
        (GenericRegions.Atomicity.analysis_open then_exit)
        (GenericRegions.Atomicity.analysis_step_taken then_exit ||
          GenericRegions.Atomicity.analysis_step_taken else_exit)
        (GenericRegions.Atomicity.analysis_in_atomic then_exit))
      statement post.
Proof.
  intros Hopen. apply translated_runtime_wp_active_masks_ext; first reflexivity.
  now apply conditional_else_active_mask_join.
Qed.

(** Genuine trusted-language boundary for [TAtomic].  Raven permits a user
    module to declare the hardware substrate represented by an atomic block.
    The Hoare logic still verifies its body through [Execution.region_wp]; the
    module must justify that this certified body implements the concrete
    runtime translation as one trusted atomic operation. *)
Parameter trusted_atomic_runtime_refinement : forall
    {Γ fuel cost state node body outer inner}
    (body_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask outer)
        (GenericRegions.Atomicity.analysis_open outer)
        (GenericRegions.Atomicity.analysis_step_taken outer) true)
      body inner)
    (runtime : Model.stack_context Γ) ambient post,
  Contracts.trusted_atomic Γ body ->
  GenericRegions.Atomicity.take_step GenericRegions.Atomicity.AtomicStep state =
    inr outer ->
  GenericRegions.Atomicity.analysis_open inner =
    GenericRegions.Atomicity.analysis_open outer ->
  Execution.region_wp body_certificate runtime ambient post ⊢
    translated_runtime_wp runtime ambient state
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask inner)
        (GenericRegions.Atomicity.analysis_open inner)
        (GenericRegions.Atomicity.analysis_step_taken outer ||
          GenericRegions.Atomicity.analysis_step_taken inner)
        (GenericRegions.Atomicity.analysis_in_atomic outer))
      (TAtomic node body) post.

(** The trusted module also certifies that a physical implementation of an
    atomic block is one Iris atomic runtime operation.  The refinement above
    relates its logical body to that implementation; this witness is the
    independent operational fact needed to move the implementation across an
    open invariant mask with [wp_atomic]. *)
Parameter trusted_atomic_runtime_atomic : forall {Γ} (body : stmt Γ)
    (runtime : Model.stack_context Γ) physical,
  Contracts.trusted_atomic Γ body ->
  Model.runtime_stmt (Model.runtime_names _ runtime)
    (Model.runtime_stack_id _ runtime) body = Some physical ->
  @Atomic LegacyLang.simp_lang WeaklyAtomic physical.

Fixpoint certificate_trusted_runtime_atomicity
    {cost Γ fuel entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit) : Model.stack_context Γ -> Prop :=
  match certificate in GenericRegions.Atomicity.analysis_certificate
      _ Γ' _ _ _ _ return Model.stack_context Γ' -> Prop with
  | GenericRegions.Atomicity.CertSequence _ _ _ _ _ _ _ _ _ _
      first_certificate second_certificate =>
      fun runtime =>
        certificate_trusted_runtime_atomicity first_certificate runtime /\
        certificate_trusted_runtime_atomicity second_certificate runtime
  | GenericRegions.Atomicity.CertConditional _ _ _ _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      fun runtime =>
        certificate_trusted_runtime_atomicity then_certificate runtime /\
        certificate_trusted_runtime_atomicity else_certificate runtime
  | GenericRegions.Atomicity.CertAtomic _ _ _ _ _ body _ _ _ _ _ _ =>
      fun runtime => forall physical,
          Model.runtime_stmt (Model.runtime_names _ runtime)
            (Model.runtime_stack_id _ runtime) body = Some physical ->
          @Atomic LegacyLang.simp_lang WeaklyAtomic physical
  | _ => fun _ => True
  end.

Lemma aligned_certificate_trusted_runtime_atomicity {cost Γ F Δ fuel entry
    statement exit pre post}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    (derivation : @Certified.Rules.RavenHoareTriple Γ F Δ pre statement
      (GenericRegions.Atomicity.analysis_mask entry)
      (GenericRegions.Atomicity.analysis_mask exit) post)
    (aligned : Certified.certificate_hoare_aligned cost certificate derivation)
    (runtime : Model.stack_context Γ) :
  certificate_trusted_runtime_atomicity certificate runtime.
Proof.
  induction aligned; simpl.
  - exact I.
  - exact I.
  - exact I.
  - split; [apply IHaligned1|apply IHaligned2].
  - split; [apply IHaligned1|apply IHaligned2].
  - intros physical Hphysical.
    eapply trusted_atomic_runtime_atomic; eauto.
  - apply IHaligned.
  - apply IHaligned.
  - apply IHaligned.
  - apply IHaligned.
Qed.

Fixpoint operational_suffix_trusted_runtime_atomicity
    {cost Γ entry exit} (suffix : operational_suffix cost Γ entry exit)
    (runtime : Model.stack_context Γ) : Prop :=
  match suffix with
  | OperationalDone _ => True
  | OperationalCons certificate rest =>
      certificate_trusted_runtime_atomicity certificate runtime /\
      operational_suffix_trusted_runtime_atomicity rest runtime
  end.

Lemma aligned_suffix_trusted_runtime_atomicity
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (suffix : aligned_operational_suffix cost Γ F Δ
      entry pre stack_in exit post stack_out)
    (runtime : Model.stack_context Γ) :
  operational_suffix_trusted_runtime_atomicity
    (erase_aligned_operational_suffix suffix) runtime.
Proof.
  induction suffix; simpl; first exact I.
  split.
  - eapply aligned_certificate_trusted_runtime_atomicity; eauto.
  - exact IHsuffix.
Qed.

(** Ambient-aware validity for the primitive leaf rules.  These lemmas are
    intentionally stated against the certified-region primitive interface:
    the physical runtime mask is [active_runtime_mask ambient entry], while
    Raven's logical mask transition is supplied by the certificate. *)
Lemma ambient_skip_rule_valid {Γ F Δ} (node : node_id)
    (store : symbolic_store Γ F Δ) frame
    (entry exit : GenericRegions.Atomicity.analysis_state) :
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    VSemantics.S.interp_assertion (Leaf.predicates atoms)
      runtime formals binders atoms (AAnd (AStack store) frame) ⊢
    Execution.Primitives.operation_wp runtime ambient entry (TSkip node) exit
      (VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms (AAnd (AStack store) frame)).
Proof.
  intros runtime formals binders atoms ambient.
  unfold Execution.Primitives.operation_wp. simpl. reflexivity.
Qed.

Lemma ambient_assert_rule_valid {Γ F Δ} (node : node_id)
    (store : symbolic_store Γ F Δ) frame condition
    (entry exit : GenericRegions.Atomicity.analysis_state) :
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    VSemantics.S.interp_assertion (Leaf.predicates atoms)
      runtime formals binders atoms
      (AAnd (AStack store) (AAnd frame
        (AExpr (Hoare.symbolize_expr store condition)))) ⊢
    Execution.Primitives.operation_wp runtime ambient entry
      (TAssert node condition) exit
      (VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms
        (AAnd (AStack store) (AAnd frame
          (AExpr (Hoare.symbolize_expr store condition))))).
Proof.
  intros runtime formals binders atoms ambient.
  unfold Execution.Primitives.operation_wp. simpl. reflexivity.
Qed.

Lemma ambient_assignment_rule_valid {Γ F Δ t} (node : node_id)
    (store : symbolic_store Γ F Δ) (target : pvar Γ t)
    (expression : pexpr Γ t)
    (entry exit : GenericRegions.Atomicity.analysis_state) :
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    VSemantics.S.interp_assertion (Leaf.predicates atoms)
      runtime formals binders atoms (AStack store) ⊢
    Execution.Primitives.operation_wp runtime ambient entry
      (TAssign node target expression) exit
      (VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms
        (AExists t
          (AAnd (AStack (Hoare.update_store_with_bound store target))
            (AExpr (EBinOp (BEq t) (ERef (RefBound MHere))
              (weaken_expr (Hoare.symbolize_expr store expression))))))).
Proof.
  intros runtime formals binders atoms ambient.
  unfold Execution.Primitives.operation_wp. simpl.
  unfold Execution.Primitives.ambient_leaf_wp.
  simpl. unfold Execution.Primitives.ambient_physical_leaf_wp.
  iIntros "Hpre".
  iPoseProof (Model.runtime_assignment_wp runtime formals binders atoms store
    target expression (Model.active_runtime_mask ambient entry)
    with "Hpre") as "Hwp".
  iEval (unfold Model.runtime_wp) in "Hwp". unfold Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iDestruct "Hpost" as (value) "[%Hvalue Hstack]".
  iExists value. iFrame. iPureIntro. rewrite interp_weaken_expr.
  unfold interp_program_expr in Hvalue. rewrite Hvalue. simpl.
  unfold binder_cons. rewrite view_member_here.
  rewrite (proj2 (tval_eqb_eq t value value) eq_refl). reflexivity.
Qed.

Lemma ambient_field_write_rule_valid {Γ F Δ} (node : node_id)
    (store : symbolic_store Γ F Δ) field (base : pexpr Γ TRef)
    (expression : pexpr Γ (Logic.field_type field)) old_chunk
    (entry exit : GenericRegions.Atomicity.analysis_state) :
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    VSemantics.S.interp_assertion (Leaf.predicates atoms)
      runtime formals binders atoms
      (AAnd (AStack store)
        (AOwn field (Hoare.symbolize_expr store base) old_chunk)) ⊢
    Execution.Primitives.operation_wp runtime ambient entry
      (TFieldWrite node field base expression) exit
      (VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms
        (AAnd (AStack store)
          (AOwn field (Hoare.symbolize_expr store base)
            (Hoare.symbolize_expr store expression)))).
Proof.
  intros runtime formals binders atoms ambient.
  unfold Execution.Primitives.operation_wp. simpl.
  unfold Execution.Primitives.ambient_leaf_wp.
  simpl. unfold Execution.Primitives.ambient_physical_leaf_wp.
  iIntros "[Hstack Hown]".
  iDestruct "Hown" as (location old_value) "(%Hlocation & %Hold & Hown)".
  iPoseProof (Model.runtime_field_write_wp runtime formals binders atoms store
    field base expression location old_value
    (Model.active_runtime_mask ambient entry) Hlocation
    with "[$Hstack $Hown]") as "Hwp".
  iEval (unfold Model.runtime_wp) in "Hwp". unfold Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iDestruct "Hpost" as (new_value) "(%Hvalue & Hstack & Hown)".
  iFrame "Hstack". iExists location, new_value.
  iSplit; first done. iSplit; last iExact "Hown". iPureIntro. exact Hvalue.
Qed.

Lemma ambient_field_read_rule_valid {Γ F Δ} (node : node_id)
    (store : symbolic_store Γ F Δ) field
    (target : pvar Γ (Logic.field_type field)) (base : pexpr Γ TRef)
    chunk (entry exit : GenericRegions.Atomicity.analysis_state) :
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    VSemantics.S.interp_assertion (Leaf.predicates atoms)
      runtime formals binders atoms
      (AAnd (AStack store)
        (AOwn field (Hoare.symbolize_expr store base) chunk)) ⊢
    Execution.Primitives.operation_wp runtime ambient entry
      (TFieldRead node field target base) exit
      (VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms
        (AExists (Logic.field_type field)
          (AAnd (AStack (Hoare.update_store_with_bound store target))
            (AAnd
              (AOwn field (weaken_expr (Hoare.symbolize_expr store base))
                (weaken_expr chunk))
              (AExpr (EBinOp (BEq (Logic.field_type field))
                (ERef (RefBound MHere)) (weaken_expr chunk))))))).
Proof.
  intros runtime formals binders atoms ambient.
  unfold Execution.Primitives.operation_wp. simpl.
  unfold Execution.Primitives.ambient_leaf_wp.
  simpl. unfold Execution.Primitives.ambient_physical_leaf_wp.
  iIntros "[Hstack Hown]".
  iDestruct "Hown" as (location value) "(%Hlocation & %Hchunk & Hown)".
  iPoseProof (Model.runtime_field_read_wp runtime formals binders atoms store
    field target base location value (Model.active_runtime_mask ambient entry)
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

Lemma ambient_allocated_fields_rule_interp {Γ F Δ}
    (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) fields address :
  Model.allocated_fields_own runtime formals binders atoms store
      (VRef address) fields ⊢
  VSemantics.S.interp_assertion (Leaf.predicates atoms) runtime formals
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

Lemma ambient_allocation_rule_valid {Γ F Δ} (node : node_id)
    (store : symbolic_store Γ F Δ) (target : pvar Γ TRef)
    fields (entry exit : GenericRegions.Atomicity.analysis_state) :
  NoDup (map field_init_id fields) ->
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    VSemantics.S.interp_assertion (Leaf.predicates atoms)
      runtime formals binders atoms (AStack store) ⊢
    Execution.Primitives.operation_wp runtime ambient entry
      (TAlloc node target fields) exit
      (VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms
        (AExists TRef
          (AAnd (AStack (Hoare.update_store_with_bound store target))
            (Hoare.allocated_fields_assertion store fields)))).
Proof.
  intros Hnodup runtime formals binders atoms ambient.
  unfold Execution.Primitives.operation_wp. simpl.
  unfold Execution.Primitives.ambient_leaf_wp.
  simpl. unfold Execution.Primitives.ambient_physical_leaf_wp.
  iIntros "Hstack".
  iPoseProof (Model.runtime_allocation_wp runtime formals binders atoms store
    target fields (Model.active_runtime_mask ambient entry) Hnodup
    with "Hstack") as "Hwp".
  iEval (unfold Model.runtime_wp) in "Hwp". unfold Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iDestruct "Hpost" as (address) "[Hstack Hfields]".
  iExists (VRef address). iFrame "Hstack".
  iApply (ambient_allocated_fields_rule_interp runtime formals binders atoms store
    fields address with "Hfields").
Qed.

Lemma ambient_predicate_unfold_rule_valid {Γ F Δ} (node : node_id)
    predicate arguments (store : symbolic_store Γ F Δ) body
    (entry exit : GenericRegions.Atomicity.analysis_state) :
  Contracts.instantiated_predicate Γ F Δ (Logic.predicate_args predicate)
    predicate (Hoare.symbolize_expr_list store arguments) body ->
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    VSemantics.S.interp_assertion (Leaf.predicates atoms) runtime formals
      binders atoms
      (AAnd (AStack store)
        (APredicate predicate (Hoare.symbolize_expr_list store arguments))) ⊢
    Execution.Primitives.operation_wp runtime ambient entry
      (TPredicateUnfold node predicate arguments) exit
      (VSemantics.S.interp_assertion (Leaf.predicates atoms) runtime formals
        binders atoms (AAnd (AStack store) body)).
Proof.
  intros Hinst runtime formals binders atoms ambient.
  unfold Execution.Primitives.operation_wp. simpl.
  iIntros "[Hstack Hpredicate]". iFrame "Hstack".
  rewrite (Leaf.predicate_instantiation_valid runtime formals binders atoms
    predicate (Hoare.symbolize_expr_list store arguments) body Hinst).
  iExact "Hpredicate".
Qed.

Lemma ambient_predicate_fold_rule_valid {Γ F Δ} (node : node_id)
    predicate arguments (store : symbolic_store Γ F Δ) body
    (entry exit : GenericRegions.Atomicity.analysis_state) :
  Contracts.instantiated_predicate Γ F Δ (Logic.predicate_args predicate)
    predicate (Hoare.symbolize_expr_list store arguments) body ->
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    VSemantics.S.interp_assertion (Leaf.predicates atoms) runtime formals
      binders atoms (AAnd (AStack store) body) ⊢
    Execution.Primitives.operation_wp runtime ambient entry
      (TPredicateFold node predicate arguments) exit
      (VSemantics.S.interp_assertion (Leaf.predicates atoms) runtime formals
        binders atoms
        (AAnd (AStack store)
          (APredicate predicate (Hoare.symbolize_expr_list store arguments)))).
Proof.
  intros Hinst runtime formals binders atoms ambient.
  unfold Execution.Primitives.operation_wp. simpl.
  iIntros "[Hstack Hbody]". iFrame "Hstack".
  fold (VSemantics.S.interp_assertion (Leaf.predicates atoms) runtime formals
    binders atoms
    (APredicate predicate (Hoare.symbolize_expr_list store arguments))).
  rewrite -(Leaf.predicate_instantiation_valid runtime formals binders atoms
    predicate (Hoare.symbolize_expr_list store arguments) body Hinst).
  iExact "Hbody".
Qed.

(** Until the Hoare calculus carries an explicit open-instance snapshot, the
    first soundness theorem deliberately covers argument-free invariants.
    Unlike the former [invariant_values_unique] axiom, this exposes the actual
    syntactic restriction and makes uniqueness a proved consequence. *)
Parameter invariant_argument_free : forall invariant,
  Logic.invariant_args invariant = [].

Lemma invariant_values_unique invariant
    (left right : tval_list (Logic.invariant_args invariant)) : left = right.
Proof.
  have Hargs := invariant_argument_free invariant.
  revert left right. rewrite Hargs. intros left right.
  dependent destruction left. dependent destruction right. reflexivity.
Qed.

(** Definition instantiation is the non-control semantic premise: it connects
    the caller-context body selected by the Hoare rule to the canonical body
    stored in [World.world]. *)
Parameter invariant_definition_compatible : forall {Γ F Δ}
    (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) invariant
    (expressions : Translation.Assertions.expr_list F Δ
      (Logic.invariant_args invariant)) body,
  Contracts.instantiated_invariant Γ F Δ
    (Logic.invariant_args invariant) invariant expressions body ->
  exists values : tval_list (Logic.invariant_args invariant),
    interp_expr_list formals binders atoms expressions = Some values /\
    VSemantics.S.interp_assertion (Leaf.predicates atoms)
      runtime formals binders atoms body ≡
    World.body_interp atoms invariant values.

(** Ghost updates are the sole leaves whose meaning is genuinely selected by
    the user's resource-algebra configuration.  Procedures are kept behind a
    separate interface below so that Phase 7 can derive calls and spawns from
    one verified, mutually recursive procedure environment. *)
Inductive externally_specified_ghost_leaf : forall {Γ}, stmt Γ -> Prop :=
| ExternalGhostUpdate Γ node field base old_value new_value :
    externally_specified_ghost_leaf
      (TGhostUpdate (Γ := Γ) node field base old_value new_value).

Inductive procedure_leaf : forall {Γ}, stmt Γ -> Prop :=
| ProcedureCall Γ args return_type node procedure
    (arguments : pexpr_list Γ args) (target : call_target Γ return_type) :
    procedure_leaf (TCall (Γ := Γ) node procedure arguments target)
| ProcedureSpawn Γ args node procedure (arguments : pexpr_list Γ args) :
    procedure_leaf (TSpawn (Γ := Γ) node procedure arguments).

(** Exactly the three base procedure rules.  Assertion-only structural rules
    are discharged by [ordinary_leaf_rule_valid], so the recursive procedure
    environment never needs to invert an arbitrary Hoare derivation. *)
Inductive procedure_leaf_obligation {Γ F Δ} :
    Hoare.mask -> Hoare.mask -> assertion Γ F Δ -> stmt Γ ->
    assertion Γ F Δ -> Prop :=
| ProcedureDiscardObligation args t node procedure arguments store contract_pre
    (contract_post : assertion Γ F (t :: Δ)) current_mask :
    Contracts.instantiated_pre Γ F Δ args procedure
      (Hoare.symbolize_expr_list store arguments) contract_pre ->
    Contracts.instantiated_post_value Γ F (t :: Δ) args t procedure
      (weaken_expr_list (Hoare.symbolize_expr_list store arguments))
      (ERef (RefBound MHere)) contract_post ->
    Contracts.required_mask procedure ⊆ current_mask ->
    procedure_leaf_obligation current_mask
      (current_mask ∪ Contracts.granted_mask procedure)
      (AAnd (AStack store) contract_pre)
      (TCall node procedure arguments (@CTDiscard Γ t))
      (AExists t (AAnd (AStack (weaken_store store)) contract_post))
| ProcedureStoreObligation args t node procedure arguments store target
    contract_pre (contract_post : assertion Γ F (t :: Δ)) current_mask :
    Contracts.instantiated_pre Γ F Δ args procedure
      (Hoare.symbolize_expr_list store arguments) contract_pre ->
    Contracts.instantiated_post_value Γ F (t :: Δ) args t procedure
      (weaken_expr_list (Hoare.symbolize_expr_list store arguments))
      (ERef (RefBound MHere)) contract_post ->
    Contracts.required_mask procedure ⊆ current_mask ->
    procedure_leaf_obligation current_mask
      (current_mask ∪ Contracts.granted_mask procedure)
      (AAnd (AStack store) contract_pre)
      (TCall node procedure arguments (CTStore target))
      (AExists t
        (AAnd (AStack (Hoare.update_store_with_bound store target))
          contract_post))
| ProcedureSpawnObligation args node procedure arguments store contract_pre
    current_mask :
    Contracts.instantiated_pre Γ F Δ args procedure
      (Hoare.symbolize_expr_list store arguments) contract_pre ->
    Contracts.required_mask procedure ⊆ current_mask ->
    procedure_leaf_obligation current_mask current_mask
      (AAnd (AStack store) contract_pre)
      (TSpawn node procedure arguments) (AStack store).

Parameter externally_specified_ghost_leaf_valid : forall {Γ F Δ}
    (pre post : assertion Γ F Δ) statement entry exit,
  externally_specified_ghost_leaf statement ->
  (exists mask_pre mask_post,
    Certified.Rules.RavenHoareTriple pre statement mask_pre mask_post post) ->
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    VSemantics.S.interp_assertion (Leaf.predicates atoms)
      runtime formals binders atoms pre ⊢
    Execution.Primitives.operation_wp runtime ambient entry statement exit
      (VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms post).

(** The recursively available procedure environment is an Iris resource, not
    a collection of unrelated Coq hypotheses at individual call sites.  Its
    persistence is what permits recursive and mutually recursive bodies to
    use the same environment under Löb induction. *)
Definition verified_procedure_specs : iProp :=
  (□ ∀ (Γ F Δ : context) (pre post : assertion Γ F Δ)
      (statement : stmt Γ) (mask_pre mask_post : Hoare.mask) entry exit
      (runtime : Model.stack_context Γ) (formals : formal_env F)
      (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    ⌜procedure_leaf_obligation mask_pre mask_post pre statement post⌝ -∗
    ⌜Model.runtime_mask mask_post ⊆
      Model.active_runtime_mask ambient entry⌝ -∗
    World.world_context atoms -∗
    VSemantics.S.interp_assertion (Leaf.predicates atoms)
      runtime formals binders atoms pre -∗
    Execution.Primitives.operation_wp runtime ambient entry statement exit
      (VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms post))%I.

(** Close any concrete guarded body proof by Löb induction.  The guarded
    premise is supplied downstream, where the closed certificate
    normalization theorem is available; keeping it explicit here avoids a
    cyclic dependency and, crucially, avoids postulating procedure
    soundness. *)
Lemma verified_procedure_specs_valid
    (Hguarded : all_registered_procedure_chunks ∗
      ▷ verified_procedure_specs ⊢ verified_procedure_specs) :
  all_registered_procedure_chunks ⊢ verified_procedure_specs.
Proof.
  iIntros "#Hprocedures".
  iLöb as "IH".
  iApply Hguarded.
  iFrame "Hprocedures". iNext. iExact "IH".
Qed.

(** Relative certified validity carries the recursive specification resource
    explicitly.  During body assembly this resource is supplied by the Löb
    hypothesis; initialized adequacy supplies the closed instance above. *)
Definition global_world_context (atoms : atom_env) : iProp :=
  (World.world_context atoms ∗
    (all_registered_procedure_chunks ∗ verified_procedure_specs))%I.

Global Instance global_world_context_persistent atoms :
  Persistent (global_world_context atoms).
Proof. unfold global_world_context, all_registered_procedure_chunks. apply _. Qed.

Lemma global_world_procedure_specs atoms :
  global_world_context atoms ⊢
    World.world_context atoms ∗ verified_procedure_specs.
Proof.
  rewrite /global_world_context.
  iIntros "[$ [_ $]]".
Qed.

Lemma ordinary_leaf_rule_valid : forall {Γ F Δ}
    (pre post : assertion Γ F Δ) statement entry exit,
  RegionSyntax.view statement = TypedAnalysisView.ViewLeaf ->
  Certified.Rules.RavenHoareTriple pre statement
    (GenericRegions.Atomicity.analysis_mask entry)
    (GenericRegions.Atomicity.analysis_mask exit) post ->
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    Model.runtime_mask (GenericRegions.Atomicity.analysis_mask exit) ⊆
      Model.active_runtime_mask ambient entry ->
    (global_world_context atoms ∗
     VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre) ⊢
    Execution.Primitives.operation_wp runtime ambient entry statement exit
      (VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms post).
Proof.
  intros Γ F Δ pre post statement entry exit Hview Htriple.
  induction Htriple; intros runtime formals binders atoms ambient Henvelope;
    simpl in Hview; try discriminate.
  - iIntros "[_ Hpre]". iApply ambient_skip_rule_valid. iExact "Hpre".
  - iIntros "[_ Hpre]". iApply ambient_assert_rule_valid. iExact "Hpre".
  - iIntros "[_ Hpre]". iApply ambient_assignment_rule_valid. iExact "Hpre".
  - iIntros "[_ Hpre]". iApply ambient_field_read_rule_valid. iExact "Hpre".
  - iIntros "[_ Hpre]". iApply ambient_field_write_rule_valid. iExact "Hpre".
  - iIntros "[_ Hpre]". iApply ambient_allocation_rule_valid; [exact H|].
    iExact "Hpre".
  - iIntros "[_ Hpre]".
    iApply (externally_specified_ghost_leaf_valid with "Hpre");
      [eapply ExternalGhostUpdate|eexists _, _; econstructor; exact H].
  - iIntros "[#Hglobal [Hpre Hframe]]".
    iApply (Execution.Primitives.Interface.operation_frame with "[Hpre Hframe]").
    iFrame "Hframe". iApply IHHtriple; [exact Hview|exact Henvelope|].
    iFrame "Hglobal Hpre".
  - iIntros "[#Hglobal Hpre]".
    iPoseProof (VSemantics.assertion_entails_valid (Leaf.predicates atoms)
      pre' pre H runtime formals binders atoms with "Hpre") as "Hpre".
    iPoseProof (IHHtriple Hview runtime formals binders atoms ambient Henvelope
      with "[$Hglobal $Hpre]") as "Hwp".
    iApply (Execution.Primitives.Interface.operation_mono with "Hwp").
    apply (VSemantics.assertion_entails_valid (Leaf.predicates atoms)
      post post' H0 runtime formals binders atoms).
  - iIntros "[#Hglobal Hpre]". iDestruct "Hpre" as (value) "Hbody".
    iPoseProof (IHHtriple Hview runtime formals (binder_cons value binders)
      atoms ambient Henvelope with "[$Hglobal $Hbody]") as "Hwp".
    iApply (Execution.Primitives.Interface.operation_mono with "Hwp").
    rewrite VSemantics.S.interp_weaken_assertion. done.
  - iIntros "[#Hglobal Hpre]". iDestruct "Hpre" as (value) "Hbody".
    iPoseProof (IHHtriple Hview runtime formals (binder_cons value binders)
      atoms ambient Henvelope with "[$Hglobal $Hbody]") as "Hwp".
    iApply (Execution.Primitives.Interface.operation_mono with "Hwp").
    iIntros "Hpost". iExists value. iExact "Hpost".
  - iIntros "[#Hglobal Hpre]".
    iPoseProof (global_world_procedure_specs with "Hglobal")
      as "[#Hworld #Hprocedures]".
    iApply ("Hprocedures" with "[] [] Hworld Hpre").
    iPureIntro.
    eapply ProcedureDiscardObligation; eassumption.
    iPureIntro. exact Henvelope.
  - iIntros "[#Hglobal Hpre]".
    iPoseProof (global_world_procedure_specs with "Hglobal")
      as "[#Hworld #Hprocedures]".
    iApply ("Hprocedures" with "[] [] Hworld Hpre").
    iPureIntro. eapply ProcedureStoreObligation; eassumption.
    iPureIntro. exact Henvelope.
  - iIntros "[_ Hpre]". iApply ambient_predicate_unfold_rule_valid; [exact H|].
    iExact "Hpre".
  - iIntros "[_ Hpre]". iApply ambient_predicate_fold_rule_valid; [exact H|].
    iExact "Hpre".
  - iIntros "[#Hglobal Hpre]".
    iPoseProof (global_world_procedure_specs with "Hglobal")
      as "[#Hworld #Hprocedures]".
    iApply ("Hprocedures" with "[] [] Hworld Hpre").
    iPureIntro. eapply ProcedureSpawnObligation; eassumption.
    iPureIntro. exact Henvelope.
  Unshelve. all: eauto.
Qed.

(** A successful flat leaf step preserves the active runtime mask.  This is
    the physical half of the leaf refinement: assertion-only leaves,
    including [TSkip], now translate to [None] and are deliberately excluded
    by [translated]. *)
Lemma leaf_operation_runtime_refinement {Γ cost entry statement exit}
    (view : RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : GenericRegions.Atomicity.take_step (cost Γ statement) entry =
      inr exit)
    (runtime : Model.stack_context Γ) (ambient : coPset) (post : iProp)
    (runtime_statement : LegacyLang.runtime_stmt)
    (translated : Model.runtime_stmt (Model.runtime_names _ runtime)
      (Model.runtime_stack_id _ runtime) statement = Some runtime_statement) :
  Execution.Primitives.operation_wp runtime ambient entry statement exit post ⊢
    translated_runtime_wp runtime ambient entry exit statement post.
Proof.
  apply GenericRegions.Atomicity.take_step_preserves_sets in step as [_ Hopen].
  have Hactive : Model.active_runtime_mask ambient entry =
      Model.active_runtime_mask ambient exit :=
    Model.active_runtime_mask_same_open ambient entry exit (eq_sym Hopen).
  unfold translated_runtime_wp. rewrite translated. rewrite <- Hactive.
  destruct statement; simpl in view, translated; try discriminate.
  all: try (inversion translated; subst runtime_statement).
  5: (destruct target; simpl in translated;
      inversion translated; subst runtime_statement).
  all: unfold Execution.Primitives.operation_wp; simpl.
  all: unfold Execution.Primitives.ambient_physical_leaf_wp, Model.runtime_wp.
  all: iIntros "Hwp"; iApply (wp_mono with "Hwp");
    iIntros (result) "[Hunit Hpost]"; iSplit; first done;
    iModIntro; iExact "Hpost".
Qed.

Lemma leaf_operation_runtime_refinement_total {Γ cost entry statement exit}
    (view : RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : GenericRegions.Atomicity.take_step (cost Γ statement) entry =
      inr exit)
    (runtime : Model.stack_context Γ) (ambient : coPset) (post : iProp) :
  Execution.Primitives.operation_wp runtime ambient entry statement exit post ⊢
    translated_runtime_wp runtime ambient entry exit statement post.
Proof.
  destruct (Model.runtime_stmt (Model.runtime_names _ runtime)
    (Model.runtime_stack_id _ runtime) statement) as [physical|] eqn:Hruntime.
  - eapply leaf_operation_runtime_refinement; eauto.
  - apply GenericRegions.Atomicity.take_step_preserves_sets in step as [_ Hopen].
    have Hactive : Model.active_runtime_mask ambient entry =
        Model.active_runtime_mask ambient exit :=
      Model.active_runtime_mask_same_open ambient entry exit (eq_sym Hopen).
    unfold translated_runtime_wp. rewrite Hruntime. rewrite <- Hactive.
    destruct statement; simpl in view, Hruntime; try discriminate.
    all: try destruct target; simpl in Hruntime; try discriminate.
    all: unfold Execution.Primitives.operation_wp; simpl.
    all: try (iIntros "Hpost"; iModIntro; iExact "Hpost").
    all: iIntros "Hpost"; iMod "Hpost"; iModIntro; iExact "Hpost".
Qed.

Lemma open_leaf_runtime_atomic {Γ cost entry statement exit}
    (view : RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : GenericRegions.Atomicity.take_step (cost Γ statement) entry =
      inr exit)
    (runtime : Model.stack_context Γ) physical :
  Model.runtime_cost_model_sound cost ->
  GenericRegions.Atomicity.analysis_open entry ≠ ∅ ->
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  Model.runtime_stmt (Model.runtime_names _ runtime)
    (Model.runtime_stack_id _ runtime) statement = Some physical ->
  @Atomic LegacyLang.simp_lang WeaklyAtomic physical.
Proof.
  intros Hcost Hopen Hin_atomic Hruntime.
  specialize (Hcost Γ (Model.runtime_names _ runtime)
    (Model.runtime_stack_id _ runtime) statement physical view Hruntime).
  destruct (cost Γ statement) eqn:Hstep_cost; simpl in Hcost.
  - contradiction.
  - exact Hcost.
  - unfold GenericRegions.Atomicity.take_step in step.
    rewrite Hin_atomic in step. simpl in step.
    rewrite bool_decide_false in step; [discriminate|exact Hopen].
Qed.

Lemma open_physical_leaf_takes_unique_step {Γ cost entry statement exit}
    (view : RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : GenericRegions.Atomicity.take_step (cost Γ statement) entry =
      inr exit)
    (runtime : Model.stack_context Γ) physical :
  Model.runtime_cost_model_sound cost ->
  GenericRegions.Atomicity.analysis_open entry ≠ ∅ ->
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  Model.runtime_stmt (Model.runtime_names _ runtime)
    (Model.runtime_stack_id _ runtime) statement = Some physical ->
  GenericRegions.Atomicity.analysis_step_taken entry = false /\
  GenericRegions.Atomicity.analysis_step_taken exit = true.
Proof.
  intros Hcost Hopen Hin_atomic Hruntime.
  specialize (Hcost Γ (Model.runtime_names _ runtime)
    (Model.runtime_stack_id _ runtime) statement physical view Hruntime).
  destruct (cost Γ statement) eqn:Hstep_cost; simpl in Hcost.
  - contradiction.
  - unfold GenericRegions.Atomicity.take_step in step.
    rewrite Hin_atomic in step. simpl in step.
    rewrite bool_decide_false in step; last exact Hopen.
    destruct (GenericRegions.Atomicity.analysis_step_taken entry) eqn:Htaken;
      first discriminate.
    inversion step; subst exit. simpl. auto.
  - unfold GenericRegions.Atomicity.take_step in step.
    rewrite Hin_atomic in step. simpl in step.
    rewrite bool_decide_false in step; [discriminate|exact Hopen].
Qed.

Lemma open_after_step_leaf_is_erased {Γ cost entry statement exit}
    (view : RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : GenericRegions.Atomicity.take_step (cost Γ statement) entry =
      inr exit)
    (runtime : Model.stack_context Γ) :
  Model.runtime_cost_model_sound cost ->
  GenericRegions.Atomicity.analysis_open entry ≠ ∅ ->
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  GenericRegions.Atomicity.analysis_step_taken entry = true ->
  Model.runtime_stmt (Model.runtime_names _ runtime)
    (Model.runtime_stack_id _ runtime) statement = None.
Proof.
  intros Hcost Hopen Hin_atomic Htaken.
  destruct (Model.runtime_stmt (Model.runtime_names _ runtime)
    (Model.runtime_stack_id _ runtime) statement) as [physical|] eqn:Hruntime;
    last reflexivity.
  exfalso. destruct (open_physical_leaf_takes_unique_step view step runtime
    physical Hcost Hopen Hin_atomic Hruntime) as [Hnot_taken _].
  rewrite Htaken in Hnot_taken. discriminate.
Qed.

Lemma open_leaf_runtime_step_budget {Γ cost fuel entry statement exit}
    (view : RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : GenericRegions.Atomicity.take_step (cost Γ statement) entry =
      inr exit)
    (runtime : Model.stack_context Γ) :
  Model.runtime_cost_model_sound cost ->
  certificate_open_continuous
    (GenericRegions.Atomicity.CertLeaf cost Γ fuel entry statement exit
      view step) ->
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  analysis_step_bit entry +
      runtime_option_count
        (certificate_runtime_statement
          (GenericRegions.Atomicity.CertLeaf cost Γ fuel entry statement exit
            view step) runtime) <=
    analysis_step_bit exit.
Proof.
  intros Hcost Hcontinuous Hin_atomic.
  destruct Hcontinuous as [Hopen [_ _]].
  unfold certificate_runtime_statement.
  destruct (Model.runtime_stmt (Model.runtime_names Γ runtime)
    (Model.runtime_stack_id Γ runtime) statement) as [physical|] eqn:Hruntime.
  - destruct (open_physical_leaf_takes_unique_step view step runtime physical
      Hcost Hopen Hin_atomic Hruntime) as [Hentry Hexit].
    unfold analysis_step_bit, runtime_option_count.
    rewrite Hentry Hexit. lia.
  - unfold runtime_option_count, analysis_step_bit.
    unfold GenericRegions.Atomicity.take_step in step.
    rewrite Hin_atomic in step. simpl in step.
    rewrite bool_decide_false in step; last exact Hopen.
    destruct (cost Γ statement).
    + inversion step; subst exit.
      destruct (GenericRegions.Atomicity.analysis_step_taken entry); simpl; lia.
    + destruct (GenericRegions.Atomicity.analysis_step_taken entry) eqn:Hentry;
        first discriminate.
      inversion step; subst exit. simpl. lia.
    + discriminate.
Qed.

(** A syntactic sequence contributes at most the sum of the runtime chunks of
    its two components.  The inequality, rather than an equality, is the
    useful formulation here: a whole conditional or trusted atomic block is
    deliberately represented by one runtime chunk. *)
Lemma runtime_option_count_combine first second :
  runtime_option_count (Model.combine_runtime_statements first second) <=
    runtime_option_count first + runtime_option_count second.
Proof.
  destruct first, second; simpl; lia.
Qed.

(** A certificate entered outside a trusted atomic block also exits outside
    one.  Its [CertAtomic] body is intentionally not exposed: the constructor
    restores the outer flag after checking that trusted body. *)
Lemma certificate_preserves_nonatomic {Γ cost fuel entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit) :
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  GenericRegions.Atomicity.analysis_in_atomic exit = false.
Proof.
  intro Hin_atomic. induction certificate; simpl in *.
  - unfold GenericRegions.Atomicity.take_step in e0.
    rewrite Hin_atomic in e0. simpl in e0.
    destruct (bool_decide (GenericRegions.Atomicity.analysis_open state = ∅));
      [inversion e0; subst exit; exact Hin_atomic|].
    destruct (cost Γ statement);
      try (inversion e0; subst exit; exact Hin_atomic).
    destruct (GenericRegions.Atomicity.analysis_step_taken state);
      try discriminate.
    inversion e0; reflexivity.
  - unfold GenericRegions.Atomicity.open_invariant in e0.
    destruct (bool_decide (invariant ∈
      GenericRegions.Atomicity.analysis_open state)); try discriminate.
    destruct (bool_decide (invariant ∈
      GenericRegions.Atomicity.analysis_mask state)); try discriminate.
    inversion e0; subst exit; exact Hin_atomic.
  - unfold GenericRegions.Atomicity.fold_invariant.
    destruct (bool_decide (invariant ∈
      GenericRegions.Atomicity.analysis_open state)); exact Hin_atomic.
  - apply IHcertificate2. apply IHcertificate1. exact Hin_atomic.
  - apply IHcertificate1. exact Hin_atomic.
  - unfold GenericRegions.Atomicity.take_step in e0.
    rewrite Hin_atomic in e0. simpl in e0.
    destruct (bool_decide (GenericRegions.Atomicity.analysis_open state = ∅));
      [inversion e0; subst outer; exact Hin_atomic|].
    destruct (GenericRegions.Atomicity.analysis_step_taken state) eqn:Htaken.
    + discriminate e0.
    + inversion e0; reflexivity.
Qed.

(** While the same nonempty invariant-access segment remains open, the
    concrete translation contains at most the one step tracked by the
    analysis state.  Conditional branches are considered separately: their
    join stores the disjunction of their step bits, while the runtime emits
    only the branch selected at execution time. *)
Lemma certificate_runtime_step_budget {Γ cost fuel entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    (runtime : Model.stack_context Γ) :
  Model.runtime_cost_model_sound cost ->
  certificate_open_continuous certificate ->
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  analysis_step_bit entry +
      runtime_option_count (certificate_runtime_statement certificate runtime) <=
    analysis_step_bit exit.
Proof.
  intros Hcost Hcontinuous Hin_atomic.
  induction certificate as
      [Γ fuel state statement exit view step
      | Γ fuel state statement invariant exit view step
      | Γ fuel state statement invariant view
      | Γ fuel state statement first middle second exit view first_certificate
        IHfirst second_certificate IHsecond
      | Γ fuel state statement then_branch else_branch then_exit else_exit
        view then_certificate IHthen else_certificate IHelse
        open_equal atomic_equal
      | Γ fuel state statement body outer inner view step body_certificate
        IHbody open_equal]; simpl in Hcontinuous |- *.
  - eapply open_leaf_runtime_step_budget; eauto.
  - destruct Hcontinuous as [_ [_ _]].
    destruct statement; simpl in view; try discriminate.
    inversion view; subst.
    unfold certificate_runtime_statement. simpl.
    unfold GenericRegions.Atomicity.open_invariant in step.
    destruct (bool_decide (invariant ∈
      GenericRegions.Atomicity.analysis_open state)); try discriminate.
    destruct (bool_decide (invariant ∈
      GenericRegions.Atomicity.analysis_mask state)); try discriminate.
    inversion step; subst exit. simpl.
    unfold analysis_step_bit, runtime_option_count.
    destruct (GenericRegions.Atomicity.analysis_step_taken state); simpl; lia.
  - destruct Hcontinuous as [_ [Hexit _]].
    destruct statement; simpl in view; try discriminate.
    inversion view; subst.
    unfold certificate_runtime_statement. simpl.
    unfold GenericRegions.Atomicity.fold_invariant in Hexit |- *.
    destruct (bool_decide (invariant ∈
      GenericRegions.Atomicity.analysis_open state)) eqn:Hmember.
    + simpl in Hexit |- *.
      rewrite bool_decide_false; last exact Hexit.
      unfold analysis_step_bit, runtime_option_count.
      destruct (GenericRegions.Atomicity.analysis_step_taken state); simpl; lia.
    + simpl.
      unfold analysis_step_bit, runtime_option_count.
      destruct (GenericRegions.Atomicity.analysis_step_taken state); simpl; lia.
  - destruct Hcontinuous as [_ [_ [Hfirst Hsecond]]].
    destruct statement; simpl in view; try discriminate.
    inversion view; subst.
    have Hmiddle_atomic :
        GenericRegions.Atomicity.analysis_in_atomic middle = false.
    { eapply certificate_preserves_nonatomic; eauto. }
    specialize (IHfirst runtime Hfirst Hin_atomic).
    specialize (IHsecond runtime Hsecond Hmiddle_atomic).
    unfold certificate_runtime_statement in *. simpl in *.
    pose proof (runtime_option_count_combine
      (Model.runtime_stmt (Model.runtime_names Γ runtime)
        (Model.runtime_stack_id Γ runtime) first)
      (Model.runtime_stmt (Model.runtime_names Γ runtime)
        (Model.runtime_stack_id Γ runtime) second)) as Hcombine.
    lia.
  - destruct Hcontinuous as [_ [_ [Hthen Helse]]].
    destruct statement; simpl in view; try discriminate.
    inversion view; subst.
    specialize (IHthen runtime Hthen Hin_atomic).
    specialize (IHelse runtime Helse Hin_atomic).
    unfold certificate_runtime_statement in IHthen, IHelse |- *.
    remember (Model.runtime_stmt (Model.runtime_names Γ runtime)
      (Model.runtime_stack_id Γ runtime)
      (TIf node condition then_branch else_branch)) as conditional_option
      eqn:Hconditional.
    destruct conditional_option as [conditional_runtime|].
    + have Hbranch :
        (exists then_runtime,
          Model.runtime_stmt (Model.runtime_names Γ runtime)
            (Model.runtime_stack_id Γ runtime) then_branch =
            Some then_runtime) \/
        (exists else_runtime,
          Model.runtime_stmt (Model.runtime_names Γ runtime)
            (Model.runtime_stack_id Γ runtime) else_branch =
            Some else_runtime).
      { symmetry in Hconditional. simpl in Hconditional.
        destruct (Model.runtime_stmt (Model.runtime_names Γ runtime)
          (Model.runtime_stack_id Γ runtime) then_branch) as [then_runtime|]
          eqn:Hthen_runtime; first by left; eauto.
        destruct (Model.runtime_stmt (Model.runtime_names Γ runtime)
          (Model.runtime_stack_id Γ runtime) else_branch) as [else_runtime|]
          eqn:Helse_runtime; [right; eauto|discriminate]. }
      destruct Hbranch as [[then_runtime Hthen_runtime]|
          [else_runtime Helse_runtime]].
      * rewrite Hthen_runtime in IHthen.
        unfold runtime_option_count, analysis_step_bit in *.
        destruct (GenericRegions.Atomicity.analysis_step_taken state),
          (GenericRegions.Atomicity.analysis_step_taken then_exit),
          (GenericRegions.Atomicity.analysis_step_taken else_exit);
          simpl in *; lia.
      * rewrite Helse_runtime in IHelse.
        unfold runtime_option_count, analysis_step_bit in *.
        destruct (GenericRegions.Atomicity.analysis_step_taken state),
          (GenericRegions.Atomicity.analysis_step_taken then_exit),
          (GenericRegions.Atomicity.analysis_step_taken else_exit);
          simpl in *; lia.
    + unfold runtime_option_count, analysis_step_bit in *.
      destruct (Model.runtime_stmt (Model.runtime_names Γ runtime)
        (Model.runtime_stack_id Γ runtime) then_branch),
        (GenericRegions.Atomicity.analysis_step_taken state),
        (GenericRegions.Atomicity.analysis_step_taken then_exit),
        (GenericRegions.Atomicity.analysis_step_taken else_exit);
        simpl in *; lia.
  - destruct Hcontinuous as [Hopen [_ _]].
    destruct statement; simpl in view; try discriminate.
    inversion view; subst.
    unfold certificate_runtime_statement. simpl.
    unfold GenericRegions.Atomicity.take_step in step.
    rewrite Hin_atomic in step. simpl in step.
    rewrite bool_decide_false in step; last exact Hopen.
    destruct (GenericRegions.Atomicity.analysis_step_taken state) eqn:Htaken;
      first discriminate.
    inversion step; subst outer. simpl.
    unfold analysis_step_bit, runtime_option_count.
    destruct (Model.runtime_stmt (Model.runtime_names Γ runtime)
      (Model.runtime_stack_id Γ runtime) body); rewrite Htaken; simpl; lia.
Qed.

Fixpoint operational_suffix_open_continuous {cost Γ entry exit}
    (suffix : operational_suffix cost Γ entry exit) : Prop :=
  match suffix with
  | OperationalDone _ => True
  | OperationalCons certificate rest =>
      certificate_open_continuous certificate /\
      operational_suffix_open_continuous rest
  end.

Lemma operational_suffix_step_budget {Γ cost entry exit}
    (suffix : operational_suffix cost Γ entry exit)
    (runtime : Model.stack_context Γ) :
  Model.runtime_cost_model_sound cost ->
  operational_suffix_open_continuous suffix ->
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  analysis_step_bit entry + operational_suffix_chunk_count suffix runtime <=
    analysis_step_bit exit.
Proof.
  intros Hcost Hcontinuous Hin_atomic.
  induction suffix as [state|fuel state statement middle final certificate rest
      IHrest]; simpl in Hcontinuous |- *.
  - lia.
  - destruct Hcontinuous as [Hhead Hrest].
    have Hmiddle_atomic :
        GenericRegions.Atomicity.analysis_in_atomic middle = false.
    { eapply certificate_preserves_nonatomic; eauto. }
    have Hhead_budget := certificate_runtime_step_budget certificate runtime
      Hcost Hhead Hin_atomic.
    specialize (IHrest Hrest Hmiddle_atomic). lia.
Qed.

Corollary operational_suffix_chunk_count_le_one {Γ cost entry exit}
    (suffix : operational_suffix cost Γ entry exit)
    (runtime : Model.stack_context Γ) :
  Model.runtime_cost_model_sound cost ->
  operational_suffix_open_continuous suffix ->
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  operational_suffix_chunk_count suffix runtime <= 1.
Proof.
  intros Hcost Hcontinuous Hin_atomic.
  have Hbudget := operational_suffix_step_budget suffix runtime
    Hcost Hcontinuous Hin_atomic.
  unfold analysis_step_bit in Hbudget.
  destruct (GenericRegions.Atomicity.analysis_step_taken entry),
    (GenericRegions.Atomicity.analysis_step_taken exit); simpl in *; lia.
Qed.

Lemma operational_suffix_runtime_count_le_chunks {Γ cost entry exit}
    (suffix : operational_suffix cost Γ entry exit)
    (runtime : Model.stack_context Γ) :
  runtime_option_count (operational_suffix_runtime suffix runtime) <=
    operational_suffix_chunk_count suffix runtime.
Proof.
  induction suffix; simpl; first lia.
  etrans; first apply combine_runtime_statements_count_le.
  lia.
Qed.

Lemma expand_sequence_suffix_runtime_sparse {cost Γ fuel state statement first
    middle second next final}
    (view : RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel state first middle)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel middle second next)
    (rest : operational_suffix cost Γ next final)
    (runtime : Model.stack_context Γ) :
  operational_suffix_chunk_count
      (expand_sequence_suffix view first_certificate second_certificate rest)
      runtime <= 1 ->
  operational_suffix_runtime
      (OperationalCons
        (GenericRegions.Atomicity.CertSequence cost Γ fuel state statement
          first middle second next view first_certificate second_certificate)
        rest) runtime =
    operational_suffix_runtime
      (expand_sequence_suffix view first_certificate second_certificate rest)
      runtime.
Proof.
  intros Hsparse. unfold expand_sequence_suffix in *.
  simpl in Hsparse |- *.
  unfold certificate_runtime_statement in *.
  destruct statement; simpl in view; try discriminate.
  inversion view; subst. simpl.
  apply combine_runtime_statements_assoc_sparse.
  have Hrest := operational_suffix_runtime_count_le_chunks rest runtime.
  lia.
Qed.

Lemma open_invariant_preserves_step_bit invariant entry exit :
  GenericRegions.Atomicity.open_invariant invariant entry = inr exit ->
  analysis_step_bit exit = analysis_step_bit entry.
Proof.
  unfold GenericRegions.Atomicity.open_invariant.
  destruct (bool_decide
    (invariant ∈ GenericRegions.Atomicity.analysis_open entry));
    first discriminate.
  destruct (bool_decide
    (invariant ∈ GenericRegions.Atomicity.analysis_mask entry));
    last discriminate.
  intros Hinr. inversion Hinr; subst exit. reflexivity.
Qed.

Lemma fold_invariant_preserves_step_bit_if_open invariant entry :
  GenericRegions.Atomicity.analysis_open
      (GenericRegions.Atomicity.fold_invariant invariant entry) ≠ ∅ ->
  analysis_step_bit
      (GenericRegions.Atomicity.fold_invariant invariant entry) =
    analysis_step_bit entry.
Proof.
  unfold GenericRegions.Atomicity.fold_invariant.
  destruct (bool_decide
    (invariant ∈ GenericRegions.Atomicity.analysis_open entry)); simpl.
  - destruct (bool_decide
      (GenericRegions.Atomicity.analysis_open entry ∖ {[invariant]} = ∅))
      eqn:Hremaining; simpl.
    + intros Hopen. apply bool_decide_eq_true in Hremaining.
      rewrite Hremaining in Hopen. contradiction.
    + reflexivity.
  - reflexivity.
Qed.

Lemma open_atomic_step_sets_step_bit entry outer :
  GenericRegions.Atomicity.take_step GenericRegions.Atomicity.AtomicStep entry =
    inr outer ->
  GenericRegions.Atomicity.analysis_open entry ≠ ∅ ->
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  analysis_step_bit entry = 0 /\ analysis_step_bit outer = 1.
Proof.
  intros Hstep Hopen Hin_atomic.
  unfold GenericRegions.Atomicity.take_step in Hstep.
  rewrite Hin_atomic in Hstep. simpl in Hstep.
  rewrite bool_decide_false in Hstep; last exact Hopen.
  destruct (GenericRegions.Atomicity.analysis_step_taken entry) eqn:Htaken;
    first discriminate.
  inversion Hstep; subst outer. unfold analysis_step_bit.
  rewrite Htaken. simpl. auto.
Qed.

Lemma aligned_ordinary_leaf_runtime_valid {Γ F Δ cost entry statement exit}
    (view : RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : GenericRegions.Atomicity.take_step (cost Γ statement) entry =
      inr exit)
    (pre post : assertion Γ F Δ)
    (derivation : Certified.Rules.RavenHoareTriple pre statement
      (GenericRegions.Atomicity.analysis_mask entry)
      (GenericRegions.Atomicity.analysis_mask exit) post)
    stack runtime formals binders atoms ambient
    (Hactive : Model.runtime_mask
      (GenericRegions.Atomicity.analysis_mask exit) ⊆
      Model.active_runtime_mask ambient entry) :
  (global_world_context atoms ∗
   VSemantics.S.interp_assertion (Leaf.predicates atoms)
     runtime formals binders atoms pre ∗
   World.access_stack_interp atoms ambient stack) ⊢
  translated_runtime_wp runtime ambient entry exit statement
    (global_world_context atoms ∗
     VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms post ∗
     World.access_stack_interp atoms ambient stack).
Proof.
  iIntros "[#Hglobal [Hpre Haccess]]".
  iPoseProof (ordinary_leaf_rule_valid pre post statement entry exit view
    derivation runtime formals binders atoms ambient Hactive
    with "[$Hglobal $Hpre]")
    as "Hwp".
  iCombine "Hglobal Haccess" as "Hframe".
  iCombine "Hwp Hframe" as "Hcombined".
  iPoseProof (Execution.Primitives.Interface.operation_frame
    with "Hcombined") as "Hwp".
  iApply leaf_operation_runtime_refinement_total; [exact view|exact step|].
  iApply (Execution.Primitives.Interface.operation_mono with "Hwp").
  iIntros "[Hpost [#Hglobal Haccess]]". iFrame.
  Unshelve. all: eauto.
Qed.

Lemma invariant_namespace_active_from_footprint
    {Γ fuel entry statement exit cost}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    ambient invariant :
  invariant ∈ GenericRegions.Atomicity.certificate_footprint certificate ->
  invariant ∉ GenericRegions.Atomicity.analysis_open entry ->
  Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint certificate) ⊆ ambient ->
  ↑(Resources.invariant_namespace invariant) ⊆
    Model.active_runtime_mask ambient entry.
Proof.
  intros Hfootprint Hnot_open Henvelope.
  have Hnamespace : ↑(Resources.invariant_namespace invariant) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply Model.invariant_namespace_subset_runtime_mask. exact Hfootprint. }
  have Hdisjoint : (↑(Resources.invariant_namespace invariant) : coPset) ##
      Model.invariant_mask (GenericRegions.Atomicity.analysis_open entry).
  { apply Model.invariant_mask_disjoint. exact Hnot_open. }
  unfold Model.active_runtime_mask, Model.enabled_runtime_mask.
  set_solver.
Qed.

Lemma invariant_unfold_node_valid {Γ F Δ} node invariant arguments
    (store : symbolic_store Γ F Δ) body
    (entry exit : GenericRegions.Atomicity.analysis_state) ambient rest :
  GenericRegions.Atomicity.open_invariant invariant entry = inr exit ->
  ↑(Resources.invariant_namespace invariant) ⊆
    Model.active_runtime_mask ambient entry ->
  Contracts.instantiated_invariant Γ F Δ
    (Logic.invariant_args invariant) invariant
    (Hoare.symbolize_expr_list store arguments) body ->
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env),
  (global_world_context atoms ∗
   VSemantics.S.interp_assertion (Leaf.predicates atoms)
     runtime formals binders atoms
     (AAnd (AStack store)
       (AInvariant invariant (Hoare.symbolize_expr_list store arguments))) ∗
   World.access_stack_interp atoms ambient rest) ⊢
  Execution.Primitives.operation_wp runtime ambient
    entry (TUnfold node invariant arguments) exit
    (global_world_context atoms ∗
     VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms (AAnd (AStack store) body) ∗
     World.access_stack_interp atoms ambient
       ((invariant, GenericRegions.Atomicity.analysis_open entry) :: rest)).
Proof.
  intros Htransition Hnamespace Hinst runtime formals binders atoms.
  have Htransition_facts := Htransition.
  apply GenericRegions.Atomicity.open_invariant_success in Htransition_facts as
    (_ & _ & _ & Hexit_open).
  have Hactive_exit : Model.active_runtime_mask ambient exit =
      Model.enabled_runtime_mask ambient
        ({[invariant]} ∪ GenericRegions.Atomicity.analysis_open entry).
  { unfold Model.active_runtime_mask. now rewrite Hexit_open. }
  destruct (invariant_definition_compatible runtime formals binders atoms
    invariant (Hoare.symbolize_expr_list store arguments) body Hinst)
    as (canonical_values & Hcanonical & Hbody).
  iIntros "[#Hworld [[Hstack Htoken] Haccess]]".
  iPoseProof "Hworld" as "#Hglobal".
  iEval (unfold global_world_context) in "Hworld".
  iDestruct "Hworld" as "[#Hinvariant_world [#Hchunks #Hprocedures]]".
  iRename "Hglobal" into "Hworld".
  iDestruct "Htoken" as (actual_values) "[%Hactual #Htoken]".
  have Hvalues := invariant_values_unique invariant actual_values canonical_values.
  subst actual_values.
  iPoseProof ("Hinvariant_world" $! invariant) as "#Hinvariant".
  unfold Execution.Primitives.operation_wp.
  simpl. rewrite Hactive_exit.
  iMod (World.open_world_access_frame atoms ambient invariant canonical_values
    (GenericRegions.Atomicity.analysis_open entry) Hnamespace
    with "Hinvariant Htoken") as "[Hbody Hframe]".
  iModIntro. iFrame "Hworld Hstack Haccess Hframe".
  rewrite Hbody. iExact "Hbody".
Qed.

Lemma invariant_fold_node_valid {Γ F Δ} node invariant arguments
    (store : symbolic_store Γ F Δ) body
    (entry : GenericRegions.Atomicity.analysis_state) ambient outer_open rest :
  GenericRegions.Atomicity.state_wf entry ->
  invariant ∈ GenericRegions.Atomicity.analysis_open entry ->
  invariant ∉ outer_open ->
  GenericRegions.Atomicity.analysis_open entry = {[invariant]} ∪ outer_open ->
  Contracts.instantiated_invariant Γ F Δ
    (Logic.invariant_args invariant) invariant
    (Hoare.symbolize_expr_list store arguments) body ->
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env),
  (global_world_context atoms ∗
   VSemantics.S.interp_assertion (Leaf.predicates atoms)
     runtime formals binders atoms (AAnd (AStack store) body) ∗
   World.access_stack_interp atoms ambient
     ((invariant, outer_open) :: rest)) ⊢
  Execution.Primitives.operation_wp runtime ambient entry
    (TFold node invariant arguments)
    (GenericRegions.Atomicity.fold_invariant invariant entry)
    (global_world_context atoms ∗
     VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms
       (AAnd (AStack store)
         (AInvariant invariant (Hoare.symbolize_expr_list store arguments))) ∗
     World.access_stack_interp atoms ambient rest).
Proof.
  intros Hwf Hopen Houter Hopen_eq Hinst runtime formals binders atoms.
  have Hfold := GenericRegions.Atomicity.fold_open_invariant invariant entry Hopen.
  destruct Hfold as [_ Hfold_open].
  have Hremaining :
      GenericRegions.Atomicity.analysis_open entry ∖ {[invariant]} = outer_open.
  { rewrite Hopen_eq. set_solver. }
  have Hactive_entry : Model.active_runtime_mask ambient entry =
      Model.enabled_runtime_mask ambient ({[invariant]} ∪ outer_open).
  { unfold Model.active_runtime_mask. now rewrite Hopen_eq. }
  have Hactive_exit :
      Model.active_runtime_mask ambient
        (GenericRegions.Atomicity.fold_invariant invariant entry) =
      Model.enabled_runtime_mask ambient outer_open.
  { unfold Model.active_runtime_mask. rewrite Hfold_open Hremaining. reflexivity. }
  destruct (invariant_definition_compatible runtime formals binders atoms
    invariant (Hoare.symbolize_expr_list store arguments) body Hinst)
    as (values & Harguments & Hbody).
  iIntros "[#Hworld [[Hstack Hbody] [Hframe Haccess]]]".
  iPoseProof (bi.equiv_entails_1_1 _ _ Hbody with "Hbody") as "Hbody".
  unfold Execution.Primitives.operation_wp. simpl.
  rewrite Hactive_entry Hactive_exit.
  iMod (World.close_access_frame atoms ambient invariant values outer_open
    (fun stored_values =>
      invariant_values_unique invariant stored_values values)
    with "[$Hbody $Hframe]") as "#Htoken".
  iModIntro. iFrame "Hworld Hstack Haccess". iExists values. iFrame "Htoken".
  iPureIntro. exact Harguments.
Qed.

(** An unmatched fold allocates a fresh logical invariant instance.  The
    Raven mask grows, but no invariant is open or closed, so the physical
    Iris mask remains unchanged inside the ambient envelope. *)
Lemma invariant_fresh_fold_node_valid {Γ F Δ} node invariant arguments
    (store : symbolic_store Γ F Δ) body
    (entry : GenericRegions.Atomicity.analysis_state) ambient rest :
  invariant ∉ GenericRegions.Atomicity.analysis_open entry ->
  ↑(Resources.invariant_namespace invariant) ⊆
    Model.active_runtime_mask ambient entry ->
  Contracts.instantiated_invariant Γ F Δ
    (Logic.invariant_args invariant) invariant
    (Hoare.symbolize_expr_list store arguments) body ->
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env),
  (global_world_context atoms ∗
   VSemantics.S.interp_assertion (Leaf.predicates atoms)
     runtime formals binders atoms (AAnd (AStack store) body) ∗
   World.access_stack_interp atoms ambient rest) ⊢
  Execution.Primitives.operation_wp runtime ambient entry
    (TFold node invariant arguments)
    (GenericRegions.Atomicity.fold_invariant invariant entry)
    (global_world_context atoms ∗
     VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms
       (AAnd (AStack store)
         (AInvariant invariant (Hoare.symbolize_expr_list store arguments))) ∗
     World.access_stack_interp atoms ambient rest).
Proof.
  intros Hfresh Hnamespace Hinst runtime formals binders atoms.
  destruct (invariant_definition_compatible runtime formals binders atoms
    invariant (Hoare.symbolize_expr_list store arguments) body Hinst)
    as (values & Harguments & Hbody).
  have Hfold_facts := GenericRegions.Atomicity.fold_fresh_invariant
    invariant entry Hfresh.
  destruct Hfold_facts as [_ Hfold_open].
  have Hactive : Model.active_runtime_mask ambient
      (GenericRegions.Atomicity.fold_invariant invariant entry) =
      Model.active_runtime_mask ambient entry.
  { apply Model.active_runtime_mask_same_open. exact Hfold_open. }
  iIntros "[#Hworld [[Hstack Hbody] Haccess]]".
  iPoseProof "Hworld" as "#Hglobal".
  iEval (unfold global_world_context) in "Hworld".
  iDestruct "Hworld" as "[#Hinvariant_world [#Hchunks #Hprocedures]]".
  iRename "Hglobal" into "Hworld".
  iPoseProof (bi.equiv_entails_1_1 _ _ Hbody with "Hbody") as "Hbody".
  iPoseProof ("Hinvariant_world" $! invariant) as "#Hinvariant".
  unfold Execution.Primitives.operation_wp. simpl. rewrite Hactive.
  iMod (World.establish_world atoms invariant values
    (Model.active_runtime_mask ambient entry) Hnamespace
    with "Hinvariant Hbody") as "#Htoken".
  iModIntro. iFrame "Hworld Hstack Haccess". iExists values.
  iFrame "Htoken". iPureIntro. exact Harguments.
Qed.

(** Semantic validity for the suffix-preserving operational interpreter.
    Unlike [certificate_semantically_valid], this judgment already exposes
    concrete runtime WPs at physical leaves, conditionals, and trusted atomic
    blocks. *)
Definition aligned_runtime_certificate_valid {Γ F Δ fuel}
    {cost : GenericRegions.Atomicity.cost_model}
    {stack_in stack_out : list GenericRegions.Atomicity.access_marker}
    {pre post : Translation.Assertions.assertion Γ F Δ}
    {statement : stmt Γ}
    {entry exit : GenericRegions.Atomicity.analysis_state}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit) : Prop :=
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint certificate) ⊆ ambient ->
    forall tail : iProp,
    ((global_world_context atoms ∗
      VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms post ∗
      World.access_stack_interp atoms ambient stack_out) ⊢ tail) ->
    (global_world_context atoms ∗
     VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     World.access_stack_interp atoms ambient stack_in) ⊢
    aligned_runtime_region_wp certificate runtime ambient tail.

Lemma aligned_runtime_ordinary_leaf_valid {Γ F Δ fuel cost entry statement exit}
    (view : RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : GenericRegions.Atomicity.take_step (cost Γ statement) entry =
      inr exit)
    stack (pre post : assertion Γ F Δ)
    (derivation : Certified.Rules.RavenHoareTriple pre statement
      (GenericRegions.Atomicity.analysis_mask entry)
      (GenericRegions.Atomicity.analysis_mask exit) post)
    (Hwf : GenericRegions.Atomicity.state_wf entry) :
  aligned_runtime_certificate_valid (stack_in := stack) (stack_out := stack)
    (pre := pre) (post := post)
    (GenericRegions.Atomicity.CertLeaf cost Γ fuel entry statement exit
      view step).
Proof.
  intros runtime formals binders atoms ambient Henvelope tail Htail.
  have Hexit_envelope : Model.runtime_mask
      (GenericRegions.Atomicity.analysis_mask exit) ⊆ ambient.
  { etrans; last exact Henvelope. apply Model.runtime_mask_mono.
    apply GenericRegions.Atomicity.certificate_exit_subset_footprint. }
  have Hsets := GenericRegions.Atomicity.take_step_preserves_sets _ _ _ step.
  destruct Hsets as [_ Hopen].
  have Hexit_wf : GenericRegions.Atomicity.state_wf exit.
  { eapply GenericRegions.Atomicity.certificate_preserves_wf; [exact Hwf|].
    exact (GenericRegions.Atomicity.CertLeaf cost Γ fuel entry statement exit
      view step). }
  have Hactive_exit := Model.runtime_mask_subset_active ambient exit Hexit_wf
    Hexit_envelope.
  have Hactive : Model.runtime_mask
      (GenericRegions.Atomicity.analysis_mask exit) ⊆
      Model.active_runtime_mask ambient entry.
  { rewrite (Model.active_runtime_mask_same_open ambient entry exit
      (eq_sym Hopen)).
    exact Hactive_exit. }
  simpl. iIntros "Hresources".
  iPoseProof (aligned_ordinary_leaf_runtime_valid view step pre post derivation
    stack runtime formals binders atoms ambient Hactive with "Hresources") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp"). exact Htail.
Qed.

Lemma aligned_runtime_unfold_valid {Γ F Δ fuel cost entry node invariant
    arguments exit store body}
    (view : RegionSyntax.view (TUnfold node invariant arguments) =
      TypedAnalysisView.ViewUnfold invariant)
    (step : GenericRegions.Atomicity.open_invariant invariant entry = inr exit)
    (available : invariant ∈ GenericRegions.Atomicity.analysis_mask entry)
    (instantiated : Contracts.instantiated_invariant Γ F Δ
      (Logic.invariant_args invariant) invariant
      (Hoare.symbolize_expr_list store arguments) body)
    rest :
  aligned_runtime_certificate_valid
    (stack_in := rest)
    (stack_out := (invariant, GenericRegions.Atomicity.analysis_open entry) :: rest)
    (pre := AAnd (AStack store)
      (AInvariant invariant (Hoare.symbolize_expr_list store arguments)))
    (post := AAnd (AStack store) body)
    (GenericRegions.Atomicity.CertUnfold cost Γ fuel entry
      (TUnfold node invariant arguments) invariant exit view step).
Proof.
  intros runtime formals binders atoms ambient Henvelope tail Htail.
  have Hfacts := step.
  apply GenericRegions.Atomicity.open_invariant_success in Hfacts as
    (Hfresh & _ & _ & _).
  have Hfootprint : invariant ∈
      GenericRegions.Atomicity.certificate_footprint
        (GenericRegions.Atomicity.CertUnfold cost Γ fuel entry
          (TUnfold node invariant arguments) invariant exit view step).
  { apply GenericRegions.Atomicity.certificate_entry_subset_footprint.
    exact available. }
  have Hnamespace := invariant_namespace_active_from_footprint
    (GenericRegions.Atomicity.CertUnfold cost Γ fuel entry
      (TUnfold node invariant arguments) invariant exit view step)
    ambient invariant Hfootprint Hfresh Henvelope.
  simpl. iIntros "Hresources".
  iPoseProof (invariant_unfold_node_valid node invariant arguments store body
    entry exit ambient rest step Hnamespace instantiated runtime formals
    binders atoms with "Hresources") as "Hwp".
  iApply (Execution.Primitives.Interface.operation_mono with "Hwp").
  exact Htail.
Qed.

Lemma aligned_runtime_matched_fold_valid {Γ F Δ fuel cost entry node invariant
    arguments store body outer_open rest}
    (view : RegionSyntax.view (TFold node invariant arguments) =
      TypedAnalysisView.ViewFold invariant)
    (Hwf : GenericRegions.Atomicity.state_wf entry)
    (Hopen : invariant ∈ GenericRegions.Atomicity.analysis_open entry)
    (Houter : invariant ∉ outer_open)
    (Hopen_eq : GenericRegions.Atomicity.analysis_open entry =
      {[invariant]} ∪ outer_open)
    (instantiated : Contracts.instantiated_invariant Γ F Δ
      (Logic.invariant_args invariant) invariant
      (Hoare.symbolize_expr_list store arguments) body) :
  aligned_runtime_certificate_valid
    (stack_in := (invariant, outer_open) :: rest) (stack_out := rest)
    (pre := AAnd (AStack store) body)
    (post := AAnd (AStack store)
      (AInvariant invariant (Hoare.symbolize_expr_list store arguments)))
    (GenericRegions.Atomicity.CertFold cost Γ fuel entry
      (TFold node invariant arguments) invariant view).
Proof.
  intros runtime formals binders atoms ambient _ tail Htail.
  simpl. iIntros "Hresources".
  iPoseProof (invariant_fold_node_valid node invariant arguments store body
    entry ambient outer_open rest Hwf Hopen Houter Hopen_eq instantiated
    runtime formals binders atoms with "Hresources") as "Hwp".
  iApply (Execution.Primitives.Interface.operation_mono with "Hwp").
  exact Htail.
Qed.

Lemma aligned_runtime_fresh_fold_valid {Γ F Δ fuel cost entry node invariant
    arguments store body rest}
    (view : RegionSyntax.view (TFold node invariant arguments) =
      TypedAnalysisView.ViewFold invariant)
    (Hfresh : invariant ∉ GenericRegions.Atomicity.analysis_open entry)
    (instantiated : Contracts.instantiated_invariant Γ F Δ
      (Logic.invariant_args invariant) invariant
      (Hoare.symbolize_expr_list store arguments) body) :
  aligned_runtime_certificate_valid
    (stack_in := rest) (stack_out := rest)
    (pre := AAnd (AStack store) body)
    (post := AAnd (AStack store)
      (AInvariant invariant (Hoare.symbolize_expr_list store arguments)))
    (GenericRegions.Atomicity.CertFold cost Γ fuel entry
      (TFold node invariant arguments) invariant view).
Proof.
  intros runtime formals binders atoms ambient Henvelope tail Htail.
  have Hexit_member : invariant ∈
      GenericRegions.Atomicity.analysis_mask
        (GenericRegions.Atomicity.fold_invariant invariant entry).
  { rewrite Certified.fold_analysis_mask. set_solver. }
  have Hfootprint : invariant ∈
      GenericRegions.Atomicity.certificate_footprint
        (GenericRegions.Atomicity.CertFold cost Γ fuel entry
          (TFold node invariant arguments) invariant view).
  { apply GenericRegions.Atomicity.certificate_exit_subset_footprint.
    exact Hexit_member. }
  have Hnamespace := invariant_namespace_active_from_footprint
    (GenericRegions.Atomicity.CertFold cost Γ fuel entry
      (TFold node invariant arguments) invariant view)
    ambient invariant Hfootprint Hfresh Henvelope.
  simpl. iIntros "Hresources".
  iPoseProof (invariant_fresh_fold_node_valid node invariant arguments store
    body entry ambient rest Hfresh Hnamespace instantiated runtime formals
    binders atoms with "Hresources") as "Hwp".
  iApply (Execution.Primitives.Interface.operation_mono with "Hwp").
  exact Htail.
Qed.

Lemma aligned_runtime_sequence_valid {Γ F Δ fuel cost state statement first
    middle second exit}
    (view : RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel state first middle)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel middle second exit)
    stack_in stack_middle stack_out
    (pre middle_assertion post : assertion Γ F Δ) :
  aligned_runtime_certificate_valid (stack_in := stack_in)
    (stack_out := stack_middle) (pre := pre) (post := middle_assertion)
    first_certificate ->
  aligned_runtime_certificate_valid (stack_in := stack_middle)
    (stack_out := stack_out) (pre := middle_assertion) (post := post)
    second_certificate ->
  aligned_runtime_certificate_valid (stack_in := stack_in)
    (stack_out := stack_out) (pre := pre) (post := post)
    (GenericRegions.Atomicity.CertSequence cost Γ fuel state statement first
      middle second exit view first_certificate second_certificate).
Proof.
  intros Hfirst Hsecond runtime formals binders atoms ambient Hfootprint.
  have Hfirst_footprint : Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint first_certificate) ⊆ ambient.
  { etrans; last exact Hfootprint. apply Model.runtime_mask_mono.
    simpl. set_solver. }
  have Hsecond_footprint : Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint second_certificate) ⊆ ambient.
  { etrans; last exact Hfootprint. apply Model.runtime_mask_mono.
    simpl. set_solver. }
  intros tail Htail. simpl. iIntros "Hresources".
  iApply (Hfirst runtime formals binders atoms ambient Hfirst_footprint
    (aligned_runtime_region_wp second_certificate runtime ambient tail)).
  - iIntros "Hmiddle".
    iApply (Hsecond runtime formals binders atoms ambient Hsecond_footprint
      tail Htail). iExact "Hmiddle".
  - iExact "Hresources".
Qed.

Definition certificate_semantically_valid {Γ F Δ fuel}
    {cost : GenericRegions.Atomicity.cost_model}
    {stack_in stack_out : list GenericRegions.Atomicity.access_marker}
    {pre post : Translation.Assertions.assertion Γ F Δ}
    {statement : stmt Γ}
    {entry exit : GenericRegions.Atomicity.analysis_state}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit) : Prop :=
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint certificate) ⊆ ambient ->
    (global_world_context atoms ∗
     VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     World.access_stack_interp atoms ambient stack_in) ⊢
    Execution.region_wp certificate runtime ambient
      (global_world_context atoms ∗
       VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       World.access_stack_interp atoms ambient stack_out).

(** Closed operational refinement of the same certificate.  Unlike bare
    [region_wp], this target remembers the translated statement and its
    entry/exit active masks.  Its proof must proceed over the Hoare-aligned
    certificate so that the conditional case retains the symbolic store used
    to justify the selected runtime branch.

    This is deliberately restricted to a well-bracketed region.  A prefix
    ending with an open invariant cannot independently refine to a raw Iris
    WP: [wp_atomic] needs the certified suffix containing the matching close.
    The eventual proof therefore uses a continuation-passing induction over
    the LIFO certificate and exposes only this closed theorem. *)
Definition closed_certificate_runtime_semantically_valid {Γ F Δ fuel}
    {cost : GenericRegions.Atomicity.cost_model}
    {pre post : Translation.Assertions.assertion Γ F Δ}
    {statement : stmt Γ}
    {entry exit : GenericRegions.Atomicity.analysis_state}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit) : Prop :=
  GenericRegions.Atomicity.analysis_open entry = ∅ ->
  GenericRegions.Atomicity.analysis_open exit = ∅ ->
  GenericRegions.Atomicity.lifo_certificate certificate [] [] ->
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    Model.runtime_mask
      (GenericRegions.Atomicity.analysis_mask exit) ⊆ ambient ->
    (global_world_context atoms ∗
     VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     World.access_stack_interp atoms ambient []) ⊢
    translated_runtime_wp runtime ambient entry exit statement
      (global_world_context atoms ∗
       VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       World.access_stack_interp atoms ambient []).

Definition semantically_valid {Γ F Δ fuel}
    {cost : GenericRegions.Atomicity.cost_model}
    {stack_in stack_out : list GenericRegions.Atomicity.access_marker}
    {pre post : Translation.Assertions.assertion Γ F Δ}
    {statement : stmt Γ}
    {entry exit : GenericRegions.Atomicity.analysis_state}
    (certified : @Certified.CertifiedRavenHoareTriple cost Γ F Δ fuel
      stack_in stack_out pre statement entry exit post) : Prop :=
  @certificate_semantically_valid Γ F Δ fuel cost stack_in stack_out pre post
    statement entry exit
    (@Certified.certified_analysis cost Γ F Δ fuel stack_in stack_out
      pre statement entry exit post certified).

Lemma preserve_access_stack_valid {Γ F Δ fuel cost entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    stack (pre post : assertion Γ F Δ) :
  (forall (runtime : Model.stack_context Γ) (formals : formal_env F)
      (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint certificate) ⊆ ambient ->
    (global_world_context atoms ∗
     VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre) ⊢
    Execution.region_wp certificate runtime ambient
      (VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms post)) ->
  certificate_semantically_valid (stack_in := stack) (stack_out := stack)
    (pre := pre) (post := post) certificate.
Proof.
  intros Hvalid runtime formals binders atoms ambient Hfootprint.
  iIntros "[#Hworld [Hpre Haccess]]".
  iCombine "Hworld Haccess" as "Hframe".
  iApply (Execution.region_wp_mono runtime ambient certificate
    (VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms post ∗
     (global_world_context atoms ∗
      World.access_stack_interp atoms ambient stack))%I
    (global_world_context atoms ∗
     VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms post ∗
     World.access_stack_interp atoms ambient stack)%I).
  { iIntros "[Hpost [#Hworld Haccess]]".
    iFrame "Hworld Hpost Haccess". }
  iApply Execution.region_wp_frame. iFrame "Hframe".
  iApply (Hvalid runtime formals binders atoms ambient Hfootprint).
  iFrame "Hworld Hpre".
Qed.

Lemma leaf_statement_valid {Γ F Δ fuel cost entry statement exit}
    (view : RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : GenericRegions.Atomicity.take_step (cost Γ statement) entry =
      inr exit)
    stack (pre post : assertion Γ F Δ) :
  (forall (runtime : Model.stack_context Γ) (formals : formal_env F)
      (binders : binder_env Δ) (atoms : atom_env) (ambient : coPset),
    Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint
        (GenericRegions.Atomicity.CertLeaf cost Γ fuel entry statement exit
          view step)) ⊆ ambient ->
    (global_world_context atoms ∗
     VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre) ⊢
    Execution.Primitives.operation_wp runtime ambient entry statement exit
      (VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms post)) ->
  certificate_semantically_valid (stack_in := stack) (stack_out := stack)
    (pre := pre) (post := post)
    (GenericRegions.Atomicity.CertLeaf cost Γ fuel entry statement exit
      view step).
Proof.
  intros Hvalid. apply preserve_access_stack_valid.
  intros runtime formals binders atoms ambient Henvelope.
  apply Hvalid. exact Henvelope.
Qed.

Lemma assertion_frame_valid {Γ F Δ fuel cost entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    stack_in stack_out (pre post frame : assertion Γ F Δ) :
  certificate_semantically_valid (stack_in := stack_in) (stack_out := stack_out)
    (pre := pre) (post := post) certificate ->
  certificate_semantically_valid (stack_in := stack_in) (stack_out := stack_out)
    (pre := AAnd pre frame) (post := AAnd post frame) certificate.
Proof.
  intros Hvalid runtime formals binders atoms ambient Hfootprint.
  iIntros "[#Hworld [[Hpre Hframe] Haccess]]".
  iApply (Execution.region_wp_mono runtime ambient certificate
    ((global_world_context atoms ∗
      VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms post ∗
      World.access_stack_interp atoms ambient stack_out) ∗
     VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms frame)%I
    (global_world_context atoms ∗
     (VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms post ∗
      VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms frame) ∗
     World.access_stack_interp atoms ambient stack_out)%I).
  { iIntros "[[#Hworld [Hpost Haccess]] Hframe]".
    iFrame "Hworld Hpost Hframe Haccess". }
  iApply (Execution.region_wp_frame runtime ambient certificate
    (global_world_context atoms ∗
     VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms post ∗
     World.access_stack_interp atoms ambient stack_out)%I
    (VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms frame)%I).
  iSplitL "Hworld Hpre Haccess".
  - iPoseProof (Hvalid runtime formals binders atoms ambient Hfootprint
      with "[$Hworld $Hpre $Haccess]") as "Hwp".
    iExact "Hwp".
  - iExact "Hframe".
Qed.

Lemma consequence_valid {Γ F Δ fuel cost entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    stack_in stack_out (pre pre' post post' : assertion Γ F Δ) :
  certificate_semantically_valid (stack_in := stack_in) (stack_out := stack_out)
    (pre := pre) (post := post) certificate ->
  Hoare.assertion_entails pre' pre -> Hoare.assertion_entails post post' ->
  certificate_semantically_valid (stack_in := stack_in) (stack_out := stack_out)
    (pre := pre') (post := post') certificate.
Proof.
  intros Hvalid Hpre Hpost runtime formals binders atoms ambient Hfootprint.
  iIntros "[#Hworld [Hpre Haccess]]".
  iPoseProof (VSemantics.assertion_entails_valid (Leaf.predicates atoms)
    pre' pre Hpre runtime
    formals binders atoms with "Hpre") as "Hpre".
  iPoseProof (Hvalid runtime formals binders atoms ambient Hfootprint
    with "[$Hworld $Hpre $Haccess]") as "Hwp".
  iApply (Execution.region_wp_mono with "Hwp").
  iIntros "[#Hworld [Hpost Haccess]]". iFrame "Hworld Haccess".
  iApply (VSemantics.assertion_entails_valid (Leaf.predicates atoms)
    post post' Hpost runtime
    formals binders atoms with "Hpost").
Qed.

Lemma exists_elim_valid {Γ F Δ t fuel cost entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    stack_in stack_out (body : assertion Γ F (t :: Δ))
    (post : assertion Γ F Δ) :
  certificate_semantically_valid (F := F) (Δ := t :: Δ)
    (stack_in := stack_in) (stack_out := stack_out)
    (pre := body) (post := weaken_assertion post) certificate ->
  certificate_semantically_valid (stack_in := stack_in) (stack_out := stack_out)
    (pre := AExists t body) (post := post) certificate.
Proof.
  intros Hvalid runtime formals binders atoms ambient Hfootprint.
  iIntros "[#Hworld [Hpre Haccess]]". iDestruct "Hpre" as (value) "Hbody".
  iPoseProof (Hvalid runtime formals (binder_cons value binders) atoms
    ambient Hfootprint
    with "[$Hworld $Hbody $Haccess]") as "Hwp".
  iApply (Execution.region_wp_mono with "Hwp").
  iIntros "[#Hworld [Hpost Haccess]]". iFrame "Hworld Haccess".
  rewrite VSemantics.S.interp_weaken_assertion. iExact "Hpost".
Qed.

Lemma exists_preserve_valid {Γ F Δ t fuel cost entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    stack_in stack_out (body post : assertion Γ F (t :: Δ)) :
  certificate_semantically_valid (F := F) (Δ := t :: Δ)
    (stack_in := stack_in) (stack_out := stack_out)
    (pre := body) (post := post) certificate ->
  certificate_semantically_valid (stack_in := stack_in) (stack_out := stack_out)
    (pre := AExists t body) (post := AExists t post) certificate.
Proof.
  intros Hvalid runtime formals binders atoms ambient Hfootprint.
  iIntros "[#Hworld [Hpre Haccess]]". iDestruct "Hpre" as (value) "Hbody".
  iPoseProof (Hvalid runtime formals (binder_cons value binders) atoms
    ambient Hfootprint
    with "[$Hworld $Hbody $Haccess]") as "Hwp".
  iApply (Execution.region_wp_mono with "Hwp").
  iIntros "[#Hworld [Hpost Haccess]]". iFrame "Hworld Haccess".
  iExists value. iExact "Hpost".
Qed.

Lemma sequence_valid {Γ F Δ fuel cost state statement first middle second exit}
    (view : RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel state first middle)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel middle second exit)
    stack_in stack_middle stack_out
    (pre middle_assertion post : assertion Γ F Δ) :
  certificate_semantically_valid (stack_in := stack_in)
    (stack_out := stack_middle) (pre := pre) (post := middle_assertion)
    first_certificate ->
  certificate_semantically_valid (stack_in := stack_middle)
    (stack_out := stack_out) (pre := middle_assertion) (post := post)
    second_certificate ->
  certificate_semantically_valid (stack_in := stack_in)
    (stack_out := stack_out) (pre := pre) (post := post)
    (GenericRegions.Atomicity.CertSequence cost Γ fuel state statement first
      middle second exit view first_certificate second_certificate).
Proof.
  intros Hfirst Hsecond runtime formals binders atoms ambient Hfootprint.
  have Hfirst_footprint : Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint first_certificate) ⊆ ambient.
  { etrans; last exact Hfootprint. apply Model.runtime_mask_mono.
    simpl. set_solver. }
  have Hsecond_footprint : Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint second_certificate) ⊆ ambient.
  { etrans; last exact Hfootprint. apply Model.runtime_mask_mono.
    simpl. set_solver. }
  simpl. iIntros "[#Hworld [Hpre Haccess]]".
  iPoseProof (Hfirst runtime formals binders atoms ambient Hfirst_footprint
    with "[$Hworld $Hpre $Haccess]") as "Hfirst_wp".
  iApply (Execution.region_wp_mono with "Hfirst_wp").
  iIntros "[#Hworld [Hmiddle Haccess]]".
  iApply (Hsecond runtime formals binders atoms ambient Hsecond_footprint).
  iFrame "Hworld Hmiddle Haccess".
Qed.

Lemma conditional_valid {Γ F Δ fuel cost state node store frame condition
    then_branch else_branch then_exit else_exit}
    (then_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel state then_branch then_exit)
    (else_certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel state else_branch else_exit)
    (open_equal : GenericRegions.Atomicity.analysis_open then_exit =
      GenericRegions.Atomicity.analysis_open else_exit)
    (atomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    stack_in stack_out (post : assertion Γ F Δ) :
  certificate_semantically_valid (stack_in := stack_in) (stack_out := stack_out)
    (pre := AAnd (AStack store)
      (AAnd frame (AExpr (Hoare.symbolize_expr store condition))))
    (post := post) then_certificate ->
  certificate_semantically_valid (stack_in := stack_in) (stack_out := stack_out)
    (pre := AAnd (AStack store)
      (AAnd frame (AExpr (EUnOp UNot
        (Hoare.symbolize_expr store condition)))))
    (post := post) else_certificate ->
  certificate_semantically_valid (stack_in := stack_in) (stack_out := stack_out)
    (pre := AAnd (AStack store) frame) (post := post)
    (GenericRegions.Atomicity.CertConditional cost Γ fuel state
      (TIf node condition then_branch else_branch) then_branch else_branch
      then_exit else_exit eq_refl then_certificate else_certificate
      open_equal atomic_equal).
Proof.
  intros Hthen Helse runtime formals binders atoms ambient Hfootprint.
  have Hthen_footprint : Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint then_certificate) ⊆ ambient.
  { etrans; last exact Hfootprint. apply Model.runtime_mask_mono.
    simpl. set_solver. }
  have Helse_footprint : Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint else_certificate) ⊆ ambient.
  { etrans; last exact Hfootprint. apply Model.runtime_mask_mono.
    simpl. set_solver. }
  simpl.
  unfold Execution.Primitives.branch_wp. simpl.
  iIntros "[#Hworld [[Hstack Hframe] Haccess]]".
  destruct (interp_expr_total formals binders atoms
    (Hoare.symbolize_expr store condition)) as [value Hvalue].
  dependent destruction value. destruct b.
  - iLeft. iApply (Hthen runtime formals binders atoms ambient Hthen_footprint).
    iFrame "Hworld Hstack Hframe Haccess". iPureIntro. exact Hvalue.
  - iRight. iApply (Helse runtime formals binders atoms ambient Helse_footprint).
    iFrame "Hworld Hstack Hframe Haccess". iPureIntro. simpl.
    rewrite Hvalue. reflexivity.
Qed.

Lemma atomic_valid {Γ F Δ fuel cost state node body outer inner}
    (step : GenericRegions.Atomicity.take_step
      GenericRegions.Atomicity.AtomicStep state = inr outer)
    (body_certificate : GenericRegions.Atomicity.analysis_certificate cost Γ fuel
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask outer)
        (GenericRegions.Atomicity.analysis_open outer)
        (GenericRegions.Atomicity.analysis_step_taken outer) true)
      body inner)
    (open_equal : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open outer)
    stack (pre post : assertion Γ F Δ) :
  Contracts.trusted_atomic Γ body ->
  certificate_semantically_valid (stack_in := stack) (stack_out := stack)
    (pre := pre) (post := post) body_certificate ->
  certificate_semantically_valid (stack_in := stack) (stack_out := stack)
    (pre := pre) (post := post)
    (GenericRegions.Atomicity.CertAtomic cost Γ fuel state
      (TAtomic node body) body outer inner eq_refl step body_certificate
      open_equal).
Proof.
  intros _ Hbody runtime formals binders atoms ambient Hfootprint.
  have Hbody_footprint : Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint body_certificate) ⊆ ambient.
  { etrans; last exact Hfootprint. apply Model.runtime_mask_mono.
    simpl. set_solver. }
  simpl.
  unfold Execution.Primitives.operation_wp. simpl.
  iIntros "Hpre".
  iApply (Execution.Operations.atomic_intro Γ runtime body
    (GenericRegions.Atomicity.analysis_mask state)
    (GenericRegions.Atomicity.analysis_mask inner)
    (Execution.region_wp body_certificate runtime ambient
      (global_world_context atoms ∗
       VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       World.access_stack_interp atoms ambient stack))%I).
  iApply (Hbody runtime formals binders atoms ambient Hbody_footprint).
  iExact "Hpre".
Qed.

Theorem aligned_certificate_valid {cost Γ F Δ fuel entry statement exit
    stack_in stack_out pre post}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    (derivation : @Certified.Rules.RavenHoareTriple Γ F Δ pre statement
      (GenericRegions.Atomicity.analysis_mask entry)
      (GenericRegions.Atomicity.analysis_mask exit) post) :
  GenericRegions.Atomicity.state_wf entry ->
  GenericRegions.Atomicity.lifo_certificate certificate stack_in stack_out ->
  Certified.certificate_hoare_aligned cost certificate derivation ->
  certificate_semantically_valid (stack_in := stack_in)
    (stack_out := stack_out) (pre := pre) (post := post) certificate.
Proof.
  intros Hwf Hlifo Haligned.
  revert stack_in stack_out Hwf Hlifo.
  induction Haligned; intros stack_in stack_out Hwf Hlifo.
  - simpl in Hlifo. subst stack_out.
    eapply leaf_statement_valid. intros runtime formals binders atoms ambient.
    intros Henvelope.
    have Hentry_envelope : Model.runtime_mask
        (GenericRegions.Atomicity.analysis_mask entry) ⊆ ambient.
    { etrans; last exact Henvelope. apply Model.runtime_mask_mono.
      apply GenericRegions.Atomicity.certificate_entry_subset_footprint. }
    have Hactive := Model.runtime_mask_subset_active ambient entry Hwf
      Hentry_envelope.
    have Hmask := proj1
      (GenericRegions.Atomicity.take_step_preserves_sets _ _ _ step).
    have Hactive_exit : Model.runtime_mask
        (GenericRegions.Atomicity.analysis_mask exit) ⊆
        Model.active_runtime_mask ambient entry.
    { rewrite Hmask. exact Hactive. }
    iIntros "[#Hglobal Hpre]".
    iApply ordinary_leaf_rule_valid;
      [exact view|exact derivation|exact Hactive_exit|].
    iFrame "Hglobal Hpre".
  - simpl in Hlifo. subst stack_out.
    unfold certificate_semantically_valid.
    intros runtime formals binders atoms ambient Henvelope.
    have Hfacts := step.
    apply GenericRegions.Atomicity.open_invariant_success in Hfacts as
      (Hfresh & _ & _ & _).
    have Hfootprint : invariant ∈
        GenericRegions.Atomicity.certificate_footprint
          (GenericRegions.Atomicity.CertUnfold cost Γ fuel entry
            (TUnfold node invariant arguments) invariant exit view step).
    { apply GenericRegions.Atomicity.certificate_entry_subset_footprint.
      exact available. }
    have Hnamespace := invariant_namespace_active_from_footprint
      (GenericRegions.Atomicity.CertUnfold cost Γ fuel entry
        (TUnfold node invariant arguments) invariant exit view step)
      ambient invariant Hfootprint Hfresh Henvelope.
    eapply invariant_unfold_node_valid; eauto.
  - simpl in Hlifo. destruct Hlifo as
      [(outer_open & -> & Hopen & Houter & Hopen_eq)|[-> Hfresh]].
    + unfold certificate_semantically_valid.
      intros runtime formals binders atoms ambient Henvelope.
      eapply invariant_fold_node_valid; eauto.
    + unfold certificate_semantically_valid.
      intros runtime formals binders atoms ambient Henvelope.
      have Hexit_member : invariant ∈
          GenericRegions.Atomicity.analysis_mask
            (GenericRegions.Atomicity.fold_invariant invariant entry).
      { rewrite Certified.fold_analysis_mask. set_solver. }
      have Hfootprint : invariant ∈
          GenericRegions.Atomicity.certificate_footprint
            (GenericRegions.Atomicity.CertFold cost Γ fuel entry
              (TFold node invariant arguments) invariant view).
      { apply GenericRegions.Atomicity.certificate_exit_subset_footprint.
        exact Hexit_member. }
      have Hnamespace := invariant_namespace_active_from_footprint
        (GenericRegions.Atomicity.CertFold cost Γ fuel entry
          (TFold node invariant arguments) invariant view)
        ambient invariant Hfootprint Hfresh Henvelope.
      eapply invariant_fresh_fold_node_valid; eauto.
  - simpl in Hlifo. destruct Hlifo as
      (stack_middle & Hfirst_lifo & Hsecond_lifo).
    eapply sequence_valid.
    + eapply IHHaligned1; eauto.
    + eapply IHHaligned2; eauto using
        GenericRegions.Atomicity.certificate_preserves_wf.
  - simpl in Hlifo. destruct Hlifo as [Hthen_lifo Helse_lifo].
    eapply (conditional_valid (node := node) (state := state)
      (store := store) (frame := frame) (condition := condition)
      (then_branch := then_branch) (else_branch := else_branch)
      (then_exit := then_exit) (else_exit := else_exit)
      then_certificate else_certificate open_equal atomic_equal).
    + eapply IHHaligned1; eauto.
    + eapply IHHaligned2; eauto.
  - simpl in Hlifo. destruct Hlifo as [Hbody_lifo ->].
    eapply (atomic_valid (state := state) (node := node) (body := body)
      (outer := outer) (inner := inner) step body_certificate open_equal);
      first exact trusted.
    eapply IHHaligned; eauto.
    unfold GenericRegions.Atomicity.state_wf in *; simpl.
    destruct (GenericRegions.Atomicity.take_step_preserves_sets
      GenericRegions.Atomicity.AtomicStep state outer step) as [Hmask Hopen].
    rewrite Hmask Hopen. exact Hwf.
  - eapply assertion_frame_valid. eapply IHHaligned; eauto.
  - eapply consequence_valid; [eapply IHHaligned; eauto|exact pre_entails|exact post_entails].
  - eapply exists_elim_valid. eapply IHHaligned; eauto.
  - eapply exists_preserve_valid. eapply IHHaligned; eauto.
Qed.

Theorem certified_region_valid {cost Γ F Δ fuel entry statement exit
    stack_in stack_out pre post}
    (certified : @Certified.CertifiedRavenHoareTriple cost Γ F Δ fuel
      stack_in stack_out pre statement entry exit post) :
  GenericRegions.Atomicity.state_wf entry -> semantically_valid certified.
Proof.
  intros Hwf. destruct certified as [certificate Hlifo derivation Haligned].
  eapply aligned_certificate_valid; eauto.
Qed.

End CertifiedRegionValidity.

End Make.
End TypedRuntimeCertified.
