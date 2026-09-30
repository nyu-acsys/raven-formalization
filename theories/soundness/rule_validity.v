From Coq Require Import List String ZArith Program.Equality Lia ClassicalEpsilon.
From stdpp Require Import countable gmap namespaces sets.

From iris.algebra Require Import auth gset.
From iris.base_logic Require Import fancy_updates.
From iris.base_logic.lib Require Import own invariants.

From raven Require Import runtime.erasure analysis.structured_certificates runtime.lang runtime.ghost_state.
From raven Require Import verification.expressions analysis.atomicity verification.assertions verification.ir soundness.interpretation soundness.entailment_validity soundness.runtime_model analysis.normalization_base analysis.normalization.

Import ListNotations.
Import weakestpre.
Open Scope list_scope.

(** Validity of the certified-region rules: the concrete runtime
    interpretation, its Iris transport laws, registered procedure layout, and
    the validity of structured certificates. *)
Module RuleValidity.
Import Runtime RuntimeErasure.
Module Hoare := Runtime.Validation.Hoare.
Module IR := Runtime.IR.
Module Translation := Runtime.Translation.
Module GenericRegions := Runtime.GenericRegions.
Module RuntimeModel := Runtime.RuntimeModel.
Module RuntimeLifting := Runtime.RuntimeLifting.
Module RuntimeGhost := Runtime.RuntimeGhost.
Module RuntimeLang := Runtime.RuntimeLang.
Import Core IR Core IR Translation.
Module RI := Hoare.ResourceHoare.
Module RegionExecution := ConcreteGenericRegionExecutionCore.
Module TermLeaf := TermSemanticLeafContracts.
Module CertifiedNormalization := NormalizationConditional.ConditionalNormalizationPrefix.
Module Certified := CertifiedNormalization.Certified.
Module ResourceInstances := CertifiedNormalization.RavenHoareRules.
Module Structured := StructuredCertificates.
Import Translation.Assertions.
(* [Translation.Assertions] also exports a module named [Model]; [CoreModel]
   names the concrete one unambiguously. *)
Module CoreModel := RegionExecution.Primitives.Model.

Section WithContracts.
Context {RAs : ra_base.RAConfig} {Logic : Assertion.LogicSignature}
  {Contracts : Hoare.ResourceHoare.ResourceContractEnv}
  {Coherence : Hoare.ProcedureContractCoherence}.

(** Call and spawn premises combine admission of the callee with the canonical
    contract instance computed from its actual arguments. *)
Definition resource_instantiated_pre F Δ (procedure : proc_id)
    (arguments : Translation.Assertions.expr_list F Δ (Assertion.procedure_args procedure))
    (contract : Translation.Resource.core_assertion F Δ) : Prop :=
  Hoare.ResourceHoare.procedure_verified procedure /\
  contract = @RI.instantiated_pre _ _ _ F Δ procedure arguments.

Definition resource_instantiated_post_value F Δ (procedure : proc_id)
    (arguments : Translation.Assertions.expr_list F (Assertion.procedure_return procedure :: Δ)
      (Assertion.procedure_args procedure))
    (result : Core.expr F
      (Assertion.procedure_return procedure :: Δ)
      (Assertion.procedure_return procedure))
    (contract : Translation.Resource.core_assertion F
      (Assertion.procedure_return procedure :: Δ)) : Prop :=
  Hoare.ResourceHoare.procedure_verified procedure /\
  contract = @RI.instantiated_post _ _ _ F Δ procedure arguments.


(** Selection and coherence are derived from the authoritative resource
    environment, so the declared contract and executable table cannot
    disagree. *)
Definition instantiated_pre_selects {F Δ} identity
    (arguments : Translation.Assertions.expr_list F Δ
      (Assertion.procedure_args identity))
    (contract : Translation.Resource.core_assertion F Δ)
    (Hinst : resource_instantiated_pre F Δ identity arguments contract) :
    { callee_variables : decl_context &
      { procedure : typed_procedure callee_variables identity |
        lookup_typed_procedure Hoare.coherent_procedures identity =
          Some (pack_typed_procedure procedure) } } :=
  Hoare.procedure_selects identity (proj1 Hinst).

Lemma instantiated_pre_coherent {callee_variables identity}
    (procedure : typed_procedure callee_variables identity) {F Δ}
    (arguments : Translation.Assertions.expr_list F Δ
      (Assertion.procedure_args identity))
    (contract : Translation.Resource.core_assertion F Δ) :
  lookup_typed_procedure Hoare.coherent_procedures identity =
    Some (pack_typed_procedure procedure) ->
  resource_instantiated_pre F Δ identity arguments contract ->
  contract = Hoare.procedure_pre_instantiation procedure arguments.
Proof.
  intros Hlookup [_ ->].
  unfold RI.instantiated_pre, Hoare.procedure_pre_instantiation.
  rewrite (Hoare.contract_pre_coherent _ _ procedure Hlookup).
  reflexivity.
Qed.

Lemma instantiated_post_value_coherent {callee_variables identity}
    (procedure : typed_procedure callee_variables identity) {F Δ}
    (arguments : Translation.Assertions.expr_list F
      (Assertion.procedure_return identity :: Δ)
      (Assertion.procedure_args identity))
    (result : Core.expr F
      (Assertion.procedure_return identity :: Δ)
      (Assertion.procedure_return identity))
    (contract : Translation.Resource.core_assertion F
      (Assertion.procedure_return identity :: Δ)) :
  lookup_typed_procedure Hoare.coherent_procedures identity =
    Some (pack_typed_procedure procedure) ->
  resource_instantiated_post_value F Δ identity arguments result contract ->
  contract = Translation.Resource.subst_formals_core
    (Translation.Assertions.expr_list_formal_subst arguments)
    (Translation.Resource.rename_bound_core
      Translation.Assertions.return_bound_renaming
      (procedure_postcondition _ _ procedure)).
Proof.
  intros Hlookup [_ ->].
  unfold RI.instantiated_post.
  rewrite (Hoare.contract_post_coherent _ _ procedure Hlookup).
  reflexivity.
Qed.

(** Resource-independent executable registration.  Initialization must inspect
    this data before it can construct [runtimeG], in particular to allocate
    exactly the finite family of invariant-token authorities. *)
Record certified_module_registration := CertifiedModuleRegistration {
  registered_invariants : gset inv_id;
  registered_runtime_procedure_body :
    packed_typed_procedure -> RuntimeLang.stack_id -> RuntimeLang.runtime_stmt;
  registered_runtime_procedure_layout :
    forall (packed : packed_typed_procedure),
    List.In packed (procedure_entries Hoare.coherent_procedures) ->
    match packed with
    | existT Γ (existT F procedure) =>
        procedure_wf procedure /\
        forall stack,
          @RuntimeErasure.runtime_stmt _ _ Γ
            (@RuntimeErasure.runtime_procedure_names _ _
              Γ F procedure) stack (procedure_body Γ F procedure) =
          registered_runtime_procedure_body packed stack
    end;
}.

(** ** The canonical registration

    A module determines its registration directly: the body stored for each
    procedure is its stack-parametric erasure, and the invariant tokens are
    those of the module's invariants. *)
Definition canonical_procedure_body (packed : packed_typed_procedure) :
    RuntimeLang.stack_id -> RuntimeLang.runtime_stmt :=
  match packed with
  | existT Γ (existT F procedure) =>
      fun stack => @RuntimeErasure.runtime_stmt _ _ Γ
        (@RuntimeErasure.runtime_procedure_names _ _ Γ F procedure) stack
        (procedure_body Γ F procedure)
  end.

Lemma canonical_procedure_layout packed :
  List.In packed (procedure_entries Hoare.coherent_procedures) ->
  match packed with
  | existT Γ (existT F procedure) =>
      procedure_wf procedure /\
      forall stack,
        @RuntimeErasure.runtime_stmt _ _ Γ
          (@RuntimeErasure.runtime_procedure_names _ _
            Γ F procedure) stack (procedure_body Γ F procedure) =
        canonical_procedure_body packed stack
  end.
Proof.
  intros Hin.
  pose proof (proj1 (List.Forall_forall _ _)
    (procedure_entries_wf Hoare.coherent_procedures) packed Hin) as Hwf.
  destruct packed as [Γ [F procedure]].
  split; [exact Hwf | reflexivity].
Qed.

Definition canonical_registration (invariants : gset inv_id) :
    certified_module_registration :=
  CertifiedModuleRegistration invariants canonical_procedure_body
    canonical_procedure_layout.

(** Pure association between the finite registration and the names allocated
    before [runtimeG] is assembled.  The default is deliberately outside the
    allocated range; it only totalizes the runtime [invTokenG] lookup. *)
Definition registered_invariant_enumeration
    (registration : certified_module_registration) : list inv_id :=
  elements (registered_invariants registration).

Definition registered_invtoken_map
    (registration : certified_module_registration) (names : list gname) :
    gmap RuntimeModel.inv_name gname :=
  list_to_map (zip
    (map invariant_name
      (registered_invariant_enumeration registration)) names).

Definition registered_invtoken_name
  (registration : certified_module_registration) (names : list gname) :
    RuntimeModel.inv_name -> gname := fun invariant_name =>
  default (fresh (list_to_set names : gset gname))
    (registered_invtoken_map registration names !! invariant_name).

Definition registered_invTokenG {Σ : gFunctors} `{!RuntimeModel.invTokenGpreS Σ}
    (registration : certified_module_registration) (names : list gname) :
    RuntimeModel.invTokenG Σ :=
  Runtime.initialized_invTokenG (registered_invtoken_name registration names).

Definition registered_runtime_procedure_entry
    (registration : certified_module_registration)
    (packed : packed_typed_procedure) : RuntimeLang.proc :=
  match packed with
  | existT Γ (existT F procedure) =>
      RuntimeLang.Proc
        (procedure_name (procedure_identity Γ F procedure))
        (@RuntimeErasure.runtime_procedure_arguments _ _
          Γ F procedure)
        (@RuntimeErasure.runtime_procedure_locals _ _
          Γ F procedure)
        (registered_runtime_procedure_body registration packed)
  end.

Definition registered_runtime_procedure_bindings
    (registration : certified_module_registration) :
    list (RuntimeLang.proc_name * RuntimeLang.proc) :=
  map (fun procedure =>
    (procedure_name (packed_procedure_id procedure),
      registered_runtime_procedure_entry registration procedure))
    (procedure_entries Hoare.coherent_procedures).

Definition registered_runtime_procedure_map
    (registration : certified_module_registration) :
    gmap RuntimeLang.proc_name RuntimeLang.proc :=
  list_to_map (registered_runtime_procedure_bindings registration).

Lemma registered_invtoken_map_lookup_nth
    (registration : certified_module_registration) (names : list gname)
    index invariant name :
  length names = length (registered_invariant_enumeration registration) ->
  registered_invariant_enumeration registration !! index = Some invariant ->
  names !! index = Some name ->
  registered_invtoken_map registration names !! invariant_name invariant =
    Some name.
Proof.
  intros Hlength Hinvariant Hname.
  apply elem_of_list_to_map_1.
  - rewrite fst_zip; last by rewrite length_fmap Hlength.
    apply NoDup_fmap_2_strong.
    + intros left right _ _ Hequal.
      apply invariant_name_injective. exact Hequal.
    + unfold registered_invariant_enumeration. apply NoDup_elements.
  - apply elem_of_list_lookup. exists index.
    rewrite lookup_zip_Some. split; last exact Hname.
    apply list_lookup_fmap_Some. exists invariant. split; done.
Qed.

Lemma registered_invtoken_name_nth
    (registration : certified_module_registration) (names : list gname)
    index invariant name :
  length names = length (registered_invariant_enumeration registration) ->
  registered_invariant_enumeration registration !! index = Some invariant ->
  names !! index = Some name ->
  registered_invtoken_name registration names
    (invariant_name invariant) = name.
Proof.
  intros Hlength Hinvariant Hname.
  unfold registered_invtoken_name.
  rewrite (registered_invtoken_map_lookup_nth registration names index
    invariant name Hlength Hinvariant Hname). done.
Qed.

Section RegisteredTokenAuthorities.
Context {Σ : gFunctors} `{!RuntimeModel.invTokenGpreS Σ}.

Lemma registered_invtoken_authorities
    (registration : certified_module_registration) (names : list gname) :
  length names = length (registered_invariant_enumeration registration) ->
  ([∗ list] name ∈ names,
    @own Σ (authR RuntimeModel.inv_argsUR) RuntimeModel.invtoken_pre_inG name
      (● (∅ : RuntimeModel.inv_argsUR))) ⊢
  ([∗ set] invariant ∈ registered_invariants registration,
    @own Σ (authR RuntimeModel.inv_argsUR) RuntimeModel.invtoken_pre_inG
      (registered_invtoken_name registration names
        (invariant_name invariant))
      (● (∅ : RuntimeModel.inv_argsUR))).
Proof.
  intros Hlength. iIntros "Hnames".
  iAssert ([∗ list] index ↦ invariant; name ∈
      registered_invariant_enumeration registration; names,
      @own Σ (authR RuntimeModel.inv_argsUR) RuntimeModel.invtoken_pre_inG name
        (● (∅ : RuntimeModel.inv_argsUR)))%I with "[Hnames]" as "Hpairs".
  { rewrite big_sepL2_const_sepL_r. iSplit; first by iPureIntro.
    iExact "Hnames". }
  rewrite big_sepS_elements.
  iAssert ([∗ list] index ↦ invariant; name ∈
      registered_invariant_enumeration registration; names,
      @own Σ (authR RuntimeModel.inv_argsUR) RuntimeModel.invtoken_pre_inG
        (registered_invtoken_name registration names
          (invariant_name invariant))
        (● (∅ : RuntimeModel.inv_argsUR)))%I with "[Hpairs]" as "Hassigned".
  { iApply (big_sepL2_impl with "Hpairs").
    iIntros "!>" (index invariant name Hinvariant Hname) "Htoken".
    rewrite (registered_invtoken_name_nth registration names index invariant
      name Hlength Hinvariant Hname). iExact "Htoken". }
  iEval (rewrite big_sepL2_const_sepL_l) in "Hassigned".
  iDestruct "Hassigned" as "[_ Htokens]". iExact "Htokens".
Qed.

End RegisteredTokenAuthorities.

Section WithRuntime.
Context {Σ : gFunctors} `{RG : !runtimeG Σ}.
Local Instance core_simpLangG : RuntimeLifting.simpLangG Σ := runtime_simpLangG.
Local Instance core_invTokenG : RuntimeModel.invTokenG Σ := runtime_invTokenG.
Local Instance core_heapG : RuntimeGhost.heapG Σ :=
  RuntimeLifting.simpLangG_gen_heapG.
Local Instance core_irisG : irisGS RuntimeLang.simp_lang Σ :=
  @RegionExecution.Primitives.Model.core_irisG _ _ Σ RG.
Local Existing Instance weakestpre.wp'.
Local Notation iProp := (bi_car (iPropI Σ)).

Definition semantic_data : Translation.semantic_config_data (iPropI Σ) :=
  @RegionExecution.Primitives.semantic_data _ _ Σ RG.

Lemma term_interp_assertion_timeless
    (predicates : Translation.TermSemantics.predicate_semantics)
    (Hpredicates : forall predicate values,
      Timeless (predicates predicate values))
    {Γ F Δ} (runtime : Translation.data_stack_context semantic_data Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (formula : Translation.Assertions.assertion Γ F Δ) :
  Timeless (Translation.TermSemantics.interp_assertion semantic_data predicates
    runtime formals binders valuation formula).
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

Local Notation predicate_semantics :=
  (Translation.TermSemantics.predicate_semantics (PROP := iPropI Σ)).

(** ** Predicate semantics

    A module's predicates denote the least timeless solution of their
    unfolding equations: the meet of all timeless prefixed points of the
    functional that interprets the predicate bodies (Knaster--Tarski).  The
    functional is monotone because predicate occurrences in core assertions
    are positive, and it preserves timelessness; hence the meet is itself a
    timeless fixpoint. *)
Definition predicate_functional (valuation : symbol_valuation)
    (predicates : predicate_semantics) :
    predicate_semantics :=
  fun predicate values =>
    Translation.TermSemantics.interp_core semantic_data predicates
      (formal_env_of_values values) empty_binder_env valuation
      (Hoare.ResourceHoare.predicate_body predicate).

Definition timeless_predicate_semantics : Type :=
  { predicates : predicate_semantics |
    forall predicate values, Timeless (predicates predicate values) }.

Definition predicate_fixpoint (valuation : symbol_valuation) :
    predicate_semantics :=
  fun predicate values =>
    (∀ Φ : timeless_predicate_semantics,
      □ (∀ predicate' values',
          predicate_functional valuation (proj1_sig Φ) predicate' values' -∗
          proj1_sig Φ predicate' values') -∗
      proj1_sig Φ predicate values)%I.

Lemma interp_core_predicates_mono {F Δ}
    (left_predicates right_predicates : predicate_semantics)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (formula : Translation.Resource.core_assertion F Δ) :
  □ (∀ predicate values,
      left_predicates predicate values -∗ right_predicates predicate values) ⊢
  Translation.TermSemantics.interp_core semantic_data left_predicates
      formals binders valuation formula -∗
  Translation.TermSemantics.interp_core semantic_data right_predicates
      formals binders valuation formula.
Proof.
  rewrite -!(Translation.TermSemantics.interp_core_to_assertion semantic_data
    _ (Translation.data_empty_stack_context semantic_data)).
  apply Translation.TermSemantics.interp_assertion_mono.
Qed.

Lemma interp_core_predicates_timeless {F Δ}
    (predicates : predicate_semantics)
    (Hpredicates : forall predicate values,
      Timeless (predicates predicate values))
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (formula : Translation.Resource.core_assertion F Δ) :
  Timeless (Translation.TermSemantics.interp_core semantic_data predicates
    formals binders valuation formula).
Proof.
  rewrite -(Translation.TermSemantics.interp_core_to_assertion semantic_data
    _ (Translation.data_empty_stack_context semantic_data)).
  apply term_interp_assertion_timeless, Hpredicates.
Qed.

Lemma predicate_functional_mono valuation
    (left_predicates right_predicates : predicate_semantics) :
  □ (∀ predicate values,
      left_predicates predicate values -∗ right_predicates predicate values) ⊢
  ∀ predicate values,
    predicate_functional valuation left_predicates predicate values -∗
    predicate_functional valuation right_predicates predicate values.
Proof.
  iIntros "#Hmono" (predicate values). unfold predicate_functional.
  iApply (interp_core_predicates_mono with "Hmono").
Qed.

Lemma predicate_fixpoint_timeless valuation predicate values :
  Timeless (predicate_fixpoint valuation predicate values).
Proof.
  unfold predicate_fixpoint.
  apply bi.forall_timeless. intros [Φ HΦ].
  apply bi.wand_timeless. apply HΦ.
Qed.

Lemma predicate_fixpoint_fold valuation predicate values :
  predicate_functional valuation (predicate_fixpoint valuation) predicate values ⊢
  predicate_fixpoint valuation predicate values.
Proof.
  iIntros "Hbody" (Φ) "#Hprefixed".
  iApply "Hprefixed".
  iApply (predicate_functional_mono with "[] Hbody").
  iIntros "!>" (predicate' values') "Hfixpoint".
  iApply ("Hfixpoint" $! Φ with "Hprefixed").
Qed.

Lemma predicate_fixpoint_unfold valuation predicate values :
  predicate_fixpoint valuation predicate values ⊢
  predicate_functional valuation (predicate_fixpoint valuation) predicate values.
Proof.
  iIntros "Hfixpoint".
  set (Φ := exist (fun predicates : predicate_semantics =>
      forall predicate values, Timeless (predicates predicate values))
    (predicate_functional valuation (predicate_fixpoint valuation))
    (fun predicate values => interp_core_predicates_timeless _
      (predicate_fixpoint_timeless valuation) _ _ _ _)).
  iApply ("Hfixpoint" $! Φ). simpl.
  iIntros "!>" (predicate' values') "Hbody".
  iApply (predicate_functional_mono with "[] Hbody").
  iIntros "!>" (predicate'' values'') "Hbody".
  iApply (predicate_fixpoint_fold with "Hbody").
Qed.

Lemma predicate_fixpoint_eq valuation predicate values :
  predicate_fixpoint valuation predicate values ⊣⊢
  predicate_functional valuation (predicate_fixpoint valuation) predicate values.
Proof.
  iSplit; [iApply predicate_fixpoint_unfold | iApply predicate_fixpoint_fold].
Qed.

Lemma constant_symbols_agree_sym left_valuation right_valuation :
  constant_symbols_agree left_valuation right_valuation ->
  constant_symbols_agree right_valuation left_valuation.
Proof.
  intros Hagree t symbolic. specialize (Hagree t symbolic).
  destruct symbolic; [symmetry |]; exact Hagree.
Qed.

Lemma predicate_functional_stable left_valuation right_valuation
    (predicates : predicate_semantics) predicate values :
  constant_symbols_agree left_valuation right_valuation ->
  predicate_functional left_valuation predicates predicate values ≡
  predicate_functional right_valuation predicates predicate values.
Proof.
  intros Hagree. unfold predicate_functional.
  apply Translation.TermSemantics.interp_core_constant_symbols; [done | exact Hagree |].
  apply Hoare.ResourceHoare.predicate_body_entry_free.
Qed.

Lemma predicate_fixpoint_stable_entails left_valuation right_valuation predicate values :
  constant_symbols_agree left_valuation right_valuation ->
  predicate_fixpoint left_valuation predicate values ⊢
  predicate_fixpoint right_valuation predicate values.
Proof.
  iIntros (Hagree) "Hfixpoint".
  set (Φ := exist (fun predicates : predicate_semantics =>
      forall predicate values, Timeless (predicates predicate values))
    (predicate_fixpoint right_valuation) (predicate_fixpoint_timeless right_valuation)).
  iApply ("Hfixpoint" $! Φ). simpl.
  iIntros "!>" (predicate' values') "Hbody".
  iApply predicate_fixpoint_fold.
  by rewrite (predicate_functional_stable left_valuation right_valuation).
Qed.

(** The leaf contracts of the module: its predicates, interpreted by their
    least timeless fixpoint. *)
Definition fixpoint_leaf : @TermLeaf.semantic_leaf_contracts_data _ _ _
    (iPropI Σ) semantic_data.
Proof.
  refine (@TermLeaf.SemanticLeafContractsData _ _ _ (iPropI Σ) semantic_data
    predicate_fixpoint predicate_fixpoint_timeless _ _).
  - intros left_valuation right_valuation Hagree predicate values.
    iSplit; iApply predicate_fixpoint_stable_entails;
      [exact Hagree | exact (constant_symbols_agree_sym _ _ Hagree)].
  - intros F Δ formals binders valuation predicate arguments.
    destruct (interp_expr_list_total formals binders valuation arguments)
      as [values Harguments].
    have Hactuals := interp_expr_list_formal_subst_of_values arguments values
      formals binders valuation Harguments.
    unfold RI.instantiated_predicate.
    rewrite (Translation.TermSemantics.interp_subst_formals_core semantic_data
      (predicate_fixpoint valuation) (expr_list_formal_subst arguments)
      (formal_env_of_values values) formals binders valuation Hactuals).
    rewrite (Translation.TermSemantics.interp_weaken_core_to semantic_data).
    cbn [Translation.TermSemantics.interp_core].
    change (Translation.TermSemantics.interp_core semantic_data
      (predicate_fixpoint valuation) (formal_env_of_values values) empty_binder_env
      valuation (Hoare.ResourceHoare.predicate_body predicate)) with
      (predicate_functional valuation (predicate_fixpoint valuation) predicate values).
    rewrite -predicate_fixpoint_eq.
    iSplit.
    + iIntros "H". iExists values. iFrame. done.
    + iIntros "H". iDestruct "H" as (values') "[%Hvalues' H]".
      rewrite Harguments in Hvalues'. injection Hvalues' as <-. iExact "H".
Defined.

(** The leaf contracts are always the module's predicate fixpoint. *)
Local Notation Leaf := fixpoint_leaf.
Context (Hruntime_ghost_namespace :
  @runtime_ghost_namespace _ _ Σ RG = ghost_heap_namespace).

Definition term_predicates (valuation : symbol_valuation) :=
  @TermLeaf.term_predicates _ _ _ (iPropI Σ) semantic_data Leaf
    valuation.

(** Static zipper payload for the later structured-refinement proof.  It is
    deliberately independent of the runtime model, so the certificates and
    resource derivations do not depend on the configuration or on Σ. *)
Inductive operational_suffix Γ :
    GenericRegions.Atomicity.analysis_state ->
    GenericRegions.Atomicity.analysis_state -> Type :=
| OperationalDone state : operational_suffix Γ state state
| OperationalCons entry statement middle exit
    (certificate : GenericRegions.Atomicity.analysis_certificate
      Γ entry statement middle)
    (suffix : operational_suffix Γ middle exit) :
    operational_suffix Γ entry exit.

Arguments OperationalDone {_} _.
Arguments OperationalCons {_ _ _ _ _} _ _.

(** The runtime meaning of an erased statement: run it, then change masks.
    Erasure is total, so there is no case split here; a proof-only statement
    erases to the terminal statement, whose [wp] is just the mask change
    ([runtime_masked_wp_noop]). *)
Definition runtime_masked_wp (entry_mask exit_mask : coPset)
    (physical : RuntimeLang.runtime_stmt) (post : iProp) : iProp :=
  @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG entry_mask physical
    (fun result =>
      (⌜result = RuntimeLang.LitUnit⌝ ∗
       |={entry_mask, exit_mask}=> post)%I).

Definition translated_runtime_wp {Γ} (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (ambient : coPset) (entry exit : GenericRegions.Atomicity.analysis_state)
    (statement : stmt Γ) (post : iProp) : iProp :=
  runtime_masked_wp
    (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
    (RegionExecution.Primitives.Model.active_runtime_mask ambient exit)
    (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) statement)
    post.

Lemma term_translated_runtime_wp_runtime_stmt_ext {Γ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) ambient entry exit
    (left right : stmt Γ) post :
  @RuntimeErasure.runtime_stmt _ _ Γ
    (RegionExecution.Primitives.Model.runtime_names Γ runtime)
    (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) left =
  @RuntimeErasure.runtime_stmt _ _ Γ
    (RegionExecution.Primitives.Model.runtime_names Γ runtime)
    (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) right ->
  translated_runtime_wp runtime ambient entry exit left post ⊣⊢
    translated_runtime_wp runtime ambient entry exit right post.
Proof.
  intros Hequal. unfold translated_runtime_wp. now rewrite Hequal.
Qed.

Lemma runtime_masked_wp_noop entry_mask exit_mask (post : iProp) :
  runtime_masked_wp entry_mask exit_mask
    RuntimeErasure.runtime_noop post ⊣⊢
  (|={entry_mask, exit_mask}=> post)%I.
Proof.
  unfold runtime_masked_wp, RegionExecution.Primitives.Model.runtime_wp,
    RuntimeErasure.runtime_noop.
  change (RuntimeLang.RTVal RuntimeLang.LitUnit) with
    (@of_val RuntimeLang.simp_lang RuntimeLang.LitUnit).
  rewrite wp_value_fupd'.
  iSplit.
  - iIntros ">[_ H]". iExact "H".
  - iIntros "H". iModIntro. iSplit; first done. iExact "H".
Qed.

Lemma translated_runtime_wp_erased {Γ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) ambient entry exit
    (statement : stmt Γ) post :
  @RuntimeErasure.runtime_stmt _ _ Γ
    (RegionExecution.Primitives.Model.runtime_names Γ runtime)
    (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) statement =
    RuntimeErasure.runtime_noop ->
  translated_runtime_wp runtime ambient entry exit statement post ⊣⊢
  (|={RegionExecution.Primitives.Model.active_runtime_mask ambient entry,
      RegionExecution.Primitives.Model.active_runtime_mask ambient exit}=> post)%I.
Proof.
  intros Herased. unfold translated_runtime_wp. rewrite Herased.
  apply runtime_masked_wp_noop.
Qed.

Lemma runtime_masked_wp_noop_eq entry_mask exit_mask physical (post : iProp) :
  physical = RuntimeErasure.runtime_noop ->
  runtime_masked_wp entry_mask exit_mask physical post ⊣⊢
  (|={entry_mask, exit_mask}=> post)%I.
Proof. intros ->. apply runtime_masked_wp_noop. Qed.

(** The terminal statement takes no step, so it is trivially atomic. *)
Global Instance runtime_value_atomic value :
  @Atomic RuntimeLang.simp_lang WeaklyAtomic (RuntimeLang.RTVal value).
Proof. apply RuntimeLang.atomic_val. Qed.

Lemma runtime_noop_atomic :
  @Atomic RuntimeLang.simp_lang WeaklyAtomic
    RuntimeErasure.runtime_noop.
Proof. apply _. Qed.

Lemma runtime_wp_atomic_mask_change
    (physical : RuntimeLang.runtime_stmt) E1 E2
    (Phi : RuntimeLang.val -> iProp)
    `{!@Atomic RuntimeLang.simp_lang WeaklyAtomic physical} :
  (|={E1,E2}=> @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG E2 physical
      (fun value => |={E2,E1}=> Phi value)) ⊢
    @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG E1 physical Phi.
Proof.
  unfold RegionExecution.Primitives.Model.runtime_wp. iIntros "Hwp". iApply wp_atomic.
  iExact "Hwp".
Qed.

Lemma runtime_wp_sequence
    (first second : RuntimeLang.runtime_stmt) E
    (Phi : RuntimeLang.val -> iProp) :
  @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG E first
      (fun result =>
        ⌜result = RuntimeLang.LitUnit⌝ ∗ @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG E second Phi) ⊢
    @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG E (RuntimeLang.RTSeq first second) Phi.
Proof.
  unfold RegionExecution.Primitives.Model.runtime_wp. iIntros "Hfirst".
  iApply RuntimeLifting.wp_seq_wp. iExact "Hfirst".
Qed.

Lemma translated_runtime_wp_as_masked {Γ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) ambient entry exit statement post :
  translated_runtime_wp runtime ambient entry exit statement post ⊣⊢
    runtime_masked_wp
      (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
      (RegionExecution.Primitives.Model.active_runtime_mask ambient exit)
      (@RuntimeErasure.runtime_stmt _ _ Γ (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) statement) post.
Proof. reflexivity. Qed.

Lemma runtime_masked_wp_mono entry_mask exit_mask physical (P Q : iProp) :
  (P ⊢ Q) ->
  runtime_masked_wp entry_mask exit_mask physical P ⊢
    runtime_masked_wp entry_mask exit_mask physical Q.
Proof.
  intros HPQ. unfold runtime_masked_wp.
  iIntros "Hwp". iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iMod "Hpost". iModIntro. iApply HPQ. iExact "Hpost".
Qed.

Lemma runtime_masked_wp_frame entry_mask exit_mask physical (post frame : iProp) :
  runtime_masked_wp entry_mask exit_mask physical post ∗ frame ⊢
    runtime_masked_wp entry_mask exit_mask physical (post ∗ frame).
Proof.
  unfold runtime_masked_wp, RegionExecution.Primitives.Model.runtime_wp.
  iIntros "[Hwp Hframe]".
  iPoseProof (@wp_frame_r HasLc RuntimeLang.simp_lang Σ core_irisG
    NotStuck entry_mask _
    (fun result =>
      (⌜result = RuntimeLang.LitUnit⌝ ∗ |={entry_mask,exit_mask}=> post)%I)
    frame with "[$Hwp $Hframe]") as "Hwp".
  iApply (wp_mono with "Hwp").
  iIntros (result) "[[%Hresult Hpost] Hframe]". iSplit; first done.
  iMod "Hpost". iModIntro. iFrame.
Qed.

Lemma runtime_masked_wp_atomic_mask_change outer inner physical (post : iProp) :
  @Atomic RuntimeLang.simp_lang WeaklyAtomic physical ->
  (|={outer,inner}=>
    runtime_masked_wp inner inner physical (|={inner,outer}=> post)) ⊢
  runtime_masked_wp outer outer physical post.
Proof.
  intros Hstatement_atomic. unfold runtime_masked_wp.
  iIntros "Hbracket". iApply runtime_wp_atomic_mask_change.
  iMod "Hbracket". iModIntro.
  iApply (wp_mono with "Hbracket").
  iIntros (result) "[%Hresult Hpost]".
  iMod "Hpost". iMod "Hpost". iModIntro.
  iSplit; first done. iExact "Hpost".
Qed.

Lemma runtime_masked_wp_fupd mask physical (post : iProp) :
  (|={mask}=> runtime_masked_wp mask mask physical (|={mask}=> post)) ⊢
  runtime_masked_wp mask mask physical post.
Proof.
  unfold runtime_masked_wp, RegionExecution.Primitives.Model.runtime_wp.
  iIntros "Hwp". iApply fupd_wp. iMod "Hwp". iModIntro.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iMod "Hpost". iExact "Hpost".
Qed.

(** Sequencing through the smart constructor: a terminal operand is dropped
    and contributes only its (identity) mask change. *)
Lemma runtime_masked_wp_seq mask exit_mask first second (post : iProp) :
  runtime_masked_wp mask mask first
      (runtime_masked_wp mask exit_mask second post) ⊢
    runtime_masked_wp mask exit_mask
      (RuntimeErasure.runtime_seq first second) post.
Proof.
  apply (RuntimeErasure.runtime_seq_ind
    (fun combined => runtime_masked_wp mask mask first
      (runtime_masked_wp mask exit_mask second post) ⊢
      runtime_masked_wp mask exit_mask combined post)).
  - intros ->. rewrite runtime_masked_wp_noop.
    unfold runtime_masked_wp. iIntros "Hsecond". iMod "Hsecond".
    iExact "Hsecond".
  - intros ->. etrans.
    { apply runtime_masked_wp_mono. apply bi.equiv_entails_1_1.
      apply runtime_masked_wp_noop. }
    unfold runtime_masked_wp. iIntros "Hfirst".
    iApply (wp_mono with "Hfirst").
    iIntros (result) "[%Hresult Hpost]". iSplit; first done.
    iMod "Hpost". iExact "Hpost".
  - intros _ _. unfold runtime_masked_wp. iIntros "Hfirst".
    iApply runtime_wp_sequence.
    iApply (wp_mono with "Hfirst").
    iIntros (result) "[%Hresult Hsecond]".
    iSplit; first done.
    iMod "Hsecond". iExact "Hsecond".
Qed.

Lemma translated_runtime_wp_mono {Γ} (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    ambient entry exit statement (P Q : iProp) :
  (P ⊢ Q) ->
  translated_runtime_wp runtime ambient entry exit statement P ⊢
    translated_runtime_wp runtime ambient entry exit statement Q.
Proof. apply runtime_masked_wp_mono. Qed.

Lemma translated_runtime_wp_frame {Γ} (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    ambient entry exit statement (post frame : iProp) :
  translated_runtime_wp runtime ambient entry exit statement post ∗ frame ⊢
    translated_runtime_wp runtime ambient entry exit statement (post ∗ frame).
Proof. apply runtime_masked_wp_frame. Qed.

Definition term_semantic_runtime {Γ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) :
    Translation.data_stack_context semantic_data Γ := runtime.

Lemma term_stack_own_update {Γ F Δ t}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) {init} (target : lvar (keep_write init) Γ t)
    (value : tval t) :
  Translation.data_stack_own semantic_data (term_semantic_runtime runtime)
      (interp_store formals (binder_cons value binders) valuation
        (IR.update_store_with_bound store target)) ⊣⊢
    RuntimeGhost.stack_frame_own
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      (RuntimeLang.StackFrame
        (<[@RuntimeErasure.runtime_variable Γ _ t
              (RegionExecution.Primitives.Model.runtime_names Γ runtime) target :=
            @RuntimeErasure.tval_to_val _ t value]>
          (RuntimeLang.locals (RuntimeLang.StackFrame
            (@RegionExecution.Primitives.Model.concrete_locals _ Γ
              (RegionExecution.Primitives.Model.runtime_names Γ runtime)
              (interp_store formals binders valuation store)))))).
Proof.
  apply RegionExecution.Primitives.semantic_stack_own_update.
Qed.

(** Interpretation of an assertion at a concrete runtime stack context. *)
Definition term_interp_assertion {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (formula : Translation.Assertions.assertion Γ F Δ) : iProp :=
  Translation.TermSemantics.interp_assertion semantic_data
    (term_predicates valuation)
    (term_semantic_runtime runtime) formals binders valuation formula.

(** *** Interpretation over resource telescopes

    The same [semantic_data] identity, read through the resource
    representation.  Nothing below routes a rule's validity through
    [prenex_to_assertion]: the slice is proved against the runtime
    primitives directly. *)
Definition term_interp_core {F Δ}
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (formula : Translation.Resource.core_assertion F Δ) : iProp :=
  Translation.TermSemantics.interp_core semantic_data
    (term_predicates valuation) formals binders valuation formula.

Lemma term_interp_core_constant_symbols {F Δ}
    (formals : formal_env F) (binders : binder_env Δ)
    (left_valuation right_valuation : symbol_valuation)
    (formula : Translation.Resource.core_assertion F Δ) :
  constant_symbols_agree left_valuation right_valuation ->
  Translation.Resource.core_entry_free formula ->
  term_interp_core formals binders left_valuation formula ≡
    term_interp_core formals binders right_valuation formula.
Proof.
  intros Hagree Hfree. unfold term_interp_core.
  eapply Translation.TermSemantics.interp_core_constant_symbols;
    [apply (@TermLeaf.term_predicates_stable _ _ _ (iPropI Σ) semantic_data Leaf);
      exact Hagree
    | exact Hagree | exact Hfree].
Qed.

Lemma term_interp_core_as_assertion {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (formula : Translation.Resource.core_assertion F Δ) :
  term_interp_core formals binders valuation formula ⊣⊢
  term_interp_assertion runtime formals binders valuation
    (@Translation.Resource.core_to_assertion _ _ Γ F Δ formula).
Proof.
  symmetry.
  apply (Translation.TermSemantics.interp_core_to_assertion semantic_data).
Qed.

Definition term_interp_resource_prenex {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (prenex : Translation.Resource.resource_prenex Γ F Δ) : iProp :=
  Translation.TermSemantics.interp_resource_prenex semantic_data
    (term_predicates valuation)
    (term_semantic_runtime runtime) formals binders valuation prenex.

(** A telescope leaf is a stack assertion separated from a core assertion,
    by construction rather than by a theorem about where [AStack] sits. *)
Lemma term_interp_rstate {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ)
    (body : Translation.Resource.core_assertion F Δ) :
  term_interp_resource_prenex runtime formals binders valuation
      (Translation.Resource.RState store body) =
    (Translation.data_stack_own semantic_data (term_semantic_runtime runtime)
       (interp_store formals binders valuation store) ∗
     term_interp_core formals binders valuation body)%I.
Proof. reflexivity. Qed.

Lemma term_interp_resource_exists {Γ F Δ t}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (rest : Translation.Resource.resource_prenex Γ F (t :: Δ)) :
  term_interp_resource_prenex runtime formals binders valuation
      (Translation.Resource.ResourceExists t rest) =
    (∃ value : tval t,
      term_interp_resource_prenex runtime formals (binder_cons value binders)
        valuation rest)%I.
Proof. reflexivity. Qed.

(** Resource interpretation enriched with the *semantic* value of a vector
    of program expressions.  The remembered value follows the witnesses
    actually chosen by the telescope; no equality between symbolic witness
    expressions is required. *)
Fixpoint term_interp_resource_prenex_at_arguments {Γ F Δ ts}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (arguments : gexpr_list Γ ts) (values : tval_list ts)
    (prenex : Translation.Resource.resource_prenex Γ F Δ) : iProp :=
  (match prenex in Translation.Resource.resource_prenex _ _ Δ0
    return binder_env Δ0 -> iProp with
  | Translation.Resource.ResourceBody state =>
      fun binders0 =>
        (term_interp_resource_prenex runtime formals binders0 valuation
            (Translation.Resource.ResourceBody state) ∗
         ⌜interp_expr_list formals binders0 valuation
            (IR.symbolize_expr_list
              (Translation.Resource.resource_stack state) arguments) =
          Some values⌝)%I
  | Translation.Resource.ResourceExists t rest =>
      fun binders0 =>
        (∃ value : tval t,
          term_interp_resource_prenex_at_arguments runtime formals
            (binder_cons value binders0) valuation arguments values rest)%I
  end) binders.

Lemma term_interp_resource_prenex_at_arguments_rename {Γ F Δ ts}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (valuation : symbol_valuation)
    (arguments : gexpr_list Γ ts) (values : tval_list ts)
    (prenex : Translation.Resource.resource_prenex Γ F Δ) :
  forall Δ' (renaming : bound_renaming Δ Δ')
    (source_binders : binder_env Δ) (target_binders : binder_env Δ'),
  (forall t (variable : bvar Δ t),
    target_binders t (renaming t variable) = source_binders t variable) ->
  term_interp_resource_prenex_at_arguments runtime formals target_binders
      valuation arguments values
      (Translation.Resource.rename_resource_prenex prenex _ renaming) ≡
    term_interp_resource_prenex_at_arguments runtime formals source_binders
      valuation arguments values prenex.
Proof.
  induction prenex; intros Δ' renaming source_binders target_binders
    Hrenaming.
  - cbn [term_interp_resource_prenex_at_arguments
      Translation.Resource.rename_resource_prenex].
    apply bi.sep_proper.
    + unfold term_interp_resource_prenex.
      apply (Translation.TermSemantics.interp_rename_resource_prenex
        semantic_data (term_predicates valuation)
        (Translation.Resource.ResourceBody state) Δ' renaming formals
        source_binders target_binders valuation (term_semantic_runtime runtime)
        Hrenaming).
    + apply bi.pure_proper. rewrite IR.symbolize_expr_list_rename_bound_store.
      rewrite (interp_rename_bound_expr_list renaming formals source_binders
        target_binders valuation Hrenaming). reflexivity.
  - cbn [term_interp_resource_prenex_at_arguments
      Translation.Resource.rename_resource_prenex].
    apply bi.exist_proper. intros value.
    apply IHprenex. apply binder_cons_lift_bound_renaming. exact Hrenaming.
Qed.

Lemma term_interp_resource_prenex_at_arguments_weaken {Γ F Δ ts u}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (arguments : gexpr_list Γ ts) (values : tval_list ts)
    (head : tval u)
    (prenex : Translation.Resource.resource_prenex Γ F Δ) :
  term_interp_resource_prenex_at_arguments runtime formals
      (binder_cons head binders) valuation arguments values
      (Translation.Resource.weaken_resource_prenex prenex) ≡
    term_interp_resource_prenex_at_arguments runtime formals binders valuation
      arguments values prenex.
Proof.
  apply term_interp_resource_prenex_at_arguments_rename.
  intros t variable. apply binder_cons_weaken.
Qed.

Lemma track_values_iff {F Δ t ts} (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (value tracked : Core.expr F Δ t) (rest : expr_list F Δ ts)
    (tracked_value : tval t) (values : tval_list ts) :
  interp_expr formals binders valuation value = Some tracked_value ->
  (interp_expr formals binders valuation (EBinOp (BEq t) value tracked) =
      Some (VBool true) /\
    interp_expr_list formals binders valuation rest = Some values) <->
  interp_expr_list formals binders valuation (ExprCons tracked rest) =
    Some (TVCons tracked_value values).
Proof.
  intros Hvalue. cbn [interp_expr interp_expr_list]. rewrite Hvalue.
  destruct (interp_expr_total formals binders valuation tracked)
    as [actual Hactual].
  rewrite Hactual. cbn [interp_binop].
  destruct (interp_expr_list formals binders valuation rest) as [actuals|].
  - split.
    + intros [Hequal Hrest]. injection Hequal as Hequal.
      apply tval_eqb_eq in Hequal. subst. injection Hrest as ->. reflexivity.
    + intros Hcons. inversion Hcons as [[Hhead Htail]].
      repeat match goal with
      | H : existT _ _ = existT _ _ |- _ =>
          apply Eqdep.EqdepTheory.inj_pair2 in H
      end. subst.
      rewrite (proj2 (tval_eqb_eq t tracked_value tracked_value) eq_refl).
      split; reflexivity.
  - split; [intros [_ Hrest]; discriminate | discriminate].
Qed.

(** Tracking an expression in the telescope is tracking it in the argument
    vector. *)
Lemma term_interp_resource_prenex_at_arguments_track {Γ F Δ ts t}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (valuation : symbol_valuation)
    (arguments : gexpr_list Γ ts) (values : tval_list ts)
    (expression : gexpr Γ t)
    (prenex : Translation.Resource.resource_prenex Γ F Δ) :
  forall (binders : binder_env Δ) (value : Core.expr F Δ t)
    (tracked_value : tval t),
  interp_expr formals binders valuation value = Some tracked_value ->
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      arguments values
      (Hoare.ResourceHoare.track_prenex expression prenex value) ⊣⊢
    term_interp_resource_prenex_at_arguments runtime formals binders valuation
      (PECons expression arguments) (TVCons tracked_value values) prenex.
Proof.
  induction prenex as [Δ [stack body] | Δ u rest IH];
    intros binders value tracked_value Hvalue.
  - cbn [Hoare.ResourceHoare.track_prenex term_interp_resource_prenex_at_arguments
      Translation.Resource.resource_stack Translation.Resource.resource_body
      IR.symbolize_expr_list].
    change (Translation.Resource.ResourceBody
      (Translation.Resource.ResourceState ?store ?core)) with
      (Translation.Resource.RState store core).
    rewrite !term_interp_rstate.
    unfold term_interp_core. cbn [Translation.TermSemantics.interp_core].
    pose proof (track_values_iff formals binders valuation value
      (IR.symbolize_expr stack expression)
      (IR.symbolize_expr_list stack arguments) tracked_value values Hvalue)
      as Hiff.
    iSplit.
    + iIntros "[[Hstack [Hbody %Hequal]] %Hrest]". iFrame. iPureIntro.
      apply Hiff. split; assumption.
    + iIntros "[[Hstack Hbody] %Hcons]".
      apply Hiff in Hcons as [Hequal Hrest]. iFrame. iPureIntro.
      split; assumption.
  - cbn [Hoare.ResourceHoare.track_prenex term_interp_resource_prenex_at_arguments].
    apply bi.exist_proper. intros head. apply IH.
    rewrite interp_weaken_expr. exact Hvalue.
Qed.

Lemma term_interp_resource_prenex_at_arguments_entails {Γ F Δ ts}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (arguments : gexpr_list Γ ts) (values : tval_list ts)
    (left right : Translation.Resource.resource_prenex Γ F Δ) :
  Hoare.ResourceHoare.resource_prenex_entails left right ->
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      arguments values left ⊢
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      arguments values right.
Proof.
  intro Hentails. induction Hentails;
    intros; cbn [term_interp_resource_prenex_at_arguments].
  - destruct H as [Hstack Hcore].
    destruct left as [lstore lbody]; destruct right as [rstore rbody].
    cbn [Translation.Resource.resource_stack Translation.Resource.resource_body]
      in *. subst rstore.
    rewrite !term_interp_rstate.
    iIntros "[[Hstack Hbody] %Hargs]".
    iSplitL "Hstack Hbody".
    + iSplitL "Hstack"; [iExact "Hstack"|].
      iApply (Validation.TermSemantics.core_entails_valid semantic_data
        (term_predicates valuation) lbody rbody Hcore formals binders valuation).
      iExact "Hbody".
    + iPureIntro. exact Hargs.
  - iIntros "H". iDestruct "H" as (value) "H".
    iExists value. iApply IHHentails. iExact "H".
  - destruct state as [store body].
    cbn [Translation.Resource.subst_bound_resource
      Translation.Resource.resource_stack Translation.Resource.resource_body]
      in *.
    rewrite !term_interp_rstate.
    iIntros "[[Hstack Hbody] %Hargs]".
    iExists (interp_ref formals binders valuation witness).
    rewrite term_interp_rstate.
    rewrite (Translation.interp_subst_bound_store
      (Translation.Resource.head_bound_ref_subst witness) formals _ binders
      valuation (Translation.interp_head_bound_ref_subst witness formals
        binders valuation) store).
    rewrite <- (Translation.TermSemantics.interp_subst_bound_core semantic_data
      (term_predicates valuation)
      (Translation.Resource.bound_subst_of_refs
        (Translation.Resource.head_bound_ref_subst witness))
      formals _ binders valuation
        (fun u variable => f_equal Some
          (Translation.interp_head_bound_ref_subst witness formals binders
            valuation u variable)) body).
    iSplit.
    + iSplitL "Hstack"; [iExact "Hstack" | iExact "Hbody"].
    + iPureIntro.
      rewrite (IR.symbolize_expr_list_subst_bound_store
        (Translation.Resource.head_bound_ref_subst witness) store arguments)
        in Hargs.
      rewrite (Translation.interp_subst_bound_expr_list
        (Translation.Resource.bound_subst_of_refs
          (Translation.Resource.head_bound_ref_subst witness)) formals
        (binder_cons (interp_ref formals binders valuation witness) binders)
        binders valuation
        (fun u variable => f_equal Some
          (Translation.interp_head_bound_ref_subst witness formals binders
            valuation u variable)) (IR.symbolize_expr_list store arguments)) in Hargs.
      exact Hargs.
  - iIntros "[[Hstack Hbody] %Hargs]".
    iDestruct "Hbody" as (value) "Hbody". iExists value.
    cbn [Translation.Resource.resource_stack].
    iEval (rewrite <- (Translation.interp_weaken_store formals binders valuation
      value store)) in "Hstack".
    iSplit.
    + iSplitL "Hstack"; [iExact "Hstack" | iExact "Hbody"].
    + iPureIntro.
    rewrite NormalizationBase.symbolize_expr_list_weaken_store.
    rewrite interp_weaken_expr_list. exact Hargs.
  - iIntros "H". iDestruct "H" as (value) "H".
    iDestruct "H" as "[[Hstack Hbody] %Hargs]".
    cbn [Translation.Resource.resource_stack].
    iEval (rewrite (Translation.interp_weaken_store formals binders valuation
      value store)) in "Hstack".
    iFrame "Hstack". iSplitL "Hbody".
    + iExists value. iExact "Hbody".
    + iPureIntro. rewrite NormalizationBase.symbolize_expr_list_weaken_store in Hargs.
      rewrite interp_weaken_expr_list in Hargs. exact Hargs.
  - iIntros "H". iDestruct "H" as (value) "H".
    iApply (bi.equiv_entails_1_1 _ _
      (term_interp_resource_prenex_at_arguments_weaken runtime formals
        binders valuation arguments values value body)).
    iExact "H".
  - iIntros "Hfirst".
    iApply (IHHentails2 binders).
    iApply (IHHentails1 binders with "Hfirst").
  - pose (source_binders := fun t (variable : bvar Δ t) =>
      binders t (renaming t variable)).
    have Hrenaming : forall t (variable : bvar Δ t),
        binders t (renaming t variable) = source_binders t variable.
    { intros. reflexivity. }
    rewrite (term_interp_resource_prenex_at_arguments_rename runtime formals
      valuation arguments values left _ renaming source_binders binders Hrenaming).
    rewrite (term_interp_resource_prenex_at_arguments_rename runtime formals
      valuation arguments values right _ renaming source_binders binders Hrenaming).
    apply IHHentails.
  - pose (tail := fun u (variable : bvar Δ u) =>
      binders u (MThere variable)).
    have Heta : binder_cons (binders t MHere) tail = binders :=
      binder_cons_eta binders.
    iIntros "Hbody".
    iPoseProof (IHHentails tail with "[Hbody]")
      as "Htarget".
    { iExists (binders t MHere). rewrite Heta. iExact "Hbody". }
    rewrite <- Heta.
    iApply (bi.equiv_entails_1_2 _ _
      (term_interp_resource_prenex_at_arguments_weaken runtime formals tail
        valuation arguments values (binders t MHere) target)).
    iExact "Htarget".
Qed.

Lemma term_interp_resource_prenex_at_arguments_and {Γ F Δ ts}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (arguments : gexpr_list Γ ts) (values : tval_list ts)
    (prenex : Translation.Resource.resource_prenex Γ F Δ)
    (frame : Translation.Resource.core_assertion F Δ) :
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      arguments values (Translation.Resource.prenex_and prenex frame) ≡
    (term_interp_resource_prenex_at_arguments runtime formals binders valuation
       arguments values prenex ∗
     term_interp_core formals binders valuation frame)%I.
Proof.
  revert binders frame. induction prenex; intros binders frame.
  - cbn [term_interp_resource_prenex_at_arguments
      Translation.Resource.prenex_and].
    rewrite !term_interp_rstate.
    cbn [Translation.TermSemantics.interp_core].
    iSplit.
    + iIntros "[[Hstack [Hbody Hframe]] Harguments]".
      iFrame "Hstack Hbody Harguments Hframe".
    + iIntros "[[[Hstack Hbody] Harguments] Hframe]".
      iFrame "Hstack Hbody Hframe Harguments".
  - simpl. iSplit.
    + iIntros "H". iDestruct "H" as (value) "H".
      iPoseProof (bi.equiv_entails_1_1 _ _
        (IHprenex (binder_cons value binders)
          (Translation.Resource.weaken_core frame)) with "H") as
        "[Hbody Hframe]".
      iSplitL "Hbody"; first by iExists value.
      unfold term_interp_core.
      rewrite (Translation.TermSemantics.interp_weaken_core semantic_data).
      iExact "Hframe".
    + iIntros "[Hbody Hframe]". iDestruct "Hbody" as (value) "Hbody".
      iExists value. iApply (bi.equiv_entails_1_2 _ _
        (IHprenex (binder_cons value binders)
          (Translation.Resource.weaken_core frame))).
      iFrame "Hbody". unfold term_interp_core.
      rewrite (Translation.TermSemantics.interp_weaken_core semantic_data).
      iExact "Hframe".
Qed.

Lemma term_interp_resource_prenex_at_arguments_empty {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (prenex : Translation.Resource.resource_prenex Γ F Δ) :
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      (@PENil _ keep_all Γ) Translation.TVNil prenex ≡
    term_interp_resource_prenex runtime formals binders valuation prenex.
Proof.
  revert binders. induction prenex; intros binders; simpl.
  - iSplit.
    + iIntros "[H _]". iExact "H".
    + iIntros "H". iFrame. iPureIntro. reflexivity.
  - iSplit.
    + iIntros "H". iDestruct "H" as (value) "H".
      rewrite term_interp_resource_exists. iExists value.
      iApply (bi.equiv_entails_1_1 _ _ (IHprenex _)). iExact "H".
    + rewrite term_interp_resource_exists.
      iIntros "H". iDestruct "H" as (value) "H". iExists value.
      iApply (bi.equiv_entails_1_2 _ _ (IHprenex _)). iExact "H".
Qed.

Definition concrete_operation_wp {Γ} :=
  @RegionExecution.Primitives.operation_wp _ _ Σ RG Γ
    (@RegionExecution.Control.concrete_control_operations _ _ Σ RG)
    (@RegionExecution.Primitives.concrete_invariant_operations _ _ Σ RG).

(** The finite registration fixes invariant names and executable procedure
    layouts.  Operation semantics come from the concrete interpreter exported
    by [ConcreteGenericRegionExecutionCore]. *)
Context (Registration : certified_module_registration).

(** Semantic trust boundary for Raven atomic blocks.  An explicit [TAtomic]
    block is itself the trust declaration: every configured transition must
    refine execution of the erased body as one physical step.  This is a
    property of the runtime substrate, not evidence supplied by a program. *)
Axiom term_trusted_atomic_runtime_refinement : forall
      {Γ state body outer inner}
      (body_certificate : Structured.structured_certificate Γ
        (GenericRegions.Atomicity.atomic_entry outer)
        body inner)
      (runtime : RegionExecution.Primitives.Model.stack_context Γ) ambient post,
    GenericRegions.Atomicity.take_step GenericRegions.Atomicity.AtomicStep state =
      inr outer ->
    GenericRegions.Atomicity.analysis_records inner =
      GenericRegions.Atomicity.analysis_records outer ->
    translated_runtime_wp runtime ambient
      (GenericRegions.Atomicity.atomic_entry outer)
      inner body post ⊢
      translated_runtime_wp runtime ambient state
        (GenericRegions.Atomicity.atomic_exit outer inner)
        (TAtomic body) post.

(** Registration projections used throughout the dynamic theorem ladder. *)
Definition term_registered_invariants : gset inv_id :=
  registered_invariants Registration.

Definition term_runtime_procedure_body
    (packed : packed_typed_procedure) :
    RuntimeLang.stack_id -> RuntimeLang.runtime_stmt :=
  registered_runtime_procedure_body Registration packed.

Lemma term_runtime_procedure_layout_configured
    (packed : packed_typed_procedure) :
  List.In packed (procedure_entries Hoare.coherent_procedures) ->
  match packed with
  | existT Γ (existT F procedure) =>
      procedure_wf procedure /\
      forall stack,
        @RuntimeErasure.runtime_stmt _ _ Γ
          (@RuntimeErasure.runtime_procedure_names _ _
            Γ F procedure) stack (procedure_body Γ F procedure) =
        term_runtime_procedure_body packed stack
  end.
Proof.
  apply registered_runtime_procedure_layout.
Qed.

Definition runtime_procedure_entry
    (packed : packed_typed_procedure) : RuntimeLang.proc :=
  registered_runtime_procedure_entry Registration packed.

Lemma runtime_procedure_entry_coherent procedure :
  List.In procedure (procedure_entries Hoare.coherent_procedures) ->
  RegionExecution.Primitives.Model.packed_runtime_procedure_registration procedure
    (runtime_procedure_entry procedure).
Proof.
  intros Hin.
  pose proof (term_runtime_procedure_layout_configured procedure Hin)
    as Hlayout.
  destruct procedure as [Γ [F procedure]]. simpl in *.
  destruct Hlayout as (Hwf & Hbody).
  pose proof (procedure_reserved_return_fresh _ Hwf) as Hfresh.
  constructor; simpl; try reflexivity.
  - apply NoDup_ListNoDup.
    apply RuntimeErasure.runtime_procedure_argument_names_nodup. exact Hwf.
  - apply RuntimeErasure.runtime_procedure_locals_nodup; assumption.
  - apply RuntimeErasure.runtime_procedure_arguments_locals_disjoint; assumption.
  - apply RuntimeErasure.runtime_procedure_return_local; assumption.
  - exact Hbody.
Qed.

(** The executable procedure table is term data; its Iris ownership is
    introduced only by [registered_procedure_chunk]. *)
Definition registered_procedure_chunk
    (procedure : packed_typed_procedure) : iProp :=
  RuntimeGhost.proc_tbl_chunk
    (procedure_name (packed_procedure_id procedure))
    (runtime_procedure_entry procedure).

Definition all_registered_procedure_chunks : iProp :=
  ([∗ list] procedure ∈ procedure_entries Hoare.coherent_procedures,
    registered_procedure_chunk procedure)%I.

(** Concrete finite table allocated by initialized adequacy.  Keeping the
    list of bindings visible makes its persistent ghost-map fragments line up
    directly with [all_registered_procedure_chunks]. *)
Definition runtime_procedure_bindings :
    list (RuntimeLang.proc_name * RuntimeLang.proc) :=
  registered_runtime_procedure_bindings Registration.

Definition runtime_procedure_map :
    gmap RuntimeLang.proc_name RuntimeLang.proc :=
  registered_runtime_procedure_map Registration.

Lemma runtime_procedure_binding_names_nodup :
  NoDup (runtime_procedure_bindings ).*1.
Proof.
  unfold runtime_procedure_bindings, registered_runtime_procedure_bindings.
  rewrite <- list_fmap_compose.
  change (NoDup (map (fun procedure =>
    procedure_name (packed_procedure_id procedure))
    (procedure_entries Hoare.coherent_procedures))).
  pose proof (procedure_ids_unique Hoare.coherent_procedures) as Hids.
  generalize dependent Hids.
  induction (procedure_entries Hoare.coherent_procedures) as
      [|procedure procedures IH]; intros Hids; simpl; first constructor.
  inversion Hids as [|identity identities Hnotin Hnodup]; subst.
  constructor.
  - intros Hmember. apply Hnotin.
    apply elem_of_list_fmap in Hmember as [other [Hequal Hin]].
    apply procedure_name_injective in Hequal.
    apply in_map_iff. exists other. split; first symmetry; first exact Hequal.
    rewrite <- elem_of_list_In. exact Hin.
  - apply IH. exact Hnodup.
Qed.

Lemma runtime_procedure_map_chunks :
  ([∗ map] name ↦ procedure ∈ runtime_procedure_map ,
      RuntimeGhost.proc_tbl_chunk name procedure) ⊣⊢
    all_registered_procedure_chunks .
Proof.
  unfold runtime_procedure_map, registered_runtime_procedure_map.
  rewrite big_sepM_list_to_map;
    last exact (runtime_procedure_binding_names_nodup ).
  unfold runtime_procedure_bindings, registered_runtime_procedure_bindings,
    all_registered_procedure_chunks, registered_procedure_chunk,
    runtime_procedure_entry.
  rewrite big_sepL_fmap. reflexivity.
Qed.

Lemma registered_procedure_chunks_lookup procedures procedure :
  List.In procedure procedures ->
  ([∗ list] entry ∈ procedures, registered_procedure_chunk entry) ⊢
    registered_procedure_chunk procedure.
Proof.
  intros Hin. induction procedures as [|head tail IH].
  - inversion Hin.
  - simpl in Hin. destruct Hin as [<- | Hin].
    + rewrite big_sepL_cons. iIntros "[$ _]".
    + rewrite big_sepL_cons. iIntros "[_ Htail]".
      iApply (IH Hin). iExact "Htail".
Qed.

Lemma all_registered_procedure_chunks_lookup procedure :
  List.In procedure (procedure_entries Hoare.coherent_procedures) ->
  all_registered_procedure_chunks  ⊢
    registered_procedure_chunk procedure.
Proof. apply registered_procedure_chunks_lookup. Qed.

(** The invariant world, stated against the semantic data of the dynamic
    interpreter. *)
Definition world_body_interp (valuation : symbol_valuation) invariant
    (values : tval_list (Assertion.invariant_args invariant)) : iProp :=
  term_interp_core (formal_env_of_values values) empty_binder_env valuation
    (Hoare.ResourceHoare.invariant_body invariant).

Definition world_body_at (valuation : symbol_valuation) invariant
    (raw_values : list RuntimeModel.val) : iProp :=
  (∃ values : tval_list (Assertion.invariant_args invariant),
    ⌜@RegionExecution.Primitives.Model.tval_list_to_rich_list _
       (Assertion.invariant_args invariant) values = raw_values⌝ ∗
    world_body_interp valuation invariant values)%I.

Definition term_world (valuation : symbol_valuation) invariant : iProp :=
  (∃ established : gset (list RuntimeModel.val),
    @own Σ (authR RuntimeModel.inv_argsUR)
      (@RegionExecution.Primitives.Model.core_invtoken_inG _ _ Σ RG)
      (RuntimeModel.invtoken_names (invariant_name invariant))
      (● (established : RuntimeModel.inv_argsUR)) ∗
    [∗ set] raw_values ∈ established,
      world_body_at valuation invariant raw_values)%I.

Definition term_world_context (valuation : symbol_valuation) : iProp :=
  ([∗ set] invariant ∈ term_registered_invariants ,
    inv (invariant_namespace invariant) (term_world valuation invariant))%I.

Global Instance term_world_context_persistent valuation :
  Persistent (term_world_context valuation).
Proof. unfold term_world_context. apply _. Qed.

Lemma world_body_interp_constant_symbols left_valuation right_valuation invariant values :
  constant_symbols_agree left_valuation right_valuation ->
  world_body_interp left_valuation invariant values ≡
    world_body_interp right_valuation invariant values.
Proof.
  intros Hagree. unfold world_body_interp.
  apply term_interp_core_constant_symbols; first exact Hagree.
  apply Hoare.ResourceHoare.invariant_body_entry_free.
Qed.

Lemma world_body_at_constant_symbols left_valuation right_valuation invariant raw_values :
  constant_symbols_agree left_valuation right_valuation ->
  world_body_at left_valuation invariant raw_values ≡
    world_body_at right_valuation invariant raw_values.
Proof.
  intros Hagree. unfold world_body_at.
  apply bi.exist_proper. intro values.
  rewrite (world_body_interp_constant_symbols left_valuation right_valuation invariant
    values Hagree). reflexivity.
Qed.

Lemma term_world_constant_symbols left_valuation right_valuation invariant :
  constant_symbols_agree left_valuation right_valuation ->
  term_world left_valuation invariant ≡ term_world right_valuation invariant.
Proof.
  intros Hagree. unfold term_world.
  apply bi.exist_proper. intro established.
  apply bi.sep_proper; first reflexivity.
  apply big_sepS_proper. intros raw_values Hmember.
  apply world_body_at_constant_symbols. exact Hagree.
Qed.

Lemma term_world_context_constant_symbols left_valuation right_valuation :
  constant_symbols_agree left_valuation right_valuation ->
  term_world_context left_valuation ≡
    term_world_context right_valuation.
Proof.
  intros Hagree. unfold term_world_context.
  apply big_sepS_proper. intros invariant Hmember.
  apply inv_proper. apply term_world_constant_symbols. exact Hagree.
Qed.

Lemma term_world_context_lookup valuation invariant :
  invariant ∈ term_registered_invariants  ->
  term_world_context valuation ⊢
    inv (invariant_namespace invariant) (term_world valuation invariant).
Proof.
  intros Hmember. iIntros "#Hworlds".
  iApply (big_sepS_elem_of with "Hworlds"). exact Hmember.
Qed.

(** Install the finite family of invariant worlds from the empty authorities
    allocated before [runtimeG] was assembled. *)
Lemma term_world_context_alloc (valuation : symbol_valuation) :
  ([∗ set] invariant ∈ term_registered_invariants ,
    @own Σ (authR RuntimeModel.inv_argsUR)
      (@RegionExecution.Primitives.Model.core_invtoken_inG _ _ Σ RG)
      (RuntimeModel.invtoken_names (invariant_name invariant))
      (● (∅ : RuntimeModel.inv_argsUR))) ={⊤}=∗
    term_world_context valuation.
Proof.
  iIntros "Htokens".
  iApply big_sepS_fupd.
  iApply (big_sepS_impl with "Htokens").
  iIntros "!#" (invariant Hregistered) "Htoken".
  iApply inv_alloc. iNext.
  iExists (∅ : gset (list RuntimeModel.val)).
  rewrite big_sepS_empty. iFrame.
Qed.



Global Instance world_body_interp_timeless valuation invariant values :
  Timeless (world_body_interp valuation invariant values).
Proof.
  unfold world_body_interp.
  rewrite (term_interp_core_as_assertion
    (Translation.data_empty_stack_context semantic_data)).
  apply term_interp_assertion_timeless.
  apply TermLeaf.term_predicates_timeless.
Qed.

Global Instance world_body_at_timeless valuation invariant raw_values :
  Timeless (world_body_at valuation invariant raw_values).
Proof.
  unfold world_body_at. apply bi.exist_timeless. intros values.
  apply bi.sep_timeless; apply _.
Qed.

Global Instance term_world_timeless valuation invariant :
  Timeless (term_world valuation invariant).
Proof.
  unfold term_world. apply bi.exist_timeless. intros established.
  apply bi.sep_timeless; first apply _.
  apply big_sepS_timeless. intros raw_values _. apply _.
Qed.

Lemma term_world_fragment_member invariant established values :
  @own Σ (authR RuntimeModel.inv_argsUR)
      (@RegionExecution.Primitives.Model.core_invtoken_inG _ _ Σ RG)
      (RuntimeModel.invtoken_names (invariant_name invariant))
      (● (established : RuntimeModel.inv_argsUR)) -∗
  @RegionExecution.Primitives.Model.core_invariant_own _ _ Σ RG invariant values -∗
  ⌜@RegionExecution.Primitives.Model.tval_list_to_rich_list _ (Assertion.invariant_args invariant) values ∈
    established⌝.
Proof.
  iIntros "Hauth Hfrag". unfold RegionExecution.Primitives.Model.core_invariant_own.
  iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
  apply auth_both_valid_discrete in Hvalid as [Hincluded _].
  apply gset_included in Hincluded. iPureIntro. set_solver.
Qed.

Lemma term_world_open valuation invariant values E :
  ↑(invariant_namespace invariant) ⊆ E ->
  inv (invariant_namespace invariant) (term_world valuation invariant) -∗
  @RegionExecution.Primitives.Model.core_invariant_own _ _ Σ RG invariant values
    ={E, E ∖ ↑(invariant_namespace invariant)}=∗
  world_body_interp valuation invariant values ∗
    (world_body_interp valuation invariant values
      ={E ∖ ↑(invariant_namespace invariant), E}=∗ True).
Proof.
  intros Hnamespace. iIntros "#Hworld Hfragment".
  iMod (inv_acc_timeless with "Hworld") as "[Hcontents Hclose]";
    first exact Hnamespace.
  iDestruct "Hcontents" as (established) "[Hauth Hbodies]".
  iDestruct (term_world_fragment_member with "Hauth Hfragment") as %Hmember.
  rewrite (big_sepS_delete _ established
    (@RegionExecution.Primitives.Model.tval_list_to_rich_list _ (Assertion.invariant_args invariant) values) Hmember).
  iDestruct "Hbodies" as "[Hbody_at Hbodies]".
  iDestruct "Hbody_at" as (stored_values) "[%Hstored Hbody]".
  apply (RegionExecution.Primitives.Model.tval_list_to_rich_list_injective
    (Assertion.invariant_args invariant)) in Hstored. subst stored_values.
  iModIntro. iFrame "Hbody". iIntros "Hbody". iApply "Hclose".
  iExists established. iFrame "Hauth".
  rewrite (big_sepS_delete _ established
    (@RegionExecution.Primitives.Model.tval_list_to_rich_list _ (Assertion.invariant_args invariant) values) Hmember).
  iFrame "Hbodies". iExists values. iFrame. done.
Qed.

Lemma term_world_establish valuation invariant values E :
  ↑(invariant_namespace invariant) ⊆ E ->
  inv (invariant_namespace invariant) (term_world valuation invariant) -∗
  world_body_interp valuation invariant values ={E}=∗
  @RegionExecution.Primitives.Model.core_invariant_own _ _ Σ RG invariant values.
Proof.
  intros Hnamespace. iIntros "#Hworld Hbody".
  iMod (inv_acc_timeless with "Hworld") as "[Hcontents Hclose]";
    first exact Hnamespace.
  iDestruct "Hcontents" as (established) "[Hauth Hbodies]".
  set raw_values := @RegionExecution.Primitives.Model.tval_list_to_rich_list _
    (Assertion.invariant_args invariant) values.
  iMod (own_update _ _
    (● ((established ∪ {[raw_values]}) : RuntimeModel.inv_argsUR) ⋅
     ◯ ({[raw_values]} : RuntimeModel.inv_argsUR)) with "Hauth")
    as "[Hauth Hfragment]".
  { etrans.
    - apply (auth_update_auth (established : RuntimeModel.inv_argsUR)
        (established ∪ {[raw_values]}) (established ∪ {[raw_values]})).
      apply gset_local_update. set_solver.
    - apply auth_update_dfrac_alloc; [apply _|].
      apply gset_included. set_solver. }
  iMod ("Hclose" with "[-Hfragment]").
  { iExists (established ∪ {[raw_values]}). iFrame "Hauth".
    destruct (decide (raw_values ∈ established)) as [Hpresent|Hfresh].
    - have Heq : established ∪ {[raw_values]} = established.
      { apply set_eq. intros other. rewrite elem_of_union elem_of_singleton.
        split.
        - intros [Hother|Heq]; first exact Hother. subst. exact Hpresent.
        - intros Hother. left. exact Hother. }
      rewrite Heq. iFrame "Hbodies".
    - rewrite big_sepS_union; last set_solver.
      iFrame "Hbodies". rewrite big_sepS_singleton.
      iExists values. iFrame. done. }
  iModIntro. unfold RegionExecution.Primitives.Model.core_invariant_own. iExact "Hfragment".
Qed.

(** ** Held worlds

    While instances of an invariant are open, the rest of its world -- the
    bodies of its other established instances -- is held by the enclosing
    accesses instead of the Iris invariant, so that another instance can be
    opened from it. *)
Definition held_world_of (valuation : symbol_valuation) (invariant : inv_id)
    (opened : gset (list RuntimeModel.val)) : iProp :=
  (∃ established : gset (list RuntimeModel.val),
    ⌜opened ⊆ established⌝ ∗
    @own Σ (authR RuntimeModel.inv_argsUR)
      (@RegionExecution.Primitives.Model.core_invtoken_inG _ _ Σ RG)
      (RuntimeModel.invtoken_names (invariant_name invariant))
      (● (established : RuntimeModel.inv_argsUR)) ∗
    [∗ set] raw_values ∈ established ∖ opened,
      world_body_at valuation invariant raw_values)%I.

Lemma world_body_at_values valuation (invariant : inv_id) values :
  world_body_at valuation invariant
      (@RegionExecution.Primitives.Model.tval_list_to_rich_list _
        (Assertion.invariant_args invariant) values) ⊣⊢
    world_body_interp valuation invariant values.
Proof.
  iSplit.
  - iIntros "Hat". iDestruct "Hat" as (stored_values) "[%Hstored Hbody]".
    apply (RegionExecution.Primitives.Model.tval_list_to_rich_list_injective
      (Assertion.invariant_args invariant)) in Hstored. subst stored_values.
    iExact "Hbody".
  - iIntros "Hbody". iExists values. iFrame. done.
Qed.

(** Opening the first instance of an invariant holds the rest of its
    world. *)
Lemma term_world_open_held valuation (invariant : inv_id) values E :
  ↑(invariant_namespace invariant) ⊆ E ->
  inv (invariant_namespace invariant) (term_world valuation invariant) -∗
  @RegionExecution.Primitives.Model.core_invariant_own _ _ Σ RG invariant values
    ={E, E ∖ ↑(invariant_namespace invariant)}=∗
  world_body_interp valuation invariant values ∗
  held_world_of valuation invariant
    {[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
      (Assertion.invariant_args invariant) values]} ∗
  (held_world_of valuation invariant
      {[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
        (Assertion.invariant_args invariant) values]} -∗
    world_body_interp valuation invariant values
      ={E ∖ ↑(invariant_namespace invariant), E}=∗ True).
Proof.
  intros Hnamespace. iIntros "#Hworld Hfragment".
  set raw_values := @RegionExecution.Primitives.Model.tval_list_to_rich_list _
    (Assertion.invariant_args invariant) values.
  iMod (inv_acc_timeless with "Hworld") as "[Hcontents Hclose]";
    first exact Hnamespace.
  iDestruct "Hcontents" as (established) "[Hauth Hbodies]".
  iDestruct (term_world_fragment_member with "Hauth Hfragment") as %Hmember.
  rewrite (big_sepS_delete _ established raw_values Hmember).
  iDestruct "Hbodies" as "[Hbody_at Hbodies]".
  iModIntro. iSplitL "Hbody_at"; [by iApply world_body_at_values|].
  iSplitL "Hauth Hbodies".
  { iExists established. iFrame. iPureIntro. set_solver. }
  iIntros "Hheld Hbody". iApply "Hclose".
  iDestruct "Hheld" as (established') "(%Hsubset & Hauth & Hbodies)".
  iExists established'. iFrame "Hauth".
  have Hmember' : raw_values ∈ established' by set_solver.
  rewrite (big_sepS_delete _ established' raw_values Hmember').
  iFrame "Hbodies". by iApply world_body_at_values.
Qed.

(** Another instance is opened from the held world ... *)
Lemma held_world_take valuation (invariant : inv_id) opened values :
  @RegionExecution.Primitives.Model.tval_list_to_rich_list _
    (Assertion.invariant_args invariant) values ∉ opened ->
  held_world_of valuation invariant opened -∗
  @RegionExecution.Primitives.Model.core_invariant_own _ _ Σ RG invariant values -∗
  world_body_interp valuation invariant values ∗
  held_world_of valuation invariant
    ({[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
      (Assertion.invariant_args invariant) values]} ∪ opened).
Proof.
  intros Hfresh. iIntros "Hheld Hfragment".
  set raw_values := @RegionExecution.Primitives.Model.tval_list_to_rich_list _
    (Assertion.invariant_args invariant) values.
  iDestruct "Hheld" as (established) "(%Hsubset & Hauth & Hbodies)".
  iDestruct (term_world_fragment_member with "Hauth Hfragment") as %Hmember.
  have Hremaining : raw_values ∈ established ∖ opened by set_solver.
  rewrite (big_sepS_delete _ (established ∖ opened) raw_values Hremaining).
  iDestruct "Hbodies" as "[Hbody_at Hbodies]".
  iSplitL "Hbody_at"; [by iApply world_body_at_values|].
  iExists established. iFrame "Hauth". iSplit; [iPureIntro; set_solver|].
  replace (established ∖ ({[raw_values]} ∪ opened))
    with (established ∖ opened ∖ {[raw_values]}) by set_solver.
  iExact "Hbodies".
Qed.

(** ... and returned to it. *)
Lemma held_world_put valuation (invariant : inv_id) opened values :
  @RegionExecution.Primitives.Model.tval_list_to_rich_list _
    (Assertion.invariant_args invariant) values ∉ opened ->
  held_world_of valuation invariant
    ({[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
      (Assertion.invariant_args invariant) values]} ∪ opened) -∗
  world_body_interp valuation invariant values -∗
  held_world_of valuation invariant opened.
Proof.
  intros Hfresh. iIntros "Hheld Hbody".
  set raw_values := @RegionExecution.Primitives.Model.tval_list_to_rich_list _
    (Assertion.invariant_args invariant) values.
  iDestruct "Hheld" as (established) "(%Hsubset & Hauth & Hbodies)".
  iExists established. iFrame "Hauth". iSplit; [iPureIntro; set_solver|].
  have Hremaining : raw_values ∈ established ∖ opened by set_solver.
  rewrite (big_sepS_delete _ (established ∖ opened) raw_values Hremaining).
  replace (established ∖ opened ∖ {[raw_values]})
    with (established ∖ ({[raw_values]} ∪ opened)) by set_solver.
  iFrame "Hbodies". by iApply world_body_at_values.
Qed.

(** ** Held instances

    The instances open in enclosing accesses, innermost first.  A list is
    indexed by the types of its pinned vector: the tracked expressions
    followed by the instances' arguments, outermost first. *)
Inductive held_list (Γ : decl_context) (ts : context) : context -> Type :=
| HeldNil : held_list Γ ts ts
| HeldCons types (invariant : inv_id)
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (values : tval_list (Assertion.invariant_args invariant))
    (rest : held_list Γ ts types) :
    held_list Γ ts (types ++ Assertion.invariant_args invariant).

Arguments HeldNil {_ _}.
Arguments HeldCons {_ _ _} _ _ _ _.

(** The pinned expressions and their values. *)
Fixpoint held_pinned {Γ ts types} (tracked : gexpr_list Γ ts)
    (held : held_list Γ ts types) : gexpr_list Γ types :=
  match held with
  | HeldNil => tracked
  | HeldCons _ arguments _ rest =>
      IR.pexpr_list_append (held_pinned tracked rest) arguments
  end.

Fixpoint held_pinned_values {Γ ts types} (values : tval_list ts)
    (held : held_list Γ ts types) : tval_list types :=
  match held with
  | HeldNil => values
  | HeldCons _ _ opened rest =>
      Translation.tval_list_append (held_pinned_values values rest) opened
  end.

(** The analyzer records the held instances correspond to. *)
Fixpoint held_records {Γ ts types} (held : held_list Γ ts types) :
    list (inv_id * AnalysisView.access_key) :=
  match held with
  | HeldNil => []
  | HeldCons invariant arguments _ rest =>
      (invariant, RegionSyntax.argument_key arguments) :: held_records rest
  end.

Definition held_aligned {Γ ts types}
    (records : list GenericRegions.Atomicity.open_record)
    (held : held_list Γ ts types) : Prop :=
  map (fun record => (GenericRegions.Atomicity.record_invariant record,
    GenericRegions.Atomicity.record_key record)) records = held_records held.

(** The values each held declaration is open at. *)
Fixpoint held_opened {Γ ts types} (held : held_list Γ ts types) :
    gmap inv_id (gset (list RuntimeModel.val)) :=
  match held with
  | HeldNil => ∅
  | HeldCons invariant _ opened rest =>
      <[invariant := {[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
          (Assertion.invariant_args invariant) opened]} ∪
        default ∅ (held_opened rest !! invariant)]> (held_opened rest)
  end.

Definition held_world {Γ ts types} (valuation : symbol_valuation)
    (held : held_list Γ ts types) : iProp :=
  [∗ map] invariant ↦ opened ∈ held_opened held,
    held_world_of valuation invariant opened.

(** Held instances under one more declaration. *)
Fixpoint held_shift {d Γ ts types} (held : held_list Γ ts types) :
    held_list (d :: Γ) ts types :=
  match held with
  | HeldNil => HeldNil
  | HeldCons invariant arguments opened rest =>
      HeldCons invariant (IR.pexpr_list_shift arguments) opened
        (held_shift rest)
  end.

Lemma pexpr_list_shift_append {keep d Γ left_types right_types}
    (left : pexpr_list keep Γ left_types)
    (right : pexpr_list keep Γ right_types) :
  IR.pexpr_list_shift (d := d) (IR.pexpr_list_append left right) =
    IR.pexpr_list_append (IR.pexpr_list_shift left) (IR.pexpr_list_shift right).
Proof.
  induction left as [|t ts expression tail IH]; cbn; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma held_shift_pinned {d Γ ts types} (tracked : gexpr_list Γ ts)
    (held : held_list Γ ts types) :
  held_pinned (IR.pexpr_list_shift (d := d) tracked) (held_shift held) =
    IR.pexpr_list_shift (held_pinned tracked held).
Proof.
  induction held; cbn; [reflexivity|].
  rewrite IHheld pexpr_list_shift_append. reflexivity.
Qed.

Lemma held_shift_pinned_values {d Γ ts types} (values : tval_list ts)
    (held : held_list Γ ts types) :
  held_pinned_values values (held_shift (d := d) held) =
    held_pinned_values values held.
Proof. induction held; cbn; [reflexivity|]. rewrite IHheld. reflexivity. Qed.

Lemma held_shift_records {d Γ ts types} (held : held_list Γ ts types) :
  held_records (held_shift (d := d) held) = held_records held.
Proof.
  induction held; cbn; [reflexivity|].
  rewrite IHheld RegionSyntax.argument_key_shift. reflexivity.
Qed.

Lemma held_shift_opened {d Γ ts types} (held : held_list Γ ts types) :
  held_opened (held_shift (d := d) held) = held_opened held.
Proof. induction held; cbn; [reflexivity|]. rewrite IHheld. reflexivity. Qed.

Lemma held_shift_world {d Γ ts types} valuation (held : held_list Γ ts types) :
  held_world valuation (held_shift (d := d) held) = held_world valuation held.
Proof. unfold held_world. rewrite held_shift_opened. reflexivity. Qed.

(** Held instances under one more tracked expression. *)
Fixpoint held_track {Γ ts types} t (held : held_list Γ ts types) :
    held_list Γ (t :: ts) (t :: types) :=
  match held in held_list _ _ types
    return held_list Γ (t :: ts) (t :: types) with
  | HeldNil => HeldNil
  | HeldCons invariant arguments opened rest =>
      HeldCons invariant arguments opened (held_track t rest)
  end.

Lemma held_track_pinned {Γ ts types t} (expression : gexpr Γ t)
    (tracked : gexpr_list Γ ts) (held : held_list Γ ts types) :
  held_pinned (PECons expression tracked) (held_track t held) =
    PECons expression (held_pinned tracked held).
Proof. induction held; cbn; [reflexivity|]. rewrite IHheld. reflexivity. Qed.

Lemma held_track_pinned_values {Γ ts types t} (value : tval t)
    (values : tval_list ts) (held : held_list Γ ts types) :
  held_pinned_values (TVCons value values) (held_track t held) =
    TVCons value (held_pinned_values values held).
Proof. induction held; cbn; [reflexivity|]. rewrite IHheld. reflexivity. Qed.

Lemma held_track_records {Γ ts types t} (held : held_list Γ ts types) :
  held_records (held_track t held) = held_records held.
Proof. induction held; cbn; [reflexivity|]. rewrite IHheld. reflexivity. Qed.

Lemma held_track_opened {Γ ts types t} (held : held_list Γ ts types) :
  held_opened (held_track t held) = held_opened held.
Proof. induction held; cbn; [reflexivity|]. rewrite IHheld. reflexivity. Qed.

Lemma held_track_world {Γ ts types t} valuation
    (held : held_list Γ ts types) :
  held_world valuation (held_track t held) = held_world valuation held.
Proof. unfold held_world. rewrite held_track_opened. reflexivity. Qed.

(** The recursive procedure interface has exactly the three operational
    leaves: discard-result call, storing call, and spawn.  It is supplied
    under Löb later and does not assume procedure semantics.

    Stated over [resource_prenex], not [assertion]: with procedure
    contracts core-shaped, the obligation's
    pre- and post-conditions are resource telescopes, and the resource
    call and spawn rules discharge against it with no interpretation
    bridge. *)
Inductive procedure_leaf_obligation {Γ F Δ} :
    Hoare.mask -> Hoare.mask -> Translation.Resource.resource_prenex Γ F Δ ->
    stmt Γ -> Translation.Resource.resource_prenex Γ F Δ -> Prop :=
| ProcedureDiscardObligation procedure arguments store contract_pre
    (contract_post : Translation.Resource.core_assertion F
      (Assertion.procedure_return procedure :: Δ)) current_mask mask_post :
    resource_instantiated_pre F Δ procedure
      (IR.symbolize_expr_list store arguments) contract_pre ->
    resource_instantiated_post_value F Δ procedure
      (Translation.Assertions.weaken_expr_list
        (IR.symbolize_expr_list store arguments))
      (ERef (RefBound MHere)) contract_post ->
    Certified.required_mask procedure ⊆ current_mask ->
    mask_post ⊆ current_mask ∪ Certified.granted_mask procedure ->
    procedure_leaf_obligation current_mask mask_post
      (Translation.Resource.RState store contract_pre)
      (TCall procedure arguments (@CTDiscard Γ (Assertion.procedure_return procedure)))
      (Translation.Resource.ResourceExists (Assertion.procedure_return procedure)
        (Translation.Resource.RState
          (Translation.Assertions.weaken_store store) contract_post))
| ProcedureStoreObligation procedure arguments store init
    (target : IR.write_target init Γ (Assertion.procedure_return procedure))
    contract_pre (contract_post : Translation.Resource.core_assertion F
      (Assertion.procedure_return procedure :: Δ))
    current_mask mask_post :
    resource_instantiated_pre F Δ procedure
      (IR.symbolize_expr_list store arguments) contract_pre ->
    resource_instantiated_post_value F Δ procedure
      (Translation.Assertions.weaken_expr_list
        (IR.symbolize_expr_list store arguments))
      (ERef (RefBound MHere)) contract_post ->
    Certified.required_mask procedure ⊆ current_mask ->
    mask_post ⊆ current_mask ∪ Certified.granted_mask procedure ->
    procedure_leaf_obligation current_mask mask_post
      (Translation.Resource.RState store contract_pre)
      (TCall procedure arguments (CTStore init target))
      (Translation.Resource.ResourceExists (Assertion.procedure_return procedure)
        (Translation.Resource.RState
          (IR.update_store_with_bound store target) contract_post))
| ProcedureSpawnObligation procedure arguments store contract_pre
    current_mask mask_post :
    resource_instantiated_pre F Δ procedure
      (IR.symbolize_expr_list store arguments) contract_pre ->
    Certified.required_mask procedure ⊆ current_mask ->
    mask_post ⊆ current_mask ->
    procedure_leaf_obligation current_mask mask_post
      (Translation.Resource.RState store contract_pre)
      (TSpawn procedure arguments)
      (Translation.Resource.RState store
        (Translation.Resource.CPure True)).

(** *** The rules and the obligation meet

    These three say that the premises of [RavenHoareRules.RTCallDiscard],
    [RTCallStore] and [RTSpawn] are exactly what
    [procedure_leaf_obligation] needs, at exactly the pre- and
    post-conditions those rules produce.  They are what makes an
    induction over a [RavenHoareRules.RavenHoareTriple] usable against
    the runtime call lemma.  The premises are stated directly over the one
    authoritative [ResourceContracts] environment and its total contract
    instantiation functions. *)
Lemma call_discard_obligation {Γ F Δ} procedure
    (store : symbolic_store Γ F Δ)
    (typed_arguments : rexpr_list Γ (Assertion.procedure_args procedure))
    (current_mask mask_post : Hoare.mask) :
  Hoare.ResourceHoare.procedure_verified procedure ->
  Certified.required_mask procedure ⊆ current_mask ->
  mask_post ⊆ current_mask ∪ Certified.granted_mask procedure ->
  procedure_leaf_obligation current_mask mask_post
    (Translation.Resource.RState store
      (ResourceInstances.instantiated_pre procedure
        (IR.symbolize_expr_list store typed_arguments)))
    (TCall procedure typed_arguments
      (@CTDiscard Γ (Assertion.procedure_return procedure)))
    (Translation.Resource.ResourceExists (Assertion.procedure_return procedure)
      (Translation.Resource.RState
        (Translation.Assertions.weaken_store store)
        (ResourceInstances.instantiated_post procedure
          (Translation.Assertions.weaken_expr_list
            (IR.symbolize_expr_list store typed_arguments))))).
Proof.
  intros Hverified Hmask Hpost.
  apply ProcedureDiscardObligation;
    [split; [exact Hverified | reflexivity]
    | split; [exact Hverified | reflexivity]
    | exact Hmask | exact Hpost].
Qed.

Lemma call_store_obligation {Γ F Δ} procedure
    (store : symbolic_store Γ F Δ)
    {init} (target : write_target init Γ (Assertion.procedure_return procedure))
    (typed_arguments : rexpr_list Γ (Assertion.procedure_args procedure))
    (current_mask mask_post : Hoare.mask) :
  Hoare.ResourceHoare.procedure_verified procedure ->
  Certified.required_mask procedure ⊆ current_mask ->
  mask_post ⊆ current_mask ∪ Certified.granted_mask procedure ->
  procedure_leaf_obligation current_mask mask_post
    (Translation.Resource.RState store
      (ResourceInstances.instantiated_pre procedure
        (IR.symbolize_expr_list store typed_arguments)))
    (TCall procedure typed_arguments (CTStore init target))
    (Translation.Resource.ResourceExists (Assertion.procedure_return procedure)
      (Translation.Resource.RState
        (IR.update_store_with_bound store target)
        (ResourceInstances.instantiated_post procedure
          (Translation.Assertions.weaken_expr_list
            (IR.symbolize_expr_list store typed_arguments))))).
Proof.
  intros Hverified Hmask Hpost.
  apply ProcedureStoreObligation;
    [split; [exact Hverified | reflexivity]
    | split; [exact Hverified | reflexivity]
    | exact Hmask | exact Hpost].
Qed.

Lemma spawn_obligation {Γ F Δ} procedure
    (store : symbolic_store Γ F Δ)
    (typed_arguments : rexpr_list Γ (Assertion.procedure_args procedure))
    (current_mask mask_post : Hoare.mask) :
  Hoare.ResourceHoare.procedure_verified procedure ->
  Certified.required_mask procedure ⊆ current_mask ->
  mask_post ⊆ current_mask ->
  procedure_leaf_obligation current_mask mask_post
    (Translation.Resource.RState store
      (ResourceInstances.instantiated_pre procedure
        (IR.symbolize_expr_list store typed_arguments)))
    (TSpawn procedure typed_arguments)
    (Translation.Resource.RState store
      (Translation.Resource.CPure True)).
Proof.
  intros Hverified Hmask Hpost.
  apply ProcedureSpawnObligation;
    [split; [exact Hverified | reflexivity] | exact Hmask | exact Hpost].
Qed.

Definition verified_procedure_specs : iProp :=
  (□ ∀ (Γ : decl_context) (F Δ : context)
      (pre post : Translation.Resource.resource_prenex Γ F Δ)
      (statement : stmt Γ) (mask_pre mask_post : Hoare.mask) entry exit
      (runtime : RegionExecution.Primitives.Model.stack_context Γ)
      (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
      (ambient : coPset),
    ⌜procedure_leaf_obligation mask_pre mask_post pre statement post⌝ -∗
    ⌜RegionExecution.Primitives.Model.runtime_mask mask_post ⊆
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry⌝ -∗
    ⌜RegionExecution.Primitives.Model.runtime_mask term_registered_invariants ⊆
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry⌝ -∗
    term_world_context valuation -∗
    term_interp_resource_prenex runtime formals binders valuation pre -∗
    concrete_operation_wp runtime ambient entry statement exit
      (term_interp_resource_prenex runtime formals binders valuation post))%I.

Definition global_world_context (valuation : symbol_valuation) : iProp :=
  (term_world_context valuation ∗
    (all_registered_procedure_chunks  ∗
      verified_procedure_specs ))%I.

Global Instance global_world_context_persistent valuation :
  Persistent (global_world_context valuation).
Proof. unfold global_world_context, all_registered_procedure_chunks. apply _. Qed.

Lemma global_world_context_constant_symbols left_valuation right_valuation :
  constant_symbols_agree left_valuation right_valuation ->
  global_world_context left_valuation ≡
    global_world_context right_valuation.
Proof.
  intros Hagree. unfold global_world_context.
  rewrite (term_world_context_constant_symbols left_valuation right_valuation
    Hagree). reflexivity.
Qed.

Lemma verified_procedure_specs_valid
    (Hguarded : all_registered_procedure_chunks  ∗
      ▷ verified_procedure_specs  ⊢ verified_procedure_specs ) :
  all_registered_procedure_chunks  ⊢ verified_procedure_specs .
Proof.
  iIntros "#Hprocedures". iLöb as "IH". iApply Hguarded.
  iFrame "Hprocedures". iNext. iExact "IH".
Qed.

Lemma global_world_procedure_specs valuation :
  global_world_context valuation ⊢
    term_world_context valuation ∗ verified_procedure_specs .
Proof.
  rewrite /global_world_context.
  iIntros "[$ [_ $]]".
Qed.

Lemma term_interpreted_expr_list_total {F Δ ts} (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (expressions : Translation.Assertions.expr_list F Δ ts) :
  exists values, interp_expr_list formals binders valuation expressions =
    Some values.
Proof.
  induction expressions as [|t ts expression expressions IH].
  - exists TVNil. reflexivity.
  - destruct (interp_expr_total formals binders valuation expression) as
      [value Hvalue].
    destruct IH as [values Hvalues].
    exists (TVCons value values). simpl. rewrite Hvalue. rewrite Hvalues.
    reflexivity.
Qed.


(** Interpretation-level form of canonical procedure-precondition
    instantiation.  With core-shaped contracts this is one formal
    substitution and one binder weakening: the [subst_bound_assertion]
    step and the [reindex_stack_context] step are gone, the latter because
    a core assertion has no stack context to reindex. *)
Lemma procedure_pre_instantiation_interp
    {callee_variables callee_formals}
    (procedure : typed_procedure callee_variables callee_formals)
    {F Δ} (arguments : expr_list F Δ (Assertion.procedure_args callee_formals))
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (values : tval_list (Assertion.procedure_args callee_formals))
    (Harguments : interp_expr_list formals binders valuation arguments =
      Some values) :
  term_interp_core formals binders valuation
      (Hoare.procedure_pre_instantiation procedure arguments) ⊣⊢
  term_interp_core (formal_env_of_values values) empty_binder_env valuation
    (procedure_precondition _ _ procedure).
Proof.
  have Hactuals := interp_expr_list_formal_subst_of_values arguments values
    formals binders valuation Harguments.
  unfold Hoare.procedure_pre_instantiation, term_interp_core.
  etrans;
    [apply (Translation.TermSemantics.interp_subst_formals_core semantic_data
      (term_predicates valuation) (expr_list_formal_subst arguments)
      (formal_env_of_values values) formals binders valuation Hactuals) |].
  apply (Translation.TermSemantics.interp_weaken_core_to semantic_data).
Qed.

Lemma existentially_close_prenex_interp {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (valuation : symbol_valuation)
    (prenex : Translation.Resource.resource_prenex Γ F Δ) :
  term_interp_resource_prenex runtime formals empty_binder_env valuation
      (Hoare.existentially_close_prenex prenex) ⊣⊢
  (∃ values : tval_list Δ,
    term_interp_resource_prenex runtime formals
      (formal_env_of_values values) valuation prenex)%I.
Proof.
  induction Δ as [|t tail IH].
  - simpl. iSplit.
    + iIntros "H". iExists TVNil. iExact "H".
    + iIntros "H". iDestruct "H" as (values) "H".
      dependent destruction values. iExact "H".
  - cbn [Hoare.existentially_close_prenex_at]. rewrite IH.
    iSplit.
    + iIntros "H". iDestruct "H" as (tail_values head) "H".
      iExists (TVCons head tail_values). iExact "H".
    + iIntros "H". iDestruct "H" as (values) "H".
      dependent destruction values. iExists values, t1. iExact "H".
Qed.

Lemma procedure_body_post_interp {Γ F Δ}
    (procedure : typed_procedure Γ F)
    (exit_store : symbolic_store Γ (Assertion.procedure_args F) Δ)
    (return_reference : value_ref (Assertion.procedure_args F) Δ
      (procedure_return_type _ _ procedure))
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env (Assertion.procedure_args F))
    (valuation : symbol_valuation) :
  term_interp_resource_prenex runtime formals empty_binder_env valuation
      (Hoare.procedure_body_post procedure exit_store return_reference) ⊣⊢
  (∃ values : tval_list Δ,
    Translation.data_stack_own semantic_data (term_semantic_runtime runtime)
      (interp_store formals (formal_env_of_values values) valuation exit_store) ∗
    term_interp_core formals
      (binder_cons
        (interp_ref formals (formal_env_of_values values) valuation
          return_reference) empty_binder_env) valuation
      (procedure_postcondition _ _ procedure))%I.
Proof.
  unfold Hoare.procedure_body_post.
  rewrite existentially_close_prenex_interp.
  apply bi.exist_proper. intros values.
  rewrite term_interp_rstate.
  apply bi.sep_proper; first reflexivity.
  unfold term_interp_core.
  apply (Translation.TermSemantics.interp_subst_bound_core
    semantic_data (term_predicates valuation)
    (singleton_bound_subst return_reference) formals
    (binder_cons
      (interp_ref formals (formal_env_of_values values) valuation
        return_reference) empty_binder_env)
    (formal_env_of_values values) valuation).
  intros t variable. apply interp_singleton_bound_subst.
Qed.

(** The [exists Hreturn] transport is gone: the caller's result binder has
    type [procedure_return callee_formals] by construction. *)
Lemma procedure_post_instantiation_interp
    {callee_variables callee_formals}
    (procedure : typed_procedure callee_variables callee_formals)
    {F Δ}
    (arguments : expr_list F
      (Assertion.procedure_return callee_formals :: Δ)
      (Assertion.procedure_args callee_formals))
    (result : expr F (Assertion.procedure_return callee_formals :: Δ)
      (Assertion.procedure_return callee_formals))
    (contract : Translation.Resource.core_assertion F
      (Assertion.procedure_return callee_formals :: Δ))
    (Hlookup : lookup_typed_procedure Hoare.coherent_procedures
      (procedure_identity _ _ procedure) =
      Some (pack_typed_procedure procedure))
    (Hinst : resource_instantiated_post_value F Δ
      (procedure_identity _ _ procedure)
      arguments result contract)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (values : tval_list (Assertion.procedure_args callee_formals))
    (return_value : tval (Assertion.procedure_return callee_formals))
    (Harguments : interp_expr_list formals
      (binder_cons return_value binders) valuation arguments = Some values) :
    term_interp_core formals
        (binder_cons return_value binders) valuation contract ⊣⊢
    term_interp_core (formal_env_of_values values)
        (binder_cons return_value empty_binder_env) valuation
        (procedure_postcondition _ _ procedure).
Proof.
  apply (instantiated_post_value_coherent procedure arguments result contract
    Hlookup) in Hinst.
  subst contract.
  have Hactuals := interp_expr_list_formal_subst_of_values arguments values
    formals (binder_cons return_value binders) valuation Harguments.
  unfold term_interp_core.
  etrans;
    [apply (Translation.TermSemantics.interp_subst_formals_core
      semantic_data (term_predicates valuation)
      (expr_list_formal_subst arguments)
      (formal_env_of_values values) formals
      (binder_cons return_value binders) valuation Hactuals) |].
  apply (Translation.TermSemantics.interp_rename_bound_core semantic_data).
  apply binder_cons_return_bound_renaming.
Qed.

Lemma procedure_leaf_operation_valid {Γ F Δ}
    (pre post : Translation.Resource.resource_prenex Γ F Δ) statement
    mask_pre mask_post entry exit
    (Hprocedure : procedure_leaf_obligation
      mask_pre mask_post pre statement post) :
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    RegionExecution.Primitives.Model.runtime_mask mask_post ⊆
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry ->
    RegionExecution.Primitives.Model.runtime_mask term_registered_invariants ⊆
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry ->
    (global_world_context valuation ∗
      term_interp_resource_prenex runtime formals binders valuation pre) ⊢
    concrete_operation_wp runtime ambient entry statement exit
      (term_interp_resource_prenex runtime formals binders valuation post).
Proof.
  intros runtime formals binders valuation ambient Henvelope Hregistered.
  iIntros "[#Hglobal Hpre]".
  iPoseProof (global_world_procedure_specs valuation with "Hglobal")
    as "[#Hworld #Hprocedures]".
  iApply ("Hprocedures" with "[] [] [] Hworld Hpre").
  - iPureIntro. exact Hprocedure.
  - iPureIntro. exact Henvelope.
  - iPureIntro. exact Hregistered.
Qed.

Lemma concrete_operation_wp_mono {Γ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (ambient : coPset) entry (statement : stmt Γ) exit (P Q : iProp) :
  (P ⊢ Q) ->
  concrete_operation_wp runtime ambient entry statement exit P ⊢
    concrete_operation_wp runtime ambient entry statement exit Q.
Proof.
  intros HPQ. unfold concrete_operation_wp.
  apply RegionExecution.Primitives.operation_mono. exact HPQ.
Qed.

Lemma concrete_operation_wp_frame {Γ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (ambient : coPset) entry (statement : stmt Γ) exit (P R : iProp) :
  concrete_operation_wp runtime ambient entry statement exit P ∗ R ⊢
    concrete_operation_wp runtime ambient entry statement exit (P ∗ R).
Proof.
  unfold concrete_operation_wp.
  apply RegionExecution.Primitives.operation_frame.
Qed.

Lemma world_body_interp_core (valuation : symbol_valuation) invariant
    (values : tval_list (Assertion.invariant_args invariant)) :
  world_body_interp valuation invariant values ⊣⊢
  term_interp_core (formal_env_of_values values) empty_binder_env valuation
    (Hoare.ResourceHoare.invariant_body invariant).
Proof. reflexivity. Qed.

(** Semantic interpretation of the canonical invariant instance.  The
    instance is a total function of its arguments. *)
Lemma term_invariant_definition_compatible {F Δ}
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    invariant
    (expressions : Translation.Assertions.expr_list F Δ
      (Assertion.invariant_args invariant)) :
  exists values : tval_list (Assertion.invariant_args invariant),
    interp_expr_list formals binders valuation expressions = Some values /\
    term_interp_core formals binders valuation
      (ResourceInstances.instantiated_invariant invariant expressions) ≡
      world_body_interp valuation invariant values.
Proof.
  destruct (term_interpreted_expr_list_total formals binders valuation expressions)
    as [values Hvalues].
  exists values. split; first exact Hvalues.
  have Hactuals := interp_expr_list_formal_subst_of_values expressions values
    formals binders valuation Hvalues.
  rewrite world_body_interp_core.
  unfold ResourceInstances.instantiated_invariant, term_interp_core.
  etrans;
    [apply (Translation.TermSemantics.interp_subst_formals_core semantic_data
      (term_predicates valuation)
      (Translation.Assertions.expr_list_formal_subst expressions)
      (formal_env_of_values values) formals binders valuation Hactuals) |].
  apply (Translation.TermSemantics.interp_weaken_core_to semantic_data).
Qed.

(** Ambient rule for [assert], a proof-only leaf.  It carries no physical
    step, so the weakest precondition is the identity and the
    interpretation never has to cross into the assertion representation.
    ([done] has no ambient rule: it is not an operation at all, and its
    meaning is given structurally by [region_wp].) *)
Lemma term_ambient_assert_rule_valid {Γ F Δ}
    (store : symbolic_store Γ F Δ)
    (body : Translation.Resource.core_assertion F Δ) condition
    (entry exit : GenericRegions.Atomicity.analysis_state) :
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    term_interp_resource_prenex runtime formals binders valuation
      (Translation.Resource.RState store
        (Translation.Resource.CAnd body
          (Translation.Resource.CExpr (IR.symbolize_expr store condition)))) ⊢
    concrete_operation_wp runtime ambient entry (TAssert condition) exit
      (term_interp_resource_prenex runtime formals binders valuation
        (Translation.Resource.RState store
          (Translation.Resource.CAnd body
            (Translation.Resource.CExpr (IR.symbolize_expr store condition))))).
Proof.
  intros runtime formals binders valuation ambient.
  unfold concrete_operation_wp, RegionExecution.Primitives.operation_wp.
  simpl. reflexivity.
Qed.


(** Ambient rule for [TFieldWrite], over resource telescopes.  The core
    assertion [COwn] interprets exactly like the assertion constructor
    [AOwn], so the proof is the same appeal to [runtime_field_write_wp],
    only routed through [term_interp_rstate] and [term_interp_core]
    instead of [term_interp_assertion]. *)
Lemma term_ambient_field_write_rule_valid {Γ F Δ}
    (store : symbolic_store Γ F Δ) field (base : rexpr Γ TRef)
    (expression : rexpr Γ (Assertion.field_type field)) old_chunk
    (entry exit : GenericRegions.Atomicity.analysis_state) :
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    term_interp_resource_prenex runtime formals binders valuation
      (Translation.Resource.RState store
        (Translation.Resource.COwn field (IR.symbolize_expr store base)
          old_chunk)) ⊢
    concrete_operation_wp runtime ambient entry
      (TFieldWrite field base expression) exit
      (term_interp_resource_prenex runtime formals binders valuation
        (Translation.Resource.RState store
          (Translation.Resource.COwn field
            (IR.symbolize_expr store base)
            (IR.symbolize_expr store expression)))).
Proof.
  intros runtime formals binders valuation ambient.
  rewrite term_interp_rstate.
  unfold concrete_operation_wp, RegionExecution.Primitives.operation_wp.
  simpl. unfold RegionExecution.Primitives.ambient_leaf_wp.
  simpl. unfold RegionExecution.Primitives.ambient_physical_leaf_wp.
  unfold term_interp_core. iIntros "[Hstack Hown]".
  iDestruct "Hown" as (location old_value) "(%Hlocation & %Hold & Hown)".
  iPoseProof (@RegionExecution.Primitives.Model.runtime_field_write_wp _ _ Σ RG Γ F Δ
    runtime formals binders valuation store field base expression location old_value
    (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
    Hlocation with "[$Hstack $Hown]") as "Hwp".
  iEval (unfold RegionExecution.Primitives.Model.runtime_wp) in "Hwp".
  unfold RegionExecution.Primitives.Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iDestruct "Hpost" as (new_value) "(%Hvalue & Hstack & Hown)".
  rewrite term_interp_rstate. iFrame "Hstack". iExists location, new_value.
  iSplit; first done. iSplit; last iExact "Hown". iPureIntro. exact Hvalue.
Qed.

(** Ambient rule for [TFieldRead], over resource telescopes, by the same
    appeal to [runtime_field_read_wp] routed through
    [term_interp_rstate]/[term_interp_core]. *)
Lemma term_ambient_field_read_rule_valid {Γ F Δ}
    (store : symbolic_store Γ F Δ) field
    {init} (target : write_target init Γ (Assertion.field_type field)) (base : rexpr Γ TRef)
    chunk (entry exit : GenericRegions.Atomicity.analysis_state) :
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    term_interp_resource_prenex runtime formals binders valuation
      (Translation.Resource.RState store
        (Translation.Resource.COwn field (IR.symbolize_expr store base)
          chunk)) ⊢
    concrete_operation_wp runtime ambient entry
      (TFieldRead init field target base) exit
      (term_interp_resource_prenex runtime formals binders valuation
        (Translation.Resource.ResourceExists (Assertion.field_type field)
          (Translation.Resource.RState
            (IR.update_store_with_bound store target)
            (Translation.Resource.CAnd
              (Translation.Resource.COwn field
                (Translation.Assertions.weaken_expr
                  (IR.symbolize_expr store base))
                (Translation.Assertions.weaken_expr chunk))
              (Translation.Resource.CExpr
                (EBinOp (BEq (Assertion.field_type field))
                  (ERef (RefBound MHere))
                  (Translation.Assertions.weaken_expr chunk))))))).
Proof.
  intros runtime formals binders valuation ambient.
  rewrite term_interp_rstate term_interp_resource_exists.
  unfold concrete_operation_wp, RegionExecution.Primitives.operation_wp.
  simpl. unfold RegionExecution.Primitives.ambient_leaf_wp.
  simpl. unfold RegionExecution.Primitives.ambient_physical_leaf_wp.
  unfold term_interp_core. iIntros "[Hstack Hown]".
  iDestruct "Hown" as (location value) "(%Hlocation & %Hchunk & Hown)".
  iPoseProof (@RegionExecution.Primitives.Model.runtime_field_read_wp _ _ Σ RG Γ F Δ
    runtime formals binders valuation store field init target base location value
    (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
    Hlocation with "[$Hstack $Hown]") as "Hwp".
  iEval (unfold RegionExecution.Primitives.Model.runtime_wp) in "Hwp".
  unfold RegionExecution.Primitives.Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iDestruct "Hpost" as (read_value) "(%Hread & Hstack & Hown)".
  iExists read_value. rewrite term_interp_rstate. iFrame "Hstack".
  unfold term_interp_core. iSplit.
  - iExists location, value. repeat iSplit; try iExact "Hown"; iPureIntro;
      rewrite interp_weaken_expr; assumption.
  - iPureIntro. simpl. unfold binder_cons. rewrite view_member_here.
    rewrite interp_weaken_expr. rewrite Hchunk. simpl.
    rewrite Hread. rewrite (proj2 (tval_eqb_eq _ value value) eq_refl).
    reflexivity.
Qed.

Lemma term_interp_expr_eq_rect {F Δ left right}
    (equality : left = right) (expression : expr F Δ left)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation) :
  interp_expr formals binders valuation
      (eq_rect left (fun t => expr F Δ t) expression right equality) =
  option_map (fun value => eq_rect left tval value right equality)
    (interp_expr formals binders valuation expression).
Proof.
  destruct equality. simpl.
  destruct (interp_expr formals binders valuation expression); reflexivity.
Qed.

(** The three allocation helpers below establish [term_interp_core] for
    fully-allocated physical fields, ghost fields, and their combination,
    each by a straightforward induction on the field list.  Stating them
    over [term_interp_core] is what lets the resource allocation rule
    appeal to the runtime primitive without passing through the
    assertion grammar. *)
Lemma term_ambient_allocated_physical_fields_rule_interp_core {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) fields address :
  @RegionExecution.Primitives.Model.allocated_physical_fields_own _ _ Σ RG Γ F Δ runtime formals
      binders valuation store (VRef address) fields ⊢
  term_interp_core formals (binder_cons (VRef address) binders)
    valuation (Hoare.ResourceHoare.allocated_physical_fields_core store fields).
Proof.
  induction fields as [|[field expression] fields IH]; simpl.
  - iIntros "_". done.
  - iIntros "Hfields". iDestruct "Hfields" as (value)
      "(%Hvalue & Hown & Hfields)". iSplitL "Hown".
    + iExists (VRef address), value. iSplit.
      { iPureIntro. simpl. unfold Core.interp_expr. simpl.
        unfold binder_cons.
        rewrite view_member_here. reflexivity. }
      iSplit; last iExact "Hown". iPureIntro.
      rewrite interp_weaken_expr. exact Hvalue.
    + iApply IH. iExact "Hfields".
Qed.

Lemma term_ambient_allocated_ghost_fields_rule_interp_core {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) address :
  @RegionExecution.Primitives.Model.allocated_ghost_fields_own _ _ Σ RG Γ F Δ runtime
      formals binders valuation store (VRef address) fields ⊢
  term_interp_core formals (binder_cons (VRef address) binders)
    valuation (Hoare.ResourceHoare.allocated_ghost_fields_core store fields).
Proof.
  induction fields as [|[resource field Hfield expression] fields IH]; simpl.
  - iIntros "_". done.
  - iIntros "Hfields". iDestruct "Hfields" as (value)
      "(%Hvalue & Hown & Hfields)". iSplitL "Hown".
    + iExists (VRef address),
        (eq_rect (TRA resource) tval (@VRA RuntimeErasure.RAValues.ra_values resource value)
          (Assertion.field_type field) (eq_sym Hfield)).
      iSplit.
      { iPureIntro. simpl. unfold Core.interp_expr. simpl.
        unfold binder_cons. rewrite view_member_here. reflexivity. }
      iSplit; last iExact "Hown". iPureIntro.
      rewrite term_interp_expr_eq_rect. rewrite interp_weaken_expr.
      unfold interp_program_expr in Hvalue. rewrite Hvalue. reflexivity.
    + iApply IH. iExact "Hfields".
Qed.

Lemma term_ambient_allocated_fields_rule_interp_core {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) fields address :
  @RegionExecution.Primitives.Model.allocated_fields_own _ _ Σ RG Γ F Δ runtime formals
      binders valuation store (VRef address) fields ⊢
  term_interp_core formals (binder_cons (VRef address) binders)
    valuation (Hoare.ResourceHoare.allocated_fields_core store fields).
Proof.
  unfold RegionExecution.Primitives.Model.allocated_fields_own,
    Hoare.ResourceHoare.allocated_fields_core.
  iIntros "[Hphysical Hghost]". iSplitL "Hphysical".
  - iApply term_ambient_allocated_physical_fields_rule_interp_core.
    iExact "Hphysical".
  - iApply term_ambient_allocated_ghost_fields_rule_interp_core. iExact "Hghost".
Qed.

Lemma term_valid_ghost_initializers_semantic_core {Γ F Δ}
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) fields :
  term_interp_core formals binders valuation
    (Hoare.ResourceHoare.ghost_initializers_valid_core store fields) ⊢
  ⌜
  @RegionExecution.Primitives.Model.ghost_initializers_semantically_valid _ _
    Γ F Δ formals binders valuation store fields⌝.
Proof.
  induction fields as [|initialization rest IH].
  - simpl. iPureIntro. constructor.
  - destruct initialization as [resource field Hfield expression].
    unfold term_interp_core. simpl. iIntros "[%Hhead Hrest]".
    iDestruct (IH with "Hrest") as %Hrest.
    iPureIntro. constructor; last exact Hrest.
    destruct Hhead as (evaluated & Hevaluated & Hvalid).
    dependent destruction evaluated.
    change (@ra_base.valid _ (ra_base.RA_inst (RuntimeLang.ra_map resource))
      value) in Hvalid.
    intros candidate Hcandidate. unfold interp_program_expr in Hcandidate.
    rewrite Hcandidate in Hevaluated. inversion Hevaluated.
    apply (Eqdep_dec.inj_pair2_eq_dec string String.string_dec) in H0.
    subst candidate. exact Hvalid.
Qed.

(** Ambient rule for ghost update, over resource telescopes.  Ghost
    update performs no physical step -- it is the same ghost frame-
    preserving update [runtime_ghost_update], just routed through
    [term_interp_rstate]/[term_interp_core] instead of
    [term_interp_assertion]. *)
Lemma term_ambient_ghost_update_rule_valid {Γ F Δ}
    (store : symbolic_store Γ F Δ) field base old_value new_value
    (entry exit : GenericRegions.Atomicity.analysis_state) :
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    term_interp_resource_prenex runtime formals binders valuation
      (Translation.Resource.RState store
        (Translation.Resource.CAnd
          (Translation.Resource.CGhostOwn field
            (IR.symbolize_expr store base)
            (IR.symbolize_expr store old_value))
          (Translation.Resource.CFpuAllowed (Assertion.field_type field)
            (IR.symbolize_expr store old_value)
            (IR.symbolize_expr store new_value)))) ⊢
    concrete_operation_wp runtime ambient entry
      (TGhostUpdate field base old_value new_value) exit
      (term_interp_resource_prenex runtime formals binders valuation
        (Translation.Resource.RState store
          (Translation.Resource.CGhostOwn field
            (IR.symbolize_expr store base)
            (IR.symbolize_expr store new_value)))).
Proof.
  intros runtime formals binders valuation ambient.
  rewrite !term_interp_rstate.
  unfold concrete_operation_wp, RegionExecution.Primitives.operation_wp.
  simpl. unfold RegionExecution.Primitives.ambient_leaf_wp. simpl.
  unfold term_interp_core. iIntros "[Hstack [Hown %Hallowed]]".
  iDestruct "Hown" as (location old_chunk) "(%Hlocation & %Hold & Hown)".
  destruct Hallowed as (allowed_old & allowed_new & Hallowed_old &
    Hallowed_new & Hallowed).
  have Heq_old : Some old_chunk = Some allowed_old.
  { etrans; [symmetry; exact Hold|exact Hallowed_old]. }
  inversion Heq_old; subst old_chunk.
  iMod (runtime_ghost_update
    (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
    field location allowed_old allowed_new Hallowed with "Hown") as "Hown".
  iModIntro. iFrame "Hstack". iExists location, allowed_new.
  iFrame "Hown". iPureIntro. split; assumption.
Qed.


(* ------------------------------------------------------------------ *)
(** ** Resource validity slice, ambient leaves

    One representative per rule family, stated over
    [term_interp_resource_prenex].  Assignment is proved outright; the
    fold/unfold pair takes the leaf contract's instantiation equivalence
    as a premise, discharged by
    [TermLeaf.term_predicate_instantiation_valid] (see
    [term_interp_core_instantiated_predicate] below). *)

Lemma term_ambient_assignment_rule_valid {Γ F Δ t}
    (store : symbolic_store Γ F Δ) {init} (target : write_target init Γ t)
    (expression : rexpr Γ t)
    (entry exit : GenericRegions.Atomicity.analysis_state) :
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    term_interp_resource_prenex runtime formals binders valuation
      (Translation.Resource.RState store
        (Translation.Resource.CPure True)) ⊢
    concrete_operation_wp runtime ambient entry
      (TAssign init target expression) exit
      (term_interp_resource_prenex runtime formals binders valuation
        (Translation.Resource.ResourceExists t
          (Translation.Resource.RState
            (IR.update_store_with_bound store target)
            (Translation.Resource.CExpr
              (EBinOp (BEq t) (ERef (RefBound MHere))
                (Translation.Assertions.weaken_expr
                  (IR.symbolize_expr store expression))))))).
Proof.
  intros runtime formals binders valuation ambient.
  rewrite term_interp_rstate term_interp_resource_exists.
  unfold concrete_operation_wp, RegionExecution.Primitives.operation_wp.
  simpl. unfold RegionExecution.Primitives.ambient_leaf_wp.
  simpl. unfold RegionExecution.Primitives.ambient_physical_leaf_wp.
  iIntros "[Hstack _]".
  iPoseProof (@RegionExecution.Primitives.Model.runtime_assignment_wp _ _ Σ RG
    Γ F Δ t runtime formals binders valuation store init target expression
    (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
    with "Hstack") as "Hwp".
  iEval (unfold RegionExecution.Primitives.Model.runtime_wp) in "Hwp".
  unfold RegionExecution.Primitives.Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iDestruct "Hpost" as (value) "[%Hvalue Hstack]".
  iExists value. rewrite term_interp_rstate. iFrame. iPureIntro.
  simpl. unfold binder_cons. rewrite view_member_here.
  rewrite interp_weaken_expr.
  unfold interp_program_expr in Hvalue. rewrite Hvalue. simpl.
  rewrite (proj2 (tval_eqb_eq t value value) eq_refl). reflexivity.
Qed.

Lemma term_ambient_predicate_unfold_rule_valid {Γ F Δ}
    predicate arguments (store : symbolic_store Γ F Δ)
    (body : Translation.Resource.core_assertion F Δ)
    (entry exit : GenericRegions.Atomicity.analysis_state) :
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    term_interp_core formals binders valuation body ≡
      term_interp_core formals binders valuation
        (Translation.Resource.CPredicate predicate
          (IR.symbolize_expr_list store arguments)) ->
    term_interp_resource_prenex runtime formals binders valuation
      (Translation.Resource.RState store
        (Translation.Resource.CPredicate predicate
          (IR.symbolize_expr_list store arguments))) ⊢
    concrete_operation_wp runtime ambient entry
      (TPredicateUnfold predicate arguments) exit
      (term_interp_resource_prenex runtime formals binders valuation
        (Translation.Resource.RState store body)).
Proof.
  intros runtime formals binders valuation ambient Hinstantiation.
  rewrite !term_interp_rstate.
  unfold concrete_operation_wp, RegionExecution.Primitives.operation_wp.
  simpl. iIntros "[Hstack Hpredicate]". iFrame "Hstack".
  iApply (bi.equiv_entails_1_2 _ _ Hinstantiation). iExact "Hpredicate".
Qed.

Lemma term_ambient_predicate_fold_rule_valid {Γ F Δ}
    predicate arguments (store : symbolic_store Γ F Δ)
    (body : Translation.Resource.core_assertion F Δ)
    (entry exit : GenericRegions.Atomicity.analysis_state) :
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    term_interp_core formals binders valuation body ≡
      term_interp_core formals binders valuation
        (Translation.Resource.CPredicate predicate
          (IR.symbolize_expr_list store arguments)) ->
    term_interp_resource_prenex runtime formals binders valuation
      (Translation.Resource.RState store body) ⊢
    concrete_operation_wp runtime ambient entry
      (TPredicateFold predicate arguments) exit
      (term_interp_resource_prenex runtime formals binders valuation
        (Translation.Resource.RState store
          (Translation.Resource.CPredicate predicate
            (IR.symbolize_expr_list store arguments)))).
Proof.
  intros runtime formals binders valuation ambient Hinstantiation.
  rewrite !term_interp_rstate.
  unfold concrete_operation_wp, RegionExecution.Primitives.operation_wp.
  simpl. iIntros "[Hstack Hbody]". iFrame "Hstack".
  iApply (bi.equiv_entails_1_1 _ _ Hinstantiation). iExact "Hbody".
Qed.


(** Structured certificates are interpreted directly by the configured
    runtime model, using this module's single [semantic_data] instance. *)
Definition term_structured_runtime_wp
    {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (ambient : coPset) (post : iProp) : iProp :=
  translated_runtime_wp runtime ambient entry exit statement post.

(** Structured validity, over resource telescopes.  The certificate and
    its runtime weakest precondition are unchanged from
    [term_structured_runtime_wp]; only the pre- and post-conditions move
    to the resource representation. *)
Definition term_structured_runtime_valid
    {Γ F Δ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (pre post : Translation.Resource.resource_prenex Γ F Δ) : Prop :=
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint certificate ∪
        term_registered_invariants) ⊆ ambient ->
    (global_world_context valuation ∗
      term_interp_resource_prenex runtime formals binders valuation pre) ⊢
    term_structured_runtime_wp certificate runtime ambient
      (global_world_context valuation ∗
        term_interp_resource_prenex runtime formals binders valuation post).

(** [conditions] are true in every store in which [pinned] evaluates to
    [values]. *)
Definition conditions_hold {Γ ts} (conditions : list (gexpr Γ TBool))
    (pinned : gexpr_list Γ ts) (values : tval_list ts) : Prop :=
  forall F Δ (store : symbolic_store Γ F Δ) (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation),
  interp_expr_list formals binders valuation
    (IR.symbolize_expr_list store pinned) = Some values ->
  Forall (fun condition =>
    interp_expr formals binders valuation
      (IR.symbolize_expr store condition) = Some (VBool true)) conditions.

Lemma conditions_hold_nil {Γ ts} (pinned : gexpr_list Γ ts)
    (values : tval_list ts) :
  conditions_hold [] pinned values.
Proof. intros. constructor. Qed.

(** Parametric strengthening used by matched invariant accesses.  For every
    vector whose stack dependencies the statement does not write, the
    certificate transports its evaluated value through the actual telescope
    witnesses selected at run time.  The instances open in enclosing
    accesses are held alongside: their arguments are pinned after the
    vector's, and the rest of their worlds is framed through.  The
    [conditions] are known to hold wherever the pinned vector has its
    values. *)
Definition term_structured_runtime_arguments_valid
    {Γ F Δ entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (conditions : list (gexpr Γ TBool))
    (arguments : gexpr_list Γ ts)
    (pre post : Translation.Resource.resource_prenex Γ F Δ) : Prop :=
  forall types (held : held_list Γ ts types),
  held_aligned (GenericRegions.Atomicity.analysis_records entry) held ->
  Hoare.ResourceHoare.pexpr_list_dependencies (held_pinned arguments held) ##
      Hoare.ResourceHoare.statement_writes statement ->
  forall (values : tval_list ts)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint certificate ∪
        term_registered_invariants) ⊆ ambient ->
    conditions_hold conditions (held_pinned arguments held)
      (held_pinned_values values held) ->
    (global_world_context valuation ∗ held_world valuation held ∗
      term_interp_resource_prenex_at_arguments runtime formals binders valuation
        (held_pinned arguments held) (held_pinned_values values held) pre) ⊢
    term_structured_runtime_wp certificate runtime ambient
      (global_world_context valuation ∗ held_world valuation held ∗
       term_interp_resource_prenex_at_arguments runtime formals binders valuation
         (held_pinned arguments held) (held_pinned_values values held) post).

Lemma fold_after_open_access_records invariant key key' excluded outer opened
    inner :
  GenericRegions.Atomicity.open_access invariant key excluded outer =
    inr opened ->
  GenericRegions.Atomicity.analysis_records inner =
    GenericRegions.Atomicity.analysis_records opened ->
  GenericRegions.Atomicity.analysis_records
    (GenericRegions.Atomicity.fold_invariant invariant key' inner) =
    GenericRegions.Atomicity.analysis_records outer.
Proof.
  intros Hopen Hinner.
  destruct (GenericRegions.Atomicity.open_access_records _ _ _ _ _ Hopen)
    as (entry & ->).
  cbn [GenericRegions.Atomicity.analysis_records] in Hinner.
  rewrite (GenericRegions.Atomicity.fold_invariant_closes _ _ _ _ _ Hinner
    eq_refl). reflexivity.
Qed.

Lemma term_structured_certificate_preserves_records
    {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit) :
  GenericRegions.Atomicity.analysis_records exit =
    GenericRegions.Atomicity.analysis_records entry.
Proof.
  induction certificate; simpl.
  - eapply GenericRegions.Atomicity.take_leaf_preserves_records; eauto.
  - reflexivity.
  - apply GenericRegions.Atomicity.fold_fresh_records. exact n.
  - etrans; eauto.
  - exact IHcertificate1.
  - rewrite e0.
    eapply GenericRegions.Atomicity.take_step_preserves_records; eauto.
  - eapply fold_after_open_access_records; eauto.
  - exact IHcertificate.
  - exact IHcertificate1.
Qed.

Lemma term_structured_certificate_preserves_open
    {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit) :
  GenericRegions.Atomicity.analysis_open exit =
    GenericRegions.Atomicity.analysis_open entry.
Proof.
  apply GenericRegions.Atomicity.analysis_open_records.
  exact (term_structured_certificate_preserves_records certificate).
Qed.

Lemma term_invariant_namespace_active_from_footprint
    {Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      Γ entry statement exit)
    ambient invariant :
  invariant ∈ GenericRegions.Atomicity.certificate_footprint certificate ->
  invariant ∉ GenericRegions.Atomicity.analysis_open entry ->
  RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint certificate) ⊆ ambient ->
  ↑(invariant_namespace invariant) ⊆
    RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
Proof.
  intros Hfootprint Hnot_open Henvelope.
  have Hnamespace : ↑(invariant_namespace invariant) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.invariant_namespace_subset_runtime_mask. exact Hfootprint. }
  have Hdisjoint : (↑(invariant_namespace invariant) : coPset) ##
      RegionExecution.Primitives.Model.invariant_mask (GenericRegions.Atomicity.analysis_open entry).
  { apply RegionExecution.Primitives.Model.invariant_mask_disjoint. exact Hnot_open. }
  unfold RegionExecution.Primitives.Model.active_runtime_mask, RegionExecution.Primitives.Model.enabled_runtime_mask.
  intros namespace Hnamespace_member.
  change (namespace ∈ ambient ∖
    RegionExecution.Primitives.Model.invariant_mask
      (GenericRegions.Atomicity.analysis_open entry)).
  apply elem_of_difference.
  split.
  - exact (Hnamespace namespace Hnamespace_member).
  - intro Hinvariant_mask.
    exact (Hdisjoint namespace Hnamespace_member Hinvariant_mask).
Qed.

Lemma term_invariant_fresh_fold_node_valid {Γ F Δ} invariant arguments
    (store : symbolic_store Γ F Δ)
    (entry : GenericRegions.Atomicity.analysis_state) ambient :
  invariant ∉ GenericRegions.Atomicity.analysis_open entry ->
  invariant ∈ term_registered_invariants  ->
  ↑(invariant_namespace invariant) ⊆
    RegionExecution.Primitives.Model.active_runtime_mask ambient entry ->
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation),
  (global_world_context valuation ∗
   term_interp_resource_prenex runtime formals binders valuation
     (Translation.Resource.RState store
       (ResourceInstances.instantiated_invariant invariant
         (IR.symbolize_expr_list store arguments)))) ⊢
  concrete_operation_wp runtime ambient entry
    (TFold invariant arguments)
    (GenericRegions.Atomicity.fold_invariant invariant
        (RegionSyntax.argument_key arguments) entry)
    (global_world_context valuation ∗
     term_interp_resource_prenex runtime formals binders valuation
       (Translation.Resource.RState store
         (Translation.Resource.CInvariant invariant
           (IR.symbolize_expr_list store arguments)))).
Proof.
  intros Hfresh Hregistered Hnamespace runtime formals binders valuation.
  destruct (term_invariant_definition_compatible formals binders valuation
    invariant (IR.symbolize_expr_list store arguments))
    as (values & Harguments & Hbody_core).
  have Hfold_facts := GenericRegions.Atomicity.fold_fresh_invariant
    invariant (RegionSyntax.argument_key arguments) entry Hfresh.
  destruct Hfold_facts as [_ Hfold_open].
  have Hactive : RegionExecution.Primitives.Model.active_runtime_mask ambient
      (GenericRegions.Atomicity.fold_invariant invariant
        (RegionSyntax.argument_key arguments) entry) =
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
  { apply RegionExecution.Primitives.Model.active_runtime_mask_same_open.
    exact Hfold_open. }
  unfold concrete_operation_wp, RegionExecution.Primitives.operation_wp.
  unfold RegionSyntax.view. simpl.
  rewrite !term_interp_rstate.
  iIntros "[#Hglobal [Hstack Hbody]]".
  iPoseProof "Hglobal" as "#Hglobal_saved".
  iEval (unfold global_world_context) in "Hglobal".
  iDestruct "Hglobal" as "[#Hworlds [#Hchunks #Hprocedures]]".
  iDestruct "Hbody" as "Hbody".
  iPoseProof (bi.equiv_entails_1_1 _ _ Hbody_core with "Hbody") as "Hbody".
  iPoseProof (term_world_context_lookup valuation invariant Hregistered
    with "Hworlds") as "#Hworld".
  iMod (term_world_establish valuation invariant values
    (RegionExecution.Primitives.Model.active_runtime_mask ambient entry) Hnamespace
    with "Hworld Hbody") as "#Htoken".
  iApply fupd_mask_intro.
  { intros namespace Hnamespace_member.
    change (namespace ∈ ambient ∖
      RegionExecution.Primitives.Model.invariant_mask
        (GenericRegions.Atomicity.analysis_open
          (GenericRegions.Atomicity.fold_invariant invariant
        (RegionSyntax.argument_key arguments) entry)))
      in Hnamespace_member.
    change (namespace ∈ ambient ∖
      RegionExecution.Primitives.Model.invariant_mask
        (GenericRegions.Atomicity.analysis_open entry)).
    rewrite Hfold_open in Hnamespace_member. exact Hnamespace_member. }
  iIntros "Hclose". iClear "Hclose".
  iFrame "Hglobal_saved Hstack". iExists values.
  iFrame "Htoken". iPureIntro. exact Harguments.
Qed.

Lemma term_translated_runtime_wp_sequence {Γ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    ambient entry middle exit (first second : stmt Γ) (post : iProp)
    (Hopen : GenericRegions.Atomicity.analysis_open entry =
      GenericRegions.Atomicity.analysis_open middle) :
  translated_runtime_wp runtime ambient entry middle first
      (translated_runtime_wp runtime ambient middle exit second post) ⊢
    translated_runtime_wp runtime ambient entry exit
      (TSeq first second) post.
Proof.
  unfold translated_runtime_wp. simpl.
  unfold RegionExecution.Primitives.Model.active_runtime_mask. rewrite Hopen.
  apply runtime_masked_wp_seq.
Qed.

Lemma term_leaf_operation_to_translated {Γ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    ambient entry exit (statement : stmt Γ) (post : iProp)
    (Hview : RegionSyntax.view statement = AnalysisView.ViewLeaf)
    (Hopen : GenericRegions.Atomicity.analysis_open entry =
      GenericRegions.Atomicity.analysis_open exit) :
  concrete_operation_wp runtime ambient entry statement exit post ⊢
    translated_runtime_wp runtime ambient entry exit statement post.
Proof.
  have Hactive : RegionExecution.Primitives.Model.active_runtime_mask
      ambient exit =
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
  { symmetry. apply RegionExecution.Primitives.active_runtime_mask_same_open.
    exact Hopen. }
  destruct statement.
  all: simpl in Hview; try discriminate.
  all: try (exfalso; guarded_view_cases; fail).
  all: unfold concrete_operation_wp.
  all: unfold RegionExecution.Primitives.operation_wp; simpl.
  all: unfold translated_runtime_wp; simpl.
  all: try destruct target; simpl.
  all: unfold RegionExecution.Primitives.ambient_physical_leaf_wp.
  all: try (rewrite runtime_masked_wp_noop_eq; [|reflexivity]).
  all: try unfold runtime_masked_wp.
  all: try rewrite Hactive.
  all: try (iIntros "Hwp"; iApply (wp_mono with "Hwp");
    iIntros (result) "[%Hresult Hpost]"; iSplit; first done;
    iModIntro; iExact "Hpost").
  all: try (iIntros "Hpost"; iMod "Hpost"; iModIntro; iExact "Hpost").
  all: iIntros "Hpost".
  all: try iExact "Hpost".
  all: try iExact "Hpost".
  all: iModIntro; iExact "Hpost".
Qed.


Lemma translated_runtime_wp_default_arm {Γ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) ambient entry exit
    (statement : stmt Γ) post :
  translated_runtime_wp runtime ambient entry exit statement post ⊢
  @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
    (@RuntimeErasure.runtime_stmt _ _ Γ (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) statement)
    (fun result =>
      (⌜result = RuntimeLang.LitUnit⌝ ∗
       |={RegionExecution.Primitives.Model.active_runtime_mask ambient entry,
          RegionExecution.Primitives.Model.active_runtime_mask ambient exit}=> post)%I).
Proof. reflexivity. Qed.

Lemma runtime_condition_step {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (condition : rexpr Γ TBool) b :
  interp_expr formals binders valuation
    (IR.symbolize_expr store condition) = Some (VBool b) ->
  RuntimeLang.expr_step
    (@RuntimeErasure.runtime_expr _ Γ _ _ (RegionExecution.Primitives.Model.runtime_names Γ runtime) condition)
    (RuntimeLang.StackFrame
      (@RegionExecution.Primitives.Model.concrete_locals _ Γ (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (interp_store formals binders valuation store)))
    (RuntimeLang.Val (@RuntimeErasure.tval_to_val _ TBool (VBool b))).
Proof.
  intros Hcondition. eapply RuntimeErasure.runtime_expr_sound.
  - apply RegionExecution.Primitives.Model.runtime_stack_frame_corresponds.
  - exact Hcondition.
Qed.

Lemma runtime_wp_if_true {Γ} (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    frame (condition : rexpr Γ TBool) then_runtime else_runtime mask
    (P : iProp) (Phi : RuntimeLang.val -> iProp) :
  RuntimeLang.expr_step
    (@RuntimeErasure.runtime_expr _ Γ _ _ (RegionExecution.Primitives.Model.runtime_names Γ runtime) condition) frame
    (RuntimeLang.Val (RuntimeLang.LitBool true)) ->
  (RuntimeGhost.stack_frame_own (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) frame ∗ P ⊢
    @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG mask then_runtime Phi) ->
  RuntimeGhost.stack_frame_own (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) frame ∗ P ⊢
    @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG mask
      (RuntimeLang.RTIfS
        (@RuntimeErasure.runtime_expr _ Γ _ _ (RegionExecution.Primitives.Model.runtime_names Γ runtime) condition)
        then_runtime else_runtime (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)) Phi.
Proof.
  intros Hcondition Hthen. iIntros "Hresources". unfold RegionExecution.Primitives.Model.runtime_wp.
  iApply (RuntimeLifting.wp_if_t_wp _ _ _ _ frame P Phi mask Hcondition
    with "[] Hresources").
  iIntros "Hresources". iPoseProof (Hthen with "Hresources") as "Hwp".
  iExact "Hwp".
Qed.

Lemma runtime_wp_if_false {Γ} (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    frame (condition : rexpr Γ TBool) then_runtime else_runtime mask
    (P : iProp) (Phi : RuntimeLang.val -> iProp) :
  RuntimeLang.expr_step
    (@RuntimeErasure.runtime_expr _ Γ _ _ (RegionExecution.Primitives.Model.runtime_names Γ runtime) condition) frame
    (RuntimeLang.Val (RuntimeLang.LitBool false)) ->
  (RuntimeGhost.stack_frame_own (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) frame ∗ P ⊢
    @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG mask else_runtime Phi) ->
  RuntimeGhost.stack_frame_own (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) frame ∗ P ⊢
    @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG mask
      (RuntimeLang.RTIfS
        (@RuntimeErasure.runtime_expr _ Γ _ _ (RegionExecution.Primitives.Model.runtime_names Γ runtime) condition)
        then_runtime else_runtime (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)) Phi.
Proof.
  intros Hcondition Helse. iIntros "Hresources". unfold RegionExecution.Primitives.Model.runtime_wp.
  iApply (RuntimeLifting.wp_if_f_wp _ _ _ _ frame P Phi mask Hcondition
    with "[] Hresources").
  iIntros "Hresources". iPoseProof (Helse with "Hresources") as "Hwp".
  iExact "Hwp".
Qed.

Lemma conditional_then_active_mask_join ambient then_exit else_exit :
  RegionExecution.Primitives.Model.active_runtime_mask ambient then_exit =
    RegionExecution.Primitives.Model.active_runtime_mask ambient
      (GenericRegions.Atomicity.join_state then_exit else_exit).
Proof. apply RegionExecution.Primitives.Model.active_runtime_mask_same_open. reflexivity. Qed.

Lemma conditional_else_active_mask_join ambient then_exit else_exit :
  GenericRegions.Atomicity.analysis_records then_exit =
    GenericRegions.Atomicity.analysis_records else_exit ->
  RegionExecution.Primitives.Model.active_runtime_mask ambient else_exit =
    RegionExecution.Primitives.Model.active_runtime_mask ambient
      (GenericRegions.Atomicity.join_state then_exit else_exit).
Proof.
  intros Hrecords.
  apply RegionExecution.Primitives.Model.active_runtime_mask_same_open.
  apply GenericRegions.Atomicity.analysis_open_records.
  symmetry. exact Hrecords.
Qed.

Lemma translated_runtime_wp_if {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) ambient entry exit condition
    (then_branch else_branch : stmt Γ) post P b :
  interp_expr formals binders valuation
    (IR.symbolize_expr store condition) = Some (VBool b) ->
  (@RegionExecution.Primitives.Model.core_stack_own _ _ Σ RG Γ runtime (interp_store formals binders valuation store) ∗ P ⊢
    translated_runtime_wp runtime ambient entry exit
      (if b then then_branch else else_branch) post) ->
  @RegionExecution.Primitives.Model.core_stack_own _ _ Σ RG Γ runtime (interp_store formals binders valuation store) ∗ P ⊢
    translated_runtime_wp runtime ambient entry exit
      (TIf condition then_branch else_branch) post.
Proof.
  intros Hcondition Hselected.
  unfold translated_runtime_wp.
  cbn [RuntimeErasure.runtime_stmt].
  match goal with
  | |- ?lhs ⊢ runtime_masked_wp ?entry_mask ?exit_mask _ ?q =>
      apply (RuntimeErasure.runtime_if_ind
        (fun combined => lhs ⊢
          runtime_masked_wp entry_mask exit_mask combined q))
  end.
  - (* both arms proof-only: the conditional is erased entirely *)
    intros Hthen Helse. etrans; [exact Hselected|].
    rewrite runtime_masked_wp_noop.
    destruct b; cbv iota; unfold translated_runtime_wp;
      [rewrite (runtime_masked_wp_noop_eq _ _ _ _ Hthen)
      |rewrite (runtime_masked_wp_noop_eq _ _ _ _ Helse)];
      reflexivity.
  - intros _. unfold runtime_masked_wp. destruct b.
    + eapply runtime_wp_if_true; [|exact Hselected].
      exact (runtime_condition_step runtime formals binders valuation store
        condition true Hcondition).
    + eapply runtime_wp_if_false; [|exact Hselected].
      exact (runtime_condition_step runtime formals binders valuation store
        condition false Hcondition).
Qed.

Corollary translated_runtime_wp_if_total {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) ambient entry exit condition
    (then_branch else_branch : stmt Γ) post P :
  (interp_expr formals binders valuation
      (IR.symbolize_expr store condition) = Some (VBool true) ->
    @RegionExecution.Primitives.Model.core_stack_own _ _ Σ RG Γ runtime (interp_store formals binders valuation store) ∗ P ⊢
      translated_runtime_wp runtime ambient entry exit then_branch post) ->
  (interp_expr formals binders valuation
      (IR.symbolize_expr store condition) = Some (VBool false) ->
    @RegionExecution.Primitives.Model.core_stack_own _ _ Σ RG Γ runtime (interp_store formals binders valuation store) ∗ P ⊢
      translated_runtime_wp runtime ambient entry exit else_branch post) ->
  @RegionExecution.Primitives.Model.core_stack_own _ _ Σ RG Γ runtime (interp_store formals binders valuation store) ∗ P ⊢
    translated_runtime_wp runtime ambient entry exit
      (TIf condition then_branch else_branch) post.
Proof.
  intros Hthen Helse.
  destruct (interp_expr_total formals binders valuation
    (IR.symbolize_expr store condition)) as [value Hvalue].
  dependent destruction value. destruct b.
  - eapply translated_runtime_wp_if; [exact Hvalue|apply Hthen; exact Hvalue].
  - eapply translated_runtime_wp_if; [exact Hvalue|apply Helse; exact Hvalue].
Qed.

Lemma translated_runtime_wp_then_join_transport {Γ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) ambient state then_exit else_exit
    statement post :
  translated_runtime_wp runtime ambient state then_exit statement post ⊣⊢
    translated_runtime_wp runtime ambient state
      (GenericRegions.Atomicity.join_state then_exit else_exit)
      statement post.
Proof.
  unfold translated_runtime_wp.
  rewrite (conditional_then_active_mask_join ambient then_exit else_exit).
  reflexivity.
Qed.

Lemma translated_runtime_wp_else_join_transport {Γ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) ambient state then_exit else_exit
    statement post :
  GenericRegions.Atomicity.analysis_records then_exit =
    GenericRegions.Atomicity.analysis_records else_exit ->
  translated_runtime_wp runtime ambient state else_exit statement post ⊣⊢
    translated_runtime_wp runtime ambient state
      (GenericRegions.Atomicity.join_state then_exit else_exit)
      statement post.
Proof.
  intros Hopen. unfold translated_runtime_wp.
  rewrite (conditional_else_active_mask_join ambient then_exit else_exit Hopen).
  reflexivity.
Qed.

Lemma translated_runtime_wp_if_total_join {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) ambient state condition
    (then_branch else_branch : stmt Γ) then_exit else_exit post P
    (records_equal : GenericRegions.Atomicity.analysis_records then_exit =
      GenericRegions.Atomicity.analysis_records else_exit) :
  (interp_expr formals binders valuation
      (IR.symbolize_expr store condition) = Some (VBool true) ->
    @RegionExecution.Primitives.Model.core_stack_own _ _ Σ RG Γ runtime (interp_store formals binders valuation store) ∗ P ⊢
      translated_runtime_wp runtime ambient state then_exit
        then_branch post) ->
  (interp_expr formals binders valuation
      (IR.symbolize_expr store condition) = Some (VBool false) ->
    @RegionExecution.Primitives.Model.core_stack_own _ _ Σ RG Γ runtime (interp_store formals binders valuation store) ∗ P ⊢
      translated_runtime_wp runtime ambient state else_exit
        else_branch post) ->
  @RegionExecution.Primitives.Model.core_stack_own _ _ Σ RG Γ runtime (interp_store formals binders valuation store) ∗ P ⊢
    translated_runtime_wp runtime ambient state
      (GenericRegions.Atomicity.join_state then_exit else_exit)
      (TIf condition then_branch else_branch) post.
Proof.
  intros Hthen Helse. eapply translated_runtime_wp_if_total.
  - intros Hcondition. rewrite <- translated_runtime_wp_then_join_transport.
    now apply Hthen.
  - intros Hcondition.
    rewrite <- (translated_runtime_wp_else_join_transport
      runtime ambient state then_exit else_exit else_branch post records_equal).
    now apply Helse.
Qed.



(** A ghost conditional erases to nothing: its wp is that of the branch
    its guard selects. *)
Lemma translated_runtime_wp_ghost_if_total_join {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) ambient state condition
    (then_branch else_branch : stmt Γ) then_exit else_exit post P
    (records_equal : GenericRegions.Atomicity.analysis_records then_exit =
      GenericRegions.Atomicity.analysis_records else_exit) :
  proof_onlyb then_branch = true ->
  proof_onlyb else_branch = true ->
  (interp_expr formals binders valuation
      (IR.symbolize_expr store condition) = Some (VBool true) ->
    @RegionExecution.Primitives.Model.core_stack_own _ _ Σ RG Γ runtime (interp_store formals binders valuation store) ∗ P ⊢
      translated_runtime_wp runtime ambient state then_exit
        then_branch post) ->
  (interp_expr formals binders valuation
      (IR.symbolize_expr store condition) = Some (VBool false) ->
    @RegionExecution.Primitives.Model.core_stack_own _ _ Σ RG Γ runtime (interp_store formals binders valuation store) ∗ P ⊢
      translated_runtime_wp runtime ambient state else_exit
        else_branch post) ->
  @RegionExecution.Primitives.Model.core_stack_own _ _ Σ RG Γ runtime (interp_store formals binders valuation store) ∗ P ⊢
    translated_runtime_wp runtime ambient state
      (GenericRegions.Atomicity.join_state then_exit else_exit)
      (TGhostIf condition then_branch else_branch) post.
Proof.
  intros Hthen_proof Helse_proof Hthen Helse.
  destruct (interp_expr_total formals binders valuation
    (IR.symbolize_expr store condition)) as [value Hvalue].
  dependent destruction value. destruct b.
  - rewrite (term_translated_runtime_wp_runtime_stmt_ext runtime ambient state _
      (TGhostIf condition then_branch else_branch) then_branch post).
    + rewrite <- translated_runtime_wp_then_join_transport.
      apply Hthen. exact Hvalue.
    + cbn [RuntimeErasure.runtime_stmt].
      rewrite RuntimeErasure.runtime_stmt_proof_only; [reflexivity|exact Hthen_proof].
  - rewrite (term_translated_runtime_wp_runtime_stmt_ext runtime ambient state _
      (TGhostIf condition then_branch else_branch) else_branch post).
    + rewrite <- (translated_runtime_wp_else_join_transport runtime ambient state
        then_exit else_exit else_branch post records_equal).
      apply Helse. exact Hvalue.
    + cbn [RuntimeErasure.runtime_stmt].
      rewrite RuntimeErasure.runtime_stmt_proof_only; [reflexivity|exact Helse_proof].
Qed.

Lemma term_structured_runtime_fresh_fold_valid {Γ F Δ entry invariant
    arguments} {store : symbolic_store Γ F Δ}
    (Hfresh : invariant ∉ GenericRegions.Atomicity.analysis_open entry)
    (Hregistered : invariant ∈ term_registered_invariants ) :
  term_structured_runtime_valid
    (Structured.StructuredFreshFold Γ entry invariant arguments Hfresh)
    (Translation.Resource.RState store
      (ResourceInstances.instantiated_invariant invariant
        (IR.symbolize_expr_list store arguments)))
    (Translation.Resource.RState store
      (Translation.Resource.CInvariant invariant
        (IR.symbolize_expr_list store arguments))).
Proof.
  intros runtime formals binders valuation ambient Henvelope.
  pose (raw := GenericRegions.Atomicity.CertFold Γ entry
    (TFold invariant arguments) invariant (RegionSyntax.argument_key arguments)
    eq_refl (GenericRegions.Atomicity.fold_admissible_fresh _ _ _ Hfresh)).
  have Hraw_envelope : RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint raw) ⊆ ambient.
  { etrans; last exact Henvelope. apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros candidate Hin. apply elem_of_union_l.
    simpl in Hin |- *. repeat rewrite elem_of_union in *.
    tauto. }
  have Hexit_member : invariant ∈ GenericRegions.Atomicity.analysis_mask
      (GenericRegions.Atomicity.fold_invariant invariant
        (RegionSyntax.argument_key arguments) entry).
  { rewrite Certified.fold_analysis_mask; [set_solver | exact Hfresh]. }
  have Hfootprint : invariant ∈
      GenericRegions.Atomicity.certificate_footprint raw.
  { apply GenericRegions.Atomicity.certificate_exit_subset_footprint.
    exact Hexit_member. }
  have Hnamespace := term_invariant_namespace_active_from_footprint raw ambient
    invariant Hfootprint Hfresh Hraw_envelope.
  unfold term_structured_runtime_wp.
  iIntros "[Hglobal Hpre]".
  iPoseProof (term_invariant_fresh_fold_node_valid invariant
    arguments store entry ambient Hfresh Hregistered Hnamespace runtime
    formals binders valuation with "[$Hglobal $Hpre]") as "Hwp".
  iEval (unfold concrete_operation_wp,
    RegionExecution.Primitives.operation_wp, RegionSyntax.view) in "Hwp".
  rewrite translated_runtime_wp_erased; [|reflexivity]. iExact "Hwp".
Qed.

Lemma term_structured_invariant_namespace_active_from_footprint
    {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit) ambient invariant :
  invariant ∈ GenericRegions.Atomicity.analysis_mask entry ->
  invariant ∉ GenericRegions.Atomicity.analysis_open entry ->
  RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint certificate) ⊆ ambient ->
  ↑(invariant_namespace invariant) ⊆
    RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
Proof.
  intros Hmask Hopen Henvelope.
  have Hnamespace : ↑(invariant_namespace invariant) ⊆ ambient.
  { etrans; last exact Henvelope. etrans.
    - apply RegionExecution.Primitives.Model.invariant_namespace_subset_runtime_mask.
      apply (Structured.structured_certificate_entry_subset_footprint
        certificate). exact Hmask.
    - reflexivity. }
  have Hdisjoint : (↑(invariant_namespace invariant) : coPset) ##
      RegionExecution.Primitives.Model.invariant_mask (GenericRegions.Atomicity.analysis_open entry).
  { apply RegionExecution.Primitives.Model.invariant_mask_disjoint. exact Hopen. }
  intros namespace Hnamespace_member.
  change (namespace ∈ ambient ∖
    RegionExecution.Primitives.Model.invariant_mask
      (GenericRegions.Atomicity.analysis_open entry)).
  apply elem_of_difference. split.
  - exact (Hnamespace namespace Hnamespace_member).
  - intro Hinvariant_mask.
    exact (Hdisjoint namespace Hnamespace_member Hinvariant_mask).
Qed.

Lemma interp_store_equal_under {Γ F Δ}
    (body : Translation.Resource.core_assertion F Δ)
    (store store' : symbolic_store Γ F Δ)
    (Hstore : Hoare.ResourceHoare.store_equal_under body Γ store' store)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation) :
  term_interp_core formals binders valuation body ⊢
    ⌜interp_store formals binders valuation store' =
     interp_store formals binders valuation store⌝.
Proof.
  induction Hstore.
  - iIntros "_". iPureIntro. reflexivity.
  - have Hhead : (term_interp_core formals binders valuation body ⊢
        ⌜interp_ref formals binders valuation left =
         interp_ref formals binders valuation right⌝)%I.
    { iIntros "Hbody".
      iPoseProof (Validation.TermSemantics.core_entails_valid semantic_data
        (term_predicates valuation) _ _ H formals binders valuation with "Hbody")
        as "%Hequal".
      iPureIntro.
      cbn [Translation.TermSemantics.interp_core interp_expr interp_binop]
        in Hequal.
      apply tval_eqb_eq.
      destruct (tval_eqb (decl_type d) (interp_ref formals binders valuation left)
        (interp_ref formals binders valuation right)) eqn:Hbool.
      + reflexivity.
      + first [ discriminate Hequal | inversion Hequal | congruence ]. }
    iIntros "Hbody".
    iAssert (⌜interp_ref formals binders valuation left =
               interp_ref formals binders valuation right⌝ ∧
             ⌜interp_store formals binders valuation left_tail =
               interp_store formals binders valuation right_tail⌝)%I
      with "[Hbody]" as "[%Hhead' %Htail]".
    { iSplit.
      - iApply Hhead. iExact "Hbody".
      - iApply IHHstore. iExact "Hbody". }
    iPureIntro. simpl. rewrite Hhead' Htail. reflexivity.
Qed.

(** Opening-side interpretation for the canonical independent access.  It
    extends the caller's semantic vector with the values at which the
    invariant is opened.  Thus the body induction can preserve both vectors
    in one invocation, without equating symbolic telescope witnesses. *)
Lemma interp_expr_list_cons_inv {F Δ t ts} (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (expression : expr F Δ t) (expressions : expr_list F Δ ts)
    (values : tval_list (t :: ts)) :
  interp_expr_list formals binders valuation (ExprCons expression expressions) =
    Some values ->
  exists value rest, values = TVCons value rest /\
    interp_expr formals binders valuation expression = Some value /\
    interp_expr_list formals binders valuation expressions = Some rest.
Proof.
  cbn [interp_expr_list].
  destruct (interp_expr formals binders valuation expression) as [head|];
    destruct (interp_expr_list formals binders valuation expressions)
      as [tail|]; try discriminate.
  intros Heq. injection Heq as <-. eauto.
Qed.

Definition tval_list_head {t ts} (values : tval_list (t :: ts)) : tval t :=
  match values in tval_list ts0
    return match ts0 with [] => unit | t0 :: _ => tval t0 end
  with
  | TVNil => tt
  | TVCons value _ => value
  end.

Definition tval_list_tail {t ts} (values : tval_list (t :: ts)) :
    tval_list ts :=
  match values in tval_list ts0
    return match ts0 with [] => unit | _ :: ts1 => tval_list ts1 end
  with
  | TVNil => tt
  | TVCons _ rest => rest
  end.

Lemma pexpr_list_eta {keep D t ts} (expressions : pexpr_list keep D (t :: ts)) :
  expressions =
    PECons (IR.pexpr_list_head expressions) (IR.pexpr_list_tail expressions).
Proof.
  refine (match expressions as expressions0 in pexpr_list _ _ ts0
    return match ts0 return pexpr_list keep D ts0 -> Prop with
           | [] => fun _ => True
           | _ :: _ => fun expressions1 =>
               expressions1 = PECons (IR.pexpr_list_head expressions1)
                 (IR.pexpr_list_tail expressions1)
           end expressions0
  with
  | PENil => I
  | PECons _ _ => eq_refl
  end).
Qed.

(** Any expression can be pinned, at the value it has in the chosen state. *)
Lemma term_interp_resource_prenex_at_arguments_pin {Γ F Δ ts t}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (valuation : symbol_valuation)
    (tracked : gexpr_list Γ ts) (values : tval_list ts)
    (expression : gexpr Γ t)
    (prenex : Translation.Resource.resource_prenex Γ F Δ) :
  forall (binders : binder_env Δ),
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      tracked values prenex ⊢
    ∃ value : tval t,
      term_interp_resource_prenex_at_arguments runtime formals binders valuation
        (PECons expression tracked) (TVCons value values) prenex.
Proof.
  induction prenex as [Δ [stack body] | Δ u rest IH]; intros binders.
  - cbn [term_interp_resource_prenex_at_arguments
      Translation.Resource.resource_stack].
    iIntros "[Hstate %Hvalues]".
    destruct (interp_expr_total formals binders valuation
      (IR.symbolize_expr stack expression)) as [value Hvalue].
    iExists value. iFrame. iPureIntro.
    cbn [IR.symbolize_expr_list interp_expr_list]. rewrite Hvalue Hvalues.
    reflexivity.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "H". iDestruct "H" as (head) "H".
    iDestruct (IH with "H") as (value) "H".
    iExists value, head. iExact "H".
Qed.

Lemma term_interp_resource_prenex_at_arguments_unpin {Γ F Δ ts t}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (valuation : symbol_valuation)
    (tracked : gexpr_list Γ ts) (values : tval_list ts)
    (expression : gexpr Γ t) (value : tval t)
    (prenex : Translation.Resource.resource_prenex Γ F Δ) :
  forall (binders : binder_env Δ),
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      (PECons expression tracked) (TVCons value values) prenex ⊢
    term_interp_resource_prenex_at_arguments runtime formals binders valuation
      tracked values prenex.
Proof.
  induction prenex as [Δ [stack body] | Δ u rest IH]; intros binders.
  - cbn [term_interp_resource_prenex_at_arguments
      Translation.Resource.resource_stack].
    iIntros "[Hstate %Hvalues]". iFrame. iPureIntro.
    cbn [IR.symbolize_expr_list] in Hvalues.
    apply interp_expr_list_cons_inv in Hvalues
      as (head & rest & Heq & _ & Hrest).
    have Htail := f_equal tval_list_tail Heq. cbn in Htail.
    rewrite Htail. exact Hrest.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "H". iDestruct "H" as (head) "H". iExists head.
    iApply (IH with "H").
Qed.

(** A derivation of [assert condition] makes the condition true in every
    state satisfying its precondition, at the value the pinned vector
    determines. *)
Lemma term_assert_derivation_true {Γ F Δ}
    (pre post : Translation.Resource.resource_prenex Γ F Δ) statement :
  CertifiedNormalization.RavenHoareRules.RavenHoareTriple pre statement post ->
  forall (condition : gexpr Γ TBool), statement = TAssert condition ->
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ)
    (valuation : symbol_valuation) ts (pinned : gexpr_list Γ ts)
    (values : tval_list ts) (truth : tval TBool),
  (forall Δ' (store : symbolic_store Γ F Δ') (binders' : binder_env Δ'),
    interp_expr_list formals binders' valuation
      (IR.symbolize_expr_list store pinned) = Some values ->
    interp_expr formals binders' valuation
      (IR.symbolize_expr store condition) = Some truth) ->
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      pinned values pre ⊢
    ⌜truth = VBool true⌝.
Proof.
  intros Hderivation. induction Hderivation;
    intros asserted Hstatement runtime formals binders valuation ts pinned
      values truth Hdetermined; try discriminate.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "H". iDestruct "H" as (head) "H".
    iApply (IHHderivation asserted Hstatement with "H"). exact Hdetermined.
  - pose (source_binders := fun u (variable : bvar Δ u) =>
      binders u (MThere variable)).
    have Hrenaming : forall u (variable : bvar Δ u),
        binders u (Assertions.weaken_bound_renaming u variable) =
          source_binders u variable.
    { intros. reflexivity. }
    rewrite (term_interp_resource_prenex_at_arguments_rename runtime formals
      valuation _ _ pre _ Assertions.weaken_bound_renaming source_binders
      binders Hrenaming).
    iApply (IHHderivation asserted Hstatement). exact Hdetermined.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "H". iDestruct "H" as (head) "H".
    iApply (IHHderivation asserted Hstatement with "H"). exact Hdetermined.
  - iIntros "H". iApply (IHHderivation asserted Hstatement); [exact Hdetermined|].
    iApply (term_interp_resource_prenex_at_arguments_entails with "H").
    assumption.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "[[Hstack [Hbody _]] %Harguments]".
    iApply (IHHderivation asserted Hstatement); [exact Hdetermined|].
    cbn [term_interp_resource_prenex_at_arguments]. iFrame.
    iPureIntro. exact Harguments.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "[[Hstack Hbody] %Harguments]".
    iPoseProof (Validation.TermSemantics.core_entails_valid semantic_data
      (term_predicates valuation) _ _ ltac:(eassumption) formals binders
      valuation with "Hbody") as "Hbody".
    iApply (IHHderivation asserted Hstatement); [exact Hdetermined|].
    cbn [term_interp_resource_prenex_at_arguments]. iFrame.
    iPureIntro. exact Harguments.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "[[Hstack Hbody] %Harguments]".
    cbn [Translation.Resource.resource_stack] in Harguments.
    iPoseProof (interp_store_equal_under body store store' H formals
      binders valuation with "Hbody") as "%Hstores".
    iEval (rewrite Hstores) in "Hstack".
    have Hargument_interp := interp_program_expr_list_store_ext formals
      binders valuation store' store pinned Hstores.
    unfold interp_program_expr_list in Hargument_interp.
    rewrite Harguments in Hargument_interp.
    iApply (IHHderivation asserted Hstatement); [exact Hdetermined|].
    cbn [term_interp_resource_prenex_at_arguments]. iFrame.
    iPureIntro. symmetry. exact Hargument_interp.
  - injection Hstatement as ->.
    cbn [term_interp_resource_prenex_at_arguments
      Translation.Resource.resource_stack].
    iIntros "[[_ [_ Hcondition]] %Harguments]".
    unfold term_interp_core. cbn [Translation.TermSemantics.interp_core].
    iDestruct "Hcondition" as %Hcondition.
    iPureIntro.
    rewrite (Hdetermined _ store binders Harguments) in Hcondition.
    injection Hcondition as Htruth. exact Htruth.
  - destruct (interp_expr_total formals binders valuation value)
      as [tracked_value Htracked_value].
    rewrite (term_interp_resource_prenex_at_arguments_track runtime formals
      valuation _ _ expression pre binders value tracked_value
      Htracked_value).
    iApply (IHHderivation asserted Hstatement runtime formals binders
      valuation _ (PECons expression pinned) (TVCons tracked_value values)).
    intros Δ' store binders' Hcons.
    cbn [IR.symbolize_expr_list] in Hcons.
    apply interp_expr_list_cons_inv in Hcons
      as (head & rest & Heq & _ & Hrest).
    have Htail := f_equal tval_list_tail Heq. cbn in Htail. subst rest.
    exact (Hdetermined Δ' store binders' Hrest).
Qed.

(** Arguments that evaluate like the opened ones do not differ from them. *)
Lemma arguments_differ_same {D F Δ keep ts} (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store D F Δ) (left right : pexpr_list keep D ts)
    (values : tval_list ts) :
  interp_expr_list formals binders valuation
    (IR.symbolize_expr_list store left) = Some values ->
  interp_expr_list formals binders valuation
    (IR.symbolize_expr_list store right) = Some values ->
  interp_expr formals binders valuation
    (IR.symbolize_expr store (IR.arguments_differ left right)) =
    Some (VBool false).
Proof.
  revert right values.
  induction left as [|t ts expression tail IH]; intros right values Hleft Hright.
  - reflexivity.
  - rewrite (pexpr_list_eta right) in Hright.
    cbn [IR.symbolize_expr_list] in Hleft, Hright.
    apply interp_expr_list_cons_inv in Hleft
      as (value & rest & -> & Hhead & Htail).
    apply interp_expr_list_cons_inv in Hright
      as (value' & rest' & Hvalues & Hhead' & Htail').
    have Hvalue := f_equal tval_list_head Hvalues.
    have Hrest := f_equal tval_list_tail Hvalues.
    cbn in Hvalue, Hrest. subst value' rest'.
    cbn [IR.arguments_differ].
    have Hdiffer : interp_expr formals binders valuation
        (IR.symbolize_expr store
          (PEBinOp (BNe t) expression (IR.pexpr_list_head right))) =
        Some (VBool false).
    { cbn [IR.symbolize_expr interp_expr]. rewrite Hhead Hhead'.
      cbn [interp_binop]. rewrite (proj2 (tval_eqb_eq t value value) eq_refl).
      reflexivity. }
    destruct (IR.pexpr_list_nil tail); [exact Hdiffer|].
    have Hrest := IH (IR.pexpr_list_tail right) rest Htail Htail'.
    transitivity (match interp_expr formals binders valuation
        (IR.symbolize_expr store
          (PEBinOp (BNe t) expression (IR.pexpr_list_head right))),
      interp_expr formals binders valuation
        (IR.symbolize_expr store
          (IR.arguments_differ tail (IR.pexpr_list_tail right))) with
      | Some value1, Some value2 => interp_binop BOr value1 value2
      | _, _ => None
      end); [reflexivity|].
    rewrite Hdiffer Hrest. reflexivity.
Qed.

(** A true distinctness condition rules out every excluded vector. *)
Lemma arguments_distinct_excludes {D F Δ keep ts} (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store D F Δ) (arguments : pexpr_list keep D ts)
    (excluded : list (pexpr_list keep D ts)) (values : tval_list ts) :
  interp_expr formals binders valuation
    (IR.symbolize_expr store (IR.arguments_distinct arguments excluded)) =
    Some (VBool true) ->
  interp_expr_list formals binders valuation
    (IR.symbolize_expr_list store arguments) = Some values ->
  forall other, List.In other excluded ->
  interp_expr_list formals binders valuation
    (IR.symbolize_expr_list store other) <> Some values.
Proof.
  intros Htrue Harguments other Hin Hother.
  induction excluded as [|first rest IH]; [contradiction|].
  have Hfirst : forall first',
      interp_expr formals binders valuation
        (IR.symbolize_expr store (IR.arguments_differ arguments first')) =
        Some (VBool true) ->
      first' = other -> False.
  { intros first' Hdiffer ->.
    rewrite (arguments_differ_same formals binders valuation store arguments
      other values Harguments Hother) in Hdiffer.
    discriminate. }
  destruct rest as [|second rest'].
  - destruct Hin as [-> | []]. exact (Hfirst other Htrue eq_refl).
  - change (match interp_expr formals binders valuation
        (IR.symbolize_expr store (IR.arguments_differ arguments first)),
      interp_expr formals binders valuation
        (IR.symbolize_expr store
          (IR.arguments_distinct arguments (second :: rest'))) with
      | Some value1, Some value2 => interp_binop BAnd value1 value2
      | _, _ => None
      end = Some (VBool true)) in Htrue.
    destruct (interp_expr formals binders valuation
      (IR.symbolize_expr store (IR.arguments_differ arguments first)))
      as [left|] eqn:Hleft; [|discriminate].
    destruct (interp_expr formals binders valuation
      (IR.symbolize_expr store (IR.arguments_distinct arguments
        (second :: rest')))) as [right|] eqn:Hright; [|discriminate].
    dependent destruction left. dependent destruction right.
    cbn [interp_binop] in Htrue. injection Htrue as Htrue.
    apply andb_true_iff in Htrue as [-> ->].
    destruct Hin as [-> | Hin].
    + exact (Hfirst other Hleft eq_refl).
    + exact (IH eq_refl Hin).
Qed.

(** An opened instance's values, with the anchored vector, as evaluated in
    one store. *)
Definition anchor_fact {Γ F ts} (formals : formal_env F)
    (valuation : symbol_valuation) (anchor : gexpr_list Γ ts)
    (anchor_values : tval_list ts) {invariant : inv_id}
    (program_arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (values : tval_list (Assertion.invariant_args invariant)) : Prop :=
  exists Δ (store : symbolic_store Γ F Δ) (binders : binder_env Δ),
    interp_expr_list formals binders valuation
      (IR.symbolize_expr_list store anchor) = Some anchor_values /\
    interp_expr_list formals binders valuation
      (IR.symbolize_expr_list store program_arguments) = Some values.

(** The held world of a just-opened instance, with the means to close the
    access once it is returned. *)
Definition held_access (valuation : symbol_valuation) (invariant : inv_id)
    (values : tval_list (Assertion.invariant_args invariant))
    (outer_mask : coPset) : iProp :=
  (held_world_of valuation invariant
    {[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
      (Assertion.invariant_args invariant) values]} ∗
   (held_world_of valuation invariant
      {[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
        (Assertion.invariant_args invariant) values]} -∗
    world_body_interp valuation invariant values
      ={outer_mask ∖ ↑(invariant_namespace invariant), outer_mask}=∗ True))%I.

Lemma term_access_opening_arguments_valid {Γ F Δ} invariant
    (program_arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (focus : CertifiedNormalization.RavenHoareRules.access_focus
      invariant program_arguments Δ)
    (external body_pre : Translation.Resource.resource_prenex Γ F Δ)
    (Hopening : CertifiedNormalization.RavenHoareRules.access_opening
      invariant program_arguments focus external body_pre)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    {anchor_types} (anchor : gexpr_list Γ anchor_types)
    (anchor_values : tval_list anchor_types)
    (inner_mask outer_mask : coPset)
    (result : tval_list (Assertion.invariant_args invariant) -> iProp)
    {tracked_types} (tracked : gexpr_list Γ tracked_types)
    (tracked_values : tval_list tracked_types) :
  (∀ values, ⌜anchor_fact formals valuation anchor anchor_values
      program_arguments values⌝ -∗
    @RegionExecution.Primitives.Model.core_invariant_own _ _ Σ RG invariant
      values ={outer_mask, inner_mask}=∗
    world_body_interp valuation invariant values ∗ result values) -∗
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      (IR.pexpr_list_append tracked anchor)
      (Translation.tval_list_append tracked_values anchor_values) external -∗
  |={outer_mask, inner_mask}=>
    ∃ invariant_values : tval_list (Assertion.invariant_args invariant),
      term_interp_resource_prenex_at_arguments runtime formals binders valuation
        (IR.pexpr_list_append (IR.pexpr_list_append tracked anchor)
          program_arguments)
        (Translation.tval_list_append
          (Translation.tval_list_append tracked_values anchor_values)
          invariant_values)
        body_pre ∗
      result invariant_values ∗
      @RegionExecution.Primitives.Model.core_invariant_own _ _ Σ RG invariant
        invariant_values.
Proof.
  revert binders tracked_types tracked tracked_values.
  induction Hopening; intros binders tracked_types tracked tracked_values;
    iIntros "Hopener Hpre".
  - cbn [term_interp_resource_prenex_at_arguments].
    iDestruct "Hpre" as "[[Hstack Htoken] %Htracked]".
    iDestruct "Htoken" as (values) "[%Harguments #Htoken]".
    have Hanchor := Htracked.
    rewrite IR.symbolize_expr_list_append in Hanchor.
    apply Translation.interp_expr_list_append_some_inv in Hanchor as
      [_ Hanchor].
    iMod ("Hopener" $! values with "[] Htoken") as "[Hbody Hresult]".
    { iPureIntro. exists Δ, store, binders. split; assumption. }
    destruct (term_invariant_definition_compatible formals binders
      valuation invariant (IR.symbolize_expr_list store program_arguments)) as
      (actual_values & Hactual & Hbody_equiv).
    rewrite Harguments in Hactual. injection Hactual as Hvalues.
    subst actual_values.
    iEval (rewrite -Hbody_equiv) in "Hbody".
    iModIntro. iExists values. iFrame "Hresult Htoken".
    cbn [term_interp_resource_prenex_at_arguments].
    iFrame "Hstack Hbody". iPureIntro.
    rewrite IR.symbolize_expr_list_append.
    apply Translation.interp_expr_list_append_some; assumption.
  - cbn [term_interp_resource_prenex_at_arguments] in *.
    iDestruct "Hpre" as (value) "Hpre".
    iMod (IHHopening (binder_cons value binders) with "Hopener Hpre") as
      (values) "[Hbody [Hclose Htoken]]".
    iModIntro. iExists values. iFrame "Hclose Htoken". iExists value.
    iExact "Hbody".
  - pose (source_binders := fun u (variable : bvar Δ u) =>
      binders u (MThere variable)).
    have Hrenaming : forall u (variable : bvar Δ u),
        binders u (Assertions.weaken_bound_renaming u variable) =
          source_binders u variable.
    { intros. reflexivity. }
    iEval (rewrite (term_interp_resource_prenex_at_arguments_rename runtime formals
      valuation (IR.pexpr_list_append tracked anchor)
      (Translation.tval_list_append tracked_values anchor_values) external _
      Assertions.weaken_bound_renaming source_binders binders Hrenaming)) in
      "Hpre".
    iMod (IHHopening source_binders with "Hopener Hpre") as
      (values) "[Hbody [Hclose Htoken]]".
    iModIntro. iExists values. iFrame "Hclose Htoken".
    iEval (rewrite (term_interp_resource_prenex_at_arguments_rename runtime formals
      valuation (IR.pexpr_list_append (IR.pexpr_list_append tracked anchor)
        program_arguments)
      (Translation.tval_list_append (Translation.tval_list_append tracked_values anchor_values)
        values) body_pre _
      Assertions.weaken_bound_renaming source_binders binders Hrenaming)).
    iExact "Hbody".
  - iEval (cbn [term_interp_resource_prenex_at_arguments]) in "Hpre".
    iDestruct "Hpre" as (value) "Hpre".
    iMod (IHHopening (binder_cons value binders) with "Hopener Hpre") as
      (values) "[Hbody [Hclose Htoken]]".
    iModIntro. iExists values. iFrame "Hclose Htoken".
    iEval (rewrite (term_interp_resource_prenex_at_arguments_weaken runtime
      formals binders valuation
      (IR.pexpr_list_append (IR.pexpr_list_append tracked anchor)
        program_arguments)
      (Translation.tval_list_append (Translation.tval_list_append tracked_values anchor_values)
        values) value body_pre)) in
      "Hbody".
    iExact "Hbody".
  - iPoseProof (term_interp_resource_prenex_at_arguments_entails runtime
      formals binders valuation (IR.pexpr_list_append tracked anchor)
      (Translation.tval_list_append tracked_values anchor_values) external' external H
      with "Hpre") as "Hpre".
    iMod (IHHopening binders with "Hopener Hpre") as
      (values) "[Hbody [Hclose Htoken]]".
    iModIntro. iExists values. iFrame "Hclose Htoken".
    iApply (term_interp_resource_prenex_at_arguments_entails runtime formals
      binders valuation (IR.pexpr_list_append (IR.pexpr_list_append tracked anchor)
        program_arguments)
      (Translation.tval_list_append (Translation.tval_list_append tracked_values anchor_values)
        values)
      body_pre body_pre' H0 with "Hbody").
  - iEval (cbn [term_interp_resource_prenex_at_arguments]) in "Hpre".
    iDestruct "Hpre" as "[[Hstack [Hpre Hframe]] %Htracked]".
    iMod (IHHopening binders with "Hopener [Hstack Hpre]") as
      (values) "[Hbody [Hclose Htoken]]".
    { cbn [term_interp_resource_prenex_at_arguments]. iFrame.
      iPureIntro. exact Htracked. }
    iModIntro. iExists values. iFrame "Hclose Htoken".
    iEval (rewrite (term_interp_resource_prenex_at_arguments_and runtime
      formals binders valuation (IR.pexpr_list_append (IR.pexpr_list_append tracked anchor)
        program_arguments)
      (Translation.tval_list_append (Translation.tval_list_append tracked_values anchor_values)
        values) body_pre frame)).
    iFrame.
  - iEval (cbn [term_interp_resource_prenex_at_arguments]) in "Hpre".
    iDestruct "Hpre" as "[[Hstack Hpre] %Htracked]".
    iPoseProof (Validation.TermSemantics.core_entails_valid semantic_data
      (term_predicates valuation) _ _ H formals binders valuation with "Hpre") as
      "Hpre".
    iMod (IHHopening binders with "Hopener [Hstack Hpre]") as
      (values) "[Hbody [Hclose Htoken]]".
    { cbn [term_interp_resource_prenex_at_arguments]. iFrame.
      iPureIntro. exact Htracked. }
    iModIntro. iExists values. iFrame "Hclose Htoken".
    iApply (term_interp_resource_prenex_at_arguments_entails runtime formals
      binders valuation (IR.pexpr_list_append (IR.pexpr_list_append tracked anchor)
        program_arguments)
      (Translation.tval_list_append (Translation.tval_list_append tracked_values anchor_values)
        values)
      body_pre body_pre' H0 with "Hbody").
  - iEval (cbn [term_interp_resource_prenex_at_arguments]) in "Hpre".
    iDestruct "Hpre" as "[[Hstack Hbody] %Htracked]".
    iPoseProof (interp_store_equal_under pre_body store store' H formals
      binders valuation with "Hbody") as "%Hstores".
    iEval (rewrite Hstores) in "Hstack".
    have Hargument_interp := interp_program_expr_list_store_ext formals
      binders valuation store' store (IR.pexpr_list_append tracked anchor) Hstores.
    unfold interp_program_expr_list in Hargument_interp.
    rewrite Htracked in Hargument_interp.
    iApply (IHHopening binders with "Hopener [Hstack Hbody]").
    cbn [term_interp_resource_prenex_at_arguments]. iFrame.
    iPureIntro. symmetry. exact Hargument_interp.
  - destruct (interp_expr_total formals binders valuation value)
      as [tracked_value Htracked_value].
    iEval (rewrite (term_interp_resource_prenex_at_arguments_track runtime
      formals valuation (IR.pexpr_list_append tracked anchor)
      (Translation.tval_list_append tracked_values anchor_values) expression external binders
      value tracked_value Htracked_value)) in "Hpre".
    iMod (IHHopening binders _ (PECons expression tracked)
      (TVCons tracked_value tracked_values) with "Hopener Hpre") as
      (values) "[Hbody [Hclose Htoken]]".
    iModIntro. iExists values. iFrame "Hclose Htoken".
    rewrite (term_interp_resource_prenex_at_arguments_track runtime formals
      valuation (IR.pexpr_list_append (IR.pexpr_list_append tracked anchor)
        program_arguments)
      (Translation.tval_list_append (Translation.tval_list_append tracked_values anchor_values)
        values) expression body_pre
      binders value tracked_value Htracked_value).
    iExact "Hbody".
Qed.

(** Structural [TDone] steps preserve the argument-indexed interpretation. *)
Lemma term_done_triple_arguments_valid {Γ F Δ}
    (pre post : Translation.Resource.resource_prenex Γ F Δ)
    (Hdone : CertifiedNormalization.RavenHoareRules.done_triple pre post)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    {tracked_types} (tracked : gexpr_list Γ tracked_types)
    (tracked_values : tval_list tracked_types) :
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      tracked tracked_values pre ⊢
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      tracked tracked_values post.
Proof.
  revert binders tracked_types tracked tracked_values.
  induction Hdone; intros binders tracked_types tracked tracked_values.
  - done.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "Hpre". iDestruct "Hpre" as (value) "Hpre".
    iExists value. iApply (IHHdone with "Hpre").
  - pose (source_binders := fun u (variable : bvar Δ u) =>
      binders u (MThere variable)).
    have Hrenaming : forall u (variable : bvar Δ u),
        binders u (Assertions.weaken_bound_renaming u variable) =
          source_binders u variable.
    { intros. reflexivity. }
    rewrite !(term_interp_resource_prenex_at_arguments_rename runtime formals
      valuation tracked tracked_values _ _ Assertions.weaken_bound_renaming
      source_binders binders Hrenaming).
    apply IHHdone.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "Hpre". iDestruct "Hpre" as (value) "Hpre".
    iPoseProof (IHHdone (binder_cons value binders) with "Hpre") as "Hpost".
    iEval (rewrite (term_interp_resource_prenex_at_arguments_weaken runtime
      formals binders valuation tracked tracked_values value post)) in "Hpost".
    iExact "Hpost".
  - iIntros "Hpre".
    iPoseProof (term_interp_resource_prenex_at_arguments_entails runtime
      formals binders valuation tracked tracked_values pre' pre H with "Hpre")
      as "Hpre".
    iPoseProof (IHHdone binders with "Hpre") as "Hpost".
    iApply (term_interp_resource_prenex_at_arguments_entails runtime formals
      binders valuation tracked tracked_values post post' H0 with "Hpost").
  - change (Translation.Resource.RState store
      (Translation.Resource.CAnd pre_body frame)) with
      (Translation.Resource.prenex_and (Translation.Resource.RState store pre_body)
        frame).
    rewrite !term_interp_resource_prenex_at_arguments_and.
    iIntros "[Hpre Hframe]". iFrame "Hframe". iApply (IHHdone with "Hpre").
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "[[Hstack Hbody] %Harguments]".
    iPoseProof (interp_store_equal_under body store store' H formals binders
      valuation with "Hbody") as "%Hstores".
    iEval (rewrite Hstores) in "Hstack".
    have Hargument_interp := interp_program_expr_list_store_ext formals
      binders valuation store' store tracked Hstores.
    unfold interp_program_expr_list in Hargument_interp.
    rewrite Harguments in Hargument_interp.
    iApply (IHHdone binders with "[Hstack Hbody]").
    cbn [term_interp_resource_prenex_at_arguments]. iFrame.
    iPureIntro. symmetry. exact Hargument_interp.
  - destruct (interp_expr_total formals binders valuation value)
      as [tracked_value Htracked_value].
    rewrite !(term_interp_resource_prenex_at_arguments_track runtime formals
      valuation tracked tracked_values expression _ binders value tracked_value
      Htracked_value).
    apply (IHHdone binders _ (PECons expression tracked)
      (TVCons tracked_value tracked_values)).
Qed.

(** Closing-side interpretation for the canonical independent access.  The
    body carries one combined semantic vector: the caller's tracked
    expressions followed by the invariant's program arguments.  The closing
    spine consumes only the latter component and returns the former. *)
Lemma term_access_closing_arguments_valid {Γ F Δ} invariant
    (program_arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (focus : CertifiedNormalization.RavenHoareRules.access_focus
      invariant program_arguments Δ)
    (body_post external_post : Translation.Resource.resource_prenex Γ F Δ)
    (Hclosing : CertifiedNormalization.RavenHoareRules.access_closing
      invariant program_arguments focus body_post external_post)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    {tracked_types} (tracked : gexpr_list Γ tracked_types)
    (tracked_values : tval_list tracked_types)
    (invariant_values : tval_list (Assertion.invariant_args invariant))
    (inner_mask outer_mask : coPset) (result : iProp) :
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      (IR.pexpr_list_append tracked program_arguments)
      (Translation.tval_list_append tracked_values invariant_values)
      body_post -∗
  (world_body_interp valuation invariant invariant_values
    ={inner_mask, outer_mask}=∗ result) -∗
  @RegionExecution.Primitives.Model.core_invariant_own _ _ Σ RG invariant
    invariant_values -∗
  |={inner_mask, outer_mask}=> result ∗
    term_interp_resource_prenex_at_arguments runtime formals binders valuation
      tracked tracked_values external_post.
Proof.
  revert binders tracked_types tracked tracked_values.
  induction Hclosing; intros binders tracked_types tracked tracked_values.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "[[Hstack Hbody] %Hcombined] Hclose Htoken".
    rewrite IR.symbolize_expr_list_append in Hcombined.
    cbn [Validation.Resource.resource_stack] in Hcombined.
    apply Translation.interp_expr_list_append_some_inv in Hcombined as
      [Htracked Hinvariant].
    destruct (term_invariant_definition_compatible formals binders
      valuation invariant (IR.symbolize_expr_list store program_arguments)) as
      (actual_values & Hactual & Hbody_equiv).
    rewrite Hinvariant in Hactual. injection Hactual as Hvalues.
    subst actual_values.
    iPoseProof (bi.equiv_entails_1_1 _ _ Hbody_equiv with "Hbody") as
      "Hbody".
    iMod ("Hclose" with "Hbody") as "$". iModIntro.
    cbn [term_interp_resource_prenex_at_arguments].
    iFrame "Hstack". iSplitL "Htoken".
    + iExists invariant_values. iFrame "Htoken".
      iPureIntro. exact Hinvariant.
    + iPureIntro. exact Htracked.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "Hpost Hclose Htoken". iDestruct "Hpost" as (value) "Hpost".
    iPoseProof (IHHclosing (binder_cons value binders) with
      "Hpost Hclose Htoken") as "Hclosed".
    iMod "Hclosed" as "[$ Hclosed]". iModIntro. iExists value. iExact "Hclosed".
  - pose (source_binders := fun u (variable : bvar Δ u) =>
      binders u (MThere variable)).
    have Hrenaming : forall u (variable : bvar Δ u),
        binders u (Assertions.weaken_bound_renaming u variable) =
          source_binders u variable.
    { intros. reflexivity. }
    rewrite (term_interp_resource_prenex_at_arguments_rename runtime formals
      valuation (IR.pexpr_list_append tracked program_arguments)
      (Translation.tval_list_append tracked_values invariant_values)
      body_post _ Assertions.weaken_bound_renaming source_binders binders
      Hrenaming).
    iIntros "Hpost Hclose Htoken".
    iPoseProof (IHHclosing source_binders with "Hpost Hclose Htoken") as
      "Hclosed".
    iMod "Hclosed" as "[$ Hclosed]". iModIntro.
    rewrite (term_interp_resource_prenex_at_arguments_rename runtime formals
      valuation tracked tracked_values external_post _
      Assertions.weaken_bound_renaming source_binders binders Hrenaming).
    iExact "Hclosed".
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "Hpost Hclose Htoken". iDestruct "Hpost" as (value) "Hpost".
    iPoseProof (IHHclosing (binder_cons value binders) with
      "Hpost Hclose Htoken") as "Hclosed".
    iMod "Hclosed" as "[$ Hclosed]". iModIntro.
    iEval (rewrite (term_interp_resource_prenex_at_arguments_weaken runtime
      formals binders valuation tracked tracked_values value external_post)) in
      "Hclosed".
    iExact "Hclosed".
  - iIntros "Hpost Hclose Htoken".
    iPoseProof (term_interp_resource_prenex_at_arguments_entails runtime
      formals binders valuation (IR.pexpr_list_append tracked program_arguments)
      (Translation.tval_list_append tracked_values invariant_values)
      body_post' body_post H with "Hpost") as "Hpost".
    iPoseProof (IHHclosing binders with "Hpost Hclose Htoken") as "Hclosed".
    iMod "Hclosed" as "[$ Hclosed]". iModIntro.
    iApply (term_interp_resource_prenex_at_arguments_entails runtime formals
      binders valuation tracked tracked_values external_post external_post' H0
      with "Hclosed").
  - iIntros "Hpost Hclose Htoken".
    iEval (rewrite (term_interp_resource_prenex_at_arguments_and runtime
      formals binders valuation (IR.pexpr_list_append tracked program_arguments)
      (Translation.tval_list_append tracked_values invariant_values)
      body_post frame)) in "Hpost".
    iDestruct "Hpost" as "[Hpost Hframe]".
    iPoseProof (IHHclosing binders with "Hpost Hclose Htoken") as "Hclosed".
    iMod "Hclosed" as "[$ Hclosed]". iModIntro.
    iEval (rewrite (term_interp_resource_prenex_at_arguments_and runtime
      formals binders valuation tracked tracked_values external_post frame)).
    iFrame.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "[[Hstack Hbody] %Harguments] Hclose Htoken".
    iPoseProof (interp_store_equal_under body store store' H formals binders
      valuation with "Hbody") as "%Hstores".
    iEval (rewrite Hstores) in "Hstack".
    have Hargument_interp := interp_program_expr_list_store_ext formals
      binders valuation store' store
      (IR.pexpr_list_append tracked program_arguments) Hstores.
    unfold interp_program_expr_list in Hargument_interp.
    rewrite Harguments in Hargument_interp.
    iApply (IHHclosing binders with "[Hstack Hbody] Hclose Htoken").
    cbn [term_interp_resource_prenex_at_arguments]. iFrame.
    iPureIntro. symmetry. exact Hargument_interp.
  - destruct (interp_expr_total formals binders valuation value)
      as [tracked_value Htracked_value].
    rewrite (term_interp_resource_prenex_at_arguments_track runtime formals
      valuation (IR.pexpr_list_append tracked program_arguments)
      (Translation.tval_list_append tracked_values invariant_values) expression
      body_post binders value tracked_value Htracked_value).
    iIntros "Hpost Hclose Htoken".
    iPoseProof (IHHclosing binders _ (PECons expression tracked)
      (TVCons tracked_value tracked_values) with "Hpost Hclose Htoken") as
      "Hclosed".
    iMod "Hclosed" as "[$ Hclosed]". iModIntro.
    rewrite (term_interp_resource_prenex_at_arguments_track runtime formals
      valuation tracked tracked_values expression external_post binders value
      tracked_value Htracked_value).
    iExact "Hclosed".
  - iIntros "Hpost Hclose Htoken".
    iMod (IHHclosing binders with "Hpost Hclose Htoken") as "[$ Hmiddle]".
    iModIntro.
    iApply (term_done_triple_arguments_valid _ _ H with "Hmiddle").
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "[[Hstack Hbody] %Harguments] Hclose Htoken".
    destruct (interp_expr_total formals binders valuation
      (IR.symbolize_expr store condition)) as [value Hvalue].
    dependent destruction value. destruct b.
    + iApply (IHHclosing1 binders with "[Hstack Hbody] Hclose Htoken").
      cbn [term_interp_resource_prenex_at_arguments].
      iFrame "Hstack Hbody". iPureIntro. split; [exact Hvalue | exact Harguments].
    + iApply (IHHclosing2 binders with "[Hstack Hbody] Hclose Htoken").
      cbn [term_interp_resource_prenex_at_arguments].
      iFrame "Hstack Hbody". iPureIntro. split.
      * simpl. rewrite Hvalue. reflexivity.
      * exact Harguments.
Qed.

(** The semantic seam for [RTInvAccessIndependent].  The body is invoked
    exactly once, at the concatenation of the caller vector and the values
    chosen while opening the invariant. *)
Lemma term_independent_inv_access_runtime_arguments_valid {Γ F Δ ts} invariant program_arguments
    (focus_open focus_close :
      CertifiedNormalization.RavenHoareRules.access_focus
        invariant program_arguments Δ)
    (external_pre body_pre body_post external_post :
      Translation.Resource.resource_prenex Γ F Δ)
    (Hopening : CertifiedNormalization.RavenHoareRules.access_opening
      invariant program_arguments focus_open external_pre body_pre)
    (Hclosing : CertifiedNormalization.RavenHoareRules.access_closing
      invariant program_arguments focus_close body_post external_post)
    (body : stmt Γ)
    (tracked : gexpr_list Γ ts) (tracked_values : tval_list ts)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (outer_mask : coPset) (frame : iProp) :
  invariant ∈ term_registered_invariants  ->
  ↑(invariant_namespace invariant) ⊆ outer_mask ->
  (forall invariant_values : tval_list (Assertion.invariant_args invariant),
    (global_world_context valuation ∗
     (held_world_of valuation invariant
        {[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
          (Assertion.invariant_args invariant) invariant_values]} ∗ frame) ∗
     term_interp_resource_prenex_at_arguments runtime formals binders valuation
       (IR.pexpr_list_append tracked program_arguments)
       (Translation.tval_list_append tracked_values invariant_values)
       body_pre) ⊢
    runtime_masked_wp
      (outer_mask ∖ ↑(invariant_namespace invariant))
      (outer_mask ∖ ↑(invariant_namespace invariant))
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) body)
      (global_world_context valuation ∗
       (held_world_of valuation invariant
          {[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
            (Assertion.invariant_args invariant) invariant_values]} ∗ frame) ∗
       term_interp_resource_prenex_at_arguments runtime formals binders valuation
         (IR.pexpr_list_append tracked program_arguments)
         (Translation.tval_list_append tracked_values invariant_values)
         body_post)) ->
  @Atomic RuntimeLang.simp_lang WeaklyAtomic
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) body) ->
  (global_world_context valuation ∗ frame ∗
   term_interp_resource_prenex_at_arguments runtime formals binders valuation
     tracked tracked_values external_pre) ⊢
  runtime_masked_wp outer_mask outer_mask
    (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      (TInvAccess invariant program_arguments body))
    (global_world_context valuation ∗ frame ∗
     term_interp_resource_prenex_at_arguments runtime formals binders valuation
       tracked tracked_values external_post).
Proof.
  intros Hregistered Hnamespace Hbody Hatomic.
  simpl. iIntros "[#Hglobal [Hframe Hpre]]".
  iEval (unfold global_world_context) in "Hglobal".
  iDestruct "Hglobal" as "[#Hworlds [#Hchunks #Hprocedures]]".
  iPoseProof (term_world_context_lookup valuation invariant Hregistered
    with "Hworlds") as "#Hworld".
  iApply (runtime_masked_wp_atomic_mask_change outer_mask
    (outer_mask ∖ ↑(invariant_namespace invariant))
    (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      body) _ Hatomic).
  iMod (term_access_opening_arguments_valid invariant
    program_arguments focus_open external_pre body_pre Hopening runtime
    formals binders valuation tracked tracked_values
    (outer_mask ∖ ↑(invariant_namespace invariant)) outer_mask
    (fun values => held_access valuation invariant values outer_mask)
    (@PENil _ keep_all Γ) Translation.TVNil
    with "[] Hpre") as (invariant_values) "[Hpre [Hclose Htoken]]".
  { iIntros (values _) "Htoken".
    iMod (term_world_open_held valuation invariant values outer_mask Hnamespace
      with "Hworld Htoken") as "(Hbody & Hheld & Hclose)".
    iModIntro. iFrame. }
  cbn [IR.pexpr_list_append Translation.tval_list_append] in *.
  iModIntro. iDestruct "Hclose" as "[Hheld Hclose]".
  iPoseProof (Hbody invariant_values with
    "[$Hworlds $Hchunks $Hprocedures $Hheld $Hframe $Hpre]") as "Hwp".
  iCombine "Hwp Hclose Htoken" as "Hwp".
  iPoseProof (runtime_masked_wp_frame with "Hwp") as "Hwp".
  iApply (runtime_masked_wp_mono with "Hwp").
  iIntros "[[#Hglobal [[Hheld Hframe] Hpost]] [Hclose Htoken]]".
  iFrame "Hglobal Hframe". iSpecialize ("Hclose" with "Hheld").
  iMod (term_access_closing_arguments_valid invariant
    program_arguments focus_close body_post external_post Hclosing runtime
    formals binders valuation tracked tracked_values invariant_values
    (outer_mask ∖ ↑(invariant_namespace invariant)) outer_mask True%I
    with "Hpost Hclose Htoken") as "[_ $]".
  done.
Qed.

(** A nested access of an open declaration: the instance's body is taken
    from the held world and returned to it, with no mask change. *)
Lemma term_nested_inv_access_runtime_arguments_valid {Γ F Δ ts} invariant
    program_arguments
    (focus_open focus_close :
      CertifiedNormalization.RavenHoareRules.access_focus
        invariant program_arguments Δ)
    (external_pre body_pre body_post external_post :
      Translation.Resource.resource_prenex Γ F Δ)
    (Hopening : CertifiedNormalization.RavenHoareRules.access_opening
      invariant program_arguments focus_open external_pre body_pre)
    (Hclosing : CertifiedNormalization.RavenHoareRules.access_closing
      invariant program_arguments focus_close body_post external_post)
    (body : stmt Γ)
    (tracked : gexpr_list Γ ts) (tracked_values : tval_list ts)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (mask : coPset) (opened : gset (list RuntimeModel.val)) (frame : iProp) :
  (forall values, anchor_fact formals valuation tracked tracked_values
      program_arguments values ->
    @RegionExecution.Primitives.Model.tval_list_to_rich_list _
      (Assertion.invariant_args invariant) values ∉ opened) ->
  (forall invariant_values : tval_list (Assertion.invariant_args invariant),
    (global_world_context valuation ∗
     (held_world_of valuation invariant
        ({[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
          (Assertion.invariant_args invariant) invariant_values]} ∪ opened) ∗
      frame) ∗
     term_interp_resource_prenex_at_arguments runtime formals binders valuation
       (IR.pexpr_list_append tracked program_arguments)
       (Translation.tval_list_append tracked_values invariant_values)
       body_pre) ⊢
    runtime_masked_wp mask mask
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) body)
      (global_world_context valuation ∗
       (held_world_of valuation invariant
          ({[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
            (Assertion.invariant_args invariant) invariant_values]} ∪ opened) ∗
        frame) ∗
       term_interp_resource_prenex_at_arguments runtime formals binders valuation
         (IR.pexpr_list_append tracked program_arguments)
         (Translation.tval_list_append tracked_values invariant_values)
         body_post)) ->
  (global_world_context valuation ∗
   (held_world_of valuation invariant opened ∗ frame) ∗
   term_interp_resource_prenex_at_arguments runtime formals binders valuation
     tracked tracked_values external_pre) ⊢
  runtime_masked_wp mask mask
    (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      (TInvAccess invariant program_arguments body))
    (global_world_context valuation ∗
     (held_world_of valuation invariant opened ∗ frame) ∗
     term_interp_resource_prenex_at_arguments runtime formals binders valuation
       tracked tracked_values external_post).
Proof.
  intros Hfresh Hbody.
  simpl. iIntros "(#Hglobal & [Hheld Hframe] & Hpre)".
  iApply runtime_masked_wp_fupd.
  iMod (term_access_opening_arguments_valid invariant
    program_arguments focus_open external_pre body_pre Hopening runtime
    formals binders valuation tracked tracked_values mask mask
    (fun values =>
      ⌜@RegionExecution.Primitives.Model.tval_list_to_rich_list _
        (Assertion.invariant_args invariant) values ∉ opened⌝ ∗
      held_world_of valuation invariant
        ({[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
          (Assertion.invariant_args invariant) values]} ∪ opened))%I
    (@PENil _ keep_all Γ) Translation.TVNil
    with "[Hheld] Hpre") as (invariant_values)
    "[Hpre [[%Hvalues_fresh Hheld] Htoken]]".
  { iIntros (values Hfact) "Htoken".
    have Hvalues_fresh := Hfresh values Hfact.
    iPoseProof (held_world_take valuation invariant opened values
      Hvalues_fresh with "Hheld Htoken") as "[Hbody Hheld]".
    iModIntro. iFrame. done. }
  cbn [IR.pexpr_list_append Translation.tval_list_append] in *.
  iModIntro.
  iPoseProof (Hbody invariant_values with "[$Hglobal $Hheld $Hframe $Hpre]")
    as "Hwp".
  iCombine "Hwp Htoken" as "Hwp".
  iPoseProof (runtime_masked_wp_frame with "Hwp") as "Hwp".
  iApply (runtime_masked_wp_mono with "Hwp").
  iIntros "[(#Hglobal' & [Hheld Hframe] & Hpost) Htoken]".
  iMod (term_access_closing_arguments_valid invariant
    program_arguments focus_close body_post external_post Hclosing runtime
    formals binders valuation tracked tracked_values invariant_values
    mask mask (held_world_of valuation invariant opened)
    with "Hpost [Hheld] Htoken") as "[Hheld Hpost]".
  { iIntros "Hbody". iModIntro.
    iApply (held_world_put valuation invariant opened invariant_values
      Hvalues_fresh with "Hheld Hbody"). }
  iModIntro. iFrame "Hglobal' Hheld Hframe Hpost".
Qed.

Lemma held_opened_lookup_none {Γ ts types} (held : held_list Γ ts types)
    records (invariant : inv_id) :
  held_aligned records held ->
  invariant ∉ (list_to_set (map GenericRegions.Atomicity.record_invariant
    records) : gset inv_id) ->
  held_opened held !! invariant = None.
Proof.
  unfold held_aligned. revert records.
  induction held as [|types' invariant' arguments opened rest IH];
    intros records Haligned Hout; cbn; [reflexivity|].
  destruct records as [|record records]; [discriminate|].
  cbn in Haligned. injection Haligned as Hinvariant _ Hrest.
  cbn in Hout. rewrite lookup_insert_ne.
  - apply (IH records Hrest). set_solver.
  - intros ->. apply Hout. rewrite Hinvariant. set_solver.
Qed.

Lemma held_world_cons_fresh {Γ ts types} valuation (invariant : inv_id)
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (values : tval_list (Assertion.invariant_args invariant))
    (held : held_list Γ ts types) :
  held_opened held !! invariant = None ->
  held_world valuation (HeldCons invariant arguments values held) ⊣⊢
    held_world_of valuation invariant
      {[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
        (Assertion.invariant_args invariant) values]} ∗
    held_world valuation held.
Proof.
  intros Hnone. unfold held_world. cbn [held_opened]. rewrite Hnone. cbn.
  rewrite union_empty_r_L. by rewrite big_sepM_insert.
Qed.

Lemma held_aligned_open {Γ ts types} (invariant : inv_id)
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (values : tval_list (Assertion.invariant_args invariant))
    (held : held_list Γ ts types) excluded entry opened :
  GenericRegions.Atomicity.open_access invariant
    (RegionSyntax.argument_key arguments) excluded entry = inr opened ->
  held_aligned (GenericRegions.Atomicity.analysis_records entry) held ->
  held_aligned (GenericRegions.Atomicity.analysis_records opened)
    (HeldCons invariant arguments values held).
Proof.
  intros Hopen Haligned.
  destruct (GenericRegions.Atomicity.open_access_records _ _ _ _ _ Hopen)
    as (consumed & ->).
  unfold held_aligned in *. cbn. rewrite Haligned. reflexivity.
Qed.

(** Structured form of the independent access seam.  Its body premise is
    already the strengthened induction hypothesis at the concatenated
    vector; this is the exact interface used by the top-level induction. *)
Lemma term_structured_runtime_independent_inv_access_arguments_valid
    {Γ F Δ entry invariant program_arguments excluded body opened inner ts}
    (Hregistered : invariant ∈ term_registered_invariants )
    (Hopen : GenericRegions.Atomicity.open_access invariant
      (RegionSyntax.argument_key program_arguments)
      (map RegionSyntax.argument_key excluded) entry =
      inr opened)
    (Hclosed : invariant ∉ GenericRegions.Atomicity.analysis_open entry)
    (body_certificate : Structured.structured_certificate
      Γ opened body inner)
    (Hpreserved : GenericRegions.Atomicity.analysis_records inner =
      GenericRegions.Atomicity.analysis_records opened)
    (focus_open focus_close :
      CertifiedNormalization.RavenHoareRules.access_focus
        invariant program_arguments Δ)
    (external_pre body_pre body_post external_post :
      Translation.Resource.resource_prenex Γ F Δ)
    (Hprogram_stable :
      Hoare.ResourceHoare.pexpr_list_dependencies program_arguments ##
        Hoare.ResourceHoare.statement_writes body)
    (Hopening : CertifiedNormalization.RavenHoareRules.access_opening
      invariant program_arguments focus_open external_pre body_pre)
    (Hclosing : CertifiedNormalization.RavenHoareRules.access_closing
      invariant program_arguments focus_close body_post external_post)
    (conditions : list (gexpr Γ TBool)) (tracked : gexpr_list Γ ts) :
  term_structured_runtime_arguments_valid body_certificate
    [] tracked body_pre body_post ->
  (forall (runtime : RegionExecution.Primitives.Model.stack_context Γ),
    @Atomic RuntimeLang.simp_lang WeaklyAtomic
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) body)) ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredInvAccess Γ entry invariant program_arguments
      excluded body opened inner Hopen body_certificate Hpreserved)
    conditions tracked external_pre external_post.
Proof.
  intros Hbody Hatomic types held Haligned Htracked_stable tracked_values
    runtime formals binders valuation ambient Henvelope _.
  cbn [Hoare.ResourceHoare.statement_writes] in Htracked_stable.
  have Hcombined_stable :
      Hoare.ResourceHoare.pexpr_list_dependencies
          (IR.pexpr_list_append (held_pinned tracked held) program_arguments) ##
        Hoare.ResourceHoare.statement_writes body.
  { rewrite Hoare.ResourceHoare.pexpr_list_dependencies_append.
    apply disjoint_union_l. split; assumption. }
  have Hopen_facts := GenericRegions.Atomicity.open_access_fresh _ _ _ _ _
    Hclosed Hopen.
  apply GenericRegions.Atomicity.open_invariant_success in Hopen_facts as
    (Hfresh & Hmember & _ & Hopened).
  have Hheld_fresh := held_opened_lookup_none held _ invariant Haligned Hfresh.
  have Hfootprint_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint
        (Structured.StructuredInvAccess Γ entry invariant program_arguments
          excluded body opened inner Hopen body_certificate Hpreserved)) ⊆ ambient.
  { etrans; last exact Henvelope. apply RegionExecution.Primitives.Model.runtime_mask_mono.
    simpl. intros candidate Hcandidate. apply elem_of_union_l. exact Hcandidate. }
  have Hnamespace := term_structured_invariant_namespace_active_from_footprint
    (Structured.StructuredInvAccess Γ entry invariant program_arguments
      excluded body opened inner Hopen body_certificate Hpreserved)
    ambient invariant Hmember Hfresh Hfootprint_envelope.
  have Hinner_mask : RegionExecution.Primitives.Model.active_runtime_mask
      ambient inner =
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry ∖
        ↑(invariant_namespace invariant).
  { exact (RegionExecution.Primitives.active_runtime_mask_access ambient entry
      invariant opened inner Hopened Hpreserved). }
  have Hexit_mask : RegionExecution.Primitives.Model.active_runtime_mask ambient
      (GenericRegions.Atomicity.fold_invariant invariant
        (RegionSyntax.argument_key program_arguments) inner) =
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
  { apply RegionExecution.Primitives.Model.active_runtime_mask_same_open.
    exact (term_structured_certificate_preserves_open
      (Structured.StructuredInvAccess Γ entry invariant program_arguments
        excluded body opened inner Hopen body_certificate Hpreserved)). }
  unfold term_structured_runtime_wp.
  rewrite translated_runtime_wp_as_masked Hexit_mask. simpl.
  eapply (term_independent_inv_access_runtime_arguments_valid
    invariant program_arguments focus_open focus_close external_pre body_pre
    body_post external_post Hopening Hclosing body (held_pinned tracked held)
    (held_pinned_values tracked_values held) runtime formals binders valuation
    (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
    (held_world valuation held)).
  - exact Hregistered.
  - exact Hnamespace.
  - intros invariant_values.
    have Hbody_envelope : RegionExecution.Primitives.Model.runtime_mask
        (Structured.structured_certificate_footprint body_certificate ∪
          term_registered_invariants) ⊆ ambient.
    { etrans; last exact Henvelope.
      apply RegionExecution.Primitives.Model.runtime_mask_mono.
      intros candidate Hcandidate.
      apply elem_of_union in Hcandidate as [Hcandidate | Hregistered'].
      - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
      - apply elem_of_union_r. exact Hregistered'. }
    have Hbody_wp := Hbody _ (HeldCons invariant program_arguments
      invariant_values held)
      (held_aligned_open invariant program_arguments invariant_values held
        _ entry opened Hopen Haligned)
      Hcombined_stable tracked_values runtime formals binders valuation ambient
      Hbody_envelope (conditions_hold_nil _ _).
    unfold term_structured_runtime_wp in Hbody_wp.
    rewrite translated_runtime_wp_as_masked in Hbody_wp.
    have Hopened_inner : RegionExecution.Primitives.Model.active_runtime_mask
        ambient opened =
        RegionExecution.Primitives.Model.active_runtime_mask ambient inner.
    { apply RegionExecution.Primitives.Model.active_runtime_mask_same_open.
      apply GenericRegions.Atomicity.analysis_open_records.
      symmetry. exact Hpreserved. }
    rewrite Hopened_inner Hinner_mask in Hbody_wp.
    iIntros "(#Hglobal & [Hheld Hframe] & Hpre)".
    iPoseProof (Hbody_wp with "[Hheld Hframe Hpre]") as "Hwp".
    { iFrame "Hglobal Hpre".
      iApply (held_world_cons_fresh valuation invariant program_arguments
        invariant_values held Hheld_fresh). iFrame. }
    iApply (runtime_masked_wp_mono with "Hwp").
    iIntros "(#Hglobal' & Hheld & Hpost)". iFrame "Hglobal' Hpost".
    iApply (held_world_cons_fresh valuation invariant program_arguments
      invariant_values held Hheld_fresh with "Hheld").
  - apply Hatomic.
Qed.

Lemma held_opened_lookup_some {Γ ts types} (held : held_list Γ ts types)
    records (invariant : inv_id) :
  held_aligned records held ->
  invariant ∈ (list_to_set (map GenericRegions.Atomicity.record_invariant
    records) : gset inv_id) ->
  is_Some (held_opened held !! invariant).
Proof.
  unfold held_aligned. revert records.
  induction held as [|types' invariant' arguments opened rest IH];
    intros records Haligned Hin.
  - destruct records; [set_solver|discriminate].
  - destruct records as [|record records]; [discriminate|].
    cbn in Haligned. injection Haligned as Hinvariant _ Hrest.
    cbn. destruct (decide (invariant = invariant')) as [->|Hne].
    + rewrite lookup_insert. eauto.
    + rewrite lookup_insert_ne; [|congruence].
      apply (IH records Hrest). cbn in Hin. set_solver.
Qed.

Lemma held_world_split {Γ ts types} valuation (invariant : inv_id)
    (held : held_list Γ ts types) opened :
  held_opened held !! invariant = Some opened ->
  held_world valuation held ⊣⊢
    held_world_of valuation invariant opened ∗
    [∗ map] other ↦ others ∈ delete invariant (held_opened held),
      held_world_of valuation other others.
Proof. intros Hlookup. unfold held_world. by rewrite big_sepM_delete. Qed.

Lemma held_world_cons_open {Γ ts types} valuation (invariant : inv_id)
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (values : tval_list (Assertion.invariant_args invariant))
    (held : held_list Γ ts types) opened :
  held_opened held !! invariant = Some opened ->
  held_world valuation (HeldCons invariant arguments values held) ⊣⊢
    held_world_of valuation invariant
      ({[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
        (Assertion.invariant_args invariant) values]} ∪ opened) ∗
    [∗ map] other ↦ others ∈ delete invariant (held_opened held),
      held_world_of valuation other others.
Proof.
  intros Hlookup. unfold held_world. cbn [held_opened]. rewrite Hlookup.
  cbn. by rewrite big_sepM_insert_delete.
Qed.

(** The values an invariant is held open at are those of held arguments
    with the keys of its records. *)
Lemma held_opened_evaluated {Γ ts types} (tracked : gexpr_list Γ ts)
    (values : tval_list ts) (held : held_list Γ ts types)
    {F Δ} (store : symbolic_store Γ F Δ) (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (invariant : inv_id) raw :
  interp_expr_list formals binders valuation
    (IR.symbolize_expr_list store (held_pinned tracked held)) =
    Some (held_pinned_values values held) ->
  raw ∈ default ∅ (held_opened held !! invariant) ->
  exists (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (opened : tval_list (Assertion.invariant_args invariant)),
    List.In (invariant, RegionSyntax.argument_key arguments)
      (held_records held) /\
    interp_expr_list formals binders valuation
      (IR.symbolize_expr_list store arguments) = Some opened /\
    raw = @RegionExecution.Primitives.Model.tval_list_to_rich_list _
      (Assertion.invariant_args invariant) opened.
Proof.
  induction held as [|types' invariant' arguments opened rest IH];
    intros Heval Hraw.
  - cbn in Hraw. rewrite lookup_empty in Hraw. cbn in Hraw. set_solver.
  - cbn [held_pinned held_pinned_values] in Heval.
    rewrite IR.symbolize_expr_list_append in Heval.
    apply Translation.interp_expr_list_append_some_inv in Heval as
      [Hrest Harguments].
    cbn [held_opened] in Hraw.
    destruct (decide (invariant = invariant')) as [<-|Hne].
    + rewrite lookup_insert in Hraw. cbn in Hraw.
      apply elem_of_union in Hraw as [Hraw|Hraw].
      * apply elem_of_singleton in Hraw as ->.
        exists arguments, opened. split; [left; reflexivity|]. split; auto.
      * destruct (IH Hrest Hraw) as (arguments' & opened' & Hin & ? & ?).
        exists arguments', opened'. split; [right; exact Hin|]. auto.
    + rewrite lookup_insert_ne in Hraw; [|congruence].
      destruct (IH Hrest Hraw) as (arguments' & opened' & Hin & ? & ?).
      exists arguments', opened'. split; [right; exact Hin|]. auto.
Qed.

(** Structured form of the nested access seam: the access's own condition,
    known to hold where the pinned vector has its values, rules out the
    instances held open. *)
Lemma term_structured_runtime_nested_inv_access_arguments_valid
    {Γ F Δ entry invariant program_arguments excluded body opened inner ts}
    (Hopen : GenericRegions.Atomicity.open_access invariant
      (RegionSyntax.argument_key program_arguments)
      (map RegionSyntax.argument_key excluded) entry =
      inr opened)
    (Hnested : invariant ∈ GenericRegions.Atomicity.analysis_open entry)
    (body_certificate : Structured.structured_certificate
      Γ opened body inner)
    (Hpreserved : GenericRegions.Atomicity.analysis_records inner =
      GenericRegions.Atomicity.analysis_records opened)
    (focus_open focus_close :
      CertifiedNormalization.RavenHoareRules.access_focus
        invariant program_arguments Δ)
    (external_pre body_pre body_post external_post :
      Translation.Resource.resource_prenex Γ F Δ)
    (Hprogram_stable :
      Hoare.ResourceHoare.pexpr_list_dependencies program_arguments ##
        Hoare.ResourceHoare.statement_writes body)
    (Hopening : CertifiedNormalization.RavenHoareRules.access_opening
      invariant program_arguments focus_open external_pre body_pre)
    (Hclosing : CertifiedNormalization.RavenHoareRules.access_closing
      invariant program_arguments focus_close body_post external_post)
    (conditions : list (gexpr Γ TBool)) (tracked : gexpr_list Γ ts) :
  List.In (IR.arguments_distinct program_arguments excluded) conditions ->
  term_structured_runtime_arguments_valid body_certificate
    [] tracked body_pre body_post ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredInvAccess Γ entry invariant program_arguments
      excluded body opened inner Hopen body_certificate Hpreserved)
    conditions tracked external_pre external_post.
Proof.
  intros Hcondition Hbody types held Haligned Htracked_stable tracked_values
    runtime formals binders valuation ambient Henvelope Hconditions.
  cbn [Hoare.ResourceHoare.statement_writes] in Htracked_stable.
  have Hcombined_stable :
      Hoare.ResourceHoare.pexpr_list_dependencies
          (IR.pexpr_list_append (held_pinned tracked held) program_arguments) ##
        Hoare.ResourceHoare.statement_writes body.
  { rewrite Hoare.ResourceHoare.pexpr_list_dependencies_append.
    apply disjoint_union_l. split; assumption. }
  destruct (GenericRegions.Atomicity.open_access_nested _ _ _ _ _ Hnested Hopen)
    as (_ & Hcovered & Hopened_open & _).
  destruct (held_opened_lookup_some held _ invariant Haligned Hnested)
    as [held_values Hlookup].
  have Hinner_mask : RegionExecution.Primitives.Model.active_runtime_mask
      ambient inner =
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
  { apply RegionExecution.Primitives.Model.active_runtime_mask_same_open.
    rewrite (GenericRegions.Atomicity.analysis_open_records _ _ Hpreserved).
    exact Hopened_open. }
  have Hopened_mask : RegionExecution.Primitives.Model.active_runtime_mask
      ambient opened =
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
  { apply RegionExecution.Primitives.Model.active_runtime_mask_same_open.
    exact Hopened_open. }
  have Hexit_mask : RegionExecution.Primitives.Model.active_runtime_mask ambient
      (GenericRegions.Atomicity.fold_invariant invariant
        (RegionSyntax.argument_key program_arguments) inner) =
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
  { apply RegionExecution.Primitives.Model.active_runtime_mask_same_open.
    exact (term_structured_certificate_preserves_open
      (Structured.StructuredInvAccess Γ entry invariant program_arguments
        excluded body opened inner Hopen body_certificate
        Hpreserved)). }
  (* The opened values are none of the held ones. *)
  have Hfresh : forall values,
      anchor_fact formals valuation (held_pinned tracked held)
        (held_pinned_values tracked_values held) program_arguments values ->
      @RegionExecution.Primitives.Model.tval_list_to_rich_list _
        (Assertion.invariant_args invariant) values ∉ held_values.
  { intros values (Δ' & store & binders' & Hpinned & Hvalues) Hraw.
    have Htrue := Hconditions _ _ store formals binders' valuation Hpinned.
    rewrite Forall_forall in Htrue.
    specialize (Htrue _ (proj2 (elem_of_list_In _ _) Hcondition)).
    have Hraw' : @RegionExecution.Primitives.Model.tval_list_to_rich_list _
        (Assertion.invariant_args invariant) values ∈
        default ∅ (held_opened held !! invariant).
    { rewrite Hlookup. exact Hraw. }
    destruct (held_opened_evaluated tracked tracked_values held store formals
      binders' valuation invariant _ Hpinned Hraw')
      as (held_arguments & opened_values & Hin & Hheld_eval & Hrich).
    apply RegionExecution.Primitives.Model.tval_list_to_rich_list_injective
      in Hrich. subst opened_values.
    unfold held_aligned in Haligned. rewrite <- Haligned in Hin.
    apply in_map_iff in Hin as (record & Hrecord & Hrecord_in).
    injection Hrecord as Hrecord_invariant Hrecord_key.
    pose proof Hcovered as Hcover.
    unfold GenericRegions.Atomicity.records_covered in Hcover.
    rewrite forallb_forall in Hcover.
    specialize (Hcover record Hrecord_in).
    rewrite decide_True in Hcover; [|exact Hrecord_invariant].
    apply bool_decide_eq_true in Hcover as [Hsome Hexcluded].
    rewrite Hrecord_key in Hsome Hexcluded.
    apply elem_of_list_In, in_map_iff in Hexcluded
      as (other & Hother_key & Hother_in).
    destruct (RegionSyntax.argument_key held_arguments) as [key|] eqn:Hkey;
      [|contradiction].
    have Hsame := RegionSyntax.argument_key_injective other held_arguments key
      Hother_key Hkey.
    subst other.
    exact (arguments_distinct_excludes formals binders' valuation store
      program_arguments excluded values Htrue Hvalues held_arguments
      Hother_in Hheld_eval). }
  set frame := ([∗ map] other ↦ others ∈ delete invariant (held_opened held),
    held_world_of valuation other others)%I.
  have Hbody_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint body_certificate ∪
        term_registered_invariants) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros candidate Hcandidate.
    apply elem_of_union in Hcandidate as [Hcandidate | Hregistered'].
    - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
    - apply elem_of_union_r. exact Hregistered'. }
  have Hbody_premise : forall invariant_values,
      (global_world_context valuation ∗
       (held_world_of valuation invariant
          ({[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
            (Assertion.invariant_args invariant) invariant_values]} ∪
            held_values) ∗ frame) ∗
       term_interp_resource_prenex_at_arguments runtime formals binders
         valuation
         (IR.pexpr_list_append (held_pinned tracked held) program_arguments)
         (Translation.tval_list_append (held_pinned_values tracked_values held)
           invariant_values)
         body_pre) ⊢
      runtime_masked_wp
        (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
        (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
        (@RuntimeErasure.runtime_stmt _ _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) body)
        (global_world_context valuation ∗
         (held_world_of valuation invariant
            ({[@RegionExecution.Primitives.Model.tval_list_to_rich_list _
              (Assertion.invariant_args invariant) invariant_values]} ∪
              held_values) ∗ frame) ∗
         term_interp_resource_prenex_at_arguments runtime formals binders
           valuation
           (IR.pexpr_list_append (held_pinned tracked held) program_arguments)
           (Translation.tval_list_append
             (held_pinned_values tracked_values held) invariant_values)
           body_post).
  { intros invariant_values.
    have Hbody_wp := Hbody _ (HeldCons invariant program_arguments
      invariant_values held)
      (held_aligned_open invariant program_arguments invariant_values held
        _ entry opened Hopen Haligned)
      Hcombined_stable tracked_values runtime formals binders valuation ambient
      Hbody_envelope (conditions_hold_nil _ _).
    unfold term_structured_runtime_wp in Hbody_wp.
    rewrite translated_runtime_wp_as_masked Hopened_mask Hinner_mask
      in Hbody_wp.
    iIntros "(#Hglobal & [Hheld_invariant Hheld_rest] & Hpre)".
    iPoseProof (Hbody_wp with "[Hheld_invariant Hheld_rest Hpre]") as "Hwp".
    { iFrame "Hglobal Hpre".
      iApply (held_world_cons_open valuation invariant program_arguments
        invariant_values held held_values Hlookup). iFrame. }
    iApply (runtime_masked_wp_mono with "Hwp").
    iIntros "(#Hglobal' & Hheld & Hpost)". iFrame "Hglobal' Hpost".
    iApply (held_world_cons_open valuation invariant program_arguments
      invariant_values held held_values Hlookup with "Hheld"). }
  unfold term_structured_runtime_wp.
  rewrite translated_runtime_wp_as_masked Hexit_mask. simpl.
  iIntros "(#Hglobal & Hheld & Hpre)".
  iPoseProof (held_world_split valuation invariant held held_values Hlookup
    with "Hheld") as "[Hheld_invariant Hheld_rest]".
  iPoseProof (term_nested_inv_access_runtime_arguments_valid invariant
    program_arguments focus_open focus_close external_pre body_pre body_post
    external_post Hopening Hclosing body (held_pinned tracked held)
    (held_pinned_values tracked_values held) runtime formals binders valuation
    (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
    held_values frame Hfresh Hbody_premise
    with "[$Hglobal $Hheld_invariant $Hheld_rest $Hpre]") as "Hwp".
  iApply (runtime_masked_wp_mono with "Hwp").
  iIntros "(#Hglobal' & [Hheld_invariant Hheld_rest] & Hpost)".
  iFrame "Hglobal' Hpost".
  iApply (held_world_split valuation invariant held held_values Hlookup).
  iFrame.
Qed.

(** The atomic-block representative of the structured runtime validity
    slice.  The trusted-atomicity refinement is agnostic in the
    post-condition, so the proof is a direct appeal to
    [term_trusted_atomic_runtime_refinement], with the resource
    interpretation substituted for the post-condition. *)
Lemma term_structured_runtime_atomic_valid
    {Γ F Δ state body outer inner}
    (step : GenericRegions.Atomicity.take_step
      GenericRegions.Atomicity.AtomicStep state = inr outer)
    (body_certificate : Structured.structured_certificate Γ
      (GenericRegions.Atomicity.atomic_entry outer)
      body inner)
    (records_equal : GenericRegions.Atomicity.analysis_records inner =
      GenericRegions.Atomicity.analysis_records outer)
    (pre post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_valid body_certificate pre post ->
  term_structured_runtime_valid
    (Structured.StructuredAtomic Γ state body outer inner step
      body_certificate records_equal) pre post.
Proof.
  intros Hbody runtime formals binders valuation ambient Henvelope.
  have Hbody_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint body_certificate ∪
        term_registered_invariants) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union in Hin as [Hin | Hregistered'].
    - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
    - apply elem_of_union_r. exact Hregistered'. }
  iIntros "Hpre".
  iPoseProof (Hbody runtime formals binders valuation ambient Hbody_envelope
    with "Hpre") as "Hwp".
  unfold term_structured_runtime_wp.
  iApply (term_trusted_atomic_runtime_refinement body_certificate
    runtime ambient _ step records_equal).
  iExact "Hwp".
Qed.

Lemma term_structured_runtime_arguments_atomic_valid
    {Γ F Δ state body outer inner ts}
    (step : GenericRegions.Atomicity.take_step
      GenericRegions.Atomicity.AtomicStep state = inr outer)
    (body_certificate : Structured.structured_certificate Γ
      (GenericRegions.Atomicity.atomic_entry outer)
      body inner)
    (records_equal : GenericRegions.Atomicity.analysis_records inner =
      GenericRegions.Atomicity.analysis_records outer)
    (conditions : list (gexpr Γ TBool))
    (tracked : gexpr_list Γ ts)
    (pre post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid body_certificate
    [] tracked pre post ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredAtomic Γ state body outer inner step
      body_certificate records_equal) conditions tracked pre post.
Proof.
  intros Hbody types held Haligned Hdisjoint values runtime formals binders
    valuation ambient Henvelope _.
  have Hbody_aligned : held_aligned
      (GenericRegions.Atomicity.analysis_records
        (GenericRegions.Atomicity.atomic_entry outer)) held.
  { cbn [GenericRegions.Atomicity.analysis_records].
    rewrite (GenericRegions.Atomicity.take_step_preserves_records _ _ _ step).
    exact Haligned. }
  cbn [Hoare.ResourceHoare.statement_writes] in Hdisjoint.
  have Hbody_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint body_certificate ∪
        term_registered_invariants) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union in Hin as [Hin | Hregistered'].
    - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
    - apply elem_of_union_r. exact Hregistered'. }
  iIntros "Hpre".
  iPoseProof (Hbody types held Hbody_aligned Hdisjoint values runtime formals
    binders valuation ambient Hbody_envelope (conditions_hold_nil _ _) with "Hpre") as "Hwp".
  unfold term_structured_runtime_wp.
  iApply (term_trusted_atomic_runtime_refinement body_certificate
    runtime ambient _ step records_equal).
  iExact "Hwp".
Qed.

(** Tracked arguments read the same locals across a ghost binder. *)
Lemma term_interp_resource_prenex_at_arguments_ghost {Γ F Δ ts}
    name t (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (valuation : symbol_valuation)
    (arguments : gexpr_list Γ ts) (values : tval_list ts)
    (prenex : Translation.Resource.resource_prenex (ghost_val t :: Γ) F Δ) :
  forall binders : binder_env Δ,
  term_interp_resource_prenex_at_arguments
      (RegionExecution.Primitives.Model.ghost_stack_context name t runtime)
      formals binders valuation (pexpr_list_shift arguments) values prenex ⊣⊢
    term_interp_resource_prenex_at_arguments runtime formals binders valuation
      arguments values (Translation.Resource.drop_head_prenex prenex).
Proof.
  induction prenex as [Δ state | Δ u rest IH]; intros binders;
    cbn [term_interp_resource_prenex_at_arguments
      Translation.Resource.drop_head_prenex].
  - destruct state as [stack body]. dependent destruction stack.
    cbn [Translation.Resource.resource_stack].
    rewrite IR.symbolize_expr_list_shift. reflexivity.
  - apply bi.exist_proper. intros value. apply IH.
Qed.

(** Entering a ghost binder: the slot holds the initializer's value. *)
Lemma term_interp_resource_prenex_at_arguments_ghost_entry {Γ F Δ ts}
    name t (initializer : gexpr Γ t)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ)
    (valuation : symbol_valuation)
    (arguments : gexpr_list Γ ts) (values : tval_list ts)
    (store : symbolic_store Γ F Δ)
    (frame : Translation.Resource.core_assertion F Δ) (value : tval t) :
  interp_expr formals binders valuation
    (IR.symbolize_expr store initializer) = Some value ->
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      arguments values (Translation.Resource.RState store frame) ⊢
  term_interp_resource_prenex_at_arguments
      (RegionExecution.Primitives.Model.ghost_stack_context name t runtime)
      formals (binder_cons value binders) valuation
      (pexpr_list_shift arguments) values
      (Translation.Resource.RState
        (StoreCons (d := ghost_val t) (RefBound MHere)
          (Translation.Assertions.weaken_store store))
        (Translation.Resource.CAnd (Translation.Resource.weaken_core frame)
          (Translation.Resource.CExpr
            (EBinOp (BEq t) (ERef (RefBound MHere))
              (Translation.Assertions.weaken_expr
                (IR.symbolize_expr store initializer)))))).
Proof.
  intros Hvalue.
  cbn [term_interp_resource_prenex_at_arguments Translation.Resource.RState
    Translation.Resource.resource_stack].
  rewrite IR.symbolize_expr_list_shift. cbn [store_tail].
  rewrite NormalizationBase.symbolize_expr_list_weaken_store.
  rewrite interp_weaken_expr_list.
  change (Translation.Resource.ResourceBody
    (Translation.Resource.ResourceState ?stack ?body)) with
    (Translation.Resource.RState stack body).
  rewrite !term_interp_rstate.
  iIntros "[[Hstack Hframe] %Harguments]".
  iSplitL; [|iPureIntro; exact Harguments].
  iSplitL "Hstack".
  - rewrite <- (interp_weaken_store formals binders valuation value store).
    iExact "Hstack".
  - unfold term_interp_core. cbn [Translation.TermSemantics.interp_core].
    rewrite Translation.TermSemantics.interp_weaken_core.
    iFrame "Hframe". iPureIntro.
    simpl. unfold binder_cons. rewrite view_member_here.
    rewrite interp_weaken_expr. rewrite Hvalue. simpl.
    rewrite (proj2 (tval_eqb_eq t value value) eq_refl). reflexivity.
Qed.

Lemma term_structured_runtime_arguments_ghost_val_valid
    {Γ F Δ entry exit ts} name t (initializer : gexpr Γ t)
    (body : stmt (ghost_val t :: Γ))
    (body_certificate : Structured.structured_certificate
      (ghost_val t :: Γ) (AnalysisView.enter_scope (length Γ)
        (RegionSyntax.argument_atom initializer) entry) body exit)
    (admissible : GenericRegions.Atomicity.leave_scope_admissible
      (length Γ) exit = true)
    (conditions : list (gexpr Γ TBool))
    (tracked : gexpr_list Γ ts)
    (store : symbolic_store Γ F Δ)
    (frame : Translation.Resource.core_assertion F Δ)
    (post : Translation.Resource.resource_prenex (ghost_val t :: Γ) F (t :: Δ)) :
  term_structured_runtime_arguments_valid body_certificate
    [] (pexpr_list_shift tracked)
    (Translation.Resource.RState
      (StoreCons (d := ghost_val t) (RefBound MHere)
        (Translation.Assertions.weaken_store store))
      (Translation.Resource.CAnd (Translation.Resource.weaken_core frame)
        (Translation.Resource.CExpr
          (EBinOp (BEq t) (ERef (RefBound MHere))
            (Translation.Assertions.weaken_expr
              (IR.symbolize_expr store initializer))))))
    post ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredGhostVal Γ entry name t initializer body exit
      body_certificate admissible)
    conditions tracked (Translation.Resource.RState store frame)
    (Translation.Resource.ResourceExists t
      (Translation.Resource.drop_head_prenex post)).
Proof.
  intros Hbody types held Haligned Hdisjoint values runtime formals binders
    valuation ambient Henvelope _.
  cbn [Hoare.ResourceHoare.statement_writes] in Hdisjoint.
  have Hbody_aligned : held_aligned
      (GenericRegions.Atomicity.analysis_records
        (AnalysisView.enter_scope (length Γ)
          (RegionSyntax.argument_atom initializer) entry))
      (held_shift (d := ghost_val t) held).
  { unfold held_aligned. rewrite held_shift_records. exact Haligned. }
  have Hbody_disjoint : Hoare.ResourceHoare.pexpr_list_dependencies
      (held_pinned (pexpr_list_shift (d := ghost_val t) tracked)
        (held_shift held)) ##
      Hoare.ResourceHoare.statement_writes body.
  { rewrite held_shift_pinned.
    exact (Hoare.ResourceHoare.pexpr_list_dependencies_shift_disjoint
      _ _ Hdisjoint). }
  specialize (Hbody types (held_shift held) Hbody_aligned Hbody_disjoint).
  have Hbody_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint body_certificate ∪
        term_registered_invariants) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union in Hin as [Hin | Hregistered'].
    - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
    - apply elem_of_union_r. exact Hregistered'. }
  destruct (interp_expr_total formals binders valuation
    (IR.symbolize_expr store initializer)) as [value Hvalue].
  specialize (Hbody values
    (RegionExecution.Primitives.Model.ghost_stack_context name t runtime)
    formals (binder_cons value binders) valuation ambient Hbody_envelope (conditions_hold_nil _ _)).
  rewrite (held_shift_pinned (d := ghost_val t) tracked held)
    (held_shift_pinned_values (d := ghost_val t) values held)
    (held_shift_world (d := ghost_val t) valuation held) in Hbody.
  iIntros "(Hworld & Hheld & Hpre)".
  iPoseProof (term_interp_resource_prenex_at_arguments_ghost_entry name t
    initializer runtime formals binders valuation (held_pinned tracked held)
    (held_pinned_values values held) store frame value Hvalue with "Hpre")
    as "Hpre".
  iPoseProof (Hbody with "[$Hworld $Hheld $Hpre]") as "Hwp".
  unfold term_structured_runtime_wp.
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "($ & $ & Hpost)". cbn [term_interp_resource_prenex_at_arguments].
  iExists value.
  iApply (term_interp_resource_prenex_at_arguments_ghost with "Hpost").
Qed.

(** Sequential composition over resource telescopes.  The intermediate
    assertion is a telescope; the certificate and the mask reasoning are
    the ordinary ones. *)
Lemma term_structured_runtime_sequence_valid
    {Γ F Δ entry first middle second exit}
    (first_certificate : Structured.structured_certificate
      Γ entry first middle)
    (second_certificate : Structured.structured_certificate
      Γ middle second exit)
    (pre middle_prenex post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_valid first_certificate pre
    middle_prenex ->
  term_structured_runtime_valid second_certificate
    middle_prenex post ->
  term_structured_runtime_valid
    (Structured.StructuredSequence Γ entry first middle second exit
      first_certificate second_certificate) pre post.
Proof.
  intros Hfirst Hsecond runtime formals binders valuation ambient Henvelope.
  have Hfirst_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint first_certificate ∪
        term_registered_invariants) ⊆ ambient.
  { etrans; last exact Henvelope. apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union in Hin as [Hin | Hregistered'].
    - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
    - apply elem_of_union_r. exact Hregistered'. }
  have Hsecond_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint second_certificate ∪
        term_registered_invariants) ⊆ ambient.
  { etrans; last exact Henvelope. apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union in Hin as [Hin | Hregistered'].
    - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
    - apply elem_of_union_r. exact Hregistered'. }
  iIntros "Hpre".
  iApply term_translated_runtime_wp_sequence.
  - exact (eq_sym
      (term_structured_certificate_preserves_open first_certificate)).
  - iPoseProof (Hfirst runtime formals binders valuation ambient Hfirst_envelope
      with "Hpre") as "Hfirst".
    iApply (translated_runtime_wp_mono with "Hfirst").
    iIntros "[Hglobal Hmiddle]".
    iApply (Hsecond runtime formals binders valuation ambient Hsecond_envelope).
    iFrame.
Qed.

Lemma term_structured_runtime_arguments_sequence_valid
    {Γ F Δ entry first middle second exit ts}
    (first_certificate : Structured.structured_certificate
      Γ entry first middle)
    (second_certificate : Structured.structured_certificate
      Γ middle second exit)
    (conditions : list (gexpr Γ TBool))
    (arguments : gexpr_list Γ ts)
    (pre middle_prenex post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid first_certificate
    [] arguments pre middle_prenex ->
  term_structured_runtime_arguments_valid second_certificate
    [] arguments middle_prenex post ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredSequence Γ entry first middle second exit
      first_certificate second_certificate) conditions arguments pre post.
Proof.
  intros Hfirst Hsecond types held Haligned Hdisjoint values runtime formals
    binders valuation ambient Henvelope _.
  cbn [Hoare.ResourceHoare.statement_writes] in Hdisjoint.
  have Hsecond_aligned : held_aligned
      (GenericRegions.Atomicity.analysis_records middle) held.
  { unfold held_aligned.
    rewrite (term_structured_certificate_preserves_records first_certificate).
    exact Haligned. }
  have Hfirst_disjoint : Hoare.ResourceHoare.pexpr_list_dependencies
      (held_pinned arguments held)
      ## Hoare.ResourceHoare.statement_writes first.
  { intros slot Harg Hwrite. apply (Hdisjoint slot Harg).
    apply elem_of_union_l. exact Hwrite. }
  have Hsecond_disjoint : Hoare.ResourceHoare.pexpr_list_dependencies
      (held_pinned arguments held)
      ## Hoare.ResourceHoare.statement_writes second.
  { intros slot Harg Hwrite. apply (Hdisjoint slot Harg).
    apply elem_of_union_r. exact Hwrite. }
  have Hfirst_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint first_certificate ∪
        term_registered_invariants) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union in Hin as [Hin | Hregistered'].
    - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
    - apply elem_of_union_r. exact Hregistered'. }
  have Hsecond_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint second_certificate ∪
        term_registered_invariants) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union in Hin as [Hin | Hregistered'].
    - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
    - apply elem_of_union_r. exact Hregistered'. }
  iIntros "Hpre". iApply term_translated_runtime_wp_sequence.
  - exact (eq_sym
      (term_structured_certificate_preserves_open first_certificate)).
  - iPoseProof (Hfirst types held Haligned Hfirst_disjoint values runtime
      formals binders valuation ambient Hfirst_envelope (conditions_hold_nil _ _) with "Hpre")
      as "Hfirst".
    iApply (translated_runtime_wp_mono with "Hfirst").
    iIntros "Hmiddle".
    iApply (Hsecond types held Hsecond_aligned Hsecond_disjoint values runtime
      formals binders valuation ambient Hsecond_envelope (conditions_hold_nil _ _) with "Hmiddle").
Qed.

Lemma conditions_hold_pinned_true {Γ ts} (condition : gexpr Γ TBool)
    (pinned : gexpr_list Γ ts) (values : tval_list ts) :
  conditions_hold [condition] (PECons condition pinned)
    (TVCons (VBool true) values).
Proof.
  intros F Δ store formals binders valuation Heval.
  cbn [IR.symbolize_expr_list] in Heval.
  apply interp_expr_list_cons_inv in Heval as (head & rest & Heq & Hhead & _).
  have Hvalue := f_equal tval_list_head Heq. cbn in Hvalue. subst head.
  constructor; [exact Hhead | constructor].
Qed.

(** A sequence whose first statement asserts a condition: the condition,
    pinned through the assertion, is known to the second statement. *)
Lemma term_structured_runtime_arguments_asserted_sequence_valid
    {Γ F Δ entry middle second exit ts} (condition : gexpr Γ TBool)
    (first_certificate : Structured.structured_certificate
      Γ entry (TAssert condition) middle)
    (second_certificate : Structured.structured_certificate
      Γ middle second exit)
    (conditions : list (gexpr Γ TBool))
    (arguments : gexpr_list Γ ts)
    (pre middle_prenex post : Translation.Resource.resource_prenex Γ F Δ) :
  CertifiedNormalization.RavenHoareRules.RavenHoareTriple pre
    (TAssert condition) middle_prenex ->
  Hoare.ResourceHoare.pexpr_dependencies condition ##
    Hoare.ResourceHoare.statement_writes second ->
  term_structured_runtime_arguments_valid first_certificate
    [] (PECons condition arguments) pre middle_prenex ->
  term_structured_runtime_arguments_valid second_certificate
    [condition] (PECons condition arguments) middle_prenex post ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredSequence Γ entry (TAssert condition) middle second
      exit first_certificate second_certificate) conditions arguments pre post.
Proof.
  intros Hassert Hstable Hfirst Hsecond types held Haligned Hdisjoint values
    runtime formals binders valuation ambient Henvelope _.
  cbn [Hoare.ResourceHoare.statement_writes] in Hdisjoint.
  have Hfirst_aligned : held_aligned
      (GenericRegions.Atomicity.analysis_records entry)
      (held_track TBool held).
  { unfold held_aligned. rewrite held_track_records. exact Haligned. }
  have Hsecond_aligned : held_aligned
      (GenericRegions.Atomicity.analysis_records middle)
      (held_track TBool held).
  { unfold held_aligned. rewrite held_track_records.
    rewrite (term_structured_certificate_preserves_records first_certificate).
    exact Haligned. }
  have Hfirst_disjoint : Hoare.ResourceHoare.pexpr_list_dependencies
      (held_pinned (PECons condition arguments) (held_track TBool held)) ##
      Hoare.ResourceHoare.statement_writes (TAssert condition).
  { cbn [Hoare.ResourceHoare.statement_writes]. apply disjoint_empty_r. }
  have Hsecond_disjoint : Hoare.ResourceHoare.pexpr_list_dependencies
      (held_pinned (PECons condition arguments) (held_track TBool held)) ##
      Hoare.ResourceHoare.statement_writes second.
  { rewrite held_track_pinned.
    cbn [Hoare.ResourceHoare.pexpr_list_dependencies].
    apply disjoint_union_l. split; [exact Hstable|].
    intros slot Harg Hwrite. apply (Hdisjoint slot Harg).
    apply elem_of_union_r. exact Hwrite. }
  have Hfirst_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint first_certificate ∪
        term_registered_invariants) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union in Hin as [Hin | Hregistered'].
    - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
    - apply elem_of_union_r. exact Hregistered'. }
  have Hsecond_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint second_certificate ∪
        term_registered_invariants) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union in Hin as [Hin | Hregistered'].
    - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
    - apply elem_of_union_r. exact Hregistered'. }
  have Hfirst_wp := Hfirst _ (held_track TBool held) Hfirst_aligned
    Hfirst_disjoint (TVCons (VBool true) values) runtime formals binders
    valuation ambient Hfirst_envelope (conditions_hold_nil _ _).
  have Hsecond_wp := Hsecond _ (held_track TBool held) Hsecond_aligned
    Hsecond_disjoint (TVCons (VBool true) values) runtime formals binders
    valuation ambient Hsecond_envelope.
  rewrite held_track_pinned held_track_pinned_values held_track_world
    in Hfirst_wp.
  rewrite held_track_pinned held_track_pinned_values held_track_world
    in Hsecond_wp.
  specialize (Hsecond_wp (conditions_hold_pinned_true condition
    (held_pinned arguments held) (held_pinned_values values held))).
  have Htrue : term_interp_resource_prenex_at_arguments runtime formals
      binders valuation (held_pinned arguments held)
      (held_pinned_values values held) pre ⊢
    term_interp_resource_prenex_at_arguments runtime formals binders valuation
      (PECons condition (held_pinned arguments held))
      (TVCons (VBool true) (held_pinned_values values held)) pre.
  { iIntros "Hpre".
    iDestruct (term_interp_resource_prenex_at_arguments_pin runtime formals
      valuation _ _ condition pre binders with "Hpre") as (truth) "Hpre".
    have Hfact : term_interp_resource_prenex_at_arguments runtime formals
        binders valuation (PECons condition (held_pinned arguments held))
        (TVCons truth (held_pinned_values values held)) pre ⊢
      ⌜truth = VBool true⌝ ∧
      term_interp_resource_prenex_at_arguments runtime formals binders
        valuation (PECons condition (held_pinned arguments held))
        (TVCons truth (held_pinned_values values held)) pre.
    { apply bi.and_intro; [|done].
      apply (term_assert_derivation_true pre middle_prenex (TAssert condition)
        Hassert condition eq_refl).
      intros Δ' store binders' Heval.
      cbn [IR.symbolize_expr_list] in Heval.
      apply interp_expr_list_cons_inv in Heval
        as (head & rest & Heq & Hhead & _).
      have Hvalue := f_equal tval_list_head Heq. cbn in Hvalue.
      subst head. exact Hhead. }
    iDestruct (Hfact with "Hpre") as "[%Htruth Hpre]". subst truth.
    iExact "Hpre". }
  iIntros "(#Hglobal & Hheld & Hpre)". iPoseProof (Htrue with "Hpre") as "Hpre".
  iApply term_translated_runtime_wp_sequence.
  - exact (eq_sym
      (term_structured_certificate_preserves_open first_certificate)).
  - iPoseProof (Hfirst_wp with "[$Hglobal $Hheld $Hpre]") as "Hfirst".
    iApply (translated_runtime_wp_mono with "Hfirst").
    iIntros "Hmiddle".
    iPoseProof (Hsecond_wp with "Hmiddle") as "Hsecond".
    iApply (translated_runtime_wp_mono with "Hsecond").
    iIntros "($ & $ & Hpost)".
    iApply (term_interp_resource_prenex_at_arguments_unpin with "Hpost").
Qed.

(** *** The remaining structural cases of the resource driver

    Six lemmas, one per rule of the Hoare calculus that leaves the
    statement and the certificate alone (or, for the conditional, splits
    both).  The only genuinely new content beyond routine structural
    recursion is [interp_store_equal_under], which the erasure could
    afford to leave as a hypothesis ([rt_stack_rewrite_admissible]) and a
    semantic driver cannot. *)


Lemma term_structured_runtime_arguments_frame_valid
    {Γ F Δ entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (conditions : list (gexpr Γ TBool))
    (tracked : gexpr_list Γ ts)
    (store : symbolic_store Γ F Δ)
    (pre_body frame : Translation.Resource.core_assertion F Δ)
    (post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid certificate
    conditions tracked (Translation.Resource.RState store pre_body) post ->
  term_structured_runtime_arguments_valid certificate
    conditions tracked
    (Translation.Resource.RState store
      (Translation.Resource.CAnd pre_body frame))
    (Translation.Resource.prenex_and post frame).
Proof.
  intros Hvalid types held Haligned Hdisjoint values runtime formals binders
    valuation ambient Henvelope Hconditions.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "(#Hglobal & Hheld & [Hstack [Hbody Hframe]] & %Harguments)".
  iPoseProof (Hvalid types held Haligned Hdisjoint values runtime formals binders valuation ambient
    Henvelope Hconditions with "[-Hframe]") as "Hwp".
  { cbn [term_interp_resource_prenex_at_arguments].
    iFrame "Hglobal Hheld Hstack Hbody". iPureIntro. exact Harguments. }
  iCombine "Hwp Hframe" as "Hwp".
  iPoseProof (translated_runtime_wp_frame with "Hwp") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[(Hglobal' & Hheld' & Hpost) Hframe]". iFrame "Hglobal' Hheld'".
  iEval (rewrite (term_interp_resource_prenex_at_arguments_and runtime
    formals binders valuation (held_pinned tracked held)
    (held_pinned_values values held) post frame)).
  iFrame.
Qed.




Lemma term_structured_runtime_arguments_prenex_preserve_valid
    {Γ F Δ t entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (conditions : list (gexpr Γ TBool))
    (arguments : gexpr_list Γ ts)
    (pre post : Translation.Resource.resource_prenex Γ F (t :: Δ)) :
  term_structured_runtime_arguments_valid certificate
    conditions arguments pre post ->
  term_structured_runtime_arguments_valid certificate
    conditions arguments (Translation.Resource.ResourceExists t pre)
      (Translation.Resource.ResourceExists t post).
Proof.
  intros Hvalid types held Haligned Hdisjoint values runtime formals binders
    valuation ambient Henvelope Hconditions.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "(#Hglobal & Hheld & Hpre)". iDestruct "Hpre" as (value) "Hbody".
  iPoseProof (Hvalid types held Haligned Hdisjoint values runtime formals
    (binder_cons value binders) valuation ambient Henvelope Hconditions
    with "[$Hglobal $Hheld $Hbody]") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "(Hglobal' & Hheld' & Hpost)". iFrame "Hglobal' Hheld'".
  iExists value. iExact "Hpost".
Qed.

Lemma term_structured_runtime_arguments_prenex_elim_valid
    {Γ F Δ t entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (conditions : list (gexpr Γ TBool))
    (arguments : gexpr_list Γ ts)
    (pre : Translation.Resource.resource_prenex Γ F (t :: Δ))
    (post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid certificate
    conditions arguments pre (Translation.Resource.weaken_resource_prenex post) ->
  term_structured_runtime_arguments_valid certificate
    conditions arguments (Translation.Resource.ResourceExists t pre) post.
Proof.
  intros Hvalid types held Haligned Hdisjoint values runtime formals binders
    valuation ambient Henvelope Hconditions.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "(#Hglobal & Hheld & Hpre)". iDestruct "Hpre" as (value) "Hbody".
  iPoseProof (Hvalid types held Haligned Hdisjoint values runtime formals
    (binder_cons value binders) valuation ambient Henvelope Hconditions
    with "[$Hglobal $Hheld $Hbody]") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "(Hglobal' & Hheld' & Hpost)". iFrame "Hglobal' Hheld'".
  iEval (rewrite (term_interp_resource_prenex_at_arguments_weaken runtime
    formals binders valuation (held_pinned arguments held)
    (held_pinned_values values held) value post)) in "Hpost".
  iExact "Hpost".
Qed.


Lemma term_structured_runtime_arguments_bound_weaken_valid
    {Γ F Δ t entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (conditions : list (gexpr Γ TBool))
    (arguments : gexpr_list Γ ts)
    (pre post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid certificate
    conditions arguments pre post ->
  term_structured_runtime_arguments_valid
    (Δ := t :: Δ) certificate
    conditions arguments
    (Translation.Resource.weaken_resource_prenex pre)
    (Translation.Resource.weaken_resource_prenex post).
Proof.
  intros Hvalid types held Haligned Hdisjoint values runtime formals binders
    valuation ambient Henvelope Hconditions.
  pose (source_binders := fun u (variable : bvar Δ u) =>
    binders u (MThere variable)).
  have Hrenaming : forall u (variable : bvar Δ u),
      binders u (Assertions.weaken_bound_renaming u variable) =
        source_binders u variable.
  { intros. reflexivity. }
  rewrite (term_interp_resource_prenex_at_arguments_rename runtime formals
    valuation (held_pinned arguments held) (held_pinned_values values held)
    pre _ Assertions.weaken_bound_renaming
    source_binders binders Hrenaming).
  iIntros "(#Hglobal & Hheld & Hpre)".
  iPoseProof (Hvalid types held Haligned Hdisjoint values runtime formals source_binders valuation
    ambient Henvelope Hconditions with "[$Hglobal $Hheld $Hpre]") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "(Hglobal' & Hheld' & Hpost)". iFrame "Hglobal' Hheld'".
  rewrite (term_interp_resource_prenex_at_arguments_rename runtime formals
    valuation (held_pinned arguments held) (held_pinned_values values held)
    post _ Assertions.weaken_bound_renaming
    source_binders binders Hrenaming).
  iExact "Hpost".
Qed.


(** The corresponding transports for the argument-indexed interpretation.
    The dependency side-condition is threaded unchanged; it is precisely
    what permits the selected telescope witnesses to remain fixed. *)
Lemma term_structured_runtime_arguments_prenex_consequence_valid
    {Γ F Δ entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (conditions : list (gexpr Γ TBool))
    (arguments : gexpr_list Γ ts)
    (pre pre' post post' : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid certificate
    conditions arguments pre post ->
  Hoare.ResourceHoare.resource_prenex_entails pre' pre ->
  Hoare.ResourceHoare.resource_prenex_entails post post' ->
  term_structured_runtime_arguments_valid certificate
    conditions arguments pre' post'.
Proof.
  intros Hvalid Hpre Hpost types held Haligned Hdisjoint values runtime formals
    binders valuation ambient Henvelope Hconditions.
  iIntros "(#Hglobal & Hheld & Hpre)".
  iPoseProof (term_interp_resource_prenex_at_arguments_entails runtime
    formals binders valuation (held_pinned arguments held)
    (held_pinned_values values held) pre' pre Hpre with "Hpre")
    as "Hpre".
  iPoseProof (Hvalid types held Haligned Hdisjoint values runtime formals binders valuation ambient
    Henvelope Hconditions with "[$Hglobal $Hheld $Hpre]") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "(Hglobal' & Hheld' & Hpost)". iFrame "Hglobal' Hheld'".
  iApply (term_interp_resource_prenex_at_arguments_entails runtime formals
    binders valuation (held_pinned arguments held)
    (held_pinned_values values held) post post' Hpost with "Hpost").
Qed.

Lemma term_structured_runtime_arguments_frame_pre_valid
    {Γ F Δ entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (conditions : list (gexpr Γ TBool))
    (arguments : gexpr_list Γ ts)
    (pre pre' post : Translation.Resource.resource_prenex Γ F Δ)
    (frame : Translation.Resource.core_assertion F Δ) :
  term_structured_runtime_arguments_valid certificate
    conditions arguments (Translation.Resource.prenex_and pre frame) post ->
  Hoare.ResourceHoare.resource_prenex_entails pre' pre ->
  term_structured_runtime_arguments_valid certificate
    conditions arguments (Translation.Resource.prenex_and pre' frame) post.
Proof.
  intros Hvalid Hpre types held Haligned Hdisjoint values runtime formals
    binders valuation ambient Henvelope Hconditions.
  iIntros "(#Hglobal & Hheld & Hframed)".
  iEval (rewrite (term_interp_resource_prenex_at_arguments_and runtime
    formals binders valuation (held_pinned arguments held)
    (held_pinned_values values held) pre' frame)) in "Hframed".
  iDestruct "Hframed" as "[Hpre Hframe]".
  iPoseProof (term_interp_resource_prenex_at_arguments_entails runtime
    formals binders valuation (held_pinned arguments held)
    (held_pinned_values values held) pre' pre Hpre with "Hpre")
    as "Hpre".
  iApply (Hvalid types held Haligned Hdisjoint values runtime formals binders valuation ambient
    Henvelope Hconditions).
  iEval (rewrite (term_interp_resource_prenex_at_arguments_and runtime
    formals binders valuation (held_pinned arguments held)
    (held_pinned_values values held) pre frame)).
  iFrame "Hglobal Hheld Hpre Hframe".
Qed.

Lemma term_structured_runtime_arguments_core_consequence_valid
    {Γ F Δ entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (conditions : list (gexpr Γ TBool))
    (arguments : gexpr_list Γ ts)
    (store : symbolic_store Γ F Δ)
    (pre_body pre_body' : Translation.Resource.core_assertion F Δ)
    (post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid certificate
    conditions arguments (Translation.Resource.RState store pre_body) post ->
  Hoare.ResourceHoare.core_entails pre_body' pre_body ->
  term_structured_runtime_arguments_valid certificate
    conditions arguments (Translation.Resource.RState store pre_body') post.
Proof.
  intros Hvalid Hpre types held Haligned Hdisjoint values runtime formals
    binders valuation ambient Henvelope Hconditions.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "(#Hglobal & Hheld & [Hstack Hbody] & %Harguments)".
  iPoseProof (Validation.TermSemantics.core_entails_valid semantic_data
    (term_predicates valuation) _ _ Hpre formals binders valuation with "Hbody")
    as "Hbody".
  iPoseProof (Hvalid types held Haligned Hdisjoint values runtime formals binders valuation ambient
    Henvelope Hconditions with "[-]") as "Hwp".
  { iFrame "Hglobal Hheld Hstack Hbody". iPureIntro. exact Harguments. }
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "(Hglobal' & Hheld' & Hpost)". iFrame "Hglobal' Hheld'".
  iExact "Hpost".
Qed.

Lemma term_structured_runtime_arguments_stack_rewrite_valid
    {Γ F Δ entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (conditions : list (gexpr Γ TBool))
    (arguments : gexpr_list Γ ts)
    (store store' : symbolic_store Γ F Δ)
    (body : Translation.Resource.core_assertion F Δ)
    (post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid certificate
    conditions arguments (Translation.Resource.RState store body) post ->
  Hoare.ResourceHoare.store_equal_under body Γ store' store ->
  term_structured_runtime_arguments_valid certificate
    conditions arguments (Translation.Resource.RState store' body) post.
Proof.
  intros Hvalid Hstore types held Haligned Hdisjoint values runtime formals
    binders valuation ambient Henvelope Hconditions.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "(#Hglobal & Hheld & [Hstack Hbody] & %Harguments)".
  iAssert (⌜interp_store formals binders valuation store' =
             interp_store formals binders valuation store⌝)%I
    with "[Hbody]" as "%Hequal".
  { iApply (interp_store_equal_under body store store' Hstore). iExact "Hbody". }
  rewrite Hequal.
  iApply (Hvalid types held Haligned Hdisjoint values runtime formals binders valuation ambient
    Henvelope Hconditions).
  cbn [term_interp_resource_prenex_at_arguments].
  iFrame "Hglobal Hheld Hstack Hbody".
  iPureIntro.
  have Hargument_interp := interp_program_expr_list_store_ext formals
    binders valuation store' store (held_pinned arguments held) Hequal.
  unfold interp_program_expr_list in Hargument_interp.
  rewrite Harguments in Hargument_interp. symmetry. exact Hargument_interp.
Qed.

Lemma term_structured_runtime_arguments_conditional_valid
    {Γ F Δ state condition then_branch else_branch
     then_exit else_exit ts}
    (then_certificate : Structured.structured_certificate
      Γ state then_branch then_exit)
    (else_certificate : Structured.structured_certificate
      Γ state else_branch else_exit)
    (records_equal : GenericRegions.Atomicity.analysis_records then_exit =
      GenericRegions.Atomicity.analysis_records else_exit)
    (atomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (conditions : list (gexpr Γ TBool))
    (arguments : gexpr_list Γ ts)
    (store : symbolic_store Γ F Δ)
    (body : Translation.Resource.core_assertion F Δ)
    (post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid then_certificate
    [] arguments
    (Translation.Resource.RState store
      (Translation.Resource.CAnd body
        (Translation.Resource.CExpr (IR.symbolize_expr store condition))))
    post ->
  term_structured_runtime_arguments_valid else_certificate
    [] arguments
    (Translation.Resource.RState store
      (Translation.Resource.CAnd body
        (Translation.Resource.CExpr (EUnOp UNot
          (IR.symbolize_expr store condition))))) post ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredConditional Γ state condition
      then_branch else_branch then_exit else_exit then_certificate
      else_certificate records_equal atomic_equal)
    conditions arguments (Translation.Resource.RState store body) post.
Proof.
  intros Hthen Helse types held Haligned Hdisjoint values runtime formals
    binders valuation ambient Henvelope _.
  cbn [Hoare.ResourceHoare.statement_writes] in Hdisjoint.
  have Hthen_disjoint : Hoare.ResourceHoare.pexpr_list_dependencies
      (held_pinned arguments held)
      ## Hoare.ResourceHoare.statement_writes then_branch.
  { intros slot Hargument Hwrite. apply (Hdisjoint slot Hargument).
    apply elem_of_union_l. exact Hwrite. }
  have Helse_disjoint : Hoare.ResourceHoare.pexpr_list_dependencies
      (held_pinned arguments held)
      ## Hoare.ResourceHoare.statement_writes else_branch.
  { intros slot Hargument Hwrite. apply (Hdisjoint slot Hargument).
    apply elem_of_union_r. exact Hwrite. }
  have Hthen_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint then_certificate ∪
        term_registered_invariants) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union in Hin as [Hin | Hregistered'].
    - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
    - apply elem_of_union_r. exact Hregistered'. }
  have Helse_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint else_certificate ∪
        term_registered_invariants) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union in Hin as [Hin | Hregistered'].
    - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
    - apply elem_of_union_r. exact Hregistered'. }
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "(#Hglobal & Hheld & [Hstack Hbody] & %Harguments)".
  destruct (interp_expr_total formals binders valuation
    (IR.symbolize_expr store condition)) as [value Hvalue].
  dependent destruction value. destruct b.
  - iApply (translated_runtime_wp_if_total_join runtime formals binders valuation
      store ambient state condition then_branch else_branch then_exit
      else_exit
      (global_world_context valuation ∗ held_world valuation held ∗
       term_interp_resource_prenex_at_arguments runtime formals binders valuation
         (held_pinned arguments held) (held_pinned_values values held) post)
      (global_world_context valuation ∗ held_world valuation held ∗
       (term_interp_core formals binders valuation body ∗
        ⌜interp_expr_list formals binders valuation
          (IR.symbolize_expr_list store (held_pinned arguments held)) =
          Some (held_pinned_values values held)⌝)) records_equal).
    + intros _. iIntros "[Hstack (#Hglobal' & Hheld & Hbody & %Harguments')]".
      iApply (Hthen types held Haligned Hthen_disjoint values runtime formals binders valuation ambient
        Hthen_envelope (conditions_hold_nil _ _)).
      cbn [term_interp_resource_prenex_at_arguments].
      iFrame "Hglobal' Hheld Hstack Hbody". iPureIntro. split;
        [exact Hvalue | exact Harguments'].
    + intros Hfalse. rewrite Hvalue in Hfalse. discriminate.
    + iFrame "Hstack Hglobal Hheld Hbody". iPureIntro. exact Harguments.
  - iApply (translated_runtime_wp_if_total_join runtime formals binders valuation
      store ambient state condition then_branch else_branch then_exit
      else_exit
      (global_world_context valuation ∗ held_world valuation held ∗
       term_interp_resource_prenex_at_arguments runtime formals binders valuation
         (held_pinned arguments held) (held_pinned_values values held) post)
      (global_world_context valuation ∗ held_world valuation held ∗
       (term_interp_core formals binders valuation body ∗
        ⌜interp_expr_list formals binders valuation
          (IR.symbolize_expr_list store (held_pinned arguments held)) =
          Some (held_pinned_values values held)⌝)) records_equal).
    + intros Htrue. rewrite Hvalue in Htrue. discriminate.
    + intros _. iIntros "[Hstack (#Hglobal' & Hheld & Hbody & %Harguments')]".
      iApply (Helse types held Haligned Helse_disjoint values runtime formals binders valuation ambient
        Helse_envelope (conditions_hold_nil _ _)).
      cbn [term_interp_resource_prenex_at_arguments].
      iFrame "Hglobal' Hheld Hstack Hbody". iPureIntro. split.
      * simpl. rewrite Hvalue. reflexivity.
      * exact Harguments'.
    + iFrame "Hstack Hglobal Hheld Hbody". iPureIntro. exact Harguments.
Qed.

Lemma term_structured_runtime_arguments_ghost_conditional_valid
    {Γ F Δ state condition then_branch else_branch
     then_exit else_exit ts}
    (then_certificate : Structured.structured_certificate
      Γ state then_branch then_exit)
    (else_certificate : Structured.structured_certificate
      Γ state else_branch else_exit)
    (records_equal : GenericRegions.Atomicity.analysis_records then_exit =
      GenericRegions.Atomicity.analysis_records else_exit)
    (atomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (conditions : list (gexpr Γ TBool))
    (arguments : gexpr_list Γ ts)
    (store : symbolic_store Γ F Δ)
    (body : Translation.Resource.core_assertion F Δ)
    (post : Translation.Resource.resource_prenex Γ F Δ)
    (then_proof_only : proof_onlyb then_branch = true)
    (else_proof_only : proof_onlyb else_branch = true) :
  term_structured_runtime_arguments_valid then_certificate
    [] arguments
    (Translation.Resource.RState store
      (Translation.Resource.CAnd body
        (Translation.Resource.CExpr (IR.symbolize_expr store condition))))
    post ->
  term_structured_runtime_arguments_valid else_certificate
    [] arguments
    (Translation.Resource.RState store
      (Translation.Resource.CAnd body
        (Translation.Resource.CExpr (EUnOp UNot
          (IR.symbolize_expr store condition))))) post ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredGhostConditional Γ state condition
      then_branch else_branch then_exit else_exit then_certificate
      else_certificate records_equal atomic_equal)
    conditions arguments (Translation.Resource.RState store body) post.
Proof.
  intros Hthen Helse types held Haligned Hdisjoint values runtime formals
    binders valuation ambient Henvelope _.
  cbn [Hoare.ResourceHoare.statement_writes] in Hdisjoint.
  have Hthen_disjoint : Hoare.ResourceHoare.pexpr_list_dependencies
      (held_pinned arguments held)
      ## Hoare.ResourceHoare.statement_writes then_branch.
  { intros slot Hargument Hwrite. apply (Hdisjoint slot Hargument).
    apply elem_of_union_l. exact Hwrite. }
  have Helse_disjoint : Hoare.ResourceHoare.pexpr_list_dependencies
      (held_pinned arguments held)
      ## Hoare.ResourceHoare.statement_writes else_branch.
  { intros slot Hargument Hwrite. apply (Hdisjoint slot Hargument).
    apply elem_of_union_r. exact Hwrite. }
  have Hthen_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint then_certificate ∪
        term_registered_invariants) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union in Hin as [Hin | Hregistered'].
    - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
    - apply elem_of_union_r. exact Hregistered'. }
  have Helse_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint else_certificate ∪
        term_registered_invariants) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union in Hin as [Hin | Hregistered'].
    - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
    - apply elem_of_union_r. exact Hregistered'. }
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "(#Hglobal & Hheld & [Hstack Hbody] & %Harguments)".
  destruct (interp_expr_total formals binders valuation
    (IR.symbolize_expr store condition)) as [value Hvalue].
  dependent destruction value. destruct b.
  - iApply (translated_runtime_wp_ghost_if_total_join runtime formals binders valuation
      store ambient state condition then_branch else_branch then_exit
      else_exit
      (global_world_context valuation ∗ held_world valuation held ∗
       term_interp_resource_prenex_at_arguments runtime formals binders valuation
         (held_pinned arguments held) (held_pinned_values values held) post)
      (global_world_context valuation ∗ held_world valuation held ∗
       (term_interp_core formals binders valuation body ∗
        ⌜interp_expr_list formals binders valuation
          (IR.symbolize_expr_list store (held_pinned arguments held)) =
          Some (held_pinned_values values held)⌝)) records_equal
      then_proof_only else_proof_only).
    + intros _. iIntros "[Hstack (#Hglobal' & Hheld & Hbody & %Harguments')]".
      iApply (Hthen types held Haligned Hthen_disjoint values runtime formals binders valuation ambient
        Hthen_envelope (conditions_hold_nil _ _)).
      cbn [term_interp_resource_prenex_at_arguments].
      iFrame "Hglobal' Hheld Hstack Hbody". iPureIntro. split;
        [exact Hvalue | exact Harguments'].
    + intros Hfalse. rewrite Hvalue in Hfalse. discriminate.
    + iFrame "Hstack Hglobal Hheld Hbody". iPureIntro. exact Harguments.
  - iApply (translated_runtime_wp_ghost_if_total_join runtime formals binders valuation
      store ambient state condition then_branch else_branch then_exit
      else_exit
      (global_world_context valuation ∗ held_world valuation held ∗
       term_interp_resource_prenex_at_arguments runtime formals binders valuation
         (held_pinned arguments held) (held_pinned_values values held) post)
      (global_world_context valuation ∗ held_world valuation held ∗
       (term_interp_core formals binders valuation body ∗
        ⌜interp_expr_list formals binders valuation
          (IR.symbolize_expr_list store (held_pinned arguments held)) =
          Some (held_pinned_values values held)⌝)) records_equal
      then_proof_only else_proof_only).
    + intros Htrue. rewrite Hvalue in Htrue. discriminate.
    + intros _. iIntros "[Hstack (#Hglobal' & Hheld & Hbody & %Harguments')]".
      iApply (Helse types held Haligned Helse_disjoint values runtime formals binders valuation ambient
        Helse_envelope (conditions_hold_nil _ _)).
      cbn [term_interp_resource_prenex_at_arguments].
      iFrame "Hglobal' Hheld Hstack Hbody". iPureIntro. split.
      * simpl. rewrite Hvalue. reflexivity.
      * exact Harguments'.
    + iFrame "Hstack Hglobal Hheld Hbody". iPureIntro. exact Harguments.
Qed.


(** Allocation over resource telescopes.  Like the other ambient rules,
    this appeals to the runtime allocation primitive directly:
    the ghost-initializer validity side condition and the allocated-fields
    telescope are both read through their core-shaped interpretations, so the
    rule never mentions the assertion representation. *)
Lemma term_ambient_allocation_rule_valid {Γ F Δ}
    (store : symbolic_store Γ F Δ) {init} (target : write_target init Γ TRef)
    fields (entry exit : GenericRegions.Atomicity.analysis_state) :
  NoDup (map field_init_id fields) ->
  NoDup (map ghost_field_init_id (ghost_field_initializers fields)) ->
  ghost_initializers_require_physical fields ->
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    ↑ghost_heap_namespace ⊆
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry ->
    term_interp_resource_prenex runtime formals binders valuation
      (Translation.Resource.RState store
        (Hoare.ResourceHoare.ghost_initializers_valid_core store
          (ghost_field_initializers fields))) ⊢
    concrete_operation_wp runtime ambient entry (TAlloc init target fields) exit
      (term_interp_resource_prenex runtime formals binders valuation
        (Translation.Resource.ResourceExists TRef
          (Translation.Resource.RState
            (IR.update_store_with_bound store target)
            (Hoare.ResourceHoare.allocated_fields_core store fields)))).
Proof.
  intros Hnodup Hghostnodup Hphysical runtime formals binders valuation
    ambient Hghostmask.
  unfold concrete_operation_wp, RegionExecution.Primitives.operation_wp.
  simpl. unfold RegionExecution.Primitives.ambient_leaf_wp.
  simpl. unfold RegionExecution.Primitives.ambient_physical_leaf_wp.
  rewrite term_interp_rstate. iIntros "[Hstack Hvalid]".
  iDestruct (term_valid_ghost_initializers_semantic_core formals binders valuation
    store (ghost_field_initializers fields) with "Hvalid") as %Hvalid.
  iPoseProof (@RegionExecution.Primitives.Model.runtime_allocation_wp _ _ Σ RG Γ F Δ
    runtime formals binders valuation store init target fields
    (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
    Hnodup Hghostnodup Hphysical Hvalid with "Hstack") as "Hwp".
  { rewrite Hruntime_ghost_namespace. exact Hghostmask. }
  iEval (unfold RegionExecution.Primitives.Model.runtime_wp) in "Hwp".
  unfold RegionExecution.Primitives.Model.runtime_wp.
  iApply (wp_mono with "Hwp").
  iIntros (result) "[%Hresult Hpost]". iSplit; first done.
  iDestruct "Hpost" as (address) "[Hstack Hfields]".
  rewrite term_interp_resource_exists.
  iExists (VRef address). rewrite term_interp_rstate. iFrame "Hstack".
  iApply (term_ambient_allocated_fields_rule_interp_core runtime formals
    binders valuation store fields address with "Hfields").
Qed.

(** The predicate-definition compatibility the resource fold/unfold
    leaves need.  The premise comes from
    [TermLeaf.term_predicate_instantiation_valid]; since the resource
    body *is* [ResourceInstances.instantiated_predicate], the premise is
    discharged once, here, rather than separately at each leaf. *)
Lemma term_interp_core_instantiated_predicate {Γ F Δ}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    predicate
    (arguments : Translation.Assertions.expr_list F Δ
      (Assertion.predicate_args predicate)) :
  term_interp_core formals binders valuation
      (ResourceInstances.instantiated_predicate predicate arguments) ≡
    term_interp_core formals binders valuation
      (Translation.Resource.CPredicate predicate arguments).
Proof.
  exact (@TermLeaf.term_predicate_instantiation_valid _ _ _ (iPropI Σ) semantic_data
    Leaf F Δ formals binders valuation predicate arguments).
Qed.

(** A single-slot stack update preserves every program expression whose
    syntactic dependency set excludes that slot. *)
Lemma interp_program_expr_update_store_with_bound_disjoint
    {Γ F Δ keep keep' t u}
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (target : lvar keep Γ u)
    (value : tval u) (expression : pexpr keep' Γ t) :
  Hoare.ResourceHoare.pexpr_dependencies expression ##
      ({[lvar_index target]} : gset nat) ->
  interp_program_expr formals (binder_cons value binders) valuation
      (IR.update_store_with_bound store target) expression =
    interp_program_expr formals binders valuation store expression.
Proof.
  intro Hdisjoint. induction expression; cbn [interp_program_expr] in *.
  - have Hneq : lvar_index variable <> lvar_index target.
    { intro Heq. apply (Hdisjoint (lvar_index variable)).
      - apply elem_of_singleton_2. reflexivity.
      - apply elem_of_singleton_2. exact Heq. }
    unfold interp_program_expr. cbn [IR.symbolize_expr interp_expr].
    rewrite IR.lookup_update_store_with_bound_other; [|exact Hneq].
    f_equal. apply Translation.interp_weaken_ref.
  - reflexivity.
  - unfold interp_program_expr in *.
    cbn [IR.symbolize_expr interp_expr] in *.
    rewrite (IHexpression Hdisjoint). reflexivity.
  - unfold interp_program_expr in *.
    cbn [IR.symbolize_expr interp_expr] in *.
    have Hleft : Hoare.ResourceHoare.pexpr_dependencies expression1 ##
        ({[lvar_index target]} : gset nat).
    { intros slot Hin1 Hin2. apply (Hdisjoint slot); [apply elem_of_union_l |];
        assumption. }
    have Hright : Hoare.ResourceHoare.pexpr_dependencies expression2 ##
        ({[lvar_index target]} : gset nat).
    { intros slot Hin1 Hin2. apply (Hdisjoint slot); [apply elem_of_union_r |];
        assumption. }
    rewrite (IHexpression1 Hleft). rewrite (IHexpression2 Hright). reflexivity.
Qed.

Lemma interp_program_expr_list_update_store_with_bound_disjoint
    {Γ F Δ keep keep' ts u}
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (target : lvar keep Γ u)
    (value : tval u) (expressions : pexpr_list keep' Γ ts) :
  Hoare.ResourceHoare.pexpr_list_dependencies expressions ##
      ({[lvar_index target]} : gset nat) ->
  interp_program_expr_list formals (binder_cons value binders) valuation
      (IR.update_store_with_bound store target) expressions =
    interp_program_expr_list formals binders valuation store expressions.
Proof.
  intro Hdisjoint. induction expressions; cbn [interp_program_expr_list] in *.
  - reflexivity.
  - have Hhead : Hoare.ResourceHoare.pexpr_dependencies p ##
        ({[lvar_index target]} : gset nat).
    { intros slot Hin1 Hin2. apply (Hdisjoint slot); [apply elem_of_union_l |];
        assumption. }
    have Htail : Hoare.ResourceHoare.pexpr_list_dependencies expressions ##
        ({[lvar_index target]} : gset nat).
    { intros slot Hin1 Hin2. apply (Hdisjoint slot); [apply elem_of_union_r |];
        assumption. }
    unfold interp_program_expr_list in *.
    cbn [IR.symbolize_expr_list interp_expr_list] in *.
    have Hhead_equal :=
      interp_program_expr_update_store_with_bound_disjoint formals binders
        valuation store target value p Hhead.
    unfold interp_program_expr in Hhead_equal.
    rewrite Hhead_equal.
    rewrite (IHexpressions Htail). reflexivity.
Qed.

(** *** Ordinary leaf operations, over resource telescopes

    The derivation is in [RavenHoareRules] and the pre- and postconditions
    are resource telescopes.

    Every leaf rule has an ambient lemma, so no case crosses into the
    assertion representation.  The call and spawn rules go through
    [procedure_leaf_operation_valid] with the obligations of
    [call_discard_obligation] and its siblings. *)
Lemma term_registered_mask_active_closed entry ambient :
  GenericRegions.Atomicity.analysis_open entry = ∅ ->
  RegionExecution.Primitives.Model.runtime_mask term_registered_invariants ⊆
    ambient ->
  RegionExecution.Primitives.Model.runtime_mask term_registered_invariants ⊆
    RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
Proof.
  intros Hclosed Henvelope.
  rewrite (RegionExecution.Primitives.Model.active_runtime_mask_closed ambient
    entry Hclosed). exact Henvelope.
Qed.

Lemma term_resource_prenex_ordinary_leaf_operation_valid : forall {Γ F Δ}
    (pre post : Translation.Resource.resource_prenex Γ F Δ)
    statement entry exit,
  RegionSyntax.view statement = AnalysisView.ViewLeaf ->
  GenericRegions.Atomicity.take_leaf (RegionSyntax.cost Γ statement)
    (RegionSyntax.write statement) entry = inr exit ->
  Certified.procedure_cost_model_sound ->
  CertifiedNormalization.RavenHoareRules.leaf_triple pre statement post ->
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.analysis_mask exit) ⊆
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry ->
    RegionExecution.Primitives.Model.runtime_mask term_registered_invariants ⊆
      ambient ->
    (global_world_context valuation ∗
      term_interp_resource_prenex runtime formals binders valuation pre) ⊢
    concrete_operation_wp runtime ambient entry statement exit
      (term_interp_resource_prenex runtime formals binders valuation post).
Proof.
  intros Γ F Δ pre post statement entry exit Hview Hstep Hcost
    Htriple.
  induction Htriple; intros runtime formals binders valuation ambient Henvelope
    Hregistry;
    simpl in Hview; try discriminate.
  - (* assert *)
    iIntros "[_ Hpre]". iApply term_ambient_assert_rule_valid.
    iExact "Hpre".
  - (* assignment *)
    iIntros "[_ Hpre]". iApply term_ambient_assignment_rule_valid.
    iExact "Hpre".
  - (* field read *)
    iIntros "[_ Hpre]". iApply term_ambient_field_read_rule_valid.
    iExact "Hpre".
  - (* field write *)
    iIntros "[_ Hpre]". iApply term_ambient_field_write_rule_valid.
    iExact "Hpre".
  - (* allocation *)
    iIntros "[_ Hpre]". iApply term_ambient_allocation_rule_valid;
      [exact H | exact H0 | exact H1 | |].
    + etrans; last exact Henvelope. intros name Hname.
      unfold RegionExecution.Primitives.Model.runtime_mask.
      apply elem_of_union. right. exact Hname.
    + iExact "Hpre".
  - (* ghost update *)
    iIntros "[_ Hpre]". iApply term_ambient_ghost_update_rule_valid.
    iExact "Hpre".
  - (* predicate unfold *)
    iIntros "[_ Hpre]".
    iApply term_ambient_predicate_unfold_rule_valid;
      [apply (term_interp_core_instantiated_predicate runtime) |].
    iExact "Hpre".
  - (* predicate fold *)
    iIntros "[_ Hpre]".
    iApply term_ambient_predicate_fold_rule_valid;
      [apply (term_interp_core_instantiated_predicate runtime) |].
    iExact "Hpre".
  - (* call, result discarded *)
    have Hfacts := Certified.certified_call_step_effect Hcost Γ
      procedure typed_arguments
      (@Hoare.IR.CTDiscard Γ (Assertion.procedure_return procedure))
      entry exit Hstep.
    destruct Hfacts as (Hrequired & Hclosed & Hmask & _).
    iIntros "[#Hglobal Hpre]".
    iApply (procedure_leaf_operation_valid _ _ _
      (GenericRegions.Atomicity.analysis_mask entry)
      (GenericRegions.Atomicity.analysis_mask exit) entry exit
      (call_discard_obligation procedure store typed_arguments
        (GenericRegions.Atomicity.analysis_mask entry) _ H Hrequired Hmask)
      with "[$Hglobal $Hpre]").
    + exact Henvelope.
    + eapply term_registered_mask_active_closed; [exact Hclosed|exact Hregistry].
  - (* call, result stored *)
    have Hfacts := Certified.certified_call_step_effect Hcost Γ
      procedure typed_arguments (Hoare.IR.CTStore init target) entry exit
      Hstep.
    destruct Hfacts as (Hrequired & Hclosed & Hmask & _).
    iIntros "[#Hglobal Hpre]".
    iApply (procedure_leaf_operation_valid _ _ _
      (GenericRegions.Atomicity.analysis_mask entry)
      (GenericRegions.Atomicity.analysis_mask exit) entry exit
      (call_store_obligation procedure store target
        typed_arguments (GenericRegions.Atomicity.analysis_mask entry) _ H
        Hrequired Hmask)
      with "[$Hglobal $Hpre]").
    + exact Henvelope.
    + eapply term_registered_mask_active_closed; [exact Hclosed|exact Hregistry].
  - (* spawn *)
    have Hfacts := Certified.certified_spawn_step_effect Hcost
      _ _ _ _ _ Hstep.
    destruct Hfacts as (Hrequired & Hclosed & ->).
    iIntros "[#Hglobal Hpre]".
    iApply (procedure_leaf_operation_valid _ _ _
      (GenericRegions.Atomicity.analysis_mask entry)
      (GenericRegions.Atomicity.analysis_mask entry) entry entry
      (spawn_obligation procedure store typed_arguments
        (GenericRegions.Atomicity.analysis_mask entry) _ H Hrequired
        (reflexivity _))
      with "[$Hglobal $Hpre]").
    + exact Henvelope.
    + eapply term_registered_mask_active_closed; [exact Hclosed|exact Hregistry].
  Unshelve. all: eauto.
Qed.

Lemma term_structured_runtime_resource_prenex_leaf_valid
    {Γ F Δ entry statement exit}
    (view : RegionSyntax.view statement = AnalysisView.ViewLeaf)
    (step : GenericRegions.Atomicity.take_leaf (RegionSyntax.cost Γ statement)
      (RegionSyntax.write statement) entry = inr exit)
    (pre post : Translation.Resource.resource_prenex Γ F Δ)
    (derivation : CertifiedNormalization.RavenHoareRules.leaf_triple
      pre statement post)
    (Hwf : GenericRegions.Atomicity.state_wf entry)
    (Hprocedure : Certified.procedure_cost_model_sound) :
  term_structured_runtime_valid
    (Structured.StructuredLeaf Γ entry statement exit view step) pre post.
Proof.
  intros runtime formals binders valuation ambient Henvelope.
  have Hopen := GenericRegions.Atomicity.take_leaf_preserves_open _ _ _ _ step.
  have Hexit_envelope : RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.analysis_mask exit) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union_l.
    apply Structured.structured_certificate_exit_subset_footprint. exact Hin. }
  have Hactive_exit :=
    RegionExecution.Primitives.Model.runtime_mask_subset_active ambient exit
      Hexit_envelope.
  have Hactive : RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.analysis_mask exit) ⊆
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
  { change (RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.analysis_mask exit) ⊆
      ambient ∖ RegionExecution.Primitives.Model.invariant_mask
        (GenericRegions.Atomicity.analysis_open exit)) in Hactive_exit.
    change (RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.analysis_mask exit) ⊆
      ambient ∖ RegionExecution.Primitives.Model.invariant_mask
        (GenericRegions.Atomicity.analysis_open entry)).
    rewrite <- Hopen. exact Hactive_exit. }
  have Hregistry : RegionExecution.Primitives.Model.runtime_mask
      term_registered_invariants ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union_r. exact Hin. }
  unfold term_structured_runtime_valid, term_structured_runtime_wp.
  iIntros "[#Hglobal Hpre]".
  iPoseProof (term_resource_prenex_ordinary_leaf_operation_valid
    pre post statement entry exit view step Hprocedure derivation runtime
    formals binders valuation ambient Hactive Hregistry
      with "[$Hglobal $Hpre]") as "Hleaf".
  iPoseProof (@concrete_operation_wp_frame Γ runtime ambient entry statement
    exit (term_interp_resource_prenex runtime formals binders valuation post)
    (global_world_context valuation) with "[$Hleaf $Hglobal]") as "Hleaf".
  iPoseProof (term_leaf_operation_to_translated runtime ambient entry exit
    statement _ view (eq_sym Hopen) with "Hleaf") as "Hleaf".
  iApply (translated_runtime_wp_mono with "Hleaf").
  iIntros "[Hpost Hglobal']". iFrame.
Qed.

(** Argument-preserving lifts for the three store shapes produced by genuine
    leaf rules.  Structural proof rules are handled by the outer induction,
    so the leaf layer needs no second dispatcher induction. *)
Lemma term_structured_runtime_arguments_same_store_valid
    {Γ F Δ entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (conditions : list (gexpr Γ TBool))
    (tracked : gexpr_list Γ ts) (store : symbolic_store Γ F Δ)
    (pre_body post_body : Translation.Resource.core_assertion F Δ) :
  term_structured_runtime_valid certificate
    (Translation.Resource.RState store pre_body)
    (Translation.Resource.RState store post_body) ->
  term_structured_runtime_arguments_valid certificate
    conditions tracked (Translation.Resource.RState store pre_body)
      (Translation.Resource.RState store post_body).
Proof.
  intros Hvalid types held _ _ values runtime formals binders valuation ambient Henvelope _.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "(#Hglobal & Hheld & Hpre & %Harguments)".
  iPoseProof (Hvalid runtime formals binders valuation ambient Henvelope
    with "[$Hglobal $Hpre]") as "Hwp".
  iAssert (⌜interp_expr_list formals binders valuation
      (IR.symbolize_expr_list store (held_pinned tracked held)) =
        Some (held_pinned_values values held)⌝)%I
    with "[]" as "Harguments_saved".
  { iPureIntro. exact Harguments. }
  iCombine "Hwp Hheld Harguments_saved" as "Hwp".
  iPoseProof (translated_runtime_wp_frame with "Hwp") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[[Hglobal' Hpost] [Hheld' %Harguments']]". iFrame "Hglobal' Hheld' Hpost".
  iPureIntro. exact Harguments'.
Qed.

Lemma term_structured_runtime_arguments_updated_store_valid
    {Γ F Δ entry statement exit ts u}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (conditions : list (gexpr Γ TBool))
    (tracked : gexpr_list Γ ts) (store : symbolic_store Γ F Δ)
    {init} (target : write_target init Γ u)
    (pre_body : Translation.Resource.core_assertion F Δ)
    (post_body : Translation.Resource.core_assertion F (u :: Δ)) :
  Hoare.ResourceHoare.statement_writes statement =
    ({[lvar_index target]} : gset nat) ->
  term_structured_runtime_valid certificate
    (Translation.Resource.RState store pre_body)
    (Translation.Resource.ResourceExists u
      (Translation.Resource.RState
        (IR.update_store_with_bound store target) post_body)) ->
  term_structured_runtime_arguments_valid certificate
    conditions tracked (Translation.Resource.RState store pre_body)
      (Translation.Resource.ResourceExists u
        (Translation.Resource.RState
          (IR.update_store_with_bound store target) post_body)).
Proof.
  intros Hwrites Hvalid types held _ Hdisjoint values runtime formals binders
    valuation ambient Henvelope _.
  rewrite Hwrites in Hdisjoint.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "(#Hglobal & Hheld & Hpre & %Harguments)".
  iPoseProof (Hvalid runtime formals binders valuation ambient Henvelope
    with "[$Hglobal $Hpre]") as "Hwp".
  iAssert (⌜interp_expr_list formals binders valuation
      (IR.symbolize_expr_list store (held_pinned tracked held)) =
        Some (held_pinned_values values held)⌝)%I
    with "[]" as "Harguments_saved".
  { iPureIntro. exact Harguments. }
  iCombine "Hwp Hheld Harguments_saved" as "Hwp".
  iPoseProof (translated_runtime_wp_frame with "Hwp") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[[Hglobal' Hpost] [Hheld' %Harguments']]". iFrame "Hglobal' Hheld'".
  iEval (rewrite term_interp_resource_exists) in "Hpost".
  iDestruct "Hpost" as (result) "Hpost".
  iExists result. cbn [term_interp_resource_prenex_at_arguments].
  iFrame "Hpost". iPureIntro.
  have Hstable := interp_program_expr_list_update_store_with_bound_disjoint
    formals binders valuation store target result (held_pinned tracked held) Hdisjoint.
  unfold interp_program_expr_list in Hstable.
  rewrite Harguments' in Hstable. exact Hstable.
Qed.

Lemma term_structured_runtime_arguments_weakened_store_valid
    {Γ F Δ entry statement exit ts u}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (conditions : list (gexpr Γ TBool))
    (tracked : gexpr_list Γ ts) (store : symbolic_store Γ F Δ)
    (pre_body : Translation.Resource.core_assertion F Δ)
    (post_body : Translation.Resource.core_assertion F (u :: Δ)) :
  term_structured_runtime_valid certificate
    (Translation.Resource.RState store pre_body)
    (Translation.Resource.ResourceExists u
      (Translation.Resource.RState (weaken_store store) post_body)) ->
  term_structured_runtime_arguments_valid certificate
    conditions tracked (Translation.Resource.RState store pre_body)
      (Translation.Resource.ResourceExists u
        (Translation.Resource.RState (weaken_store store) post_body)).
Proof.
  intros Hvalid types held _ _ values runtime formals binders valuation ambient Henvelope _.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "(#Hglobal & Hheld & Hpre & %Harguments)".
  iPoseProof (Hvalid runtime formals binders valuation ambient Henvelope
    with "[$Hglobal $Hpre]") as "Hwp".
  iAssert (⌜interp_expr_list formals binders valuation
      (IR.symbolize_expr_list store (held_pinned tracked held)) =
        Some (held_pinned_values values held)⌝)%I
    with "[]" as "Harguments_saved".
  { iPureIntro. exact Harguments. }
  iCombine "Hwp Hheld Harguments_saved" as "Hwp".
  iPoseProof (translated_runtime_wp_frame with "Hwp") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[[Hglobal' Hpost] [Hheld' %Harguments']]". iFrame "Hglobal' Hheld'".
  iEval (rewrite term_interp_resource_exists) in "Hpost".
  iDestruct "Hpost" as (result) "Hpost".
  iExists result. cbn [term_interp_resource_prenex_at_arguments].
  iFrame "Hpost". iPureIntro.
  rewrite NormalizationBase.symbolize_expr_list_weaken_store.
  rewrite Translation.interp_weaken_expr_list. exact Harguments'.
Qed.

Lemma term_structured_runtime_arguments_fresh_fold_valid
    {Γ F Δ entry invariant arguments ts}
    (Hfresh : invariant ∉ GenericRegions.Atomicity.analysis_open entry)
    (Hregistered : invariant ∈ term_registered_invariants )
    (conditions : list (gexpr Γ TBool))
    (tracked : gexpr_list Γ ts)
    (store : symbolic_store Γ F Δ) :
  term_structured_runtime_arguments_valid
    (Structured.StructuredFreshFold Γ entry invariant arguments
      Hfresh) conditions tracked
    (Translation.Resource.RState store
      (ResourceInstances.instantiated_invariant invariant
        (IR.symbolize_expr_list store arguments)))
    (Translation.Resource.RState store
      (Translation.Resource.CInvariant invariant
        (IR.symbolize_expr_list store arguments))).
Proof.
  intros types held _ _ values runtime formals binders valuation ambient Henvelope _.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "(#Hglobal & Hheld & Hpre & %Harguments)".
  have Hvalid := @term_structured_runtime_fresh_fold_valid
    _ _ _ _ _ _ store Hfresh Hregistered
    runtime formals binders valuation ambient Henvelope.
  iPoseProof (Hvalid with "[$Hglobal $Hpre]") as "Hwp".
  iAssert (⌜interp_expr_list formals binders valuation
      (IR.symbolize_expr_list store (held_pinned tracked held)) =
        Some (held_pinned_values values held)⌝)%I
    with "[]" as "Harguments_saved".
  { iPureIntro. exact Harguments. }
  iCombine "Hwp Hheld Harguments_saved" as "Hwp".
  iPoseProof (translated_runtime_wp_frame with "Hwp") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[[Hglobal' Hpost] [Hheld' %Harguments']]". iFrame "Hglobal' Hheld' Hpost".
  iPureIntro. exact Harguments'.
Qed.


(** *** The procedure boundary

    Lifting the slice to a procedure-level statement.  The declared
    contract enters as [procedure_body_pre] and [procedure_body_post],
    both of which are now [resource_prenex]-valued, so
    the procedure boundary is stated in the same representation as the
    body derivation -- no [prenex_to_assertion] anywhere.

    The one piece of real content is the transport: structured runtime
    validity holds for the *normalized* statement, while the procedure
    boundary must speak about the procedure's actual body.  The
    normalization result's own erasure equation bridges that, through
    [term_translated_runtime_wp_runtime_stmt_ext]. *)
Theorem term_procedure_body_source_valid
    {Γ identity} (procedure : typed_procedure Γ identity)
    {entry exit exit_context}
    (exit_store : symbolic_store Γ (Assertion.procedure_args identity) exit_context)
    (return_reference : value_ref (Assertion.procedure_args identity) exit_context
      (procedure_return_type _ _ procedure))
    {body_pre body_post :
      Translation.Resource.resource_prenex Γ (Assertion.procedure_args identity)
        (@nil typ)}
    (** The declared contract, carried as equations rather than
        substituted into the derivations' types.  Both this and
        [Hsource] keep the dependent indices out of the way: the proof
        needs only rewriting in the goal. *)
    (Hpre : Hoare.procedure_body_pre procedure = body_pre)
    (Hpost : Hoare.procedure_body_post procedure exit_store return_reference =
      body_post)
    {source : stmt Γ}
    (source_derivation :
      CertifiedNormalization.RavenHoareRules.RavenHoareTriple
        body_pre source body_post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (normalization : @CertifiedNormalization.normalization_result _ _ _
      Γ (Assertion.procedure_args identity) [] entry exit
      body_pre body_post source source_derivation source_certificate)
    (Hsource : procedure_body _ _ procedure = source) :
  term_structured_runtime_valid
    (CertifiedNormalization.normalization_target_certificate
      normalization)
    body_pre body_post ->
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env (Assertion.procedure_args identity))
    (valuation : symbol_valuation) (ambient : coPset),
    RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint
        (CertifiedNormalization.normalization_target_certificate
          normalization) ∪ term_registered_invariants) ⊆ ambient ->
    (global_world_context valuation ∗
     term_interp_resource_prenex runtime formals empty_binder_env valuation
       (Hoare.procedure_body_pre procedure)) ⊢
    translated_runtime_wp runtime ambient entry exit
      (procedure_body _ _ procedure)
      (global_world_context valuation ∗
       term_interp_resource_prenex runtime formals empty_binder_env valuation
         (Hoare.procedure_body_post procedure exit_store return_reference)).
Proof.
  intros Hvalid runtime formals valuation ambient Henvelope.
  rewrite Hpre Hpost.
  rewrite (term_translated_runtime_wp_runtime_stmt_ext runtime ambient
    entry exit (procedure_body _ _ procedure)
    (CertifiedNormalization.normalized_statement normalization) _
    (eq_trans (f_equal _ Hsource)
      (CertifiedNormalization.normalization_runtime_erasure
        normalization _ _))).
  pose proof (Hvalid runtime formals empty_binder_env valuation ambient Henvelope)
    as Hwp.
  unfold term_structured_runtime_wp in Hwp.
  exact Hwp.
Qed.

(** The same lift in the interface an analysis-driven caller actually
    has.  The external analysis provides an envelope for the *source*
    certificate's footprint; the strengthened record carries the bridge
    to the target certificate's, so the caller never has to know the
    normalized shape. *)
Theorem term_procedure_body_source_valid_footprinted
    {Γ identity} (procedure : typed_procedure Γ identity)
    {entry exit exit_context}
    (exit_store : symbolic_store Γ (Assertion.procedure_args identity) exit_context)
    (return_reference :
      value_ref (Assertion.procedure_args identity) exit_context
        (procedure_return_type _ _ procedure))
    {body_pre body_post :
      Translation.Resource.resource_prenex Γ (Assertion.procedure_args identity)
        (@nil typ)}
    (Hpre : Hoare.procedure_body_pre procedure = body_pre)
    (Hpost : Hoare.procedure_body_post procedure exit_store return_reference =
      body_post)
    {source : stmt Γ}
    (source_derivation :
      CertifiedNormalization.RavenHoareRules.RavenHoareTriple
        body_pre source body_post)
    (source_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry source exit)
    (normalization :
      @CertifiedNormalization.footprinted_normalization_result _ _ _
        Γ (Assertion.procedure_args identity) [] entry exit
        body_pre body_post source source_derivation source_certificate)
    (Hsource : procedure_body _ _ procedure = source) :
  term_structured_runtime_valid
    (CertifiedNormalization.normalization_target_certificate
      (CertifiedNormalization.footprinted_normalization
        normalization))
    body_pre body_post ->
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env (Assertion.procedure_args identity))
    (valuation : symbol_valuation) (ambient : coPset),
    RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint source_certificate ∪
        term_registered_invariants) ⊆ ambient ->
    (global_world_context valuation ∗
     term_interp_resource_prenex runtime formals empty_binder_env valuation
       (Hoare.procedure_body_pre procedure)) ⊢
    translated_runtime_wp runtime ambient entry exit
      (procedure_body _ _ procedure)
      (global_world_context valuation ∗
       term_interp_resource_prenex runtime formals empty_binder_env valuation
         (Hoare.procedure_body_post procedure exit_store return_reference)).
Proof.
  intros Hvalid runtime formals valuation ambient Henvelope.
  apply (term_procedure_body_source_valid procedure
    exit_store return_reference Hpre Hpost source_derivation
    source_certificate
    (CertifiedNormalization.footprinted_normalization normalization)
    Hsource Hvalid).
  etrans; [| exact Henvelope].
  apply RegionExecution.Primitives.Model.runtime_mask_mono.
  intros invariant Hin.
  apply elem_of_union in Hin as [Hin | Hin].
  - apply elem_of_union_l.
    eapply CertifiedNormalization.footprinted_normalization_subset.
    exact Hin.
  - apply elem_of_union_r. exact Hin.
Qed.



(** Trusted atomicity is carried separately from the analyzer certificate.
    The dynamic Core receives the module-specific witness through []. *)
Fixpoint term_structured_certificate_trusted_runtime_atomicity
    {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit) :
    RegionExecution.Primitives.Model.stack_context Γ -> Prop :=
  match certificate in Structured.structured_certificate
      Γ' _ statement' _ return
        RegionExecution.Primitives.Model.stack_context Γ' -> Prop with
  | Structured.StructuredSequence _ _ _ _ _ _ first second =>
      fun runtime =>
        term_structured_certificate_trusted_runtime_atomicity first runtime /\
        term_structured_certificate_trusted_runtime_atomicity second runtime
  | Structured.StructuredConditional _ _ _ _ _ _ _ then_branch
      else_branch _ _ =>
      fun runtime =>
        term_structured_certificate_trusted_runtime_atomicity then_branch runtime /\
        term_structured_certificate_trusted_runtime_atomicity else_branch runtime
  | Structured.StructuredAtomic _ _ _ _ _ _ _ _ =>
      fun _ => True
  | Structured.StructuredInvAccess _ _ _ _ _ _ _ _ _ body_certificate _ =>
      fun runtime =>
        term_structured_certificate_trusted_runtime_atomicity body_certificate runtime
  | Structured.StructuredGhostVal _ _ name t _ _ _ body_certificate _ =>
      fun runtime =>
        term_structured_certificate_trusted_runtime_atomicity body_certificate
          (RegionExecution.Primitives.Model.ghost_stack_context name t runtime)
  | Structured.StructuredGhostConditional _ _ _ _ _ _ _ then_branch
      else_branch _ _ =>
      fun runtime =>
        term_structured_certificate_trusted_runtime_atomicity then_branch runtime /\
        term_structured_certificate_trusted_runtime_atomicity else_branch runtime
  | _ => fun _ => True
  end.

Lemma term_structured_certificate_preserves_wf
    {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit) :
  GenericRegions.Atomicity.state_wf entry ->
  GenericRegions.Atomicity.state_wf exit.
Proof.
  induction certificate; intros Hwf.
  - eapply GenericRegions.Atomicity.take_leaf_preserves_wf; eauto.
  - exact Hwf.
  - apply GenericRegions.Atomicity.fold_invariant_preserves_wf. exact Hwf.
  - apply IHcertificate2. apply IHcertificate1. exact Hwf.
  - exact (IHcertificate1 Hwf).
  - have Houter_wf : GenericRegions.Atomicity.state_wf outer.
    { eapply GenericRegions.Atomicity.take_step_preserves_wf; eauto. }
    exact (IHcertificate Houter_wf).
  - have Hopened_wf : GenericRegions.Atomicity.state_wf opened.
    { eapply GenericRegions.Atomicity.open_access_preserves_wf; eauto. }
    apply GenericRegions.Atomicity.fold_invariant_preserves_wf.
    exact (IHcertificate Hopened_wf).
  - exact (IHcertificate Hwf).
  - exact (IHcertificate1 Hwf).
Qed.

Lemma term_structured_certificate_preserves_nonatomic
    {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit) :
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  GenericRegions.Atomicity.analysis_in_atomic exit = false.
Proof.
  intro Hin_atomic. induction certificate; simpl in *.
  - rewrite (GenericRegions.Atomicity.take_leaf_preserves_in_atomic
      _ _ _ _ e0). exact Hin_atomic.
  - exact Hin_atomic.
  - rewrite GenericRegions.Atomicity.fold_invariant_preserves_in_atomic.
    exact Hin_atomic.
  - apply IHcertificate2. apply IHcertificate1. exact Hin_atomic.
  - apply IHcertificate1. exact Hin_atomic.
  - rewrite (GenericRegions.Atomicity.take_step_preserves_in_atomic
      _ _ _ e). exact Hin_atomic.
  - rewrite GenericRegions.Atomicity.fold_invariant_preserves_in_atomic.
    apply IHcertificate.
    rewrite (GenericRegions.Atomicity.open_access_preserves_in_atomic
      _ _ _ _ _ e). exact Hin_atomic.
  - exact (IHcertificate Hin_atomic).
  - apply IHcertificate1. exact Hin_atomic.
Qed.

Lemma term_runtime_conditional_statement_atomic {Γ}
    (names : named_context Γ) stack condition
    (then_branch else_branch : stmt Γ) :
  @Atomic RuntimeLang.simp_lang WeaklyAtomic
    (@RuntimeErasure.runtime_stmt _ _ Γ names stack then_branch) ->
  @Atomic RuntimeLang.simp_lang WeaklyAtomic
    (@RuntimeErasure.runtime_stmt _ _ Γ names stack else_branch) ->
  @Atomic RuntimeLang.simp_lang WeaklyAtomic
    (@RuntimeErasure.runtime_stmt _ _ Γ names stack
      (TIf condition then_branch else_branch)).
Proof.
  intros Hthen Helse. cbn [RuntimeErasure.runtime_stmt].
  apply (RuntimeErasure.runtime_if_ind
    (fun combined => @Atomic RuntimeLang.simp_lang WeaklyAtomic combined)).
  - intros _ _. apply runtime_noop_atomic.
  - intros _. apply RuntimeLang.atomic_if; assumption.
Qed.

Lemma term_open_leaf_runtime_atomic {Γ entry statement exit}
    (view : RegionSyntax.view statement = AnalysisView.ViewLeaf)
    (step : GenericRegions.Atomicity.take_step (RegionSyntax.cost Γ statement) entry =
      inr exit)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) :
  RegionExecution.Primitives.Model.runtime_cost_model_sound ->
  GenericRegions.Atomicity.analysis_open entry ≠ ∅ ->
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  @Atomic RuntimeLang.simp_lang WeaklyAtomic
    (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      statement).
Proof.
  intros Hcost Hopen Hin_atomic.
  specialize (Hcost Γ
    (RegionExecution.Primitives.Model.runtime_names Γ runtime)
    (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
    statement view).
  destruct (RegionSyntax.cost Γ statement) eqn:Hstep_cost; simpl in Hcost.
  - refine (eq_ind_r (fun physical =>
      @Atomic RuntimeLang.simp_lang WeaklyAtomic physical)
      runtime_noop_atomic Hcost).
  - exact Hcost.
  - unfold GenericRegions.Atomicity.take_step in step.
    rewrite (GenericRegions.Atomicity.take_plain_non_atomic_rejected entry
      Hopen Hin_atomic) in step. discriminate.
  - exfalso.
    eapply (GenericRegions.Atomicity.procedure_call_rejected_while_open
      _ _ entry exit Hopen Hin_atomic). exact step.
  - exfalso.
    eapply (GenericRegions.Atomicity.procedure_spawn_rejected_while_open
      _ entry exit Hopen Hin_atomic). exact step.
Qed.

Lemma term_open_physical_leaf_takes_unique_step
    {Γ entry statement exit}
    (view : RegionSyntax.view statement = AnalysisView.ViewLeaf)
    (step : GenericRegions.Atomicity.take_step (RegionSyntax.cost Γ statement) entry =
      inr exit)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) :
  RegionExecution.Primitives.Model.runtime_cost_model_sound ->
  GenericRegions.Atomicity.analysis_open entry ≠ ∅ ->
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  RuntimeErasure.runtime_is_noop
    (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      statement) = false ->
  GenericRegions.Atomicity.analysis_step_taken entry = false /\
  GenericRegions.Atomicity.analysis_step_taken exit = true.
Proof.
  intros Hcost Hopen Hin_atomic Hphysical.
  specialize (Hcost Γ
    (RegionExecution.Primitives.Model.runtime_names Γ runtime)
    (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
    statement view).
  destruct (RegionSyntax.cost Γ statement) eqn:Hstep_cost; simpl in Hcost.
  - pose proof (f_equal RuntimeErasure.runtime_is_noop Hcost)
      as Hnoop.
    pose proof (eq_trans (eq_sym Hnoop) Hphysical). discriminate.
  - unfold GenericRegions.Atomicity.take_step,
      GenericRegions.Atomicity.take_plain_step in step.
    rewrite Hin_atomic in step. simpl in step.
    rewrite bool_decide_false in step; last exact Hopen.
    destruct (GenericRegions.Atomicity.analysis_step_taken entry) eqn:Htaken;
      first discriminate.
    inversion step; subst exit. simpl. auto.
  - unfold GenericRegions.Atomicity.take_step,
      GenericRegions.Atomicity.take_plain_step in step.
    rewrite Hin_atomic in step. simpl in step.
    rewrite bool_decide_false in step; [discriminate|exact Hopen].
  - exfalso.
    eapply (GenericRegions.Atomicity.procedure_call_rejected_while_open
      _ _ entry exit Hopen Hin_atomic). exact step.
  - exfalso.
    eapply (GenericRegions.Atomicity.procedure_spawn_rejected_while_open
      _ entry exit Hopen Hin_atomic). exact step.
Qed.

(** The number of physical steps an erased statement contributes to a
    region: none for the terminal statement, one otherwise. *)
Definition term_runtime_step_count
    (physical : RuntimeLang.runtime_stmt) : nat :=
  if RuntimeErasure.runtime_is_noop physical then 0 else 1.

Definition term_analysis_step_bit
    (state : GenericRegions.Atomicity.analysis_state) : nat :=
  if GenericRegions.Atomicity.analysis_step_taken state then 1 else 0.

Lemma term_runtime_step_count_noop :
  term_runtime_step_count RuntimeErasure.runtime_noop = 0.
Proof. reflexivity. Qed.

Lemma term_runtime_step_count_seq first second :
  term_runtime_step_count
    (RuntimeErasure.runtime_seq first second) <=
  term_runtime_step_count first + term_runtime_step_count second.
Proof.
  apply (RuntimeErasure.runtime_seq_ind
    (fun combined => term_runtime_step_count combined <=
      term_runtime_step_count first + term_runtime_step_count second)).
  - intros ->. rewrite term_runtime_step_count_noop. lia.
  - intros ->. rewrite term_runtime_step_count_noop. lia.
  - (* restate the Model-side hypotheses in local terms; see
       [term_runtime_step_count_if] *)
    intros Hfirst Hsecond.
    assert (Hfirst' : RuntimeErasure.runtime_is_noop first =
      false) by exact Hfirst.
    assert (Hsecond' : RuntimeErasure.runtime_is_noop second =
      false) by exact Hsecond.
    unfold term_runtime_step_count. rewrite Hfirst' Hsecond'. simpl. lia.
Qed.

Lemma term_runtime_step_count_if condition then_branch else_branch stack :
  term_runtime_step_count
    (RuntimeErasure.runtime_if condition
      then_branch else_branch stack) <=
  Nat.max (term_runtime_step_count then_branch)
    (term_runtime_step_count else_branch).
Proof.
  apply (RuntimeErasure.runtime_if_ind
    (fun combined => term_runtime_step_count combined <=
      Nat.max (term_runtime_step_count then_branch)
        (term_runtime_step_count else_branch))).
  - intros _ _. rewrite term_runtime_step_count_noop. lia.
  - intros Hphysical.
    assert (Hphysical' :
      RuntimeErasure.runtime_is_noop then_branch &&
      RuntimeErasure.runtime_is_noop else_branch = false)
      by exact Hphysical.
    clear Hphysical. rename Hphysical' into Hphysical.
    unfold term_runtime_step_count. simpl.
    destruct (RuntimeErasure.runtime_is_noop then_branch),
      (RuntimeErasure.runtime_is_noop else_branch);
      simpl in *; first discriminate; lia.
Qed.

Lemma term_open_invariant_preserves_step_bit invariant key excluded entry
    exit :
  GenericRegions.Atomicity.open_access invariant key excluded entry =
    inr exit ->
  term_analysis_step_bit exit = term_analysis_step_bit entry.
Proof.
  intros Hopen.
  destruct (GenericRegions.Atomicity.open_access_records _ _ _ _ _ Hopen)
    as (consumed & ->).
  reflexivity.
Qed.

Lemma term_fold_invariant_preserves_step_bit_if_open invariant key entry :
  GenericRegions.Atomicity.analysis_open
      (GenericRegions.Atomicity.fold_invariant invariant key entry) ≠ ∅ ->
  term_analysis_step_bit
      (GenericRegions.Atomicity.fold_invariant invariant key entry) =
    term_analysis_step_bit entry.
Proof.
  unfold GenericRegions.Atomicity.fold_invariant.
  destruct (GenericRegions.Atomicity.analysis_records entry)
    as [|record rest]; [reflexivity|].
  destruct (decide (GenericRegions.Atomicity.record_invariant record =
    invariant)); [|reflexivity].
  destruct rest; [|reflexivity].
  intros Hopen. exfalso. apply Hopen. reflexivity.
Qed.

Lemma term_structured_certificate_runtime_step_budget
    {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) :
  RegionExecution.Primitives.Model.runtime_cost_model_sound ->
  GenericRegions.Atomicity.analysis_open entry ≠ ∅ ->
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  term_analysis_step_bit entry +
      term_runtime_step_count
        (@RuntimeErasure.runtime_stmt _ _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
          statement) <=
    term_analysis_step_bit exit.
Proof.
  intros Hcost Hopen Hin_atomic.
  induction certificate as
      [Γ state statement exit view step
      | Γ state statement view
      | Γ state invariant arguments Hfresh
      | Γ state first middle second exit first_certificate IHfirst
        second_certificate IHsecond
      | Γ state condition then_branch else_branch then_exit else_exit
        then_certificate IHthen else_certificate IHelse records_equal atomic_equal
      | Γ state body outer inner step body_certificate IHbody records_equal
      | Γ state invariant arguments excluded body opened inner step
        body_certificate IHbody records_equal
      | Γ state name t initializer body exit body_certificate IHbody
        admissible
      | Γ state condition then_branch else_branch then_exit else_exit
        then_certificate IHthen else_certificate IHelse records_equal atomic_equal];
    simpl in *.
  - destruct (GenericRegions.Atomicity.take_leaf_step_taken _ _ _ _ step)
      as (stepped & Hstepped & Hbit).
    replace (term_analysis_step_bit exit) with (term_analysis_step_bit stepped)
      by (unfold term_analysis_step_bit; rewrite Hbit; reflexivity).
    clear step Hbit. clear exit. rename stepped into exit.
    rename Hstepped into step.
    destruct (RuntimeErasure.runtime_is_noop
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
        statement)) eqn:Hruntime.
    2: { destruct (term_open_physical_leaf_takes_unique_step view step runtime
        Hcost Hopen Hin_atomic Hruntime) as [Hentry Hexit].
      unfold term_runtime_step_count, term_analysis_step_bit.
      rewrite Hruntime Hentry Hexit. lia. }
    + unfold term_runtime_step_count, term_analysis_step_bit.
      rewrite Hruntime.
      destruct (RegionSyntax.cost Γ statement) eqn:Hstep_cost.
      * unfold GenericRegions.Atomicity.take_step,
          GenericRegions.Atomicity.take_plain_step in step.
        rewrite Hin_atomic in step. simpl in step.
        rewrite bool_decide_false in step; last exact Hopen.
        inversion step; subst exit.
        destruct (GenericRegions.Atomicity.analysis_step_taken state); simpl; lia.
      * unfold GenericRegions.Atomicity.take_step,
          GenericRegions.Atomicity.take_plain_step in step.
        rewrite Hin_atomic in step. simpl in step.
        rewrite bool_decide_false in step; last exact Hopen.
        destruct (GenericRegions.Atomicity.analysis_step_taken state) eqn:Hentry;
          first discriminate.
        inversion step; subst exit. simpl. lia.
      * unfold GenericRegions.Atomicity.take_step in step.
        rewrite (GenericRegions.Atomicity.take_plain_non_atomic_rejected state
          Hopen Hin_atomic) in step. discriminate.
      * exfalso. eapply (GenericRegions.Atomicity.procedure_call_rejected_while_open
          _ _ state exit Hopen Hin_atomic). exact step.
      * exfalso. eapply (GenericRegions.Atomicity.procedure_spawn_rejected_while_open
          _ state exit Hopen Hin_atomic). exact step.
  - (* done erases to the terminal statement, which takes no step, and
       leaves the state unchanged *)
    destruct statement; cbn in view; try discriminate.
    all: try (exfalso; guarded_view_cases; fail).
    cbn. lia.
  - have Hfold_open : GenericRegions.Atomicity.analysis_open
        (GenericRegions.Atomicity.fold_invariant invariant
          (RegionSyntax.argument_key arguments) state) ≠ ∅.
    { rewrite (proj2 (GenericRegions.Atomicity.fold_fresh_invariant
        _ _ _ Hfresh)). exact Hopen. }
    rewrite (term_fold_invariant_preserves_step_bit_if_open _ _ _ Hfold_open).
    unfold RuntimeErasure.runtime_stmt. simpl.
    unfold term_runtime_step_count. simpl. lia.
  - have Hmiddle_open : GenericRegions.Atomicity.analysis_open middle ≠ ∅.
    { rewrite (term_structured_certificate_preserves_open first_certificate).
      exact Hopen. }
    have Hmiddle_atomic :
        GenericRegions.Atomicity.analysis_in_atomic middle = false.
    { eapply term_structured_certificate_preserves_nonatomic; eauto. }
    specialize (IHfirst runtime Hopen Hin_atomic).
    specialize (IHsecond runtime Hmiddle_open Hmiddle_atomic).
    unfold RuntimeErasure.runtime_stmt; simpl.
    pose proof (term_runtime_step_count_seq
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) first)
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) second)) as Hcombine.
    etrans.
    + apply Nat.add_le_mono_l. exact Hcombine.
    + lia.
  - specialize (IHthen runtime Hopen Hin_atomic).
    specialize (IHelse runtime Hopen Hin_atomic).
    match goal with
    | |- context [term_runtime_step_count ?erased] =>
        change erased with (RuntimeErasure.runtime_if
          (@RuntimeErasure.runtime_expr _ Γ _ _
            (RegionExecution.Primitives.Model.runtime_names Γ runtime) condition)
          (@RuntimeErasure.runtime_stmt _ _ Γ
            (RegionExecution.Primitives.Model.runtime_names Γ runtime)
            (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
            then_branch)
          (@RuntimeErasure.runtime_stmt _ _ Γ
            (RegionExecution.Primitives.Model.runtime_names Γ runtime)
            (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
            else_branch)
          (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime))
    end.
    remember (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) then_branch)
      as then_runtime eqn:Hthen.
    remember (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) else_branch)
      as else_runtime eqn:Helse.
    pose proof (term_runtime_step_count_if
      (@RuntimeErasure.runtime_expr _ Γ _ _
        (RegionExecution.Primitives.Model.runtime_names Γ runtime) condition)
      then_runtime else_runtime
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)) as Hif.
    unfold term_runtime_step_count, term_analysis_step_bit in *.
    destruct (RuntimeErasure.runtime_is_noop then_runtime),
      (RuntimeErasure.runtime_is_noop else_runtime),
      (RuntimeErasure.runtime_is_noop
        (RuntimeErasure.runtime_if
          (@RuntimeErasure.runtime_expr _ Γ _ _
            (RegionExecution.Primitives.Model.runtime_names Γ runtime) condition)
          then_runtime else_runtime
          (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)));
      destruct (GenericRegions.Atomicity.analysis_step_taken state),
        (GenericRegions.Atomicity.analysis_step_taken then_exit),
        (GenericRegions.Atomicity.analysis_step_taken else_exit);
      simpl in *; lia.
  - remember (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) body)
      as body_runtime.
    unfold RuntimeErasure.runtime_stmt. simpl.
    unfold GenericRegions.Atomicity.take_step,
      GenericRegions.Atomicity.take_plain_step in step.
    rewrite Hin_atomic in step. simpl in step.
    rewrite bool_decide_false in step; last exact Hopen.
    destruct (GenericRegions.Atomicity.analysis_step_taken state) eqn:Htaken;
      first discriminate.
    inversion step; subst outer. simpl.
    unfold term_analysis_step_bit, term_runtime_step_count.
    rewrite Htaken; simpl; lia.
  - have Hopen_transition := step.
    apply GenericRegions.Atomicity.open_access_success in step as
      (Hopened_mask & Hopened_open).
    have Hopened_nonempty :
        GenericRegions.Atomicity.analysis_open opened ≠ ∅.
    { rewrite Hopened_open. intro Hempty. apply Hopen. set_solver. }
    have Hopened_atomic :
        GenericRegions.Atomicity.analysis_in_atomic opened = false.
    { rewrite (GenericRegions.Atomicity.open_access_preserves_in_atomic
        _ _ _ _ _ Hopen_transition). exact Hin_atomic. }
    specialize (IHbody runtime Hopened_nonempty Hopened_atomic).
    have Hexit_open : GenericRegions.Atomicity.analysis_open
        (GenericRegions.Atomicity.fold_invariant invariant
          (RegionSyntax.argument_key arguments) inner) ≠ ∅.
    { rewrite (GenericRegions.Atomicity.analysis_open_records _ _
        (fold_after_open_access_records _ _ _ _ _ _ _
          Hopen_transition records_equal)).
      exact Hopen. }
    have Hopen_bit := term_open_invariant_preserves_step_bit
      invariant _ _ state opened Hopen_transition.
    have Hfold_bit := term_fold_invariant_preserves_step_bit_if_open
      invariant _ inner Hexit_open.
    unfold RuntimeErasure.runtime_stmt. simpl.
    rewrite Hopen_bit in IHbody. rewrite Hfold_bit.
    exact IHbody.
  - exact (IHbody (RegionExecution.Primitives.Model.ghost_stack_context
      name t runtime) Hopen Hin_atomic).
  - (* a ghost conditional takes no step, and its exit keeps the then
       branch's step bit *)
    specialize (IHthen runtime Hopen Hin_atomic). revert IHthen.
    unfold term_analysis_step_bit, term_runtime_step_count.
    cbn [GenericRegions.Atomicity.analysis_step_taken].
    destruct (GenericRegions.Atomicity.analysis_step_taken state),
      (GenericRegions.Atomicity.analysis_step_taken then_exit),
      (GenericRegions.Atomicity.analysis_step_taken else_exit);
      cbn; repeat case_match; lia.
Qed.

Lemma term_open_structured_certificate_runtime_atomic
    {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) :
  RegionExecution.Primitives.Model.runtime_cost_model_sound ->
  GenericRegions.Atomicity.analysis_open entry ≠ ∅ ->
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  term_structured_certificate_trusted_runtime_atomicity certificate runtime ->
  @Atomic RuntimeLang.simp_lang WeaklyAtomic
    (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      statement).
Proof.
  intros Hcost Hopen Hin_atomic Htrusted.
  induction certificate as
      [Γ state statement exit view step
      | Γ state statement view
      | Γ state invariant arguments Hfresh
      | Γ state first middle second exit first_certificate IHfirst
        second_certificate IHsecond
      | Γ state condition then_branch else_branch then_exit else_exit
        then_certificate IHthen else_certificate IHelse records_equal atomic_equal
      | Γ state body outer inner step body_certificate IHbody records_equal
      | Γ state invariant arguments excluded body opened inner step
        body_certificate IHbody records_equal
      | Γ state name t initializer body exit body_certificate IHbody
        admissible
      | Γ state condition then_branch else_branch then_exit else_exit
        then_certificate IHthen else_certificate IHelse records_equal atomic_equal];
    simpl in Htrusted |- *.
  - destruct (GenericRegions.Atomicity.take_leaf_step_taken _ _ _ _ step)
      as (stepped & Hstepped & _).
    eapply term_open_leaf_runtime_atomic; eauto.
  - (* done erases to the terminal statement, which takes no step *)
    destruct statement; cbn in view; try discriminate.
    all: try (exfalso; guarded_view_cases; fail).
    exact runtime_noop_atomic.
  - exact runtime_noop_atomic.
  - destruct Htrusted as [Hfirst_trusted Hsecond_trusted].
    have Hmiddle_open : GenericRegions.Atomicity.analysis_open middle ≠ ∅.
    { rewrite (term_structured_certificate_preserves_open first_certificate).
      exact Hopen. }
    have Hmiddle_atomic :
        GenericRegions.Atomicity.analysis_in_atomic middle = false.
    { eapply term_structured_certificate_preserves_nonatomic; eauto. }
    specialize (IHfirst runtime Hopen Hin_atomic Hfirst_trusted).
    specialize (IHsecond runtime Hmiddle_open Hmiddle_atomic Hsecond_trusted).
    apply (RuntimeErasure.runtime_seq_ind
      (fun combined => @Atomic RuntimeLang.simp_lang WeaklyAtomic combined)).
    + intros _. exact IHsecond.
    + intros _. exact IHfirst.
    + (* two physical steps would exceed the region's single-step budget *)
      intros Hfirst_physical Hsecond_physical. exfalso.
      assert (Hfirst_count : term_runtime_step_count
        (@RuntimeErasure.runtime_stmt _ _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
          first) = 1).
      { unfold term_runtime_step_count.
        assert (Hnoop : RuntimeErasure.runtime_is_noop
          (@RuntimeErasure.runtime_stmt _ _ Γ
            (RegionExecution.Primitives.Model.runtime_names Γ runtime)
            (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
            first) = false) by exact Hfirst_physical.
        rewrite Hnoop. reflexivity. }
      assert (Hsecond_count : term_runtime_step_count
        (@RuntimeErasure.runtime_stmt _ _ Γ
          (RegionExecution.Primitives.Model.runtime_names Γ runtime)
          (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
          second) = 1).
      { unfold term_runtime_step_count.
        assert (Hnoop : RuntimeErasure.runtime_is_noop
          (@RuntimeErasure.runtime_stmt _ _ Γ
            (RegionExecution.Primitives.Model.runtime_names Γ runtime)
            (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
            second) = false) by exact Hsecond_physical.
        rewrite Hnoop. reflexivity. }
      have Hfirst_budget := term_structured_certificate_runtime_step_budget
        first_certificate runtime Hcost Hopen Hin_atomic.
      have Hsecond_budget := term_structured_certificate_runtime_step_budget
        second_certificate runtime Hcost Hmiddle_open Hmiddle_atomic.
      rewrite Hfirst_count in Hfirst_budget.
      rewrite Hsecond_count in Hsecond_budget.
      unfold term_analysis_step_bit in *.
      destruct (GenericRegions.Atomicity.analysis_step_taken state),
        (GenericRegions.Atomicity.analysis_step_taken middle),
        (GenericRegions.Atomicity.analysis_step_taken exit); simpl in *; lia.
  - destruct Htrusted as [Hthen_trusted Helse_trusted].
    apply (term_runtime_conditional_statement_atomic
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      condition then_branch else_branch).
    + eapply IHthen; eauto.
    + eapply IHelse; eauto.
  - apply RuntimeLang.atomic_trusted_atomic.
  - have Hopen_transition := step.
    apply GenericRegions.Atomicity.open_access_success in step as
      (_ & Hopened_open).
    have Hopened_nonempty :
        GenericRegions.Atomicity.analysis_open opened ≠ ∅.
    { rewrite Hopened_open. intros Hempty.
      have Hmember : invariant ∈
          {[invariant]} ∪ GenericRegions.Atomicity.analysis_open state.
      { apply elem_of_union_l. apply elem_of_singleton_2. reflexivity. }
      rewrite Hempty elem_of_empty in Hmember. contradiction. }
    have Hopened_atomic :
        GenericRegions.Atomicity.analysis_in_atomic opened = false.
    { rewrite (GenericRegions.Atomicity.open_access_preserves_in_atomic
        _ _ _ _ _ Hopen_transition). exact Hin_atomic. }
    eapply IHbody; eauto.
  - exact (IHbody (RegionExecution.Primitives.Model.ghost_stack_context
      name t runtime) Hopen Hin_atomic Htrusted).
  - exact runtime_noop_atomic.
Qed.


(** Invariant access is only admitted outside a trusted atomic block.  The
    opposite nesting remains available: an access body may itself be a
    trusted atomic block. *)
Definition term_structured_accesses_outside_atomic
    {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit) : Prop :=
  NormalizationBase.structured_accesses_outside_atomic certificate.

(** Pure coverage condition connecting a certificate to the finite invariant
    registry that adequacy allocates. *)
Definition term_structured_invariants_registered
    {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit) : Prop :=
  Structured.structured_certificate_footprint certificate ⊆
    term_registered_invariants .

(** An access at the top of a certificate opens a closed declaration, or its
    own distinctness condition is among the known [conditions]. *)
Definition term_access_conditions_ok {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (conditions : list (gexpr Γ TBool)) : Prop :=
  (match certificate in Structured.structured_certificate Γ0 _ _ _
    return list (gexpr Γ0 TBool) -> Prop with
  | Structured.StructuredInvAccess _ access_entry invariant arguments excluded
      _ _ _ _ _ _ => fun conditions0 =>
      invariant ∉ GenericRegions.Atomicity.analysis_open access_entry \/
      List.In (IR.arguments_distinct arguments excluded) conditions0
  | _ => fun _ => True
  end) conditions.

(** [term_structured_accesses_outside_atomic], except that an access at the
    top of the certificate may open an open declaration. *)
Definition term_access_safe {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit) : Prop :=
  match certificate with
  | Structured.StructuredInvAccess _ access_entry _ _ _ _ _ _ _ body _ =>
      GenericRegions.Atomicity.analysis_in_atomic access_entry = false /\
      NormalizationBase.structured_accesses_outside_atomic body
  | other => NormalizationBase.structured_accesses_outside_atomic other
  end.

Lemma term_access_safe_strict {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit) :
  NormalizationBase.structured_accesses_outside_atomic certificate ->
  term_access_safe certificate.
Proof.
  destruct certificate; try (intros H; exact H).
  intros (Hatomic & _ & Hbody). split; assumption.
Qed.

Lemma term_access_conditions_ok_strict {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit) :
  NormalizationBase.structured_accesses_outside_atomic certificate ->
  term_access_conditions_ok certificate [].
Proof.
  destruct certificate; try (intros _; exact I).
  intros (_ & Hclosed & _). left. exact Hclosed.
Qed.

(** The second statement of a safe sequence is safe; if it opens an open
    declaration, the first statement asserts its condition. *)
Lemma term_access_safe_sequence {Γ entry first middle second exit}
    (first_certificate : Structured.structured_certificate
      Γ entry first middle)
    (second_certificate : Structured.structured_certificate
      Γ middle second exit) :
  NormalizationBase.structured_accesses_outside_atomic
    (Structured.StructuredSequence Γ entry first middle second exit
      first_certificate second_certificate) ->
  NormalizationBase.structured_accesses_outside_atomic first_certificate /\
  ((term_access_safe second_certificate /\
    term_access_conditions_ok second_certificate []) \/
   (exists condition, first = TAssert condition /\
    Hoare.ResourceHoare.pexpr_dependencies condition ##
      Hoare.ResourceHoare.statement_writes second /\
    term_access_safe second_certificate /\
    term_access_conditions_ok second_certificate [condition])).
Proof.
  intros [Hfirst Hsecond]. split; [exact Hfirst|].
  destruct second_certificate; try (left; split; [exact Hsecond | exact I]).
  destruct Hsecond as (Hatomic & [Hclosed | [Hassert Hstable]] & Hbody).
  - left. split; [split; assumption|]. left. exact Hclosed.
  - right. exists (IR.arguments_distinct arguments excluded).
    split; [exact Hassert|]. split; [exact Hstable|].
    split; [split; assumption|]. right. left. reflexivity.
Qed.

Lemma conditions_hold_cons {Γ ts t} (conditions : list (gexpr Γ TBool))
    (expression : gexpr Γ t) (pinned : gexpr_list Γ ts)
    (value : tval t) (values : tval_list ts) :
  conditions_hold conditions pinned values ->
  conditions_hold conditions (PECons expression pinned) (TVCons value values).
Proof.
  intros Hconditions F Δ store formals binders valuation Heval.
  cbn [IR.symbolize_expr_list] in Heval.
  apply interp_expr_list_cons_inv in Heval as (head & rest & Heq & _ & Hrest).
  have Htail := f_equal tval_list_tail Heq. cbn in Htail. subst rest.
  exact (Hconditions F Δ store formals binders valuation Hrest).
Qed.

(** *** The generic driver over resource telescopes

    The generic driver theorem, with the derivation in [RavenHoareRules]
    and the pre- and postconditions resource telescopes.  This is the
    semantic consumer of a normalized derivation: everything the
    procedure boundary needs beyond the producer.

    The induction is on the derivation, with the structured certificate
    destructed alongside whenever the rule fixes the statement's shape.
    Fold and unfold of an invariant or a predicate have no structured
    counterpart except the fresh fold, so those cases are closed by the
    contradictory [ViewLeaf] premise of [StructuredLeaf]. *)
Theorem term_structured_certificate_resource_prenex_arguments_valid
    {Γ F Δ entry statement exit}
    {pre post : Translation.Resource.resource_prenex Γ F Δ}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (derivation : CertifiedNormalization.RavenHoareRules.RavenHoareTriple
      pre statement post) :
  GenericRegions.Atomicity.state_wf entry ->
  RegionExecution.Primitives.Model.runtime_cost_model_sound ->
  Certified.procedure_cost_model_sound ->
  term_structured_invariants_registered certificate ->
  term_access_safe certificate ->
  (forall conditions ts (tracked : gexpr_list Γ ts),
    term_access_conditions_ok certificate conditions ->
    term_structured_runtime_arguments_valid certificate
      conditions tracked pre post) /\
  (forall runtime,
    term_structured_certificate_trusted_runtime_atomicity certificate runtime).
Proof.
  revert entry exit certificate.
  induction derivation; intros entry exit certificate Hwf Hcost
    Hprocedure_cost Hregistered Hsafe.
  all: tryif is_var statement then idtac else dependent destruction certificate.
  all: try discriminate.
  all: try (exfalso; guarded_view_cases; fail).
  - destruct (IHderivation entry exit certificate Hwf Hcost
      Hprocedure_cost Hregistered Hsafe) as [Hvalid Htrusted].
    split.
    + intros conditions ts tracked Hok.
      apply term_structured_runtime_arguments_prenex_preserve_valid.
      exact (Hvalid _ _ _ Hok).
    + exact Htrusted.
  - destruct (IHderivation entry exit certificate Hwf Hcost
      Hprocedure_cost Hregistered Hsafe) as [Hvalid Htrusted].
    split.
    + intros conditions ts tracked Hok.
      apply term_structured_runtime_arguments_bound_weaken_valid.
      exact (Hvalid _ _ _ Hok).
    + exact Htrusted.
  - destruct (IHderivation entry exit certificate Hwf Hcost
      Hprocedure_cost Hregistered Hsafe) as [Hvalid Htrusted].
    split.
    + intros conditions ts tracked Hok.
      apply term_structured_runtime_arguments_prenex_elim_valid.
      exact (Hvalid _ _ _ Hok).
    + exact Htrusted.
  - destruct (IHderivation entry exit certificate Hwf Hcost
      Hprocedure_cost Hregistered Hsafe) as [Hvalid Htrusted].
    split.
    + intros conditions ts tracked Hok.
      eapply term_structured_runtime_arguments_prenex_consequence_valid;
        [exact (Hvalid _ _ _ Hok) | exact H | exact H0].
    + exact Htrusted.
  - destruct (IHderivation entry exit certificate Hwf Hcost
      Hprocedure_cost Hregistered Hsafe) as [Hvalid Htrusted].
    split.
    + intros conditions ts tracked Hok.
      apply term_structured_runtime_arguments_frame_valid.
      exact (Hvalid _ _ _ Hok).
    + exact Htrusted.
  - destruct (IHderivation entry exit certificate Hwf Hcost
      Hprocedure_cost Hregistered Hsafe) as [Hvalid Htrusted].
    split.
    + intros conditions ts tracked Hok.
      eapply term_structured_runtime_arguments_prenex_consequence_valid.
      * eapply term_structured_runtime_arguments_core_consequence_valid.
        -- exact (Hvalid _ _ _ Hok).
        -- exact H.
      * apply Hoare.ResourceHoare.resource_prenex_entails_refl.
      * exact H0.
    + exact Htrusted.
  - destruct (IHderivation entry exit certificate Hwf Hcost
      Hprocedure_cost Hregistered Hsafe) as [Hvalid Htrusted].
    split.
    + intros conditions ts tracked Hok.
      eapply term_structured_runtime_arguments_stack_rewrite_valid;
        [exact (Hvalid _ _ _ Hok) | exact H].
    + exact Htrusted.
  - (* done: it erases to the terminal statement and leaves the analysis
       state unchanged, so its runtime meaning is the identity update
       [|={E,E}=> post] — no leaf machinery, and no dependence on the shape
       of the pre- and postcondition. *)
    split; [|intros runtime; exact I]. intros conditions ts tracked Hok.
    intros types held _ _ values runtime formals binders valuation ambient
      Henvelope _.
    unfold term_structured_runtime_wp.
    rewrite translated_runtime_wp_erased; [|reflexivity].
    iIntros "H". iModIntro. iExact "H".
  - (* assert *)
    split; [|intros runtime; exact I]. intros conditions ts tracked Hok.
    eapply term_structured_runtime_arguments_same_store_valid.
    match goal with
    | Hview : _ = AnalysisView.ViewLeaf,
      Hstep : _ = inr _ |- _ =>
        eapply (term_structured_runtime_resource_prenex_leaf_valid
          Hview Hstep); [constructor | exact Hwf | exact Hprocedure_cost]
    end.
  - (* assignment *)
    split; [|intros runtime; exact I]. intros conditions ts tracked Hok.
    eapply term_structured_runtime_arguments_updated_store_valid.
    + reflexivity.
    + match goal with
      | Hview : _ = AnalysisView.ViewLeaf,
        Hstep : _ = inr _ |- _ =>
          eapply (term_structured_runtime_resource_prenex_leaf_valid
            Hview Hstep); [constructor | exact Hwf | exact Hprocedure_cost]
      end.
  - (* field read *)
    split; [|intros runtime; exact I]. intros conditions ts tracked Hok.
    eapply term_structured_runtime_arguments_updated_store_valid.
    + reflexivity.
    + match goal with
      | Hview : _ = AnalysisView.ViewLeaf,
        Hstep : _ = inr _ |- _ =>
          eapply (term_structured_runtime_resource_prenex_leaf_valid
            Hview Hstep); [constructor | exact Hwf | exact Hprocedure_cost]
      end.
  - (* field write *)
    split; [|intros runtime; exact I]. intros conditions ts tracked Hok.
    eapply term_structured_runtime_arguments_same_store_valid.
    match goal with
    | Hview : _ = AnalysisView.ViewLeaf,
      Hstep : _ = inr _ |- _ =>
        eapply (term_structured_runtime_resource_prenex_leaf_valid
          Hview Hstep); [constructor | exact Hwf | exact Hprocedure_cost]
    end.
  - (* allocation *)
    split; [|intros runtime; exact I]. intros conditions ts tracked Hok.
    eapply term_structured_runtime_arguments_updated_store_valid.
    + reflexivity.
    + match goal with
      | Hview : _ = AnalysisView.ViewLeaf,
        Hstep : _ = inr _ |- _ =>
          eapply (term_structured_runtime_resource_prenex_leaf_valid
            Hview Hstep); [constructor; eauto | exact Hwf |
              exact Hprocedure_cost]
      end.
  - (* ghost update *)
    split; [|intros runtime; exact I]. intros conditions ts tracked Hok.
    eapply term_structured_runtime_arguments_same_store_valid.
    match goal with
    | Hview : _ = AnalysisView.ViewLeaf,
      Hstep : _ = inr _ |- _ =>
        eapply (term_structured_runtime_resource_prenex_leaf_valid
          Hview Hstep); [constructor | exact Hwf | exact Hprocedure_cost]
    end.
  - destruct (term_access_safe_sequence certificate1 certificate2 Hsafe)
      as [Hfirst_safe Hsecond_cases].
    have Hsecond_safe : term_access_safe certificate2
      by (destruct Hsecond_cases as [[? _] | (? & _ & _ & ? & _)]; assumption).
    destruct (IHderivation1 entry middle0 certificate1 Hwf Hcost
      Hprocedure_cost
      (fun invariant Hin => Hregistered invariant
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      (term_access_safe_strict _ Hfirst_safe)) as [Hfirst Hfirst_trusted].
    have Hmiddle_wf := term_structured_certificate_preserves_wf certificate1 Hwf.
    destruct (IHderivation2 middle0 exit certificate2 Hmiddle_wf Hcost
      Hprocedure_cost
      (fun invariant Hin => Hregistered invariant
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      Hsecond_safe) as [Hsecond Hsecond_trusted].
    split.
    + intros conditions ts tracked _.
      have Hfirst_ok := term_access_conditions_ok_strict _ Hfirst_safe.
      destruct Hsecond_cases as [[_ Hsecond_ok] |
        (condition & -> & Hstable & _ & Hsecond_ok)].
      * eapply term_structured_runtime_arguments_sequence_valid;
          [exact (Hfirst _ _ _ Hfirst_ok) | exact (Hsecond _ _ _ Hsecond_ok)].
      * eapply term_structured_runtime_arguments_asserted_sequence_valid;
          [exact derivation1 | exact Hstable
          | exact (Hfirst _ _ _ Hfirst_ok) | exact (Hsecond _ _ _ Hsecond_ok)].
    + intros runtime. simpl. split;
        [apply Hfirst_trusted | apply Hsecond_trusted].
  - destruct (IHderivation1 entry then_exit certificate1 Hwf Hcost
      Hprocedure_cost
      (fun invariant Hin => Hregistered invariant
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      (term_access_safe_strict _ (proj1 Hsafe))) as [Hthen Hthen_trusted].
    destruct (IHderivation2 entry else_exit certificate2 Hwf Hcost
      Hprocedure_cost
      (fun invariant Hin => Hregistered invariant
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      (term_access_safe_strict _ (proj2 Hsafe))) as [Helse Helse_trusted].
    split.
    + intros conditions ts tracked Hok.
      eapply term_structured_runtime_arguments_conditional_valid;
        [exact (Hthen _ _ _ (term_access_conditions_ok_strict _ (proj1 Hsafe)))
        | exact (Helse _ _ _
            (term_access_conditions_ok_strict _ (proj2 Hsafe)))].
    + intros runtime. simpl. split;
        [apply Hthen_trusted | apply Helse_trusted].
  - (* unmatched fold allocates the invariant *)
    split.
    + intros conditions ts tracked Hok.
      have Hregistered_invariant :
          invariant ∈ term_registered_invariants .
      { apply Hregistered.
        apply (Structured.structured_certificate_exit_subset_footprint
          (Structured.StructuredFreshFold Γ entry invariant
            arguments n)).
        rewrite Certified.fold_analysis_mask; [|exact n].
        apply elem_of_union_r. apply elem_of_singleton_2. reflexivity. }
      exact (term_structured_runtime_arguments_fresh_fold_valid
         n Hregistered_invariant conditions tracked store).
    + intros runtime. exact I.
  - (* predicate unfold *)
    split; [|intros runtime; exact I]. intros conditions ts tracked Hok.
    eapply term_structured_runtime_arguments_same_store_valid.
    match goal with
    | Hview : _ = AnalysisView.ViewLeaf,
      Hstep : _ = inr _ |- _ =>
        eapply (term_structured_runtime_resource_prenex_leaf_valid
          Hview Hstep); [constructor | exact Hwf | exact Hprocedure_cost]
    end.
  - (* predicate fold *)
    split; [|intros runtime; exact I]. intros conditions ts tracked Hok.
    eapply term_structured_runtime_arguments_same_store_valid.
    match goal with
    | Hview : _ = AnalysisView.ViewLeaf,
      Hstep : _ = inr _ |- _ =>
        eapply (term_structured_runtime_resource_prenex_leaf_valid
          Hview Hstep); [constructor | exact Hwf | exact Hprocedure_cost]
    end.
  - (* invariant access *)
    simpl in Hsafe. destruct Hsafe as [Hentry_nonatomic Hbody_safe].
    have Hopen_facts := e.
    apply GenericRegions.Atomicity.open_access_success in Hopen_facts as
      (Hopened_mask & Hopened_open).
    have Hopened_wf : GenericRegions.Atomicity.state_wf opened.
    { eapply GenericRegions.Atomicity.open_access_preserves_wf; eauto. }
    destruct (IHderivation opened inner certificate Hopened_wf Hcost
      Hprocedure_cost
      (fun candidate Hin => Hregistered candidate
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      (term_access_safe_strict _ Hbody_safe)) as [Hbody_valid Hbody_trusted].
    have Hbody_ok := term_access_conditions_ok_strict _ Hbody_safe.
    split; [|exact Hbody_trusted].
    intros conditions ts tracked Hok.
    destruct (decide (invariant ∈
      GenericRegions.Atomicity.analysis_open entry)) as [Hnested|Hclosed].
    + destruct Hok as [Hclosed | Hcondition]; [contradiction|].
      exact (term_structured_runtime_nested_inv_access_arguments_valid
        e Hnested certificate e0 opening_focus closing_focus
        external_pre body_pre body_post external_post H H0 H1
        conditions tracked Hcondition (Hbody_valid _ _ _ Hbody_ok)).
    + { have Hopen_fresh := GenericRegions.Atomicity.open_access_fresh _ _ _ _ _
        Hclosed e.
      have Havailable := proj1 (proj2
        (GenericRegions.Atomicity.open_invariant_success _ _ _ _ Hopen_fresh)).
      have Hregistered_invariant :
          invariant ∈ term_registered_invariants .
      { apply Hregistered.
        apply (Structured.structured_certificate_entry_subset_footprint
          (Structured.StructuredInvAccess Γ entry invariant arguments
            excluded body opened inner e certificate e0)).
        exact Havailable. }
      eapply (term_structured_runtime_independent_inv_access_arguments_valid
        Hregistered_invariant e Hclosed certificate e0 opening_focus
        closing_focus external_pre body_pre body_post external_post H H0 H1
        conditions tracked).
      - exact (Hbody_valid _ _ _ Hbody_ok).
      - intros runtime.
        eapply (term_open_structured_certificate_runtime_atomic certificate
          runtime Hcost).
        + simpl. intros Hempty.
          have Hin_opened : invariant ∈
              GenericRegions.Atomicity.analysis_open opened.
          { rewrite Hopened_open. set_solver. }
          rewrite Hempty in Hin_opened. set_solver.
        + rewrite (GenericRegions.Atomicity.open_access_preserves_in_atomic
                _ _ _ entry opened e). exact Hentry_nonatomic.
        + apply Hbody_trusted.
      }
  - (* trusted atomic block *)
    simpl in Hsafe.
    have Houter_wf : GenericRegions.Atomicity.state_wf outer.
    { eapply GenericRegions.Atomicity.take_step_preserves_wf; eauto. }
    have Hbody_wf : GenericRegions.Atomicity.state_wf
        (GenericRegions.Atomicity.atomic_entry outer).
    { exact Houter_wf. }
    destruct (IHderivation _ inner certificate Hbody_wf Hcost
      Hprocedure_cost
      (fun invariant Hin => Hregistered invariant
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      (term_access_safe_strict _ Hsafe)) as [Hbody_valid Hbody_trusted].
    split.
    + intros conditions ts tracked Hok.
      eapply term_structured_runtime_arguments_atomic_valid.
      exact (Hbody_valid _ _ _ (term_access_conditions_ok_strict _ Hsafe)).
    + intros runtime. exact I.
  - (* ghost value *)
    simpl in Hsafe.
    destruct (IHderivation _ _ certificate Hwf Hcost Hprocedure_cost
      (fun invariant Hin => Hregistered invariant
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      (term_access_safe_strict _ Hsafe)) as [Hbody_valid Hbody_trusted].
    split.
    + intros conditions ts tracked Hok.
      apply term_structured_runtime_arguments_ghost_val_valid.
      exact (Hbody_valid _ _ _ (term_access_conditions_ok_strict _ Hsafe)).
    + intros runtime. apply Hbody_trusted.
  - (* call, result discarded *)
    split; [|intros runtime; exact I]. intros conditions ts tracked Hok.
    eapply term_structured_runtime_arguments_weakened_store_valid.
    match goal with
    | Hview : _ = AnalysisView.ViewLeaf,
      Hstep : _ = inr _ |- _ =>
        eapply (term_structured_runtime_resource_prenex_leaf_valid
          Hview Hstep); [constructor; exact H | exact Hwf |
            exact Hprocedure_cost]
    end.
  - (* call, result stored *)
    split; [|intros runtime; exact I]. intros conditions ts tracked Hok.
    eapply term_structured_runtime_arguments_updated_store_valid.
    + reflexivity.
    + match goal with
      | Hview : _ = AnalysisView.ViewLeaf,
        Hstep : _ = inr _ |- _ =>
          eapply (term_structured_runtime_resource_prenex_leaf_valid
            Hview Hstep); [constructor; exact H | exact Hwf |
              exact Hprocedure_cost]
      end.
  - (* spawn *)
    split; [|intros runtime; exact I]. intros conditions ts tracked Hok.
    eapply term_structured_runtime_arguments_same_store_valid.
    match goal with
    | Hview : _ = AnalysisView.ViewLeaf,
      Hstep : _ = inr _ |- _ =>
        eapply (term_structured_runtime_resource_prenex_leaf_valid
          Hview Hstep); [constructor; exact H | exact Hwf |
            exact Hprocedure_cost]
    end.
  - (* ghost conditional *)
    destruct (IHderivation1 entry then_exit certificate1 Hwf Hcost
      Hprocedure_cost
      (fun invariant Hin => Hregistered invariant
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      (term_access_safe_strict _ (proj1 Hsafe))) as [Hthen Hthen_trusted].
    destruct (IHderivation2 entry else_exit certificate2 Hwf Hcost
      Hprocedure_cost
      (fun invariant Hin => Hregistered invariant
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      (term_access_safe_strict _ (proj2 Hsafe))) as [Helse Helse_trusted].
    split.
    + intros conditions ts tracked Hok.
      match goal with
      | Hthen_proof : proof_onlyb then_branch = true,
        Helse_proof : proof_onlyb else_branch = true |- _ =>
          exact (term_structured_runtime_arguments_ghost_conditional_valid
            certificate1 certificate2 _ _ conditions tracked _ _ _ Hthen_proof
            Helse_proof
            (Hthen _ _ _ (term_access_conditions_ok_strict _ (proj1 Hsafe)))
            (Helse _ _ _ (term_access_conditions_ok_strict _ (proj2 Hsafe))))
      end.
    + intros runtime. simpl. split;
        [apply Hthen_trusted | apply Helse_trusted].
  - (* tracked expression *)
    destruct (IHderivation entry _ certificate Hwf Hcost Hprocedure_cost
      Hregistered Hsafe) as [Hvalid Htrusted].
    split; [|exact Htrusted].
    intros conditions ts tracked Hok types held Haligned Hdisjoint values
      runtime formals binders valuation ambient Henvelope Hconditions.
    have Haligned' : held_aligned
        (GenericRegions.Atomicity.analysis_records entry)
        (held_track (ltac:(match type of expression with
          | gexpr _ ?u => exact u end)) held).
    { unfold held_aligned. rewrite held_track_records. exact Haligned. }
    match goal with
    | Hstable : Hoare.ResourceHoare.pexpr_dependencies expression ## _ |- _ =>
        have Hdisjoint' : Hoare.ResourceHoare.pexpr_list_dependencies
            (held_pinned (PECons expression tracked) (held_track _ held)) ##
          Hoare.ResourceHoare.statement_writes statement
          by (rewrite held_track_pinned;
              cbn [Hoare.ResourceHoare.pexpr_list_dependencies];
              apply disjoint_union_l; split; assumption)
    end.
    destruct (interp_expr_total formals binders valuation value)
      as [tracked_value Htracked_value].
    specialize (Hvalid conditions _ (PECons expression tracked) Hok _
      (held_track _ held) Haligned' Hdisjoint' (TVCons tracked_value values)
      runtime formals binders valuation ambient Henvelope).
    rewrite held_track_pinned held_track_pinned_values held_track_world
      in Hvalid.
    specialize (Hvalid (conditions_hold_cons _ _ _ _ _ Hconditions)).
    iIntros "(#Hglobal & Hheld & Hpre)".
    iEval (rewrite (term_interp_resource_prenex_at_arguments_track runtime
      formals valuation (held_pinned tracked held)
      (held_pinned_values values held) expression pre binders value
      tracked_value Htracked_value)) in "Hpre".
    iPoseProof (Hvalid with "[$Hglobal $Hheld $Hpre]") as "Hwp".
    unfold term_structured_runtime_wp.
    iApply (translated_runtime_wp_mono with "Hwp").
    iIntros "($ & $ & Hpost)".
    rewrite (term_interp_resource_prenex_at_arguments_track runtime formals
      valuation (held_pinned tracked held) (held_pinned_values values held)
      expression post binders value tracked_value Htracked_value).
    iExact "Hpost".
Qed.

Theorem term_structured_certificate_resource_prenex_valid
    {Γ F Δ entry statement exit}
    {pre post : Translation.Resource.resource_prenex Γ F Δ}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (derivation : CertifiedNormalization.RavenHoareRules.RavenHoareTriple
      pre statement post) :
  GenericRegions.Atomicity.analysis_records entry = [] ->
  GenericRegions.Atomicity.state_wf entry ->
  RegionExecution.Primitives.Model.runtime_cost_model_sound ->
  Certified.procedure_cost_model_sound ->
  term_structured_invariants_registered certificate ->
  term_structured_accesses_outside_atomic certificate ->
  term_structured_runtime_valid certificate pre post /\
  (forall runtime,
    term_structured_certificate_trusted_runtime_atomicity certificate runtime).
Proof.
  intros Hrecords Hwf Hcost Hprocedure_cost Hregistered Hsafe.
  destruct (term_structured_certificate_resource_prenex_arguments_valid
     certificate derivation Hwf Hcost Hprocedure_cost Hregistered
     (term_access_safe_strict _ Hsafe))
    as [Harguments Htrusted].
  split; [|exact Htrusted].
  intros runtime formals binders valuation ambient Henvelope.
  have Hempty := Harguments [] [] (@PENil _ keep_all Γ)
    (term_access_conditions_ok_strict _ Hsafe).
  unfold term_structured_runtime_arguments_valid in Hempty.
  have Haligned : held_aligned
      (GenericRegions.Atomicity.analysis_records entry)
      (HeldNil (Γ := Γ) (ts := [])).
  { unfold held_aligned. rewrite Hrecords. reflexivity. }
  specialize (Hempty [] HeldNil Haligned ltac:(simpl; apply disjoint_empty_l)
    Translation.TVNil runtime formals binders valuation ambient Henvelope
    (conditions_hold_nil _ _)).
  cbn [held_pinned held_pinned_values] in Hempty.
  rewrite term_interp_resource_prenex_at_arguments_empty in Hempty.
  iIntros "[Hglobal Hpre]".
  iPoseProof (Hempty with "[Hglobal Hpre]") as "Hwp".
  { iFrame "Hglobal Hpre". unfold held_world. cbn [held_opened].
    by rewrite big_sepM_empty. }
  unfold term_structured_runtime_wp.
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "($ & _ & Hpost)".
  rewrite term_interp_resource_prenex_at_arguments_empty. done.
Qed.

End WithRuntime.
End WithContracts.
End RuleValidity.
