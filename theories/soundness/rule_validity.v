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
    { callee_variables : context &
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
    (store : symbolic_store Γ F Δ) (target : pvar Γ t) (value : tval t) :
  Translation.data_stack_own semantic_data (term_semantic_runtime runtime)
      (interp_store formals (binder_cons value binders) valuation
        (IR.update_store_with_bound store target)) ⊣⊢
    RuntimeGhost.stack_frame_own
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      (RuntimeLang.StackFrame
        (<[@RuntimeErasure.runtime_variable Γ t
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
    (arguments : pexpr_list Γ ts) (values : tval_list ts)
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
    (arguments : pexpr_list Γ ts) (values : tval_list ts)
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
    (arguments : pexpr_list Γ ts) (values : tval_list ts)
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

Lemma term_interp_resource_prenex_at_arguments_entails {Γ F Δ ts}
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (arguments : pexpr_list Γ ts) (values : tval_list ts)
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
    (arguments : pexpr_list Γ ts) (values : tval_list ts)
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
      (@PENil _ Γ) Translation.TVNil prenex ≡
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
        (GenericRegions.Atomicity.AnalysisState
          (GenericRegions.Atomicity.analysis_mask outer)
          (GenericRegions.Atomicity.analysis_open outer)
          (GenericRegions.Atomicity.analysis_step_taken outer) true)
        body inner)
      (runtime : RegionExecution.Primitives.Model.stack_context Γ) ambient post,
    GenericRegions.Atomicity.take_step GenericRegions.Atomicity.AtomicStep state =
      inr outer ->
    GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open outer ->
    translated_runtime_wp runtime ambient
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask outer)
        (GenericRegions.Atomicity.analysis_open outer)
        (GenericRegions.Atomicity.analysis_step_taken outer) true)
      inner body post ⊢
      translated_runtime_wp runtime ambient state
        (GenericRegions.Atomicity.AnalysisState
          (GenericRegions.Atomicity.analysis_mask inner)
          (GenericRegions.Atomicity.analysis_open inner)
          (GenericRegions.Atomicity.analysis_step_taken outer ||
            GenericRegions.Atomicity.analysis_step_taken inner)
          (GenericRegions.Atomicity.analysis_in_atomic outer))
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
      (Assertion.procedure_return procedure :: Δ)) current_mask :
    resource_instantiated_pre F Δ procedure
      (IR.symbolize_expr_list store arguments) contract_pre ->
    resource_instantiated_post_value F Δ procedure
      (Translation.Assertions.weaken_expr_list
        (IR.symbolize_expr_list store arguments))
      (ERef (RefBound MHere)) contract_post ->
    Certified.required_mask procedure ⊆ current_mask ->
    procedure_leaf_obligation current_mask
      (current_mask ∪ Certified.granted_mask procedure)
      (Translation.Resource.RState store contract_pre)
      (TCall procedure arguments (@CTDiscard Γ (Assertion.procedure_return procedure)))
      (Translation.Resource.ResourceExists (Assertion.procedure_return procedure)
        (Translation.Resource.RState
          (Translation.Assertions.weaken_store store) contract_post))
| ProcedureStoreObligation procedure arguments store target
    contract_pre (contract_post : Translation.Resource.core_assertion F
      (Assertion.procedure_return procedure :: Δ))
    current_mask :
    resource_instantiated_pre F Δ procedure
      (IR.symbolize_expr_list store arguments) contract_pre ->
    resource_instantiated_post_value F Δ procedure
      (Translation.Assertions.weaken_expr_list
        (IR.symbolize_expr_list store arguments))
      (ERef (RefBound MHere)) contract_post ->
    Certified.required_mask procedure ⊆ current_mask ->
    procedure_leaf_obligation current_mask
      (current_mask ∪ Certified.granted_mask procedure)
      (Translation.Resource.RState store contract_pre)
      (TCall procedure arguments (CTStore target))
      (Translation.Resource.ResourceExists (Assertion.procedure_return procedure)
        (Translation.Resource.RState
          (IR.update_store_with_bound store target) contract_post))
| ProcedureSpawnObligation procedure arguments store contract_pre
    current_mask :
    resource_instantiated_pre F Δ procedure
      (IR.symbolize_expr_list store arguments) contract_pre ->
    Certified.required_mask procedure ⊆ current_mask ->
    procedure_leaf_obligation current_mask current_mask
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
    (typed_arguments : pexpr_list Γ (Assertion.procedure_args procedure))
    (current_mask : Hoare.mask) :
  Hoare.ResourceHoare.procedure_verified procedure ->
  Certified.required_mask procedure ⊆ current_mask ->
  procedure_leaf_obligation current_mask
    (current_mask ∪ Certified.granted_mask procedure)
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
  intros Hverified Hmask.
  apply ProcedureDiscardObligation;
    [split; [exact Hverified | reflexivity]
    | split; [exact Hverified | reflexivity]
    | exact Hmask].
Qed.

Lemma call_store_obligation {Γ F Δ} procedure
    (store : symbolic_store Γ F Δ)
    (target : pvar Γ (Assertion.procedure_return procedure))
    (typed_arguments : pexpr_list Γ (Assertion.procedure_args procedure))
    (current_mask : Hoare.mask) :
  Hoare.ResourceHoare.procedure_verified procedure ->
  Certified.required_mask procedure ⊆ current_mask ->
  procedure_leaf_obligation current_mask
    (current_mask ∪ Certified.granted_mask procedure)
    (Translation.Resource.RState store
      (ResourceInstances.instantiated_pre procedure
        (IR.symbolize_expr_list store typed_arguments)))
    (TCall procedure typed_arguments (CTStore target))
    (Translation.Resource.ResourceExists (Assertion.procedure_return procedure)
      (Translation.Resource.RState
        (IR.update_store_with_bound store target)
        (ResourceInstances.instantiated_post procedure
          (Translation.Assertions.weaken_expr_list
            (IR.symbolize_expr_list store typed_arguments))))).
Proof.
  intros Hverified Hmask.
  apply ProcedureStoreObligation;
    [split; [exact Hverified | reflexivity]
    | split; [exact Hverified | reflexivity]
    | exact Hmask].
Qed.

Lemma spawn_obligation {Γ F Δ} procedure
    (store : symbolic_store Γ F Δ)
    (typed_arguments : pexpr_list Γ (Assertion.procedure_args procedure))
    (current_mask : Hoare.mask) :
  Hoare.ResourceHoare.procedure_verified procedure ->
  Certified.required_mask procedure ⊆ current_mask ->
  procedure_leaf_obligation current_mask current_mask
    (Translation.Resource.RState store
      (ResourceInstances.instantiated_pre procedure
        (IR.symbolize_expr_list store typed_arguments)))
    (TSpawn procedure typed_arguments)
    (Translation.Resource.RState store
      (Translation.Resource.CPure True)).
Proof.
  intros Hverified Hmask.
  apply ProcedureSpawnObligation;
    [split; [exact Hverified | reflexivity] | exact Hmask].
Qed.

Definition verified_procedure_specs : iProp :=
  (□ ∀ (Γ F Δ : context)
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
    (store : symbolic_store Γ F Δ) field (base : pexpr Γ TRef)
    (expression : pexpr Γ (Assertion.field_type field)) old_chunk
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
    (target : pvar Γ (Assertion.field_type field)) (base : pexpr Γ TRef)
    chunk (entry exit : GenericRegions.Atomicity.analysis_state) :
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    term_interp_resource_prenex runtime formals binders valuation
      (Translation.Resource.RState store
        (Translation.Resource.COwn field (IR.symbolize_expr store base)
          chunk)) ⊢
    concrete_operation_wp runtime ambient entry
      (TFieldRead field target base) exit
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
    runtime formals binders valuation store field target base location value
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
    (store : symbolic_store Γ F Δ) (target : pvar Γ t)
    (expression : pexpr Γ t)
    (entry exit : GenericRegions.Atomicity.analysis_state) :
  forall (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    term_interp_resource_prenex runtime formals binders valuation
      (Translation.Resource.RState store
        (Translation.Resource.CPure True)) ⊢
    concrete_operation_wp runtime ambient entry
      (TAssign target expression) exit
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
    Γ F Δ t runtime formals binders valuation store target expression
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

(** Parametric strengthening used by matched invariant accesses.  For every
    vector whose stack dependencies the statement does not write, the
    certificate transports its evaluated value through the actual telescope
    witnesses selected at run time. *)
Definition term_structured_runtime_arguments_valid
    {Γ F Δ entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (arguments : pexpr_list Γ ts)
    (pre post : Translation.Resource.resource_prenex Γ F Δ) : Prop :=
  Hoare.ResourceHoare.pexpr_list_dependencies arguments ##
      Hoare.ResourceHoare.statement_writes statement ->
  forall (values : tval_list ts)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (ambient : coPset),
    RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint certificate ∪
        term_registered_invariants) ⊆ ambient ->
    (global_world_context valuation ∗
      term_interp_resource_prenex_at_arguments runtime formals binders valuation
        arguments values pre) ⊢
    term_structured_runtime_wp certificate runtime ambient
      (global_world_context valuation ∗
       term_interp_resource_prenex_at_arguments runtime formals binders valuation
         arguments values post).

Lemma term_structured_certificate_preserves_open
    {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit) :
  GenericRegions.Atomicity.analysis_open exit =
    GenericRegions.Atomicity.analysis_open entry.
Proof.
  induction certificate; simpl.
  - eapply GenericRegions.Atomicity.take_step_preserves_open; eauto.
  - reflexivity.
  - apply GenericRegions.Atomicity.fold_fresh_invariant in n as [_ Hopen].
    exact Hopen.
  - etrans; eauto.
  - exact IHcertificate1.
  - simpl. rewrite e0.
    eapply GenericRegions.Atomicity.take_step_preserves_open; eauto.
  - apply GenericRegions.Atomicity.open_invariant_success in e as
      (Hfresh & _ & _ & Hopened).
    have Hmember : invariant ∈ GenericRegions.Atomicity.analysis_open inner.
    { rewrite e0 Hopened. apply elem_of_union_l.
      apply elem_of_singleton_2. reflexivity. }
    destruct (GenericRegions.Atomicity.fold_open_invariant invariant inner Hmember)
      as [_ Hfolded].
    rewrite Hfolded e0 Hopened.
    apply set_eq. intros candidate.
    rewrite elem_of_difference elem_of_union elem_of_singleton.
    split.
    + intros [[->|Hcandidate] Hneq]; [contradiction|exact Hcandidate].
    + intros Hcandidate. split; [right; exact Hcandidate|].
      intros ->. apply Hfresh. exact Hcandidate.
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
    (GenericRegions.Atomicity.fold_invariant invariant entry)
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
    invariant entry Hfresh.
  destruct Hfold_facts as [_ Hfold_open].
  have Hactive : RegionExecution.Primitives.Model.active_runtime_mask ambient
      (GenericRegions.Atomicity.fold_invariant invariant entry) =
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
          (GenericRegions.Atomicity.fold_invariant invariant entry)))
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
    (store : symbolic_store Γ F Δ) condition b :
  interp_expr formals binders valuation
    (IR.symbolize_expr store condition) = Some (VBool b) ->
  RuntimeLang.expr_step
    (@RuntimeErasure.runtime_expr _ Γ _ (RegionExecution.Primitives.Model.runtime_names Γ runtime) condition)
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
    frame (condition : pexpr Γ TBool) then_runtime else_runtime mask
    (P : iProp) (Phi : RuntimeLang.val -> iProp) :
  RuntimeLang.expr_step
    (@RuntimeErasure.runtime_expr _ Γ _ (RegionExecution.Primitives.Model.runtime_names Γ runtime) condition) frame
    (RuntimeLang.Val (RuntimeLang.LitBool true)) ->
  (RuntimeGhost.stack_frame_own (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) frame ∗ P ⊢
    @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG mask then_runtime Phi) ->
  RuntimeGhost.stack_frame_own (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) frame ∗ P ⊢
    @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG mask
      (RuntimeLang.RTIfS
        (@RuntimeErasure.runtime_expr _ Γ _ (RegionExecution.Primitives.Model.runtime_names Γ runtime) condition)
        then_runtime else_runtime (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)) Phi.
Proof.
  intros Hcondition Hthen. iIntros "Hresources". unfold RegionExecution.Primitives.Model.runtime_wp.
  iApply (RuntimeLifting.wp_if_t_wp _ _ _ _ frame P Phi mask Hcondition
    with "[] Hresources").
  iIntros "Hresources". iPoseProof (Hthen with "Hresources") as "Hwp".
  iExact "Hwp".
Qed.

Lemma runtime_wp_if_false {Γ} (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    frame (condition : pexpr Γ TBool) then_runtime else_runtime mask
    (P : iProp) (Phi : RuntimeLang.val -> iProp) :
  RuntimeLang.expr_step
    (@RuntimeErasure.runtime_expr _ Γ _ (RegionExecution.Primitives.Model.runtime_names Γ runtime) condition) frame
    (RuntimeLang.Val (RuntimeLang.LitBool false)) ->
  (RuntimeGhost.stack_frame_own (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) frame ∗ P ⊢
    @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG mask else_runtime Phi) ->
  RuntimeGhost.stack_frame_own (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) frame ∗ P ⊢
    @RegionExecution.Primitives.Model.runtime_wp _ _ Σ RG mask
      (RuntimeLang.RTIfS
        (@RuntimeErasure.runtime_expr _ Γ _ (RegionExecution.Primitives.Model.runtime_names Γ runtime) condition)
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
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask then_exit ∩
          GenericRegions.Atomicity.analysis_mask else_exit)
        (GenericRegions.Atomicity.analysis_open then_exit)
        (GenericRegions.Atomicity.analysis_step_taken then_exit ||
          GenericRegions.Atomicity.analysis_step_taken else_exit)
        (GenericRegions.Atomicity.analysis_in_atomic then_exit)).
Proof. apply RegionExecution.Primitives.Model.active_runtime_mask_same_open. reflexivity. Qed.

Lemma conditional_else_active_mask_join ambient then_exit else_exit :
  GenericRegions.Atomicity.analysis_open then_exit =
    GenericRegions.Atomicity.analysis_open else_exit ->
  RegionExecution.Primitives.Model.active_runtime_mask ambient else_exit =
    RegionExecution.Primitives.Model.active_runtime_mask ambient
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask then_exit ∩
          GenericRegions.Atomicity.analysis_mask else_exit)
        (GenericRegions.Atomicity.analysis_open then_exit)
        (GenericRegions.Atomicity.analysis_step_taken then_exit ||
          GenericRegions.Atomicity.analysis_step_taken else_exit)
        (GenericRegions.Atomicity.analysis_in_atomic then_exit)).
Proof.
  intros Hopen. apply RegionExecution.Primitives.Model.active_runtime_mask_same_open. simpl.
  symmetry. exact Hopen.
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
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) ambient state then_exit else_exit
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
    (runtime : RegionExecution.Primitives.Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) ambient state condition
    (then_branch else_branch : stmt Γ) then_exit else_exit post P
    (open_equal : GenericRegions.Atomicity.analysis_open then_exit =
      GenericRegions.Atomicity.analysis_open else_exit) :
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
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask then_exit ∩
          GenericRegions.Atomicity.analysis_mask else_exit)
        (GenericRegions.Atomicity.analysis_open then_exit)
        (GenericRegions.Atomicity.analysis_step_taken then_exit ||
          GenericRegions.Atomicity.analysis_step_taken else_exit)
        (GenericRegions.Atomicity.analysis_in_atomic then_exit))
      (TIf condition then_branch else_branch) post.
Proof.
  intros Hthen Helse. eapply translated_runtime_wp_if_total.
  - intros Hcondition. rewrite <- translated_runtime_wp_then_join_transport.
    now apply Hthen.
  - intros Hcondition.
    rewrite <- (translated_runtime_wp_else_join_transport
      runtime ambient state then_exit else_exit else_branch post open_equal).
    now apply Helse.
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
    (TFold invariant arguments) invariant eq_refl).
  have Hraw_envelope : RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.certificate_footprint raw) ⊆ ambient.
  { etrans; last exact Henvelope. apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros candidate Hin. apply elem_of_union_l.
    simpl in Hin |- *. repeat rewrite elem_of_union in *.
    tauto. }
  have Hexit_member : invariant ∈ GenericRegions.Atomicity.analysis_mask
      (GenericRegions.Atomicity.fold_invariant invariant entry).
  { rewrite Certified.fold_analysis_mask. set_solver. }
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
      destruct (tval_eqb t (interp_ref formals binders valuation left)
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
Lemma term_access_opening_arguments_valid {Γ F Δ} invariant
    (program_arguments : pexpr_list Γ (Assertion.invariant_args invariant))
    (focus : CertifiedNormalization.RavenHoareRules.access_focus
      invariant program_arguments Δ)
    (external body_pre : Translation.Resource.resource_prenex Γ F Δ)
    (Hopening : CertifiedNormalization.RavenHoareRules.access_opening
      invariant program_arguments focus external body_pre)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    {tracked_types} (tracked : pexpr_list Γ tracked_types)
    (tracked_values : tval_list tracked_types) (outer_mask : coPset) :
  ↑(invariant_namespace invariant) ⊆ outer_mask ->
  inv (invariant_namespace invariant) (term_world valuation invariant) -∗
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      tracked tracked_values external -∗
  |={outer_mask, outer_mask ∖ ↑(invariant_namespace invariant)}=>
    ∃ invariant_values : tval_list (Assertion.invariant_args invariant),
      term_interp_resource_prenex_at_arguments runtime formals binders valuation
        (IR.pexpr_list_append tracked program_arguments)
        (Translation.tval_list_append tracked_values invariant_values)
        body_pre ∗
      (world_body_interp valuation invariant invariant_values
        ={outer_mask ∖ ↑(invariant_namespace invariant), outer_mask}=∗
        True) ∗
      @RegionExecution.Primitives.Model.core_invariant_own _ _ Σ RG invariant
        invariant_values.
Proof.
  intros Hnamespace. revert binders.
  induction Hopening; intros binders; iIntros "#Hworld Hpre".
  - cbn [term_interp_resource_prenex_at_arguments].
    iDestruct "Hpre" as "[[Hstack Htoken] %Htracked]".
    iDestruct "Htoken" as (values) "[%Harguments #Htoken]".
    iPoseProof "Htoken" as "#Htoken_saved".
    iMod (term_world_open valuation invariant values outer_mask Hnamespace
      with "Hworld Htoken") as "[Hbody Hclose]".
    destruct (term_invariant_definition_compatible formals binders
      valuation invariant (IR.symbolize_expr_list store program_arguments)) as
      (actual_values & Hactual & Hbody_equiv).
    rewrite Harguments in Hactual. injection Hactual as Hvalues.
    subst actual_values.
    iEval (rewrite -Hbody_equiv) in "Hbody".
    iModIntro. iExists values. iFrame "Hclose Htoken_saved".
    cbn [term_interp_resource_prenex_at_arguments].
    iFrame "Hstack Hbody". iPureIntro.
    rewrite IR.symbolize_expr_list_append.
    apply Translation.interp_expr_list_append_some; assumption.
  - cbn [term_interp_resource_prenex_at_arguments] in *.
    iDestruct "Hpre" as (value) "Hpre".
    iMod (IHHopening (binder_cons value binders) with "Hworld Hpre") as
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
      valuation tracked tracked_values external _
      Assertions.weaken_bound_renaming source_binders binders Hrenaming)) in
      "Hpre".
    iMod (IHHopening source_binders with "Hworld Hpre") as
      (values) "[Hbody [Hclose Htoken]]".
    iModIntro. iExists values. iFrame "Hclose Htoken".
    iEval (rewrite (term_interp_resource_prenex_at_arguments_rename runtime formals
      valuation (IR.pexpr_list_append tracked program_arguments)
      (Translation.tval_list_append tracked_values values) body_pre _
      Assertions.weaken_bound_renaming source_binders binders Hrenaming)).
    iExact "Hbody".
  - iEval (cbn [term_interp_resource_prenex_at_arguments]) in "Hpre".
    iDestruct "Hpre" as (value) "Hpre".
    iMod (IHHopening (binder_cons value binders) with "Hworld Hpre") as
      (values) "[Hbody [Hclose Htoken]]".
    iModIntro. iExists values. iFrame "Hclose Htoken".
    iEval (rewrite (term_interp_resource_prenex_at_arguments_weaken runtime
      formals binders valuation
      (IR.pexpr_list_append tracked program_arguments)
      (Translation.tval_list_append tracked_values values) value body_pre)) in
      "Hbody".
    iExact "Hbody".
  - iPoseProof (term_interp_resource_prenex_at_arguments_entails runtime
      formals binders valuation tracked tracked_values external' external H
      with "Hpre") as "Hpre".
    iMod (IHHopening binders with "Hworld Hpre") as
      (values) "[Hbody [Hclose Htoken]]".
    iModIntro. iExists values. iFrame "Hclose Htoken".
    iApply (term_interp_resource_prenex_at_arguments_entails runtime formals
      binders valuation (IR.pexpr_list_append tracked program_arguments)
      (Translation.tval_list_append tracked_values values)
      body_pre body_pre' H0 with "Hbody").
  - iEval (cbn [term_interp_resource_prenex_at_arguments]) in "Hpre".
    iDestruct "Hpre" as "[[Hstack [Hpre Hframe]] %Htracked]".
    iMod (IHHopening binders with "Hworld [Hstack Hpre]") as
      (values) "[Hbody [Hclose Htoken]]".
    { cbn [term_interp_resource_prenex_at_arguments]. iFrame.
      iPureIntro. exact Htracked. }
    iModIntro. iExists values. iFrame "Hclose Htoken".
    iEval (rewrite (term_interp_resource_prenex_at_arguments_and runtime
      formals binders valuation (IR.pexpr_list_append tracked program_arguments)
      (Translation.tval_list_append tracked_values values) body_pre frame)).
    iFrame.
  - iEval (cbn [term_interp_resource_prenex_at_arguments]) in "Hpre".
    iDestruct "Hpre" as "[[Hstack Hpre] %Htracked]".
    iPoseProof (Validation.TermSemantics.core_entails_valid semantic_data
      (term_predicates valuation) _ _ H formals binders valuation with "Hpre") as
      "Hpre".
    iMod (IHHopening binders with "Hworld [Hstack Hpre]") as
      (values) "[Hbody [Hclose Htoken]]".
    { cbn [term_interp_resource_prenex_at_arguments]. iFrame.
      iPureIntro. exact Htracked. }
    iModIntro. iExists values. iFrame "Hclose Htoken".
    iApply (term_interp_resource_prenex_at_arguments_entails runtime formals
      binders valuation (IR.pexpr_list_append tracked program_arguments)
      (Translation.tval_list_append tracked_values values)
      body_pre body_pre' H0 with "Hbody").
  - iEval (cbn [term_interp_resource_prenex_at_arguments]) in "Hpre".
    iDestruct "Hpre" as "[[Hstack Hbody] %Htracked]".
    iPoseProof (interp_store_equal_under pre_body store store' H formals
      binders valuation with "Hbody") as "%Hstores".
    iEval (rewrite Hstores) in "Hstack".
    have Hargument_interp := interp_program_expr_list_store_ext formals
      binders valuation store' store tracked Hstores.
    unfold interp_program_expr_list in Hargument_interp.
    rewrite Htracked in Hargument_interp.
    iApply (IHHopening binders with "Hworld [Hstack Hbody]").
    cbn [term_interp_resource_prenex_at_arguments]. iFrame.
    iPureIntro. symmetry. exact Hargument_interp.
Qed.

(** Closing-side interpretation for the canonical independent access.  The
    body carries one combined semantic vector: the caller's tracked
    expressions followed by the invariant's program arguments.  The closing
    spine consumes only the latter component and returns the former. *)
Lemma term_access_closing_arguments_valid {Γ F Δ} invariant
    (program_arguments : pexpr_list Γ (Assertion.invariant_args invariant))
    (focus : CertifiedNormalization.RavenHoareRules.access_focus
      invariant program_arguments Δ)
    (body_post external_post : Translation.Resource.resource_prenex Γ F Δ)
    (Hclosing : CertifiedNormalization.RavenHoareRules.access_closing
      invariant program_arguments focus body_post external_post)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    {tracked_types} (tracked : pexpr_list Γ tracked_types)
    (tracked_values : tval_list tracked_types)
    (invariant_values : tval_list (Assertion.invariant_args invariant))
    (inner_mask outer_mask : coPset) :
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      (IR.pexpr_list_append tracked program_arguments)
      (Translation.tval_list_append tracked_values invariant_values)
      body_post -∗
  (world_body_interp valuation invariant invariant_values
    ={inner_mask, outer_mask}=∗ True) -∗
  @RegionExecution.Primitives.Model.core_invariant_own _ _ Σ RG invariant
    invariant_values -∗
  |={inner_mask, outer_mask}=>
    term_interp_resource_prenex_at_arguments runtime formals binders valuation
      tracked tracked_values external_post.
Proof.
  revert binders.
  induction Hclosing; intros binders.
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
    iMod ("Hclose" with "Hbody"). iModIntro.
    cbn [term_interp_resource_prenex_at_arguments].
    iFrame "Hstack". iSplitL "Htoken".
    + iExists invariant_values. iFrame "Htoken".
      iPureIntro. exact Hinvariant.
    + iPureIntro. exact Htracked.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "Hpost Hclose Htoken". iDestruct "Hpost" as (value) "Hpost".
    iPoseProof (IHHclosing (binder_cons value binders) with
      "Hpost Hclose Htoken") as "Hclosed".
    iMod "Hclosed". iModIntro. iExists value. iExact "Hclosed".
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
    iMod "Hclosed". iModIntro.
    rewrite (term_interp_resource_prenex_at_arguments_rename runtime formals
      valuation tracked tracked_values external_post _
      Assertions.weaken_bound_renaming source_binders binders Hrenaming).
    iExact "Hclosed".
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "Hpost Hclose Htoken". iDestruct "Hpost" as (value) "Hpost".
    iPoseProof (IHHclosing (binder_cons value binders) with
      "Hpost Hclose Htoken") as "Hclosed".
    iMod "Hclosed". iModIntro.
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
    iMod "Hclosed". iModIntro.
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
    iMod "Hclosed". iModIntro.
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
    (tracked : pexpr_list Γ ts) (tracked_values : tval_list ts)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (outer_mask : coPset) :
  invariant ∈ term_registered_invariants  ->
  ↑(invariant_namespace invariant) ⊆ outer_mask ->
  (forall invariant_values : tval_list (Assertion.invariant_args invariant),
    (global_world_context valuation ∗
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
       term_interp_resource_prenex_at_arguments runtime formals binders valuation
         (IR.pexpr_list_append tracked program_arguments)
         (Translation.tval_list_append tracked_values invariant_values)
         body_post)) ->
  @Atomic RuntimeLang.simp_lang WeaklyAtomic
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) body) ->
  (global_world_context valuation ∗
   term_interp_resource_prenex_at_arguments runtime formals binders valuation
     tracked tracked_values external_pre) ⊢
  runtime_masked_wp outer_mask outer_mask
    (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      (TInvAccess invariant program_arguments body))
    (global_world_context valuation ∗
     term_interp_resource_prenex_at_arguments runtime formals binders valuation
       tracked tracked_values external_post).
Proof.
  intros Hregistered Hnamespace Hbody Hatomic.
  simpl. iIntros "[#Hglobal Hpre]".
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
    formals binders valuation tracked tracked_values outer_mask Hnamespace
    with "Hworld Hpre") as (invariant_values)
    "[Hpre [Hclose Htoken]]".
  iModIntro.
  iPoseProof (Hbody invariant_values with
    "[$Hworlds $Hchunks $Hprocedures $Hpre]") as "Hwp".
  iCombine "Hwp Hclose Htoken" as "Hwp".
  iPoseProof (runtime_masked_wp_frame with "Hwp") as "Hwp".
  iApply (runtime_masked_wp_mono with "Hwp").
  iIntros "[[#Hglobal Hpost] [Hclose Htoken]]". iFrame "Hglobal".
  iApply (term_access_closing_arguments_valid invariant
    program_arguments focus_close body_post external_post Hclosing runtime
    formals binders valuation tracked tracked_values invariant_values
    (outer_mask ∖ ↑(invariant_namespace invariant)) outer_mask
    with "Hpost Hclose Htoken").
Qed.

(** *** Structured invariant access over resource telescopes

    Validity of invariant access, over resource telescopes.  The six
    cases match [access_closure]'s six constructors one for one.  Two
    points are worth noting: the invariant body is a [core_assertion],
    so weakening and renaming it use the core lemmas and cannot disturb
    the store; and the consequence case appeals to
    [resource_prenex_entails_valid], whose [RPEIntro] case is discharged
    by [rpe_intro_holds] rather than assumed. *)
Lemma term_invariant_access_closure_valid {Γ F Δ} invariant
    arguments invariant_body opened closed
    (Hclosure : CertifiedNormalization.RavenHoareRules.access_closure
      invariant Δ arguments invariant_body opened closed)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (values : tval_list (Assertion.invariant_args invariant))
    (inner_mask outer_mask : coPset) :
  interp_expr_list formals binders valuation arguments = Some values ->
  term_interp_core formals binders valuation invariant_body ≡
    world_body_interp valuation invariant values ->
  term_interp_resource_prenex runtime formals binders valuation opened -∗
  (world_body_interp valuation invariant values
    ={inner_mask, outer_mask}=∗ True) -∗
  @RegionExecution.Primitives.Model.core_invariant_own _ _ Σ RG invariant values -∗
  |={inner_mask, outer_mask}=>
    term_interp_resource_prenex runtime formals binders valuation closed.
Proof.
  revert binders.
  induction Hclosure; intros binders Harguments Hinvariant_body.
  - rewrite !term_interp_rstate.
    cbn [Translation.TermSemantics.interp_core].
    iIntros "[Hstack [Hbody Hremainder]] Hclose Htoken".
    iPoseProof (bi.equiv_entails_1_1 _ _ Hinvariant_body with "Hbody")
      as "Hbody".
    iMod ("Hclose" with "Hbody"). iModIntro.
    iFrame "Hstack Hremainder". iExists values. iFrame "Htoken".
    iPureIntro. exact Harguments.
  - rewrite !term_interp_resource_exists.
    iIntros "Hopened Hclose Htoken".
    iDestruct "Hopened" as (value) "Hopened".
    have Harguments' : interp_expr_list formals (binder_cons value binders)
        valuation (Translation.Assertions.weaken_expr_list arguments) =
        Some values.
    { rewrite interp_weaken_expr_list. exact Harguments. }
    have Hinvariant_body' :
        term_interp_core formals (binder_cons value binders) valuation
          (Translation.Resource.weaken_core invariant_body) ≡
        world_body_interp valuation invariant values.
    { unfold term_interp_core.
      rewrite (Translation.TermSemantics.interp_weaken_core semantic_data).
      exact Hinvariant_body. }
    iPoseProof (IHHclosure (binder_cons value binders) Harguments'
      Hinvariant_body' with "Hopened Hclose Htoken") as "Hclosed".
    iMod "Hclosed". iModIntro. iExists value. iExact "Hclosed".
  - rewrite !term_interp_rstate.
    cbn [Translation.TermSemantics.interp_core].
    iIntros "[Hstack [Hbody [Hremainder %Hcondition]]] Hclose Htoken".
    destruct (term_invariant_definition_compatible formals binders
      valuation invariant closing_arguments) as
      [closing_values [Hclosing_arguments Hclosing_body]].
    have Hsame_arguments :
        interp_expr_list formals binders valuation closing_arguments =
        interp_expr_list formals binders valuation opening_arguments.
    { apply Translation.interp_expr_list_equal_assuming with
        (condition := condition); assumption. }
    rewrite Harguments in Hsame_arguments.
    rewrite Hclosing_arguments in Hsame_arguments.
    injection Hsame_arguments as Hvalues.
    subst closing_values.
    iPoseProof (bi.equiv_entails_1_1 _ _ Hclosing_body with "Hbody")
      as "Hbody".
    iMod ("Hclose" with "Hbody"). iModIntro.
    iFrame "Hstack Hremainder". iSplitL "Htoken".
    + iExists values. iFrame "Htoken". iPureIntro. exact Harguments.
    + iPureIntro. exact Hcondition.
  - unfold term_interp_resource_prenex.
    rewrite !(Translation.TermSemantics.interp_prenex_and semantic_data).
    iIntros "[Hopened Hframe] Hclose Htoken".
    iPoseProof (IHHclosure binders Harguments Hinvariant_body with
      "Hopened Hclose Htoken") as "Hclosed".
    iMod "Hclosed". iModIntro. iFrame.
  - iIntros "Hopened Hclose Htoken".
    iPoseProof (Validation.TermSemantics.resource_prenex_entails_valid
      semantic_data (term_predicates valuation) opened' opened H runtime formals
      binders valuation with "Hopened") as "Hopened".
    iPoseProof (IHHclosure binders Harguments Hinvariant_body with
      "Hopened Hclose Htoken") as "Hclosed".
    iMod "Hclosed". iModIntro.
    iApply (Validation.TermSemantics.resource_prenex_entails_valid
      semantic_data (term_predicates valuation) closed closed' H0 runtime formals
      binders valuation with "Hclosed").
  - rewrite !term_interp_rstate.
    iIntros "[Hstack Hbody] Hclose Htoken".
    iPoseProof (interp_store_equal_under body store store' H formals binders
      valuation with "Hbody") as "%Hstores".
    iEval (rewrite Hstores) in "Hstack".
    iApply (IHHclosure binders Harguments Hinvariant_body with
      "[Hstack Hbody] Hclose Htoken").
    iFrame.
  - rewrite !term_interp_rstate.
    iIntros "[Hstack Hbody] Hclose Htoken".
    iPoseProof (interp_store_equal_under body closing_store opening_store H
      formals binders valuation with "Hbody") as "%Hstores".
    have Hargument_interp := interp_program_expr_list_store_ext formals
      binders valuation opening_store closing_store program_arguments Hstores.
    unfold interp_program_expr_list in Hargument_interp.
    rewrite Harguments in Hargument_interp.
    destruct (term_invariant_definition_compatible formals binders
      valuation invariant
      (IR.symbolize_expr_list closing_store program_arguments)) as
      (closing_values & Hclosing_arguments & Hclosing_body).
    rewrite Hclosing_arguments in Hargument_interp.
    injection Hargument_interp as Hvalues. subst closing_values.
    iEval (rewrite Hstores) in "Hstack".
    iApply (IHHclosure binders Hclosing_arguments Hclosing_body with
      "[Hstack Hbody] Hclose Htoken").
    iFrame.
  - pose (source_binders := fun t (variable : bvar Δ t) =>
      binders t (renaming t variable)).
    have Hrenaming : forall t (variable : bvar Δ t),
        binders t (renaming t variable) = source_binders t variable.
    { intros. reflexivity. }
    have Harguments' :
        interp_expr_list formals source_binders valuation arguments = Some values.
    { rewrite <- (Translation.interp_rename_bound_expr_list renaming formals
        source_binders binders valuation Hrenaming).
      exact Harguments. }
    have Hinvariant_body' :
        term_interp_core formals source_binders valuation invariant_body ≡
        world_body_interp valuation invariant values.
    { etrans.
      - symmetry. unfold term_interp_core.
        apply (Translation.TermSemantics.interp_rename_bound_core
          semantic_data (term_predicates valuation) renaming formals
          source_binders binders valuation Hrenaming).
      - exact Hinvariant_body. }
    iIntros "Hopened Hclose Htoken".
    unfold term_interp_resource_prenex at 1.
    rewrite (Translation.TermSemantics.interp_rename_resource_prenex
      semantic_data (term_predicates valuation) opened _ renaming formals
      source_binders binders valuation (term_semantic_runtime runtime)
      Hrenaming).
    iPoseProof (IHHclosure source_binders Harguments' Hinvariant_body'
      with "Hopened Hclose Htoken") as "Hclosed".
    iMod "Hclosed". iModIntro.
    unfold term_interp_resource_prenex.
    rewrite (Translation.TermSemantics.interp_rename_resource_prenex
      semantic_data (term_predicates valuation) closed _ renaming formals
      source_binders binders valuation (term_semantic_runtime runtime)
      Hrenaming).
    iExact "Hclosed".
Qed.

(** Matched invariant closure while preserving an arbitrary caller argument
    vector. *)
Lemma term_invariant_access_closure_arguments_valid {Γ F Δ ts}
    invariant arguments invariant_body opened closed
    (Hclosure : CertifiedNormalization.RavenHoareRules.access_closure
      invariant Δ arguments invariant_body opened closed)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (values : tval_list (Assertion.invariant_args invariant))
    (tracked : pexpr_list Γ ts) (tracked_values : tval_list ts)
    (inner_mask outer_mask : coPset) :
  interp_expr_list formals binders valuation arguments = Some values ->
  term_interp_core formals binders valuation invariant_body ≡
    world_body_interp valuation invariant values ->
  term_interp_resource_prenex_at_arguments runtime formals binders valuation
      tracked tracked_values opened -∗
  (world_body_interp valuation invariant values
    ={inner_mask, outer_mask}=∗ True) -∗
  @RegionExecution.Primitives.Model.core_invariant_own _ _ Σ RG invariant values -∗
  |={inner_mask, outer_mask}=>
    term_interp_resource_prenex_at_arguments runtime formals binders valuation
      tracked tracked_values closed.
Proof.
  revert binders.
  induction Hclosure; intros binders Harguments Hinvariant_body.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "[Hopened %Htracked] Hclose Htoken".
    iMod (term_invariant_access_closure_valid invariant arguments
      invariant_body _ _ (CertifiedNormalization.RavenHoareRules.AccessBase
        invariant Δ arguments invariant_body store remainder)
      runtime formals binders valuation values inner_mask outer_mask Harguments
      Hinvariant_body with "Hopened Hclose Htoken") as "Hclosed".
    iModIntro. iFrame. iPureIntro. exact Htracked.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "Hopened Hclose Htoken". iDestruct "Hopened" as (value) "Hopened".
    have Harguments' : interp_expr_list formals (binder_cons value binders)
        valuation (Translation.Assertions.weaken_expr_list arguments) = Some values.
    { rewrite interp_weaken_expr_list. exact Harguments. }
    have Hinvariant_body' :
        term_interp_core formals (binder_cons value binders) valuation
          (Translation.Resource.weaken_core invariant_body) ≡
        world_body_interp valuation invariant values.
    { unfold term_interp_core.
      rewrite (Translation.TermSemantics.interp_weaken_core semantic_data).
      exact Hinvariant_body. }
    iMod (IHHclosure (binder_cons value binders) Harguments'
      Hinvariant_body' with "Hopened Hclose Htoken") as "Hclosed".
    iModIntro. iExists value. iExact "Hclosed".
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "[Hopened %Htracked] Hclose Htoken".
    iMod (term_invariant_access_closure_valid invariant
      opening_arguments opening_body _ _
      (CertifiedNormalization.RavenHoareRules.AccessEquality invariant Δ
        opening_arguments closing_arguments opening_body store remainder
        condition H)
      runtime formals binders valuation values inner_mask outer_mask Harguments Hinvariant_body
      with "Hopened Hclose Htoken") as "Hclosed".
    iModIntro. iFrame. iPureIntro. exact Htracked.
  - iEval (rewrite (term_interp_resource_prenex_at_arguments_and runtime
      formals binders valuation tracked tracked_values opened frame)).
    iIntros "[Hopened Hframe] Hclose Htoken".
    iMod (IHHclosure binders Harguments Hinvariant_body with
      "Hopened Hclose Htoken") as "Hclosed".
    iModIntro.
    iEval (rewrite (term_interp_resource_prenex_at_arguments_and runtime
      formals binders valuation tracked tracked_values closed frame)). iFrame.
  - iIntros "Hopened Hclose Htoken".
    iPoseProof (term_interp_resource_prenex_at_arguments_entails runtime
      formals binders valuation tracked tracked_values opened' opened H
      with "Hopened") as "Hopened".
    iMod (IHHclosure binders Harguments Hinvariant_body with
      "Hopened Hclose Htoken") as "Hclosed".
    iModIntro. iApply (term_interp_resource_prenex_at_arguments_entails runtime
      formals binders valuation tracked tracked_values closed closed' H0
      with "Hclosed").
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "[[Hstack Hbody] %Htracked] Hclose Htoken".
    iPoseProof (interp_store_equal_under body store store' H formals binders
      valuation with "Hbody") as "%Hstores".
    iEval (rewrite Hstores) in "Hstack".
    have Htracked' := interp_program_expr_list_store_ext formals binders valuation
      store' store tracked Hstores.
    unfold interp_program_expr_list in Htracked'. rewrite Htracked in Htracked'.
    iApply (IHHclosure binders Harguments Hinvariant_body with
      "[Hstack Hbody] Hclose Htoken").
    cbn [term_interp_resource_prenex_at_arguments]. iFrame.
    iPureIntro. symmetry. exact Htracked'.
  - cbn [term_interp_resource_prenex_at_arguments].
    iIntros "[[Hstack Hbody] %Htracked] Hclose Htoken".
    iPoseProof (interp_store_equal_under body closing_store opening_store H
      formals binders valuation with "Hbody") as "%Hstores".
    have Hargument_interp := interp_program_expr_list_store_ext formals
      binders valuation opening_store closing_store program_arguments Hstores.
    unfold interp_program_expr_list in Hargument_interp.
    rewrite Harguments in Hargument_interp.
    destruct (term_invariant_definition_compatible formals binders
      valuation invariant (IR.symbolize_expr_list closing_store program_arguments))
      as (closing_values & Hclosing_arguments & Hclosing_body).
    rewrite Hclosing_arguments in Hargument_interp.
    injection Hargument_interp as Hvalues. subst closing_values.
    have Htracked' := interp_program_expr_list_store_ext formals binders valuation
      opening_store closing_store tracked Hstores.
    unfold interp_program_expr_list in Htracked'. rewrite Htracked in Htracked'.
    iEval (rewrite Hstores) in "Hstack".
    iApply (IHHclosure binders Hclosing_arguments Hclosing_body with
      "[Hstack Hbody] Hclose Htoken").
    cbn [term_interp_resource_prenex_at_arguments]. iFrame.
    iPureIntro. symmetry. exact Htracked'.
  - pose (source_binders := fun t (variable : bvar Δ t) =>
      binders t (renaming t variable)).
    have Hrenaming : forall t (variable : bvar Δ t),
        binders t (renaming t variable) = source_binders t variable.
    { intros. reflexivity. }
    have Harguments' :
        interp_expr_list formals source_binders valuation arguments = Some values.
    { rewrite <- (Translation.interp_rename_bound_expr_list renaming formals
        source_binders binders valuation Hrenaming). exact Harguments. }
    have Hinvariant_body' :
        term_interp_core formals source_binders valuation invariant_body ≡
        world_body_interp valuation invariant values.
    { etrans.
      - symmetry. unfold term_interp_core.
        apply (Translation.TermSemantics.interp_rename_bound_core semantic_data
          (term_predicates valuation) renaming formals source_binders binders valuation
          Hrenaming).
      - exact Hinvariant_body. }
    iIntros "Hopened Hclose Htoken".
    iEval (rewrite (term_interp_resource_prenex_at_arguments_rename runtime
      formals valuation tracked tracked_values opened _ renaming source_binders
      binders Hrenaming)) in "Hopened".
    iMod (IHHclosure source_binders Harguments' Hinvariant_body' with
      "Hopened Hclose Htoken") as "Hclosed".
    iModIntro.
    iEval (rewrite (term_interp_resource_prenex_at_arguments_rename runtime
      formals valuation tracked tracked_values closed _ renaming source_binders
      binders Hrenaming)). iExact "Hclosed".
Qed.

Lemma term_structured_inv_access_runtime_valid {Γ F Δ} invariant arguments
    (input_store : symbolic_store Γ F Δ)
    (frame : Translation.Resource.core_assertion F Δ)
    (opened_post closed_post : Translation.Resource.resource_prenex Γ F Δ)
    (body : stmt Γ)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (outer_mask inner_mask : coPset) :
  invariant ∈ term_registered_invariants  ->
  ↑(invariant_namespace invariant) ⊆ outer_mask ->
  inner_mask = outer_mask ∖ ↑(invariant_namespace invariant) ->
  (global_world_context valuation ∗
   term_interp_resource_prenex runtime formals binders valuation
     (Translation.Resource.RState input_store
       (Translation.Resource.CAnd
         (ResourceInstances.instantiated_invariant invariant
           (IR.symbolize_expr_list input_store arguments)) frame)) ⊢
   runtime_masked_wp inner_mask inner_mask
     (@RuntimeErasure.runtime_stmt _ _ Γ
       (RegionExecution.Primitives.Model.runtime_names Γ runtime)
       (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) body)
     (global_world_context valuation ∗
     term_interp_resource_prenex runtime formals binders valuation
       opened_post)) ->
  CertifiedNormalization.RavenHoareRules.access_closure invariant Δ
    (IR.symbolize_expr_list input_store arguments)
    (ResourceInstances.instantiated_invariant invariant
      (IR.symbolize_expr_list input_store arguments))
    opened_post closed_post ->
  @Atomic RuntimeLang.simp_lang WeaklyAtomic
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
        body) ->
  (global_world_context valuation ∗
   term_interp_resource_prenex runtime formals binders valuation
     (Translation.Resource.RState input_store
       (Translation.Resource.CAnd
         (Translation.Resource.CInvariant invariant
           (IR.symbolize_expr_list input_store arguments)) frame))) ⊢
  runtime_masked_wp outer_mask outer_mask
    (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      (TInvAccess invariant arguments body))
    (global_world_context valuation ∗
     term_interp_resource_prenex runtime formals binders valuation closed_post).
Proof.
  intros Hregistered Hnamespace -> Hbody Hclosure Hatomic.
  destruct (term_invariant_definition_compatible formals binders
    valuation invariant (IR.symbolize_expr_list input_store arguments))
    as (values & Harguments & Hinvariant_body).
  rewrite term_interp_rstate.
  cbn [Translation.TermSemantics.interp_core].
  simpl.
  iIntros "[#Hglobal [Hstack [Htoken Hframe]]]".
  iEval (unfold global_world_context) in "Hglobal".
  iDestruct "Hglobal" as "[#Hworlds [#Hchunks #Hprocedures]]".
  iDestruct "Htoken" as (actual_values) "[%Hactual #Htoken]".
  have Hvalues : actual_values = values by congruence.
  subst actual_values.
  iPoseProof "Htoken" as "#Htoken_saved".
  iPoseProof (term_world_context_lookup valuation invariant Hregistered
    with "Hworlds") as "#Hworld".
  iApply (runtime_masked_wp_atomic_mask_change outer_mask
    (outer_mask ∖ ↑(invariant_namespace invariant))
    (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      body) _ Hatomic).
  iMod (term_world_open valuation invariant values outer_mask Hnamespace
    with "Hworld Htoken") as "[Hinv_body Hclose]".
  iModIntro.
  iEval (rewrite -Hinvariant_body) in "Hinv_body".
  iPoseProof (Hbody with
    "[$Hworlds $Hchunks $Hprocedures $Hstack $Hinv_body $Hframe]") as "Hwp".
  iCombine "Hwp Hclose Htoken_saved" as "Hwp".
  iPoseProof (runtime_masked_wp_frame with "Hwp") as "Hwp".
  iApply (runtime_masked_wp_mono with "Hwp").
  iIntros "[[#Hglobal Hpost] [Hclose Htoken_saved]]".
  iFrame "Hglobal".
  iApply (term_invariant_access_closure_valid invariant
    (IR.symbolize_expr_list input_store arguments)
    (ResourceInstances.instantiated_invariant invariant
      (IR.symbolize_expr_list input_store arguments))
    opened_post closed_post Hclosure runtime formals binders valuation values
    (outer_mask ∖ ↑(invariant_namespace invariant)) outer_mask
    Harguments Hinvariant_body with "Hpost Hclose Htoken_saved").
Qed.

(** The canonical matched-access theorem with an arbitrary stable caller
    vector threaded through the body.  The invariant's own access arguments
    remain governed by its world token; [tracked] is independent bookkeeping
    preserved by the strengthened body induction and closure theorem. *)
Lemma term_structured_inv_access_runtime_arguments_valid {Γ F Δ ts} invariant arguments
    (input_store : symbolic_store Γ F Δ)
    (frame : Translation.Resource.core_assertion F Δ)
    (opened_post closed_post : Translation.Resource.resource_prenex Γ F Δ)
    (body : stmt Γ)
    (runtime : RegionExecution.Primitives.Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (tracked : pexpr_list Γ ts) (tracked_values : tval_list ts)
    (outer_mask inner_mask : coPset) :
  invariant ∈ term_registered_invariants  ->
  ↑(invariant_namespace invariant) ⊆ outer_mask ->
  inner_mask = outer_mask ∖ ↑(invariant_namespace invariant) ->
  (global_world_context valuation ∗
   term_interp_resource_prenex_at_arguments runtime formals binders valuation
     tracked tracked_values
     (Translation.Resource.RState input_store
       (Translation.Resource.CAnd
         (ResourceInstances.instantiated_invariant invariant
           (IR.symbolize_expr_list input_store arguments)) frame)) ⊢
   runtime_masked_wp inner_mask inner_mask
     (@RuntimeErasure.runtime_stmt _ _ Γ
       (RegionExecution.Primitives.Model.runtime_names Γ runtime)
       (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) body)
     (global_world_context valuation ∗
      term_interp_resource_prenex_at_arguments runtime formals binders valuation
        tracked tracked_values opened_post)) ->
  CertifiedNormalization.RavenHoareRules.access_closure invariant Δ
    (IR.symbolize_expr_list input_store arguments)
    (ResourceInstances.instantiated_invariant invariant
      (IR.symbolize_expr_list input_store arguments))
    opened_post closed_post ->
  @Atomic RuntimeLang.simp_lang WeaklyAtomic
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
        body) ->
  (global_world_context valuation ∗
   term_interp_resource_prenex_at_arguments runtime formals binders valuation
     tracked tracked_values
     (Translation.Resource.RState input_store
       (Translation.Resource.CAnd
         (Translation.Resource.CInvariant invariant
           (IR.symbolize_expr_list input_store arguments)) frame))) ⊢
  runtime_masked_wp outer_mask outer_mask
    (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      (TInvAccess invariant arguments body))
    (global_world_context valuation ∗
     term_interp_resource_prenex_at_arguments runtime formals binders valuation
       tracked tracked_values closed_post).
Proof.
  intros Hregistered Hnamespace -> Hbody Hclosure Hatomic.
  destruct (term_invariant_definition_compatible formals binders
    valuation invariant (IR.symbolize_expr_list input_store arguments))
    as (values & Harguments & Hinvariant_body).
  cbn [term_interp_resource_prenex_at_arguments term_interp_rstate
    Translation.TermSemantics.interp_core].
  iIntros "[#Hglobal [[Hstack [Htoken Hframe]] %Htracked]]".
  iEval (unfold global_world_context) in "Hglobal".
  iDestruct "Hglobal" as "[#Hworlds [#Hchunks #Hprocedures]]".
  iDestruct "Htoken" as (actual_values) "[%Hactual #Htoken]".
  have Hvalues : actual_values = values by congruence.
  subst actual_values.
  iPoseProof "Htoken" as "#Htoken_saved".
  iPoseProof (term_world_context_lookup valuation invariant Hregistered
    with "Hworlds") as "#Hworld".
  iApply (runtime_masked_wp_atomic_mask_change outer_mask
    (outer_mask ∖ ↑(invariant_namespace invariant))
    (@RuntimeErasure.runtime_stmt _ _ Γ
      (RegionExecution.Primitives.Model.runtime_names Γ runtime)
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
      body) _ Hatomic).
  iMod (term_world_open valuation invariant values outer_mask Hnamespace
    with "Hworld Htoken") as "[Hinv_body Hclose]".
  iModIntro.
  iEval (rewrite -Hinvariant_body) in "Hinv_body".
  iPoseProof (Hbody with
    "[$Hworlds $Hchunks $Hprocedures $Hstack $Hinv_body $Hframe]") as "Hwp".
  { iPureIntro. exact Htracked. }
  iCombine "Hwp Hclose Htoken_saved" as "Hwp".
  iPoseProof (runtime_masked_wp_frame with "Hwp") as "Hwp".
  iApply (runtime_masked_wp_mono with "Hwp").
  iIntros "[[#Hglobal Hpost] [Hclose Htoken_saved]]".
  iFrame "Hglobal".
  iApply (term_invariant_access_closure_arguments_valid invariant
    (IR.symbolize_expr_list input_store arguments)
    (ResourceInstances.instantiated_invariant invariant
      (IR.symbolize_expr_list input_store arguments))
    opened_post closed_post Hclosure runtime formals binders valuation values
    tracked tracked_values
    (outer_mask ∖ ↑(invariant_namespace invariant)) outer_mask
    Harguments Hinvariant_body with "Hpost Hclose Htoken_saved").
Qed.


(** Matched invariant access, lifted to structured runtime validity over
    resource telescopes.  Composing this with
    [term_structured_runtime_atomic_valid] gives the terminal
    access-around-a-trusted-atomic-block path end to end. *)
Lemma term_structured_runtime_inv_access_valid
    {Γ F Δ entry invariant arguments body opened inner}
    (Hregistered : invariant ∈ term_registered_invariants )
    (Hopen : GenericRegions.Atomicity.open_invariant invariant entry =
      inr opened)
    (body_certificate : Structured.structured_certificate
      Γ opened body inner)
    (Hpreserved : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open opened)
    (input_store : symbolic_store Γ F Δ)
    (frame : Translation.Resource.core_assertion F Δ)
    (opened_post closed_post : Translation.Resource.resource_prenex Γ F Δ)
    (Hclosure :
      CertifiedNormalization.RavenHoareRules.access_closure invariant Δ
        (IR.symbolize_expr_list input_store arguments)
        (ResourceInstances.instantiated_invariant invariant
          (IR.symbolize_expr_list input_store arguments))
        opened_post closed_post) :
  term_structured_runtime_valid body_certificate
    (Translation.Resource.RState input_store
      (Translation.Resource.CAnd
        (ResourceInstances.instantiated_invariant invariant
          (IR.symbolize_expr_list input_store arguments)) frame))
    opened_post ->
  (forall (runtime : RegionExecution.Primitives.Model.stack_context Γ),
    @Atomic RuntimeLang.simp_lang WeaklyAtomic
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
        body)) ->
  term_structured_runtime_valid
    (Structured.StructuredInvAccess Γ entry invariant arguments body
      opened inner Hopen body_certificate Hpreserved)
    (Translation.Resource.RState input_store
      (Translation.Resource.CAnd
        (Translation.Resource.CInvariant invariant
          (IR.symbolize_expr_list input_store arguments)) frame))
    closed_post.
Proof.
  intros Hbody Hatomic runtime formals binders valuation ambient Henvelope.
  have Hopen_facts := Hopen.
  apply GenericRegions.Atomicity.open_invariant_success in Hopen_facts as
    (Hfresh & Hmember & _ & Hopened).
  have Hfootprint_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint
        (Structured.StructuredInvAccess Γ entry invariant arguments body
          opened inner Hopen body_certificate Hpreserved)) ⊆ ambient.
  { etrans; last exact Henvelope. apply RegionExecution.Primitives.Model.runtime_mask_mono.
    simpl. intros candidate Hcandidate. apply elem_of_union_l. exact Hcandidate. }
  have Hnamespace := term_structured_invariant_namespace_active_from_footprint
    (Structured.StructuredInvAccess Γ entry invariant arguments body
      opened inner Hopen body_certificate Hpreserved)
    ambient invariant Hmember Hfresh Hfootprint_envelope.
  have Hinner_mask : RegionExecution.Primitives.Model.active_runtime_mask ambient inner =
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry ∖
        ↑(invariant_namespace invariant).
  { exact (RegionExecution.Primitives.active_runtime_mask_access
      ambient entry invariant opened inner Hopened Hpreserved). }
  have Hexit_mask : RegionExecution.Primitives.Model.active_runtime_mask ambient
      (GenericRegions.Atomicity.fold_invariant invariant inner) =
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
  { apply RegionExecution.Primitives.Model.active_runtime_mask_same_open.
    exact (term_structured_certificate_preserves_open
      (Structured.StructuredInvAccess Γ entry invariant arguments body
        opened inner Hopen body_certificate Hpreserved)). }
  unfold term_structured_runtime_wp.
  rewrite translated_runtime_wp_as_masked Hexit_mask. simpl.
  eapply (term_structured_inv_access_runtime_valid invariant
    arguments input_store frame opened_post closed_post body runtime
    formals binders valuation
    (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
    (RegionExecution.Primitives.Model.active_runtime_mask ambient inner)).
  - exact Hregistered.
  - exact Hnamespace.
  - exact Hinner_mask.
  - have Hbody_wp := Hbody runtime formals binders valuation ambient.
    have Hbody_envelope : RegionExecution.Primitives.Model.runtime_mask
        (Structured.structured_certificate_footprint body_certificate ∪
          term_registered_invariants) ⊆ ambient.
    { etrans; last exact Henvelope. apply RegionExecution.Primitives.Model.runtime_mask_mono.
      intros candidate Hcandidate. apply elem_of_union in Hcandidate as [Hcandidate | Hregistered'].
      - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
      - apply elem_of_union_r. exact Hregistered'. }
    specialize (Hbody_wp Hbody_envelope).
    unfold term_structured_runtime_wp in Hbody_wp.
    rewrite translated_runtime_wp_as_masked in Hbody_wp.
    have Hopened_inner : RegionExecution.Primitives.Model.active_runtime_mask ambient opened =
        RegionExecution.Primitives.Model.active_runtime_mask ambient inner.
    { apply RegionExecution.Primitives.Model.active_runtime_mask_same_open. symmetry. exact Hpreserved. }
    rewrite Hopened_inner in Hbody_wp. exact Hbody_wp.
  - exact Hclosure.
  - apply Hatomic.
Qed.

Lemma term_structured_runtime_inv_access_arguments_valid
    {Γ F Δ entry invariant arguments body opened inner ts}
    (Hregistered : invariant ∈ term_registered_invariants )
    (Hopen : GenericRegions.Atomicity.open_invariant invariant entry =
      inr opened)
    (body_certificate : Structured.structured_certificate
      Γ opened body inner)
    (Hpreserved : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open opened)
    (input_store : symbolic_store Γ F Δ)
    (frame : Translation.Resource.core_assertion F Δ)
    (opened_post closed_post : Translation.Resource.resource_prenex Γ F Δ)
    (Hclosure :
      CertifiedNormalization.RavenHoareRules.access_closure invariant Δ
        (IR.symbolize_expr_list input_store arguments)
        (ResourceInstances.instantiated_invariant invariant
          (IR.symbolize_expr_list input_store arguments))
        opened_post closed_post)
    (tracked : pexpr_list Γ ts) :
  term_structured_runtime_arguments_valid body_certificate
    tracked
    (Translation.Resource.RState input_store
      (Translation.Resource.CAnd
        (ResourceInstances.instantiated_invariant invariant
          (IR.symbolize_expr_list input_store arguments)) frame))
    opened_post ->
  (forall (runtime : RegionExecution.Primitives.Model.stack_context Γ),
    @Atomic RuntimeLang.simp_lang WeaklyAtomic
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
        body)) ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredInvAccess Γ entry invariant arguments body
      opened inner Hopen body_certificate Hpreserved)
    tracked
    (Translation.Resource.RState input_store
      (Translation.Resource.CAnd
        (Translation.Resource.CInvariant invariant
          (IR.symbolize_expr_list input_store arguments)) frame))
    closed_post.
Proof.
  intros Hbody Hatomic Hstable tracked_values runtime formals binders valuation
    ambient Henvelope.
  cbn [Hoare.ResourceHoare.statement_writes] in Hstable.
  have Hopen_facts := Hopen.
  apply GenericRegions.Atomicity.open_invariant_success in Hopen_facts as
    (Hfresh & Hmember & _ & Hopened).
  have Hfootprint_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint
        (Structured.StructuredInvAccess Γ entry invariant arguments body
          opened inner Hopen body_certificate Hpreserved)) ⊆ ambient.
  { etrans; last exact Henvelope. apply RegionExecution.Primitives.Model.runtime_mask_mono.
    simpl. intros candidate Hcandidate. apply elem_of_union_l. exact Hcandidate. }
  have Hnamespace := term_structured_invariant_namespace_active_from_footprint
    (Structured.StructuredInvAccess Γ entry invariant arguments body
      opened inner Hopen body_certificate Hpreserved)
    ambient invariant Hmember Hfresh Hfootprint_envelope.
  have Hinner_mask : RegionExecution.Primitives.Model.active_runtime_mask ambient inner =
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry ∖
        ↑(invariant_namespace invariant).
  { exact (RegionExecution.Primitives.active_runtime_mask_access
      ambient entry invariant opened inner Hopened Hpreserved). }
  have Hexit_mask : RegionExecution.Primitives.Model.active_runtime_mask ambient
      (GenericRegions.Atomicity.fold_invariant invariant inner) =
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
  { apply RegionExecution.Primitives.Model.active_runtime_mask_same_open.
    exact (term_structured_certificate_preserves_open
      (Structured.StructuredInvAccess Γ entry invariant arguments body
        opened inner Hopen body_certificate Hpreserved)). }
  unfold term_structured_runtime_wp.
  rewrite translated_runtime_wp_as_masked Hexit_mask. simpl.
  eapply (term_structured_inv_access_runtime_arguments_valid
    invariant arguments input_store frame opened_post closed_post body runtime
    formals binders valuation tracked tracked_values
    (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)
    (RegionExecution.Primitives.Model.active_runtime_mask ambient inner)).
  - exact Hregistered.
  - exact Hnamespace.
  - exact Hinner_mask.
  - have Hbody_wp := Hbody Hstable tracked_values runtime formals binders valuation ambient.
    have Hbody_envelope : RegionExecution.Primitives.Model.runtime_mask
        (Structured.structured_certificate_footprint body_certificate ∪
          term_registered_invariants) ⊆ ambient.
    { etrans; last exact Henvelope.
      apply RegionExecution.Primitives.Model.runtime_mask_mono.
      intros candidate Hcandidate. apply elem_of_union in Hcandidate as [Hcandidate | Hregistered'].
      - apply elem_of_union_l. simpl. repeat rewrite elem_of_union. tauto.
      - apply elem_of_union_r. exact Hregistered'. }
    specialize (Hbody_wp Hbody_envelope).
    unfold term_structured_runtime_wp in Hbody_wp.
    rewrite translated_runtime_wp_as_masked in Hbody_wp.
    have Hopened_inner : RegionExecution.Primitives.Model.active_runtime_mask ambient opened =
        RegionExecution.Primitives.Model.active_runtime_mask ambient inner.
    { apply RegionExecution.Primitives.Model.active_runtime_mask_same_open.
      symmetry. exact Hpreserved. }
    rewrite Hopened_inner in Hbody_wp. exact Hbody_wp.
  - exact Hclosure.
  - apply Hatomic.
Qed.

(** Structured form of the independent access seam.  Its body premise is
    already the strengthened induction hypothesis at the concatenated
    vector; this is the exact interface used by the top-level induction. *)
Lemma term_structured_runtime_independent_inv_access_arguments_valid
    {Γ F Δ entry invariant program_arguments body opened inner ts}
    (Hregistered : invariant ∈ term_registered_invariants )
    (Hopen : GenericRegions.Atomicity.open_invariant invariant entry =
      inr opened)
    (body_certificate : Structured.structured_certificate
      Γ opened body inner)
    (Hpreserved : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open opened)
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
    (tracked : pexpr_list Γ ts) :
  term_structured_runtime_arguments_valid body_certificate
    (IR.pexpr_list_append tracked program_arguments) body_pre body_post ->
  (forall (runtime : RegionExecution.Primitives.Model.stack_context Γ),
    @Atomic RuntimeLang.simp_lang WeaklyAtomic
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) body)) ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredInvAccess Γ entry invariant program_arguments
      body opened inner Hopen body_certificate Hpreserved)
    tracked external_pre external_post.
Proof.
  intros Hbody Hatomic Htracked_stable tracked_values runtime formals binders
    valuation ambient Henvelope.
  cbn [Hoare.ResourceHoare.statement_writes] in Htracked_stable.
  have Hcombined_stable :
      Hoare.ResourceHoare.pexpr_list_dependencies
          (IR.pexpr_list_append tracked program_arguments) ##
        Hoare.ResourceHoare.statement_writes body.
  { rewrite Hoare.ResourceHoare.pexpr_list_dependencies_append.
    apply disjoint_union_l. split; assumption. }
  have Hopen_facts := Hopen.
  apply GenericRegions.Atomicity.open_invariant_success in Hopen_facts as
    (Hfresh & Hmember & _ & Hopened).
  have Hfootprint_envelope : RegionExecution.Primitives.Model.runtime_mask
      (Structured.structured_certificate_footprint
        (Structured.StructuredInvAccess Γ entry invariant program_arguments
          body opened inner Hopen body_certificate Hpreserved)) ⊆ ambient.
  { etrans; last exact Henvelope. apply RegionExecution.Primitives.Model.runtime_mask_mono.
    simpl. intros candidate Hcandidate. apply elem_of_union_l. exact Hcandidate. }
  have Hnamespace := term_structured_invariant_namespace_active_from_footprint
    (Structured.StructuredInvAccess Γ entry invariant program_arguments
      body opened inner Hopen body_certificate Hpreserved)
    ambient invariant Hmember Hfresh Hfootprint_envelope.
  have Hinner_mask : RegionExecution.Primitives.Model.active_runtime_mask
      ambient inner =
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry ∖
        ↑(invariant_namespace invariant).
  { exact (RegionExecution.Primitives.active_runtime_mask_access ambient entry
      invariant opened inner Hopened Hpreserved). }
  have Hexit_mask : RegionExecution.Primitives.Model.active_runtime_mask ambient
      (GenericRegions.Atomicity.fold_invariant invariant inner) =
      RegionExecution.Primitives.Model.active_runtime_mask ambient entry.
  { apply RegionExecution.Primitives.Model.active_runtime_mask_same_open.
    exact (term_structured_certificate_preserves_open
      (Structured.StructuredInvAccess Γ entry invariant program_arguments
        body opened inner Hopen body_certificate Hpreserved)). }
  unfold term_structured_runtime_wp.
  rewrite translated_runtime_wp_as_masked Hexit_mask. simpl.
  eapply (term_independent_inv_access_runtime_arguments_valid
    invariant program_arguments focus_open focus_close external_pre body_pre
    body_post external_post Hopening Hclosing body tracked tracked_values
    runtime formals binders valuation
    (RegionExecution.Primitives.Model.active_runtime_mask ambient entry)).
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
    have Hbody_wp := Hbody Hcombined_stable
      (Translation.tval_list_append tracked_values invariant_values)
      runtime formals binders valuation ambient Hbody_envelope.
    unfold term_structured_runtime_wp in Hbody_wp.
    rewrite translated_runtime_wp_as_masked in Hbody_wp.
    have Hopened_inner : RegionExecution.Primitives.Model.active_runtime_mask
        ambient opened =
        RegionExecution.Primitives.Model.active_runtime_mask ambient inner.
    { apply RegionExecution.Primitives.Model.active_runtime_mask_same_open.
      symmetry. exact Hpreserved. }
    rewrite Hopened_inner Hinner_mask in Hbody_wp. exact Hbody_wp.
  - apply Hatomic.
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
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask outer)
        (GenericRegions.Atomicity.analysis_open outer)
        (GenericRegions.Atomicity.analysis_step_taken outer) true)
      body inner)
    (open_equal : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open outer)
    (pre post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_valid body_certificate pre post ->
  term_structured_runtime_valid
    (Structured.StructuredAtomic Γ state body outer inner step
      body_certificate open_equal) pre post.
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
    runtime ambient _ step open_equal).
  iExact "Hwp".
Qed.

Lemma term_structured_runtime_arguments_atomic_valid
    {Γ F Δ state body outer inner ts}
    (step : GenericRegions.Atomicity.take_step
      GenericRegions.Atomicity.AtomicStep state = inr outer)
    (body_certificate : Structured.structured_certificate Γ
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask outer)
        (GenericRegions.Atomicity.analysis_open outer)
        (GenericRegions.Atomicity.analysis_step_taken outer) true)
      body inner)
    (open_equal : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open outer)
    (tracked : pexpr_list Γ ts)
    (pre post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid body_certificate
    tracked pre post ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredAtomic Γ state body outer inner step
      body_certificate open_equal) tracked pre post.
Proof.
  intros Hbody Hdisjoint values runtime formals binders valuation ambient
    Henvelope.
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
  iPoseProof (Hbody Hdisjoint values runtime formals binders valuation ambient
    Hbody_envelope with "Hpre") as "Hwp".
  unfold term_structured_runtime_wp.
  iApply (term_trusted_atomic_runtime_refinement body_certificate
    runtime ambient _ step open_equal).
  iExact "Hwp".
Qed.

(** *** The terminal slice, end to end

    A matched invariant access whose body is a trusted atomic block,
    carried from the invariant access closure all the way to
    structured runtime validity.  This is the composition the baseline
    monotonic counter needs, and it is stated and proved entirely over
    [resource_prenex]: the pre- and post-conditions are telescopes, the
    frame is a [core_assertion] so it cannot hide a second stack, and the
    opened body is the total instantiated invariant rather than a
    relationally-specified one. *)
Lemma term_structured_runtime_terminal_access_valid
    {Γ F Δ entry invariant arguments atomic_body
     opened atomic_outer atomic_inner}
    (Hregistered : invariant ∈ term_registered_invariants )
    (Hopen : GenericRegions.Atomicity.open_invariant invariant entry =
      inr opened)
    (step : GenericRegions.Atomicity.take_step
      GenericRegions.Atomicity.AtomicStep opened = inr atomic_outer)
    (atomic_certificate : Structured.structured_certificate Γ
      (GenericRegions.Atomicity.AnalysisState
        (GenericRegions.Atomicity.analysis_mask atomic_outer)
        (GenericRegions.Atomicity.analysis_open atomic_outer)
        (GenericRegions.Atomicity.analysis_step_taken atomic_outer) true)
      atomic_body atomic_inner)
    (open_equal : GenericRegions.Atomicity.analysis_open atomic_inner =
      GenericRegions.Atomicity.analysis_open atomic_outer)
    (Hpreserved : GenericRegions.Atomicity.analysis_open
        (GenericRegions.Atomicity.AnalysisState
          (GenericRegions.Atomicity.analysis_mask atomic_inner)
          (GenericRegions.Atomicity.analysis_open atomic_inner)
          (GenericRegions.Atomicity.analysis_step_taken atomic_outer ||
            GenericRegions.Atomicity.analysis_step_taken atomic_inner)
          (GenericRegions.Atomicity.analysis_in_atomic atomic_outer)) =
      GenericRegions.Atomicity.analysis_open opened)
    (input_store : symbolic_store Γ F Δ)
    (frame : Translation.Resource.core_assertion F Δ)
    (opened_post closed_post : Translation.Resource.resource_prenex Γ F Δ)
    (Hclosure :
      CertifiedNormalization.RavenHoareRules.access_closure invariant Δ
        (IR.symbolize_expr_list input_store arguments)
        (ResourceInstances.instantiated_invariant invariant
          (IR.symbolize_expr_list input_store arguments))
        opened_post closed_post) :
  term_structured_runtime_valid atomic_certificate
    (Translation.Resource.RState input_store
      (Translation.Resource.CAnd
        (ResourceInstances.instantiated_invariant invariant
          (IR.symbolize_expr_list input_store arguments)) frame))
    opened_post ->
  (forall (runtime : RegionExecution.Primitives.Model.stack_context Γ),
    @Atomic RuntimeLang.simp_lang WeaklyAtomic
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)
        (TAtomic atomic_body))) ->
  term_structured_runtime_valid
    (Structured.StructuredInvAccess Γ entry invariant arguments
      (TAtomic atomic_body) opened _ Hopen
      (Structured.StructuredAtomic Γ opened atomic_body
        atomic_outer atomic_inner step atomic_certificate open_equal)
      Hpreserved)
    (Translation.Resource.RState input_store
      (Translation.Resource.CAnd
        (Translation.Resource.CInvariant invariant
          (IR.symbolize_expr_list input_store arguments)) frame))
    closed_post.
Proof.
  intros Hbody Hatomic.
  apply (term_structured_runtime_inv_access_valid
    Hregistered Hopen _ Hpreserved input_store frame opened_post closed_post
    Hclosure).
  - apply term_structured_runtime_atomic_valid. exact Hbody.
  - exact Hatomic.
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
    (arguments : pexpr_list Γ ts)
    (pre middle_prenex post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid first_certificate
    arguments pre middle_prenex ->
  term_structured_runtime_arguments_valid second_certificate
    arguments middle_prenex post ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredSequence Γ entry first middle second exit
      first_certificate second_certificate) arguments pre post.
Proof.
  intros Hfirst Hsecond Hdisjoint values runtime formals binders valuation ambient
    Henvelope.
  cbn [Hoare.ResourceHoare.statement_writes] in Hdisjoint.
  have Hfirst_disjoint : Hoare.ResourceHoare.pexpr_list_dependencies arguments
      ## Hoare.ResourceHoare.statement_writes first.
  { intros slot Harg Hwrite. apply (Hdisjoint slot Harg).
    apply elem_of_union_l. exact Hwrite. }
  have Hsecond_disjoint : Hoare.ResourceHoare.pexpr_list_dependencies arguments
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
  - iPoseProof (Hfirst Hfirst_disjoint values runtime formals binders valuation
      ambient Hfirst_envelope with "Hpre") as "Hfirst".
    iApply (translated_runtime_wp_mono with "Hfirst").
    iIntros "[Hglobal Hmiddle]".
    iApply (Hsecond Hsecond_disjoint values runtime formals binders valuation
      ambient Hsecond_envelope). iFrame.
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
    (tracked : pexpr_list Γ ts)
    (store : symbolic_store Γ F Δ)
    (pre_body frame : Translation.Resource.core_assertion F Δ)
    (post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid certificate
    tracked (Translation.Resource.RState store pre_body) post ->
  term_structured_runtime_arguments_valid certificate
    tracked
    (Translation.Resource.RState store
      (Translation.Resource.CAnd pre_body frame))
    (Translation.Resource.prenex_and post frame).
Proof.
  intros Hvalid Hdisjoint values runtime formals binders valuation ambient
    Henvelope.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "[#Hglobal [[Hstack [Hbody Hframe]] %Harguments]]".
  iPoseProof (Hvalid Hdisjoint values runtime formals binders valuation ambient
    Henvelope with "[-Hframe]") as "Hwp".
  { cbn [term_interp_resource_prenex_at_arguments].
    iFrame "Hglobal Hstack Hbody". iPureIntro. exact Harguments. }
  iCombine "Hwp Hframe" as "Hwp".
  iPoseProof (translated_runtime_wp_frame with "Hwp") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[[Hglobal' Hpost] Hframe]". iFrame "Hglobal'".
  iEval (rewrite (term_interp_resource_prenex_at_arguments_and runtime
    formals binders valuation tracked values post frame)).
  iFrame.
Qed.




Lemma term_structured_runtime_arguments_prenex_preserve_valid
    {Γ F Δ t entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (arguments : pexpr_list Γ ts)
    (pre post : Translation.Resource.resource_prenex Γ F (t :: Δ)) :
  term_structured_runtime_arguments_valid certificate
    arguments pre post ->
  term_structured_runtime_arguments_valid certificate
    arguments (Translation.Resource.ResourceExists t pre)
      (Translation.Resource.ResourceExists t post).
Proof.
  intros Hvalid Hdisjoint values runtime formals binders valuation ambient
    Henvelope.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "[#Hglobal Hpre]". iDestruct "Hpre" as (value) "Hbody".
  iPoseProof (Hvalid Hdisjoint values runtime formals
    (binder_cons value binders) valuation ambient Henvelope
    with "[$Hglobal $Hbody]") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[Hglobal' Hpost]". iFrame "Hglobal'".
  iExists value. iExact "Hpost".
Qed.

Lemma term_structured_runtime_arguments_prenex_elim_valid
    {Γ F Δ t entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (arguments : pexpr_list Γ ts)
    (pre : Translation.Resource.resource_prenex Γ F (t :: Δ))
    (post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid certificate
    arguments pre (Translation.Resource.weaken_resource_prenex post) ->
  term_structured_runtime_arguments_valid certificate
    arguments (Translation.Resource.ResourceExists t pre) post.
Proof.
  intros Hvalid Hdisjoint values runtime formals binders valuation ambient
    Henvelope.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "[#Hglobal Hpre]". iDestruct "Hpre" as (value) "Hbody".
  iPoseProof (Hvalid Hdisjoint values runtime formals
    (binder_cons value binders) valuation ambient Henvelope
    with "[$Hglobal $Hbody]") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[Hglobal' Hpost]". iFrame "Hglobal'".
  iEval (rewrite (term_interp_resource_prenex_at_arguments_weaken runtime
    formals binders valuation arguments values value post)) in "Hpost".
  iExact "Hpost".
Qed.


Lemma term_structured_runtime_arguments_bound_weaken_valid
    {Γ F Δ t entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (arguments : pexpr_list Γ ts)
    (pre post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid certificate
    arguments pre post ->
  term_structured_runtime_arguments_valid
    (Δ := t :: Δ) certificate arguments
    (Translation.Resource.weaken_resource_prenex pre)
    (Translation.Resource.weaken_resource_prenex post).
Proof.
  intros Hvalid Hdisjoint values runtime formals binders valuation ambient
    Henvelope.
  pose (source_binders := fun u (variable : bvar Δ u) =>
    binders u (MThere variable)).
  have Hrenaming : forall u (variable : bvar Δ u),
      binders u (Assertions.weaken_bound_renaming u variable) =
        source_binders u variable.
  { intros. reflexivity. }
  rewrite (term_interp_resource_prenex_at_arguments_rename runtime formals
    valuation arguments values pre _ Assertions.weaken_bound_renaming
    source_binders binders Hrenaming).
  iIntros "[#Hglobal Hpre]".
  iPoseProof (Hvalid Hdisjoint values runtime formals source_binders valuation
    ambient Henvelope with "[$Hglobal $Hpre]") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[Hglobal' Hpost]". iFrame "Hglobal'".
  rewrite (term_interp_resource_prenex_at_arguments_rename runtime formals
    valuation arguments values post _ Assertions.weaken_bound_renaming
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
    (arguments : pexpr_list Γ ts)
    (pre pre' post post' : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid certificate
    arguments pre post ->
  Hoare.ResourceHoare.resource_prenex_entails pre' pre ->
  Hoare.ResourceHoare.resource_prenex_entails post post' ->
  term_structured_runtime_arguments_valid certificate
    arguments pre' post'.
Proof.
  intros Hvalid Hpre Hpost Hdisjoint values runtime formals binders valuation
    ambient Henvelope.
  iIntros "[#Hglobal Hpre]".
  iPoseProof (term_interp_resource_prenex_at_arguments_entails runtime
    formals binders valuation arguments values pre' pre Hpre with "Hpre")
    as "Hpre".
  iPoseProof (Hvalid Hdisjoint values runtime formals binders valuation ambient
    Henvelope with "[$Hglobal $Hpre]") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[Hglobal' Hpost]". iFrame "Hglobal'".
  iApply (term_interp_resource_prenex_at_arguments_entails runtime formals
    binders valuation arguments values post post' Hpost with "Hpost").
Qed.

Lemma term_structured_runtime_arguments_frame_pre_valid
    {Γ F Δ entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (arguments : pexpr_list Γ ts)
    (pre pre' post : Translation.Resource.resource_prenex Γ F Δ)
    (frame : Translation.Resource.core_assertion F Δ) :
  term_structured_runtime_arguments_valid certificate
    arguments (Translation.Resource.prenex_and pre frame) post ->
  Hoare.ResourceHoare.resource_prenex_entails pre' pre ->
  term_structured_runtime_arguments_valid certificate
    arguments (Translation.Resource.prenex_and pre' frame) post.
Proof.
  intros Hvalid Hpre Hdisjoint values runtime formals binders valuation ambient
    Henvelope.
  iIntros "[#Hglobal Hframed]".
  iEval (rewrite (term_interp_resource_prenex_at_arguments_and runtime
    formals binders valuation arguments values pre' frame)) in "Hframed".
  iDestruct "Hframed" as "[Hpre Hframe]".
  iPoseProof (term_interp_resource_prenex_at_arguments_entails runtime
    formals binders valuation arguments values pre' pre Hpre with "Hpre")
    as "Hpre".
  iApply (Hvalid Hdisjoint values runtime formals binders valuation ambient
    Henvelope).
  iEval (rewrite (term_interp_resource_prenex_at_arguments_and runtime
    formals binders valuation arguments values pre frame)).
  iFrame "Hglobal Hpre Hframe".
Qed.

Lemma term_structured_runtime_arguments_core_consequence_valid
    {Γ F Δ entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (arguments : pexpr_list Γ ts)
    (store : symbolic_store Γ F Δ)
    (pre_body pre_body' : Translation.Resource.core_assertion F Δ)
    (post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid certificate
    arguments (Translation.Resource.RState store pre_body) post ->
  Hoare.ResourceHoare.core_entails pre_body' pre_body ->
  term_structured_runtime_arguments_valid certificate
    arguments (Translation.Resource.RState store pre_body') post.
Proof.
  intros Hvalid Hpre Hdisjoint values runtime formals binders valuation ambient
    Henvelope.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "[#Hglobal [[Hstack Hbody] %Harguments]]".
  iPoseProof (Validation.TermSemantics.core_entails_valid semantic_data
    (term_predicates valuation) _ _ Hpre formals binders valuation with "Hbody")
    as "Hbody".
  iPoseProof (Hvalid Hdisjoint values runtime formals binders valuation ambient
    Henvelope with "[-]") as "Hwp".
  { iFrame "Hglobal Hstack Hbody". iPureIntro. exact Harguments. }
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[Hglobal' Hpost]". iFrame "Hglobal'".
  iExact "Hpost".
Qed.

Lemma term_structured_runtime_arguments_stack_rewrite_valid
    {Γ F Δ entry statement exit ts}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (arguments : pexpr_list Γ ts)
    (store store' : symbolic_store Γ F Δ)
    (body : Translation.Resource.core_assertion F Δ)
    (post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid certificate
    arguments (Translation.Resource.RState store body) post ->
  Hoare.ResourceHoare.store_equal_under body Γ store' store ->
  term_structured_runtime_arguments_valid certificate
    arguments (Translation.Resource.RState store' body) post.
Proof.
  intros Hvalid Hstore Hdisjoint values runtime formals binders valuation ambient
    Henvelope.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "[#Hglobal [[Hstack Hbody] %Harguments]]".
  iAssert (⌜interp_store formals binders valuation store' =
             interp_store formals binders valuation store⌝)%I
    with "[Hbody]" as "%Hequal".
  { iApply (interp_store_equal_under body store store' Hstore). iExact "Hbody". }
  rewrite Hequal.
  iApply (Hvalid Hdisjoint values runtime formals binders valuation ambient
    Henvelope).
  cbn [term_interp_resource_prenex_at_arguments].
  iFrame "Hglobal Hstack Hbody".
  iPureIntro.
  have Hargument_interp := interp_program_expr_list_store_ext formals
    binders valuation store' store arguments Hequal.
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
    (open_equal : GenericRegions.Atomicity.analysis_open then_exit =
      GenericRegions.Atomicity.analysis_open else_exit)
    (atomic_equal : GenericRegions.Atomicity.analysis_in_atomic then_exit =
      GenericRegions.Atomicity.analysis_in_atomic else_exit)
    (arguments : pexpr_list Γ ts)
    (store : symbolic_store Γ F Δ)
    (body : Translation.Resource.core_assertion F Δ)
    (post : Translation.Resource.resource_prenex Γ F Δ) :
  term_structured_runtime_arguments_valid then_certificate
    arguments
    (Translation.Resource.RState store
      (Translation.Resource.CAnd body
        (Translation.Resource.CExpr (IR.symbolize_expr store condition))))
    post ->
  term_structured_runtime_arguments_valid else_certificate
    arguments
    (Translation.Resource.RState store
      (Translation.Resource.CAnd body
        (Translation.Resource.CExpr (EUnOp UNot
          (IR.symbolize_expr store condition))))) post ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredConditional Γ state condition
      then_branch else_branch then_exit else_exit then_certificate
      else_certificate open_equal atomic_equal)
    arguments (Translation.Resource.RState store body) post.
Proof.
  intros Hthen Helse Hdisjoint values runtime formals binders valuation ambient
    Henvelope.
  cbn [Hoare.ResourceHoare.statement_writes] in Hdisjoint.
  have Hthen_disjoint : Hoare.ResourceHoare.pexpr_list_dependencies arguments
      ## Hoare.ResourceHoare.statement_writes then_branch.
  { intros slot Hargument Hwrite. apply (Hdisjoint slot Hargument).
    apply elem_of_union_l. exact Hwrite. }
  have Helse_disjoint : Hoare.ResourceHoare.pexpr_list_dependencies arguments
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
  iIntros "[#Hglobal [[Hstack Hbody] %Harguments]]".
  destruct (interp_expr_total formals binders valuation
    (IR.symbolize_expr store condition)) as [value Hvalue].
  dependent destruction value. destruct b.
  - iApply (translated_runtime_wp_if_total_join runtime formals binders valuation
      store ambient state condition then_branch else_branch then_exit
      else_exit
      (global_world_context valuation ∗
       term_interp_resource_prenex_at_arguments runtime formals binders valuation
         arguments values post)
      (global_world_context valuation ∗
       (term_interp_core formals binders valuation body ∗
        ⌜interp_expr_list formals binders valuation
          (IR.symbolize_expr_list store arguments) = Some values⌝)) open_equal).
    + intros _. iIntros "[Hstack [#Hglobal' [Hbody %Harguments']]]".
      iApply (Hthen Hthen_disjoint values runtime formals binders valuation ambient
        Hthen_envelope).
      cbn [term_interp_resource_prenex_at_arguments].
      iFrame "Hglobal' Hstack Hbody". iPureIntro. split;
        [exact Hvalue | exact Harguments'].
    + intros Hfalse. rewrite Hvalue in Hfalse. discriminate.
    + iFrame "Hstack Hglobal Hbody". iPureIntro. exact Harguments.
  - iApply (translated_runtime_wp_if_total_join runtime formals binders valuation
      store ambient state condition then_branch else_branch then_exit
      else_exit
      (global_world_context valuation ∗
       term_interp_resource_prenex_at_arguments runtime formals binders valuation
         arguments values post)
      (global_world_context valuation ∗
       (term_interp_core formals binders valuation body ∗
        ⌜interp_expr_list formals binders valuation
          (IR.symbolize_expr_list store arguments) = Some values⌝)) open_equal).
    + intros Htrue. rewrite Hvalue in Htrue. discriminate.
    + intros _. iIntros "[Hstack [#Hglobal' [Hbody %Harguments']]]".
      iApply (Helse Helse_disjoint values runtime formals binders valuation ambient
        Helse_envelope).
      cbn [term_interp_resource_prenex_at_arguments].
      iFrame "Hglobal' Hstack Hbody". iPureIntro. split.
      * simpl. rewrite Hvalue. reflexivity.
      * exact Harguments'.
    + iFrame "Hstack Hglobal Hbody". iPureIntro. exact Harguments.
Qed.


(** Argument-indexed counterpart of the canonical-boundary interpretation.
    This follows the same proof-only opening spine while preserving the
    caller's stable argument vector. *)
Lemma term_structured_runtime_inv_access_focus_base_framed_arguments_valid
    {Γ F Δ entry invariant arguments body opened inner ts}
    (Hregistered : invariant ∈ term_registered_invariants )
    (Hopen : GenericRegions.Atomicity.open_invariant invariant entry = inr opened)
    (body_certificate : Structured.structured_certificate Γ opened body inner)
    (Hpreserved : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open opened)
    (focus_arguments : expr_list F Δ (Assertion.invariant_args invariant))
    (external body_pre body_post external_post :
      Translation.Resource.resource_prenex Γ F Δ)
    (Hopening : CertifiedNormalization.RavenHoareRules.access_opening
      invariant arguments
      (@CertifiedNormalization.RavenHoareRules.AccessFocusBase _ _
        Γ F invariant arguments Δ focus_arguments) external body_pre)
    (Hclosure : CertifiedNormalization.RavenHoareRules.access_closure
      invariant Δ focus_arguments
      (ResourceInstances.instantiated_invariant invariant focus_arguments)
      body_post external_post)
    (frame : Translation.Resource.core_assertion F Δ)
    (tracked : pexpr_list Γ ts) :
  term_structured_runtime_arguments_valid body_certificate
      tracked (Translation.Resource.prenex_and body_pre frame) body_post ->
  (forall (runtime : RegionExecution.Primitives.Model.stack_context Γ),
    @Atomic RuntimeLang.simp_lang WeaklyAtomic
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) body)) ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredInvAccess Γ entry invariant arguments body
      opened inner Hopen body_certificate Hpreserved)
    tracked (Translation.Resource.prenex_and external frame) external_post.
Proof.
  intros Hbody Hatomic.
  pose proof (CertifiedNormalization.RavenHoareRules.access_opening_base_view
    invariant arguments focus_arguments external body_pre Hopening) as Hbase.
  clear Hopening. revert frame Hbody. induction Hbase; intros extra Hbody.
  - eapply (term_structured_runtime_inv_access_arguments_valid
      Hregistered Hopen body_certificate Hpreserved store extra body_post
      external_post Hclosure tracked); [exact Hbody | exact Hatomic].
  - eapply term_structured_runtime_arguments_frame_pre_valid.
    + eapply IHHbase; try eassumption.
      eapply term_structured_runtime_arguments_frame_pre_valid;
        [exact Hbody | exact H0].
    + exact H.
  - eapply term_structured_runtime_arguments_prenex_consequence_valid.
    + eapply IHHbase; try eassumption.
      eapply term_structured_runtime_arguments_prenex_consequence_valid.
      { exact Hbody. }
      { apply Hoare.ResourceHoare.resource_prenex_entails_frame_assoc_back. }
      { apply Hoare.ResourceHoare.resource_prenex_entails_refl. }
    + cbn [Translation.Resource.prenex_and].
      apply Hoare.ResourceHoare.RPEBody. split; [reflexivity |].
      apply Hoare.ResourceHoare.CEntailsStep,
        Hoare.ResourceHoare.CESAndAssocR.
    + apply Hoare.ResourceHoare.resource_prenex_entails_refl.
  - eapply term_structured_runtime_arguments_frame_pre_valid.
    + eapply IHHbase; try eassumption.
      eapply term_structured_runtime_arguments_frame_pre_valid;
        [exact Hbody | exact H0].
    + apply Hoare.ResourceHoare.RPEBody. split; [reflexivity | exact H].
  - eapply term_structured_runtime_arguments_stack_rewrite_valid.
    + eapply IHHbase; try eassumption.
    + apply Hoare.ResourceHoare.store_equal_under_frame. exact H.
Qed.

Lemma term_structured_runtime_inv_access_boundary_arguments_valid
    {Γ F Δ entry invariant arguments body opened inner ts}
    (Hregistered : invariant ∈ term_registered_invariants )
    (Hopen : GenericRegions.Atomicity.open_invariant invariant entry = inr opened)
    (body_certificate : Structured.structured_certificate Γ opened body inner)
    (Hpreserved : GenericRegions.Atomicity.analysis_open inner =
      GenericRegions.Atomicity.analysis_open opened)
    (external_pre body_pre body_post external_post :
      Translation.Resource.resource_prenex Γ F Δ)
    (Hboundary : CertifiedNormalization.RavenHoareRules.access_boundary
      invariant arguments external_pre body_pre body_post external_post)
    (tracked : pexpr_list Γ ts) :
  term_structured_runtime_arguments_valid body_certificate
      tracked body_pre body_post ->
  (forall (runtime : RegionExecution.Primitives.Model.stack_context Γ),
    @Atomic RuntimeLang.simp_lang WeaklyAtomic
      (@RuntimeErasure.runtime_stmt _ _ Γ
        (RegionExecution.Primitives.Model.runtime_names Γ runtime)
        (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime) body)) ->
  term_structured_runtime_arguments_valid
    (Structured.StructuredInvAccess Γ entry invariant arguments body
      opened inner Hopen body_certificate Hpreserved)
    tracked external_pre external_post.
Proof.
  intros Hbody Hatomic.
  destruct (CertifiedNormalization.RavenHoareRules.access_boundary_base_view
    invariant arguments external_pre body_pre body_post external_post Hboundary)
    as (focus_arguments & Hopening & Hclosure).
  have Hbody_framed : term_structured_runtime_arguments_valid
      body_certificate tracked
      (Translation.Resource.prenex_and body_pre Translation.Resource.CTrue)
      body_post.
  { eapply term_structured_runtime_arguments_prenex_consequence_valid.
    - exact Hbody.
    - apply Hoare.ResourceHoare.resource_prenex_entails_frame_true_elim.
    - apply Hoare.ResourceHoare.resource_prenex_entails_refl. }
  have Haccess :=
    term_structured_runtime_inv_access_focus_base_framed_arguments_valid
       Hregistered Hopen body_certificate Hpreserved focus_arguments
      external_pre body_pre body_post external_post Hopening Hclosure
      Translation.Resource.CTrue tracked Hbody_framed Hatomic.
  eapply term_structured_runtime_arguments_prenex_consequence_valid.
  - exact Haccess.
  - apply Hoare.ResourceHoare.resource_prenex_entails_frame_true_intro.
  - apply Hoare.ResourceHoare.resource_prenex_entails_refl.
Qed.

(** Allocation over resource telescopes.  Like the other ambient rules,
    this appeals to the runtime allocation primitive directly:
    the ghost-initializer validity side condition and the allocated-fields
    telescope are both read through their core-shaped interpretations, so the
    rule never mentions the assertion representation. *)
Lemma term_ambient_allocation_rule_valid {Γ F Δ}
    (store : symbolic_store Γ F Δ) (target : pvar Γ TRef)
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
    concrete_operation_wp runtime ambient entry (TAlloc target fields) exit
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
    runtime formals binders valuation store target fields
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
Lemma interp_program_expr_update_store_with_bound_disjoint {Γ F Δ t u}
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (target : pvar Γ u)
    (value : tval u) (expression : pexpr Γ t) :
  Hoare.ResourceHoare.pexpr_dependencies expression ##
      ({[member_index target]} : gset nat) ->
  interp_program_expr formals (binder_cons value binders) valuation
      (IR.update_store_with_bound store target) expression =
    interp_program_expr formals binders valuation store expression.
Proof.
  intro Hdisjoint. induction expression; cbn [interp_program_expr] in *.
  - have Hneq : member_index variable <> member_index target.
    { intro Heq. apply (Hdisjoint (member_index variable)).
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
        ({[member_index target]} : gset nat).
    { intros slot Hin1 Hin2. apply (Hdisjoint slot); [apply elem_of_union_l |];
        assumption. }
    have Hright : Hoare.ResourceHoare.pexpr_dependencies expression2 ##
        ({[member_index target]} : gset nat).
    { intros slot Hin1 Hin2. apply (Hdisjoint slot); [apply elem_of_union_r |];
        assumption. }
    rewrite (IHexpression1 Hleft). rewrite (IHexpression2 Hright). reflexivity.
Qed.

Lemma interp_program_expr_list_update_store_with_bound_disjoint
    {Γ F Δ ts u}
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (target : pvar Γ u)
    (value : tval u) (expressions : pexpr_list Γ ts) :
  Hoare.ResourceHoare.pexpr_list_dependencies expressions ##
      ({[member_index target]} : gset nat) ->
  interp_program_expr_list formals (binder_cons value binders) valuation
      (IR.update_store_with_bound store target) expressions =
    interp_program_expr_list formals binders valuation store expressions.
Proof.
  intro Hdisjoint. induction expressions; cbn [interp_program_expr_list] in *.
  - reflexivity.
  - have Hhead : Hoare.ResourceHoare.pexpr_dependencies p ##
        ({[member_index target]} : gset nat).
    { intros slot Hin1 Hin2. apply (Hdisjoint slot); [apply elem_of_union_l |];
        assumption. }
    have Htail : Hoare.ResourceHoare.pexpr_list_dependencies expressions ##
        ({[member_index target]} : gset nat).
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
  GenericRegions.Atomicity.take_step (RegionSyntax.cost Γ statement) entry = inr exit ->
  Certified.procedure_cost_model_sound ->
  CertifiedNormalization.RavenHoareRules.RavenHoareTriple pre statement post ->
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
  - (* telescope preservation *)
    rewrite !term_interp_resource_exists.
    iIntros "[#Hglobal Hpre]". iDestruct "Hpre" as (value) "Hbody".
    iPoseProof (IHHtriple Hview Hstep runtime formals
      (binder_cons value binders) valuation ambient Henvelope Hregistry
      with "[$Hglobal $Hbody]") as "Hwp".
    iApply (RegionExecution.Primitives.operation_mono with "Hwp").
    iIntros "Hpost". iExists value. iExact "Hpost".
  - (* bound weakening *)
    pose (source_binders := fun u (variable : bvar Δ u) =>
      binders u (MThere variable)).
    have Hrenaming : forall u (variable : bvar Δ u),
        binders u (Assertions.weaken_bound_renaming u variable) =
          source_binders u variable.
    { intros. reflexivity. }
    unfold term_interp_resource_prenex at 1.
    rewrite (Translation.TermSemantics.interp_rename_resource_prenex
      semantic_data (term_predicates valuation) pre _
      Assertions.weaken_bound_renaming formals source_binders binders valuation
      (term_semantic_runtime runtime) Hrenaming).
    iIntros "[#Hglobal Hpre]".
    iPoseProof (IHHtriple Hview Hstep runtime formals source_binders valuation
      ambient Henvelope Hregistry with "[$Hglobal $Hpre]") as "Hwp".
    iApply (RegionExecution.Primitives.operation_mono with "Hwp").
    unfold term_interp_resource_prenex.
    rewrite (Translation.TermSemantics.interp_rename_resource_prenex
      semantic_data (term_predicates valuation) post _
      Assertions.weaken_bound_renaming formals source_binders binders valuation
      (term_semantic_runtime runtime) Hrenaming).
    done.
  - (* telescope elimination *)
    rewrite term_interp_resource_exists.
    iIntros "[#Hglobal Hpre]". iDestruct "Hpre" as (value) "Hbody".
    iPoseProof (IHHtriple Hview Hstep runtime formals
      (binder_cons value binders) valuation ambient Henvelope Hregistry
      with "[$Hglobal $Hbody]") as "Hwp".
    iApply (RegionExecution.Primitives.operation_mono with "Hwp").
    unfold term_interp_resource_prenex.
    rewrite (Translation.TermSemantics.interp_weaken_resource_prenex
      semantic_data). done.
  - (* prenex consequence *)
    iIntros "[#Hglobal Hpre]".
    iPoseProof (Validation.TermSemantics.resource_prenex_entails_valid
      semantic_data (term_predicates valuation) _ _ H runtime formals binders
      valuation with "Hpre") as "Hpre".
    iPoseProof (IHHtriple Hview Hstep runtime formals binders valuation ambient
      Henvelope Hregistry with "[$Hglobal $Hpre]") as "Hwp".
    iApply (RegionExecution.Primitives.operation_mono with "Hwp").
    iApply (Validation.TermSemantics.resource_prenex_entails_valid
      semantic_data (term_predicates valuation) _ _ H0 runtime formals binders
      valuation).
  - (* frame *)
    etrans; [| apply concrete_operation_wp_mono with
      (P := (term_interp_resource_prenex runtime formals binders valuation post ∗
             term_interp_core formals binders valuation frame)%I)].
    2: { unfold term_interp_resource_prenex.
         rewrite (Translation.TermSemantics.interp_prenex_and semantic_data).
         done. }
    rewrite term_interp_rstate.
    cbn [Translation.TermSemantics.interp_core].
    iIntros "[#Hglobal [Hstack [Hbody Hframe]]]".
    iApply (RegionExecution.Primitives.operation_frame with
      "[Hstack Hbody Hframe]").
    iFrame "Hframe".
    iApply IHHtriple; [exact Hview | exact Hstep | exact Henvelope |
      exact Hregistry |].
    rewrite term_interp_rstate. iFrame "Hglobal Hstack Hbody".
  - (* consequence *)
    rewrite term_interp_rstate.
    iIntros "[#Hglobal [Hstack Hbody]]".
    iPoseProof (Validation.TermSemantics.core_entails_valid semantic_data
      (term_predicates valuation) _ _ H formals binders valuation with "Hbody")
      as "Hbody".
    iPoseProof (IHHtriple Hview Hstep runtime formals binders valuation ambient
      Henvelope Hregistry with "[Hstack Hbody]") as "Hwp".
    { rewrite term_interp_rstate. iFrame "Hglobal Hstack Hbody". }
    iApply (RegionExecution.Primitives.operation_mono with "Hwp").
    apply (Validation.TermSemantics.resource_prenex_entails_valid
      semantic_data (term_predicates valuation) post post' H0 runtime formals
      binders valuation).
  - (* store rewrite *)
    rewrite term_interp_rstate.
    iIntros "[#Hglobal [Hstack Hbody]]".
    iAssert (⌜interp_store formals binders valuation store' =
               interp_store formals binders valuation store⌝)%I
      with "[Hbody]" as "%Hequal".
    { iApply (interp_store_equal_under body store store' H). iExact "Hbody". }
    rewrite Hequal.
    iApply (IHHtriple Hview Hstep runtime formals binders valuation ambient
      Henvelope Hregistry).
    rewrite term_interp_rstate. iFrame "Hglobal Hstack Hbody".
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
    destruct Hfacts as (Hrequired & _ & Hmask & _).
    iIntros "[#Hglobal Hpre]".
    iApply (procedure_leaf_operation_valid _ _ _
      (GenericRegions.Atomicity.analysis_mask entry)
      (GenericRegions.Atomicity.analysis_mask entry ∪
        Certified.granted_mask procedure) entry exit
      (call_discard_obligation procedure store typed_arguments
        (GenericRegions.Atomicity.analysis_mask entry) H Hrequired)
      with "[$Hglobal $Hpre]").
    + etrans; last exact Henvelope.
      apply RegionExecution.Primitives.Model.runtime_mask_mono.
      rewrite Hmask. reflexivity.
    + eapply term_registered_mask_active_closed.
      * eapply GenericRegions.Atomicity.procedure_call_step_success_closed.
        exact Hstep.
      * exact Hregistry.
  - (* call, result stored *)
    have Hfacts := Certified.certified_call_step_effect Hcost Γ
      procedure typed_arguments (Hoare.IR.CTStore target) entry exit
      Hstep.
    destruct Hfacts as (Hrequired & _ & Hmask & _).
    iIntros "[#Hglobal Hpre]".
    iApply (procedure_leaf_operation_valid _ _ _
      (GenericRegions.Atomicity.analysis_mask entry)
      (GenericRegions.Atomicity.analysis_mask entry ∪
        Certified.granted_mask procedure) entry exit
      (call_store_obligation procedure store target
        typed_arguments (GenericRegions.Atomicity.analysis_mask entry) H
        Hrequired)
      with "[$Hglobal $Hpre]").
    + etrans; last exact Henvelope.
      apply RegionExecution.Primitives.Model.runtime_mask_mono.
      rewrite Hmask. reflexivity.
    + eapply term_registered_mask_active_closed.
      * eapply GenericRegions.Atomicity.procedure_call_step_success_closed.
        exact Hstep.
      * exact Hregistry.
  - (* spawn *)
    have Hfacts := Certified.certified_spawn_step_effect Hcost
      _ _ _ _ _ Hstep.
    destruct Hfacts as (Hrequired & Hmask & _).
    iIntros "[#Hglobal Hpre]".
    iApply (procedure_leaf_operation_valid _ _ _
      (GenericRegions.Atomicity.analysis_mask entry)
      (GenericRegions.Atomicity.analysis_mask entry) entry exit
      (spawn_obligation procedure store typed_arguments
        (GenericRegions.Atomicity.analysis_mask entry) H Hrequired)
      with "[$Hglobal $Hpre]").
    + etrans; last exact Henvelope.
      apply RegionExecution.Primitives.Model.runtime_mask_mono.
      rewrite Hmask. reflexivity.
    + eapply term_registered_mask_active_closed.
      * eapply GenericRegions.Atomicity.procedure_spawn_step_success_closed.
        exact Hstep.
      * exact Hregistry.
  Unshelve. all: eauto.
Qed.

Lemma term_structured_runtime_resource_prenex_leaf_valid
    {Γ F Δ entry statement exit}
    (view : RegionSyntax.view statement = AnalysisView.ViewLeaf)
    (step : GenericRegions.Atomicity.take_step (RegionSyntax.cost Γ statement) entry =
      inr exit)
    (pre post : Translation.Resource.resource_prenex Γ F Δ)
    (derivation : CertifiedNormalization.RavenHoareRules.RavenHoareTriple
      pre statement post)
    (Hwf : GenericRegions.Atomicity.state_wf entry)
    (Hprocedure : Certified.procedure_cost_model_sound) :
  term_structured_runtime_valid
    (Structured.StructuredLeaf Γ entry statement exit view step) pre post.
Proof.
  intros runtime formals binders valuation ambient Henvelope.
  have Hexit_wf : GenericRegions.Atomicity.state_wf exit.
  { eapply GenericRegions.Atomicity.certificate_preserves_wf; [exact Hwf |].
    exact (GenericRegions.Atomicity.CertLeaf Γ entry statement exit
      view step). }
  have Hopen := GenericRegions.Atomicity.take_step_preserves_open _ _ _ step.
  have Hexit_envelope : RegionExecution.Primitives.Model.runtime_mask
      (GenericRegions.Atomicity.analysis_mask exit) ⊆ ambient.
  { etrans; last exact Henvelope.
    apply RegionExecution.Primitives.Model.runtime_mask_mono.
    intros invariant Hin. apply elem_of_union_l.
    apply Structured.structured_certificate_exit_subset_footprint. exact Hin. }
  have Hactive_exit :=
    RegionExecution.Primitives.Model.runtime_mask_subset_active ambient exit
      Hexit_wf Hexit_envelope.
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
    (tracked : pexpr_list Γ ts) (store : symbolic_store Γ F Δ)
    (pre_body post_body : Translation.Resource.core_assertion F Δ) :
  term_structured_runtime_valid certificate
    (Translation.Resource.RState store pre_body)
    (Translation.Resource.RState store post_body) ->
  term_structured_runtime_arguments_valid certificate
    tracked (Translation.Resource.RState store pre_body)
      (Translation.Resource.RState store post_body).
Proof.
  intros Hvalid _ values runtime formals binders valuation ambient Henvelope.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "[#Hglobal [Hpre %Harguments]]".
  iPoseProof (Hvalid runtime formals binders valuation ambient Henvelope
    with "[$Hglobal $Hpre]") as "Hwp".
  iAssert (⌜interp_expr_list formals binders valuation
      (IR.symbolize_expr_list store tracked) = Some values⌝)%I
    with "[]" as "Harguments_saved".
  { iPureIntro. exact Harguments. }
  iCombine "Hwp Harguments_saved" as "Hwp".
  iPoseProof (translated_runtime_wp_frame with "Hwp") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[[Hglobal' Hpost] %Harguments']". iFrame "Hglobal' Hpost".
  iPureIntro. exact Harguments'.
Qed.

Lemma term_structured_runtime_arguments_updated_store_valid
    {Γ F Δ entry statement exit ts u}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (tracked : pexpr_list Γ ts) (store : symbolic_store Γ F Δ)
    (target : pvar Γ u)
    (pre_body : Translation.Resource.core_assertion F Δ)
    (post_body : Translation.Resource.core_assertion F (u :: Δ)) :
  Hoare.ResourceHoare.statement_writes statement =
    ({[member_index target]} : gset nat) ->
  term_structured_runtime_valid certificate
    (Translation.Resource.RState store pre_body)
    (Translation.Resource.ResourceExists u
      (Translation.Resource.RState
        (IR.update_store_with_bound store target) post_body)) ->
  term_structured_runtime_arguments_valid certificate
    tracked (Translation.Resource.RState store pre_body)
      (Translation.Resource.ResourceExists u
        (Translation.Resource.RState
          (IR.update_store_with_bound store target) post_body)).
Proof.
  intros Hwrites Hvalid Hdisjoint values runtime formals binders valuation ambient
    Henvelope.
  rewrite Hwrites in Hdisjoint.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "[#Hglobal [Hpre %Harguments]]".
  iPoseProof (Hvalid runtime formals binders valuation ambient Henvelope
    with "[$Hglobal $Hpre]") as "Hwp".
  iAssert (⌜interp_expr_list formals binders valuation
      (IR.symbolize_expr_list store tracked) = Some values⌝)%I
    with "[]" as "Harguments_saved".
  { iPureIntro. exact Harguments. }
  iCombine "Hwp Harguments_saved" as "Hwp".
  iPoseProof (translated_runtime_wp_frame with "Hwp") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[[Hglobal' Hpost] %Harguments']". iFrame "Hglobal'".
  iEval (rewrite term_interp_resource_exists) in "Hpost".
  iDestruct "Hpost" as (result) "Hpost".
  iExists result. cbn [term_interp_resource_prenex_at_arguments].
  iFrame "Hpost". iPureIntro.
  have Hstable := interp_program_expr_list_update_store_with_bound_disjoint
    formals binders valuation store target result tracked Hdisjoint.
  unfold interp_program_expr_list in Hstable.
  rewrite Harguments' in Hstable. exact Hstable.
Qed.

Lemma term_structured_runtime_arguments_weakened_store_valid
    {Γ F Δ entry statement exit ts u}
    (certificate : Structured.structured_certificate
      Γ entry statement exit)
    (tracked : pexpr_list Γ ts) (store : symbolic_store Γ F Δ)
    (pre_body : Translation.Resource.core_assertion F Δ)
    (post_body : Translation.Resource.core_assertion F (u :: Δ)) :
  term_structured_runtime_valid certificate
    (Translation.Resource.RState store pre_body)
    (Translation.Resource.ResourceExists u
      (Translation.Resource.RState (weaken_store store) post_body)) ->
  term_structured_runtime_arguments_valid certificate
    tracked (Translation.Resource.RState store pre_body)
      (Translation.Resource.ResourceExists u
        (Translation.Resource.RState (weaken_store store) post_body)).
Proof.
  intros Hvalid _ values runtime formals binders valuation ambient Henvelope.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "[#Hglobal [Hpre %Harguments]]".
  iPoseProof (Hvalid runtime formals binders valuation ambient Henvelope
    with "[$Hglobal $Hpre]") as "Hwp".
  iAssert (⌜interp_expr_list formals binders valuation
      (IR.symbolize_expr_list store tracked) = Some values⌝)%I
    with "[]" as "Harguments_saved".
  { iPureIntro. exact Harguments. }
  iCombine "Hwp Harguments_saved" as "Hwp".
  iPoseProof (translated_runtime_wp_frame with "Hwp") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[[Hglobal' Hpost] %Harguments']". iFrame "Hglobal'".
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
    (tracked : pexpr_list Γ ts)
    (store : symbolic_store Γ F Δ) :
  term_structured_runtime_arguments_valid
    (Structured.StructuredFreshFold Γ entry invariant arguments
      Hfresh) tracked
    (Translation.Resource.RState store
      (ResourceInstances.instantiated_invariant invariant
        (IR.symbolize_expr_list store arguments)))
    (Translation.Resource.RState store
      (Translation.Resource.CInvariant invariant
        (IR.symbolize_expr_list store arguments))).
Proof.
  intros _ values runtime formals binders valuation ambient Henvelope.
  cbn [term_interp_resource_prenex_at_arguments].
  iIntros "[#Hglobal [Hpre %Harguments]]".
  have Hvalid := @term_structured_runtime_fresh_fold_valid
    _ _ _ _ _ _ store Hfresh Hregistered
    runtime formals binders valuation ambient Henvelope.
  iPoseProof (Hvalid with "[$Hglobal $Hpre]") as "Hwp".
  iAssert (⌜interp_expr_list formals binders valuation
      (IR.symbolize_expr_list store tracked) = Some values⌝)%I
    with "[]" as "Harguments_saved".
  { iPureIntro. exact Harguments. }
  iCombine "Hwp Harguments_saved" as "Hwp".
  iPoseProof (translated_runtime_wp_frame with "Hwp") as "Hwp".
  iApply (translated_runtime_wp_mono with "Hwp").
  iIntros "[[Hglobal' Hpost] %Harguments']". iFrame "Hglobal' Hpost".
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
  | Structured.StructuredInvAccess _ _ _ _ _ _ _ _ body_certificate _ =>
      fun runtime =>
        term_structured_certificate_trusted_runtime_atomicity body_certificate runtime
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
  - eapply GenericRegions.Atomicity.take_step_preserves_wf; eauto.
  - exact Hwf.
  - apply GenericRegions.Atomicity.fold_invariant_preserves_wf. exact Hwf.
  - apply IHcertificate2. apply IHcertificate1. exact Hwf.
  - have Hthen_wf := IHcertificate1 Hwf.
    unfold GenericRegions.Atomicity.state_wf in *.
    rewrite elem_of_disjoint in Hthen_wf |- *.
    intros candidate Hcandidate_open Hcandidate_mask.
    apply (Hthen_wf candidate Hcandidate_open).
    rewrite elem_of_intersection in Hcandidate_mask.
    destruct Hcandidate_mask as [Hcandidate_mask _]. exact Hcandidate_mask.
  - have Houter_wf : GenericRegions.Atomicity.state_wf outer.
    { eapply GenericRegions.Atomicity.take_step_preserves_wf; eauto. }
    exact (IHcertificate Houter_wf).
  - have Hopened_wf : GenericRegions.Atomicity.state_wf opened.
    { eapply GenericRegions.Atomicity.open_invariant_preserves_wf; eauto. }
    apply GenericRegions.Atomicity.fold_invariant_preserves_wf.
    exact (IHcertificate Hopened_wf).
Qed.

Lemma term_structured_certificate_preserves_nonatomic
    {Γ entry statement exit}
    (certificate : Structured.structured_certificate
      Γ entry statement exit) :
  GenericRegions.Atomicity.analysis_in_atomic entry = false ->
  GenericRegions.Atomicity.analysis_in_atomic exit = false.
Proof.
  intro Hin_atomic. induction certificate; simpl in *.
  - rewrite (GenericRegions.Atomicity.take_step_preserves_in_atomic
      _ _ _ e0). exact Hin_atomic.
  - exact Hin_atomic.
  - unfold GenericRegions.Atomicity.fold_invariant.
    destruct (bool_decide (invariant ∈
      GenericRegions.Atomicity.analysis_open entry)); exact Hin_atomic.
  - apply IHcertificate2. apply IHcertificate1. exact Hin_atomic.
  - apply IHcertificate1. exact Hin_atomic.
  - rewrite (GenericRegions.Atomicity.take_step_preserves_in_atomic
      _ _ _ e). exact Hin_atomic.
  - unfold GenericRegions.Atomicity.open_invariant in e.
    destruct (bool_decide (invariant ∈
      GenericRegions.Atomicity.analysis_open entry)); try discriminate.
    destruct (bool_decide (invariant ∈
      GenericRegions.Atomicity.analysis_mask entry)); try discriminate.
    inversion e; subst opened.
    have Hinner := IHcertificate Hin_atomic.
    unfold GenericRegions.Atomicity.fold_invariant.
    destruct (bool_decide (invariant ∈
      GenericRegions.Atomicity.analysis_open inner)); simpl; exact Hinner.
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

Lemma term_open_invariant_preserves_step_bit invariant entry exit :
  GenericRegions.Atomicity.open_invariant invariant entry = inr exit ->
  term_analysis_step_bit exit = term_analysis_step_bit entry.
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

Lemma term_fold_invariant_preserves_step_bit_if_open invariant entry :
  GenericRegions.Atomicity.analysis_open
      (GenericRegions.Atomicity.fold_invariant invariant entry) ≠ ∅ ->
  term_analysis_step_bit
      (GenericRegions.Atomicity.fold_invariant invariant entry) =
    term_analysis_step_bit entry.
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
        then_certificate IHthen else_certificate IHelse open_equal atomic_equal
      | Γ state body outer inner step body_certificate IHbody open_equal
      | Γ state invariant arguments body opened inner step body_certificate
        IHbody open_equal]; simpl in *.
  - destruct (RuntimeErasure.runtime_is_noop
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
    cbn. lia.
  - unfold RuntimeErasure.runtime_stmt. simpl.
    unfold term_analysis_step_bit, term_runtime_step_count.
    unfold GenericRegions.Atomicity.fold_invariant.
    rewrite bool_decide_false; [simpl; lia|exact Hfresh].
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
          (@RuntimeErasure.runtime_expr _ Γ _
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
      (@RuntimeErasure.runtime_expr _ Γ _
        (RegionExecution.Primitives.Model.runtime_names Γ runtime) condition)
      then_runtime else_runtime
      (RegionExecution.Primitives.Model.runtime_stack_id Γ runtime)) as Hif.
    unfold term_runtime_step_count, term_analysis_step_bit in *.
    destruct (RuntimeErasure.runtime_is_noop then_runtime),
      (RuntimeErasure.runtime_is_noop else_runtime),
      (RuntimeErasure.runtime_is_noop
        (RuntimeErasure.runtime_if
          (@RuntimeErasure.runtime_expr _ Γ _
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
    apply GenericRegions.Atomicity.open_invariant_success in step as
      (Hfresh_open & Havailable & Hopened_mask & Hopened_open).
    have Hopened_nonempty :
        GenericRegions.Atomicity.analysis_open opened ≠ ∅.
    { rewrite Hopened_open. intro Hempty. apply Hopen. set_solver. }
    have Hopened_atomic :
        GenericRegions.Atomicity.analysis_in_atomic opened = false.
    { unfold GenericRegions.Atomicity.open_invariant in Hopen_transition.
      destruct (bool_decide (invariant ∈
        GenericRegions.Atomicity.analysis_open state)); try discriminate.
      destruct (bool_decide (invariant ∈
        GenericRegions.Atomicity.analysis_mask state)); try discriminate.
      inversion Hopen_transition; subst opened. exact Hin_atomic. }
    specialize (IHbody runtime Hopened_nonempty Hopened_atomic).
    have Hinner_open : GenericRegions.Atomicity.analysis_open inner =
        {[invariant]} ∪ GenericRegions.Atomicity.analysis_open state.
    { rewrite open_equal. exact Hopened_open. }
    have Hmember : invariant ∈ GenericRegions.Atomicity.analysis_open inner.
    { rewrite Hinner_open. set_solver. }
    have Hexit_open : GenericRegions.Atomicity.analysis_open
        (GenericRegions.Atomicity.fold_invariant invariant inner) ≠ ∅.
    { unfold GenericRegions.Atomicity.fold_invariant.
      rewrite bool_decide_true; last exact Hmember.
      rewrite Hinner_open. intro Hremaining. simpl in Hremaining. apply Hopen.
      apply set_eq. intros candidate. rewrite elem_of_empty.
      split; last contradiction.
      intros Hcandidate.
      have Hcandidate_remaining : candidate ∈
          ({[invariant]} ∪ GenericRegions.Atomicity.analysis_open state) ∖
            {[invariant]}.
      { rewrite elem_of_difference elem_of_union elem_of_singleton.
        split; [right; exact Hcandidate|].
        intros ->. exact (Hfresh_open Hcandidate). }
      rewrite Hremaining elem_of_empty in Hcandidate_remaining.
      contradiction. }
    have Hopen_bit := term_open_invariant_preserves_step_bit
      invariant state opened Hopen_transition.
    have Hfold_bit := term_fold_invariant_preserves_step_bit_if_open
      invariant inner Hexit_open.
    unfold RuntimeErasure.runtime_stmt. simpl.
    rewrite Hopen_bit in IHbody. rewrite Hfold_bit.
    exact IHbody.
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
        then_certificate IHthen else_certificate IHelse open_equal atomic_equal
      | Γ state body outer inner step body_certificate IHbody open_equal
      | Γ state invariant arguments body opened inner step body_certificate
        IHbody open_equal]; simpl in Htrusted |- *.
  - eapply term_open_leaf_runtime_atomic; eauto.
  - (* done erases to the terminal statement, which takes no step *)
    destruct statement; cbn in view; try discriminate.
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
    apply GenericRegions.Atomicity.open_invariant_success in step as
      (_ & _ & _ & Hopened_open).
    have Hopened_nonempty :
        GenericRegions.Atomicity.analysis_open opened ≠ ∅.
    { rewrite Hopened_open. intros Hempty.
      have Hmember : invariant ∈
          {[invariant]} ∪ GenericRegions.Atomicity.analysis_open state.
      { apply elem_of_union_l. apply elem_of_singleton_2. reflexivity. }
      rewrite Hempty elem_of_empty in Hmember. contradiction. }
    have Hopened_atomic :
        GenericRegions.Atomicity.analysis_in_atomic opened = false.
    { unfold GenericRegions.Atomicity.open_invariant in Hopen_transition.
      destruct (bool_decide (invariant ∈
        GenericRegions.Atomicity.analysis_open state)); try discriminate.
      destruct (bool_decide (invariant ∈
        GenericRegions.Atomicity.analysis_mask state)); try discriminate.
      inversion Hopen_transition; subst opened. exact Hin_atomic. }
    eapply IHbody; eauto.
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
  term_structured_accesses_outside_atomic certificate ->
  (forall ts (tracked : pexpr_list Γ ts),
    term_structured_runtime_arguments_valid certificate
      tracked pre post) /\
  (forall runtime,
    term_structured_certificate_trusted_runtime_atomicity certificate runtime).
Proof.
  revert entry exit certificate.
  induction derivation; intros entry exit certificate Hwf Hcost
    Hprocedure_cost Hregistered Hsafe.
  all: tryif is_var statement then idtac else dependent destruction certificate.
  all: try discriminate.
  - destruct (IHderivation entry exit certificate Hwf Hcost
      Hprocedure_cost Hregistered Hsafe) as [Hvalid Htrusted].
    split.
    + intros ts tracked. apply term_structured_runtime_arguments_prenex_preserve_valid.
      apply Hvalid.
    + exact Htrusted.
  - destruct (IHderivation entry exit certificate Hwf Hcost
      Hprocedure_cost Hregistered Hsafe) as [Hvalid Htrusted].
    split.
    + intros ts tracked. apply term_structured_runtime_arguments_bound_weaken_valid.
      apply Hvalid.
    + exact Htrusted.
  - destruct (IHderivation entry exit certificate Hwf Hcost
      Hprocedure_cost Hregistered Hsafe) as [Hvalid Htrusted].
    split.
    + intros ts tracked. apply term_structured_runtime_arguments_prenex_elim_valid.
      apply Hvalid.
    + exact Htrusted.
  - destruct (IHderivation entry exit certificate Hwf Hcost
      Hprocedure_cost Hregistered Hsafe) as [Hvalid Htrusted].
    split.
    + intros ts tracked.
      eapply term_structured_runtime_arguments_prenex_consequence_valid;
        [apply Hvalid | exact H | exact H0].
    + exact Htrusted.
  - destruct (IHderivation entry exit certificate Hwf Hcost
      Hprocedure_cost Hregistered Hsafe) as [Hvalid Htrusted].
    split.
    + intros ts tracked. apply term_structured_runtime_arguments_frame_valid.
      apply Hvalid.
    + exact Htrusted.
  - destruct (IHderivation entry exit certificate Hwf Hcost
      Hprocedure_cost Hregistered Hsafe) as [Hvalid Htrusted].
    split.
    + intros ts tracked.
      eapply term_structured_runtime_arguments_prenex_consequence_valid.
      * eapply term_structured_runtime_arguments_core_consequence_valid.
        -- apply Hvalid.
        -- exact H.
      * apply Hoare.ResourceHoare.resource_prenex_entails_refl.
      * exact H0.
    + exact Htrusted.
  - destruct (IHderivation entry exit certificate Hwf Hcost
      Hprocedure_cost Hregistered Hsafe) as [Hvalid Htrusted].
    split.
    + intros ts tracked.
      eapply term_structured_runtime_arguments_stack_rewrite_valid;
        [apply Hvalid | exact H].
    + exact Htrusted.
  - (* done: it erases to the terminal statement and leaves the analysis
       state unchanged, so its runtime meaning is the identity update
       [|={E,E}=> post] — no leaf machinery, and no dependence on the shape
       of the pre- and postcondition. *)
    split; [|intros runtime; exact I]. intros ts tracked.
    intros Hdisjoint values runtime formals binders valuation ambient Henvelope.
    unfold term_structured_runtime_wp.
    rewrite translated_runtime_wp_erased; [|reflexivity].
    iIntros "H". iModIntro. iExact "H".
  - (* assert *)
    split; [|intros runtime; exact I]. intros ts tracked.
    eapply term_structured_runtime_arguments_same_store_valid.
    match goal with
    | Hview : _ = AnalysisView.ViewLeaf,
      Hstep : _ = inr _ |- _ =>
        eapply (term_structured_runtime_resource_prenex_leaf_valid
          Hview Hstep); [constructor | exact Hwf | exact Hprocedure_cost]
    end.
  - (* assignment *)
    split; [|intros runtime; exact I]. intros ts tracked.
    eapply term_structured_runtime_arguments_updated_store_valid.
    + reflexivity.
    + match goal with
      | Hview : _ = AnalysisView.ViewLeaf,
        Hstep : _ = inr _ |- _ =>
          eapply (term_structured_runtime_resource_prenex_leaf_valid
            Hview Hstep); [constructor | exact Hwf | exact Hprocedure_cost]
      end.
  - (* field read *)
    split; [|intros runtime; exact I]. intros ts tracked.
    eapply term_structured_runtime_arguments_updated_store_valid.
    + reflexivity.
    + match goal with
      | Hview : _ = AnalysisView.ViewLeaf,
        Hstep : _ = inr _ |- _ =>
          eapply (term_structured_runtime_resource_prenex_leaf_valid
            Hview Hstep); [constructor | exact Hwf | exact Hprocedure_cost]
      end.
  - (* field write *)
    split; [|intros runtime; exact I]. intros ts tracked.
    eapply term_structured_runtime_arguments_same_store_valid.
    match goal with
    | Hview : _ = AnalysisView.ViewLeaf,
      Hstep : _ = inr _ |- _ =>
        eapply (term_structured_runtime_resource_prenex_leaf_valid
          Hview Hstep); [constructor | exact Hwf | exact Hprocedure_cost]
    end.
  - (* allocation *)
    split; [|intros runtime; exact I]. intros ts tracked.
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
    split; [|intros runtime; exact I]. intros ts tracked.
    eapply term_structured_runtime_arguments_same_store_valid.
    match goal with
    | Hview : _ = AnalysisView.ViewLeaf,
      Hstep : _ = inr _ |- _ =>
        eapply (term_structured_runtime_resource_prenex_leaf_valid
          Hview Hstep); [constructor | exact Hwf | exact Hprocedure_cost]
    end.
  - destruct (IHderivation1 entry middle0 certificate1 Hwf Hcost
      Hprocedure_cost
      (fun invariant Hin => Hregistered invariant
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      (proj1 Hsafe)) as [Hfirst Hfirst_trusted].
    have Hmiddle_wf := term_structured_certificate_preserves_wf certificate1 Hwf.
    destruct (IHderivation2 middle0 exit certificate2 Hmiddle_wf Hcost
      Hprocedure_cost
      (fun invariant Hin => Hregistered invariant
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      (proj2 Hsafe)) as [Hsecond Hsecond_trusted].
    split.
    + intros ts tracked. eapply term_structured_runtime_arguments_sequence_valid;
        [apply Hfirst | apply Hsecond].
    + intros runtime. simpl. split;
        [apply Hfirst_trusted | apply Hsecond_trusted].
  - destruct (IHderivation1 entry then_exit certificate1 Hwf Hcost
      Hprocedure_cost
      (fun invariant Hin => Hregistered invariant
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      (proj1 Hsafe)) as [Hthen Hthen_trusted].
    destruct (IHderivation2 entry else_exit certificate2 Hwf Hcost
      Hprocedure_cost
      (fun invariant Hin => Hregistered invariant
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      (proj2 Hsafe)) as [Helse Helse_trusted].
    split.
    + intros ts tracked. eapply term_structured_runtime_arguments_conditional_valid;
        [apply Hthen | apply Helse].
    + intros runtime. simpl. split;
        [apply Hthen_trusted | apply Helse_trusted].
  - (* unmatched fold allocates the invariant *)
    split.
    + intros ts tracked.
      have Hregistered_invariant :
          invariant ∈ term_registered_invariants .
      { apply Hregistered.
        apply (Structured.structured_certificate_exit_subset_footprint
          (Structured.StructuredFreshFold Γ entry invariant
            arguments n)).
        rewrite Certified.fold_analysis_mask.
        apply elem_of_union_r. apply elem_of_singleton_2. reflexivity. }
      exact (term_structured_runtime_arguments_fresh_fold_valid
         n Hregistered_invariant tracked store).
    + intros runtime. exact I.
  - (* predicate unfold *)
    split; [|intros runtime; exact I]. intros ts tracked.
    eapply term_structured_runtime_arguments_same_store_valid.
    match goal with
    | Hview : _ = AnalysisView.ViewLeaf,
      Hstep : _ = inr _ |- _ =>
        eapply (term_structured_runtime_resource_prenex_leaf_valid
          Hview Hstep); [constructor | exact Hwf | exact Hprocedure_cost]
    end.
  - (* predicate fold *)
    split; [|intros runtime; exact I]. intros ts tracked.
    eapply term_structured_runtime_arguments_same_store_valid.
    match goal with
    | Hview : _ = AnalysisView.ViewLeaf,
      Hstep : _ = inr _ |- _ =>
        eapply (term_structured_runtime_resource_prenex_leaf_valid
          Hview Hstep); [constructor | exact Hwf | exact Hprocedure_cost]
    end.
  - (* matched invariant access *)
    simpl in Hsafe. destruct Hsafe as [Hentry_nonatomic Hbody_safe].
    have Hopen_facts := e.
    apply GenericRegions.Atomicity.open_invariant_success in Hopen_facts as
      (Hfresh & Havailable & Hopened_mask & Hopened_open).
    have Hopened_wf : GenericRegions.Atomicity.state_wf opened.
    { eapply GenericRegions.Atomicity.open_invariant_preserves_wf; eauto. }
    destruct (IHderivation opened inner certificate Hopened_wf Hcost
      Hprocedure_cost
      (fun candidate Hin => Hregistered candidate
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      Hbody_safe) as [Hbody_valid Hbody_trusted].
    split.
    + intros ts tracked.
      have Hregistered_invariant :
          invariant ∈ term_registered_invariants .
      { apply Hregistered.
        apply (Structured.structured_certificate_entry_subset_footprint
          (Structured.StructuredInvAccess Γ entry invariant arguments
            body opened inner e certificate e0)).
        exact Havailable. }
      eapply term_structured_runtime_inv_access_boundary_arguments_valid.
      * exact Hregistered_invariant.
      * exact H.
      * apply Hbody_valid.
      * intros runtime.
        eapply (term_open_structured_certificate_runtime_atomic certificate
          runtime Hcost).
        -- simpl. intros Hempty.
           have Hin : invariant ∈ {[invariant]} ∪
               GenericRegions.Atomicity.analysis_open entry.
           { apply elem_of_union_l. apply elem_of_singleton_2. reflexivity. }
           have Hin_opened : invariant ∈
               GenericRegions.Atomicity.analysis_open opened.
           { rewrite Hopened_open. exact Hin. }
           have Habsurd : invariant ∈ (∅ : gset inv_id).
           { rewrite <- Hempty. exact Hin_opened. }
           rewrite elem_of_empty in Habsurd. contradiction.
        -- rewrite (GenericRegions.Atomicity.open_invariant_preserves_in_atomic
             invariant entry opened e). exact Hentry_nonatomic.
        -- apply Hbody_trusted.
    + exact Hbody_trusted.
  - (* independent invariant access *)
    simpl in Hsafe. destruct Hsafe as [Hentry_nonatomic Hbody_safe].
    have Hopen_facts := e.
    apply GenericRegions.Atomicity.open_invariant_success in Hopen_facts as
      (Hfresh & Havailable & Hopened_mask & Hopened_open).
    have Hopened_wf : GenericRegions.Atomicity.state_wf opened.
    { eapply GenericRegions.Atomicity.open_invariant_preserves_wf; eauto. }
    destruct (IHderivation opened inner certificate Hopened_wf Hcost
      Hprocedure_cost
      (fun candidate Hin => Hregistered candidate
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      Hbody_safe) as [Hbody_valid Hbody_trusted].
    split.
    + intros ts tracked.
      have Hregistered_invariant :
          invariant ∈ term_registered_invariants .
      { apply Hregistered.
        apply (Structured.structured_certificate_entry_subset_footprint
          (Structured.StructuredInvAccess Γ entry invariant arguments
            body opened inner e certificate e0)).
        exact Havailable. }
      eapply (term_structured_runtime_independent_inv_access_arguments_valid
         Hregistered_invariant e certificate e0 opening_focus
        closing_focus external_pre body_pre body_post external_post H H0 H1
        tracked).
      * apply Hbody_valid.
      * intros runtime.
        eapply (term_open_structured_certificate_runtime_atomic certificate
          runtime Hcost).
        -- simpl. intros Hempty.
           have Hin : invariant ∈ {[invariant]} ∪
               GenericRegions.Atomicity.analysis_open entry.
           { apply elem_of_union_l. apply elem_of_singleton_2. reflexivity. }
           have Hin_opened : invariant ∈
               GenericRegions.Atomicity.analysis_open opened.
           { rewrite Hopened_open. exact Hin. }
           have Habsurd : invariant ∈ (∅ : gset inv_id).
           { rewrite <- Hempty. exact Hin_opened. }
           rewrite elem_of_empty in Habsurd. contradiction.
        -- rewrite (GenericRegions.Atomicity.open_invariant_preserves_in_atomic
             invariant entry opened e). exact Hentry_nonatomic.
        -- apply Hbody_trusted.
    + exact Hbody_trusted.
  - (* trusted atomic block *)
    simpl in Hsafe.
    have Houter_wf : GenericRegions.Atomicity.state_wf outer.
    { eapply GenericRegions.Atomicity.take_step_preserves_wf; eauto. }
    have Hbody_wf : GenericRegions.Atomicity.state_wf
        (GenericRegions.Atomicity.AnalysisState
          (GenericRegions.Atomicity.analysis_mask outer)
          (GenericRegions.Atomicity.analysis_open outer)
          (GenericRegions.Atomicity.analysis_step_taken outer) true).
    { exact Houter_wf. }
    destruct (IHderivation _ inner certificate Hbody_wf Hcost
      Hprocedure_cost
      (fun invariant Hin => Hregistered invariant
        ltac:(simpl; repeat rewrite elem_of_union; tauto))
      Hsafe) as [Hbody_valid Hbody_trusted].
    split.
    + intros ts tracked.
      eapply term_structured_runtime_arguments_atomic_valid.
      apply Hbody_valid.
    + intros runtime. exact I.
  - (* call, result discarded *)
    split; [|intros runtime; exact I]. intros ts tracked.
    eapply term_structured_runtime_arguments_weakened_store_valid.
    match goal with
    | Hview : _ = AnalysisView.ViewLeaf,
      Hstep : _ = inr _ |- _ =>
        eapply (term_structured_runtime_resource_prenex_leaf_valid
          Hview Hstep); [constructor; exact H | exact Hwf |
            exact Hprocedure_cost]
    end.
  - (* call, result stored *)
    split; [|intros runtime; exact I]. intros ts tracked.
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
    split; [|intros runtime; exact I]. intros ts tracked.
    eapply term_structured_runtime_arguments_same_store_valid.
    match goal with
    | Hview : _ = AnalysisView.ViewLeaf,
      Hstep : _ = inr _ |- _ =>
        eapply (term_structured_runtime_resource_prenex_leaf_valid
          Hview Hstep); [constructor; exact H | exact Hwf |
            exact Hprocedure_cost]
    end.
Qed.

Theorem term_structured_certificate_resource_prenex_valid
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
  term_structured_accesses_outside_atomic certificate ->
  term_structured_runtime_valid certificate pre post /\
  (forall runtime,
    term_structured_certificate_trusted_runtime_atomicity certificate runtime).
Proof.
  intros Hwf Hcost Hprocedure_cost Hregistered Hsafe.
  destruct (term_structured_certificate_resource_prenex_arguments_valid
     certificate derivation Hwf Hcost Hprocedure_cost Hregistered Hsafe)
    as [Harguments Htrusted].
  split; [|exact Htrusted].
  intros runtime formals binders valuation ambient Henvelope.
  have Hempty := Harguments [] (@PENil _ Γ).
  unfold term_structured_runtime_arguments_valid in Hempty.
  specialize (Hempty ltac:(simpl; apply disjoint_empty_l)
    Translation.TVNil runtime formals binders valuation ambient Henvelope).
  rewrite term_interp_resource_prenex_at_arguments_empty in Hempty.
  etrans; first exact Hempty.
  unfold term_structured_runtime_wp.
  apply translated_runtime_wp_mono.
  rewrite term_interp_resource_prenex_at_arguments_empty. done.
Qed.

End WithRuntime.
End WithContracts.
End RuleValidity.
