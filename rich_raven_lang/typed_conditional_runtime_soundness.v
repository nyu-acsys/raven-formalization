From raven_iris.simp_raven_lang Require Import ra_base.
From stdpp Require Import sets coPset.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic Require Import atomic.
From iris.proofmode Require Import tactics.
From Coq Require Import Program.Equality ClassicalEpsilon.
From raven_iris.rich_raven_lang Require Import
  typed_assertion typed_runtime typed_conditional_raven_adapter.

(** Supported, non-cyclic entry point for normalized runtime soundness.

    [typed_runtime] defines the concrete resources and aligned operational
    zipper.  [typed_conditional_raven_adapter] is downstream of it and proves
    normalization plus traced CPS validity.  Adequacy clients should import
    this module rather than the deprecated focused decomposition formerly
    exported directly by [typed_runtime]. *)
Module Make (LegacyRAs : ra_base.RA_CONFIG)
    (Logic : TypedAssertion.LOGIC_SIGNATURE).

Module Adapter := typed_conditional_raven_adapter.Make LegacyRAs Logic.
Module Runtime := Adapter.Runtime.

Module WithContracts (Contracts : Runtime.Validation.Hoare.CONTRACT_ENV).
Module RuntimeAdapter := Adapter.WithContracts Contracts.

Module WithRuntimeValidity
    (Resources : Runtime.RUNTIME_RESOURCES)
    (ProcedureContracts :
      Runtime.Validation.Hoare.PROCEDURE_CONTRACT_COHERENCE Contracts)
    (Leaf : Runtime.DEFAULT_SEMANTIC_LEAF_CONTRACTS Resources Contracts)
    (Defs : Runtime.Translation.DEFINITION_ENV).

Module Export Normalized := RuntimeAdapter.AlignedNormalization Resources
  ProcedureContracts Leaf Defs.
Local Existing Instance Normalized.Validity.Model.concrete_irisG.

(** Canonical relative-region result replacing the structural part of the
    legacy focused-access path.  This is deliberately not named a closed
    runtime theorem: the final [translated_runtime_wp] refinement remains a
    separate adequacy obligation. *)
Definition normalized_aligned_operational_suffix_region_valid :=
  @Normalized.aligned_suffix_has_valid_trace.

(** A normalized execution cannot in general be flattened while an invariant
    is open: the next physical statement has to run at the mask selected by
    the erased unfold prefix.  A mask-indexed continuation retains that mask
    barrier until the final closed reification theorem. *)
Definition mask_cont := coPset -> iProp Resources.Σ.

Fixpoint trace_runtime_cps_wp
    {cost Γ entry exit mode tail stack_out source tree}
    (trace : RuntimeAdapter.net_trace cost Γ entry exit mode tail stack_out
      source tree)
    (runtime : Normalized.Validity.Model.stack_context Γ) (ambient : coPset)
    (continuation : mask_cont) {struct trace} : iProp Resources.Σ :=
  match trace with
  | @RuntimeAdapter.TraceDoneNet _ _ entry _ =>
      continuation
        (Normalized.Validity.Model.active_runtime_mask ambient entry)
  | @RuntimeAdapter.TraceDoneFocused _ _ entry _ _ =>
      continuation
        (Normalized.Validity.Model.active_runtime_mask ambient entry)
  | @RuntimeAdapter.TraceChunk _ _ _ _ _ _ _ _ _ certificate _ _ _ _ Hrest =>
      Normalized.Validity.aligned_runtime_region_wp certificate runtime ambient
        (trace_runtime_cps_wp Hrest runtime ambient continuation)
  | @RuntimeAdapter.TraceFocusedPrefix _ _ _ _ _ _ _ _ _ _ certificate _ _
      _ _ _ Hrest =>
      Normalized.Validity.aligned_runtime_region_wp certificate runtime ambient
        (trace_runtime_cps_wp Hrest runtime ambient continuation)
  | @RuntimeAdapter.TraceAccess _ _ _ _ _ _ _ _ _ _ certificate _ _ _ _ _
      Hbody =>
      Normalized.Validity.aligned_runtime_region_wp certificate runtime ambient
        (trace_runtime_cps_wp Hbody runtime ambient continuation)
  | @RuntimeAdapter.TraceNestedAccess _ _ _ _ _ _ _ _ _ _ _ certificate _ _
      _ _ _ Hbody =>
      Normalized.Validity.aligned_runtime_region_wp certificate runtime ambient
        (trace_runtime_cps_wp Hbody runtime ambient continuation)
  | @RuntimeAdapter.TraceClose _ _ _ _ _ _ _ _ _ _ certificate _ _ _ _ _
      Hrest =>
      Normalized.Validity.aligned_runtime_region_wp certificate runtime ambient
        (trace_runtime_cps_wp Hrest runtime ambient continuation)
  | @RuntimeAdapter.TraceFocusedClose _ _ _ _ _ _ _ _ _ _ certificate _ _ _
      _ _ Hrest =>
      Normalized.Validity.aligned_runtime_region_wp certificate runtime ambient
        (trace_runtime_cps_wp Hrest runtime ambient continuation)
  | @RuntimeAdapter.TraceConditional _ _ _ entry statement _ _ then_exit
      else_exit _ _ _ _ _ _ _ _ _ _ _ _ _ Hthen Helse Hrest =>
      let shared := trace_runtime_cps_wp Hrest runtime ambient continuation in
      Normalized.Validity.Execution.Primitives.branch_wp runtime ambient entry
        statement then_exit else_exit
        (trace_runtime_cps_wp Hthen runtime ambient (fun _ => shared))
        (trace_runtime_cps_wp Helse runtime ambient (fun _ => shared))
  | @RuntimeAdapter.TraceFocusedConditional _ _ _ entry statement _ _
      then_exit else_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hthen Helse Hrest =>
      let shared := trace_runtime_cps_wp Hrest runtime ambient continuation in
      Normalized.Validity.Execution.Primitives.branch_wp runtime ambient entry
        statement then_exit else_exit
        (trace_runtime_cps_wp Hthen runtime ambient (fun _ => shared))
        (trace_runtime_cps_wp Helse runtime ambient (fun _ => shared))
  | @RuntimeAdapter.TraceFocusedConditionalContinue _ _ _ entry statement _ _
      then_exit else_exit _ _ _ _ _ _ _ _ _ _ _ _ _ Hthen Helse Hrest =>
      let shared := trace_runtime_cps_wp Hrest runtime ambient continuation in
      Normalized.Validity.Execution.Primitives.branch_wp runtime ambient entry
        statement then_exit else_exit
        (trace_runtime_cps_wp Hthen runtime ambient (fun _ => shared))
        (trace_runtime_cps_wp Helse runtime ambient (fun _ => shared))
  | @RuntimeAdapter.TraceExpansion _ _ _ _ _ _ _ _ _ _ _ Hflat =>
      trace_runtime_cps_wp Hflat runtime ambient continuation
  end.

Lemma aligned_runtime_region_wp_mono
    {Γ fuel entry statement exit cost}
    (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
      entry statement exit)
    (runtime : Normalized.Validity.Model.stack_context Γ) ambient (P Q : iProp Resources.Σ) :
  (P ⊢ Q) ->
  Normalized.Validity.aligned_runtime_region_wp certificate runtime ambient P ⊢
    Normalized.Validity.aligned_runtime_region_wp certificate runtime ambient Q.
Proof.
  revert P Q. induction certificate; intros P Q HPQ; simpl.
  - apply Normalized.Validity.translated_runtime_wp_mono. exact HPQ.
  - apply Normalized.Validity.Execution.Primitives.Interface.operation_mono.
    exact HPQ.
  - apply Normalized.Validity.Execution.Primitives.Interface.operation_mono.
    exact HPQ.
  - apply IHcertificate1. apply IHcertificate2. exact HPQ.
  - apply Normalized.Validity.translated_runtime_wp_mono. exact HPQ.
  - apply Normalized.Validity.translated_runtime_wp_mono. exact HPQ.
Qed.

Lemma trace_runtime_cps_wp_mono
    {cost Γ entry exit mode tail stack_out source tree}
    (trace : RuntimeAdapter.net_trace cost Γ entry exit mode tail stack_out
      source tree)
    (runtime : Normalized.Validity.Model.stack_context Γ) ambient
    (left right : mask_cont) :
  (forall mask, left mask ⊢ right mask) ->
  trace_runtime_cps_wp trace runtime ambient left ⊢
    trace_runtime_cps_wp trace runtime ambient right.
Proof.
  revert left right. induction trace; intros left right Hcontinuation; simpl.
  - apply Hcontinuation.
  - apply Hcontinuation.
  - apply aligned_runtime_region_wp_mono.
    exact (IHtrace left right Hcontinuation).
  - apply aligned_runtime_region_wp_mono.
    exact (IHtrace left right Hcontinuation).
  - apply aligned_runtime_region_wp_mono.
    exact (IHtrace left right Hcontinuation).
  - apply aligned_runtime_region_wp_mono.
    exact (IHtrace left right Hcontinuation).
  - apply aligned_runtime_region_wp_mono.
    exact (IHtrace left right Hcontinuation).
  - apply aligned_runtime_region_wp_mono.
    exact (IHtrace left right Hcontinuation).
  - apply Normalized.Validity.Execution.Primitives.Interface.branch_mono.
    + apply IHtrace1. intros _. apply IHtrace3. exact Hcontinuation.
    + apply IHtrace2. intros _. apply IHtrace3. exact Hcontinuation.
  - apply Normalized.Validity.Execution.Primitives.Interface.branch_mono.
    + apply IHtrace1. intros _. apply IHtrace3. exact Hcontinuation.
    + apply IHtrace2. intros _. apply IHtrace3. exact Hcontinuation.
  - apply Normalized.Validity.Execution.Primitives.Interface.branch_mono.
    + apply IHtrace1. intros _. apply IHtrace3. exact Hcontinuation.
    + apply IHtrace2. intros _. apply IHtrace3. exact Hcontinuation.
  - exact (IHtrace left right Hcontinuation).
Qed.

Lemma trace_runtime_cps_wp_terminal_mono
    {cost Γ entry exit mode tail stack_out source tree}
    (trace : RuntimeAdapter.net_trace cost Γ entry exit mode tail stack_out
      source tree)
    (runtime : Normalized.Validity.Model.stack_context Γ) ambient
    (left right : mask_cont) :
  (left (Normalized.Validity.Model.active_runtime_mask ambient exit) ⊢
   right (Normalized.Validity.Model.active_runtime_mask ambient exit)) ->
  trace_runtime_cps_wp trace runtime ambient left ⊢
    trace_runtime_cps_wp trace runtime ambient right.
Proof.
  revert left right. induction trace; intros left right Hterminal; simpl.
  - exact Hterminal.
  - exact Hterminal.
  - apply aligned_runtime_region_wp_mono. now apply IHtrace.
  - apply aligned_runtime_region_wp_mono. now apply IHtrace.
  - apply aligned_runtime_region_wp_mono. now apply IHtrace.
  - apply aligned_runtime_region_wp_mono. now apply IHtrace.
  - apply aligned_runtime_region_wp_mono. now apply IHtrace.
  - apply aligned_runtime_region_wp_mono. now apply IHtrace.
  - have Hshared := IHtrace3 left right Hterminal.
    apply Normalized.Validity.Execution.Primitives.Interface.branch_mono.
    + apply trace_runtime_cps_wp_mono. intros _. exact Hshared.
    + apply trace_runtime_cps_wp_mono. intros _. exact Hshared.
  - have Hshared := IHtrace3 left right Hterminal.
    apply Normalized.Validity.Execution.Primitives.Interface.branch_mono.
    + apply trace_runtime_cps_wp_mono. intros _. exact Hshared.
    + apply trace_runtime_cps_wp_mono. intros _. exact Hshared.
  - have Hshared := IHtrace3 left right Hterminal.
    apply Normalized.Validity.Execution.Primitives.Interface.branch_mono.
    + apply trace_runtime_cps_wp_mono. intros _. exact Hshared.
    + apply trace_runtime_cps_wp_mono. intros _. exact Hshared.
  - now apply IHtrace.
Qed.

(** Proof-relevant overlay used by the concrete refinement.  It deliberately
    lives in this already-instantiated functor: re-applying the runtime
    functors in a separate module would create incompatible generative
    contract signatures. *)
Record aligned_normalized_trace
    {cost : RuntimeAdapter.Atomicity.cost_model} {Γ F Δ} {entry}
    {pre : Runtime.Translation.Assertions.assertion Γ F Δ} {stack_in} {exit}
    {post : Runtime.Translation.Assertions.assertion Γ F Δ} {stack_out} : Type := {
  aligned_net_suffix : Normalized.Validity.aligned_operational_suffix cost Γ F Δ
    entry pre stack_in exit post stack_out;
  aligned_net_normal : @RuntimeAdapter.traced_suffix_net_normalization cost Γ
    entry exit stack_in stack_out
    (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
      aligned_net_suffix);
}.

Lemma normalize_aligned_net_trace
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (suffix : Normalized.Validity.aligned_operational_suffix cost Γ F Δ entry
      pre stack_in exit post stack_out)
    (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
    (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in) :
    exists _ : @aligned_normalized_trace cost Γ F Δ entry pre stack_in exit post
      stack_out, True.
Proof.
  destruct (Normalized.aligned_suffix_traced_normalization suffix Hwf Hstack)
    as [normal _].
  exists {| aligned_net_suffix := suffix; aligned_net_normal := normal |}.
  exact I.
Qed.

(** Resource-indexed view of one normalized executable trace.  Its source is
    still certificate-only, but the retained suffix carries resource triples
    and their analysis alignments rather than compatibility Hoare triples. *)
Definition resource_certificate_suffix_of_operational_suffix
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (suffix : Normalized.Validity.resource_aligned_operational_suffix
      cost Γ F Δ entry pre stack_in exit post stack_out) :
    RuntimeAdapter.certificate_suffix cost Γ entry exit :=
  Normalized.Erasure.certificate_suffix_of_operational_suffix
    (Normalized.Validity.erase_resource_aligned_operational_suffix suffix).

Record resource_aligned_normalized_trace
    {cost : RuntimeAdapter.Atomicity.cost_model} {Γ F Δ} {entry}
    {pre : Runtime.Translation.Assertions.assertion Γ F Δ} {stack_in} {exit}
    {post : Runtime.Translation.Assertions.assertion Γ F Δ} {stack_out} : Type := {
  resource_net_suffix :
    Normalized.Validity.resource_aligned_operational_suffix cost Γ F Δ
      entry pre stack_in exit post stack_out;
  resource_net_normal : @RuntimeAdapter.traced_suffix_net_normalization cost Γ
    entry exit stack_in stack_out
    (resource_certificate_suffix_of_operational_suffix resource_net_suffix);
}.

Lemma resource_certificate_suffix_has_lifo
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (suffix : Normalized.Validity.resource_aligned_operational_suffix
      cost Γ F Δ entry pre stack_in exit post stack_out) :
  RuntimeAdapter.suffix_lifo
    (resource_certificate_suffix_of_operational_suffix suffix)
    stack_in stack_out.
Proof.
  apply (proj2 (Normalized.Erasure.certificate_suffix_of_operational_suffix_lifo
    (Normalized.Validity.erase_resource_aligned_operational_suffix suffix)
    stack_in stack_out)).
  apply Normalized.Validity.erase_resource_aligned_operational_suffix_lifo.
Qed.

Lemma normalize_resource_aligned_net_trace
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (suffix : Normalized.Validity.resource_aligned_operational_suffix cost Γ F Δ
      entry pre stack_in exit post stack_out)
    (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
    (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in) :
    exists _ : @resource_aligned_normalized_trace cost Γ F Δ entry pre stack_in
      exit post stack_out, True.
Proof.
  pose proof (RuntimeAdapter.traced_total_net _
    (RuntimeAdapter.traced_suffix_net_totality_complete
      (resource_certificate_suffix_of_operational_suffix suffix) Hwf)
    stack_in stack_out Hwf Hstack
    (resource_certificate_suffix_has_lifo suffix)) as Hnormal.
  destruct Hnormal as [normal _].
  exists {| resource_net_suffix := suffix; resource_net_normal := normal |}.
  exact I.
Qed.

(** Target interface for resource structured-CPS completion.  The two cost
    witnesses are deliberately retained here: resource procedure leaves use
    the certified effect witness, while the normalized physical trace uses
    the runtime cost witness for its step-budget side conditions. *)
Definition resource_aligned_trace_structured_cps_valid
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (aligned : @resource_aligned_normalized_trace cost Γ F Δ entry pre
      stack_in exit post stack_out) : Prop :=
  Normalized.Validity.Model.runtime_cost_model_sound cost ->
  Normalized.Validity.Certified.procedure_cost_model_sound cost ->
  RuntimeAdapter.Atomicity.state_wf entry ->
  forall (runtime : Normalized.Validity.Model.stack_context Γ)
    (formals : Runtime.Core.formal_env F)
    (binders : Runtime.Core.binder_env Δ) (atoms : Runtime.Core.atom_env)
    (ambient : coPset),
    Normalized.Validity.Model.runtime_mask
      (Normalized.suffix_footprint
        (resource_certificate_suffix_of_operational_suffix
          aligned.(resource_net_suffix))) ⊆ ambient ->
    forall continuation : mask_cont,
    ((Normalized.Validity.global_world_context atoms ∗
      Normalized.Validity.VSemantics.S.interp_assertion
        (Leaf.predicates atoms) runtime formals binders atoms post ∗
      Normalized.Validity.World.access_stack_interp atoms ambient stack_out) ⊢
      continuation
        (Normalized.Validity.Model.active_runtime_mask ambient exit)) ->
    (Normalized.Validity.global_world_context atoms ∗
     Normalized.Validity.VSemantics.S.interp_assertion
       (Leaf.predicates atoms) runtime formals binders atoms pre ∗
     Normalized.Validity.World.access_stack_interp atoms ambient stack_in) ⊢
    trace_runtime_cps_wp
      (RuntimeAdapter.traced_net_source _ aligned.(resource_net_normal))
      runtime ambient continuation.

Definition aligned_trace_structured_cps_valid
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (aligned : @aligned_normalized_trace cost Γ F Δ entry pre stack_in exit post
      stack_out) : Prop :=
  RuntimeAdapter.Atomicity.state_wf entry ->
  forall (runtime : Normalized.Validity.Model.stack_context Γ)
    (formals : Runtime.Core.formal_env F)
    (binders : Runtime.Core.binder_env Δ) (atoms : Runtime.Core.atom_env)
    (ambient : coPset),
    Normalized.Validity.Model.runtime_mask
      (Normalized.suffix_footprint
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          aligned.(aligned_net_suffix))) ⊆ ambient ->
    forall continuation : mask_cont,
    ((Normalized.Validity.global_world_context atoms ∗
      Normalized.Validity.VSemantics.S.interp_assertion
        (Leaf.predicates atoms) runtime formals binders atoms post ∗
      Normalized.Validity.World.access_stack_interp atoms ambient stack_out) ⊢
      continuation
        (Normalized.Validity.Model.active_runtime_mask ambient exit)) ->
    (Normalized.Validity.global_world_context atoms ∗
     Normalized.Validity.VSemantics.S.interp_assertion
       (Leaf.predicates atoms) runtime formals binders atoms pre ∗
     Normalized.Validity.World.access_stack_interp atoms ambient stack_in) ⊢
    trace_runtime_cps_wp
      (RuntimeAdapter.traced_net_source _ aligned.(aligned_net_normal))
      runtime ambient continuation.

(** Exactly the trusted-language evidence erased by certificate-only trace
    normalization.  Ordinary access and control nodes contribute no premise;
    a trusted atomic chunk retains the module boundary declared by Raven. *)
Fixpoint certificate_runtime_trusted
    {cost Γ fuel entry statement exit}
    (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
      entry statement exit) : Prop :=
  match certificate in RuntimeAdapter.Atomicity.analysis_certificate
      _ Γ' _ _ _ _ return Prop with
  | RuntimeAdapter.Atomicity.CertSequence _ _ _ _ _ _ _ _ _ _ first second =>
      certificate_runtime_trusted first /\ certificate_runtime_trusted second
  | RuntimeAdapter.Atomicity.CertConditional _ _ _ _ _ _ _ _ _ _ first second
      _ _ =>
      certificate_runtime_trusted first /\ certificate_runtime_trusted second
  | RuntimeAdapter.Atomicity.CertAtomic _ Γ' _ _ _ body _ _ _ _ _ _ =>
      Contracts.trusted_atomic Γ' body
  | _ => True
  end.

Fixpoint suffix_runtime_trusted
    {cost Γ entry exit}
    (suffix : RuntimeAdapter.certificate_suffix cost Γ entry exit) : Prop :=
  match suffix with
  | RuntimeAdapter.SuffixDone _ => True
  | RuntimeAdapter.SuffixCons certificate rest =>
      certificate_runtime_trusted certificate /\ suffix_runtime_trusted rest
  end.

Lemma aligned_certificate_runtime_trusted
    {cost Γ F Δ fuel entry statement exit}
    {pre post : Runtime.Translation.Assertions.assertion Γ F Δ}
    {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
      entry statement exit}
    {derivation : Normalized.Validity.Certified.Rules.RavenHoareTriple pre
      statement (RuntimeAdapter.Atomicity.analysis_mask entry)
      (RuntimeAdapter.Atomicity.analysis_mask exit) post} :
  Normalized.Validity.Certified.certificate_hoare_aligned cost certificate
    derivation ->
  certificate_runtime_trusted certificate.
Proof.
  intros Haligned. induction Haligned; simpl; auto.
Qed.

Lemma aligned_suffix_runtime_trusted
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (suffix : Normalized.Validity.aligned_operational_suffix cost Γ F Δ entry
      pre stack_in exit post stack_out) :
  suffix_runtime_trusted
    (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
      suffix).
Proof.
  induction suffix; simpl; first done.
  split; last exact IHsuffix.
  exact (aligned_certificate_runtime_trusted
    (derivation := derivation) aligned).
Qed.

Lemma resource_aligned_certificate_runtime_trusted
    {cost Γ F Δ fuel entry statement exit}
    {pre post : Runtime.Translation.Assertions.assertion Γ F Δ}
    {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
      entry statement exit}
    {derivation : Normalized.Validity.Certified.Rules.RavenResourceTriple
      pre statement post} :
  Normalized.Validity.Certified.resource_certificate_hoare_aligned
    cost certificate derivation ->
  certificate_runtime_trusted certificate.
Proof.
  intros Haligned. induction Haligned; simpl; auto.
Qed.

Lemma resource_aligned_suffix_runtime_trusted
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (suffix : Normalized.Validity.resource_aligned_operational_suffix
      cost Γ F Δ entry pre stack_in exit post stack_out) :
  suffix_runtime_trusted
    (resource_certificate_suffix_of_operational_suffix suffix).
Proof.
  induction suffix; simpl; first done.
  split; last exact IHsuffix.
  exact (resource_aligned_certificate_runtime_trusted
    (derivation := derivation) aligned).
Qed.

Lemma resource_singleton_normalization_source
    {cost} {Γ F Δ : typed_core.TypedCore.context}
    {fuel entry statement exit pre post stack_in stack_out}
    (certificate : RuntimeAdapter.Atomicity.analysis_certificate
      cost Γ fuel entry statement exit)
    (derivation : Normalized.Validity.Certified.Rules.RavenResourceTriple
      pre statement post)
    (aligned : Normalized.Validity.Certified.resource_certificate_hoare_aligned
      cost certificate derivation)
    (lifo : RuntimeAdapter.Atomicity.lifo_certificate
      certificate stack_in stack_out) :
  @resource_certificate_suffix_of_operational_suffix cost Γ F Δ
    entry pre stack_in exit post stack_out
    (Normalized.Validity.resource_aligned_singleton_suffix certificate
      derivation aligned lifo) = RuntimeAdapter.singleton_suffix certificate.
Proof. reflexivity. Qed.

Lemma resource_sequence_expansion_normalization_source
    {cost} {Γ F Δ : typed_core.TypedCore.context}
    {fuel state statement first middle second next final
      pre middle_assertion next_assertion post
      stack_in stack_middle stack_next stack_out}
    (view : Runtime.RegionSyntax.view statement =
      typed_analysis_view.TypedAnalysisView.ViewSequence first second)
    (first_certificate : RuntimeAdapter.Atomicity.analysis_certificate
      cost Γ fuel state first middle)
    (second_certificate : RuntimeAdapter.Atomicity.analysis_certificate
      cost Γ fuel middle second next)
    (first_derivation : Normalized.Validity.Certified.Rules.RavenResourceTriple
      pre first middle_assertion)
    (second_derivation : Normalized.Validity.Certified.Rules.RavenResourceTriple
      middle_assertion second next_assertion)
    (first_aligned :
      Normalized.Validity.Certified.resource_certificate_hoare_aligned cost
        first_certificate first_derivation)
    (second_aligned :
      Normalized.Validity.Certified.resource_certificate_hoare_aligned cost
        second_certificate second_derivation)
    (first_lifo : RuntimeAdapter.Atomicity.lifo_certificate
      first_certificate stack_in stack_middle)
    (second_lifo : RuntimeAdapter.Atomicity.lifo_certificate
      second_certificate stack_middle stack_next)
    (rest : Normalized.Validity.resource_aligned_operational_suffix
      cost Γ F Δ next next_assertion stack_next final post stack_out) :
  @resource_certificate_suffix_of_operational_suffix cost Γ F Δ
    state pre stack_in final post stack_out
    (Normalized.Validity.expand_resource_aligned_sequence_suffix view
      first_certificate second_certificate first_derivation second_derivation
      first_aligned second_aligned first_lifo second_lifo rest) =
  RuntimeAdapter.SuffixCons first_certificate
    (RuntimeAdapter.SuffixCons second_certificate
      (@resource_certificate_suffix_of_operational_suffix cost Γ F Δ
        next next_assertion stack_next final post stack_out rest)).
Proof. reflexivity. Qed.

Lemma suffix_expands_runtime_trusted
    {cost Γ entry exit flat source}
    (expansion : RuntimeAdapter.suffix_expands cost Γ entry exit flat source) :
  suffix_runtime_trusted source -> suffix_runtime_trusted flat.
Proof.
  induction expansion; simpl; intros Htrusted.
  - exact Htrusted.
  - destruct Htrusted as [[Hfirst Hsecond] Hrest].
    repeat split; assumption.
  - destruct Htrusted as [Hhead Hsource]. split; first exact Hhead.
    now apply IHexpansion.
  - apply IHexpansion1. now apply IHexpansion2.
Qed.

Fixpoint trace_runtime_trusted
    {cost Γ entry exit mode tail stack_out source tree}
    (trace : RuntimeAdapter.net_trace cost Γ entry exit mode tail stack_out
      source tree) : Prop :=
  match trace with
  | @RuntimeAdapter.TraceDoneNet _ _ _ _ => True
  | @RuntimeAdapter.TraceDoneFocused _ _ _ _ _ => True
  | @RuntimeAdapter.TraceChunk _ _ _ _ _ _ _ _ _ certificate _ _ _ _ Hrest =>
      certificate_runtime_trusted certificate /\ trace_runtime_trusted Hrest
  | @RuntimeAdapter.TraceFocusedPrefix _ _ _ _ _ _ _ _ _ _ certificate _ _
      _ _ _ Hrest =>
      certificate_runtime_trusted certificate /\ trace_runtime_trusted Hrest
  | @RuntimeAdapter.TraceAccess _ _ _ _ _ _ _ _ _ _ certificate _ _ _ _ _
      Hbody =>
      certificate_runtime_trusted certificate /\ trace_runtime_trusted Hbody
  | @RuntimeAdapter.TraceNestedAccess _ _ _ _ _ _ _ _ _ _ _ certificate _ _
      _ _ _ Hbody =>
      certificate_runtime_trusted certificate /\ trace_runtime_trusted Hbody
  | @RuntimeAdapter.TraceClose _ _ _ _ _ _ _ _ _ _ certificate _ _ _ _ _
      Hrest =>
      certificate_runtime_trusted certificate /\ trace_runtime_trusted Hrest
  | @RuntimeAdapter.TraceFocusedClose _ _ _ _ _ _ _ _ _ _ certificate _ _ _
      _ _ Hrest =>
      certificate_runtime_trusted certificate /\ trace_runtime_trusted Hrest
  | @RuntimeAdapter.TraceConditional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ Hthen Helse Hrest =>
      trace_runtime_trusted Hthen /\ trace_runtime_trusted Helse /\
        trace_runtime_trusted Hrest
  | @RuntimeAdapter.TraceFocusedConditional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ Hthen Helse Hrest =>
      trace_runtime_trusted Hthen /\ trace_runtime_trusted Helse /\
        trace_runtime_trusted Hrest
  | @RuntimeAdapter.TraceFocusedConditionalContinue _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ Hthen Helse Hrest =>
      trace_runtime_trusted Hthen /\ trace_runtime_trusted Helse /\
        trace_runtime_trusted Hrest
  | @RuntimeAdapter.TraceExpansion _ _ _ _ _ _ _ _ _ _ _ Hflat =>
      trace_runtime_trusted Hflat
  end.

Lemma trace_runtime_trusted_of_suffix
    {cost Γ entry exit mode tail stack_out source tree}
    (trace : RuntimeAdapter.net_trace cost Γ entry exit mode tail stack_out
      source tree) :
  suffix_runtime_trusted source -> trace_runtime_trusted trace.
Proof.
  induction trace; simpl; intros Htrusted; try done.
  - destruct Htrusted as [Htrusted_head Hrest].
    split; [exact Htrusted_head|]. now apply IHtrace.
  - destruct Htrusted as [Htrusted_head Hrest].
    split; [exact Htrusted_head|]. now apply IHtrace.
  - destruct Htrusted as [Htrusted_head Hrest].
    split; [exact Htrusted_head|]. now apply IHtrace.
  - destruct Htrusted as [Htrusted_head Hrest].
    split; [exact Htrusted_head|]. now apply IHtrace.
  - destruct Htrusted as [Htrusted_head Hrest].
    split; [exact Htrusted_head|]. now apply IHtrace.
  - destruct Htrusted as [Htrusted_head Hrest].
    split; [exact Htrusted_head|]. now apply IHtrace.
  - destruct Htrusted as [[Hthen Helse] Hrest].
    split; [apply IHtrace1; simpl; auto|].
    split; [apply IHtrace2; simpl; auto|].
    now apply IHtrace3.
  - destruct Htrusted as [[Hthen Helse] Hrest].
    split; [apply IHtrace1; simpl; auto|].
    split; [apply IHtrace2; simpl; auto|].
    now apply IHtrace3.
  - destruct Htrusted as [[Hthen Helse] Hrest].
    split; [apply IHtrace1; simpl; auto|].
    split; [apply IHtrace2; simpl; auto|].
    now apply IHtrace3.
  - apply IHtrace. eapply suffix_expands_runtime_trusted; eauto.
Qed.

Definition resource_aligned_trace_runtime_trusted
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (aligned : @resource_aligned_normalized_trace cost Γ F Δ entry pre
      stack_in exit post stack_out) : Prop :=
  trace_runtime_trusted
    (RuntimeAdapter.traced_net_source _ aligned.(resource_net_normal)).

Theorem resource_aligned_trace_runtime_trusted_complete
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (aligned : @resource_aligned_normalized_trace cost Γ F Δ entry pre
      stack_in exit post stack_out) :
  resource_aligned_trace_runtime_trusted aligned.
Proof.
  destruct aligned as [suffix normal]. simpl.
  apply trace_runtime_trusted_of_suffix.
  apply resource_aligned_suffix_runtime_trusted.
Qed.

Lemma traced_chunk_region_runtime_refinement
    {cost Γ fuel entry statement exit stack_in stack_out certificate chunk}
    (source : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement exit
      stack_in stack_out certificate chunk)
    (runtime : Normalized.Validity.Model.stack_context Γ) ambient
    (post : iProp Resources.Σ) :
  certificate_runtime_trusted certificate ->
  Normalized.Validity.Execution.region_wp certificate runtime ambient post ⊢
    Normalized.Validity.aligned_runtime_region_wp certificate runtime ambient
      post.
Proof.
  intros Htrusted. destruct source; simpl in *.
  - eapply Normalized.Validity.leaf_operation_runtime_refinement_total; eauto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct statement; simpl in view; try discriminate.
    inversion view; subst. simpl in *.
    eapply Normalized.Validity.trusted_atomic_runtime_refinement; eauto.
Qed.

Theorem trace_iris_runtime_cps_refinement
    {cost Γ entry exit mode tail stack_out source tree}
    (trace : RuntimeAdapter.net_trace cost Γ entry exit mode tail stack_out
      source tree)
    (runtime : Normalized.Validity.Model.stack_context Γ) ambient
    (post : iProp Resources.Σ) :
  trace_runtime_trusted trace ->
  Normalized.trace_iris_wp trace runtime ambient post ⊢
    trace_runtime_cps_wp trace runtime ambient (fun _ => post).
Proof.
  revert post. induction trace; intros post Htrusted; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct Htrusted as [Htrusted_head Hrest].
    etrans; first eapply traced_chunk_region_runtime_refinement; eauto.
    apply aligned_runtime_region_wp_mono. now apply IHtrace.
  - destruct Htrusted as [Htrusted_head Hrest].
    etrans; first eapply traced_chunk_region_runtime_refinement; eauto.
    apply aligned_runtime_region_wp_mono. now apply IHtrace.
  - destruct Htrusted as [Htrusted_head Hbody].
    etrans; first eapply traced_chunk_region_runtime_refinement; eauto.
    apply aligned_runtime_region_wp_mono. now apply IHtrace.
  - destruct Htrusted as [Htrusted_head Hbody].
    etrans; first eapply traced_chunk_region_runtime_refinement; eauto.
    apply aligned_runtime_region_wp_mono. now apply IHtrace.
  - destruct Htrusted as [Htrusted_head Hrest].
    etrans; first eapply traced_chunk_region_runtime_refinement; eauto.
    apply aligned_runtime_region_wp_mono. now apply IHtrace.
  - destruct Htrusted as [Htrusted_head Hrest].
    etrans; first eapply traced_chunk_region_runtime_refinement; eauto.
    apply aligned_runtime_region_wp_mono. now apply IHtrace.
  - destruct Htrusted as [Hthen [Helse Hrest]].
    apply Normalized.Validity.Execution.Primitives.Interface.branch_mono.
    + etrans; first exact (IHtrace1 _ Hthen).
      apply trace_runtime_cps_wp_mono. intros _.
      exact (IHtrace3 _ Hrest).
    + etrans; first exact (IHtrace2 _ Helse).
      apply trace_runtime_cps_wp_mono. intros _.
      exact (IHtrace3 _ Hrest).
  - destruct Htrusted as [Hthen [Helse Hrest]].
    apply Normalized.Validity.Execution.Primitives.Interface.branch_mono.
    + etrans; first exact (IHtrace1 _ Hthen).
      apply trace_runtime_cps_wp_mono. intros _.
      exact (IHtrace3 _ Hrest).
    + etrans; first exact (IHtrace2 _ Helse).
      apply trace_runtime_cps_wp_mono. intros _.
      exact (IHtrace3 _ Hrest).
  - destruct Htrusted as [Hthen [Helse Hrest]].
    apply Normalized.Validity.Execution.Primitives.Interface.branch_mono.
    + etrans; first exact (IHtrace1 _ Hthen).
      apply trace_runtime_cps_wp_mono. intros _.
      exact (IHtrace3 _ Hrest).
    + etrans; first exact (IHtrace2 _ Helse).
      apply trace_runtime_cps_wp_mono. intros _.
      exact (IHtrace3 _ Hrest).
  - now apply IHtrace.
Qed.

Theorem aligned_trace_structured_cps_valid_from_trust
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (aligned : @aligned_normalized_trace cost Γ F Δ entry pre stack_in exit post
      stack_out) :
  trace_runtime_trusted
    (RuntimeAdapter.traced_net_source _ aligned.(aligned_net_normal)) ->
  aligned_trace_structured_cps_valid aligned.
Proof.
  destruct aligned as [suffix normal]. simpl.
  intros Htrusted Hwf runtime formals binders atoms ambient Henvelope
    continuation Hpost.
  pose proof (Normalized.aligned_trace_cps_valid_complete suffix normal) as
    Hlogical.
  iIntros "Hresources".
  iPoseProof (Hlogical Hwf runtime formals binders atoms ambient Henvelope
    (continuation
      (Normalized.Validity.Model.active_runtime_mask ambient exit)) Hpost
    with "Hresources") as "Hlogical".
  iPoseProof (trace_iris_runtime_cps_refinement
    (RuntimeAdapter.traced_net_source _ normal) runtime ambient
    (continuation
      (Normalized.Validity.Model.active_runtime_mask ambient exit)) Htrusted
    with "Hlogical") as "Hruntime".
  iApply (trace_runtime_cps_wp_terminal_mono with "Hruntime").
  reflexivity.
Qed.

Theorem aligned_trace_structured_cps_valid_complete
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (aligned : @aligned_normalized_trace cost Γ F Δ entry pre stack_in exit post
      stack_out) :
  aligned_trace_structured_cps_valid aligned.
Proof.
  apply aligned_trace_structured_cps_valid_from_trust.
  apply trace_runtime_trusted_of_suffix.
  apply aligned_suffix_runtime_trusted.
Qed.

Theorem resource_aligned_trace_structured_cps_valid_complete
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (aligned : @resource_aligned_normalized_trace cost Γ F Δ entry pre
      stack_in exit post stack_out) :
  resource_aligned_trace_structured_cps_valid aligned.
Proof.
  intros _ Hprocedure_cost Hwf runtime formals binders atoms ambient Henvelope
    continuation Hpost.
  pose proof (Normalized.resource_aligned_trace_cps_valid_complete
    aligned.(resource_net_suffix) aligned.(resource_net_normal)) as Hlogical.
  iIntros "Hresources".
  iPoseProof (Hlogical Hprocedure_cost Hwf runtime formals binders atoms
    ambient Henvelope
    (continuation
      (Normalized.Validity.Model.active_runtime_mask ambient exit)) Hpost
    with "Hresources") as "Hlogical".
  iPoseProof (trace_iris_runtime_cps_refinement
    (RuntimeAdapter.traced_net_source _ aligned.(resource_net_normal))
    runtime ambient
    (continuation
      (Normalized.Validity.Model.active_runtime_mask ambient exit))
    (resource_aligned_trace_runtime_trusted_complete aligned)
    with "Hlogical") as "Hruntime".
  iApply (trace_runtime_cps_wp_terminal_mono with "Hruntime").
  reflexivity.
Qed.

Theorem aligned_suffix_has_structured_cps_valid
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (suffix : Normalized.Validity.aligned_operational_suffix cost Γ F Δ entry
      pre stack_in exit post stack_out) :
  RuntimeAdapter.Atomicity.state_wf entry ->
  RuntimeAdapter.Atomicity.access_stack_consistent
    (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
  exists aligned : @aligned_normalized_trace cost Γ F Δ entry pre stack_in exit post
      stack_out,
    aligned_trace_structured_cps_valid aligned.
Proof.
  intros Hwf Hstack.
  destruct (normalize_aligned_net_trace suffix Hwf Hstack) as [aligned _].
  exists aligned. apply aligned_trace_structured_cps_valid_complete.
Qed.

Theorem resource_suffix_has_structured_cps_valid
    {cost Γ F Δ entry pre stack_in exit post stack_out}
    (suffix : Normalized.Validity.resource_aligned_operational_suffix
      cost Γ F Δ entry pre stack_in exit post stack_out) :
  RuntimeAdapter.Atomicity.state_wf entry ->
  RuntimeAdapter.Atomicity.access_stack_consistent
    (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
  exists aligned : @resource_aligned_normalized_trace cost Γ F Δ entry pre
      stack_in exit post stack_out,
    resource_aligned_trace_structured_cps_valid aligned.
Proof.
  intros Hwf Hstack.
  destruct (normalize_resource_aligned_net_trace suffix Hwf Hstack)
    as [aligned _].
  exists aligned. apply resource_aligned_trace_structured_cps_valid_complete.
Qed.

(** The first concrete leaves needed by a later normalized-trace induction.
    These deliberately stop at one certificate chunk: normalizing a suffix
    changes only the grouping of such chunks, while the actual sequence and
    conditional composition needs its own continuation-sensitive proof. *)
Module ConcreteChunks.
  Module Validity := Normalized.Validity.

  Local Notation iProp := (iProp Resources.Σ).
  Import Runtime.IR.Core Runtime.IR Runtime.Translation.Assertions.

  Lemma ordinary_leaf_runtime_refinement
      {Γ F Δ cost entry statement exit}
      (view : Runtime.RegionSyntax.view statement =
        typed_analysis_view.TypedAnalysisView.ViewLeaf)
      (step : RuntimeAdapter.Atomicity.take_step (cost Γ statement) entry = inr exit)
      stack (pre post : Runtime.Translation.Assertions.assertion Γ F Δ)
      (derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post)
      runtime formals binders atoms ambient
      (Hactive : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.analysis_mask exit) ⊆
        Validity.Model.active_runtime_mask ambient entry) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack) ⊢
    Validity.translated_runtime_wp runtime ambient entry exit statement
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       Validity.World.access_stack_interp atoms ambient stack).
  Proof.
    apply (Validity.aligned_ordinary_leaf_runtime_valid (cost := cost));
      assumption.
  Qed.

  (** Resource-proof concrete-leaf bridge.  The runtime cost witness is
      threaded at the trace boundary together with the resource procedure
      effect witness; only the latter is consumed by an ordinary leaf. *)
  Lemma resource_ordinary_leaf_runtime_refinement
      {Γ F Δ cost entry statement exit}
      (view : Runtime.RegionSyntax.view statement =
        typed_analysis_view.TypedAnalysisView.ViewLeaf)
      (step : RuntimeAdapter.Atomicity.take_step (cost Γ statement) entry =
        inr exit)
      stack (pre post : Runtime.Translation.Assertions.assertion Γ F Δ)
      (derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post)
      (Hruntime_cost : Validity.Model.runtime_cost_model_sound cost)
      (Hprocedure_cost : Validity.Certified.procedure_cost_model_sound cost)
      runtime formals binders atoms ambient
      (Hactive : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.analysis_mask exit) ⊆
        Validity.Model.active_runtime_mask ambient entry) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack) ⊢
    Validity.translated_runtime_wp runtime ambient entry exit statement
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       Validity.World.access_stack_interp atoms ambient stack).
  Proof.
    intros. eapply (Validity.resource_aligned_ordinary_leaf_runtime_valid
      (cost := cost)); eauto.
  Qed.

  (** Trusted atomic chunks use the body certificate only to establish the
      logical [region_wp] expected by the user-defined atomic module.  The
      resulting conclusion is already a concrete runtime WP for the atomic
      source statement. *)
  Lemma atomic_chunk_runtime_refinement
      {Γ F Δ fuel cost entry node body outer inner}
      (step : RuntimeAdapter.Atomicity.take_step
        RuntimeAdapter.Atomicity.AtomicStep entry =
        inr outer)
      (body_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        body inner)
      (open_equal : RuntimeAdapter.Atomicity.analysis_open inner =
        RuntimeAdapter.Atomicity.analysis_open outer)
      (stack : list RuntimeAdapter.Atomicity.access_marker)
      (pre post : Runtime.Translation.Assertions.assertion Γ F Δ)
      (trusted : Contracts.trusted_atomic Γ body)
      (body_valid : Validity.certificate_semantically_valid
        (stack_in := stack) (stack_out := stack) (pre := pre) (post := post)
        body_certificate) :
    forall runtime formals binders atoms ambient,
      Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint
          (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel entry (TAtomic node body)
            body outer inner eq_refl step body_certificate open_equal)) ⊆ ambient ->
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms pre ∗
       Validity.World.access_stack_interp atoms ambient stack) ⊢
      Validity.translated_runtime_wp runtime ambient entry
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask inner)
          (RuntimeAdapter.Atomicity.analysis_open inner)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer ||
            RuntimeAdapter.Atomicity.analysis_step_taken inner)
          (RuntimeAdapter.Atomicity.analysis_in_atomic outer))
        (TAtomic node body)
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms post ∗
         Validity.World.access_stack_interp atoms ambient stack).
  Proof.
    intros runtime formals binders atoms ambient Henvelope.
    have Hbody_envelope : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint body_certificate) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      simpl. set_solver. }
    iIntros "Hresources".
    iApply (Validity.trusted_atomic_runtime_refinement body_certificate runtime
      ambient _ trusted step open_equal).
    iApply (body_valid runtime formals binders atoms ambient Hbody_envelope).
    iExact "Hresources".
  Qed.

  (** Conditional trace refinement.  Both normalized arms are required to
      refine the same postcondition, and the static branch facts are threaded
      through the shared continuation.  The runtime conditional transport
      then reuses the analyzer join state; in particular, no branch-specific
      active-mask equality is guessed by the trace proof. *)
  Lemma conditional_trace_runtime_refinement
      {Γ F Δ node state then_exit else_exit}
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env)
      (store : Runtime.IR.Core.symbolic_store Γ F Δ)
      (frame : iProp)
      (condition : Runtime.IR.pexpr Γ typed_core.TypedCore.TBool)
      (ambient : coPset) (then_branch else_branch : Runtime.IR.stmt Γ)
      (then_wp else_wp post : iProp)
      (then_refine : then_wp ⊢
        Validity.translated_runtime_wp runtime ambient state then_exit
          then_branch post)
      (else_refine : else_wp ⊢
        Validity.translated_runtime_wp runtime ambient state else_exit
          else_branch post)
      (Hthen : (Validity.Model.stack_own Γ runtime
          (Runtime.Translation.interp_store formals binders atoms store) ∗
          frame ∗ ⌜Runtime.IR.Core.interp_expr formals binders atoms
            (Runtime.Validation.Hoare.symbolize_expr store condition) =
            Some (Runtime.IR.Core.VBool true)⌝) ⊢ then_wp)
      (Helse : (Validity.Model.stack_own Γ runtime
          (Runtime.Translation.interp_store formals binders atoms store) ∗
          frame ∗ ⌜Runtime.IR.Core.interp_expr formals binders atoms
            (Runtime.Validation.Hoare.symbolize_expr store condition) <>
            Some (Runtime.IR.Core.VBool true)⌝) ⊢ else_wp)
      (open_equal : RuntimeAdapter.Atomicity.analysis_open then_exit =
        RuntimeAdapter.Atomicity.analysis_open else_exit) :
      (Validity.Model.stack_own Γ runtime
        (Runtime.Translation.interp_store formals binders atoms store) ∗
        frame) ⊢
      Validity.translated_runtime_wp runtime ambient state
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask then_exit ∩
            RuntimeAdapter.Atomicity.analysis_mask else_exit)
          (RuntimeAdapter.Atomicity.analysis_open then_exit)
          (RuntimeAdapter.Atomicity.analysis_step_taken then_exit ||
            RuntimeAdapter.Atomicity.analysis_step_taken else_exit)
          (RuntimeAdapter.Atomicity.analysis_in_atomic then_exit))
        (Runtime.IR.TIf node condition then_branch else_branch) post.
  Proof.
    eapply (Validity.translated_runtime_wp_if_total_join
      runtime formals binders atoms store ambient state node condition
      then_branch else_branch then_exit else_exit post frame open_equal).
    - intros Hcondition.
      iIntros "[Hstack Hframe]".
      iApply then_refine.
      iApply Hthen. iFrame. iPureIntro. exact Hcondition.
    - intros Hcondition.
      iIntros "[Hstack Hframe]".
      iApply else_refine.
      iApply Helse. iFrame. iPureIntro.
      intros Heq. rewrite Hcondition in Heq. discriminate.
  Qed.

  (** The [AlignedConditional] constructor supplies branch derivations from
      these two interpreted assertions.  Keeping the world and access-stack
      resources in the frame passed to the total-join theorem is essential:
      an ordinary conditional and a focused conditional differ only in that
      final [access] resource.  Thus the same lemma closes both trace cases
      without reconstructing symbolic guard entailments at each caller. *)
  Lemma aligned_conditional_interpreted_runtime_refinement
      {Γ F Δ node state then_exit else_exit}
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env)
      (store : Runtime.IR.Core.symbolic_store Γ F Δ)
      (frame : Runtime.Translation.Assertions.assertion Γ F Δ)
      (condition : Runtime.IR.pexpr Γ typed_core.TypedCore.TBool)
      (ambient : coPset) (then_branch else_branch : Runtime.IR.stmt Γ)
      (access post : iProp)
      (then_refine :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms
           (AAnd (AStack store)
             (AAnd frame
               (AExpr (Runtime.Validation.Hoare.symbolize_expr store
                 condition)))) ∗
         access) ⊢
        Validity.translated_runtime_wp runtime ambient state then_exit
          then_branch post)
      (else_refine :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms
           (AAnd (AStack store)
             (AAnd frame
               (AExpr (EUnOp UNot
                 (Runtime.Validation.Hoare.symbolize_expr store
                   condition))))) ∗
         access) ⊢
        Validity.translated_runtime_wp runtime ambient state else_exit
          else_branch post)
      (open_equal : RuntimeAdapter.Atomicity.analysis_open then_exit =
        RuntimeAdapter.Atomicity.analysis_open else_exit) :
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms (AAnd (AStack store) frame) ∗
       access) ⊢
      Validity.translated_runtime_wp runtime ambient state
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask then_exit ∩
            RuntimeAdapter.Atomicity.analysis_mask else_exit)
          (RuntimeAdapter.Atomicity.analysis_open then_exit)
          (RuntimeAdapter.Atomicity.analysis_step_taken then_exit ||
            RuntimeAdapter.Atomicity.analysis_step_taken else_exit)
          (RuntimeAdapter.Atomicity.analysis_in_atomic then_exit))
        (Runtime.IR.TIf node condition then_branch else_branch) post.
  Proof.
    etrans; last eapply (Validity.translated_runtime_wp_if_total_join
      runtime formals binders atoms store ambient state node condition
      then_branch else_branch then_exit else_exit post
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms frame ∗ access) open_equal).
    - iIntros "[#Hworld [[Hstack Hframe] Haccess]]".
      simpl. iFrame "Hstack Hworld Hframe Haccess".
    - intros Hcondition.
      iIntros "[Hstack [#Hworld [Hframe Haccess]]]".
      iApply then_refine. simpl. iFrame.
      iSplit; [iFrame "#"|]. iPureIntro. exact Hcondition.
    - intros Hcondition.
      iIntros "[Hstack [#Hworld [Hframe Haccess]]]".
      iApply else_refine. simpl. iFrame.
      iSplit; [iFrame "#"|]. iPureIntro.
      rewrite Hcondition. reflexivity.
  Qed.
End ConcreteChunks.

(** Concrete endpoint refinements for the three invariant-access nodes.
    The CPS trace interpreter will use the access-stack versions internally,
    but these endpoint lemmas record that an individual erased source node is
    exactly its ambient-mask-changing [translated_runtime_wp]. *)
Module ConcreteAccessNodes.
  Module Validity := Normalized.Validity.

  Local Notation iProp := (iProp Resources.Σ).
  Import Runtime.IR.Core Runtime.IR Runtime.Translation.Assertions.

  Lemma unfold_node_runtime_refinement
      {Γ F Δ node invariant arguments}
      (store : Runtime.IR.Core.symbolic_store Γ F Δ) body entry exit ambient rest
      (step : RuntimeAdapter.Atomicity.open_invariant invariant entry = inr exit)
      (Hnamespace :
        ↑(Resources.invariant_namespace invariant) ⊆
          Validity.Model.active_runtime_mask ambient entry)
      (instantiated : Contracts.instantiated_invariant Γ F Δ
        (Logic.invariant_args invariant) invariant
        (Runtime.Validation.Hoare.symbolize_expr_list store arguments) body)
      runtime formals binders atoms :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms
       (AAnd (AStack store)
         (AInvariant invariant
           (Runtime.Validation.Hoare.symbolize_expr_list store arguments))) ∗
     Validity.World.access_stack_interp atoms ambient rest) ⊢
    Validity.translated_runtime_wp runtime ambient entry exit
      (TUnfold node invariant arguments)
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms (AAnd (AStack store) body) ∗
       Validity.World.access_stack_interp atoms ambient
         ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: rest)).
  Proof.
    unfold Validity.translated_runtime_wp. simpl.
    exact (Validity.invariant_unfold_node_valid node invariant arguments store
      body entry exit ambient rest step Hnamespace instantiated runtime
      formals binders atoms).
  Qed.

  Lemma matched_fold_node_runtime_refinement
      {Γ F Δ node invariant arguments}
      (store : Runtime.IR.Core.symbolic_store Γ F Δ) body entry ambient outer_open rest
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hopen : invariant ∈ RuntimeAdapter.Atomicity.analysis_open entry)
      (Houter : invariant ∉ outer_open)
      (Hopen_eq : RuntimeAdapter.Atomicity.analysis_open entry =
        {[invariant]} ∪ outer_open)
      (instantiated : Contracts.instantiated_invariant Γ F Δ
        (Logic.invariant_args invariant) invariant
        (Runtime.Validation.Hoare.symbolize_expr_list store arguments) body)
      runtime formals binders atoms :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms (AAnd (AStack store) body) ∗
     Validity.World.access_stack_interp atoms ambient
       ((invariant, outer_open) :: rest)) ⊢
    Validity.translated_runtime_wp runtime ambient entry
      (RuntimeAdapter.Atomicity.fold_invariant invariant entry)
      (TFold node invariant arguments)
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms
         (AAnd (AStack store)
           (AInvariant invariant
             (Runtime.Validation.Hoare.symbolize_expr_list store arguments))) ∗
       Validity.World.access_stack_interp atoms ambient rest).
  Proof.
    unfold Validity.translated_runtime_wp. simpl.
    exact (Validity.invariant_fold_node_valid node invariant arguments store
      body entry ambient outer_open rest Hwf Hopen Houter Hopen_eq instantiated
      runtime formals binders atoms).
  Qed.

  Lemma fresh_fold_node_runtime_refinement
      {Γ F Δ node invariant arguments}
      (store : Runtime.IR.Core.symbolic_store Γ F Δ) body entry ambient rest
      (Hfresh : invariant ∉ RuntimeAdapter.Atomicity.analysis_open entry)
      (Hnamespace :
        ↑(Resources.invariant_namespace invariant) ⊆
          Validity.Model.active_runtime_mask ambient entry)
      (instantiated : Contracts.instantiated_invariant Γ F Δ
        (Logic.invariant_args invariant) invariant
        (Runtime.Validation.Hoare.symbolize_expr_list store arguments) body)
      runtime formals binders atoms :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms (AAnd (AStack store) body) ∗
     Validity.World.access_stack_interp atoms ambient rest) ⊢
    Validity.translated_runtime_wp runtime ambient entry
      (RuntimeAdapter.Atomicity.fold_invariant invariant entry)
      (TFold node invariant arguments)
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms
         (AAnd (AStack store)
           (AInvariant invariant
             (Runtime.Validation.Hoare.symbolize_expr_list store arguments))) ∗
       Validity.World.access_stack_interp atoms ambient rest).
  Proof.
    unfold Validity.translated_runtime_wp. simpl.
    exact (Validity.invariant_fresh_fold_node_valid node invariant arguments
      store body entry ambient rest Hfresh Hnamespace instantiated runtime
      formals binders atoms).
  Qed.
End ConcreteAccessNodes.

(** Reification of the non-branching invariant-access path.  The unfold and
    matching fold are proof-only runtime nodes; consequently the only
    physical code in the bracket is the operational body suffix.  This is
    the exact slice to which [wp_atomic] applies.  A conditional body needs a
    separate arm-wise argument and is intentionally not hidden in this
    lemma. *)
Module ConcreteFocusedAccess.
  Module Validity := Normalized.Validity.

  Local Notation iProp := (iProp Resources.Σ).
  Import Runtime.IR.Core Runtime.IR Runtime.Translation.Assertions.

  Lemma nonconditional_access_body_runtime_refinement
      {cost Γ F Δ invariant arguments body entry opened before_close}
      (node : typed_core.TypedCore.node_id)
      (store : Runtime.IR.Core.symbolic_store Γ F Δ)
      (suffix : Validity.operational_suffix cost Γ opened before_close)
      (rest : list RuntimeAdapter.Atomicity.access_marker)
      (ambient : coPset)
      (step : RuntimeAdapter.Atomicity.open_invariant invariant entry =
        inr opened)
      (Hnamespace :
        ↑(Resources.invariant_namespace invariant) ⊆
          Validity.Model.active_runtime_mask ambient entry)
      (Hwf : RuntimeAdapter.Atomicity.state_wf before_close)
      (Hopen : invariant ∈
        RuntimeAdapter.Atomicity.analysis_open before_close)
      (Houter : invariant ∉ RuntimeAdapter.Atomicity.analysis_open entry)
      (Hopen_eq : RuntimeAdapter.Atomicity.analysis_open before_close =
        {[invariant]} ∪ RuntimeAdapter.Atomicity.analysis_open entry)
      (Hbody_open : RuntimeAdapter.Atomicity.analysis_open opened =
        RuntimeAdapter.Atomicity.analysis_open before_close)
      (instantiated : Contracts.instantiated_invariant Γ F Δ
        (Logic.invariant_args invariant) invariant
        (Runtime.Validation.Hoare.symbolize_expr_list store arguments) body)
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env)
      (final : iProp)
      (finalize :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms
           (AAnd (AStack store)
             (AInvariant invariant
               (Runtime.Validation.Hoare.symbolize_expr_list store arguments))) ∗
         Validity.World.access_stack_interp atoms ambient rest) ⊢ final)
      (body_refine :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms (AAnd (AStack store) body) ∗
         Validity.World.access_stack_interp atoms ambient
           ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: rest))
        ⊢
        Validity.operational_suffix_translated_wp suffix runtime ambient
          (Validity.global_world_context atoms ∗
           Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
             runtime formals binders atoms (AAnd (AStack store) body) ∗
           Validity.World.access_stack_interp atoms ambient
             ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: rest)))
      (Hatomic : forall statement,
        Validity.operational_suffix_runtime suffix runtime = Some statement ->
        @Atomic Runtime.LegacyLang.simp_lang WeaklyAtomic statement) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms
       (AAnd (AStack store)
         (AInvariant invariant
           (Runtime.Validation.Hoare.symbolize_expr_list store arguments))) ∗
     Validity.World.access_stack_interp atoms ambient rest) ⊢
    Validity.legacy_focused_operational_suffix_wp suffix runtime
      (Validity.Model.active_runtime_mask ambient entry) final.
  Proof.
    destruct (RuntimeAdapter.Atomicity.fold_open_invariant invariant
      before_close Hopen) as [_ Hfold_open].
    have Hclosed_open :
        RuntimeAdapter.Atomicity.analysis_open
          (RuntimeAdapter.Atomicity.fold_invariant invariant before_close) =
        RuntimeAdapter.Atomicity.analysis_open entry.
    { rewrite Hfold_open Hopen_eq. set_solver. }
    have Hclosed_active :
        Validity.Model.active_runtime_mask ambient
          (RuntimeAdapter.Atomicity.fold_invariant invariant before_close) =
        Validity.Model.active_runtime_mask ambient entry.
    { apply Validity.Model.active_runtime_mask_same_open. exact Hclosed_open. }
    iIntros "Hresources".
    iPoseProof (ConcreteAccessNodes.unfold_node_runtime_refinement
      (node := node) store body
      entry opened ambient rest step Hnamespace instantiated runtime formals
      binders atoms with "Hresources") as "Hopen".
    iApply (Validity.operational_suffix_translated_wp_atomic_mask_change
      suffix runtime ambient
      (Validity.Model.active_runtime_mask ambient entry) final Hbody_open
      Hatomic).
    iMod "Hopen" as "Hbody".
    iPoseProof (body_refine with "Hbody") as "Hbody".
    iApply (Validity.runtime_option_wp_mono with "Hbody").
    iIntros "Hclose".
    iPoseProof (ConcreteAccessNodes.matched_fold_node_runtime_refinement
      (node := node) store
      body before_close ambient (RuntimeAdapter.Atomicity.analysis_open entry)
      rest Hwf Hopen Houter Hopen_eq instantiated runtime formals binders atoms
      with "Hclose") as "Hfinal".
    iMod "Hfinal". rewrite Hclosed_active. iModIntro.
    iApply finalize. iExact "Hfinal".
  Qed.

  (** A physical conditional inside an open invariant is reified arm by arm.
      Both arms retain the same open-access stack and discharge the same
      translated suffix continuation.  Thus the conditional itself remains
      outside the single-step atomic-mask bracket used by the linear access
      lemma above. *)
  Lemma focused_conditional_shared_rest_runtime_refinement
      {cost Γ F Δ node state then_exit else_exit rest_exit}
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env)
      (store : Runtime.IR.Core.symbolic_store Γ F Δ)
      (frame : Runtime.Translation.Assertions.assertion Γ F Δ)
      (condition : Runtime.IR.pexpr Γ typed_core.TypedCore.TBool)
      (ambient : coPset) (then_branch else_branch : Runtime.IR.stmt Γ)
      (stack : list RuntimeAdapter.Atomicity.access_marker)
      (rest_suffix : Validity.operational_suffix cost Γ
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask then_exit ∩
            RuntimeAdapter.Atomicity.analysis_mask else_exit)
          (RuntimeAdapter.Atomicity.analysis_open then_exit)
          (RuntimeAdapter.Atomicity.analysis_step_taken then_exit ||
            RuntimeAdapter.Atomicity.analysis_step_taken else_exit)
          (RuntimeAdapter.Atomicity.analysis_in_atomic then_exit)) rest_exit)
      (final : iProp)
      (then_refine :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms
           (AAnd (AStack store)
             (AAnd frame
               (AExpr (Runtime.Validation.Hoare.symbolize_expr store
                 condition)))) ∗
         Validity.World.access_stack_interp atoms ambient stack) ⊢
        Validity.translated_runtime_wp runtime ambient state then_exit
          then_branch
          (Validity.operational_suffix_translated_wp rest_suffix runtime
            ambient final))
      (else_refine :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms
           (AAnd (AStack store)
             (AAnd frame
               (AExpr (EUnOp UNot
                 (Runtime.Validation.Hoare.symbolize_expr store
                   condition))))) ∗
         Validity.World.access_stack_interp atoms ambient stack) ⊢
        Validity.translated_runtime_wp runtime ambient state else_exit
          else_branch
          (Validity.operational_suffix_translated_wp rest_suffix runtime
            ambient final))
      (open_equal : RuntimeAdapter.Atomicity.analysis_open then_exit =
        RuntimeAdapter.Atomicity.analysis_open else_exit) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms (AAnd (AStack store) frame) ∗
     Validity.World.access_stack_interp atoms ambient stack) ⊢
    Validity.translated_runtime_wp runtime ambient state
      (RuntimeAdapter.Atomicity.AnalysisState
        (RuntimeAdapter.Atomicity.analysis_mask then_exit ∩
          RuntimeAdapter.Atomicity.analysis_mask else_exit)
        (RuntimeAdapter.Atomicity.analysis_open then_exit)
        (RuntimeAdapter.Atomicity.analysis_step_taken then_exit ||
          RuntimeAdapter.Atomicity.analysis_step_taken else_exit)
        (RuntimeAdapter.Atomicity.analysis_in_atomic then_exit))
      (TIf node condition then_branch else_branch)
      (Validity.operational_suffix_translated_wp rest_suffix runtime ambient
        final).
  Proof.
    eapply ConcreteChunks.aligned_conditional_interpreted_runtime_refinement;
      eauto.
  Qed.

  Lemma focused_suffix_as_translated_arm
      {cost Γ entry exit}
      (suffix : Validity.operational_suffix cost Γ entry exit)
      (runtime : Validity.Model.stack_context Γ) ambient
      (statement : Runtime.IR.stmt Γ) (post : iProp)
      (Hentry : Validity.Model.active_runtime_mask ambient entry =
        Validity.Model.active_runtime_mask ambient exit)
      (Hruntime : Validity.Model.runtime_stmt
          (Validity.Model.runtime_names Γ runtime)
          (Validity.Model.runtime_stack_id Γ runtime) statement =
        Validity.operational_suffix_runtime suffix runtime) :
    Validity.legacy_focused_operational_suffix_wp suffix runtime
      (Validity.Model.active_runtime_mask ambient entry) post ⊣⊢
    Validity.translated_runtime_wp runtime ambient entry exit statement post.
  Proof.
    unfold Validity.legacy_focused_operational_suffix_wp,
      Validity.translated_runtime_wp.
    rewrite Hruntime. now rewrite Hentry.
  Qed.

  (** Go/no-go vertical slice for a focused conditional.  Each selected arm
      discharges its own invariant bracket; the concrete runtime equivalence
      then moves the proof-only unfold/fold pair through the conditional. *)
  Lemma distributed_focused_conditional_runtime_refinement
      {cost Γ F Δ node unfold_node inner_node fold_node invariant
        unfold_arguments fold_arguments state then_exit else_exit}
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env)
      (store : Runtime.IR.Core.symbolic_store Γ F Δ)
      (frame : Runtime.Translation.Assertions.assertion Γ F Δ)
      (condition : Runtime.IR.pexpr Γ typed_core.TypedCore.TBool)
      (ambient : coPset) (then_branch else_branch : Runtime.IR.stmt Γ)
      (stack : list RuntimeAdapter.Atomicity.access_marker)
      (then_suffix : Validity.operational_suffix cost Γ state then_exit)
      (else_suffix : Validity.operational_suffix cost Γ state else_exit)
      (final : iProp)
      (Hthen_open : RuntimeAdapter.Atomicity.analysis_open state =
        RuntimeAdapter.Atomicity.analysis_open then_exit)
      (Helse_open : RuntimeAdapter.Atomicity.analysis_open state =
        RuntimeAdapter.Atomicity.analysis_open else_exit)
      (Hthen_runtime : Validity.Model.runtime_stmt
          (Validity.Model.runtime_names Γ runtime)
          (Validity.Model.runtime_stack_id Γ runtime)
          (Runtime.IR.TSeq unfold_node
            (Runtime.IR.TUnfold unfold_node invariant unfold_arguments)
            (Runtime.IR.TSeq inner_node then_branch
              (Runtime.IR.TFold fold_node invariant fold_arguments))) =
        Validity.operational_suffix_runtime then_suffix runtime)
      (Helse_runtime : Validity.Model.runtime_stmt
          (Validity.Model.runtime_names Γ runtime)
          (Validity.Model.runtime_stack_id Γ runtime)
          (Runtime.IR.TSeq unfold_node
            (Runtime.IR.TUnfold unfold_node invariant unfold_arguments)
            (Runtime.IR.TSeq inner_node else_branch
              (Runtime.IR.TFold fold_node invariant fold_arguments))) =
        Validity.operational_suffix_runtime else_suffix runtime)
      (then_refine :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms
           (AAnd (AStack store)
             (AAnd frame
               (AExpr (Runtime.Validation.Hoare.symbolize_expr store
                 condition)))) ∗
         Validity.World.access_stack_interp atoms ambient stack) ⊢
        Validity.legacy_focused_operational_suffix_wp then_suffix runtime
          (Validity.Model.active_runtime_mask ambient state) final)
      (else_refine :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms
           (AAnd (AStack store)
             (AAnd frame
               (AExpr (EUnOp UNot
                 (Runtime.Validation.Hoare.symbolize_expr store
                   condition))))) ∗
         Validity.World.access_stack_interp atoms ambient stack) ⊢
        Validity.legacy_focused_operational_suffix_wp else_suffix runtime
          (Validity.Model.active_runtime_mask ambient state) final)
      (open_equal : RuntimeAdapter.Atomicity.analysis_open then_exit =
        RuntimeAdapter.Atomicity.analysis_open else_exit) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms (AAnd (AStack store) frame) ∗
     Validity.World.access_stack_interp atoms ambient stack) ⊢
    Validity.translated_runtime_wp runtime ambient state
      (RuntimeAdapter.conditional_join then_exit else_exit)
      (Runtime.IR.TSeq unfold_node
        (Runtime.IR.TUnfold unfold_node invariant unfold_arguments)
        (Runtime.IR.TSeq inner_node
          (Runtime.IR.TIf node condition then_branch else_branch)
          (Runtime.IR.TFold fold_node invariant fold_arguments))) final.
  Proof.
    rewrite Validity.translated_runtime_wp_distribute_unfold_fold_if.
    eapply ConcreteChunks.aligned_conditional_interpreted_runtime_refinement;
      [| |exact open_equal].
    - etrans; first exact then_refine.
      rewrite (focused_suffix_as_translated_arm then_suffix runtime ambient
        _ final
        (Validity.Model.active_runtime_mask_same_open ambient state then_exit
          Hthen_open)
        Hthen_runtime). reflexivity.
    - etrans; first exact else_refine.
      rewrite (focused_suffix_as_translated_arm else_suffix runtime ambient
        _ final
        (Validity.Model.active_runtime_mask_same_open ambient state else_exit
          Helse_open)
        Helse_runtime). reflexivity.
  Qed.
End ConcreteFocusedAccess.

(** Ordinary normalized traces can be flattened independently of the focused
    proof exactly when they contain no access or branch node.  Expansion also
    records the operational equality needed to reassociate source sequences;
    this keeps the theorem independent of a particular cost-model sparsity
    proof. *)
Module ConcreteOrdinaryTrace.
  Module Validity := Normalized.Validity.

  Fixpoint source_runtime {cost Γ entry exit}
      (source : RuntimeAdapter.certificate_suffix cost Γ entry exit)
      (runtime : Validity.Model.stack_context Γ) :
      option Runtime.LegacyLang.runtime_stmt :=
    match source with
    | RuntimeAdapter.SuffixDone _ => None
    | RuntimeAdapter.SuffixCons certificate rest =>
        Validity.Model.combine_runtime_statements
          (Validity.certificate_runtime_statement certificate runtime)
          (source_runtime rest runtime)
    end.

  Definition source_translated_wp {cost Γ entry exit}
      (source : RuntimeAdapter.certificate_suffix cost Γ entry exit)
      (runtime : Validity.Model.stack_context Γ) ambient
      (post : iProp Resources.Σ) : iProp Resources.Σ :=
    Validity.runtime_option_wp
      (Validity.Model.active_runtime_mask ambient entry)
      (Validity.Model.active_runtime_mask ambient exit)
      (source_runtime source runtime) post.

  Lemma source_translated_wp_mono {cost Γ entry exit}
      (source : RuntimeAdapter.certificate_suffix cost Γ entry exit)
      (runtime : Validity.Model.stack_context Γ) ambient (P Q : iProp Resources.Σ) :
    (P ⊢ Q) ->
    source_translated_wp source runtime ambient P ⊢
      source_translated_wp source runtime ambient Q.
  Proof. intros HPQ. unfold source_translated_wp. apply Validity.runtime_option_wp_mono, HPQ. Qed.

  Lemma source_translated_wp_frame {cost Γ entry exit}
      (source : RuntimeAdapter.certificate_suffix cost Γ entry exit)
      (runtime : Validity.Model.stack_context Γ) ambient (post frame : iProp Resources.Σ) :
    source_translated_wp source runtime ambient post ∗ frame ⊢
      source_translated_wp source runtime ambient (post ∗ frame).
  Proof. unfold source_translated_wp. apply Validity.runtime_option_wp_frame. Qed.

  Lemma singleton_source_translated_wp
      {cost Γ fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (runtime : Validity.Model.stack_context Γ) ambient post :
    source_translated_wp (RuntimeAdapter.singleton_suffix certificate) runtime
      ambient post =
    Validity.translated_runtime_wp runtime ambient entry exit statement post.
  Proof.
    unfold source_translated_wp, Validity.translated_runtime_wp.
    simpl. unfold Validity.certificate_runtime_statement.
    destruct (Validity.Model.runtime_stmt
      (Validity.Model.runtime_names Γ runtime)
      (Validity.Model.runtime_stack_id Γ runtime) statement); reflexivity.
  Qed.

  Lemma translated_runtime_wp_prepend_source
      {cost Γ fuel entry statement middle exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement middle)
      (rest : RuntimeAdapter.certificate_suffix cost Γ middle exit)
      (runtime : Validity.Model.stack_context Γ) ambient post
      (Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open middle) :
    Validity.translated_runtime_wp runtime ambient entry middle statement
      (source_translated_wp rest runtime ambient post) ⊢
    source_translated_wp (RuntimeAdapter.SuffixCons certificate rest) runtime
      ambient post.
  Proof.
    unfold Validity.translated_runtime_wp, source_translated_wp.
    simpl. unfold Validity.certificate_runtime_statement,
      Validity.Model.active_runtime_mask.
    rewrite Hopen. apply Validity.runtime_option_wp_sequence.
  Qed.

  Lemma translated_head_prepend_source
      {cost Γ fuel entry statement middle exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement middle)
      (rest : RuntimeAdapter.certificate_suffix cost Γ middle exit)
      (runtime : Validity.Model.stack_context Γ) ambient
      (P Q R : iProp Resources.Σ)
      (Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open middle)
      (Hhead : P ⊢ Validity.translated_runtime_wp runtime ambient entry middle
        statement Q)
      (Hrest : Q ⊢ source_translated_wp rest runtime ambient R) :
    P ⊢ source_translated_wp (RuntimeAdapter.SuffixCons certificate rest)
      runtime ambient R.
  Proof.
    etrans; first exact Hhead.
    etrans.
    - apply Validity.translated_runtime_wp_mono. exact Hrest.
    - apply translated_runtime_wp_prepend_source. exact Hopen.
  Qed.

  (** Mask-direct variants of the two lemmas above, for seams where the Iris
      active mask at [entry] and [middle] is already known to coincide
      without [entry]'s and [middle]'s Raven-level [analysis_open] sets
      being equal (e.g. a branch's own analyzer exit and the shared
      conditional join, connected only via [conditional_join]'s definition
      and [open_equal], never by equating the two Raven states themselves).
      The proofs are identical to the [Hopen]-indexed versions except for
      which equation gets rewritten. *)
  Lemma translated_runtime_wp_prepend_source_mask
      {cost Γ fuel entry statement middle exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement middle)
      (rest : RuntimeAdapter.certificate_suffix cost Γ middle exit)
      (runtime : Validity.Model.stack_context Γ) ambient post
      (Hmask : Validity.Model.active_runtime_mask ambient entry =
        Validity.Model.active_runtime_mask ambient middle) :
    Validity.translated_runtime_wp runtime ambient entry middle statement
      (source_translated_wp rest runtime ambient post) ⊢
    source_translated_wp (RuntimeAdapter.SuffixCons certificate rest) runtime
      ambient post.
  Proof.
    unfold Validity.translated_runtime_wp, source_translated_wp.
    simpl. unfold Validity.certificate_runtime_statement.
    rewrite Hmask. apply Validity.runtime_option_wp_sequence.
  Qed.

  Lemma translated_head_prepend_source_mask
      {cost Γ fuel entry statement middle exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement middle)
      (rest : RuntimeAdapter.certificate_suffix cost Γ middle exit)
      (runtime : Validity.Model.stack_context Γ) ambient
      (P Q R : iProp Resources.Σ)
      (Hmask : Validity.Model.active_runtime_mask ambient entry =
        Validity.Model.active_runtime_mask ambient middle)
      (Hhead : P ⊢ Validity.translated_runtime_wp runtime ambient entry middle
        statement Q)
      (Hrest : Q ⊢ source_translated_wp rest runtime ambient R) :
    P ⊢ source_translated_wp (RuntimeAdapter.SuffixCons certificate rest)
      runtime ambient R.
  Proof.
    etrans; first exact Hhead.
    etrans.
    - apply Validity.translated_runtime_wp_mono. exact Hrest.
    - apply translated_runtime_wp_prepend_source_mask. exact Hmask.
  Qed.

  (** Certificate erasure preserves the concrete program assembled by the
      operational zipper.  This small correspondence is what lets the final
      trace theorem state its result using the original aligned suffix rather
      than its normalization-only certificate view. *)
  Lemma source_runtime_of_operational_suffix
      {cost Γ entry exit}
      (suffix : Validity.operational_suffix cost Γ entry exit)
      (runtime : Validity.Model.stack_context Γ) :
    source_runtime
      (Normalized.Erasure.certificate_suffix_of_operational_suffix suffix)
      runtime =
    Validity.operational_suffix_runtime suffix runtime.
  Proof.
    induction suffix; simpl; first reflexivity.
    now rewrite IHsuffix.
  Qed.

  Lemma source_runtime_of_aligned_operational_suffix
      {cost Γ F Δ entry pre stack_in exit post stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre
        stack_in exit post stack_out)
      (runtime : Validity.Model.stack_context Γ) :
    source_runtime
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
        suffix) runtime =
    Validity.operational_suffix_runtime
      (Validity.erase_aligned_operational_suffix suffix) runtime.
  Proof.
    apply source_runtime_of_operational_suffix.
  Qed.

  Lemma source_translated_wp_of_aligned_operational_suffix
      {cost Γ F Δ entry pre stack_in exit post_assertion stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre
        stack_in exit post_assertion stack_out)
      (runtime : Validity.Model.stack_context Γ) ambient post :
    source_translated_wp
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
        suffix) runtime ambient post =
    Validity.operational_suffix_translated_wp
      (Validity.erase_aligned_operational_suffix suffix) runtime ambient post.
  Proof.
    unfold source_translated_wp,
      Validity.operational_suffix_translated_wp.
    now rewrite source_runtime_of_aligned_operational_suffix.
  Qed.

  Definition physical_chunk
      {cost Γ fuel entry statement exit stack_in stack_out certificate chunk}
      (source : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        exit stack_in stack_out certificate chunk) : Prop :=
    match source with
    | @RuntimeAdapter.ChunkCertificateLeaf _ _ _ _ _ _ _ _ _ => True
    | @RuntimeAdapter.ChunkCertificateAtomic _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        True
    | _ => False
    end.

  Fixpoint flattenable
      {cost Γ entry exit mode tail stack_out source tree}
      (trace : RuntimeAdapter.net_trace cost Γ entry exit mode tail stack_out
        source tree) (runtime : Validity.Model.stack_context Γ) : Prop :=
    match trace with
    | @RuntimeAdapter.TraceDoneNet _ _ _ _ => True
    | @RuntimeAdapter.TraceChunk _ _ _ entry _ middle _ _ _ _ _ _ Hhead _
        rest =>
        physical_chunk Hhead /\
        RuntimeAdapter.Atomicity.analysis_open entry =
          RuntimeAdapter.Atomicity.analysis_open middle /\
        flattenable rest runtime
    | @RuntimeAdapter.TraceExpansion _ _ _ _ _ _ _ flat source _ expansion
        expanded =>
        flattenable expanded runtime /\
        source_runtime flat runtime = source_runtime source runtime
    | _ => False
    end.

  Lemma chunk_region_is_translated
      {cost Γ fuel entry statement exit stack certificate chunk}
      (source : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        exit stack stack certificate chunk)
      (runtime : Validity.Model.stack_context Γ) ambient (post : iProp Resources.Σ) :
    physical_chunk source ->
    Validity.aligned_runtime_region_wp certificate runtime ambient post ⊢
      Validity.translated_runtime_wp runtime ambient entry exit statement post.
  Proof.
    destruct source; simpl; intros Hphysical; try contradiction; reflexivity.
  Qed.

  Theorem flattenable_trace_runtime_refinement
      {cost Γ entry exit mode tail stack_out source tree}
      (trace : RuntimeAdapter.net_trace cost Γ entry exit mode tail stack_out
        source tree)
      (runtime : Validity.Model.stack_context Γ) ambient
      (post : iProp Resources.Σ) :
    flattenable trace runtime ->
    trace_runtime_cps_wp trace runtime ambient (fun _ => post) ⊢
      source_translated_wp source runtime ambient post.
  Proof.
    induction trace; simpl; intros Hflat; try contradiction.
    - iIntros "Hpost". iModIntro. iExact "Hpost".
    - destruct Hflat as [Hphysical [Hopen Hrest]].
      etrans.
      + apply aligned_runtime_region_wp_mono. exact (IHtrace Hrest).
      + etrans; first apply (chunk_region_is_translated Hhead _ _ _ Hphysical).
        unfold Validity.translated_runtime_wp, source_translated_wp.
        simpl. unfold Validity.Model.active_runtime_mask. rewrite Hopen.
        apply Validity.runtime_option_wp_sequence.
    - destruct Hflat as [Hflat Heq].
      etrans; first exact (IHtrace Hflat).
      unfold source_translated_wp. rewrite Heq.
      reflexivity.
  Qed.

  (** Closed assembly for the ordinary fragment of a normalized aligned
      suffix.  This is deliberately phrased over the aligned suffix and its
      traced normalization together: the former retains Hoare evidence while
      the latter supplies the concrete reassociation proof.  The remaining
      mutually recursive theorem removes [flattenable] by treating access
      brackets and conditionals explicitly. *)
  Theorem aligned_flattenable_suffix_runtime_refinement
      {cost Γ F Δ entry pre exit post_assertion}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre []
        exit post_assertion [])
      (normal : @RuntimeAdapter.traced_suffix_net_normalization cost Γ entry
        exit [] []
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          suffix))
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env)
      (ambient : coPset)
      (Henvelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            suffix)) ⊆ ambient)
      (Hflat : flattenable (RuntimeAdapter.traced_net_source _ normal)
        runtime) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient []) ⊢
    Validity.operational_suffix_translated_wp
      (Validity.erase_aligned_operational_suffix suffix) runtime ambient
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post_assertion ∗
       Validity.World.access_stack_interp atoms ambient []).
  Proof.
    pose proof (aligned_trace_structured_cps_valid_complete
      {| aligned_net_suffix := suffix; aligned_net_normal := normal |}) as
      Hstructured.
    iIntros "Hresources".
    iPoseProof (Hstructured Hwf runtime formals binders atoms ambient
      Henvelope (fun _ =>
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms post_assertion ∗
         Validity.World.access_stack_interp atoms ambient []))%I
      ltac:(reflexivity) with "Hresources") as "Htrace".
    iPoseProof (flattenable_trace_runtime_refinement
      (RuntimeAdapter.traced_net_source _ normal) runtime ambient _ Hflat
      with "Htrace") as "Hruntime".
    rewrite <- source_translated_wp_of_aligned_operational_suffix.
    iExact "Hruntime".
  Qed.
End ConcreteOrdinaryTrace.

(** Proof-relevant aligned normalization.  The following base constructor is
    the first lockstep reconstruction case, exposing a matching fold at the
    head of an aligned suffix together with its remaining aligned
    continuation. *)
Module AlignedTraceNormalization.
  Module Validity := Normalized.Validity.

  (** Lockstep relation between an assertion-carrying operational zipper and
      its certificate-only normalized trace.  Its mode and stack indices are
      those of [net_trace], while the aligned suffix retains the Hoare
      evidence needed by concrete invariant reification. *)
  Inductive aligned_net_trace (cost : RuntimeAdapter.Atomicity.cost_model) Γ F Δ :
    forall entry (pre : Runtime.Translation.Assertions.assertion Γ F Δ)
      stack_in exit (post : Runtime.Translation.Assertions.assertion Γ F Δ)
      stack_out mode tail source tree,
      Validity.aligned_operational_suffix cost Γ F Δ entry pre stack_in exit
        post stack_out ->
      RuntimeAdapter.net_trace cost Γ entry exit mode tail stack_out source
        tree -> Type :=
  | AlignedTraceDone state assertion stack :
      aligned_net_trace cost Γ F Δ state assertion stack state assertion stack
        None stack (RuntimeAdapter.SuffixDone state)
        (@RuntimeAdapter.NetOrdinary stack stack state state
          (RuntimeAdapter.Slice.ExecDone state stack))
        (Validity.AlignedOperationalDone state assertion stack)
        (@RuntimeAdapter.TraceDoneNet cost Γ state stack)
  | AlignedTraceDoneFocused state assertion focused tail :
      aligned_net_trace cost Γ F Δ state assertion (focused :: tail) state
        assertion (focused :: tail) (Some focused) tail
        (RuntimeAdapter.SuffixDone state)
        (@RuntimeAdapter.FocusNetOutcome focused tail state state
          (RuntimeAdapter.Slice.OutcomeStillOpen focused tail state state
            (RuntimeAdapter.Slice.FocusedPrefixDone focused tail state)))
        (Validity.AlignedOperationalDone state assertion (focused :: tail))
        (@RuntimeAdapter.TraceDoneFocused cost Γ state focused tail)
  | AlignedTraceChunk fuel entry statement middle exit pre middle_assertion post
      stack stack_out certificate derivation aligned lifo rest
      chunk Hchunk rest_tree Hrest
      (aligned_rest : aligned_net_trace cost Γ F Δ middle middle_assertion
        stack exit post stack_out None stack
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
        rest_tree rest Hrest) :
      aligned_net_trace cost Γ F Δ entry pre stack exit post stack_out None
        stack
        (RuntimeAdapter.SuffixCons certificate
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest))
        (@RuntimeAdapter.NetChunk stack middle stack_out entry exit chunk rest_tree)
        (@Validity.AlignedOperationalCons cost Γ F Δ fuel entry statement
          middle pre middle_assertion stack stack certificate derivation aligned
          lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceChunk cost Γ fuel entry statement middle exit
          stack stack_out certificate
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
          chunk Hchunk rest_tree Hrest)
  | AlignedTraceAccess fuel entry statement opened exit pre opened_assertion post
      focused tail stack_out certificate derivation aligned lifo rest opening
      Hopening open_ok body Hbody
      (aligned_body : aligned_net_trace cost Γ F Δ opened opened_assertion
        (focused :: tail) exit post stack_out (Some focused) tail
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
        body rest Hbody) :
      aligned_net_trace cost Γ F Δ entry pre tail exit post stack_out None
        tail
        (RuntimeAdapter.SuffixCons certificate
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest))
        (@RuntimeAdapter.NetAccess tail stack_out focused entry opened exit
          opening open_ok body)
        (@Validity.AlignedOperationalCons cost Γ F Δ fuel entry statement
          opened pre opened_assertion tail (focused :: tail) certificate
          derivation aligned lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceAccess cost Γ fuel entry statement opened exit
          focused tail stack_out certificate
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
          opening Hopening open_ok body Hbody)
  | AlignedTraceNestedAccess fuel entry statement opened exit pre
      opened_assertion post focused tail nested stack_out certificate derivation
      aligned lifo rest opening Hopening open_ok body Hbody
      (aligned_body : aligned_net_trace cost Γ F Δ opened opened_assertion
        (nested :: focused :: tail) exit post stack_out (Some nested)
        (focused :: tail)
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
        body rest Hbody) :
      aligned_net_trace cost Γ F Δ entry pre (focused :: tail) exit post
        stack_out (Some focused) tail
        (RuntimeAdapter.SuffixCons certificate
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest))
        (@RuntimeAdapter.FocusNetNested focused tail stack_out nested entry opened
          exit opening open_ok body)
        (@Validity.AlignedOperationalCons cost Γ F Δ fuel entry statement
          opened pre opened_assertion (focused :: tail)
          (nested :: focused :: tail) certificate derivation aligned lifo exit
          post stack_out rest)
        (@RuntimeAdapter.TraceNestedAccess cost Γ fuel entry statement opened
          exit focused tail nested stack_out certificate
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
          opening Hopening open_ok body Hbody)
  | AlignedTraceFocusedPrefix fuel entry statement middle exit pre
      middle_assertion post focused tail stack_out certificate derivation aligned
      lifo rest chunk Hchunk head_ok rest_tree Hrest
      (aligned_rest : aligned_net_trace cost Γ F Δ middle middle_assertion
        (focused :: tail) exit post stack_out (Some focused) tail
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
        rest_tree rest Hrest) :
      aligned_net_trace cost Γ F Δ entry pre (focused :: tail) exit post
        stack_out (Some focused) tail
        (RuntimeAdapter.SuffixCons certificate
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest))
        (@RuntimeAdapter.FocusNetPrefix focused tail stack_out entry middle exit
          chunk head_ok rest_tree)
        (@Validity.AlignedOperationalCons cost Γ F Δ fuel entry statement
          middle pre middle_assertion (focused :: tail) (focused :: tail)
          certificate derivation aligned lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceFocusedPrefix cost Γ fuel entry statement middle
          exit focused tail stack_out certificate
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
          chunk Hchunk head_ok rest_tree Hrest)
  | AlignedTraceClose fuel entry statement closed exit pre closed_assertion post
      focused tail stack_out certificate derivation aligned lifo rest closing
      Hclosing close_ok rest_tree Hrest
      (aligned_rest : aligned_net_trace cost Γ F Δ closed closed_assertion
        tail exit post stack_out None tail
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
        rest_tree rest Hrest) :
      aligned_net_trace cost Γ F Δ entry pre (focused :: tail) exit post
        stack_out None (focused :: tail)
        (RuntimeAdapter.SuffixCons certificate
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest))
        (@RuntimeAdapter.NetClose focused tail stack_out entry closed exit
          closing close_ok rest_tree)
        (@Validity.AlignedOperationalCons cost Γ F Δ fuel entry statement
          closed pre closed_assertion (focused :: tail) tail certificate
          derivation aligned lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceClose cost Γ fuel entry statement closed exit
          focused tail stack_out certificate
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
          closing Hclosing close_ok rest_tree Hrest)
  | AlignedTraceFocusedClose fuel entry statement closed exit pre
      closed_assertion post focused tail stack_out certificate derivation aligned
      lifo rest closing Hclosing close_ok rest_tree Hrest
      (aligned_rest : aligned_net_trace cost Γ F Δ closed closed_assertion
        tail exit post stack_out None tail
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
        rest_tree rest Hrest) :
      aligned_net_trace cost Γ F Δ entry pre (focused :: tail) exit post
        stack_out (Some focused) tail
        (RuntimeAdapter.SuffixCons certificate
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest))
        (@RuntimeAdapter.FocusNetClose focused tail stack_out entry closed exit
          (RuntimeAdapter.Slice.FocusedClose focused tail entry closed closing
            close_ok) rest_tree)
        (@Validity.AlignedOperationalCons cost Γ F Δ fuel entry statement
          closed pre closed_assertion (focused :: tail) tail certificate
          derivation aligned lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceFocusedClose cost Γ fuel entry statement closed
          exit focused tail stack_out certificate
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
          closing Hclosing close_ok rest_tree Hrest)
  | AlignedTraceConditional fuel entry statement then_statement else_statement
      then_exit else_exit exit pre join_assertion post stack_in join_stack
      stack_out view then_certificate else_certificate open_equal atomic_equal
      derivation aligned lifo rest then_tree else_tree rest_tree Hthen Helse
      Hrest
      (aligned_rest : aligned_net_trace cost Γ F Δ
        (RuntimeAdapter.conditional_join then_exit else_exit) join_assertion
        join_stack exit post stack_out None join_stack
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
        rest_tree rest Hrest) :
      aligned_net_trace cost Γ F Δ entry pre stack_in exit post stack_out
        None stack_in
        (RuntimeAdapter.SuffixCons
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest))
        (@RuntimeAdapter.NetConditional stack_in join_stack stack_out entry
          then_exit else_exit (RuntimeAdapter.conditional_join then_exit else_exit)
          exit
          (RuntimeAdapter.Payload.RavenConditional Γ fuel cost entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          then_tree else_tree rest_tree)
        (@Validity.AlignedOperationalCons cost Γ F Δ (S fuel) entry
          statement (RuntimeAdapter.conditional_join then_exit else_exit) pre
          join_assertion stack_in join_stack
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          derivation aligned lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceConditional cost Γ fuel entry statement
          then_statement else_statement then_exit else_exit exit stack_in
          join_stack stack_out view then_certificate else_certificate open_equal
          atomic_equal
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
          then_tree else_tree rest_tree Hthen Helse Hrest)
  | AlignedTraceFocusedConditional fuel entry statement then_statement
      else_statement then_exit else_exit exit pre join_assertion post focused tail
      join_stack stack_out view then_certificate else_certificate open_equal
      atomic_equal derivation aligned lifo rest then_tree else_tree rest_tree
      Hthen Helse Hrest
      (aligned_rest : aligned_net_trace cost Γ F Δ
        (RuntimeAdapter.conditional_join then_exit else_exit) join_assertion
        join_stack exit post stack_out None join_stack
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
        rest_tree rest Hrest) :
      aligned_net_trace cost Γ F Δ entry pre (focused :: tail) exit post
        stack_out (Some focused) tail
        (RuntimeAdapter.SuffixCons
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest))
        (@RuntimeAdapter.FocusNetConditional focused tail join_stack stack_out
          entry then_exit else_exit
          (RuntimeAdapter.conditional_join then_exit else_exit) exit
          (RuntimeAdapter.Payload.RavenConditional Γ fuel cost entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          then_tree else_tree rest_tree)
        (@Validity.AlignedOperationalCons cost Γ F Δ (S fuel) entry
          statement (RuntimeAdapter.conditional_join then_exit else_exit) pre
          join_assertion (focused :: tail) join_stack
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          derivation aligned lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceFocusedConditional cost Γ fuel entry statement
          then_statement else_statement then_exit else_exit exit focused tail
          join_stack stack_out view then_certificate else_certificate open_equal
          atomic_equal
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
          then_tree else_tree rest_tree Hthen Helse Hrest)
  | AlignedTraceFocusedConditionalContinue fuel entry statement then_statement
      else_statement then_exit else_exit exit pre join_assertion post focused
      tail stack_out view then_certificate else_certificate open_equal
      atomic_equal derivation aligned lifo rest then_tree else_tree rest_tree
      Hthen Helse Hrest
      (aligned_rest : aligned_net_trace cost Γ F Δ
        (RuntimeAdapter.conditional_join then_exit else_exit) join_assertion
        (focused :: tail) exit post stack_out (Some focused) tail
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
        rest_tree rest Hrest) :
      aligned_net_trace cost Γ F Δ entry pre (focused :: tail) exit post
        stack_out (Some focused) tail
        (RuntimeAdapter.SuffixCons
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest))
        (@RuntimeAdapter.FocusNetConditionalContinue focused tail stack_out
          entry then_exit else_exit
          (RuntimeAdapter.conditional_join then_exit else_exit) exit
          (RuntimeAdapter.Payload.RavenConditional Γ fuel cost entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          then_tree else_tree rest_tree)
        (@Validity.AlignedOperationalCons cost Γ F Δ (S fuel) entry
          statement (RuntimeAdapter.conditional_join then_exit else_exit) pre
          join_assertion (focused :: tail) (focused :: tail)
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          derivation aligned lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceFocusedConditionalContinue cost Γ fuel entry
          statement then_statement else_statement then_exit else_exit exit
          focused tail stack_out view then_certificate else_certificate
          open_equal atomic_equal
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
          then_tree else_tree rest_tree Hthen Helse Hrest)
  | AlignedTraceSequenceExpansion fuel entry statement first middle second next exit
      pre
      (middle_assertion next_assertion post :
        Runtime.Translation.Assertions.assertion Γ F Δ)
      (stack_in stack_middle stack_next stack_out :
        list RuntimeAdapter.Atomicity.access_marker)
      view first_certificate second_certificate
      (first_derivation : Validity.Certified.Rules.RavenHoareTriple pre first
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask middle) middle_assertion)
      (second_derivation : Validity.Certified.Rules.RavenHoareTriple
        middle_assertion second (RuntimeAdapter.Atomicity.analysis_mask middle)
        (RuntimeAdapter.Atomicity.analysis_mask next) next_assertion)
      (first_aligned : Validity.Certified.certificate_hoare_aligned cost
        first_certificate first_derivation)
      (second_aligned : Validity.Certified.certificate_hoare_aligned cost
        second_certificate second_derivation)
      (head_derivation : Validity.Certified.Rules.RavenHoareTriple pre
        statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask next) next_assertion)
      (head_aligned : Validity.Certified.certificate_hoare_aligned cost
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate) head_derivation)
      head_lifo
      (first_lifo : RuntimeAdapter.Atomicity.lifo_certificate first_certificate
        stack_in stack_middle)
      (second_lifo : RuntimeAdapter.Atomicity.lifo_certificate second_certificate
        stack_middle stack_next)
      rest mode tail tree Hflat
      (aligned_flat : aligned_net_trace cost Γ F Δ entry pre stack_in exit
        post stack_out mode tail
        (RuntimeAdapter.SuffixCons first_certificate
          (RuntimeAdapter.SuffixCons second_certificate
            (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
              rest))) tree
        (Validity.expand_aligned_sequence_suffix view first_certificate
          second_certificate first_derivation second_derivation first_aligned
          second_aligned first_lifo second_lifo rest) Hflat) :
      aligned_net_trace cost Γ F Δ entry pre stack_in exit post stack_out
        mode tail
        (RuntimeAdapter.SuffixCons
          (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
            statement first middle second next view
            first_certificate second_certificate)
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest)) tree
        (@Validity.AlignedOperationalCons cost Γ F Δ (S fuel) entry
          statement next pre next_assertion stack_in
          stack_next
          (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
            statement first middle second next view
            first_certificate second_certificate)
          head_derivation head_aligned head_lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceExpansion cost Γ entry exit mode tail stack_out
          (RuntimeAdapter.SuffixCons first_certificate
            (RuntimeAdapter.SuffixCons second_certificate
              (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
                rest)))
          (RuntimeAdapter.SuffixCons
            (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
              statement first middle second next view
              first_certificate second_certificate)
            (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
              rest)) tree
          (@RuntimeAdapter.ExpandsSequence cost Γ fuel entry
            statement first middle second next exit
            view first_certificate second_certificate
            (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
              rest)) Hflat)
  | AlignedTraceExpansion entry pre stack_in exit post stack_out mode tail
      source tree
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre
        stack_in exit post stack_out)
      flat
      (flat_suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre
        stack_in exit post stack_out)
      (expansion : RuntimeAdapter.suffix_expands cost Γ entry exit flat source)
      (Hsource : source =
        Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          suffix)
      (Hflat_source : flat =
        Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          flat_suffix)
      (flat_trace : RuntimeAdapter.net_trace cost Γ entry exit mode tail
        stack_out flat tree)
      (aligned_flat : aligned_net_trace cost Γ F Δ entry pre stack_in exit
        post stack_out mode tail flat tree flat_suffix flat_trace) :
      aligned_net_trace cost Γ F Δ entry pre stack_in exit post stack_out
        mode tail source tree suffix
        (@RuntimeAdapter.TraceExpansion cost Γ entry exit mode tail stack_out
          flat source tree expansion flat_trace).

  Lemma aligned_net_trace_source_eq
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source tree
        suffix trace}
      (aligned : @aligned_net_trace cost Γ F Δ entry pre stack_in exit post
        stack_out mode tail source tree suffix trace) :
    source =
      Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
        suffix.
  Proof.
    induction aligned; simpl; try reflexivity.
    - exact Hsource.
  Qed.

(** Resource-native lockstep relation.  It retains resource triples at every
    zipper head while sharing only the executable certificate source. *)
  Inductive resource_aligned_net_trace (cost : RuntimeAdapter.Atomicity.cost_model) Γ F Δ :
    forall entry (pre : Runtime.Translation.Assertions.assertion Γ F Δ)
      stack_in exit (post : Runtime.Translation.Assertions.assertion Γ F Δ)
      stack_out mode tail source tree,
      Validity.resource_aligned_operational_suffix cost Γ F Δ entry pre stack_in exit
        post stack_out ->
      RuntimeAdapter.net_trace cost Γ entry exit mode tail stack_out source
        tree -> Type :=
  | ResourceAlignedTraceDone state assertion stack :
      resource_aligned_net_trace cost Γ F Δ state assertion stack state assertion stack
        None stack (RuntimeAdapter.SuffixDone state)
        (@RuntimeAdapter.NetOrdinary stack stack state state
          (RuntimeAdapter.Slice.ExecDone state stack))
        (Validity.ResourceAlignedOperationalDone state assertion stack)
        (@RuntimeAdapter.TraceDoneNet cost Γ state stack)
  | ResourceAlignedTraceDoneFocused state assertion focused tail :
      resource_aligned_net_trace cost Γ F Δ state assertion (focused :: tail) state
        assertion (focused :: tail) (Some focused) tail
        (RuntimeAdapter.SuffixDone state)
        (@RuntimeAdapter.FocusNetOutcome focused tail state state
          (RuntimeAdapter.Slice.OutcomeStillOpen focused tail state state
            (RuntimeAdapter.Slice.FocusedPrefixDone focused tail state)))
        (Validity.ResourceAlignedOperationalDone state assertion (focused :: tail))
        (@RuntimeAdapter.TraceDoneFocused cost Γ state focused tail)
  | ResourceAlignedTraceChunk fuel entry statement middle exit pre middle_assertion post
      stack stack_out certificate derivation aligned lifo rest
      chunk Hchunk rest_tree Hrest
      (aligned_rest : resource_aligned_net_trace cost Γ F Δ middle middle_assertion
        stack exit post stack_out None stack
        (resource_certificate_suffix_of_operational_suffix rest)
        rest_tree rest Hrest) :
      resource_aligned_net_trace cost Γ F Δ entry pre stack exit post stack_out None
        stack
        (RuntimeAdapter.SuffixCons certificate
          (resource_certificate_suffix_of_operational_suffix rest))
        (@RuntimeAdapter.NetChunk stack middle stack_out entry exit chunk rest_tree)
        (@Validity.ResourceAlignedOperationalCons cost Γ F Δ fuel entry statement
          middle pre middle_assertion stack stack certificate derivation aligned
          lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceChunk cost Γ fuel entry statement middle exit
          stack stack_out certificate
          (resource_certificate_suffix_of_operational_suffix rest)
          chunk Hchunk rest_tree Hrest)
  | ResourceAlignedTraceAccess fuel entry statement opened exit pre opened_assertion post
      focused tail stack_out certificate derivation aligned lifo rest opening
      Hopening open_ok body Hbody
      (aligned_body : resource_aligned_net_trace cost Γ F Δ opened opened_assertion
        (focused :: tail) exit post stack_out (Some focused) tail
        (resource_certificate_suffix_of_operational_suffix rest)
        body rest Hbody) :
      resource_aligned_net_trace cost Γ F Δ entry pre tail exit post stack_out None
        tail
        (RuntimeAdapter.SuffixCons certificate
          (resource_certificate_suffix_of_operational_suffix rest))
        (@RuntimeAdapter.NetAccess tail stack_out focused entry opened exit
          opening open_ok body)
        (@Validity.ResourceAlignedOperationalCons cost Γ F Δ fuel entry statement
          opened pre opened_assertion tail (focused :: tail) certificate
          derivation aligned lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceAccess cost Γ fuel entry statement opened exit
          focused tail stack_out certificate
          (resource_certificate_suffix_of_operational_suffix rest)
          opening Hopening open_ok body Hbody)
  | ResourceAlignedTraceNestedAccess fuel entry statement opened exit pre
      opened_assertion post focused tail nested stack_out certificate derivation
      aligned lifo rest opening Hopening open_ok body Hbody
      (aligned_body : resource_aligned_net_trace cost Γ F Δ opened opened_assertion
        (nested :: focused :: tail) exit post stack_out (Some nested)
        (focused :: tail)
        (resource_certificate_suffix_of_operational_suffix rest)
        body rest Hbody) :
      resource_aligned_net_trace cost Γ F Δ entry pre (focused :: tail) exit post
        stack_out (Some focused) tail
        (RuntimeAdapter.SuffixCons certificate
          (resource_certificate_suffix_of_operational_suffix rest))
        (@RuntimeAdapter.FocusNetNested focused tail stack_out nested entry opened
          exit opening open_ok body)
        (@Validity.ResourceAlignedOperationalCons cost Γ F Δ fuel entry statement
          opened pre opened_assertion (focused :: tail)
          (nested :: focused :: tail) certificate derivation aligned lifo exit
          post stack_out rest)
        (@RuntimeAdapter.TraceNestedAccess cost Γ fuel entry statement opened
          exit focused tail nested stack_out certificate
          (resource_certificate_suffix_of_operational_suffix rest)
          opening Hopening open_ok body Hbody)
  | ResourceAlignedTraceFocusedPrefix fuel entry statement middle exit pre
      middle_assertion post focused tail stack_out certificate derivation aligned
      lifo rest chunk Hchunk head_ok rest_tree Hrest
      (aligned_rest : resource_aligned_net_trace cost Γ F Δ middle middle_assertion
        (focused :: tail) exit post stack_out (Some focused) tail
        (resource_certificate_suffix_of_operational_suffix rest)
        rest_tree rest Hrest) :
      resource_aligned_net_trace cost Γ F Δ entry pre (focused :: tail) exit post
        stack_out (Some focused) tail
        (RuntimeAdapter.SuffixCons certificate
          (resource_certificate_suffix_of_operational_suffix rest))
        (@RuntimeAdapter.FocusNetPrefix focused tail stack_out entry middle exit
          chunk head_ok rest_tree)
        (@Validity.ResourceAlignedOperationalCons cost Γ F Δ fuel entry statement
          middle pre middle_assertion (focused :: tail) (focused :: tail)
          certificate derivation aligned lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceFocusedPrefix cost Γ fuel entry statement middle
          exit focused tail stack_out certificate
          (resource_certificate_suffix_of_operational_suffix rest)
          chunk Hchunk head_ok rest_tree Hrest)
  | ResourceAlignedTraceClose fuel entry statement closed exit pre closed_assertion post
      focused tail stack_out certificate derivation aligned lifo rest closing
      Hclosing close_ok rest_tree Hrest
      (aligned_rest : resource_aligned_net_trace cost Γ F Δ closed closed_assertion
        tail exit post stack_out None tail
        (resource_certificate_suffix_of_operational_suffix rest)
        rest_tree rest Hrest) :
      resource_aligned_net_trace cost Γ F Δ entry pre (focused :: tail) exit post
        stack_out None (focused :: tail)
        (RuntimeAdapter.SuffixCons certificate
          (resource_certificate_suffix_of_operational_suffix rest))
        (@RuntimeAdapter.NetClose focused tail stack_out entry closed exit
          closing close_ok rest_tree)
        (@Validity.ResourceAlignedOperationalCons cost Γ F Δ fuel entry statement
          closed pre closed_assertion (focused :: tail) tail certificate
          derivation aligned lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceClose cost Γ fuel entry statement closed exit
          focused tail stack_out certificate
          (resource_certificate_suffix_of_operational_suffix rest)
          closing Hclosing close_ok rest_tree Hrest)
  | ResourceAlignedTraceFocusedClose fuel entry statement closed exit pre
      closed_assertion post focused tail stack_out certificate derivation aligned
      lifo rest closing Hclosing close_ok rest_tree Hrest
      (aligned_rest : resource_aligned_net_trace cost Γ F Δ closed closed_assertion
        tail exit post stack_out None tail
        (resource_certificate_suffix_of_operational_suffix rest)
        rest_tree rest Hrest) :
      resource_aligned_net_trace cost Γ F Δ entry pre (focused :: tail) exit post
        stack_out (Some focused) tail
        (RuntimeAdapter.SuffixCons certificate
          (resource_certificate_suffix_of_operational_suffix rest))
        (@RuntimeAdapter.FocusNetClose focused tail stack_out entry closed exit
          (RuntimeAdapter.Slice.FocusedClose focused tail entry closed closing
            close_ok) rest_tree)
        (@Validity.ResourceAlignedOperationalCons cost Γ F Δ fuel entry statement
          closed pre closed_assertion (focused :: tail) tail certificate
          derivation aligned lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceFocusedClose cost Γ fuel entry statement closed
          exit focused tail stack_out certificate
          (resource_certificate_suffix_of_operational_suffix rest)
          closing Hclosing close_ok rest_tree Hrest)
  | ResourceAlignedTraceConditional fuel entry statement then_statement else_statement
      then_exit else_exit exit pre join_assertion post stack_in join_stack
      stack_out view then_certificate else_certificate open_equal atomic_equal
      derivation aligned lifo rest then_tree else_tree rest_tree Hthen Helse
      Hrest
      (branch_data : @resource_conditional_branch_data cost Γ F Δ fuel entry
        statement then_statement else_statement then_exit else_exit pre
        join_assertion view then_certificate else_certificate open_equal
        atomic_equal derivation aligned stack_in join_stack None stack_in
        then_tree else_tree lifo Hthen Helse)
      (aligned_rest : resource_aligned_net_trace cost Γ F Δ
        (RuntimeAdapter.conditional_join then_exit else_exit) join_assertion
        join_stack exit post stack_out None join_stack
        (resource_certificate_suffix_of_operational_suffix rest)
        rest_tree rest Hrest) :
      resource_aligned_net_trace cost Γ F Δ entry pre stack_in exit post stack_out
        None stack_in
        (RuntimeAdapter.SuffixCons
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          (resource_certificate_suffix_of_operational_suffix rest))
        (@RuntimeAdapter.NetConditional stack_in join_stack stack_out entry
          then_exit else_exit (RuntimeAdapter.conditional_join then_exit else_exit)
          exit
          (RuntimeAdapter.Payload.RavenConditional Γ fuel cost entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          then_tree else_tree rest_tree)
        (@Validity.ResourceAlignedOperationalCons cost Γ F Δ (S fuel) entry
          statement (RuntimeAdapter.conditional_join then_exit else_exit) pre
          join_assertion stack_in join_stack
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          derivation aligned lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceConditional cost Γ fuel entry statement
          then_statement else_statement then_exit else_exit exit stack_in
          join_stack stack_out view then_certificate else_certificate open_equal
          atomic_equal
          (resource_certificate_suffix_of_operational_suffix rest)
          then_tree else_tree rest_tree Hthen Helse Hrest)
  | ResourceAlignedTraceFocusedConditional fuel entry statement then_statement
      else_statement then_exit else_exit exit pre join_assertion post focused tail
      join_stack stack_out view then_certificate else_certificate open_equal
      atomic_equal derivation aligned lifo rest then_tree else_tree rest_tree
      Hthen Helse Hrest
      (branch_data : @resource_conditional_branch_data cost Γ F Δ fuel entry
        statement then_statement else_statement then_exit else_exit pre
        join_assertion view then_certificate else_certificate open_equal
        atomic_equal derivation aligned (focused :: tail) join_stack
        (Some focused) tail then_tree else_tree lifo Hthen Helse)
      (aligned_rest : resource_aligned_net_trace cost Γ F Δ
        (RuntimeAdapter.conditional_join then_exit else_exit) join_assertion
        join_stack exit post stack_out None join_stack
        (resource_certificate_suffix_of_operational_suffix rest)
        rest_tree rest Hrest) :
      resource_aligned_net_trace cost Γ F Δ entry pre (focused :: tail) exit post
        stack_out (Some focused) tail
        (RuntimeAdapter.SuffixCons
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          (resource_certificate_suffix_of_operational_suffix rest))
        (@RuntimeAdapter.FocusNetConditional focused tail join_stack stack_out
          entry then_exit else_exit
          (RuntimeAdapter.conditional_join then_exit else_exit) exit
          (RuntimeAdapter.Payload.RavenConditional Γ fuel cost entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          then_tree else_tree rest_tree)
        (@Validity.ResourceAlignedOperationalCons cost Γ F Δ (S fuel) entry
          statement (RuntimeAdapter.conditional_join then_exit else_exit) pre
          join_assertion (focused :: tail) join_stack
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          derivation aligned lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceFocusedConditional cost Γ fuel entry statement
          then_statement else_statement then_exit else_exit exit focused tail
          join_stack stack_out view then_certificate else_certificate open_equal
          atomic_equal
          (resource_certificate_suffix_of_operational_suffix rest)
          then_tree else_tree rest_tree Hthen Helse Hrest)
  | ResourceAlignedTraceFocusedConditionalContinue fuel entry statement then_statement
      else_statement then_exit else_exit exit pre join_assertion post focused
      tail stack_out view then_certificate else_certificate open_equal
      atomic_equal derivation aligned lifo rest then_tree else_tree rest_tree
      Hthen Helse Hrest
      (branch_data : @resource_conditional_branch_data cost Γ F Δ fuel entry
        statement then_statement else_statement then_exit else_exit pre
        join_assertion view then_certificate else_certificate open_equal
        atomic_equal derivation aligned (focused :: tail) (focused :: tail)
        (Some focused) tail then_tree else_tree lifo Hthen Helse)
      (aligned_rest : resource_aligned_net_trace cost Γ F Δ
        (RuntimeAdapter.conditional_join then_exit else_exit) join_assertion
        (focused :: tail) exit post stack_out (Some focused) tail
        (resource_certificate_suffix_of_operational_suffix rest)
        rest_tree rest Hrest) :
      resource_aligned_net_trace cost Γ F Δ entry pre (focused :: tail) exit post
        stack_out (Some focused) tail
        (RuntimeAdapter.SuffixCons
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          (resource_certificate_suffix_of_operational_suffix rest))
        (@RuntimeAdapter.FocusNetConditionalContinue focused tail stack_out
          entry then_exit else_exit
          (RuntimeAdapter.conditional_join then_exit else_exit) exit
          (RuntimeAdapter.Payload.RavenConditional Γ fuel cost entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          then_tree else_tree rest_tree)
        (@Validity.ResourceAlignedOperationalCons cost Γ F Δ (S fuel) entry
          statement (RuntimeAdapter.conditional_join then_exit else_exit) pre
          join_assertion (focused :: tail) (focused :: tail)
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)
          derivation aligned lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceFocusedConditionalContinue cost Γ fuel entry
          statement then_statement else_statement then_exit else_exit exit
          focused tail stack_out view then_certificate else_certificate
          open_equal atomic_equal
          (resource_certificate_suffix_of_operational_suffix rest)
          then_tree else_tree rest_tree Hthen Helse Hrest)
  | ResourceAlignedTraceSequenceExpansion fuel entry statement first middle second next exit
      pre
      (middle_assertion next_assertion post :
        Runtime.Translation.Assertions.assertion Γ F Δ)
      (stack_in stack_middle stack_next stack_out :
        list RuntimeAdapter.Atomicity.access_marker)
      view first_certificate second_certificate
      (first_derivation : Validity.Certified.Rules.RavenResourceTriple pre first middle_assertion)
      (second_derivation : Validity.Certified.Rules.RavenResourceTriple
        middle_assertion second next_assertion)
      (first_aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        first_certificate first_derivation)
      (second_aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        second_certificate second_derivation)
      (head_derivation : Validity.Certified.Rules.RavenResourceTriple pre statement next_assertion)
      (head_aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate) head_derivation)
      head_lifo
      (first_lifo : RuntimeAdapter.Atomicity.lifo_certificate first_certificate
        stack_in stack_middle)
      (second_lifo : RuntimeAdapter.Atomicity.lifo_certificate second_certificate
        stack_middle stack_next)
      rest mode tail tree Hflat
      (aligned_flat : resource_aligned_net_trace cost Γ F Δ entry pre stack_in exit
        post stack_out mode tail
        (RuntimeAdapter.SuffixCons first_certificate
          (RuntimeAdapter.SuffixCons second_certificate
            (resource_certificate_suffix_of_operational_suffix
              rest))) tree
        (Validity.expand_resource_aligned_sequence_suffix view first_certificate
          second_certificate first_derivation second_derivation first_aligned
          second_aligned first_lifo second_lifo rest) Hflat) :
      resource_aligned_net_trace cost Γ F Δ entry pre stack_in exit post stack_out
        mode tail
        (RuntimeAdapter.SuffixCons
          (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
            statement first middle second next view
            first_certificate second_certificate)
          (resource_certificate_suffix_of_operational_suffix
            rest)) tree
        (@Validity.ResourceAlignedOperationalCons cost Γ F Δ (S fuel) entry
          statement next pre next_assertion stack_in
          stack_next
          (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
            statement first middle second next view
            first_certificate second_certificate)
          head_derivation head_aligned head_lifo exit post stack_out rest)
        (@RuntimeAdapter.TraceExpansion cost Γ entry exit mode tail stack_out
          (RuntimeAdapter.SuffixCons first_certificate
            (RuntimeAdapter.SuffixCons second_certificate
              (resource_certificate_suffix_of_operational_suffix
                rest)))
          (RuntimeAdapter.SuffixCons
            (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
              statement first middle second next view
              first_certificate second_certificate)
            (resource_certificate_suffix_of_operational_suffix
              rest)) tree
          (@RuntimeAdapter.ExpandsSequence cost Γ fuel entry
            statement first middle second next exit
            view first_certificate second_certificate
            (resource_certificate_suffix_of_operational_suffix
              rest)) Hflat)
  | ResourceAlignedTraceExpansion entry pre stack_in exit post stack_out mode tail
      source tree
      (suffix : Validity.resource_aligned_operational_suffix cost Γ F Δ entry pre
        stack_in exit post stack_out)
      flat
      (flat_suffix : Validity.resource_aligned_operational_suffix cost Γ F Δ entry pre
        stack_in exit post stack_out)
      (expansion : RuntimeAdapter.suffix_expands cost Γ entry exit flat source)
      (Hsource : source =
        resource_certificate_suffix_of_operational_suffix
          suffix)
      (Hflat_source : flat =
        resource_certificate_suffix_of_operational_suffix
          flat_suffix)
      (flat_trace : RuntimeAdapter.net_trace cost Γ entry exit mode tail
        stack_out flat tree)
      (aligned_flat : resource_aligned_net_trace cost Γ F Δ entry pre stack_in exit
        post stack_out mode tail flat tree flat_suffix flat_trace) :
      resource_aligned_net_trace cost Γ F Δ entry pre stack_in exit post stack_out
        mode tail source tree suffix
        (@RuntimeAdapter.TraceExpansion cost Γ entry exit mode tail stack_out
          flat source tree expansion flat_trace)

  with resource_conditional_branch_data (cost : RuntimeAdapter.Atomicity.cost_model)
      Γ F Δ :
    forall fuel entry statement then_statement else_statement then_exit else_exit
      (pre join_assertion : Runtime.Translation.Assertions.assertion Γ F Δ)
      view then_certificate else_certificate open_equal atomic_equal
      (derivation : Validity.Certified.Rules.RavenResourceTriple pre statement
        join_assertion)
      (aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
          then_statement else_statement then_exit else_exit view
          then_certificate else_certificate open_equal atomic_equal)
        derivation)
      stack_in join_stack mode tail then_tree else_tree
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
          then_statement else_statement then_exit else_exit view
          then_certificate else_certificate open_equal atomic_equal)
        stack_in join_stack)
      (Hthen : RuntimeAdapter.net_trace cost Γ entry then_exit mode tail
        join_stack (RuntimeAdapter.singleton_suffix then_certificate) then_tree)
      (Helse : RuntimeAdapter.net_trace cost Γ entry else_exit mode tail
        join_stack (RuntimeAdapter.singleton_suffix else_certificate) else_tree),
      Type :=
  | ResourceConditionalBranchCore fuel entry node store frame condition
      then_statement else_statement then_exit else_exit post view
      then_certificate else_certificate open_equal atomic_equal
      then_derivation else_derivation then_aligned else_aligned stack_in join_stack
      mode tail then_tree else_tree then_lifo else_lifo Hthen Helse
      (then_lockstep : resource_aligned_net_trace cost Γ F Δ entry
        (Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store)
          (Runtime.Translation.Assertions.AAnd frame
            (Runtime.Translation.Assertions.AExpr
              (Runtime.Validation.Hoare.symbolize_expr store condition))))
        stack_in then_exit post join_stack mode tail
        (RuntimeAdapter.singleton_suffix then_certificate) then_tree
        (Validity.resource_aligned_singleton_suffix then_certificate
          then_derivation then_aligned then_lifo) Hthen)
      (else_lockstep : resource_aligned_net_trace cost Γ F Δ entry
        (Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store)
          (Runtime.Translation.Assertions.AAnd frame
            (Runtime.Translation.Assertions.AExpr
              (Runtime.Core.EUnOp Runtime.Core.UNot
                (Runtime.Validation.Hoare.symbolize_expr store condition)))))
        stack_in else_exit post join_stack mode tail
        (RuntimeAdapter.singleton_suffix else_certificate) else_tree
        (Validity.resource_aligned_singleton_suffix else_certificate
          else_derivation else_aligned else_lifo) Helse) :
      resource_conditional_branch_data cost Γ F Δ fuel entry
        (Runtime.IR.TIf node condition then_statement else_statement)
        then_statement else_statement then_exit else_exit
        (Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store) frame) post view
        then_certificate else_certificate open_equal atomic_equal
        (Validity.Certified.Rules.ResourceConditionalRule node store frame
          condition then_statement else_statement post then_derivation
          else_derivation)
        (Validity.Certified.ResourceAlignedConditional cost Γ F Δ fuel entry
          node store frame condition then_statement else_statement then_exit
          else_exit post view then_certificate else_certificate open_equal
          atomic_equal then_derivation else_derivation then_aligned else_aligned)
        stack_in join_stack mode tail then_tree else_tree
        (conj then_lifo else_lifo) Hthen Helse
  | ResourceConditionalBranchFrame fuel entry statement then_statement
      else_statement then_exit else_exit pre post frame view then_certificate
      else_certificate open_equal atomic_equal derivation aligned stack_in
      join_stack mode tail then_tree else_tree lifo Hthen Helse
      (inner : resource_conditional_branch_data cost Γ F Δ fuel entry
        statement then_statement else_statement then_exit else_exit pre post
        view then_certificate else_certificate open_equal atomic_equal
        derivation aligned stack_in join_stack mode tail then_tree else_tree
        lifo Hthen Helse) :
      resource_conditional_branch_data cost Γ F Δ fuel entry statement
        then_statement else_statement then_exit else_exit
        (Runtime.Translation.Assertions.AAnd pre frame)
        (Runtime.Translation.Assertions.AAnd post frame) view then_certificate
        else_certificate open_equal atomic_equal
        (Validity.Certified.Rules.ResourceFrameRule pre post frame statement derivation)
        (Validity.Certified.ResourceAlignedFrame cost Γ F Δ (S fuel) entry
          (RuntimeAdapter.conditional_join then_exit else_exit) statement pre post
          frame _ derivation aligned)
        stack_in join_stack mode tail then_tree else_tree lifo Hthen Helse
  | ResourceConditionalBranchConsequence fuel entry statement then_statement
      else_statement then_exit else_exit pre pre' post post' view then_certificate
      else_certificate open_equal atomic_equal derivation pre_entails post_entails
      aligned stack_in join_stack mode tail then_tree else_tree lifo Hthen Helse
      (inner : resource_conditional_branch_data cost Γ F Δ fuel entry
        statement then_statement else_statement then_exit else_exit pre post
        view then_certificate else_certificate open_equal atomic_equal
        derivation aligned stack_in join_stack mode tail then_tree else_tree
        lifo Hthen Helse) :
      resource_conditional_branch_data cost Γ F Δ fuel entry statement
        then_statement else_statement then_exit else_exit pre' post' view
        then_certificate else_certificate open_equal atomic_equal
        (Validity.Certified.Rules.ResourceConsequenceRule pre pre' post post'
          statement derivation pre_entails post_entails)
        (Validity.Certified.ResourceAlignedConsequence cost Γ F Δ (S fuel) entry
          (RuntimeAdapter.conditional_join then_exit else_exit) statement pre pre'
          post post' _ derivation pre_entails post_entails aligned)
        stack_in join_stack mode tail then_tree else_tree lifo Hthen Helse
  | ResourceConditionalBranchExistsElim (t : typed_core.TypedCore.typ) fuel
      entry statement then_statement else_statement then_exit else_exit body
      post view then_certificate else_certificate open_equal atomic_equal
      derivation aligned stack_in join_stack mode tail then_tree else_tree lifo
      Hthen Helse
      (inner : @resource_conditional_branch_data cost Γ F (t :: Δ) fuel
        entry statement then_statement else_statement then_exit else_exit body
        (Runtime.Translation.Assertions.weaken_assertion post) view
        then_certificate else_certificate open_equal atomic_equal derivation
        aligned stack_in join_stack mode tail then_tree else_tree lifo Hthen
        Helse) :
      resource_conditional_branch_data cost Γ F Δ fuel entry statement
        then_statement else_statement then_exit else_exit
        (Runtime.Translation.Assertions.AExists t body) post view
        then_certificate else_certificate open_equal atomic_equal
        (Validity.Certified.Rules.ResourceExistsElimRule t body post statement
          derivation)
        (Validity.Certified.ResourceAlignedExistsElim cost Γ F Δ t (S fuel)
          entry (RuntimeAdapter.conditional_join then_exit else_exit) statement
          body post _ derivation aligned)
        stack_in join_stack mode tail then_tree else_tree lifo Hthen Helse
  | ResourceConditionalBranchExistsPreserve (t : typed_core.TypedCore.typ)
      fuel entry statement then_statement else_statement then_exit else_exit
      body post view then_certificate else_certificate open_equal atomic_equal
      derivation aligned stack_in join_stack mode tail then_tree else_tree lifo
      Hthen Helse
      (inner : @resource_conditional_branch_data cost Γ F (t :: Δ) fuel
        entry statement then_statement else_statement then_exit else_exit body
        post view then_certificate else_certificate open_equal atomic_equal
        derivation aligned stack_in join_stack mode tail then_tree else_tree
        lifo Hthen Helse) :
      resource_conditional_branch_data cost Γ F Δ fuel entry statement
        then_statement else_statement then_exit else_exit
        (Runtime.Translation.Assertions.AExists t body)
        (Runtime.Translation.Assertions.AExists t post) view then_certificate
        else_certificate open_equal atomic_equal
        (Validity.Certified.Rules.ResourceExistsPreserveRule t body post statement
          derivation)
        (Validity.Certified.ResourceAlignedExistsPreserve cost Γ F Δ t
          (S fuel) entry (RuntimeAdapter.conditional_join then_exit else_exit)
          statement body post _ derivation aligned)
        stack_in join_stack mode tail then_tree else_tree lifo Hthen Helse.

  Scheme resource_aligned_net_trace_mutind := Induction for
    resource_aligned_net_trace Sort Prop
  with resource_conditional_branch_data_mutind := Induction for
    resource_conditional_branch_data Sort Prop.

  Combined Scheme resource_aligned_trace_and_branch_data_mutind
    from resource_aligned_net_trace_mutind,
      resource_conditional_branch_data_mutind.

  Definition resource_fixed_singleton_lockstep_builder
      {cost Γ fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (stack_in stack_out : list RuntimeAdapter.Atomicity.access_marker)
      (mode : option RuntimeAdapter.Payload.marker)
      (tail : list RuntimeAdapter.Payload.marker) : Type :=
    forall (F Δ : typed_core.TypedCore.context)
      (pre post : Runtime.Translation.Assertions.assertion Γ F Δ)
      (derivation : Validity.Certified.Rules.RavenResourceTriple pre statement post)
      (aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        certificate derivation)
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in stack_out),
      { tree : RuntimeAdapter.net_tree mode tail stack_out entry exit &
        { trace : RuntimeAdapter.net_trace cost Γ entry exit mode tail stack_out
            (RuntimeAdapter.singleton_suffix certificate) tree &
          resource_aligned_net_trace cost Γ F Δ entry pre stack_in exit post
            stack_out mode tail (RuntimeAdapter.singleton_suffix certificate) tree
            (Validity.resource_aligned_singleton_suffix certificate derivation
              aligned lifo) trace } }.

  Definition resource_conditional_branch_data_target
      {cost Γ fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit) :
    forall F Δ pre post
      (derivation : Validity.Certified.Rules.RavenResourceTriple pre statement post),
      Validity.Certified.resource_certificate_hoare_aligned cost certificate
        derivation -> Type :=
    match certificate as certificate' in
        RuntimeAdapter.Atomicity.analysis_certificate _ Γ' fuel' entry'
          statement' exit'
      return forall F' Δ' pre' post'
        (derivation' : Validity.Certified.Rules.RavenResourceTriple pre'
          statement' post'),
        Validity.Certified.resource_certificate_hoare_aligned cost certificate'
          derivation' -> Type
    with
    | @RuntimeAdapter.Atomicity.CertConditional _ Γ' fuel' entry' statement'
        then_statement else_statement then_exit else_exit view then_certificate
        else_certificate open_equal atomic_equal =>
        fun F' Δ' pre' post' derivation' aligned' =>
          forall stack_in join_stack mode tail
            (lifo : RuntimeAdapter.Atomicity.lifo_certificate
              (RuntimeAdapter.Atomicity.CertConditional cost Γ' fuel' entry'
                statement' then_statement else_statement then_exit else_exit
                view then_certificate else_certificate open_equal atomic_equal)
              stack_in join_stack)
            (build_then : resource_fixed_singleton_lockstep_builder
              then_certificate stack_in join_stack mode tail)
            (build_else : resource_fixed_singleton_lockstep_builder
              else_certificate stack_in join_stack mode tail),
            { then_tree : RuntimeAdapter.net_tree mode tail join_stack entry'
                then_exit &
              { else_tree : RuntimeAdapter.net_tree mode tail join_stack entry'
                  else_exit &
                { Hthen : RuntimeAdapter.net_trace cost Γ' entry' then_exit mode
                    tail join_stack (RuntimeAdapter.singleton_suffix
                      then_certificate) then_tree &
                  { Helse : RuntimeAdapter.net_trace cost Γ' entry' else_exit
                      mode tail join_stack (RuntimeAdapter.singleton_suffix
                        else_certificate) else_tree &
                    @resource_conditional_branch_data cost Γ' F' Δ' fuel'
                      entry' statement' then_statement else_statement then_exit
                      else_exit pre' post' view then_certificate else_certificate
                      open_equal atomic_equal derivation' aligned' stack_in
                      join_stack mode tail then_tree else_tree lifo Hthen Helse } } } }
    | _ => fun _ _ _ _ _ _ => unit
    end.

  Fixpoint resource_aligned_conditional_branch_data_fix
      {cost Γ F Δ fuel entry statement exit pre post}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenResourceTriple pre statement post}
      (aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        certificate derivation) {struct aligned} :
    resource_conditional_branch_data_target certificate F Δ pre post
      derivation aligned.
  Proof.
    destruct aligned; simpl; try exact tt.
    - intros stack_in join_stack mode tail lifo build_then build_else.
      destruct lifo as [then_lifo else_lifo].
      destruct (build_then F Δ _ post then_derivation aligned1 then_lifo) as
        [then_tree [Hthen then_lockstep]].
      destruct (build_else F Δ _ post else_derivation aligned2 else_lifo) as
        [else_tree [Helse else_lockstep]].
      exists then_tree, else_tree, Hthen, Helse. econstructor; assumption.
    - dependent destruction certificate; simpl; try exact tt.
      intros stack_in join_stack mode tail lifo build_then build_else.
      destruct (@resource_aligned_conditional_branch_data_fix cost Γ F Δ (S fuel)
        state statement (RuntimeAdapter.conditional_join then_exit else_exit) pre post
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state statement
          then_branch else_branch then_exit else_exit e certificate1
          certificate2 e0 e1) derivation aligned stack_in join_stack mode tail
          lifo build_then build_else) as [then_tree [else_tree [Hthen [Helse data]]]].
      exists then_tree, else_tree, Hthen, Helse.
      constructor. exact data.
    - dependent destruction certificate; simpl; try exact tt.
      intros stack_in join_stack mode tail lifo build_then build_else.
      destruct (@resource_aligned_conditional_branch_data_fix cost Γ F Δ (S fuel)
        state statement (RuntimeAdapter.conditional_join then_exit else_exit) pre post
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state statement
          then_branch else_branch then_exit else_exit e certificate1
          certificate2 e0 e1) derivation aligned stack_in join_stack mode tail
          lifo build_then build_else) as [then_tree [else_tree [Hthen [Helse data]]]].
      exists then_tree, else_tree, Hthen, Helse.
      constructor. exact data.
    - dependent destruction certificate; simpl; try exact tt.
      intros stack_in join_stack mode tail lifo build_then build_else.
      destruct (@resource_aligned_conditional_branch_data_fix cost Γ F (t :: Δ)
        (S fuel) state statement (RuntimeAdapter.conditional_join then_exit else_exit) body
        (Runtime.Translation.Assertions.weaken_assertion post)
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state statement
          then_branch else_branch then_exit else_exit e certificate1
          certificate2 e0 e1) derivation aligned stack_in join_stack mode tail
          lifo build_then build_else) as [then_tree [else_tree [Hthen [Helse data]]]].
      exists then_tree, else_tree, Hthen, Helse.
      constructor. exact data.
    - dependent destruction certificate; simpl; try exact tt.
      intros stack_in join_stack mode tail lifo build_then build_else.
      destruct (@resource_aligned_conditional_branch_data_fix cost Γ F (t :: Δ)
        (S fuel) state statement (RuntimeAdapter.conditional_join then_exit else_exit) body post
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state statement
          then_branch else_branch then_exit else_exit e certificate1
          certificate2 e0 e1) derivation aligned stack_in join_stack mode tail
          lifo build_then build_else) as [then_tree [else_tree [Hthen [Helse data]]]].
      exists then_tree, else_tree, Hthen, Helse.
      constructor. exact data.
  Defined.

  Lemma resource_aligned_net_trace_source_eq
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source tree
        suffix trace}
      (aligned : @resource_aligned_net_trace cost Γ F Δ entry pre stack_in exit post
        stack_out mode tail source tree suffix trace) :
    source =
      resource_certificate_suffix_of_operational_suffix
        suffix.
  Proof.
    induction aligned; simpl; try reflexivity.
    - exact Hsource.
  Qed.


  Definition has_resource_aligned_ordinary_normalization
      {cost Γ F Δ entry pre stack exit post stack_out}
      (suffix : Validity.resource_aligned_operational_suffix cost Γ F Δ entry
        pre stack exit post stack_out) : Type :=
    { tree : RuntimeAdapter.net_tree None stack stack_out entry exit &
      { trace : RuntimeAdapter.net_trace cost Γ entry exit None stack stack_out
          (resource_certificate_suffix_of_operational_suffix suffix) tree &
        resource_aligned_net_trace cost Γ F Δ entry pre stack exit post
          stack_out None stack
          (resource_certificate_suffix_of_operational_suffix suffix) tree
          suffix trace } }.

  Definition has_resource_aligned_focused_normalization
      {cost Γ F Δ focused tail entry pre exit post stack_out}
      (suffix : Validity.resource_aligned_operational_suffix cost Γ F Δ entry
        pre (focused :: tail) exit post stack_out) : Type :=
    { tree : RuntimeAdapter.net_tree (Some focused) tail stack_out entry exit &
      { trace : RuntimeAdapter.net_trace cost Γ entry exit (Some focused) tail
          stack_out (resource_certificate_suffix_of_operational_suffix suffix)
          tree &
        resource_aligned_net_trace cost Γ F Δ entry pre (focused :: tail)
          exit post stack_out (Some focused) tail
          (resource_certificate_suffix_of_operational_suffix suffix) tree
          suffix trace } }.

  Definition resource_lockstep_of_normalization
      {cost Γ F Δ entry pre stack_in exit post stack_out}
      (suffix : Validity.resource_aligned_operational_suffix cost Γ F Δ entry
        pre stack_in exit post stack_out)
      (normal : @RuntimeAdapter.traced_suffix_net_normalization cost Γ entry
        exit stack_in stack_out
        (resource_certificate_suffix_of_operational_suffix suffix)) : Type :=
    @resource_aligned_net_trace cost Γ F Δ entry pre stack_in exit post
      stack_out None stack_in
      (resource_certificate_suffix_of_operational_suffix suffix)
      (RuntimeAdapter.suffix_net_tree _
        (RuntimeAdapter.traced_net_normal _ normal)) suffix
      (RuntimeAdapter.traced_net_source _ normal).

  Definition normalize_resource_aligned_done
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {state : RuntimeAdapter.Atomicity.analysis_state}
      {assertion : Runtime.Translation.Assertions.assertion Γ F Δ}
      {stack : list RuntimeAdapter.Atomicity.access_marker} :
    has_resource_aligned_ordinary_normalization
      (Validity.ResourceAlignedOperationalDone (cost := cost) state assertion
        stack).
  Proof.
    exists (@RuntimeAdapter.NetOrdinary stack stack state state
      (RuntimeAdapter.Slice.ExecDone state stack)).
    exists (@RuntimeAdapter.TraceDoneNet cost Γ state stack).
    apply ResourceAlignedTraceDone.
  Defined.

  Definition normalize_resource_aligned_focused_done
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {state : RuntimeAdapter.Atomicity.analysis_state}
      {assertion : Runtime.Translation.Assertions.assertion Γ F Δ}
      {focused : RuntimeAdapter.Atomicity.access_marker}
      {tail : list RuntimeAdapter.Atomicity.access_marker} :
    has_resource_aligned_focused_normalization
      (Validity.ResourceAlignedOperationalDone (cost := cost) state assertion
        (focused :: tail)).
  Proof.
    exists (@RuntimeAdapter.FocusNetOutcome focused tail state state
      (RuntimeAdapter.Slice.OutcomeStillOpen focused tail state state
        (RuntimeAdapter.Slice.FocusedPrefixDone focused tail state))).
    exists (@RuntimeAdapter.TraceDoneFocused cost Γ state focused tail).
    apply ResourceAlignedTraceDoneFocused.
  Defined.

  Record has_resource_aligned_total_normalization
      {cost Γ F Δ entry pre stack_in exit post stack_out}
      (suffix : Validity.resource_aligned_operational_suffix cost Γ F Δ entry
        pre stack_in exit post stack_out) : Type := {
    resource_total_ordinary :
      has_resource_aligned_ordinary_normalization suffix;
    resource_total_focused :
      match stack_in as stack return
          Validity.resource_aligned_operational_suffix cost Γ F Δ entry pre
            stack exit post stack_out -> Type
      with
      | [] => fun _ => unit
      | focused :: tail => fun focused_suffix =>
          has_resource_aligned_focused_normalization focused_suffix
      end suffix;
  }.

  Definition normalize_resource_aligned_ordinary_chunk
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        stack stack_out certificate derivation aligned lifo rest chunk}
      (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        middle stack stack certificate chunk)
      (normal_rest : has_resource_aligned_ordinary_normalization rest) :
    has_resource_aligned_ordinary_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ fuel entry
        statement middle pre middle_assertion stack stack certificate
        derivation aligned lifo exit post stack_out rest).
  Proof.
    destruct normal_rest as [rest_tree [Hrest aligned_rest]].
    eexists (@RuntimeAdapter.NetChunk stack middle stack_out entry exit chunk
      rest_tree).
    eexists (@RuntimeAdapter.TraceChunk cost Γ fuel entry statement middle
      exit stack stack_out certificate
      (resource_certificate_suffix_of_operational_suffix rest)
      chunk Hchunk rest_tree Hrest).
    eapply ResourceAlignedTraceChunk. exact aligned_rest.
  Defined.

  Definition normalize_resource_aligned_focused_prefix
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        focused tail stack_out certificate derivation aligned lifo rest chunk}
      (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        middle (focused :: tail) (focused :: tail) certificate chunk)
      (head_ok : RuntimeAdapter.Payload.preserves focused tail entry middle
        chunk)
      (normal_rest : has_resource_aligned_focused_normalization rest) :
    has_resource_aligned_focused_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ fuel entry
        statement middle pre middle_assertion (focused :: tail)
        (focused :: tail) certificate derivation aligned lifo exit post
        stack_out rest).
  Proof.
    destruct normal_rest as [rest_tree [Hrest aligned_rest]].
    eexists (@RuntimeAdapter.FocusNetPrefix focused tail stack_out entry middle
      exit chunk head_ok rest_tree).
    eexists (@RuntimeAdapter.TraceFocusedPrefix cost Γ fuel entry statement
      middle exit focused tail stack_out certificate
      (resource_certificate_suffix_of_operational_suffix rest)
      chunk Hchunk head_ok rest_tree Hrest).
    eapply ResourceAlignedTraceFocusedPrefix. exact aligned_rest.
  Defined.

  Definition normalize_resource_aligned_access
      {cost Γ F Δ fuel entry statement opened exit pre opened_assertion post
        focused tail stack_out certificate derivation aligned lifo rest opening}
      (Hopening : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        opened tail (focused :: tail) certificate opening)
      (open_ok : RuntimeAdapter.Payload.opens focused tail entry opened opening)
      (normal_body : has_resource_aligned_focused_normalization rest) :
    has_resource_aligned_ordinary_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ fuel entry statement
        opened pre opened_assertion tail (focused :: tail) certificate derivation
        aligned lifo exit post stack_out rest).
  Proof.
    destruct normal_body as [body [Hbody aligned_body]].
    eexists (@RuntimeAdapter.NetAccess tail stack_out focused entry opened exit
      opening open_ok body).
    eexists (@RuntimeAdapter.TraceAccess cost Γ fuel entry statement opened
      exit focused tail stack_out certificate
      (resource_certificate_suffix_of_operational_suffix rest)
      opening Hopening open_ok body Hbody).
    eapply ResourceAlignedTraceAccess. exact aligned_body.
  Defined.

  Definition normalize_resource_aligned_close
      {cost Γ F Δ fuel entry statement closed exit pre closed_assertion post
        focused tail stack_out certificate derivation aligned lifo rest closing}
      (Hclosing : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        closed (focused :: tail) tail certificate closing)
      (close_ok : RuntimeAdapter.Payload.closes focused tail entry closed closing)
      (normal_rest : has_resource_aligned_ordinary_normalization rest) :
    has_resource_aligned_focused_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ fuel entry statement
        closed pre closed_assertion (focused :: tail) tail certificate derivation
        aligned lifo exit post stack_out rest).
  Proof.
    destruct normal_rest as [rest_tree [Hrest aligned_rest]].
    eexists (@RuntimeAdapter.FocusNetClose focused tail stack_out entry closed
      exit (RuntimeAdapter.Slice.FocusedClose focused tail entry closed closing
        close_ok) rest_tree).
    eexists (@RuntimeAdapter.TraceFocusedClose cost Γ fuel entry statement
      closed exit focused tail stack_out certificate
      (resource_certificate_suffix_of_operational_suffix rest)
      closing Hclosing close_ok rest_tree Hrest).
    eapply ResourceAlignedTraceFocusedClose. exact aligned_rest.
  Defined.

  Definition normalize_resource_aligned_ordinary_close
      {cost Γ F Δ fuel entry statement closed exit pre closed_assertion post
        focused tail stack_out certificate derivation aligned lifo rest closing}
      (Hclosing : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        closed (focused :: tail) tail certificate closing)
      (close_ok : RuntimeAdapter.Payload.closes focused tail entry closed closing)
      (normal_rest : has_resource_aligned_ordinary_normalization rest) :
    has_resource_aligned_ordinary_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ fuel entry statement
        closed pre closed_assertion (focused :: tail) tail certificate derivation
        aligned lifo exit post stack_out rest).
  Proof.
    destruct normal_rest as [rest_tree [Hrest aligned_rest]].
    eexists (@RuntimeAdapter.NetClose focused tail stack_out entry closed exit
      closing close_ok rest_tree).
    eexists (@RuntimeAdapter.TraceClose cost Γ fuel entry statement closed exit
      focused tail stack_out certificate
      (resource_certificate_suffix_of_operational_suffix rest)
      closing Hclosing close_ok rest_tree Hrest).
    eapply ResourceAlignedTraceClose. exact aligned_rest.
  Defined.

  Definition normalize_resource_aligned_nested_access
      {cost Γ F Δ fuel entry statement opened exit pre opened_assertion post
        focused tail nested stack_out certificate derivation aligned lifo rest opening}
      (Hopening : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        opened (focused :: tail) (nested :: focused :: tail) certificate opening)
      (open_ok : RuntimeAdapter.Payload.opens nested (focused :: tail) entry opened opening)
      (normal_body : has_resource_aligned_focused_normalization rest) :
    has_resource_aligned_focused_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ fuel entry statement
        opened pre opened_assertion (focused :: tail) (nested :: focused :: tail)
        certificate derivation aligned lifo exit post stack_out rest).
  Proof.
    destruct normal_body as [body [Hbody aligned_body]].
    eexists (@RuntimeAdapter.FocusNetNested focused tail stack_out nested entry
      opened exit opening open_ok body).
    eexists (@RuntimeAdapter.TraceNestedAccess cost Γ fuel entry statement
      opened exit focused tail nested stack_out certificate
      (resource_certificate_suffix_of_operational_suffix rest)
      opening Hopening open_ok body Hbody).
    eapply ResourceAlignedTraceNestedAccess. exact aligned_body.
  Defined.

  Definition has_aligned_ordinary_normalization
      {cost Γ F Δ entry pre stack exit post stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre
        stack exit post stack_out) : Type :=
    { tree : RuntimeAdapter.net_tree None stack stack_out entry exit &
      { trace : RuntimeAdapter.net_trace cost Γ entry exit None stack stack_out
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            suffix) tree &
        aligned_net_trace cost Γ F Δ entry pre stack exit post stack_out None
          stack
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            suffix) tree suffix trace } }.

  Definition has_aligned_focused_normalization
      {cost Γ F Δ focused tail entry pre exit post stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre
        (focused :: tail) exit post stack_out) : Type :=
    { tree : RuntimeAdapter.net_tree (Some focused) tail stack_out entry exit &
      { trace : RuntimeAdapter.net_trace cost Γ entry exit (Some focused) tail
          stack_out
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            suffix) tree &
        aligned_net_trace cost Γ F Δ entry pre (focused :: tail) exit post
          stack_out (Some focused) tail
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            suffix) tree suffix trace } }.

  (** A certificate-boundary factorization used by the direct-close and
      preserving-prefix cases.  This is deliberately not the semantic
      interface for the general focused proof: a conditional may close the
      focus at different states in its two arms and retain branch-local
      post-close work.  Those cases must be interpreted through
      [Slice.focused_execution]/[Slice.closed_branch], rather than by placing
      this whole linear prefix under one atomic-mask bracket. *)
  Record aligned_focused_close_split
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source tree
        suffix trace}
      (aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace) : Type := {
    aligned_split_close_state : RuntimeAdapter.Atomicity.analysis_state;
    aligned_split_close_assertion :
      Runtime.Translation.Assertions.assertion Γ F Δ;
    aligned_split_prefix : Validity.aligned_operational_suffix cost Γ F Δ
      entry pre ((invariant, outer) :: tail) aligned_split_close_state
      aligned_split_close_assertion tail;
    aligned_split_rest : Validity.aligned_operational_suffix cost Γ F Δ
      aligned_split_close_state aligned_split_close_assertion tail exit post
      stack_out;
    aligned_split_prefix_tree : RuntimeAdapter.focused_net
      (invariant, outer) tail tail entry aligned_split_close_state;
    aligned_split_rest_tree : RuntimeAdapter.normalized_net tail stack_out
      aligned_split_close_state exit;
    aligned_split_prefix_trace : RuntimeAdapter.net_trace cost Γ entry
      aligned_split_close_state (Some (invariant, outer)) tail tail
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
        aligned_split_prefix) aligned_split_prefix_tree;
    aligned_split_rest_trace : RuntimeAdapter.net_trace cost Γ
      aligned_split_close_state exit None tail stack_out
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
        aligned_split_rest) aligned_split_rest_tree;
    aligned_split_prefix_lockstep : aligned_net_trace cost Γ F Δ entry pre
      ((invariant, outer) :: tail) aligned_split_close_state
      aligned_split_close_assertion tail (Some (invariant, outer)) tail
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
        aligned_split_prefix) aligned_split_prefix_tree aligned_split_prefix
      aligned_split_prefix_trace;
    aligned_split_rest_lockstep : aligned_net_trace cost Γ F Δ
      aligned_split_close_state aligned_split_close_assertion tail exit post
      stack_out None tail
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
        aligned_split_rest) aligned_split_rest_tree aligned_split_rest
      aligned_split_rest_trace;
    aligned_split_source_expansion : RuntimeAdapter.suffix_expands cost Γ entry
      exit
      (RuntimeAdapter.append_suffix
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          aligned_split_prefix)
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          aligned_split_rest)) source;
  }.

  Lemma suffix_iris_wp_append
      {cost Γ entry middle exit}
      (prefix : RuntimeAdapter.certificate_suffix cost Γ entry middle)
      (rest : RuntimeAdapter.certificate_suffix cost Γ middle exit)
      (runtime : Validity.Model.stack_context Γ) ambient post :
    Normalized.suffix_iris_wp
      (RuntimeAdapter.append_suffix prefix rest) runtime ambient post =
    Normalized.suffix_iris_wp prefix runtime ambient
      (Normalized.suffix_iris_wp rest runtime ambient post).
  Proof.
    induction prefix; simpl; first reflexivity.
    rewrite IHprefix. reflexivity.
  Qed.

  Lemma aligned_focused_close_split_trace_iris_wp
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (split : aligned_focused_close_split aligned_trace)
      (runtime : Validity.Model.stack_context Γ) ambient final :
    Normalized.trace_iris_wp trace runtime ambient final =
    Normalized.trace_iris_wp (aligned_split_prefix_trace _ split)
      runtime ambient
      (Normalized.trace_iris_wp (aligned_split_rest_trace _ split)
        runtime ambient final).
  Proof.
    repeat rewrite Normalized.trace_iris_wp_is_suffix_iris_wp.
    rewrite <- suffix_iris_wp_append.
    symmetry. apply Normalized.suffix_expands_iris_wp.
    exact (aligned_split_source_expansion _ split).
  Qed.

  Definition aligned_focused_close_split_here
      {cost Γ F Δ fuel entry statement closed exit pre closed_assertion post
        invariant outer tail stack_out certificate derivation aligned lifo rest
        closing}
      (Hclosing : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        closed ((invariant, outer) :: tail) tail certificate closing)
      (close_ok : RuntimeAdapter.Payload.closes (invariant, outer) tail entry
        closed closing)
      {rest_tree : RuntimeAdapter.normalized_net tail stack_out closed exit}
      {Hrest : RuntimeAdapter.net_trace cost Γ closed exit None tail stack_out
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest) rest_tree}
      (aligned_rest : aligned_net_trace cost Γ F Δ closed closed_assertion tail
        exit post stack_out None tail
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest) rest_tree rest Hrest) :
    aligned_focused_close_split
      (@AlignedTraceFocusedClose cost Γ F Δ fuel entry statement closed exit pre
        closed_assertion post (invariant, outer) tail stack_out certificate
        derivation aligned lifo rest closing Hclosing close_ok rest_tree Hrest
        aligned_rest).
  Proof.
    let prefix := constr:(@Validity.AlignedOperationalCons cost Γ F Δ fuel
      entry statement closed pre closed_assertion ((invariant, outer) :: tail)
      tail certificate derivation aligned lifo closed closed_assertion tail
      (Validity.AlignedOperationalDone closed closed_assertion tail)) in
    refine {| aligned_split_close_state := closed;
              aligned_split_close_assertion := closed_assertion;
              aligned_split_prefix := prefix;
              aligned_split_rest := rest;
              aligned_split_prefix_tree :=
                @RuntimeAdapter.FocusNetClose (invariant, outer) tail tail
                  entry closed closed
                  (RuntimeAdapter.Slice.FocusedClose (invariant, outer) tail
                    entry closed closing close_ok)
                  (@RuntimeAdapter.NetOrdinary tail tail closed closed
                    (RuntimeAdapter.Slice.ExecDone closed tail));
              aligned_split_rest_tree := rest_tree;
              aligned_split_prefix_trace :=
                @RuntimeAdapter.TraceFocusedClose cost Γ fuel entry statement
                  closed closed (invariant, outer) tail tail certificate
                  (RuntimeAdapter.SuffixDone closed) closing Hclosing close_ok
                  (@RuntimeAdapter.NetOrdinary tail tail closed closed
                    (RuntimeAdapter.Slice.ExecDone closed tail))
                  (@RuntimeAdapter.TraceDoneNet cost Γ closed tail);
              aligned_split_rest_trace := Hrest |}.
    - eapply AlignedTraceFocusedClose. apply AlignedTraceDone.
    - exact aligned_rest.
    - apply RuntimeAdapter.ExpandsRefl.
  Defined.

  Definition aligned_focused_close_split_later
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        invariant outer tail stack_out certificate derivation aligned lifo rest
        chunk}
      (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        middle ((invariant, outer) :: tail) ((invariant, outer) :: tail)
        certificate chunk)
      (head_ok : RuntimeAdapter.Payload.preserves (invariant, outer) tail entry
        middle chunk)
      {rest_tree : RuntimeAdapter.focused_net (invariant, outer) tail stack_out
        middle exit}
      {Hrest : RuntimeAdapter.net_trace cost Γ middle exit
        (Some (invariant, outer)) tail stack_out
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest) rest_tree}
      (aligned_rest : aligned_net_trace cost Γ F Δ middle middle_assertion
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest) rest_tree rest Hrest)
      (split : aligned_focused_close_split aligned_rest) :
    aligned_focused_close_split
      (@AlignedTraceFocusedPrefix cost Γ F Δ fuel entry statement middle exit
        pre middle_assertion post (invariant, outer) tail stack_out certificate
        derivation aligned lifo rest chunk Hchunk head_ok rest_tree Hrest
        aligned_rest).
  Proof.
    destruct split as [closed close_assertion prefix suffix prefix_tree
      suffix_tree prefix_trace suffix_trace aligned_prefix aligned_suffix
      expansion].
    let extended_prefix := constr:(@Validity.AlignedOperationalCons cost Γ F Δ
      fuel entry statement middle pre middle_assertion
      ((invariant, outer) :: tail) ((invariant, outer) :: tail) certificate
      derivation aligned lifo closed close_assertion tail prefix) in
    refine {| aligned_split_close_state := closed;
              aligned_split_close_assertion := close_assertion;
              aligned_split_prefix := extended_prefix;
              aligned_split_rest := suffix;
              aligned_split_prefix_tree :=
                @RuntimeAdapter.FocusNetPrefix (invariant, outer) tail tail
                  entry middle closed chunk head_ok prefix_tree;
              aligned_split_rest_tree := suffix_tree;
              aligned_split_prefix_trace :=
                @RuntimeAdapter.TraceFocusedPrefix cost Γ fuel entry statement
                  middle closed (invariant, outer) tail tail certificate
                  (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
                    prefix) chunk Hchunk head_ok prefix_tree prefix_trace;
              aligned_split_rest_trace := suffix_trace |}.
    - eapply AlignedTraceFocusedPrefix. exact aligned_prefix.
    - exact aligned_suffix.
    - apply RuntimeAdapter.ExpandsCons. exact expansion.
  Defined.

  Definition aligned_focused_close_split_conditional_here
      {cost Γ F Δ fuel entry statement then_statement else_statement
        then_exit else_exit exit pre join_assertion post invariant outer tail
        stack_out view then_certificate else_certificate open_equal atomic_equal
        derivation aligned lifo rest then_tree else_tree rest_tree}
      (Hthen : RuntimeAdapter.net_trace cost Γ entry then_exit
        (Some (invariant, outer)) tail tail
        (RuntimeAdapter.SuffixCons then_certificate
          (RuntimeAdapter.SuffixDone then_exit)) then_tree)
      (Helse : RuntimeAdapter.net_trace cost Γ entry else_exit
        (Some (invariant, outer)) tail tail
        (RuntimeAdapter.SuffixCons else_certificate
          (RuntimeAdapter.SuffixDone else_exit)) else_tree)
      (Hrest : RuntimeAdapter.net_trace cost Γ
        (RuntimeAdapter.conditional_join then_exit else_exit) exit None tail
        stack_out
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest) rest_tree)
      (aligned_rest : aligned_net_trace cost Γ F Δ
        (RuntimeAdapter.conditional_join then_exit else_exit) join_assertion tail
        exit post stack_out None tail
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest) rest_tree rest Hrest) :
    aligned_focused_close_split
      (@AlignedTraceFocusedConditional cost Γ F Δ fuel entry statement
        then_statement else_statement then_exit else_exit exit pre
        join_assertion post (invariant, outer) tail tail stack_out view
        then_certificate else_certificate open_equal atomic_equal derivation
        aligned lifo rest then_tree else_tree rest_tree Hthen Helse Hrest
        aligned_rest).
  Proof.
    let conditional_certificate := constr:(RuntimeAdapter.Atomicity.CertConditional
      cost Γ fuel entry statement then_statement else_statement then_exit
      else_exit view then_certificate else_certificate open_equal atomic_equal) in
    let closed := constr:(RuntimeAdapter.conditional_join then_exit else_exit) in
    let prefix := constr:(@Validity.AlignedOperationalCons cost Γ F Δ (S fuel)
      entry statement closed pre join_assertion ((invariant, outer) :: tail)
      tail conditional_certificate derivation aligned lifo closed
      join_assertion tail
      (Validity.AlignedOperationalDone closed join_assertion tail)) in
    refine {| aligned_split_close_state := closed;
              aligned_split_close_assertion := join_assertion;
              aligned_split_prefix := prefix;
              aligned_split_rest := rest;
              aligned_split_prefix_tree :=
                @RuntimeAdapter.FocusNetConditional (invariant, outer) tail tail
                  tail entry then_exit else_exit closed closed
                  (RuntimeAdapter.Payload.RavenConditional Γ fuel cost entry
                    statement then_statement else_statement then_exit else_exit
                    view then_certificate else_certificate open_equal
                    atomic_equal) then_tree else_tree
                  (@RuntimeAdapter.NetOrdinary tail tail closed closed
                    (RuntimeAdapter.Slice.ExecDone closed tail));
              aligned_split_rest_tree := rest_tree;
              aligned_split_prefix_trace :=
                @RuntimeAdapter.TraceFocusedConditional cost Γ fuel entry
                  statement then_statement else_statement then_exit else_exit
                  closed (invariant, outer) tail tail tail view then_certificate
                  else_certificate open_equal atomic_equal
                  (RuntimeAdapter.SuffixDone closed) then_tree else_tree
                  (@RuntimeAdapter.NetOrdinary tail tail closed closed
                    (RuntimeAdapter.Slice.ExecDone closed tail)) Hthen Helse
                  (@RuntimeAdapter.TraceDoneNet cost Γ closed tail);
              aligned_split_rest_trace := Hrest |}.
    - eapply AlignedTraceFocusedConditional. apply AlignedTraceDone.
    - exact aligned_rest.
    - apply RuntimeAdapter.ExpandsRefl.
  Defined.

  (** Semantic base case for the focused-slice induction.  The slice witness
      records that this fold is the first close of the current accessor; the
      Iris refinement itself is exactly the matched-fold endpoint rule. *)
  Lemma focused_close_slice_runtime_refinement
      {cost Γ F Δ fuel node invariant arguments store body entry outer tail}
      (view : Runtime.RegionSyntax.view
        (Runtime.IR.TFold node invariant arguments) =
        typed_analysis_view.TypedAnalysisView.ViewFold invariant)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hopen : invariant ∈ RuntimeAdapter.Atomicity.analysis_open entry)
      (Houter : invariant ∉ outer)
      (Hopen_eq : RuntimeAdapter.Atomicity.analysis_open entry =
        {[invariant]} ∪ outer)
      (instantiated : Contracts.instantiated_invariant Γ F Δ
        (Logic.invariant_args invariant) invariant
        (Runtime.Validation.Hoare.symbolize_expr_list store arguments) body)
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset) :
    let closing := RuntimeAdapter.Payload.ChunkFold Γ fuel cost entry
      (Runtime.IR.TFold node invariant arguments) invariant outer tail view
      Hopen Houter Hopen_eq in
    let first_close := @RuntimeAdapter.Slice.FocusedClose
      (invariant, outer) tail entry
      (RuntimeAdapter.Atomicity.fold_invariant invariant entry) closing I in
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms
       (Runtime.Translation.Assertions.AAnd
         (Runtime.Translation.Assertions.AStack store) body) ∗
     Validity.World.access_stack_interp atoms ambient
       ((invariant, outer) :: tail)) ⊢
    Validity.translated_runtime_wp runtime ambient entry
      (RuntimeAdapter.Atomicity.fold_invariant invariant entry)
      (Runtime.IR.TFold node invariant arguments)
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms
         (Runtime.Translation.Assertions.AAnd
           (Runtime.Translation.Assertions.AStack store)
           (Runtime.Translation.Assertions.AInvariant invariant
             (Runtime.Validation.Hoare.symbolize_expr_list store arguments))) ∗
       Validity.World.access_stack_interp atoms ambient tail).
  Proof.
    simpl.
    apply ConcreteAccessNodes.matched_fold_node_runtime_refinement;
      assumption.
  Qed.

  (** The direct-close endpoint already has the concrete source-WP shape.
      Keeping this conversion explicit is useful for the first focused-prefix
      slice: the erased [TFold] has no physical runtime statement, so the
      singleton source suffix reduces definitionally to the same mask-changing
      WP as the endpoint lemma above. *)
  Lemma focused_close_slice_source_runtime_refinement
      {cost Γ F Δ fuel node invariant arguments store body entry outer tail}
      (view : Runtime.RegionSyntax.view
        (Runtime.IR.TFold node invariant arguments) =
        typed_analysis_view.TypedAnalysisView.ViewFold invariant)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hopen : invariant ∈ RuntimeAdapter.Atomicity.analysis_open entry)
      (Houter : invariant ∉ outer)
      (Hopen_eq : RuntimeAdapter.Atomicity.analysis_open entry =
        {[invariant]} ∪ outer)
      (instantiated : Contracts.instantiated_invariant Γ F Δ
        (Logic.invariant_args invariant) invariant
        (Runtime.Validation.Hoare.symbolize_expr_list store arguments) body)
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms
       (Runtime.Translation.Assertions.AAnd
         (Runtime.Translation.Assertions.AStack store) body) ∗
     Validity.World.access_stack_interp atoms ambient
       ((invariant, outer) :: tail)) ⊢
    ConcreteOrdinaryTrace.source_translated_wp
      (RuntimeAdapter.SuffixCons
        (RuntimeAdapter.Atomicity.CertFold cost Γ fuel entry
          (Runtime.IR.TFold node invariant arguments) invariant view)
        (RuntimeAdapter.SuffixDone
          (RuntimeAdapter.Atomicity.fold_invariant invariant entry)))
      runtime ambient
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms
         (Runtime.Translation.Assertions.AAnd
           (Runtime.Translation.Assertions.AStack store)
           (Runtime.Translation.Assertions.AInvariant invariant
             (Runtime.Validation.Hoare.symbolize_expr_list store arguments))) ∗
       Validity.World.access_stack_interp atoms ambient tail).
  Proof.
    change ((Validity.global_world_context atoms ∗
      Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms
        (Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store) body) ∗
      Validity.World.access_stack_interp atoms ambient
        ((invariant, outer) :: tail)) ⊢
      Validity.translated_runtime_wp runtime ambient entry
        (RuntimeAdapter.Atomicity.fold_invariant invariant entry)
        (Runtime.IR.TFold node invariant arguments)
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms
           (Runtime.Translation.Assertions.AAnd
             (Runtime.Translation.Assertions.AStack store)
             (Runtime.Translation.Assertions.AInvariant invariant
               (Runtime.Validation.Hoare.symbolize_expr_list store arguments))) ∗
         Validity.World.access_stack_interp atoms ambient tail)).
    apply (focused_close_slice_runtime_refinement
      (cost := cost) (fuel := fuel));
      assumption.
  Qed.

  (** Like [has_aligned_focused_normalization], but additionally records that
      the witness closes -- i.e. is not [AlignedTraceDoneFocused] -- via the
      [aligned_focused_close_split] taken at its first matching close.  This
      is what lets a seam's own continuation start *after* that close, at
      the restored, wider mask, instead of at the seam's own (narrower)
      focused-entry mask -- see [aligned_seam_runtime_refinement] below. *)
  Definition has_aligned_focused_closing_normalization
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out) : Type :=
    { tree : RuntimeAdapter.net_tree (Some (invariant, outer)) tail stack_out
        entry exit &
      { trace : RuntimeAdapter.net_trace cost Γ entry exit
          (Some (invariant, outer)) tail stack_out
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            suffix) tree &
        { aligned_trace : aligned_net_trace cost Γ F Δ entry pre
            ((invariant, outer) :: tail) exit post stack_out
            (Some (invariant, outer)) tail
            (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
              suffix) tree suffix trace &
          aligned_focused_close_split aligned_trace } } }.

  (** A seam-indexed branch/bracket/continuation triple for the general
      (ordinary) conditional case.  A branch certificate starts unfocused, at
      whatever raw stack [tail] the conditional itself entered with (mode
      [None], matching [AlignedTraceConditional]'s own [then_tree]/
      [else_tree] shape) and normalizes, independently, all the way to its
      own analyzer exit [branch_exit], having opened [(invariant, outer)]
      internally and never closed it again.  A shared continuation
      normalizes, independently, from [conditional_join] onward, starting
      already focused on the same marker -- but, unlike a first version of
      this record, it must eventually close it again: [aligned_seam_rest]'s
      [has_aligned_focused_closing_normalization] carries the
      [aligned_focused_close_split] at that first matching close, splitting
      [rest_suffix] into [aligned_split_prefix] (up to and including the
      close) and [aligned_split_rest] (everything after, already at mode
      [None] and the wider, restored mask).  [branch_exit] and
      [conditional_join] are connected solely by [aligned_seam_mask_eq] --
      equality of the concrete Iris access mask at the seam, which
      [conditional_join]'s own definition and [open_equal] already make
      available unconditionally (see the CertConditional certificate) --
      never by equating the two states themselves, which are genuinely
      different Raven analysis states.  This is deliberately not a
      dependently appended suffix: each side keeps its own, independently
      normalized [aligned_net_trace], reusing exactly the existing
      [None]/[Some focused] machinery ([AlignedTraceAccess],
      [AlignedTraceNestedAccess], [AlignedTraceFocusedPrefix],
      [AlignedTraceFocusedClose], etc., via [has_aligned_ordinary_normalization]
      and [has_aligned_focused_closing_normalization]) rather than
      synthesizing a new structural append across two different states. *)
  Record aligned_seam_trace
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {invariant : typed_core.TypedCore.inv_id}
      {outer : gset typed_core.TypedCore.inv_id}
      {tail : list RuntimeAdapter.Atomicity.access_marker}
      {branch_entry : RuntimeAdapter.Atomicity.analysis_state}
      {branch_pre : Runtime.Translation.Assertions.assertion Γ F Δ}
      {branch_exit : RuntimeAdapter.Atomicity.analysis_state}
      {branch_post : Runtime.Translation.Assertions.assertion Γ F Δ}
      (branch_suffix : Validity.aligned_operational_suffix cost Γ F Δ
        branch_entry branch_pre tail branch_exit branch_post
        ((invariant, outer) :: tail))
      {conditional_join : RuntimeAdapter.Atomicity.analysis_state}
      {join_assertion : Runtime.Translation.Assertions.assertion Γ F Δ}
      {exit : RuntimeAdapter.Atomicity.analysis_state}
      {post : Runtime.Translation.Assertions.assertion Γ F Δ}
      {stack_out : list RuntimeAdapter.Atomicity.access_marker}
      (rest_suffix : Validity.aligned_operational_suffix cost Γ F Δ
        conditional_join join_assertion ((invariant, outer) :: tail) exit post
        stack_out)
      (ambient : coPset) : Type := {
    aligned_seam_branch : has_aligned_ordinary_normalization branch_suffix;
    aligned_seam_mask_eq : Validity.Model.active_runtime_mask ambient
      branch_exit = Validity.Model.active_runtime_mask ambient
      conditional_join;
    aligned_seam_rest : has_aligned_focused_closing_normalization rest_suffix;
  }.

  (** Resource-native factorization at the first matching close.  Runtime
      programs are related semantically through [suffix_expands], rather than
      by the false syntactic associativity equation for [RTSeq]. *)
  Record resource_aligned_focused_close_split
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source tree
        suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace) : Type := {
    resource_split_close_state : RuntimeAdapter.Atomicity.analysis_state;
    resource_split_close_assertion :
      Runtime.Translation.Assertions.assertion Γ F Δ;
    resource_split_prefix : Validity.resource_aligned_operational_suffix cost Γ F Δ
      entry pre ((invariant, outer) :: tail) resource_split_close_state
      resource_split_close_assertion tail;
    resource_split_rest : Validity.resource_aligned_operational_suffix cost Γ F Δ
      resource_split_close_state resource_split_close_assertion tail exit post
      stack_out;
    resource_split_prefix_tree : RuntimeAdapter.focused_net
      (invariant, outer) tail tail entry resource_split_close_state;
    resource_split_rest_tree : RuntimeAdapter.normalized_net tail stack_out
      resource_split_close_state exit;
    resource_split_prefix_trace : RuntimeAdapter.net_trace cost Γ entry
      resource_split_close_state (Some (invariant, outer)) tail tail
      (resource_certificate_suffix_of_operational_suffix resource_split_prefix)
      resource_split_prefix_tree;
    resource_split_rest_trace : RuntimeAdapter.net_trace cost Γ
      resource_split_close_state exit None tail stack_out
      (resource_certificate_suffix_of_operational_suffix resource_split_rest)
      resource_split_rest_tree;
    resource_split_prefix_lockstep : resource_aligned_net_trace cost Γ F Δ
      entry pre ((invariant, outer) :: tail) resource_split_close_state
      resource_split_close_assertion tail (Some (invariant, outer)) tail
      (resource_certificate_suffix_of_operational_suffix resource_split_prefix)
      resource_split_prefix_tree resource_split_prefix resource_split_prefix_trace;
    resource_split_rest_lockstep : resource_aligned_net_trace cost Γ F Δ
      resource_split_close_state resource_split_close_assertion tail exit post
      stack_out None tail
      (resource_certificate_suffix_of_operational_suffix resource_split_rest)
      resource_split_rest_tree resource_split_rest resource_split_rest_trace;
    resource_split_source_expansion : RuntimeAdapter.suffix_expands cost Γ entry exit
      (RuntimeAdapter.append_suffix
        (resource_certificate_suffix_of_operational_suffix resource_split_prefix)
        (resource_certificate_suffix_of_operational_suffix resource_split_rest)) source;
  }.

  (** General close-stack search.  Unlike the seam-facing specialization,
      the marker being searched for may lie below the currently focused
      head (the nested-access case). *)
  Record resource_aligned_close_stack_split
      {cost Γ F Δ entry pre stack_in exit post stack_out mode focus_tail
        source tree suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        stack_in exit post stack_out mode focus_tail source tree suffix trace)
      (close_stack : list RuntimeAdapter.Atomicity.access_marker) : Type := {
    resource_close_stack_state : RuntimeAdapter.Atomicity.analysis_state;
    resource_close_stack_assertion :
      Runtime.Translation.Assertions.assertion Γ F Δ;
    resource_close_stack_prefix : Validity.resource_aligned_operational_suffix
      cost Γ F Δ entry pre stack_in resource_close_stack_state
      resource_close_stack_assertion close_stack;
    resource_close_stack_rest : Validity.resource_aligned_operational_suffix
      cost Γ F Δ resource_close_stack_state resource_close_stack_assertion
      close_stack exit post stack_out;
    resource_close_stack_prefix_tree : RuntimeAdapter.net_tree mode focus_tail
      close_stack entry resource_close_stack_state;
    resource_close_stack_rest_tree : RuntimeAdapter.normalized_net close_stack
      stack_out resource_close_stack_state exit;
    resource_close_stack_prefix_trace : RuntimeAdapter.net_trace cost Γ entry
      resource_close_stack_state mode focus_tail close_stack
      (resource_certificate_suffix_of_operational_suffix
        resource_close_stack_prefix) resource_close_stack_prefix_tree;
    resource_close_stack_rest_trace : RuntimeAdapter.net_trace cost Γ
      resource_close_stack_state exit None close_stack stack_out
      (resource_certificate_suffix_of_operational_suffix
        resource_close_stack_rest) resource_close_stack_rest_tree;
    resource_close_stack_prefix_lockstep : resource_aligned_net_trace cost Γ F Δ
      entry pre stack_in resource_close_stack_state
      resource_close_stack_assertion close_stack mode focus_tail
      (resource_certificate_suffix_of_operational_suffix
        resource_close_stack_prefix) resource_close_stack_prefix_tree
      resource_close_stack_prefix resource_close_stack_prefix_trace;
    resource_close_stack_rest_lockstep : resource_aligned_net_trace cost Γ F Δ
      resource_close_stack_state resource_close_stack_assertion close_stack exit
      post stack_out None close_stack
      (resource_certificate_suffix_of_operational_suffix
        resource_close_stack_rest) resource_close_stack_rest_tree
      resource_close_stack_rest resource_close_stack_rest_trace;
    resource_close_stack_source_expansion : RuntimeAdapter.suffix_expands cost Γ
      entry exit
      (RuntimeAdapter.append_suffix
        (resource_certificate_suffix_of_operational_suffix
          resource_close_stack_prefix)
        (resource_certificate_suffix_of_operational_suffix
          resource_close_stack_rest)) source;
  }.

  Definition resource_close_stack_split_of_focused
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (split : resource_aligned_focused_close_split aligned_trace) :
    resource_aligned_close_stack_split aligned_trace tail.
  Proof.
    destruct split.
    econstructor; eassumption.
  Defined.

  Definition resource_focused_split_of_close_stack
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (split : resource_aligned_close_stack_split aligned_trace tail) :
    resource_aligned_focused_close_split aligned_trace.
  Proof.
    destruct split.
    econstructor; eassumption.
  Defined.

  Definition resource_aligned_close_stack_split_nested
      {cost Γ F Δ fuel entry statement opened exit pre opened_assertion post
        focused tail nested stack_out certificate derivation aligned lifo rest
        opening Hopening open_ok body Hbody}
      (aligned_body : resource_aligned_net_trace cost Γ F Δ opened
        opened_assertion (nested :: focused :: tail) exit post stack_out
        (Some nested) (focused :: tail)
        (resource_certificate_suffix_of_operational_suffix rest) body rest Hbody)
      {close_stack}
      (split : resource_aligned_close_stack_split aligned_body close_stack) :
    resource_aligned_close_stack_split
      (@ResourceAlignedTraceNestedAccess cost Γ F Δ fuel entry statement
        opened exit pre opened_assertion post focused tail nested stack_out
        certificate derivation aligned lifo rest opening Hopening open_ok body
        Hbody aligned_body) close_stack.
  Proof.
    destruct split as [closed close_assertion prefix suffix prefix_tree
      suffix_tree prefix_trace suffix_trace aligned_prefix aligned_suffix
      expansion].
    let extended_prefix := constr:(@Validity.ResourceAlignedOperationalCons cost
      Γ F Δ fuel entry statement opened pre opened_assertion
      (focused :: tail) (nested :: focused :: tail) certificate derivation
      aligned lifo closed close_assertion close_stack prefix) in
    refine {| resource_close_stack_state := closed;
              resource_close_stack_assertion := close_assertion;
              resource_close_stack_prefix := extended_prefix;
              resource_close_stack_rest := suffix;
              resource_close_stack_prefix_tree :=
                @RuntimeAdapter.FocusNetNested focused tail close_stack nested
                  entry opened closed opening open_ok prefix_tree;
              resource_close_stack_rest_tree := suffix_tree;
              resource_close_stack_prefix_trace :=
                @RuntimeAdapter.TraceNestedAccess cost Γ fuel entry statement
                  opened closed focused tail nested close_stack certificate
                  (resource_certificate_suffix_of_operational_suffix prefix)
                  opening Hopening open_ok prefix_tree prefix_trace;
              resource_close_stack_rest_trace := suffix_trace |}.
    - eapply ResourceAlignedTraceNestedAccess. exact aligned_prefix.
    - exact aligned_suffix.
    - apply RuntimeAdapter.ExpandsCons. exact expansion.
  Defined.

  Definition resource_aligned_close_stack_split_expansion
      {cost Γ F Δ entry pre stack_in exit post stack_out mode focus_tail
        source tree suffix flat flat_suffix expansion Hsource Hflat_source
        flat_trace}
      (aligned_flat : resource_aligned_net_trace cost Γ F Δ entry pre stack_in
        exit post stack_out mode focus_tail flat tree flat_suffix flat_trace)
      {close_stack}
      (split : resource_aligned_close_stack_split aligned_flat close_stack) :
    resource_aligned_close_stack_split
      (@ResourceAlignedTraceExpansion cost Γ F Δ entry pre stack_in exit post
        stack_out mode focus_tail source tree suffix flat flat_suffix expansion
        Hsource Hflat_source flat_trace aligned_flat) close_stack.
  Proof.
    destruct split as [closed close_assertion prefix rest prefix_tree rest_tree
      prefix_trace rest_trace aligned_prefix aligned_rest split_expansion].
    refine {| resource_close_stack_state := closed;
              resource_close_stack_assertion := close_assertion;
              resource_close_stack_prefix := prefix;
              resource_close_stack_rest := rest;
              resource_close_stack_prefix_tree := prefix_tree;
              resource_close_stack_rest_tree := rest_tree;
              resource_close_stack_prefix_trace := prefix_trace;
              resource_close_stack_rest_trace := rest_trace;
              resource_close_stack_prefix_lockstep := aligned_prefix;
              resource_close_stack_rest_lockstep := aligned_rest |}.
    eapply RuntimeAdapter.ExpandsTrans.
    - exact split_expansion.
    - exact expansion.
  Defined.

  Lemma resource_aligned_focused_close_split_trace_iris_wp
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (split : resource_aligned_focused_close_split aligned_trace)
      (runtime : Validity.Model.stack_context Γ) ambient final :
    Normalized.trace_iris_wp trace runtime ambient final =
    Normalized.trace_iris_wp (resource_split_prefix_trace _ split) runtime ambient
      (Normalized.trace_iris_wp (resource_split_rest_trace _ split)
        runtime ambient final).
  Proof.
    repeat rewrite Normalized.trace_iris_wp_is_suffix_iris_wp.
    rewrite <- suffix_iris_wp_append.
    symmetry. apply Normalized.suffix_expands_iris_wp.
    exact (resource_split_source_expansion _ split).
  Qed.

  Definition resource_aligned_focused_close_split_here
      {cost Γ F Δ fuel entry statement closed exit pre closed_assertion post
        invariant outer tail stack_out certificate derivation aligned lifo rest
        closing}
      (Hclosing : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        closed ((invariant, outer) :: tail) tail certificate closing)
      (close_ok : RuntimeAdapter.Payload.closes (invariant, outer) tail entry
        closed closing)
      {rest_tree : RuntimeAdapter.normalized_net tail stack_out closed exit}
      {Hrest : RuntimeAdapter.net_trace cost Γ closed exit None tail stack_out
        (resource_certificate_suffix_of_operational_suffix rest) rest_tree}
      (aligned_rest : resource_aligned_net_trace cost Γ F Δ closed
        closed_assertion tail exit post stack_out None tail
        (resource_certificate_suffix_of_operational_suffix rest) rest_tree rest
        Hrest) :
    resource_aligned_focused_close_split
      (@ResourceAlignedTraceFocusedClose cost Γ F Δ fuel entry statement
        closed exit pre closed_assertion post (invariant, outer) tail stack_out
        certificate derivation aligned lifo rest closing Hclosing close_ok
        rest_tree Hrest aligned_rest).
  Proof.
    let prefix := constr:(@Validity.ResourceAlignedOperationalCons cost Γ F Δ
      fuel entry statement closed pre closed_assertion
      ((invariant, outer) :: tail) tail certificate derivation aligned lifo
      closed closed_assertion tail
      (Validity.ResourceAlignedOperationalDone closed closed_assertion tail)) in
    refine {| resource_split_close_state := closed;
              resource_split_close_assertion := closed_assertion;
              resource_split_prefix := prefix;
              resource_split_rest := rest;
              resource_split_prefix_tree :=
                @RuntimeAdapter.FocusNetClose (invariant, outer) tail tail
                  entry closed closed
                  (RuntimeAdapter.Slice.FocusedClose (invariant, outer) tail
                    entry closed closing close_ok)
                  (@RuntimeAdapter.NetOrdinary tail tail closed closed
                    (RuntimeAdapter.Slice.ExecDone closed tail));
              resource_split_rest_tree := rest_tree;
              resource_split_prefix_trace :=
                @RuntimeAdapter.TraceFocusedClose cost Γ fuel entry statement
                  closed closed (invariant, outer) tail tail certificate
                  (RuntimeAdapter.SuffixDone closed) closing Hclosing close_ok
                  (@RuntimeAdapter.NetOrdinary tail tail closed closed
                    (RuntimeAdapter.Slice.ExecDone closed tail))
                  (@RuntimeAdapter.TraceDoneNet cost Γ closed tail);
              resource_split_rest_trace := Hrest |}.
    - eapply ResourceAlignedTraceFocusedClose. apply ResourceAlignedTraceDone.
    - exact aligned_rest.
    - apply RuntimeAdapter.ExpandsRefl.
  Defined.

  Definition resource_aligned_focused_close_split_later
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        invariant outer tail stack_out certificate derivation aligned lifo rest
        chunk}
      (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        middle ((invariant, outer) :: tail) ((invariant, outer) :: tail)
        certificate chunk)
      (head_ok : RuntimeAdapter.Payload.preserves (invariant, outer) tail entry
        middle chunk)
      {rest_tree : RuntimeAdapter.focused_net (invariant, outer) tail stack_out
        middle exit}
      {Hrest : RuntimeAdapter.net_trace cost Γ middle exit
        (Some (invariant, outer)) tail stack_out
        (resource_certificate_suffix_of_operational_suffix rest) rest_tree}
      (aligned_rest : resource_aligned_net_trace cost Γ F Δ middle
        middle_assertion ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail
        (resource_certificate_suffix_of_operational_suffix rest) rest_tree rest
        Hrest)
      (split : resource_aligned_focused_close_split aligned_rest) :
    resource_aligned_focused_close_split
      (@ResourceAlignedTraceFocusedPrefix cost Γ F Δ fuel entry statement
        middle exit pre middle_assertion post (invariant, outer) tail stack_out
        certificate derivation aligned lifo rest chunk Hchunk head_ok rest_tree
        Hrest aligned_rest).
  Proof.
    destruct split as [closed close_assertion prefix suffix prefix_tree
      suffix_tree prefix_trace suffix_trace aligned_prefix aligned_suffix
      expansion].
    let extended_prefix := constr:(@Validity.ResourceAlignedOperationalCons cost
      Γ F Δ fuel entry statement middle pre middle_assertion
      ((invariant, outer) :: tail) ((invariant, outer) :: tail) certificate
      derivation aligned lifo closed close_assertion tail prefix) in
    refine {| resource_split_close_state := closed;
              resource_split_close_assertion := close_assertion;
              resource_split_prefix := extended_prefix;
              resource_split_rest := suffix;
              resource_split_prefix_tree :=
                @RuntimeAdapter.FocusNetPrefix (invariant, outer) tail tail
                  entry middle closed chunk head_ok prefix_tree;
              resource_split_rest_tree := suffix_tree;
              resource_split_prefix_trace :=
                @RuntimeAdapter.TraceFocusedPrefix cost Γ fuel entry statement
                  middle closed (invariant, outer) tail tail certificate
                  (resource_certificate_suffix_of_operational_suffix prefix)
                  chunk Hchunk head_ok prefix_tree prefix_trace;
              resource_split_rest_trace := suffix_trace |}.
    - eapply ResourceAlignedTraceFocusedPrefix. exact aligned_prefix.
    - exact aligned_suffix.
    - apply RuntimeAdapter.ExpandsCons. exact expansion.
  Defined.

  Definition resource_aligned_focused_close_split_conditional_here
      {cost Γ F Δ fuel entry statement then_statement else_statement
        then_exit else_exit exit pre join_assertion post invariant outer tail
        stack_out view then_certificate else_certificate open_equal atomic_equal
        derivation aligned lifo rest then_tree else_tree rest_tree}
      (Hthen : RuntimeAdapter.net_trace cost Γ entry then_exit
        (Some (invariant, outer)) tail tail
        (RuntimeAdapter.SuffixCons then_certificate
          (RuntimeAdapter.SuffixDone then_exit)) then_tree)
      (Helse : RuntimeAdapter.net_trace cost Γ entry else_exit
        (Some (invariant, outer)) tail tail
        (RuntimeAdapter.SuffixCons else_certificate
          (RuntimeAdapter.SuffixDone else_exit)) else_tree)
      (Hrest : RuntimeAdapter.net_trace cost Γ
        (RuntimeAdapter.conditional_join then_exit else_exit) exit None tail
        stack_out (resource_certificate_suffix_of_operational_suffix rest)
        rest_tree)
      (branch_data : @resource_conditional_branch_data cost Γ F Δ fuel entry
        statement then_statement else_statement then_exit else_exit pre
        join_assertion view then_certificate else_certificate open_equal
        atomic_equal derivation aligned ((invariant, outer) :: tail) tail
        (Some (invariant, outer)) tail then_tree else_tree lifo Hthen Helse)
      (aligned_rest : resource_aligned_net_trace cost Γ F Δ
        (RuntimeAdapter.conditional_join then_exit else_exit) join_assertion tail
        exit post stack_out None tail
        (resource_certificate_suffix_of_operational_suffix rest) rest_tree rest
        Hrest) :
    resource_aligned_focused_close_split
      (@ResourceAlignedTraceFocusedConditional cost Γ F Δ fuel entry
        statement then_statement else_statement then_exit else_exit exit pre
        join_assertion post (invariant, outer) tail tail stack_out view
        then_certificate else_certificate open_equal atomic_equal derivation
        aligned lifo rest then_tree else_tree rest_tree Hthen Helse Hrest
        branch_data aligned_rest).
  Proof.
    let conditional_certificate := constr:(RuntimeAdapter.Atomicity.CertConditional
      cost Γ fuel entry statement then_statement else_statement then_exit
      else_exit view then_certificate else_certificate open_equal atomic_equal) in
    let closed := constr:(RuntimeAdapter.conditional_join then_exit else_exit) in
    let prefix := constr:(@Validity.ResourceAlignedOperationalCons cost Γ F Δ
      (S fuel) entry statement closed pre join_assertion
      ((invariant, outer) :: tail) tail conditional_certificate derivation
      aligned lifo closed join_assertion tail
      (Validity.ResourceAlignedOperationalDone closed join_assertion tail)) in
    refine {| resource_split_close_state := closed;
              resource_split_close_assertion := join_assertion;
              resource_split_prefix := prefix;
              resource_split_rest := rest;
              resource_split_prefix_tree :=
                @RuntimeAdapter.FocusNetConditional (invariant, outer) tail tail
                  tail entry then_exit else_exit closed closed
                  (RuntimeAdapter.Payload.RavenConditional Γ fuel cost entry
                    statement then_statement else_statement then_exit else_exit
                    view then_certificate else_certificate open_equal
                    atomic_equal) then_tree else_tree
                  (@RuntimeAdapter.NetOrdinary tail tail closed closed
                    (RuntimeAdapter.Slice.ExecDone closed tail));
              resource_split_rest_tree := rest_tree;
              resource_split_prefix_trace :=
                @RuntimeAdapter.TraceFocusedConditional cost Γ fuel entry
                  statement then_statement else_statement then_exit else_exit
                  closed (invariant, outer) tail tail tail view then_certificate
                  else_certificate open_equal atomic_equal
                  (RuntimeAdapter.SuffixDone closed) then_tree else_tree
                  (@RuntimeAdapter.NetOrdinary tail tail closed closed
                    (RuntimeAdapter.Slice.ExecDone closed tail)) Hthen Helse
                  (@RuntimeAdapter.TraceDoneNet cost Γ closed tail);
              resource_split_rest_trace := Hrest |}.
    - constructor; [exact branch_data | apply ResourceAlignedTraceDone].
    - exact aligned_rest.
    - apply RuntimeAdapter.ExpandsRefl.
  Defined.

  Definition resource_aligned_focused_close_split_conditional_later
      {cost Γ F Δ fuel entry statement then_statement else_statement
        then_exit else_exit exit pre join_assertion post invariant outer tail
        stack_out view then_certificate else_certificate open_equal atomic_equal
        derivation aligned lifo rest then_tree else_tree rest_tree Hthen Helse
        Hrest}
      (branch_data : @resource_conditional_branch_data cost Γ F Δ fuel entry
        statement then_statement else_statement then_exit else_exit pre
        join_assertion view then_certificate else_certificate open_equal
        atomic_equal derivation aligned ((invariant, outer) :: tail)
        ((invariant, outer) :: tail) (Some (invariant, outer)) tail then_tree
        else_tree lifo Hthen Helse)
      (aligned_rest : resource_aligned_net_trace cost Γ F Δ
        (RuntimeAdapter.conditional_join then_exit else_exit) join_assertion
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail
        (resource_certificate_suffix_of_operational_suffix rest) rest_tree rest
        Hrest)
      (split : resource_aligned_focused_close_split aligned_rest) :
    resource_aligned_focused_close_split
      (@ResourceAlignedTraceFocusedConditionalContinue cost Γ F Δ fuel
        entry statement then_statement else_statement then_exit else_exit exit
        pre join_assertion post (invariant, outer) tail stack_out view
        then_certificate else_certificate open_equal atomic_equal derivation
        aligned lifo rest then_tree else_tree rest_tree Hthen Helse Hrest
        branch_data aligned_rest).
  Proof.
    destruct split as [closed close_assertion prefix suffix prefix_tree
      suffix_tree prefix_trace suffix_trace aligned_prefix aligned_suffix
      expansion].
    let certificate := constr:(RuntimeAdapter.Atomicity.CertConditional cost Γ
      fuel entry statement then_statement else_statement then_exit else_exit
      view then_certificate else_certificate open_equal atomic_equal) in
    let extended_prefix := constr:(@Validity.ResourceAlignedOperationalCons cost
      Γ F Δ (S fuel) entry statement
      (RuntimeAdapter.conditional_join then_exit else_exit) pre join_assertion
      ((invariant, outer) :: tail) ((invariant, outer) :: tail) certificate
      derivation aligned lifo closed close_assertion tail prefix) in
    refine {| resource_split_close_state := closed;
              resource_split_close_assertion := close_assertion;
              resource_split_prefix := extended_prefix;
              resource_split_rest := suffix;
              resource_split_prefix_tree :=
                @RuntimeAdapter.FocusNetConditionalContinue (invariant, outer)
                  tail tail entry then_exit else_exit
                  (RuntimeAdapter.conditional_join then_exit else_exit) closed
                  (RuntimeAdapter.Payload.RavenConditional Γ fuel cost entry
                    statement then_statement else_statement then_exit else_exit
                    view then_certificate else_certificate open_equal
                    atomic_equal) then_tree else_tree prefix_tree;
              resource_split_rest_tree := suffix_tree;
              resource_split_prefix_trace :=
                @RuntimeAdapter.TraceFocusedConditionalContinue cost Γ fuel
                  entry statement then_statement else_statement then_exit
                  else_exit closed (invariant, outer) tail tail view
                  then_certificate else_certificate open_equal atomic_equal
                  (resource_certificate_suffix_of_operational_suffix prefix)
                  then_tree else_tree prefix_tree Hthen Helse prefix_trace;
              resource_split_rest_trace := suffix_trace |}.
    - constructor; [exact branch_data | exact aligned_prefix].
    - exact aligned_suffix.
    - apply RuntimeAdapter.ExpandsCons. exact expansion.
  Defined.

  Definition has_resource_aligned_focused_closing_normalization
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out}
      (suffix : Validity.resource_aligned_operational_suffix cost Γ F Δ entry
        pre ((invariant, outer) :: tail) exit post stack_out) : Type :=
    { tree : RuntimeAdapter.net_tree (Some (invariant, outer)) tail stack_out
        entry exit &
      { trace : RuntimeAdapter.net_trace cost Γ entry exit
          (Some (invariant, outer)) tail stack_out
          (resource_certificate_suffix_of_operational_suffix suffix) tree &
        { aligned_trace : resource_aligned_net_trace cost Γ F Δ entry pre
            ((invariant, outer) :: tail) exit post stack_out
            (Some (invariant, outer)) tail
            (resource_certificate_suffix_of_operational_suffix suffix) tree
            suffix trace &
          resource_aligned_focused_close_split aligned_trace } } }.

  (** Resource seam carrier.  Its branch and continuation retain resource
      operational suffixes; the continuation additionally carries its
      resource-native first-close factorization. *)
  Record resource_aligned_seam_trace
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {invariant : typed_core.TypedCore.inv_id} {outer : gset typed_core.TypedCore.inv_id}
      {tail : list RuntimeAdapter.Atomicity.access_marker}
      {branch_entry : RuntimeAdapter.Atomicity.analysis_state}
      {branch_pre : Runtime.Translation.Assertions.assertion Γ F Δ}
      {branch_exit : RuntimeAdapter.Atomicity.analysis_state}
      {branch_post : Runtime.Translation.Assertions.assertion Γ F Δ}
      (branch_suffix : Normalized.Validity.resource_aligned_operational_suffix
        cost Γ F Δ branch_entry branch_pre tail branch_exit branch_post ((invariant, outer) :: tail))
      {conditional_join : RuntimeAdapter.Atomicity.analysis_state}
      {join_assertion : Runtime.Translation.Assertions.assertion Γ F Δ}
      {exit : RuntimeAdapter.Atomicity.analysis_state}
      {post : Runtime.Translation.Assertions.assertion Γ F Δ}
      {stack_out : list RuntimeAdapter.Atomicity.access_marker}
      (rest_suffix : Normalized.Validity.resource_aligned_operational_suffix
        cost Γ F Δ conditional_join join_assertion ((invariant, outer) :: tail) exit post stack_out)
      (ambient : coPset) : Type := {
    resource_seam_branch : @resource_aligned_normalized_trace cost Γ F Δ
      branch_entry branch_pre tail branch_exit branch_post ((invariant, outer) :: tail);
    resource_seam_branch_suffix : resource_net_suffix resource_seam_branch = branch_suffix;
    resource_seam_mask_eq : Validity.Model.active_runtime_mask ambient branch_exit =
      Validity.Model.active_runtime_mask ambient conditional_join;
    resource_seam_rest :
      has_resource_aligned_focused_closing_normalization rest_suffix;
  }.

  (** Bare, non-dependent combination of two erased runtime programs.  Named
      separately from [Validity.Model.combine_runtime_statements] only to
      mark the specific use site: selecting one arm's own physical
      continuation and sequencing it with whatever the shared continuation
      erases to. *)
  Definition selected_conditional_continuation
      (selected rest : option Runtime.LegacyLang.runtime_stmt) :
      option Runtime.LegacyLang.runtime_stmt :=
    Validity.Model.combine_runtime_statements selected rest.

  (** Projects the [aligned_focused_close_split] out of a seam's own
      [aligned_seam_rest] witness. *)
  Definition aligned_seam_split
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {invariant : typed_core.TypedCore.inv_id}
      {outer : gset typed_core.TypedCore.inv_id}
      {tail : list RuntimeAdapter.Atomicity.access_marker}
      {branch_entry branch_pre branch_exit branch_post}
      {branch_suffix : Validity.aligned_operational_suffix cost Γ F Δ
        branch_entry branch_pre tail branch_exit branch_post
        ((invariant, outer) :: tail)}
      {conditional_join join_assertion exit post stack_out}
      {rest_suffix : Validity.aligned_operational_suffix cost Γ F Δ
        conditional_join join_assertion ((invariant, outer) :: tail) exit post
        stack_out}
      {ambient}
      (seam : aligned_seam_trace branch_suffix rest_suffix ambient) :
      aligned_focused_close_split
        (projT1 (projT2 (projT2
          (aligned_seam_rest _ _ _ seam)))) :=
    projT2 (projT2 (projT2 (aligned_seam_rest _ _ _ seam))).

  (** The semantic, whole-arm seam refinement, CPS-style, split at the first
      matching close.  Unlike a first version, the combined program is not
      [branch ++ rest] as one flat sequence handed to a single, external
      continuation at the branch's own (narrower) exit mask -- Iris fancy
      updates only compose forward (an [Einner -> Eouter] update followed by
      an [Eouter -> Efinal] one gives [Einner -> Efinal]), never the reverse
      factorization an atomic-mask bracket needs (recovering a distinguished
      stop at [Eouter] from a direct [Einner -> Efinal] update).  So the seam
      is split, using [aligned_focused_close_split] at [rest_suffix]'s own
      first matching close, into a *bracket* -- the branch together with
      [aligned_split_prefix], the portion of [rest_suffix] up to and
      including that close -- and an *after* piece, [aligned_split_rest],
      which resumes at mode [None] and the wider, restored mask.  The
      external continuation now consumes the *post-close* resources (at
      [aligned_split_close_assertion]/[tail], the wider mask) rather than the
      branch's own post-unfold resources (at [branch_post]/
      [(invariant, outer) :: tail], the narrower mask) -- so the internal
      proof is free to establish the bracket in the stronger, atomic-bracket
      form [|={Eouter,Einner}=> runtime_wp Einner bracket (fun v =>
      |={Einner,Eouter}=> post)] and apply [runtime_wp_atomic_mask_change],
      with the fold itself supplying the closing update back to [Eouter].
      The outer mask [Eouter] is deliberately [Validity.Model.
      enabled_runtime_mask ambient outer] -- read off the access marker
      itself -- rather than [active_runtime_mask ambient branch_entry]: the
      two coincide (via the unfold's own [lifo_certificate], which pushes
      exactly [(invariant, analysis_open branch_entry)]), but stating the
      refinement in terms of [outer] avoids baking in more equality between
      Raven states than the stack-consistency evidence actually provides.
      [aligned_singleton_ordinary_runtime_refinement] is not the semantic
      premise of the general assembly built on top of this -- it remains
      useful for the item-4 fast path and as a regression target. *)
  Definition aligned_seam_runtime_refinement
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {invariant : typed_core.TypedCore.inv_id}
      {outer : gset typed_core.TypedCore.inv_id}
      {tail : list RuntimeAdapter.Atomicity.access_marker}
      {branch_entry : RuntimeAdapter.Atomicity.analysis_state}
      {branch_pre : Runtime.Translation.Assertions.assertion Γ F Δ}
      {branch_exit : RuntimeAdapter.Atomicity.analysis_state}
      {branch_post : Runtime.Translation.Assertions.assertion Γ F Δ}
      {branch_suffix : Validity.aligned_operational_suffix cost Γ F Δ
        branch_entry branch_pre tail branch_exit branch_post
        ((invariant, outer) :: tail)}
      {conditional_join : RuntimeAdapter.Atomicity.analysis_state}
      {join_assertion : Runtime.Translation.Assertions.assertion Γ F Δ}
      {exit : RuntimeAdapter.Atomicity.analysis_state}
      {post : Runtime.Translation.Assertions.assertion Γ F Δ}
      {stack_out : list RuntimeAdapter.Atomicity.access_marker}
      {rest_suffix : Validity.aligned_operational_suffix cost Γ F Δ
        conditional_join join_assertion ((invariant, outer) :: tail) exit post
        stack_out}
      {ambient : coPset}
      (seam : aligned_seam_trace branch_suffix rest_suffix ambient) : Prop :=
    let split := aligned_seam_split seam in
    let Eouter := Validity.Model.enabled_runtime_mask ambient outer in
    Validity.Model.runtime_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf branch_entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open branch_entry) tail ->
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env),
    Validity.Model.runtime_mask
      (Normalized.suffix_footprint
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          branch_suffix) ∪
       Normalized.suffix_footprint
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          (aligned_split_prefix _ split)) ∪
       Normalized.suffix_footprint
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          (aligned_split_rest _ split))) ⊆ ambient ->
    forall (final_mask : coPset) (carried final : iProp Resources.Σ),
    ((Validity.global_world_context atoms ∗
      Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms (aligned_split_close_assertion _ split) ∗
      Validity.World.access_stack_interp atoms ambient tail ∗ carried) ⊢
      Validity.runtime_option_wp Eouter final_mask
        (ConcreteOrdinaryTrace.source_runtime
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            (aligned_split_rest _ split)) runtime)
        final) ->
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms branch_pre ∗
     Validity.World.access_stack_interp atoms ambient tail ∗ carried) ⊢
    Validity.runtime_option_wp Eouter final_mask
      (Validity.Model.combine_runtime_statements
        (selected_conditional_continuation
          (ConcreteOrdinaryTrace.source_runtime
            (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
              branch_suffix) runtime)
          (ConcreteOrdinaryTrace.source_runtime
            (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
              (aligned_split_prefix _ split)) runtime))
        (ConcreteOrdinaryTrace.source_runtime
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            (aligned_split_rest _ split)) runtime))
      final.

  (** Feasibility checkpoint for the direct normalizer.  Packaging all zipper
      indices lets its recursive definition use exactly the source-size
      measure already validated by the certificate-only normalizer. *)
  Record packed_resource_aligned_suffix cost Γ : Type := {
    packed_resource_F : typed_core.TypedCore.context;
    packed_resource_Delta : typed_core.TypedCore.context;
    packed_resource_entry : RuntimeAdapter.Atomicity.analysis_state;
    packed_resource_pre : Runtime.Translation.Assertions.assertion Γ
      packed_resource_F packed_resource_Delta;
    packed_resource_stack_in : list RuntimeAdapter.Atomicity.access_marker;
    packed_resource_exit : RuntimeAdapter.Atomicity.analysis_state;
    packed_resource_post : Runtime.Translation.Assertions.assertion Γ
      packed_resource_F packed_resource_Delta;
    packed_resource_stack_out : list RuntimeAdapter.Atomicity.access_marker;
    packed_resource_tree : Validity.resource_aligned_operational_suffix cost
      Γ packed_resource_F packed_resource_Delta packed_resource_entry packed_resource_pre
      packed_resource_stack_in packed_resource_exit packed_resource_post
      packed_resource_stack_out;
  }.

  Definition pack_resource_aligned_suffix
      {cost Γ F Δ entry pre stack_in exit post stack_out}
      (suffix : Validity.resource_aligned_operational_suffix cost Γ F Δ entry
        pre stack_in exit post stack_out) :
      packed_resource_aligned_suffix cost Γ :=
    {| packed_resource_F := F;
       packed_resource_Delta := Δ;
       packed_resource_entry := entry;
       packed_resource_pre := pre;
       packed_resource_stack_in := stack_in;
       packed_resource_exit := exit;
       packed_resource_post := post;
       packed_resource_stack_out := stack_out;
       packed_resource_tree := suffix |}.

  Definition packed_resource_aligned_measure {cost Γ}
      (packed : packed_resource_aligned_suffix cost Γ) : nat :=
    RuntimeAdapter.suffix_measure
      (resource_certificate_suffix_of_operational_suffix
        (packed_resource_tree cost Γ packed)).

  Definition packed_resource_aligned_well_founded_induction
      {cost Γ} (P : packed_resource_aligned_suffix cost Γ -> Type) :
      (forall packed,
        (forall smaller, packed_resource_aligned_measure smaller <
          packed_resource_aligned_measure packed -> P smaller) -> P packed) ->
      forall packed, P packed :=
    well_founded_induction_type
      (well_founded_ltof (packed_resource_aligned_suffix cost Γ)
        packed_resource_aligned_measure) P.

  Definition packed_has_resource_aligned_total_normalization
      {cost Γ} (packed : packed_resource_aligned_suffix cost Γ) : Type :=
    has_resource_aligned_total_normalization
      (packed_resource_tree cost Γ packed).

  Record packed_aligned_suffix cost Γ F Δ : Type := {
    packed_aligned_entry : RuntimeAdapter.Atomicity.analysis_state;
    packed_aligned_pre : Runtime.Translation.Assertions.assertion Γ F Δ;
    packed_aligned_stack_in : list RuntimeAdapter.Atomicity.access_marker;
    packed_aligned_exit : RuntimeAdapter.Atomicity.analysis_state;
    packed_aligned_post : Runtime.Translation.Assertions.assertion Γ F Δ;
    packed_aligned_stack_out : list RuntimeAdapter.Atomicity.access_marker;
    packed_aligned_tree : Validity.aligned_operational_suffix cost Γ F Δ
      packed_aligned_entry packed_aligned_pre packed_aligned_stack_in
      packed_aligned_exit packed_aligned_post packed_aligned_stack_out;
  }.

  Definition pack_aligned_suffix
      {cost Γ F Δ entry pre stack_in exit post stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre
        stack_in exit post stack_out) : packed_aligned_suffix cost Γ F Δ :=
    {| packed_aligned_entry := entry;
       packed_aligned_pre := pre;
       packed_aligned_stack_in := stack_in;
       packed_aligned_exit := exit;
       packed_aligned_post := post;
       packed_aligned_stack_out := stack_out;
       packed_aligned_tree := suffix |}.

  Definition packed_aligned_measure {cost Γ F Δ}
      (packed : packed_aligned_suffix cost Γ F Δ) : nat :=
    RuntimeAdapter.suffix_measure
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
        (packed_aligned_tree cost Γ F Δ packed)).

  Definition packed_aligned_well_founded_induction
      {cost Γ F Δ} (P : packed_aligned_suffix cost Γ F Δ -> Type) :
      (forall packed,
        (forall smaller, packed_aligned_measure smaller <
          packed_aligned_measure packed -> P smaller) -> P packed) ->
      forall packed, P packed :=
    well_founded_induction_type
      (well_founded_ltof (packed_aligned_suffix cost Γ F Δ)
        packed_aligned_measure) P.

  Record has_aligned_total_normalization
      {cost Γ F Δ entry pre stack_in exit post stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre
        stack_in exit post stack_out) : Type := {
    aligned_total_ordinary : has_aligned_ordinary_normalization suffix;
    aligned_total_focused :
      match stack_in as stack return
          Validity.aligned_operational_suffix cost Γ F Δ entry pre stack
            exit post stack_out -> Type
      with
      | [] => fun _ => unit
      | focused :: tail => fun focused_suffix =>
          has_aligned_focused_normalization focused_suffix
      end suffix;
  }.

  Definition packed_has_aligned_total_normalization
      {cost Γ F Δ} (packed : packed_aligned_suffix cost Γ F Δ) : Type :=
    has_aligned_total_normalization
      (packed_aligned_tree cost Γ F Δ packed).

  Definition normalize_aligned_done
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {state : RuntimeAdapter.Atomicity.analysis_state}
      {assertion : Runtime.Translation.Assertions.assertion Γ F Δ}
      {stack : list RuntimeAdapter.Atomicity.access_marker} :
    has_aligned_ordinary_normalization
      (Validity.AlignedOperationalDone (cost := cost) state assertion stack).
  Proof.
    exists (@RuntimeAdapter.NetOrdinary stack stack state state
      (RuntimeAdapter.Slice.ExecDone state stack)).
    exists (@RuntimeAdapter.TraceDoneNet cost Γ state stack).
    apply AlignedTraceDone.
  Defined.

  Definition normalize_aligned_focused_done
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {state : RuntimeAdapter.Atomicity.analysis_state}
      {assertion : Runtime.Translation.Assertions.assertion Γ F Δ}
      {focused : RuntimeAdapter.Atomicity.access_marker}
      {tail : list RuntimeAdapter.Atomicity.access_marker} :
    has_aligned_focused_normalization
      (Validity.AlignedOperationalDone (cost := cost) state assertion
        (focused :: tail)).
  Proof.
    exists (@RuntimeAdapter.FocusNetOutcome focused tail state state
      (RuntimeAdapter.Slice.OutcomeStillOpen focused tail state state
        (RuntimeAdapter.Slice.FocusedPrefixDone focused tail state))).
    exists (@RuntimeAdapter.TraceDoneFocused cost Γ state focused tail).
    apply AlignedTraceDoneFocused.
  Defined.

  Definition normalize_aligned_ordinary_chunk
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        stack stack_out certificate derivation aligned lifo rest chunk}
      (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        middle stack stack certificate chunk)
      (normal_rest : has_aligned_ordinary_normalization rest) :
    has_aligned_ordinary_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ fuel entry statement
        middle pre middle_assertion stack stack certificate derivation aligned
        lifo exit post stack_out rest).
  Proof.
    destruct normal_rest as [rest_tree [Hrest aligned_rest]].
    eexists (@RuntimeAdapter.NetChunk stack middle stack_out entry exit chunk
      rest_tree).
    eexists (@RuntimeAdapter.TraceChunk cost Γ fuel entry statement middle
      exit stack stack_out certificate
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
      chunk Hchunk rest_tree Hrest).
    eapply AlignedTraceChunk. exact aligned_rest.
  Defined.

  Definition normalize_aligned_focused_prefix
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        focused tail stack_out certificate derivation aligned lifo rest chunk}
      (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        middle (focused :: tail) (focused :: tail) certificate chunk)
      (head_ok : RuntimeAdapter.Payload.preserves focused tail entry middle chunk)
      (normal_rest : has_aligned_focused_normalization rest) :
    has_aligned_focused_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ fuel entry statement
        middle pre middle_assertion (focused :: tail) (focused :: tail)
        certificate derivation aligned lifo exit post stack_out rest).
  Proof.
    destruct normal_rest as [rest_tree [Hrest aligned_rest]].
    eexists (@RuntimeAdapter.FocusNetPrefix focused tail stack_out entry middle
      exit chunk head_ok rest_tree).
    eexists (@RuntimeAdapter.TraceFocusedPrefix cost Γ fuel entry statement
      middle exit focused tail stack_out certificate
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
      chunk Hchunk head_ok rest_tree Hrest).
    eapply AlignedTraceFocusedPrefix. exact aligned_rest.
  Defined.

  Definition normalize_aligned_access
      {cost Γ F Δ fuel entry statement opened exit pre opened_assertion post
        focused tail stack_out certificate derivation aligned lifo rest opening}
      (Hopening : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        opened tail (focused :: tail) certificate opening)
      (open_ok : RuntimeAdapter.Payload.opens focused tail entry opened opening)
      (normal_body : has_aligned_focused_normalization rest) :
    has_aligned_ordinary_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ fuel entry statement
        opened pre opened_assertion tail (focused :: tail) certificate derivation
        aligned lifo exit post stack_out rest).
  Proof.
    destruct normal_body as [body [Hbody aligned_body]].
    eexists (@RuntimeAdapter.NetAccess tail stack_out focused entry opened exit
      opening open_ok body).
    eexists (@RuntimeAdapter.TraceAccess cost Γ fuel entry statement opened
      exit focused tail stack_out certificate
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
      opening Hopening open_ok body Hbody).
    eapply AlignedTraceAccess. exact aligned_body.
  Defined.

  Definition normalize_aligned_nested_access
      {cost Γ F Δ fuel entry statement opened exit pre opened_assertion post
        focused tail nested stack_out certificate derivation aligned lifo rest
        opening}
      (Hopening : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        opened (focused :: tail) (nested :: focused :: tail) certificate opening)
      (open_ok : RuntimeAdapter.Payload.opens nested (focused :: tail) entry
        opened opening)
      (normal_body : has_aligned_focused_normalization rest) :
    has_aligned_focused_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ fuel entry statement
        opened pre opened_assertion (focused :: tail)
        (nested :: focused :: tail) certificate derivation aligned lifo exit post
        stack_out rest).
  Proof.
    destruct normal_body as [body [Hbody aligned_body]].
    eexists (@RuntimeAdapter.FocusNetNested focused tail stack_out nested entry
      opened exit opening open_ok body).
    eexists (@RuntimeAdapter.TraceNestedAccess cost Γ fuel entry statement
      opened exit focused tail nested stack_out certificate
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
      opening Hopening open_ok body Hbody).
    eapply AlignedTraceNestedAccess. exact aligned_body.
  Defined.

  Definition normalize_aligned_close
      {cost Γ F Δ fuel entry statement closed exit pre closed_assertion post
        focused tail stack_out certificate derivation aligned lifo rest closing}
      (Hclosing : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        closed (focused :: tail) tail certificate closing)
      (close_ok : RuntimeAdapter.Payload.closes focused tail entry closed closing)
      (normal_rest : has_aligned_ordinary_normalization rest) :
    has_aligned_focused_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ fuel entry statement
        closed pre closed_assertion (focused :: tail) tail certificate derivation
        aligned lifo exit post stack_out rest).
  Proof.
    destruct normal_rest as [rest_tree [Hrest aligned_rest]].
    eexists (@RuntimeAdapter.FocusNetClose focused tail stack_out entry closed exit
      (RuntimeAdapter.Slice.FocusedClose focused tail entry closed closing
        close_ok) rest_tree).
    eexists (@RuntimeAdapter.TraceFocusedClose cost Γ fuel entry statement
      closed exit focused tail stack_out certificate
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
      closing Hclosing close_ok rest_tree Hrest).
    eapply AlignedTraceFocusedClose. exact aligned_rest.
  Defined.

  Definition normalize_aligned_ordinary_close
      {cost Γ F Δ fuel entry statement closed exit pre closed_assertion post
        focused tail stack_out certificate derivation aligned lifo rest closing}
      (Hclosing : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        closed (focused :: tail) tail certificate closing)
      (close_ok : RuntimeAdapter.Payload.closes focused tail entry closed closing)
      (normal_rest : has_aligned_ordinary_normalization rest) :
    has_aligned_ordinary_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ fuel entry statement
        closed pre closed_assertion (focused :: tail) tail certificate derivation
        aligned lifo exit post stack_out rest).
  Proof.
    destruct normal_rest as [rest_tree [Hrest aligned_rest]].
    eexists (@RuntimeAdapter.NetClose focused tail stack_out entry closed exit
      closing close_ok rest_tree).
    eexists (@RuntimeAdapter.TraceClose cost Γ fuel entry statement closed exit
      focused tail stack_out certificate
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
      closing Hclosing close_ok rest_tree Hrest).
    eapply AlignedTraceClose. exact aligned_rest.
  Defined.

  Definition normalize_aligned_conditional
      {cost Γ F Δ fuel entry statement then_statement else_statement
        then_exit else_exit exit pre join_assertion post stack_in join_stack
        stack_out view then_certificate else_certificate open_equal atomic_equal
        derivation aligned lifo rest then_tree else_tree}
      (Hthen : RuntimeAdapter.net_trace cost Γ entry then_exit None stack_in
        join_stack
        (RuntimeAdapter.SuffixCons then_certificate
          (RuntimeAdapter.SuffixDone then_exit)) then_tree)
      (Helse : RuntimeAdapter.net_trace cost Γ entry else_exit None stack_in
        join_stack
        (RuntimeAdapter.SuffixCons else_certificate
          (RuntimeAdapter.SuffixDone else_exit)) else_tree)
      (normal_rest : has_aligned_ordinary_normalization rest) :
    has_aligned_ordinary_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ (S fuel) entry statement
        (RuntimeAdapter.conditional_join then_exit else_exit) pre join_assertion
        stack_in join_stack
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
          then_statement else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal)
        derivation aligned lifo exit post stack_out rest).
  Proof.
    destruct normal_rest as [rest_tree [Hrest aligned_rest]].
    eexists (@RuntimeAdapter.NetConditional stack_in join_stack stack_out entry
      then_exit else_exit (RuntimeAdapter.conditional_join then_exit else_exit)
      exit
      (RuntimeAdapter.Payload.RavenConditional Γ fuel cost entry statement
        then_statement else_statement then_exit else_exit view then_certificate
        else_certificate open_equal atomic_equal) then_tree else_tree rest_tree).
    eexists (@RuntimeAdapter.TraceConditional cost Γ fuel entry statement
      then_statement else_statement then_exit else_exit exit stack_in join_stack
      stack_out view then_certificate else_certificate open_equal atomic_equal
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
      then_tree else_tree rest_tree Hthen Helse Hrest).
    eapply AlignedTraceConditional. exact aligned_rest.
  Defined.

  Definition normalize_aligned_focused_conditional
      {cost Γ F Δ fuel entry statement then_statement else_statement
        then_exit else_exit exit pre join_assertion post focused tail join_stack
        stack_out view then_certificate else_certificate open_equal atomic_equal
        derivation aligned lifo rest then_tree else_tree}
      (Hthen : RuntimeAdapter.net_trace cost Γ entry then_exit (Some focused)
        tail join_stack
        (RuntimeAdapter.SuffixCons then_certificate
          (RuntimeAdapter.SuffixDone then_exit)) then_tree)
      (Helse : RuntimeAdapter.net_trace cost Γ entry else_exit (Some focused)
        tail join_stack
        (RuntimeAdapter.SuffixCons else_certificate
          (RuntimeAdapter.SuffixDone else_exit)) else_tree)
      (normal_rest : has_aligned_ordinary_normalization rest) :
    has_aligned_focused_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ (S fuel) entry statement
        (RuntimeAdapter.conditional_join then_exit else_exit) pre join_assertion
        (focused :: tail) join_stack
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
          then_statement else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal)
        derivation aligned lifo exit post stack_out rest).
  Proof.
    destruct normal_rest as [rest_tree [Hrest aligned_rest]].
    eexists (@RuntimeAdapter.FocusNetConditional focused tail join_stack stack_out
      entry then_exit else_exit (RuntimeAdapter.conditional_join then_exit else_exit)
      exit
      (RuntimeAdapter.Payload.RavenConditional Γ fuel cost entry statement
        then_statement else_statement then_exit else_exit view then_certificate
        else_certificate open_equal atomic_equal) then_tree else_tree rest_tree).
    eexists (@RuntimeAdapter.TraceFocusedConditional cost Γ fuel entry
      statement then_statement else_statement then_exit else_exit exit focused
      tail join_stack stack_out view then_certificate else_certificate open_equal
      atomic_equal
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix rest)
      then_tree else_tree rest_tree Hthen Helse Hrest).
    eapply AlignedTraceFocusedConditional. exact aligned_rest.
  Defined.

  Definition normalize_aligned_sequence_expansion
      {cost Γ F Δ fuel entry statement first middle second next exit pre}
      {middle_assertion next_assertion post :
        Runtime.Translation.Assertions.assertion Γ F Δ}
      {stack_in stack_middle stack_next stack_out :
        list RuntimeAdapter.Atomicity.access_marker}
      {view first_certificate second_certificate}
      {first_derivation : Validity.Certified.Rules.RavenHoareTriple pre first
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask middle) middle_assertion}
      {second_derivation : Validity.Certified.Rules.RavenHoareTriple
        middle_assertion second (RuntimeAdapter.Atomicity.analysis_mask middle)
        (RuntimeAdapter.Atomicity.analysis_mask next) next_assertion}
      {first_aligned : Validity.Certified.certificate_hoare_aligned cost
        first_certificate first_derivation}
      {second_aligned : Validity.Certified.certificate_hoare_aligned cost
        second_certificate second_derivation}
      {head_derivation : Validity.Certified.Rules.RavenHoareTriple pre
        statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask next) next_assertion}
      {head_aligned : Validity.Certified.certificate_hoare_aligned cost
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate) head_derivation}
      {head_lifo}
      {first_lifo : RuntimeAdapter.Atomicity.lifo_certificate first_certificate
        stack_in stack_middle}
      {second_lifo : RuntimeAdapter.Atomicity.lifo_certificate second_certificate
        stack_middle stack_next}
      {rest}
      (normal_flat : has_aligned_ordinary_normalization
        (Validity.expand_aligned_sequence_suffix view first_certificate
          second_certificate first_derivation second_derivation first_aligned
          second_aligned first_lifo second_lifo rest)) :
    has_aligned_ordinary_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ (S fuel) entry
        statement next pre next_assertion stack_in
        stack_next
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate)
        head_derivation head_aligned head_lifo exit post stack_out rest).
  Proof.
    destruct normal_flat as [tree [Hflat aligned_flat]].
    eexists tree.
    eexists (@RuntimeAdapter.TraceExpansion cost Γ entry exit None stack_in
      stack_out
      (RuntimeAdapter.SuffixCons first_certificate
        (RuntimeAdapter.SuffixCons second_certificate
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest)))
      (RuntimeAdapter.SuffixCons
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate)
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest)) tree
      (@RuntimeAdapter.ExpandsSequence cost Γ fuel entry
        statement first middle second next exit view
        first_certificate second_certificate
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest)) Hflat).
    eapply AlignedTraceSequenceExpansion. exact aligned_flat.
  Defined.

  Definition normalize_aligned_focused_sequence_expansion
      {cost Γ F Δ fuel entry statement first middle second next exit pre}
      {middle_assertion next_assertion post :
        Runtime.Translation.Assertions.assertion Γ F Δ}
      {focused : RuntimeAdapter.Atomicity.access_marker}
      {tail stack_middle stack_next stack_out :
        list RuntimeAdapter.Atomicity.access_marker}
      {view first_certificate second_certificate}
      {first_derivation : Validity.Certified.Rules.RavenHoareTriple pre first
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask middle) middle_assertion}
      {second_derivation : Validity.Certified.Rules.RavenHoareTriple
        middle_assertion second (RuntimeAdapter.Atomicity.analysis_mask middle)
        (RuntimeAdapter.Atomicity.analysis_mask next) next_assertion}
      {first_aligned : Validity.Certified.certificate_hoare_aligned cost
        first_certificate first_derivation}
      {second_aligned : Validity.Certified.certificate_hoare_aligned cost
        second_certificate second_derivation}
      {head_derivation : Validity.Certified.Rules.RavenHoareTriple pre
        statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask next) next_assertion}
      {head_aligned : Validity.Certified.certificate_hoare_aligned cost
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate) head_derivation}
      {head_lifo}
      {first_lifo : RuntimeAdapter.Atomicity.lifo_certificate first_certificate
        (focused :: tail) stack_middle}
      {second_lifo : RuntimeAdapter.Atomicity.lifo_certificate second_certificate
        stack_middle stack_next}
      {rest}
      (normal_flat : has_aligned_focused_normalization
        (Validity.expand_aligned_sequence_suffix view first_certificate
          second_certificate first_derivation second_derivation first_aligned
          second_aligned first_lifo second_lifo rest)) :
    has_aligned_focused_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ (S fuel) entry
        statement next pre next_assertion
        (focused :: tail) stack_next
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate)
        head_derivation head_aligned head_lifo exit post stack_out rest).
  Proof.
    destruct normal_flat as [tree [Hflat aligned_flat]].
    eexists tree.
    eexists (@RuntimeAdapter.TraceExpansion cost Γ entry exit (Some focused)
      tail stack_out
      (RuntimeAdapter.SuffixCons first_certificate
        (RuntimeAdapter.SuffixCons second_certificate
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest)))
      (RuntimeAdapter.SuffixCons
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate)
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest)) tree
      (@RuntimeAdapter.ExpandsSequence cost Γ fuel entry
        statement first middle second next exit view
        first_certificate second_certificate
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest)) Hflat).
    eapply AlignedTraceSequenceExpansion. exact aligned_flat.
  Defined.

  Definition aligned_total_leaf_head
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        stack_in stack_middle stack_out view step derivation aligned lifo rest}
      (total_rest : has_aligned_total_normalization rest) :
    has_aligned_total_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ (S fuel) entry statement
        middle pre middle_assertion stack_in stack_middle
        (RuntimeAdapter.Atomicity.CertLeaf cost Γ fuel entry statement middle
          view step) derivation aligned lifo exit post stack_out rest).
  Proof.
    simpl in lifo. subst stack_middle.
    destruct total_rest as [Hordinary Hfocused].
    constructor.
    - eapply normalize_aligned_ordinary_chunk.
      + apply RuntimeAdapter.ChunkCertificateLeaf.
      + exact Hordinary.
    - destruct stack_in as [|focused tail]; simpl in Hfocused |- *.
      + exact tt.
      + eapply normalize_aligned_focused_prefix.
        * apply RuntimeAdapter.ChunkCertificateLeaf.
        * exact I.
        * exact Hfocused.
  Defined.

  Definition aligned_total_atomic_head
      {cost Γ F Δ fuel entry statement body outer inner exit pre
        middle_assertion post stack_in stack_middle stack_out view step
        body_certificate open_equal derivation aligned lifo rest}
      (total_rest : has_aligned_total_normalization rest) :
    has_aligned_total_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ (S fuel) entry statement
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask inner)
          (RuntimeAdapter.Atomicity.analysis_open inner)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer ||
            RuntimeAdapter.Atomicity.analysis_step_taken inner)
          (RuntimeAdapter.Atomicity.analysis_in_atomic outer))
        pre middle_assertion stack_in stack_middle
        (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel entry statement body
          outer inner view step body_certificate open_equal)
        derivation aligned lifo exit post stack_out rest).
  Proof.
    simpl in lifo. pose proof (proj2 lifo) as Heq. subst stack_middle.
    destruct total_rest as [Hordinary Hfocused].
    constructor.
    - eapply normalize_aligned_ordinary_chunk.
      + apply RuntimeAdapter.ChunkCertificateAtomic.
      + exact Hordinary.
    - destruct stack_in as [|focused tail]; simpl in Hfocused |- *.
      + exact tt.
      + eapply normalize_aligned_focused_prefix.
        * apply RuntimeAdapter.ChunkCertificateAtomic.
        * exact I.
        * exact Hfocused.
  Defined.

  Definition aligned_total_unfold_head
      {cost Γ F Δ fuel entry statement invariant opened exit pre
        opened_assertion post stack_in stack_opened stack_out view step
        derivation aligned lifo rest}
      (total_rest : has_aligned_total_normalization rest) :
    has_aligned_total_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ (S fuel) entry statement
        opened pre opened_assertion stack_in stack_opened
        (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry statement
          invariant opened view step) derivation aligned lifo exit post
        stack_out rest).
  Proof.
    simpl in lifo. subst stack_opened.
    destruct total_rest as [Hordinary Hfocused]. simpl in Hfocused.
    constructor.
    - eapply normalize_aligned_access.
      + eapply RuntimeAdapter.ChunkCertificateUnfold.
      + exact I.
      + exact Hfocused.
    - destruct stack_in as [|focused tail]; simpl.
      + exact tt.
      + eapply normalize_aligned_nested_access.
        * eapply RuntimeAdapter.ChunkCertificateUnfold.
        * exact I.
        * exact Hfocused.
  Defined.

  Lemma fold_lifo_fresh_stack
      {cost Γ fuel entry statement invariant view stack_in stack_out}
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate
        (RuntimeAdapter.Atomicity.CertFold cost Γ fuel entry statement
          invariant view) stack_in stack_out)
      (Hfresh : invariant ∉ RuntimeAdapter.Atomicity.analysis_open entry) :
    stack_out = stack_in.
  Proof.
    simpl in lifo. destruct lifo as [Hmatched | [Heq _]]; last exact Heq.
    destruct Hmatched as [outer [_ [Hopen _]]]. contradiction.
  Qed.

  Lemma fold_lifo_matched_nonempty
      {cost Γ fuel entry statement invariant view stack_out}
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate
        (RuntimeAdapter.Atomicity.CertFold cost Γ fuel entry statement
          invariant view) [] stack_out)
      (Hopen : invariant ∈ RuntimeAdapter.Atomicity.analysis_open entry) :
    False.
  Proof.
    simpl in lifo. destruct lifo as [[outer [Heq _]] | [_ Hfresh]].
    - discriminate Heq.
    - contradiction.
  Qed.

  Lemma fold_lifo_matched_facts
      {cost Γ fuel entry statement invariant view head outer tail stack_out}
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate
        (RuntimeAdapter.Atomicity.CertFold cost Γ fuel entry statement
          invariant view) ((head, outer) :: tail) stack_out)
      (Hopen : invariant ∈ RuntimeAdapter.Atomicity.analysis_open entry) :
    head = invariant /\ tail = stack_out /\
    invariant ∈ RuntimeAdapter.Atomicity.analysis_open entry /\
    invariant ∉ outer /\
    RuntimeAdapter.Atomicity.analysis_open entry = {[invariant]} ∪ outer.
  Proof.
    simpl in lifo. destruct lifo as [Hmatched | [_ Hfresh]]; last contradiction.
    destruct Hmatched as [outer' [Heq [Hmember [Houter Hopen_eq]]]].
    inversion Heq; subst. repeat split; assumption.
  Qed.

  Definition aligned_total_fold_head
      {cost Γ F Δ fuel entry statement invariant exit pre middle_assertion post
        stack_in stack_middle stack_out view derivation aligned lifo rest}
      (total_rest : has_aligned_total_normalization rest) :
    has_aligned_total_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ (S fuel) entry statement
        (RuntimeAdapter.Atomicity.fold_invariant invariant entry) pre
        middle_assertion stack_in stack_middle
        (RuntimeAdapter.Atomicity.CertFold cost Γ fuel entry statement invariant
          view) derivation aligned lifo exit post stack_out rest).
  Proof.
    destruct (decide (invariant ∈
      RuntimeAdapter.Atomicity.analysis_open entry)) as [Hopen | Hfresh].
    - destruct stack_in as [|[head outer] tail].
      + exact (False_rect _ (fold_lifo_matched_nonempty lifo Hopen)).
      + pose proof (fold_lifo_matched_facts lifo Hopen) as Hfacts.
        pose proof (proj1 Hfacts) as Hhead.
        pose proof (proj1 (proj2 Hfacts)) as Htail.
        subst head. subst stack_middle.
        destruct total_rest as [Hordinary Hfocused].
        constructor.
        * eapply normalize_aligned_ordinary_close.
          -- eapply RuntimeAdapter.ChunkCertificateFold.
          -- exact I.
          -- exact Hordinary.
        * simpl. eapply normalize_aligned_close.
          -- eapply RuntimeAdapter.ChunkCertificateFold.
          -- exact I.
          -- exact Hordinary.
    - pose proof (fold_lifo_fresh_stack lifo Hfresh) as Heq.
      subst stack_middle.
      destruct total_rest as [Hordinary Hfocused].
      constructor.
      + eapply normalize_aligned_ordinary_chunk.
        * eapply RuntimeAdapter.ChunkCertificateFreshFold.
        * exact Hordinary.
      + destruct stack_in as [|focused tail]; simpl in Hfocused |- *.
        * exact tt.
        * eapply normalize_aligned_focused_prefix.
          -- eapply RuntimeAdapter.ChunkCertificateFreshFold.
          -- exact I.
          -- exact Hfocused.
    Unshelve. all: intuition.
  Defined.

  Definition choose_sequence_lifo_middle
      {cost Γ fuel entry statement first middle second next view
        first_certificate second_certificate stack_in stack_out}
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry statement
          first middle second next view first_certificate second_certificate)
        stack_in stack_out) :
    { stack_middle : list RuntimeAdapter.Atomicity.access_marker |
      RuntimeAdapter.Atomicity.lifo_certificate first_certificate stack_in
        stack_middle /\
      RuntimeAdapter.Atomicity.lifo_certificate second_certificate stack_middle
        stack_out }.
  Proof.
    apply constructive_indefinite_description. exact lifo.
  Defined.

  Definition choose_prop_witness {A : Type} (H : exists _ : A, True) : A :=
    proj1_sig (constructive_indefinite_description (fun _ : A => True) H).

  Record aligned_atomic_decomposition
      {cost} {Γ F Δ : typed_core.TypedCore.context} {fuel}
      {state outer inner : RuntimeAdapter.Atomicity.analysis_state}
      {statement body : Runtime.IR.stmt Γ}
      {pre post : Runtime.Translation.Assertions.assertion Γ F Δ}
      (body_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        body inner) : Type := {
    atomic_source_node : typed_core.TypedCore.node_id;
    atomic_source_statement : statement =
      Runtime.IR.TAtomic atomic_source_node body;
    atomic_source_trusted : Contracts.trusted_atomic Γ body;
    atomic_body_derivation : Validity.Certified.Rules.RavenHoareTriple pre body
      (RuntimeAdapter.Atomicity.analysis_mask outer)
      (RuntimeAdapter.Atomicity.analysis_mask inner) post;
    atomic_body_aligned : Validity.Certified.certificate_hoare_aligned cost
      body_certificate atomic_body_derivation;
  }.

  Definition aligned_atomic_decomposition_target
      {cost Γ fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit) :
      forall (F Δ : typed_core.TypedCore.context)
        (pre post : Runtime.Translation.Assertions.assertion Γ F Δ),
        Validity.Certified.Rules.RavenHoareTriple pre statement
          (RuntimeAdapter.Atomicity.analysis_mask entry)
          (RuntimeAdapter.Atomicity.analysis_mask exit) post -> Type :=
    match certificate as certificate' in
        RuntimeAdapter.Atomicity.analysis_certificate _ Γ' fuel' entry'
          statement' exit'
      return forall F' Δ' pre' post',
        Validity.Certified.Rules.RavenHoareTriple pre' statement'
          (RuntimeAdapter.Atomicity.analysis_mask entry')
          (RuntimeAdapter.Atomicity.analysis_mask exit') post' -> Type
    with
    | @RuntimeAdapter.Atomicity.CertAtomic _ Γ' fuel' state' statement' body
        outer inner view step body_certificate open_equal =>
        fun F' Δ' pre' post' _ =>
          @aligned_atomic_decomposition cost Γ' F' Δ' fuel' state' outer inner
            statement' body pre' post' body_certificate
    | _ => fun _ _ _ _ _ => unit
    end.

  Fixpoint aligned_atomic_decompose_fix
      {cost Γ F Δ fuel entry statement exit pre post}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post}
      (Haligned : Validity.Certified.certificate_hoare_aligned cost certificate
        derivation) {struct Haligned} :
    aligned_atomic_decomposition_target certificate F Δ pre post derivation.
  Proof.
    destruct Haligned; simpl; try exact tt.
    - refine {| atomic_source_node := node;
        atomic_source_statement := eq_refl;
        atomic_source_trusted := trusted;
        atomic_body_derivation :=
          (Validity.Certified.hoare_mask_transport body_derivation
          (eq_sym (Validity.Certified.step_analysis_mask
            state outer step)) eq_refl);
        atomic_body_aligned := Haligned |}.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@aligned_atomic_decompose_fix cost Γ F Δ (S fuel) state
        statement _ pre post
        (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel state statement body
          outer inner e e0 certificate e1) derivation Haligned) as
        [atomic_node Hstatement Htrusted Hbody Haligned_body].
      refine {| atomic_source_node := atomic_node;
        atomic_source_statement := Hstatement;
        atomic_source_trusted := Htrusted;
        atomic_body_derivation :=
          Validity.Certified.Rules.FrameRule _ _ frame _ _ _ Hbody;
        atomic_body_aligned := _ |}.
      eapply (@Validity.Certified.AlignedFrame cost Γ F Δ fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        inner body pre post frame certificate Hbody).
      exact Haligned_body.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@aligned_atomic_decompose_fix cost Γ F Δ (S fuel) state
        statement _ pre post
        (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel state statement body
          outer inner e e0 certificate e1) derivation Haligned) as
        [atomic_node Hstatement Htrusted Hbody Haligned_body].
      pose (Hbody' := Validity.Certified.Rules.ConsequenceRule
        pre pre' post post' body
        (RuntimeAdapter.Atomicity.analysis_mask outer)
        (RuntimeAdapter.Atomicity.analysis_mask inner) Hbody pre_entails
        post_entails).
      refine {| atomic_source_node := atomic_node;
        atomic_source_statement := Hstatement;
        atomic_source_trusted := Htrusted;
        atomic_body_derivation := Hbody';
        atomic_body_aligned := _ |}.
      eapply (@Validity.Certified.AlignedConsequence cost Γ F Δ fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        inner body pre pre' post post' certificate Hbody pre_entails
        post_entails).
      exact Haligned_body.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@aligned_atomic_decompose_fix cost Γ F (t :: Δ) (S fuel)
        state statement _ body
        (Runtime.Translation.Assertions.weaken_assertion post)
        (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel state statement body0
          outer inner e e0 certificate e1) derivation Haligned) as
        [atomic_node Hstatement Htrusted Hbody Haligned_body].
      pose (Hbody' := Validity.Certified.Rules.ExistsElimRule t body post body0
        (RuntimeAdapter.Atomicity.analysis_mask outer)
        (RuntimeAdapter.Atomicity.analysis_mask inner) Hbody).
      refine {| atomic_source_node := atomic_node;
        atomic_source_statement := Hstatement;
        atomic_source_trusted := Htrusted;
        atomic_body_derivation := Hbody';
        atomic_body_aligned := _ |}.
      eapply (@Validity.Certified.AlignedExistsElim cost Γ F Δ t fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        inner body0 body post certificate Hbody).
      exact Haligned_body.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@aligned_atomic_decompose_fix cost Γ F (t :: Δ) (S fuel)
        state statement _ body post
        (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel state statement body0
          outer inner e e0 certificate e1) derivation Haligned) as
        [atomic_node Hstatement Htrusted Hbody Haligned_body].
      pose (Hbody' := Validity.Certified.Rules.ExistsPreserveRule t body post
        body0 (RuntimeAdapter.Atomicity.analysis_mask outer)
        (RuntimeAdapter.Atomicity.analysis_mask inner) Hbody).
      refine {| atomic_source_node := atomic_node;
        atomic_source_statement := Hstatement;
        atomic_source_trusted := Htrusted;
        atomic_body_derivation := Hbody';
        atomic_body_aligned := _ |}.
      eapply (@Validity.Certified.AlignedExistsPreserve cost Γ F Δ t fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        inner body0 body post certificate Hbody).
      exact Haligned_body.
  Defined.

  Record resource_aligned_atomic_decomposition
      {cost} {Γ F Δ : typed_core.TypedCore.context} {fuel}
      {state outer inner : RuntimeAdapter.Atomicity.analysis_state}
      {statement body : Runtime.IR.stmt Γ}
      {pre post : Runtime.Translation.Assertions.assertion Γ F Δ}
      (body_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        body inner) : Type := {
    resource_atomic_source_node : typed_core.TypedCore.node_id;
    resource_atomic_source_statement : statement =
      Runtime.IR.TAtomic resource_atomic_source_node body;
    resource_atomic_source_trusted : Contracts.trusted_atomic Γ body;
    resource_atomic_body_derivation :
      Validity.Certified.Rules.RavenResourceTriple pre body post;
    resource_atomic_body_aligned :
      Validity.Certified.resource_certificate_hoare_aligned cost
        body_certificate resource_atomic_body_derivation;
  }.

  Definition resource_aligned_atomic_decomposition_target
      {cost Γ fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit) :
      forall (F Δ : typed_core.TypedCore.context)
        (pre post : Runtime.Translation.Assertions.assertion Γ F Δ),
        Validity.Certified.Rules.RavenResourceTriple pre statement post -> Type :=
    match certificate as certificate' in
        RuntimeAdapter.Atomicity.analysis_certificate _ Γ' fuel' entry'
          statement' exit'
      return forall F' Δ' pre' post',
        Validity.Certified.Rules.RavenResourceTriple pre' statement' post' -> Type
    with
    | @RuntimeAdapter.Atomicity.CertAtomic _ Γ' fuel' state' statement' body
        outer inner view step body_certificate open_equal =>
        fun F' Δ' pre' post' _ =>
          @resource_aligned_atomic_decomposition cost Γ' F' Δ' fuel' state'
            outer inner statement' body pre' post' body_certificate
    | _ => fun _ _ _ _ _ => unit
    end.

  Fixpoint resource_aligned_atomic_decompose_fix
      {cost Γ F Δ fuel entry statement exit pre post}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post}
      (Haligned : Validity.Certified.resource_certificate_hoare_aligned
        cost certificate derivation) {struct Haligned} :
    resource_aligned_atomic_decomposition_target certificate F Δ pre post
      derivation.
  Proof.
    destruct Haligned; simpl; try exact tt.
    - refine {| resource_atomic_source_node := node;
        resource_atomic_source_statement := eq_refl;
        resource_atomic_source_trusted := trusted;
        resource_atomic_body_derivation := body_derivation;
        resource_atomic_body_aligned := Haligned |}.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@resource_aligned_atomic_decompose_fix cost Γ F Δ (S fuel)
        state statement _ pre post
        (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel state statement body
          outer inner e e0 certificate e1) derivation Haligned) as
        [atomic_node Hstatement Htrusted Hbody Haligned_body].
      refine {| resource_atomic_source_node := atomic_node;
        resource_atomic_source_statement := Hstatement;
        resource_atomic_source_trusted := Htrusted;
        resource_atomic_body_derivation :=
          Validity.Certified.Rules.ResourceFrameRule _ _ frame _ Hbody;
        resource_atomic_body_aligned := _ |}.
      eapply (@Validity.Certified.ResourceAlignedFrame cost Γ F Δ fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        inner body pre post frame certificate Hbody).
      exact Haligned_body.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@resource_aligned_atomic_decompose_fix cost Γ F Δ (S fuel)
        state statement _ pre post
        (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel state statement body
          outer inner e e0 certificate e1) derivation Haligned) as
        [atomic_node Hstatement Htrusted Hbody Haligned_body].
      pose (Hbody' := Validity.Certified.Rules.ResourceConsequenceRule
        pre pre' post post' body Hbody pre_entails post_entails).
      refine {| resource_atomic_source_node := atomic_node;
        resource_atomic_source_statement := Hstatement;
        resource_atomic_source_trusted := Htrusted;
        resource_atomic_body_derivation := Hbody';
        resource_atomic_body_aligned := _ |}.
      eapply (@Validity.Certified.ResourceAlignedConsequence cost Γ F Δ fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        inner body pre pre' post post' certificate Hbody pre_entails
        post_entails).
      exact Haligned_body.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@resource_aligned_atomic_decompose_fix cost Γ F (t :: Δ)
        (S fuel) state statement _ body
        (Runtime.Translation.Assertions.weaken_assertion post)
        (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel state statement body0
          outer inner e e0 certificate e1) derivation Haligned) as
        [atomic_node Hstatement Htrusted Hbody Haligned_body].
      pose (Hbody' := Validity.Certified.Rules.ResourceExistsElimRule t body
        post body0 Hbody).
      refine {| resource_atomic_source_node := atomic_node;
        resource_atomic_source_statement := Hstatement;
        resource_atomic_source_trusted := Htrusted;
        resource_atomic_body_derivation := Hbody';
        resource_atomic_body_aligned := _ |}.
      eapply (@Validity.Certified.ResourceAlignedExistsElim cost Γ F Δ t fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        inner body0 body post certificate Hbody).
      exact Haligned_body.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@resource_aligned_atomic_decompose_fix cost Γ F (t :: Δ)
        (S fuel) state statement _ body post
        (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel state statement body0
          outer inner e e0 certificate e1) derivation Haligned) as
        [atomic_node Hstatement Htrusted Hbody Haligned_body].
      pose (Hbody' := Validity.Certified.Rules.ResourceExistsPreserveRule t
        body post body0 Hbody).
      refine {| resource_atomic_source_node := atomic_node;
        resource_atomic_source_statement := Hstatement;
        resource_atomic_source_trusted := Htrusted;
        resource_atomic_body_derivation := Hbody';
        resource_atomic_body_aligned := _ |}.
      eapply (@Validity.Certified.ResourceAlignedExistsPreserve cost Γ F Δ
        t fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        inner body0 body post certificate Hbody).
      exact Haligned_body.
  Defined.

  Lemma aligned_atomic_decomposition_body_valid
      {cost Γ F Δ fuel state statement outer inner pre post body}
      {body_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        body inner}
      (decomposition : @aligned_atomic_decomposition cost Γ F Δ fuel state
        outer inner statement body pre post body_certificate)
      (stack : list RuntimeAdapter.Atomicity.access_marker)
      (Hwf : RuntimeAdapter.Atomicity.state_wf
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true))
      (Hlifo : RuntimeAdapter.Atomicity.lifo_certificate body_certificate stack
        stack) :
    Validity.certificate_semantically_valid (stack_in := stack)
      (stack_out := stack) (pre := pre) (post := post) body_certificate.
  Proof.
    eapply Validity.aligned_certificate_valid.
    - exact Hwf.
    - exact Hlifo.
    - exact (atomic_body_aligned _ decomposition).
  Qed.

  Lemma resource_aligned_atomic_decomposition_body_valid
      {cost Γ F Δ fuel state statement outer inner pre post body}
      {body_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        body inner}
      (decomposition : @resource_aligned_atomic_decomposition cost Γ F Δ fuel
        state outer inner statement body pre post body_certificate)
      (stack : list RuntimeAdapter.Atomicity.access_marker)
      (Hwf : RuntimeAdapter.Atomicity.state_wf
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true))
      (Hlifo : RuntimeAdapter.Atomicity.lifo_certificate body_certificate stack
        stack)
      (Hprocedure_cost : Validity.Certified.procedure_cost_model_sound cost) :
    Validity.certificate_semantically_valid (stack_in := stack)
      (stack_out := stack) (pre := pre) (post := post) body_certificate.
  Proof.
    eapply Validity.resource_aligned_certificate_valid.
    - exact Hwf.
    - exact Hlifo.
    - exact Hprocedure_cost.
    - exact (resource_atomic_body_aligned _ decomposition).
  Qed.

  Lemma atomic_body_entry_wf {state outer}
      (step : RuntimeAdapter.Atomicity.take_step
        RuntimeAdapter.Atomicity.AtomicStep state = inr outer) :
    RuntimeAdapter.Atomicity.state_wf state ->
    RuntimeAdapter.Atomicity.state_wf
      (RuntimeAdapter.Atomicity.AnalysisState
        (RuntimeAdapter.Atomicity.analysis_mask outer)
        (RuntimeAdapter.Atomicity.analysis_open outer)
        (RuntimeAdapter.Atomicity.analysis_step_taken outer) true).
  Proof.
    intros Hwf. pose proof step as Hsets.
    apply RuntimeAdapter.Atomicity.atomic_step_preserves_sets in Hsets as
      [Hmask Hopen].
    unfold RuntimeAdapter.Atomicity.state_wf in *. simpl.
    rewrite Hmask. rewrite Hopen. exact Hwf.
  Qed.

  (** Assembly point for the core conditional.  Wrapper cases supply the
      three displayed entailments while recursively preserving their binder
      environment.  Keeping those transports explicit prevents the old
      runtime-only proof from choosing an arm independently of the concrete
      guard. *)
  Lemma aligned_conditional_semantic_assembly
      {Γ F Δ node state then_exit else_exit}
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env)
      (store : Runtime.IR.Core.symbolic_store Γ F Δ)
      (frame outer_pre then_pre else_pre :
        Runtime.Translation.Assertions.assertion Γ F Δ)
      (condition : Runtime.IR.pexpr Γ typed_core.TypedCore.TBool)
      (ambient : coPset) (then_branch else_branch : Runtime.IR.stmt Γ)
      (access post : iProp Resources.Σ) (then_refine :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms then_pre ∗ access) ⊢
        Validity.translated_runtime_wp runtime ambient state then_exit
          then_branch post)
      (else_refine :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms else_pre ∗ access) ⊢
        Validity.translated_runtime_wp runtime ambient state else_exit
          else_branch post)
      (pre_transport :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms outer_pre ∗ access) ⊢
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms
           (Runtime.Translation.Assertions.AAnd
             (Runtime.Translation.Assertions.AStack store) frame) ∗ access))
      (then_transport :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms
           (Runtime.Translation.Assertions.AAnd
             (Runtime.Translation.Assertions.AStack store)
             (Runtime.Translation.Assertions.AAnd frame
               (Runtime.Translation.Assertions.AExpr
                 (Runtime.Validation.Hoare.symbolize_expr store condition)))) ∗
         access) ⊢
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms then_pre ∗ access))
      (else_transport :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms
           (Runtime.Translation.Assertions.AAnd
             (Runtime.Translation.Assertions.AStack store)
             (Runtime.Translation.Assertions.AAnd frame
               (Runtime.Translation.Assertions.AExpr
                 (Runtime.Core.EUnOp Runtime.Core.UNot
                   (Runtime.Validation.Hoare.symbolize_expr store
                     condition))))) ∗ access) ⊢
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms else_pre ∗ access))
      (open_equal : RuntimeAdapter.Atomicity.analysis_open then_exit =
        RuntimeAdapter.Atomicity.analysis_open else_exit) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms outer_pre ∗ access) ⊢
    Validity.translated_runtime_wp runtime ambient state
      (RuntimeAdapter.conditional_join then_exit else_exit)
      (Runtime.IR.TIf node condition then_branch else_branch) post.
  Proof.
    etrans; first exact pre_transport.
    eapply ConcreteChunks.aligned_conditional_interpreted_runtime_refinement;
      [| |exact open_equal].
    - etrans; first exact then_transport. exact then_refine.
    - etrans; first exact else_transport. exact else_refine.
  Qed.

  (** Phase 7 remaining semantic interfaces.

      This is the assertion-aware, concrete-runtime counterpart of
      [Validity.aligned_runtime_certificate_valid].  It is deliberately
      indexed by the original derivation: structural Hoare wrappers may
      change assertions and binder contexts even though the underlying
      analysis certificate is unchanged. *)
  Definition aligned_certificate_translated_runtime_refinement
      {cost Γ F Δ fuel entry statement exit pre post}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post) : Prop :=
    forall stack_in stack_out,
    Validity.Model.runtime_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in stack_out ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
    Validity.Certified.certificate_hoare_aligned cost certificate derivation ->
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset),
    Validity.Model.runtime_mask
      (RuntimeAdapter.Atomicity.certificate_footprint certificate) ⊆ ambient ->
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack_in) ⊢
    Validity.translated_runtime_wp runtime ambient entry exit statement
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       Validity.World.access_stack_interp atoms ambient stack_out).

  (** Resource-indexed counterpart.  Resource procedure leaves consume
      [Hprocedure_cost], while the concrete translated-runtime layer keeps
      [Hruntime_cost] available for its physical-step side conditions. *)
  Definition resource_certificate_translated_runtime_refinement
      {cost Γ F Δ fuel entry statement exit pre post}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post) : Prop :=
    forall stack_in stack_out,
    Validity.Model.runtime_cost_model_sound cost ->
    Validity.Certified.procedure_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in stack_out ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
    Validity.Certified.resource_certificate_hoare_aligned cost certificate
      derivation ->
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset),
    Validity.Model.runtime_mask
      (RuntimeAdapter.Atomicity.certificate_footprint certificate) ⊆ ambient ->
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack_in) ⊢
    Validity.translated_runtime_wp runtime ambient entry exit statement
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       Validity.World.access_stack_interp atoms ambient stack_out).

  (** The tempting stronger theorem for *all* aligned certificates cannot be
      proved by structural composition at [AlignedSequence].  A first child
      may end in an unmatched unfold and the second child may contain its
      matching fold.  Erasing the proof-only boundary changes the active Iris
      mask of the physical continuation, so [translated_runtime_wp_sequence]
      is applicable only when the intermediate open set is unchanged.  Such
      sequences are handled by the normalized focused-region induction, not
      by this certificate-local wrapper layer. *)

  Lemma aligned_certificate_translated_frame
      {cost Γ F Δ fuel entry statement exit pre post}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post)
      (inner_aligned : Validity.Certified.certificate_hoare_aligned cost
        certificate derivation)
      (frame : Runtime.Translation.Assertions.assertion Γ F Δ) :
    aligned_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ) (pre := pre) (post := post)
      certificate derivation ->
    aligned_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ)
      (pre := Runtime.Translation.Assertions.AAnd pre frame)
      (post := Runtime.Translation.Assertions.AAnd post frame) certificate
      (Validity.Certified.Rules.FrameRule pre post frame statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) derivation).
  Proof.
    intros Hinner stack_in stack_out Hcost Hwf Hlifo Hstack Haligned runtime
      formals binders atoms ambient Hfootprint.
    iIntros "[#Hworld [Hpre Haccess]]".
    iDestruct "Hpre" as "[Hpre Hframe]".
    iPoseProof (Hinner stack_in stack_out Hcost Hwf Hlifo Hstack inner_aligned
      runtime formals binders atoms ambient Hfootprint
      with "[$Hworld $Hpre $Haccess]") as "Hwp".
    iPoseProof (Validity.translated_runtime_wp_frame runtime ambient entry exit
      statement
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       Validity.World.access_stack_interp atoms ambient stack_out)%I
      (Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms frame)%I
      with "[$Hwp $Hframe]") as "Hwp'".
    iApply (Validity.translated_runtime_wp_mono with "Hwp'").
    iIntros "[[#Hworld [Hpost Haccess]] Hframe]".
    iFrame "Hworld Hpost Hframe Haccess".
  Qed.

  Lemma resource_certificate_translated_frame
      {cost Γ F Δ fuel entry statement exit pre post}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post)
      (inner_aligned :
        Validity.Certified.resource_certificate_hoare_aligned cost certificate
          derivation)
      (frame : Runtime.Translation.Assertions.assertion Γ F Δ) :
    resource_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ) (pre := pre) (post := post) certificate derivation ->
    resource_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ)
      (pre := Runtime.Translation.Assertions.AAnd pre frame)
      (post := Runtime.Translation.Assertions.AAnd post frame) certificate
      (Validity.Certified.Rules.ResourceFrameRule pre post frame statement
        derivation).
  Proof.
    intros Hinner stack_in stack_out Hruntime_cost Hprocedure_cost Hwf Hlifo
      Hstack _ runtime formals binders atoms ambient Hfootprint.
    iIntros "[#Hworld [Hpre Haccess]]".
    iDestruct "Hpre" as "[Hpre Hframe]".
    iPoseProof (Hinner stack_in stack_out Hruntime_cost Hprocedure_cost Hwf
      Hlifo Hstack inner_aligned runtime formals binders atoms ambient
      Hfootprint with "[$Hworld $Hpre $Haccess]") as "Hwp".
    iPoseProof (Validity.translated_runtime_wp_frame runtime ambient entry exit
      statement
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       Validity.World.access_stack_interp atoms ambient stack_out)%I
      (Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms frame)%I
      with "[$Hwp $Hframe]") as "Hwp'".
    iApply (Validity.translated_runtime_wp_mono with "Hwp'").
    iIntros "[[#Hworld [Hpost Haccess]] Hframe]".
    iFrame "Hworld Hpost Hframe Haccess".
  Qed.

  Lemma aligned_certificate_translated_consequence
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit pre pre' post post'}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post)
      (inner_aligned : Validity.Certified.certificate_hoare_aligned cost
        certificate derivation)
      (pre_entails : Runtime.Validation.Hoare.assertion_entails pre' pre)
      (post_entails : Runtime.Validation.Hoare.assertion_entails post post') :
    aligned_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ) (pre := pre) (post := post)
      certificate derivation ->
    aligned_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ) (pre := pre') (post := post') certificate
      (Validity.Certified.Rules.ConsequenceRule pre pre' post post' statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) derivation pre_entails
        post_entails).
  Proof.
    intros Hinner stack_in stack_out Hcost Hwf Hlifo Hstack _ runtime formals
      binders atoms ambient Hfootprint.
    iIntros "[#Hworld [Hpre' Haccess]]".
    iPoseProof (Validity.VSemantics.assertion_entails_valid
      (Leaf.predicates atoms) pre' pre pre_entails runtime formals binders atoms
      with "Hpre'") as "Hpre".
    iPoseProof (Hinner stack_in stack_out Hcost Hwf Hlifo Hstack inner_aligned
      runtime formals binders atoms ambient Hfootprint
      with "[$Hworld $Hpre $Haccess]") as "Hwp".
    iApply (Validity.translated_runtime_wp_mono with "Hwp").
    iIntros "[#Hworld [Hpost Haccess]]". iFrame "Hworld Haccess".
    iApply (Validity.VSemantics.assertion_entails_valid
      (Leaf.predicates atoms) post post' post_entails runtime formals binders
      atoms with "Hpost").
  Qed.

  Lemma aligned_certificate_translated_exists_elim
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {t fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (body : Runtime.Translation.Assertions.assertion Γ F (t :: Δ))
      (post : Runtime.Translation.Assertions.assertion Γ F Δ)
      (derivation : Validity.Certified.Rules.RavenHoareTriple body statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit)
        (Runtime.Translation.Assertions.weaken_assertion post))
      (inner_aligned : Validity.Certified.certificate_hoare_aligned cost
        certificate derivation) :
    aligned_certificate_translated_runtime_refinement
      (F := F) (Δ := t :: Δ) (pre := body)
      (post := Runtime.Translation.Assertions.weaken_assertion post)
      certificate derivation ->
    aligned_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ)
      (pre := Runtime.Translation.Assertions.AExists t body)
      (post := post) certificate
      (Validity.Certified.Rules.ExistsElimRule t body post statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) derivation).
  Proof.
    intros Hinner stack_in stack_out Hcost Hwf Hlifo Hstack _ runtime formals
      binders atoms ambient Hfootprint.
    iIntros "[#Hworld [Hpre Haccess]]". iDestruct "Hpre" as (value) "Hbody".
    iPoseProof (Hinner stack_in stack_out Hcost Hwf Hlifo Hstack inner_aligned
      runtime formals (Runtime.Translation.binder_cons value binders) atoms ambient
      Hfootprint with "[$Hworld $Hbody $Haccess]") as "Hwp".
    iApply (Validity.translated_runtime_wp_mono with "Hwp").
    iIntros "[#Hworld [Hpost Haccess]]". iFrame "Hworld Haccess".
    rewrite Validity.VSemantics.S.interp_weaken_assertion. iExact "Hpost".
  Qed.

  Lemma aligned_certificate_translated_exists_preserve
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {t fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (body post : Runtime.Translation.Assertions.assertion Γ F (t :: Δ))
      (derivation : Validity.Certified.Rules.RavenHoareTriple body statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post)
      (inner_aligned : Validity.Certified.certificate_hoare_aligned cost
        certificate derivation) :
    aligned_certificate_translated_runtime_refinement
      (F := F) (Δ := t :: Δ) (pre := body) (post := post)
      certificate derivation ->
    aligned_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ)
      (pre := Runtime.Translation.Assertions.AExists t body)
      (post := Runtime.Translation.Assertions.AExists t post) certificate
      (Validity.Certified.Rules.ExistsPreserveRule t body post statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) derivation).
  Proof.
    intros Hinner stack_in stack_out Hcost Hwf Hlifo Hstack _ runtime formals
      binders atoms ambient Hfootprint.
    iIntros "[#Hworld [Hpre Haccess]]". iDestruct "Hpre" as (value) "Hbody".
    iPoseProof (Hinner stack_in stack_out Hcost Hwf Hlifo Hstack inner_aligned
      runtime formals (Runtime.Translation.binder_cons value binders) atoms ambient
      Hfootprint with "[$Hworld $Hbody $Haccess]") as "Hwp".
    iApply (Validity.translated_runtime_wp_mono with "Hwp").
    iIntros "[#Hworld [Hpost Haccess]]". iFrame "Hworld Haccess".
    iExists value. iExact "Hpost".
  Qed.

  Lemma resource_certificate_translated_consequence
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit pre pre' post post'}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post)
      (inner_aligned :
        Validity.Certified.resource_certificate_hoare_aligned cost certificate
          derivation)
      (pre_entails : Runtime.Validation.Hoare.assertion_entails pre' pre)
      (post_entails : Runtime.Validation.Hoare.assertion_entails post post') :
    resource_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ) (pre := pre) (post := post) certificate derivation ->
    resource_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ) (pre := pre') (post := post') certificate
      (Validity.Certified.Rules.ResourceConsequenceRule pre pre' post post'
        statement derivation pre_entails post_entails).
  Proof.
    intros Hinner stack_in stack_out Hruntime_cost Hprocedure_cost Hwf Hlifo
      Hstack _ runtime formals binders atoms ambient Hfootprint.
    iIntros "[#Hworld [Hpre' Haccess]]".
    iPoseProof (Validity.VSemantics.assertion_entails_valid
      (Leaf.predicates atoms) pre' pre pre_entails runtime formals binders atoms
      with "Hpre'") as "Hpre".
    iPoseProof (Hinner stack_in stack_out Hruntime_cost Hprocedure_cost Hwf
      Hlifo Hstack inner_aligned runtime formals binders atoms ambient
      Hfootprint with "[$Hworld $Hpre $Haccess]") as "Hwp".
    iApply (Validity.translated_runtime_wp_mono with "Hwp").
    iIntros "[#Hworld [Hpost Haccess]]". iFrame "Hworld Haccess".
    iApply (Validity.VSemantics.assertion_entails_valid
      (Leaf.predicates atoms) post post' post_entails runtime formals binders
      atoms with "Hpost").
  Qed.

  Lemma resource_certificate_translated_exists_elim
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {t fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (body : Runtime.Translation.Assertions.assertion Γ F (t :: Δ))
      (post : Runtime.Translation.Assertions.assertion Γ F Δ)
      (derivation : Validity.Certified.Rules.RavenResourceTriple body statement
        (Runtime.Translation.Assertions.weaken_assertion post))
      (inner_aligned :
        Validity.Certified.resource_certificate_hoare_aligned cost certificate
          derivation) :
    resource_certificate_translated_runtime_refinement
      (F := F) (Δ := t :: Δ) (pre := body)
      (post := Runtime.Translation.Assertions.weaken_assertion post)
      certificate derivation ->
    resource_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ)
      (pre := Runtime.Translation.Assertions.AExists t body)
      (post := post) certificate
      (Validity.Certified.Rules.ResourceExistsElimRule t body post statement
        derivation).
  Proof.
    intros Hinner stack_in stack_out Hruntime_cost Hprocedure_cost Hwf Hlifo
      Hstack _ runtime formals binders atoms ambient Hfootprint.
    iIntros "[#Hworld [Hpre Haccess]]". iDestruct "Hpre" as (value) "Hbody".
    iPoseProof (Hinner stack_in stack_out Hruntime_cost Hprocedure_cost Hwf
      Hlifo Hstack inner_aligned runtime formals
      (Runtime.Translation.binder_cons value binders) atoms ambient Hfootprint
      with "[$Hworld $Hbody $Haccess]") as "Hwp".
    iApply (Validity.translated_runtime_wp_mono with "Hwp").
    iIntros "[#Hworld [Hpost Haccess]]". iFrame "Hworld Haccess".
    rewrite Validity.VSemantics.S.interp_weaken_assertion. iExact "Hpost".
  Qed.

  Lemma resource_certificate_translated_exists_preserve
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {t fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (body post : Runtime.Translation.Assertions.assertion Γ F (t :: Δ))
      (derivation : Validity.Certified.Rules.RavenResourceTriple body statement
        post)
      (inner_aligned :
        Validity.Certified.resource_certificate_hoare_aligned cost certificate
          derivation) :
    resource_certificate_translated_runtime_refinement
      (F := F) (Δ := t :: Δ) (pre := body) (post := post)
      certificate derivation ->
    resource_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ)
      (pre := Runtime.Translation.Assertions.AExists t body)
      (post := Runtime.Translation.Assertions.AExists t post) certificate
      (Validity.Certified.Rules.ResourceExistsPreserveRule t body post
        statement derivation).
  Proof.
    intros Hinner stack_in stack_out Hruntime_cost Hprocedure_cost Hwf Hlifo
      Hstack _ runtime formals binders atoms ambient Hfootprint.
    iIntros "[#Hworld [Hpre Haccess]]". iDestruct "Hpre" as (value) "Hbody".
    iPoseProof (Hinner stack_in stack_out Hruntime_cost Hprocedure_cost Hwf
      Hlifo Hstack inner_aligned runtime formals
      (Runtime.Translation.binder_cons value binders) atoms ambient Hfootprint
      with "[$Hworld $Hbody $Haccess]") as "Hwp".
    iApply (Validity.translated_runtime_wp_mono with "Hwp").
    iIntros "[#Hworld [Hpost Haccess]]". iFrame "Hworld Haccess".
    iExists value. iExact "Hpost".
  Qed.

  (** Resource-proof analogue of [aligned_conditional_core_obligation].  The
      only semantic difference is that a conditional core carries resource
      triples, so its concrete refinement retains both cost-model witnesses.
      The wrapper spine itself is unchanged. *)
  Definition resource_aligned_conditional_core_obligation
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit}
      {pre post : Runtime.Translation.Assertions.assertion Γ F Δ}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post}
      (aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        certificate derivation) : Prop.
  Proof.
    induction aligned.
    - exact False.
    - exact False.
    - exact False.
    - exact False.
    - exact (@resource_certificate_translated_runtime_refinement cost Γ F Δ
        (S fuel) state (Runtime.IR.TIf node condition then_branch else_branch)
        (RuntimeAdapter.conditional_join then_exit else_exit) _ post
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state
          (Runtime.IR.TIf node condition then_branch else_branch)
          then_branch else_branch then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal)
        (Validity.Certified.Rules.ResourceConditionalRule node store frame
          condition then_branch else_branch post then_derivation
          else_derivation)).
    - exact False.
    - exact IHaligned.
    - exact IHaligned.
    - exact IHaligned.
    - exact IHaligned.
  Defined.

  (** Semantic motive carried by the wrapper-sensitive branch payload.  At
      the exposed conditional core it asks for translated-runtime
      refinements of the exact retained child certificates; structural
      wrappers preserve that request recursively. *)
  Definition resource_conditional_branch_data_semantic
      {cost Γ F Δ fuel entry statement then_statement else_statement
        then_exit else_exit pre post view then_certificate else_certificate
        open_equal atomic_equal derivation aligned stack_in join_stack mode
        tail then_tree else_tree lifo Hthen Helse}
      (data : @resource_conditional_branch_data cost Γ F Δ fuel entry
        statement then_statement else_statement then_exit else_exit pre post
        view then_certificate else_certificate open_equal atomic_equal
        derivation aligned stack_in join_stack mode tail then_tree else_tree
        lifo Hthen Helse) : Prop.
  Proof.
    induction data.
    - exact (resource_certificate_translated_runtime_refinement then_certificate
        then_derivation /\
      resource_certificate_translated_runtime_refinement else_certificate
        else_derivation).
    - exact IHdata.
    - exact IHdata.
    - exact IHdata.
    - exact IHdata.
  Defined.

  Theorem resource_aligned_conditional_wrapper_translated_runtime_refinement
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit pre post}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post}
      (aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        certificate derivation) :
    resource_aligned_conditional_core_obligation aligned ->
    resource_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ) (pre := pre) (post := post)
      certificate derivation.
  Proof.
    induction aligned; simpl; intros Hcore; try contradiction.
    - exact Hcore.
    - eapply resource_certificate_translated_frame; eauto.
    - eapply resource_certificate_translated_consequence; eauto.
    - eapply resource_certificate_translated_exists_elim; eauto.
    - eapply resource_certificate_translated_exists_preserve; eauto.
  Qed.

  (** A wrapper-sensitive eliminator for conditional alignments.  At the
      unique conditional core it asks for the concrete, trace-aware head
      refinement that the next constructor proof supplies.  Structural
      wrappers merely propagate that obligation; every other certificate
      constructor is impossible for this adapter.  Indexing the obligation by
      the alignment proof itself retains existential binder changes and the
      exact pre/post derivations without flattening them into a same-context
      record. *)
  Fixpoint aligned_conditional_core_obligation
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit}
      {pre post : Runtime.Translation.Assertions.assertion Γ F Δ}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post}
      (aligned : Validity.Certified.certificate_hoare_aligned cost certificate
        derivation) : Prop :=
    match aligned with
    | Validity.Certified.AlignedConditional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ =>
        aligned_certificate_translated_runtime_refinement certificate derivation
    | Validity.Certified.AlignedFrame _ _ _ _ _ _ _ _ _ _ _ _ _ inner =>
        aligned_conditional_core_obligation inner
    | Validity.Certified.AlignedConsequence _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ inner => aligned_conditional_core_obligation inner
    | Validity.Certified.AlignedExistsElim _ Γ' F' Δ' t' fuel' entry' exit'
        statement' body' post' certificate' derivation' inner =>
        @aligned_conditional_core_obligation cost Γ' F' (t' :: Δ') fuel'
          entry' statement' exit' body'
          (Runtime.Translation.Assertions.weaken_assertion post') certificate'
          derivation' inner
    | Validity.Certified.AlignedExistsPreserve _ Γ' F' Δ' t' fuel' entry' exit'
        statement' body' post' certificate' derivation' inner =>
        @aligned_conditional_core_obligation cost Γ' F' (t' :: Δ') fuel'
          entry' statement' exit' body' post' certificate' derivation' inner
    | _ => False
    end.

  Theorem aligned_conditional_wrapper_translated_runtime_refinement
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit pre post}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post}
      (aligned : Validity.Certified.certificate_hoare_aligned cost certificate
        derivation) :
    aligned_conditional_core_obligation aligned ->
    aligned_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ) (pre := pre) (post := post)
      certificate derivation.
  Proof.
    induction aligned; simpl; intros Hcore; try contradiction.
    - exact Hcore.
    - eapply aligned_certificate_translated_frame; eauto.
    - eapply aligned_certificate_translated_consequence; eauto.
    - eapply aligned_certificate_translated_exists_elim; eauto.
    - eapply aligned_certificate_translated_exists_preserve; eauto.
  Qed.

  (** The closed seam target, CPS-style, specialized to one concrete LIFO
      transition.  Unlike a first attempt that fixed a shared continuation
      ahead of time (indexing by a concrete [rest_suffix] and its constant
      [final_post]/[final_stack_out]), this version is parametric in an
      arbitrary continuation premise over the certificate's own [post] and a
      [carried] resource threaded from entry to the seam.  That
      parametricity is exactly what makes the wrapper transports below
      meaningful instead of vacuous: [Frame] adds [interp frame] to
      [carried], which survives untouched until the continuation premise --
      supplied by whoever discharges this obligation -- actually consumes
      it; a version fixing the continuation ahead of time let [Frame]
      discard the framed resource for free ([pre ∗ frame ⊢ pre]), which is
      provable but useless, since nothing then reaches the continuation.

      Unlike a first version of this same interface, [stack_in]/[mid_stack]/
      [lifo] are explicit parameters, not bound by an internal [forall]:
      this is a trace-local obligation about the one concrete LIFO
      transition the parent [AlignedTraceConditional] (or, generally,
      whatever normalized-trace constructor is discharging this fact)
      already supplies, not a global property of the certificate for every
      LIFO transition it could in principle admit.  All four wrapper
      transports below preserve [certificate] exactly (Frame/Consequence
      change only [pre]/[post]/[derivation]; ExistsElim/ExistsPreserve
      change only [Δ]/[body]/[post], never [Γ]/[entry]/[statement]/[exit]/
      [certificate] itself -- see their definitions in
      [typed_runtime.v:280-327]), so [stack_in]/[mid_stack]/[lifo] thread
      through unchanged.

      Also unlike a first version, the continuation is a [rest_source :
      RuntimeAdapter.certificate_suffix cost Γ exit final_exit] -- the
      erased Raven suffix attached to the whole conditional certificate's
      own [exit] (never to a branch's own exit, which would reintroduce the
      forbidden branch-exit/join identification) -- rather than a bare,
      externally fixed [option runtime_stmt].  A bare [rest_runtime] fixed
      *before* the internal [forall runtime ...] cannot be made to equal
      [ConcreteOrdinaryTrace.source_runtime rest_source runtime] for every
      [runtime] simultaneously, since that erasure genuinely varies with
      [runtime] (concrete variable/stack-id naming); computing
      [ConcreteOrdinaryTrace.source_runtime rest_source runtime] *after*
      [runtime] is introduced avoids that mismatch while keeping
      [runtime]/[formals]/[binders]/[atoms] internally quantified -- which
      the [AlignedExistsElim]/[AlignedExistsPreserve] transports need:
      [ExistsElim] invokes the inner refinement at
      [Runtime.Translation.binder_cons value binders], a *different*
      [binders] value per witness, so the inner fact must stay
      polymorphic in [binders] rather than being pre-specialized to one. *)
  (** Resource-indexed seam CPS target.  This deliberately preserves the
      old first-close continuation shape: it never flattens the certificate
      and continuation across a mask-changing access boundary. *)
  Definition resource_aligned_certificate_seam_refinement
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit pre post}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post)
      (stack_in mid_stack : list RuntimeAdapter.Atomicity.access_marker)
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in
        mid_stack)
      {final_exit : RuntimeAdapter.Atomicity.analysis_state}
      (rest_source : RuntimeAdapter.certificate_suffix cost Γ exit final_exit)
      (ambient : coPset) : Prop :=
    Validity.Model.runtime_cost_model_sound cost ->
    Validity.Certified.procedure_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
    Validity.Certified.resource_certificate_hoare_aligned cost certificate
      derivation ->
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env),
    Validity.Model.runtime_mask
      (RuntimeAdapter.Atomicity.certificate_footprint certificate) ⊆ ambient ->
    forall (final_mask : coPset) (carried final : iProp Resources.Σ),
    ((Validity.global_world_context atoms ∗
      Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms post ∗
      Validity.World.access_stack_interp atoms ambient mid_stack ∗ carried) ⊢
      Validity.runtime_option_wp
        (Validity.Model.active_runtime_mask ambient exit) final_mask
        (ConcreteOrdinaryTrace.source_runtime rest_source runtime) final) ->
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack_in ∗ carried) ⊢
    Validity.runtime_option_wp
      (Validity.Model.active_runtime_mask ambient entry) final_mask
      (Validity.Model.combine_runtime_statements
        (Validity.certificate_runtime_statement certificate runtime)
        (ConcreteOrdinaryTrace.source_runtime rest_source runtime)) final.

  Definition aligned_certificate_seam_refinement
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit pre post}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post)
      (stack_in mid_stack : list RuntimeAdapter.Atomicity.access_marker)
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in
        mid_stack)
      {final_exit : RuntimeAdapter.Atomicity.analysis_state}
      (rest_source : RuntimeAdapter.certificate_suffix cost Γ exit final_exit)
      (ambient : coPset) : Prop :=
    Validity.Model.runtime_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
    Validity.Certified.certificate_hoare_aligned cost certificate derivation ->
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env),
    Validity.Model.runtime_mask
      (RuntimeAdapter.Atomicity.certificate_footprint certificate) ⊆ ambient ->
    forall (final_mask : coPset) (carried final : iProp Resources.Σ),
    ((Validity.global_world_context atoms ∗
      Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms post ∗
      Validity.World.access_stack_interp atoms ambient mid_stack ∗ carried) ⊢
      Validity.runtime_option_wp
        (Validity.Model.active_runtime_mask ambient exit) final_mask
        (ConcreteOrdinaryTrace.source_runtime rest_source runtime) final) ->
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack_in ∗ carried) ⊢
    Validity.runtime_option_wp
      (Validity.Model.active_runtime_mask ambient entry) final_mask
      (Validity.Model.combine_runtime_statements
        (Validity.certificate_runtime_statement certificate runtime)
        (ConcreteOrdinaryTrace.source_runtime rest_source runtime))
      final.

  Lemma resource_aligned_certificate_seam_frame
      {cost Γ F Δ fuel entry statement exit pre post}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post)
      (inner_aligned : Validity.Certified.resource_certificate_hoare_aligned
        cost certificate derivation)
      {stack_in mid_stack}
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in
        mid_stack)
      {final_exit}
      (rest_source : RuntimeAdapter.certificate_suffix cost Γ exit final_exit)
      (ambient : coPset)
      (frame : Runtime.Translation.Assertions.assertion Γ F Δ) :
    resource_aligned_certificate_seam_refinement
      (F := F) (Δ := Δ) (pre := pre) (post := post)
      certificate derivation stack_in mid_stack lifo rest_source ambient ->
    resource_aligned_certificate_seam_refinement
      (F := F) (Δ := Δ)
      (pre := Runtime.Translation.Assertions.AAnd pre frame)
      (post := Runtime.Translation.Assertions.AAnd post frame) certificate
      (Validity.Certified.Rules.ResourceFrameRule pre post frame statement
        derivation) stack_in mid_stack lifo rest_source ambient.
  Proof.
    intros Hinner Hruntime_cost Hprocedure_cost Hwf Hstack _ runtime
      formals binders atoms Hfootprint final_mask carried final Hcont.
    iIntros "[#Hworld [[Hpre Hframe] Hrest]]".
    iApply (Hinner Hruntime_cost Hprocedure_cost Hwf Hstack inner_aligned
      runtime formals binders atoms Hfootprint final_mask
      (Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms frame ∗ carried)%I final).
    - iIntros "[#Hworld' [Hpost [Haccess [Hframe' Hcarried]]]]".
      iApply Hcont. iFrame "Hworld' Hframe' Hcarried". iFrame "Hpost Haccess".
    - iFrame "Hworld Hpre Hframe Hrest".
  Qed.

  Lemma aligned_certificate_seam_frame
      {cost Γ F Δ fuel entry statement exit pre post}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post)
      (inner_aligned : Validity.Certified.certificate_hoare_aligned cost
        certificate derivation)
      {stack_in mid_stack}
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in
        mid_stack)
      {final_exit}
      (rest_source : RuntimeAdapter.certificate_suffix cost Γ exit final_exit)
      (ambient : coPset)
      (frame : Runtime.Translation.Assertions.assertion Γ F Δ) :
    aligned_certificate_seam_refinement
      (F := F) (Δ := Δ) (pre := pre) (post := post)
      certificate derivation stack_in mid_stack lifo rest_source ambient ->
    aligned_certificate_seam_refinement
      (F := F) (Δ := Δ)
      (pre := Runtime.Translation.Assertions.AAnd pre frame)
      (post := Runtime.Translation.Assertions.AAnd post frame) certificate
      (Validity.Certified.Rules.FrameRule pre post frame statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) derivation)
      stack_in mid_stack lifo rest_source ambient.
  Proof.
    intros Hinner Hcost Hwf Hstack Haligned runtime
      formals binders atoms Hfootprint final_mask carried final Hcont.
    iIntros "[#Hworld [[Hpre Hframe] Hrest]]".
    iApply (Hinner Hcost Hwf Hstack inner_aligned
      runtime formals binders atoms Hfootprint final_mask
      (Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms frame ∗ carried)%I final).
    - iIntros "[#Hworld' [Hpost [Haccess [Hframe' Hcarried]]]]".
      iApply Hcont. iFrame "Hworld' Hframe' Hcarried". iFrame "Hpost Haccess".
    - iFrame "Hworld Hpre Hframe Hrest".
  Qed.

  Lemma resource_aligned_certificate_seam_consequence
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit pre pre' post post'}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel entry statement exit)
      (derivation : Validity.Certified.Rules.RavenResourceTriple pre statement post)
      (inner_aligned : Validity.Certified.resource_certificate_hoare_aligned cost certificate derivation)
      {stack_in mid_stack} (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in mid_stack)
      {final_exit} (rest_source : RuntimeAdapter.certificate_suffix cost Γ exit final_exit)
      (ambient : coPset)
      (pre_entails : Runtime.Validation.Hoare.assertion_entails pre' pre)
      (post_entails : Runtime.Validation.Hoare.assertion_entails post post') :
    resource_aligned_certificate_seam_refinement (F := F) (Δ := Δ)
      (pre := pre) (post := post) certificate derivation stack_in mid_stack lifo rest_source ambient ->
    resource_aligned_certificate_seam_refinement (F := F) (Δ := Δ)
      (pre := pre') (post := post') certificate
      (Validity.Certified.Rules.ResourceConsequenceRule pre pre' post post' statement derivation pre_entails post_entails)
      stack_in mid_stack lifo rest_source ambient.
  Proof.
    intros Hinner Hruntime_cost Hprocedure_cost Hwf Hstack _ runtime formals binders atoms Hfootprint final_mask carried final Hcont.
    iIntros "[#Hworld [Hpre' Hrest]]".
    iPoseProof (Validity.VSemantics.assertion_entails_valid (Leaf.predicates atoms) pre' pre pre_entails runtime formals binders atoms with "Hpre'") as "Hpre".
    iApply (Hinner Hruntime_cost Hprocedure_cost Hwf Hstack inner_aligned runtime formals binders atoms Hfootprint final_mask carried final).
    - iIntros "[#Hworld' [Hpost Hcarried]]". iApply Hcont. iFrame "Hworld'".
      iPoseProof (Validity.VSemantics.assertion_entails_valid (Leaf.predicates atoms) post post' post_entails runtime formals binders atoms with "Hpost") as "Hpost'".
      iFrame "Hpost' Hcarried".
    - iFrame "Hworld Hpre Hrest".
  Qed.

  Lemma resource_aligned_certificate_seam_exists_elim
      {cost} {Γ F Δ : typed_core.TypedCore.context} {t fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel entry statement exit)
      (body : Runtime.Translation.Assertions.assertion Γ F (t :: Δ))
      (post : Runtime.Translation.Assertions.assertion Γ F Δ)
      (derivation : Validity.Certified.Rules.RavenResourceTriple body statement (Runtime.Translation.Assertions.weaken_assertion post))
      (inner_aligned : Validity.Certified.resource_certificate_hoare_aligned cost certificate derivation)
      {stack_in mid_stack} (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in mid_stack)
      {final_exit} (rest_source : RuntimeAdapter.certificate_suffix cost Γ exit final_exit) (ambient : coPset) :
    resource_aligned_certificate_seam_refinement (F := F) (Δ := t :: Δ) (pre := body) (post := Runtime.Translation.Assertions.weaken_assertion post) certificate derivation stack_in mid_stack lifo rest_source ambient ->
    resource_aligned_certificate_seam_refinement (F := F) (Δ := Δ) (pre := Runtime.Translation.Assertions.AExists t body) (post := post) certificate
      (Validity.Certified.Rules.ResourceExistsElimRule t body post statement derivation) stack_in mid_stack lifo rest_source ambient.
  Proof.
    intros Hinner Hruntime_cost Hprocedure_cost Hwf Hstack _ runtime formals binders atoms Hfootprint final_mask carried final Hcont.
    iIntros "[#Hworld [Hpre Hrest]]". iDestruct "Hpre" as (value) "Hbody".
    iApply (Hinner Hruntime_cost Hprocedure_cost Hwf Hstack inner_aligned runtime formals (Runtime.Translation.binder_cons value binders) atoms Hfootprint final_mask carried final).
    - iIntros "[#Hworld' [Hpost Hcarried]]". iApply Hcont. iFrame "Hworld' Hcarried".
      rewrite Validity.VSemantics.S.interp_weaken_assertion. iExact "Hpost".
    - iFrame "Hworld Hbody Hrest".
  Qed.

  Lemma resource_aligned_certificate_seam_exists_preserve
      {cost} {Γ F Δ : typed_core.TypedCore.context} {t fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel entry statement exit)
      (body post : Runtime.Translation.Assertions.assertion Γ F (t :: Δ))
      (derivation : Validity.Certified.Rules.RavenResourceTriple body statement post)
      (inner_aligned : Validity.Certified.resource_certificate_hoare_aligned cost certificate derivation)
      {stack_in mid_stack} (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in mid_stack)
      {final_exit} (rest_source : RuntimeAdapter.certificate_suffix cost Γ exit final_exit) (ambient : coPset) :
    resource_aligned_certificate_seam_refinement (F := F) (Δ := t :: Δ) (pre := body) (post := post) certificate derivation stack_in mid_stack lifo rest_source ambient ->
    resource_aligned_certificate_seam_refinement (F := F) (Δ := Δ) (pre := Runtime.Translation.Assertions.AExists t body) (post := Runtime.Translation.Assertions.AExists t post) certificate
      (Validity.Certified.Rules.ResourceExistsPreserveRule t body post statement derivation) stack_in mid_stack lifo rest_source ambient.
  Proof.
    intros Hinner Hruntime_cost Hprocedure_cost Hwf Hstack _ runtime formals binders atoms Hfootprint final_mask carried final Hcont.
    iIntros "[#Hworld [Hpre Hrest]]". iDestruct "Hpre" as (value) "Hbody".
    iApply (Hinner Hruntime_cost Hprocedure_cost Hwf Hstack inner_aligned runtime formals (Runtime.Translation.binder_cons value binders) atoms Hfootprint final_mask carried final).
    - iIntros "[#Hworld' [Hpost Hcarried]]". iApply Hcont. iFrame "Hworld' Hcarried". iExists value. iExact "Hpost".
    - iFrame "Hworld Hbody Hrest".
  Qed.

  (** Purely semantic wrapper obligation for the resource conditional seam.
      The Type-valued branch normalizations are constructed only while the
      [ResourceAlignedConditional] constructor is exposed; this Prop-valued
      interface is what can soundly pass through the proof wrappers. *)
  Definition resource_aligned_conditional_seam_core_obligation
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit pre post}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post}
      (aligned : @Validity.Certified.resource_certificate_hoare_aligned cost Γ
        F Δ fuel entry statement exit pre post certificate derivation) :
      forall (stack_in mid_stack : list RuntimeAdapter.Atomicity.access_marker),
      RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in mid_stack ->
      forall {final_exit : RuntimeAdapter.Atomicity.analysis_state},
      RuntimeAdapter.certificate_suffix cost Γ exit final_exit -> coPset -> Prop.
  Proof.
    induction aligned; intros stack_in mid_stack lifo final_exit rest_source
      ambient.
    - exact False.
    - exact False.
    - exact False.
    - exact False.
    - exact (resource_aligned_certificate_seam_refinement
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state
          (Runtime.IR.TIf node condition then_branch else_branch) then_branch
          else_branch then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal)
        (Validity.Certified.Rules.ResourceConditionalRule node store frame
          condition then_branch else_branch post then_derivation
          else_derivation)
        stack_in mid_stack lifo rest_source ambient).
    - exact False.
    - exact (IHaligned stack_in mid_stack lifo final_exit rest_source ambient).
    - exact (IHaligned stack_in mid_stack lifo final_exit rest_source ambient).
    - exact (IHaligned stack_in mid_stack lifo final_exit rest_source ambient).
    - exact (IHaligned stack_in mid_stack lifo final_exit rest_source ambient).
  Defined.

  Theorem resource_aligned_conditional_wrapper_seam_runtime_refinement
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit pre post}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post}
      (aligned : @Validity.Certified.resource_certificate_hoare_aligned cost Γ
        F Δ fuel entry statement exit pre post certificate derivation)
      {stack_in mid_stack : list RuntimeAdapter.Atomicity.access_marker}
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in
        mid_stack)
      {final_exit : RuntimeAdapter.Atomicity.analysis_state}
      (rest_source : RuntimeAdapter.certificate_suffix cost Γ exit final_exit)
      (ambient : coPset) :
    resource_aligned_conditional_seam_core_obligation aligned stack_in
      mid_stack lifo rest_source ambient ->
    resource_aligned_certificate_seam_refinement
      (F := F) (Δ := Δ) (pre := pre) (post := post)
      certificate derivation stack_in mid_stack lifo rest_source ambient.
  Proof.
    revert stack_in mid_stack lifo final_exit rest_source ambient.
    induction aligned; simpl; intros stack_in mid_stack lifo final_exit
      rest_source ambient Hcore; try contradiction.
    - exact Hcore.
    - eapply resource_aligned_certificate_seam_frame; eauto.
    - eapply resource_aligned_certificate_seam_consequence; eauto.
    - eapply resource_aligned_certificate_seam_exists_elim; eauto.
    - eapply resource_aligned_certificate_seam_exists_preserve; eauto.
  Qed.

  Lemma aligned_certificate_seam_consequence
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit pre pre' post post'}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post)
      (inner_aligned : Validity.Certified.certificate_hoare_aligned cost
        certificate derivation)
      {stack_in mid_stack}
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in
        mid_stack)
      {final_exit}
      (rest_source : RuntimeAdapter.certificate_suffix cost Γ exit final_exit)
      (ambient : coPset)
      (pre_entails : Runtime.Validation.Hoare.assertion_entails pre' pre)
      (post_entails : Runtime.Validation.Hoare.assertion_entails post post') :
    aligned_certificate_seam_refinement
      (F := F) (Δ := Δ) (pre := pre) (post := post)
      certificate derivation stack_in mid_stack lifo rest_source ambient ->
    aligned_certificate_seam_refinement
      (F := F) (Δ := Δ) (pre := pre') (post := post') certificate
      (Validity.Certified.Rules.ConsequenceRule pre pre' post post' statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) derivation pre_entails
        post_entails)
      stack_in mid_stack lifo rest_source ambient.
  Proof.
    intros Hinner Hcost Hwf Hstack _ runtime formals
      binders atoms Hfootprint final_mask carried final Hcont.
    iIntros "[#Hworld [Hpre' Hrest]]".
    iPoseProof (Validity.VSemantics.assertion_entails_valid
      (Leaf.predicates atoms) pre' pre pre_entails runtime formals binders atoms
      with "Hpre'") as "Hpre".
    iApply (Hinner Hcost Hwf Hstack inner_aligned
      runtime formals binders atoms Hfootprint final_mask carried final).
    - iIntros "[#Hworld' [Hpost Hcarried]]".
      iApply Hcont. iFrame "Hworld'".
      iPoseProof (Validity.VSemantics.assertion_entails_valid
        (Leaf.predicates atoms) post post' post_entails runtime formals binders
        atoms with "Hpost") as "Hpost'".
      iFrame "Hpost' Hcarried".
    - iFrame "Hworld Hpre Hrest".
  Qed.

  Lemma aligned_certificate_seam_exists_elim
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {t fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (body : Runtime.Translation.Assertions.assertion Γ F (t :: Δ))
      (post : Runtime.Translation.Assertions.assertion Γ F Δ)
      (derivation : Validity.Certified.Rules.RavenHoareTriple body statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit)
        (Runtime.Translation.Assertions.weaken_assertion post))
      (inner_aligned : Validity.Certified.certificate_hoare_aligned cost
        certificate derivation)
      {stack_in mid_stack}
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in
        mid_stack)
      {final_exit}
      (rest_source : RuntimeAdapter.certificate_suffix cost Γ exit final_exit)
      (ambient : coPset) :
    aligned_certificate_seam_refinement
      (F := F) (Δ := t :: Δ) (pre := body)
      (post := Runtime.Translation.Assertions.weaken_assertion post)
      certificate derivation stack_in mid_stack lifo rest_source ambient ->
    aligned_certificate_seam_refinement
      (F := F) (Δ := Δ)
      (pre := Runtime.Translation.Assertions.AExists t body)
      (post := post) certificate
      (Validity.Certified.Rules.ExistsElimRule t body post statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) derivation)
      stack_in mid_stack lifo rest_source ambient.
  Proof.
    intros Hinner Hcost Hwf Hstack _ runtime formals
      binders atoms Hfootprint final_mask carried final Hcont.
    iIntros "[#Hworld [Hpre Hrest]]". iDestruct "Hpre" as (value) "Hbody".
    iApply (Hinner Hcost Hwf Hstack inner_aligned
      runtime formals (Runtime.Translation.binder_cons value binders) atoms
      Hfootprint final_mask carried final).
    - iIntros "[#Hworld' [Hpost Hcarried]]".
      iApply Hcont. iFrame "Hworld' Hcarried".
      rewrite Validity.VSemantics.S.interp_weaken_assertion. iExact "Hpost".
    - iFrame "Hworld Hbody Hrest".
  Qed.

  Lemma aligned_certificate_seam_exists_preserve
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {t fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (body post : Runtime.Translation.Assertions.assertion Γ F (t :: Δ))
      (derivation : Validity.Certified.Rules.RavenHoareTriple body statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post)
      (inner_aligned : Validity.Certified.certificate_hoare_aligned cost
        certificate derivation)
      {stack_in mid_stack}
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in
        mid_stack)
      {final_exit}
      (rest_source : RuntimeAdapter.certificate_suffix cost Γ exit final_exit)
      (ambient : coPset) :
    aligned_certificate_seam_refinement
      (F := F) (Δ := t :: Δ) (pre := body) (post := post)
      certificate derivation stack_in mid_stack lifo rest_source ambient ->
    aligned_certificate_seam_refinement
      (F := F) (Δ := Δ)
      (pre := Runtime.Translation.Assertions.AExists t body)
      (post := Runtime.Translation.Assertions.AExists t post) certificate
      (Validity.Certified.Rules.ExistsPreserveRule t body post statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) derivation)
      stack_in mid_stack lifo rest_source ambient.
  Proof.
    intros Hinner Hcost Hwf Hstack _ runtime formals
      binders atoms Hfootprint final_mask carried final Hcont.
    iIntros "[#Hworld [Hpre Hrest]]". iDestruct "Hpre" as (value) "Hbody".
    iApply (Hinner Hcost Hwf Hstack inner_aligned
      runtime formals (Runtime.Translation.binder_cons value binders) atoms
      Hfootprint final_mask carried final).
    - iIntros "[#Hworld' [Hpost Hcarried]]".
      iApply Hcont. iFrame "Hworld' Hcarried". iExists value. iExact "Hpost".
    - iFrame "Hworld Hbody Hrest".
  Qed.

  (** Seam analogue of [aligned_conditional_core_obligation]: recurses in
      lockstep with [aligned]'s own wrapper spine, returning at the
      [AlignedConditional] leaf the seam-CPS leaf obligation *specialized to
      the one concrete LIFO transition [stack_in]/[mid_stack]/[lifo]
      already in hand* (per the correction below), for a fixed
      [rest_source]/[ambient] threaded unchanged through every case.  Unlike
      [aligned_conditional_seam_obligation] (the purely structural
      recognizer), this does carry content -- but only content already
      abstracted away from [rest_suffix]/[branch_suffix]/[runtime] by
      [aligned_certificate_seam_refinement] itself, so [rest_source]/
      [ambient] thread through [AlignedExistsElim]/[AlignedExistsPreserve]'s
      context shift exactly as trivially as they do through
      [AlignedFrame]/[AlignedConsequence], since neither value depends on
      [Γ]/[F]/[Δ] (nor, for [rest_source], on [Δ] specifically -- it is
      indexed only by [exit], which every one of these four wrappers
      preserves).

      Built via [induction aligned] in tactic mode (yielding a transparent,
      [Defined] term, still usable by [simpl] downstream) rather than a
      term-mode [Fixpoint]/[match]: [stack_in]/[mid_stack]/[lifo] are curried
      into the *return type*, and a term-mode [match] returning a type that
      mentions [lifo_certificate certificate ...] does not, by itself,
      refine [lifo] to match a branch's own (dependently different, though
      identical per [typed_runtime.v:280-327]) certificate -- neither a bare
      motive naming just [certificate] nor a hand-written
      [in ... return ...] clause (this instantiated inductive's actual index
      arity did not match what its `typed_runtime.v` source declaration
      suggested) reproduces the needed refinement.  [induction]'s own
      dependent generalization handles it automatically instead (the same
      mechanism [aligned_conditional_wrapper_seam_runtime_refinement] below
      relies on for the identical reason).  One further wrinkle: unlike
      [certificate] (whose refinement the goal exposes via [lifo]'s own
      type), [derivation] is invisible to the goal (no hypothesis mentions
      it after [induction aligned]'s automatic generalization + case split,
      since [lifo_certificate] doesn't depend on it), so the
      [AlignedConditional] case reconstructs both explicitly --
      [RuntimeAdapter.Atomicity.CertConditional ...]/[hoare_mask_transport
      (Rules.ConditionalRule ...) ...] -- mirroring
      [aligned_conditional_core_from_ordinary_branch_traces]'s own
      reconstruction of the same terms. *)
  Definition aligned_conditional_seam_core_obligation
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit}
      {pre post : Runtime.Translation.Assertions.assertion Γ F Δ}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post}
      (aligned : Validity.Certified.certificate_hoare_aligned cost certificate
        derivation) :
      forall (stack_in mid_stack : list RuntimeAdapter.Atomicity.access_marker),
      RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in mid_stack ->
      forall {final_exit : RuntimeAdapter.Atomicity.analysis_state},
      RuntimeAdapter.certificate_suffix cost Γ exit final_exit -> coPset ->
      Prop.
  Proof.
    induction aligned; intros stack_in mid_stack lifo final_exit rest_source
      ambient.
    - exact False. (* AlignedOrdinaryLeaf *)
    - exact False. (* AlignedUnfold *)
    - exact False. (* AlignedFold *)
    - exact False. (* AlignedSequence *)
    - exact (aligned_certificate_seam_refinement
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state
          (Runtime.IR.TIf node condition then_branch else_branch) then_branch
          else_branch then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal)
        (Validity.Certified.hoare_mask_transport
          (Validity.Certified.Rules.ConditionalRule node store frame condition
            then_branch else_branch post
            (RuntimeAdapter.Atomicity.analysis_mask state) branch_mask
            then_derivation
            else_derivation) eq_refl
          (Validity.Certified.conditional_analysis_mask state then_exit
            else_exit branch_mask then_mask else_mask))
        stack_in mid_stack lifo rest_source ambient). (* AlignedConditional *)
    - exact False. (* AlignedAtomic *)
    - exact (IHaligned stack_in mid_stack lifo final_exit rest_source
        ambient). (* AlignedFrame *)
    - exact (IHaligned stack_in mid_stack lifo final_exit rest_source
        ambient). (* AlignedConsequence *)
    - exact (IHaligned stack_in mid_stack lifo final_exit rest_source
        ambient). (* AlignedExistsElim *)
    - exact (IHaligned stack_in mid_stack lifo final_exit rest_source
        ambient). (* AlignedExistsPreserve *)
  Defined.

  (** Seam analogue of [aligned_conditional_wrapper_translated_runtime_refinement]:
      propagates the leaf seam obligation up through [AlignedFrame]/
      [AlignedConsequence]/[AlignedExistsElim]/[AlignedExistsPreserve] using
      the transports proved just above, for the caller-supplied, fixed
      [rest_source]/[ambient].  [induction aligned] performs all the
      dependent generalization over [Γ]/[F]/[Δ]/[certificate]/[derivation]
      needed for the [ExistsElim]/[ExistsPreserve] cases automatically; no
      induction hypothesis is needed at the [AlignedConditional] case itself
      ([Hcore] already supplies exactly that leaf's obligation, ignoring the
      constructor's own nested [then_aligned]/[else_aligned] sub-proofs,
      which are irrelevant here -- they are consumed separately, by whoever
      builds [Hcore] in the first place (see
      [aligned_conditional_seam_core_from_branch_traces] below). *)
  Theorem aligned_conditional_wrapper_seam_runtime_refinement
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit pre post}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post}
      (aligned : Validity.Certified.certificate_hoare_aligned cost certificate
        derivation)
      {stack_in mid_stack : list RuntimeAdapter.Atomicity.access_marker}
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in
        mid_stack)
      {final_exit : RuntimeAdapter.Atomicity.analysis_state}
      (rest_source : RuntimeAdapter.certificate_suffix cost Γ exit final_exit)
      (ambient : coPset) :
    aligned_conditional_seam_core_obligation aligned stack_in mid_stack lifo
      rest_source ambient ->
    aligned_certificate_seam_refinement
      (F := F) (Δ := Δ) (pre := pre) (post := post)
      certificate derivation stack_in mid_stack lifo rest_source ambient.
  Proof.
    revert stack_in mid_stack lifo final_exit rest_source ambient.
    induction aligned; simpl; intros stack_in mid_stack lifo final_exit
      rest_source ambient Hcore; try contradiction.
    - exact Hcore.
    - eapply aligned_certificate_seam_frame; eauto.
    - eapply aligned_certificate_seam_consequence; eauto.
    - eapply aligned_certificate_seam_exists_elim; eauto.
    - eapply aligned_certificate_seam_exists_preserve; eauto.
  Qed.

  (** The [AlignedConditional]-leaf recipe: builds the seam-CPS leaf
      obligation from the two branches' own alignment/stack evidence and one
      shared, [linear_focused_close]-restricted closing witness for
      [rest_suffix]. Moved to just after [linear_ordinary_close_source_
      refinement_complete] (see [aligned_conditional_seam_core_from_
      branch_traces] there): it needs [linear_focused_close] and everything
      built on it, all defined later in this file. *)

  Record aligned_sequence_decomposition
      {cost Γ F Δ fuel entry first middle second next pre post}
      (first_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel entry first middle)
      (second_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel middle second next) : Type := {
    sequence_middle_assertion : Runtime.Translation.Assertions.assertion Γ F Δ;
    sequence_first_derivation :
      Validity.Certified.Rules.RavenHoareTriple pre first
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask middle)
        sequence_middle_assertion;
    sequence_second_derivation :
      Validity.Certified.Rules.RavenHoareTriple sequence_middle_assertion second
        (RuntimeAdapter.Atomicity.analysis_mask middle)
        (RuntimeAdapter.Atomicity.analysis_mask next) post;
    sequence_first_aligned : Validity.Certified.certificate_hoare_aligned cost
      first_certificate sequence_first_derivation;
    sequence_second_aligned : Validity.Certified.certificate_hoare_aligned cost
      second_certificate sequence_second_derivation;
  }.

  Definition aligned_sequence_decomposition_target
      {cost Γ fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit) :
      forall F Δ pre post,
        Validity.Certified.Rules.RavenHoareTriple pre statement
          (RuntimeAdapter.Atomicity.analysis_mask entry)
          (RuntimeAdapter.Atomicity.analysis_mask exit) post -> Type :=
    match certificate as certificate' in
        RuntimeAdapter.Atomicity.analysis_certificate _ Γ' fuel' entry'
          statement' exit'
      return forall F' Δ' pre' post',
        Validity.Certified.Rules.RavenHoareTriple pre' statement'
          (RuntimeAdapter.Atomicity.analysis_mask entry')
          (RuntimeAdapter.Atomicity.analysis_mask exit') post' -> Type
    with
    | @RuntimeAdapter.Atomicity.CertSequence _ Γ' fuel' entry' statement'
        first middle second next view first_certificate second_certificate =>
        fun F' Δ' pre' post' _ =>
          @aligned_sequence_decomposition cost Γ' F' Δ' fuel' entry'
            first middle second next pre' post' first_certificate
            second_certificate
    | _ => fun _ _ _ _ _ => unit
    end.

  Fixpoint aligned_sequence_decompose_fix
      {cost Γ F Δ fuel entry statement exit pre post}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post}
      (Haligned : Validity.Certified.certificate_hoare_aligned cost certificate
        derivation) {struct Haligned} :
    aligned_sequence_decomposition_target certificate F Δ pre post derivation.
  Proof.
    destruct Haligned; simpl; try exact tt.
    - unshelve econstructor.
      + exact middle_assertion.
      + exact first_derivation.
      + exact second_derivation.
      + exact Haligned1.
      + exact Haligned2.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@aligned_sequence_decompose_fix cost Γ F Δ (S fuel) state
        statement exit pre post
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel state statement
          first middle second exit e certificate1 certificate2)
        derivation Haligned) as
        [mid Hfirst Hsecond HAfirst HAsecond].
      unshelve econstructor.
      + exact (Runtime.Translation.Assertions.AAnd mid frame).
      + exact (Validity.Certified.Rules.FrameRule _ _ frame _ _ _ Hfirst).
      + exact (Validity.Certified.Rules.FrameRule _ _ frame _ _ _ Hsecond).
      + eapply Validity.Certified.AlignedFrame. exact HAfirst.
      + eapply Validity.Certified.AlignedFrame. exact HAsecond.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@aligned_sequence_decompose_fix cost Γ F Δ (S fuel) state
        statement exit pre post
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel state statement
          first middle second exit e certificate1 certificate2)
        derivation Haligned) as
        [mid Hfirst Hsecond HAfirst HAsecond].
      unshelve econstructor.
      + exact mid.
      + eapply Validity.Certified.Rules.ConsequenceRule.
        * exact Hfirst.
        * exact pre_entails.
        * apply Runtime.Validation.Hoare.EntailsRefl.
      + eapply Validity.Certified.Rules.ConsequenceRule.
        * exact Hsecond.
        * apply Runtime.Validation.Hoare.EntailsRefl.
        * exact post_entails.
      + eapply Validity.Certified.AlignedConsequence. exact HAfirst.
      + eapply Validity.Certified.AlignedConsequence. exact HAsecond.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@aligned_sequence_decompose_fix cost Γ F (t :: Δ) (S fuel)
        state statement exit body
        (Runtime.Translation.Assertions.weaken_assertion post)
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel state statement
          first middle second exit e certificate1 certificate2)
        derivation Haligned) as
        [mid Hfirst Hsecond HAfirst HAsecond].
      unshelve econstructor.
      + exact (Runtime.Translation.Assertions.AExists t mid).
      + exact (Validity.Certified.Rules.ExistsPreserveRule _ _ _ _ _ _ Hfirst).
      + exact (Validity.Certified.Rules.ExistsElimRule _ _ _ _ _ _ Hsecond).
      + eapply Validity.Certified.AlignedExistsPreserve. exact HAfirst.
      + eapply Validity.Certified.AlignedExistsElim. exact HAsecond.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@aligned_sequence_decompose_fix cost Γ F (t :: Δ) (S fuel)
        state statement exit body post
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel state statement
          first middle second exit e certificate1 certificate2)
        derivation Haligned) as
        [mid Hfirst Hsecond HAfirst HAsecond].
      unshelve econstructor.
      + exact (Runtime.Translation.Assertions.AExists t mid).
      + exact (Validity.Certified.Rules.ExistsPreserveRule _ _ _ _ _ _ Hfirst).
      + exact (Validity.Certified.Rules.ExistsPreserveRule _ _ _ _ _ _ Hsecond).
      + eapply Validity.Certified.AlignedExistsPreserve. exact HAfirst.
      + eapply Validity.Certified.AlignedExistsPreserve. exact HAsecond.
  Defined.

  Record resource_aligned_sequence_decomposition
      {cost Γ F Δ fuel entry first middle second next pre post}
      (first_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel entry first middle)
      (second_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel middle second next) : Type := {
    resource_sequence_middle_assertion : Runtime.Translation.Assertions.assertion Γ F Δ;
    resource_sequence_first_derivation :
      Validity.Certified.Rules.RavenResourceTriple pre first
        resource_sequence_middle_assertion;
    resource_sequence_second_derivation :
      Validity.Certified.Rules.RavenResourceTriple resource_sequence_middle_assertion second post;
    resource_sequence_first_aligned : Validity.Certified.resource_certificate_hoare_aligned cost
      first_certificate resource_sequence_first_derivation;
    resource_sequence_second_aligned : Validity.Certified.resource_certificate_hoare_aligned cost
      second_certificate resource_sequence_second_derivation;
  }.

  Definition resource_aligned_sequence_decomposition_target
      {cost Γ fuel entry statement exit}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit) :
      forall F Δ pre post,
        Validity.Certified.Rules.RavenResourceTriple pre statement post -> Type :=
    match certificate as certificate' in
        RuntimeAdapter.Atomicity.analysis_certificate _ Γ' fuel' entry'
          statement' exit'
      return forall F' Δ' pre' post',
        Validity.Certified.Rules.RavenResourceTriple pre' statement' post' -> Type
    with
    | @RuntimeAdapter.Atomicity.CertSequence _ Γ' fuel' entry' statement'
        first middle second next view first_certificate second_certificate =>
        fun F' Δ' pre' post' _ =>
          @resource_aligned_sequence_decomposition cost Γ' F' Δ' fuel' entry'
            first middle second next pre' post' first_certificate
            second_certificate
    | _ => fun _ _ _ _ _ => unit
    end.

  Fixpoint resource_aligned_sequence_decompose_fix
      {cost Γ F Δ fuel entry statement exit pre post}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenResourceTriple pre statement post}
      (Haligned : Validity.Certified.resource_certificate_hoare_aligned cost certificate
        derivation) {struct Haligned} :
    resource_aligned_sequence_decomposition_target certificate F Δ pre post derivation.
  Proof.
    destruct Haligned; simpl; try exact tt.
    - unshelve econstructor.
      + exact middle_assertion.
      + exact first_derivation.
      + exact second_derivation.
      + exact Haligned1.
      + exact Haligned2.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@resource_aligned_sequence_decompose_fix cost Γ F Δ (S fuel) state
        statement exit pre post
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel state statement
          first middle second exit e certificate1 certificate2)
        derivation Haligned) as
        [mid Hfirst Hsecond HAfirst HAsecond].
      unshelve econstructor.
      + exact (Runtime.Translation.Assertions.AAnd mid frame).
      + exact (Validity.Certified.Rules.ResourceFrameRule _ _ frame _ Hfirst).
      + exact (Validity.Certified.Rules.ResourceFrameRule _ _ frame _ Hsecond).
      + eapply Validity.Certified.ResourceAlignedFrame. exact HAfirst.
      + eapply Validity.Certified.ResourceAlignedFrame. exact HAsecond.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@resource_aligned_sequence_decompose_fix cost Γ F Δ (S fuel) state
        statement exit pre post
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel state statement
          first middle second exit e certificate1 certificate2)
        derivation Haligned) as
        [mid Hfirst Hsecond HAfirst HAsecond].
      unshelve econstructor.
      + exact mid.
      + eapply Validity.Certified.Rules.ResourceConsequenceRule.
        * exact Hfirst.
        * exact pre_entails.
        * apply Runtime.Validation.Hoare.EntailsRefl.
      + eapply Validity.Certified.Rules.ResourceConsequenceRule.
        * exact Hsecond.
        * apply Runtime.Validation.Hoare.EntailsRefl.
        * exact post_entails.
      + eapply Validity.Certified.ResourceAlignedConsequence. exact HAfirst.
      + eapply Validity.Certified.ResourceAlignedConsequence. exact HAsecond.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@resource_aligned_sequence_decompose_fix cost Γ F (t :: Δ) (S fuel)
        state statement exit body
        (Runtime.Translation.Assertions.weaken_assertion post)
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel state statement
          first middle second exit e certificate1 certificate2)
        derivation Haligned) as
        [mid Hfirst Hsecond HAfirst HAsecond].
      unshelve econstructor.
      + exact (Runtime.Translation.Assertions.AExists t mid).
      + exact (Validity.Certified.Rules.ResourceExistsPreserveRule _ _ _ _ Hfirst).
      + exact (Validity.Certified.Rules.ResourceExistsElimRule _ _ _ _ Hsecond).
      + eapply Validity.Certified.ResourceAlignedExistsPreserve. exact HAfirst.
      + eapply Validity.Certified.ResourceAlignedExistsElim. exact HAsecond.
    - dependent destruction certificate; simpl; try exact tt.
      destruct (@resource_aligned_sequence_decompose_fix cost Γ F (t :: Δ) (S fuel)
        state statement exit body post
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel state statement
          first middle second exit e certificate1 certificate2)
        derivation Haligned) as
        [mid Hfirst Hsecond HAfirst HAsecond].
      unshelve econstructor.
      + exact (Runtime.Translation.Assertions.AExists t mid).
      + exact (Validity.Certified.Rules.ResourceExistsPreserveRule _ _ _ _ Hfirst).
      + exact (Validity.Certified.Rules.ResourceExistsPreserveRule _ _ _ _ Hsecond).
      + eapply Validity.Certified.ResourceAlignedExistsPreserve. exact HAfirst.
      + eapply Validity.Certified.ResourceAlignedExistsPreserve. exact HAsecond.
  Defined.

  Definition normalize_resource_aligned_conditional
      {cost Γ F Δ fuel entry statement then_statement else_statement
        then_exit else_exit exit pre join_assertion post stack_in join_stack
        stack_out view then_certificate else_certificate open_equal atomic_equal
        derivation aligned lifo rest then_tree else_tree}
      (Hthen : RuntimeAdapter.net_trace cost Γ entry then_exit None stack_in
        join_stack (RuntimeAdapter.singleton_suffix then_certificate) then_tree)
      (Helse : RuntimeAdapter.net_trace cost Γ entry else_exit None stack_in
        join_stack (RuntimeAdapter.singleton_suffix else_certificate) else_tree)
      (branch_data : @resource_conditional_branch_data cost Γ F Δ fuel entry
        statement then_statement else_statement then_exit else_exit pre
        join_assertion view then_certificate else_certificate open_equal
        atomic_equal derivation aligned stack_in join_stack None stack_in
        then_tree else_tree lifo Hthen Helse)
      (normal_rest : has_resource_aligned_ordinary_normalization rest) :
    has_resource_aligned_ordinary_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ (S fuel) entry
        statement (RuntimeAdapter.conditional_join then_exit else_exit) pre
        join_assertion stack_in join_stack
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
          then_statement else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal)
        derivation aligned lifo exit post stack_out rest).
  Proof.
    destruct normal_rest as [rest_tree [Hrest aligned_rest]].
    eexists (@RuntimeAdapter.NetConditional stack_in join_stack stack_out entry
      then_exit else_exit (RuntimeAdapter.conditional_join then_exit else_exit)
      exit
      (RuntimeAdapter.Payload.RavenConditional Γ fuel cost entry statement
        then_statement else_statement then_exit else_exit view then_certificate
        else_certificate open_equal atomic_equal) then_tree else_tree rest_tree).
    eexists (@RuntimeAdapter.TraceConditional cost Γ fuel entry statement
      then_statement else_statement then_exit else_exit exit stack_in join_stack
      stack_out view then_certificate else_certificate open_equal atomic_equal
      (resource_certificate_suffix_of_operational_suffix rest)
      then_tree else_tree rest_tree Hthen Helse Hrest).
    constructor; [exact branch_data | exact aligned_rest].
  Defined.

  Definition normalize_resource_aligned_focused_conditional
      {cost Γ F Δ fuel entry statement then_statement else_statement
        then_exit else_exit exit pre join_assertion post focused tail join_stack
        stack_out view then_certificate else_certificate open_equal atomic_equal
        derivation aligned lifo rest then_tree else_tree}
      (Hthen : RuntimeAdapter.net_trace cost Γ entry then_exit (Some focused)
        tail join_stack (RuntimeAdapter.singleton_suffix then_certificate)
        then_tree)
      (Helse : RuntimeAdapter.net_trace cost Γ entry else_exit (Some focused)
        tail join_stack (RuntimeAdapter.singleton_suffix else_certificate)
        else_tree)
      (branch_data : @resource_conditional_branch_data cost Γ F Δ fuel entry
        statement then_statement else_statement then_exit else_exit pre
        join_assertion view then_certificate else_certificate open_equal
        atomic_equal derivation aligned (focused :: tail) join_stack
        (Some focused) tail then_tree else_tree lifo Hthen Helse)
      (normal_rest : has_resource_aligned_ordinary_normalization rest) :
    has_resource_aligned_focused_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ (S fuel) entry
        statement (RuntimeAdapter.conditional_join then_exit else_exit) pre
        join_assertion (focused :: tail) join_stack
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
          then_statement else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal)
        derivation aligned lifo exit post stack_out rest).
  Proof.
    destruct normal_rest as [rest_tree [Hrest aligned_rest]].
    eexists (@RuntimeAdapter.FocusNetConditional focused tail join_stack stack_out
      entry then_exit else_exit (RuntimeAdapter.conditional_join then_exit else_exit)
      exit
      (RuntimeAdapter.Payload.RavenConditional Γ fuel cost entry statement
        then_statement else_statement then_exit else_exit view then_certificate
        else_certificate open_equal atomic_equal) then_tree else_tree rest_tree).
    eexists (@RuntimeAdapter.TraceFocusedConditional cost Γ fuel entry
      statement then_statement else_statement then_exit else_exit exit focused
      tail join_stack stack_out view then_certificate else_certificate open_equal
      atomic_equal (resource_certificate_suffix_of_operational_suffix rest)
      then_tree else_tree rest_tree Hthen Helse Hrest).
    constructor; [exact branch_data | exact aligned_rest].
  Defined.

  Definition normalize_resource_aligned_sequence_expansion
      {cost Γ F Δ fuel entry statement first middle second next exit pre}
      {middle_assertion next_assertion post :
        Runtime.Translation.Assertions.assertion Γ F Δ}
      {stack_in stack_middle stack_next stack_out :
        list RuntimeAdapter.Atomicity.access_marker}
      {view first_certificate second_certificate}
      {first_derivation : Validity.Certified.Rules.RavenResourceTriple pre first middle_assertion}
      {second_derivation : Validity.Certified.Rules.RavenResourceTriple
        middle_assertion second next_assertion}
      {first_aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        first_certificate first_derivation}
      {second_aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        second_certificate second_derivation}
      {head_derivation : Validity.Certified.Rules.RavenResourceTriple pre statement next_assertion}
      {head_aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate) head_derivation}
      {head_lifo}
      {first_lifo : RuntimeAdapter.Atomicity.lifo_certificate first_certificate
        stack_in stack_middle}
      {second_lifo : RuntimeAdapter.Atomicity.lifo_certificate second_certificate
        stack_middle stack_next}
      {rest}
      (normal_flat : has_resource_aligned_ordinary_normalization
        (Validity.expand_resource_aligned_sequence_suffix view first_certificate
          second_certificate first_derivation second_derivation first_aligned
          second_aligned first_lifo second_lifo rest)) :
    has_resource_aligned_ordinary_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ (S fuel) entry
        statement next pre next_assertion stack_in
        stack_next
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate)
        head_derivation head_aligned head_lifo exit post stack_out rest).
  Proof.
    destruct normal_flat as [tree [Hflat aligned_flat]].
    eexists tree.
    eexists (@RuntimeAdapter.TraceExpansion cost Γ entry exit None stack_in
      stack_out
      (RuntimeAdapter.SuffixCons first_certificate
        (RuntimeAdapter.SuffixCons second_certificate
          (resource_certificate_suffix_of_operational_suffix
            rest)))
      (RuntimeAdapter.SuffixCons
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate)
        (resource_certificate_suffix_of_operational_suffix
          rest)) tree
      (@RuntimeAdapter.ExpandsSequence cost Γ fuel entry
        statement first middle second next exit view
        first_certificate second_certificate
        (resource_certificate_suffix_of_operational_suffix
          rest)) Hflat).
    eapply ResourceAlignedTraceSequenceExpansion. exact aligned_flat.
  Defined.


  Definition normalize_resource_aligned_focused_sequence_expansion
      {cost Γ F Δ fuel entry statement first middle second next exit pre}
      {middle_assertion next_assertion post :
        Runtime.Translation.Assertions.assertion Γ F Δ}
      {focused : RuntimeAdapter.Atomicity.access_marker}
      {tail stack_middle stack_next stack_out :
        list RuntimeAdapter.Atomicity.access_marker}
      {view first_certificate second_certificate}
      {first_derivation : Validity.Certified.Rules.RavenResourceTriple pre first middle_assertion}
      {second_derivation : Validity.Certified.Rules.RavenResourceTriple
        middle_assertion second next_assertion}
      {first_aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        first_certificate first_derivation}
      {second_aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        second_certificate second_derivation}
      {head_derivation : Validity.Certified.Rules.RavenResourceTriple pre statement next_assertion}
      {head_aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate) head_derivation}
      {head_lifo}
      {first_lifo : RuntimeAdapter.Atomicity.lifo_certificate first_certificate
        (focused :: tail) stack_middle}
      {second_lifo : RuntimeAdapter.Atomicity.lifo_certificate second_certificate
        stack_middle stack_next}
      {rest}
      (normal_flat : has_resource_aligned_focused_normalization
        (Validity.expand_resource_aligned_sequence_suffix view first_certificate
          second_certificate first_derivation second_derivation first_aligned
          second_aligned first_lifo second_lifo rest)) :
    has_resource_aligned_focused_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ (S fuel) entry
        statement next pre next_assertion
        (focused :: tail) stack_next
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate)
        head_derivation head_aligned head_lifo exit post stack_out rest).
  Proof.
    destruct normal_flat as [tree [Hflat aligned_flat]].
    eexists tree.
    eexists (@RuntimeAdapter.TraceExpansion cost Γ entry exit (Some focused)
      tail stack_out
      (RuntimeAdapter.SuffixCons first_certificate
        (RuntimeAdapter.SuffixCons second_certificate
          (resource_certificate_suffix_of_operational_suffix
            rest)))
      (RuntimeAdapter.SuffixCons
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate)
        (resource_certificate_suffix_of_operational_suffix
          rest)) tree
      (@RuntimeAdapter.ExpandsSequence cost Γ fuel entry
        statement first middle second next exit view
        first_certificate second_certificate
        (resource_certificate_suffix_of_operational_suffix
          rest)) Hflat).
    eapply ResourceAlignedTraceSequenceExpansion. exact aligned_flat.
  Defined.

  Definition resource_total_leaf_head
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        stack_in stack_middle stack_out view step derivation aligned lifo rest}
      (total_rest : has_resource_aligned_total_normalization rest) :
    has_resource_aligned_total_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ (S fuel) entry
        statement middle pre middle_assertion stack_in stack_middle
        (RuntimeAdapter.Atomicity.CertLeaf cost Γ fuel entry statement middle
          view step) derivation aligned lifo exit post stack_out rest).
  Proof.
    simpl in lifo. subst stack_middle.
    destruct total_rest as [Hordinary Hfocused].
    constructor.
    - eapply normalize_resource_aligned_ordinary_chunk.
      + apply RuntimeAdapter.ChunkCertificateLeaf.
      + exact Hordinary.
    - destruct stack_in as [|focused tail]; simpl in Hfocused |- *.
      + exact tt.
      + eapply normalize_resource_aligned_focused_prefix.
        * apply RuntimeAdapter.ChunkCertificateLeaf.
        * exact I.
        * exact Hfocused.
  Defined.

  Definition resource_total_atomic_head
      {cost Γ F Δ fuel entry statement body outer inner exit pre
        middle_assertion post stack_in stack_middle stack_out view step
        body_certificate open_equal derivation aligned lifo rest}
      (total_rest : has_resource_aligned_total_normalization rest) :
    has_resource_aligned_total_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ (S fuel) entry
        statement
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask inner)
          (RuntimeAdapter.Atomicity.analysis_open inner)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer ||
            RuntimeAdapter.Atomicity.analysis_step_taken inner)
          (RuntimeAdapter.Atomicity.analysis_in_atomic outer))
        pre middle_assertion stack_in stack_middle
        (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel entry statement body
          outer inner view step body_certificate open_equal)
        derivation aligned lifo exit post stack_out rest).
  Proof.
    simpl in lifo. pose proof (proj2 lifo) as Heq. subst stack_middle.
    destruct total_rest as [Hordinary Hfocused].
    constructor.
    - eapply normalize_resource_aligned_ordinary_chunk.
      + apply RuntimeAdapter.ChunkCertificateAtomic.
      + exact Hordinary.
    - destruct stack_in as [|focused tail]; simpl in Hfocused |- *.
      + exact tt.
      + eapply normalize_resource_aligned_focused_prefix.
        * apply RuntimeAdapter.ChunkCertificateAtomic.
        * exact I.
        * exact Hfocused.
  Defined.

  Definition resource_total_unfold_head
      {cost Γ F Δ fuel entry statement invariant opened exit pre
        opened_assertion post stack_in stack_opened stack_out view step
        derivation aligned lifo rest}
      (total_rest : has_resource_aligned_total_normalization rest) :
    has_resource_aligned_total_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ (S fuel) entry
        statement opened pre opened_assertion stack_in stack_opened
        (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry statement
          invariant opened view step) derivation aligned lifo exit post
        stack_out rest).
  Proof.
    simpl in lifo. subst stack_opened.
    destruct total_rest as [Hordinary Hfocused]. simpl in Hfocused.
    constructor.
    - eapply normalize_resource_aligned_access.
      + eapply RuntimeAdapter.ChunkCertificateUnfold.
      + exact I.
      + exact Hfocused.
    - destruct stack_in as [|focused tail]; simpl.
      + exact tt.
      + eapply normalize_resource_aligned_nested_access.
        * eapply RuntimeAdapter.ChunkCertificateUnfold.
        * exact I.
        * exact Hfocused.
  Defined.

  Definition resource_total_fold_head
      {cost Γ F Δ fuel entry statement invariant exit pre middle_assertion post
        stack_in stack_middle stack_out view derivation aligned lifo rest}
      (total_rest : has_resource_aligned_total_normalization rest) :
    has_resource_aligned_total_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ (S fuel) entry
        statement (RuntimeAdapter.Atomicity.fold_invariant invariant entry) pre
        middle_assertion stack_in stack_middle
        (RuntimeAdapter.Atomicity.CertFold cost Γ fuel entry statement invariant
          view) derivation aligned lifo exit post stack_out rest).
  Proof.
    destruct (decide (invariant ∈
      RuntimeAdapter.Atomicity.analysis_open entry)) as [Hopen | Hfresh].
    - destruct stack_in as [|[head outer] tail].
      + exact (False_rect _ (fold_lifo_matched_nonempty lifo Hopen)).
      + pose proof (fold_lifo_matched_facts lifo Hopen) as Hfacts.
        pose proof (proj1 Hfacts) as Hhead.
        pose proof (proj1 (proj2 Hfacts)) as Htail.
        subst head. subst stack_middle.
        destruct total_rest as [Hordinary Hfocused].
        constructor.
        * eapply normalize_resource_aligned_ordinary_close.
          -- eapply RuntimeAdapter.ChunkCertificateFold.
          -- exact I.
          -- exact Hordinary.
        * simpl. eapply normalize_resource_aligned_close.
          -- eapply RuntimeAdapter.ChunkCertificateFold.
          -- exact I.
          -- exact Hordinary.
    - pose proof (fold_lifo_fresh_stack lifo Hfresh) as Heq.
      subst stack_middle.
      destruct total_rest as [Hordinary Hfocused].
      constructor.
      + eapply normalize_resource_aligned_ordinary_chunk.
        * eapply RuntimeAdapter.ChunkCertificateFreshFold.
        * exact Hordinary.
      + destruct stack_in as [|focused tail]; simpl in Hfocused |- *.
        * exact tt.
        * eapply normalize_resource_aligned_focused_prefix.
          -- eapply RuntimeAdapter.ChunkCertificateFreshFold.
          -- exact I.
          -- exact Hfocused.
    Unshelve. all: intuition.
  Defined.

  Definition resource_total_sequence_head
      {cost Γ F Δ fuel entry statement first middle second next exit pre}
      {next_assertion post : Runtime.Translation.Assertions.assertion Γ F Δ}
      {stack_in stack_next stack_out : list RuntimeAdapter.Atomicity.access_marker}
      {view first_certificate second_certificate}
      {head_derivation : Validity.Certified.Rules.RavenResourceTriple pre
        statement next_assertion}
      {head_aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry statement first
          middle second next view first_certificate second_certificate)
        head_derivation}
      {head_lifo : RuntimeAdapter.Atomicity.lifo_certificate
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry statement first
          middle second next view first_certificate second_certificate)
        stack_in stack_next}
      {rest}
      (normal_flat :
        let decomposition := resource_aligned_sequence_decompose_fix head_aligned in
        let split := choose_sequence_lifo_middle head_lifo in
        has_resource_aligned_total_normalization
          (Validity.expand_resource_aligned_sequence_suffix view first_certificate
            second_certificate
            (resource_sequence_first_derivation first_certificate second_certificate
              decomposition)
            (resource_sequence_second_derivation first_certificate second_certificate
              decomposition)
            (resource_sequence_first_aligned first_certificate second_certificate
              decomposition)
            (resource_sequence_second_aligned first_certificate second_certificate
              decomposition)
            (proj1 (proj2_sig split)) (proj2 (proj2_sig split)) rest)) :
    has_resource_aligned_total_normalization
      (@Validity.ResourceAlignedOperationalCons cost Γ F Δ (S fuel) entry
        statement next pre next_assertion stack_in stack_next
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry statement first
          middle second next view first_certificate second_certificate)
        head_derivation head_aligned head_lifo exit post stack_out rest).
  Proof.
    destruct (resource_aligned_sequence_decompose_fix head_aligned) as
      [middle_assertion first_derivation second_derivation first_aligned
        second_aligned].
    destruct (choose_sequence_lifo_middle head_lifo) as [stack_middle split].
    pose proof (proj1 split) as first_lifo.
    pose proof (proj2 split) as second_lifo.
    simpl in normal_flat.
    destruct normal_flat as [Hordinary Hfocused].
    constructor.
    - eapply normalize_resource_aligned_sequence_expansion. exact Hordinary.
    - destruct stack_in as [|focused tail]; simpl in Hfocused |- *.
      + exact tt.
      + eapply normalize_resource_aligned_focused_sequence_expansion.
        exact Hfocused.
  Defined.

  Definition aligned_total_sequence_head
      {cost Γ F Δ fuel entry statement first middle second next exit pre}
      {next_assertion post : Runtime.Translation.Assertions.assertion Γ F Δ}
      {stack_in stack_next stack_out :
        list RuntimeAdapter.Atomicity.access_marker}
      {view first_certificate second_certificate}
      {head_derivation : Validity.Certified.Rules.RavenHoareTriple pre
        statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask next) next_assertion}
      {head_aligned : Validity.Certified.certificate_hoare_aligned cost
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate) head_derivation}
      {head_lifo : RuntimeAdapter.Atomicity.lifo_certificate
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate) stack_in stack_next}
      {rest}
      (normal_flat :
        let decomposition := aligned_sequence_decompose_fix head_aligned in
        let split := choose_sequence_lifo_middle head_lifo in
        has_aligned_total_normalization
          (Validity.expand_aligned_sequence_suffix view first_certificate
            second_certificate
            (sequence_first_derivation first_certificate second_certificate
              decomposition)
            (sequence_second_derivation first_certificate second_certificate
              decomposition)
            (sequence_first_aligned first_certificate second_certificate
              decomposition)
            (sequence_second_aligned first_certificate second_certificate
              decomposition)
            (proj1 (proj2_sig split)) (proj2 (proj2_sig split)) rest)) :
    has_aligned_total_normalization
      (@Validity.AlignedOperationalCons cost Γ F Δ (S fuel) entry
        statement next pre next_assertion stack_in
        stack_next
        (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
          statement first middle second next view
          first_certificate second_certificate)
        head_derivation head_aligned head_lifo exit post stack_out rest).
  Proof.
    destruct (aligned_sequence_decompose_fix head_aligned) as
      [middle_assertion first_derivation second_derivation first_aligned
        second_aligned].
    destruct (choose_sequence_lifo_middle head_lifo) as
      [stack_middle split].
    pose proof (proj1 split) as first_lifo.
    pose proof (proj2 split) as second_lifo.
    simpl in normal_flat.
    destruct normal_flat as [Hordinary Hfocused].
    constructor.
    - eapply normalize_aligned_sequence_expansion. exact Hordinary.
    - destruct stack_in as [|focused tail]; simpl in Hfocused |- *.
      + exact tt.
      + eapply normalize_aligned_focused_sequence_expansion. exact Hfocused.
  Defined.

  Theorem packed_resource_aligned_total_normalization_complete
      (cost : RuntimeAdapter.Atomicity.cost_model) Γ
      (packed : packed_resource_aligned_suffix cost Γ) :
    RuntimeAdapter.Atomicity.state_wf
      (packed_resource_entry cost Γ packed) ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open
        (packed_resource_entry cost Γ packed))
      (packed_resource_stack_in cost Γ packed) ->
    packed_has_resource_aligned_total_normalization packed.
  Proof.
    induction packed as [packed IH] using
      packed_resource_aligned_well_founded_induction.
    destruct packed as [F Δ entry pre stack_in exit post stack_out suffix].
    simpl in *. intros Hwf Hstack.
    destruct suffix.
    - constructor.
      + apply normalize_resource_aligned_done.
      + destruct stack.
        * exact tt.
        * apply normalize_resource_aligned_focused_done.
    - dependent destruction certificate.
      + apply resource_total_leaf_head.
        apply (IH (pack_resource_aligned_suffix suffix)).
        * unfold packed_resource_aligned_measure. cbn.
          unfold RuntimeAdapter.certificate_source_size.
          pose proof (Runtime.RegionSyntax.size_positive Γ statement). lia.
        * exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost state
            statement exit Hwf
            (RuntimeAdapter.Atomicity.CertLeaf cost Γ fuel state statement
              exit e e0)).
        * exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
            (RuntimeAdapter.Atomicity.CertLeaf cost Γ fuel state statement
              exit e e0) _ _ Hwf lifo Hstack).
      + apply resource_total_unfold_head.
        apply (IH (pack_resource_aligned_suffix suffix)).
        * unfold packed_resource_aligned_measure. cbn.
          unfold RuntimeAdapter.certificate_source_size.
          pose proof (Runtime.RegionSyntax.size_positive Γ statement). lia.
        * exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost state
            statement exit Hwf
            (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel state statement
              invariant exit e e0)).
        * exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
            (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel state statement
              invariant exit e e0) _ _ Hwf lifo Hstack).
      + apply resource_total_fold_head.
        apply (IH (pack_resource_aligned_suffix suffix)).
        * unfold packed_resource_aligned_measure. cbn.
          unfold RuntimeAdapter.certificate_source_size.
          pose proof (Runtime.RegionSyntax.size_positive Γ statement). lia.
        * exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost state
            statement (RuntimeAdapter.Atomicity.fold_invariant invariant state)
            Hwf (RuntimeAdapter.Atomicity.CertFold cost Γ fuel state statement
              invariant e)).
        * exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
            (RuntimeAdapter.Atomicity.CertFold cost Γ fuel state statement
              invariant e) _ _ Hwf lifo Hstack).
      + { refine (@resource_total_sequence_head cost Γ F Δ fuel state
          statement first middle second exit final pre middle_assertion post
          stack_in stack_middle stack_out e certificate1 certificate2 derivation
          aligned lifo suffix _).
        cbn.
        lazymatch goal with
        | |- has_resource_aligned_total_normalization ?flat =>
            refine (IH (pack_resource_aligned_suffix flat) _ Hwf Hstack)
        end.
        unfold packed_resource_aligned_measure. cbn.
        exact (RuntimeAdapter.expand_sequence_suffix_measure_decreases e
          certificate1 certificate2
          (resource_certificate_suffix_of_operational_suffix suffix)). }
      + destruct lifo as [Hthen Helse].
        assert (Hthen_suffix : RuntimeAdapter.suffix_lifo
          (RuntimeAdapter.singleton_suffix certificate1) stack_in stack_middle).
        { apply (proj2 (RuntimeAdapter.singleton_suffix_lifo certificate1 _ _)).
          exact Hthen. }
        assert (Helse_suffix : RuntimeAdapter.suffix_lifo
          (RuntimeAdapter.singleton_suffix certificate2) stack_in stack_middle).
        { apply (proj2 (RuntimeAdapter.singleton_suffix_lifo certificate2 _ _)).
          exact Helse. }
        assert (Hjoin_wf : RuntimeAdapter.Atomicity.state_wf
          (RuntimeAdapter.conditional_join then_exit else_exit)).
        { exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost state
            statement _ Hwf
            (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state
              statement then_branch else_branch then_exit else_exit e
              certificate1 certificate2 e0 e1)). }
        assert (Hjoin_stack : RuntimeAdapter.Atomicity.access_stack_consistent
          (RuntimeAdapter.Atomicity.analysis_open
            (RuntimeAdapter.conditional_join then_exit else_exit)) stack_middle).
        { exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
            (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state
              statement then_branch else_branch then_exit else_exit e
              certificate1 certificate2 e0 e1) _ _ Hwf
            (conj Hthen Helse) Hstack). }
        pose proof (IH (pack_resource_aligned_suffix suffix)) as Hrest_total.
        specialize (Hrest_total ltac:(
          unfold packed_resource_aligned_measure; cbn;
          unfold RuntimeAdapter.certificate_source_size;
          pose proof (Runtime.RegionSyntax.size_positive Γ statement); lia)
          Hjoin_wf Hjoin_stack).
        destruct Hrest_total as [Hordinary_rest Hfocused_rest].
        assert (build_then_ordinary :
          resource_fixed_singleton_lockstep_builder certificate1 stack_in
            stack_middle None stack_in).
        { intros F' Δ' pre' post' derivation' aligned' lifo'.
          pose proof (IH (pack_resource_aligned_suffix
            (Validity.resource_aligned_singleton_suffix certificate1
              derivation' aligned' lifo'))) as Htotal.
          specialize (Htotal ltac:(
            unfold packed_resource_aligned_measure; cbn;
            exact (RuntimeAdapter.conditional_then_measure_decreases e
              certificate1 certificate2 e0 e1
              (resource_certificate_suffix_of_operational_suffix suffix)))
            Hwf Hstack).
          exact (resource_total_ordinary _ Htotal). }
        assert (build_else_ordinary :
          resource_fixed_singleton_lockstep_builder certificate2 stack_in
            stack_middle None stack_in).
        { intros F' Δ' pre' post' derivation' aligned' lifo'.
          pose proof (IH (pack_resource_aligned_suffix
            (Validity.resource_aligned_singleton_suffix certificate2
              derivation' aligned' lifo'))) as Htotal.
          specialize (Htotal ltac:(
            unfold packed_resource_aligned_measure; cbn;
            exact (RuntimeAdapter.conditional_else_measure_decreases e
              certificate1 certificate2 e0 e1
              (resource_certificate_suffix_of_operational_suffix suffix)))
            Hwf Hstack).
          exact (resource_total_ordinary _ Htotal). }
        destruct (@resource_aligned_conditional_branch_data_fix cost Γ F Δ
          (S fuel) state statement
          (RuntimeAdapter.conditional_join then_exit else_exit) pre
          middle_assertion
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state statement
            then_branch else_branch then_exit else_exit e certificate1
            certificate2 e0 e1) derivation aligned stack_in stack_middle None
          stack_in (conj Hthen Helse) build_then_ordinary build_else_ordinary)
          as [then_tree [else_tree [Hthen_trace [Helse_trace branch_data]]]].
        constructor.
        * exact (normalize_resource_aligned_conditional Hthen_trace Helse_trace
            branch_data Hordinary_rest).
        * destruct stack_in as [|focused tail]; simpl.
          -- exact tt.
          -- destruct focused as [invariant outer].
             assert (Hthen_focused_suffix : RuntimeAdapter.suffix_lifo
                (RuntimeAdapter.singleton_suffix certificate1)
                ((invariant, outer) :: tail) stack_middle) by exact Hthen_suffix.
             assert (Helse_focused_suffix : RuntimeAdapter.suffix_lifo
                (RuntimeAdapter.singleton_suffix certificate2)
                ((invariant, outer) :: tail) stack_middle) by exact Helse_suffix.
             assert (build_then_focused :
               resource_fixed_singleton_lockstep_builder certificate1
                 ((invariant, outer) :: tail) stack_middle
                 (Some (invariant, outer)) tail).
             { intros F' Δ' pre' post' derivation' aligned' lifo'.
               pose proof (IH (pack_resource_aligned_suffix
                 (Validity.resource_aligned_singleton_suffix certificate1
                   derivation' aligned' lifo'))) as Htotal.
               specialize (Htotal ltac:(
                 unfold packed_resource_aligned_measure; cbn;
                 exact (RuntimeAdapter.conditional_then_measure_decreases e
                   certificate1 certificate2 e0 e1
                   (resource_certificate_suffix_of_operational_suffix suffix)))
                 Hwf Hstack).
               exact (resource_total_focused _ Htotal). }
             assert (build_else_focused :
               resource_fixed_singleton_lockstep_builder certificate2
                 ((invariant, outer) :: tail) stack_middle
                 (Some (invariant, outer)) tail).
             { intros F' Δ' pre' post' derivation' aligned' lifo'.
               pose proof (IH (pack_resource_aligned_suffix
                 (Validity.resource_aligned_singleton_suffix certificate2
                   derivation' aligned' lifo'))) as Htotal.
               specialize (Htotal ltac:(
                 unfold packed_resource_aligned_measure; cbn;
                 exact (RuntimeAdapter.conditional_else_measure_decreases e
                   certificate1 certificate2 e0 e1
                   (resource_certificate_suffix_of_operational_suffix suffix)))
                 Hwf Hstack).
               exact (resource_total_focused _ Htotal). }
             destruct (@resource_aligned_conditional_branch_data_fix cost Γ F Δ
               (S fuel) state statement
               (RuntimeAdapter.conditional_join then_exit else_exit) pre
               middle_assertion
               (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state
                 statement then_branch else_branch then_exit else_exit e
                 certificate1 certificate2 e0 e1) derivation aligned
               ((invariant, outer) :: tail) stack_middle
               (Some (invariant, outer)) tail (conj Hthen Helse)
               build_then_focused build_else_focused)
               as [then_tree' [else_tree' [Hthen_trace'
                 [Helse_trace' branch_data']]]].
             exact (normalize_resource_aligned_focused_conditional Hthen_trace'
               Helse_trace' branch_data' Hordinary_rest).
      + apply resource_total_atomic_head.
        apply (IH (pack_resource_aligned_suffix suffix)).
        * unfold packed_resource_aligned_measure. cbn.
          unfold RuntimeAdapter.certificate_source_size.
          pose proof (Runtime.RegionSyntax.size_positive Γ statement). lia.
        * exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost state
            statement _ Hwf
            (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel state statement
              body outer inner e e0 certificate e1)).
        * exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
            (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel state statement
              body outer inner e e0 certificate e1) _ _ Hwf lifo Hstack).
  Defined.

  (** Resource-native normalization of one conditional arm.  The returned
      lockstep witness need not use the same normalized tree as the
      branch-indexed trace retained by [TraceFocusedConditional].  Both
      witnesses erase to [singleton_suffix certificate], and the semantic
      reification below deliberately relates them through that common source
      rather than through a false (and unnecessary) equality of trees. *)
  Definition resource_aligned_singleton_total_normalization_complete
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit pre post stack_in stack_out}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post)
      (aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        certificate derivation)
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in
        stack_out)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open entry) stack_in) :
    @has_resource_aligned_total_normalization cost Γ F Δ entry pre stack_in
      exit post stack_out
      (Validity.resource_aligned_singleton_suffix certificate derivation
        aligned lifo).
  Proof.
    apply (packed_resource_aligned_total_normalization_complete cost Γ
      (pack_resource_aligned_suffix
        (Validity.resource_aligned_singleton_suffix certificate derivation
          aligned lifo)) Hwf Hstack).
  Defined.

  (** The branch-indexed half of focused conditional reification.  [trace]
      retains the analyzer's actual focused outcome (including
      [ClosedBranchOpened]); [resource_branch_normalization] independently
      supplies assertions and Iris resources for the same singleton source.
      No canonical-normalizer or tree-equality theorem is required. *)
  Record resource_focused_branch_reification
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit pre post focused tail stack_out}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit)
      (derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post)
      (aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        certificate derivation)
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate
        (focused :: tail) stack_out)
      (tree : RuntimeAdapter.net_tree (Some focused) tail stack_out entry exit)
      (trace : RuntimeAdapter.net_trace cost Γ entry exit (Some focused) tail
        stack_out (RuntimeAdapter.singleton_suffix certificate) tree) : Type := {
    resource_branch_normalization :
      @has_resource_aligned_total_normalization cost Γ F Δ entry pre
        (focused :: tail) exit post stack_out
        (Validity.resource_aligned_singleton_suffix certificate derivation
          aligned lifo);
  }.

  Definition build_resource_focused_branch_reification
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit pre post focused tail stack_out}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post}
      {aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        certificate derivation}
      {lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate
        (focused :: tail) stack_out}
      {tree : RuntimeAdapter.net_tree (Some focused) tail stack_out entry exit}
      {trace : RuntimeAdapter.net_trace cost Γ entry exit (Some focused) tail
        stack_out (RuntimeAdapter.singleton_suffix certificate) tree}
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open entry) (focused :: tail)) :
    @resource_focused_branch_reification cost Γ F Δ fuel entry statement exit
      pre post focused tail stack_out certificate derivation aligned lifo tree
      trace.
  Proof.
    constructor.
    exact (resource_aligned_singleton_total_normalization_complete certificate
      derivation aligned lifo Hwf Hstack).
  Defined.

  (** Type-valued reification is performed at the exposed conditional core,
      where both child alignments are constructor fields.  The wrapper layer
      above it transports only the Prop-valued source-WP consequence. *)
  Definition resource_aligned_conditional_focused_branches_reify
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel state then_branch else_branch then_exit else_exit}
      {then_pre else_pre post :
        Runtime.Translation.Assertions.assertion Γ F Δ}
      {then_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel state then_branch then_exit}
      {else_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel state else_branch else_exit}
      {then_derivation : Validity.Certified.Rules.RavenResourceTriple
        then_pre then_branch post}
      {else_derivation : Validity.Certified.Rules.RavenResourceTriple
        else_pre else_branch post}
      (then_aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        then_certificate then_derivation)
      (else_aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        else_certificate else_derivation)
      {focused tail stack_out}
      (then_lifo : RuntimeAdapter.Atomicity.lifo_certificate then_certificate
        (focused :: tail) stack_out)
      (else_lifo : RuntimeAdapter.Atomicity.lifo_certificate else_certificate
        (focused :: tail) stack_out)
      (Hwf : RuntimeAdapter.Atomicity.state_wf state)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open state) (focused :: tail))
      {then_tree : RuntimeAdapter.net_tree (Some focused) tail stack_out state
        then_exit}
      {else_tree : RuntimeAdapter.net_tree (Some focused) tail stack_out state
        else_exit}
      (then_trace : RuntimeAdapter.net_trace cost Γ state then_exit
        (Some focused) tail stack_out
        (RuntimeAdapter.singleton_suffix then_certificate) then_tree)
      (else_trace : RuntimeAdapter.net_trace cost Γ state else_exit
        (Some focused) tail stack_out
        (RuntimeAdapter.singleton_suffix else_certificate) else_tree) :
    prod
      (@resource_focused_branch_reification cost Γ F Δ fuel state then_branch
        then_exit then_pre post focused tail stack_out then_certificate
        then_derivation then_aligned then_lifo then_tree then_trace)
      (@resource_focused_branch_reification cost Γ F Δ fuel state else_branch
        else_exit else_pre post focused tail stack_out else_certificate
        else_derivation else_aligned else_lifo else_tree else_trace).
  Proof.
    split.
    - exact (build_resource_focused_branch_reification Hwf Hstack).
    - exact (build_resource_focused_branch_reification Hwf Hstack).
  Defined.

  Theorem packed_aligned_total_normalization_complete
      (cost : RuntimeAdapter.Atomicity.cost_model) Γ F Δ
      (packed : packed_aligned_suffix cost Γ F Δ) :
    RuntimeAdapter.Atomicity.state_wf
      (packed_aligned_entry cost Γ F Δ packed) ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open
        (packed_aligned_entry cost Γ F Δ packed))
      (packed_aligned_stack_in cost Γ F Δ packed) ->
    packed_has_aligned_total_normalization packed.
  Proof.
    induction packed as [packed IH] using
      packed_aligned_well_founded_induction.
    destruct packed as [entry pre stack_in exit post stack_out suffix].
    simpl in *. intros Hwf Hstack.
    destruct suffix.
    - constructor.
      + apply normalize_aligned_done.
      + destruct stack.
        * exact tt.
        * apply normalize_aligned_focused_done.
    - dependent destruction certificate.
      + apply aligned_total_leaf_head.
        apply (IH (pack_aligned_suffix suffix)).
        * unfold packed_aligned_measure. cbn.
          unfold RuntimeAdapter.certificate_source_size.
          pose proof (Runtime.RegionSyntax.size_positive Γ statement). lia.
        * exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost state
            statement exit Hwf
            (RuntimeAdapter.Atomicity.CertLeaf cost Γ fuel state statement
              exit e e0)).
        * exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
            (RuntimeAdapter.Atomicity.CertLeaf cost Γ fuel state statement
              exit e e0) _ _ Hwf lifo Hstack).
      + apply aligned_total_unfold_head.
        apply (IH (pack_aligned_suffix suffix)).
        * unfold packed_aligned_measure. cbn.
          unfold RuntimeAdapter.certificate_source_size.
          pose proof (Runtime.RegionSyntax.size_positive Γ statement). lia.
        * exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost state
            statement exit Hwf
            (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel state statement
              invariant exit e e0)).
        * exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
            (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel state statement
              invariant exit e e0) _ _ Hwf lifo Hstack).
      + apply aligned_total_fold_head.
        apply (IH (pack_aligned_suffix suffix)).
        * unfold packed_aligned_measure. cbn.
          unfold RuntimeAdapter.certificate_source_size.
          pose proof (Runtime.RegionSyntax.size_positive Γ statement). lia.
        * exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost state
            statement (RuntimeAdapter.Atomicity.fold_invariant invariant state)
            Hwf (RuntimeAdapter.Atomicity.CertFold cost Γ fuel state statement
              invariant e)).
        * exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
            (RuntimeAdapter.Atomicity.CertFold cost Γ fuel state statement
              invariant e) _ _ Hwf lifo Hstack).
      + { refine (@aligned_total_sequence_head cost Γ F Δ fuel state statement
          first middle second exit final pre middle_assertion post stack_in
          stack_middle stack_out e certificate1 certificate2 derivation aligned
          lifo suffix _).
        cbn.
        lazymatch goal with
        | |- has_aligned_total_normalization ?flat =>
            refine (IH (pack_aligned_suffix flat) _ Hwf Hstack)
        end.
        unfold packed_aligned_measure. cbn.
        exact (RuntimeAdapter.expand_sequence_suffix_measure_decreases e
          certificate1 certificate2
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            suffix)). }
      + destruct lifo as [Hthen Helse].
        assert (Hthen_suffix : RuntimeAdapter.suffix_lifo
          (RuntimeAdapter.singleton_suffix certificate1) stack_in stack_middle).
        { apply (proj2 (RuntimeAdapter.singleton_suffix_lifo certificate1 _ _)).
          exact Hthen. }
        assert (Helse_suffix : RuntimeAdapter.suffix_lifo
          (RuntimeAdapter.singleton_suffix certificate2) stack_in stack_middle).
        { apply (proj2 (RuntimeAdapter.singleton_suffix_lifo certificate2 _ _)).
          exact Helse. }
        pose proof (RuntimeAdapter.traced_suffix_net_totality_complete
          (RuntimeAdapter.singleton_suffix certificate1) Hwf) as Hthen_total.
        pose proof (RuntimeAdapter.traced_suffix_net_totality_complete
          (RuntimeAdapter.singleton_suffix certificate2) Hwf) as Helse_total.
        pose (then_normal := choose_prop_witness
          (RuntimeAdapter.traced_total_net _ Hthen_total stack_in
            stack_middle Hwf Hstack Hthen_suffix)).
        pose (else_normal := choose_prop_witness
          (RuntimeAdapter.traced_total_net _ Helse_total stack_in
            stack_middle Hwf Hstack Helse_suffix)).
        assert (Hjoin_wf : RuntimeAdapter.Atomicity.state_wf
          (RuntimeAdapter.conditional_join then_exit else_exit)).
        { exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost state
            statement _ Hwf
            (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state
              statement then_branch else_branch then_exit else_exit e
              certificate1 certificate2 e0 e1)). }
        assert (Hjoin_stack : RuntimeAdapter.Atomicity.access_stack_consistent
          (RuntimeAdapter.Atomicity.analysis_open
            (RuntimeAdapter.conditional_join then_exit else_exit)) stack_middle).
        { exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
            (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state
              statement then_branch else_branch then_exit else_exit e
              certificate1 certificate2 e0 e1) _ _ Hwf
            (conj Hthen Helse) Hstack). }
        pose proof (IH (pack_aligned_suffix suffix)) as Hrest_total.
        specialize (Hrest_total ltac:(
          unfold packed_aligned_measure; cbn;
          unfold RuntimeAdapter.certificate_source_size;
          pose proof (Runtime.RegionSyntax.size_positive Γ statement); lia)
          Hjoin_wf Hjoin_stack).
        destruct Hrest_total as [Hordinary_rest Hfocused_rest].
        constructor.
        * eapply normalize_aligned_conditional.
          -- exact (RuntimeAdapter.traced_net_source _ then_normal).
          -- exact (RuntimeAdapter.traced_net_source _ else_normal).
          -- exact Hordinary_rest.
        * destruct stack_in as [|focused tail]; simpl.
          -- exact tt.
          -- destruct focused as [invariant outer].
             assert (Hthen_focused_suffix : RuntimeAdapter.suffix_lifo
                (RuntimeAdapter.singleton_suffix certificate1)
                ((invariant, outer) :: tail) stack_middle) by exact Hthen_suffix.
             assert (Helse_focused_suffix : RuntimeAdapter.suffix_lifo
                (RuntimeAdapter.singleton_suffix certificate2)
                ((invariant, outer) :: tail) stack_middle) by exact Helse_suffix.
             pose (then_focused := choose_prop_witness
               (RuntimeAdapter.traced_total_focused_net _ Hthen_total
                 invariant outer tail stack_middle Hwf Hstack
                 Hthen_focused_suffix)).
             pose (else_focused := choose_prop_witness
               (RuntimeAdapter.traced_total_focused_net _ Helse_total
                 invariant outer tail stack_middle Hwf Hstack
                 Helse_focused_suffix)).
             eapply normalize_aligned_focused_conditional.
             ++ exact (RuntimeAdapter.traced_focused_net_source _ then_focused).
             ++ exact (RuntimeAdapter.traced_focused_net_source _ else_focused).
             ++ exact Hordinary_rest.
      + apply aligned_total_atomic_head.
        apply (IH (pack_aligned_suffix suffix)).
        * unfold packed_aligned_measure. cbn.
          unfold RuntimeAdapter.certificate_source_size.
          pose proof (Runtime.RegionSyntax.size_positive Γ statement). lia.
        * exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost state
            statement _ Hwf
            (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel state statement
              body outer inner e e0 certificate e1)).
        * exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
            (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel state statement
              body outer inner e e0 certificate e1) _ _ Hwf lifo Hstack).
  Defined.

  Definition aligned_singleton_total_normalization
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit}
      {pre post : Runtime.Translation.Assertions.assertion Γ F Δ}
      {stack_in stack_out : list RuntimeAdapter.Atomicity.access_marker}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post}
      (aligned : Validity.Certified.certificate_hoare_aligned cost certificate
        derivation)
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in
        stack_out)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open entry) stack_in) :
    has_aligned_total_normalization
      (Validity.aligned_singleton_suffix certificate derivation aligned lifo).
  Proof.
    exact (packed_aligned_total_normalization_complete cost Γ F Δ
      (pack_aligned_suffix
        (Validity.aligned_singleton_suffix certificate derivation aligned lifo))
      Hwf Hstack).
  Defined.

  (** Assertion-aware semantic target for the final reification induction.
      Unlike the runtime-only helper judgments below, this relation retains
      the interpreted symbolic state needed to select a concrete conditional
      arm.  Its mode and access-stack indices remain general so the same
      induction can cover ordinary execution and focused slices. *)
  Definition aligned_trace_runtime_refinement
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source tree
        suffix trace}
      (_ : @aligned_net_trace cost Γ F Δ entry pre stack_in exit post
        stack_out mode tail source tree suffix trace) : Prop :=
    Validity.Model.runtime_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset),
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack_in) ⊢
    ConcreteOrdinaryTrace.source_translated_wp source runtime ambient
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       Validity.World.access_stack_interp atoms ambient stack_out).

  (** Resource-triple analogue of [aligned_trace_runtime_refinement].  This
      is intentionally assertion-aware: concrete conditional erasure is
      guard-directed, whereas the structural trace branch is merely a
      disjunction.  Keeping the symbolic and access resources in the motive
      lets [runtime_wp_if_context_full] select the appropriate arm. *)
  Definition resource_aligned_trace_runtime_refinement
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source tree
        suffix trace}
      (_ : @resource_aligned_net_trace cost Γ F Δ entry pre stack_in exit
        post stack_out mode tail source tree suffix trace) : Prop :=
    Validity.Model.runtime_cost_model_sound cost ->
    Validity.Certified.procedure_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset),
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack_in) ⊢
    ConcreteOrdinaryTrace.source_translated_wp source runtime ambient
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       Validity.World.access_stack_interp atoms ambient stack_out).

  Lemma resource_aligned_trace_done_runtime_refinement
      {cost Γ F Δ state assertion stack} :
    resource_aligned_trace_runtime_refinement
      (@ResourceAlignedTraceDone cost Γ F Δ state assertion stack).
  Proof.
    intros _ _ _ _ runtime formals binders atoms ambient _.
    unfold ConcreteOrdinaryTrace.source_translated_wp. simpl.
    iIntros "Hresources". iModIntro. iExact "Hresources".
  Qed.

  Lemma resource_aligned_trace_done_focused_runtime_refinement
      {cost Γ F Δ state assertion focused tail} :
    resource_aligned_trace_runtime_refinement
      (@ResourceAlignedTraceDoneFocused cost Γ F Δ state assertion focused
        tail).
  Proof.
    intros _ _ _ _ runtime formals binders atoms ambient _.
    unfold ConcreteOrdinaryTrace.source_translated_wp. simpl.
    iIntros "Hresources". iModIntro. iExact "Hresources".
  Qed.

  (** A branch solver used by the conditional constructor.  Normalization is
      deliberately delayed until the parent conditional supplies its actual
      LIFO stacks and entry consistency proof. *)
  Definition aligned_singleton_ordinary_runtime_refinement
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit}
      {pre post : Runtime.Translation.Assertions.assertion Γ F Δ}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post}
      (aligned : Validity.Certified.certificate_hoare_aligned cost certificate
        derivation) : Prop :=
    forall (stack_in stack_out : list RuntimeAdapter.Atomicity.access_marker)
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack_in
        stack_out)
      (normal : has_aligned_ordinary_normalization
        (Validity.aligned_singleton_suffix certificate derivation aligned
          lifo)),
    match normal with
    | existT _ (existT _ aligned_trace) =>
        aligned_trace_runtime_refinement aligned_trace
    end.

  (** A purely structural recognizer: does [aligned]'s wrapper spine consist
      only of [AlignedConditional] at the core, wrapped by any number of
      [AlignedFrame]/[AlignedConsequence]/[AlignedExistsElim]/
      [AlignedExistsPreserve]?  Unlike [aligned_conditional_core_obligation],
      this does not attempt to also carry the branch-refinement content: a
      seam refinement (see [aligned_seam_runtime_refinement] below) depends
      on [rest]/[ambient]/[runtime], none of which belong in a fixpoint
      indexed only by [aligned].  The semantic eliminator built on top of
      this recognizer instead takes the two branches' seam refinements as
      explicit, separate hypotheses. *)
  Fixpoint aligned_conditional_seam_obligation
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel entry statement exit}
      {pre post : Runtime.Translation.Assertions.assertion Γ F Δ}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post}
      (aligned : Validity.Certified.certificate_hoare_aligned cost certificate
        derivation) : Prop :=
    match aligned with
    | Validity.Certified.AlignedConditional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ => True
    | Validity.Certified.AlignedFrame _ _ _ _ _ _ _ _ _ _ _ _ _ inner =>
        aligned_conditional_seam_obligation inner
    | Validity.Certified.AlignedConsequence _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ inner => aligned_conditional_seam_obligation inner
    | Validity.Certified.AlignedExistsElim _ Γ' F' Δ' t' fuel' entry' exit'
        statement' body' post' certificate' derivation' inner =>
        @aligned_conditional_seam_obligation cost Γ' F' (t' :: Δ') fuel'
          entry' statement' exit' body'
          (Runtime.Translation.Assertions.weaken_assertion post') certificate'
          derivation' inner
    | Validity.Certified.AlignedExistsPreserve _ Γ' F' Δ' t' fuel' entry' exit'
        statement' body' post' certificate' derivation' inner =>
        @aligned_conditional_seam_obligation cost Γ' F' (t' :: Δ') fuel'
          entry' statement' exit' body' post' certificate' derivation' inner
    | _ => False
    end.

  (** Step 6: the unfold-only seam case, for an arbitrary continuation whose
      own erasure is [None] -- i.e. a seam where *nothing physical* runs
      anywhere, branch or rest.  This validates the seam's indices, masks,
      erasure, and continuation hand-off without needing the atomicity
      argument at all: since [TUnfold] itself erases to [None]
      (`typed_runtime.v`'s own [runtime_stmt] TUnfold case) and [rest_suffix]
      is assumed to erase to [None] too, [aligned_seam_runtime] collapses to
      [None], and [runtime_option_wp]'s own [None] case is a bare fancy
      update -- no [runtime_wp]/mask-monotonicity argument (which does not
      hold for non-atomic programs) is needed anywhere; ordinary [fupd_trans]
      composes [unfold_node_runtime_refinement]'s own bare update
      ([mask entry -> mask exit]) directly with the caller-supplied
      continuation (already at [mask exit]).  Step 7 is the litmus test for
      when [rest_suffix] genuinely contains a physical (atomic) step, and
      step 8 generalizes it.

      Pending: [aligned_seam_trace]'s [aligned_seam_rest] field now requires
      [has_aligned_focused_closing_normalization], i.e. a witness that
      [rest_suffix] eventually closes via [aligned_focused_close_split] --
      but this lemma's own scenario is exactly a [rest_suffix] that never
      closes.  A never-closing continuation needs a separate, non-
      [aligned_seam_trace]-based statement (or [aligned_seam_trace] itself
      needs a degenerate no-close variant); this is not yet resolved. *)
  (*
  Lemma aligned_seam_runtime_refinement_unfold_only
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel node invariant arguments entry exit}
      (store : Runtime.IR.Core.symbolic_store Γ F Δ)
      (body : Runtime.Translation.Assertions.assertion Γ F Δ)
      (view : Runtime.RegionSyntax.view
        (Runtime.IR.TUnfold node invariant arguments) =
        typed_analysis_view.TypedAnalysisView.ViewUnfold invariant)
      (step : RuntimeAdapter.Atomicity.open_invariant invariant entry =
        inr exit)
      (available : invariant ∈ RuntimeAdapter.Atomicity.analysis_mask entry)
      (instantiated : Contracts.instantiated_invariant Γ F Δ
        (Logic.invariant_args invariant) invariant
        (Runtime.Validation.Hoare.symbolize_expr_list store arguments) body)
      {tail : list RuntimeAdapter.Atomicity.access_marker}
      {conditional_join : RuntimeAdapter.Atomicity.analysis_state}
      {join_assertion : Runtime.Translation.Assertions.assertion Γ F Δ}
      {final_exit : RuntimeAdapter.Atomicity.analysis_state}
      {final_post : Runtime.Translation.Assertions.assertion Γ F Δ}
      {final_stack_out : list RuntimeAdapter.Atomicity.access_marker}
      {rest_suffix : Validity.aligned_operational_suffix cost Γ F Δ
        conditional_join join_assertion
        ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)
        final_exit final_post final_stack_out}
      (rest_normal : has_aligned_focused_normalization rest_suffix)
      (Hrest_erased : forall runtime, ConcreteOrdinaryTrace.source_runtime
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest_suffix) runtime = None)
      {ambient : coPset}
      (mask_eq : Validity.Model.active_runtime_mask ambient exit =
        Validity.Model.active_runtime_mask ambient conditional_join)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open entry) tail)
      (Hnamespace : ↑(Resources.invariant_namespace invariant) ⊆
        Validity.Model.active_runtime_mask ambient entry) :
    aligned_seam_runtime_refinement
      {|
         aligned_seam_branch := aligned_total_ordinary _
           (aligned_singleton_total_normalization
             (Validity.Certified.AlignedUnfold cost Γ F Δ fuel entry node
               invariant arguments exit store body view step available
               instantiated)
             (eq_refl :
               RuntimeAdapter.Atomicity.lifo_certificate
                 (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
                   (Runtime.IR.TUnfold node invariant arguments) invariant
                   exit view step)
                 tail
                 ((invariant, RuntimeAdapter.Atomicity.analysis_open entry)
                   :: tail))
             Hwf Hstack);
         aligned_seam_mask_eq := mask_eq;
         aligned_seam_rest := rest_normal |}.
  Proof.
    intros Hcost Hwf'' Hstack'' runtime formals binders atoms Hfootprint
      final_mask carried final Hcont.
    unfold aligned_seam_runtime, selected_conditional_continuation.
    rewrite (Hrest_erased runtime) in Hcont |- *.
    simpl in Hcont |- *.
    iIntros "[Hworld [Hpre [Haccess Hcarried]]]".
    iPoseProof (ConcreteAccessNodes.unfold_node_runtime_refinement
      (node := node) store body entry exit ambient tail step Hnamespace
      instantiated runtime formals binders atoms
      with "[$Hworld $Hpre $Haccess]") as "Hopen".
    iMod "Hopen" as "[Hworld' [Hpost Haccess']]".
    iApply Hcont. iFrame "Hworld' Hpost Haccess' Hcarried".
  Qed.
  *)

  (** Step 7's litmus case: [unfold I; atomic { ... }; fold I], with the
      atomic step and the fold both living in the continuation
      ([rest_suffix]).  This exercises every part of the retargeted
      [aligned_seam_runtime_refinement]: the split lands exactly at the
      fold (so [aligned_split_prefix] is "atomic step, then fold" and
      [aligned_split_rest] is trivially empty), and the atomic step's own
      Hoare content is generic -- an arbitrary [atomic_body_certificate]
      trusted via [Contracts.trusted_atomic], mirroring
      [atomic_chunk_runtime_refinement]'s own genericity -- so this is a
      real regression case, not a hand-picked concrete program. The atomic
      step's pre/post are deliberately both [AAnd (AStack store) body]: the
      step need not be a logical no-op physically, but it must hand the
      invariant's own assertion back unchanged, which is exactly what lets
      the same [store]/[body]/[instantiated] serve both the unfold and the
      matching fold. *)
  Section LitmusUnfoldAtomicFold.
    Context {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel node invariant arguments entry exit}
      (store : Runtime.IR.Core.symbolic_store Γ F Δ)
      (body : Runtime.Translation.Assertions.assertion Γ F Δ)
      (view : Runtime.RegionSyntax.view
        (Runtime.IR.TUnfold node invariant arguments) =
        typed_analysis_view.TypedAnalysisView.ViewUnfold invariant)
      (step : RuntimeAdapter.Atomicity.open_invariant invariant entry = inr exit)
      (available : invariant ∈ RuntimeAdapter.Atomicity.analysis_mask entry)
      (instantiated : Contracts.instantiated_invariant Γ F Δ
        (Logic.invariant_args invariant) invariant
        (Runtime.Validation.Hoare.symbolize_expr_list store arguments) body)
      {tail : list RuntimeAdapter.Atomicity.access_marker}
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open entry) tail)
      {atomic_node : typed_core.TypedCore.node_id}
      {atomic_program : Runtime.IR.stmt Γ}
      {atomic_outer atomic_inner : RuntimeAdapter.Atomicity.analysis_state}
      (atomic_view : Runtime.RegionSyntax.view
        (Runtime.IR.TAtomic atomic_node atomic_program) =
        typed_analysis_view.TypedAnalysisView.ViewAtomic atomic_program)
      (atomic_step : RuntimeAdapter.Atomicity.take_step
        RuntimeAdapter.Atomicity.AtomicStep exit = inr atomic_outer)
      (atomic_body_certificate : RuntimeAdapter.Atomicity.analysis_certificate
        cost Γ fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask atomic_outer)
          (RuntimeAdapter.Atomicity.analysis_open atomic_outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken atomic_outer) true)
        atomic_program atomic_inner)
      (atomic_open_equal : RuntimeAdapter.Atomicity.analysis_open atomic_inner =
        RuntimeAdapter.Atomicity.analysis_open atomic_outer)
      (atomic_trusted : Contracts.trusted_atomic Γ atomic_program)
      (atomic_body_derivation : Validity.Certified.Rules.RavenHoareTriple
        (Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store) body)
        atomic_program
        (RuntimeAdapter.Atomicity.analysis_mask exit)
        (RuntimeAdapter.Atomicity.analysis_mask atomic_inner)
        (Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store) body))
      (atomic_body_aligned : Validity.Certified.certificate_hoare_aligned cost
        atomic_body_certificate
        (Validity.Certified.hoare_mask_transport atomic_body_derivation
          (eq_sym (Validity.Certified.step_analysis_mask
            exit atomic_outer atomic_step))
          eq_refl))
      (atomic_body_valid : Validity.certificate_semantically_valid
        (stack_in := (invariant, RuntimeAdapter.Atomicity.analysis_open entry)
          :: tail)
        (stack_out := (invariant, RuntimeAdapter.Atomicity.analysis_open entry)
          :: tail)
        (pre := Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store) body)
        (post := Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store) body)
        atomic_body_certificate)
      (atomic_body_lifo : RuntimeAdapter.Atomicity.lifo_certificate
        atomic_body_certificate
        ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)
        ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail))
      {fold_node : typed_core.TypedCore.node_id}
      (fold_view : Runtime.RegionSyntax.view
        (Runtime.IR.TFold fold_node invariant arguments) =
        typed_analysis_view.TypedAnalysisView.ViewFold invariant)
      (fold_Hwf : RuntimeAdapter.Atomicity.state_wf
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask atomic_inner)
          (RuntimeAdapter.Atomicity.analysis_open atomic_inner)
          (RuntimeAdapter.Atomicity.analysis_step_taken atomic_outer ||
            RuntimeAdapter.Atomicity.analysis_step_taken atomic_inner)
          (RuntimeAdapter.Atomicity.analysis_in_atomic atomic_outer)))
      {ambient : coPset}
      (Hnamespace : ↑(Resources.invariant_namespace invariant) ⊆
        Validity.Model.active_runtime_mask ambient entry).

    Let branch_suffix := Validity.aligned_singleton_suffix
      (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
        (Runtime.IR.TUnfold node invariant arguments) invariant exit view step)
      (Validity.Certified.hoare_mask_transport
        (Validity.Certified.Rules.UnfoldInvariantRule node invariant arguments
          store body (RuntimeAdapter.Atomicity.analysis_mask entry) available
          instantiated) eq_refl
        (eq_sym (Validity.Certified.unfold_analysis_mask view step)))
      (Validity.Certified.AlignedUnfold cost Γ F Δ fuel entry node invariant
        arguments exit store body view step available instantiated)
      (eq_refl :
        RuntimeAdapter.Atomicity.lifo_certificate
          (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
            (Runtime.IR.TUnfold node invariant arguments) invariant exit view
            step)
          tail
          ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)).

    Let atomic_certificate := RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel
      exit (Runtime.IR.TAtomic atomic_node atomic_program) atomic_program
      atomic_outer atomic_inner atomic_view atomic_step atomic_body_certificate
      atomic_open_equal.

    Let atomic_derivation := Validity.Certified.Rules.AtomicBlockRule
      atomic_node
      (Runtime.Translation.Assertions.AAnd
        (Runtime.Translation.Assertions.AStack store) body)
      (Runtime.Translation.Assertions.AAnd
        (Runtime.Translation.Assertions.AStack store) body)
      atomic_program (RuntimeAdapter.Atomicity.analysis_mask exit)
      (RuntimeAdapter.Atomicity.analysis_mask atomic_inner) atomic_trusted
      atomic_body_derivation.

    Let atomic_aligned := Validity.Certified.AlignedAtomic cost Γ F Δ fuel exit
      atomic_node atomic_program atomic_outer atomic_inner
      (Runtime.Translation.Assertions.AAnd
        (Runtime.Translation.Assertions.AStack store) body)
      (Runtime.Translation.Assertions.AAnd
        (Runtime.Translation.Assertions.AStack store) body)
      atomic_view atomic_step atomic_body_certificate atomic_open_equal
      atomic_trusted atomic_body_derivation atomic_body_aligned.

    Let atomic_lifo :
        RuntimeAdapter.Atomicity.lifo_certificate atomic_certificate
          ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)
          ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail) :=
      conj atomic_body_lifo eq_refl.

    Let atomic_cert_exit := RuntimeAdapter.Atomicity.AnalysisState
      (RuntimeAdapter.Atomicity.analysis_mask atomic_inner)
      (RuntimeAdapter.Atomicity.analysis_open atomic_inner)
      (RuntimeAdapter.Atomicity.analysis_step_taken atomic_outer ||
        RuntimeAdapter.Atomicity.analysis_step_taken atomic_inner)
      (RuntimeAdapter.Atomicity.analysis_in_atomic atomic_outer).

    Let fold_certificate := RuntimeAdapter.Atomicity.CertFold cost Γ fuel
      atomic_cert_exit (Runtime.IR.TFold fold_node invariant arguments)
      invariant fold_view.

    Let fold_derivation := Validity.Certified.hoare_mask_transport
      (Validity.Certified.Rules.FoldInvariantRule fold_node invariant
        arguments store body
        (RuntimeAdapter.Atomicity.analysis_mask atomic_cert_exit) instantiated)
      eq_refl (eq_sym (Validity.Certified.fold_analysis_mask invariant atomic_cert_exit)).

    Let fold_aligned := Validity.Certified.AlignedFold cost Γ F Δ fuel
      atomic_cert_exit fold_node invariant arguments store body fold_view
      instantiated.

    Lemma litmus_open_fresh :
      invariant ∉ RuntimeAdapter.Atomicity.analysis_open entry /\
      RuntimeAdapter.Atomicity.analysis_open exit =
        {[invariant]} ∪ RuntimeAdapter.Atomicity.analysis_open entry.
    Proof.
      pose proof (RuntimeAdapter.Atomicity.open_invariant_success invariant
        entry exit step) as (Hfresh & _ & _ & Hopen).
      exact (conj Hfresh Hopen).
    Qed.

    Lemma litmus_atomic_cert_exit_open :
      RuntimeAdapter.Atomicity.analysis_open atomic_cert_exit =
        {[invariant]} ∪ RuntimeAdapter.Atomicity.analysis_open entry.
    Proof.
      unfold atomic_cert_exit. simpl.
      rewrite atomic_open_equal.
      pose proof (RuntimeAdapter.Atomicity.atomic_step_preserves_sets
        exit atomic_outer atomic_step) as
        [_ Hopen].
      rewrite Hopen. exact (proj2 litmus_open_fresh).
    Qed.

    Lemma litmus_fold_member :
      invariant ∈ RuntimeAdapter.Atomicity.analysis_open atomic_cert_exit.
    Proof.
      rewrite litmus_atomic_cert_exit_open.
      apply elem_of_union_l, elem_of_singleton. reflexivity.
    Qed.

    Let fold_lifo :
        RuntimeAdapter.Atomicity.lifo_certificate fold_certificate
          ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)
          tail :=
      or_introl (ex_intro _ (RuntimeAdapter.Atomicity.analysis_open entry)
        (conj eq_refl (conj litmus_fold_member (conj
          (proj1 litmus_open_fresh) litmus_atomic_cert_exit_open)))).

    Let fold_suffix := @Validity.AlignedOperationalCons cost Γ F Δ
      _ _ _ _ _ _ _ _
      fold_certificate fold_derivation fold_aligned fold_lifo
      _ _ _
      (Validity.AlignedOperationalDone
        (RuntimeAdapter.Atomicity.fold_invariant invariant atomic_cert_exit)
        (Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store)
          (Runtime.Translation.Assertions.AInvariant invariant
            (Runtime.Validation.Hoare.symbolize_expr_list store arguments)))
        tail).

    Let atomic_chunk_certificate := @RuntimeAdapter.ChunkCertificateAtomic
      cost Γ
      fuel exit (Runtime.IR.TAtomic atomic_node atomic_program) atomic_program
      atomic_outer atomic_inner
      ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)
      atomic_view atomic_step atomic_body_certificate atomic_open_equal.

    Let fold_closing := @RuntimeAdapter.ChunkCertificateFold cost Γ fuel
      atomic_cert_exit (Runtime.IR.TFold fold_node invariant arguments)
      invariant (RuntimeAdapter.Atomicity.analysis_open entry) tail fold_view
      litmus_fold_member (proj1 litmus_open_fresh) litmus_atomic_cert_exit_open.

    Let fold_split :=
      aligned_focused_close_split_here
        (certificate := fold_certificate) (derivation := fold_derivation)
        (aligned := fold_aligned) (lifo := fold_lifo)
        (rest := Validity.AlignedOperationalDone
          (RuntimeAdapter.Atomicity.fold_invariant invariant atomic_cert_exit)
          (Runtime.Translation.Assertions.AAnd
            (Runtime.Translation.Assertions.AStack store)
            (Runtime.Translation.Assertions.AInvariant invariant
              (Runtime.Validation.Hoare.symbolize_expr_list store arguments)))
          tail)
        fold_closing I
        (@AlignedTraceDone cost Γ F Δ
          (RuntimeAdapter.Atomicity.fold_invariant invariant atomic_cert_exit)
          (Runtime.Translation.Assertions.AAnd
            (Runtime.Translation.Assertions.AStack store)
            (Runtime.Translation.Assertions.AInvariant invariant
              (Runtime.Validation.Hoare.symbolize_expr_list store arguments)))
          tail).

    Let atomic_fold_split :=
      aligned_focused_close_split_later
        (certificate := atomic_certificate) (derivation := atomic_derivation)
        (aligned := atomic_aligned) (lifo := atomic_lifo) (rest := fold_suffix)
        atomic_chunk_certificate I _ fold_split.

    Let rest_suffix := @Validity.AlignedOperationalCons cost Γ F Δ
      _ _ _ _ _ _ _ _
      atomic_certificate atomic_derivation atomic_aligned atomic_lifo
      _ _ _ fold_suffix.

    Let litmus_rest_normal :
        has_aligned_focused_closing_normalization rest_suffix.
    Proof.
      refine (existT _ (existT _ (existT _ atomic_fold_split))).
    Defined.

    Let litmus_seam : aligned_seam_trace branch_suffix rest_suffix ambient := {|
      aligned_seam_branch := aligned_total_ordinary _
        (aligned_singleton_total_normalization
          (Validity.Certified.AlignedUnfold cost Γ F Δ fuel entry node
            invariant arguments exit store body view step available
            instantiated)
          (eq_refl :
            RuntimeAdapter.Atomicity.lifo_certificate
              (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
                (Runtime.IR.TUnfold node invariant arguments) invariant exit
                view step)
              tail
              ((invariant, RuntimeAdapter.Atomicity.analysis_open entry)
                :: tail))
          Hwf Hstack);
      aligned_seam_mask_eq := eq_refl;
      aligned_seam_rest := litmus_rest_normal;
    |}.

    Lemma aligned_seam_runtime_refinement_unfold_atomic_fold :
      aligned_seam_runtime_refinement litmus_seam.
    Proof.
      unfold aligned_seam_runtime_refinement.
      intros Hcost Hwf' Hstack' runtime formals binders atoms Hfootprint
        final_mask carried final Hcont.
      unfold selected_conditional_continuation in *.
      simpl in Hfootprint, Hcont |- *.
      have Hcombine_none_r : forall X : option Runtime.LegacyLang.runtime_stmt,
          Validity.Model.combine_runtime_statements X None = X.
      { intros X. destruct X; reflexivity. }
      have Hatomic_footprint : Validity.Model.runtime_mask
          (RuntimeAdapter.Atomicity.certificate_footprint atomic_certificate)
          ⊆ ambient.
      { etrans; last exact Hfootprint. apply Validity.Model.runtime_mask_mono.
        etrans; first apply
          (Normalized.suffix_footprint_head_subset atomic_certificate
            (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
              fold_suffix)).
        etrans; first apply union_subseteq_r. apply union_subseteq_l. }
      have Hfold_active : Validity.Model.active_runtime_mask ambient
          (RuntimeAdapter.Atomicity.fold_invariant invariant atomic_cert_exit) =
          Validity.Model.enabled_runtime_mask ambient
            (RuntimeAdapter.Atomicity.analysis_open entry).
      { have Hmember : invariant ∈
            {[invariant]} ∪ RuntimeAdapter.Atomicity.analysis_open entry.
        { apply elem_of_union_l, elem_of_singleton. reflexivity. }
        apply Validity.Model.active_runtime_mask_same_open.
        unfold RuntimeAdapter.Atomicity.fold_invariant.
        rewrite litmus_atomic_cert_exit_open.
        rewrite (bool_decide_eq_true_2 _ Hmember).
        simpl.
        apply set_eq. intros y.
        rewrite elem_of_difference.
        rewrite elem_of_union.
        rewrite elem_of_singleton.
        split.
        - intros [[Heq | Hy] Hneq].
          + exfalso. exact (Hneq Heq).
          + exact Hy.
        - intros Hy. split.
          + right. exact Hy.
          + intros Heq. subst y. exact (proj1 litmus_open_fresh Hy). }
      have Hweaken : ((Validity.global_world_context atoms ∗
          Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
            runtime formals binders atoms
            (Runtime.Translation.Assertions.AAnd
              (Runtime.Translation.Assertions.AStack store) body) ∗
          Validity.World.access_stack_interp atoms ambient
            ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail))
            ∗ carried) ⊢
        |={Validity.Model.active_runtime_mask ambient atomic_cert_exit,
           Validity.Model.enabled_runtime_mask ambient
             (RuntimeAdapter.Atomicity.analysis_open entry)}=>
        |={Validity.Model.enabled_runtime_mask ambient
             (RuntimeAdapter.Atomicity.analysis_open entry), final_mask}=>
          final.
      { iIntros "[[Hworld [Hpost Haccess]] Hcarried]".
        iPoseProof (ConcreteAccessNodes.matched_fold_node_runtime_refinement
          (node := fold_node) store body atomic_cert_exit ambient
          (RuntimeAdapter.Atomicity.analysis_open entry) tail fold_Hwf
          litmus_fold_member (proj1 litmus_open_fresh)
          litmus_atomic_cert_exit_open instantiated runtime formals binders
          atoms with "[$Hworld $Hpost $Haccess]") as "Hfold".
        iEval (unfold Validity.translated_runtime_wp; simpl) in "Hfold".
        rewrite Hfold_active.
        iMod "Hfold" as "[Hworld' [Hpost' Haccess']]".
        iModIntro. iApply Hcont. iFrame "Hworld' Hpost' Haccess' Hcarried". }
      destruct (Validity.certificate_runtime_statement atomic_certificate
        runtime) as [physical|] eqn:Hphysical.
      - have Hphysical' : Validity.Model.runtime_stmt
            (Validity.Model.runtime_names Γ runtime)
            (Validity.Model.runtime_stack_id Γ runtime) atomic_program =
            Some physical := Hphysical.
        have Hatomic_instance : @Atomic Runtime.LegacyLang.simp_lang
            WeaklyAtomic physical.
        { exact (Validity.trusted_atomic_runtime_atomic atomic_program runtime
            physical atomic_trusted Hphysical'). }
        iIntros "[Hworld [Hpre [Haccess Hcarried]]]".
        iApply (Validity.translated_atomic_leaf_mask_change runtime ambient
          exit atomic_cert_exit (Runtime.IR.TAtomic atomic_node atomic_program)
          physical
          (Validity.Model.enabled_runtime_mask ambient
            (RuntimeAdapter.Atomicity.analysis_open entry))
          (|={Validity.Model.enabled_runtime_mask ambient
               (RuntimeAdapter.Atomicity.analysis_open entry), final_mask}=>
            final)%I Hphysical').
        iPoseProof (ConcreteAccessNodes.unfold_node_runtime_refinement
          (node := node) store body entry exit ambient tail step Hnamespace
          instantiated runtime formals binders atoms
          with "[$Hworld $Hpre $Haccess]") as "Hopen".
        iEval (unfold Validity.translated_runtime_wp; simpl) in "Hopen".
        iMod "Hopen" as "[Hworld' [Hpost Haccess']]".
        iPoseProof (ConcreteChunks.atomic_chunk_runtime_refinement atomic_step
          atomic_body_certificate atomic_open_equal
          ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)
          (Runtime.Translation.Assertions.AAnd
            (Runtime.Translation.Assertions.AStack store) body)
          (Runtime.Translation.Assertions.AAnd
            (Runtime.Translation.Assertions.AStack store) body) atomic_trusted
          atomic_body_valid runtime formals binders atoms ambient
          Hatomic_footprint with "[$Hworld' $Hpost $Haccess']") as "Hatomic_wp".
        iPoseProof (Validity.translated_runtime_wp_frame runtime ambient exit
          atomic_cert_exit (Runtime.IR.TAtomic atomic_node atomic_program) _
          carried with "[$Hatomic_wp $Hcarried]") as "Hatomic_wp_framed".
        iApply (Validity.translated_runtime_wp_mono runtime ambient exit
          atomic_cert_exit (Runtime.IR.TAtomic atomic_node atomic_program) _ _
          Hweaken).
        iExact "Hatomic_wp_framed".
      - iIntros "[Hworld [Hpre [Haccess Hcarried]]]".
        iPoseProof (ConcreteAccessNodes.unfold_node_runtime_refinement
          (node := node) store body entry exit ambient tail step Hnamespace
          instantiated runtime formals binders atoms
          with "[$Hworld $Hpre $Haccess]") as "Hopen".
        iEval (unfold Validity.translated_runtime_wp; simpl) in "Hopen".
        iMod "Hopen" as "[Hworld' [Hpost Haccess']]".
        have Hphysical' : Validity.Model.runtime_stmt
            (Validity.Model.runtime_names Γ runtime)
            (Validity.Model.runtime_stack_id Γ runtime) atomic_program =
            None := Hphysical.
        pose proof (@ConcreteChunks.atomic_chunk_runtime_refinement Γ F Δ fuel
          cost exit atomic_node atomic_program atomic_outer atomic_inner
          atomic_step atomic_body_certificate atomic_open_equal
          ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)
          (Runtime.Translation.Assertions.AAnd
            (Runtime.Translation.Assertions.AStack store) body)
          (Runtime.Translation.Assertions.AAnd
            (Runtime.Translation.Assertions.AStack store) body) atomic_trusted
          atomic_body_valid runtime formals binders atoms ambient
          Hatomic_footprint) as Hatomic_wp.
        unfold Validity.translated_runtime_wp in Hatomic_wp.
        simpl in Hatomic_wp.
        rewrite Hphysical' in Hatomic_wp.
        iPoseProof (Hatomic_wp with "[$Hworld' $Hpost $Haccess']") as "Hfin".
        iMod "Hfin" as "[Hworld'' [Hpost'' Haccess'']]".
        iPoseProof (ConcreteAccessNodes.matched_fold_node_runtime_refinement
          (node := fold_node) store body atomic_cert_exit ambient
          (RuntimeAdapter.Atomicity.analysis_open entry) tail fold_Hwf
          litmus_fold_member (proj1 litmus_open_fresh)
          litmus_atomic_cert_exit_open instantiated runtime formals binders
          atoms with "[$Hworld'' $Hpost'' $Haccess'']") as "Hfold".
        iEval (unfold Validity.translated_runtime_wp; simpl) in "Hfold".
        rewrite Hfold_active.
        iMod "Hfold" as "[Hworld3 [Hpost3 Haccess3]]".
        iApply Hcont. iFrame "Hworld3 Hpost3 Haccess3 Hcarried".
    Qed.

  End LitmusUnfoldAtomicFold.

  Lemma aligned_conditional_core_from_ordinary_branch_traces
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel state node store frame condition then_branch else_branch
        then_exit else_exit post view then_certificate else_certificate
        open_equal atomic_equal branch_mask then_derivation else_derivation
        then_mask else_mask}
      (then_aligned : Validity.Certified.certificate_hoare_aligned cost
        then_certificate
        (Validity.Certified.hoare_mask_transport then_derivation eq_refl
          (eq_sym then_mask)))
      (else_aligned : Validity.Certified.certificate_hoare_aligned cost
        else_certificate
        (Validity.Certified.hoare_mask_transport else_derivation eq_refl
          (eq_sym else_mask)))
      (Hthen : aligned_singleton_ordinary_runtime_refinement then_aligned)
      (Helse : aligned_singleton_ordinary_runtime_refinement else_aligned) :
    aligned_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ)
      (pre := Runtime.Translation.Assertions.AAnd
        (Runtime.Translation.Assertions.AStack store) frame)
      (post := post)
      (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state
        (Runtime.IR.TIf node condition then_branch else_branch) then_branch
        else_branch then_exit else_exit view then_certificate else_certificate
        open_equal atomic_equal)
      (Validity.Certified.hoare_mask_transport
        (Validity.Certified.Rules.ConditionalRule node store frame condition
          then_branch else_branch post
          (RuntimeAdapter.Atomicity.analysis_mask state) branch_mask
          then_derivation
          else_derivation) eq_refl
        (Validity.Certified.conditional_analysis_mask state then_exit else_exit
          branch_mask then_mask else_mask)).
  Proof.
    intros stack_in stack_out Hcost Hwf Hlifo Hstack _ runtime formals binders
      atoms ambient Hfootprint.
    simpl in Hlifo. destruct Hlifo as [Hthen_lifo Helse_lifo].
    pose (then_total := aligned_singleton_total_normalization then_aligned
      Hthen_lifo Hwf Hstack).
    pose (else_total := aligned_singleton_total_normalization else_aligned
      Helse_lifo Hwf Hstack).
    pose proof (Hthen stack_in stack_out Hthen_lifo
      (aligned_total_ordinary _ then_total)) as Hthen_refinement.
    pose proof (Helse stack_in stack_out Helse_lifo
      (aligned_total_ordinary _ else_total)) as Helse_refinement.
    destruct (aligned_total_ordinary _ then_total) as
      [then_tree [then_trace aligned_then]].
    destruct (aligned_total_ordinary _ else_total) as
      [else_tree [else_trace aligned_else]].
    simpl in Hthen_refinement, Helse_refinement.
    have Hthen_footprint : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (RuntimeAdapter.singleton_suffix then_certificate)) ⊆ ambient.
    { etrans; last exact Hfootprint.
      apply Validity.Model.runtime_mask_mono. simpl. set_unfold. tauto. }
    have Helse_footprint : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (RuntimeAdapter.singleton_suffix else_certificate)) ⊆ ambient.
    { etrans; last exact Hfootprint.
      apply Validity.Model.runtime_mask_mono. simpl. set_unfold. tauto. }
    pose proof (Hthen_refinement Hcost Hwf Hstack runtime formals binders atoms
      ambient Hthen_footprint) as Hthen_wp.
    pose proof (Helse_refinement Hcost Hwf Hstack runtime formals binders atoms
      ambient Helse_footprint) as Helse_wp.
    rewrite ConcreteOrdinaryTrace.singleton_source_translated_wp in Hthen_wp.
    rewrite ConcreteOrdinaryTrace.singleton_source_translated_wp in Helse_wp.
    eapply ConcreteChunks.aligned_conditional_interpreted_runtime_refinement;
      eauto.
  Qed.

  (** Resource-proof conditional core.  Each branch is supplied through the
      resource translated-runtime interface, so no mask transport or
      compatibility derivation is introduced at the conditional boundary. *)
  Lemma resource_conditional_core_from_resource_branch_refinements
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel state node store frame condition then_branch else_branch
        then_exit else_exit post view then_certificate else_certificate
        open_equal atomic_equal then_derivation else_derivation}
      (then_aligned : Validity.Certified.resource_certificate_hoare_aligned
        cost then_certificate then_derivation)
      (else_aligned : Validity.Certified.resource_certificate_hoare_aligned
        cost else_certificate else_derivation)
      (Hthen : resource_certificate_translated_runtime_refinement
        then_certificate then_derivation)
      (Helse : resource_certificate_translated_runtime_refinement
        else_certificate else_derivation) :
    resource_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ)
      (pre := Runtime.Translation.Assertions.AAnd
        (Runtime.Translation.Assertions.AStack store) frame)
      (post := post)
      (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state
        (Runtime.IR.TIf node condition then_branch else_branch) then_branch
        else_branch then_exit else_exit view then_certificate else_certificate
        open_equal atomic_equal)
      (Validity.Certified.Rules.ResourceConditionalRule node store frame
        condition then_branch else_branch post then_derivation
        else_derivation).
  Proof.
    intros stack_in stack_out Hruntime_cost Hprocedure_cost Hwf Hlifo Hstack
      _ runtime formals binders atoms ambient Hfootprint.
    simpl in Hlifo. destruct Hlifo as [Hthen_lifo Helse_lifo].
    have Hthen_footprint : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint then_certificate) ⊆
        ambient.
    { etrans; last exact Hfootprint.
      apply Validity.Model.runtime_mask_mono. simpl. set_unfold. tauto. }
    have Helse_footprint : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint else_certificate) ⊆
        ambient.
    { etrans; last exact Hfootprint.
      apply Validity.Model.runtime_mask_mono. simpl. set_unfold. tauto. }
    pose proof (Hthen stack_in stack_out Hruntime_cost Hprocedure_cost Hwf
      Hthen_lifo Hstack then_aligned runtime formals binders atoms ambient
      Hthen_footprint) as Hthen_wp.
    pose proof (Helse stack_in stack_out Hruntime_cost Hprocedure_cost Hwf
      Helse_lifo Hstack else_aligned runtime formals binders atoms ambient
      Helse_footprint) as Helse_wp.
    eapply ConcreteChunks.aligned_conditional_interpreted_runtime_refinement;
      eauto.
  Qed.

  Lemma resource_aligned_conditional_core_from_resource_branch_refinements
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel state node store frame condition then_branch else_branch
        then_exit else_exit post view then_certificate else_certificate
        open_equal atomic_equal then_derivation else_derivation}
      (then_aligned : Validity.Certified.resource_certificate_hoare_aligned
        cost then_certificate then_derivation)
      (else_aligned : Validity.Certified.resource_certificate_hoare_aligned
        cost else_certificate else_derivation)
      (Hthen : resource_certificate_translated_runtime_refinement
        then_certificate then_derivation)
      (Helse : resource_certificate_translated_runtime_refinement
        else_certificate else_derivation) :
    resource_aligned_conditional_core_obligation
      (Validity.Certified.ResourceAlignedConditional cost Γ F Δ fuel state
        node store frame condition then_branch else_branch then_exit else_exit
        post view then_certificate else_certificate open_equal atomic_equal
        then_derivation else_derivation then_aligned else_aligned).
  Proof.
    simpl.
    apply resource_conditional_core_from_resource_branch_refinements;
      assumption.
  Qed.

  Lemma resource_conditional_branch_data_core_obligation
      {cost Γ F Δ fuel entry statement then_statement else_statement
        then_exit else_exit pre post view then_certificate else_certificate
        open_equal atomic_equal derivation aligned stack_in join_stack mode
        tail then_tree else_tree lifo Hthen Helse}
      (data : @resource_conditional_branch_data cost Γ F Δ fuel entry
        statement then_statement else_statement then_exit else_exit pre post
        view then_certificate else_certificate open_equal atomic_equal
        derivation aligned stack_in join_stack mode tail then_tree else_tree
        lifo Hthen Helse) :
    resource_conditional_branch_data_semantic data ->
    resource_aligned_conditional_core_obligation aligned.
  Proof.
    induction data; simpl; intros Hsemantic.
    - destruct Hsemantic as [Hthen_refinement Helse_refinement].
      apply resource_aligned_conditional_core_from_resource_branch_refinements;
        assumption.
    - exact (IHdata Hsemantic).
    - exact (IHdata Hsemantic).
    - exact (IHdata Hsemantic).
    - exact (IHdata Hsemantic).
  Qed.

  (** Immediate resource conditional-prefix assembly.  This is the focused
      trace boundary needed by the resource core: the conditional's concrete
      LIFO transition and its erased continuation are kept in lockstep,
      while wrapper elimination is discharged by the resource core
      obligation. *)
  Lemma resource_aligned_conditional_prepend_source_runtime_refinement
      {cost Γ F Δ fuel entry node}
      {store : Runtime.IR.Core.symbolic_store Γ F Δ}
      {frame : Runtime.Translation.Assertions.assertion Γ F Δ}
      {condition then_branch else_branch then_exit else_exit pre post stack_in
        join_stack final_exit}
      (view : Runtime.RegionSyntax.view
        (Runtime.IR.TIf node condition then_branch else_branch) =
        typed_analysis_view.TypedAnalysisView.ViewConditional then_branch
          else_branch)
      (then_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel entry then_branch then_exit)
      (else_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel entry else_branch else_exit)
      (open_equal : RuntimeAdapter.Atomicity.analysis_open then_exit =
        RuntimeAdapter.Atomicity.analysis_open else_exit)
      (atomic_equal : RuntimeAdapter.Atomicity.analysis_in_atomic then_exit =
        RuntimeAdapter.Atomicity.analysis_in_atomic else_exit)
      (derivation : Validity.Certified.Rules.RavenResourceTriple
        pre (Runtime.IR.TIf node condition then_branch else_branch) post)
      (aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry
          (Runtime.IR.TIf node condition then_branch else_branch) then_branch
          else_branch then_exit else_exit view then_certificate else_certificate
          open_equal atomic_equal) derivation)
      (Hcore : resource_aligned_conditional_core_obligation aligned)
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry
          (Runtime.IR.TIf node condition then_branch else_branch) then_branch
          else_branch then_exit else_exit view then_certificate else_certificate
          open_equal atomic_equal) stack_in join_stack)
      (Hruntime_cost : Validity.Model.runtime_cost_model_sound cost)
      (Hprocedure_cost : Validity.Certified.procedure_cost_model_sound cost)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open entry) stack_in)
      (Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open
          (RuntimeAdapter.conditional_join then_exit else_exit))
      (rest : RuntimeAdapter.certificate_suffix cost Γ
        (RuntimeAdapter.conditional_join then_exit else_exit) final_exit)
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset)
      (Henvelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (RuntimeAdapter.SuffixCons
            (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry
              (Runtime.IR.TIf node condition then_branch else_branch)
              then_branch else_branch then_exit else_exit view then_certificate
              else_certificate open_equal atomic_equal) rest)) ⊆ ambient)
      (final : iProp Resources.Σ)
      (Hrest :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms post ∗
         Validity.World.access_stack_interp atoms ambient join_stack) ⊢
        ConcreteOrdinaryTrace.source_translated_wp rest runtime ambient final) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack_in) ⊢
    ConcreteOrdinaryTrace.source_translated_wp
      (RuntimeAdapter.SuffixCons
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry
          (Runtime.IR.TIf node condition then_branch else_branch) then_branch
          else_branch then_exit else_exit view then_certificate else_certificate
          open_equal atomic_equal) rest) runtime ambient final.
  Proof.
    have Hhead_envelope : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry
            (Runtime.IR.TIf node condition then_branch else_branch)
            then_branch else_branch then_exit else_exit view then_certificate
            else_certificate open_equal atomic_equal)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_head_subset. }
    pose proof (resource_aligned_conditional_wrapper_translated_runtime_refinement
      aligned Hcore stack_in join_stack Hruntime_cost Hprocedure_cost Hwf lifo
      Hstack aligned runtime formals binders atoms ambient Hhead_envelope)
      as Hhead.
    eapply ConcreteOrdinaryTrace.translated_head_prepend_source.
    - exact Hopen.
    - exact Hhead.
    - exact Hrest.
  Qed.

  Lemma aligned_trace_conditional_runtime_refinement
      {cost Γ F Δ fuel entry statement then_statement else_statement
        then_exit else_exit exit pre join_assertion post stack_in join_stack
        stack_out view then_certificate else_certificate open_equal atomic_equal
        derivation aligned lifo rest then_tree else_tree rest_tree Hthen Helse
        Hrest}
      (aligned_rest : aligned_net_trace cost Γ F Δ
        (RuntimeAdapter.conditional_join then_exit else_exit) join_assertion
        join_stack exit post stack_out None join_stack
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest) rest_tree rest Hrest)
      (Hcore : aligned_conditional_core_obligation aligned)
      (IHrest : aligned_trace_runtime_refinement aligned_rest)
      (Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open
          (RuntimeAdapter.conditional_join then_exit else_exit)) :
    aligned_trace_runtime_refinement
      (@AlignedTraceConditional cost Γ F Δ fuel entry statement then_statement
        else_statement then_exit else_exit exit pre join_assertion post stack_in
        join_stack stack_out view then_certificate else_certificate open_equal
        atomic_equal derivation aligned lifo rest then_tree else_tree rest_tree
        Hthen Helse Hrest aligned_rest).
  Proof.
    intros Hcost Hwf Hstack runtime formals binders atoms ambient Henvelope.
    have Hjoin_wf : RuntimeAdapter.Atomicity.state_wf
        (RuntimeAdapter.conditional_join then_exit else_exit).
    { exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry
        statement _ Hwf
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
          then_statement else_statement then_exit else_exit view
          then_certificate else_certificate open_equal atomic_equal)). }
    have Hjoin_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open
          (RuntimeAdapter.conditional_join then_exit else_exit)) join_stack.
    { exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
          then_statement else_statement then_exit else_exit view
          then_certificate else_certificate open_equal atomic_equal)
        stack_in join_stack Hwf lifo Hstack). }
    have Hrest_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    pose proof (IHrest Hcost Hjoin_wf Hjoin_stack runtime formals binders atoms
      ambient Hrest_envelope) as Hrest_refinement.
    have Hhead_envelope : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal))
        ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_head_subset. }
    pose proof (aligned_conditional_wrapper_translated_runtime_refinement
      aligned Hcore stack_in join_stack Hcost Hwf lifo Hstack aligned runtime
      formals binders atoms ambient Hhead_envelope) as Hhead_refinement.
    eapply ConcreteOrdinaryTrace.translated_head_prepend_source.
    - exact Hopen.
    - etrans; first exact Hhead_refinement.
      apply Validity.translated_runtime_wp_mono. exact Hrest_refinement.
    - reflexivity.
  Qed.

  (** Trace-aware conditional core, general case: both arms leave [focused]
      open (their normalization is [FocusNetConditionalContinue]-shaped) and
      the shared continuation stays focused too, so its matching close can
      land anywhere downstream.  Unlike
      [aligned_trace_conditional_runtime_refinement], no [Hopen] hypothesis
      is needed: since both arms and the continuation share the exact same
      LIFO stack [focused :: tail], [access_stack_consistent_functional]
      derives [analysis_open entry = analysis_open join] directly from the
      stack shape, rather than assuming it. *)
  Lemma aligned_trace_focused_conditional_continue_runtime_refinement
      {cost Γ F Δ fuel entry statement then_statement else_statement
        then_exit else_exit exit pre join_assertion post focused tail
        stack_out view then_certificate else_certificate open_equal
        atomic_equal derivation aligned lifo rest then_tree else_tree
        rest_tree Hthen Helse Hrest}
      (aligned_rest : aligned_net_trace cost Γ F Δ
        (RuntimeAdapter.conditional_join then_exit else_exit) join_assertion
        (focused :: tail) exit post stack_out (Some focused) tail
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest) rest_tree rest Hrest)
      (Hcore : aligned_conditional_core_obligation aligned)
      (IHrest : aligned_trace_runtime_refinement aligned_rest) :
    aligned_trace_runtime_refinement
      (@AlignedTraceFocusedConditionalContinue cost Γ F Δ fuel entry statement
        then_statement else_statement then_exit else_exit exit pre
        join_assertion post focused tail stack_out view then_certificate
        else_certificate open_equal atomic_equal derivation aligned lifo rest
        then_tree else_tree rest_tree Hthen Helse Hrest aligned_rest).
  Proof.
    intros Hcost Hwf Hstack runtime formals binders atoms ambient Henvelope.
    have Hjoin_wf : RuntimeAdapter.Atomicity.state_wf
        (RuntimeAdapter.conditional_join then_exit else_exit).
    { exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry
        statement _ Hwf
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
          then_statement else_statement then_exit else_exit view
          then_certificate else_certificate open_equal atomic_equal)). }
    have Hjoin_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open
          (RuntimeAdapter.conditional_join then_exit else_exit))
        (focused :: tail).
    { exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
          then_statement else_statement then_exit else_exit view
          then_certificate else_certificate open_equal atomic_equal)
        (focused :: tail) (focused :: tail) Hwf lifo Hstack). }
    have Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open
          (RuntimeAdapter.conditional_join then_exit else_exit).
    { eapply RuntimeAdapter.Atomicity.access_stack_consistent_functional.
      - exact Hstack.
      - exact Hjoin_stack. }
    have Hrest_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    pose proof (IHrest Hcost Hjoin_wf Hjoin_stack runtime formals binders atoms
      ambient Hrest_envelope) as Hrest_refinement.
    have Hhead_envelope : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry statement
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal))
        ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_head_subset. }
    pose proof (aligned_conditional_wrapper_translated_runtime_refinement
      aligned Hcore (focused :: tail) (focused :: tail) Hcost Hwf lifo Hstack
      aligned runtime formals binders atoms ambient Hhead_envelope)
      as Hhead_refinement.
    eapply ConcreteOrdinaryTrace.translated_head_prepend_source.
    - exact Hopen.
    - etrans; first exact Hhead_refinement.
      apply Validity.translated_runtime_wp_mono. exact Hrest_refinement.
    - reflexivity.
  Qed.

  (** Final Phase 7 reification induction.  Its proof is intentionally left
      as one visible obligation while the constructor lemmas are assembled:
      ordinary conditionals use the preceding translated-certificate
      boundary and a shared continuation; focused conditionals split into
      preserving and branch-local-close cases. *)
  Theorem aligned_trace_runtime_refinement_complete
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source tree
        suffix trace}
      (aligned_trace : @aligned_net_trace cost Γ F Δ entry pre stack_in exit
        post stack_out mode tail source tree suffix trace) :
    aligned_trace_runtime_refinement aligned_trace.
  Proof.
  Admitted.

  (** Closed adequacy consumes the empty-stack, ordinary-mode specialization
      of the assertion-aware relation.  Keeping the certificate [source]
      explicit avoids imposing syntactic associativity on translated
      sequences. *)
  Definition closed_aligned_trace_runtime_refinement
      {cost Γ F Δ entry pre exit post source tree suffix trace}
      (aligned_trace : @aligned_net_trace cost Γ F Δ entry pre [] exit post []
        None [] source tree suffix trace) : Prop :=
    aligned_trace_runtime_refinement aligned_trace.

  (** Runtime-only half of ordinary reification.  The structured CPS theorem
      already proves all assertion and resource transport along a normalized
      trace.  What remains is solely that executing that trace refines the
      concrete translation of its source suffix.  This judgment is restricted
      to ordinary mode: focused execution must retain the explicit Iris mask
      bracket through its first matching close, and is handled separately. *)
  Definition ordinary_trace_cps_source_refinement
      {cost Γ F Δ entry pre stack_in exit post stack_out source tree suffix trace}
      (_ : @aligned_net_trace cost Γ F Δ entry pre stack_in exit post
        stack_out None stack_in source tree suffix trace) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (final : iProp Resources.Σ),
    Validity.Model.runtime_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    trace_runtime_cps_wp trace runtime ambient (fun _ => final) ⊢
      ConcreteOrdinaryTrace.source_translated_wp source runtime ambient final.

  (** Runtime-only first-close judgment for focused execution.  The outer
      Iris mask is reconstructed from the Raven open-set stored in the access
      marker.  Both mask changes stay explicit until the matching close, so
      this statement does not conflate Raven masks with Iris masks or execute
      the focused physical fragment at the enclosing mask. *)
  (** Resource-native focused source-reification judgments.  These mirror the
      indexed compatibility layer below, but obtain Raven masks solely from
      the analyzer state carried by the resource lockstep trace. *)
  Definition resource_ordinary_trace_cps_source_refinement
      {cost Γ F Δ entry pre stack exit post stack_out source tree suffix trace}
      (_ : @resource_aligned_net_trace cost Γ F Δ entry pre stack exit post
        stack_out None stack source tree suffix trace) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (final : iProp Resources.Σ),
    Validity.Model.runtime_cost_model_sound cost ->
    Validity.Certified.procedure_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    trace_runtime_cps_wp trace runtime ambient (fun _ => final) ⊢
      ConcreteOrdinaryTrace.source_translated_wp source runtime ambient final.

  (** Assertion-aware handoff for a trace that may leave its current focus
      open.  The continuation is an Iris proposition consumed at the trace's
      actual exit mask; consequently this judgment never moves unmatched
      invariant-opening updates across arbitrary continuation code. *)
  Definition resource_pending_open_trace_refinement
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source tree
        suffix trace}
      (_ : @resource_aligned_net_trace cost Γ F Δ entry pre stack_in exit post
        stack_out mode tail source tree suffix trace) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (continuation : mask_cont),
    Validity.Model.runtime_cost_model_sound cost ->
    Validity.Certified.procedure_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    ((Validity.global_world_context atoms ∗
      Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms post ∗
      Validity.World.access_stack_interp atoms ambient stack_out) ⊢
      continuation (Validity.Model.active_runtime_mask ambient exit)) ->
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack_in) ⊢
    trace_runtime_cps_wp trace runtime ambient continuation.

  Lemma resource_pending_open_trace_refinement_complete
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source tree
        suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        stack_in exit post stack_out mode tail source tree suffix trace) :
    resource_pending_open_trace_refinement aligned_trace.
  Proof.
    intros runtime ambient formals binders atoms continuation Hruntime_cost
      Hprocedure_cost Hwf _ Henvelope Hcont.
    pose proof (resource_aligned_net_trace_source_eq aligned_trace) as Hsource.
    subst source.
    pose proof (Normalized.resource_aligned_suffix_iris_wp_valid suffix
      Hprocedure_cost Hwf runtime formals binders atoms ambient Henvelope
      (continuation (Validity.Model.active_runtime_mask ambient exit)) Hcont)
      as Hlogical.
    rewrite <- (Normalized.trace_iris_wp_is_suffix_iris_wp trace runtime
      ambient _) in Hlogical.
    iIntros "Hresources".
    iPoseProof (Hlogical with "Hresources") as "Hlogical".
    iPoseProof (trace_iris_runtime_cps_refinement trace runtime ambient
      (continuation (Validity.Model.active_runtime_mask ambient exit))
      (trace_runtime_trusted_of_suffix trace
        (resource_aligned_suffix_runtime_trusted suffix))
      with "Hlogical") as "Hruntime".
    iApply (trace_runtime_cps_wp_terminal_mono with "Hruntime").
    reflexivity.
  Qed.

  Definition resource_focused_close_trace_cps_source_refinement
      {cost Γ F Δ invariant outer tail entry pre closed post source tree suffix
        trace}
      (_ : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) closed post tail
        (Some (invariant, outer)) tail source tree suffix trace) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (final : iProp Resources.Σ),
    Validity.Model.runtime_cost_model_sound cost ->
    Validity.Certified.procedure_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry)
      ((invariant, outer) :: tail) ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    let outer_mask := Validity.Model.enabled_runtime_mask ambient outer in
    ((|={outer_mask, Validity.Model.active_runtime_mask ambient entry}=>
       trace_runtime_cps_wp trace runtime ambient
         (fun _ =>
           |={Validity.Model.active_runtime_mask ambient closed, outer_mask}=>
             final)) ⊢
      Validity.runtime_option_wp outer_mask outer_mask
        (ConcreteOrdinaryTrace.source_runtime source runtime) final)%I.

  Definition resource_focused_closing_trace_cps_source_refinement
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace)
      (_ : resource_aligned_focused_close_split aligned_trace) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (final : iProp Resources.Σ),
    Validity.Model.runtime_cost_model_sound cost ->
    Validity.Certified.procedure_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry)
      ((invariant, outer) :: tail) ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    let outer_mask := Validity.Model.enabled_runtime_mask ambient outer in
    ((|={outer_mask, Validity.Model.active_runtime_mask ambient entry}=>
       trace_runtime_cps_wp trace runtime ambient (fun _ => final)) ⊢
      Validity.runtime_option_wp outer_mask
        (Validity.Model.active_runtime_mask ambient exit)
        (ConcreteOrdinaryTrace.source_runtime source runtime) final)%I.

  Definition resource_focused_inner_trace_cps_source_refinement
      {cost Γ F Δ focused tail entry pre closed post source tree suffix trace}
      (_ : @resource_aligned_net_trace cost Γ F Δ entry pre
        (focused :: tail) closed post tail (Some focused) tail source tree
        suffix trace) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (final : iProp Resources.Σ),
    Validity.Model.runtime_cost_model_sound cost ->
    Validity.Certified.procedure_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) (focused :: tail) ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    trace_runtime_cps_wp trace runtime ambient (fun _ => final) ⊢
      ConcreteOrdinaryTrace.source_translated_wp source runtime ambient final.

  Definition resource_focused_open_trace_cps_source_refinement
      {cost Γ F Δ focused tail entry pre exit post stack_out source tree suffix
        trace}
      (_ : @resource_aligned_net_trace cost Γ F Δ entry pre
        (focused :: tail) exit post stack_out (Some focused) tail source tree
        suffix trace) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (final : iProp Resources.Σ),
    Validity.Model.runtime_cost_model_sound cost ->
    Validity.Certified.procedure_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) (focused :: tail) ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    trace_runtime_cps_wp trace runtime ambient (fun _ => final) ⊢
      ConcreteOrdinaryTrace.source_translated_wp source runtime ambient final.

  Inductive resource_focused_semantic_result
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source tree suffix
        trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace) : Type :=
    | ResourceFocusedStillOpen
        (_ : resource_pending_open_trace_refinement aligned_trace) :
        resource_focused_semantic_result aligned_trace
    | ResourceFocusedLocallyClosing
        (split : resource_aligned_focused_close_split aligned_trace)
        (_ : resource_focused_closing_trace_cps_source_refinement
          aligned_trace split) :
        resource_focused_semantic_result aligned_trace.

  Inductive resource_ordinary_semantic_result
      {cost Γ F Δ entry pre stack_in exit post stack_out source tree suffix
        trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        stack_in exit post stack_out None stack_in source tree suffix trace) :
      Type :=
    | ResourceOrdinaryBalanced
        (_ : resource_aligned_trace_runtime_refinement aligned_trace) :
        resource_ordinary_semantic_result aligned_trace
    | ResourceOrdinaryPendingOpen
        (_ : resource_pending_open_trace_refinement aligned_trace) :
        resource_ordinary_semantic_result aligned_trace.

  Lemma resource_focused_semantic_result_still_open
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source tree
        suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace) :
    resource_focused_semantic_result aligned_trace.
  Proof.
    constructor 1. exact (resource_pending_open_trace_refinement_complete
      aligned_trace).
  Qed.

  Lemma resource_ordinary_semantic_result_pending
      {cost Γ F Δ entry pre stack_in exit post stack_out source tree suffix
        trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        stack_in exit post stack_out None stack_in source tree suffix trace) :
    resource_ordinary_semantic_result aligned_trace.
  Proof.
    constructor 2. exact (resource_pending_open_trace_refinement_complete
      aligned_trace).
  Qed.

  Definition resource_assertion_focused_closing_refinement
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace)
      (_ : resource_aligned_focused_close_split aligned_trace) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset),
    Validity.Model.runtime_cost_model_sound cost ->
    Validity.Certified.procedure_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry)
      ((invariant, outer) :: tail) ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    forall (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ) (atoms : Runtime.Core.atom_env),
    let outer_mask := Validity.Model.enabled_runtime_mask ambient outer in
    ((|={outer_mask, Validity.Model.active_runtime_mask ambient entry}=>
       Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms pre ∗
       Validity.World.access_stack_interp atoms ambient
         ((invariant, outer) :: tail)) ⊢
     Validity.runtime_option_wp outer_mask
       (Validity.Model.active_runtime_mask ambient exit)
       (ConcreteOrdinaryTrace.source_runtime source runtime)
       (Validity.global_world_context atoms ∗
        Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
          runtime formals binders atoms post ∗
        Validity.World.access_stack_interp atoms ambient stack_out))%I.

  Lemma resource_assertion_focused_closing_from_runtime
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace)
      (split : resource_aligned_focused_close_split aligned_trace) :
    resource_focused_closing_trace_cps_source_refinement aligned_trace split ->
    resource_assertion_focused_closing_refinement aligned_trace split.
  Proof.
    intros Hclosing runtime ambient Hruntime_cost Hprocedure_cost Hwf Hstack
      Henvelope formals binders atoms. simpl.
    pose proof (Hclosing runtime ambient
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       Validity.World.access_stack_interp atoms ambient stack_out)%I
      Hruntime_cost Hprocedure_cost Hwf Hstack Henvelope) as Hclose.
    iIntros "Hresources". iApply Hclose.
    iMod "Hresources" as "Hresources". iModIntro.
    iApply (resource_pending_open_trace_refinement_complete aligned_trace
      runtime ambient formals binders atoms
      (fun _ =>
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms post ∗
         Validity.World.access_stack_interp atoms ambient stack_out)%I)
      Hruntime_cost Hprocedure_cost Hwf Hstack Henvelope).
    - reflexivity.
    - iExact "Hresources".
  Qed.

  Inductive resource_assertion_focused_semantic_result
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source tree
        suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace) : Type :=
    | ResourceAssertionFocusedStillOpen
        (_ : resource_pending_open_trace_refinement aligned_trace) :
        resource_assertion_focused_semantic_result aligned_trace
    | ResourceAssertionFocusedLocallyClosing
        (split : resource_aligned_focused_close_split aligned_trace)
        (_ : resource_assertion_focused_closing_refinement aligned_trace split) :
        resource_assertion_focused_semantic_result aligned_trace.

  Lemma resource_aligned_trace_runtime_refinement_from_ordinary_cps
      {cost Γ F Δ entry pre stack exit post stack_out source tree suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre stack
        exit post stack_out None stack source tree suffix trace) :
    resource_ordinary_trace_cps_source_refinement aligned_trace ->
    resource_aligned_trace_runtime_refinement aligned_trace.
  Proof.
    intros Hsource Hruntime_cost Hprocedure_cost Hwf Hstack runtime formals
      binders atoms ambient Henvelope.
    iIntros "Hresources".
    iApply (Hsource runtime ambient _ Hruntime_cost Hprocedure_cost Hwf Hstack
      Henvelope).
    iApply (resource_pending_open_trace_refinement_complete aligned_trace
      runtime ambient formals binders atoms
      (fun _ =>
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms post ∗
         Validity.World.access_stack_interp atoms ambient stack_out)%I)
      Hruntime_cost Hprocedure_cost Hwf Hstack Henvelope).
    - reflexivity.
    - iExact "Hresources".
  Qed.

  Lemma resource_focused_open_done_cps_source
      {cost Γ F Δ state assertion focused tail} :
    resource_focused_open_trace_cps_source_refinement
      (@ResourceAlignedTraceDoneFocused cost Γ F Δ state assertion focused
        tail).
  Proof.
    intros runtime ambient final _ _ _ _ _. simpl.
    unfold ConcreteOrdinaryTrace.source_translated_wp. simpl.
    iIntros "Hfinal". iModIntro. iExact "Hfinal".
  Qed.

  Lemma resource_pending_open_done_focused
      {cost Γ F Δ state assertion focused tail} :
    resource_pending_open_trace_refinement
      (@ResourceAlignedTraceDoneFocused cost Γ F Δ state assertion focused
        tail).
  Proof.
    intros runtime ambient formals binders atoms continuation _ _ _ _ _ Hcont.
    simpl. iIntros "Hresources". iApply Hcont. iExact "Hresources".
  Qed.

  Lemma resource_focused_done_semantic_result
      {cost Γ F Δ state assertion invariant outer tail} :
    resource_focused_semantic_result
      (@ResourceAlignedTraceDoneFocused cost Γ F Δ state assertion
        (invariant, outer) tail).
  Proof. constructor 1. apply resource_pending_open_done_focused. Qed.

  Lemma resource_ordinary_done_cps_source
      {cost Γ F Δ state assertion stack} :
    resource_ordinary_trace_cps_source_refinement
      (@ResourceAlignedTraceDone cost Γ F Δ state assertion stack).
  Proof.
    intros runtime ambient final _ _ _ _ _. simpl.
    unfold ConcreteOrdinaryTrace.source_translated_wp. simpl.
    iIntros "Hfinal". iModIntro. iExact "Hfinal".
  Qed.

  Lemma resource_focused_close_direct_done_inner_source
      {cost Γ F Δ fuel entry statement closed pre closed_assertion invariant
        outer tail certificate derivation aligned lifo closing}
      (Hclosing : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        closed ((invariant, outer) :: tail) tail certificate closing)
      (close_ok : RuntimeAdapter.Payload.closes (invariant, outer) tail entry
        closed closing) :
    resource_focused_inner_trace_cps_source_refinement
      (@ResourceAlignedTraceFocusedClose cost Γ F Δ fuel entry statement closed
        closed pre closed_assertion closed_assertion (invariant, outer) tail
        tail certificate derivation aligned lifo
        (Validity.ResourceAlignedOperationalDone closed closed_assertion tail)
        closing Hclosing close_ok
        (@RuntimeAdapter.NetOrdinary tail tail closed closed
          (RuntimeAdapter.Slice.ExecDone closed tail))
        (@RuntimeAdapter.TraceDoneNet cost Γ closed tail)
        (@ResourceAlignedTraceDone cost Γ F Δ closed closed_assertion tail)).
  Proof.
    intros runtime ambient final _ _ _ _ _. simpl.
    dependent destruction Hclosing.
    all: try (exfalso;
      repeat match goal with
      | H : @eq (list _) _ _ |- _ =>
          pose proof (f_equal (@List.length _) H); clear H
      end; simpl in *; lia).
    destruct statement; simpl in view; try discriminate.
    inversion view; subst. simpl.
    iIntros "Hclose". iMod "Hclose". iModIntro. iExact "Hclose".
  Qed.

  Lemma resource_focused_close_direct_done_cps_source
      {cost Γ F Δ fuel entry statement closed pre closed_assertion invariant
        outer tail certificate derivation aligned lifo closing}
      (Hclosing : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        closed ((invariant, outer) :: tail) tail certificate closing)
      (close_ok : RuntimeAdapter.Payload.closes (invariant, outer) tail entry
        closed closing) :
    resource_focused_close_trace_cps_source_refinement
      (@ResourceAlignedTraceFocusedClose cost Γ F Δ fuel entry statement closed
        closed pre closed_assertion closed_assertion (invariant, outer) tail
        tail certificate derivation aligned lifo
        (Validity.ResourceAlignedOperationalDone closed closed_assertion tail)
        closing Hclosing close_ok
        (@RuntimeAdapter.NetOrdinary tail tail closed closed
          (RuntimeAdapter.Slice.ExecDone closed tail))
        (@RuntimeAdapter.TraceDoneNet cost Γ closed tail)
        (@ResourceAlignedTraceDone cost Γ F Δ closed closed_assertion tail)).
  Proof.
    intros runtime ambient final _ _ _ _ _. simpl.
    dependent destruction Hclosing.
    all: try (exfalso;
      repeat match goal with
      | H : @eq (list _) _ _ |- _ =>
          pose proof (f_equal (@List.length _) H); clear H
      end; simpl in *; lia).
    destruct statement; simpl in view; try discriminate.
    inversion view; subst. simpl.
    iIntros "Hclose". iMod "Hclose". iMod "Hclose".
    iMod "Hclose". iModIntro. iExact "Hclose".
  Qed.

  Lemma resource_focused_closing_direct_close_cps_source
      {cost Γ F Δ fuel entry statement closed exit pre closed_assertion post
        invariant outer tail stack_out certificate derivation aligned lifo
        rest closing rest_tree Hrest}
      (Hclosing : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        closed ((invariant, outer) :: tail) tail certificate closing)
      (close_ok : RuntimeAdapter.Payload.closes (invariant, outer) tail entry
        closed closing)
      (aligned_rest : resource_aligned_net_trace cost Γ F Δ closed
        closed_assertion tail exit post stack_out None tail
        (resource_certificate_suffix_of_operational_suffix rest) rest_tree rest
        Hrest) :
    resource_ordinary_trace_cps_source_refinement aligned_rest ->
    resource_focused_closing_trace_cps_source_refinement
      (@ResourceAlignedTraceFocusedClose cost Γ F Δ fuel entry statement closed
        exit pre closed_assertion post (invariant, outer) tail stack_out
        certificate derivation aligned lifo rest closing Hclosing close_ok
        rest_tree Hrest aligned_rest)
      (resource_aligned_focused_close_split_here Hclosing close_ok
        aligned_rest).
  Proof.
    intros IH runtime ambient final Hruntime_cost Hprocedure_cost Hwf Hstack
      Henvelope. cbn.
    have Hclosed_wf : RuntimeAdapter.Atomicity.state_wf closed :=
      RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry statement
        closed Hwf certificate.
    have Hclosed_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open closed) tail :=
      RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
        certificate ((invariant, outer) :: tail) tail Hwf lifo Hstack.
    have Hrest_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (resource_certificate_suffix_of_operational_suffix rest)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    pose proof (IH runtime ambient final Hruntime_cost Hprocedure_cost
      Hclosed_wf Hclosed_stack Hrest_envelope) as IHsource.
    dependent destruction Hclosing.
    all: try (exfalso;
      repeat match goal with
      | H : @eq (list _) _ _ |- _ =>
          pose proof (f_equal (@List.length _) H); clear H
      end; simpl in *; lia).
    destruct statement; simpl in view; try discriminate.
    inversion view; subst. simpl.
    have Hremaining : RuntimeAdapter.Atomicity.analysis_open entry ∖
        {[invariant]} = outer.
    { rewrite opened. set_solver. }
    have Hclosed_active : Validity.Model.active_runtime_mask ambient
        (RuntimeAdapter.Atomicity.fold_invariant invariant entry) =
        Validity.Model.enabled_runtime_mask ambient outer.
    { destruct (RuntimeAdapter.Atomicity.fold_open_invariant invariant entry
        member) as [_ Hfold_open].
      unfold Validity.Model.active_runtime_mask.
      rewrite Hfold_open Hremaining. reflexivity. }
    unfold ConcreteOrdinaryTrace.source_translated_wp in IHsource.
    rewrite Hclosed_active in IHsource.
    remember (ConcreteOrdinaryTrace.source_runtime
      (resource_certificate_suffix_of_operational_suffix rest) runtime)
      as rest_runtime.
    destruct rest_runtime as [rest_statement|]; simpl in *.
    - etrans; last exact (Validity.runtime_option_wp_fupd_roundtrip
        (Validity.Model.enabled_runtime_mask ambient outer)
        (Validity.Model.active_runtime_mask ambient entry)
        (Validity.Model.active_runtime_mask ambient exit)
        (Some rest_statement) final).
      iIntros "Hclose".
      iApply (fupd_mono with "Hclose"). iIntros "Hclose".
      rewrite <- Hclosed_active.
      iApply (fupd_mono with "Hclose"). iIntros "Hclose".
      rewrite Hclosed_active. iApply IHsource. iExact "Hclose".
    - etrans; last exact (Validity.runtime_option_wp_fupd_roundtrip
        (Validity.Model.enabled_runtime_mask ambient outer)
        (Validity.Model.active_runtime_mask ambient entry)
        (Validity.Model.active_runtime_mask ambient exit) None final).
      iIntros "Hclose".
      iApply (fupd_mono with "Hclose"). iIntros "Hclose".
      rewrite <- Hclosed_active.
      iApply (fupd_mono with "Hclose"). iIntros "Hclose".
      rewrite Hclosed_active. iApply IHsource. iExact "Hclose".
  Qed.

  Lemma resource_assertion_focused_closing_direct_close
      {cost Γ F Δ fuel entry statement closed exit pre closed_assertion post
        invariant outer tail stack_out certificate derivation aligned lifo
        rest closing rest_tree Hrest}
      (Hclosing : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        closed ((invariant, outer) :: tail) tail certificate closing)
      (close_ok : RuntimeAdapter.Payload.closes (invariant, outer) tail entry
        closed closing)
      (aligned_rest : resource_aligned_net_trace cost Γ F Δ closed
        closed_assertion tail exit post stack_out None tail
        (resource_certificate_suffix_of_operational_suffix rest) rest_tree rest
        Hrest)
      (IHrest : resource_ordinary_trace_cps_source_refinement aligned_rest) :
    resource_assertion_focused_closing_refinement
      (@ResourceAlignedTraceFocusedClose cost Γ F Δ fuel entry statement
        closed exit pre closed_assertion post (invariant, outer) tail stack_out
        certificate derivation aligned lifo rest closing Hclosing close_ok
        rest_tree Hrest aligned_rest)
      (resource_aligned_focused_close_split_here Hclosing close_ok aligned_rest).
  Proof.
    apply resource_assertion_focused_closing_from_runtime.
    exact (resource_focused_closing_direct_close_cps_source Hclosing close_ok
      aligned_rest IHrest).
  Qed.

  Definition focused_close_trace_cps_source_refinement
      {cost Γ F Δ invariant outer tail entry pre closed post source tree suffix
        trace}
      (_ : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) closed post tail
        (Some (invariant, outer)) tail source tree suffix trace) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (final : iProp Resources.Σ),
    Validity.Model.runtime_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry)
      ((invariant, outer) :: tail) ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    let outer_mask := Validity.Model.enabled_runtime_mask ambient outer in
    ((|={outer_mask, Validity.Model.active_runtime_mask ambient entry}=>
       trace_runtime_cps_wp trace runtime ambient
         (fun _ =>
           |={Validity.Model.active_runtime_mask ambient closed, outer_mask}=>
             final)) ⊢
      Validity.runtime_option_wp outer_mask outer_mask
        (ConcreteOrdinaryTrace.source_runtime source runtime) final)%I.

  (** General first-close judgment.  Unlike
      [focused_close_trace_cps_source_refinement], the trace may contain an
      arbitrary ordinary suffix after its first matching close.  That suffix
      starts only after the close has restored [outer_mask], and the result
      may therefore finish at [exit]'s active mask without assuming that the
      post-close code is atomic.  The accompanying
      [aligned_focused_close_split] is the structural witness used by the
      proof to keep the atomic prefix separate from that suffix. *)
  Definition focused_closing_trace_cps_source_refinement
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      (aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace)
      (_ : aligned_focused_close_split aligned_trace) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (final : iProp Resources.Σ),
    Validity.Model.runtime_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry)
      ((invariant, outer) :: tail) ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    let outer_mask := Validity.Model.enabled_runtime_mask ambient outer in
    ((|={outer_mask, Validity.Model.active_runtime_mask ambient entry}=>
       trace_runtime_cps_wp trace runtime ambient (fun _ => final)) ⊢
      Validity.runtime_option_wp outer_mask
        (Validity.Model.active_runtime_mask ambient exit)
        (ConcreteOrdinaryTrace.source_runtime source runtime) final)%I.

  (** Internal induction judgment while the focused slice is still at its
      active masks.  It composes through preserving prefixes; the enclosing
      Iris-mask transition is applied only after the complete first-close
      slice has been assembled. *)
  Definition focused_inner_trace_cps_source_refinement
      {cost Γ F Δ invariant outer tail entry pre closed post source tree suffix
        trace}
      (_ : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) closed post tail
        (Some (invariant, outer)) tail source tree suffix trace) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (final : iProp Resources.Σ),
    Validity.Model.runtime_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry)
      ((invariant, outer) :: tail) ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    trace_runtime_cps_wp trace runtime ambient (fun _ => final) ⊢
      ConcreteOrdinaryTrace.source_translated_wp source runtime ambient final.

  (** Runtime-only handoff for a focused trace which has not closed its
      current marker.  This is the recursive invariant for the linear
      preserving spine ([DoneFocused]/[FocusedPrefix]); it is deliberately
      not claimed as the general focused IH.  Nested access must classify its
      child's close/open outcome, and focused conditionals additionally need
      interpreted assertion and access-stack resources to relate logical arm
      selection to the physical guard. *)
  Definition focused_open_trace_cps_source_refinement
      {cost Γ F Δ focused tail entry pre exit post stack_out source tree suffix
        trace}
      (_ : @aligned_net_trace cost Γ F Δ entry pre
        (focused :: tail) exit post stack_out (Some focused) tail source tree
        suffix trace) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (final : iProp Resources.Σ),
    Validity.Model.runtime_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
      RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry)
      (focused :: tail) ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    trace_runtime_cps_wp trace runtime ambient (fun _ => final) ⊢
      ConcreteOrdinaryTrace.source_translated_wp source runtime ambient final.

  (** Phase 7 Part-B candidate judgment.  The constructor-complete skeleton
      below established that this uniform type is accepted by the dependent
      induction principle.  Part C subsequently showed that the semantic
      judgment is intentionally too strong at [AlignedTraceClose]: flattening
      there would eliminate a close-induced mask update in front of an
      arbitrary continuation.  The proved base and preserving-prefix cases
      remain useful, but the final induction must pair ordinary refinement
      with the explicit focused first-close handoff rather than prove this
      candidate for every constructor. *)
  Definition aligned_trace_cps_source_refinement
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source tree
        suffix trace}
      (_ : @aligned_net_trace cost Γ F Δ entry pre stack_in exit post
        stack_out mode tail source tree suffix trace) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (final : iProp Resources.Σ),
    Validity.Model.runtime_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆ ambient ->
    trace_runtime_cps_wp trace runtime ambient (fun _ => final) ⊢
      ConcreteOrdinaryTrace.source_translated_wp source runtime ambient final.

  Lemma focused_fold_cps_source_runtime_refinement
      {cost Γ fuel entry node invariant arguments outer}
      (view : Runtime.RegionSyntax.view
        (Runtime.IR.TFold node invariant arguments) =
        typed_analysis_view.TypedAnalysisView.ViewFold invariant)
      (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (final : iProp Resources.Σ) :
    let closed := RuntimeAdapter.Atomicity.fold_invariant invariant entry in
    let certificate := RuntimeAdapter.Atomicity.CertFold cost Γ fuel entry
      (Runtime.IR.TFold node invariant arguments) invariant view in
    let outer_mask := Validity.Model.enabled_runtime_mask ambient outer in
    ((|={outer_mask, Validity.Model.active_runtime_mask ambient entry}=>
        Validity.aligned_runtime_region_wp certificate runtime ambient
          (|={Validity.Model.active_runtime_mask ambient closed, outer_mask}=>
            final)) ⊢
      Validity.runtime_option_wp outer_mask outer_mask
        (Validity.certificate_runtime_statement certificate runtime) final)%I.
  Proof.
    simpl. iIntros "Hclose". iMod "Hclose". iMod "Hclose".
    iMod "Hclose". iModIntro. iExact "Hclose".
  Qed.

  Lemma focused_close_direct_done_cps_source
      {cost Γ F Δ fuel entry statement closed pre closed_assertion invariant
        outer tail certificate derivation aligned lifo closing}
      (Hclosing : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        closed ((invariant, outer) :: tail) tail certificate closing)
      (close_ok : RuntimeAdapter.Payload.closes (invariant, outer) tail entry
        closed closing) :
    focused_close_trace_cps_source_refinement
      (@AlignedTraceFocusedClose cost Γ F Δ fuel entry statement closed closed
        pre closed_assertion closed_assertion (invariant, outer) tail tail
        certificate derivation aligned lifo
        (Validity.AlignedOperationalDone closed closed_assertion tail) closing
        Hclosing close_ok
        (@RuntimeAdapter.NetOrdinary tail tail closed closed
          (RuntimeAdapter.Slice.ExecDone closed tail))
        (@RuntimeAdapter.TraceDoneNet cost Γ closed tail)
        (@AlignedTraceDone cost Γ F Δ closed closed_assertion tail)).
  Proof.
    intros runtime ambient final _ _ _ _. simpl.
    dependent destruction Hclosing.
    all: try (exfalso;
      repeat match goal with
      | H : @eq (list _) _ _ |- _ =>
          pose proof (f_equal (@List.length _) H); clear H
      end; simpl in *; lia).
    destruct statement; simpl in view; try discriminate.
    inversion view; subst. simpl.
    iIntros "Hclose". iMod "Hclose". iMod "Hclose".
    iMod "Hclose". iModIntro. iExact "Hclose".
  Qed.

  Lemma focused_closing_direct_close_cps_source
      {cost Γ F Δ fuel entry statement closed exit pre closed_assertion post
        invariant outer tail stack_out certificate derivation aligned lifo
        rest closing rest_tree Hrest}
      (Hclosing : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        closed ((invariant, outer) :: tail) tail certificate closing)
      (close_ok : RuntimeAdapter.Payload.closes (invariant, outer) tail entry
        closed closing)
      (aligned_rest : aligned_net_trace cost Γ F Δ closed closed_assertion tail
        exit post stack_out None tail
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest) rest_tree rest Hrest) :
    aligned_trace_cps_source_refinement aligned_rest ->
    focused_closing_trace_cps_source_refinement
      (@AlignedTraceFocusedClose cost Γ F Δ fuel entry statement closed exit pre
        closed_assertion post (invariant, outer) tail stack_out certificate
        derivation aligned lifo rest closing Hclosing close_ok rest_tree Hrest
        aligned_rest)
      (aligned_focused_close_split_here Hclosing close_ok aligned_rest).
  Proof.
    intros IH runtime ambient final Hcost Hwf Hstack Henvelope. cbn.
    have Hclosed_wf : RuntimeAdapter.Atomicity.state_wf closed :=
      RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry statement
        closed Hwf certificate.
    have Hclosed_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open closed) tail :=
      RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
        certificate ((invariant, outer) :: tail) tail Hwf lifo Hstack.
    have Hrest_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest)) ⊆ ambient.
    { etrans; last exact Henvelope.
      apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    pose proof (IH runtime ambient final Hcost Hclosed_wf Hclosed_stack
      Hrest_envelope) as IHsource.
    dependent destruction Hclosing.
    all: try (exfalso;
      repeat match goal with
      | H : @eq (list _) _ _ |- _ =>
          pose proof (f_equal (@List.length _) H); clear H
      end; simpl in *; lia).
    destruct statement; simpl in view; try discriminate.
    inversion view; subst. simpl.
    have Hremaining : RuntimeAdapter.Atomicity.analysis_open entry ∖
        {[invariant]} = outer.
    { rewrite opened. set_solver. }
    have Hclosed_active : Validity.Model.active_runtime_mask ambient
        (RuntimeAdapter.Atomicity.fold_invariant invariant entry) =
        Validity.Model.enabled_runtime_mask ambient outer.
    { destruct (RuntimeAdapter.Atomicity.fold_open_invariant invariant entry
        member) as [_ Hfold_open].
      unfold Validity.Model.active_runtime_mask.
      rewrite Hfold_open Hremaining. reflexivity. }
    unfold ConcreteOrdinaryTrace.source_translated_wp in IHsource.
    rewrite Hclosed_active in IHsource.
    remember (ConcreteOrdinaryTrace.source_runtime
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
        rest) runtime) as rest_runtime.
    destruct rest_runtime as [rest_statement|]; simpl in *.
    - etrans; last exact (Validity.runtime_option_wp_fupd_roundtrip
        (Validity.Model.enabled_runtime_mask ambient outer)
        (Validity.Model.active_runtime_mask ambient entry)
        (Validity.Model.active_runtime_mask ambient exit)
        (Some rest_statement) final).
      iIntros "Hclose".
      iApply (fupd_mono with "Hclose"). iIntros "Hclose".
      rewrite <- Hclosed_active.
      iApply (fupd_mono with "Hclose"). iIntros "Hclose".
      rewrite Hclosed_active.
      iApply IHsource. iExact "Hclose".
    - etrans; last exact (Validity.runtime_option_wp_fupd_roundtrip
        (Validity.Model.enabled_runtime_mask ambient outer)
        (Validity.Model.active_runtime_mask ambient entry)
        (Validity.Model.active_runtime_mask ambient exit)
        None final).
      iIntros "Hclose".
      iApply (fupd_mono with "Hclose"). iIntros "Hclose".
      rewrite <- Hclosed_active.
      iApply (fupd_mono with "Hclose"). iIntros "Hclose".
      rewrite Hclosed_active.
      iApply IHsource. iExact "Hclose".
  Qed.

  Lemma focused_close_direct_done_inner_source
      {cost Γ F Δ fuel entry statement closed pre closed_assertion invariant
        outer tail certificate derivation aligned lifo closing}
      (Hclosing : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        closed ((invariant, outer) :: tail) tail certificate closing)
      (close_ok : RuntimeAdapter.Payload.closes (invariant, outer) tail entry
        closed closing) :
    focused_inner_trace_cps_source_refinement
      (@AlignedTraceFocusedClose cost Γ F Δ fuel entry statement closed closed
        pre closed_assertion closed_assertion (invariant, outer) tail tail
        certificate derivation aligned lifo
        (Validity.AlignedOperationalDone closed closed_assertion tail) closing
        Hclosing close_ok
        (@RuntimeAdapter.NetOrdinary tail tail closed closed
          (RuntimeAdapter.Slice.ExecDone closed tail))
        (@RuntimeAdapter.TraceDoneNet cost Γ closed tail)
        (@AlignedTraceDone cost Γ F Δ closed closed_assertion tail)).
  Proof.
    intros runtime ambient final _ _ _ _. simpl.
    dependent destruction Hclosing.
    all: try (exfalso;
      repeat match goal with
      | H : @eq (list _) _ _ |- _ =>
          pose proof (f_equal (@List.length _) H); clear H
      end; simpl in *; lia).
    destruct statement; simpl in view; try discriminate.
    inversion view; subst. simpl.
    iIntros "Hclose". iMod "Hclose". iModIntro. iExact "Hclose".
  Qed.

  Lemma balanced_chunk_region_runtime_refinement
      {cost Γ fuel entry statement middle stack certificate chunk}
      (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        middle stack stack certificate chunk)
      (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (post : iProp Resources.Σ) :
    Validity.aligned_runtime_region_wp certificate runtime ambient post ⊢
      Validity.translated_runtime_wp runtime ambient entry middle statement
        post.
  Proof.
    dependent destruction Hchunk.
    - reflexivity.
    - exfalso. pose proof (f_equal (@List.length _) x0). simpl in *. lia.
    - exfalso. pose proof (f_equal (@List.length _) x0). simpl in *. lia.
    - destruct statement; simpl in view; try discriminate.
      inversion view; subst. simpl.
      unfold Validity.translated_runtime_wp. simpl.
      unfold Validity.Model.active_runtime_mask.
      destruct (RuntimeAdapter.Atomicity.fold_fresh_invariant invariant entry
        closed) as [_ Hopen]. rewrite Hopen.
      unfold Validity.Execution.Primitives.operation_wp. simpl.
      iIntros "Hpost". iMod "Hpost".
      unfold Validity.Model.active_runtime_mask. rewrite Hopen.
      iModIntro. iExact "Hpost".
    - reflexivity.
  Qed.

  Lemma focused_inner_prepend_preserving
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        invariant outer tail certificate derivation aligned lifo rest chunk
        Hchunk head_ok rest_tree Hrest}
      (aligned_rest : @aligned_net_trace cost Γ F Δ middle middle_assertion
        ((invariant, outer) :: tail) exit post tail
        (Some (invariant, outer)) tail
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest) rest_tree rest Hrest)
      (IHrest : focused_inner_trace_cps_source_refinement aligned_rest) :
    focused_inner_trace_cps_source_refinement
      (@AlignedTraceFocusedPrefix cost Γ F Δ fuel entry statement middle
        exit pre middle_assertion post (invariant, outer) tail tail certificate
        derivation aligned lifo rest chunk Hchunk head_ok rest_tree Hrest
        aligned_rest).
  Proof.
    intros runtime ambient final Hcost Hwf Hstack Henvelope. simpl.
    have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle.
    { exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry
        statement middle Hwf certificate). }
    have Hmiddle_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open middle)
        ((invariant, outer) :: tail).
    { exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
        certificate _ _ Hwf lifo Hstack). }
    have Hrest_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    have Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open middle.
    { eapply RuntimeAdapter.Atomicity.access_stack_consistent_functional;
        eauto. }
    pose proof (IHrest runtime ambient final Hcost Hmiddle_wf Hmiddle_stack
      Hrest_envelope) as IHsource.
    etrans.
    - apply aligned_runtime_region_wp_mono. exact IHsource.
    - etrans.
      + exact (balanced_chunk_region_runtime_refinement Hchunk runtime
          ambient _).
      + apply ConcreteOrdinaryTrace.translated_runtime_wp_prepend_source.
        exact Hopen.
  Qed.

  Lemma focused_open_done_cps_source
      {cost Γ F Δ state assertion focused tail} :
    focused_open_trace_cps_source_refinement
      (@AlignedTraceDoneFocused cost Γ F Δ state assertion
        focused tail).
  Proof.
    intros runtime ambient final _ _ _ _. simpl.
    unfold ConcreteOrdinaryTrace.source_translated_wp. simpl.
    iIntros "Hfinal". iModIntro. iExact "Hfinal".
  Qed.

  Lemma focused_open_prepend_preserving
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        focused tail stack_out certificate derivation aligned lifo
        rest chunk Hchunk head_ok rest_tree Hrest}
      (aligned_rest : @aligned_net_trace cost Γ F Δ middle middle_assertion
        (focused :: tail) exit post stack_out (Some focused) tail
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest) rest_tree rest Hrest)
      (IHrest : focused_open_trace_cps_source_refinement aligned_rest) :
    focused_open_trace_cps_source_refinement
      (@AlignedTraceFocusedPrefix cost Γ F Δ fuel entry statement middle
        exit pre middle_assertion post focused tail
        stack_out certificate derivation aligned lifo rest chunk Hchunk
        head_ok rest_tree Hrest aligned_rest).
  Proof.
    intros runtime ambient final Hcost Hwf Hstack Henvelope. simpl.
    have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle.
    { exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry
        statement middle Hwf certificate). }
    have Hmiddle_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open middle)
        (focused :: tail).
    { exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
        certificate _ _ Hwf lifo Hstack). }
    have Hrest_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    have Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open middle.
    { eapply RuntimeAdapter.Atomicity.access_stack_consistent_functional;
        eauto. }
    pose proof (IHrest runtime ambient final Hcost Hmiddle_wf Hmiddle_stack
      Hrest_envelope) as IHsource.
    etrans.
    - apply aligned_runtime_region_wp_mono. exact IHsource.
    - etrans.
      + exact (balanced_chunk_region_runtime_refinement Hchunk runtime
          ambient _).
      + apply ConcreteOrdinaryTrace.translated_runtime_wp_prepend_source.
        exact Hopen.
  Qed.

  (** Closed reification is the empty-stack specialization consumed by the
      top-level assembly theorem. *)
  Definition closed_trace_cps_source_refinement
      {cost Γ F Δ entry pre exit post source tree suffix trace}
      (aligned_trace : @aligned_net_trace cost Γ F Δ entry pre [] exit post
        [] None [] source tree suffix trace) : Prop :=
    ordinary_trace_cps_source_refinement aligned_trace.

  Lemma closed_aligned_trace_runtime_refinement_from_cps
      {cost Γ F Δ entry pre exit post source tree suffix trace}
      (aligned_trace : @aligned_net_trace cost Γ F Δ entry pre [] exit post []
        None [] source tree suffix trace) :
    closed_trace_cps_source_refinement aligned_trace ->
    closed_aligned_trace_runtime_refinement aligned_trace.
  Proof.
    intros Hsource Hcost Hwf Hstack runtime formals binders atoms ambient
      Henvelope.
    pose proof (aligned_net_trace_source_eq aligned_trace) as Hsource_eq.
    subst source.
    pose (normalization :=
      {| RuntimeAdapter.traced_net_normal :=
          {| RuntimeAdapter.suffix_net_lifo :=
              Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix_has_lifo
                suffix;
             RuntimeAdapter.suffix_net_tree := tree |};
         RuntimeAdapter.traced_net_source := trace |}).
    pose (structured :=
      {| aligned_net_suffix := suffix;
         aligned_net_normal := normalization |}).
    pose proof (aligned_trace_structured_cps_valid_complete structured)
      as Hstructured.
    iIntros "Hresources".
    iApply (Hsource runtime ambient _ Hcost Hwf Hstack Henvelope).
    iApply (Hstructured Hwf runtime formals binders atoms ambient Henvelope
      (fun _ =>
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms post ∗
         Validity.World.access_stack_interp atoms ambient [])%I)).
    - reflexivity.
    - iExact "Hresources".
  Qed.

  Module Phase7EndToEndSpike.
    (** Constructor-complete dependent-type spike for the candidate uniform
        CPS judgment.  Each remaining [admit] corresponds, in declaration
        order, to one constructor of [aligned_net_trace].  This exposes all
        dependent induction hypotheses and indices, but an admitted skeleton
        is not a semantic go/no-go check: the [AlignedTraceClose] case below
        demonstrated that the candidate conclusion itself is too strong. *)
    Theorem aligned_trace_cps_source_refinement_spike
        {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source
          tree suffix trace}
        (aligned_trace : @aligned_net_trace cost Γ F Δ entry pre stack_in exit
          post stack_out mode tail source tree suffix trace) :
      aligned_trace_cps_source_refinement aligned_trace.
    Proof.
      induction aligned_trace.
      - (* AlignedTraceDone *)
        intros runtime ambient final _ _ _ _. simpl.
        unfold ConcreteOrdinaryTrace.source_translated_wp. simpl.
        iIntros "Hfinal". iModIntro. iExact "Hfinal".
      - (* AlignedTraceDoneFocused *)
        intros runtime ambient final _ _ _ _. simpl.
        unfold ConcreteOrdinaryTrace.source_translated_wp. simpl.
        iIntros "Hfinal". iModIntro. iExact "Hfinal".
      - (* AlignedTraceChunk *)
        intros runtime ambient final Hcost Hwf Hstack Henvelope. simpl.
        have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle :=
          RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry
            statement middle Hwf certificate.
        have Hmiddle_stack :
            RuntimeAdapter.Atomicity.access_stack_consistent
              (RuntimeAdapter.Atomicity.analysis_open middle) stack :=
          RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
            certificate stack stack Hwf lifo Hstack.
        have Hrest_envelope : Validity.Model.runtime_mask
            (Normalized.suffix_footprint
              (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
                rest)) ⊆ ambient.
        { etrans; last exact Henvelope.
          apply Validity.Model.runtime_mask_mono.
          apply Normalized.suffix_footprint_rest_subset. }
        have Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
            RuntimeAdapter.Atomicity.analysis_open middle.
        { eapply RuntimeAdapter.Atomicity.access_stack_consistent_functional;
            eauto. }
        pose proof (IHaligned_trace runtime ambient final Hcost Hmiddle_wf
          Hmiddle_stack Hrest_envelope) as IHsource.
        etrans; [apply aligned_runtime_region_wp_mono; exact IHsource|].
        etrans; [exact (balanced_chunk_region_runtime_refinement Hchunk runtime
          ambient _)|].
        apply ConcreteOrdinaryTrace.translated_runtime_wp_prepend_source.
        exact Hopen.
      - admit. (* AlignedTraceAccess *)
      - admit. (* AlignedTraceNestedAccess *)
      - (* AlignedTraceFocusedPrefix *)
        intros runtime ambient final Hcost Hwf Hstack Henvelope. simpl.
        have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle :=
          RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry
            statement middle Hwf certificate.
        have Hmiddle_stack :
            RuntimeAdapter.Atomicity.access_stack_consistent
              (RuntimeAdapter.Atomicity.analysis_open middle)
              (focused :: tail) :=
          RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
            certificate (focused :: tail) (focused :: tail) Hwf lifo Hstack.
        have Hrest_envelope : Validity.Model.runtime_mask
            (Normalized.suffix_footprint
              (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
                rest)) ⊆ ambient.
        { etrans; last exact Henvelope.
          apply Validity.Model.runtime_mask_mono.
          apply Normalized.suffix_footprint_rest_subset. }
        have Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
            RuntimeAdapter.Atomicity.analysis_open middle.
        { eapply RuntimeAdapter.Atomicity.access_stack_consistent_functional;
            eauto. }
        pose proof (IHaligned_trace runtime ambient final Hcost Hmiddle_wf
          Hmiddle_stack Hrest_envelope) as IHsource.
        etrans; [apply aligned_runtime_region_wp_mono; exact IHsource|].
        etrans; [exact (balanced_chunk_region_runtime_refinement Hchunk runtime
          ambient _)|].
        apply ConcreteOrdinaryTrace.translated_runtime_wp_prepend_source.
        exact Hopen.
      - admit. (* AlignedTraceClose *)
      - admit. (* AlignedTraceFocusedClose *)
      - admit. (* AlignedTraceConditional *)
      - admit. (* AlignedTraceFocusedConditional *)
      - admit. (* AlignedTraceFocusedConditionalContinue *)
      - admit. (* AlignedTraceSequenceExpansion *)
      - admit. (* AlignedTraceExpansion *)
    Admitted.

    Lemma ordinary_trace_cps_source_refinement_from_spike
        {cost Γ F Δ entry pre stack_in exit post stack_out source tree suffix
          trace}
        (aligned_trace : @aligned_net_trace cost Γ F Δ entry pre stack_in exit
          post stack_out None stack_in source tree suffix trace) :
      aligned_trace_cps_source_refinement aligned_trace ->
      ordinary_trace_cps_source_refinement aligned_trace.
    Proof.
      intros Hspike runtime ambient final Hcost Hwf Hstack Henvelope.
      exact (Hspike runtime ambient final Hcost Hwf Hstack Henvelope).
    Qed.

    (** The spike reaches the actual closed assertion-level theorem consumed
        by adequacy, rather than stopping at the conditional constructor. *)
    Theorem closed_aligned_trace_runtime_refinement_spike
        {cost Γ F Δ entry pre exit post source tree suffix trace}
        (aligned_trace : @aligned_net_trace cost Γ F Δ entry pre [] exit post
          [] None [] source tree suffix trace) :
      closed_aligned_trace_runtime_refinement aligned_trace.
    Proof.
      apply closed_aligned_trace_runtime_refinement_from_cps.
      apply ordinary_trace_cps_source_refinement_from_spike.
      apply aligned_trace_cps_source_refinement_spike.
    Qed.
  End Phase7EndToEndSpike.

  Lemma closed_trace_cps_source_done
      {cost Γ F Δ state assertion} :
    closed_trace_cps_source_refinement
      (@AlignedTraceDone cost Γ F Δ state assertion []).
  Proof.
    intros runtime ambient final _ _ _ _. simpl.
    unfold ConcreteOrdinaryTrace.source_translated_wp. simpl.
    iIntros "Hfinal". iModIntro. iExact "Hfinal".
  Qed.

  Lemma ordinary_trace_cps_source_done
      {cost Γ F Δ state assertion stack} :
    ordinary_trace_cps_source_refinement
      (@AlignedTraceDone cost Γ F Δ state assertion stack).
  Proof.
    intros runtime ambient final _ _ _ _. simpl.
    unfold ConcreteOrdinaryTrace.source_translated_wp. simpl.
    iIntros "Hfinal". iModIntro. iExact "Hfinal".
  Qed.

  Lemma aligned_trace_done_runtime_refinement
      {cost Γ F Δ state assertion stack} :
    aligned_trace_runtime_refinement
      (@AlignedTraceDone cost Γ F Δ state assertion stack).
  Proof.
    intros _ _ _ runtime formals binders atoms ambient _. simpl.
    unfold ConcreteOrdinaryTrace.source_translated_wp. simpl.
    iIntros "Hresources". iModIntro. iExact "Hresources".
  Qed.

  Lemma aligned_trace_focused_done_runtime_refinement
      {cost Γ F Δ state assertion focused tail} :
    aligned_trace_runtime_refinement
      (@AlignedTraceDoneFocused cost Γ F Δ state assertion focused tail).
  Proof.
    intros _ _ _ runtime formals binders atoms ambient _. simpl.
    unfold ConcreteOrdinaryTrace.source_translated_wp. simpl.
    iIntros "Hresources". iModIntro. iExact "Hresources".
  Qed.

  Lemma closed_aligned_trace_done_runtime_refinement
      {cost Γ F Δ state assertion} :
    closed_aligned_trace_runtime_refinement
      (@AlignedTraceDone cost Γ F Δ state assertion []).
  Proof.
    apply aligned_trace_done_runtime_refinement.
  Qed.

  Lemma aligned_leaf_prepend_source_runtime_refinement
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion
        stack}
      (view : Runtime.RegionSyntax.view statement =
        typed_analysis_view.TypedAnalysisView.ViewLeaf)
      (step : RuntimeAdapter.Atomicity.take_step (cost Γ statement) entry =
        inr middle)
      (derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask middle) middle_assertion)
      (rest : RuntimeAdapter.certificate_suffix cost Γ middle exit)
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset)
      (final : iProp Resources.Σ)
      (Hactive : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.analysis_mask middle) ⊆
        Validity.Model.active_runtime_mask ambient entry)
      (Hrest :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms middle_assertion ∗
         Validity.World.access_stack_interp atoms ambient stack) ⊢
        ConcreteOrdinaryTrace.source_translated_wp rest runtime ambient final) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack) ⊢
    ConcreteOrdinaryTrace.source_translated_wp
      (RuntimeAdapter.SuffixCons
        (RuntimeAdapter.Atomicity.CertLeaf cost Γ fuel entry statement middle
          view step) rest) runtime ambient final.
  Proof.
    have Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open middle.
    { apply RuntimeAdapter.Atomicity.take_step_preserves_open in step as Hopen.
      exact (eq_sym Hopen). }
    iIntros "Hresources".
    iPoseProof (ConcreteChunks.ordinary_leaf_runtime_refinement view step stack
      pre middle_assertion derivation runtime formals binders atoms ambient
      Hactive
      with "Hresources") as "Hhead".
    iApply (ConcreteOrdinaryTrace.translated_runtime_wp_prepend_source
      (RuntimeAdapter.Atomicity.CertLeaf cost Γ fuel entry statement middle
        view step) rest runtime ambient final Hopen).
    iApply (Validity.translated_runtime_wp_mono with "Hhead").
    exact Hrest.
  Qed.

  (** Resource-proof variant of the one-leaf source-prefix bridge.  It keeps
      the legacy certificate suffix as the executable source while replacing
      the compatibility Hoare derivation with its resource proof. *)
  Lemma resource_leaf_prepend_source_runtime_refinement
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion
        stack}
      (view : Runtime.RegionSyntax.view statement =
        typed_analysis_view.TypedAnalysisView.ViewLeaf)
      (step : RuntimeAdapter.Atomicity.take_step (cost Γ statement) entry =
        inr middle)
      (derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement middle_assertion)
      (Hruntime_cost : Validity.Model.runtime_cost_model_sound cost)
      (Hprocedure_cost : Validity.Certified.procedure_cost_model_sound cost)
      (rest : RuntimeAdapter.certificate_suffix cost Γ middle exit)
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset)
      (final : iProp Resources.Σ)
      (Hactive : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.analysis_mask middle) ⊆
        Validity.Model.active_runtime_mask ambient entry)
      (Hrest :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms middle_assertion ∗
         Validity.World.access_stack_interp atoms ambient stack) ⊢
        ConcreteOrdinaryTrace.source_translated_wp rest runtime ambient final) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack) ⊢
    ConcreteOrdinaryTrace.source_translated_wp
      (RuntimeAdapter.SuffixCons
        (RuntimeAdapter.Atomicity.CertLeaf cost Γ fuel entry statement middle
          view step) rest) runtime ambient final.
  Proof.
    have Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open middle.
    { apply RuntimeAdapter.Atomicity.take_step_preserves_open in step as Hopen.
      exact (eq_sym Hopen). }
    iIntros "Hresources".
    iPoseProof (ConcreteChunks.resource_ordinary_leaf_runtime_refinement
      view step stack pre middle_assertion derivation Hruntime_cost
      Hprocedure_cost runtime formals binders atoms ambient Hactive
      with "Hresources") as "Hhead".
    iApply (ConcreteOrdinaryTrace.translated_runtime_wp_prepend_source
      (RuntimeAdapter.Atomicity.CertLeaf cost Γ fuel entry statement middle
        view step) rest runtime ambient final Hopen).
    iApply (Validity.translated_runtime_wp_mono with "Hhead").
    exact Hrest.
  Qed.

  Lemma aligned_fresh_fold_prepend_source_runtime_refinement
      {cost Γ F Δ fuel entry node invariant arguments store body exit stack}
      (view : Runtime.RegionSyntax.view
        (Runtime.IR.TFold node invariant arguments) =
        typed_analysis_view.TypedAnalysisView.ViewFold invariant)
      (Hfresh : invariant ∉ RuntimeAdapter.Atomicity.analysis_open entry)
      (instantiated : Contracts.instantiated_invariant Γ F Δ
        (Logic.invariant_args invariant) invariant
        (Runtime.Validation.Hoare.symbolize_expr_list store arguments) body)
      (rest : RuntimeAdapter.certificate_suffix cost Γ
        (RuntimeAdapter.Atomicity.fold_invariant invariant entry) exit)
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset)
      (Hnamespace : ↑(Resources.invariant_namespace invariant) ⊆
        Validity.Model.active_runtime_mask ambient entry)
      (final : iProp Resources.Σ)
      (Hrest :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms
           (Runtime.Translation.Assertions.AAnd
             (Runtime.Translation.Assertions.AStack store)
             (Runtime.Translation.Assertions.AInvariant invariant
               (Runtime.Validation.Hoare.symbolize_expr_list store
                 arguments))) ∗
         Validity.World.access_stack_interp atoms ambient stack) ⊢
        ConcreteOrdinaryTrace.source_translated_wp rest runtime ambient final) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms
       (Runtime.Translation.Assertions.AAnd
         (Runtime.Translation.Assertions.AStack store) body) ∗
     Validity.World.access_stack_interp atoms ambient stack) ⊢
    ConcreteOrdinaryTrace.source_translated_wp
      (RuntimeAdapter.SuffixCons
        (RuntimeAdapter.Atomicity.CertFold cost Γ fuel entry
          (Runtime.IR.TFold node invariant arguments) invariant view) rest)
      runtime ambient final.
  Proof.
    have Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open
          (RuntimeAdapter.Atomicity.fold_invariant invariant entry).
    { destruct (RuntimeAdapter.Atomicity.fold_fresh_invariant invariant entry
        Hfresh) as [_ Hfold]. exact (eq_sym Hfold). }
    iIntros "Hresources".
    iPoseProof (ConcreteAccessNodes.fresh_fold_node_runtime_refinement store body
      entry ambient stack Hfresh Hnamespace instantiated runtime formals
      binders atoms with "Hresources") as "Hhead".
    iApply (ConcreteOrdinaryTrace.translated_runtime_wp_prepend_source
      (RuntimeAdapter.Atomicity.CertFold cost Γ fuel entry
        (Runtime.IR.TFold node invariant arguments) invariant view)
      rest runtime ambient final Hopen).
    iApply (Validity.translated_runtime_wp_mono with "Hhead"). exact Hrest.
  Qed.

  Lemma aligned_atomic_prepend_source_runtime_refinement
      {cost Γ F Δ fuel entry node body outer inner pre middle_assertion exit
        stack}
      (step : RuntimeAdapter.Atomicity.take_step
        RuntimeAdapter.Atomicity.AtomicStep entry = inr outer)
      (body_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        body inner)
      (open_equal : RuntimeAdapter.Atomicity.analysis_open inner =
        RuntimeAdapter.Atomicity.analysis_open outer)
      (trusted : Contracts.trusted_atomic Γ body)
      (body_valid : Validity.certificate_semantically_valid
        (stack_in := stack) (stack_out := stack) (pre := pre)
        (post := middle_assertion) body_certificate)
      (rest : RuntimeAdapter.certificate_suffix cost Γ
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask inner)
          (RuntimeAdapter.Atomicity.analysis_open inner)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer ||
            RuntimeAdapter.Atomicity.analysis_step_taken inner)
          (RuntimeAdapter.Atomicity.analysis_in_atomic outer)) exit)
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset)
      (Henvelope : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint
          (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel entry
            (Runtime.IR.TAtomic node body) body outer inner eq_refl step
            body_certificate open_equal)) ⊆ ambient)
      (final : iProp Resources.Σ)
      (Hrest :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms middle_assertion ∗
         Validity.World.access_stack_interp atoms ambient stack) ⊢
        ConcreteOrdinaryTrace.source_translated_wp rest runtime ambient final) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack) ⊢
    ConcreteOrdinaryTrace.source_translated_wp
      (RuntimeAdapter.SuffixCons
        (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel entry
          (Runtime.IR.TAtomic node body) body outer inner eq_refl step
          body_certificate open_equal) rest) runtime ambient final.
  Proof.
    have Houter_open : RuntimeAdapter.Atomicity.analysis_open outer =
        RuntimeAdapter.Atomicity.analysis_open entry.
    { pose proof step as Hstep_sets.
      apply RuntimeAdapter.Atomicity.take_step_preserves_open in Hstep_sets as
        Hopen. exact Hopen. }
    have Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open inner.
    { rewrite open_equal. rewrite Houter_open. reflexivity. }
    eapply ConcreteOrdinaryTrace.translated_head_prepend_source.
    - exact Hopen.
    - apply (ConcreteChunks.atomic_chunk_runtime_refinement step body_certificate
        open_equal stack pre middle_assertion trusted body_valid runtime formals
        binders atoms ambient Henvelope).
    - exact Hrest.
  Qed.

  (** Resource-proof atomic prefix bridge.  The executable suffix remains
      the common certificate erasure; the body validity consumed by the
      trusted atomic runtime rule is obtained directly from the resource
      alignment and its LIFO witness. *)
  Lemma resource_aligned_atomic_prepend_source_runtime_refinement
      {cost Γ F Δ fuel entry node body outer inner pre middle_assertion exit
        stack}
      (step : RuntimeAdapter.Atomicity.take_step
        RuntimeAdapter.Atomicity.AtomicStep entry = inr outer)
      (body_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask outer)
          (RuntimeAdapter.Atomicity.analysis_open outer)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer) true)
        body inner)
      (open_equal : RuntimeAdapter.Atomicity.analysis_open inner =
        RuntimeAdapter.Atomicity.analysis_open outer)
      (trusted : Contracts.trusted_atomic Γ body)
      (body_derivation : Validity.Certified.Rules.RavenResourceTriple
        pre body middle_assertion)
      (body_aligned : Validity.Certified.resource_certificate_hoare_aligned
        cost body_certificate body_derivation)
      (body_lifo : RuntimeAdapter.Atomicity.lifo_certificate body_certificate
        stack stack)
      (Hruntime_cost : Validity.Model.runtime_cost_model_sound cost)
      (Hprocedure_cost : Validity.Certified.procedure_cost_model_sound cost)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (rest : RuntimeAdapter.certificate_suffix cost Γ
        (RuntimeAdapter.Atomicity.AnalysisState
          (RuntimeAdapter.Atomicity.analysis_mask inner)
          (RuntimeAdapter.Atomicity.analysis_open inner)
          (RuntimeAdapter.Atomicity.analysis_step_taken outer ||
            RuntimeAdapter.Atomicity.analysis_step_taken inner)
          (RuntimeAdapter.Atomicity.analysis_in_atomic outer)) exit)
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset)
      (Henvelope : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint
          (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel entry
            (Runtime.IR.TAtomic node body) body outer inner eq_refl step
            body_certificate open_equal)) ⊆ ambient)
      (final : iProp Resources.Σ)
      (Hrest :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms middle_assertion ∗
         Validity.World.access_stack_interp atoms ambient stack) ⊢
        ConcreteOrdinaryTrace.source_translated_wp rest runtime ambient final) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack) ⊢
    ConcreteOrdinaryTrace.source_translated_wp
      (RuntimeAdapter.SuffixCons
        (RuntimeAdapter.Atomicity.CertAtomic cost Γ fuel entry
          (Runtime.IR.TAtomic node body) body outer inner eq_refl step
          body_certificate open_equal) rest) runtime ambient final.
  Proof.
    have Houter_open : RuntimeAdapter.Atomicity.analysis_open outer =
        RuntimeAdapter.Atomicity.analysis_open entry.
    { pose proof step as Hstep_sets.
      apply RuntimeAdapter.Atomicity.take_step_preserves_open in Hstep_sets as
        Hopen. exact Hopen. }
    have Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open inner.
    { rewrite open_equal. rewrite Houter_open. reflexivity. }
    have Hbody_valid := Validity.resource_aligned_certificate_valid
      body_certificate body_derivation (atomic_body_entry_wf step Hwf)
      body_lifo Hprocedure_cost body_aligned.
    eapply ConcreteOrdinaryTrace.translated_head_prepend_source.
    - exact Hopen.
    - apply (ConcreteChunks.atomic_chunk_runtime_refinement step body_certificate
        open_equal stack pre middle_assertion trusted Hbody_valid runtime formals
        binders atoms ambient Henvelope).
    - exact Hrest.
  Qed.

  Lemma aligned_preserving_chunk_runtime_refinement
      {cost Γ F Δ fuel entry statement middle pre post stack certificate chunk}
      (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        middle stack stack certificate chunk)
      (derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask middle) post)
      (aligned : Validity.Certified.certificate_hoare_aligned cost certificate
        derivation)
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack stack)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset)
      (Henvelope : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint certificate) ⊆ ambient) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack) ⊢
    Validity.translated_runtime_wp runtime ambient entry middle statement
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       Validity.World.access_stack_interp atoms ambient stack).
  Proof.
    dependent destruction Hchunk.
    - pose proof (Validity.aligned_certificate_valid _ derivation Hwf lifo
        aligned) as Hvalid.
      etrans; first exact (Hvalid runtime formals binders atoms ambient
        Henvelope).
      apply (Validity.leaf_operation_runtime_refinement_total (cost := cost));
        assumption.
    - exfalso.
      pose proof (f_equal (@List.length _) x0) as Hlength.
      simpl in Hlength. lia.
    - exfalso.
      repeat match goal with
      | H : @eq (list _) _ _ |- _ =>
          pose proof (f_equal (@List.length _) H); clear H
      end.
      simpl in *. lia.
    - pose proof (Validity.aligned_certificate_valid _ derivation Hwf lifo
        aligned) as Hvalid.
      destruct statement; simpl in view; try discriminate.
      inversion view; subst.
      exact (Hvalid runtime formals binders atoms ambient Henvelope).
    - destruct (aligned_atomic_decompose_fix aligned) as
        [atomic_node Hstatement Htrusted Hbody Haligned_body].
      subst statement.
      replace view with
        (@eq_refl _ (typed_analysis_view.TypedAnalysisView.ViewAtomic body))
        in * by apply proof_irrelevance.
      simpl in lifo.
      have Hbody_wf := atomic_body_entry_wf step Hwf.
      have Hbody_valid := aligned_atomic_decomposition_body_valid
        (state := entry)
        {| atomic_source_node := atomic_node;
           atomic_source_statement := eq_refl;
           atomic_source_trusted := Htrusted;
           atomic_body_derivation := Hbody;
           atomic_body_aligned := Haligned_body |}
        stack Hbody_wf (proj1 lifo).
      exact (ConcreteChunks.atomic_chunk_runtime_refinement step
        body_certificate open_equal stack pre post Htrusted Hbody_valid runtime
        formals binders atoms ambient Henvelope).
  Qed.

  (** Resource-indexed concrete refinement for a stack-preserving chunk.
      This is the certificate-local base layer for the core constructors:
      leaves use the resource procedure-cost interpretation, access nodes use
      resource semantic validity directly, and atomic blocks expose their
      resource-aligned body through [resource_aligned_atomic_decompose_fix]. *)
  Lemma resource_aligned_preserving_chunk_runtime_refinement
      {cost Γ F Δ fuel entry statement middle pre post stack certificate chunk}
      (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        middle stack stack certificate chunk)
      (derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement post)
      (aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        certificate derivation)
      (Hruntime_cost : Validity.Model.runtime_cost_model_sound cost)
      (Hprocedure_cost : Validity.Certified.procedure_cost_model_sound cost)
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack stack)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset)
      (Henvelope : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint certificate) ⊆ ambient) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack) ⊢
    Validity.translated_runtime_wp runtime ambient entry middle statement
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       Validity.World.access_stack_interp atoms ambient stack).
  Proof.
    dependent destruction Hchunk.
    - pose proof (Validity.resource_aligned_certificate_valid _ derivation
        Hwf lifo Hprocedure_cost aligned) as Hvalid.
      etrans; first exact (Hvalid runtime formals binders atoms ambient
        Henvelope).
      apply (Validity.leaf_operation_runtime_refinement_total (cost := cost));
        assumption.
    - exfalso.
      pose proof (f_equal (@List.length _) x0) as Hlength.
      simpl in Hlength. lia.
    - exfalso.
      repeat match goal with
      | H : @eq (list _) _ _ |- _ =>
          pose proof (f_equal (@List.length _) H); clear H
      end.
      simpl in *. lia.
    - pose proof (Validity.resource_aligned_certificate_valid _ derivation
        Hwf lifo Hprocedure_cost aligned) as Hvalid.
      destruct statement; simpl in view; try discriminate.
      inversion view; subst.
      exact (Hvalid runtime formals binders atoms ambient Henvelope).
    - destruct (resource_aligned_atomic_decompose_fix aligned) as
        [atomic_node Hstatement Htrusted Hbody Haligned_body].
      subst statement.
      replace view with
        (@eq_refl _ (typed_analysis_view.TypedAnalysisView.ViewAtomic body))
        in * by apply proof_irrelevance.
      simpl in lifo.
      have Hbody_wf := atomic_body_entry_wf step Hwf.
      have Hbody_valid := resource_aligned_atomic_decomposition_body_valid
        (state := entry)
        {| resource_atomic_source_node := atomic_node;
           resource_atomic_source_statement := eq_refl;
           resource_atomic_source_trusted := Htrusted;
           resource_atomic_body_derivation := Hbody;
           resource_atomic_body_aligned := Haligned_body |}
        stack Hbody_wf (proj1 lifo) Hprocedure_cost.
      exact (ConcreteChunks.atomic_chunk_runtime_refinement step
        body_certificate open_equal stack pre post Htrusted Hbody_valid runtime
        formals binders atoms ambient Henvelope).
  Qed.

  Lemma balanced_certificate_open_equal
      {cost Γ fuel entry statement middle stack}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement middle)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open entry) stack)
      (Hlifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack
        stack) :
    RuntimeAdapter.Atomicity.analysis_open entry =
      RuntimeAdapter.Atomicity.analysis_open middle.
  Proof.
    eapply RuntimeAdapter.Atomicity.access_stack_consistent_functional.
    - exact Hstack.
    - eapply RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency;
        eauto.
  Qed.

  Lemma aligned_preserving_chunk_prepend_source_runtime_refinement
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion stack
        certificate chunk}
      (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        middle stack stack certificate chunk)
      (derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask middle) middle_assertion)
      (aligned : Validity.Certified.certificate_hoare_aligned cost certificate
        derivation)
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack stack)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open entry) stack)
      (rest : RuntimeAdapter.certificate_suffix cost Γ middle exit)
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset)
      (Henvelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (RuntimeAdapter.SuffixCons certificate rest)) ⊆ ambient)
      (final : iProp Resources.Σ)
      (Hrest :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms middle_assertion ∗
         Validity.World.access_stack_interp atoms ambient stack) ⊢
        ConcreteOrdinaryTrace.source_translated_wp rest runtime ambient final) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack) ⊢
    ConcreteOrdinaryTrace.source_translated_wp
      (RuntimeAdapter.SuffixCons certificate rest) runtime ambient final.
  Proof.
    have Hhead_envelope : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint certificate) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_head_subset. }
    eapply ConcreteOrdinaryTrace.translated_head_prepend_source.
    - eapply balanced_certificate_open_equal; eauto.
    - eapply aligned_preserving_chunk_runtime_refinement; eauto.
    - exact Hrest.
  Qed.

  (** Resource-indexed stack-preserving prefix bridge.  [Hchunk] and
      [lifo] are the concrete chunk/stack lockstep witness; resource
      alignment supplies the proof content without changing the erased
      executable suffix. *)
  Lemma resource_aligned_preserving_chunk_prepend_source_runtime_refinement
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion stack
        certificate chunk}
      (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        middle stack stack certificate chunk)
      (derivation : Validity.Certified.Rules.RavenResourceTriple
        pre statement middle_assertion)
      (aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        certificate derivation)
      (Hruntime_cost : Validity.Model.runtime_cost_model_sound cost)
      (Hprocedure_cost : Validity.Certified.procedure_cost_model_sound cost)
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate stack stack)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open entry) stack)
      (rest : RuntimeAdapter.certificate_suffix cost Γ middle exit)
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (ambient : coPset)
      (Henvelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (RuntimeAdapter.SuffixCons certificate rest)) ⊆ ambient)
      (final : iProp Resources.Σ)
      (Hrest :
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms middle_assertion ∗
         Validity.World.access_stack_interp atoms ambient stack) ⊢
        ConcreteOrdinaryTrace.source_translated_wp rest runtime ambient final) :
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient stack) ⊢
    ConcreteOrdinaryTrace.source_translated_wp
      (RuntimeAdapter.SuffixCons certificate rest) runtime ambient final.
  Proof.
    have Hhead_envelope : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint certificate) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_head_subset. }
    eapply ConcreteOrdinaryTrace.translated_head_prepend_source.
    - eapply balanced_certificate_open_equal; eauto.
    - eapply resource_aligned_preserving_chunk_runtime_refinement; eauto.
    - exact Hrest.
  Qed.

  Lemma resource_aligned_trace_chunk_runtime_refinement
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        stack stack_out certificate derivation aligned lifo suffix chunk Hchunk
        rest_tree Hrest}
      (aligned_rest : @resource_aligned_net_trace cost Γ F Δ middle
        middle_assertion stack exit post stack_out None stack
        (resource_certificate_suffix_of_operational_suffix suffix) rest_tree
        suffix Hrest)
      (IHrest : resource_aligned_trace_runtime_refinement aligned_rest) :
    resource_aligned_trace_runtime_refinement
      (@ResourceAlignedTraceChunk cost Γ F Δ fuel entry statement middle exit
        pre middle_assertion post stack stack_out certificate derivation aligned
        lifo suffix chunk Hchunk rest_tree Hrest aligned_rest).
  Proof.
    intros Hruntime_cost Hprocedure_cost Hwf Hstack runtime formals binders
      atoms ambient Henvelope.
    have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle :=
      RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry statement
        middle Hwf certificate.
    have Hmiddle_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open middle) stack :=
      RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
        certificate _ _ Hwf lifo Hstack.
    have Hrest_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (resource_certificate_suffix_of_operational_suffix suffix)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    pose proof (IHrest Hruntime_cost Hprocedure_cost Hmiddle_wf Hmiddle_stack
      runtime formals binders atoms ambient Hrest_envelope) as Hrest_refinement.
    eapply resource_aligned_preserving_chunk_prepend_source_runtime_refinement;
      eauto.
  Qed.

  Lemma resource_pending_open_prepend_preserving
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        focused tail stack_out certificate derivation aligned lifo rest chunk
        Hchunk head_ok rest_tree Hrest}
      (aligned_rest : @resource_aligned_net_trace cost Γ F Δ middle
        middle_assertion (focused :: tail) exit post stack_out (Some focused)
        tail (resource_certificate_suffix_of_operational_suffix rest) rest_tree
        rest Hrest)
      (IHrest : resource_pending_open_trace_refinement aligned_rest) :
    resource_pending_open_trace_refinement
      (@ResourceAlignedTraceFocusedPrefix cost Γ F Δ fuel entry statement
        middle exit pre middle_assertion post focused tail stack_out certificate
        derivation aligned lifo rest chunk Hchunk head_ok rest_tree Hrest
        aligned_rest).
  Proof.
    intros runtime ambient formals binders atoms continuation Hruntime_cost
      Hprocedure_cost Hwf Hstack Henvelope Hcont.
    have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle :=
      RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry statement
        middle Hwf certificate.
    have Hmiddle_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open middle) (focused :: tail) :=
      RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
        certificate _ _ Hwf lifo Hstack.
    have Hrest_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (resource_certificate_suffix_of_operational_suffix rest)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    have Hrest_refinement := IHrest runtime ambient formals binders atoms
      continuation Hruntime_cost Hprocedure_cost Hmiddle_wf Hmiddle_stack
      Hrest_envelope Hcont.
    have Hhead_envelope : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint certificate) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_head_subset. }
    simpl. iIntros "Hresources".
    iPoseProof (Validity.resource_aligned_certificate_valid certificate
      derivation Hwf lifo Hprocedure_cost aligned runtime formals binders atoms
      ambient Hhead_envelope with "Hresources") as "Hhead".
    iPoseProof (traced_chunk_region_runtime_refinement Hchunk runtime ambient _
      (resource_aligned_certificate_runtime_trusted aligned)
      with "Hhead") as "Hhead".
    iApply (aligned_runtime_region_wp_mono certificate runtime ambient).
    - iIntros "Hmiddle". iApply Hrest_refinement. iExact "Hmiddle".
    - iExact "Hhead".
  Qed.

  Lemma resource_ordinary_prepend_preserving
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        stack stack_out certificate derivation aligned lifo rest chunk Hchunk
        rest_tree Hrest}
      (aligned_rest : @resource_aligned_net_trace cost Γ F Δ middle
        middle_assertion stack exit post stack_out None stack
        (resource_certificate_suffix_of_operational_suffix rest) rest_tree rest
        Hrest)
      (IHrest : resource_ordinary_trace_cps_source_refinement aligned_rest) :
    resource_ordinary_trace_cps_source_refinement
      (@ResourceAlignedTraceChunk cost Γ F Δ fuel entry statement middle exit
        pre middle_assertion post stack stack_out certificate derivation aligned
        lifo rest chunk Hchunk rest_tree Hrest aligned_rest).
  Proof.
    intros runtime ambient final Hruntime_cost Hprocedure_cost Hwf Hstack
      Henvelope. simpl.
    have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle :=
      RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry statement
        middle Hwf certificate.
    have Hmiddle_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open middle) stack :=
      RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
        certificate _ _ Hwf lifo Hstack.
    have Hrest_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (resource_certificate_suffix_of_operational_suffix rest)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    have Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open middle.
    { eapply RuntimeAdapter.Atomicity.access_stack_consistent_functional;
        eauto. }
    pose proof (IHrest runtime ambient final Hruntime_cost Hprocedure_cost
      Hmiddle_wf Hmiddle_stack Hrest_envelope) as IHsource.
    etrans.
    - apply aligned_runtime_region_wp_mono. exact IHsource.
    - etrans.
      + exact (balanced_chunk_region_runtime_refinement Hchunk runtime
          ambient _).
      + apply ConcreteOrdinaryTrace.translated_runtime_wp_prepend_source.
        exact Hopen.
  Qed.

  Lemma resource_focused_open_prepend_preserving
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        focused tail stack_out certificate derivation aligned lifo rest chunk
        Hchunk head_ok rest_tree Hrest}
      (aligned_rest : @resource_aligned_net_trace cost Γ F Δ middle
        middle_assertion (focused :: tail) exit post stack_out (Some focused)
        tail (resource_certificate_suffix_of_operational_suffix rest) rest_tree
        rest Hrest)
      (IHrest : resource_focused_open_trace_cps_source_refinement aligned_rest) :
    resource_focused_open_trace_cps_source_refinement
      (@ResourceAlignedTraceFocusedPrefix cost Γ F Δ fuel entry statement
        middle exit pre middle_assertion post focused tail stack_out certificate
        derivation aligned lifo rest chunk Hchunk head_ok rest_tree Hrest
        aligned_rest).
  Proof.
    intros runtime ambient final Hruntime_cost Hprocedure_cost Hwf Hstack
      Henvelope. simpl.
    have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle :=
      RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry statement
        middle Hwf certificate.
    have Hmiddle_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open middle) (focused :: tail) :=
      RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
        certificate _ _ Hwf lifo Hstack.
    have Hrest_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (resource_certificate_suffix_of_operational_suffix rest)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    have Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open middle.
    { eapply RuntimeAdapter.Atomicity.access_stack_consistent_functional;
        eauto. }
    pose proof (IHrest runtime ambient final Hruntime_cost Hprocedure_cost
      Hmiddle_wf Hmiddle_stack Hrest_envelope) as IHsource.
    etrans.
    - apply aligned_runtime_region_wp_mono. exact IHsource.
    - etrans.
      + exact (balanced_chunk_region_runtime_refinement Hchunk runtime
          ambient _).
      + apply ConcreteOrdinaryTrace.translated_runtime_wp_prepend_source.
        exact Hopen.
  Qed.

  Lemma resource_focused_inner_prepend_preserving
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        focused tail certificate derivation aligned lifo rest chunk Hchunk
        head_ok rest_tree Hrest}
      (aligned_rest : @resource_aligned_net_trace cost Γ F Δ middle
        middle_assertion (focused :: tail) exit post tail (Some focused) tail
        (resource_certificate_suffix_of_operational_suffix rest) rest_tree rest
        Hrest)
      (IHrest : resource_focused_inner_trace_cps_source_refinement aligned_rest) :
    resource_focused_inner_trace_cps_source_refinement
      (@ResourceAlignedTraceFocusedPrefix cost Γ F Δ fuel entry statement
        middle exit pre middle_assertion post focused tail tail certificate
        derivation aligned lifo rest chunk Hchunk head_ok rest_tree Hrest
        aligned_rest).
  Proof.
    intros runtime ambient final Hruntime_cost Hprocedure_cost Hwf Hstack
      Henvelope. simpl.
    have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle :=
      RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry statement
        middle Hwf certificate.
    have Hmiddle_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open middle) (focused :: tail) :=
      RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
        certificate _ _ Hwf lifo Hstack.
    have Hrest_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (resource_certificate_suffix_of_operational_suffix rest)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    have Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
        RuntimeAdapter.Atomicity.analysis_open middle.
    { eapply RuntimeAdapter.Atomicity.access_stack_consistent_functional;
        eauto. }
    pose proof (IHrest runtime ambient final Hruntime_cost Hprocedure_cost
      Hmiddle_wf Hmiddle_stack Hrest_envelope) as IHsource.
    etrans.
    - apply aligned_runtime_region_wp_mono. exact IHsource.
    - etrans.
      + exact (balanced_chunk_region_runtime_refinement Hchunk runtime
          ambient _).
      + apply ConcreteOrdinaryTrace.translated_runtime_wp_prepend_source.
        exact Hopen.
  Qed.

  Lemma resource_ordinary_access_from_focused_closing
      {cost Γ F Δ fuel entry statement opened exit pre opened_assertion post
        invariant outer tail stack_out certificate derivation aligned lifo rest opening
        Hopening open_ok body Hbody}
      (aligned_body : @resource_aligned_net_trace cost Γ F Δ opened
        opened_assertion ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail
        (resource_certificate_suffix_of_operational_suffix rest) body rest
        Hbody)
      (split : resource_aligned_focused_close_split aligned_body)
      (IHbody : resource_focused_closing_trace_cps_source_refinement
        aligned_body split) :
    resource_ordinary_trace_cps_source_refinement
      (@ResourceAlignedTraceAccess cost Γ F Δ fuel entry statement opened exit
        pre opened_assertion post (invariant, outer) tail stack_out certificate derivation
        aligned lifo rest opening Hopening open_ok body Hbody aligned_body).
  Proof.
    intros runtime ambient final Hruntime_cost Hprocedure_cost Hwf Hstack
      Henvelope. simpl.
    dependent destruction Hopening.
    all: try (exfalso;
      repeat match goal with
      | H : @eq (list _) _ _ |- _ =>
          pose proof (f_equal (@List.length _) H); clear H
      end; simpl in *; lia).
    destruct statement; simpl in view; try discriminate.
    inversion view; subst. simpl.
    have Hopened_wf : RuntimeAdapter.Atomicity.state_wf exit0.
    { eapply RuntimeAdapter.Atomicity.open_invariant_preserves_wf; eauto. }
    have Hopened_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open exit0)
        ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail).
    { destruct (RuntimeAdapter.Atomicity.open_invariant_success invariant entry
        exit0 step) as [Hopen [_ [_ Hfresh]]].
      split; [exact Hopen|]. split; [exact Hfresh|exact Hstack]. }
    have Hbody_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (resource_certificate_suffix_of_operational_suffix rest)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    pose proof (IHbody runtime ambient final Hruntime_cost Hprocedure_cost
      Hopened_wf Hopened_stack Hbody_envelope) as IH.
    unfold ConcreteOrdinaryTrace.source_translated_wp.
    simpl. unfold Validity.Execution.Primitives.operation_wp. simpl.
    unfold Validity.Model.active_runtime_mask in IH |- *.
    have Hid : forall X : option Runtime.LegacyLang.runtime_stmt,
        match X with Some s => Some s | None => None end = X.
    { intros X. destruct X; reflexivity. }
    rewrite Hid. exact IH.
  Qed.

  Lemma resource_aligned_access_runtime_refinement_from_closing
      {cost Γ F Δ fuel entry statement opened exit pre opened_assertion post
        invariant outer tail stack_out certificate derivation aligned lifo rest
        opening Hopening open_ok body Hbody}
      (aligned_body : @resource_aligned_net_trace cost Γ F Δ opened
        opened_assertion ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail
        (resource_certificate_suffix_of_operational_suffix rest) body rest
        Hbody)
      (split : resource_aligned_focused_close_split aligned_body)
      (IHbody : resource_focused_closing_trace_cps_source_refinement
        aligned_body split) :
    resource_aligned_trace_runtime_refinement
      (@ResourceAlignedTraceAccess cost Γ F Δ fuel entry statement opened
        exit pre opened_assertion post (invariant, outer) tail stack_out
        certificate derivation aligned lifo rest opening Hopening open_ok body
        Hbody aligned_body).
  Proof.
    apply resource_aligned_trace_runtime_refinement_from_ordinary_cps.
    exact (resource_ordinary_access_from_focused_closing aligned_body split
      IHbody).
  Qed.

  Lemma resource_focused_nested_access_from_closing
      {cost Γ F Δ fuel entry statement opened exit pre opened_assertion post
        focused tail nested outer stack_out certificate derivation aligned lifo
        rest opening Hopening open_ok body Hbody}
      (aligned_body : @resource_aligned_net_trace cost Γ F Δ opened
        opened_assertion ((nested, outer) :: focused :: tail) exit post
        stack_out (Some (nested, outer)) (focused :: tail)
        (resource_certificate_suffix_of_operational_suffix rest) body rest
        Hbody)
      (split : resource_aligned_focused_close_split aligned_body)
      (IHbody : resource_focused_closing_trace_cps_source_refinement
        aligned_body split) :
    resource_focused_open_trace_cps_source_refinement
      (@ResourceAlignedTraceNestedAccess cost Γ F Δ fuel entry statement opened
        exit pre opened_assertion post focused tail (nested, outer) stack_out
        certificate derivation aligned lifo rest opening Hopening open_ok body
        Hbody aligned_body).
  Proof.
    intros runtime ambient final Hruntime_cost Hprocedure_cost Hwf Hstack
      Henvelope. simpl.
    dependent destruction Hopening.
    all: try (exfalso;
      repeat match goal with
      | H : @eq (list _) _ _ |- _ =>
          pose proof (f_equal (@List.length _) H); clear H
      end; simpl in *; lia).
    destruct statement; simpl in view; try discriminate.
    inversion view; subst. simpl.
    have Hopened_wf : RuntimeAdapter.Atomicity.state_wf exit0.
    { eapply RuntimeAdapter.Atomicity.open_invariant_preserves_wf; eauto. }
    have Hopened_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open exit0)
        ((nested, RuntimeAdapter.Atomicity.analysis_open entry) ::
          focused :: tail).
    { destruct (RuntimeAdapter.Atomicity.open_invariant_success nested entry
        exit0 step) as [Hopen [_ [_ Hfresh]]].
      split; [exact Hopen|]. split; [exact Hfresh|exact Hstack]. }
    have Hbody_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (resource_certificate_suffix_of_operational_suffix rest)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    pose proof (IHbody runtime ambient final Hruntime_cost Hprocedure_cost
      Hopened_wf Hopened_stack Hbody_envelope) as IH.
    unfold ConcreteOrdinaryTrace.source_translated_wp.
    simpl. unfold Validity.Execution.Primitives.operation_wp. simpl.
    unfold Validity.Model.active_runtime_mask in IH |- *.
    have Hid : forall X : option Runtime.LegacyLang.runtime_stmt,
        match X with Some s => Some s | None => None end = X.
    { intros X. destruct X; reflexivity. }
    rewrite Hid. exact IH.
  Qed.

  Lemma resource_pending_open_nested_access
      {cost Γ F Δ fuel entry statement opened exit pre opened_assertion post
        focused tail nested stack_out certificate derivation aligned lifo rest
        opening Hopening open_ok body Hbody}
      (aligned_body : @resource_aligned_net_trace cost Γ F Δ opened
        opened_assertion (nested :: focused :: tail) exit post stack_out
        (Some nested) (focused :: tail)
        (resource_certificate_suffix_of_operational_suffix rest) body rest
        Hbody)
      (IHbody : resource_pending_open_trace_refinement aligned_body) :
    resource_pending_open_trace_refinement
      (@ResourceAlignedTraceNestedAccess cost Γ F Δ fuel entry statement
        opened exit pre opened_assertion post focused tail nested stack_out
        certificate derivation aligned lifo rest opening Hopening open_ok body
        Hbody aligned_body).
  Proof.
    intros runtime ambient formals binders atoms continuation Hruntime_cost
      Hprocedure_cost Hwf Hstack Henvelope Hcont.
    have Hopened_wf : RuntimeAdapter.Atomicity.state_wf opened :=
      RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry statement
        opened Hwf certificate.
    have Hopened_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open opened)
        (nested :: focused :: tail) :=
      RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
        certificate _ _ Hwf lifo Hstack.
    have Hbody_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (resource_certificate_suffix_of_operational_suffix rest)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    have Hbody_refinement := IHbody runtime ambient formals binders atoms
      continuation Hruntime_cost Hprocedure_cost Hopened_wf Hopened_stack
      Hbody_envelope Hcont.
    have Hhead_envelope : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint certificate) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_head_subset. }
    simpl. iIntros "Hresources".
    iPoseProof (Validity.resource_aligned_certificate_valid certificate
      derivation Hwf lifo Hprocedure_cost aligned runtime formals binders atoms
      ambient Hhead_envelope with "Hresources") as "Hhead".
    iPoseProof (traced_chunk_region_runtime_refinement Hopening runtime ambient _
      (resource_aligned_certificate_runtime_trusted aligned)
      with "Hhead") as "Hhead".
    iApply (aligned_runtime_region_wp_mono certificate runtime ambient).
    - iIntros "Hopened". iApply Hbody_refinement. iExact "Hopened".
    - iExact "Hhead".
  Qed.

  (** Step 8: the "linear" sub-family of [aligned_focused_close_split] --
      any number of preserving chunks (leaf or atomic) followed immediately
      by the matching close, with no nested conditional along the way.  This
      mirrors [aligned_focused_close_split]'s own [_here]/[_later] builders
      exactly (same explicit hypotheses, same conclusion shape) but as a
      genuine two-constructor [Inductive], so it carries its own induction
      principle -- unlike [aligned_focused_close_split] (a record, indexed
      by an arbitrary [aligned_net_trace], with three builders but no way to
      recover "which builder" from an opaque value of the record type).  The
      third builder, [_conditional_here] (a nested conditional inside the
      focused region), is deliberately not covered here -- generalizing to
      it needs its own arm-selection argument, comparable in shape to step
      5's own conditional handling, and is out of scope for this pass. *)
  Inductive linear_focused_close
      : forall {cost Γ F Δ invariant outer tail entry pre exit post stack_out
          source tree suffix trace},
        @aligned_net_trace cost Γ F Δ entry pre ((invariant, outer) :: tail)
          exit post stack_out (Some (invariant, outer)) tail source tree
          suffix trace -> Type :=
    | LinearClose
        {cost Γ F Δ fuel entry invariant outer tail exit post stack_out}
        (fold_node : typed_core.TypedCore.node_id)
        (fold_arguments : Runtime.IR.pexpr_list Γ
          (Logic.invariant_args invariant))
        (store : Runtime.IR.Core.symbolic_store Γ F Δ)
        (body : Runtime.Translation.Assertions.assertion Γ F Δ)
        (fold_view : Runtime.RegionSyntax.view
          (Runtime.IR.TFold fold_node invariant fold_arguments) =
          typed_analysis_view.TypedAnalysisView.ViewFold invariant)
        (Hopen : invariant ∈ RuntimeAdapter.Atomicity.analysis_open entry)
        (Houter : invariant ∉ outer)
        (Hopen_eq : RuntimeAdapter.Atomicity.analysis_open entry =
          {[invariant]} ∪ outer)
        (instantiated : Contracts.instantiated_invariant Γ F Δ
          (Logic.invariant_args invariant) invariant
          (Runtime.Validation.Hoare.symbolize_expr_list store fold_arguments)
          body)
        {rest}
        {rest_tree : RuntimeAdapter.normalized_net tail stack_out
          (RuntimeAdapter.Atomicity.fold_invariant invariant entry) exit}
        {Hrest : RuntimeAdapter.net_trace cost Γ
          (RuntimeAdapter.Atomicity.fold_invariant invariant entry) exit None
          tail stack_out
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest) rest_tree}
        (aligned_rest : aligned_net_trace cost Γ F Δ
          (RuntimeAdapter.Atomicity.fold_invariant invariant entry)
          (Runtime.Translation.Assertions.AAnd
            (Runtime.Translation.Assertions.AStack store)
            (Runtime.Translation.Assertions.AInvariant invariant
              (Runtime.Validation.Hoare.symbolize_expr_list store
                fold_arguments)))
          tail exit post stack_out None tail
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest) rest_tree rest Hrest) :
        linear_focused_close
          (@AlignedTraceFocusedClose cost Γ F Δ (S fuel) entry
            (Runtime.IR.TFold fold_node invariant fold_arguments)
            (RuntimeAdapter.Atomicity.fold_invariant invariant entry) exit
            (Runtime.Translation.Assertions.AAnd
              (Runtime.Translation.Assertions.AStack store) body)
            (Runtime.Translation.Assertions.AAnd
              (Runtime.Translation.Assertions.AStack store)
              (Runtime.Translation.Assertions.AInvariant invariant
                (Runtime.Validation.Hoare.symbolize_expr_list store
                  fold_arguments)))
            post (invariant, outer) tail stack_out
            (RuntimeAdapter.Atomicity.CertFold cost Γ fuel entry
              (Runtime.IR.TFold fold_node invariant fold_arguments) invariant
              fold_view)
            (Validity.Certified.hoare_mask_transport
              (Validity.Certified.Rules.FoldInvariantRule fold_node invariant
                fold_arguments store body
                (RuntimeAdapter.Atomicity.analysis_mask entry) instantiated)
              eq_refl
              (eq_sym (Validity.Certified.fold_analysis_mask invariant entry)))
            (Validity.Certified.AlignedFold cost Γ F Δ fuel entry fold_node
              invariant fold_arguments store body fold_view instantiated)
            (or_introl (ex_intro _ outer (conj eq_refl (conj Hopen (conj
              Houter Hopen_eq)))))
            rest
            (@RuntimeAdapter.Payload.ChunkFold Γ fuel cost entry
              (Runtime.IR.TFold fold_node invariant fold_arguments) invariant
              outer tail fold_view Hopen Houter Hopen_eq)
            (@RuntimeAdapter.ChunkCertificateFold cost Γ fuel entry
              (Runtime.IR.TFold fold_node invariant fold_arguments) invariant
              outer tail fold_view Hopen Houter Hopen_eq) I rest_tree Hrest
            aligned_rest)
    | LinearPrefix
        {cost Γ F Δ fuel entry statement middle exit pre middle_assertion
          post invariant outer tail stack_out certificate derivation aligned
          lifo rest chunk}
        (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry
          statement middle ((invariant, outer) :: tail)
          ((invariant, outer) :: tail) certificate chunk)
        (head_ok : RuntimeAdapter.Payload.preserves (invariant, outer) tail
          entry middle chunk)
        {rest_tree : RuntimeAdapter.focused_net (invariant, outer) tail
          stack_out middle exit}
        {Hrest : RuntimeAdapter.net_trace cost Γ middle exit
          (Some (invariant, outer)) tail stack_out
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest) rest_tree}
        {aligned_rest : aligned_net_trace cost Γ F Δ middle middle_assertion
          ((invariant, outer) :: tail) exit post stack_out
          (Some (invariant, outer)) tail
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest) rest_tree rest Hrest}
        (linear : linear_focused_close aligned_rest) :
        linear_focused_close
          (@AlignedTraceFocusedPrefix cost Γ F Δ fuel entry statement middle
            exit pre middle_assertion post (invariant, outer) tail stack_out
            certificate derivation aligned lifo rest chunk Hchunk head_ok
            rest_tree Hrest aligned_rest).

  Definition aligned_focused_close_split_of_linear
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (linear : linear_focused_close aligned_trace) :
      aligned_focused_close_split aligned_trace.
  Proof.
    induction linear as
      [cost Γ F Δ fuel entry invariant outer tail exit post stack_out
         fold_node fold_arguments store body fold_view Hopen Houter Hopen_eq
         instantiated rest rest_tree Hrest aligned_rest
      |cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
         invariant outer tail stack_out certificate derivation aligned lifo
         rest chunk Hchunk head_ok rest_tree Hrest aligned_rest linear' IH].
    - exact (aligned_focused_close_split_here
        (@RuntimeAdapter.ChunkCertificateFold cost Γ fuel entry
          (Runtime.IR.TFold fold_node invariant fold_arguments) invariant
          outer tail fold_view Hopen Houter Hopen_eq) I aligned_rest).
    - exact (aligned_focused_close_split_later Hchunk head_ok _ IH).
  Defined.

  Lemma preserving_chunk_open_continuous
      {cost Γ fuel entry statement middle stack certificate chunk}
      (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        middle stack stack certificate chunk)
      (Hopen : RuntimeAdapter.Atomicity.analysis_open entry <>
        (empty : gset typed_core.TypedCore.inv_id)) :
    Validity.certificate_open_continuous certificate.
  Proof.
    dependent destruction Hchunk; simpl.
    - split; first exact Hopen. split; last exact I.
      apply RuntimeAdapter.Atomicity.take_step_preserves_open in step as
        Hopen_eq.
      rewrite Hopen_eq. exact Hopen.
    - exfalso. apply (f_equal (@List.length _)) in x0. simpl in x0. lia.
    - exfalso. apply (f_equal (@List.length _)) in x0. simpl in x0. lia.
    - split; first exact Hopen. split; last exact I.
      unfold RuntimeAdapter.Atomicity.fold_invariant.
      rewrite bool_decide_eq_false_2; eauto.
    - split; first exact Hopen. split; last exact I.
      rewrite open_equal.
      apply RuntimeAdapter.Atomicity.take_step_preserves_open in step as
        Hopen_eq.
      rewrite Hopen_eq. exact Hopen.
  Qed.

  (** Cost-model sparsity for one preserving chunk under an open, non-atomic
      focus: either the chunk is ghost (erases to [None], in which case
      [analysis_step_taken] simply carries through unchanged from entry to
      middle), or the chunk is the analysis's own single permitted atomic
      step (entry had not yet taken it, middle has). Never both physical.
      This is the elementary fact this pass needs from the cost model to
      avoid [combine_runtime_statements]'s own associativity (item 3's
      Obstacle 1): a preserving chunk and the remaining pre-close prefix
      can never both be physical, so [combine_runtime_statements_assoc_
      left_sparse] always applies at each [LinearPrefix] reassociation
      point.  The proof is a direct corollary of the generic certificate
      step budget; in particular, its existing [CertAtomic] case handles
      trusted [TAtomic] blocks without another trust assumption here. *)
  Lemma linear_prefix_chunk_sparse
      {cost Γ fuel entry statement middle stack}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel entry statement middle)
      (chunk : RuntimeAdapter.Payload.chunk entry stack middle stack)
      (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry statement
        middle stack stack certificate chunk)
      (Hcost : Validity.Model.runtime_cost_model_sound cost)
      (Hopen : RuntimeAdapter.Atomicity.analysis_open entry <>
        (empty : gset typed_core.TypedCore.inv_id))
      (Hnotatomic : RuntimeAdapter.Atomicity.analysis_in_atomic entry = false)
      (runtime : Validity.Model.stack_context Γ) :
    RuntimeAdapter.Atomicity.analysis_in_atomic middle = false /\
    ((Validity.certificate_runtime_statement certificate runtime = None /\
      (RuntimeAdapter.Atomicity.analysis_step_taken entry = true ->
       RuntimeAdapter.Atomicity.analysis_step_taken middle = true)) \/
    (RuntimeAdapter.Atomicity.analysis_step_taken entry = false /\
     RuntimeAdapter.Atomicity.analysis_step_taken middle = true)).
  Proof.
    split.
    - eapply Validity.certificate_preserves_nonatomic; eauto.
    - have Hcontinuous := preserving_chunk_open_continuous Hchunk Hopen.
      have Hbudget := Validity.certificate_runtime_step_budget certificate
        runtime Hcost Hcontinuous Hnotatomic.
      destruct (Validity.certificate_runtime_statement certificate runtime)
        as [physical|] eqn:Herasure.
      + right.
        unfold Validity.analysis_step_bit, Validity.runtime_option_count in
          Hbudget.
        destruct (RuntimeAdapter.Atomicity.analysis_step_taken entry)
            eqn:Hentry,
          (RuntimeAdapter.Atomicity.analysis_step_taken middle) eqn:Hmiddle;
          simpl in Hbudget; try lia; auto.
      + left. split; first reflexivity.
        intros Hentry.
        unfold Validity.analysis_step_bit, Validity.runtime_option_count in
          Hbudget.
        rewrite Hentry in Hbudget.
        destruct (RuntimeAdapter.Atomicity.analysis_step_taken middle)
          eqn:Hmiddle; simpl in Hbudget; [reflexivity|lia].
  Qed.

  (** Downstream propagation of [linear_prefix_chunk_sparse]: once the
      cost model has taken its one permitted atomic step, no further
      chunk on the way to the matching close may be physical -- the whole
      remaining prefix erases to [None]. Proved directly by induction on
      [linear], mirroring [linear_focused_close_source_refinement_
      complete]'s own recursive structure. *)
  Lemma linear_focused_close_split_prefix_none_when_step_taken
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (linear : linear_focused_close aligned_trace)
      (Hcost : Validity.Model.runtime_cost_model_sound cost)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open entry) ((invariant, outer)
          :: tail))
      (Hnotatomic : RuntimeAdapter.Atomicity.analysis_in_atomic entry = false)
      (Hstep_taken : RuntimeAdapter.Atomicity.analysis_step_taken entry =
        true)
      (runtime : Validity.Model.stack_context Γ) :
    ConcreteOrdinaryTrace.source_runtime
      (Erasure.certificate_suffix_of_aligned_operational_suffix
        (aligned_split_prefix _ (aligned_focused_close_split_of_linear
          linear))) runtime = None.
  Proof.
    induction linear as
      [cost Γ F Δ fuel entry invariant outer tail exit post stack_out
         fold_node fold_arguments store body fold_view Hopen Houter Hopen_eq
         instantiated rest rest_tree Hrest aligned_rest
      |cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
         invariant outer tail stack_out certificate derivation aligned lifo
         rest chunk Hchunk head_ok rest_tree Hrest aligned_rest linear' IH]
      in Hcost, Hwf, Hstack, Hnotatomic, Hstep_taken, runtime |- *.
    - simpl. unfold Validity.certificate_runtime_statement. reflexivity.
    - simpl.
      remember (aligned_focused_close_split_of_linear linear') as s
        eqn:Hsplit'.
      destruct s as
        [closed close_assertion prefix rest' prefix_tree rest_tree'
          prefix_trace rest_trace aligned_prefix aligned_rest' expansion].
      simpl.
      have Hopen_ne : RuntimeAdapter.Atomicity.analysis_open entry <>
          (empty : gset typed_core.TypedCore.inv_id).
      { rewrite (proj1 (proj2 Hstack)). set_solver. }
      have Hsparse := linear_prefix_chunk_sparse certificate chunk Hchunk
        Hcost Hopen_ne Hnotatomic runtime.
      destruct Hsparse as [Hmiddle_notatomic [[Hnone Himpl] | [Hfalse _]]];
        last (rewrite Hfalse in Hstep_taken; discriminate Hstep_taken).
      have Hmiddle_taken := Himpl Hstep_taken.
      have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle.
      { exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry
          statement middle Hwf certificate). }
      have Hmiddle_stack : RuntimeAdapter.Atomicity.access_stack_consistent
          (RuntimeAdapter.Atomicity.analysis_open middle) ((invariant, outer)
            :: tail).
      { exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate _ _ Hwf lifo Hstack). }
      have IH' := IH Hcost Hmiddle_wf Hmiddle_stack Hmiddle_notatomic
        Hmiddle_taken runtime.
      rewrite Hnone. simpl.
      unfold Erasure.certificate_suffix_of_aligned_operational_suffix in IH'.
      simpl in IH'.
      rewrite IH'. reflexivity.
  Qed.

  (** The split/source equality item 3's linear-closing step needs: the
      trace's own combined ["source"] field equals [combine(split.prefix,
      split.rest)] -- proved directly by induction on [linear], never as a
      bare [combine_runtime_statements] re-association (which is false in
      general, item 3's Obstacle 1), but via [combine_runtime_statements_
      assoc_left_sparse] gated on the cost-model sparsity established by
      [linear_prefix_chunk_sparse]/[linear_focused_close_split_prefix_
      none_when_step_taken] above. This is exactly the missing link that
      lets a caller (e.g. [linear_ordinary_close]) use [linear_focused_
      close_cps_handoff], which is stated over the split, to discharge a
      goal stated over the trace's own ["source"]. *)
  Lemma linear_focused_close_split_source_runtime
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (linear : linear_focused_close aligned_trace)
      (Hcost : Validity.Model.runtime_cost_model_sound cost)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open entry) ((invariant, outer)
          :: tail))
      (Hnotatomic : RuntimeAdapter.Atomicity.analysis_in_atomic entry = false)
      (runtime : Validity.Model.stack_context Γ) :
    ConcreteOrdinaryTrace.source_runtime source runtime =
    Validity.Model.combine_runtime_statements
      (ConcreteOrdinaryTrace.source_runtime
        (Erasure.certificate_suffix_of_aligned_operational_suffix
          (aligned_split_prefix _ (aligned_focused_close_split_of_linear
            linear))) runtime)
      (ConcreteOrdinaryTrace.source_runtime
        (Erasure.certificate_suffix_of_aligned_operational_suffix
          (aligned_split_rest _ (aligned_focused_close_split_of_linear
            linear))) runtime).
  Proof.
    induction linear as
      [cost Γ F Δ fuel entry invariant outer tail exit post stack_out
         fold_node fold_arguments store body fold_view Hopen Houter Hopen_eq
         instantiated rest rest_tree Hrest aligned_rest
      |cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
         invariant outer tail stack_out certificate derivation aligned lifo
         rest chunk Hchunk head_ok rest_tree Hrest aligned_rest linear' IH]
      in Hcost, Hwf, Hstack, Hnotatomic, runtime |- *.
    - simpl. reflexivity.
    - simpl.
      remember (aligned_focused_close_split_of_linear linear') as s
        eqn:Hsplit'.
      destruct s as
        [closed close_assertion prefix rest' prefix_tree rest_tree'
          prefix_trace rest_trace aligned_prefix aligned_rest' expansion].
      simpl.
      have Hopen_ne : RuntimeAdapter.Atomicity.analysis_open entry <>
          (empty : gset typed_core.TypedCore.inv_id).
      { rewrite (proj1 (proj2 Hstack)). set_solver. }
      have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle.
      { exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry
          statement middle Hwf certificate). }
      have Hmiddle_stack : RuntimeAdapter.Atomicity.access_stack_consistent
          (RuntimeAdapter.Atomicity.analysis_open middle) ((invariant, outer)
            :: tail).
      { exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate _ _ Hwf lifo Hstack). }
      have Hsparse := linear_prefix_chunk_sparse certificate chunk Hchunk
        Hcost Hopen_ne Hnotatomic runtime.
      destruct Hsparse as [Hmiddle_notatomic Hdisj].
      have IH' := IH Hcost Hmiddle_wf Hmiddle_stack Hmiddle_notatomic runtime.
      simpl in IH'.
      have Hassoc : Validity.certificate_runtime_statement certificate runtime
          = None \/
        ConcreteOrdinaryTrace.source_runtime
          (Erasure.certificate_suffix_of_aligned_operational_suffix prefix)
          runtime = None.
      { destruct Hdisj as [[Hnone _] | [Hentry_false Hmiddle_taken]].
        - left. exact Hnone.
        - right.
          have Hprefix_none :=
            linear_focused_close_split_prefix_none_when_step_taken
              linear' Hcost Hmiddle_wf Hmiddle_stack Hmiddle_notatomic
              Hmiddle_taken runtime.
          rewrite <- Hsplit' in Hprefix_none. simpl in Hprefix_none.
          exact Hprefix_none. }
      rewrite IH'.
      apply Validity.combine_runtime_statements_assoc_left_sparse.
      exact Hassoc.
  Qed.

  (** The plain (non-CPS) runtime refinement of the linear split's own
      prefix, as a certificate suffix -- [source_translated_wp]'s own
      entry/exit masks already are the narrow (post-unfold) and restored
      (post-fold) masks respectively, so this needs no continuation
      parameter at all; a caller composes it with whatever comes after via
      ordinary [source_translated_wp] sequencing at the shared, restored
      exit mask. *)
  Definition linear_focused_close_source_refinement
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (linear : linear_focused_close aligned_trace)
      (ambient : coPset) : Prop :=
    let split := aligned_focused_close_split_of_linear linear in
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) ((invariant, outer)
        :: tail) ->
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env),
    Validity.Model.runtime_mask
      (Normalized.suffix_footprint
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          (aligned_split_prefix _ split))) ⊆ ambient ->
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient
       ((invariant, outer) :: tail)) ⊢
    ConcreteOrdinaryTrace.source_translated_wp
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
        (aligned_split_prefix _ split)) runtime ambient
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms (aligned_split_close_assertion _ split)
         ∗
       Validity.World.access_stack_interp atoms ambient tail).

  Lemma linear_focused_close_source_refinement_complete
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (linear : linear_focused_close aligned_trace) (ambient : coPset) :
    linear_focused_close_source_refinement linear ambient.
  Proof.
    induction linear as
      [cost Γ F Δ fuel entry invariant outer tail exit post stack_out
         fold_node fold_arguments store body fold_view Hopen Houter Hopen_eq
         instantiated rest rest_tree Hrest aligned_rest
      |cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
         invariant outer tail stack_out certificate derivation aligned lifo
         rest chunk Hchunk head_ok rest_tree Hrest aligned_rest linear' IH].
    - unfold linear_focused_close_source_refinement. cbv zeta. simpl.
      intros Hwf Hstack runtime formals binders atoms Henvelope.
      apply focused_close_slice_source_runtime_refinement; assumption.
    - unfold linear_focused_close_source_refinement. cbv zeta. simpl.
      destruct (aligned_focused_close_split_of_linear linear') as
        [closed close_assertion prefix rest' prefix_tree rest_tree'
          prefix_trace rest_trace aligned_prefix aligned_rest' expansion]
        eqn:Hsplit'.
      unfold linear_focused_close_source_refinement in IH.
      cbv zeta in IH.
      rewrite Hsplit' in IH.
      simpl. simpl in IH.
      intros Hwf Hstack runtime formals binders atoms Henvelope.
      have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle.
      { exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry
          statement middle Hwf certificate). }
      have Hmiddle_stack : RuntimeAdapter.Atomicity.access_stack_consistent
          (RuntimeAdapter.Atomicity.analysis_open middle)
          ((invariant, outer) :: tail).
      { exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate _ _ Hwf lifo Hstack). }
      have Hchunk_envelope : Validity.Model.runtime_mask
          (RuntimeAdapter.Atomicity.certificate_footprint certificate)
          ⊆ ambient.
      { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
        apply Normalized.suffix_footprint_head_subset. }
      have Hrest_envelope : Validity.Model.runtime_mask
          (Normalized.suffix_footprint
            (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
              prefix))
          ⊆ ambient.
      { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
        apply Normalized.suffix_footprint_rest_subset. }
      simpl.
      change (Validity.World.access_frame atoms ambient invariant outer ∗
        Validity.World.access_stack_interp atoms ambient tail)%I with
        (Validity.World.access_stack_interp atoms ambient
          ((invariant, outer) :: tail)).
      eapply aligned_preserving_chunk_prepend_source_runtime_refinement.
      + exact Hchunk.
      + exact aligned.
      + exact lifo.
      + exact Hwf.
      + exact Hstack.
      + exact Henvelope.
      + exact (IH Hmiddle_wf Hmiddle_stack runtime formals binders atoms
          Hrest_envelope).
  Qed.

  (** The closing state a linear split eventually reaches always has the
      marker's own recorded [outer] as its open set -- the fold that closes
      it can only ever restore exactly that, regardless of how many
      preserving chunks come before it. *)
  Lemma linear_focused_close_split_close_open
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (linear : linear_focused_close aligned_trace) :
    RuntimeAdapter.Atomicity.analysis_open
      (aligned_split_close_state _ (aligned_focused_close_split_of_linear
        linear)) = outer.
  Proof.
    induction linear as
      [cost Γ F Δ fuel entry invariant outer tail exit post stack_out
         fold_node fold_arguments store body fold_view Hopen Houter Hopen_eq
         instantiated rest rest_tree Hrest aligned_rest
      |cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
         invariant outer tail stack_out certificate derivation aligned lifo
         rest chunk Hchunk head_ok rest_tree Hrest aligned_rest linear' IH].
    - simpl. unfold RuntimeAdapter.Atomicity.fold_invariant.
      rewrite Hopen_eq.
      rewrite bool_decide_eq_true_2;
        last (apply elem_of_union_l, elem_of_singleton; reflexivity).
      simpl.
      apply set_eq. intros y.
      rewrite elem_of_difference.
      rewrite elem_of_union.
      rewrite elem_of_singleton.
      split.
      + intros [[Heq | Hy] Hneq].
        * exfalso. exact (Hneq Heq).
        * exact Hy.
      + intros Hy. split.
        * right. exact Hy.
        * intros Heq. subst y. exact (Houter Hy).
    - simpl.
      remember (aligned_focused_close_split_of_linear linear') as s
        eqn:Hsplit'.
      destruct s as
        [closed close_assertion prefix rest' prefix_tree rest_tree'
          prefix_trace rest_trace aligned_prefix aligned_rest' expansion].
      simpl in IH |- *. exact IH.
  Qed.

  (** Re-target a bare [runtime_option_wp] fact's own exit mask to match its
      entry mask, absorbing the actual exit mask into an extra fancy update
      wrapped around the postcondition instead -- the mask-bracket tools
      ([runtime_wp_atomic_mask_change] and its [runtime_option_wp] wrapper)
      need their own inner fact stated at one fixed mask throughout, with
      any further mask change pushed into the postcondition; this converts
      an ordinarily-shaped fact (different entry/exit masks) into that
      form. *)
  Lemma runtime_option_wp_retarget_exit E1 E2
      (physical : option Runtime.LegacyLang.runtime_stmt) (post : iProp
        Resources.Σ) :
    Validity.runtime_option_wp E1 E2 physical post ⊢
    Validity.runtime_option_wp E1 E1 physical (|={E1, E2}=> post).
  Proof.
    destruct physical as [statement|]; simpl.
    - iIntros "Hwp". iApply (wp_mono with "Hwp").
      iIntros (result) "[%Hresult Hpost]". iSplit; first done.
      iModIntro. iExact "Hpost".
    - iIntros "Hpost". iModIntro. iExact "Hpost".
  Qed.

  (** CPS sibling of [linear_focused_close_source_refinement]: instead of
      landing on a single [runtime_option_wp] fixed at the split's own
      restored mask, or trying to land flatly at a caller-chosen
      [final_mask] over the combined source (which would require
      eliminating a mask-changing update against an arbitrary, non-atomic
      [aligned_split_rest] -- something Iris's own [wp] elimination rules
      do not support unless the bracketed statement is atomic, confirmed
      directly: the only instance eliminating a different-mask update
      against a [wp] goal, [elim_modal_fupd_wp_atomic], carries an
      [Atomic] side-condition), this hands the post-close continuation to
      the caller *nested* inside [aligned_split_prefix]'s own
      postcondition, at [aligned_split_prefix]'s own fixed (inner) mask
      throughout, with the widening to [Eouter] made an explicit, separate
      fancy update. This is exactly [Section LinearUnfoldSeam]'s own
      [Hweaken] shape, generalized over an arbitrary [linear_focused_close]
      witness -- hence "handoff", not "source_refinement": nothing here
      concludes a single [wp] over the complete source suffix. No
      atomicity premise is needed to build this handoff: it composes
      [linear_focused_close_source_refinement_complete] (already proven for
      an arbitrary witness) with the caller's own continuation via
      [runtime_option_wp_mono], then [runtime_option_wp_retarget_exit] --
      both free, no [wp_atomic] round-trip. Atomicity is needed only later,
      at [linear_ordinary_close]'s own call site, to fold this handoff's
      inner-mask [aligned_split_prefix] WP back down to the caller's own
      outer mask via [runtime_option_wp_atomic_mask_change]. *)
  Definition linear_focused_close_cps_handoff
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (linear : linear_focused_close aligned_trace)
      (ambient : coPset) : Prop :=
    let split := aligned_focused_close_split_of_linear linear in
    (* [Eouter] is read directly off the marker's own recorded [outer],
       mirroring [Section LinearUnfoldSeam]'s own [Hweaken] target -- not
       derived from [aligned_split_close_state], even though the two are
       provably equal via [linear_focused_close_split_close_open]. *)
    let Eouter := Validity.Model.enabled_runtime_mask ambient outer in
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) ((invariant, outer)
        :: tail) ->
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env),
    Validity.Model.runtime_mask
      (Normalized.suffix_footprint
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          (aligned_split_prefix _ split))) ⊆ ambient ->
    forall (final_mask : coPset) (final : iProp Resources.Σ),
    ((Validity.global_world_context atoms ∗
      Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
        runtime formals binders atoms (aligned_split_close_assertion _
          split) ∗
      Validity.World.access_stack_interp atoms ambient tail) ⊢
      Validity.runtime_option_wp
        Eouter final_mask
        (ConcreteOrdinaryTrace.source_runtime
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            (aligned_split_rest _ split)) runtime) final) ->
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient
       ((invariant, outer) :: tail)) ⊢
    Validity.runtime_option_wp
      (Validity.Model.active_runtime_mask ambient entry)
      (Validity.Model.active_runtime_mask ambient entry)
      (ConcreteOrdinaryTrace.source_runtime
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          (aligned_split_prefix _ split)) runtime)
      (|={Validity.Model.active_runtime_mask ambient entry, Eouter}=>
        Validity.runtime_option_wp Eouter final_mask
          (ConcreteOrdinaryTrace.source_runtime
            (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
              (aligned_split_rest _ split)) runtime) final).

  Lemma linear_focused_close_cps_handoff_complete
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (linear : linear_focused_close aligned_trace) (ambient : coPset) :
    linear_focused_close_cps_handoff linear ambient.
  Proof.
    unfold linear_focused_close_cps_handoff. cbv zeta.
    intros Hwf Hstack runtime formals binders atoms Hfootprint final_mask
      final Hcont.
    have Hcomplete := linear_focused_close_source_refinement_complete
      linear ambient.
    unfold linear_focused_close_source_refinement in Hcomplete.
    cbv zeta in Hcomplete.
    specialize (Hcomplete Hwf Hstack runtime formals binders atoms
      Hfootprint).
    unfold ConcreteOrdinaryTrace.source_translated_wp in Hcomplete.
    have Heq := linear_focused_close_split_close_open linear.
    have Hclosed_active : Validity.Model.active_runtime_mask ambient
        (aligned_split_close_state _ (aligned_focused_close_split_of_linear
          linear)) = Validity.Model.enabled_runtime_mask ambient outer.
    { unfold Validity.Model.active_runtime_mask. rewrite Heq. reflexivity. }
    rewrite Hclosed_active in Hcomplete.
    etrans; [| apply runtime_option_wp_retarget_exit].
    etrans; [exact Hcomplete | apply Validity.runtime_option_wp_mono, Hcont].
  Qed.

  (** Item 3, linear branch, step 2: a focused sub-trace that never closes
      the marker it started under -- any number of preserving chunks
      ([AlignedTraceFocusedPrefix]), ending in [AlignedTraceDoneFocused]
      (still open, nothing further happens). Dual to [linear_focused_close]:
      same recursive-chunk shape, but the base case stops rather than
      folds. No [AlignedTraceNestedAccess] case -- a nested access/close
      pair inside this suffix is out of scope for this pass, per the linear
      branch's own scope boundary. *)
  Inductive linear_focused_open
      : forall {cost Γ F Δ focused tail entry pre exit post stack_out
          source tree suffix trace},
        @aligned_net_trace cost Γ F Δ entry pre (focused :: tail) exit post
          stack_out (Some focused) tail source tree suffix trace -> Type :=
    | LinearOpenDone
        {cost Γ F Δ state assertion focused tail} :
        linear_focused_open
          (@AlignedTraceDoneFocused cost Γ F Δ state assertion focused tail)
    | LinearOpenPrefix
        {cost Γ F Δ fuel entry statement middle exit pre middle_assertion
          post focused tail stack_out certificate derivation aligned
          lifo rest chunk}
        (Hchunk : RuntimeAdapter.chunk_certificate cost Γ fuel entry
          statement middle (focused :: tail) (focused :: tail) certificate
          chunk)
        (head_ok : RuntimeAdapter.Payload.preserves focused tail entry middle
          chunk)
        {rest_tree : RuntimeAdapter.focused_net focused tail stack_out middle
          exit}
        {Hrest : RuntimeAdapter.net_trace cost Γ middle exit (Some focused)
          tail stack_out
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest) rest_tree}
        {aligned_rest : aligned_net_trace cost Γ F Δ middle middle_assertion
          (focused :: tail) exit post stack_out (Some focused) tail
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest) rest_tree rest Hrest}
        (linear : linear_focused_open aligned_rest) :
        linear_focused_open
          (@AlignedTraceFocusedPrefix cost Γ F Δ fuel entry statement middle
            exit pre middle_assertion post focused tail stack_out certificate
            derivation aligned lifo rest chunk Hchunk head_ok rest_tree Hrest
            aligned_rest).

  Lemma linear_focused_open_cps_source_refinement_complete
      {cost Γ F Δ focused tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        (focused :: tail) exit post stack_out (Some focused) tail source tree
        suffix trace}
      (linear : linear_focused_open aligned_trace) :
    focused_open_trace_cps_source_refinement aligned_trace.
  Proof.
    induction linear.
    - apply focused_open_done_cps_source.
    - eapply focused_open_prepend_preserving. exact IHlinear.
  Qed.

  (** The plain (non-CPS) runtime refinement of a [linear_focused_open]
      witness. Unlike [linear_focused_close_source_refinement], there is no
      split to project through: the witness's own [suffix]/[source] (already
      part of [aligned_trace]'s type index) is exactly the program this
      refinement is about, since nothing here ever closes. *)
  Definition linear_focused_open_source_refinement
      {cost Γ F Δ focused tail entry pre exit post stack_out source tree
        suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        (focused :: tail) exit post stack_out (Some focused) tail source tree
        suffix trace}
      (linear : linear_focused_open aligned_trace)
      (ambient : coPset) : Prop :=
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) (focused :: tail) ->
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env),
    Validity.Model.runtime_mask (Normalized.suffix_footprint source)
      ⊆ ambient ->
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient (focused :: tail)) ⊢
    ConcreteOrdinaryTrace.source_translated_wp source runtime ambient
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       Validity.World.access_stack_interp atoms ambient (focused :: tail)).

  Lemma linear_focused_open_source_refinement_complete
      {cost Γ F Δ focused tail entry pre exit post stack_out source tree
        suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        (focused :: tail) exit post stack_out (Some focused) tail source tree
        suffix trace}
      (linear : linear_focused_open aligned_trace) (ambient : coPset) :
    linear_focused_open_source_refinement linear ambient.
  Proof.
    induction linear as
      [cost Γ F Δ state assertion focused tail
      |cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
         focused tail stack_out certificate derivation aligned lifo rest
         chunk Hchunk head_ok rest_tree Hrest aligned_rest linear' IH].
    - unfold linear_focused_open_source_refinement. simpl.
      intros _ _ runtime formals binders atoms _.
      unfold ConcreteOrdinaryTrace.source_translated_wp. simpl.
      iIntros "Hresources". iModIntro. iExact "Hresources".
    - unfold linear_focused_open_source_refinement. simpl.
      destruct focused as [invariant outer_open].
      intros Hwf Hstack runtime formals binders atoms Henvelope.
      have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle.
      { exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry
          statement middle Hwf certificate). }
      have Hmiddle_stack : RuntimeAdapter.Atomicity.access_stack_consistent
          (RuntimeAdapter.Atomicity.analysis_open middle)
          ((invariant, outer_open) :: tail).
      { exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate _ _ Hwf lifo Hstack). }
      have Hrest_envelope : Validity.Model.runtime_mask
          (Normalized.suffix_footprint
            (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
              rest)) ⊆ ambient.
      { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
        apply Normalized.suffix_footprint_rest_subset. }
      change (Validity.World.access_frame atoms ambient invariant outer_open
        ∗ Validity.World.access_stack_interp atoms ambient tail)%I with
        (Validity.World.access_stack_interp atoms ambient
          ((invariant, outer_open) :: tail)).
      eapply aligned_preserving_chunk_prepend_source_runtime_refinement.
      + exact Hchunk.
      + exact aligned.
      + exact lifo.
      + exact Hwf.
      + exact Hstack.
      + exact Henvelope.
      + exact (IH Hmiddle_wf Hmiddle_stack runtime formals binders atoms
          Hrest_envelope).
  Qed.

  (** A [linear_focused_open] witness never closes or opens anything
      further -- every step is either the trivial base case (entry = exit
      literally) or a preserving chunk, so the open set never changes. *)
  Lemma linear_focused_open_same_open
      {cost Γ F Δ focused tail entry pre exit post stack_out source tree
        suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        (focused :: tail) exit post stack_out (Some focused) tail source tree
        suffix trace}
      (linear : linear_focused_open aligned_trace) :
    RuntimeAdapter.Atomicity.analysis_open exit =
      RuntimeAdapter.Atomicity.analysis_open entry.
  Proof.
    induction linear as
      [cost Γ F Δ state assertion focused tail
      |cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
         focused tail stack_out certificate derivation aligned lifo rest
         chunk Hchunk head_ok rest_tree Hrest aligned_rest linear' IH].
    - reflexivity.
    - rewrite IH. clear IH.
      dependent destruction Hchunk.
      + exact (RuntimeAdapter.Atomicity.take_step_preserves_open _ _ _ step).
      + exfalso. pose proof (f_equal (@List.length _) x0) as Hlength.
        simpl in Hlength. lia.
      + exfalso.
        repeat match goal with
        | H : @eq (list _) _ _ |- _ =>
            pose proof (f_equal (@List.length _) H); clear H
        end.
        simpl in *. lia.
      + unfold RuntimeAdapter.Atomicity.fold_invariant.
        rewrite bool_decide_eq_false_2; [reflexivity | exact closed].
      + simpl. rewrite open_equal.
        exact (RuntimeAdapter.Atomicity.take_step_preserves_open _ _ _ step).
  Qed.

  (** A [linear_focused_open] witness's own [stack_out] index is always
      literally [focused :: tail] -- a purely structural fact (both
      constructors either fix it directly or inherit it unchanged from
      their recursive sub-witness), needed to identify a
      [linear_ordinary_open] witness's outer [stack_out] binder (shared
      with its [linear_focused_open] body via [OrdinaryAccess]'s own
      type) with the concrete access-stack shape
      [linear_focused_open_source_refinement]'s conclusion is stated
      against. *)
  Lemma linear_focused_open_same_stack
      {cost Γ F Δ focused tail entry pre exit post stack_out source tree
        suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        (focused :: tail) exit post stack_out (Some focused) tail source tree
        suffix trace}
      (linear : linear_focused_open aligned_trace) :
    stack_out = focused :: tail.
  Proof.
    induction linear as
      [cost Γ F Δ state assertion focused tail
      |cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
         focused tail stack_out certificate derivation aligned lifo rest
         chunk Hchunk head_ok rest_tree Hrest aligned_rest linear' IH].
    - reflexivity.
    - exact IH.
  Qed.

  (** Item 3, linear branch, step 1: any number of ordinary
      ([AlignedTraceChunk]) steps, then one [AlignedTraceAccess], whose own
      body is constrained to be a [linear_focused_open] witness -- i.e. it
      opens exactly one marker and never closes it. This is the *whole*
      linear branch witness (steps 1 and 2 combined into one type), the
      analogue of [linear_focused_close] for the *opening* side of the
      seam. No [AlignedTraceNestedAccess] anywhere in this shape, per the
      linear branch's own scope boundary. *)
  Inductive linear_ordinary_open
      : forall {cost Γ F Δ tail entry pre exit post stack_out source tree
          suffix trace},
        @aligned_net_trace cost Γ F Δ entry pre tail exit post stack_out
          None tail source tree suffix trace -> Type :=
    | OrdinaryAccess
        {cost Γ F Δ fuel entry}
        (node : typed_core.TypedCore.node_id)
        (invariant : typed_core.TypedCore.inv_id)
        (arguments : Runtime.IR.pexpr_list Γ (Logic.invariant_args invariant))
        {opened}
        (store : Runtime.IR.Core.symbolic_store Γ F Δ)
        (body : Runtime.Translation.Assertions.assertion Γ F Δ)
        (view : Runtime.RegionSyntax.view
          (Runtime.IR.TUnfold node invariant arguments) =
          typed_analysis_view.TypedAnalysisView.ViewUnfold invariant)
        (step : RuntimeAdapter.Atomicity.open_invariant invariant entry =
          inr opened)
        (available : invariant ∈ RuntimeAdapter.Atomicity.analysis_mask
          entry)
        (instantiated : Contracts.instantiated_invariant Γ F Δ
          (Logic.invariant_args invariant) invariant
          (Runtime.Validation.Hoare.symbolize_expr_list store arguments)
          body)
        {tail : list RuntimeAdapter.Atomicity.access_marker}
        {exit post stack_out}
        {rest : Erasure.Validity.aligned_operational_suffix cost Γ F Δ
          opened
          (Runtime.Translation.Assertions.AAnd
            (Runtime.Translation.Assertions.AStack store) body)
          ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)
          exit post stack_out}
        {body_tree} {Hbody}
        {aligned_body : aligned_net_trace cost Γ F Δ opened
          (Runtime.Translation.Assertions.AAnd
            (Runtime.Translation.Assertions.AStack store) body)
          ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)
          exit post stack_out
          (Some (invariant, RuntimeAdapter.Atomicity.analysis_open entry))
          tail
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest) body_tree rest Hbody}
        (linear_body : linear_focused_open aligned_body) :
        linear_ordinary_open
          (@AlignedTraceAccess cost Γ F Δ (S fuel) entry
            (Runtime.IR.TUnfold node invariant arguments) opened exit
            (Runtime.Translation.Assertions.AAnd
              (Runtime.Translation.Assertions.AStack store)
              (Runtime.Translation.Assertions.AInvariant invariant
                (Runtime.Validation.Hoare.symbolize_expr_list store
                  arguments)))
            (Runtime.Translation.Assertions.AAnd
              (Runtime.Translation.Assertions.AStack store) body)
            post (invariant, RuntimeAdapter.Atomicity.analysis_open entry)
            tail stack_out
            (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
              (Runtime.IR.TUnfold node invariant arguments) invariant opened
              view step)
            (Validity.Certified.hoare_mask_transport
              (Validity.Certified.Rules.UnfoldInvariantRule node invariant
                arguments store body
                (RuntimeAdapter.Atomicity.analysis_mask entry) available
                instantiated) eq_refl
              (eq_sym (Validity.Certified.unfold_analysis_mask view step)))
            (Validity.Certified.AlignedUnfold cost Γ F Δ fuel entry node
              invariant arguments opened store body view step available
              instantiated)
            (eq_refl :
              RuntimeAdapter.Atomicity.lifo_certificate
                (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
                  (Runtime.IR.TUnfold node invariant arguments) invariant
                  opened view step)
                tail
                ((invariant, RuntimeAdapter.Atomicity.analysis_open entry)
                  :: tail))
            rest
            (@RuntimeAdapter.Payload.ChunkUnfold Γ fuel cost entry
              (Runtime.IR.TUnfold node invariant arguments) invariant opened
              tail view step)
            (@RuntimeAdapter.ChunkCertificateUnfold cost Γ fuel entry
              (Runtime.IR.TUnfold node invariant arguments) invariant opened
              tail view step)
            I body_tree Hbody aligned_body)
    | OrdinaryPrefix
        {cost Γ F Δ fuel entry statement middle exit pre middle_assertion
          post stack stack_out certificate derivation aligned lifo rest
          chunk Hchunk}
        {rest_tree : RuntimeAdapter.net_tree None stack stack_out middle
          exit}
        {Hrest : RuntimeAdapter.net_trace cost Γ middle exit None stack
          stack_out
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest) rest_tree}
        {aligned_rest : aligned_net_trace cost Γ F Δ middle middle_assertion
          stack exit post stack_out None stack
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest) rest_tree rest Hrest}
        (linear : linear_ordinary_open aligned_rest) :
        linear_ordinary_open
          (@AlignedTraceChunk cost Γ F Δ fuel entry statement middle exit pre
            middle_assertion post stack stack_out certificate derivation
            aligned lifo rest chunk Hchunk rest_tree Hrest aligned_rest).

  (** [linear_ordinary_open]'s sibling for the *closing* case: any number of
      ordinary ([AlignedTraceChunk]) steps, then one [AlignedTraceAccess],
      whose own body is a [linear_focused_close] witness instead of a
      [linear_focused_open] one -- i.e. it opens exactly one marker and
      *does* eventually close it again (through some shared continuation),
      rather than handing it off still open. This is the branch shape item
      3's linear closing-seam theorem needs: generalizing [Section
      LinearUnfoldSeam]'s own fixed single-[unfold] branch to admit
      preceding ordinary chunks too. Structurally identical to
      [linear_ordinary_open] otherwise -- same two constructors, same
      concrete-unfold-pieces shape for the access case (mirroring
      [linear_focused_close]'s own [LinearClose] precedent), differing only
      in which focused-body family [OrdinaryCloseAccess] requires. *)
  Inductive linear_ordinary_close
      : forall {cost Γ F Δ tail entry pre exit post stack_out source tree
          suffix trace},
        @aligned_net_trace cost Γ F Δ entry pre tail exit post stack_out
          None tail source tree suffix trace -> Type :=
    | OrdinaryCloseAccess
        {cost Γ F Δ fuel entry}
        (node : typed_core.TypedCore.node_id)
        (invariant : typed_core.TypedCore.inv_id)
        (arguments : Runtime.IR.pexpr_list Γ (Logic.invariant_args invariant))
        {opened}
        (store : Runtime.IR.Core.symbolic_store Γ F Δ)
        (body : Runtime.Translation.Assertions.assertion Γ F Δ)
        (view : Runtime.RegionSyntax.view
          (Runtime.IR.TUnfold node invariant arguments) =
          typed_analysis_view.TypedAnalysisView.ViewUnfold invariant)
        (step : RuntimeAdapter.Atomicity.open_invariant invariant entry =
          inr opened)
        (available : invariant ∈ RuntimeAdapter.Atomicity.analysis_mask
          entry)
        (instantiated : Contracts.instantiated_invariant Γ F Δ
          (Logic.invariant_args invariant) invariant
          (Runtime.Validation.Hoare.symbolize_expr_list store arguments)
          body)
        {tail : list RuntimeAdapter.Atomicity.access_marker}
        {exit post stack_out}
        {rest : Erasure.Validity.aligned_operational_suffix cost Γ F Δ
          opened
          (Runtime.Translation.Assertions.AAnd
            (Runtime.Translation.Assertions.AStack store) body)
          ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)
          exit post stack_out}
        {body_tree} {Hbody}
        {aligned_body : aligned_net_trace cost Γ F Δ opened
          (Runtime.Translation.Assertions.AAnd
            (Runtime.Translation.Assertions.AStack store) body)
          ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)
          exit post stack_out
          (Some (invariant, RuntimeAdapter.Atomicity.analysis_open entry))
          tail
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest) body_tree rest Hbody}
        (linear_body : linear_focused_close aligned_body) :
        linear_ordinary_close
          (@AlignedTraceAccess cost Γ F Δ (S fuel) entry
            (Runtime.IR.TUnfold node invariant arguments) opened exit
            (Runtime.Translation.Assertions.AAnd
              (Runtime.Translation.Assertions.AStack store)
              (Runtime.Translation.Assertions.AInvariant invariant
                (Runtime.Validation.Hoare.symbolize_expr_list store
                  arguments)))
            (Runtime.Translation.Assertions.AAnd
              (Runtime.Translation.Assertions.AStack store) body)
            post (invariant, RuntimeAdapter.Atomicity.analysis_open entry)
            tail stack_out
            (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
              (Runtime.IR.TUnfold node invariant arguments) invariant opened
              view step)
            (Validity.Certified.hoare_mask_transport
              (Validity.Certified.Rules.UnfoldInvariantRule node invariant
                arguments store body
                (RuntimeAdapter.Atomicity.analysis_mask entry) available
                instantiated) eq_refl
              (eq_sym (Validity.Certified.unfold_analysis_mask view step)))
            (Validity.Certified.AlignedUnfold cost Γ F Δ fuel entry node
              invariant arguments opened store body view step available
              instantiated)
            (eq_refl :
              RuntimeAdapter.Atomicity.lifo_certificate
                (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
                  (Runtime.IR.TUnfold node invariant arguments) invariant
                  opened view step)
                tail
                ((invariant, RuntimeAdapter.Atomicity.analysis_open entry)
                  :: tail))
            rest
            (@RuntimeAdapter.Payload.ChunkUnfold Γ fuel cost entry
              (Runtime.IR.TUnfold node invariant arguments) invariant opened
              tail view step)
            (@RuntimeAdapter.ChunkCertificateUnfold cost Γ fuel entry
              (Runtime.IR.TUnfold node invariant arguments) invariant opened
              tail view step)
            I body_tree Hbody aligned_body)
    | OrdinaryClosePrefix
        {cost Γ F Δ fuel entry statement middle exit pre middle_assertion
          post stack stack_out certificate derivation aligned lifo rest
          chunk Hchunk}
        {rest_tree : RuntimeAdapter.net_tree None stack stack_out middle
          exit}
        {Hrest : RuntimeAdapter.net_trace cost Γ middle exit None stack
          stack_out
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest) rest_tree}
        {aligned_rest : aligned_net_trace cost Γ F Δ middle middle_assertion
          stack exit post stack_out None stack
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest) rest_tree rest Hrest}
        (linear : linear_ordinary_close aligned_rest) :
        linear_ordinary_close
          (@AlignedTraceChunk cost Γ F Δ fuel entry statement middle exit pre
            middle_assertion post stack stack_out certificate derivation
            aligned lifo rest chunk Hchunk rest_tree Hrest aligned_rest).

  (** [append_suffix]'s own footprint is exactly the union of its two
      pieces' footprints -- a direct induction on the first suffix, no
      restructuring of the underlying certificates involved. *)
  Lemma suffix_footprint_append_eq
      {cost Γ entry middle exit}
      (first : RuntimeAdapter.certificate_suffix cost Γ entry middle)
      (second : RuntimeAdapter.certificate_suffix cost Γ middle exit) :
    Normalized.suffix_footprint (RuntimeAdapter.append_suffix first second) =
      Normalized.suffix_footprint first ∪ Normalized.suffix_footprint second.
  Proof.
    induction first as
      [state|fuel entry0 statement middle0 exit0 certificate rest IHrest];
      simpl.
    - rewrite union_empty_l_L. reflexivity.
    - rewrite IHrest. rewrite union_assoc_L. reflexivity.
  Qed.

  (** [suffix_expands]'s [flat] side has a footprint no larger than its
      [source] side: [ExpandsSequence] only adds redundant envelope terms
      (the merged [CertSequence]'s own entry/exit mask and open set, both
      already implied by its two sub-certificates' own footprints), so this
      is [⊆], not the stronger [=] -- exactly what's needed to bound a
      normalized-away prefix's footprint by the original, pre-normalization
      suffix's. *)
  Lemma suffix_footprint_expands_subseteq
      {cost Γ entry exit}
      {flat source : RuntimeAdapter.certificate_suffix cost Γ entry exit} :
    RuntimeAdapter.suffix_expands cost Γ entry exit flat source ->
    Normalized.suffix_footprint flat ⊆ Normalized.suffix_footprint source.
  Proof.
    intros Hexpand. induction Hexpand.
    - intros x Hx. exact Hx.
    - simpl.
      intros x Hx. apply elem_of_union in Hx as [HxA | HxBC].
      + apply elem_of_union_l. apply elem_of_union_r. apply elem_of_union_l.
        exact HxA.
      + apply elem_of_union in HxBC as [HxB | HxC].
        * apply elem_of_union_l. apply elem_of_union_r. apply elem_of_union_r.
          exact HxB.
        * apply elem_of_union_r. exact HxC.
    - simpl.
      intros x Hx. apply elem_of_union in Hx as [Hx1 | Hx2].
      + apply elem_of_union_l. exact Hx1.
      + apply elem_of_union_r. apply IHHexpand. exact Hx2.
    - etransitivity; eauto.
  Qed.

  (** An [aligned_focused_close_split]'s own prefix footprint is bounded by
      the original suffix's, composing the two facts above: the prefix's
      footprint sits inside [append_suffix prefix rest]'s (via
      [suffix_footprint_append_eq]), which [suffix_expands]'s own
      [aligned_split_source_expansion] bounds by the original, unsplit
      suffix's (via [suffix_footprint_expands_subseteq]). *)
  Lemma aligned_focused_close_split_prefix_footprint_subseteq
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (split : aligned_focused_close_split aligned_trace) :
    Normalized.suffix_footprint
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
        (aligned_split_prefix _ split)) ⊆
    Normalized.suffix_footprint source.
  Proof.
    etransitivity;
      last exact (suffix_footprint_expands_subseteq
        (aligned_split_source_expansion _ split)).
    rewrite suffix_footprint_append_eq. apply union_subseteq_l.
  Qed.

  (** Companion to the lemma above, for the split's *rest* piece instead of
      its prefix -- same composition, [union_subseteq_r] in place of
      [union_subseteq_l]. *)
  Lemma aligned_focused_close_split_rest_footprint_subseteq
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (split : aligned_focused_close_split aligned_trace) :
    Normalized.suffix_footprint
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
        (aligned_split_rest _ split)) ⊆
    Normalized.suffix_footprint source.
  Proof.
    etransitivity;
      last exact (suffix_footprint_expands_subseteq
        (aligned_split_source_expansion _ split)).
    rewrite suffix_footprint_append_eq. apply union_subseteq_r.
  Qed.

  (** The Iris atomic-bracket obligation a [linear_ordinary_close] witness
      needs at its own eventual [AlignedTraceAccess]: the combined erased
      program of the *first-close bracket* -- [linear_body]'s own split
      prefix, up to and including the matching fold -- must be Atomic when
      physical at all. Unlike [linear_ordinary_open_ghost] this covers the
      genuinely physical case: the bracket closes back to the outer mask by
      construction (via the matching fold), so [wp_atomic] applies to it
      directly, no CPS handoff needed for *this* piece. Only the region
      *after* the close ([aligned_split_rest], covered by
      [linear_ordinary_close_cont] below) is left open-ended, exactly as
      [Section LinearUnfoldSeam]'s own [Hatomic] Context premise already
      assumed for its one fixed branch -- this generalizes that premise
      over an arbitrary [linear_ordinary_close] branch. Deriving it from the
      cost model (item 3's plan step 3) is separate, later work; this stays
      an assumed premise of the refinement for now, mirroring [Section
      LinearUnfoldSeam] exactly. *)
  Definition linear_ordinary_close_atomic
      {cost Γ F Δ tail entry pre exit post stack_out source tree suffix
        trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre tail exit post
        stack_out None tail source tree suffix trace}
      (linear : linear_ordinary_close aligned_trace) : Prop.
  Proof.
    induction linear as
      [cost Γ F Δ fuel entry node invariant arguments opened store body view
         step available instantiated tail exit post stack_out rest body_tree
         Hbody aligned_body linear_body
      |cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
         stack stack_out certificate derivation aligned lifo rest chunk
         Hchunk rest_tree Hrest aligned_rest linear' IH].
    - exact (forall (runtime : Validity.Model.stack_context Γ) statement,
        ConcreteOrdinaryTrace.source_runtime
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            (aligned_split_prefix _
              (aligned_focused_close_split_of_linear linear_body)))
          runtime = Some statement ->
        @Atomic Runtime.LegacyLang.simp_lang WeaklyAtomic statement).
    - exact IH.
  Defined.

  (** The externally-supplied continuation obligation a [linear_ordinary_
      close] witness needs: a plain refinement of whatever comes *after*
      the witness's own first matching close ([linear_body]'s own split
      rest, [aligned_split_rest] -- an arbitrary, independently-normalized
      [None]-mode trace, exactly [Section LinearUnfoldSeam]'s own [Hcont]
      parameter, generalized over the branch). This is the CPS handoff:
      the caller supplies this fact (from whatever further induction is
      available to them -- e.g. the top-level [aligned_trace_runtime_
      refinement_complete] assembly), not this development. Parametrized
      by the same [ambient]/[final_mask]/[runtime]/[formals]/[binders]/
      [atoms]/[carried]/[final] the main refinement below threads through,
      since prefix chunks before the access don't change what this
      continuation needs to say -- only the access case actually
      constrains it. *)
  Definition linear_ordinary_close_cont
      {cost Γ F Δ tail entry pre exit post stack_out source tree suffix
        trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre tail exit post
        stack_out None tail source tree suffix trace}
      (linear : linear_ordinary_close aligned_trace)
      (ambient final_mask : coPset) : Prop.
  Proof.
    induction linear as
      [cost Γ F Δ fuel entry node invariant arguments opened store body view
         step available instantiated tail exit post stack_out rest body_tree
         Hbody aligned_body linear_body
      |cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
         stack stack_out certificate derivation aligned lifo rest chunk
         Hchunk rest_tree Hrest aligned_rest linear' IH].
    - exact (let split := aligned_focused_close_split_of_linear linear_body in
        forall (runtime : Validity.Model.stack_context Γ)
          (formals : Runtime.Core.formal_env F)
          (binders : Runtime.Core.binder_env Δ) (atoms : Runtime.Core.atom_env)
          (carried final : iProp Resources.Σ),
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms
           (aligned_split_close_assertion _ split) ∗
         Validity.World.access_stack_interp atoms ambient tail ∗ carried) ⊢
        Validity.runtime_option_wp
          (Validity.Model.enabled_runtime_mask ambient
            (RuntimeAdapter.Atomicity.analysis_open entry)) final_mask
          (ConcreteOrdinaryTrace.source_runtime
            (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
              (aligned_split_rest _ split)) runtime)
          final).
    - exact IH.
  Defined.

  (** The plain (non-CPS-for-the-branch, but CPS-for-the-continuation)
      runtime refinement of a [linear_ordinary_close] witness: threads
      resources from [pre]/[tail] at [entry], through the ordinary prefix
      chunks, the unfold, and the first-close bracket, up to whatever the
      externally-supplied [linear_ordinary_close_cont] establishes about
      the post-close continuation -- landing at [final]/[final_mask]. This
      generalizes [Section LinearUnfoldSeam]'s own
      [aligned_seam_runtime_refinement_unfold_linear] (a single fixed
      [unfold I] branch) to admit ordinary chunks before the access, per
      item 3's plan step 4. *)
  Definition linear_ordinary_close_source_refinement
      {cost Γ F Δ tail entry pre exit post stack_out source tree suffix
        trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre tail exit post
        stack_out None tail source tree suffix trace}
      (linear : linear_ordinary_close aligned_trace)
      (ambient : coPset) : Prop :=
    (* [Hcost]/[Hnotatomic] are needed to bridge this theorem's own
       [source]-based conclusion to the [OrdinaryCloseAccess] branch's own
       split (via [linear_focused_close_split_source_runtime]), mirroring
       exactly how [aligned_seam_runtime_refinement] already takes
       [runtime_cost_model_sound] as its own first premise. *)
    Validity.Model.runtime_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.analysis_in_atomic entry = false ->
    linear_ordinary_close_atomic linear ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) tail ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source)
      ⊆ ambient ->
    forall (final_mask : coPset),
    linear_ordinary_close_cont linear ambient final_mask ->
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env)
      (carried final : iProp Resources.Σ),
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient tail ∗ carried) ⊢
    Validity.runtime_option_wp
      (Validity.Model.active_runtime_mask ambient entry) final_mask
      (ConcreteOrdinaryTrace.source_runtime source runtime) final.

  Lemma linear_ordinary_close_source_refinement_complete
      {cost Γ F Δ tail entry pre exit post stack_out source tree suffix
        trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre tail exit post
        stack_out None tail source tree suffix trace}
      (linear : linear_ordinary_close aligned_trace) (ambient : coPset) :
    linear_ordinary_close_source_refinement linear ambient.
  Proof.
    induction linear as
      [cost Γ F Δ fuel entry node invariant arguments opened store body view
         step available instantiated tail exit post stack_out rest body_tree
         Hbody aligned_body linear_body
      |cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
         stack stack_out certificate derivation aligned lifo rest chunk
         Hchunk rest_tree Hrest aligned_rest linear' IH].
    - (* OrdinaryCloseAccess: structurally identical to Section
         LinearUnfoldSeam's own Qed'd proof (a fixed unfold, exactly as
         here -- not a generalization over an arbitrary access node), with
         one extra bridge: [linear_body]'s own "source" field (an
         [aligned_operational_suffix]-level statement) is not itself
         split into prefix/rest -- [linear_focused_close_split_source_
         runtime] rewrites it into [combine(split.prefix, split.rest)]
         first, sidestepping [combine_runtime_statements]'s general
         non-associativity via the sparse (one side [None]) case. From
         there: build the closing net's own Hoare-triple bridge
         ([Hmiddle], via [linear_focused_close_source_refinement_complete]
         on [linear_body]); retarget its exit mask back to [entry]'s
         ([Hclosed_active], since closing restores [analysis_open]); frame
         in the externally-supplied continuation ([Hweaken], mirroring
         Section LinearUnfoldSeam's own construction); then discharge the
         physical unfold step itself via [runtime_option_wp_sequence] +
         [runtime_option_wp_atomic_mask_change] (atomicity supplied by
         [Hatomic], already stated over [aligned_split_prefix] alone,
         resolved automatically against context) and
         [unfold_node_runtime_refinement]. *)
      unfold linear_ordinary_close_source_refinement. simpl.
      unfold linear_ordinary_close_atomic, linear_ordinary_close_cont.
      cbv zeta beta. simpl.
      intros Hcost Hnotatomic Hatomic Hwf Hstack Hfootprint final_mask Hcont
        runtime formals binders atoms carried final.
      simpl.
      have Hwf_opened : RuntimeAdapter.Atomicity.state_wf opened.
      { exact (RuntimeAdapter.Atomicity.open_invariant_preserves_wf invariant
          entry opened Hwf step). }
      have Hopen_success := RuntimeAdapter.Atomicity.open_invariant_success
        invariant entry opened step.
      have Hstack_opened : RuntimeAdapter.Atomicity.access_stack_consistent
          (RuntimeAdapter.Atomicity.analysis_open opened)
          ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail).
      { split; [exact (proj1 Hopen_success)|].
        split; [exact (proj2 (proj2 (proj2 Hopen_success)))|exact Hstack]. }
      have Hnotatomic_opened : RuntimeAdapter.Atomicity.analysis_in_atomic
          opened = false.
      { unfold RuntimeAdapter.Atomicity.open_invariant in step.
        destruct (bool_decide
          (invariant ∈ RuntimeAdapter.Atomicity.analysis_open entry));
          try discriminate step.
        destruct (bool_decide
          (invariant ∈ RuntimeAdapter.Atomicity.analysis_mask entry));
          try discriminate step.
        injection step as step.
        subst opened.
        exact Hnotatomic. }
      have Hsource := linear_focused_close_split_source_runtime linear_body
        Hcost Hwf_opened Hstack_opened Hnotatomic_opened runtime.
      rewrite Hsource.
      simpl.
      remember (aligned_focused_close_split_of_linear linear_body) as
        split_val eqn:Hsplit.
      destruct split_val as
        [closed close_assertion prefix rest' prefix_tree rest_tree'
          prefix_trace rest_trace aligned_prefix aligned_rest' expansion].
      simpl in Hcont |- *.
      have Hid : forall X : option Runtime.LegacyLang.runtime_stmt,
          match X with Some a => Some a | None => None end = X.
      { intros X. destruct X; reflexivity. }
      destruct Hopen_success as (Hopen_not & Havailable & Hmask_eq &
        Hopen_eq2).
      have Hfootprint_mem : invariant ∈
          RuntimeAdapter.Atomicity.certificate_footprint
            (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
              (Runtime.IR.TUnfold node invariant arguments) invariant opened
              view step).
      { simpl.
        apply elem_of_union_l. apply elem_of_union_l. apply elem_of_union_l.
        apply elem_of_union_l. exact Havailable. }
      have Hcert_envelope : Validity.Model.runtime_mask
          (RuntimeAdapter.Atomicity.certificate_footprint
            (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
              (Runtime.IR.TUnfold node invariant arguments) invariant opened
              view step)) ⊆ ambient.
      { etransitivity; [| exact Hfootprint].
        apply Validity.Model.runtime_mask_mono. apply union_subseteq_l. }
      have Hnamespace : ↑(Resources.invariant_namespace invariant) ⊆
          Validity.Model.active_runtime_mask ambient entry.
      { exact (Validity.invariant_namespace_active_from_footprint _ ambient
          invariant Hfootprint_mem Hopen_not Hcert_envelope). }
      have Hprefix_envelope : Validity.Model.runtime_mask
          (Normalized.suffix_footprint
            (Erasure.certificate_suffix_of_aligned_operational_suffix
              prefix)) ⊆ ambient.
      { have Hprefix_envelope0 : Validity.Model.runtime_mask
            (Normalized.suffix_footprint
              (Erasure.certificate_suffix_of_aligned_operational_suffix
                (aligned_split_prefix _ (aligned_focused_close_split_of_linear
                  linear_body)))) ⊆ ambient.
        { etransitivity;
            [apply Validity.Model.runtime_mask_mono;
              exact (aligned_focused_close_split_prefix_footprint_subseteq
                (aligned_focused_close_split_of_linear linear_body))
            |].
          etransitivity;
            [apply Validity.Model.runtime_mask_mono, union_subseteq_r
            |exact Hfootprint]. }
        rewrite <- Hsplit in Hprefix_envelope0.
        simpl in Hprefix_envelope0.
        exact Hprefix_envelope0. }
      have Hmiddle :
          (Validity.global_world_context atoms ∗
           Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
             runtime formals binders atoms
             (Runtime.Translation.Assertions.AAnd
               (Runtime.Translation.Assertions.AStack store) body) ∗
           Validity.World.access_stack_interp atoms ambient
             ((invariant, RuntimeAdapter.Atomicity.analysis_open entry)
               :: tail)) ⊢
          ConcreteOrdinaryTrace.source_translated_wp
            (Erasure.certificate_suffix_of_aligned_operational_suffix
              prefix) runtime ambient
            (Validity.global_world_context atoms ∗
             Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
               runtime formals binders atoms close_assertion ∗
             Validity.World.access_stack_interp atoms ambient tail).
      { have Hcomplete := linear_focused_close_source_refinement_complete
          linear_body ambient.
        unfold linear_focused_close_source_refinement in Hcomplete.
        cbv zeta in Hcomplete. rewrite <- Hsplit in Hcomplete.
        simpl in Hcomplete.
        have Hopen_success := RuntimeAdapter.Atomicity.open_invariant_success
          invariant entry opened step.
        apply Hcomplete.
        - exact (RuntimeAdapter.Atomicity.open_invariant_preserves_wf
            invariant entry opened Hwf step).
        - split; [exact (proj1 Hopen_success)|].
          split; [exact (proj2 (proj2 (proj2 Hopen_success)))|exact Hstack].
        - exact Hprefix_envelope. }
      unfold ConcreteOrdinaryTrace.source_translated_wp in Hmiddle.
      have Hclosed_open := linear_focused_close_split_close_open linear_body.
      rewrite <- Hsplit in Hclosed_open. simpl in Hclosed_open.
      have Hclosed_active : Validity.Model.active_runtime_mask ambient closed
          = Validity.Model.active_runtime_mask ambient entry.
      { apply Validity.Model.active_runtime_mask_same_open.
        exact Hclosed_open. }
      rewrite Hclosed_active in Hmiddle.
      have Hweaken :
          (Validity.global_world_context atoms ∗
           Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
             runtime formals binders atoms
             (Runtime.Translation.Assertions.AAnd
               (Runtime.Translation.Assertions.AStack store) body) ∗
           Validity.World.access_stack_interp atoms ambient
             ((invariant, RuntimeAdapter.Atomicity.analysis_open entry)
               :: tail) ∗ carried) ⊢
          Validity.runtime_option_wp
            (Validity.Model.active_runtime_mask ambient opened)
            (Validity.Model.active_runtime_mask ambient opened)
            (ConcreteOrdinaryTrace.source_runtime
              (Erasure.certificate_suffix_of_aligned_operational_suffix
                prefix) runtime)
            (|={Validity.Model.active_runtime_mask ambient opened,
                Validity.Model.active_runtime_mask ambient entry}=>
             Validity.runtime_option_wp
               (Validity.Model.active_runtime_mask ambient entry) final_mask
               (ConcreteOrdinaryTrace.source_runtime
                 (Erasure.certificate_suffix_of_aligned_operational_suffix
                   rest') runtime)
               final).
      { iIntros "[Hworld [Hpost [Haccess Hcarried]]]".
        iApply runtime_option_wp_retarget_exit.
        iApply (Validity.runtime_option_wp_mono with
          "[Hworld Hpost Haccess Hcarried]");
          last (iApply Validity.runtime_option_wp_frame;
            iSplitL "Hworld Hpost Haccess";
            [iApply (Hmiddle with "[$Hworld $Hpost $Haccess]")
              |iExact "Hcarried"]).
        iIntros "[[Hworld' [Hpost' Haccess']] Hcarried']".
        unfold Validity.Model.active_runtime_mask.
        iApply Hcont. iFrame.
        iExact "Hcarried'". }
      iIntros "[Hworld [Hpre [Haccess Hcarried]]]".
      rewrite Hid.
      iApply Validity.runtime_option_wp_sequence.
      iApply (Validity.runtime_option_wp_atomic_mask_change _
        (Validity.Model.active_runtime_mask ambient opened)).
      { iPoseProof (ConcreteAccessNodes.unfold_node_runtime_refinement
          (node := node) store body entry opened ambient tail step Hnamespace
          instantiated runtime formals binders atoms
          with "[$Hworld $Hpre $Haccess]") as "Hopen".
        iMod "Hopen" as "[Hworld' [Hpost Haccess']]".
        iModIntro.
        iApply (Hweaken with "[$Hworld' $Hpost $Haccess' $Hcarried]").
        Unshelve. }
    - (* OrdinaryPrefix: the existing source-level prepend lemma fixes the
         suffix's exit mask, whereas this CPS theorem exposes an arbitrary
         [final_mask].  Compose the head refinement with [IH] directly at
         the [runtime_option_wp] layer so the external exit mask is
         preserved. *)
      unfold linear_ordinary_close_source_refinement. simpl.
      intros Hcost Hnotatomic Hatomic Hwf Hstack Hfootprint final_mask Hcont
        runtime formals binders atoms carried final.
      have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle :=
        RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry statement
          middle Hwf certificate.
      have Hmiddle_stack : RuntimeAdapter.Atomicity.access_stack_consistent
          (RuntimeAdapter.Atomicity.analysis_open middle) stack :=
        RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate stack stack Hwf lifo Hstack.
      have Hmiddle_notatomic :
          RuntimeAdapter.Atomicity.analysis_in_atomic middle = false.
      { eapply Validity.certificate_preserves_nonatomic; eauto. }
      have Hrest_envelope : Validity.Model.runtime_mask
          (Normalized.suffix_footprint
            (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
              rest)) ⊆ ambient.
      { etrans; last exact Hfootprint.
        apply Validity.Model.runtime_mask_mono. apply union_subseteq_r. }
      unfold linear_ordinary_close_source_refinement in IH.
      have Hhead_envelope : Validity.Model.runtime_mask
          (RuntimeAdapter.Atomicity.certificate_footprint certificate)
          ⊆ ambient.
      { etrans; last exact Hfootprint.
        apply Validity.Model.runtime_mask_mono. apply union_subseteq_l. }
      have Hopen : RuntimeAdapter.Atomicity.analysis_open entry =
          RuntimeAdapter.Atomicity.analysis_open middle.
      { eapply balanced_certificate_open_equal; eauto. }
      have Hactive : Validity.Model.active_runtime_mask ambient middle =
          Validity.Model.active_runtime_mask ambient entry.
      { apply Validity.Model.active_runtime_mask_same_open.
        symmetry. exact Hopen. }
      have Hhead := aligned_preserving_chunk_runtime_refinement Hchunk
        derivation aligned lifo Hwf runtime formals binders atoms ambient
        Hhead_envelope.
      unfold Validity.translated_runtime_wp in Hhead.
      rewrite Hactive in Hhead.
      iIntros "[Hworld [Hpre [Haccess Hcarried]]]".
      iApply Validity.runtime_option_wp_sequence.
      iApply (Validity.runtime_option_wp_mono with
        "[Hworld Hpre Haccess Hcarried]");
        last (iApply Validity.runtime_option_wp_frame;
          iSplitL "Hworld Hpre Haccess";
          [iApply (Hhead with "[$Hworld $Hpre $Haccess]")
          |iExact "Hcarried"]).
      iIntros "[[Hworld [Hpost Haccess]] Hcarried]".
      rewrite <- Hactive.
      iApply (IH Hcost Hmiddle_notatomic Hatomic Hmiddle_wf Hmiddle_stack
        Hrest_envelope final_mask Hcont runtime formals binders atoms carried
        final with "[$Hworld $Hpost $Haccess $Hcarried]").
  Qed.

  (** The [AlignedConditional]-leaf recipe: builds the seam-CPS leaf
      obligation from the two branches' own alignment/lifo evidence and one
      shared, [linear_focused_close]-restricted closing witness for
      [rest_suffix] ([linear_rest]) -- matching item 3's own scope
      throughout ("the linear closing case"). [Hthen_seam]/[Helse_seam] are
      built internally from [linear_rest] (not taken as opaque, externally
      pre-built [aligned_seam_trace] records): since both branches must
      agree on the very same closing split of [rest_suffix], building both
      seams from the one [linear_rest] witness here rules out two
      independently-supplied records silently carrying different splits.

      [Hcont_seam] -- not this lemma's own generic [Hcont] premise (that one
      is a black-box fact about the *whole*, pre-close [rest_suffix],
      exactly analogous to how [aligned_certificate_seam_frame]/
      [_consequence] use their own [Hcont]) -- is the *post-close*
      continuation [aligned_seam_runtime_refinement] itself needs
      internally, mirroring [linear_ordinary_close_cont]'s own role
      exactly: a fact about [aligned_split_rest] alone, at the *restored*
      outer mask. It cannot be derived from the generic [Hcont] (Iris's
      [wp] does not invert), so it is supplied here directly, deferred like
      [linear_ordinary_close_cont] to whoever eventually discharges steps
      6-8 for a concrete continuation past this conditional. This lemma's
      own [Hcont] premise (from [aligned_certificate_seam_refinement]'s own
      shape) consequently goes unused -- the split-aware [Hcont_seam] does
      its job instead.

      [Hthen_sparse]/[Helse_sparse] are the CertConditional-seam analogue of
      [linear_ordinary_close_atomic]'s own [Hatomic]: item 3's "at most one
      physical step per still-open access interval" cost-model invariant
      also applies across the branch/close-prefix boundary here, but
      deriving that formally would mean re-running the whole chunk-level
      sparsity argument ([linear_prefix_chunk_sparse] and friends) one
      level up, for an arbitrary branch certificate rather than one
      preserving chunk -- out of scope for this recipe, so, exactly like
      [Hatomic], taken as a caller-supplied premise and deferred. *)
  Lemma runtime_mask_union_subseteq (X Y : gset typed_core.TypedCore.inv_id) :
    Validity.Model.runtime_mask (X ∪ Y) ⊆
      Validity.Model.runtime_mask X ∪ Validity.Model.runtime_mask Y.
  Proof.
    unfold Validity.Model.runtime_mask.
    have Hinv : Validity.Model.invariant_mask (X ∪ Y) ⊆
        Validity.Model.invariant_mask X ∪ Validity.Model.invariant_mask Y.
    { revert Y. induction X as [|x X Hx IHX] using set_ind_L; intros Y.
      - rewrite left_id_L. set_solver.
      - rewrite <- union_assoc_L.
        rewrite (Validity.Model.invariant_mask_union_singleton x (X ∪ Y)).
        rewrite (Validity.Model.invariant_mask_union_singleton x X).
        specialize (IHX Y). set_solver. }
    set_solver.
  Qed.

  Lemma aligned_conditional_seam_core_from_branch_traces
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel state node store frame condition then_branch else_branch
        then_exit else_exit post view then_certificate else_certificate
        open_equal atomic_equal branch_mask then_derivation else_derivation
        then_mask else_mask}
      (then_aligned : Validity.Certified.certificate_hoare_aligned cost
        then_certificate
        (Validity.Certified.hoare_mask_transport then_derivation eq_refl
          (eq_sym then_mask)))
      (else_aligned : Validity.Certified.certificate_hoare_aligned cost
        else_certificate
        (Validity.Certified.hoare_mask_transport else_derivation eq_refl
          (eq_sym else_mask)))
      {invariant : typed_core.TypedCore.inv_id}
      {outer : gset typed_core.TypedCore.inv_id}
      {tail : list RuntimeAdapter.Atomicity.access_marker}
      (then_lifo : RuntimeAdapter.Atomicity.lifo_certificate then_certificate
        tail ((invariant, outer) :: tail))
      (else_lifo : RuntimeAdapter.Atomicity.lifo_certificate else_certificate
        tail ((invariant, outer) :: tail))
      {join_assertion : Runtime.Translation.Assertions.assertion Γ F Δ}
      {final_exit : RuntimeAdapter.Atomicity.analysis_state}
      {final_post : Runtime.Translation.Assertions.assertion Γ F Δ}
      {final_stack_out : list RuntimeAdapter.Atomicity.access_marker}
      {rest_suffix : Validity.aligned_operational_suffix cost Γ F Δ
        (RuntimeAdapter.conditional_join then_exit else_exit) join_assertion
        ((invariant, outer) :: tail) final_exit final_post final_stack_out}
      {rest_tree}
      {rest_trace}
      {rest_aligned_trace : aligned_net_trace cost Γ F Δ
        (RuntimeAdapter.conditional_join then_exit else_exit) join_assertion
        ((invariant, outer) :: tail) final_exit final_post final_stack_out
        (Some (invariant, outer)) tail
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          rest_suffix) rest_tree rest_suffix rest_trace}
      (linear_rest : linear_focused_close rest_aligned_trace)
      {ambient : coPset}
      (Hwf : RuntimeAdapter.Atomicity.state_wf state)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open state) tail)
      (Hnotatomic : RuntimeAdapter.Atomicity.analysis_in_atomic
        (RuntimeAdapter.conditional_join then_exit else_exit) = false)
      (Hatomic : forall (runtime : Validity.Model.stack_context Γ) statement,
        ConcreteOrdinaryTrace.source_runtime
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            (aligned_split_prefix _
              (aligned_focused_close_split_of_linear linear_rest))) runtime =
          Some statement ->
        @Atomic Runtime.LegacyLang.simp_lang WeaklyAtomic statement)
      (Hrest_footprint : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest_suffix)) ⊆ ambient)
      (Hthen_sparse : forall runtime : Validity.Model.stack_context Γ,
        Validity.certificate_runtime_statement then_certificate runtime =
          None \/
        ConcreteOrdinaryTrace.source_runtime
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            (aligned_split_prefix _
              (aligned_focused_close_split_of_linear linear_rest))) runtime =
          None)
      (Helse_sparse : forall runtime : Validity.Model.stack_context Γ,
        Validity.certificate_runtime_statement else_certificate runtime =
          None \/
        ConcreteOrdinaryTrace.source_runtime
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            (aligned_split_prefix _
              (aligned_focused_close_split_of_linear linear_rest))) runtime =
          None)
      (Hcont_seam : forall (final_mask : coPset)
        (runtime : Validity.Model.stack_context Γ)
        (formals : Runtime.Core.formal_env F)
        (binders : Runtime.Core.binder_env Δ) (atoms : Runtime.Core.atom_env)
        (carried final : iProp Resources.Σ),
        (Validity.global_world_context atoms ∗
         Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
           runtime formals binders atoms
           (aligned_split_close_assertion _
             (aligned_focused_close_split_of_linear linear_rest)) ∗
         Validity.World.access_stack_interp atoms ambient tail ∗ carried) ⊢
        Validity.runtime_option_wp
          (Validity.Model.enabled_runtime_mask ambient outer) final_mask
          (ConcreteOrdinaryTrace.source_runtime
            (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
              (aligned_split_rest _
                (aligned_focused_close_split_of_linear linear_rest)))
            runtime)
          final)
      (Hthen_seam : aligned_seam_runtime_refinement
        (@Build_aligned_seam_trace cost Γ F Δ invariant outer tail _ _ _ _
          (Validity.aligned_singleton_suffix then_certificate _ then_aligned
            then_lifo)
          (RuntimeAdapter.conditional_join then_exit else_exit) _ _ _ _
          rest_suffix ambient
          (aligned_total_ordinary _
            (aligned_singleton_total_normalization then_aligned then_lifo
              Hwf Hstack))
          (eq_refl : Validity.Model.active_runtime_mask ambient then_exit =
            Validity.Model.active_runtime_mask ambient
              (RuntimeAdapter.conditional_join then_exit else_exit))
          (existT rest_tree (existT rest_trace (existT rest_aligned_trace
            (aligned_focused_close_split_of_linear linear_rest))))))
      (Helse_seam : aligned_seam_runtime_refinement
        (@Build_aligned_seam_trace cost Γ F Δ invariant outer tail _ _ _ _
          (Validity.aligned_singleton_suffix else_certificate _ else_aligned
            else_lifo)
          (RuntimeAdapter.conditional_join then_exit else_exit) _ _ _ _
          rest_suffix ambient
          (aligned_total_ordinary _
            (aligned_singleton_total_normalization else_aligned else_lifo
              Hwf Hstack))
          (Validity.Model.active_runtime_mask_same_open ambient else_exit
            then_exit (eq_sym open_equal))
          (existT rest_tree (existT rest_trace (existT rest_aligned_trace
            (aligned_focused_close_split_of_linear linear_rest)))))) :
    aligned_certificate_seam_refinement
      (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state
        (Runtime.IR.TIf node condition then_branch else_branch) then_branch
        else_branch then_exit else_exit view then_certificate else_certificate
        open_equal atomic_equal)
      (Validity.Certified.hoare_mask_transport
        (Validity.Certified.Rules.ConditionalRule node store frame condition
          then_branch else_branch post
          (RuntimeAdapter.Atomicity.analysis_mask state) branch_mask
          then_derivation
          else_derivation) eq_refl
        (Validity.Certified.conditional_analysis_mask state then_exit
          else_exit branch_mask then_mask else_mask))
      tail ((invariant, outer) :: tail) (conj then_lifo else_lifo)
      (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
        rest_suffix)
      ambient.
  Proof.
    intros Hcost Hwf' Hstack' Haligned runtime formals binders atoms
      Hfootprint final_mask carried final Hcont.
    have Hstack_join : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open
          (RuntimeAdapter.conditional_join then_exit else_exit))
        ((invariant, outer) :: tail).
    { exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state
          (Runtime.IR.TIf node condition then_branch else_branch) then_branch
          else_branch then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal)
        tail ((invariant, outer) :: tail) Hwf (conj then_lifo else_lifo)
        Hstack). }
    have Hsource := linear_focused_close_split_source_runtime linear_rest
      Hcost
      (RuntimeAdapter.Atomicity.certificate_preserves_wf cost state
        (Runtime.IR.TIf node condition then_branch else_branch)
        (RuntimeAdapter.conditional_join then_exit else_exit) Hwf
        (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state
          (Runtime.IR.TIf node condition then_branch else_branch) then_branch
          else_branch then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal))
      Hstack_join Hnotatomic runtime.
    remember (aligned_focused_close_split_of_linear linear_rest) as split_val
      eqn:Hsplit.
    destruct split_val as
      [closed close_assertion prefix rest' prefix_tree rest_tree'
        prefix_trace rest_trace' aligned_prefix aligned_rest' expansion].
    simpl in Hsource, Hcont_seam.
    have Hthen_footprint : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint then_certificate)
        ⊆ ambient.
    { etrans; last exact Hfootprint. apply Validity.Model.runtime_mask_mono.
      simpl. etransitivity; [apply union_subseteq_l|apply union_subseteq_r]. }
    have Helse_footprint : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint else_certificate)
        ⊆ ambient.
    { etrans; last exact Hfootprint. apply Validity.Model.runtime_mask_mono.
      simpl. etransitivity; [apply union_subseteq_r|apply union_subseteq_r]. }
    have Hprefix_envelope0 : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (Erasure.certificate_suffix_of_aligned_operational_suffix
            (aligned_split_prefix _ (aligned_focused_close_split_of_linear
              linear_rest)))) ⊆ ambient.
    { etransitivity;
        [apply Validity.Model.runtime_mask_mono;
          exact (aligned_focused_close_split_prefix_footprint_subseteq
            (aligned_focused_close_split_of_linear linear_rest))
        |exact Hrest_footprint]. }
    rewrite <- Hsplit in Hprefix_envelope0. simpl in Hprefix_envelope0.
    rename Hprefix_envelope0 into Hprefix_envelope.
    have Hrest_envelope0 : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (Erasure.certificate_suffix_of_aligned_operational_suffix
            (aligned_split_rest _ (aligned_focused_close_split_of_linear
              linear_rest)))) ⊆ ambient.
    { etransitivity;
        [apply Validity.Model.runtime_mask_mono;
          exact (aligned_focused_close_split_rest_footprint_subseteq
            (aligned_focused_close_split_of_linear linear_rest))
        |exact Hrest_footprint]. }
    rewrite <- Hsplit in Hrest_envelope0. simpl in Hrest_envelope0.
    rename Hrest_envelope0 into Hrest_envelope.
    have Hthen_seam_footprint : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (RuntimeAdapter.singleton_suffix then_certificate) ∪
         Normalized.suffix_footprint
          (Erasure.certificate_suffix_of_aligned_operational_suffix prefix) ∪
         Normalized.suffix_footprint
          (Erasure.certificate_suffix_of_aligned_operational_suffix rest'))
        ⊆ ambient.
    { etransitivity; first apply runtime_mask_union_subseteq.
      apply union_least.
      - etransitivity; first apply runtime_mask_union_subseteq.
        apply union_least.
        + simpl. try rewrite union_empty_r_L. exact Hthen_footprint.
        + exact Hprefix_envelope.
      - exact Hrest_envelope. }
    have Helse_seam_footprint : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (RuntimeAdapter.singleton_suffix else_certificate) ∪
         Normalized.suffix_footprint
          (Erasure.certificate_suffix_of_aligned_operational_suffix prefix) ∪
         Normalized.suffix_footprint
          (Erasure.certificate_suffix_of_aligned_operational_suffix rest'))
        ⊆ ambient.
    { etransitivity; first apply runtime_mask_union_subseteq.
      apply union_least.
      - etransitivity; first apply runtime_mask_union_subseteq.
        apply union_least.
        + simpl. try rewrite union_empty_r_L. exact Helse_footprint.
        + exact Hprefix_envelope.
      - exact Hrest_envelope. }
    unshelve epose proof (Hthen_seam Hcost Hwf Hstack runtime formals binders
      atoms Hthen_seam_footprint final_mask carried final _) as Hthen_wp;
      [cbn; exact (Hcont_seam final_mask runtime formals binders atoms carried
        final)|].
    unshelve epose proof (Helse_seam Hcost Hwf Hstack runtime formals binders
      atoms Helse_seam_footprint final_mask carried final _) as Helse_wp;
      [cbn; exact (Hcont_seam final_mask runtime formals binders atoms carried
        final)|].
    cbn [aligned_seam_split aligned_seam_rest projT1 projT2
         aligned_split_prefix aligned_split_rest] in Hthen_wp, Helse_wp.
    cbn [aligned_split_close_state aligned_split_close_assertion
         aligned_split_prefix aligned_split_rest aligned_split_prefix_tree
         aligned_split_rest_tree aligned_split_prefix_trace
         aligned_split_rest_trace aligned_split_prefix_lockstep
         aligned_split_rest_lockstep aligned_split_source_expansion]
      in Hthen_wp, Helse_wp.
    have Hcombine_none_r : forall X : option Runtime.LegacyLang.runtime_stmt,
        Validity.Model.combine_runtime_statements X None = X.
    { intros X; destruct X; reflexivity. }
    cbn [Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
         Validity.aligned_singleton_suffix
         Normalized.Validity.erase_aligned_operational_suffix
         Normalized.Erasure.certificate_suffix_of_operational_suffix
         ConcreteOrdinaryTrace.source_runtime] in Hthen_wp, Helse_wp.
    unfold selected_conditional_continuation in Hthen_wp, Helse_wp.
    rewrite Hcombine_none_r in Hthen_wp.
    rewrite Hcombine_none_r in Helse_wp.
    rewrite <- (Validity.combine_runtime_statements_assoc_left_sparse _ _ _
      (Hthen_sparse runtime)) in Hthen_wp.
    rewrite <- (Validity.combine_runtime_statements_assoc_left_sparse _ _ _
      (Helse_sparse runtime)) in Helse_wp.
    cbn [aligned_split_close_state aligned_split_close_assertion
         aligned_split_prefix aligned_split_rest aligned_split_prefix_tree
         aligned_split_rest_tree aligned_split_prefix_trace
         aligned_split_rest_trace aligned_split_prefix_lockstep
         aligned_split_rest_lockstep aligned_split_source_expansion]
      in Hthen_wp, Helse_wp.
    rewrite <- Hsource in Hthen_wp.
    rewrite <- Hsource in Helse_wp.
    have Houter_eq : outer = RuntimeAdapter.Atomicity.analysis_open state.
    { exact (RuntimeAdapter.Atomicity.access_stack_consistent_functional _ _
        tail (proj2 (proj2 Hstack_join)) Hstack). }
    have HEouter : Validity.Model.enabled_runtime_mask ambient outer =
        Validity.Model.active_runtime_mask ambient state.
    { unfold Validity.Model.active_runtime_mask. rewrite Houter_eq.
      reflexivity. }
    rewrite HEouter in Hthen_wp.
    rewrite HEouter in Helse_wp.
    unfold Validity.certificate_runtime_statement.
    etrans; last eapply (Validity.runtime_wp_if_context_full runtime formals
      binders atoms store node condition then_branch else_branch
      (ConcreteOrdinaryTrace.source_runtime
        (Erasure.certificate_suffix_of_aligned_operational_suffix rest_suffix)
        runtime)
      (Validity.Model.active_runtime_mask ambient state) final_mask final
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms frame ∗
       Validity.World.access_stack_interp atoms ambient tail ∗ carried)%I).
    - iIntros "[#Hworld [[Hstack Hframe] [Haccess Hcarried]]]".
      simpl. iFrame "Hstack Hworld Hframe Haccess Hcarried".
    - intros Hcondition.
      iIntros "[Hstack [#Hworld [Hframe [Haccess Hcarried]]]]".
      iApply Hthen_wp. simpl.
      iFrame "Hworld Hstack Hframe Haccess Hcarried".
      iPureIntro. exact Hcondition.
    - intros Hcondition.
      iIntros "[Hstack [#Hworld [Hframe [Haccess Hcarried]]]]".
      iApply Helse_wp. simpl.
      iFrame "Hworld Hstack Hframe Haccess Hcarried".
      iPureIntro. rewrite Hcondition. reflexivity.
  Qed.

  (** The ghost-only obligation a [linear_ordinary_open] witness needs at
      its own eventual [AlignedTraceAccess] to have a standalone
      (non-CPS) plain refinement: the combined erased program of the
      focused body ([linear_body]'s own ["rest"]) must be [None] --
      always ghost, never physical. Ordinary-prefix chunks (outside the
      open invariant) never need this -- [OrdinaryPrefix] just recurses.

      This is *not* the general case. A focused body that erases to
      [Some statement] cannot be given a standalone outer-mask
      refinement here: [wp_atomic] can move a physical step from the
      post-unfold ("inner") mask back to the pre-unfold ("outer") mask
      only if the postcondition closes back to the outer mask, and this
      witness's own conclusion returns the still-open access frame for
      the newly unfolded invariant -- deliberately not closing. Checked
      directly (a standalone scratch goal, [P ⊢ |={inner,outer}=> P]
      given [inner ⊆ outer]): none of Iris's free mask-changing intro
      lemmas ([fupd_mask_intro_subseteq], [fupd_mask_intro_discard],
      [fupd_mask_weaken]) grant that widening without an actual matching
      close. So the physical case genuinely needs the eventual closing
      continuation supplied from outside this fragment (a CPS judgment,
      per item 3's plan) -- not a stronger version of this Prop. *)
  Definition linear_ordinary_open_ghost
      {cost Γ F Δ tail entry pre exit post stack_out source tree suffix
        trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre tail exit post
        stack_out None tail source tree suffix trace}
      (linear : linear_ordinary_open aligned_trace) : Prop.
  Proof.
    induction linear as
      [cost Γ F Δ fuel entry node invariant arguments opened store body view
         step available instantiated tail exit post stack_out rest body_tree
         Hbody aligned_body linear_body
      |cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
         stack stack_out certificate derivation aligned lifo rest chunk
         Hchunk rest_tree Hrest aligned_rest linear' IH].
    - exact (forall (runtime : Validity.Model.stack_context Γ),
        ConcreteOrdinaryTrace.source_runtime
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            rest) runtime = None).
    - exact IH.
  Defined.

  (** The plain (non-CPS) runtime refinement of a [linear_ordinary_open]
      witness, threading resources from [pre]/[tail] at [entry] all the way
      to [post]/[stack_out] at [exit] -- [stack_out] is whatever the
      eventual [AlignedTraceAccess] leaves open (via its own
      [linear_focused_open] body), not fixed to [tail]. Restricted to the
      ghost-only sub-case ([linear_ordinary_open_ghost]) -- see that
      definition's comment for why the physical case needs a CPS judgment
      instead, not a stronger version of this theorem. *)
  Definition linear_ordinary_open_ghost_source_refinement
      {cost Γ F Δ tail entry pre exit post stack_out source tree suffix
        trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre tail exit post
        stack_out None tail source tree suffix trace}
      (linear : linear_ordinary_open aligned_trace)
      (ambient : coPset) : Prop :=
    linear_ordinary_open_ghost linear ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) tail ->
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env),
    Validity.Model.runtime_mask (Normalized.suffix_footprint source)
      ⊆ ambient ->
    (Validity.global_world_context atoms ∗
     Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
       runtime formals binders atoms pre ∗
     Validity.World.access_stack_interp atoms ambient tail) ⊢
    ConcreteOrdinaryTrace.source_translated_wp source runtime ambient
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       Validity.World.access_stack_interp atoms ambient stack_out).

  Lemma linear_ordinary_open_ghost_source_refinement_complete
      {cost Γ F Δ tail entry pre exit post stack_out source tree suffix
        trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ entry pre tail exit post
        stack_out None tail source tree suffix trace}
      (linear : linear_ordinary_open aligned_trace) (ambient : coPset) :
    linear_ordinary_open_ghost_source_refinement linear ambient.
  Proof.
    induction linear as
      [cost Γ F Δ fuel entry node invariant arguments opened store body view
         step available instantiated tail exit post stack_out rest body_tree
         Hbody aligned_body linear_body
      |cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
         stack stack_out certificate derivation aligned lifo rest chunk
         Hchunk rest_tree Hrest aligned_rest linear' IH].
    - unfold linear_ordinary_open_ghost_source_refinement.
      intros Hghost Hwf Hstack runtime formals binders atoms Henvelope.
      simpl in Hghost.
      destruct (RuntimeAdapter.Atomicity.open_invariant_success invariant entry
        opened step) as (Hopen_not & Havailable & Hmask_eq & Hopen_eq).
      have Hopened_wf : RuntimeAdapter.Atomicity.state_wf opened.
      { exact (RuntimeAdapter.Atomicity.open_invariant_preserves_wf invariant
          entry opened Hwf step). }
      have Hopened_stack : RuntimeAdapter.Atomicity.access_stack_consistent
          (RuntimeAdapter.Atomicity.analysis_open opened)
          ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail).
      { rewrite Hopen_eq.
        apply RuntimeAdapter.Atomicity.access_stack_consistent_cons.
        split; [exact Hopen_not | exact Hstack]. }
      simpl in Henvelope.
      have Hfootprint_mem : invariant ∈
          RuntimeAdapter.Atomicity.certificate_footprint
            (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
              (Runtime.IR.TUnfold node invariant arguments) invariant opened
              view step).
      { simpl. apply elem_of_union_l. apply elem_of_union_l.
        apply elem_of_union_l. apply elem_of_union_l. exact Havailable. }
      have Hcert_envelope : Validity.Model.runtime_mask
          (RuntimeAdapter.Atomicity.certificate_footprint
            (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
              (Runtime.IR.TUnfold node invariant arguments) invariant opened
              view step)) ⊆ ambient.
      { etransitivity; [| exact Henvelope].
        apply Validity.Model.runtime_mask_mono. apply union_subseteq_l. }
      have Hnamespace : ↑(Resources.invariant_namespace invariant) ⊆
          Validity.Model.active_runtime_mask ambient entry.
      { exact (Validity.invariant_namespace_active_from_footprint _ ambient
          invariant Hfootprint_mem Hopen_not Hcert_envelope). }
      have Hrest_envelope : Validity.Model.runtime_mask
          (Normalized.suffix_footprint
            (Erasure.certificate_suffix_of_aligned_operational_suffix rest))
          ⊆ ambient.
      { etransitivity; [| exact Henvelope].
        apply Validity.Model.runtime_mask_mono. apply union_subseteq_r. }
      pose proof (linear_focused_open_source_refinement_complete linear_body
        ambient) as Hbody_refine.
      unfold linear_focused_open_source_refinement in Hbody_refine.
      specialize (Hbody_refine Hopened_wf Hopened_stack runtime formals binders
        atoms Hrest_envelope).
      have Hopen_same := linear_focused_open_same_open linear_body.
      have Hstack_shape := linear_focused_open_same_stack linear_body.
      have Hmask_same : Validity.Model.active_runtime_mask ambient exit =
          Validity.Model.active_runtime_mask ambient opened.
      { apply Validity.Model.active_runtime_mask_same_open. exact Hopen_same. }
      unfold ConcreteOrdinaryTrace.source_translated_wp in Hbody_refine.
      rewrite Hmask_same in Hbody_refine.
      rewrite (Hghost runtime) in Hbody_refine.
      simpl in Hbody_refine.
      unfold ConcreteOrdinaryTrace.source_translated_wp. simpl.
      rewrite (Hghost runtime). simpl.
      rewrite Hmask_same.
      rewrite Hstack_shape.
      iIntros "Hresources".
      iPoseProof (ConcreteAccessNodes.unfold_node_runtime_refinement
        (node := node) store body entry opened ambient tail step Hnamespace
        instantiated runtime formals binders atoms with "Hresources") as
        "Hopen".
      iMod "Hopen" as "Hbody".
      iSimpl in "Hbody".
      iApply (Hbody_refine with "Hbody").
    - unfold linear_ordinary_open_ghost_source_refinement.
      intros Hghost Hwf Hstack runtime formals binders atoms Henvelope.
      simpl in Hghost.
      have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle.
      { exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry
          statement middle Hwf certificate). }
      have Hmiddle_stack : RuntimeAdapter.Atomicity.access_stack_consistent
          (RuntimeAdapter.Atomicity.analysis_open middle) stack.
      { exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate stack stack Hwf lifo Hstack). }
      have Hrest_envelope : Validity.Model.runtime_mask
          (Normalized.suffix_footprint
            (Erasure.certificate_suffix_of_aligned_operational_suffix rest))
          ⊆ ambient.
      { etransitivity; [| exact Henvelope].
        apply Validity.Model.runtime_mask_mono.
        apply Normalized.suffix_footprint_rest_subset. }
      pose proof (IH Hghost Hmiddle_wf Hmiddle_stack runtime formals binders
        atoms Hrest_envelope) as Hrest_refinement.
      eapply aligned_preserving_chunk_prepend_source_runtime_refinement; eauto.
  Qed.

  (** Step 8's own top-level instance: [aligned_seam_runtime_refinement] for
      the decisive regression target's own branch shape (a single unmatched
      [unfold I]) held fixed, generalizing the continuation from step 7's
      one hand-picked atomic chunk to any [linear_focused_close] witness,
      given only that the *combined* physical program the region's own
      preserving chunks erase to is, when physical at all, [Atomic] -- the
      same side condition [ConcreteFocusedAccess.
      nonconditional_access_body_runtime_refinement] needs for its own,
      differently-shaped continuation.  Step 7's own lemma is now a
      corollary (its single [CertAtomic] chunk trivially satisfies
      [Hatomic], and its trivial empty [aligned_split_rest] makes [Hcont]
      collapse to a bare fupd) rather than a separate proof. *)
  Section LinearUnfoldSeam.
    Context {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel : nat} {node invariant arguments entry exit}
      (store : Runtime.IR.Core.symbolic_store Γ F Δ)
      (body : Runtime.Translation.Assertions.assertion Γ F Δ)
      (view : Runtime.RegionSyntax.view
        (Runtime.IR.TUnfold node invariant arguments) =
        typed_analysis_view.TypedAnalysisView.ViewUnfold invariant)
      (step : RuntimeAdapter.Atomicity.open_invariant invariant entry =
        inr exit)
      (available : invariant ∈ RuntimeAdapter.Atomicity.analysis_mask entry)
      (instantiated : Contracts.instantiated_invariant Γ F Δ
        (Logic.invariant_args invariant) invariant
        (Runtime.Validation.Hoare.symbolize_expr_list store arguments) body)
      {tail : list RuntimeAdapter.Atomicity.access_marker}
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open entry) tail)
      {rest_exit rest_post rest_stack_out}
      {suffix : Validity.aligned_operational_suffix cost Γ F Δ exit
        (Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store) body)
        ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)
        rest_exit rest_post rest_stack_out}
      {tree trace}
      {aligned_trace : @aligned_net_trace cost Γ F Δ exit
        (Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store) body)
        ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)
        rest_exit rest_post rest_stack_out
        (Some (invariant, RuntimeAdapter.Atomicity.analysis_open entry)) tail
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          suffix) tree suffix trace}
      (linear : linear_focused_close aligned_trace)
      {ambient : coPset}
      (Hnamespace : ↑(Resources.invariant_namespace invariant) ⊆
        Validity.Model.active_runtime_mask ambient entry).

    Let litmus_split := aligned_focused_close_split_of_linear linear.

    Context
      (Hatomic : forall (runtime : Validity.Model.stack_context Γ) statement,
        ConcreteOrdinaryTrace.source_runtime
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            (aligned_split_prefix _ litmus_split)) runtime = Some statement ->
        @Atomic Runtime.LegacyLang.simp_lang WeaklyAtomic statement).

    Let branch_suffix := Validity.aligned_singleton_suffix
      (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
        (Runtime.IR.TUnfold node invariant arguments) invariant exit view
        step)
      (Validity.Certified.hoare_mask_transport
        (Validity.Certified.Rules.UnfoldInvariantRule node invariant
          arguments store body (RuntimeAdapter.Atomicity.analysis_mask entry)
          available instantiated) eq_refl
        (eq_sym (Validity.Certified.unfold_analysis_mask view step)))
      (Validity.Certified.AlignedUnfold cost Γ F Δ fuel entry node invariant
        arguments exit store body view step available instantiated)
      (eq_refl :
        RuntimeAdapter.Atomicity.lifo_certificate
          (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
            (Runtime.IR.TUnfold node invariant arguments) invariant exit view
            step)
          tail
          ((invariant, RuntimeAdapter.Atomicity.analysis_open entry) :: tail)).

    Let litmus_rest_normal :
        has_aligned_focused_closing_normalization suffix.
    Proof. exact (existT _ (existT _ (existT _ litmus_split))). Defined.

    Let litmus_seam : aligned_seam_trace branch_suffix suffix ambient := {|
      aligned_seam_branch := aligned_total_ordinary _
        (aligned_singleton_total_normalization
          (Validity.Certified.AlignedUnfold cost Γ F Δ fuel entry node
            invariant arguments exit store body view step available
            instantiated)
          (eq_refl :
            RuntimeAdapter.Atomicity.lifo_certificate
              (RuntimeAdapter.Atomicity.CertUnfold cost Γ fuel entry
                (Runtime.IR.TUnfold node invariant arguments) invariant exit
                view step)
              tail
              ((invariant, RuntimeAdapter.Atomicity.analysis_open entry)
                :: tail))
          Hwf Hstack);
      aligned_seam_mask_eq := eq_refl;
      aligned_seam_rest := litmus_rest_normal;
    |}.

    Lemma aligned_seam_runtime_refinement_unfold_linear :
      aligned_seam_runtime_refinement litmus_seam.
    Proof.
      unfold aligned_seam_runtime_refinement.
      intros Hcost Hwf' Hstack' runtime formals binders atoms Hfootprint
        final_mask carried final Hcont.
      unfold selected_conditional_continuation in *.
      unfold aligned_seam_split, aligned_seam_rest, litmus_seam,
        litmus_rest_normal in *.
      simpl in *.
      remember litmus_split as split_val eqn:Hsplit.
      destruct split_val as
        [closed close_assertion prefix rest' prefix_tree rest_tree'
          prefix_trace rest_trace aligned_prefix aligned_rest' expansion].
      unfold litmus_split in Hsplit.
      simpl in Hcont |- *.
      have Hid : forall X : option Runtime.LegacyLang.runtime_stmt,
          match X with Some a => Some a | None => None end = X.
      { intros X. destruct X; reflexivity. }
      have Hmiddle :
          (Validity.global_world_context atoms ∗
           Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
             runtime formals binders atoms
             (Runtime.Translation.Assertions.AAnd
               (Runtime.Translation.Assertions.AStack store) body) ∗
           Validity.World.access_stack_interp atoms ambient
             ((invariant, RuntimeAdapter.Atomicity.analysis_open entry)
               :: tail)) ⊢
          ConcreteOrdinaryTrace.source_translated_wp
            (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
              prefix) runtime ambient
            (Validity.global_world_context atoms ∗
             Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
               runtime formals binders atoms close_assertion ∗
             Validity.World.access_stack_interp atoms ambient tail).
      { have Hcomplete := linear_focused_close_source_refinement_complete
          linear ambient.
        unfold linear_focused_close_source_refinement in Hcomplete.
        cbv zeta in Hcomplete. rewrite <- Hsplit in Hcomplete. simpl in Hcomplete.
        have Hopen_success := RuntimeAdapter.Atomicity.open_invariant_success
          invariant entry exit step.
        apply Hcomplete.
        - exact (RuntimeAdapter.Atomicity.open_invariant_preserves_wf
            invariant entry exit Hwf step).
        - split; [exact (proj1 Hopen_success)|].
          split; [exact (proj2 (proj2 (proj2 Hopen_success)))|exact Hstack].
        - etrans; last exact Hfootprint. apply Validity.Model.runtime_mask_mono.
          etrans; [apply union_subseteq_r|apply union_subseteq_l]. }
      unfold ConcreteOrdinaryTrace.source_translated_wp in Hmiddle.
      have Hclosed_open := linear_focused_close_split_close_open linear.
      rewrite <- Hsplit in Hclosed_open. simpl in Hclosed_open.
      have Hclosed_active : Validity.Model.active_runtime_mask ambient closed
          = Validity.Model.active_runtime_mask ambient entry.
      { apply Validity.Model.active_runtime_mask_same_open.
        exact Hclosed_open. }
      rewrite Hclosed_active in Hmiddle.
      have Hweaken :
          (Validity.global_world_context atoms ∗
           Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
             runtime formals binders atoms
             (Runtime.Translation.Assertions.AAnd
               (Runtime.Translation.Assertions.AStack store) body) ∗
           Validity.World.access_stack_interp atoms ambient
             ((invariant, RuntimeAdapter.Atomicity.analysis_open entry)
               :: tail) ∗ carried) ⊢
          Validity.runtime_option_wp
            (Validity.Model.active_runtime_mask ambient exit)
            (Validity.Model.active_runtime_mask ambient exit)
            (ConcreteOrdinaryTrace.source_runtime
              (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
                prefix) runtime)
            (|={Validity.Model.active_runtime_mask ambient exit,
                Validity.Model.active_runtime_mask ambient entry}=>
             Validity.runtime_option_wp
               (Validity.Model.active_runtime_mask ambient entry) final_mask
               (ConcreteOrdinaryTrace.source_runtime
                 (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
                   rest') runtime)
               final).
      { iIntros "[Hworld [Hpost [Haccess Hcarried]]]".
        iApply runtime_option_wp_retarget_exit.
        iApply (Validity.runtime_option_wp_mono with
          "[Hworld Hpost Haccess Hcarried]");
          last (iApply Validity.runtime_option_wp_frame;
            iSplitL "Hworld Hpost Haccess";
            [iApply (Hmiddle with "[$Hworld $Hpost $Haccess]")
              |iExact "Hcarried"]).
        iIntros "[[Hworld' [Hpost' Haccess']] Hcarried']".
        iApply Hcont. iFrame "Hworld' Hpost' Haccess' Hcarried'". }
      iIntros "[Hworld [Hpre [Haccess Hcarried]]]".
      iApply Validity.runtime_option_wp_sequence.
      iApply (Validity.runtime_option_wp_atomic_mask_change _
        (Validity.Model.active_runtime_mask ambient exit)).
      { intros s Hs. eapply Hatomic. simpl. rewrite Hid in Hs. exact Hs. }
      iPoseProof (ConcreteAccessNodes.unfold_node_runtime_refinement
        (node := node) store body entry exit ambient tail step Hnamespace
        instantiated runtime formals binders atoms
        with "[$Hworld $Hpre $Haccess]") as "Hopen".
      iMod "Hopen" as "[Hworld' [Hpost Haccess']]".
      iModIntro.
      rewrite Hid.
      iApply (Hweaken with "[$Hworld' $Hpost $Haccess' $Hcarried]").
    Qed.
  End LinearUnfoldSeam.

  Lemma aligned_trace_chunk_runtime_refinement
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        stack stack_out certificate derivation aligned lifo suffix chunk Hchunk
        rest_tree Hrest}
      (aligned_rest : @aligned_net_trace cost Γ F Δ middle middle_assertion
        stack exit post stack_out None stack
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          suffix) rest_tree suffix Hrest)
      (IHrest : aligned_trace_runtime_refinement aligned_rest) :
    aligned_trace_runtime_refinement
      (@AlignedTraceChunk cost Γ F Δ fuel entry statement middle exit pre
        middle_assertion post stack stack_out certificate derivation aligned
        lifo suffix chunk Hchunk rest_tree Hrest aligned_rest).
  Proof.
    intros Hcost Hwf Hstack runtime formals binders atoms ambient Henvelope.
    have Hmiddle_wf : RuntimeAdapter.Atomicity.state_wf middle.
    { exact (RuntimeAdapter.Atomicity.certificate_preserves_wf cost entry
        statement middle Hwf certificate). }
    have Hmiddle_stack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open middle) stack.
    { exact (RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
        certificate stack stack Hwf lifo Hstack). }
    have Hrest_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
            suffix)) ⊆ ambient.
    { etrans; last exact Henvelope. apply Validity.Model.runtime_mask_mono.
      apply Normalized.suffix_footprint_rest_subset. }
    pose proof (IHrest Hcost Hmiddle_wf Hmiddle_stack runtime formals binders
      atoms ambient Hrest_envelope) as Hrest_refinement.
    eapply aligned_preserving_chunk_prepend_source_runtime_refinement; eauto.
  Qed.

  Lemma closed_aligned_trace_chunk_runtime_refinement
      {cost Γ F Δ fuel entry statement middle exit pre middle_assertion post
        certificate derivation aligned lifo suffix chunk Hchunk rest_tree Hrest}
      (aligned_rest : @aligned_net_trace cost Γ F Δ middle middle_assertion []
        exit post [] None []
        (Normalized.Erasure.certificate_suffix_of_aligned_operational_suffix
          suffix) rest_tree suffix Hrest)
      (IHrest : closed_aligned_trace_runtime_refinement aligned_rest) :
    closed_aligned_trace_runtime_refinement
      (@AlignedTraceChunk cost Γ F Δ fuel entry statement middle exit pre
        middle_assertion post [] [] certificate derivation aligned lifo suffix
        chunk Hchunk rest_tree Hrest aligned_rest).
  Proof.
    exact (aligned_trace_chunk_runtime_refinement aligned_rest IHrest).
  Qed.

End AlignedTraceNormalization.

End WithRuntimeValidity.
End WithContracts.
End Make.
