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
  - apply IHtrace. eapply suffix_expands_runtime_trusted; eauto.
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

(** Proof-relevant aligned normalization.  We reuse the legacy-namespaced
    aligned zipper here only as a datatype: unlike the deprecated semantic
    path, it retains precisely the Hoare witnesses erased by certificate
    normalization.  The following base constructor is the first lockstep
    reconstruction case, exposing a matching fold at the head of an aligned
    suffix together with its remaining aligned continuation. *)
Module AlignedTraceNormalization.
  Module Validity := Normalized.Validity.
  Module Focused := Validity.LegacyFocusedAccess.

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

  (** Feasibility checkpoint for the direct normalizer.  Packaging all zipper
      indices lets its recursive definition use exactly the source-size
      measure already validated by the certificate-only normalizer. *)
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
            RuntimeAdapter.Atomicity.AtomicStep state outer step)) eq_refl);
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
    apply RuntimeAdapter.Atomicity.take_step_preserves_sets in Hsets as
      [Hmask Hopen].
    unfold RuntimeAdapter.Atomicity.state_wf in *. simpl.
    rewrite Hmask. rewrite Hopen. exact Hwf.
  Qed.

  (** The conditional certificate itself contains the two guard-indexed
      branch derivations, but an aligned witness may put any of the four
      structural Hoare wrappers around that certificate.  In particular the
      existential wrappers change the logical-binder context, so flattening
      this information into a same-context record would be unsound.  This
      small wrapper tree retains the context change explicitly.  The
      subsequent conditional proof consumes it by induction. *)
  Inductive aligned_conditional_wrapper (cost : RuntimeAdapter.Atomicity.cost_model)
      Γ F Δ : Type :=
  | ConditionalWrapperCore : forall (fuel : nat)
      (state : RuntimeAdapter.Atomicity.analysis_state)
      (node : typed_core.TypedCore.node_id)
      (store : Runtime.IR.Core.symbolic_store Γ F Δ)
      (frame : Runtime.Translation.Assertions.assertion Γ F Δ)
      (condition : Runtime.IR.pexpr Γ typed_core.TypedCore.TBool)
      (then_branch else_branch : Runtime.IR.stmt Γ)
      (then_exit else_exit : RuntimeAdapter.Atomicity.analysis_state)
      (post : Runtime.Translation.Assertions.assertion Γ F Δ)
      (view : Runtime.RegionSyntax.view
        (Runtime.IR.TIf node condition then_branch else_branch) =
        typed_analysis_view.TypedAnalysisView.ViewConditional then_branch
          else_branch)
      (then_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel state then_branch then_exit)
      (else_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel state else_branch else_exit)
      (open_equal : RuntimeAdapter.Atomicity.analysis_open then_exit =
        RuntimeAdapter.Atomicity.analysis_open else_exit)
      (atomic_equal : RuntimeAdapter.Atomicity.analysis_in_atomic then_exit =
        RuntimeAdapter.Atomicity.analysis_in_atomic else_exit)
      (then_derivation : Validity.Certified.Rules.RavenHoareTriple
        (Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store)
          (Runtime.Translation.Assertions.AAnd frame
            (Runtime.Translation.Assertions.AExpr
              (Runtime.Validation.Hoare.symbolize_expr store condition))))
        then_branch (RuntimeAdapter.Atomicity.analysis_mask state)
        (RuntimeAdapter.Atomicity.analysis_mask state) post)
      (else_derivation : Validity.Certified.Rules.RavenHoareTriple
        (Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store)
          (Runtime.Translation.Assertions.AAnd frame
            (Runtime.Translation.Assertions.AExpr
              (Runtime.Core.EUnOp Runtime.Core.UNot
                (Runtime.Validation.Hoare.symbolize_expr store condition)))))
        else_branch (RuntimeAdapter.Atomicity.analysis_mask state)
        (RuntimeAdapter.Atomicity.analysis_mask state) post)
      (then_mask : RuntimeAdapter.Atomicity.analysis_mask then_exit =
        RuntimeAdapter.Atomicity.analysis_mask state)
      (else_mask : RuntimeAdapter.Atomicity.analysis_mask else_exit =
        RuntimeAdapter.Atomicity.analysis_mask state),
      Validity.Certified.certificate_hoare_aligned cost then_certificate
        (Validity.Certified.hoare_mask_transport then_derivation eq_refl
          (eq_sym then_mask)) ->
      Validity.Certified.certificate_hoare_aligned cost else_certificate
        (Validity.Certified.hoare_mask_transport else_derivation eq_refl
          (eq_sym else_mask)) ->
      aligned_conditional_wrapper cost Γ F Δ
  | ConditionalWrapperFrame : forall
      (frame : Runtime.Translation.Assertions.assertion Γ F Δ),
      aligned_conditional_wrapper cost Γ F Δ ->
      aligned_conditional_wrapper cost Γ F Δ
  | ConditionalWrapperConsequence : forall
      (pre pre' post post' : Runtime.Translation.Assertions.assertion Γ F Δ),
      Runtime.Validation.Hoare.assertion_entails pre' pre ->
      Runtime.Validation.Hoare.assertion_entails post post' ->
      aligned_conditional_wrapper cost Γ F Δ ->
      aligned_conditional_wrapper cost Γ F Δ
  | ConditionalWrapperExistsElim : forall (t : typed_core.TypedCore.typ),
      aligned_conditional_wrapper cost Γ F (t :: Δ) ->
      aligned_conditional_wrapper cost Γ F Δ
  | ConditionalWrapperExistsPreserve : forall (t : typed_core.TypedCore.typ),
      aligned_conditional_wrapper cost Γ F (t :: Δ) ->
      aligned_conditional_wrapper cost Γ F Δ.

  Definition aligned_conditional_decomposition_target
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
      return forall (F' Δ' : typed_core.TypedCore.context)
        (pre' post' : Runtime.Translation.Assertions.assertion Γ' F' Δ'),
        Validity.Certified.Rules.RavenHoareTriple pre' statement'
          (RuntimeAdapter.Atomicity.analysis_mask entry')
          (RuntimeAdapter.Atomicity.analysis_mask exit') post' -> Type
    with
    | @RuntimeAdapter.Atomicity.CertConditional _ Γ' fuel' state' statement'
        then_branch else_branch then_exit else_exit view then_certificate
        else_certificate open_equal atomic_equal =>
        fun F' Δ' _ _ _ => aligned_conditional_wrapper cost Γ' F' Δ'
    | _ => fun _ _ _ _ _ => unit
    end.

  Fixpoint aligned_conditional_decompose_fix
      {cost Γ F Δ fuel entry statement exit pre post}
      {certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ fuel
        entry statement exit}
      {derivation : Validity.Certified.Rules.RavenHoareTriple pre statement
        (RuntimeAdapter.Atomicity.analysis_mask entry)
        (RuntimeAdapter.Atomicity.analysis_mask exit) post}
      (Haligned : Validity.Certified.certificate_hoare_aligned cost certificate
        derivation) {struct Haligned} :
    aligned_conditional_decomposition_target certificate F Δ pre post derivation.
  Proof.
    destruct Haligned; simpl; try exact tt.
    - exact (ConditionalWrapperCore cost Γ F Δ fuel state node store frame
        condition then_branch else_branch then_exit else_exit post view
        then_certificate else_certificate open_equal atomic_equal
        then_derivation else_derivation then_mask else_mask Haligned1
        Haligned2).
    - dependent destruction certificate; simpl; try exact tt.
      refine (ConditionalWrapperFrame cost Γ F Δ frame _).
      exact (@aligned_conditional_decompose_fix cost _ _ _ _ _ _ _ _ _ _ _
        Haligned).
    - dependent destruction certificate; simpl; try exact tt.
      refine (ConditionalWrapperConsequence cost Γ F Δ pre pre' post post'
        pre_entails post_entails _).
      exact (@aligned_conditional_decompose_fix cost _ _ _ _ _ _ _ _ _ _ _
        Haligned).
    - dependent destruction certificate; simpl; try exact tt.
      refine (ConditionalWrapperExistsElim cost Γ F Δ t _).
      exact (@aligned_conditional_decompose_fix cost _ _ _ _ _ _ _ _ _ _ _
        Haligned).
    - dependent destruction certificate; simpl; try exact tt.
      refine (ConditionalWrapperExistsPreserve cost Γ F Δ t _).
      exact (@aligned_conditional_decompose_fix cost _ _ _ _ _ _ _ _ _ _ _
        Haligned).
  Defined.

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

  (** The next proof must recurse through [certificate_hoare_aligned], using
      the interpreted guard at [AlignedConditional] and transporting Frame,
      Consequence, ExistsElim, and ExistsPreserve without flattening their
      assertion or binder indices. *)
  Theorem aligned_conditional_certificate_translated_runtime_refinement
      {cost} {Γ F Δ : typed_core.TypedCore.context}
      {fuel state node condition then_branch else_branch
        then_exit else_exit pre post}
      (view : Runtime.RegionSyntax.view
        (Runtime.IR.TIf node condition then_branch else_branch) =
        typed_analysis_view.TypedAnalysisView.ViewConditional then_branch
          else_branch)
      (then_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel state then_branch then_exit)
      (else_certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel state else_branch else_exit)
      (open_equal : RuntimeAdapter.Atomicity.analysis_open then_exit =
        RuntimeAdapter.Atomicity.analysis_open else_exit)
      (atomic_equal : RuntimeAdapter.Atomicity.analysis_in_atomic then_exit =
        RuntimeAdapter.Atomicity.analysis_in_atomic else_exit)
      (derivation : Validity.Certified.Rules.RavenHoareTriple
        pre
        (Runtime.IR.TIf node condition then_branch else_branch)
        (RuntimeAdapter.Atomicity.analysis_mask state)
        (RuntimeAdapter.Atomicity.analysis_mask
          (RuntimeAdapter.conditional_join then_exit else_exit)) post) :
    aligned_certificate_translated_runtime_refinement
      (F := F) (Δ := Δ) (pre := pre) (post := post)
      (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel state
        (Runtime.IR.TIf node condition then_branch else_branch) then_branch
        else_branch then_exit else_exit view then_certificate else_certificate
        open_equal atomic_equal) derivation.
  Proof.
  Admitted.

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
    { apply RuntimeAdapter.Atomicity.take_step_preserves_sets in step as
        [_ Hopen]. exact (eq_sym Hopen). }
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
      apply RuntimeAdapter.Atomicity.take_step_preserves_sets in Hstep_sets as
        [_ Hopen]. exact Hopen. }
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

  Lemma focused_prefix_of_aligned_fold_head
      {cost Γ F Δ invariant outer tail fuel entry node arguments store body
        final post stack_out}
      (view : Runtime.RegionSyntax.view (Runtime.IR.TFold node invariant arguments) =
        typed_analysis_view.TypedAnalysisView.ViewFold invariant)
      (instantiated : Contracts.instantiated_invariant Γ F Δ
        (Logic.invariant_args invariant) invariant
        (Runtime.Validation.Hoare.symbolize_expr_list store arguments) body)
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate
        (RuntimeAdapter.Atomicity.CertFold cost Γ fuel entry
          (Runtime.IR.TFold node invariant arguments) invariant view)
        ((invariant, outer) :: tail) tail)
      (rest : Validity.aligned_operational_suffix cost Γ F Δ
        (RuntimeAdapter.Atomicity.fold_invariant invariant entry)
        (Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store)
          (Runtime.Translation.Assertions.AInvariant invariant
            (Runtime.Validation.Hoare.symbolize_expr_list store arguments)))
        tail final post stack_out) :
    Focused.focused_prefix cost Γ F Δ invariant outer tail entry
      (Runtime.Translation.Assertions.AAnd
        (Runtime.Translation.Assertions.AStack store) body)
      final post stack_out
      (@Validity.AlignedOperationalCons cost Γ F Δ (S fuel) entry
        (Runtime.IR.TFold node invariant arguments)
        (RuntimeAdapter.Atomicity.fold_invariant invariant entry)
        (Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store) body)
        (Runtime.Translation.Assertions.AAnd
          (Runtime.Translation.Assertions.AStack store)
          (Runtime.Translation.Assertions.AInvariant invariant
            (Runtime.Validation.Hoare.symbolize_expr_list store arguments)))
        ((invariant, outer) :: tail) tail
        (RuntimeAdapter.Atomicity.CertFold cost Γ fuel entry
          (Runtime.IR.TFold node invariant arguments) invariant view)
        (Validity.Certified.hoare_mask_transport
          (Validity.Certified.Rules.FoldInvariantRule node invariant
            arguments store body (RuntimeAdapter.Atomicity.analysis_mask entry)
            instantiated)
          eq_refl
          (eq_sym (Validity.Certified.fold_analysis_mask invariant entry)))
        (Validity.Certified.AlignedFold cost Γ F Δ fuel entry node
          invariant arguments store body view instantiated)
        lifo final post stack_out rest).
  Proof.
    eapply Focused.FocusedPrefixHere.
    exact (@Focused.FocusedCertificateFold cost Γ invariant outer tail fuel
      entry node arguments view lifo).
  Qed.

  Lemma focused_prefix_prepend_preserving
      {cost Γ F Δ invariant outer tail fuel entry statement middle pre
        middle_assertion final post stack_out certificate derivation}
      (aligned : Validity.Certified.certificate_hoare_aligned cost certificate
        derivation)
      (lifo : RuntimeAdapter.Atomicity.lifo_certificate certificate
        ((invariant, outer) :: tail) ((invariant, outer) :: tail))
      (preserving : Focused.focused_preserving_certificate invariant certificate)
      (rest : Validity.aligned_operational_suffix cost Γ F Δ middle
        middle_assertion ((invariant, outer) :: tail) final post stack_out)
      (focus : Focused.focused_prefix cost Γ F Δ invariant outer tail middle
        middle_assertion final post stack_out rest) :
    Focused.focused_prefix cost Γ F Δ invariant outer tail entry pre final
      post stack_out
      (@Validity.AlignedOperationalCons cost Γ F Δ fuel entry statement
        middle pre middle_assertion ((invariant, outer) :: tail)
        ((invariant, outer) :: tail) certificate derivation aligned lifo final
        post stack_out rest).
  Proof.
    exact (@Focused.FocusedPrefixLater cost Γ F Δ invariant outer tail fuel
      entry statement middle pre middle_assertion certificate derivation
      aligned lifo preserving final post stack_out rest focus).
  Qed.

  Lemma focused_core_sequence_left
      {cost Γ invariant outer tail fuel entry node first middle second exit
        first_certificate second_certificate}
      (view : Runtime.RegionSyntax.view (Runtime.IR.TSeq node first second) =
        typed_analysis_view.TypedAnalysisView.ViewSequence first second)
      (first_core : Focused.focused_certificate_core cost Γ invariant outer
        tail fuel entry first middle first_certificate)
      (second_lifo : RuntimeAdapter.Atomicity.lifo_certificate
        second_certificate tail tail) :
    Focused.focused_certificate_core cost Γ invariant outer tail (S fuel)
      entry (Runtime.IR.TSeq node first second) exit
      (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
        (Runtime.IR.TSeq node first second) first middle second exit view
        first_certificate second_certificate).
  Proof.
    exact (@Focused.FocusedCertificateSequenceLeft cost Γ invariant outer
      tail fuel entry node first middle second exit first_certificate
      second_certificate view first_core second_lifo).
  Qed.

  Lemma focused_core_sequence_right
      {cost Γ invariant outer tail fuel entry node first middle second exit
        first_certificate second_certificate}
      (view : Runtime.RegionSyntax.view (Runtime.IR.TSeq node first second) =
        typed_analysis_view.TypedAnalysisView.ViewSequence first second)
      (first_lifo : RuntimeAdapter.Atomicity.lifo_certificate first_certificate
        ((invariant, outer) :: tail) ((invariant, outer) :: tail))
      (second_core : Focused.focused_certificate_core cost Γ invariant outer
        tail fuel middle second exit second_certificate) :
    Focused.focused_certificate_core cost Γ invariant outer tail (S fuel)
      entry (Runtime.IR.TSeq node first second) exit
      (RuntimeAdapter.Atomicity.CertSequence cost Γ fuel entry
        (Runtime.IR.TSeq node first second) first middle second exit view
        first_certificate second_certificate).
  Proof.
    exact (@Focused.FocusedCertificateSequenceRight cost Γ invariant outer
      tail fuel entry node first middle second exit first_certificate
      second_certificate view first_lifo second_core).
  Qed.

  Lemma focused_core_conditional
      {cost Γ invariant outer tail fuel entry node condition then_branch
        else_branch then_exit else_exit then_certificate else_certificate}
      (open_equal : RuntimeAdapter.Atomicity.analysis_open then_exit =
        RuntimeAdapter.Atomicity.analysis_open else_exit)
      (atomic_equal : RuntimeAdapter.Atomicity.analysis_in_atomic then_exit =
        RuntimeAdapter.Atomicity.analysis_in_atomic else_exit)
      (view : Runtime.RegionSyntax.view
        (Runtime.IR.TIf node condition then_branch else_branch) =
        typed_analysis_view.TypedAnalysisView.ViewConditional then_branch
          else_branch)
      (then_core : Focused.focused_certificate_core cost Γ invariant outer
        tail fuel entry then_branch then_exit then_certificate)
      (else_core : Focused.focused_certificate_core cost Γ invariant outer
        tail fuel entry else_branch else_exit else_certificate) :
    Focused.focused_certificate_core cost Γ invariant outer tail (S fuel)
      entry (Runtime.IR.TIf node condition then_branch else_branch)
      (RuntimeAdapter.conditional_join then_exit else_exit)
      (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry
        (Runtime.IR.TIf node condition then_branch else_branch) then_branch
        else_branch then_exit else_exit view then_certificate else_certificate
        open_equal atomic_equal).
  Proof.
    exact (@Focused.FocusedCertificateConditional cost Γ invariant outer
      tail fuel entry node condition then_branch else_branch then_exit
      else_exit then_certificate else_certificate open_equal atomic_equal view
      then_core else_core).
  Qed.

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
End AlignedTraceNormalization.

End WithRuntimeValidity.
End WithContracts.
End Make.
