From raven_iris.simp_raven_lang Require Import ra_base.
From stdpp Require Import sets coPset.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic Require Import atomic.
From iris.proofmode Require Import tactics.
From Coq Require Import Program.Equality ClassicalEpsilon.
From raven_iris.rich_raven_lang Require Import
  typed_assertion typed_conditional_runtime_soundness.

(** Final Phase 7 assembly, kept downstream of the reusable conditional
    runtime-soundness machinery so this active proof remains small enough for
    interactive rocq-mcp checking. *)
Module Make (LegacyRAs : ra_base.RA_CONFIG)
    (Logic : TypedAssertion.LOGIC_SIGNATURE).

Module Base := typed_conditional_runtime_soundness.Make LegacyRAs Logic.
Module Runtime := Base.Runtime.

Module WithContracts (Contracts : Runtime.Validation.Hoare.CONTRACT_ENV).
Module BaseContracts := Base.WithContracts Contracts.
Module RuntimeAdapter := BaseContracts.RuntimeAdapter.

Module WithRuntimeValidity
    (Resources : Runtime.RUNTIME_RESOURCES)
    (ProcedureContracts :
      Runtime.Validation.Hoare.PROCEDURE_CONTRACT_COHERENCE Contracts)
    (Leaf : Runtime.DEFAULT_SEMANTIC_LEAF_CONTRACTS Resources Contracts)
    (Defs : Runtime.Translation.DEFINITION_ENV).

Module Import RuntimeSoundness := BaseContracts.WithRuntimeValidity Resources
  ProcedureContracts Leaf Defs.
Module Import AlignedTraceNormalization :=
  RuntimeSoundness.AlignedTraceNormalization.
Local Existing Instance Normalized.Validity.Model.concrete_irisG.

Module Phase7MixedEndToEndSpike.
  (** The two remaining semantic obligations are isolated here so that the
      rest of this module is a real assembly proof to the public closed
      certificate theorem.  The first obligation is Step 3 proper; the
      second is the resource-calculus analogue of the legacy
      footprint-to-final-resources lemma. *)
  Definition resource_focused_general_closing_refinement
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      (_ : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset),
    Validity.Model.runtime_cost_model_sound cost ->
    Validity.Certified.procedure_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.analysis_in_atomic entry = false ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry)
      ((invariant, outer) :: tail) ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆
      ambient ->
    forall (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env),
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

  (** Continuation-parametric induction motive for a marker that is available
      somewhere in the input stack.  The continuation is an Iris proposition,
      not an appended runtime statement: recursive conditional arms can use
      the shared-rest WP as [final] without requiring a false reassociation of
      three concrete [RTSeq] nodes.  Stack ownership stays outside the
      outer-to-active update, so pure control flow can inspect the runtime
      stack before the selected arm opens the invariant.  [carried]
      explicitly transports resources introduced by structural proof
      wrappers (notably [Frame]) through the target seam to the continuation.
      This is the same stack-exposed boundary used by the earlier focused
      seam proofs. *)
  Definition resource_target_outer_cps_refinement
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail
        source tree suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry
        pre stack_in exit post stack_out mode tail source tree suffix trace)
      (target : RuntimeAdapter.Atomicity.access_marker)
      (below : list RuntimeAdapter.Atomicity.access_marker)
      (_ : resource_target_position target below stack_in) : Prop :=
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset),
    Validity.Model.runtime_cost_model_sound cost ->
    Validity.Certified.procedure_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.analysis_in_atomic entry = false ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆
      ambient ->
    forall (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (carried final : iProp Resources.Σ),
    let outer_mask := Validity.Model.enabled_runtime_mask ambient target.2 in
    (((|={outer_mask, Validity.Model.active_runtime_mask ambient exit}=>
        Validity.global_world_context atoms ∗
        Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
          runtime formals binders atoms post ∗
        Validity.World.access_stack_interp atoms ambient stack_out ∗ carried)
        ⊢ final) ->
     ((|={outer_mask, Validity.Model.active_runtime_mask ambient entry}=>
        Validity.global_world_context atoms ∗
        Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
          runtime formals binders atoms pre ∗
        Validity.World.access_stack_interp atoms ambient stack_in ∗ carried)
        ⊢
      Validity.runtime_option_wp outer_mask outer_mask
        (ConcreteOrdinaryTrace.source_runtime source runtime) final))%I.

  Lemma resource_target_outer_cps_stack_exposed
      {Γ F Δ} (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env)
      (store : Runtime.IR.Core.symbolic_store Γ F Δ)
      (body : Runtime.Translation.Assertions.assertion Γ F Δ)
      (access final : iProp Resources.Σ) (Eouter Einner : coPset)
      (Hbundled :
        (|={Eouter, Einner}=>
          Validity.global_world_context atoms ∗
          Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
            runtime formals binders atoms
            (Runtime.Translation.Assertions.AAnd
              (Runtime.Translation.Assertions.AStack store) body) ∗ access) ⊢
        final) :
    (Validity.Model.stack_own Γ runtime
       (Runtime.Translation.interp_store formals binders atoms store) ∗
     (|={Eouter, Einner}=>
       Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms body ∗ access)) ⊢ final.
  Proof.
    iIntros "[Hstack Hopened]". iApply Hbundled.
    iMod "Hopened" as "[Hworld [Hbody Haccess]]". iModIntro.
    simpl. iFrame.
  Qed.

  (** Critical [FocusedConditionalRest] runtime assembly.  Each recursive arm
      ends in the *proposition* expressing the shared-rest WP.  Sequencing is
      therefore performed once per selected arm, before the conditional
      bracket is assembled; no three-way source reassociation is involved. *)
  Lemma resource_target_outer_cps_conditional_shared_rest
      {Γ F Δ node}
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env)
      (store : Runtime.IR.Core.symbolic_store Γ F Δ)
      (condition : Runtime.IR.pexpr Γ typed_core.TypedCore.TBool)
      (then_branch else_branch : Runtime.IR.stmt Γ)
      (rest_runtime : option Runtime.LegacyLang.runtime_stmt)
      (Eouter Einner : coPset) (opened final : iProp Resources.Σ)
      (Hthen : Runtime.IR.Core.interp_expr formals binders atoms
          (Runtime.Validation.Hoare.symbolize_expr store condition) =
          Some (Runtime.IR.Core.VBool true) ->
        (Validity.Model.stack_own Γ runtime
           (Runtime.Translation.interp_store formals binders atoms store) ∗
         (|={Eouter, Einner}=> opened)) ⊢
        Validity.runtime_option_wp Eouter Eouter
          (Validity.Model.runtime_stmt
            (Validity.Model.runtime_names Γ runtime)
            (Validity.Model.runtime_stack_id Γ runtime) then_branch)
          (Validity.runtime_option_wp Eouter Eouter rest_runtime final))
      (Helse : Runtime.IR.Core.interp_expr formals binders atoms
          (Runtime.Validation.Hoare.symbolize_expr store condition) =
          Some (Runtime.IR.Core.VBool false) ->
        (Validity.Model.stack_own Γ runtime
           (Runtime.Translation.interp_store formals binders atoms store) ∗
         (|={Eouter, Einner}=> opened)) ⊢
        Validity.runtime_option_wp Eouter Eouter
          (Validity.Model.runtime_stmt
            (Validity.Model.runtime_names Γ runtime)
            (Validity.Model.runtime_stack_id Γ runtime) else_branch)
          (Validity.runtime_option_wp Eouter Eouter rest_runtime final)) :
    (Validity.Model.stack_own Γ runtime
       (Runtime.Translation.interp_store formals binders atoms store) ∗
     (|={Eouter, Einner}=> opened)) ⊢
    Validity.runtime_option_wp Eouter Eouter
      (Validity.Model.combine_runtime_statements
        (Validity.Model.runtime_stmt
          (Validity.Model.runtime_names Γ runtime)
          (Validity.Model.runtime_stack_id Γ runtime)
          (Runtime.IR.TIf node condition then_branch else_branch))
        rest_runtime) final.
  Proof.
    eapply resource_focused_conditional_stack_exposed_bracket.
    - intros Hcondition. iIntros "Hopened".
      iApply Validity.runtime_option_wp_sequence_same_mask.
      iApply (Hthen Hcondition with "Hopened").
    - intros Hcondition. iIntros "Hopened".
      iApply Validity.runtime_option_wp_sequence_same_mask.
      iApply (Helse Hcondition with "Hopened").
  Qed.

  Lemma resource_conditional_core_shared_rest_outer_cps
      {cost Γ F Δ fuel entry node store frame condition then_statement
        else_statement then_exit else_exit post view then_certificate
        else_certificate open_equal atomic_equal then_derivation
        else_derivation then_aligned else_aligned stack_in join_stack mode tail
        then_tree else_tree then_lifo else_lifo Hthen Helse}
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
          else_derivation else_aligned else_lifo) Helse)
      (target : RuntimeAdapter.Atomicity.access_marker) below
      (position : resource_target_position target below stack_in)
      (Hthen_refinement : resource_target_outer_cps_refinement then_lockstep
        target below position)
      (Helse_refinement : resource_target_outer_cps_refinement else_lockstep
        target below position)
      (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (Hruntime_cost : Validity.Model.runtime_cost_model_sound cost)
      (Hprocedure_cost : Validity.Certified.procedure_cost_model_sound cost)
      (Hwf : RuntimeAdapter.Atomicity.state_wf entry)
      (Hnotatomic : RuntimeAdapter.Atomicity.analysis_in_atomic entry = false)
      (Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open entry) stack_in)
      (Hfootprint : Validity.Model.runtime_mask
        (RuntimeAdapter.Atomicity.certificate_footprint
          (RuntimeAdapter.Atomicity.CertConditional cost Γ fuel entry
            (Runtime.IR.TIf node condition then_statement else_statement)
            then_statement else_statement then_exit else_exit view
            then_certificate else_certificate open_equal atomic_equal)) ⊆
        ambient)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ) (atoms : Runtime.Core.atom_env)
      (rest_runtime : option Runtime.LegacyLang.runtime_stmt)
      (carried final : iProp Resources.Σ)
      (Hrest :
        (|={Validity.Model.enabled_runtime_mask ambient target.2,
            Validity.Model.active_runtime_mask ambient
              (RuntimeAdapter.conditional_join then_exit else_exit)}=>
          Validity.global_world_context atoms ∗
          Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
            runtime formals binders atoms post ∗
          Validity.World.access_stack_interp atoms ambient join_stack ∗ carried)
        ⊢ Validity.runtime_option_wp
          (Validity.Model.enabled_runtime_mask ambient target.2)
          (Validity.Model.enabled_runtime_mask ambient target.2)
          rest_runtime final) :
    (Validity.Model.stack_own Γ runtime
       (Runtime.Translation.interp_store formals binders atoms store) ∗
     (|={Validity.Model.enabled_runtime_mask ambient target.2,
         Validity.Model.active_runtime_mask ambient entry}=>
       Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms frame ∗
       Validity.World.access_stack_interp atoms ambient stack_in ∗ carried)) ⊢
    Validity.runtime_option_wp
      (Validity.Model.enabled_runtime_mask ambient target.2)
      (Validity.Model.enabled_runtime_mask ambient target.2)
      (Validity.Model.combine_runtime_statements
        (Validity.Model.runtime_stmt
          (Validity.Model.runtime_names Γ runtime)
          (Validity.Model.runtime_stack_id Γ runtime)
          (Runtime.IR.TIf node condition then_statement else_statement))
        rest_runtime) final.
  Proof.
    have Hthen_footprint : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (RuntimeAdapter.singleton_suffix then_certificate)) ⊆ ambient.
    { etransitivity; last exact Hfootprint.
      apply Validity.Model.runtime_mask_mono. simpl.
      rewrite union_empty_r_L.
      etransitivity; [apply union_subseteq_l|apply union_subseteq_r]. }
    have Helse_footprint : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (RuntimeAdapter.singleton_suffix else_certificate)) ⊆ ambient.
    { etransitivity; last exact Hfootprint.
      apply Validity.Model.runtime_mask_mono. simpl.
      rewrite union_empty_r_L.
      etransitivity; [apply union_subseteq_r|apply union_subseteq_r]. }
    eapply resource_target_outer_cps_conditional_shared_rest.
    - intros Hcondition.
      have Hthen_cont :
          ((|={Validity.Model.enabled_runtime_mask ambient target.2,
              Validity.Model.active_runtime_mask ambient then_exit}=>
             Validity.global_world_context atoms ∗
             Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
               runtime formals binders atoms post ∗
             Validity.World.access_stack_interp atoms ambient join_stack ∗
             carried) ⊢
           Validity.runtime_option_wp
             (Validity.Model.enabled_runtime_mask ambient target.2)
             (Validity.Model.enabled_runtime_mask ambient target.2)
             rest_runtime final)%I.
      { rewrite (Validity.conditional_then_active_mask_join ambient then_exit
          else_exit). exact Hrest. }
      pose proof (Hthen_refinement runtime ambient Hruntime_cost
        Hprocedure_cost Hwf Hnotatomic Hstack Hthen_footprint formals binders
        atoms carried
        (Validity.runtime_option_wp
          (Validity.Model.enabled_runtime_mask ambient target.2)
          (Validity.Model.enabled_runtime_mask ambient target.2)
          rest_runtime final) Hthen_cont) as Hthen_bundled.
      have Hthen_runtime :
          ConcreteOrdinaryTrace.source_runtime
            (RuntimeAdapter.singleton_suffix then_certificate) runtime =
          Validity.Model.runtime_stmt
            (Validity.Model.runtime_names Γ runtime)
            (Validity.Model.runtime_stack_id Γ runtime) then_statement.
      { simpl. unfold Validity.certificate_runtime_statement.
        destruct (Validity.Model.runtime_stmt
          (Validity.Model.runtime_names Γ runtime)
          (Validity.Model.runtime_stack_id Γ runtime) then_statement);
          reflexivity. }
      rewrite Hthen_runtime in Hthen_bundled.
      iIntros "[Hstackown Hopened]".
      iApply (resource_target_outer_cps_stack_exposed runtime formals binders
        atoms store
        (Runtime.Translation.Assertions.AAnd frame
          (Runtime.Translation.Assertions.AExpr
            (Runtime.Validation.Hoare.symbolize_expr store condition)))
        (Validity.World.access_stack_interp atoms ambient stack_in ∗ carried)
        _ _ _ Hthen_bundled).
      iFrame "Hstackown".
      iMod "Hopened" as "[Hworld [Hframe [Haccess Hcarried]]]".
      iModIntro. simpl. iFrame. iPureIntro. exact Hcondition.
    - intros Hcondition.
      have Helse_cont :
          ((|={Validity.Model.enabled_runtime_mask ambient target.2,
              Validity.Model.active_runtime_mask ambient else_exit}=>
             Validity.global_world_context atoms ∗
             Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
               runtime formals binders atoms post ∗
             Validity.World.access_stack_interp atoms ambient join_stack ∗
             carried) ⊢
           Validity.runtime_option_wp
             (Validity.Model.enabled_runtime_mask ambient target.2)
             (Validity.Model.enabled_runtime_mask ambient target.2)
             rest_runtime final)%I.
      { rewrite (Validity.conditional_else_active_mask_join ambient then_exit
          else_exit open_equal). exact Hrest. }
      pose proof (Helse_refinement runtime ambient Hruntime_cost
        Hprocedure_cost Hwf Hnotatomic Hstack Helse_footprint formals binders
        atoms carried
        (Validity.runtime_option_wp
          (Validity.Model.enabled_runtime_mask ambient target.2)
          (Validity.Model.enabled_runtime_mask ambient target.2)
          rest_runtime final) Helse_cont) as Helse_bundled.
      have Helse_runtime :
          ConcreteOrdinaryTrace.source_runtime
            (RuntimeAdapter.singleton_suffix else_certificate) runtime =
          Validity.Model.runtime_stmt
            (Validity.Model.runtime_names Γ runtime)
            (Validity.Model.runtime_stack_id Γ runtime) else_statement.
      { simpl. unfold Validity.certificate_runtime_statement.
        destruct (Validity.Model.runtime_stmt
          (Validity.Model.runtime_names Γ runtime)
          (Validity.Model.runtime_stack_id Γ runtime) else_statement);
          reflexivity. }
      rewrite Helse_runtime in Helse_bundled.
      iIntros "[Hstackown Hopened]".
      iApply (resource_target_outer_cps_stack_exposed runtime formals binders
        atoms store
        (Runtime.Translation.Assertions.AAnd frame
          (Runtime.Translation.Assertions.AExpr
            (Runtime.Core.EUnOp Runtime.Core.UNot
              (Runtime.Validation.Hoare.symbolize_expr store condition))))
        (Validity.World.access_stack_interp atoms ambient stack_in ∗ carried)
        _ _ _ Helse_bundled).
      iFrame "Hstackown".
      iMod "Hopened" as "[Hworld [Hframe [Haccess Hcarried]]]".
      iModIntro. simpl. iFrame. iPureIntro.
      rewrite Hcondition. reflexivity.
  Qed.

  Inductive resource_focused_outcome_semantics
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace) : Type :=
  | ResourceFocusedOutcomeSemanticsPending
      (_ : resource_pending_open_trace_refinement aligned_trace) :
      resource_focused_outcome_semantics aligned_trace
  | ResourceFocusedOutcomeSemanticsClosing
      (_ : resource_focused_general_closing_refinement aligned_trace) :
      resource_focused_outcome_semantics aligned_trace.

  Theorem resource_focused_target_outcome_total_spike
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace) :
    resource_target_trace_outcome aligned_trace (invariant, outer) tail
      (@ResourceTargetHere (invariant, outer) tail).
  Proof.
    exact (resource_target_trace_outcome_complete aligned_trace
      (invariant, outer) tail
      (@ResourceTargetHere (invariant, outer) tail)).
  Qed.

  Theorem resource_focused_target_outcome_closes_spike
      {cost Γ F Δ invariant outer tail entry pre exit post stack_out source
        tree suffix trace}
      {aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        ((invariant, outer) :: tail) exit post stack_out
        (Some (invariant, outer)) tail source tree suffix trace}
      (outcome : resource_target_trace_outcome aligned_trace
        (invariant, outer) tail
        (@ResourceTargetHere (invariant, outer) tail))
      (Habsent : resource_target_position (invariant, outer) tail stack_out ->
        False) :
    resource_target_outcome_closes outcome.
  Proof.
    exact (resource_target_outcome_closes_complete outcome Habsent).
  Qed.

  Definition resource_target_close_splice_assertion_refinement
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source tree
       suffix trace target below position}
      {aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        stack_in exit post stack_out mode tail source tree suffix trace}
      (handoff : resource_target_close_handoff aligned_trace target below
        position) : Prop :=
    let split := resource_close_stack_split_of_target_handoff handoff in
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset),
    Validity.Model.runtime_cost_model_sound cost ->
    Validity.Certified.procedure_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.analysis_in_atomic entry = false ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
    Validity.Model.runtime_mask (Normalized.suffix_footprint source) ⊆
      ambient ->
    forall (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env) (carried final : iProp Resources.Σ),
    let outer_mask := Validity.Model.enabled_runtime_mask ambient target.2 in
    (((Validity.global_world_context atoms ∗
        Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
          runtime formals binders atoms
          (resource_close_stack_assertion _ _ split) ∗
        Validity.World.access_stack_interp atoms ambient below ∗ carried) ⊢
       ConcreteOrdinaryTrace.source_translated_wp
         (resource_certificate_suffix_of_operational_suffix
           (resource_close_stack_rest _ _ split)) runtime ambient
         (Validity.global_world_context atoms ∗
          Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
            runtime formals binders atoms post ∗
          Validity.World.access_stack_interp atoms ambient stack_out ∗
          carried)) ->
     ((|={outer_mask, Validity.Model.active_runtime_mask ambient exit}=>
        Validity.global_world_context atoms ∗
        Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
          runtime formals binders atoms post ∗
        Validity.World.access_stack_interp atoms ambient stack_out ∗ carried)
       ⊢ final) ->
    ((|={outer_mask, Validity.Model.active_runtime_mask ambient entry}=>
       Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms pre ∗
       Validity.World.access_stack_interp atoms ambient stack_in ∗ carried) ⊢
     Validity.runtime_option_wp outer_mask outer_mask
       (ConcreteOrdinaryTrace.source_runtime source runtime) final))%I.

  Definition resource_target_close_splice_assertion_contract : Prop :=
    forall cost Γ F Δ entry pre stack_in exit post stack_out mode tail source
      tree suffix trace target below position
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        stack_in exit post stack_out mode tail source tree suffix trace)
      (handoff : resource_target_close_handoff aligned_trace target below
        position),
    resource_target_close_splice_cps_handoff handoff ->
    resource_target_close_splice_assertion_refinement handoff.

  (** The continuation after the selected matching close is structurally
      smaller than the source containing that close.  This is the decrease
      needed by the balanced well-founded reification proof: the selected
      rest is allowed to sit below any number of ordinary/focused wrappers,
      so it need not be an immediate constructor child. *)
  Lemma resource_target_close_handoff_rest_measure_lt
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source tree
       suffix trace target below position}
      {aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        stack_in exit post stack_out mode tail source tree suffix trace}
      (handoff : resource_target_close_handoff aligned_trace target below
        position) :
    RuntimeAdapter.suffix_measure
      (resource_certificate_suffix_of_operational_suffix
        (resource_close_stack_rest _ _
          (resource_close_stack_split_of_target_handoff handoff))) <
    RuntimeAdapter.suffix_measure source.
  Proof.
    induction handoff; destruct target; simpl in *;
      try (unfold RuntimeAdapter.certificate_source_size;
        pose proof (Runtime.RegionSyntax.size_positive Γ statement); lia);
      destruct (resource_close_stack_split_of_target_handoff handoff);
      simpl in *;
      unfold RuntimeAdapter.certificate_source_size;
      pose proof (Runtime.RegionSyntax.size_positive Γ statement); lia.
  Qed.


  Lemma resource_target_close_splice_ghost_prefix_closes
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source
       tree suffix trace target below position}
      {aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        stack_in exit post stack_out mode tail source tree suffix trace}
      (handoff : resource_target_close_handoff aligned_trace target below
        position)
      (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (final : iProp Resources.Σ) :
    Validity.Model.runtime_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.analysis_in_atomic entry = false ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
    ConcreteOrdinaryTrace.source_runtime
      (resource_certificate_suffix_of_operational_suffix
        (resource_close_stack_prefix _ _
          (resource_close_stack_split_of_target_handoff handoff))) runtime =
      None ->
    trace_runtime_cps_wp
      (resource_close_stack_prefix_trace _ _
        (resource_close_stack_split_of_target_handoff handoff)) runtime
      ambient (fun _ => final) ⊢
    (|={Validity.Model.active_runtime_mask ambient entry,
         Validity.Model.enabled_runtime_mask ambient target.2}=> final)%I.
  Proof.
    induction handoff; cbn;
      intros Hruntime_cost Hwf Hnotatomic Hstack Hnone.
    - destruct target as [invariant outer]. cbn in *.
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
      { rewrite opened. apply set_eq. intros other.
        rewrite elem_of_difference elem_of_union !elem_of_singleton.
        split.
        - intros [[-> | Hother] Hneq]; first contradiction. exact Hother.
        - intros Hother. split; first (right; exact Hother).
          intros ->. exact ((proj1 Hstack) Hother). }
      have Hclosed_active : Validity.Model.active_runtime_mask ambient
          (RuntimeAdapter.Atomicity.fold_invariant invariant entry) =
          Validity.Model.enabled_runtime_mask ambient outer.
      { destruct (RuntimeAdapter.Atomicity.fold_open_invariant invariant entry
          member) as [_ Hfold_open].
        unfold Validity.Model.active_runtime_mask.
        rewrite Hfold_open Hremaining. reflexivity. }
      rewrite <- Hclosed_active.
      iIntros "Hclose". iMod "Hclose". iExact "Hclose".
    - destruct target as [invariant outer]. cbn in *.
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
      { rewrite opened. apply set_eq. intros other.
        rewrite elem_of_difference elem_of_union !elem_of_singleton.
        split.
        - intros [[-> | Hother] Hneq]; first contradiction. exact Hother.
        - intros Hother. split; first (right; exact Hother).
          intros ->. exact ((proj1 Hstack) Hother). }
      have Hclosed_active : Validity.Model.active_runtime_mask ambient
          (RuntimeAdapter.Atomicity.fold_invariant invariant entry) =
          Validity.Model.enabled_runtime_mask ambient outer.
      { destruct (RuntimeAdapter.Atomicity.fold_open_invariant invariant entry
          member) as [_ Hfold_open].
        unfold Validity.Model.active_runtime_mask.
        rewrite Hfold_open Hremaining. reflexivity. }
      rewrite <- Hclosed_active.
      iIntros "Hclose". iMod "Hclose". iExact "Hclose".
    - have Hmiddle_wf := RuntimeAdapter.Atomicity.certificate_preserves_wf
        cost entry statement middle Hwf certificate.
      have Hmiddle_stack :=
        RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate stack stack Hwf lifo Hstack.
      have Hmiddle_notatomic := Validity.certificate_preserves_nonatomic
        certificate Hnotatomic.
      rewrite (resource_close_stack_split_chunk_source_runtime aligned_rest
        (resource_close_stack_split_of_target_handoff handoff) runtime)
        in Hnone.
      destruct (Validity.certificate_runtime_statement certificate runtime)
        as [head|] eqn:Hhead.
      + destruct (ConcreteOrdinaryTrace.source_runtime
          (resource_certificate_suffix_of_operational_suffix
            (resource_close_stack_prefix aligned_rest below
              (resource_close_stack_split_of_target_handoff handoff))) runtime)
          as [child|] eqn:Hchild; simpl in Hnone; discriminate Hnone.
      + simpl in Hnone.
      destruct (ConcreteOrdinaryTrace.source_runtime
        (resource_certificate_suffix_of_operational_suffix
          (resource_close_stack_prefix aligned_rest below
            (resource_close_stack_split_of_target_handoff handoff))) runtime)
        eqn:Hchild; simpl in Hnone; first discriminate.
      have IH := IHhandoff runtime Hruntime_cost Hmiddle_wf
        Hmiddle_notatomic Hmiddle_stack Hchild.
      have Hactive : Validity.Model.active_runtime_mask ambient middle =
          Validity.Model.active_runtime_mask ambient entry.
      { apply Validity.Model.active_runtime_mask_same_open.
        symmetry. exact (@balanced_certificate_open_equal cost Γ fuel entry
          statement middle stack certificate Hwf Hstack lifo). }
      rewrite Hactive in IH.
      rewrite (resource_close_stack_split_chunk_prefix_cps aligned_rest
        (resource_close_stack_split_of_target_handoff handoff) runtime
        ambient (fun _ => final)).
      iIntros "Hprefix".
      have Hrefine := balanced_chunk_region_runtime_refinement Hchunk runtime
        ambient
        (trace_runtime_cps_wp
          (resource_close_stack_prefix_trace aligned_rest below
            (resource_close_stack_split_of_target_handoff handoff)) runtime
          ambient (fun _ => final)).
      unfold Validity.translated_runtime_wp in Hrefine.
      unfold Validity.certificate_runtime_statement in Hhead.
      rewrite Hhead Hactive in Hrefine.
      iPoseProof (Hrefine with "Hprefix") as "Hprefix".
      iMod "Hprefix" as "Hchild".
      iPoseProof (IH with "Hchild") as "Hfinal".
      iExact "Hfinal".
    - rewrite (resource_close_stack_split_access_source_runtime aligned_body
        (resource_close_stack_split_of_target_handoff handoff) runtime)
        in Hnone.
      have Hopened_wf := RuntimeAdapter.Atomicity.certificate_preserves_wf
        cost entry statement opened Hwf certificate.
      have Hopened_stack :=
        RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate tail (focused :: tail) Hwf lifo Hstack.
      have Hopened_notatomic := Validity.certificate_preserves_nonatomic
        certificate Hnotatomic.
      have IH := IHhandoff runtime Hruntime_cost Hopened_wf
        Hopened_notatomic Hopened_stack Hnone.
      rewrite (resource_close_stack_split_access_prefix_cps aligned_body
        (resource_close_stack_split_of_target_handoff handoff) runtime
        ambient (fun _ => final)).
      iIntros "Hprefix".
      iPoseProof (opening_chunk_region_runtime_refinement Hopening open_ok
        runtime ambient _ with "Hprefix") as "Hprefix".
      iMod "Hprefix" as "Hchild".
      iPoseProof (IH with "Hchild") as "Hfinal".
      iExact "Hfinal".
    - have Hmiddle_wf := RuntimeAdapter.Atomicity.certificate_preserves_wf
        cost entry statement middle Hwf certificate.
      have Hmiddle_stack :=
        RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate (focused :: tail) (focused :: tail) Hwf lifo Hstack.
      have Hmiddle_notatomic := Validity.certificate_preserves_nonatomic
        certificate Hnotatomic.
      rewrite (resource_close_stack_split_focused_prefix_source_runtime
        aligned_rest (resource_close_stack_split_of_target_handoff handoff)
        runtime) in Hnone.
      destruct (Validity.certificate_runtime_statement certificate runtime)
        as [head|] eqn:Hhead.
      + destruct (ConcreteOrdinaryTrace.source_runtime
          (resource_certificate_suffix_of_operational_suffix
            (resource_close_stack_prefix aligned_rest below
              (resource_close_stack_split_of_target_handoff handoff))) runtime)
          as [child|] eqn:Hchild; simpl in Hnone; discriminate Hnone.
      + simpl in Hnone.
      destruct (ConcreteOrdinaryTrace.source_runtime
        (resource_certificate_suffix_of_operational_suffix
          (resource_close_stack_prefix aligned_rest below
            (resource_close_stack_split_of_target_handoff handoff))) runtime)
        eqn:Hchild; simpl in Hnone; first discriminate.
      have IH := IHhandoff runtime Hruntime_cost Hmiddle_wf
        Hmiddle_notatomic Hmiddle_stack Hchild.
      have Hactive : Validity.Model.active_runtime_mask ambient middle =
          Validity.Model.active_runtime_mask ambient entry.
      { apply Validity.Model.active_runtime_mask_same_open.
        symmetry. exact (@balanced_certificate_open_equal cost Γ fuel entry
          statement middle (focused :: tail) certificate Hwf Hstack lifo). }
      rewrite Hactive in IH.
      rewrite (resource_close_stack_split_focused_prefix_cps aligned_rest
        (resource_close_stack_split_of_target_handoff handoff) runtime
        ambient (fun _ => final)).
      iIntros "Hprefix".
      have Hrefine := balanced_chunk_region_runtime_refinement Hchunk runtime
        ambient
        (trace_runtime_cps_wp
          (resource_close_stack_prefix_trace aligned_rest below
            (resource_close_stack_split_of_target_handoff handoff)) runtime
          ambient (fun _ => final)).
      unfold Validity.translated_runtime_wp in Hrefine.
      unfold Validity.certificate_runtime_statement in Hhead.
      rewrite Hhead Hactive in Hrefine.
      iPoseProof (Hrefine with "Hprefix") as "Hprefix".
      iMod "Hprefix" as "Hchild".
      iPoseProof (IH with "Hchild") as "Hfinal".
      iExact "Hfinal".
    - rewrite (resource_close_stack_split_nested_source_runtime aligned_body
        (resource_close_stack_split_of_target_handoff handoff) runtime)
        in Hnone.
      have Hopened_wf := RuntimeAdapter.Atomicity.certificate_preserves_wf
        cost entry statement opened Hwf certificate.
      have Hopened_stack :=
        RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate (focused :: tail) (nested :: focused :: tail) Hwf lifo
          Hstack.
      have Hopened_notatomic := Validity.certificate_preserves_nonatomic
        certificate Hnotatomic.
      have IH := IHhandoff runtime Hruntime_cost Hopened_wf
        Hopened_notatomic Hopened_stack Hnone.
      rewrite (resource_close_stack_split_nested_prefix_cps aligned_body
        (resource_close_stack_split_of_target_handoff handoff) runtime
        ambient (fun _ => final)).
      iIntros "Hprefix".
      iPoseProof (opening_chunk_region_runtime_refinement Hopening open_ok
        runtime ambient _ with "Hprefix") as "Hprefix".
      iMod "Hprefix" as "Hchild".
      iPoseProof (IH with "Hchild") as "Hfinal".
      iExact "Hfinal".
    - rewrite
        (resource_close_stack_split_past_focused_close_source_runtime
          aligned_rest (resource_close_stack_split_of_target_handoff handoff)
          runtime) in Hnone.
      have Hclosed_wf := RuntimeAdapter.Atomicity.certificate_preserves_wf
        cost entry statement closed Hwf certificate.
      have Hclosed_stack :=
        RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate (focused :: tail) tail Hwf lifo Hstack.
      have Hclosed_notatomic := Validity.certificate_preserves_nonatomic
        certificate Hnotatomic.
      have IH := IHhandoff runtime Hruntime_cost Hclosed_wf
        Hclosed_notatomic Hclosed_stack Hnone.
      rewrite
        (resource_close_stack_split_past_focused_close_prefix_cps
          aligned_rest (resource_close_stack_split_of_target_handoff handoff)
          runtime ambient (fun _ => final)).
      iIntros "Hprefix".
      iPoseProof (closing_chunk_region_runtime_refinement Hclosing close_ok
        runtime ambient _ with "Hprefix") as "Hprefix".
      iMod "Hprefix" as "Hchild".
      iPoseProof (IH with "Hchild") as "Hfinal".
      iExact "Hfinal".
    - rewrite
        (resource_close_stack_split_past_ordinary_close_source_runtime
          aligned_rest (resource_close_stack_split_of_target_handoff handoff)
          runtime) in Hnone.
      have Hclosed_wf := RuntimeAdapter.Atomicity.certificate_preserves_wf
        cost entry statement closed Hwf certificate.
      have Hclosed_stack :=
        RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate (focused :: tail) tail Hwf lifo Hstack.
      have Hclosed_notatomic := Validity.certificate_preserves_nonatomic
        certificate Hnotatomic.
      have IH := IHhandoff runtime Hruntime_cost Hclosed_wf
        Hclosed_notatomic Hclosed_stack Hnone.
      rewrite
        (resource_close_stack_split_past_ordinary_close_prefix_cps
          aligned_rest (resource_close_stack_split_of_target_handoff handoff)
          runtime ambient (fun _ => final)).
      iIntros "Hprefix".
      iPoseProof (closing_chunk_region_runtime_refinement Hclosing close_ok
        runtime ambient _ with "Hprefix") as "Hprefix".
      iMod "Hprefix" as "Hchild".
      iPoseProof (IH with "Hchild") as "Hfinal".
      iExact "Hfinal".
  Qed.

  (** Source reification for the target-close prefix.  This is the exact
      runtime half of the existing target handoff: the sparse/atomic bridge
      justifies moving the opening update across the complete physical
      prefix, while the trace CPS postcondition remains arbitrary.  Keeping
      this as a lemma over [resource_target_close_handoff] avoids introducing
      another semantic-result layer. *)
  Lemma resource_target_close_splice_prefix_cps_source_spike
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source
       tree suffix trace target below position}
      {aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        stack_in exit post stack_out mode tail source tree suffix trace}
      (handoff : resource_target_close_handoff aligned_trace target below
        position) :
    let split := resource_close_stack_split_of_target_handoff handoff in
    forall (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (final : iProp Resources.Σ),
    Validity.Model.runtime_cost_model_sound cost ->
    Validity.Certified.procedure_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    RuntimeAdapter.Atomicity.analysis_in_atomic entry = false ->
    RuntimeAdapter.Atomicity.access_stack_consistent
      (RuntimeAdapter.Atomicity.analysis_open entry) stack_in ->
    Validity.Model.runtime_mask
      (Normalized.suffix_footprint
        (resource_certificate_suffix_of_operational_suffix
          (resource_close_stack_prefix _ _ split))) ⊆ ambient ->
    let outer_mask := Validity.Model.enabled_runtime_mask ambient target.2 in
    ((|={outer_mask, Validity.Model.active_runtime_mask ambient entry}=>
       trace_runtime_cps_wp (resource_close_stack_prefix_trace _ _ split)
         runtime ambient (fun _ => final)) ⊢
     Validity.runtime_option_wp outer_mask outer_mask
       (ConcreteOrdinaryTrace.source_runtime
         (resource_certificate_suffix_of_operational_suffix
           (resource_close_stack_prefix _ _ split)) runtime)
       final)%I.
  Proof.
    induction handoff; cbn;
      intros runtime ambient final Hruntime_cost Hprocedure_cost Hwf
        Hnotatomic Hstack Henvelope.
    - destruct target as [invariant outer]. cbn in *.
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
      { rewrite opened. apply set_eq. intros other.
        rewrite elem_of_difference. rewrite elem_of_union.
        rewrite !elem_of_singleton.
        split.
        - intros [[-> | Hother] Hneq]; first contradiction.
          exact Hother.
        - intros Hother. split; first (right; exact Hother).
          intros ->. exact ((proj1 Hstack) Hother). }
      have Hclosed_active : Validity.Model.active_runtime_mask ambient
          (RuntimeAdapter.Atomicity.fold_invariant invariant entry) =
          Validity.Model.enabled_runtime_mask ambient outer.
      { destruct (RuntimeAdapter.Atomicity.fold_open_invariant invariant entry
          member) as [_ Hfold_open].
        unfold Validity.Model.active_runtime_mask.
        rewrite Hfold_open Hremaining. reflexivity. }
      rewrite <- Hclosed_active.
      iIntros "Hclose". iMod "Hclose". iMod "Hclose".
      iExact "Hclose".
    - destruct target as [invariant outer]. cbn in *.
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
      { rewrite opened. apply set_eq. intros other.
        rewrite elem_of_difference. rewrite elem_of_union.
        rewrite !elem_of_singleton.
        split.
        - intros [[-> | Hother] Hneq]; first contradiction.
          exact Hother.
        - intros Hother. split; first (right; exact Hother).
          intros ->. exact ((proj1 Hstack) Hother). }
      have Hclosed_active : Validity.Model.active_runtime_mask ambient
          (RuntimeAdapter.Atomicity.fold_invariant invariant entry) =
          Validity.Model.enabled_runtime_mask ambient outer.
      { destruct (RuntimeAdapter.Atomicity.fold_open_invariant invariant entry
          member) as [_ Hfold_open].
        unfold Validity.Model.active_runtime_mask.
        rewrite Hfold_open Hremaining. reflexivity. }
      rewrite <- Hclosed_active.
      iIntros "Hclose". iMod "Hclose". iMod "Hclose".
      iExact "Hclose".
    - have Hmiddle_wf := RuntimeAdapter.Atomicity.certificate_preserves_wf
        cost entry statement middle Hwf certificate.
      have Hmiddle_stack :=
        RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate stack stack Hwf lifo Hstack.
      have Hmiddle_notatomic := Validity.certificate_preserves_nonatomic
        certificate Hnotatomic.
      have Hchild_envelope : Validity.Model.runtime_mask
          (Normalized.suffix_footprint
            (resource_certificate_suffix_of_operational_suffix
              (resource_close_stack_prefix aligned_rest below
                (resource_close_stack_split_of_target_handoff handoff)))) ⊆
          ambient.
      { etransitivity; last exact Henvelope.
        apply Validity.Model.runtime_mask_mono.
        exact (resource_close_stack_split_chunk_child_prefix_footprint_subseteq
          aligned_rest
          (resource_close_stack_split_of_target_handoff handoff)). }
      have IH := IHhandoff runtime ambient final Hruntime_cost
        Hprocedure_cost Hmiddle_wf Hmiddle_notatomic Hmiddle_stack
        Hchild_envelope.
      have Hopen := resource_target_position_open_nonempty target below stack
        position _ Hstack.
      destruct (resource_preserving_chunk_sparse Hchunk Hruntime_cost Hopen
        Hnotatomic runtime) as
        [_ [[Hnone _] | [Hentry_false Hmiddle_taken]]].
      + have Hnone_raw := Hnone.
        unfold Validity.certificate_runtime_statement in Hnone_raw.
        rewrite (resource_close_stack_split_chunk_source_runtime aligned_rest
          (resource_close_stack_split_of_target_handoff handoff) runtime).
        rewrite Hnone. simpl.
        have Hactive : Validity.Model.active_runtime_mask ambient middle =
            Validity.Model.active_runtime_mask ambient entry.
        { apply Validity.Model.active_runtime_mask_same_open.
          symmetry. eapply balanced_certificate_open_equal; eauto. }
        rewrite Hactive in IH.
        have Hid : forall X : option Runtime.LegacyLang.runtime_stmt,
            match X with Some physical => Some physical | None => None end = X.
        { intros [physical|]; reflexivity. }
        rewrite Hid.
        rewrite (resource_close_stack_split_chunk_prefix_cps aligned_rest
          (resource_close_stack_split_of_target_handoff handoff) runtime
          ambient (fun _ => final)).
        etrans; last exact IH.
        iIntros "Hprefix".
        iMod "Hprefix" as "Hprefix".
        have Hrefine := balanced_chunk_region_runtime_refinement Hchunk runtime
          ambient
          (trace_runtime_cps_wp
            (resource_close_stack_prefix_trace aligned_rest below
              (resource_close_stack_split_of_target_handoff handoff))
            runtime ambient (fun _ => final)).
        unfold Validity.translated_runtime_wp in Hrefine.
        rewrite Hnone_raw Hactive in Hrefine.
        iPoseProof (Hrefine with "Hprefix") as "Hprefix".
        iMod "Hprefix". iModIntro. iExact "Hprefix".
      + rewrite (resource_close_stack_split_chunk_source_runtime aligned_rest
          (resource_close_stack_split_of_target_handoff handoff) runtime).
        have Hchild_none :=
          resource_target_close_splice_prefix_none_when_step_taken handoff
            Hruntime_cost Hmiddle_wf Hmiddle_stack Hmiddle_notatomic
            Hmiddle_taken runtime.
        have Hchild_close :=
          resource_target_close_splice_ghost_prefix_closes handoff runtime
            ambient final Hruntime_cost Hmiddle_wf Hmiddle_notatomic
            Hmiddle_stack Hchild_none.
        have Hactive : Validity.Model.active_runtime_mask ambient middle =
            Validity.Model.active_runtime_mask ambient entry.
        { apply Validity.Model.active_runtime_mask_same_open.
          symmetry. eapply balanced_certificate_open_equal; eauto. }
        rewrite Hactive in Hchild_close.
        rewrite (resource_close_stack_split_chunk_prefix_cps aligned_rest
          (resource_close_stack_split_of_target_handoff handoff) runtime
          ambient (fun _ => final)).
        destruct (Validity.certificate_runtime_statement certificate runtime)
          as [physical|] eqn:Hhead; rewrite Hchild_none; simpl.
        * have Hatomic : @Atomic Runtime.LegacyLang.simp_lang WeaklyAtomic
              physical.
          { exact (Validity.open_certificate_runtime_atomic certificate
              runtime Hruntime_cost
              (resource_preserving_chunk_open_continuous Hchunk Hopen)
              Hnotatomic
              (resource_aligned_certificate_trusted_runtime_atomicity
                certificate derivation aligned runtime) physical Hhead). }
          iIntros "Hprefix".
          iApply (Validity.runtime_wp_atomic_mask_change physical
            (Validity.Model.enabled_runtime_mask ambient target.2)
            (Validity.Model.active_runtime_mask ambient entry) _).
          iMod "Hprefix" as "Hprefix".
          have Hrefine := balanced_chunk_region_runtime_refinement Hchunk
            runtime ambient
            (trace_runtime_cps_wp
              (resource_close_stack_prefix_trace aligned_rest below
                (resource_close_stack_split_of_target_handoff handoff))
              runtime ambient (fun _ => final)).
          unfold Validity.translated_runtime_wp in Hrefine.
          unfold Validity.certificate_runtime_statement in Hhead.
          rewrite Hhead Hactive in Hrefine.
          iPoseProof (Hrefine with "Hprefix") as "Hprefix".
          iApply (wp_mono with "Hprefix").
          iIntros (value) "[%Hunit Hchild]".
          iMod "Hchild" as "Hchild".
          iPoseProof (Hchild_close with "Hchild") as "Hfinal".
          iApply (fupd_mono with "Hfinal").
          iIntros "Hfinal". iSplit; first done.
          iModIntro. iExact "Hfinal".
        * iIntros "Hprefix". iMod "Hprefix" as "Hprefix".
          have Hrefine := balanced_chunk_region_runtime_refinement Hchunk
            runtime ambient
            (trace_runtime_cps_wp
              (resource_close_stack_prefix_trace aligned_rest below
                (resource_close_stack_split_of_target_handoff handoff))
              runtime ambient (fun _ => final)).
          unfold Validity.translated_runtime_wp in Hrefine.
          unfold Validity.certificate_runtime_statement in Hhead.
          rewrite Hhead Hactive in Hrefine.
          iPoseProof (Hrefine with "Hprefix") as "Hprefix".
          iMod "Hprefix" as "Hchild".
          iPoseProof (Hchild_close with "Hchild") as "Hfinal".
          iMod "Hfinal". iModIntro. iExact "Hfinal".
    - have Hopened_wf := RuntimeAdapter.Atomicity.certificate_preserves_wf
        cost entry statement opened Hwf certificate.
      have Hopened_stack :=
        RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate tail (focused :: tail) Hwf lifo Hstack.
      have Hopened_notatomic := Validity.certificate_preserves_nonatomic
        certificate Hnotatomic.
      have Hchild_envelope : Validity.Model.runtime_mask
          (Normalized.suffix_footprint
            (resource_certificate_suffix_of_operational_suffix
              (resource_close_stack_prefix aligned_body below
                (resource_close_stack_split_of_target_handoff handoff)))) ⊆
          ambient.
      { etransitivity; last exact Henvelope.
        apply Validity.Model.runtime_mask_mono.
        exact
          (resource_close_stack_split_access_child_prefix_footprint_subseteq
            aligned_body
            (resource_close_stack_split_of_target_handoff handoff)). }
      have IH := IHhandoff runtime ambient final Hruntime_cost
        Hprocedure_cost Hopened_wf Hopened_notatomic Hopened_stack
        Hchild_envelope.
      rewrite (resource_close_stack_split_access_source_runtime aligned_body
        (resource_close_stack_split_of_target_handoff handoff) runtime).
      rewrite (resource_close_stack_split_access_prefix_cps aligned_body
        (resource_close_stack_split_of_target_handoff handoff) runtime
        ambient (fun _ => final)).
      etrans; last exact IH.
      iIntros "Hprefix". iMod "Hprefix" as "Hprefix".
      iPoseProof (opening_chunk_region_runtime_refinement Hopening open_ok
        runtime ambient _ with "Hprefix") as "Hprefix".
      iMod "Hprefix". iModIntro. iExact "Hprefix".
    - have Hmiddle_wf := RuntimeAdapter.Atomicity.certificate_preserves_wf
        cost entry statement middle Hwf certificate.
      have Hmiddle_stack :=
        RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate (focused :: tail) (focused :: tail) Hwf lifo Hstack.
      have Hmiddle_notatomic := Validity.certificate_preserves_nonatomic
        certificate Hnotatomic.
      have Hchild_envelope : Validity.Model.runtime_mask
          (Normalized.suffix_footprint
            (resource_certificate_suffix_of_operational_suffix
              (resource_close_stack_prefix aligned_rest below
                (resource_close_stack_split_of_target_handoff handoff)))) ⊆
          ambient.
      { etransitivity; last exact Henvelope.
        apply Validity.Model.runtime_mask_mono.
        exact
          (resource_close_stack_split_focused_prefix_child_footprint_subseteq
            aligned_rest
            (resource_close_stack_split_of_target_handoff handoff)). }
      have IH := IHhandoff runtime ambient final Hruntime_cost
        Hprocedure_cost Hmiddle_wf Hmiddle_notatomic Hmiddle_stack
        Hchild_envelope.
      have Hopen := resource_target_position_open_nonempty target below
        (focused :: tail) position _ Hstack.
      destruct (resource_preserving_chunk_sparse Hchunk Hruntime_cost Hopen
        Hnotatomic runtime) as
        [_ [[Hnone _] | [Hentry_false Hmiddle_taken]]].
      + have Hnone_raw := Hnone.
        unfold Validity.certificate_runtime_statement in Hnone_raw.
        rewrite
          (resource_close_stack_split_focused_prefix_source_runtime
            aligned_rest
            (resource_close_stack_split_of_target_handoff handoff) runtime).
        rewrite Hnone. simpl.
        have Hactive : Validity.Model.active_runtime_mask ambient middle =
            Validity.Model.active_runtime_mask ambient entry.
        { apply Validity.Model.active_runtime_mask_same_open.
          symmetry. exact (@balanced_certificate_open_equal cost Γ fuel
            entry statement middle (focused :: tail) certificate Hwf Hstack
            lifo). }
        rewrite Hactive in IH.
        have Hid : forall X : option Runtime.LegacyLang.runtime_stmt,
            match X with Some physical => Some physical | None => None end = X.
        { intros [physical|]; reflexivity. }
        rewrite Hid.
        rewrite (resource_close_stack_split_focused_prefix_cps aligned_rest
          (resource_close_stack_split_of_target_handoff handoff) runtime
          ambient (fun _ => final)).
        etrans; last exact IH.
        iIntros "Hprefix".
        iMod "Hprefix" as "Hprefix".
        have Hrefine := balanced_chunk_region_runtime_refinement Hchunk runtime
          ambient
          (trace_runtime_cps_wp
            (resource_close_stack_prefix_trace aligned_rest below
              (resource_close_stack_split_of_target_handoff handoff))
            runtime ambient (fun _ => final)).
        unfold Validity.translated_runtime_wp in Hrefine.
        rewrite Hnone_raw Hactive in Hrefine.
        iPoseProof (Hrefine with "Hprefix") as "Hprefix".
        iMod "Hprefix". iModIntro. iExact "Hprefix".
      + rewrite
          (resource_close_stack_split_focused_prefix_source_runtime
            aligned_rest
            (resource_close_stack_split_of_target_handoff handoff) runtime).
        have Hchild_none :=
          resource_target_close_splice_prefix_none_when_step_taken handoff
            Hruntime_cost Hmiddle_wf Hmiddle_stack Hmiddle_notatomic
            Hmiddle_taken runtime.
        have Hchild_close :=
          resource_target_close_splice_ghost_prefix_closes handoff runtime
            ambient final Hruntime_cost Hmiddle_wf Hmiddle_notatomic
            Hmiddle_stack Hchild_none.
        have Hactive : Validity.Model.active_runtime_mask ambient middle =
            Validity.Model.active_runtime_mask ambient entry.
        { apply Validity.Model.active_runtime_mask_same_open.
          symmetry. exact (@balanced_certificate_open_equal cost Γ fuel
            entry statement middle (focused :: tail) certificate Hwf Hstack
            lifo). }
        rewrite Hactive in Hchild_close.
        rewrite (resource_close_stack_split_focused_prefix_cps aligned_rest
          (resource_close_stack_split_of_target_handoff handoff) runtime
          ambient (fun _ => final)).
        destruct (Validity.certificate_runtime_statement certificate runtime)
          as [physical|] eqn:Hhead; rewrite Hchild_none; simpl.
        * have Hatomic : @Atomic Runtime.LegacyLang.simp_lang WeaklyAtomic
              physical.
          { exact (Validity.open_certificate_runtime_atomic certificate
              runtime Hruntime_cost
              (resource_preserving_chunk_open_continuous Hchunk Hopen)
              Hnotatomic
              (resource_aligned_certificate_trusted_runtime_atomicity
                certificate derivation aligned runtime) physical Hhead). }
          iIntros "Hprefix".
          iApply (Validity.runtime_wp_atomic_mask_change physical
            (Validity.Model.enabled_runtime_mask ambient target.2)
            (Validity.Model.active_runtime_mask ambient entry) _).
          iMod "Hprefix" as "Hprefix".
          have Hrefine := balanced_chunk_region_runtime_refinement Hchunk
            runtime ambient
            (trace_runtime_cps_wp
              (resource_close_stack_prefix_trace aligned_rest below
                (resource_close_stack_split_of_target_handoff handoff))
              runtime ambient (fun _ => final)).
          unfold Validity.translated_runtime_wp in Hrefine.
          unfold Validity.certificate_runtime_statement in Hhead.
          rewrite Hhead Hactive in Hrefine.
          iPoseProof (Hrefine with "Hprefix") as "Hprefix".
          iApply (wp_mono with "Hprefix").
          iIntros (value) "[%Hunit Hchild]".
          iMod "Hchild" as "Hchild".
          iPoseProof (Hchild_close with "Hchild") as "Hfinal".
          iApply (fupd_mono with "Hfinal").
          iIntros "Hfinal". iSplit; first done.
          iModIntro. iExact "Hfinal".
        * iIntros "Hprefix". iMod "Hprefix" as "Hprefix".
          have Hrefine := balanced_chunk_region_runtime_refinement Hchunk
            runtime ambient
            (trace_runtime_cps_wp
              (resource_close_stack_prefix_trace aligned_rest below
                (resource_close_stack_split_of_target_handoff handoff))
              runtime ambient (fun _ => final)).
          unfold Validity.translated_runtime_wp in Hrefine.
          unfold Validity.certificate_runtime_statement in Hhead.
          rewrite Hhead Hactive in Hrefine.
          iPoseProof (Hrefine with "Hprefix") as "Hprefix".
          iMod "Hprefix" as "Hchild".
          iPoseProof (Hchild_close with "Hchild") as "Hfinal".
          iMod "Hfinal". iModIntro. iExact "Hfinal".
    - have Hopened_wf := RuntimeAdapter.Atomicity.certificate_preserves_wf
        cost entry statement opened Hwf certificate.
      have Hopened_stack :=
        RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate (focused :: tail) (nested :: focused :: tail) Hwf lifo
          Hstack.
      have Hopened_notatomic := Validity.certificate_preserves_nonatomic
        certificate Hnotatomic.
      have Hchild_envelope : Validity.Model.runtime_mask
          (Normalized.suffix_footprint
            (resource_certificate_suffix_of_operational_suffix
              (resource_close_stack_prefix aligned_body below
                (resource_close_stack_split_of_target_handoff handoff)))) ⊆
          ambient.
      { etransitivity; last exact Henvelope.
        apply Validity.Model.runtime_mask_mono.
        exact (resource_close_stack_split_nested_child_footprint_subseteq
          aligned_body
          (resource_close_stack_split_of_target_handoff handoff)). }
      have IH := IHhandoff runtime ambient final Hruntime_cost
        Hprocedure_cost Hopened_wf Hopened_notatomic Hopened_stack
        Hchild_envelope.
      rewrite (resource_close_stack_split_nested_source_runtime aligned_body
        (resource_close_stack_split_of_target_handoff handoff) runtime).
      rewrite (resource_close_stack_split_nested_prefix_cps aligned_body
        (resource_close_stack_split_of_target_handoff handoff) runtime
        ambient (fun _ => final)).
      etrans; last exact IH.
      iIntros "Hprefix". iMod "Hprefix" as "Hprefix".
      iPoseProof (opening_chunk_region_runtime_refinement Hopening open_ok
        runtime ambient _ with "Hprefix") as "Hprefix".
      iMod "Hprefix". iModIntro. iExact "Hprefix".
    - have Hclosed_wf := RuntimeAdapter.Atomicity.certificate_preserves_wf
        cost entry statement closed Hwf certificate.
      have Hclosed_stack :=
        RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate (focused :: tail) tail Hwf lifo Hstack.
      have Hclosed_notatomic := Validity.certificate_preserves_nonatomic
        certificate Hnotatomic.
      have Hchild_envelope : Validity.Model.runtime_mask
          (Normalized.suffix_footprint
            (resource_certificate_suffix_of_operational_suffix
              (resource_close_stack_prefix aligned_rest below
                (resource_close_stack_split_of_target_handoff handoff)))) ⊆
          ambient.
      { etransitivity; last exact Henvelope.
        apply Validity.Model.runtime_mask_mono.
        exact
          (resource_close_stack_split_past_focused_close_child_footprint_subseteq
            aligned_rest
            (resource_close_stack_split_of_target_handoff handoff)). }
      have IH := IHhandoff runtime ambient final Hruntime_cost
        Hprocedure_cost Hclosed_wf Hclosed_notatomic Hclosed_stack
        Hchild_envelope.
      rewrite
        (resource_close_stack_split_past_focused_close_source_runtime
          aligned_rest (resource_close_stack_split_of_target_handoff handoff)
          runtime).
      rewrite
        (resource_close_stack_split_past_focused_close_prefix_cps aligned_rest
          (resource_close_stack_split_of_target_handoff handoff) runtime
          ambient (fun _ => final)).
      etrans; last exact IH.
      iIntros "Hprefix". iMod "Hprefix" as "Hprefix".
      iPoseProof (closing_chunk_region_runtime_refinement Hclosing close_ok
        runtime ambient _ with "Hprefix") as "Hprefix".
      iMod "Hprefix". iModIntro. iExact "Hprefix".
    - have Hclosed_wf := RuntimeAdapter.Atomicity.certificate_preserves_wf
        cost entry statement closed Hwf certificate.
      have Hclosed_stack :=
        RuntimeAdapter.Atomicity.lifo_preserves_access_stack_consistency
          certificate (focused :: tail) tail Hwf lifo Hstack.
      have Hclosed_notatomic := Validity.certificate_preserves_nonatomic
        certificate Hnotatomic.
      have Hchild_envelope : Validity.Model.runtime_mask
          (Normalized.suffix_footprint
            (resource_certificate_suffix_of_operational_suffix
              (resource_close_stack_prefix aligned_rest below
                (resource_close_stack_split_of_target_handoff handoff)))) ⊆
          ambient.
      { etransitivity; last exact Henvelope.
        apply Validity.Model.runtime_mask_mono.
        exact
          (resource_close_stack_split_past_ordinary_close_child_footprint_subseteq
            aligned_rest
            (resource_close_stack_split_of_target_handoff handoff)). }
      have IH := IHhandoff runtime ambient final Hruntime_cost
        Hprocedure_cost Hclosed_wf Hclosed_notatomic Hclosed_stack
        Hchild_envelope.
      rewrite
        (resource_close_stack_split_past_ordinary_close_source_runtime
          aligned_rest (resource_close_stack_split_of_target_handoff handoff)
          runtime).
      rewrite
        (resource_close_stack_split_past_ordinary_close_prefix_cps aligned_rest
          (resource_close_stack_split_of_target_handoff handoff) runtime
          ambient (fun _ => final)).
      etrans; last exact IH.
      iIntros "Hprefix". iMod "Hprefix" as "Hprefix".
      iPoseProof (closing_chunk_region_runtime_refinement Hclosing close_ok
        runtime ambient _ with "Hprefix") as "Hprefix".
      iMod "Hprefix". iModIntro. iExact "Hprefix".
  Qed.

  Lemma resource_aligned_operational_suffix_preserves_nonatomic
      {cost Γ F Δ entry pre stack_in exit post stack_out}
      (suffix : Validity.resource_aligned_operational_suffix cost Γ F Δ
        entry pre stack_in exit post stack_out) :
    RuntimeAdapter.Atomicity.analysis_in_atomic entry = false ->
    RuntimeAdapter.Atomicity.analysis_in_atomic exit = false.
  Proof.
    induction suffix; intros Hnotatomic; first exact Hnotatomic.
    apply IHsuffix.
    eapply Validity.certificate_preserves_nonatomic; eauto.
  Qed.

  (** The only new Iris proof required at a close leaf.  Its proof consumes
      the completed sparse source equation, prefix atomicity, restored-open
      equation, and the assertion-aware CPS handoff. *)
  Theorem resource_target_close_splice_assertion_refinement_spike :
    resource_target_close_splice_assertion_contract.
  Proof.
    intros cost Γ F Δ entry pre stack_in exit post stack_out mode tail
      source tree suffix trace target below position aligned_trace handoff
      Hhandoff.
    unfold resource_target_close_splice_assertion_refinement. cbv zeta.
    intros runtime ambient Hruntime_cost Hprocedure_cost Hwf
      Hnotatomic Hstack Henvelope formals binders atoms carried final Hrest
      Hcont.
    set (split := resource_close_stack_split_of_target_handoff handoff).
    set (post_resources :=
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms post ∗
       Validity.World.access_stack_interp atoms ambient stack_out ∗ carried)%I).
    have Hprefix_envelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (resource_certificate_suffix_of_operational_suffix
            (resource_close_stack_prefix _ _ split))) ⊆ ambient.
    { etransitivity; last exact Henvelope.
      apply Validity.Model.runtime_mask_mono.
      exact (resource_close_stack_split_prefix_footprint_subseteq split). }
    have Hclose_open : RuntimeAdapter.Atomicity.analysis_open
        (resource_close_stack_state _ _ split) = target.2.
    { exact (resource_target_close_splice_close_open handoff Hwf Hstack). }
    have Hclose_active : Validity.Model.active_runtime_mask ambient
        (resource_close_stack_state _ _ split) =
        Validity.Model.enabled_runtime_mask ambient target.2.
    { unfold Validity.Model.active_runtime_mask,
        Validity.Model.enabled_runtime_mask.
      rewrite Hclose_open. reflexivity. }
    have Htrace := Hhandoff runtime ambient formals binders atoms carried
      post_resources Hruntime_cost Hprocedure_cost Hwf Hstack Hprefix_envelope
      Hrest.
    unfold ConcreteOrdinaryTrace.source_translated_wp in Htrace.
    rewrite Hclose_active in Htrace.
    have Hsource := resource_target_close_splice_source_runtime handoff
      Hruntime_cost Hwf Hstack Hnotatomic runtime.
    have Hprefix_source :=
      resource_target_close_splice_prefix_cps_source_spike handoff runtime
        ambient
        (Validity.runtime_option_wp
          (Validity.Model.enabled_runtime_mask ambient target.2)
          (Validity.Model.active_runtime_mask ambient exit)
          (ConcreteOrdinaryTrace.source_runtime
            (resource_certificate_suffix_of_operational_suffix
              (resource_close_stack_rest _ _ split)) runtime) post_resources)
        Hruntime_cost Hprocedure_cost Hwf Hnotatomic Hstack Hprefix_envelope.
    unfold split in *.
    unfold ConcreteOrdinaryTrace.source_translated_wp.
    rewrite Hsource.
    iIntros "Hresources".
    iApply (Validity.runtime_option_wp_close_continuation _ _ _ post_resources
      final Hcont).
    iApply (Validity.runtime_option_wp_sequence
      (Validity.Model.enabled_runtime_mask ambient target.2)
      (Validity.Model.active_runtime_mask ambient exit)
      (ConcreteOrdinaryTrace.source_runtime
        (resource_certificate_suffix_of_operational_suffix
          (resource_close_stack_prefix _ _
            (resource_close_stack_split_of_target_handoff handoff))) runtime)
      (ConcreteOrdinaryTrace.source_runtime
        (resource_certificate_suffix_of_operational_suffix
          (resource_close_stack_rest _ _
            (resource_close_stack_split_of_target_handoff handoff))) runtime)
      post_resources).
    iApply Hprefix_source.
    iApply (fupd_mono with "Hresources").
    iIntros "Hresources".
    iPoseProof (Htrace with "Hresources") as "Htrace".
    iExact "Htrace".
  Qed.

  (** Assertion-aware interpretation of the existing path-sensitive outcome
      tree.  This is the interpretation consumed by the final conditional
      assembly: a close leaf has already crossed the first-close source seam,
      while a continuous leaf deliberately remains continuation-parametric.
      In particular, this does not flatten an unmatched open to an outer-mask
      WP. *)
  Fixpoint resource_target_outcome_assertion_interpretation
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source tree
       suffix trace}
      {aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        stack_in exit post stack_out mode tail source tree suffix trace}
      {target below position}
      (outcome : resource_target_trace_outcome aligned_trace target below
        position) : Prop :=
    match outcome with
    | ResourceTargetOutcomeClose handoff =>
        resource_target_close_splice_assertion_refinement handoff
    | @ResourceTargetOutcomeContinuous cost0 Γ0 F0 Δ0 entry0 pre0 stack_in0
        exit0 post0 stack_out0 mode0 tail0 source0 tree0 suffix0 trace0 target0
        below0 position_in0 position_out0 aligned0 continuous0 =>
        resource_pending_open_trace_refinement aligned0
    | ResourceTargetOutcomeChunk child =>
        resource_target_outcome_assertion_interpretation child
    | ResourceTargetOutcomeAccess child =>
        resource_target_outcome_assertion_interpretation child
    | ResourceTargetOutcomeFocusedPrefix child =>
        resource_target_outcome_assertion_interpretation child
    | ResourceTargetOutcomeNestedAccess child =>
        resource_target_outcome_assertion_interpretation child
    | ResourceTargetOutcomePastFocusedClose child =>
        resource_target_outcome_assertion_interpretation child
    | ResourceTargetOutcomePastOrdinaryClose child =>
        resource_target_outcome_assertion_interpretation child
    | ResourceTargetOutcomeExpansion child =>
        resource_target_outcome_assertion_interpretation child
    | ResourceTargetOutcomeSequenceExpansion child =>
        resource_target_outcome_assertion_interpretation child
    | ResourceTargetOutcomeFocusedConditionalClose _ then_outcome else_outcome
        => resource_target_outcome_assertion_interpretation then_outcome /\
           resource_target_outcome_assertion_interpretation else_outcome
    | ResourceTargetOutcomeFocusedConditionalRest then_outcome else_outcome
        rest_outcome =>
        resource_target_outcome_assertion_interpretation then_outcome /\
        resource_target_outcome_assertion_interpretation else_outcome /\
        resource_target_outcome_assertion_interpretation rest_outcome
    | ResourceTargetOutcomeOrdinaryConditionalContinue then_outcome
        else_outcome rest_outcome =>
        resource_target_outcome_assertion_interpretation then_outcome /\
        resource_target_outcome_assertion_interpretation else_outcome /\
        resource_target_outcome_assertion_interpretation rest_outcome
    | ResourceTargetOutcomeOrdinaryConditionalClose _ then_outcome else_outcome
        => resource_target_outcome_assertion_interpretation then_outcome /\
           resource_target_outcome_assertion_interpretation else_outcome
    | ResourceTargetOutcomeFocusedConditionalContinue then_outcome else_outcome
        rest_outcome =>
        resource_target_outcome_assertion_interpretation then_outcome /\
        resource_target_outcome_assertion_interpretation else_outcome /\
        resource_target_outcome_assertion_interpretation rest_outcome
    end.

  Theorem resource_target_outcome_assertion_interpretation_complete
      (Hleaf : resource_target_close_splice_assertion_contract)
      {cost Γ F Δ entry pre stack_in exit post stack_out mode tail source tree
       suffix trace}
      {aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        stack_in exit post stack_out mode tail source tree suffix trace}
      {target below position}
      (outcome : resource_target_trace_outcome aligned_trace target below
        position) :
    resource_target_outcome_assertion_interpretation outcome.
  Proof.
    induction outcome; simpl.
    - apply Hleaf. apply resource_target_close_splice_cps_handoff_complete.
    - apply resource_pending_open_trace_refinement_complete.
    - exact IHoutcome.
    - exact IHoutcome.
    - exact IHoutcome.
    - exact IHoutcome.
    - exact IHoutcome.
    - exact IHoutcome.
    - exact IHoutcome.
    - exact IHoutcome.
    - split; assumption.
    - repeat split; assumption.
    - repeat split; assumption.
    - split; assumption.
    - repeat split; assumption.
  Qed.

  (** The adequacy-facing endpoint is deliberately balanced.  A focused
      subtrace is interpreted only through the continuation-aware
      first-close/still-open judgments above; it is never flattened into an
      outer-mask WP while its focus remains unmatched. *)
  Definition resource_closed_trace_runtime_refinement
      {cost Γ F Δ entry pre exit post source tree suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre []
        exit post [] None [] source tree suffix trace) : Prop :=
    resource_aligned_trace_runtime_refinement aligned_trace.

  (** Internal balanced induction target.  The stack may be nonempty because
      closing an outer target leaves precisely its [below] stack for the
      post-close recursive suffix.  Requiring the same stack on both sides is
      the sound strengthening; quantifying over unrelated input/output stacks
      would recreate the unmatched-open mask error. *)
  Definition resource_balanced_ordinary_trace_runtime_refinement
      {cost Γ F Δ entry pre stack exit post source tree suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre stack
        exit post stack None stack source tree suffix trace) : Prop :=
    resource_aligned_trace_runtime_refinement aligned_trace.

  (** Balanced structural boundary.  The structural component is indexed
      by the target's actual path-sensitive outcome.  This is essential for
      conditionals: a continuously-open arm contributes its pending CPS
      interpretation, whereas a locally-closing arm retains its splice
      handoff until the selected close has restored the outer mask.  It makes
      no flat outer-CPS claim for an intermediate trace; that projection is
      performed only by the balanced component.
      In particular, preserving prefixes are not composed with an already
      flattened child, since doing so would hide the close-back update needed
      by a preceding physical step. *)
  Theorem resource_aligned_trace_runtime_refinement_boundary_spike
      (Hleaf : resource_target_close_splice_assertion_contract) :
    (forall cost Γ F Δ entry pre stack_in exit post stack_out mode tail
        source tree suffix trace
        (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry
          pre stack_in exit post stack_out mode tail source tree suffix trace)
        target below
        (position : resource_target_position target below stack_in),
      exists outcome : resource_target_trace_outcome aligned_trace target below
          position,
        resource_target_outcome_assertion_interpretation outcome) /\
    (forall cost Γ F Δ entry pre stack exit post source tree suffix trace
        (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
          stack exit post stack None stack source tree suffix trace),
      resource_balanced_ordinary_trace_runtime_refinement aligned_trace).
  Proof.
    split.
    - intros cost Γ F Δ entry pre stack_in exit post stack_out mode tail source
        tree suffix trace aligned_trace target below position.
      exists (resource_target_trace_outcome_complete aligned_trace target below
        position).
      apply resource_target_outcome_assertion_interpretation_complete.
      exact Hleaf.
    - admit.
  Admitted.

  Theorem resource_aligned_trace_runtime_refinement_spike
      {cost Γ F Δ entry pre exit post source tree suffix trace}
      (aligned_trace : @resource_aligned_net_trace cost Γ F Δ entry pre
        [] exit post [] None [] source tree suffix trace) :
    resource_closed_trace_runtime_refinement aligned_trace.
  Proof.
    exact ((proj2 (resource_aligned_trace_runtime_refinement_boundary_spike
      resource_target_close_splice_assertion_refinement_spike)) _ _ _ _ _ _
      _ _ _ _ _ _ _ aligned_trace).
  Qed.

  Theorem resource_aligned_certificate_footprint_subset_exit_resources_spike
      {cost} {Γ F Δ : typed_core.TypedCore.context} {fuel}
      {entry statement exit}
      {pre post : Runtime.Translation.Assertions.assertion Γ F Δ}
      (certificate : RuntimeAdapter.Atomicity.analysis_certificate cost Γ
        fuel entry statement exit)
      (derivation : Validity.Certified.Rules.RavenResourceTriple pre
        statement post)
      (aligned : Validity.Certified.resource_certificate_hoare_aligned cost
        certificate derivation) :
    RuntimeAdapter.Atomicity.certificate_footprint certificate ⊆
    RuntimeAdapter.Atomicity.analysis_mask exit ∪
        RuntimeAdapter.Atomicity.analysis_open exit.
  Admitted.
  (* Direct induction draft; keep out of the compiled path until its
     propositional cases have been made predictably cheap.
    induction aligned; simpl.
    - have Hstart := RuntimeAdapter.Atomicity.take_step_resources_monotone
        _ _ _ step.
      intros other Hmember.
      specialize (Hstart other).
      rewrite !elem_of_union in Hmember, Hstart |- *.
      rewrite elem_of_empty in Hmember.
      tauto.
    - apply RuntimeAdapter.Atomicity.open_invariant_success in step as
        (Hfresh & Havailable & Hmask & Hopen).
      rewrite Hmask. rewrite Hopen.
      intros other Hmember.
      rewrite !elem_of_union in Hmember |- *.
      rewrite !elem_of_difference in Hmember |- *.
      rewrite !elem_of_singleton in Hmember |- *.
      rewrite elem_of_empty in Hmember.
      destruct (decide (other = invariant)) as [->|Hneq]; tauto.
    - unfold RuntimeAdapter.Atomicity.fold_invariant.
      destruct (bool_decide (invariant ∈
        RuntimeAdapter.Atomicity.analysis_open entry)); simpl;
        intros other Hmember;
        rewrite !elem_of_union in Hmember |- *;
        rewrite ?elem_of_difference in Hmember |- *;
        rewrite ?elem_of_singleton in Hmember |- *;
        rewrite elem_of_empty in Hmember;
        destruct (decide (other = invariant)) as [->|Hneq]; tauto.
    - have Hmiddle : RuntimeAdapter.Atomicity.analysis_mask middle ∪
        RuntimeAdapter.Atomicity.analysis_open middle ⊆
        RuntimeAdapter.Atomicity.analysis_mask exit ∪
        RuntimeAdapter.Atomicity.analysis_open exit.
      { etrans.
        - intros invariant Hmember.
          rewrite elem_of_union in Hmember.
          destruct Hmember as [Hmask|Hopen].
          + apply (RuntimeAdapter.Atomicity.certificate_entry_subset_footprint
              second_certificate). exact Hmask.
          + apply (RuntimeAdapter.Atomicity.certificate_entry_open_subset_footprint
              second_certificate). exact Hopen.
        - assumption. }
      have Hstart : RuntimeAdapter.Atomicity.analysis_mask state ∪
          RuntimeAdapter.Atomicity.analysis_open state ⊆
          RuntimeAdapter.Atomicity.analysis_mask middle ∪
          RuntimeAdapter.Atomicity.analysis_open middle.
      { etrans.
        - intros invariant Hmember.
          rewrite elem_of_union in Hmember.
          destruct Hmember as [Hmask|Hopen].
          + apply (RuntimeAdapter.Atomicity.certificate_entry_subset_footprint
              first_certificate). exact Hmask.
          + apply (RuntimeAdapter.Atomicity.certificate_entry_open_subset_footprint
              first_certificate). exact Hopen.
        - assumption. }
      intros other Hmember.
      rewrite !elem_of_union in Hmember, Hmiddle, Hstart |- *.
      destruct Hmember as [[[[Hentry_mask | Hentry_open] | Hexit_mask] |
        Hexit_open] | [Hfirst | Hsecond]].
      - apply Hstart. left. exact Hentry_mask.
      - apply Hstart. right. exact Hentry_open.
      - apply Hmiddle. left. exact Hexit_mask.
      - apply Hmiddle. right. exact Hexit_open.
      - eauto.
      - eauto.
    - rewrite then_mask in *.
      rewrite else_mask in *.
      rewrite <- open_equal in *.
      have Hmask_idem : branch_mask ∩ branch_mask = branch_mask.
      { apply set_eq. intros invariant.
        rewrite elem_of_intersection. tauto. }
      rewrite Hmask_idem.
      have Hstart : RuntimeAdapter.Atomicity.analysis_mask state ∪
          RuntimeAdapter.Atomicity.analysis_open state ⊆
          branch_mask ∪ RuntimeAdapter.Atomicity.analysis_open then_exit.
      { etrans.
        - intros invariant Hmember.
          rewrite elem_of_union in Hmember.
          destruct Hmember as [Hmask|Hopen].
          + apply (RuntimeAdapter.Atomicity.certificate_entry_subset_footprint
              then_certificate). exact Hmask.
          + apply (RuntimeAdapter.Atomicity.certificate_entry_open_subset_footprint
              then_certificate). exact Hopen.
        - assumption. }
      intros other Hmember.
      rewrite !elem_of_union in Hmember |- *.
      destruct Hmember as [[[[Hentry_mask | Hentry_open] | Hexit_mask] |
        Hexit_open] | [Hthen | Helse]].
      + exact (Hstart (or_introl Hentry_mask)).
      + exact (Hstart (or_intror Hentry_open)).
      + left. exact Hexit_mask.
      + right. exact Hexit_open.
      + eauto.
      + eauto.
    - have Hsets := RuntimeAdapter.Atomicity.atomic_step_preserves_sets
        _ _ step.
      destruct Hsets as [Hmask Hopen].
      have Hentry : RuntimeAdapter.Atomicity.analysis_mask state ∪
          RuntimeAdapter.Atomicity.analysis_open state ⊆
          RuntimeAdapter.Atomicity.analysis_mask inner ∪
          RuntimeAdapter.Atomicity.analysis_open inner.
      { rewrite <- Hmask, <- Hopen.
        etrans.
        - intros invariant Hmember.
          rewrite elem_of_union in Hmember.
          destruct Hmember as [Hmask'|Hopen'].
          + apply (RuntimeAdapter.Atomicity.certificate_entry_subset_footprint
              body_certificate). exact Hmask'.
          + apply (RuntimeAdapter.Atomicity.certificate_entry_open_subset_footprint
              body_certificate). exact Hopen'.
      - assumption. }
      intros other Hmember.
      rewrite !elem_of_union in Hmember, Hentry |- *.
      destruct Hmember as [[[[Hentry_mask | Hentry_open] | Hexit_mask] |
        Hexit_open] | Hbody].
      + exact (Hentry (or_introl Hentry_mask)).
      + exact (Hentry (or_intror Hentry_open)).
      + left. exact Hexit_mask.
      + right. exact Hexit_open.
      + eauto.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
  Qed. *)

  (** Go/no-go endpoint: once the two obligations above are supplied, total
      resource normalization and singleton source reification reach the
      actual closed runtime theorem consumed by adequacy. *)
  Theorem closed_resource_certificate_runtime_semantically_valid_spike
      {cost} {Γ F Δ : typed_core.TypedCore.context} {fuel}
      {entry statement exit}
      {pre post : Runtime.Translation.Assertions.assertion Γ F Δ}
      (certified : @Validity.Certified.CertifiedRavenResourceTriple cost Γ F
        Δ fuel [] [] pre statement entry exit post) :
    Validity.Model.runtime_cost_model_sound cost ->
    RuntimeAdapter.Atomicity.state_wf entry ->
    @Validity.closed_certificate_runtime_semantically_valid Γ F Δ fuel cost
      pre post statement entry exit
      (@Validity.Certified.certified_resource_analysis cost Γ F Δ fuel [] []
        pre statement entry exit post certified).
  Proof.
    destruct certified as [certificate lifo Hprocedure derivation aligned].
    simpl. intros Hruntime Hwf Hentry_open Hexit_open _ Hnotatomic runtime
      formals binders atoms ambient Hexit_mask.
    have Hstack : RuntimeAdapter.Atomicity.access_stack_consistent
        (RuntimeAdapter.Atomicity.analysis_open entry) [].
    { apply RuntimeAdapter.Atomicity.access_stack_consistent_empty.
      exact Hentry_open. }
    pose proof (resource_aligned_singleton_total_normalization_complete
      certificate derivation aligned lifo Hwf Hstack) as Htotal.
    destruct Htotal as [Hordinary _].
    destruct Hordinary as [tree [trace aligned_trace]].
    have Henvelope : Validity.Model.runtime_mask
        (Normalized.suffix_footprint
          (RuntimeAdapter.singleton_suffix certificate)) ⊆ ambient.
    { etrans; last exact Hexit_mask.
      apply Validity.Model.runtime_mask_mono.
      simpl.
      rewrite union_empty_r.
      etrans.
      - apply resource_aligned_certificate_footprint_subset_exit_resources_spike
          with (derivation := derivation). exact aligned.
      - rewrite Hexit_open. set_solver. }
    pose proof (resource_aligned_trace_runtime_refinement_spike aligned_trace
      Hruntime Hprocedure Hwf Hnotatomic Hstack runtime formals binders atoms
      ambient Henvelope) as Hrefinement.
    rewrite ConcreteOrdinaryTrace.singleton_source_translated_wp in
      Hrefinement.
    exact Hrefinement.
  Qed.
End Phase7MixedEndToEndSpike.

End WithRuntimeValidity.
End WithContracts.
End Make.
