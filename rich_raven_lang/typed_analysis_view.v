From Coq Require Import Bool Lia Program.Equality ProofIrrelevance.
From stdpp Require Import gmap.

From raven_iris.rich_raven_lang Require Import typed_core.

(** A small, non-generative boundary between an intrinsically typed statement
    family and the atomicity analyzer.  The analyzer never needs the payload
    of leaves, conditions, or invariant arguments; it needs only this control
    view while retaining the original statement opaquely. *)
Module TypedAnalysisView.

Import TypedCore.

Module Type STATEMENT_FAMILY.
  Parameter statement : context -> Type.
End STATEMENT_FAMILY.

Inductive statement_view (statement : context -> Type) (Γ : context) : Type :=
| ViewLeaf
(* The empty continuation.  Unlike a leaf it is never charged through the
   cost model: it is the identity on the analysis state by construction. *)
| ViewDone
| ViewUnfold (invariant : inv_id)
| ViewFold (invariant : inv_id)
| ViewSequence (first second : statement Γ)
| ViewConditional (then_branch else_branch : statement Γ)
| ViewStructuredAccess (invariant : inv_id) (body : statement Γ)
| ViewAtomic (body : statement Γ).

Arguments ViewLeaf {_ _}.
Arguments ViewDone {_ _}.
Arguments ViewUnfold {_ _} _.
Arguments ViewFold {_ _} _.
Arguments ViewSequence {_ _} _ _.
Arguments ViewConditional {_ _} _ _.
Arguments ViewStructuredAccess {_ _} _ _.
Arguments ViewAtomic {_ _} _.

Module Type ANALYSIS_SYNTAX.
  Include STATEMENT_FAMILY.
  Parameter view : forall Γ, statement Γ -> statement_view statement Γ.
  Parameter size : forall Γ, statement Γ -> nat.
  Parameter size_positive : forall Γ (statement : statement Γ),
    0 < size Γ statement.
  Parameter sequence_children_smaller : forall Γ statement first second,
    view Γ statement = ViewSequence first second ->
    size Γ first < size Γ statement /\ size Γ second < size Γ statement.
  Parameter conditional_children_smaller : forall Γ statement then_branch else_branch,
    view Γ statement = ViewConditional then_branch else_branch ->
    size Γ then_branch < size Γ statement /\
    size Γ else_branch < size Γ statement.
  Parameter atomic_body_smaller : forall Γ statement body,
    view Γ statement = ViewAtomic body -> size Γ body < size Γ statement.
End ANALYSIS_SYNTAX.

Module Analysis (Syntax : ANALYSIS_SYNTAX).

Inductive step_cost :=
| NoStep
| AtomicStep
| NonAtomicStep
| ProcedureCallStep (required granted : gset inv_id)
| ProcedureSpawnStep (required : gset inv_id).

Inductive analysis_error :=
| MissingInvariant (invariant : inv_id)
| ReentrantInvariant (invariant : inv_id)
| SecondAtomicStep
| NonAtomicWhileOpen
| MissingProcedureMask
| ProcedureGrantAlreadyOpen
| AtomicBlockLeaksAccess
| StructuredAccessRequiresCertificate
| IncompatibleBranches
| IncoherentConditionalMasks
| FuelExhausted.

Record analysis_state := AnalysisState {
  analysis_mask : gset inv_id;
  analysis_open : gset inv_id;
  analysis_step_taken : bool;
  analysis_in_atomic : bool;
}.

Definition state_wf state : Prop :=
  analysis_open state ## analysis_mask state.

Definition cost_model := forall Γ, Syntax.statement Γ -> step_cost.

Definition take_plain_step cost state : analysis_error + analysis_state :=
  if analysis_in_atomic state || bool_decide (analysis_open state = ∅) then
    inr state
  else match cost with
  | NoStep => inr state
  | AtomicStep =>
      if analysis_step_taken state then inl SecondAtomicStep
      else inr (AnalysisState (analysis_mask state) (analysis_open state)
        true false)
  | NonAtomicStep => inl NonAtomicWhileOpen
  | ProcedureCallStep _ _ | ProcedureSpawnStep _ => inl NonAtomicWhileOpen
  end.

Definition grant_state (granted : gset inv_id) state : analysis_state :=
  AnalysisState (analysis_mask state ∪ granted) (analysis_open state)
    (analysis_step_taken state) (analysis_in_atomic state).

Definition take_step cost state : analysis_error + analysis_state :=
  match cost with
  | ProcedureCallStep required granted =>
      if bool_decide (required ⊆ analysis_mask state) then
        match take_plain_step NonAtomicStep state with
        | inl error => inl error
        | inr stepped =>
            if bool_decide (granted ## analysis_open stepped)
            then inr (grant_state granted stepped)
            else inl ProcedureGrantAlreadyOpen
        end
      else inl MissingProcedureMask
  | ProcedureSpawnStep required =>
      if bool_decide (required ⊆ analysis_mask state)
      then take_plain_step NonAtomicStep state
      else inl MissingProcedureMask
  | NoStep | AtomicStep | NonAtomicStep => take_plain_step cost state
  end.

Arguments take_step : simpl never.

Definition open_invariant invariant state : analysis_error + analysis_state :=
  if bool_decide (invariant ∈ analysis_open state) then
    inl (ReentrantInvariant invariant)
  else if bool_decide (invariant ∈ analysis_mask state) then
    inr (AnalysisState (analysis_mask state ∖ {[invariant]})
      ({[invariant]} ∪ analysis_open state) (analysis_step_taken state)
      (analysis_in_atomic state))
  else inl (MissingInvariant invariant).

Definition fold_invariant invariant state : analysis_state :=
  if bool_decide (invariant ∈ analysis_open state) then
    let remaining := analysis_open state ∖ {[invariant]} in
    AnalysisState ({[invariant]} ∪ analysis_mask state) remaining
      (if bool_decide (remaining = ∅) then false
       else analysis_step_taken state) (analysis_in_atomic state)
  else AnalysisState ({[invariant]} ∪ analysis_mask state)
    (analysis_open state) (analysis_step_taken state) (analysis_in_atomic state).

Lemma take_plain_step_preserves_sets cost state exit :
  take_plain_step cost state = inr exit ->
  analysis_mask exit = analysis_mask state /\
  analysis_open exit = analysis_open state.
Proof.
  unfold take_plain_step.
  destruct (analysis_in_atomic state ||
    bool_decide (analysis_open state = ∅)); first by intros [= <-].
  destruct cost; try by intros [= <-]; try discriminate.
  destruct (analysis_step_taken state); first discriminate.
  intros Hinr. inversion Hinr. done.
Qed.

Lemma take_step_preserves_open cost state exit :
  take_step cost state = inr exit ->
  analysis_open exit = analysis_open state.
Proof.
  unfold take_step.
  destruct cost; try (apply take_plain_step_preserves_sets; assumption).
  - destruct (bool_decide (_ ⊆ _)); last discriminate.
    destruct (take_plain_step NonAtomicStep state) as [error|stepped]
      eqn:Hstep; first discriminate.
    destruct (bool_decide (_ ## _)); last discriminate.
    intros [= <-]. simpl.
    exact (proj2 (take_plain_step_preserves_sets _ _ _ Hstep)).
  - destruct (bool_decide (_ ⊆ _)); last discriminate.
    apply take_plain_step_preserves_sets.
Qed.

Lemma take_plain_step_preserves_in_atomic cost state exit :
  take_plain_step cost state = inr exit ->
  analysis_in_atomic exit = analysis_in_atomic state.
Proof.
  unfold take_plain_step.
  destruct (analysis_in_atomic state ||
    bool_decide (analysis_open state = ∅)) eqn:Hallowed;
    first by intros [= <-].
  apply orb_false_iff in Hallowed as [Hin_atomic _].
  destruct cost; try by intros [= <-]; try discriminate.
  destruct (analysis_step_taken state); first discriminate.
  intros [= <-]. simpl. symmetry. exact Hin_atomic.
Qed.

Lemma take_step_preserves_in_atomic cost state exit :
  take_step cost state = inr exit ->
  analysis_in_atomic exit = analysis_in_atomic state.
Proof.
  unfold take_step. destruct cost;
    try (apply take_plain_step_preserves_in_atomic; assumption).
  - destruct (bool_decide (_ ⊆ _)); last discriminate.
    destruct (take_plain_step NonAtomicStep state) as [error|stepped]
      eqn:Hplain; first discriminate.
    destruct (bool_decide (_ ## _)); last discriminate.
    intros [= <-]. simpl.
    exact (take_plain_step_preserves_in_atomic _ _ _ Hplain).
  - destruct (bool_decide (_ ⊆ _)); last discriminate.
    apply take_plain_step_preserves_in_atomic.
Qed.

Lemma take_step_preserves_wf cost state exit :
  state_wf state -> take_step cost state = inr exit -> state_wf exit.
Proof.
  intros Hwf Hstep. unfold take_step in Hstep.
  destruct cost; try (apply take_plain_step_preserves_sets in Hstep as
    [Hmask Hopen]; unfold state_wf in *; now rewrite Hmask, Hopen).
  - destruct (bool_decide (_ ⊆ _)) eqn:Hrequired; last discriminate.
    destruct (take_plain_step NonAtomicStep state) as [error|stepped]
      eqn:Hplain; first discriminate.
    destruct (bool_decide (_ ## _)) eqn:Hgrant; last discriminate.
    inversion Hstep; subst exit.
    apply bool_decide_eq_true in Hgrant.
    apply take_plain_step_preserves_sets in Hplain as [Hmask Hopen].
    assert (state_wf stepped) as Hwf_stepped.
    { unfold state_wf in Hwf |- *. now rewrite Hmask, Hopen. }
    unfold state_wf, grant_state in *. simpl in *.
    rewrite elem_of_disjoint in Hwf_stepped, Hgrant |- *.
    intros invariant Hinvariant Havailable.
    rewrite elem_of_union in Havailable. destruct Havailable as [Havailable|Hgranted].
    + exact (Hwf_stepped invariant Hinvariant Havailable).
    + exact (Hgrant invariant Hgranted Hinvariant).
  - destruct (bool_decide (_ ⊆ _)); last discriminate.
    apply take_plain_step_preserves_sets in Hstep as [Hmask Hopen].
    unfold state_wf in Hwf |- *. now rewrite Hmask, Hopen.
Qed.

Lemma procedure_call_step_success required granted state exit :
  take_step (ProcedureCallStep required granted) state = inr exit ->
  required ⊆ analysis_mask state /\
  granted ## analysis_open state /\
  analysis_mask exit = analysis_mask state ∪ granted /\
  analysis_open exit = analysis_open state.
Proof.
  unfold take_step.
  destruct (bool_decide (required ⊆ analysis_mask state)) eqn:Hrequired;
    last discriminate.
  apply bool_decide_eq_true in Hrequired.
  destruct (take_plain_step NonAtomicStep state) as [error|stepped]
    eqn:Hplain; first discriminate.
  destruct (bool_decide (granted ## analysis_open stepped)) eqn:Hgrant;
    last discriminate.
  apply bool_decide_eq_true in Hgrant. intros [= <-].
  apply take_plain_step_preserves_sets in Hplain as [Hmask Hopen].
  rewrite Hopen in Hgrant. simpl. repeat split; try assumption.
  - now rewrite Hmask.
Qed.

Lemma procedure_spawn_step_success required state exit :
  take_step (ProcedureSpawnStep required) state = inr exit ->
  required ⊆ analysis_mask state /\
  analysis_mask exit = analysis_mask state /\
  analysis_open exit = analysis_open state.
Proof.
  unfold take_step.
  destruct (bool_decide (required ⊆ analysis_mask state)) eqn:Hrequired;
    last discriminate.
  apply bool_decide_eq_true in Hrequired. intros Hplain.
  apply take_plain_step_preserves_sets in Hplain as [Hmask Hopen].
  tauto.
Qed.

Lemma atomic_step_preserves_sets state exit :
  take_step AtomicStep state = inr exit ->
  analysis_mask exit = analysis_mask state /\
  analysis_open exit = analysis_open state.
Proof. apply take_plain_step_preserves_sets. Qed.

Lemma take_step_resources_monotone cost state exit :
  take_step cost state = inr exit ->
  analysis_mask state ∪ analysis_open state ⊆
    analysis_mask exit ∪ analysis_open exit.
Proof.
  intros Hstep. destruct cost.
  - apply take_plain_step_preserves_sets in Hstep as [Hmask Hopen].
    now rewrite Hmask, Hopen.
  - apply take_plain_step_preserves_sets in Hstep as [Hmask Hopen].
    now rewrite Hmask, Hopen.
  - apply take_plain_step_preserves_sets in Hstep as [Hmask Hopen].
    now rewrite Hmask, Hopen.
  - apply procedure_call_step_success in Hstep as
      (_ & _ & Hmask & Hopen).
    intros invariant Hmember. rewrite elem_of_union in Hmember |- *.
    destruct Hmember as [Havailable|Hopened].
    + left. rewrite Hmask, elem_of_union. now left.
    + right. now rewrite Hopen.
  - apply procedure_spawn_step_success in Hstep as (_ & Hmask & Hopen).
    now rewrite Hmask, Hopen.
Qed.

Lemma take_plain_non_atomic_rejected state :
  analysis_open state ≠ ∅ -> analysis_in_atomic state = false ->
  take_plain_step NonAtomicStep state = inl NonAtomicWhileOpen.
Proof.
  intros Hopen Hin_atomic. unfold take_plain_step.
  rewrite Hin_atomic. simpl. rewrite bool_decide_false; [reflexivity|exact Hopen].
Qed.

Lemma procedure_call_rejected_while_open required granted state exit :
  analysis_open state ≠ ∅ -> analysis_in_atomic state = false ->
  take_step (ProcedureCallStep required granted) state <> inr exit.
Proof.
  intros Hopen Hin_atomic. unfold take_step.
  destruct (bool_decide (required ⊆ analysis_mask state)); last discriminate.
  rewrite (take_plain_non_atomic_rejected state Hopen Hin_atomic). discriminate.
Qed.

Lemma procedure_spawn_rejected_while_open required state exit :
  analysis_open state ≠ ∅ -> analysis_in_atomic state = false ->
  take_step (ProcedureSpawnStep required) state <> inr exit.
Proof.
  intros Hopen Hin_atomic. unfold take_step.
  destruct (bool_decide (required ⊆ analysis_mask state)); last discriminate.
  rewrite (take_plain_non_atomic_rejected state Hopen Hin_atomic). discriminate.
Qed.

Lemma fold_invariant_preserves_wf invariant state :
  state_wf state -> state_wf (fold_invariant invariant state).
Proof.
  intros Hwf. unfold fold_invariant, state_wf in *.
  destruct (bool_decide (invariant ∈ analysis_open state)) eqn:Hmember;
    cbn;
    rewrite elem_of_disjoint in Hwf |- *;
    intros other Hother_open Hother_mask;
    rewrite elem_of_union in Hother_mask;
    rewrite elem_of_singleton in Hother_mask.
  - rewrite elem_of_difference in Hother_open.
    rewrite elem_of_singleton in Hother_open.
    destruct Hother_mask as [->|Hother_mask].
    + destruct Hother_open as [_ Hneq]. exact (Hneq eq_refl).
    + destruct Hother_open as [Hother_open _].
      exact (Hwf other Hother_open Hother_mask).
  - apply bool_decide_eq_false in Hmember.
    destruct Hother_mask as [->|Hother_mask].
    + exact (Hmember Hother_open).
    + exact (Hwf other Hother_open Hother_mask).
Qed.

Lemma fold_open_invariant invariant state :
  invariant ∈ analysis_open state ->
  analysis_mask (fold_invariant invariant state) =
    {[invariant]} ∪ analysis_mask state /\
  analysis_open (fold_invariant invariant state) =
    analysis_open state ∖ {[invariant]}.
Proof.
  intros Hopen. unfold fold_invariant.
  rewrite bool_decide_true; first done. exact Hopen.
Qed.

Lemma fold_fresh_invariant invariant state :
  invariant ∉ analysis_open state ->
  analysis_mask (fold_invariant invariant state) =
    {[invariant]} ∪ analysis_mask state /\
  analysis_open (fold_invariant invariant state) = analysis_open state.
Proof.
  intros Hclosed. unfold fold_invariant.
  rewrite bool_decide_false; first done. exact Hclosed.
Qed.

Lemma open_invariant_not_available invariant state :
  state_wf state -> invariant ∈ analysis_open state ->
  invariant ∉ analysis_mask state.
Proof.
  unfold state_wf. rewrite elem_of_disjoint. intros Hwf Hopen Hmask.
  exact (Hwf invariant Hopen Hmask).
Qed.

Fixpoint analyze_fuel {Γ} (fuel : nat) (cost : cost_model)
    (state : analysis_state) (statement : Syntax.statement Γ) :
    analysis_error + analysis_state :=
  match fuel with
  | 0 => inl FuelExhausted
  | S fuel' =>
      match Syntax.view Γ statement with
      | ViewLeaf => take_step (cost Γ statement) state
      | ViewDone => inr state
      | ViewUnfold invariant => open_invariant invariant state
      | ViewFold invariant => inr (fold_invariant invariant state)
      | ViewSequence first second =>
          match analyze_fuel fuel' cost state first with
          | inl error => inl error
          | inr middle => analyze_fuel fuel' cost middle second
          end
      | ViewConditional then_branch else_branch =>
          match analyze_fuel fuel' cost state then_branch,
              analyze_fuel fuel' cost state else_branch with
          | inr then_state, inr else_state =>
              if bool_decide
                  (analysis_open then_state = analysis_open else_state /\
                   analysis_in_atomic then_state = analysis_in_atomic else_state)
              then inr (AnalysisState
                (analysis_mask then_state ∩ analysis_mask else_state)
                (analysis_open then_state)
                (analysis_step_taken then_state || analysis_step_taken else_state)
                (analysis_in_atomic then_state))
              else inl IncompatibleBranches
          | inl error, _ | _, inl error => inl error
          end
      | ViewStructuredAccess _ _ => inl StructuredAccessRequiresCertificate
      | ViewAtomic body =>
          match take_step AtomicStep state with
          | inl error => inl error
          | inr outer =>
              let inner_entry := AnalysisState (analysis_mask outer)
                (analysis_open outer) (analysis_step_taken outer) true in
              match analyze_fuel fuel' cost inner_entry body with
              | inl error => inl error
              | inr inner =>
                  if bool_decide (analysis_open inner = analysis_open outer)
                  then inr (AnalysisState (analysis_mask inner)
                    (analysis_open inner)
                    (analysis_step_taken outer || analysis_step_taken inner)
                    (analysis_in_atomic outer))
                  else inl AtomicBlockLeaksAccess
              end
          end
      end
  end.

Definition analyze {Γ} cost state (statement : Syntax.statement Γ) :=
  analyze_fuel (Syntax.size Γ statement) cost state statement.

(** Executable branch-coherence check layered over the existing flat
    analyzer.  It follows the same recursive states but additionally requires
    equal branch masks at every conditional.  Keeping this as a separate pass
    preserves the current Raven analysis result while making the baseline
    normalizer's stronger acceptance criterion explicit and computable. *)
Fixpoint check_conditional_masks_fuel {Γ} (fuel : nat) (cost : cost_model)
    (state : analysis_state) (statement : Syntax.statement Γ) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      match Syntax.view Γ statement with
      | ViewSequence first second =>
          match analyze_fuel fuel' cost state first with
          | inr middle =>
              check_conditional_masks_fuel fuel' cost state first &&
              check_conditional_masks_fuel fuel' cost middle second
          | inl _ => false
          end
      | ViewConditional then_branch else_branch =>
          match analyze_fuel fuel' cost state then_branch,
              analyze_fuel fuel' cost state else_branch with
          | inr then_exit, inr else_exit =>
              check_conditional_masks_fuel fuel' cost state then_branch &&
              check_conditional_masks_fuel fuel' cost state else_branch &&
              bool_decide (analysis_mask then_exit = analysis_mask else_exit)
          | _, _ => false
          end
      | ViewAtomic body =>
          match take_step AtomicStep state with
          | inr outer =>
              check_conditional_masks_fuel fuel' cost
                (AnalysisState (analysis_mask outer) (analysis_open outer)
                  (analysis_step_taken outer) true) body
          | inl _ => false
          end
      | ViewStructuredAccess _ _ => false
      | _ => true
      end
  end.

Definition check_conditional_masks {Γ} cost state
    (statement : Syntax.statement Γ) : bool :=
  check_conditional_masks_fuel (Syntax.size Γ statement) cost state statement.

Definition analyze_coherent {Γ} cost state
    (statement : Syntax.statement Γ) : analysis_error + analysis_state :=
  match analyze cost state statement with
  | inl error => inl error
  | inr exit =>
      if check_conditional_masks cost state statement
      then inr exit else inl IncoherentConditionalMasks
  end.

Lemma open_invariant_success invariant state exit :
  open_invariant invariant state = inr exit ->
  invariant ∉ analysis_open state /\
  invariant ∈ analysis_mask state /\
  analysis_mask exit = analysis_mask state ∖ {[invariant]} /\
  analysis_open exit = {[invariant]} ∪ analysis_open state.
Proof.
  unfold open_invariant.
  destruct (bool_decide (invariant ∈ analysis_open state)) eqn:Hopen;
    first discriminate.
  destruct (bool_decide (invariant ∈ analysis_mask state)) eqn:Hmask;
    last discriminate.
  intros Hinr. inversion Hinr; subst exit. repeat split; try reflexivity.
  - apply bool_decide_eq_false in Hopen. exact Hopen.
  - apply bool_decide_eq_true in Hmask. exact Hmask.
Qed.

Lemma open_invariant_preserves_in_atomic invariant state exit :
  open_invariant invariant state = inr exit ->
  analysis_in_atomic exit = analysis_in_atomic state.
Proof.
  unfold open_invariant.
  destruct (bool_decide (invariant ∈ analysis_open state)); try discriminate.
  destruct (bool_decide (invariant ∈ analysis_mask state)); try discriminate.
  intros Hinr. inversion Hinr. reflexivity.
Qed.

Lemma open_invariant_preserves_wf invariant state exit :
  state_wf state -> open_invariant invariant state = inr exit -> state_wf exit.
Proof.
  intros Hwf Hopen.
  apply open_invariant_success in Hopen as
    (Hnotopen & Havailable & Hmask & Hopened).
  unfold state_wf in *. rewrite Hmask. rewrite Hopened.
  rewrite elem_of_disjoint in Hwf |- *. intros other Hother_open Hother_mask.
  rewrite elem_of_union in Hother_open.
  rewrite elem_of_singleton in Hother_open.
  rewrite elem_of_difference in Hother_mask.
  rewrite elem_of_singleton in Hother_mask.
  destruct Hother_open as [->|Hother_open].
  - destruct Hother_mask as [_ Hneq]. exact (Hneq eq_refl).
  - destruct Hother_mask as [Hother_mask _].
    exact (Hwf other Hother_open Hother_mask).
Qed.

Inductive analysis_certificate (cost : cost_model) :
    forall Γ, analysis_state -> Syntax.statement Γ ->
      analysis_state -> Type :=
| CertLeaf Γ state statement exit :
    Syntax.view Γ statement = ViewLeaf ->
    take_step (cost Γ statement) state = inr exit ->
    analysis_certificate cost Γ state statement exit
| CertDone Γ state statement :
    Syntax.view Γ statement = ViewDone ->
    analysis_certificate cost Γ state statement state
| CertUnfold Γ state statement invariant exit :
    Syntax.view Γ statement = ViewUnfold invariant ->
    open_invariant invariant state = inr exit ->
    analysis_certificate cost Γ state statement exit
| CertFold Γ state statement invariant :
    Syntax.view Γ statement = ViewFold invariant ->
    analysis_certificate cost Γ state statement
      (fold_invariant invariant state)
| CertSequence Γ state statement first middle second exit :
    Syntax.view Γ statement = ViewSequence first second ->
    analysis_certificate cost Γ state first middle ->
    analysis_certificate cost Γ middle second exit ->
    analysis_certificate cost Γ state statement exit
| CertConditional Γ state statement then_branch else_branch
    then_exit else_exit :
    Syntax.view Γ statement = ViewConditional then_branch else_branch ->
    analysis_certificate cost Γ state then_branch then_exit ->
    analysis_certificate cost Γ state else_branch else_exit ->
    analysis_open then_exit = analysis_open else_exit ->
    analysis_in_atomic then_exit = analysis_in_atomic else_exit ->
    analysis_certificate cost Γ state statement
      (AnalysisState
        (analysis_mask then_exit ∩ analysis_mask else_exit)
        (analysis_open then_exit)
        (analysis_step_taken then_exit || analysis_step_taken else_exit)
        (analysis_in_atomic then_exit))
| CertAtomic Γ state statement body outer inner :
    Syntax.view Γ statement = ViewAtomic body ->
    take_step AtomicStep state = inr outer ->
    analysis_certificate cost Γ
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body inner ->
    analysis_open inner = analysis_open outer ->
    analysis_certificate cost Γ state statement
      (AnalysisState (analysis_mask inner) (analysis_open inner)
        (analysis_step_taken outer || analysis_step_taken inner)
        (analysis_in_atomic outer)).

Lemma analysis_certificate_preserves_in_atomic
    {cost Γ entry statement exit}
    (certificate : analysis_certificate cost Γ entry statement exit) :
  analysis_in_atomic exit = analysis_in_atomic entry.
Proof.
  induction certificate; simpl.
  - eapply take_step_preserves_in_atomic. exact e0.
  - reflexivity.
  - eapply open_invariant_preserves_in_atomic. exact e0.
  - unfold fold_invariant.
    destruct (bool_decide (invariant ∈ analysis_open state)); reflexivity.
  - etrans; eassumption.
  - exact IHcertificate1.
  - eapply take_step_preserves_in_atomic. exact e0.
Qed.

(** Certificate-level half of the conditional normalization spike.  An
    opening that preceded branch selection is duplicated into the selected
    branches.  Since both copies start in the same source state and only one
    branch executes, the conditional has exactly the original branch exits
    and join state. *)
Lemma certificate_push_unfold_into_conditional
    {Γ cost state unfold_statement invariant opened
      then_branch else_branch then_exit else_exit
      then_sequence else_sequence normalized_statement}
    (Hunfold_view : Syntax.view Γ unfold_statement = ViewUnfold invariant)
    (Hopen : open_invariant invariant state = inr opened)
    (Hthen : analysis_certificate cost Γ opened then_branch
      then_exit)
    (Helse : analysis_certificate cost Γ opened else_branch
      else_exit)
    (Hthen_sequence : Syntax.view Γ then_sequence =
      ViewSequence unfold_statement then_branch)
    (Helse_sequence : Syntax.view Γ else_sequence =
      ViewSequence unfold_statement else_branch)
    (Hnormalized : Syntax.view Γ normalized_statement =
      ViewConditional then_sequence else_sequence)
    (Hopen_equal : analysis_open then_exit = analysis_open else_exit)
    (Hatomic_equal : analysis_in_atomic then_exit =
      analysis_in_atomic else_exit) :
  analysis_certificate cost Γ state normalized_statement
    (AnalysisState
      (analysis_mask then_exit ∩ analysis_mask else_exit)
      (analysis_open then_exit)
      (analysis_step_taken then_exit || analysis_step_taken else_exit)
      (analysis_in_atomic then_exit)).
Proof.
  eapply CertConditional; [exact Hnormalized| | |exact Hopen_equal|exact Hatomic_equal].
  - eapply CertSequence; [exact Hthen_sequence| |exact Hthen].
    eapply CertUnfold; eauto.
  - eapply CertSequence; [exact Helse_sequence| |exact Helse].
    eapply CertUnfold; eauto.
Qed.

Definition statement_certificate {Γ} cost state
    (statement : Syntax.statement Γ) exit :=
  analysis_certificate cost Γ state statement exit.

(** Compositional builders for full statement certificates. *)
Definition statement_certificate_sequence
    {Γ cost state statement first middle second exit}
    (view : Syntax.view Γ statement = ViewSequence first second)
    (first_certificate : statement_certificate cost state first middle)
    (second_certificate : statement_certificate cost middle second exit) :
  statement_certificate cost state statement exit.
Proof.
  eapply CertSequence; eauto.
Defined.

Definition statement_certificate_conditional
    {Γ cost state statement then_branch else_branch then_exit else_exit}
    (view : Syntax.view Γ statement =
      ViewConditional then_branch else_branch)
    (then_certificate : statement_certificate cost state then_branch then_exit)
    (else_certificate : statement_certificate cost state else_branch else_exit)
    (Hopen : analysis_open then_exit = analysis_open else_exit)
    (Hatomic : analysis_in_atomic then_exit = analysis_in_atomic else_exit) :
  statement_certificate cost state statement
    (AnalysisState
      (analysis_mask then_exit ∩ analysis_mask else_exit)
      (analysis_open then_exit)
      (analysis_step_taken then_exit || analysis_step_taken else_exit)
      (analysis_in_atomic then_exit)).
Proof.
  eapply CertConditional; eauto.
Defined.

Definition statement_certificate_atomic
    {Γ cost state statement body outer inner}
    (view : Syntax.view Γ statement = ViewAtomic body)
    (Hstep : take_step AtomicStep state = inr outer)
    (body_certificate : statement_certificate cost
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body inner)
    (Hopen : analysis_open inner = analysis_open outer) :
  statement_certificate cost state statement
    (AnalysisState
      (analysis_mask inner) (analysis_open inner)
      (analysis_step_taken outer || analysis_step_taken inner)
      (analysis_in_atomic outer)).
Proof.
  eapply CertAtomic; eauto.
Defined.

(** A successful run packages its exit state behind a dependent pair.  This
    is the preferred interface for assembling large example certificates:
    intermediate states remain named by projections instead of being
    duplicated as expanded record expressions. *)
Definition certified_run {Γ} (cost : cost_model) (entry : analysis_state)
    (statement : Syntax.statement Γ) : Type :=
  { exit : analysis_state &
    statement_certificate cost entry statement exit }.

Definition certified_run_sequence
    {Γ cost entry statement first second}
    (view : Syntax.view Γ statement = ViewSequence first second)
    (first_run : certified_run cost entry first)
    (second_run : certified_run cost (projT1 first_run) second) :
  certified_run cost entry statement.
Proof.
  destruct first_run as [middle first_certificate].
  destruct second_run as [exit second_certificate].
  exists exit.
  exact (statement_certificate_sequence view first_certificate
    second_certificate).
Defined.

Definition certified_run_conditional
    {Γ cost entry statement then_branch else_branch}
    (view : Syntax.view Γ statement =
      ViewConditional then_branch else_branch)
    (then_run : certified_run cost entry then_branch)
    (else_run : certified_run cost entry else_branch)
    (Hopen : analysis_open (projT1 then_run) =
      analysis_open (projT1 else_run))
    (Hatomic : analysis_in_atomic (projT1 then_run) =
      analysis_in_atomic (projT1 else_run)) :
  certified_run cost entry statement.
Proof.
  destruct then_run as [then_exit then_certificate].
  destruct else_run as [else_exit else_certificate].
  exists (AnalysisState
    (analysis_mask then_exit ∩ analysis_mask else_exit)
    (analysis_open then_exit)
    (analysis_step_taken then_exit || analysis_step_taken else_exit)
    (analysis_in_atomic then_exit)).
  exact (statement_certificate_conditional view then_certificate
    else_certificate Hopen Hatomic).
Defined.

Definition certified_run_atomic
    {Γ cost entry statement body outer}
    (view : Syntax.view Γ statement = ViewAtomic body)
    (Hstep : take_step AtomicStep entry = inr outer)
    (body_run : certified_run cost
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body)
    (Hopen : analysis_open (projT1 body_run) = analysis_open outer) :
  certified_run cost entry statement.
Proof.
  destruct body_run as [inner body_certificate].
  exists (AnalysisState
    (analysis_mask inner) (analysis_open inner)
    (analysis_step_taken outer || analysis_step_taken inner)
    (analysis_in_atomic outer)).
  exact (statement_certificate_atomic view Hstep body_certificate Hopen).
Defined.

Definition access_marker : Type := (inv_id * gset inv_id)%type.

(** Temporary semantic restriction used by the Iris accessor proof.  The
    executable flat analysis deliberately records open declarations as a set,
    matching Raven's unordered source analysis.  This additional certificate
    witnesses that one particular successful run is nevertheless properly
    nested, without baking that restriction into the source language or the
    analyzer result. *)
Fixpoint lifo_certificate {Γ entry statement exit} {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit)
    (stack_in stack_out : list access_marker) : Prop :=
  match certificate with
  | CertLeaf _ _ _ _ _ _ _ => stack_out = stack_in
  | CertDone _ _ _ _ _ => stack_out = stack_in
  | CertUnfold _ _ _ _ invariant _ _ _ =>
      stack_out = (invariant, analysis_open entry) :: stack_in
  | CertFold _ _ state _ invariant _ =>
      (exists outer_open,
       stack_in = (invariant, outer_open) :: stack_out /\
       invariant ∈ analysis_open state /\
       invariant ∉ outer_open /\
       analysis_open state = {[invariant]} ∪ outer_open) \/
      (stack_out = stack_in /\ invariant ∉ analysis_open state)
  | CertSequence _ _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      exists stack_middle,
        lifo_certificate first_certificate stack_in stack_middle /\
        lifo_certificate second_certificate stack_middle stack_out
  | CertConditional _ _ _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      lifo_certificate then_certificate stack_in stack_out /\
      lifo_certificate else_certificate stack_in stack_out
  | CertAtomic _ _ _ _ _ _ _ _ _ body_certificate _ =>
      lifo_certificate body_certificate stack_in stack_in /\
      stack_out = stack_in
  end.

(** Executable replay of the auxiliary access stack.  This is certification
    of an already-produced analysis certificate, not another statement
    analysis: every branch follows the certificate's constructors and merely
    checks the equalities and membership facts occurring in
    [lifo_certificate]. *)
Fixpoint replay_lifo_certificate {Γ entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit)
    (stack_in : list access_marker) : option (list access_marker) :=
  match certificate with
  | CertLeaf _ _ _ _ _ _ _ => Some stack_in
  | CertDone _ _ _ _ _ => Some stack_in
  | CertUnfold _ _ _ _ invariant _ _ _ =>
      Some ((invariant, analysis_open entry) :: stack_in)
  | CertFold _ _ state _ invariant _ =>
      match stack_in with
      | (candidate, outer_open) :: stack_out =>
          if decide (candidate = invariant /\
              invariant ∈ analysis_open state /\
              invariant ∉ outer_open /\
              analysis_open state = {[invariant]} ∪ outer_open)
          then Some stack_out
          else if decide (invariant ∉ analysis_open state)
            then Some stack_in else None
      | [] =>
          if decide (invariant ∉ analysis_open state)
          then Some [] else None
      end
  | CertSequence _ _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      match replay_lifo_certificate first_certificate stack_in with
      | Some stack_middle => replay_lifo_certificate second_certificate stack_middle
      | None => None
      end
  | CertConditional _ _ _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      match replay_lifo_certificate then_certificate stack_in,
          replay_lifo_certificate else_certificate stack_in with
      | Some then_stack, Some else_stack =>
          if decide (then_stack = else_stack) then Some then_stack else None
      | _, _ => None
      end
  | CertAtomic _ _ _ _ _ _ _ _ _ body_certificate _ =>
      match replay_lifo_certificate body_certificate stack_in with
      | Some body_stack =>
          if decide (body_stack = stack_in) then Some stack_in else None
      | None => None
      end
  end.

Lemma replay_lifo_certificate_sound {Γ entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit)
    stack_in stack_out :
  replay_lifo_certificate certificate stack_in = Some stack_out ->
  lifo_certificate certificate stack_in stack_out.
Proof.
  revert stack_in stack_out.
  induction certificate; intros stack_in stack_out Hreplay; simpl in *.
  - inversion Hreplay. reflexivity.
  - inversion Hreplay. reflexivity.
  - inversion Hreplay. reflexivity.
  - destruct stack_in as [|[candidate outer_open] rest].
    + destruct (decide (invariant ∉ analysis_open state)); inversion Hreplay;
        subst. right. split; [reflexivity|assumption].
    + destruct (decide (candidate = invariant /\
          invariant ∈ analysis_open state /\ invariant ∉ outer_open /\
          analysis_open state = {[invariant]} ∪ outer_open)) as [Hclose|Hclose].
      * inversion Hreplay; subst. left. destruct Hclose as
          [-> [Hmember [Hfresh Hopen]]].
        exists outer_open. repeat split; assumption.
      * destruct (decide (invariant ∉ analysis_open state)); inversion Hreplay;
          subst. right. split; [reflexivity|assumption].
  - destruct (replay_lifo_certificate certificate1 stack_in) as
      [stack_middle|] eqn:Hfirst; try discriminate.
    exists stack_middle. split.
    + apply IHcertificate1. exact Hfirst.
    + apply IHcertificate2. exact Hreplay.
  - destruct (replay_lifo_certificate certificate1 stack_in) as
      [then_stack|] eqn:Hthen; try discriminate.
    destruct (replay_lifo_certificate certificate2 stack_in) as
      [else_stack|] eqn:Helse; try discriminate.
    destruct (decide (then_stack = else_stack)) as [->|Hdifferent];
      inversion Hreplay; subst.
    split; [apply IHcertificate1|apply IHcertificate2]; assumption.
  - destruct (replay_lifo_certificate certificate stack_in) as
      [body_stack|] eqn:Hbody; try discriminate.
    destruct (decide (body_stack = stack_in)) as [->|Hdifferent];
      inversion Hreplay; subst.
    split; [apply IHcertificate; assumption|reflexivity].
Qed.

(** A fused, certificate-free executable pass.  Unlike
    [replay_lifo_certificate], this pass follows the syntax directly while
    carrying both the analyzer state and the access stack.  Consequently its
    computation never unfolds the proof term returned by
    [analyze_builds_certificate].  Successful conditional nodes additionally
    retain equal masks, so the result subsumes [analyze_coherent]. *)
Fixpoint analyze_coherent_lifo_fuel {Γ} (fuel : nat) (cost : cost_model)
    (state : analysis_state) (stack : list access_marker)
    (statement : Syntax.statement Γ) :
    option (analysis_state * list access_marker) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match Syntax.view Γ statement with
      | ViewLeaf =>
          match take_step (cost Γ statement) state with
          | inl _ => None
          | inr exit => Some (exit, stack)
          end
      | ViewDone => Some (state, stack)
      | ViewUnfold invariant =>
          match open_invariant invariant state with
          | inl _ => None
          | inr exit => Some (exit, (invariant, analysis_open state) :: stack)
          end
      | ViewFold invariant =>
          let exit := fold_invariant invariant state in
          match stack with
          | (candidate, outer_open) :: stack_out =>
              if decide (candidate = invariant /\
                  invariant ∈ analysis_open state /\
                  invariant ∉ outer_open /\
                  analysis_open state = {[invariant]} ∪ outer_open)
              then Some (exit, stack_out)
              else if decide (invariant ∉ analysis_open state)
                then Some (exit, stack) else None
          | [] =>
              if decide (invariant ∉ analysis_open state)
              then Some (exit, []) else None
          end
      | ViewSequence first second =>
          match analyze_coherent_lifo_fuel fuel' cost state stack first with
          | Some (middle, stack_middle) =>
              analyze_coherent_lifo_fuel fuel' cost middle stack_middle second
          | None => None
          end
      | ViewConditional then_branch else_branch =>
          match analyze_coherent_lifo_fuel fuel' cost state stack then_branch,
              analyze_coherent_lifo_fuel fuel' cost state stack else_branch with
          | Some (then_exit, then_stack), Some (else_exit, else_stack) =>
              if decide
                  (analysis_open then_exit = analysis_open else_exit /\
                   analysis_in_atomic then_exit = analysis_in_atomic else_exit /\
                   analysis_mask then_exit = analysis_mask else_exit /\
                   then_stack = else_stack)
              then Some (AnalysisState
                (analysis_mask then_exit ∩ analysis_mask else_exit)
                (analysis_open then_exit)
                (analysis_step_taken then_exit || analysis_step_taken else_exit)
                (analysis_in_atomic then_exit), then_stack)
              else None
          | _, _ => None
          end
      | ViewStructuredAccess _ _ => None
      | ViewAtomic body =>
          match take_step AtomicStep state with
          | inl _ => None
          | inr outer =>
              let inner_entry := AnalysisState (analysis_mask outer)
                (analysis_open outer) (analysis_step_taken outer) true in
              match analyze_coherent_lifo_fuel fuel' cost inner_entry stack body with
              | Some (inner, body_stack) =>
                  if decide (analysis_open inner = analysis_open outer /\
                    body_stack = stack)
                  then Some (AnalysisState (analysis_mask inner)
                    (analysis_open inner)
                    (analysis_step_taken outer || analysis_step_taken inner)
                    (analysis_in_atomic outer), stack)
                  else None
              | None => None
              end
          end
      end
  end.

Definition analyze_coherent_lifo {Γ} (cost : cost_model)
    (state : analysis_state) (statement : Syntax.statement Γ) :
    option analysis_state :=
  match analyze_coherent_lifo_fuel (Syntax.size Γ statement) cost state []
      statement with
  | Some (exit, []) => Some exit
  | _ => None
  end.

Lemma analyze_coherent_lifo_fuel_projects {Γ} fuel (cost : cost_model)
    (state : analysis_state) (stack : list access_marker)
    (statement : Syntax.statement Γ) exit stack_out :
  analyze_coherent_lifo_fuel fuel cost state stack statement =
    Some (exit, stack_out) ->
  analyze_fuel fuel cost state statement = inr exit.
Proof.
  revert Γ state stack statement exit stack_out.
  induction fuel as [|fuel IH];
    intros Γ state stack statement exit stack_out Hrun; simpl in Hrun;
    first discriminate.
  destruct (Syntax.view Γ statement) eqn:Hview; simpl in Hrun.
  - destruct (take_step (cost Γ statement) state) as [error|actual]
      eqn:Hstep; try discriminate.
    inversion Hrun; subst. simpl. rewrite Hview. exact Hstep.
  - inversion Hrun; subst. simpl. rewrite Hview. reflexivity.
  - destruct (open_invariant invariant state) as [error|actual]
      eqn:Hstep; try discriminate.
    inversion Hrun; subst. simpl. rewrite Hview. exact Hstep.
  - destruct stack as [|[candidate outer_open] stack_out']; simpl in Hrun.
    + destruct (decide (invariant ∉ analysis_open state)); try discriminate.
      inversion Hrun; subst. simpl. rewrite Hview. reflexivity.
    + destruct (decide (candidate = invariant /\
          invariant ∈ analysis_open state /\ invariant ∉ outer_open /\
          analysis_open state = {[invariant]} ∪ outer_open));
        try destruct (decide (invariant ∉ analysis_open state));
        try discriminate;
        inversion Hrun; subst; simpl; rewrite Hview; reflexivity.
  - destruct (analyze_coherent_lifo_fuel fuel cost state stack first) as
      [[middle stack_middle]|] eqn:Hfirst; try discriminate.
    specialize (IH _ state stack first middle stack_middle Hfirst) as Hfirst'.
    specialize (IH _ middle stack_middle second exit stack_out Hrun) as Hsecond'.
    simpl. rewrite Hview, Hfirst'. exact Hsecond'.
  - destruct (analyze_coherent_lifo_fuel fuel cost state stack then_branch) as
      [[then_exit then_stack]|] eqn:Hthen; try discriminate.
    destruct (analyze_coherent_lifo_fuel fuel cost state stack else_branch) as
      [[else_exit else_stack]|] eqn:Helse; try discriminate.
    destruct (decide
      (analysis_open then_exit = analysis_open else_exit /\
       analysis_in_atomic then_exit = analysis_in_atomic else_exit /\
       analysis_mask then_exit = analysis_mask else_exit /\
       then_stack = else_stack)) as [Hjoin|Hjoin]; try discriminate.
    inversion Hrun; subst exit stack_out.
    specialize (IH _ state stack then_branch then_exit then_stack Hthen)
      as Hthen'.
    specialize (IH _ state stack else_branch else_exit else_stack Helse)
      as Helse'.
    destruct Hjoin as [Hopen [Hatomic _]].
    simpl. rewrite Hview, Hthen', Helse'.
    rewrite bool_decide_true; [reflexivity|]. exact (conj Hopen Hatomic).
  - discriminate.
  - destruct (take_step AtomicStep state) as [error|outer]
      eqn:Hstep; try discriminate.
    destruct (analyze_coherent_lifo_fuel fuel cost
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) stack body) as
      [[inner body_stack]|] eqn:Hbody; try discriminate.
    destruct (decide (analysis_open inner = analysis_open outer /\
      body_stack = stack)) as [Hclose|Hclose]; try discriminate.
    inversion Hrun; subst exit stack_out.
    specialize (IH _ _ stack body inner body_stack Hbody) as Hbody'.
    destruct Hclose as [Hopen _].
    simpl. rewrite Hview, Hstep, Hbody'.
    rewrite bool_decide_true; [reflexivity|exact Hopen].
Qed.

Lemma analyze_coherent_lifo_fuel_conditional_masks {Γ} fuel
    (cost : cost_model) (state : analysis_state)
    (stack : list access_marker) (statement : Syntax.statement Γ)
    exit stack_out :
  analyze_coherent_lifo_fuel fuel cost state stack statement =
    Some (exit, stack_out) ->
  check_conditional_masks_fuel fuel cost state statement = true.
Proof.
  revert Γ state stack statement exit stack_out.
  induction fuel as [|fuel IH];
    intros Γ state stack statement exit stack_out Hrun; simpl in Hrun;
    first discriminate.
  destruct (Syntax.view Γ statement) eqn:Hview; simpl.
  - rewrite Hview. reflexivity.
  - rewrite Hview. reflexivity.
  - rewrite Hview. reflexivity.
  - rewrite Hview. reflexivity.
  - simpl in Hrun.
    destruct (analyze_coherent_lifo_fuel fuel cost state stack first) as
      [[middle stack_middle]|] eqn:Hfirst; try discriminate.
    pose proof (IH _ state stack first middle stack_middle Hfirst) as Hfirst'.
    pose proof (IH _ middle stack_middle second exit stack_out Hrun)
      as Hsecond'.
    pose proof (analyze_coherent_lifo_fuel_projects _ cost state stack first
      middle stack_middle Hfirst) as Hfirst_run.
    rewrite Hview, Hfirst_run, Hfirst', Hsecond'. reflexivity.
  - simpl in Hrun.
    destruct (analyze_coherent_lifo_fuel fuel cost state stack then_branch) as
      [[then_exit then_stack]|] eqn:Hthen; try discriminate.
    destruct (analyze_coherent_lifo_fuel fuel cost state stack else_branch) as
      [[else_exit else_stack]|] eqn:Helse; try discriminate.
    destruct (decide
      (analysis_open then_exit = analysis_open else_exit /\
       analysis_in_atomic then_exit = analysis_in_atomic else_exit /\
       analysis_mask then_exit = analysis_mask else_exit /\
       then_stack = else_stack)) as [Hjoin|Hjoin]; try discriminate.
    pose proof (IH _ state stack then_branch then_exit then_stack Hthen)
      as Hthen'.
    pose proof (IH _ state stack else_branch else_exit else_stack Helse)
      as Helse'.
    pose proof (analyze_coherent_lifo_fuel_projects _ cost state stack
      then_branch then_exit then_stack Hthen) as Hthen_run.
    pose proof (analyze_coherent_lifo_fuel_projects _ cost state stack
      else_branch else_exit else_stack Helse) as Helse_run.
    destruct Hjoin as [_ [_ [Hmasks _]]].
    rewrite Hview, Hthen_run, Helse_run, Hthen', Helse'.
    rewrite bool_decide_true; [reflexivity|exact Hmasks].
  - discriminate.
  - simpl in Hrun.
    destruct (take_step AtomicStep state) as [error|outer]
      eqn:Hstep; try discriminate.
    destruct (analyze_coherent_lifo_fuel fuel cost
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) stack body) as
      [[inner body_stack]|] eqn:Hbody; try discriminate.
    destruct (decide (analysis_open inner = analysis_open outer /\
      body_stack = stack)) as [Hclose|Hclose]; try discriminate.
    pose proof (IH _ _ stack body inner body_stack Hbody) as Hbody'.
    rewrite Hview, Hbody'. reflexivity.
Qed.

Lemma analyze_coherent_lifo_projects {Γ} (cost : cost_model)
    (state : analysis_state) (statement : Syntax.statement Γ) exit :
  analyze_coherent_lifo cost state statement = Some exit ->
  analyze_coherent cost state statement = inr exit.
Proof.
  unfold analyze_coherent_lifo.
  destruct (analyze_coherent_lifo_fuel (Syntax.size Γ statement) cost state []
    statement) as [[actual stack_out]|] eqn:Hrun; try discriminate.
  destruct stack_out as [|marker stack_out]; try discriminate.
  intros Hsuccess. inversion Hsuccess; subst actual.
  unfold analyze_coherent, analyze.
  rewrite (analyze_coherent_lifo_fuel_projects _ cost state [] statement
    exit [] Hrun).
  unfold check_conditional_masks.
  rewrite (analyze_coherent_lifo_fuel_conditional_masks _ cost state []
    statement exit [] Hrun).
  reflexivity.
Qed.

(** Branch coherence required by the first certified normalizer.  The flat
    analyzer deliberately computes the intersection of branch masks; this
    additional success evidence records when that conservative join loses no
    branch-local invariant allocation.  Keeping it separate from
    [analysis_certificate] preserves the current executable analysis while
    allowing a future per-instance mask analysis to refine the compared key. *)
Fixpoint conditional_masks_coherent {Γ entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit) :
    Prop :=
  match certificate with
  | CertSequence _ _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      conditional_masks_coherent first_certificate /\
      conditional_masks_coherent second_certificate
  | CertConditional _ _ _ _ _ _ then_exit else_exit _
      then_certificate else_certificate _ _ =>
      analysis_mask then_exit = analysis_mask else_exit /\
      conditional_masks_coherent then_certificate /\
      conditional_masks_coherent else_certificate
  | CertAtomic _ _ _ _ _ _ _ _ _ body_certificate _ =>
      conditional_masks_coherent body_certificate
  | _ => True
  end.

Lemma conditional_masks_coherent_sequence {Γ entry statement first middle
    second exit cost}
    (view : Syntax.view Γ statement = ViewSequence first second)
    (first_certificate : analysis_certificate cost Γ entry first middle)
    (second_certificate : analysis_certificate cost Γ middle second exit) :
  conditional_masks_coherent
      (CertSequence cost Γ entry statement first middle second exit view
        first_certificate second_certificate) ->
  conditional_masks_coherent first_certificate /\
  conditional_masks_coherent second_certificate.
Proof. exact (fun H => H). Qed.

Lemma conditional_masks_coherent_conditional {Γ entry statement
    then_branch else_branch then_exit else_exit cost}
    (view : Syntax.view Γ statement =
      ViewConditional then_branch else_branch)
    (then_certificate : analysis_certificate cost Γ entry then_branch
      then_exit)
    (else_certificate : analysis_certificate cost Γ entry else_branch
      else_exit)
    (Hopen : analysis_open then_exit = analysis_open else_exit)
    (Hatomic : analysis_in_atomic then_exit = analysis_in_atomic else_exit) :
  conditional_masks_coherent
      (CertConditional cost Γ entry statement then_branch else_branch
        then_exit else_exit view then_certificate else_certificate Hopen
        Hatomic) ->
  analysis_mask then_exit = analysis_mask else_exit /\
  conditional_masks_coherent then_certificate /\
  conditional_masks_coherent else_certificate.
Proof. exact (fun H => H). Qed.

(** Enriched control-flow result exported by the baseline analyzer.  It
    projects definitionally to the existing flat certificate, so all current
    LIFO and replay theorems remain reusable.  Later enrichment with
    per-instance keys is orthogonal to this branch-coherence component. *)
Record coherent_analysis_certificate {Γ entry statement exit}
    (cost : cost_model) : Type := {
  coherent_flat_certificate :
    analysis_certificate cost Γ entry statement exit;
  coherent_conditional_masks :
    conditional_masks_coherent coherent_flat_certificate;
}.

Definition coherent_statement_certificate {Γ} cost entry
    (statement : Syntax.statement Γ) exit : Type :=
  @coherent_analysis_certificate Γ entry statement exit cost.

Definition coherent_analysis_lifo {Γ entry statement exit cost}
    (certificate : @coherent_analysis_certificate Γ entry statement exit
      cost) stack_in stack_out : Prop :=
  lifo_certificate (coherent_flat_certificate cost certificate)
    stack_in stack_out.

(** [lifo_certificate] is deterministic: for one fixed certificate and input
    stack, the execution it describes has exactly one output stack, not
    several -- [unfold] pushes one prescribed marker, [leaf]/[atomic]
    preserve the stack, [sequence] composes deterministic transitions, and
    [fold]'s two alternatives are separated by whether the invariant belongs
    to the fixed entry open set (mutually exclusive, so at most one can
    hold).  Reconciles independently obtained LIFO witnesses for the same
    certificate/input (e.g. two [aligned_operational_suffix] normalizations
    of the same branch) without re-deriving the underlying access-stack
    discipline from scratch. *)
Lemma lifo_certificate_functional {Γ entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit)
    stack_in stack_out1 stack_out2 :
  lifo_certificate certificate stack_in stack_out1 ->
  lifo_certificate certificate stack_in stack_out2 ->
  stack_out1 = stack_out2.
Proof.
  revert stack_in stack_out1 stack_out2.
  induction certificate; simpl; intros stack_in stack_out1 stack_out2 H1 H2.
  - congruence.
  - congruence.
  - congruence.
  - destruct H1 as [(o1 & Hin1 & Hmem1 & Hnm1 & Ho1) | (Heq1 & Hnm1)];
      destruct H2 as [(o2 & Hin2 & Hmem2 & Hnm2 & Ho2) | (Heq2 & Hnm2)].
    + pose proof (eq_trans (eq_sym Hin1) Hin2) as Heq.
      injection Heq as _ Heq_out. exact Heq_out.
    + exfalso. exact (Hnm2 Hmem1).
    + exfalso. exact (Hnm1 Hmem2).
    + congruence.
  - destruct H1 as (mid1 & Hfirst1 & Hsecond1).
    destruct H2 as (mid2 & Hfirst2 & Hsecond2).
    assert (mid1 = mid2) as Hmid by eauto.
    subst mid2. eauto.
  - destruct H1 as [Hthen1 _]. destruct H2 as [Hthen2 _]. eauto.
  - destruct H1 as [_ Heq1]. destruct H2 as [_ Heq2]. congruence.
Qed.

(** The concrete access-stack discipline underlying [lifo_certificate].
    Every marker remembers the complete open set immediately before its
    invariant was opened; hence the tail of the stack determines that set. *)
Fixpoint access_stack_consistent
    (open : gset inv_id) (stack : list access_marker) : Prop :=
  match stack with
  | [] => open = ∅
  | (invariant, outer_open) :: rest =>
      invariant ∉ outer_open /\
      open = {[invariant]} ∪ outer_open /\
      access_stack_consistent outer_open rest
  end.

(** An access segment is deliberately allowed to have different input and
    output stacks.  This is what lets a sequence join an [unfold] in one
    child to its matching [fold] in a later child. *)
Record access_segment {Γ entry statement exit cost}
    (certificate : analysis_certificate cost Γ entry statement exit)
    (stack_in stack_out : list access_marker) : Prop := {
  access_segment_lifo : lifo_certificate certificate stack_in stack_out;
  access_segment_entry_consistent :
    access_stack_consistent (analysis_open entry) stack_in;
}.

Definition balanced_access_segment {Γ entry statement exit cost}
    (certificate : analysis_certificate cost Γ entry statement exit)
    (stack : list access_marker) : Prop :=
  access_segment certificate stack stack.

Lemma access_stack_consistent_empty open :
  access_stack_consistent open [] <-> open = ∅.
Proof. reflexivity. Qed.

Lemma access_stack_consistent_cons invariant outer_open rest :
  access_stack_consistent ({[invariant]} ∪ outer_open)
    ((invariant, outer_open) :: rest) <->
  invariant ∉ outer_open /\ access_stack_consistent outer_open rest.
Proof. simpl. tauto. Qed.

(** A concrete access stack determines the open-invariant set uniquely. *)
Lemma access_stack_consistent_functional open1 open2 stack :
  access_stack_consistent open1 stack ->
  access_stack_consistent open2 stack ->
  open1 = open2.
Proof.
  destruct stack as [|[invariant outer_open] rest]; simpl.
  - intros -> ->. reflexivity.
  - intros [_ [-> _]] [_ [-> _]]. reflexivity.
Qed.

Definition well_bracketed_certificate {Γ entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit) : Prop :=
  lifo_certificate certificate [] [].

(** Logical Raven masks that may be available anywhere in a certified
    region.  The semantic translation uses this union to choose one ambient
    Iris mask; individual Raven mask transitions do not themselves enlarge
    or shrink that ambient mask. *)
Fixpoint certificate_footprint {Γ entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit) :
    gset inv_id :=
  analysis_mask entry ∪ analysis_open entry ∪
  analysis_mask exit ∪ analysis_open exit ∪
  match certificate with
  | CertSequence _ _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      certificate_footprint first_certificate ∪
      certificate_footprint second_certificate
  | CertConditional _ _ _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      certificate_footprint then_certificate ∪
      certificate_footprint else_certificate
  | CertAtomic _ _ _ _ _ _ _ _ _ body_certificate _ =>
      certificate_footprint body_certificate
  | _ => ∅
  end.

(** The operational footprint is the set of invariant identifiers at which
    the certificate actually performs an invariant operation.  In
    particular, masks and open sets in the analysis states are deliberately
    not included: they describe availability, rather than physical access.
    Sequence and conditional nodes expose both children, while an atomic
    node exposes its body certificate. *)
Fixpoint certificate_operational_footprint {Γ entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit) :
    gset inv_id :=
  match certificate with
  | CertUnfold _ _ _ _ invariant _ _ _ => {[invariant]}
  | CertFold _ _ _ _ invariant _ => {[invariant]}
  | CertSequence _ _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      certificate_operational_footprint first_certificate ∪
      certificate_operational_footprint second_certificate
  | CertConditional _ _ _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      certificate_operational_footprint then_certificate ∪
      certificate_operational_footprint else_certificate
  | CertAtomic _ _ _ _ _ _ _ _ _ body_certificate _ =>
      certificate_operational_footprint body_certificate
  | _ => ∅
  end.

Lemma certificate_sequence_first_operational_footprint_subset
    {Γ entry statement first middle second exit cost}
    (view : Syntax.view Γ statement = ViewSequence first second)
    (first_certificate : analysis_certificate cost Γ entry first middle)
    (second_certificate : analysis_certificate cost Γ middle second exit) :
  certificate_operational_footprint first_certificate ⊆
    certificate_operational_footprint
      (CertSequence cost Γ entry statement first middle second exit
        view first_certificate second_certificate).
Proof. simpl. set_solver. Qed.

Lemma certificate_sequence_second_operational_footprint_subset
    {Γ entry statement first middle second exit cost}
    (view : Syntax.view Γ statement = ViewSequence first second)
    (first_certificate : analysis_certificate cost Γ entry first middle)
    (second_certificate : analysis_certificate cost Γ middle second exit) :
  certificate_operational_footprint second_certificate ⊆
    certificate_operational_footprint
      (CertSequence cost Γ entry statement first middle second exit
        view first_certificate second_certificate).
Proof. simpl. set_solver. Qed.

Lemma certificate_conditional_then_operational_footprint_subset
    {Γ entry statement then_branch else_branch then_exit else_exit cost}
    (view : Syntax.view Γ statement = ViewConditional then_branch else_branch)
    (then_certificate : analysis_certificate cost Γ entry then_branch then_exit)
    (else_certificate : analysis_certificate cost Γ entry else_branch else_exit)
    (open_equal : analysis_open then_exit = analysis_open else_exit)
    (atomic_equal : analysis_in_atomic then_exit = analysis_in_atomic else_exit) :
  certificate_operational_footprint then_certificate ⊆
    certificate_operational_footprint
      (CertConditional cost Γ entry statement then_branch else_branch
        then_exit else_exit view then_certificate else_certificate
        open_equal atomic_equal).
Proof. simpl. set_solver. Qed.

Lemma certificate_conditional_else_operational_footprint_subset
    {Γ entry statement then_branch else_branch then_exit else_exit cost}
    (view : Syntax.view Γ statement = ViewConditional then_branch else_branch)
    (then_certificate : analysis_certificate cost Γ entry then_branch then_exit)
    (else_certificate : analysis_certificate cost Γ entry else_branch else_exit)
    (open_equal : analysis_open then_exit = analysis_open else_exit)
    (atomic_equal : analysis_in_atomic then_exit = analysis_in_atomic else_exit) :
  certificate_operational_footprint else_certificate ⊆
    certificate_operational_footprint
      (CertConditional cost Γ entry statement then_branch else_branch
        then_exit else_exit view then_certificate else_certificate
        open_equal atomic_equal).
Proof. simpl. set_solver. Qed.

Lemma certificate_atomic_body_operational_footprint_subset
    {Γ entry statement body outer inner cost}
    (view : Syntax.view Γ statement = ViewAtomic body)
    (step : take_step AtomicStep entry = inr outer)
    (body_certificate : analysis_certificate cost Γ
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body inner)
    (open_equal : analysis_open inner = analysis_open outer) :
  certificate_operational_footprint body_certificate ⊆
    certificate_operational_footprint
      (CertAtomic cost Γ entry statement body outer inner view step
        body_certificate open_equal).
Proof. simpl. set_solver. Qed.

Lemma certificate_unfold_operational_footprint_mem
    {Γ entry statement invariant exit cost}
    (view : Syntax.view Γ statement = ViewUnfold invariant)
    (step : open_invariant invariant entry = inr exit) :
  invariant ∈ certificate_operational_footprint
    (CertUnfold cost Γ entry statement invariant exit view step).
Proof. simpl. set_solver. Qed.

Lemma certificate_fold_operational_footprint_mem
    {Γ entry statement invariant cost}
    (view : Syntax.view Γ statement = ViewFold invariant) :
  invariant ∈ certificate_operational_footprint
    (CertFold cost Γ entry statement invariant view).
Proof. simpl. set_solver. Qed.

Lemma certificate_entry_subset_footprint {Γ entry statement exit cost}
    (certificate : analysis_certificate cost Γ entry statement exit) :
  analysis_mask entry ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Lemma certificate_exit_subset_footprint {Γ entry statement exit cost}
    (certificate : analysis_certificate cost Γ entry statement exit) :
  analysis_mask exit ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Lemma certificate_entry_open_subset_footprint
    {Γ entry statement exit cost}
    (certificate : analysis_certificate cost Γ entry statement exit) :
  analysis_open entry ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Lemma certificate_exit_open_subset_footprint
    {Γ entry statement exit cost}
    (certificate : analysis_certificate cost Γ entry statement exit) :
  analysis_open exit ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

(** Coherence is exactly the missing analyzer-side premise needed to recover
    the old global footprint bound without consulting mask indices on a
    Hoare derivation. *)
Lemma coherent_certificate_footprint_subset_exit_resources
    {Γ entry statement exit cost}
    (certificate : analysis_certificate cost Γ entry statement exit) :
  conditional_masks_coherent certificate ->
  certificate_footprint certificate ⊆
    analysis_mask exit ∪ analysis_open exit.
Proof.
  induction certificate; simpl; intros Hcoherent.
  - pose proof (take_step_resources_monotone _ _ _ e0) as Hstart.
    intros other Hmember.
    specialize (Hstart other).
    repeat rewrite elem_of_union in Hmember.
    rewrite elem_of_empty in Hmember.
    destruct Hmember as [[[[Hmask | Hopen] | Hexit_mask] | Hexit_open] | []].
    + apply Hstart. apply elem_of_union_l. exact Hmask.
    + apply Hstart. apply elem_of_union_r. exact Hopen.
    + apply elem_of_union_l. exact Hexit_mask.
    + apply elem_of_union_r. exact Hexit_open.
  - set_solver.
  - apply open_invariant_success in e0 as
      (Hfresh & Havailable & Hmask & Hopen).
    rewrite Hmask, Hopen.
    intros other Hmember.
    repeat rewrite elem_of_union in Hmember.
    rewrite elem_of_empty in Hmember.
    destruct Hmember as
      [[[[Hentry_mask | Hentry_open] | Hexit_mask] | Hexit_open] | []].
    + destruct (decide (other = invariant)) as [-> | Hneq].
      * apply elem_of_union_r, elem_of_union_l, elem_of_singleton_2. reflexivity.
      * apply elem_of_union_l, elem_of_difference. split.
        -- exact Hentry_mask.
        -- intros Hsingleton. apply elem_of_singleton_1 in Hsingleton.
           exact (Hneq Hsingleton).
    + apply elem_of_union_r, elem_of_union_r. exact Hentry_open.
    + apply elem_of_union_l. exact Hexit_mask.
    + apply elem_of_union_r, elem_of_union. exact Hexit_open.
  - unfold fold_invariant.
    destruct (bool_decide (invariant ∈ analysis_open state)); simpl;
      intros other Hmember;
      repeat rewrite elem_of_union in Hmember;
      rewrite elem_of_empty in Hmember;
      destruct Hmember as
        [[[[Hentry_mask | Hentry_open] | Hexit_mask] | Hexit_open] | []].
    + apply elem_of_union_l, elem_of_union_r. exact Hentry_mask.
    + destruct (decide (other = invariant)) as [-> | Hneq].
      * apply elem_of_union_l, elem_of_union_l, elem_of_singleton_2. reflexivity.
      * apply elem_of_union_r, elem_of_difference. split.
        -- exact Hentry_open.
        -- intros Hsingleton. apply elem_of_singleton_1 in Hsingleton.
           exact (Hneq Hsingleton).
    + apply elem_of_union_l, elem_of_union. exact Hexit_mask.
    + apply elem_of_union_r. exact Hexit_open.
    + apply elem_of_union_l, elem_of_union_r. exact Hentry_mask.
    + apply elem_of_union_r. exact Hentry_open.
    + apply elem_of_union_l, elem_of_union. exact Hexit_mask.
    + apply elem_of_union_r. exact Hexit_open.
  - destruct Hcoherent as [Hfirst_coherent Hsecond_coherent].
    specialize (IHcertificate1 Hfirst_coherent).
    specialize (IHcertificate2 Hsecond_coherent).
    assert (Hmiddle : analysis_mask middle ∪ analysis_open middle ⊆
        analysis_mask exit ∪ analysis_open exit).
    { etrans.
      - intros invariant Hmember.
        rewrite elem_of_union in Hmember.
        destruct Hmember as [Hmask|Hopen].
        + apply (certificate_entry_subset_footprint certificate2). exact Hmask.
        + apply (certificate_entry_open_subset_footprint certificate2).
          exact Hopen.
      - exact IHcertificate2. }
    assert (Hstart : analysis_mask state ∪ analysis_open state ⊆
        analysis_mask middle ∪ analysis_open middle).
    { etrans.
      - intros invariant Hmember.
        rewrite elem_of_union in Hmember.
        destruct Hmember as [Hmask|Hopen].
        + apply (certificate_entry_subset_footprint certificate1). exact Hmask.
        + apply (certificate_entry_open_subset_footprint certificate1).
          exact Hopen.
      - exact IHcertificate1. }
    intros other Hmember.
    repeat rewrite elem_of_union in Hmember.
    destruct Hmember as
      [[[[Hentry_mask | Hentry_open] | Hexit_mask] | Hexit_open] |
        [Hfirst | Hsecond]].
    + apply Hmiddle, Hstart, elem_of_union_l. exact Hentry_mask.
    + apply Hmiddle, Hstart, elem_of_union_r. exact Hentry_open.
    + apply elem_of_union_l. exact Hexit_mask.
    + apply elem_of_union_r. exact Hexit_open.
    + apply Hmiddle, IHcertificate1. exact Hfirst.
    + apply IHcertificate2. exact Hsecond.
  - destruct Hcoherent as [Hmasks [Hthen_coherent Helse_coherent]].
    specialize (IHcertificate1 Hthen_coherent).
    specialize (IHcertificate2 Helse_coherent).
    rewrite Hmasks.
    assert (Hmask_idem : analysis_mask else_exit ∩ analysis_mask else_exit =
        analysis_mask else_exit).
    { apply set_eq. intros invariant.
      rewrite elem_of_intersection. tauto. }
    rewrite Hmask_idem.
    match goal with
    | Hopen : analysis_open then_exit = analysis_open else_exit |- _ =>
        rewrite <- Hopen in IHcertificate2
    end.
    assert (Hstart : analysis_mask state ∪ analysis_open state ⊆
        analysis_mask else_exit ∪ analysis_open then_exit).
    { etrans.
      - intros invariant Hmember.
        rewrite elem_of_union in Hmember.
        destruct Hmember as [Hmask|Hopen].
        + apply (certificate_entry_subset_footprint certificate1). exact Hmask.
        + apply (certificate_entry_open_subset_footprint certificate1).
          exact Hopen.
      - rewrite Hmasks in IHcertificate1. exact IHcertificate1. }
    intros other Hmember.
    repeat rewrite elem_of_union in Hmember.
    destruct Hmember as
      [[[[Hentry_mask | Hentry_open] | Hexit_mask] | Hexit_open] |
        [Hthen | Helse]].
    + apply Hstart, elem_of_union_l. exact Hentry_mask.
    + apply Hstart, elem_of_union_r. exact Hentry_open.
    + apply elem_of_union_l. exact Hexit_mask.
    + apply elem_of_union_r. exact Hexit_open.
    + rewrite Hmasks in IHcertificate1. apply IHcertificate1. exact Hthen.
    + apply IHcertificate2. exact Helse.
  - specialize (IHcertificate Hcoherent).
    pose proof (atomic_step_preserves_sets _ _ e0) as Hsets.
    destruct Hsets as [Hmask Hopen].
    assert (Hentry : analysis_mask state ∪ analysis_open state ⊆
        analysis_mask inner ∪ analysis_open inner).
    { rewrite <- Hmask, <- Hopen.
      etrans.
      - intros invariant Hmember.
        rewrite elem_of_union in Hmember.
        destruct Hmember as [Hmask'|Hopen'].
        + apply (certificate_entry_subset_footprint certificate). exact Hmask'.
        + apply (certificate_entry_open_subset_footprint certificate).
          exact Hopen'.
      - exact IHcertificate. }
    intros other Hmember.
    repeat rewrite elem_of_union in Hmember.
    destruct Hmember as
      [[[[Hentry_mask | Hentry_open] | Hexit_mask] | Hexit_open] | Hbody].
    + apply Hentry, elem_of_union_l. exact Hentry_mask.
    + apply Hentry, elem_of_union_r. exact Hentry_open.
    + apply elem_of_union_l. exact Hexit_mask.
    + apply elem_of_union_r. exact Hexit_open.
    + apply IHcertificate. exact Hbody.
Qed.

Lemma closed_coherent_certificate_footprint_subset_exit_mask
    {Γ entry statement exit cost}
    (certificate : analysis_certificate cost Γ entry statement exit) :
  conditional_masks_coherent certificate ->
  analysis_open exit = ∅ ->
  certificate_footprint certificate ⊆ analysis_mask exit.
Proof.
  intros Hcoherent Hclosed invariant Hmember.
  pose proof (coherent_certificate_footprint_subset_exit_resources certificate
    Hcoherent invariant Hmember) as Hresources.
  rewrite Hclosed, elem_of_union, elem_of_empty in Hresources.
  tauto.
Qed.

Fixpoint certificate_height {Γ entry statement exit} {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit) : nat :=
  match certificate with
  | CertLeaf _ _ _ _ _ _ _ => 1
  | CertDone _ _ _ _ _ => 1
  | CertUnfold _ _ _ _ _ _ _ _ => 1
  | CertFold _ _ _ _ _ _ => 1
  | CertSequence _ _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      S (Nat.max (certificate_height first_certificate)
        (certificate_height second_certificate))
  | CertConditional _ _ _ _ _ _ _ _ _ then_certificate else_certificate _ _ =>
      S (Nat.max (certificate_height then_certificate)
        (certificate_height else_certificate))
  | CertAtomic _ _ _ _ _ _ _ _ _ body_certificate _ =>
      S (certificate_height body_certificate)
  end.

Lemma analyze_fuel_succ {Γ fuel} (cost : cost_model) state
    (statement : Syntax.statement Γ) exit :
  analyze_fuel fuel cost state statement = inr exit ->
  analyze_fuel (S fuel) cost state statement = inr exit.
Proof.
  revert Γ state statement exit.
  induction fuel as [|fuel IH]; intros Γ state statement exit Hrun;
    simpl in Hrun |- *; first discriminate.
  destruct (Syntax.view Γ statement) eqn:Hview; simpl in Hrun |- *.
  - exact Hrun.
  - exact Hrun.
  - exact Hrun.
  - exact Hrun.
  - destruct (analyze_fuel fuel cost state first) as [error|middle]
      eqn:Hfirst; try discriminate.
    eapply IH in Hfirst.
    eapply IH in Hrun.
    change (analyze_fuel (S fuel) cost state first = inr middle) in Hfirst.
    change (analyze_fuel (S fuel) cost middle second = inr exit) in Hrun.
    change (match analyze_fuel (S fuel) cost state first with
      | inl error => inl error
      | inr middle => analyze_fuel (S fuel) cost middle second
      end = inr exit).
    rewrite Hfirst. exact Hrun.
  - destruct (analyze_fuel fuel cost state then_branch) as [error|then_exit]
      eqn:Hthen; try discriminate.
    destruct (analyze_fuel fuel cost state else_branch) as [error|else_exit]
      eqn:Helse; try discriminate.
    destruct (bool_decide
      (analysis_open then_exit = analysis_open else_exit /\
       analysis_in_atomic then_exit = analysis_in_atomic else_exit)) eqn:Hjoin;
      try discriminate.
    eapply IH in Hthen. eapply IH in Helse.
    change (analyze_fuel (S fuel) cost state then_branch = inr then_exit)
      in Hthen.
    change (analyze_fuel (S fuel) cost state else_branch = inr else_exit)
      in Helse.
    change (match analyze_fuel (S fuel) cost state then_branch,
      analyze_fuel (S fuel) cost state else_branch with
      | inr then_state, inr else_state =>
          if bool_decide
            (analysis_open then_state = analysis_open else_state /\
             analysis_in_atomic then_state = analysis_in_atomic else_state)
          then inr (AnalysisState
            (analysis_mask then_state ∩ analysis_mask else_state)
            (analysis_open then_state)
            (analysis_step_taken then_state || analysis_step_taken else_state)
            (analysis_in_atomic then_state))
          else inl IncompatibleBranches
      | inl error, _ | _, inl error => inl error
      end = inr exit).
    rewrite Hthen, Helse, Hjoin. exact Hrun.
  - discriminate.
  - destruct (take_step AtomicStep state) as [error|outer] eqn:Hstep;
      try discriminate.
    destruct (analyze_fuel fuel cost
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body) as [error|inner]
      eqn:Hbody; try discriminate.
    destruct (bool_decide (analysis_open inner = analysis_open outer)) eqn:Hclose;
      try discriminate.
    eapply IH in Hbody.
    change (analyze_fuel (S fuel) cost
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body = inr inner) in Hbody.
    change (match analyze_fuel (S fuel) cost
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body with
      | inl error => inl error
      | inr inner =>
          if bool_decide (analysis_open inner = analysis_open outer)
          then inr (AnalysisState (analysis_mask inner)
            (analysis_open inner)
            (analysis_step_taken outer || analysis_step_taken inner)
            (analysis_in_atomic outer))
          else inl AtomicBlockLeaksAccess
      end = inr exit).
    rewrite Hbody, Hclose. exact Hrun.
Qed.

Lemma analyze_fuel_monotone {Γ fuel target} (cost : cost_model) state
    (statement : Syntax.statement Γ) exit :
  fuel <= target ->
  analyze_fuel fuel cost state statement = inr exit ->
  analyze_fuel target cost state statement = inr exit.
Proof.
  intros Hle Hrun. induction Hle.
  - exact Hrun.
  - apply analyze_fuel_succ. exact IHHle.
Qed.

Lemma certificate_replays_height {Γ entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit) :
  analyze_fuel (certificate_height certificate) cost entry statement = inr exit.
Proof.
  induction certificate; simpl.
  - rewrite e. exact e0.
  - rewrite e. reflexivity.
  - rewrite e. exact e0.
  - rewrite e. reflexivity.
  - rewrite e.
    rewrite (analyze_fuel_monotone cost _ _ _
      (Nat.le_max_l _ _) IHcertificate1).
    exact (analyze_fuel_monotone cost _ _ _
      (Nat.le_max_r _ _) IHcertificate2).
  - rewrite e.
    rewrite (analyze_fuel_monotone cost _ _ _
      (Nat.le_max_l _ _) IHcertificate1).
    rewrite (analyze_fuel_monotone cost _ _ _
      (Nat.le_max_r _ _) IHcertificate2).
    rewrite bool_decide_true; [reflexivity|]. split; assumption.
  - rewrite e, e0.
    rewrite IHcertificate.
    rewrite bool_decide_true; [reflexivity|exact e1].
Qed.

Lemma certificate_height_le_size {Γ entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit) :
  certificate_height certificate <= Syntax.size Γ statement.
Proof.
  induction certificate; simpl.
  - pose proof (Syntax.size_positive Γ statement). lia.
  - pose proof (Syntax.size_positive Γ statement). lia.
  - pose proof (Syntax.size_positive Γ statement). lia.
  - pose proof (Syntax.size_positive Γ statement). lia.
  - pose proof (Syntax.sequence_children_smaller Γ statement first second e)
      as [Hfirst Hsecond].
    lia.
  - pose proof (Syntax.conditional_children_smaller Γ statement then_branch
      else_branch e) as [Hthen Helse].
    lia.
  - pose proof (Syntax.atomic_body_smaller Γ statement body e) as Hbody.
    lia.
Qed.

Theorem certificate_replays {Γ} (cost : cost_model) state
    (statement : Syntax.statement Γ) exit :
  analysis_certificate cost Γ state statement exit ->
  analyze cost state statement = inr exit.
Proof.
  intros certificate. unfold analyze.
  eapply analyze_fuel_monotone;
    [exact (certificate_height_le_size (cost := cost) certificate)|].
  exact (certificate_replays_height certificate).
Qed.

Lemma analysis_certificate_exit_unique
    {Γ cost entry statement exit1 exit2}
    (certificate1 : analysis_certificate cost Γ entry statement exit1)
    (certificate2 : analysis_certificate cost Γ entry statement exit2) :
  exit1 = exit2.
Proof.
  pose proof (certificate_replays cost entry statement exit1 certificate1)
    as Hreplay1.
  pose proof (certificate_replays cost entry statement exit2 certificate2)
    as Hreplay2.
  congruence.
Qed.

Lemma analyze_fuel_certificate_exit {Γ fuel cost entry statement actual expected} :
  analyze_fuel fuel cost entry statement = inr actual ->
  analysis_certificate cost Γ entry statement expected ->
  actual = expected.
Proof.
  intros Hrun certificate.
  pose proof (analyze_fuel_monotone cost entry statement actual
    (Nat.le_max_l fuel (certificate_height certificate)) Hrun) as Hactual.
  pose proof (analyze_fuel_monotone cost entry statement expected
    (Nat.le_max_r fuel (certificate_height certificate))
    (certificate_replays_height certificate)) as Hexpected.
  congruence.
Qed.

Lemma analyze_coherent_lifo_fuel_replays {Γ fuel entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit)
    stack_in stack_out :
  analyze_coherent_lifo_fuel fuel cost entry stack_in statement =
    Some (exit, stack_out) ->
  replay_lifo_certificate certificate stack_in = Some stack_out.
Proof.
  revert fuel stack_in stack_out.
  induction certificate.
  - intros [|fuel] stack_in stack_out Hrun; cbn in Hrun |- *;
      [discriminate|].
    rewrite e, e0 in Hrun.
    inversion Hrun; reflexivity.
  - intros [|fuel] stack_in stack_out Hrun; cbn in Hrun |- *;
      [discriminate|].
    rewrite e in Hrun.
    inversion Hrun; reflexivity.
  - intros [|fuel] stack_in stack_out Hrun; cbn in Hrun |- *;
      [discriminate|].
    rewrite e, e0 in Hrun.
    inversion Hrun; reflexivity.
  - intros [|fuel] stack_in stack_out Hrun; cbn in Hrun |- *;
      [discriminate|].
    rewrite e in Hrun.
    destruct stack_in as [|[candidate outer_open] rest]; simpl in *.
    + destruct (decide (invariant ∉ analysis_open state)); try discriminate.
      inversion Hrun. reflexivity.
    + destruct (decide (candidate = invariant /\
          invariant ∈ analysis_open state /\ invariant ∉ outer_open /\
          analysis_open state = {[invariant]} ∪ outer_open)) as [Hclose|Hclose].
      * inversion Hrun. reflexivity.
      * destruct (decide (invariant ∉ analysis_open state)); try discriminate.
        inversion Hrun. reflexivity.
  - intros [|fuel] stack_in stack_out Hrun; cbn in Hrun |- *;
      [discriminate|].
    rewrite e in Hrun.
    destruct (analyze_coherent_lifo_fuel fuel cost state stack_in first) as
      [[actual_middle stack_middle]|] eqn:Hfirst; try discriminate.
    assert (Hmiddle : actual_middle = middle).
    { pose proof (analyze_coherent_lifo_fuel_projects _ cost state stack_in
        first actual_middle stack_middle Hfirst) as Hactual.
      exact (analyze_fuel_certificate_exit Hactual certificate1). }
    subst actual_middle.
    specialize (IHcertificate1 _ _ _ Hfirst) as Hfirst_replay.
    specialize (IHcertificate2 _ _ _ Hrun) as Hsecond_replay.
    rewrite Hfirst_replay. exact Hsecond_replay.
  - intros [|fuel] stack_in stack_out Hrun; cbn in Hrun |- *;
      [discriminate|].
    rewrite e in Hrun.
    destruct (analyze_coherent_lifo_fuel fuel cost state stack_in then_branch) as
      [[actual_then then_stack]|] eqn:Hthen; try discriminate.
    destruct (analyze_coherent_lifo_fuel fuel cost state stack_in else_branch) as
      [[actual_else else_stack]|] eqn:Helse; try discriminate.
    assert (Hthen_exit : actual_then = then_exit).
    { pose proof (analyze_coherent_lifo_fuel_projects _ cost state stack_in
        then_branch actual_then then_stack Hthen) as Hactual.
      exact (analyze_fuel_certificate_exit Hactual certificate1). }
    assert (Helse_exit : actual_else = else_exit).
    { pose proof (analyze_coherent_lifo_fuel_projects _ cost state stack_in
        else_branch actual_else else_stack Helse) as Hactual.
      exact (analyze_fuel_certificate_exit Hactual certificate2). }
    subst actual_then. subst actual_else.
    destruct (decide
      (analysis_open then_exit = analysis_open else_exit /\
       analysis_in_atomic then_exit = analysis_in_atomic else_exit /\
       analysis_mask then_exit = analysis_mask else_exit /\
       then_stack = else_stack)) as [Hjoin|Hjoin]; try discriminate.
    inversion Hrun; subst stack_out.
    destruct Hjoin as [_ [_ [_ Hstacks]]].
    subst else_stack.
    specialize (IHcertificate1 _ _ _ Hthen) as Hthen_replay.
    specialize (IHcertificate2 _ _ _ Helse) as Helse_replay.
    rewrite Hthen_replay, Helse_replay.
    rewrite decide_True; [reflexivity|reflexivity].
  - intros [|fuel] stack_in stack_out Hrun; cbn in Hrun |- *;
      [discriminate|].
    rewrite e in Hrun.
    destruct (take_step AtomicStep state) as [error|actual_outer]
      eqn:Hstep; try discriminate.
    assert (Houter : actual_outer = outer).
    { rewrite e0 in Hstep. congruence. }
    subst actual_outer.
    destruct (analyze_coherent_lifo_fuel fuel cost
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) stack_in body) as
      [[actual_inner body_stack]|] eqn:Hbody; try discriminate.
    assert (Hinner : actual_inner = inner).
    { pose proof (analyze_coherent_lifo_fuel_projects _ cost
        (AnalysisState (analysis_mask outer) (analysis_open outer)
          (analysis_step_taken outer) true) stack_in body actual_inner
        body_stack Hbody) as Hactual.
      exact (analyze_fuel_certificate_exit Hactual certificate). }
    subst actual_inner.
    destruct (decide (analysis_open inner = analysis_open outer /\
      body_stack = stack_in)) as [Hclose|Hclose]; try discriminate.
    inversion Hrun; subst stack_out.
    destruct Hclose as [_ Hstack]. subst body_stack.
    specialize (IHcertificate _ _ _ Hbody) as Hbody_replay.
    rewrite Hbody_replay. rewrite decide_True; [reflexivity|reflexivity].
Qed.

Lemma analyze_coherent_lifo_fuel_sound {Γ fuel entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit)
    stack_in stack_out :
  analyze_coherent_lifo_fuel fuel cost entry stack_in statement =
    Some (exit, stack_out) ->
  lifo_certificate certificate stack_in stack_out.
Proof.
  intros Hrun.
  apply replay_lifo_certificate_sound.
  eapply analyze_coherent_lifo_fuel_replays; exact Hrun.
Qed.

Lemma check_conditional_masks_fuel_sound
    {Γ fuel entry statement exit cost}
    (certificate : analysis_certificate cost Γ entry statement exit) :
  certificate_height certificate <= fuel ->
  check_conditional_masks_fuel fuel cost entry statement = true ->
  conditional_masks_coherent certificate.
Proof.
  revert fuel.
  induction certificate; simpl; intros fuel Hheight Hcheck.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - destruct fuel as [|fuel]; [lia|].
    cbn in Hcheck. rewrite e in Hcheck.
    assert (Hfirst_run : analyze_fuel fuel cost state first = inr middle).
    { apply (analyze_fuel_monotone (fuel := certificate_height certificate1)
        (target := fuel) cost state first middle); [lia|].
      exact (certificate_replays_height certificate1). }
    rewrite Hfirst_run in Hcheck.
    apply andb_true_iff in Hcheck as [Hfirst Hsecond].
    split; [apply (IHcertificate1 fuel) | apply (IHcertificate2 fuel)];
      lia || assumption.
  - destruct fuel as [|fuel]; [lia|].
    cbn in Hcheck. rewrite e in Hcheck.
    assert (Hthen_run : analyze_fuel fuel cost state then_branch = inr then_exit).
    { apply (analyze_fuel_monotone (fuel := certificate_height certificate1)
        (target := fuel) cost state then_branch then_exit); [lia|].
      exact (certificate_replays_height certificate1). }
    assert (Helse_run : analyze_fuel fuel cost state else_branch = inr else_exit).
    { apply (analyze_fuel_monotone (fuel := certificate_height certificate2)
        (target := fuel) cost state else_branch else_exit); [lia|].
      exact (certificate_replays_height certificate2). }
    rewrite Hthen_run, Helse_run in Hcheck.
    apply andb_true_iff in Hcheck as [Hbranches Hmask].
    apply andb_true_iff in Hbranches as [Hthen Helse].
    apply bool_decide_eq_true in Hmask.
    repeat split; try assumption.
    + apply (IHcertificate1 fuel); [lia|exact Hthen].
    + apply (IHcertificate2 fuel); [lia|exact Helse].
  - destruct fuel as [|fuel]; [lia|].
    cbn in Hcheck. rewrite e, e0 in Hcheck.
    apply (IHcertificate fuel); [lia|exact Hcheck].
Qed.

Definition coherent_analysis_certificate_of_success
    {Γ entry statement exit cost}
    (certificate : analysis_certificate cost Γ entry statement exit)
    (Hcoherent : check_conditional_masks_fuel (Syntax.size Γ statement)
      cost entry statement = true) :
    @coherent_analysis_certificate Γ entry statement exit cost :=
  {| coherent_flat_certificate := certificate;
     coherent_conditional_masks :=
       check_conditional_masks_fuel_sound certificate
         (certificate_height_le_size certificate) Hcoherent |}.

Lemma coherent_certificate_replays {Γ entry statement exit cost}
    (certificate : @coherent_analysis_certificate Γ entry statement exit
      cost) :
  analyze cost entry statement = inr exit.
Proof.
  apply certificate_replays.
  exact (coherent_flat_certificate cost certificate).
Qed.

(** For fixed public indices, successful analyzer certificates carry no additional
    computational choice.  This lets later certified transformations use a
    canonical certificate construction without introducing a parallel plan
    object merely to remember its proof fields. *)
Lemma analysis_certificate_unique
    {Γ cost entry statement exit}
    (certificate1 certificate2 :
      analysis_certificate cost Γ entry statement exit) :
  certificate1 = certificate2.
Proof.
  revert certificate2.
  induction certificate1; intros certificate2; dependent destruction certificate2;
    try solve [exfalso; congruence].
  - f_equal; apply proof_irrelevance.
  - f_equal; apply proof_irrelevance.
  - assert (invariant0 = invariant) by congruence. subst invariant0.
    f_equal; apply proof_irrelevance.
  - assert (invariant0 = invariant) by congruence. subst invariant0.
    apply JMeq_eq in x. subst certificate0.
    f_equal; apply proof_irrelevance.
  - assert (first0 = first) by congruence. subst first0.
    assert (second0 = second) by congruence. subst second0.
    pose proof (analysis_certificate_exit_unique certificate1_1
      certificate2_1) as Hmiddle. subst middle0.
    rewrite (IHcertificate1_1 certificate2_1).
    rewrite (IHcertificate1_2 certificate2_2).
    f_equal; apply proof_irrelevance.
  - assert (then_branch0 = then_branch) by congruence. subst then_branch0.
    assert (else_branch0 = else_branch) by congruence. subst else_branch0.
    pose proof (analysis_certificate_exit_unique certificate1_1
      certificate2_1) as Hthen. subst then_exit0.
    pose proof (analysis_certificate_exit_unique certificate1_2
      certificate2_2) as Helse. subst else_exit0.
    apply JMeq_eq in x. subst certificate0.
    rewrite (IHcertificate1_1 certificate2_1).
    rewrite (IHcertificate1_2 certificate2_2).
    f_equal; apply proof_irrelevance.
  - assert (body0 = body) by congruence. subst body0.
    assert (outer0 = outer) by congruence. subst outer0.
    pose proof (analysis_certificate_exit_unique certificate1
      certificate2) as Hinner. subst inner0.
    apply JMeq_eq in x. subst certificate0.
    rewrite (IHcertificate1 certificate2).
    f_equal; apply proof_irrelevance.
Qed.

Theorem certificate_preserves_wf {Γ} (cost : cost_model) state
    (statement : Syntax.statement Γ) exit :
  state_wf state ->
  analysis_certificate cost Γ state statement exit ->
  state_wf exit.
Proof.
  intros Hwf certificate. induction certificate.
  - eapply take_step_preserves_wf; eauto.
  - exact Hwf.
  - eapply open_invariant_preserves_wf; eauto.
  - apply fold_invariant_preserves_wf. exact Hwf.
  - apply IHcertificate2. apply IHcertificate1. exact Hwf.
  - cbn. specialize (IHcertificate1 Hwf).
    unfold state_wf in IHcertificate1 |- *.
    rewrite elem_of_disjoint in IHcertificate1 |- *.
    intros invariant Hinvariant Hmask.
    apply (IHcertificate1 invariant Hinvariant).
    apply elem_of_intersection in Hmask as [Hmask _]. exact Hmask.
  - cbn. apply IHcertificate.
    pose proof (take_step_preserves_wf _ _ _ Hwf e0) as Houter.
    exact Houter.
Qed.

Lemma lifo_preserves_access_stack_consistency
    {Γ entry statement exit cost}
    (certificate : analysis_certificate cost Γ entry statement exit)
    stack_in stack_out :
  state_wf entry ->
  lifo_certificate certificate stack_in stack_out ->
  access_stack_consistent (analysis_open entry) stack_in ->
  access_stack_consistent (analysis_open exit) stack_out.
Proof.
  revert stack_in stack_out.
  induction certificate; intros stack_in stack_out Hwf Hlifo Hstack;
    simpl in Hlifo.
  - subst stack_out.
    apply take_step_preserves_open in e0 as Hopen.
    now rewrite Hopen.
  - subst stack_out. exact Hstack.
  - subst stack_out.
    apply open_invariant_success in e0 as (Hfresh & _ & _ & Hopen).
    simpl. split; [exact Hfresh|].
    split; [exact Hopen|exact Hstack].
  - destruct Hlifo as
      [(outer_open & Hstack_in & Hmember & Hfresh & Hopen)|[Hsame Hclosed]].
    + subst stack_in. simpl in Hstack.
      destruct Hstack as [_ [Hentry Htail]].
      apply fold_open_invariant in Hmember as [_ Hexit].
      rewrite Hexit. rewrite Hopen. simpl in Htail.
      replace (({[invariant]} ∪ outer_open) ∖ {[invariant]}) with outer_open
        by set_solver.
      exact Htail.
    + subst stack_out.
      apply fold_fresh_invariant in Hclosed as [_ Hexit].
      now rewrite Hexit.
  - destruct Hlifo as (stack_middle & Hfirst & Hsecond).
    eapply IHcertificate2; [|exact Hsecond|].
    + eapply certificate_preserves_wf; eauto.
    + eapply IHcertificate1; eauto.
  - destruct Hlifo as [Hthen Helse].
    specialize (IHcertificate1 stack_in stack_out Hwf Hthen Hstack).
    simpl. exact IHcertificate1.
  - destruct Hlifo as [Hbody Hsame]. subst stack_out.
    simpl.
    eapply IHcertificate; [|exact Hbody|].
    + exact (take_step_preserves_wf _ _ _ Hwf e0).
    + apply take_step_preserves_open in e0 as Hopen.
      simpl. now rewrite Hopen.
Qed.

Lemma access_segment_sequence
    {Γ state statement first middle second exit cost}
    (view : Syntax.view Γ statement = ViewSequence first second)
    (first_certificate : analysis_certificate cost Γ state first middle)
    (second_certificate : analysis_certificate cost Γ middle second exit)
    stack_in stack_middle stack_out :
  access_segment first_certificate stack_in stack_middle ->
  access_segment second_certificate stack_middle stack_out ->
  access_segment
    (CertSequence cost Γ state statement first middle second exit
      view first_certificate second_certificate)
    stack_in stack_out.
Proof.
  intros Hfirst Hsecond.
  destruct Hfirst as [Hfirst Hstack].
  destruct Hsecond as [Hsecond _].
  constructor.
  - simpl. exists stack_middle. split; assumption.
  - exact Hstack.
Qed.

Lemma access_segment_conditional
    {Γ state statement then_branch else_branch then_exit else_exit cost}
    (view : Syntax.view Γ statement = ViewConditional then_branch else_branch)
    (then_certificate : analysis_certificate cost Γ state then_branch then_exit)
    (else_certificate : analysis_certificate cost Γ state else_branch else_exit)
    (open_equal : analysis_open then_exit = analysis_open else_exit)
    (atomic_equal : analysis_in_atomic then_exit = analysis_in_atomic else_exit)
    stack_in stack_out :
  access_segment then_certificate stack_in stack_out ->
  access_segment else_certificate stack_in stack_out ->
  access_segment
    (CertConditional cost Γ state statement then_branch else_branch
      then_exit else_exit view then_certificate else_certificate
      open_equal atomic_equal)
    stack_in stack_out.
Proof.
  intros Hthen Helse.
  destruct Hthen as [Hthen Hstack].
  destruct Helse as [Helse _].
  constructor.
  - simpl. split; assumption.
  - exact Hstack.
Qed.

Lemma access_segment_atomic
    {Γ state statement body outer inner cost}
    (view : Syntax.view Γ statement = ViewAtomic body)
    (step : take_step AtomicStep state = inr outer)
    (body_certificate : analysis_certificate cost Γ
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body inner)
    (open_equal : analysis_open inner = analysis_open outer)
    stack :
  access_segment body_certificate stack stack ->
  access_segment
    (CertAtomic cost Γ state statement body outer inner view step
      body_certificate open_equal)
    stack stack.
Proof.
  intros Hbody. destruct Hbody as [Hbody Hstack].
  constructor.
  - simpl. split; [exact Hbody|reflexivity].
  - apply take_step_preserves_open in step as Hopen.
    simpl in Hstack. now rewrite Hopen in Hstack.
Qed.

Lemma access_segment_leaf
    {Γ entry statement exit cost}
    (view : Syntax.view Γ statement = ViewLeaf)
    (step : take_step (cost Γ statement) entry = inr exit)
    stack :
  access_stack_consistent (analysis_open entry) stack ->
  access_segment
    (CertLeaf cost Γ entry statement exit view step) stack stack.
Proof.
  intros Hstack. constructor; [simpl; reflexivity|exact Hstack].
Qed.

Lemma access_segment_unfold
    {Γ entry statement invariant exit cost}
    (view : Syntax.view Γ statement = ViewUnfold invariant)
    (step : open_invariant invariant entry = inr exit)
    stack :
  access_stack_consistent (analysis_open entry) stack ->
  access_segment
    (CertUnfold cost Γ entry statement invariant exit view step)
    stack ((invariant, analysis_open entry) :: stack).
Proof.
  intros Hstack. constructor; [simpl; reflexivity|exact Hstack].
Qed.

Lemma access_segment_fold_matched
    {Γ entry statement invariant cost}
    (view : Syntax.view Γ statement = ViewFold invariant)
    outer_open stack :
  invariant ∈ analysis_open entry ->
  invariant ∉ outer_open ->
  analysis_open entry = {[invariant]} ∪ outer_open ->
  access_stack_consistent (analysis_open entry)
    ((invariant, outer_open) :: stack) ->
  access_segment
    (CertFold cost Γ entry statement invariant view)
    ((invariant, outer_open) :: stack) stack.
Proof.
  intros Hmember Hfresh Hopen Hstack.
  constructor.
  - simpl. left. exists outer_open. repeat split; assumption || reflexivity.
  - exact Hstack.
Qed.

Lemma access_segment_fold_fresh
    {Γ entry statement invariant cost}
    (view : Syntax.view Γ statement = ViewFold invariant)
    stack :
  invariant ∉ analysis_open entry ->
  access_stack_consistent (analysis_open entry) stack ->
  access_segment
    (CertFold cost Γ entry statement invariant view) stack stack.
Proof.
  intros Hclosed Hstack.
  constructor.
  - simpl. right. split; [reflexivity|exact Hclosed].
  - exact Hstack.
Qed.

Lemma closed_lifo_is_balanced
    {Γ entry statement exit cost}
    (certificate : analysis_certificate cost Γ entry statement exit) :
  state_wf entry ->
  analysis_open entry = ∅ ->
  lifo_certificate certificate [] [] ->
  balanced_access_segment certificate [] /\
  analysis_open exit = ∅.
Proof.
  intros Hwf Hentry Hlifo. split.
  - constructor; [exact Hlifo|exact Hentry].
  - pose proof (lifo_preserves_access_stack_consistency certificate [] []
      Hwf Hlifo Hentry) as Hexit.
    exact Hexit.
Qed.

Theorem analyze_fuel_builds_certificate {Γ fuel} (cost : cost_model) state
    (statement : Syntax.statement Γ) exit :
  analyze_fuel fuel cost state statement = inr exit ->
  analysis_certificate cost Γ state statement exit.
Proof.
  revert Γ state statement exit.
  induction fuel as [|fuel IH]; intros Γ state statement exit Hanalyze;
    simpl in Hanalyze; first discriminate.
  destruct (Syntax.view Γ statement) eqn:Hview.
  - eapply CertLeaf; [exact Hview|exact Hanalyze].
  - inversion Hanalyze; subst exit. eapply CertDone. exact Hview.
  - eapply CertUnfold; [exact Hview|exact Hanalyze].
  - inversion Hanalyze; subst exit. eapply CertFold. exact Hview.
  - destruct (analyze_fuel fuel cost state first) as [error|middle] eqn:Hfirst;
      try discriminate.
    eapply CertSequence; [exact Hview|eapply IH|eapply IH]; eauto.
  - destruct (analyze_fuel fuel cost state then_branch) as [error|then_exit] eqn:Hthen;
      try discriminate.
    destruct (analyze_fuel fuel cost state else_branch) as [error|else_exit] eqn:Helse;
      try discriminate.
    destruct (bool_decide
      (analysis_open then_exit = analysis_open else_exit /\
       analysis_in_atomic then_exit = analysis_in_atomic else_exit)) eqn:Hjoin;
      last discriminate.
    apply bool_decide_eq_true in Hjoin as [Hopen Hin_atomic].
    inversion Hanalyze; subst exit.
    eapply CertConditional; eauto.
  - discriminate.
  - destruct (take_step AtomicStep state) as [error|outer] eqn:Hstep;
      try discriminate.
    destruct (analyze_fuel fuel cost
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body) as [error|inner] eqn:Hbody;
      try discriminate.
    destruct (bool_decide (analysis_open inner = analysis_open outer)) eqn:Hscope;
      last discriminate.
    apply bool_decide_eq_true in Hscope.
    inversion Hanalyze; subst exit.
    eapply CertAtomic; eauto.
Defined.

Corollary analyze_builds_certificate {Γ} (cost : cost_model) state
    (statement : Syntax.statement Γ) exit :
  analyze cost state statement = inr exit ->
  statement_certificate cost state statement exit.
Proof. apply analyze_fuel_builds_certificate. Defined.

Theorem analyze_coherent_builds_certificate {Γ} (cost : cost_model) entry
    (statement : Syntax.statement Γ) exit :
  analyze_coherent cost entry statement = inr exit ->
  coherent_statement_certificate cost entry statement exit.
Proof.
  unfold analyze_coherent, check_conditional_masks.
  destruct (analyze cost entry statement) as [error|flat_exit] eqn:Hflat;
    first discriminate.
  destruct (check_conditional_masks_fuel (Syntax.size Γ statement) cost entry
    statement) eqn:Hcoherent; last discriminate.
  intros Hresult. inversion Hresult; subst flat_exit.
  apply coherent_analysis_certificate_of_success.
  - apply analyze_builds_certificate. exact Hflat.
  - exact Hcoherent.
Defined.

(** The proof-facing bridge for the fused executable pass.  Certificate
    construction is deliberately confined to this theorem: the executable
    checker above never unfolds [analyze_builds_certificate]. *)
Lemma analyze_coherent_lifo_builds_certificate {Γ} (cost : cost_model)
    entry (statement : Syntax.statement Γ) exit :
  analyze_coherent_lifo cost entry statement = Some exit ->
  { certificate : coherent_statement_certificate cost entry statement exit &
    coherent_analysis_lifo certificate [] [] }.
Proof.
  unfold analyze_coherent_lifo.
  destruct (analyze_coherent_lifo_fuel (Syntax.size Γ statement) cost entry []
    statement) as [[actual stack_out]|] eqn:Hrun; try discriminate.
  destruct stack_out as [|marker stack_out]; try discriminate.
  intros Hsuccess. inversion Hsuccess; subst actual.
  pose proof (analyze_coherent_lifo_projects cost entry statement exit) as
    Hcoherent.
  assert (Hclosed : analyze_coherent_lifo cost entry statement = Some exit).
  { unfold analyze_coherent_lifo. rewrite Hrun. reflexivity. }
  specialize (Hcoherent Hclosed).
  pose (certificate := analyze_coherent_builds_certificate cost entry
    statement exit Hcoherent).
  exists certificate.
  unfold coherent_analysis_lifo.
  eapply analyze_coherent_lifo_fuel_sound.
  exact Hrun.
Qed.

(** Turn a successful executable analysis into the compact dependent-pair
    interface used by the structural certificate combinators above. *)
Definition certified_run_of_analysis {Γ} (cost : cost_model)
    (entry : analysis_state) (statement : Syntax.statement Γ) exit
    (Hsucceeds : analyze cost entry statement = inr exit) :
  certified_run cost entry statement :=
  @existT analysis_state
    (fun exit => statement_certificate cost entry statement exit) exit
    (analyze_builds_certificate cost entry statement exit Hsucceeds).

End Analysis.
End TypedAnalysisView.
