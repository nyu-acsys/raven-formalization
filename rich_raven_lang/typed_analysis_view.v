From Coq Require Import Bool Lia.
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
| ViewUnfold (invariant : inv_id)
| ViewFold (invariant : inv_id)
| ViewSequence (first second : statement Γ)
| ViewConditional (then_branch else_branch : statement Γ)
| ViewAtomic (body : statement Γ).

Arguments ViewLeaf {_ _}.
Arguments ViewUnfold {_ _} _.
Arguments ViewFold {_ _} _.
Arguments ViewSequence {_ _} _ _.
Arguments ViewConditional {_ _} _ _.
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
| IncompatibleBranches
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
    forall Γ, nat -> analysis_state -> Syntax.statement Γ ->
      analysis_state -> Type :=
| CertLeaf Γ fuel state statement exit :
    Syntax.view Γ statement = ViewLeaf ->
    take_step (cost Γ statement) state = inr exit ->
    analysis_certificate cost Γ (S fuel) state statement exit
| CertUnfold Γ fuel state statement invariant exit :
    Syntax.view Γ statement = ViewUnfold invariant ->
    open_invariant invariant state = inr exit ->
    analysis_certificate cost Γ (S fuel) state statement exit
| CertFold Γ fuel state statement invariant :
    Syntax.view Γ statement = ViewFold invariant ->
    analysis_certificate cost Γ (S fuel) state statement
      (fold_invariant invariant state)
| CertSequence Γ fuel state statement first middle second exit :
    Syntax.view Γ statement = ViewSequence first second ->
    analysis_certificate cost Γ fuel state first middle ->
    analysis_certificate cost Γ fuel middle second exit ->
    analysis_certificate cost Γ (S fuel) state statement exit
| CertConditional Γ fuel state statement then_branch else_branch
    then_exit else_exit :
    Syntax.view Γ statement = ViewConditional then_branch else_branch ->
    analysis_certificate cost Γ fuel state then_branch then_exit ->
    analysis_certificate cost Γ fuel state else_branch else_exit ->
    analysis_open then_exit = analysis_open else_exit ->
    analysis_in_atomic then_exit = analysis_in_atomic else_exit ->
    analysis_certificate cost Γ (S fuel) state statement
      (AnalysisState
        (analysis_mask then_exit ∩ analysis_mask else_exit)
        (analysis_open then_exit)
        (analysis_step_taken then_exit || analysis_step_taken else_exit)
        (analysis_in_atomic then_exit))
| CertAtomic Γ fuel state statement body outer inner :
    Syntax.view Γ statement = ViewAtomic body ->
    take_step AtomicStep state = inr outer ->
    analysis_certificate cost Γ fuel
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body inner ->
    analysis_open inner = analysis_open outer ->
    analysis_certificate cost Γ (S fuel) state statement
      (AnalysisState (analysis_mask inner) (analysis_open inner)
        (analysis_step_taken outer || analysis_step_taken inner)
        (analysis_in_atomic outer)).

Definition statement_certificate {Γ} cost state
    (statement : Syntax.statement Γ) exit :=
  analysis_certificate cost Γ (Syntax.size Γ statement) state statement exit.

Definition access_marker : Type := (inv_id * gset inv_id)%type.

(** Temporary semantic restriction used by the Iris accessor proof.  The
    executable flat analysis deliberately records open declarations as a set,
    matching Raven's unordered source analysis.  This additional certificate
    witnesses that one particular successful run is nevertheless properly
    nested, without baking that restriction into the source language or the
    analyzer result. *)
Fixpoint lifo_certificate {Γ fuel entry statement exit} {cost : cost_model}
    (certificate : analysis_certificate cost Γ fuel entry statement exit)
    (stack_in stack_out : list access_marker) : Prop :=
  match certificate with
  | CertLeaf _ _ _ _ _ _ _ _ => stack_out = stack_in
  | CertUnfold _ _ _ _ _ invariant _ _ _ =>
      stack_out = (invariant, analysis_open entry) :: stack_in
  | CertFold _ _ _ state _ invariant _ =>
      (exists outer_open,
       stack_in = (invariant, outer_open) :: stack_out /\
       invariant ∈ analysis_open state /\
       invariant ∉ outer_open /\
       analysis_open state = {[invariant]} ∪ outer_open) \/
      (stack_out = stack_in /\ invariant ∉ analysis_open state)
  | CertSequence _ _ _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      exists stack_middle,
        lifo_certificate first_certificate stack_in stack_middle /\
        lifo_certificate second_certificate stack_middle stack_out
  | CertConditional _ _ _ _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      lifo_certificate then_certificate stack_in stack_out /\
      lifo_certificate else_certificate stack_in stack_out
  | CertAtomic _ _ _ _ _ _ _ _ _ _ body_certificate _ =>
      lifo_certificate body_certificate stack_in stack_in /\
      stack_out = stack_in
  end.

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
Lemma lifo_certificate_functional {Γ fuel entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ fuel entry statement exit)
    stack_in stack_out1 stack_out2 :
  lifo_certificate certificate stack_in stack_out1 ->
  lifo_certificate certificate stack_in stack_out2 ->
  stack_out1 = stack_out2.
Proof.
  revert stack_in stack_out1 stack_out2.
  induction certificate; simpl; intros stack_in stack_out1 stack_out2 H1 H2.
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
Record access_segment {Γ fuel entry statement exit cost}
    (certificate : analysis_certificate cost Γ fuel entry statement exit)
    (stack_in stack_out : list access_marker) : Prop := {
  access_segment_lifo : lifo_certificate certificate stack_in stack_out;
  access_segment_entry_consistent :
    access_stack_consistent (analysis_open entry) stack_in;
}.

Definition balanced_access_segment {Γ fuel entry statement exit cost}
    (certificate : analysis_certificate cost Γ fuel entry statement exit)
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

Definition well_bracketed_certificate {Γ fuel entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ fuel entry statement exit) : Prop :=
  lifo_certificate certificate [] [].

(** Logical Raven masks that may be available anywhere in a certified
    region.  The semantic translation uses this union to choose one ambient
    Iris mask; individual Raven mask transitions do not themselves enlarge
    or shrink that ambient mask. *)
Fixpoint certificate_footprint {Γ fuel entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ fuel entry statement exit) :
    gset inv_id :=
  analysis_mask entry ∪ analysis_open entry ∪
  analysis_mask exit ∪ analysis_open exit ∪
  match certificate with
  | CertSequence _ _ _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      certificate_footprint first_certificate ∪
      certificate_footprint second_certificate
  | CertConditional _ _ _ _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      certificate_footprint then_certificate ∪
      certificate_footprint else_certificate
  | CertAtomic _ _ _ _ _ _ _ _ _ _ body_certificate _ =>
      certificate_footprint body_certificate
  | _ => ∅
  end.

(** The operational footprint is the set of invariant identifiers at which
    the certificate actually performs an invariant operation.  In
    particular, masks and open sets in the analysis states are deliberately
    not included: they describe availability, rather than physical access.
    Sequence and conditional nodes expose both children, while an atomic
    node exposes its body certificate. *)
Fixpoint certificate_operational_footprint {Γ fuel entry statement exit}
    {cost : cost_model}
    (certificate : analysis_certificate cost Γ fuel entry statement exit) :
    gset inv_id :=
  match certificate with
  | CertUnfold _ _ _ _ _ invariant _ _ _ => {[invariant]}
  | CertFold _ _ _ _ _ invariant _ => {[invariant]}
  | CertSequence _ _ _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      certificate_operational_footprint first_certificate ∪
      certificate_operational_footprint second_certificate
  | CertConditional _ _ _ _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      certificate_operational_footprint then_certificate ∪
      certificate_operational_footprint else_certificate
  | CertAtomic _ _ _ _ _ _ _ _ _ _ body_certificate _ =>
      certificate_operational_footprint body_certificate
  | _ => ∅
  end.

Lemma certificate_sequence_first_operational_footprint_subset
    {Γ fuel entry statement first middle second exit cost}
    (view : Syntax.view Γ statement = ViewSequence first second)
    (first_certificate : analysis_certificate cost Γ fuel entry first middle)
    (second_certificate : analysis_certificate cost Γ fuel middle second exit) :
  certificate_operational_footprint first_certificate ⊆
    certificate_operational_footprint
      (CertSequence cost Γ fuel entry statement first middle second exit
        view first_certificate second_certificate).
Proof. simpl. set_solver. Qed.

Lemma certificate_sequence_second_operational_footprint_subset
    {Γ fuel entry statement first middle second exit cost}
    (view : Syntax.view Γ statement = ViewSequence first second)
    (first_certificate : analysis_certificate cost Γ fuel entry first middle)
    (second_certificate : analysis_certificate cost Γ fuel middle second exit) :
  certificate_operational_footprint second_certificate ⊆
    certificate_operational_footprint
      (CertSequence cost Γ fuel entry statement first middle second exit
        view first_certificate second_certificate).
Proof. simpl. set_solver. Qed.

Lemma certificate_conditional_then_operational_footprint_subset
    {Γ fuel entry statement then_branch else_branch then_exit else_exit cost}
    (view : Syntax.view Γ statement = ViewConditional then_branch else_branch)
    (then_certificate : analysis_certificate cost Γ fuel entry then_branch then_exit)
    (else_certificate : analysis_certificate cost Γ fuel entry else_branch else_exit)
    (open_equal : analysis_open then_exit = analysis_open else_exit)
    (atomic_equal : analysis_in_atomic then_exit = analysis_in_atomic else_exit) :
  certificate_operational_footprint then_certificate ⊆
    certificate_operational_footprint
      (CertConditional cost Γ fuel entry statement then_branch else_branch
        then_exit else_exit view then_certificate else_certificate
        open_equal atomic_equal).
Proof. simpl. set_solver. Qed.

Lemma certificate_conditional_else_operational_footprint_subset
    {Γ fuel entry statement then_branch else_branch then_exit else_exit cost}
    (view : Syntax.view Γ statement = ViewConditional then_branch else_branch)
    (then_certificate : analysis_certificate cost Γ fuel entry then_branch then_exit)
    (else_certificate : analysis_certificate cost Γ fuel entry else_branch else_exit)
    (open_equal : analysis_open then_exit = analysis_open else_exit)
    (atomic_equal : analysis_in_atomic then_exit = analysis_in_atomic else_exit) :
  certificate_operational_footprint else_certificate ⊆
    certificate_operational_footprint
      (CertConditional cost Γ fuel entry statement then_branch else_branch
        then_exit else_exit view then_certificate else_certificate
        open_equal atomic_equal).
Proof. simpl. set_solver. Qed.

Lemma certificate_atomic_body_operational_footprint_subset
    {Γ fuel entry statement body outer inner cost}
    (view : Syntax.view Γ statement = ViewAtomic body)
    (step : take_step AtomicStep entry = inr outer)
    (body_certificate : analysis_certificate cost Γ fuel
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body inner)
    (open_equal : analysis_open inner = analysis_open outer) :
  certificate_operational_footprint body_certificate ⊆
    certificate_operational_footprint
      (CertAtomic cost Γ fuel entry statement body outer inner view step
        body_certificate open_equal).
Proof. simpl. set_solver. Qed.

Lemma certificate_unfold_operational_footprint_mem
    {Γ fuel entry statement invariant exit cost}
    (view : Syntax.view Γ statement = ViewUnfold invariant)
    (step : open_invariant invariant entry = inr exit) :
  invariant ∈ certificate_operational_footprint
    (CertUnfold cost Γ fuel entry statement invariant exit view step).
Proof. simpl. set_solver. Qed.

Lemma certificate_fold_operational_footprint_mem
    {Γ fuel entry statement invariant cost}
    (view : Syntax.view Γ statement = ViewFold invariant) :
  invariant ∈ certificate_operational_footprint
    (CertFold cost Γ fuel entry statement invariant view).
Proof. simpl. set_solver. Qed.

Lemma certificate_entry_subset_footprint {Γ fuel entry statement exit cost}
    (certificate : analysis_certificate cost Γ fuel entry statement exit) :
  analysis_mask entry ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Lemma certificate_exit_subset_footprint {Γ fuel entry statement exit cost}
    (certificate : analysis_certificate cost Γ fuel entry statement exit) :
  analysis_mask exit ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Lemma certificate_entry_open_subset_footprint
    {Γ fuel entry statement exit cost}
    (certificate : analysis_certificate cost Γ fuel entry statement exit) :
  analysis_open entry ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Lemma certificate_exit_open_subset_footprint
    {Γ fuel entry statement exit cost}
    (certificate : analysis_certificate cost Γ fuel entry statement exit) :
  analysis_open exit ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Theorem certificate_replays {Γ fuel} (cost : cost_model) state
    (statement : Syntax.statement Γ) exit :
  analysis_certificate cost Γ fuel state statement exit ->
  analyze_fuel fuel cost state statement = inr exit.
Proof.
  intros certificate. induction certificate; simpl.
  - rewrite e. exact e0.
  - rewrite e. exact e0.
  - rewrite e. reflexivity.
  - rewrite e. rewrite IHcertificate1. exact IHcertificate2.
  - rewrite e. rewrite IHcertificate1. rewrite IHcertificate2.
    rewrite bool_decide_true; first reflexivity. split; assumption.
  - rewrite e. rewrite e0. rewrite IHcertificate.
    rewrite bool_decide_true; first reflexivity. assumption.
Qed.

Theorem certificate_preserves_wf {Γ fuel} (cost : cost_model) state
    (statement : Syntax.statement Γ) exit :
  state_wf state ->
  analysis_certificate cost Γ fuel state statement exit ->
  state_wf exit.
Proof.
  intros Hwf certificate. induction certificate.
  - eapply take_step_preserves_wf; eauto.
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
    {Γ fuel entry statement exit cost}
    (certificate : analysis_certificate cost Γ fuel entry statement exit)
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
    {Γ fuel state statement first middle second exit cost}
    (view : Syntax.view Γ statement = ViewSequence first second)
    (first_certificate : analysis_certificate cost Γ fuel state first middle)
    (second_certificate : analysis_certificate cost Γ fuel middle second exit)
    stack_in stack_middle stack_out :
  access_segment first_certificate stack_in stack_middle ->
  access_segment second_certificate stack_middle stack_out ->
  access_segment
    (CertSequence cost Γ fuel state statement first middle second exit
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
    {Γ fuel state statement then_branch else_branch then_exit else_exit cost}
    (view : Syntax.view Γ statement = ViewConditional then_branch else_branch)
    (then_certificate : analysis_certificate cost Γ fuel state then_branch then_exit)
    (else_certificate : analysis_certificate cost Γ fuel state else_branch else_exit)
    (open_equal : analysis_open then_exit = analysis_open else_exit)
    (atomic_equal : analysis_in_atomic then_exit = analysis_in_atomic else_exit)
    stack_in stack_out :
  access_segment then_certificate stack_in stack_out ->
  access_segment else_certificate stack_in stack_out ->
  access_segment
    (CertConditional cost Γ fuel state statement then_branch else_branch
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
    {Γ fuel state statement body outer inner cost}
    (view : Syntax.view Γ statement = ViewAtomic body)
    (step : take_step AtomicStep state = inr outer)
    (body_certificate : analysis_certificate cost Γ fuel
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body inner)
    (open_equal : analysis_open inner = analysis_open outer)
    stack :
  access_segment body_certificate stack stack ->
  access_segment
    (CertAtomic cost Γ fuel state statement body outer inner view step
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
    {Γ fuel entry statement exit cost}
    (view : Syntax.view Γ statement = ViewLeaf)
    (step : take_step (cost Γ statement) entry = inr exit)
    stack :
  access_stack_consistent (analysis_open entry) stack ->
  access_segment
    (CertLeaf cost Γ fuel entry statement exit view step) stack stack.
Proof.
  intros Hstack. constructor; [simpl; reflexivity|exact Hstack].
Qed.

Lemma access_segment_unfold
    {Γ fuel entry statement invariant exit cost}
    (view : Syntax.view Γ statement = ViewUnfold invariant)
    (step : open_invariant invariant entry = inr exit)
    stack :
  access_stack_consistent (analysis_open entry) stack ->
  access_segment
    (CertUnfold cost Γ fuel entry statement invariant exit view step)
    stack ((invariant, analysis_open entry) :: stack).
Proof.
  intros Hstack. constructor; [simpl; reflexivity|exact Hstack].
Qed.

Lemma access_segment_fold_matched
    {Γ fuel entry statement invariant cost}
    (view : Syntax.view Γ statement = ViewFold invariant)
    outer_open stack :
  invariant ∈ analysis_open entry ->
  invariant ∉ outer_open ->
  analysis_open entry = {[invariant]} ∪ outer_open ->
  access_stack_consistent (analysis_open entry)
    ((invariant, outer_open) :: stack) ->
  access_segment
    (CertFold cost Γ fuel entry statement invariant view)
    ((invariant, outer_open) :: stack) stack.
Proof.
  intros Hmember Hfresh Hopen Hstack.
  constructor.
  - simpl. left. exists outer_open. repeat split; assumption || reflexivity.
  - exact Hstack.
Qed.

Lemma access_segment_fold_fresh
    {Γ fuel entry statement invariant cost}
    (view : Syntax.view Γ statement = ViewFold invariant)
    stack :
  invariant ∉ analysis_open entry ->
  access_stack_consistent (analysis_open entry) stack ->
  access_segment
    (CertFold cost Γ fuel entry statement invariant view) stack stack.
Proof.
  intros Hclosed Hstack.
  constructor.
  - simpl. right. split; [reflexivity|exact Hclosed].
  - exact Hstack.
Qed.

Lemma closed_lifo_is_balanced
    {Γ fuel entry statement exit cost}
    (certificate : analysis_certificate cost Γ fuel entry statement exit) :
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
  analysis_certificate cost Γ fuel state statement exit.
Proof.
  revert Γ state statement exit.
  induction fuel as [|fuel IH]; intros Γ state statement exit Hanalyze;
    simpl in Hanalyze; first discriminate.
  destruct (Syntax.view Γ statement) eqn:Hview.
  - eapply CertLeaf; [exact Hview|exact Hanalyze].
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
Qed.

Corollary analyze_builds_certificate {Γ} (cost : cost_model) state
    (statement : Syntax.statement Γ) exit :
  analyze cost state statement = inr exit ->
  statement_certificate cost state statement exit.
Proof. apply analyze_fuel_builds_certificate. Qed.

End Analysis.
End TypedAnalysisView.
