From Coq Require Import Bool Lia Program.Equality ProofIrrelevance.
From stdpp Require Import gmap.

From raven Require Import verification.expressions.

(** A small boundary between an intrinsically typed statement
    family and the atomicity analyzer.  The analyzer never needs the payload
    of leaves, conditions, or invariant arguments; it needs only this control
    view while retaining the original statement opaquely. *)
Module AnalysisView.

Import Core.


Inductive statement_view (statement : context -> Type) (Γ : context) : Type :=
| ViewLeaf
(* The empty continuation.  Unlike a leaf it is never charged a cost: it is
   the identity on the analysis state by construction. *)
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

(** A statement family together with its control view: the analyzer's
    whole interface to a language. *)
Class AnalysisSyntax := AnalysisSyntaxData {
  syntax_statement : context -> Type;
  syntax_view : forall Γ, syntax_statement Γ -> statement_view syntax_statement Γ;
  syntax_size : forall Γ, syntax_statement Γ -> nat;
  syntax_size_positive : forall Γ (statement : syntax_statement Γ),
    0 < syntax_size Γ statement;
  syntax_sequence_children_smaller : forall Γ statement first second,
    syntax_view Γ statement = ViewSequence first second ->
    syntax_size Γ first < syntax_size Γ statement /\
    syntax_size Γ second < syntax_size Γ statement;
  syntax_conditional_children_smaller :
    forall Γ statement then_branch else_branch,
    syntax_view Γ statement = ViewConditional then_branch else_branch ->
    syntax_size Γ then_branch < syntax_size Γ statement /\
    syntax_size Γ else_branch < syntax_size Γ statement;
  syntax_atomic_body_smaller : forall Γ statement body,
    syntax_view Γ statement = ViewAtomic body ->
    syntax_size Γ body < syntax_size Γ statement;
}.


Section WithSyntax.
Context {Syntax : AnalysisSyntax}.

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
| FuelExhausted.

Record analysis_state := AnalysisState {
  analysis_mask : gset inv_id;
  analysis_open : gset inv_id;
  analysis_step_taken : bool;
  analysis_in_atomic : bool;
}.

Definition state_wf state : Prop :=
  analysis_open state ## analysis_mask state.

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
        if bool_decide (analysis_open state = ∅) then
          match take_plain_step NonAtomicStep state with
          | inl error => inl error
          | inr stepped =>
              if bool_decide (granted ## analysis_open stepped)
              then inr (grant_state granted stepped)
              else inl ProcedureGrantAlreadyOpen
          end
        else inl NonAtomicWhileOpen
      else inl MissingProcedureMask
  | ProcedureSpawnStep required =>
      if bool_decide (required ⊆ analysis_mask state)
      then if bool_decide (analysis_open state = ∅)
        then take_plain_step NonAtomicStep state
        else inl NonAtomicWhileOpen
      else inl MissingProcedureMask
  | NoStep | AtomicStep | NonAtomicStep => take_plain_step cost state
  end.

#[global] Arguments take_step : simpl never.

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
    destruct (bool_decide (analysis_open state = ∅)); last discriminate.
    destruct (take_plain_step NonAtomicStep state) as [error|stepped]
      eqn:Hstep; first discriminate.
    destruct (bool_decide (_ ## _)); last discriminate.
    intros [= <-]. simpl.
    exact (proj2 (take_plain_step_preserves_sets _ _ _ Hstep)).
  - destruct (bool_decide (_ ⊆ _)); last discriminate.
    destruct (bool_decide (analysis_open state = ∅)); last discriminate.
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
    destruct (bool_decide (analysis_open state = ∅)); last discriminate.
    destruct (take_plain_step NonAtomicStep state) as [error|stepped]
      eqn:Hplain; first discriminate.
    destruct (bool_decide (_ ## _)); last discriminate.
    intros [= <-]. simpl.
    exact (take_plain_step_preserves_in_atomic _ _ _ Hplain).
  - destruct (bool_decide (_ ⊆ _)); last discriminate.
    destruct (bool_decide (analysis_open state = ∅)); last discriminate.
    apply take_plain_step_preserves_in_atomic.
Qed.

Lemma take_step_preserves_wf cost state exit :
  state_wf state -> take_step cost state = inr exit -> state_wf exit.
Proof.
  intros Hwf Hstep. unfold take_step in Hstep.
  destruct cost; try (apply take_plain_step_preserves_sets in Hstep as
    [Hmask Hopen]; unfold state_wf in *; now rewrite Hmask, Hopen).
  - destruct (bool_decide (_ ⊆ _)) eqn:Hrequired; last discriminate.
    destruct (bool_decide (analysis_open state = ∅)); last discriminate.
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
    destruct (bool_decide (analysis_open state = ∅)); last discriminate.
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
  destruct (bool_decide (analysis_open state = ∅)); last discriminate.
  destruct (take_plain_step NonAtomicStep state) as [error|stepped]
    eqn:Hplain; first discriminate.
  destruct (bool_decide (granted ## analysis_open stepped)) eqn:Hgrant;
    last discriminate.
  apply bool_decide_eq_true in Hgrant. intros [= <-].
  apply take_plain_step_preserves_sets in Hplain as [Hmask Hopen].
  rewrite Hopen in Hgrant. simpl. repeat split; try assumption.
  - now rewrite Hmask.
Qed.

Lemma procedure_call_step_success_closed required granted state exit :
  take_step (ProcedureCallStep required granted) state = inr exit ->
  analysis_open state = ∅.
Proof.
  unfold take_step.
  destruct (bool_decide (required ⊆ analysis_mask state)); last discriminate.
  destruct (bool_decide (analysis_open state = ∅)) eqn:Hclosed;
    last discriminate.
  intros _. apply bool_decide_eq_true in Hclosed. exact Hclosed.
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
  apply bool_decide_eq_true in Hrequired.
  destruct (bool_decide (analysis_open state = ∅)); last discriminate.
  intros Hplain.
  apply take_plain_step_preserves_sets in Hplain as [Hmask Hopen].
  tauto.
Qed.

Lemma procedure_spawn_step_success_closed required state exit :
  take_step (ProcedureSpawnStep required) state = inr exit ->
  analysis_open state = ∅.
Proof.
  unfold take_step.
  destruct (bool_decide (required ⊆ analysis_mask state)); last discriminate.
  destruct (bool_decide (analysis_open state = ∅)) eqn:Hclosed;
    last discriminate.
  intros _. apply bool_decide_eq_true in Hclosed. exact Hclosed.
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
  intros Hopen _. unfold take_step.
  destruct (bool_decide (required ⊆ analysis_mask state)); last discriminate.
  rewrite bool_decide_false; [discriminate | exact Hopen].
Qed.

Lemma procedure_spawn_rejected_while_open required state exit :
  analysis_open state ≠ ∅ -> analysis_in_atomic state = false ->
  take_step (ProcedureSpawnStep required) state <> inr exit.
Proof.
  intros Hopen _. unfold take_step.
  destruct (bool_decide (required ⊆ analysis_mask state)); last discriminate.
  rewrite bool_decide_false; [discriminate | exact Hopen].
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

(** The cost of each leaf, as the analyzer consults it. *)
Class LeafCost := LeafCostData {
  leaf_cost : forall Γ, syntax_statement Γ -> step_cost;
}.
Context {Cost : LeafCost}.

Fixpoint analyze_fuel {Γ} (fuel : nat)
    (state : analysis_state) (statement : syntax_statement Γ) :
    analysis_error + analysis_state :=
  match fuel with
  | 0 => inl FuelExhausted
  | S fuel' =>
      match syntax_view Γ statement with
      | ViewLeaf => take_step (leaf_cost Γ statement) state
      | ViewDone => inr state
      | ViewUnfold invariant => open_invariant invariant state
      | ViewFold invariant => inr (fold_invariant invariant state)
      | ViewSequence first second =>
          match analyze_fuel fuel' state first with
          | inl error => inl error
          | inr middle => analyze_fuel fuel' middle second
          end
      | ViewConditional then_branch else_branch =>
          match analyze_fuel fuel' state then_branch,
              analyze_fuel fuel' state else_branch with
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
              match analyze_fuel fuel' inner_entry body with
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

Definition analyze {Γ} state (statement : syntax_statement Γ) :=
  analyze_fuel (syntax_size Γ statement) state statement.

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

Inductive analysis_certificate :
    forall Γ, analysis_state -> syntax_statement Γ ->
      analysis_state -> Type :=
| CertLeaf Γ state statement exit :
    syntax_view Γ statement = ViewLeaf ->
    take_step (leaf_cost Γ statement) state = inr exit ->
    analysis_certificate Γ state statement exit
| CertDone Γ state statement :
    syntax_view Γ statement = ViewDone ->
    analysis_certificate Γ state statement state
| CertUnfold Γ state statement invariant exit :
    syntax_view Γ statement = ViewUnfold invariant ->
    open_invariant invariant state = inr exit ->
    analysis_certificate Γ state statement exit
| CertFold Γ state statement invariant :
    syntax_view Γ statement = ViewFold invariant ->
    analysis_certificate Γ state statement
      (fold_invariant invariant state)
| CertSequence Γ state statement first middle second exit :
    syntax_view Γ statement = ViewSequence first second ->
    analysis_certificate Γ state first middle ->
    analysis_certificate Γ middle second exit ->
    analysis_certificate Γ state statement exit
| CertConditional Γ state statement then_branch else_branch
    then_exit else_exit :
    syntax_view Γ statement = ViewConditional then_branch else_branch ->
    analysis_certificate Γ state then_branch then_exit ->
    analysis_certificate Γ state else_branch else_exit ->
    analysis_open then_exit = analysis_open else_exit ->
    analysis_in_atomic then_exit = analysis_in_atomic else_exit ->
    analysis_certificate Γ state statement
      (AnalysisState
        (analysis_mask then_exit ∩ analysis_mask else_exit)
        (analysis_open then_exit)
        (analysis_step_taken then_exit || analysis_step_taken else_exit)
        (analysis_in_atomic then_exit))
| CertAtomic Γ state statement body outer inner :
    syntax_view Γ statement = ViewAtomic body ->
    take_step AtomicStep state = inr outer ->
    analysis_certificate Γ
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body inner ->
    analysis_open inner = analysis_open outer ->
    analysis_certificate Γ state statement
      (AnalysisState (analysis_mask inner) (analysis_open inner)
        (analysis_step_taken outer || analysis_step_taken inner)
        (analysis_in_atomic outer)).

Lemma analysis_certificate_preserves_in_atomic
    {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
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

Definition access_marker : Type := (inv_id * gset inv_id)%type.

(** Temporary semantic restriction used by the Iris accessor proof.  The
    executable flat analysis deliberately records open declarations as a set,
    matching Raven's unordered source analysis.  This additional certificate
    witnesses that one particular successful run is nevertheless properly
    nested, without baking that restriction into the source language or the
    analyzer result. *)
Fixpoint lifo_certificate {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit)
    (stack_in stack_out : list access_marker) : Prop :=
  match certificate with
  | CertLeaf _ _ _ _ _ _ => stack_out = stack_in
  | CertDone _ _ _ _ => stack_out = stack_in
  | CertUnfold _ _ _ invariant _ _ _ =>
      stack_out = (invariant, analysis_open entry) :: stack_in
  | CertFold _ state _ invariant _ =>
      (exists outer_open,
       stack_in = (invariant, outer_open) :: stack_out /\
       invariant ∈ analysis_open state /\
       invariant ∉ outer_open /\
       analysis_open state = {[invariant]} ∪ outer_open) \/
      (stack_out = stack_in /\ invariant ∉ analysis_open state)
  | CertSequence _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      exists stack_middle,
        lifo_certificate first_certificate stack_in stack_middle /\
        lifo_certificate second_certificate stack_middle stack_out
  | CertConditional _ _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      lifo_certificate then_certificate stack_in stack_out /\
      lifo_certificate else_certificate stack_in stack_out
  | CertAtomic _ _ _ _ _ _ _ _ body_certificate _ =>
      lifo_certificate body_certificate stack_in stack_in /\
      stack_out = stack_in
  end.

(** Executable replay of the auxiliary access stack.  This is certification
    of an already-produced analysis certificate, not another statement
    analysis: every branch follows the certificate's constructors and merely
    checks the equalities and membership facts occurring in
    [lifo_certificate]. *)
Fixpoint replay_lifo_certificate {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit)
    (stack_in : list access_marker) : option (list access_marker) :=
  match certificate with
  | CertLeaf _ _ _ _ _ _ => Some stack_in
  | CertDone _ _ _ _ => Some stack_in
  | CertUnfold _ _ _ invariant _ _ _ =>
      Some ((invariant, analysis_open entry) :: stack_in)
  | CertFold _ state _ invariant _ =>
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
  | CertSequence _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      match replay_lifo_certificate first_certificate stack_in with
      | Some stack_middle => replay_lifo_certificate second_certificate stack_middle
      | None => None
      end
  | CertConditional _ _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      match replay_lifo_certificate then_certificate stack_in,
          replay_lifo_certificate else_certificate stack_in with
      | Some then_stack, Some else_stack =>
          if decide (then_stack = else_stack) then Some then_stack else None
      | _, _ => None
      end
  | CertAtomic _ _ _ _ _ _ _ _ body_certificate _ =>
      match replay_lifo_certificate body_certificate stack_in with
      | Some body_stack =>
          if decide (body_stack = stack_in) then Some stack_in else None
      | None => None
      end
  end.

Lemma replay_lifo_certificate_sound {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit)
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
    [analyze_builds_certificate]. *)
Fixpoint analyze_lifo_fuel {Γ} (fuel : nat)
    (state : analysis_state) (stack : list access_marker)
    (statement : syntax_statement Γ) :
    option (analysis_state * list access_marker) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match syntax_view Γ statement with
      | ViewLeaf =>
          match take_step (leaf_cost Γ statement) state with
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
          match analyze_lifo_fuel fuel' state stack first with
          | Some (middle, stack_middle) =>
              analyze_lifo_fuel fuel' middle stack_middle second
          | None => None
          end
      | ViewConditional then_branch else_branch =>
          match analyze_lifo_fuel fuel' state stack then_branch,
              analyze_lifo_fuel fuel' state stack else_branch with
          | Some (then_exit, then_stack), Some (else_exit, else_stack) =>
              if decide
                  (analysis_open then_exit = analysis_open else_exit /\
                   analysis_in_atomic then_exit = analysis_in_atomic else_exit /\
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
              match analyze_lifo_fuel fuel' inner_entry stack body with
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

Definition analyze_lifo {Γ}
    (state : analysis_state) (statement : syntax_statement Γ) :
    option analysis_state :=
  match analyze_lifo_fuel (syntax_size Γ statement) state []
      statement with
  | Some (exit, []) => Some exit
  | _ => None
  end.

Lemma analyze_lifo_fuel_projects {Γ} fuel
    (state : analysis_state) (stack : list access_marker)
    (statement : syntax_statement Γ) exit stack_out :
  analyze_lifo_fuel fuel state stack statement =
    Some (exit, stack_out) ->
  analyze_fuel fuel state statement = inr exit.
Proof.
  revert Γ state stack statement exit stack_out.
  induction fuel as [|fuel IH];
    intros Γ state stack statement exit stack_out Hrun; simpl in Hrun;
    first discriminate.
  destruct (syntax_view Γ statement) eqn:Hview; simpl in Hrun.
  - destruct (take_step (leaf_cost Γ statement) state) as [error|actual]
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
  - destruct (analyze_lifo_fuel fuel state stack first) as
      [[middle stack_middle]|] eqn:Hfirst; try discriminate.
    specialize (IH _ state stack first middle stack_middle Hfirst) as Hfirst'.
    specialize (IH _ middle stack_middle second exit stack_out Hrun) as Hsecond'.
    simpl. rewrite Hview, Hfirst'. exact Hsecond'.
  - destruct (analyze_lifo_fuel fuel state stack then_branch) as
      [[then_exit then_stack]|] eqn:Hthen; try discriminate.
    destruct (analyze_lifo_fuel fuel state stack else_branch) as
      [[else_exit else_stack]|] eqn:Helse; try discriminate.
    destruct (decide
      (analysis_open then_exit = analysis_open else_exit /\
       analysis_in_atomic then_exit = analysis_in_atomic else_exit /\
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
    destruct (analyze_lifo_fuel fuel
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

Lemma analyze_lifo_projects {Γ}
    (state : analysis_state) (statement : syntax_statement Γ) exit :
  analyze_lifo state statement = Some exit ->
  analyze state statement = inr exit.
Proof.
  unfold analyze_lifo.
  destruct (analyze_lifo_fuel (syntax_size Γ statement) state []
    statement) as [[actual stack_out]|] eqn:Hrun; try discriminate.
  destruct stack_out as [|marker stack_out]; try discriminate.
  intros Hsuccess. inversion Hsuccess; subst actual.
  exact (analyze_lifo_fuel_projects _ state [] statement exit [] Hrun).
Qed.

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
    (certificate : analysis_certificate Γ entry statement exit)
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

(** Logical Raven masks that may be available anywhere in a certified
    region.  The semantic translation uses this union to choose one ambient
    Iris mask; individual Raven mask transitions do not themselves enlarge
    or shrink that ambient mask. *)
Fixpoint certificate_footprint {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
    gset inv_id :=
  analysis_mask entry ∪ analysis_open entry ∪
  analysis_mask exit ∪ analysis_open exit ∪
  match certificate with
  | CertSequence _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      certificate_footprint first_certificate ∪
      certificate_footprint second_certificate
  | CertConditional _ _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      certificate_footprint then_certificate ∪
      certificate_footprint else_certificate
  | CertAtomic _ _ _ _ _ _ _ _ body_certificate _ =>
      certificate_footprint body_certificate
  | _ => ∅
  end.

Lemma certificate_entry_subset_footprint {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  analysis_mask entry ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Lemma certificate_exit_subset_footprint {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  analysis_mask exit ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Lemma certificate_entry_open_subset_footprint
    {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  analysis_open entry ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Lemma certificate_exit_open_subset_footprint
    {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  analysis_open exit ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Fixpoint certificate_height {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) : nat :=
  match certificate with
  | CertLeaf _ _ _ _ _ _ => 1
  | CertDone _ _ _ _ => 1
  | CertUnfold _ _ _ _ _ _ _ => 1
  | CertFold _ _ _ _ _ => 1
  | CertSequence _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      S (Nat.max (certificate_height first_certificate)
        (certificate_height second_certificate))
  | CertConditional _ _ _ _ _ _ _ _ then_certificate else_certificate _ _ =>
      S (Nat.max (certificate_height then_certificate)
        (certificate_height else_certificate))
  | CertAtomic _ _ _ _ _ _ _ _ body_certificate _ =>
      S (certificate_height body_certificate)
  end.

Lemma analyze_fuel_succ {Γ fuel} state
    (statement : syntax_statement Γ) exit :
  analyze_fuel fuel state statement = inr exit ->
  analyze_fuel (S fuel) state statement = inr exit.
Proof.
  revert Γ state statement exit.
  induction fuel as [|fuel IH]; intros Γ state statement exit Hrun;
    simpl in Hrun |- *; first discriminate.
  destruct (syntax_view Γ statement) eqn:Hview; simpl in Hrun |- *.
  - exact Hrun.
  - exact Hrun.
  - exact Hrun.
  - exact Hrun.
  - destruct (analyze_fuel fuel state first) as [error|middle]
      eqn:Hfirst; try discriminate.
    eapply IH in Hfirst.
    eapply IH in Hrun.
    change (analyze_fuel (S fuel) state first = inr middle) in Hfirst.
    change (analyze_fuel (S fuel) middle second = inr exit) in Hrun.
    change (match analyze_fuel (S fuel) state first with
      | inl error => inl error
      | inr middle => analyze_fuel (S fuel) middle second
      end = inr exit).
    rewrite Hfirst. exact Hrun.
  - destruct (analyze_fuel fuel state then_branch) as [error|then_exit]
      eqn:Hthen; try discriminate.
    destruct (analyze_fuel fuel state else_branch) as [error|else_exit]
      eqn:Helse; try discriminate.
    destruct (bool_decide
      (analysis_open then_exit = analysis_open else_exit /\
       analysis_in_atomic then_exit = analysis_in_atomic else_exit)) eqn:Hjoin;
      try discriminate.
    eapply IH in Hthen. eapply IH in Helse.
    change (analyze_fuel (S fuel) state then_branch = inr then_exit)
      in Hthen.
    change (analyze_fuel (S fuel) state else_branch = inr else_exit)
      in Helse.
    change (match analyze_fuel (S fuel) state then_branch,
      analyze_fuel (S fuel) state else_branch with
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
    destruct (analyze_fuel fuel
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body) as [error|inner]
      eqn:Hbody; try discriminate.
    destruct (bool_decide (analysis_open inner = analysis_open outer)) eqn:Hclose;
      try discriminate.
    eapply IH in Hbody.
    change (analyze_fuel (S fuel)
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body = inr inner) in Hbody.
    change (match analyze_fuel (S fuel)
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

Lemma analyze_fuel_monotone {Γ fuel target} state
    (statement : syntax_statement Γ) exit :
  fuel <= target ->
  analyze_fuel fuel state statement = inr exit ->
  analyze_fuel target state statement = inr exit.
Proof.
  intros Hle Hrun. induction Hle.
  - exact Hrun.
  - apply analyze_fuel_succ. exact IHHle.
Qed.

Lemma certificate_replays_height {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  analyze_fuel (certificate_height certificate) entry statement = inr exit.
Proof.
  induction certificate; simpl.
  - rewrite e. exact e0.
  - rewrite e. reflexivity.
  - rewrite e. exact e0.
  - rewrite e. reflexivity.
  - rewrite e.
    rewrite (analyze_fuel_monotone _ _ _
      (Nat.le_max_l _ _) IHcertificate1).
    exact (analyze_fuel_monotone _ _ _
      (Nat.le_max_r _ _) IHcertificate2).
  - rewrite e.
    rewrite (analyze_fuel_monotone _ _ _
      (Nat.le_max_l _ _) IHcertificate1).
    rewrite (analyze_fuel_monotone _ _ _
      (Nat.le_max_r _ _) IHcertificate2).
    rewrite bool_decide_true; [reflexivity|]. split; assumption.
  - rewrite e, e0.
    rewrite IHcertificate.
    rewrite bool_decide_true; [reflexivity|exact e1].
Qed.

Lemma certificate_height_le_size {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  certificate_height certificate <= syntax_size Γ statement.
Proof.
  induction certificate; simpl.
  - pose proof (syntax_size_positive Γ statement). lia.
  - pose proof (syntax_size_positive Γ statement). lia.
  - pose proof (syntax_size_positive Γ statement). lia.
  - pose proof (syntax_size_positive Γ statement). lia.
  - pose proof (syntax_sequence_children_smaller Γ statement first second e)
      as [Hfirst Hsecond].
    lia.
  - pose proof (syntax_conditional_children_smaller Γ statement then_branch
      else_branch e) as [Hthen Helse].
    lia.
  - pose proof (syntax_atomic_body_smaller Γ statement body e) as Hbody.
    lia.
Qed.

(** Invariants a statement may add to the available mask: fold targets and
    procedure-call grants. *)
Definition step_cost_grants (cost : step_cost) : gset inv_id :=
  match cost with
  | ProcedureCallStep _ granted => granted
  | _ => ∅
  end.

Fixpoint statement_allocations_fuel {Γ} (fuel : nat)
    (statement : syntax_statement Γ) : gset inv_id :=
  match fuel with
  | 0 => ∅
  | S fuel' =>
      match syntax_view Γ statement with
      | ViewLeaf => step_cost_grants (leaf_cost Γ statement)
      | ViewFold invariant => {[invariant]}
      | ViewSequence first second =>
          statement_allocations_fuel fuel' first ∪
            statement_allocations_fuel fuel' second
      | ViewConditional then_branch else_branch =>
          statement_allocations_fuel fuel' then_branch ∪
            statement_allocations_fuel fuel' else_branch
      | ViewStructuredAccess _ body | ViewAtomic body =>
          statement_allocations_fuel fuel' body
      | ViewDone | ViewUnfold _ => ∅
      end
  end.

Definition statement_allocations {Γ} (statement : syntax_statement Γ) :
    gset inv_id :=
  statement_allocations_fuel (syntax_size Γ statement) statement.

Lemma take_step_resources_bound cost state exit :
  take_step cost state = inr exit ->
  analysis_mask exit ∪ analysis_open exit ⊆
    analysis_mask state ∪ analysis_open state ∪ step_cost_grants cost.
Proof.
  intros Hstep. destruct cost; simpl.
  1-3: apply take_plain_step_preserves_sets in Hstep as [Hmask Hopen];
    rewrite Hmask, Hopen; set_solver.
  - apply procedure_call_step_success in Hstep as (_ & _ & Hmask & Hopen).
    rewrite Hmask, Hopen. set_solver.
  - apply procedure_spawn_step_success in Hstep as (_ & Hmask & Hopen).
    rewrite Hmask, Hopen. set_solver.
Qed.

Lemma certificate_footprint_allocations_fuel {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) fuel :
  certificate_height certificate <= fuel ->
  certificate_footprint certificate ⊆
    analysis_mask entry ∪ analysis_open entry ∪
      statement_allocations_fuel fuel statement.
Proof.
  revert fuel.
  induction certificate; intros [|fuel] Hheight; simpl in Hheight;
    try lia; cbn [statement_allocations_fuel certificate_footprint];
    rewrite e.
  - pose proof (take_step_resources_bound _ _ _ e0). set_solver.
  - set_solver.
  - apply open_invariant_success in e0 as (_ & Havailable & Hmask & Hopen).
    rewrite Hmask, Hopen. set_solver.
  - unfold fold_invariant.
    destruct (bool_decide (invariant ∈ analysis_open state)); simpl;
      set_solver.
  - pose proof (IHcertificate1 fuel ltac:(lia)) as Hfirst.
    pose proof (IHcertificate2 fuel ltac:(lia)) as Hsecond.
    pose proof (certificate_exit_subset_footprint certificate1).
    pose proof (certificate_exit_open_subset_footprint certificate1).
    pose proof (certificate_exit_subset_footprint certificate2).
    pose proof (certificate_exit_open_subset_footprint certificate2).
    set_solver.
  - pose proof (IHcertificate1 fuel ltac:(lia)) as Hthen.
    pose proof (IHcertificate2 fuel ltac:(lia)) as Helse.
    pose proof (certificate_exit_subset_footprint certificate1).
    pose proof (certificate_exit_open_subset_footprint certificate1).
    simpl. set_solver.
  - pose proof (IHcertificate fuel ltac:(lia)) as Hbody.
    apply atomic_step_preserves_sets in e0 as [Hmask Hopen].
    pose proof (certificate_exit_subset_footprint certificate).
    pose proof (certificate_exit_open_subset_footprint certificate).
    simpl in *. set_solver.
Qed.

(** Every invariant in a certificate footprint is available or open on entry,
    or allocated by the statement.  This bound is independent of how
    conditional joins restrict the exit mask. *)
Lemma certificate_footprint_allocations {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  certificate_footprint certificate ⊆
    analysis_mask entry ∪ analysis_open entry ∪
      statement_allocations statement.
Proof.
  apply certificate_footprint_allocations_fuel.
  apply certificate_height_le_size.
Qed.

Theorem certificate_replays {Γ} state
    (statement : syntax_statement Γ) exit :
  analysis_certificate Γ state statement exit ->
  analyze state statement = inr exit.
Proof.
  intros certificate. unfold analyze.
  eapply analyze_fuel_monotone;
    [exact (certificate_height_le_size certificate)|].
  exact (certificate_replays_height certificate).
Qed.

Lemma analysis_certificate_exit_unique
    {Γ entry statement exit1 exit2}
    (certificate1 : analysis_certificate Γ entry statement exit1)
    (certificate2 : analysis_certificate Γ entry statement exit2) :
  exit1 = exit2.
Proof.
  pose proof (certificate_replays entry statement exit1 certificate1)
    as Hreplay1.
  pose proof (certificate_replays entry statement exit2 certificate2)
    as Hreplay2.
  congruence.
Qed.

Lemma analyze_fuel_certificate_exit {Γ fuel entry statement actual expected} :
  analyze_fuel fuel entry statement = inr actual ->
  analysis_certificate Γ entry statement expected ->
  actual = expected.
Proof.
  intros Hrun certificate.
  pose proof (analyze_fuel_monotone entry statement actual
    (Nat.le_max_l fuel (certificate_height certificate)) Hrun) as Hactual.
  pose proof (analyze_fuel_monotone entry statement expected
    (Nat.le_max_r fuel (certificate_height certificate))
    (certificate_replays_height certificate)) as Hexpected.
  congruence.
Qed.

Lemma analyze_lifo_fuel_replays {Γ fuel entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit)
    stack_in stack_out :
  analyze_lifo_fuel fuel entry stack_in statement =
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
    destruct (analyze_lifo_fuel fuel state stack_in first) as
      [[actual_middle stack_middle]|] eqn:Hfirst; try discriminate.
    assert (Hmiddle : actual_middle = middle).
    { pose proof (analyze_lifo_fuel_projects _ state stack_in
        first actual_middle stack_middle Hfirst) as Hactual.
      exact (analyze_fuel_certificate_exit Hactual certificate1). }
    subst actual_middle.
    specialize (IHcertificate1 _ _ _ Hfirst) as Hfirst_replay.
    specialize (IHcertificate2 _ _ _ Hrun) as Hsecond_replay.
    rewrite Hfirst_replay. exact Hsecond_replay.
  - intros [|fuel] stack_in stack_out Hrun; cbn in Hrun |- *;
      [discriminate|].
    rewrite e in Hrun.
    destruct (analyze_lifo_fuel fuel state stack_in then_branch) as
      [[actual_then then_stack]|] eqn:Hthen; try discriminate.
    destruct (analyze_lifo_fuel fuel state stack_in else_branch) as
      [[actual_else else_stack]|] eqn:Helse; try discriminate.
    assert (Hthen_exit : actual_then = then_exit).
    { pose proof (analyze_lifo_fuel_projects _ state stack_in
        then_branch actual_then then_stack Hthen) as Hactual.
      exact (analyze_fuel_certificate_exit Hactual certificate1). }
    assert (Helse_exit : actual_else = else_exit).
    { pose proof (analyze_lifo_fuel_projects _ state stack_in
        else_branch actual_else else_stack Helse) as Hactual.
      exact (analyze_fuel_certificate_exit Hactual certificate2). }
    subst actual_then. subst actual_else.
    destruct (decide
      (analysis_open then_exit = analysis_open else_exit /\
       analysis_in_atomic then_exit = analysis_in_atomic else_exit /\
       then_stack = else_stack)) as [Hjoin|Hjoin]; try discriminate.
    inversion Hrun; subst stack_out.
    destruct Hjoin as [_ [_ Hstacks]].
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
    destruct (analyze_lifo_fuel fuel
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) stack_in body) as
      [[actual_inner body_stack]|] eqn:Hbody; try discriminate.
    assert (Hinner : actual_inner = inner).
    { pose proof (analyze_lifo_fuel_projects _
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

Lemma analyze_lifo_fuel_sound {Γ fuel entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit)
    stack_in stack_out :
  analyze_lifo_fuel fuel entry stack_in statement =
    Some (exit, stack_out) ->
  lifo_certificate certificate stack_in stack_out.
Proof.
  intros Hrun.
  apply replay_lifo_certificate_sound.
  eapply analyze_lifo_fuel_replays; exact Hrun.
Qed.

(** For fixed public indices, successful analyzer certificates carry no additional
    computational choice.  This lets later certified transformations use a
    canonical certificate construction without introducing a parallel plan
    object merely to remember its proof fields. *)
Lemma analysis_certificate_unique
    {Γ entry statement exit}
    (certificate1 certificate2 :
      analysis_certificate Γ entry statement exit) :
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

Theorem certificate_preserves_wf {Γ} state
    (statement : syntax_statement Γ) exit :
  state_wf state ->
  analysis_certificate Γ state statement exit ->
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

Theorem analyze_fuel_builds_certificate {Γ fuel} state
    (statement : syntax_statement Γ) exit :
  analyze_fuel fuel state statement = inr exit ->
  analysis_certificate Γ state statement exit.
Proof.
  revert Γ state statement exit.
  induction fuel as [|fuel IH]; intros Γ state statement exit Hanalyze;
    simpl in Hanalyze; first discriminate.
  destruct (syntax_view Γ statement) eqn:Hview.
  - eapply CertLeaf; [exact Hview|exact Hanalyze].
  - inversion Hanalyze; subst exit. eapply CertDone. exact Hview.
  - eapply CertUnfold; [exact Hview|exact Hanalyze].
  - inversion Hanalyze; subst exit. eapply CertFold. exact Hview.
  - destruct (analyze_fuel fuel state first) as [error|middle] eqn:Hfirst;
      try discriminate.
    eapply CertSequence; [exact Hview|eapply IH|eapply IH]; eauto.
  - destruct (analyze_fuel fuel state then_branch) as [error|then_exit] eqn:Hthen;
      try discriminate.
    destruct (analyze_fuel fuel state else_branch) as [error|else_exit] eqn:Helse;
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
    destruct (analyze_fuel fuel
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body) as [error|inner] eqn:Hbody;
      try discriminate.
    destruct (bool_decide (analysis_open inner = analysis_open outer)) eqn:Hscope;
      last discriminate.
    apply bool_decide_eq_true in Hscope.
    inversion Hanalyze; subst exit.
    eapply CertAtomic; eauto.
Defined.

Corollary analyze_builds_certificate {Γ} state
    (statement : syntax_statement Γ) exit :
  analyze state statement = inr exit ->
  analysis_certificate Γ state statement exit.
Proof. apply analyze_fuel_builds_certificate. Defined.

(** The proof-facing bridge for the fused executable pass.  Certificate
    construction is deliberately confined to this theorem: the executable
    checker above never unfolds [analyze_builds_certificate]. *)
Lemma analyze_lifo_builds_certificate {Γ}
    entry (statement : syntax_statement Γ) exit :
  analyze_lifo entry statement = Some exit ->
  { certificate : analysis_certificate Γ entry statement exit &
    lifo_certificate certificate [] [] }.
Proof.
  unfold analyze_lifo.
  destruct (analyze_lifo_fuel (syntax_size Γ statement) entry []
    statement) as [[actual stack_out]|] eqn:Hrun; try discriminate.
  destruct stack_out as [|marker stack_out]; try discriminate.
  intros Hsuccess. inversion Hsuccess; subst actual.
  assert (Hclosed : analyze_lifo entry statement = Some exit).
  { unfold analyze_lifo. rewrite Hrun. reflexivity. }
  pose (certificate := analyze_builds_certificate entry statement exit
    (analyze_lifo_projects entry statement exit Hclosed)).
  exists certificate.
  eapply analyze_lifo_fuel_sound.
  exact Hrun.
Qed.

End WithSyntax.
End AnalysisView.
