From Coq Require Import Bool List PArith.
From stdpp Require Import gmap.

From raven_iris.rich_raven_lang Require Import
  typed_core typed_analysis_view typed_assertion typed_ir typed_hoare.

(** The first certified-analysis layer deliberately uses the flat invariant
    masks of the current Rocq logic.  Argument-prefix entries, snapshots, and
    atomic-update tokens refine this state later; they are not needed to state
    the control-flow and one-step invariants. *)
Module TypedAtomicity.

Import TypedCore TypedIR.

Module Make (RAs : RA_VALUE_CONFIG) (Logic : TypedAssertion.LOGIC_SIGNATURE).
Module Hoare := TypedHoare.Make RAs Logic.
Module IR := Hoare.IR.
Module Core := IR.Core.
Module Assertions := IR.Assertions.
Import Core Assertions IR.

Module ViewSyntax <: TypedAnalysisView.ANALYSIS_SYNTAX.
  Definition statement := IR.stmt.

  Definition view {Γ} (statement : statement Γ) :=
    match statement with
    | TUnfold _ invariant _ => TypedAnalysisView.ViewUnfold invariant
    | TFold _ invariant _ => TypedAnalysisView.ViewFold invariant
    | TSeq _ first second => TypedAnalysisView.ViewSequence first second
    | TIf _ _ then_branch else_branch =>
        TypedAnalysisView.ViewConditional then_branch else_branch
    | TAtomic _ body => TypedAnalysisView.ViewAtomic body
    | _ => TypedAnalysisView.ViewLeaf
    end.

  Fixpoint size {Γ} (statement : statement Γ) : nat :=
    match statement with
    | TSeq _ first second | TIf _ _ first second =>
        S (size first + size second)
    | TAtomic _ body => S (size body)
    | _ => 1
    end.

  Lemma size_positive Γ (statement : statement Γ) : 0 < size statement.
  Proof. induction statement; simpl; lia. Qed.

  Lemma sequence_children_smaller (Γ : context) (statement first second : statement Γ) :
    view statement = TypedAnalysisView.ViewSequence first second ->
    size first < size statement /\ size second < size statement.
  Proof. destruct statement; cbn; intros Hview; try discriminate.
    inversion Hview; subst. lia. Qed.

  Lemma conditional_children_smaller (Γ : context)
      (statement then_branch else_branch : statement Γ) :
    view statement = TypedAnalysisView.ViewConditional then_branch else_branch ->
    size then_branch < size statement /\ size else_branch < size statement.
  Proof. destruct statement; cbn; intros Hview; try discriminate.
    inversion Hview; subst. lia. Qed.

  Lemma atomic_body_smaller (Γ : context) (statement body : statement Γ) :
    view statement = TypedAnalysisView.ViewAtomic body ->
    size body < size statement.
  Proof. destruct statement; cbn; intros Hview; try discriminate.
    inversion Hview; subst. lia. Qed.
End ViewSyntax.

Module ViewAnalysis := TypedAnalysisView.Analysis ViewSyntax.

Inductive step_cost :=
| NoStep
| AtomicStep
| NonAtomicStep.

Inductive analysis_error :=
| MissingInvariant (invariant : inv_id)
| ReentrantInvariant (invariant : inv_id)
| SecondAtomicStep
| NonAtomicWhileOpen
| AtomicBlockLeaksAccess
| IncompatibleBranches.

Record analysis_state := AnalysisState {
  analysis_mask : gset inv_id;
  analysis_open : gset inv_id;
  analysis_step_taken : bool;
  analysis_in_atomic : bool;
}.

Definition state_wf (state : analysis_state) : Prop :=
  analysis_open state ## analysis_mask state.

(** Program-dependent classification is kept outside the generic analyzer.
    In particular, trusted atomic blocks are handled structurally below and
    do not obtain their status from this classifier. *)
Definition cost_model := forall Γ, stmt Γ -> step_cost.

Definition take_step (cost : step_cost) (state : analysis_state) :
    analysis_error + analysis_state :=
  if analysis_in_atomic state || bool_decide (analysis_open state = ∅) then
    inr state
  else
    match cost with
    | NoStep => inr state
    | AtomicStep =>
        if analysis_step_taken state then inl SecondAtomicStep
        else inr (AnalysisState (analysis_mask state) (analysis_open state)
          true false)
    | NonAtomicStep => inl NonAtomicWhileOpen
    end.

Definition open_invariant (invariant : inv_id) (state : analysis_state) :
    analysis_error + analysis_state :=
  if bool_decide (invariant ∈ analysis_open state) then
    inl (ReentrantInvariant invariant)
  else if bool_decide (invariant ∈ analysis_mask state) then
    inr (AnalysisState
      (analysis_mask state ∖ {[invariant]})
      ({[invariant]} ∪ analysis_open state)
      (analysis_step_taken state) (analysis_in_atomic state))
  else inl (MissingInvariant invariant).

(** In the flat model, a fold closes the unique open instance of its
    declaration when present; otherwise it establishes a fresh instance and
    grants its mask entry. *)
Definition fold_invariant (invariant : inv_id) (state : analysis_state) :
    analysis_state :=
  if bool_decide (invariant ∈ analysis_open state) then
    let remaining := analysis_open state ∖ {[invariant]} in
    AnalysisState ({[invariant]} ∪ analysis_mask state) remaining
      (if bool_decide (remaining = ∅) then false
       else analysis_step_taken state)
      (analysis_in_atomic state)
  else
    AnalysisState ({[invariant]} ∪ analysis_mask state)
      (analysis_open state) (analysis_step_taken state)
      (analysis_in_atomic state).

Fixpoint analyze {Γ} (cost : cost_model) (state : analysis_state)
    (statement : stmt Γ) : analysis_error + analysis_state :=
  match statement with
  | TUnfold _ invariant _ => open_invariant invariant state
  | TFold _ invariant _ => inr (fold_invariant invariant state)
  | TSeq _ first second =>
      match analyze cost state first with
      | inl error => inl error
      | inr middle => analyze cost middle second
      end
  | TIf _ _ then_branch else_branch =>
      match analyze cost state then_branch, analyze cost state else_branch with
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
  | TAtomic _ body =>
      match take_step AtomicStep state with
      | inl error => inl error
      | inr outer =>
          let inner_entry := AnalysisState (analysis_mask outer)
            (analysis_open outer) (analysis_step_taken outer) true in
          match analyze cost inner_entry body with
          | inl error => inl error
          | inr inner =>
              if bool_decide (analysis_open inner = analysis_open outer) then
                inr (AnalysisState (analysis_mask inner) (analysis_open inner)
                  (analysis_step_taken outer || analysis_step_taken inner)
                  (analysis_in_atomic outer))
              else inl AtomicBlockLeaksAccess
          end
      end
  | _ => take_step (cost Γ statement) state
  end.

Definition analysis_succeeds {Γ} (cost : cost_model)
    (entry : analysis_state) (statement : stmt Γ) (exit : analysis_state) :
    Prop := analyze cost entry statement = inr exit.

Definition cost_leaf {Γ} (statement : stmt Γ) : bool :=
  match statement with
  | TUnfold _ _ _ | TFold _ _ _ | TIf _ _ _ _ | TSeq _ _ _
  | TAtomic _ _ => false
  | _ => true
  end.

(** A successful analyzer run can be reified as this tree.  Unlike the final
    Iris region interpreter, the certificate is purely syntactic: it records
    the access context and step state at every sequencing, branch, and trusted
    atomic-block boundary. *)
Inductive analysis_certificate (cost : cost_model) :
    forall Γ, analysis_state -> stmt Γ -> analysis_state -> Type :=
| CertLeaf Γ state (statement : stmt Γ) exit :
    cost_leaf statement = true ->
    take_step (cost Γ statement) state = inr exit ->
    analysis_certificate cost Γ state statement exit
| CertUnfold Γ state node invariant arguments exit :
    open_invariant invariant state = inr exit ->
    analysis_certificate cost Γ state
      (TUnfold node invariant arguments) exit
| CertFold Γ state node invariant arguments :
    analysis_certificate cost Γ state (TFold node invariant arguments)
      (fold_invariant invariant state)
| CertSeq Γ state node first middle second exit :
    analysis_certificate cost Γ state first middle ->
    analysis_certificate cost Γ middle second exit ->
    analysis_certificate cost Γ state (TSeq node first second) exit
| CertIf Γ state node condition then_branch else_branch then_exit else_exit :
    analysis_certificate cost Γ state then_branch then_exit ->
    analysis_certificate cost Γ state else_branch else_exit ->
    analysis_open then_exit = analysis_open else_exit ->
    analysis_in_atomic then_exit = analysis_in_atomic else_exit ->
    analysis_certificate cost Γ state
      (TIf node condition then_branch else_branch)
      (AnalysisState
        (analysis_mask then_exit ∩ analysis_mask else_exit)
        (analysis_open then_exit)
        (analysis_step_taken then_exit || analysis_step_taken else_exit)
        (analysis_in_atomic then_exit))
| CertAtomic Γ state node body outer inner :
    take_step AtomicStep state = inr outer ->
    analysis_certificate cost Γ
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) body inner ->
    analysis_open inner = analysis_open outer ->
    analysis_certificate cost Γ state (TAtomic node body)
      (AnalysisState (analysis_mask inner) (analysis_open inner)
        (analysis_step_taken outer || analysis_step_taken inner)
        (analysis_in_atomic outer)).

Arguments CertLeaf {_ _ _ _ _} _ _.
Arguments CertUnfold {_ _ _ _ _ _ _} _.
Arguments CertFold {_ _ _ _ _ _}.
Arguments CertSeq {_ _ _ _ _ _ _ _} _ _.
Arguments CertIf {_ _ _ _ _ _ _ _ _} _ _ _ _.
Arguments CertAtomic {_ _ _ _ _ _} _ _ _.

Definition callable_entry (mask : gset inv_id) : analysis_state :=
  AnalysisState mask ∅ false false.

Definition callable_accepted {Γ} (cost : cost_model) (mask : gset inv_id)
    (statement : stmt Γ) : Prop :=
  exists exit,
    analysis_succeeds cost (callable_entry mask) statement exit /\
    analysis_open exit = ∅.

Lemma take_step_when_closed cost state :
  analysis_open state = ∅ -> take_step cost state = inr state.
Proof.
  intros Hclosed. unfold take_step. rewrite Hclosed.
  rewrite bool_decide_true; last reflexivity. destruct (analysis_in_atomic state);
    reflexivity.
Qed.

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

Lemma fold_open_invariant_removes invariant state :
  invariant ∈ analysis_open state ->
  analysis_open (fold_invariant invariant state) =
    analysis_open state ∖ {[invariant]}.
Proof.
  intros Hmember. unfold fold_invariant.
  rewrite bool_decide_true; last exact Hmember. reflexivity.
Qed.

Lemma take_step_preserves_sets cost state exit :
  take_step cost state = inr exit ->
  analysis_mask exit = analysis_mask state /\
  analysis_open exit = analysis_open state.
Proof.
  unfold take_step.
  destruct (analysis_in_atomic state ||
    bool_decide (analysis_open state = ∅)); first by intros [= <-].
  destruct cost; try by intros [= <-].
  destruct (analysis_step_taken state); first discriminate.
  intros Hinr. inversion Hinr. done.
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

Theorem analyze_preserves_wf {Γ} (cost : cost_model) state
    (statement : stmt Γ) exit :
  state_wf state -> analyze cost state statement = inr exit -> state_wf exit.
Proof.
  revert state exit.
  induction statement; intros state exit Hwf Hanalyze; simpl in Hanalyze;
    try match goal with
    | H : take_step _ _ = inr _ |- _ =>
        apply take_step_preserves_sets in H as [Hmask Hopen];
        unfold state_wf in *; rewrite Hmask; rewrite Hopen; exact Hwf
    end.
  - eapply open_invariant_preserves_wf; eauto.
  - inversion Hanalyze; subst exit. apply fold_invariant_preserves_wf. exact Hwf.
  - destruct (analyze cost state statement1) as [error|then_state] eqn:Hthen;
      try discriminate.
    destruct (analyze cost state statement2) as [error|else_state] eqn:Helse;
      try discriminate.
    destruct (bool_decide
      (analysis_open then_state = analysis_open else_state /\
       analysis_in_atomic then_state = analysis_in_atomic else_state)) eqn:Hjoin;
      last discriminate.
    inversion Hanalyze; subst exit. cbn.
    specialize (IHstatement1 state then_state Hwf Hthen).
    unfold state_wf in IHstatement1 |- *.
    rewrite elem_of_disjoint in IHstatement1 |- *.
    intros invariant Hinvariant Hmask.
    apply (IHstatement1 invariant Hinvariant).
    apply elem_of_intersection in Hmask as [Hmask _]. exact Hmask.
  - destruct (analyze cost state statement1) as [error|middle] eqn:Hfirst;
      try discriminate.
    eapply IHstatement2; [eapply IHstatement1|]; eauto.
  - destruct (take_step AtomicStep state) as [error|outer] eqn:Hstep;
      try discriminate.
    destruct (analyze cost
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) statement) as [error|inner] eqn:Hbody;
      try discriminate.
    destruct (bool_decide (analysis_open inner = analysis_open outer)) eqn:Hscope;
      last discriminate.
    inversion Hanalyze; subst exit. cbn.
    apply (IHstatement
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) inner); last exact Hbody.
    apply take_step_preserves_sets in Hstep as [Hmask Hopen].
    unfold state_wf in *. cbn. rewrite Hmask. rewrite Hopen. exact Hwf.
Qed.

Theorem certificate_replays {Γ} (cost : cost_model) state
    (statement : stmt Γ) exit :
  analysis_certificate cost Γ state statement exit ->
  analyze cost state statement = inr exit.
Proof.
  intros Hcertificate. induction Hcertificate; simpl.
  - destruct statement; simpl in *; try discriminate; assumption.
  - assumption.
  - reflexivity.
  - rewrite IHHcertificate1. exact IHHcertificate2.
  - rewrite IHHcertificate1. rewrite IHHcertificate2.
    rewrite bool_decide_true; first reflexivity. split; assumption.
  - rewrite e. rewrite IHHcertificate. rewrite bool_decide_true; first reflexivity.
    assumption.
Qed.

Theorem analyze_builds_certificate {Γ} (cost : cost_model) state
    (statement : stmt Γ) exit :
  analyze cost state statement = inr exit ->
  analysis_certificate cost Γ state statement exit.
Proof.
  revert state exit.
  induction statement; intros state exit Hanalyze; simpl in Hanalyze;
    try (eapply CertLeaf; [reflexivity|exact Hanalyze]).
  - eapply CertUnfold. exact Hanalyze.
  - inversion Hanalyze; subst exit. apply CertFold.
  - destruct (analyze cost state statement1) as [error|then_exit] eqn:Hthen;
      try discriminate.
    destruct (analyze cost state statement2) as [error|else_exit] eqn:Helse;
      try discriminate.
    destruct (bool_decide
      (analysis_open then_exit = analysis_open else_exit /\
       analysis_in_atomic then_exit = analysis_in_atomic else_exit)) eqn:Hjoin;
      last discriminate.
    apply bool_decide_eq_true in Hjoin as [Hopen Hin_atomic].
    inversion Hanalyze; subst exit.
    eapply CertIf; eauto.
  - destruct (analyze cost state statement1) as [error|middle] eqn:Hfirst;
      try discriminate.
    eapply CertSeq.
    + eapply IHstatement1. exact Hfirst.
    + eapply IHstatement2. exact Hanalyze.
  - destruct (take_step AtomicStep state) as [error|outer] eqn:Hstep;
      try discriminate.
    destruct (analyze cost
      (AnalysisState (analysis_mask outer) (analysis_open outer)
        (analysis_step_taken outer) true) statement) as [error|inner] eqn:Hbody;
      try discriminate.
    destruct (bool_decide (analysis_open inner = analysis_open outer)) eqn:Hscope;
      last discriminate.
    apply bool_decide_eq_true in Hscope.
    inversion Hanalyze; subst exit.
    eapply CertAtomic; eauto.
Qed.

Corollary analyze_certificate_iff {Γ} (cost : cost_model) state
    (statement : stmt Γ) exit :
  analyze cost state statement = inr exit <->
  exists _ : analysis_certificate cost Γ state statement exit, True.
Proof.
  split.
  - intros Hanalyze. exists (analyze_builds_certificate cost state statement exit
      Hanalyze). exact I.
  - intros [certificate _]. exact (certificate_replays cost state statement exit
      certificate).
Qed.

End Make.
End TypedAtomicity.
