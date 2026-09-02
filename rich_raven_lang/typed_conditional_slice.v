From Coq Require Import List Lia.

Import ListNotations.

(** A structural slice of conditional invariant-access normalization.

    The payload interface is intentionally independent of assertions and Iris.
    Its [chunk] will eventually be instantiated by aligned Raven certificates.
    The indices retain precisely the information needed by the soundness proof:
    analysis states and the concrete LIFO access stack. *)
Module Type CONDITIONAL_SLICE_PAYLOAD.
  Parameter state marker : Type.

  (** An indivisible, aligned piece of an operational zipper. *)
  Parameter chunk : state -> list marker -> state -> list marker -> Type.

  (** A chunk which leaves the focused marker continuously open.  Merely
      returning to the same stack is insufficient: [fold; unfold] must not
      inhabit this predicate. *)
  Parameter preserves : forall focused tail entry exit,
    chunk entry (focused :: tail) exit (focused :: tail) -> Prop.

  (** Evidence identifying an opening chunk.  The remembered tail is kept in
      the indices rather than reconstructed from analysis sets. *)
  Parameter opens : forall focused tail entry exit,
    chunk entry tail exit (focused :: tail) -> Prop.

  (** Evidence identifying the first matching close of [focused]. *)
  Parameter closes : forall focused tail entry exit,
    chunk entry (focused :: tail) exit tail -> Prop.

  (** The analyzer's conditional join.  Branch exit states need not be
      definitionally equal to the join state. *)
  Parameter conditional : state -> state -> state -> state -> Type.
End CONDITIONAL_SLICE_PAYLOAD.

Module ConditionalSlice (P : CONDITIONAL_SLICE_PAYLOAD).
  Import P.

  (** [execution] is the normalized, stack-indexed operational tree.
      [ExecConditional] retains separate branch-local executions and only
      shares the continuation after the analyzer join. *)
  Inductive execution :
      state -> list marker -> state -> list marker -> Type :=
  | ExecDone entry stack : execution entry stack entry stack
  | ExecChunk entry stack middle exit stack_out
      (head : chunk entry stack middle stack)
      (rest : execution middle stack exit stack_out) :
      execution entry stack exit stack_out
  | ExecClose focused tail entry middle exit stack_out
      (close_chunk : chunk entry (focused :: tail) middle tail)
      (close_ok : closes focused tail entry middle close_chunk)
      (rest : execution middle tail exit stack_out) :
      execution entry (focused :: tail) exit stack_out
  | ExecAccess focused tail entry opened closed exit
      (open_chunk : chunk entry tail opened (focused :: tail))
      (open_ok : opens focused tail entry opened open_chunk)
      (body : focused_execution focused tail opened closed)
      (rest : execution closed tail exit tail) :
      execution entry tail exit tail
  | ExecFocusedOutcome focused tail entry middle exit stack_out
      (outcome : focused_outcome focused tail entry middle (focused :: tail))
      (rest : execution middle (focused :: tail) exit stack_out) :
      execution entry (focused :: tail) exit stack_out
  | ExecFocusedClose focused tail entry closed exit stack_out
      (body : focused_execution focused tail entry closed)
      (rest : execution closed tail exit stack_out) :
      execution entry (focused :: tail) exit stack_out
  | ExecConditional entry stack then_exit else_exit join exit stack_out
      (test : conditional entry then_exit else_exit join)
      (then_branch : execution entry stack then_exit stack_out)
      (else_branch : execution entry stack else_exit stack_out)
      (rest : execution join stack_out exit stack_out) :
      execution entry stack exit stack_out

  (** A focused execution discovers the *first* matching close.  Post-close
      work is represented explicitly by conditional branches. *)
  with focused_execution : marker -> list marker -> state -> state -> Type :=
  | FocusedClose focused tail entry exit
      (close_chunk : chunk entry (focused :: tail) exit tail)
      (close_ok : closes focused tail entry exit close_chunk) :
      focused_execution focused tail entry exit
  | FocusedPrefix focused tail entry middle exit
      (prefix : chunk entry (focused :: tail) middle (focused :: tail))
      (prefix_ok : preserves focused tail entry middle prefix)
      (rest : focused_execution focused tail middle exit) :
      focused_execution focused tail entry exit
  | FocusedNestedAccess focused nested tail entry opened nested_closed exit
      (open_chunk : chunk entry (focused :: tail) opened
        (nested :: focused :: tail))
      (open_ok : opens nested (focused :: tail) entry opened open_chunk)
      (nested_body : focused_execution nested (focused :: tail)
        opened nested_closed)
      (rest : focused_execution focused tail nested_closed exit) :
      focused_execution focused tail entry exit
  | FocusedNestedExecution focused nested tail entry opened nested_closed exit
      (open_chunk : chunk entry (focused :: tail) opened
        (nested :: focused :: tail))
      (open_ok : opens nested (focused :: tail) entry opened open_chunk)
      (nested_body : focused_execution nested (focused :: tail)
        opened nested_closed)
      (rest : execution nested_closed (focused :: tail) exit tail) :
      focused_execution focused tail entry exit
  | FocusedConditional focused tail entry then_close then_exit
      else_close else_exit join stack_out exit
      (test : conditional entry then_exit else_exit join)
      (then_branch : closed_branch focused tail entry then_close then_exit
        stack_out)
      (else_branch : closed_branch focused tail entry else_close else_exit
        stack_out)
      (rest : execution join stack_out exit tail) :
      focused_execution focused tail entry exit
  | FocusedConditionalContinue focused tail entry then_exit else_exit join exit
      (test : conditional entry then_exit else_exit join)
      (then_branch : focused_outcome focused tail entry then_exit
        (focused :: tail))
      (else_branch : focused_outcome focused tail entry else_exit
        (focused :: tail))
      (continuation : focused_execution focused tail join exit) :
      focused_execution focused tail entry exit

  (** A conditional arm retains its own suffix after the first close.  This is
      the central distinction from a linear zipper decomposition. *)
  with closed_branch : marker -> list marker -> state -> state -> state ->
      list marker -> Type :=
  | ClosedBranch focused tail entry closed exit stack_out
      (first_close : focused_execution focused tail entry closed)
      (post_close : execution closed tail exit stack_out) :
      closed_branch focused tail entry closed exit stack_out
  | ClosedBranchOpened focused nested tail entry closed open_entry opened exit
      (first_close : focused_execution focused tail entry closed)
      (before_open : execution closed tail open_entry tail)
      (open_chunk : chunk open_entry tail opened (nested :: tail))
      (open_ok : opens nested tail open_entry opened open_chunk)
      (after_open : focused_prefix nested tail opened exit) :
      closed_branch focused tail entry closed exit (nested :: tail)

  (** A computation which continuously retains the current accessor. *)
  with focused_prefix : marker -> list marker -> state -> state -> Type :=
  | FocusedPrefixDone focused tail entry :
      focused_prefix focused tail entry entry
  | FocusedPrefixChunk focused tail entry middle exit
      (prefix : chunk entry (focused :: tail) middle (focused :: tail))
      (prefix_ok : preserves focused tail entry middle prefix)
      (rest : focused_prefix focused tail middle exit) :
      focused_prefix focused tail entry exit
  | FocusedPrefixNested focused nested tail entry opened nested_closed exit
      (open_chunk : chunk entry (focused :: tail) opened
        (nested :: focused :: tail))
      (open_ok : opens nested (focused :: tail) entry opened open_chunk)
      (nested_body : focused_execution nested (focused :: tail)
        opened nested_closed)
      (rest : focused_prefix focused tail nested_closed exit) :
      focused_prefix focused tail entry exit
  | FocusedPrefixConditional focused tail entry then_exit else_exit join
      (test : conditional entry then_exit else_exit join)
      (then_branch : focused_prefix focused tail entry then_exit)
      (else_branch : focused_prefix focused tail entry else_exit) :
      focused_prefix focused tail entry join

  (** An arm either has closed the original accessor and reopened an accessor
      at its exit, or has kept the original accessor continuously open. *)
  with focused_outcome : marker -> list marker -> state -> state ->
      list marker -> Type :=
  | OutcomeClosed focused tail entry closed exit stack_out
      (first_close : focused_execution focused tail entry closed)
      (post_close : execution closed tail exit stack_out) :
      focused_outcome focused tail entry exit stack_out
  | OutcomeClosedReopened focused tail entry closed reopen_entry reopened exit
      (first_close : focused_execution focused tail entry closed)
      (before_reopen : execution closed tail reopen_entry tail)
      (reopen_chunk : chunk reopen_entry tail reopened (focused :: tail))
      (reopen_ok : opens focused tail reopen_entry reopened reopen_chunk)
      (after_reopen : focused_prefix focused tail reopened exit) :
      focused_outcome focused tail entry exit (focused :: tail)
  | OutcomeStillOpen focused tail entry exit
      (prefix : focused_prefix focused tail entry exit) :
      focused_outcome focused tail entry exit (focused :: tail)
  | OutcomePrefix focused tail entry middle exit
      (prefix : chunk entry (focused :: tail) middle (focused :: tail))
      (prefix_ok : preserves focused tail entry middle prefix)
      (rest : focused_outcome focused tail middle exit (focused :: tail)) :
      focused_outcome focused tail entry exit (focused :: tail)
  | OutcomeNestedExecution focused nested tail entry opened nested_closed exit
      (open_chunk : chunk entry (focused :: tail) opened
        (nested :: focused :: tail))
      (open_ok : opens nested (focused :: tail) entry opened open_chunk)
      (nested_body : focused_execution nested (focused :: tail)
        opened nested_closed)
      (rest : execution nested_closed (focused :: tail) exit
        (focused :: tail)) :
      focused_outcome focused tail entry exit (focused :: tail)
  | OutcomeConditional focused tail entry then_exit else_exit join exit
      (test : conditional entry then_exit else_exit join)
      (then_branch : focused_outcome focused tail entry then_exit
        (focused :: tail))
      (else_branch : focused_outcome focused tail entry else_exit
        (focused :: tail))
      (continuation : focused_outcome focused tail join exit
        (focused :: tail)) :
      focused_outcome focused tail entry exit (focused :: tail).

  Scheme execution_ind' := Induction for execution Sort Prop
    with focused_execution_ind' := Induction for focused_execution Sort Prop
    with closed_branch_ind' := Induction for closed_branch Sort Prop
    with focused_prefix_ind' := Induction for focused_prefix Sort Prop
    with focused_outcome_ind' := Induction for focused_outcome Sort Prop.
  Combined Scheme normalized_execution_mutind
    from execution_ind', focused_execution_ind', closed_branch_ind',
      focused_prefix_ind', focused_outcome_ind'.

  (** Regression shape: after closing the outer focus, a branch may reopen and
      close the same marker before reaching its branch exit.  The reopening is
      necessarily in [post_close], never in the original focused region. *)
  Definition close_reopen_branch focused tail entry first_closed reopened
      second_closed
      (first : focused_execution focused tail entry first_closed)
      (reopen : chunk first_closed tail reopened (focused :: tail))
      (Hreopen : opens focused tail first_closed reopened reopen)
      (second : focused_execution focused tail reopened second_closed) :
      closed_branch focused tail entry first_closed second_closed tail :=
    ClosedBranch focused tail entry first_closed second_closed tail first
      (ExecAccess focused tail first_closed reopened second_closed
        second_closed reopen Hreopen second (ExecDone second_closed tail)).

  (** Regression shape for the difficult conditional: each arm closes at a
      different point and retains a different post-close suffix, while only
      the continuation following [join] is shared. *)
  Definition branch_local_conditional focused tail entry
      then_close then_exit else_close else_exit join
      (test : conditional entry then_exit else_exit join)
      (then_first : focused_execution focused tail entry then_close)
      (then_post : execution then_close tail then_exit tail)
      (else_first : focused_execution focused tail entry else_close)
      (else_post : execution else_close tail else_exit tail) :
      focused_execution focused tail entry join :=
    FocusedConditional focused tail entry then_close then_exit else_close
      else_exit join tail join test
      (ClosedBranch focused tail entry then_close then_exit tail
        then_first then_post)
      (ClosedBranch focused tail entry else_close else_exit tail
        else_first else_post) (ExecDone join tail).

  Definition stack_suffix (small big : list marker) : Prop :=
    exists prefix, big = prefix ++ small.

  Lemma execution_output_is_suffix entry stack_in exit stack_out
      (tree : execution entry stack_in exit stack_out) :
    stack_suffix stack_out stack_in.
  Proof.
    induction tree.
    - exists []. reflexivity.
    - exact IHtree.
    - destruct IHtree as [prefix Hprefix].
      exists (focused :: prefix). simpl. now rewrite Hprefix.
    - exists []. reflexivity.
    - exact IHtree.
    - destruct IHtree as [prefix Hprefix].
      exists (focused :: prefix). simpl. now rewrite Hprefix.
    - exact IHtree1.
  Qed.

  Lemma execution_cannot_grow entry base exit added
      (tree : execution entry base exit (added ++ base)) :
    added = [].
  Proof.
    destruct (execution_output_is_suffix _ _ _ _ tree) as [prefix Hprefix].
    pose proof (f_equal (@length marker) Hprefix) as Hlength.
    rewrite !app_length in Hlength.
    destruct added as [|head added]; [reflexivity|].
    simpl in Hlength. lia.
  Qed.
End ConditionalSlice.

(** A continuation algebra for the normalized tree.  Instantiating [formula]
    with Iris propositions and [chunk_wp] with the translated Raven chunk WP
    yields the semantic slice used by the operational refinement. *)
Module Type CONDITIONAL_SLICE_SEMANTICS (P : CONDITIONAL_SLICE_PAYLOAD).
  Parameter formula : Type.
  Parameter chunk_wp : forall entry stack_in exit stack_out,
    P.chunk entry stack_in exit stack_out -> formula -> formula.
  Parameter conditional_wp : forall entry then_exit else_exit join,
    P.conditional entry then_exit else_exit join ->
    formula -> formula -> formula.
End CONDITIONAL_SLICE_SEMANTICS.

Module Type CONDITIONAL_SLICE_INTERFACE (P : CONDITIONAL_SLICE_PAYLOAD).
  Include ConditionalSlice P.
End CONDITIONAL_SLICE_INTERFACE.

Module ConditionalSliceDenotation (P : CONDITIONAL_SLICE_PAYLOAD)
    (N : CONDITIONAL_SLICE_INTERFACE P)
    (S : CONDITIONAL_SLICE_SEMANTICS P).
  Import P S N.

  Fixpoint execution_wp {entry stack_in exit stack_out}
      (tree : execution entry stack_in exit stack_out)
      (post : formula) : formula :=
    match tree with
    | ExecDone _ _ => post
    | ExecChunk _ _ _ _ _ head rest =>
        chunk_wp _ _ _ _ head (execution_wp rest post)
    | ExecClose _ _ _ _ _ _ close_chunk _ rest =>
        chunk_wp _ _ _ _ close_chunk (execution_wp rest post)
    | ExecAccess _ _ _ _ _ _ open_chunk _ body rest =>
        chunk_wp _ _ _ _ open_chunk
          (focused_execution_wp body (execution_wp rest post))
    | ExecFocusedOutcome _ _ _ _ _ _ outcome rest =>
        focused_outcome_wp outcome (execution_wp rest post)
    | ExecFocusedClose _ _ _ _ _ _ body rest =>
        focused_execution_wp body (execution_wp rest post)
    | ExecConditional _ _ _ _ _ _ _ test then_branch else_branch rest =>
        conditional_wp _ _ _ _ test
          (execution_wp then_branch (execution_wp rest post))
          (execution_wp else_branch (execution_wp rest post))
    end
  with focused_execution_wp {focused tail entry exit}
      (tree : focused_execution focused tail entry exit)
      (post : formula) : formula :=
    match tree with
    | FocusedClose _ _ _ _ close_chunk _ =>
        chunk_wp _ _ _ _ close_chunk post
    | FocusedPrefix _ _ _ _ _ prefix _ rest =>
        chunk_wp _ _ _ _ prefix (focused_execution_wp rest post)
    | FocusedNestedAccess _ _ _ _ _ _ _ open_chunk _ nested_body rest =>
        chunk_wp _ _ _ _ open_chunk
          (focused_execution_wp nested_body
            (focused_execution_wp rest post))
    | FocusedNestedExecution _ _ _ _ _ _ _ open_chunk _ nested_body rest =>
        chunk_wp _ _ _ _ open_chunk
          (focused_execution_wp nested_body (execution_wp rest post))
    | FocusedConditional _ _ _ _ _ _ _ _ _ _ test then_branch else_branch
        rest =>
        let shared := execution_wp rest post in
        conditional_wp _ _ _ _ test
          (closed_branch_wp then_branch shared)
          (closed_branch_wp else_branch shared)
    | FocusedConditionalContinue _ _ _ _ _ _ _ test then_branch
        else_branch continuation =>
        let shared := focused_execution_wp continuation post in
        conditional_wp _ _ _ _ test
          (focused_outcome_wp then_branch shared)
          (focused_outcome_wp else_branch shared)
    end
  with closed_branch_wp {focused tail entry closed exit stack_out}
      (branch : closed_branch focused tail entry closed exit stack_out)
      (post : formula) : formula :=
    match branch with
    | ClosedBranch _ _ _ _ _ _ first_close post_close =>
        focused_execution_wp first_close
          (execution_wp post_close post)
    | ClosedBranchOpened _ _ _ _ _ _ _ _ first_close before_open open_chunk _
        after_open =>
        focused_execution_wp first_close
          (execution_wp before_open
            (chunk_wp _ _ _ _ open_chunk (focused_prefix_wp after_open post)))
    end
  with focused_prefix_wp {focused tail entry exit}
      (tree : focused_prefix focused tail entry exit)
      (post : formula) : formula :=
    match tree with
    | FocusedPrefixDone _ _ _ => post
    | FocusedPrefixChunk _ _ _ _ _ prefix _ rest =>
        chunk_wp _ _ _ _ prefix (focused_prefix_wp rest post)
    | FocusedPrefixNested _ _ _ _ _ _ _ open_chunk _ nested_body rest =>
        chunk_wp _ _ _ _ open_chunk
          (focused_execution_wp nested_body (focused_prefix_wp rest post))
    | FocusedPrefixConditional _ _ _ _ _ _ test then_branch else_branch =>
        conditional_wp _ _ _ _ test
          (focused_prefix_wp then_branch post)
          (focused_prefix_wp else_branch post)
    end
  with focused_outcome_wp {focused tail entry exit stack_out}
      (outcome : focused_outcome focused tail entry exit stack_out)
      (shared : formula) : formula :=
    match outcome with
    | OutcomeClosed _ _ _ _ _ _ first_close post_close =>
        focused_execution_wp first_close (execution_wp post_close shared)
    | OutcomeClosedReopened _ _ _ _ _ _ _ first_close before_reopen reopen_chunk _
        after_reopen =>
        focused_execution_wp first_close
          (execution_wp before_reopen
            (chunk_wp _ _ _ _ reopen_chunk
              (focused_prefix_wp after_reopen shared)))
    | OutcomeStillOpen _ _ _ _ prefix => focused_prefix_wp prefix shared
    | OutcomePrefix _ _ _ _ _ prefix _ rest =>
        chunk_wp _ _ _ _ prefix (focused_outcome_wp rest shared)
    | OutcomeNestedExecution _ _ _ _ _ _ _ open_chunk _ nested_body rest =>
        chunk_wp _ _ _ _ open_chunk
          (focused_execution_wp nested_body (execution_wp rest shared))
    | OutcomeConditional _ _ _ _ _ _ _ test then_branch else_branch
        continuation =>
        let rest := focused_outcome_wp continuation shared in
        conditional_wp _ _ _ _ test
          (focused_outcome_wp then_branch rest)
          (focused_outcome_wp else_branch rest)
    end.

  (** The common continuation occurs once in the normalized syntax but is
      supplied semantically to both selected arms.  Each arm first executes
      its own post-close suffix. *)
  Lemma focused_conditional_wp_unfold focused tail entry then_close then_exit
      else_close else_exit join stack_out exit test then_branch else_branch
      rest post :
    focused_execution_wp
      (FocusedConditional focused tail entry then_close then_exit
        else_close else_exit join stack_out exit test then_branch else_branch
        rest) post =
    conditional_wp _ _ _ _ test
      (closed_branch_wp then_branch (execution_wp rest post))
      (closed_branch_wp else_branch (execution_wp rest post)).
  Proof. reflexivity. Qed.

  Lemma closed_branch_wp_unfold focused tail entry closed exit stack_out
      first_close post_close post :
    closed_branch_wp
      (ClosedBranch focused tail entry closed exit stack_out first_close
        post_close)
      post =
    focused_execution_wp first_close (execution_wp post_close post).
  Proof. reflexivity. Qed.
End ConditionalSliceDenotation.

Module Type CONDITIONAL_SLICE_MONOTONE
    (P : CONDITIONAL_SLICE_PAYLOAD)
    (S : CONDITIONAL_SLICE_SEMANTICS P).
  Parameter entails : S.formula -> S.formula -> Prop.
  Parameter entails_refl : forall proposition, entails proposition proposition.
  Parameter chunk_wp_mono : forall entry stack_in exit stack_out
      (piece : P.chunk entry stack_in exit stack_out) left right,
    entails left right ->
    entails (S.chunk_wp _ _ _ _ piece left)
      (S.chunk_wp _ _ _ _ piece right).
  Parameter conditional_wp_mono : forall entry then_exit else_exit join
      (test : P.conditional entry then_exit else_exit join)
      then_left then_right else_left else_right,
    entails then_left then_right ->
    entails else_left else_right ->
    entails (S.conditional_wp _ _ _ _ test then_left else_left)
      (S.conditional_wp _ _ _ _ test then_right else_right).
End CONDITIONAL_SLICE_MONOTONE.

Module ConditionalSliceMonotonicity (P : CONDITIONAL_SLICE_PAYLOAD)
    (N : CONDITIONAL_SLICE_INTERFACE P)
    (S : CONDITIONAL_SLICE_SEMANTICS P)
    (O : CONDITIONAL_SLICE_MONOTONE P S).
  Module D := ConditionalSliceDenotation P N S.
  Import P S N O D.

  Lemma normalized_wp_mono :
    (forall entry stack_in exit stack_out
      (tree : execution entry stack_in exit stack_out) left right,
      entails left right ->
      entails (execution_wp tree left) (execution_wp tree right)) /\
    (forall focused tail entry exit
      (tree : focused_execution focused tail entry exit) left right,
      entails left right ->
      entails (focused_execution_wp tree left)
        (focused_execution_wp tree right)) /\
    (forall focused tail entry closed exit stack_out
      (branch : closed_branch focused tail entry closed exit stack_out) left right,
      entails left right ->
      entails (closed_branch_wp branch left) (closed_branch_wp branch right)) /\
    (forall focused tail entry exit
      (tree : focused_prefix focused tail entry exit) left right,
      entails left right ->
      entails (focused_prefix_wp tree left) (focused_prefix_wp tree right)) /\
    (forall focused tail entry exit stack_out
      (outcome : focused_outcome focused tail entry exit stack_out) left right,
      entails left right ->
      entails (focused_outcome_wp outcome left)
        (focused_outcome_wp outcome right)).
  Proof.
    apply normalized_execution_mutind; intros; simpl.
    - assumption.
    - apply chunk_wp_mono. auto.
    - apply chunk_wp_mono. auto.
    - apply chunk_wp_mono. auto.
    - auto.
    - auto.
    - apply conditional_wp_mono; auto.
    - apply chunk_wp_mono. assumption.
    - apply chunk_wp_mono. auto.
    - apply chunk_wp_mono. auto.
    - apply chunk_wp_mono. auto.
    - apply conditional_wp_mono; auto.
    - apply conditional_wp_mono; auto.
    - eauto using chunk_wp_mono.
    - eauto using chunk_wp_mono.
    - assumption.
    - apply chunk_wp_mono. auto.
    - apply chunk_wp_mono. auto.
    - apply conditional_wp_mono; auto.
    - auto.
    - eauto using chunk_wp_mono.
    - auto.
    - apply chunk_wp_mono. auto.
    - apply chunk_wp_mono. auto.
    - apply conditional_wp_mono; auto.
  Qed.

  Lemma execution_wp_mono entry stack_in exit stack_out
      (tree : execution entry stack_in exit stack_out) left right :
    entails left right ->
    entails (execution_wp tree left) (execution_wp tree right).
  Proof. apply normalized_wp_mono. Qed.

  Lemma focused_execution_wp_mono focused tail entry exit
      (tree : focused_execution focused tail entry exit) left right :
    entails left right ->
    entails (focused_execution_wp tree left) (focused_execution_wp tree right).
  Proof. apply normalized_wp_mono. Qed.

  Lemma closed_branch_wp_mono focused tail entry closed exit stack_out
      (branch : closed_branch focused tail entry closed exit stack_out) left right :
    entails left right ->
    entails (closed_branch_wp branch left) (closed_branch_wp branch right).
  Proof. apply normalized_wp_mono. Qed.

  Lemma focused_prefix_wp_mono focused tail entry exit
      (tree : focused_prefix focused tail entry exit) left right :
    entails left right ->
    entails (focused_prefix_wp tree left) (focused_prefix_wp tree right).
  Proof. apply normalized_wp_mono. Qed.

  Lemma focused_outcome_wp_mono focused tail entry exit stack_out
      (outcome : focused_outcome focused tail entry exit stack_out) left right :
    entails left right ->
    entails (focused_outcome_wp outcome left)
      (focused_outcome_wp outcome right).
  Proof. apply normalized_wp_mono. Qed.
End ConditionalSliceMonotonicity.
