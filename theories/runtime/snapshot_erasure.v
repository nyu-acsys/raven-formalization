From Coq Require Import List String Program.Equality.
From stdpp Require Import base.

From raven Require Import verification.expressions verification.assertions
  verification.ir verification.snapshots runtime.ra_base runtime.erasure.

Import ListNotations.

(** Invariant-argument snapshots erase to the source program exactly. *)
Module SnapshotErasure.
Import Core IR RuntimeErasure Snapshots.

Section WithSignature.
Context {RAs : ra_base.RAConfig} {Logic : Assertion.LogicSignature}.

(** A renaming that keeps the runtime name of every runtime local. *)
Definition renaming_preserves_names {D D'} (renaming : lvar_renaming D D')
    (names : named_context D) (names' : named_context D') : Prop :=
  forall keep t (variable : lvar keep D t), lvar_runtime variable = true ->
    runtime_variable names' (renaming keep t variable) =
      runtime_variable names variable.

Lemma lift_renaming_preserves_names {D D'} (renaming : lvar_renaming D D')
    names names' name d :
  renaming_preserves_names renaming names names' ->
  renaming_preserves_names (lift_renaming d renaming)
    (NCCons name d names) (NCCons name d names').
Proof.
  intros Hnames keep t variable Hruntime.
  dependent destruction variable; [reflexivity|].
  exact (Hnames _ _ variable Hruntime).
Qed.

Lemma runtime_expr_rename {D D' t} (renaming : lvar_renaming D D')
    names names' (expression : rexpr D t) :
  renaming_preserves_names renaming names names' ->
  runtime_expr names' (pexpr_rename renaming expression) =
    runtime_expr names expression.
Proof.
  intros Hnames. induction expression; simpl; try congruence.
  f_equal. apply Hnames. apply (lvar_runtime_keep (keep := keep_runtime)).
Qed.

Lemma runtime_expr_list_rename {D D' ts} (renaming : lvar_renaming D D')
    names names' (expressions : rexpr_list D ts) :
  renaming_preserves_names renaming names names' ->
  runtime_expr_list names' (pexpr_list_rename renaming expressions) =
    runtime_expr_list names expressions.
Proof.
  intros Hnames. induction expressions; simpl; [reflexivity|].
  rewrite (runtime_expr_rename _ _ _ _ Hnames), IHexpressions. reflexivity.
Qed.

Lemma field_init_rename_ghost {D D'} (renaming : lvar_renaming D D')
    (initialization : field_init D) :
  field_init_is_ghost (field_init_rename renaming initialization) =
    field_init_is_ghost initialization.
Proof. destruct initialization; reflexivity. Qed.

Lemma runtime_field_initializers_rename {D D'} (renaming : lvar_renaming D D')
    names names' (fields : list (field_init D)) :
  renaming_preserves_names renaming names names' ->
  runtime_field_initializers names'
      (physical_field_initializers (map (field_init_rename renaming) fields)) =
    runtime_field_initializers names (physical_field_initializers fields).
Proof.
  intros Hnames. induction fields as [|[field value] fields IH]; [reflexivity|].
  unfold physical_field_initializers in *. cbn [map List.filter].
  rewrite field_init_rename_ghost.
  destruct (field_init_is_ghost (FieldInit field value)); cbn [negb];
    [exact IH|].
  cbn [runtime_field_initializers field_init_rename].
  rewrite (runtime_expr_rename _ _ _ _ Hnames), IH. reflexivity.
Qed.

Lemma runtime_stmt_rename {D} (statement : stmt D) :
  forall D' (renaming : lvar_renaming D D') names names' stack,
  renaming_preserves_names renaming names names' ->
  runtime_stmt names' stack (stmt_rename renaming statement) =
    runtime_stmt names stack statement.
Proof.
  induction statement; intros D' renaming names names' stack Hnames;
    cbn [stmt_rename runtime_stmt];
    rewrite ?(runtime_expr_rename _ _ _ _ Hnames),
      ?(runtime_expr_list_rename _ _ _ _ Hnames); try reflexivity.
  - rewrite Hnames; [reflexivity | apply lvar_runtime_keep].
  - rewrite Hnames; [reflexivity | apply lvar_runtime_keep].
  - rewrite Hnames, (runtime_field_initializers_rename _ _ _ _ Hnames);
      [reflexivity | apply lvar_runtime_keep].
  - destruct target; cbn; [reflexivity|].
    rewrite Hnames; [reflexivity | apply lvar_runtime_keep].
  - apply IHstatement. exact Hnames.
  - rewrite (IHstatement1 _ _ _ _ _ Hnames), (IHstatement2 _ _ _ _ _ Hnames).
    reflexivity.
  - rewrite (IHstatement1 _ _ _ _ _ Hnames), (IHstatement2 _ _ _ _ _ Hnames).
    reflexivity.
  - apply runtime_stmt_atomic_congruence. intros stack'.
    apply IHstatement. exact Hnames.
  - apply IHstatement. apply lift_renaming_preserves_names. exact Hnames.
Qed.

Lemma matching_fold_erasure {D} invariant
    (snapshots : gexpr_list D (Assertion.invariant_args invariant))
    (statement closing check : stmt D) names stack :
  matching_fold invariant snapshots statement = Some (closing, check) ->
  runtime_stmt names stack statement = runtime_noop /\
  runtime_stmt names stack closing = runtime_noop /\
  runtime_stmt names stack check = runtime_noop.
Proof.
  destruct statement; cbn; try discriminate.
  destruct (decide (invariant0 = invariant)); [|discriminate].
  intros Hmatch. injection Hmatch as <- <-. auto.
Qed.

Lemma close_access_erasure {D} invariant (statement : stmt D) :
  forall (snapshots : gexpr_list D (Assertion.invariant_args invariant))
    names stack,
  runtime_stmt names stack (fst (close_access invariant snapshots statement)) =
    runtime_stmt names stack statement.
Proof.
  induction statement; intros snapshots names stack; cbn [close_access];
    try reflexivity.
  - (* fold *)
    destruct (matching_fold invariant snapshots (TFold invariant0 arguments))
      as [[closing check]|] eqn:Hmatch; [|reflexivity].
    destruct (matching_fold_erasure _ _ _ _ _ names stack Hmatch)
      as (Hsource & Hclosing & Hcheck).
    cbn. rewrite ?Hsource, ?Hclosing, ?Hcheck. reflexivity.
  - (* access *)
    destruct (close_access invariant snapshots statement) as [body closed]
      eqn:Hbody.
    cbn. specialize (IHstatement snapshots names stack).
    rewrite Hbody in IHstatement. exact IHstatement.
  - (* conditional *)
    destruct (close_access invariant snapshots statement1) as [left left_closed]
      eqn:Hleft.
    destruct (close_access invariant snapshots statement2)
      as [right right_closed] eqn:Hright.
    specialize (IHstatement1 snapshots names stack).
    specialize (IHstatement2 snapshots names stack).
    rewrite Hleft in IHstatement1. rewrite Hright in IHstatement2.
    cbn in IHstatement1, IHstatement2 |- *.
    rewrite IHstatement1, IHstatement2. reflexivity.
  - (* sequence *)
    destruct (matching_fold invariant snapshots statement1)
      as [[closing check]|] eqn:Hmatch.
    + destruct (matching_fold_erasure _ _ _ _ _ names stack Hmatch)
        as (Hsource & Hclosing & Hcheck).
      cbn. rewrite ?Hsource, ?Hclosing, ?Hcheck. reflexivity.
    + destruct (close_access invariant snapshots statement1)
        as [first closed] eqn:Hfirst.
      specialize (IHstatement1 snapshots names stack).
      rewrite Hfirst in IHstatement1. cbn in IHstatement1.
      destruct closed.
      * cbn. rewrite IHstatement1. reflexivity.
      * destruct (close_access invariant snapshots statement2)
          as [second closed'] eqn:Hsecond.
        specialize (IHstatement2 snapshots names stack).
        rewrite Hsecond in IHstatement2. cbn in *.
        rewrite IHstatement1, IHstatement2. reflexivity.
  - (* atomic *)
    destruct (close_access invariant snapshots statement) as [body closed]
      eqn:Hbody.
    cbn. apply runtime_stmt_atomic_congruence. intros stack'.
    specialize (IHstatement snapshots names stack').
    rewrite Hbody in IHstatement. exact IHstatement.
  - (* ghost value *)
    destruct (close_access invariant (pexpr_list_shift snapshots) statement)
      as [body closed] eqn:Hbody.
    cbn. specialize (IHstatement (pexpr_list_shift snapshots)
      (NCCons name (ghost_val t) names) stack).
    rewrite Hbody in IHstatement. exact IHstatement.
  - (* ghost conditional *)
    destruct (close_access invariant snapshots statement1) as [left left_closed].
    destruct (close_access invariant snapshots statement2)
      as [right right_closed].
    reflexivity.
Qed.

Lemma snapshot_arguments_erasure {D0 ts} (arguments : gexpr_list D0 ts) :
  forall D (renaming : lvar_renaming D0 D) continuation names stack result,
  (forall D' (renaming' : lvar_renaming D D') snapshots names',
    renaming_preserves_names renaming' names names' ->
    runtime_stmt names' stack (continuation D' renaming' snapshots) = result) ->
  runtime_stmt names stack (snapshot_arguments renaming arguments continuation) =
    result.
Proof.
  induction arguments; intros D renaming continuation names stack result
    Hcontinuation; cbn [snapshot_arguments].
  - apply Hcontinuation. intros keep u variable _. reflexivity.
  - cbn [runtime_stmt]. apply IHarguments.
    intros D' renaming' snapshots names' Hnames.
    apply Hcontinuation. intros keep u variable Hruntime.
    exact (Hnames _ _ (LThere variable) Hruntime).
Qed.

Lemma snapshot_access_erasure {D} invariant
    (arguments : gexpr_list D (Assertion.invariant_args invariant))
    (rest : stmt D) names stack :
  runtime_stmt names stack (snapshot_access invariant arguments rest) =
    runtime_stmt names stack rest.
Proof.
  unfold snapshot_access. apply snapshot_arguments_erasure.
  intros D' renaming snapshots names' Hnames. cbn [runtime_stmt].
  rewrite close_access_erasure. cbn.
  apply runtime_stmt_rename. exact Hnames.
Qed.

Theorem snapshot_accesses_erasure {D} (statement : stmt D) :
  forall names stack,
  runtime_stmt names stack (snapshot_accesses statement) =
    runtime_stmt names stack statement.
Proof.
  induction statement; intros names stack; cbn [snapshot_accesses];
    try reflexivity.
  - cbn. apply IHstatement.
  - cbn. rewrite IHstatement1, IHstatement2. reflexivity.
  - destruct statement1; cbn [runtime_stmt];
      try (rewrite IHstatement1, IHstatement2; reflexivity).
    destruct (pexpr_list_nil arguments).
    + cbn. rewrite IHstatement2. reflexivity.
    + rewrite snapshot_access_erasure, IHstatement2. reflexivity.
  - apply runtime_stmt_atomic_congruence. intros stack'. apply IHstatement.
  - cbn. apply IHstatement.
Qed.

End WithSignature.
End SnapshotErasure.
