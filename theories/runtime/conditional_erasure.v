From Coq Require Import List Bool.
From stdpp Require Import base.

From raven Require Import verification.expressions verification.assertions
  verification.ir verification.access_layout
  verification.conditional_derivations runtime.ra_base runtime.erasure.

(** The distributed and factored forms of a conditional access erase to the
    source program exactly. *)
Module ConditionalErasure.
Import Core IR RuntimeErasure AccessLayout ConditionalDerivations.

Section WithSignature.
Context {RAs : ra_base.RAConfig} {Logic : Assertion.LogicSignature}.

Lemma distribute_access_erasure {Γ} (names : named_context Γ) stack invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix then_branch else_branch : stmt Γ) (condition : rexpr Γ TBool) :
  proof_onlyb prefix = true ->
  runtime_stmt names stack
      (TIf condition
        (TSeq (TUnfold invariant arguments)
          (TSeq prefix (TSeq TDone then_branch)))
        (TSeq (TUnfold invariant arguments)
          (TSeq prefix (TSeq TDone else_branch)))) =
    runtime_stmt names stack
      (TSeq (TUnfold invariant arguments)
        (TSeq prefix (TIf condition then_branch else_branch))).
Proof.
  intros Hprefix. cbn [runtime_stmt].
  rewrite (runtime_stmt_proof_only names stack prefix Hprefix). reflexivity.
Qed.

Lemma factor_access_erasure {Γ} (names : named_context Γ) stack invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix then_prefix then_continuation else_prefix else_continuation : stmt Γ)
    (condition : rexpr Γ TBool) :
  proof_onlyb then_prefix = true ->
  proof_onlyb else_prefix = true ->
  runtime_stmt names stack
      (TSeq (TUnfold invariant arguments)
        (TSeq
          (TSeq prefix
            (TSeq TDone
              (TIf condition (TSeq then_prefix TDone)
                (TSeq else_prefix TDone))))
          (TSeq (factored_closing invariant arguments (pexpr_forget condition))
            (TIf condition then_continuation else_continuation)))) =
    runtime_stmt names stack
      (TSeq (TUnfold invariant arguments)
        (TSeq prefix
          (TIf condition
            (TSeq then_prefix
              (TSeq (TFold invariant arguments) then_continuation))
            (TSeq else_prefix
              (TSeq (TFold invariant arguments) else_continuation))))).
Proof.
  intros Hthen Helse. cbn [runtime_stmt factored_closing].
  rewrite (runtime_stmt_proof_only names stack then_prefix Hthen),
    (runtime_stmt_proof_only names stack else_prefix Helse).
  cbn. rewrite runtime_seq_noop_r. reflexivity.
Qed.

Lemma distribute_ghost_access_erasure {Γ} (names : named_context Γ) stack
    invariant (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix then_branch else_branch : stmt Γ) (condition : gexpr Γ TBool) :
  proof_onlyb prefix = true ->
  runtime_stmt names stack
      (TGhostIf condition
        (TSeq (TUnfold invariant arguments)
          (TSeq prefix (TSeq TDone then_branch)))
        (TSeq (TUnfold invariant arguments)
          (TSeq prefix (TSeq TDone else_branch)))) =
    runtime_stmt names stack
      (TSeq (TUnfold invariant arguments)
        (TSeq prefix (TGhostIf condition then_branch else_branch))).
Proof.
  intros Hprefix. cbn [runtime_stmt].
  rewrite (runtime_stmt_proof_only names stack prefix Hprefix). reflexivity.
Qed.

Lemma factor_ghost_access_erasure {Γ} (names : named_context Γ) stack
    invariant (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix then_prefix then_continuation else_prefix else_continuation : stmt Γ)
    (condition : gexpr Γ TBool) :
  runtime_stmt names stack
      (TSeq (TUnfold invariant arguments)
        (TSeq
          (TSeq prefix
            (TSeq TDone
              (TGhostIf condition (TSeq then_prefix TDone)
                (TSeq else_prefix TDone))))
          (TSeq (factored_closing invariant arguments condition)
            (TGhostIf condition then_continuation else_continuation)))) =
    runtime_stmt names stack
      (TSeq (TUnfold invariant arguments)
        (TSeq prefix
          (TGhostIf condition
            (TSeq then_prefix
              (TSeq (TFold invariant arguments) then_continuation))
            (TSeq else_prefix
              (TSeq (TFold invariant arguments) else_continuation))))).
Proof.
  cbn [runtime_stmt factored_closing]. cbn. rewrite !runtime_seq_noop_r.
  reflexivity.
Qed.

Lemma rebuild_proof_only {Γ} (statements : list (stmt Γ)) :
  forallb proof_onlyb statements = true -> proof_onlyb (rebuild statements) = true.
Proof.
  induction statements as [|statement rest IH]; cbn; [reflexivity|].
  intros Hall. apply andb_prop in Hall as [Hstatement Hrest].
  destruct rest; [exact Hstatement|].
  cbn [proof_onlyb]. rewrite Hstatement, IH by exact Hrest. reflexivity.
Qed.

Lemma runtime_seq_assoc_noop (first second third : RuntimeLang.runtime_stmt) :
  first = runtime_noop \/ second = runtime_noop \/ third = runtime_noop ->
  runtime_seq first (runtime_seq second third) =
    runtime_seq (runtime_seq first second) third.
Proof.
  intros [ -> | [ -> | -> ] ].
  - reflexivity.
  - rewrite runtime_seq_noop_r. reflexivity.
  - rewrite !runtime_seq_noop_r. reflexivity.
Qed.

Lemma rebuild_cons_erasure {Γ} (names : named_context Γ) stack
    (statement : stmt Γ) (rest : list (stmt Γ)) :
  runtime_stmt names stack (rebuild (statement :: rest)) =
    runtime_stmt names stack (TSeq statement (rebuild rest)).
Proof.
  destruct rest; [|reflexivity].
  cbn. rewrite runtime_seq_noop_r. reflexivity.
Qed.

Lemma forallb_at_most_one_physical {Γ} (statements : list (stmt Γ)) :
  forallb proof_onlyb statements = true ->
  at_most_one_physical statements = true.
Proof.
  induction statements as [|statement rest IH]; cbn; [reflexivity|].
  intros Hall. apply andb_prop in Hall as [-> Hrest]. auto.
Qed.

Lemma rebuild_app_erasure {Γ} (names : named_context Γ) stack
    (before rest : list (stmt Γ)) :
  at_most_one_physical before = true ->
  runtime_stmt names stack (rebuild (before ++ rest)) =
    runtime_stmt names stack (TSeq (rebuild before) (rebuild rest)).
Proof.
  induction before as [|statement before IH]; intros Hphysical; [reflexivity|].
  rewrite <- app_comm_cons, rebuild_cons_erasure. cbn [runtime_stmt].
  rewrite rebuild_cons_erasure. cbn [runtime_stmt].
  cbn [at_most_one_physical] in Hphysical.
  destruct (proof_onlyb statement) eqn:Hstatement.
  - rewrite (runtime_stmt_proof_only names stack statement Hstatement).
    rewrite IH by exact Hphysical. reflexivity.
  - rewrite IH by (apply forallb_at_most_one_physical; exact Hphysical).
    cbn [runtime_stmt].
    rewrite (runtime_stmt_proof_only names stack (rebuild before))
      by (apply rebuild_proof_only; exact Hphysical).
    rewrite runtime_seq_noop_r. reflexivity.
Qed.

Lemma sequence_erasure {Γ} (names : named_context Γ) stack (statement : stmt Γ)
    before found after :
  sequence statement = before ++ found :: after ->
  at_most_one_physical before = true ->
  runtime_stmt names stack statement =
    runtime_stmt names stack (TSeq (rebuild before) (TSeq found (rebuild after))).
Proof.
  intros Hsequence Hphysical.
  rewrite <- (rebuild_sequence statement), Hsequence,
    rebuild_app_erasure by exact Hphysical.
  cbn [runtime_stmt]. rewrite rebuild_cons_erasure. reflexivity.
Qed.

Lemma branch_view_erasure {Γ} (names : named_context Γ) stack invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (branch prefix continuation : stmt Γ) :
  branch_view invariant arguments branch = Some (prefix, continuation) ->
  runtime_stmt names stack
      (canonical_branch invariant arguments prefix continuation) =
    runtime_stmt names stack branch.
Proof.
  unfold branch_view.
  destruct (split_first (fold_is invariant arguments) (sequence branch))
    as [[[before found] after]|] eqn:Hsplit; [|discriminate].
  apply split_first_sound in Hsplit as [Hsequence Hfound].
  apply fold_is_sound in Hfound. subst found.
  destruct (at_most_one_physical before) eqn:Hphysical; [|discriminate].
  intros Hview. injection Hview as <- <-.
  rewrite (sequence_erasure names stack branch _ _ _ Hsequence Hphysical).
  reflexivity.
Qed.

Lemma layout_conditional_erasure {Γ} (names : named_context Γ) stack invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (conditional laid_out : stmt Γ) :
  layout_conditional invariant arguments conditional = Some laid_out ->
  runtime_stmt names stack laid_out = runtime_stmt names stack conditional.
Proof.
  unfold layout_conditional.
  destruct conditional; try discriminate.
  all: destruct (branch_view invariant arguments conditional1)
      as [[then_prefix then_continuation]|] eqn:Hthen; [|discriminate].
  all: destruct (branch_view invariant arguments conditional2)
      as [[else_prefix else_continuation]|] eqn:Helse; [|discriminate].
  all: intros Hlaid; injection Hlaid as <-.
  2: reflexivity.
  cbn [runtime_stmt].
  rewrite (branch_view_erasure names stack invariant arguments _ _ _ Hthen),
    (branch_view_erasure names stack invariant arguments _ _ _ Helse).
  reflexivity.
Qed.

Lemma layout_unfold_erasure {Γ} (names : named_context Γ) stack invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (rest : stmt Γ) :
  runtime_stmt names stack (layout_unfold invariant arguments rest) =
    runtime_stmt names stack (TSeq (TUnfold invariant arguments) rest).
Proof.
  unfold layout_unfold.
  destruct (split_first (closes invariant arguments) (sequence rest))
    as [[[before closing] after]|] eqn:Hsplit; [|reflexivity].
  apply split_first_sound in Hsplit as [Hsequence _].
  destruct (at_most_one_physical before) eqn:Hphysical; [|reflexivity].
  assert (Hrest := sequence_erasure names stack rest _ _ _ Hsequence Hphysical).
  destruct (fold_is invariant arguments closing) eqn:Hfold.
  { apply fold_is_sound in Hfold. subst closing.
    cbn [runtime_stmt]. rewrite Hrest. cbn [runtime_stmt].
    destruct after; [|reflexivity].
    cbn. rewrite !runtime_seq_noop_r. reflexivity. }
  destruct (layout_conditional invariant arguments closing) as [laid_out|]
    eqn:Hlaid; [|reflexivity].
  pose proof (layout_conditional_erasure names stack invariant arguments _ _
    Hlaid) as Hconditional.
  destruct after as [|statement after].
  - cbn [runtime_stmt]. rewrite Hrest, Hconditional. cbn.
    rewrite runtime_seq_noop_r. reflexivity.
  - destruct (proof_onlyb (rebuild before) || proof_onlyb laid_out ||
      proof_onlyb (rebuild (statement :: after))) eqn:Hproof; [|reflexivity].
    cbn [runtime_stmt] in Hrest |- *. rewrite Hrest, <- Hconditional.
    rewrite !runtime_seq_noop_l.
    symmetry. apply runtime_seq_assoc_noop.
    rewrite !orb_true_iff in Hproof.
    destruct Hproof as [[Hbefore|Hlaid_proof]|Hafter].
    + left. apply runtime_stmt_proof_only. exact Hbefore.
    + right. left. apply runtime_stmt_proof_only. exact Hlaid_proof.
    + right. right. apply runtime_stmt_proof_only. exact Hafter.
Qed.

Lemma hoist_atomic_erasure :
  forall {Γ} (body : stmt Γ) names stack,
  runtime_stmt names stack (hoist_atomic body) =
    runtime_stmt names stack (TAtomic body).
Proof.
  fix IH 2. intros Γ body names stack.
  destruct body; try reflexivity.
  - (* sequence *)
    destruct body1; try reflexivity.
    destruct body2; try reflexivity.
    destruct body2_2; try reflexivity; cbn [hoist_atomic].
    + destruct (fold_is invariant arguments (TFold invariant0 arguments0))
        eqn:Hfold; [|reflexivity].
      rewrite (runtime_stmt_atomic_congruence names names stack _ body2_1)
        by (intros stack'; cbn [runtime_stmt];
          rewrite runtime_seq_noop_l, runtime_seq_noop_r; reflexivity).
      cbn [runtime_stmt]. rewrite IH, runtime_seq_noop_l, runtime_seq_noop_r.
      reflexivity.
    + destruct (fold_is invariant arguments body2_2_1 &&
        proof_onlyb body2_2_2) eqn:Hclosing; [|reflexivity].
      apply andb_prop in Hclosing as [Hfold Hrest].
      apply fold_is_sound in Hfold. subst body2_2_1.
      rewrite (runtime_stmt_atomic_congruence names names stack _ body2_1)
        by (intros stack'; cbn [runtime_stmt];
          rewrite (runtime_stmt_proof_only _ _ body2_2_2 Hrest),
            runtime_seq_noop_l, !runtime_seq_noop_r; reflexivity).
      cbn [runtime_stmt]. rewrite IH.
      rewrite (runtime_stmt_proof_only _ _ body2_2_2 Hrest).
      rewrite runtime_seq_noop_l, !runtime_seq_noop_r.
      reflexivity.
  - (* ghost value *)
    cbn [hoist_atomic runtime_stmt]. rewrite IH. reflexivity.
Qed.

Theorem access_layout_erasure {D} (statement : stmt D) :
  forall names stack,
  runtime_stmt names stack (layout_accesses statement) =
    runtime_stmt names stack statement.
Proof.
  induction statement; intros names stack; cbn [layout_accesses];
    try reflexivity.
  - cbn. apply IHstatement.
  - cbn. rewrite IHstatement1, IHstatement2. reflexivity.
  - destruct statement1; cbn [runtime_stmt];
      try (rewrite IHstatement1, IHstatement2; reflexivity).
    rewrite layout_unfold_erasure. cbn [runtime_stmt].
    rewrite IHstatement2. reflexivity.
  - rewrite hoist_atomic_erasure.
    apply runtime_stmt_atomic_congruence. intros stack'. apply IHstatement.
  - cbn. apply IHstatement.
Qed.

Lemma distributed_access_erasure {Γ} (names : named_context Γ) stack invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation
      prefix' then_prefix' then_continuation' else_prefix'
      else_continuation' : stmt Γ) :
  proof_onlyb prefix = true ->
  runtime_stmt names stack prefix' = runtime_stmt names stack prefix ->
  runtime_stmt names stack then_prefix' =
    runtime_stmt names stack then_prefix ->
  runtime_stmt names stack else_prefix' =
    runtime_stmt names stack else_prefix ->
  runtime_stmt names stack then_continuation' =
    runtime_stmt names stack then_continuation ->
  runtime_stmt names stack else_continuation' =
    runtime_stmt names stack else_continuation ->
  runtime_stmt names stack
      (distributed_access invariant arguments prefix' guard then_prefix'
        then_continuation' else_prefix' else_continuation') =
    runtime_stmt names stack
      (conditional_access invariant arguments prefix guard then_prefix
        then_continuation else_prefix else_continuation).
Proof.
  intros Hprefix Hq Htp Hep Hthen Helse.
  destruct guard; cbn [distributed_access conditional_access guard_if
    canonical_branch runtime_stmt];
    rewrite ?Hq, ?Htp, ?Hep, ?Hthen, ?Helse,
      (runtime_stmt_proof_only names stack prefix Hprefix);
    reflexivity.
Qed.

Lemma factored_access_erasure {Γ} (names : named_context Γ) stack invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation
      prefix' then_continuation' else_continuation' : stmt Γ) :
  proof_onlyb then_prefix = true ->
  proof_onlyb else_prefix = true ->
  runtime_stmt names stack prefix' = runtime_stmt names stack prefix ->
  runtime_stmt names stack then_continuation' =
    runtime_stmt names stack then_continuation ->
  runtime_stmt names stack else_continuation' =
    runtime_stmt names stack else_continuation ->
  runtime_stmt names stack
      (factored_access invariant arguments prefix' guard then_prefix
        then_continuation' else_prefix else_continuation') =
    runtime_stmt names stack
      (conditional_access invariant arguments prefix guard then_prefix
        then_continuation else_prefix else_continuation).
Proof.
  intros Hthen_prefix Helse_prefix Hq Hthen Helse.
  destruct guard; cbn [factored_access conditional_access guard_if
    canonical_branch runtime_stmt];
    rewrite ?(runtime_stmt_proof_only names stack then_prefix Hthen_prefix),
      ?(runtime_stmt_proof_only names stack else_prefix Helse_prefix), Hq.
  - rewrite Hthen, Helse. cbn. rewrite runtime_seq_noop_r. reflexivity.
  - cbn. rewrite !runtime_seq_noop_r. reflexivity.
Qed.

End WithSignature.
End ConditionalErasure.
