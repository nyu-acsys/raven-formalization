From iris.base_logic Require Import fancy_updates.
From iris.proofmode Require Import tactics.

From raven_iris.rich_raven_lang Require Import typed_conditional_slice.

(** Iris instantiation boundary for the conditional normalization slice.

    A Raven adapter supplies the WP of one normalized chunk and the WP rule
    selecting a conditional arm.  All continuation threading—including the
    distinct post-close suffix of each arm—is then fixed by the generic slice
    denotation. *)
Module Type IRIS_CONDITIONAL_SLICE_SEMANTICS
    (P : CONDITIONAL_SLICE_PAYLOAD).
  Parameter Σ : gFunctors.

  Parameter chunk_wp : forall entry stack_in exit stack_out,
    P.chunk entry stack_in exit stack_out -> iProp Σ -> iProp Σ.

  Parameter conditional_wp : forall entry then_exit else_exit join,
    P.conditional entry then_exit else_exit join ->
    iProp Σ -> iProp Σ -> iProp Σ.

  Parameter chunk_wp_mono : forall entry stack_in exit stack_out
      (piece : P.chunk entry stack_in exit stack_out) left right,
    (left ⊢ right) ->
    chunk_wp _ _ _ _ piece left ⊢ chunk_wp _ _ _ _ piece right.

  Parameter conditional_wp_mono : forall entry then_exit else_exit join
      (test : P.conditional entry then_exit else_exit join)
      then_left then_right else_left else_right,
    (then_left ⊢ then_right) ->
    (else_left ⊢ else_right) ->
    conditional_wp _ _ _ _ test then_left else_left ⊢
      conditional_wp _ _ _ _ test then_right else_right.
End IRIS_CONDITIONAL_SLICE_SEMANTICS.

Module IrisConditionalSlice (P : CONDITIONAL_SLICE_PAYLOAD)
    (N : CONDITIONAL_SLICE_INTERFACE P)
    (I : IRIS_CONDITIONAL_SLICE_SEMANTICS P).
  Module Semantics <: CONDITIONAL_SLICE_SEMANTICS P.
    Definition formula := iProp I.Σ.
    Definition chunk_wp := I.chunk_wp.
    Definition conditional_wp := I.conditional_wp.
  End Semantics.

  Module Order <: CONDITIONAL_SLICE_MONOTONE P Semantics.
    Definition entails (left right : Semantics.formula) := left ⊢ right.
    Lemma entails_refl proposition : entails proposition proposition.
    Proof. reflexivity. Qed.
    Lemma chunk_wp_mono entry stack_in exit stack_out piece left right :
      entails left right ->
      entails (Semantics.chunk_wp entry stack_in exit stack_out piece left)
        (Semantics.chunk_wp entry stack_in exit stack_out piece right).
    Proof. apply I.chunk_wp_mono. Qed.
    Lemma conditional_wp_mono entry then_exit else_exit join test
        then_left then_right else_left else_right :
      entails then_left then_right -> entails else_left else_right ->
      entails
        (Semantics.conditional_wp entry then_exit else_exit join test
          then_left else_left)
        (Semantics.conditional_wp entry then_exit else_exit join test
          then_right else_right).
    Proof. apply I.conditional_wp_mono. Qed.
  End Order.

  Module Denotation := ConditionalSliceDenotation P N Semantics.
  Module Monotonicity := ConditionalSliceMonotonicity P N Semantics Order.
End IrisConditionalSlice.
