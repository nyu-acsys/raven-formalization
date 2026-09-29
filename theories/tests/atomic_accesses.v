From Coq Require Import List PArith.
From stdpp Require Import gmap.

From raven Require Import verification.expressions verification.assertions
  verification.ir verification.access_layout analysis.normalization_base
  soundness.runtime_model soundness.rule_validity examples.mono_nat_ra
  examples.counter_monotonic tests.conditional_accesses.

Import ListNotations.

(** Invariant accesses inside trusted atomic blocks.  An access spanning the
    block is moved around it by the elaborator's layout pass; an access that
    leaks out of the block, or is followed by a physical step inside it, is
    rejected. *)
Module AtomicAccesses.
Import CounterMonotonic ConditionalAccesses.
Import Core IR IR.Core.

#[local] Existing Instances CounterRAConfig.ra_config counter_logic.
#[local] Instance test_contracts :
  RuleValidity.Hoare.ResourceHoare.ResourceContractEnv :=
  RuleValidity.Hoare.module_contracts counter_module.

Definition normalize {Γ} (statement : stmt Γ) : option (stmt Γ) :=
  NormalizationBase.restricted_analyze_and_normalize
    (AccessLayout.layout_accesses statement).

(** [atomic { unfold I(x); fold I(x) }] *)
Definition access_in_atomic : stmt Γ :=
  TAtomic (TSeq open_counter close_counter).

Lemma access_in_atomic_accepted :
  Atomicity.analyze (closed initial_counter_mask) access_in_atomic =
    inr (closed initial_counter_mask).
Proof. vm_compute. reflexivity. Qed.

Lemma access_in_atomic_normalized :
  normalize access_in_atomic =
    Some (TInvAccess counter_invariant invariant_arguments (TAtomic TDone)).
Proof. vm_compute. reflexivity. Qed.

(** Nested accesses inside one block are moved around it in order. *)
Definition nested_in_atomic : stmt Γ :=
  TAtomic (TSeq open_counter
    (TSeq open_nested (TSeq TDone (TSeq close_nested close_counter)))).

Lemma nested_in_atomic_normalized :
  normalize nested_in_atomic =
    Some (TInvAccess counter_invariant invariant_arguments
      (TInvAccess nested_invariant nested_arguments (TAtomic TDone))).
Proof. vm_compute. reflexivity. Qed.

(** An access opened inside a block must close inside it. *)
Definition leaked_access : stmt Γ :=
  TSeq (TAtomic (TSeq open_counter (TAtomic TDone))) close_counter.

Lemma leaked_access_rejected :
  Atomicity.analyze (closed initial_counter_mask) leaked_access =
    inl Atomicity.AtomicBlockLeaksAccess.
Proof. vm_compute. reflexivity. Qed.

(** A physical step after the fold stays inside the block, so the access
    cannot be moved around it. *)
Definition physical_after_fold : stmt Γ :=
  TAtomic (TSeq open_counter
    (TSeq TDone (TSeq close_counter (TAtomic TDone)))).

Lemma physical_after_fold_rejected :
  normalize physical_after_fold = None.
Proof. vm_compute. reflexivity. Qed.

End AtomicAccesses.
