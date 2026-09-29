From Coq Require Import List PArith.
From stdpp Require Import gmap.

From raven Require Import analysis.structured_certificates
  verification.expressions verification.assertions verification.ir
  verification.snapshots soundness.runtime_model soundness.rule_validity
  examples.mono_nat_ra examples.counter_monotonic.

Import ListNotations.

(** Regressions for instance keys: the analyzer tracks the available
    instances of an invariant by their arguments, closes accesses in LIFO
    order, and forgets the instances named by a local when leaving its
    scope. *)
Module InstanceKeys.
Import CounterMonotonic.
Import Core IR IR.Core.

#[local] Existing Instances CounterRAConfig.ra_config counter_logic.
#[local] Instance test_contracts :
  RuleValidity.Hoare.ResourceHoare.ResourceContractEnv :=
  RuleValidity.Hoare.module_contracts counter_module.

Module Atomicity := RuleValidity.GenericRegions.Atomicity.

(* [x] is at level 1 and [y] at level 0. *)
Notation Γ := [runtime_val TRef; runtime_val TRef].

Definition x_arguments :
    gexpr_list Γ (Assertion.invariant_args counter_invariant) :=
  ltac:(vm_compute; exact (PECons (PEVar (LHere eq_refl)) PENil)).
Definition y_arguments :
    gexpr_list Γ (Assertion.invariant_args counter_invariant) :=
  ltac:(vm_compute; exact (PECons (PEVar (LThere (LHere eq_refl))) PENil)).

Definition x_instance : Atomicity.mask_entry :=
  (counter_invariant, Some [Atomicity.AtomLevel 1]).
Definition y_instance : Atomicity.mask_entry :=
  (counter_invariant, Some [Atomicity.AtomLevel 0]).

(** An undeclared identifier without arguments. *)
Definition other_invariant : Core.inv_id := Pos.succ counter_invariant.
Definition other_arguments :
    gexpr_list Γ (Assertion.invariant_args other_invariant) :=
  ltac:(vm_compute; exact PENil).

Definition state (entries : gset Atomicity.mask_entry) :
    Atomicity.analysis_state :=
  Atomicity.AnalysisState entries [] false false.

Definition closed (available : gset Core.inv_id) : Atomicity.analysis_state :=
  state (Atomicity.declaration_entries available).

(** Two allocated instances are available separately; an access to one
    consumes and restores exactly its own entry. *)
Definition two_instances : stmt Γ :=
  TSeq (TFold counter_invariant x_arguments)
    (TSeq (TFold counter_invariant y_arguments)
      (TSeq (TUnfold counter_invariant x_arguments)
        (TFold counter_invariant x_arguments))).

Lemma two_instances_accepted :
  Atomicity.analyze (closed ∅) two_instances =
    inr (state {[x_instance; y_instance]}).
Proof. vm_compute. reflexivity. Qed.

(** Declaration-wide availability may open any keyed instance, and closing
    restores the declaration-wide entry rather than replacing it with the
    selected instance. *)
Definition declaration_wide_round_trip : stmt Γ :=
  TSeq (TUnfold counter_invariant x_arguments)
    (TFold counter_invariant x_arguments).

Lemma declaration_wide_round_trip_restores_entry :
  Atomicity.analyze (closed {[counter_invariant]})
      declaration_wide_round_trip =
    inr (closed {[counter_invariant]}).
Proof. vm_compute. reflexivity. Qed.

(** Until the per-instance Iris world is introduced, a second instance of
    an already-open declaration is rejected even when its key differs. *)
Definition reentrant_other_instance : stmt Γ :=
  TSeq (TUnfold counter_invariant x_arguments)
    (TUnfold counter_invariant y_arguments).

Lemma reentrant_other_instance_rejected :
  Atomicity.analyze (closed {[counter_invariant]})
      reentrant_other_instance =
    inl (Atomicity.ReentrantInvariant counter_invariant).
Proof. vm_compute. reflexivity. Qed.

(** An allocated instance does not make another instance available. *)
Definition other_instance_missing : stmt Γ :=
  TSeq (TFold counter_invariant x_arguments)
    (TUnfold counter_invariant y_arguments).

Lemma other_instance_missing_rejected :
  Atomicity.analyze (closed ∅) other_instance_missing =
    inl (Atomicity.MissingInvariant counter_invariant).
Proof. vm_compute. reflexivity. Qed.

(** A fold closes the instance its access opened. *)
Definition mismatched_fold : stmt Γ :=
  TSeq (TUnfold counter_invariant x_arguments)
    (TFold counter_invariant y_arguments).

Lemma mismatched_fold_rejected :
  Atomicity.analyze (closed {[counter_invariant]}) mismatched_fold =
    inl (Atomicity.NonLifoFold counter_invariant).
Proof. vm_compute. reflexivity. Qed.

(** Accesses close in LIFO order. *)
Definition crossed_accesses : stmt Γ :=
  TSeq (TUnfold counter_invariant x_arguments)
    (TSeq (TUnfold other_invariant other_arguments)
      (TSeq (TFold counter_invariant x_arguments)
        (TFold other_invariant other_arguments))).

Lemma crossed_accesses_rejected :
  Atomicity.analyze (closed {[counter_invariant; other_invariant]})
      crossed_accesses =
    inl (Atomicity.NonLifoFold counter_invariant).
Proof. vm_compute. reflexivity. Qed.

(** [ghost val g := x; ...], with [g] at level 2. *)
Definition g_arguments :
    gexpr_list (ghost_val TRef :: Γ)
      (Assertion.invariant_args counter_invariant) :=
  ltac:(vm_compute; exact (PECons (PEVar (LHere eq_refl)) PENil)).

Definition in_scope (body : stmt (ghost_val TRef :: Γ)) : stmt Γ :=
  TGhostVal Snapshots.snapshot_name TRef (PEVar (LHere eq_refl)) body.

(** An instance allocated under the name of a ghost value is forgotten when
    its scope ends. *)
Lemma scoped_allocation_forgotten :
  Atomicity.analyze (closed ∅)
      (in_scope (TFold counter_invariant g_arguments)) =
    inr (closed ∅).
Proof. vm_compute. reflexivity. Qed.

(** An access may not remain open past the scope of its argument. *)
Lemma scoped_access_leak_rejected :
  Atomicity.analyze (closed {[counter_invariant]})
      (in_scope (TUnfold counter_invariant g_arguments)) =
    inl Atomicity.ScopeLeaksAccess.
Proof. vm_compute. reflexivity. Qed.

End InstanceKeys.
