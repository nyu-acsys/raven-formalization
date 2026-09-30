From Coq Require Import List PArith.
From stdpp Require Import gmap.

From raven Require Import analysis.structured_certificates
  verification.expressions verification.assertions verification.ir
  verification.snapshots soundness.runtime_model soundness.rule_validity
  analysis.normalization_base
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
  Atomicity.closed_state entries.

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

(** A second instance of an open declaration is rejected unless an
    assertion that it differs from the open instances precedes it. *)
Definition reentrant_other_instance : stmt Γ :=
  TSeq (TUnfold counter_invariant x_arguments)
    (TUnfold counter_invariant y_arguments).

Lemma reentrant_other_instance_rejected :
  Atomicity.analyze (closed {[counter_invariant]})
      reentrant_other_instance =
    inl (Atomicity.ReentrantInvariant counter_invariant).
Proof. vm_compute. reflexivity. Qed.

(** [unfold I(x); assert (y != x); unfold I(y); fold I(y); fold I(x)],
    with the inner access laid out and guarded as the preprocessing
    produces it. *)
Definition distinct_from_x : gexpr Γ TBool :=
  IR.arguments_distinct y_arguments [x_arguments].

Definition nested_instances : stmt Γ :=
  TSeq (TUnfold counter_invariant x_arguments)
    (TSeq
      (TSeq (TSeq (TAssert distinct_from_x)
          (TUnfold counter_invariant y_arguments))
        (TSeq TDone (TFold counter_invariant y_arguments)))
      (TFold counter_invariant x_arguments)).

Lemma distinct_from_x_parses :
  IR.arguments_distinct_parse y_arguments distinct_from_x =
    Some [x_arguments].
Proof. vm_compute. reflexivity. Qed.

(** Both instances of the declaration are open at once. *)
Lemma nested_instances_accepted :
  Atomicity.analyze (closed {[counter_invariant]}) nested_instances =
    inr (closed {[counter_invariant]}).
Proof. vm_compute. reflexivity. Qed.

(** The assertion must exclude the open instance. *)
Definition misguarded_instances : stmt Γ :=
  TSeq (TUnfold counter_invariant x_arguments)
    (TSeq (TAssert (IR.arguments_distinct y_arguments [y_arguments]))
      (TUnfold counter_invariant y_arguments)).

Lemma misguarded_instances_rejected :
  Atomicity.analyze (closed {[counter_invariant]}) misguarded_instances =
    inl (Atomicity.ReentrantInvariant counter_invariant).
Proof. vm_compute. reflexivity. Qed.

(** The preprocessing generates the assertion. *)
Lemma nested_instances_generated :
  Snapshots.distinctness_assertions
    (TSeq (TUnfold counter_invariant x_arguments)
      (TSeq
        (TSeq (TUnfold counter_invariant y_arguments)
          (TSeq TDone (TFold counter_invariant y_arguments)))
        (TFold counter_invariant x_arguments))) = nested_instances.
Proof. vm_compute. reflexivity. Qed.

(** The normalizer accepts the guarded layout and nests the accesses. *)
Lemma nested_instances_normalized :
  NormalizationBase.restricted_analyze_and_normalize nested_instances =
    Some (TInvAccess counter_invariant x_arguments
      (TSeq (TAssert distinct_from_x)
        (TInvAccess counter_invariant y_arguments TDone))).
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

(** [g] is an alias of [x]: an instance allocated under [g] is [x]'s. *)
Lemma aliased_allocation :
  Atomicity.analyze (closed ∅)
      (in_scope (TFold counter_invariant g_arguments)) =
    inr (state {[x_instance]}).
Proof. vm_compute. reflexivity. Qed.

(** An access may not remain open past the scope of its argument. *)
Lemma scoped_access_leak_rejected :
  Atomicity.analyze (closed {[counter_invariant]})
      (in_scope (TUnfold counter_invariant g_arguments)) =
    inl Atomicity.ScopeLeaksAccess.
Proof. vm_compute. reflexivity. Qed.

(** ** Writes

    [x] is a [var] at level 1 and [y] a [val] at level 0. *)
Notation Γw := [runtime_var TRef; runtime_val TRef].

Definition xw_arguments :
    gexpr_list Γw (Assertion.invariant_args counter_invariant) :=
  ltac:(vm_compute; exact (PECons (PEVar (LHere eq_refl)) PENil)).

(** [x := y] *)
Definition overwrite_x {Γ'} (x : write_target false Γ' TRef)
    (y : rexpr Γ' TRef) : stmt Γ' :=
  TAssign false x y.

Definition write_x : stmt Γw :=
  overwrite_x (LHere (d := runtime_var TRef) eq_refl)
    (PEVar (LThere (LHere (d := runtime_val TRef) eq_refl))).

(** A write forgets the instances named by the written local. *)
Definition stale_instance : stmt Γw :=
  TSeq (TFold counter_invariant xw_arguments)
    (TSeq write_x (TUnfold counter_invariant xw_arguments)).

Lemma stale_instance_rejected :
  Atomicity.analyze (closed ∅) stale_instance =
    inl (Atomicity.MissingInvariant counter_invariant).
Proof. vm_compute. reflexivity. Qed.

(** [ghost val g := x; unfold I(g); body; fold I(g)] *)
Definition gw_arguments :
    gexpr_list (ghost_val TRef :: Γw)
      (Assertion.invariant_args counter_invariant) :=
  ltac:(vm_compute; exact (PECons (PEVar (LHere eq_refl)) PENil)).

Definition snapshot_access (body : stmt (ghost_val TRef :: Γw)) : stmt Γw :=
  TSeq (TFold counter_invariant xw_arguments)
    (TGhostVal Snapshots.snapshot_name TRef (PEVar (LHere eq_refl))
      (TSeq (TUnfold counter_invariant gw_arguments)
        (TSeq body (TFold counter_invariant gw_arguments)))).

(** Through its snapshot, an access to [x]'s instance consumes and restores
    [x]'s entry. *)
Lemma snapshot_access_restores :
  Atomicity.analyze (closed ∅) (snapshot_access TDone) =
    inr (state {[(counter_invariant, Some [Atomicity.AtomLevel 1])]}).
Proof. vm_compute. reflexivity. Qed.

(** When [x] is written inside the access, the instance is restored under
    the snapshot, and forgotten with it. *)
Lemma snapshot_access_written :
  Atomicity.analyze (closed ∅)
      (snapshot_access (overwrite_x
        (LThere (LHere (d := runtime_var TRef) eq_refl))
        (PEVar (LThere (LThere (LHere (d := runtime_val TRef) eq_refl)))))) =
    inr (state ∅).
Proof. vm_compute. reflexivity. Qed.

End InstanceKeys.
