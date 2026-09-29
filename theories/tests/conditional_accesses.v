From Coq Require Import List PArith.
From stdpp Require Import gmap.

From raven Require Import analysis.structured_certificates
  verification.expressions verification.assertions verification.ir
  analysis.normalization_base soundness.runtime_model soundness.rule_validity
  examples.mono_nat_ra examples.counter_monotonic.

Import ListNotations.

(** Focused analyzer regressions for representative LIFO conditional shapes.
    These deliberately check only that analysis succeeds and returns the
    precise joined state; normalization and Hoare proofs are exercised
    separately. *)
Module ConditionalAccesses.
Import CounterMonotonic.
Import Core IR IR.Core.

#[local] Existing Instances CounterRAConfig.ra_config counter_logic.
#[local] Instance test_contracts :
  RuleValidity.Hoare.ResourceHoare.ResourceContractEnv :=
  RuleValidity.Hoare.module_contracts counter_module.

Module Atomicity := RuleValidity.GenericRegions.Atomicity.

(* Both inputs are ordinary runtime [val]s: the analyzer must preserve their
   availability across conditionals and invariant accesses without treating
   them as writable variables or proof-only ghost values. *)
Notation Γ := [runtime_val TRef; runtime_val TBool].

Definition x {keep} (Hkeep : keep (runtime_val TRef) = true) :
    pexpr keep Γ TRef :=
  PEVar (LHere Hkeep).
Definition b : rexpr Γ TBool := PEVar (LThere (LHere eq_refl)).

Definition invariant_arguments :
    gexpr_list Γ (Assertion.invariant_args counter_invariant) :=
  ltac:(vm_compute; exact (PECons (x eq_refl) PENil)).

Definition read_arguments :
    rexpr_list Γ (Assertion.procedure_args read_procedure) :=
  ltac:(vm_compute; exact (PECons (x eq_refl) PENil)).

Definition open_counter : stmt Γ :=
  TUnfold counter_invariant invariant_arguments.
Definition close_counter : stmt Γ :=
  TFold counter_invariant invariant_arguments.
Definition counter_access : stmt Γ :=
  TSeq open_counter close_counter.

Definition initial_counter_mask : gset Core.inv_id := {[counter_invariant]}.
Definition closed (available : gset Core.inv_id) : Atomicity.analysis_state :=
  Atomicity.AnalysisState available ∅ false false.

(** 1. The conditional is wholly inside the access, which has one shared
    trailing fold. *)
Definition shared_trailing_fold : stmt Γ :=
  TSeq open_counter
    (TSeq (TIf b TDone TDone) close_counter).

Lemma shared_trailing_fold_accepted :
  Atomicity.analyze_lifo (closed initial_counter_mask) shared_trailing_fold =
    Some (closed initial_counter_mask).
Proof. vm_compute. reflexivity. Qed.

(** 2. Each branch closes the access independently. *)
Definition branch_local_folds : stmt Γ :=
  TSeq open_counter
    (TIf b (TSeq TDone close_counter) (TSeq TDone close_counter)).

Lemma branch_local_folds_accepted :
  Atomicity.analyze_lifo (closed initial_counter_mask) branch_local_folds =
    Some (closed initial_counter_mask).
Proof. vm_compute. reflexivity. Qed.

(** 3. A trusted physical step occurs while the invariant is open, before
    either branch closes it. *)
Definition physical_step_before_branch_folds : stmt Γ :=
  TSeq open_counter
    (TSeq (TAtomic TDone)
      (TIf b (TSeq TDone close_counter) (TSeq TDone close_counter))).

Lemma physical_step_before_branch_folds_accepted :
  Atomicity.analyze_lifo (closed initial_counter_mask)
      physical_step_before_branch_folds = Some (closed initial_counter_mask).
Proof. vm_compute. reflexivity. Qed.

(** A fresh, undeclared identifier lets these analyzer-only programs
    exercise proper nesting.  Undeclared invariants have the signature's
    default empty argument context. *)
Definition nested_invariant : Core.inv_id := Pos.succ counter_invariant.
Definition nested_arguments :
    gexpr_list Γ (Assertion.invariant_args nested_invariant) :=
  ltac:(vm_compute; exact PENil).
Definition open_nested : stmt Γ := TUnfold nested_invariant nested_arguments.
Definition close_nested : stmt Γ := TFold nested_invariant nested_arguments.
Definition nested_mask : gset Core.inv_id :=
  {[counter_invariant; nested_invariant]}.

(** 4. A nested access appears in just one branch; both branches also close
    the outer access. *)
Definition nested_in_one_branch : stmt Γ :=
  TSeq open_counter
    (TIf b
      (TSeq open_nested (TSeq close_nested close_counter))
      close_counter).

Lemma nested_in_one_branch_accepted :
  Atomicity.analyze_lifo (closed nested_mask) nested_in_one_branch =
    Some (closed nested_mask).
Proof. vm_compute. reflexivity. Qed.

(** Nested accesses may also occur in both branches. *)
Definition nested_in_both_branches : stmt Γ :=
  TSeq open_counter
    (TIf b
      (TSeq open_nested (TSeq close_nested close_counter))
      (TSeq open_nested (TSeq close_nested close_counter))).

Lemma nested_in_both_branches_accepted :
  Atomicity.analyze_lifo (closed nested_mask) nested_in_both_branches =
    Some (closed nested_mask).
Proof. vm_compute. reflexivity. Qed.

(** 5. The branches take different physical continuations after their local
    folds: one executes a trusted atomic block and one calls [read]. *)
Definition different_physical_continuations : stmt Γ :=
  TSeq open_counter
    (TIf b
      (TSeq close_counter (TAtomic TDone))
      (TSeq close_counter (TCall read_procedure read_arguments CTDiscard))).

Lemma different_physical_continuations_accepted :
  Atomicity.analyze_lifo (closed counter_mask)
      different_physical_continuations =
    Some (closed initial_counter_mask).
Proof. vm_compute. reflexivity. Qed.

(** 6. After closing the outer access, either branch may perform any finite
    number of balanced reopen/close pairs. *)
Fixpoint balanced_pairs (count : nat) : stmt Γ :=
  match count with
  | O => TDone
  | S count' => TSeq open_counter (TSeq close_counter (balanced_pairs count'))
  end.

Definition close_then_pairs (count : nat) : stmt Γ :=
  TSeq close_counter (balanced_pairs count).

Definition arbitrary_balanced_pairs : stmt Γ :=
  TSeq open_counter
    (TIf b (close_then_pairs 3) (close_then_pairs 2)).

Lemma arbitrary_balanced_pairs_accepted :
  Atomicity.analyze_lifo (closed counter_mask) arbitrary_balanced_pairs =
    Some (closed counter_mask).
Proof. vm_compute. reflexivity. Qed.

End ConditionalAccesses.
