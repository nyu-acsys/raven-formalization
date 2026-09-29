From Coq Require Import List PArith.
From stdpp Require Import gmap.

From raven Require Import analysis.structured_certificates
  verification.expressions verification.assertions verification.ir
  verification.snapshots analysis.normalization_base soundness.runtime_model
  soundness.rule_validity examples.mono_nat_ra examples.counter_monotonic.

Import ListNotations.

(** Regressions for invariant-argument snapshots: an access whose argument
    variable is reassigned inside it is rejected as written and accepted
    once its argument is snapshotted. *)
Module ArgumentSnapshots.
Import CounterMonotonic.
Import Core IR IR.Core.

#[local] Existing Instances CounterRAConfig.ra_config counter_logic.
#[local] Instance test_contracts :
  RuleValidity.Hoare.ResourceHoare.ResourceContractEnv :=
  RuleValidity.Hoare.module_contracts counter_module.

Module Atomicity := RuleValidity.GenericRegions.Atomicity.

(* [y] names the instance; [z] is written into it inside the access. *)
Notation Γ := [runtime_var TRef; runtime_var TRef].

Definition y {keep} (Hkeep : keep (runtime_var TRef) = true) :
    pexpr keep Γ TRef :=
  PEVar (LHere Hkeep).
Definition z : rexpr Γ TRef := PEVar (LThere (LHere eq_refl)).

Definition arguments :
    gexpr_list Γ (Assertion.invariant_args counter_invariant) :=
  ltac:(vm_compute; exact (PECons (y eq_refl) PENil)).

(** [unfold I(y); y := z; fold I(y)] *)
Definition reassigned_argument : stmt Γ :=
  TSeq (TUnfold counter_invariant arguments)
    (TSeq (TAssign false (LHere eq_refl) z)
      (TFold counter_invariant arguments)).

Definition closed (available : gset Core.inv_id) : Atomicity.analysis_state :=
  Atomicity.AnalysisState available ∅ false false.

Lemma reassigned_argument_unstable :
  NormalizationBase.restricted_fragment_check reassigned_argument = false.
Proof. vm_compute. reflexivity. Qed.

(** [ghost val g := y; unfold I(g); y := z; fold I(g); assert (g == y)] *)
Lemma reassigned_argument_snapshot :
  Snapshots.snapshot_accesses reassigned_argument =
    TGhostVal Snapshots.snapshot_name TRef (y eq_refl)
      (TSeq (TUnfold counter_invariant
          ltac:(vm_compute; exact (PECons (PEVar (LHere eq_refl)) PENil)))
        (TSeq (TAssign false (LThere (LHere eq_refl))
            (PEVar (LThere (LThere (LHere eq_refl)))))
          (TSeq (TFold counter_invariant
              ltac:(vm_compute; exact (PECons (PEVar (LHere eq_refl)) PENil)))
            (TAssert (PEBinOp (BEq TRef) (PEVar (LHere eq_refl))
              (PEVar (LThere (LHere eq_refl)))))))).
Proof. vm_compute. reflexivity. Qed.

Lemma snapshot_argument_stable :
  NormalizationBase.restricted_fragment_check
    (Snapshots.snapshot_accesses reassigned_argument) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma snapshot_argument_analyzed :
  Atomicity.analyze_lifo (closed {[counter_invariant]})
    (Snapshots.snapshot_accesses reassigned_argument) =
    Some (closed {[counter_invariant]}).
Proof. vm_compute. reflexivity. Qed.

(** [unfold I(y); if (b) { fold I(y) } else { fold I(y) }]: the branch-local
    folds make the control result of the conditional worth saving. *)
Definition b {keep} (Hkeep : keep (runtime_var TRef) = true) :
    pexpr keep Γ TBool :=
  PEBinOp (BEq TRef) (y Hkeep) (PEVar (LThere (LHere Hkeep))).

Definition branch_local_folds : stmt Γ :=
  TSeq (TUnfold counter_invariant arguments)
    (TIf (b eq_refl)
      (TFold counter_invariant arguments)
      (TFold counter_invariant arguments)).

Definition snapshot_fold : stmt (ghost_val TBool :: ghost_val TRef :: Γ) :=
  TSeq (TFold counter_invariant
      ltac:(vm_compute; exact (PECons (PEVar (LThere (LHere eq_refl))) PENil)))
    (TAssert (PEBinOp (BEq TRef) (PEVar (LThere (LHere eq_refl)))
      (PEVar (LThere (LThere (LHere eq_refl)))))).

(** [ghost val g := y; unfold I(g); ghost val gb := b; if (b) { fold I(g);
    assert (g == y) } else { ... }] *)
Lemma branch_local_folds_snapshot :
  Snapshots.snapshot_accesses branch_local_folds =
    TGhostVal Snapshots.snapshot_name TRef (y eq_refl)
      (TSeq (TUnfold counter_invariant
          ltac:(vm_compute; exact (PECons (PEVar (LHere eq_refl)) PENil)))
        (TGhostVal Snapshots.guard_snapshot_name TBool
          (PEBinOp (BEq TRef) (PEVar (LThere (LHere eq_refl)))
            (PEVar (LThere (LThere (LHere eq_refl)))))
          (TIf
            (PEBinOp (BEq TRef) (PEVar (LThere (LThere (LHere eq_refl))))
              (PEVar (LThere (LThere (LThere (LHere eq_refl))))))
            snapshot_fold snapshot_fold))).
Proof. vm_compute. reflexivity. Qed.

Lemma branch_local_folds_analyzed :
  Atomicity.analyze_lifo (closed {[counter_invariant]})
    (Snapshots.snapshot_accesses branch_local_folds) =
    Some (closed {[counter_invariant]}).
Proof. vm_compute. reflexivity. Qed.

End ArgumentSnapshots.
