From Coq Require Import List PArith.
From stdpp Require Import gmap.

From raven Require Import verification.expressions verification.assertions
  verification.ir verification.access_layout verification.snapshots
  verification.conditional_derivations analysis.normalization_base
  soundness.runtime_model soundness.rule_validity examples.mono_nat_ra
  examples.counter_monotonic tests.conditional_accesses.

Import ListNotations.

(** Normalization of the conditional-access programs of [ConditionalAccesses]
    after the elaborator's layout pass, of their ghost-guarded counterparts,
    and of grouped and nested accesses. *)
Module ConditionalNormalization.
Import CounterMonotonic ConditionalAccesses ConditionalDerivations.
Import Core IR IR.Core.

#[local] Existing Instances CounterRAConfig.ra_config counter_logic.
#[local] Instance test_contracts :
  RuleValidity.Hoare.ResourceHoare.ResourceContractEnv :=
  RuleValidity.Hoare.module_contracts counter_module.

Definition normalize {Γ} (statement : stmt Γ) : option (stmt Γ) :=
  NormalizationBase.restricted_analyze_and_normalize
    (AccessLayout.layout_accesses statement).

Definition accepted {Γ} (statement : stmt Γ) : bool :=
  match normalize statement with Some _ => true | None => false end.

(** 1. A shared trailing fold is a linear access. *)
Lemma shared_trailing_fold_normalized :
  normalize shared_trailing_fold =
    Some (TInvAccess counter_invariant invariant_arguments (TIf b TDone TDone)).
Proof. vm_compute. reflexivity. Qed.

(** 2. Nothing physical precedes the conditional: the access is
    distributed. *)
Lemma branch_local_folds_normalized :
  normalize branch_local_folds =
    Some (distributed_access counter_invariant invariant_arguments TDone
      (GuardRuntime b) TDone TDone TDone TDone).
Proof. vm_compute. reflexivity. Qed.

(** 3. A physical step precedes the conditional: the access is factored. *)
Lemma physical_step_before_branch_folds_normalized :
  normalize physical_step_before_branch_folds =
    Some (factored_access counter_invariant invariant_arguments
      (TAtomic TDone) (GuardRuntime b) TDone TDone TDone TDone).
Proof. vm_compute. reflexivity. Qed.

(** 4. An access nested inside the outer one becomes an access in the
    branch prefix. *)
Lemma nested_in_one_branch_normalized :
  normalize nested_in_one_branch =
    Some (distributed_access counter_invariant invariant_arguments TDone
      (GuardRuntime b) (TInvAccess nested_invariant nested_arguments TDone)
      TDone TDone TDone).
Proof. vm_compute. reflexivity. Qed.

Lemma nested_in_both_branches_normalized :
  normalize nested_in_both_branches =
    Some (distributed_access counter_invariant invariant_arguments TDone
      (GuardRuntime b) (TInvAccess nested_invariant nested_arguments TDone)
      TDone (TInvAccess nested_invariant nested_arguments TDone) TDone).
Proof. vm_compute. reflexivity. Qed.

(** 5. The branches continue with different physical steps. *)
Lemma different_physical_continuations_normalized :
  normalize different_physical_continuations =
    Some (distributed_access counter_invariant invariant_arguments TDone
      (GuardRuntime b) TDone (TAtomic TDone) TDone
      (TCall read_procedure read_arguments CTDiscard)).
Proof. vm_compute. reflexivity. Qed.

(** 6. Balanced reopen/close pairs after the branch-local close. *)
Lemma arbitrary_balanced_pairs_normalized :
  accepted arbitrary_balanced_pairs = true.
Proof. vm_compute. reflexivity. Qed.

(** The same programs after argument snapshots. *)
Lemma snapshot_programs_normalized :
  accepted (Snapshots.snapshot_accesses shared_trailing_fold) &&
  accepted (Snapshots.snapshot_accesses branch_local_folds) &&
  accepted (Snapshots.snapshot_accesses nested_in_one_branch) &&
  accepted (Snapshots.snapshot_accesses physical_step_before_branch_folds) &&
  accepted (Snapshots.snapshot_accesses different_physical_continuations) &&
  accepted (Snapshots.snapshot_accesses arbitrary_balanced_pairs) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Grouping

    The statements before an access's close form its body or prefix, and a
    conditional access followed by further statements is grouped with its
    unfold. *)

Definition grouped_body : stmt Γ :=
  TSeq open_counter (TSeq (TAtomic TDone) (TSeq TDone close_counter)).

Lemma grouped_body_normalized :
  normalize grouped_body =
    Some (TInvAccess counter_invariant invariant_arguments
      (TSeq (TAtomic TDone) TDone)).
Proof. vm_compute. reflexivity. Qed.

Definition conditional_mid_sequence : stmt Γ :=
  TSeq open_counter
    (TSeq (TIf b (TSeq TDone close_counter) (TSeq TDone close_counter))
      (TAtomic TDone)).

Lemma conditional_mid_sequence_normalized :
  normalize conditional_mid_sequence =
    Some (TSeq
      (distributed_access counter_invariant invariant_arguments TDone
        (GuardRuntime b) TDone TDone TDone TDone)
      (TAtomic TDone)).
Proof. vm_compute. reflexivity. Qed.

(** A conditional access to [nested_invariant] inside a linear access. *)
Definition conditional_in_linear : stmt Γ :=
  TSeq open_counter
    (TSeq open_nested (TSeq (TIf b close_nested close_nested) close_counter)).

Lemma conditional_in_linear_accepted :
  Atomicity.analyze_lifo (closed nested_mask) conditional_in_linear =
    Some (closed nested_mask).
Proof. vm_compute. reflexivity. Qed.

Lemma conditional_in_linear_normalized :
  normalize conditional_in_linear =
    Some (TInvAccess counter_invariant invariant_arguments
      (distributed_access nested_invariant nested_arguments TDone
        (GuardRuntime b) TDone TDone TDone TDone)).
Proof. vm_compute. reflexivity. Qed.

(** A branch prefix after a physical step must be proof-only. *)
Definition physical_branch_prefix : stmt Γ :=
  TSeq open_counter
    (TSeq (TAtomic TDone)
      (TIf b (TSeq (TAtomic TDone) close_counter) close_counter)).

Lemma physical_branch_prefix_rejected :
  normalize physical_branch_prefix = None.
Proof. vm_compute. reflexivity. Qed.

(** ** Ghost guards *)

(* The guard [g] is a ghost value. *)
Notation Γg := [runtime_val TRef; ghost_val TBool].

Definition xg {keep} (Hkeep : keep (runtime_val TRef) = true) :
    pexpr keep Γg TRef :=
  PEVar (LHere Hkeep).
Definition g : gexpr Γg TBool := PEVar (LThere (LHere eq_refl)).

Definition ghost_arguments :
    gexpr_list Γg (Assertion.invariant_args counter_invariant) :=
  ltac:(vm_compute; exact (PECons (xg eq_refl) PENil)).

Definition ghost_open : stmt Γg := TUnfold counter_invariant ghost_arguments.
Definition ghost_close : stmt Γg := TFold counter_invariant ghost_arguments.

Definition ghost_branch_local_folds : stmt Γg :=
  TSeq ghost_open (TGhostIf g ghost_close ghost_close).

Lemma ghost_branch_local_folds_normalized :
  normalize ghost_branch_local_folds =
    Some (distributed_access counter_invariant ghost_arguments TDone
      (GuardGhost g) TDone TDone TDone TDone).
Proof. vm_compute. reflexivity. Qed.

Definition ghost_physical_step_before_branch_folds : stmt Γg :=
  TSeq ghost_open
    (TSeq (TAtomic TDone) (TGhostIf g ghost_close ghost_close)).

Lemma ghost_physical_step_before_branch_folds_normalized :
  normalize ghost_physical_step_before_branch_folds =
    Some (factored_access counter_invariant ghost_arguments (TAtomic TDone)
      (GuardGhost g) TDone TDone TDone TDone).
Proof. vm_compute. reflexivity. Qed.

End ConditionalNormalization.
