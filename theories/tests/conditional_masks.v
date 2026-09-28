From Coq Require Import List.
From stdpp Require Import gmap.

From raven Require Import analysis.structured_certificates verification.expressions verification.assertions verification.ir analysis.normalization_base soundness.runtime_model soundness.rule_validity examples.mono_nat_ra examples.counter_monotonic.

Import ListNotations.

(** Regression tests for conditional joins: an invariant allocated in only
    one branch is dropped from the joined mask, the program is accepted, and
    the continuation is checked against the joined mask. *)
Module ConditionalMasks.
Import CounterMonotonic.
Import Core IR IR.Core.

#[local] Existing Instances CounterRAConfig.ra_config counter_logic.
#[local] Instance test_contracts :
  RuleValidity.Hoare.ResourceHoare.ResourceContractEnv :=
  RuleValidity.Hoare.module_contracts counter_module.

Module Atomicity := RuleValidity.GenericRegions.Atomicity.

(** Local variables [x : Ref] and [b : Bool]. *)
Notation Γ := [TRef; TBool].

Definition x : pexpr Γ TRef := PEVar MHere.
Definition b : pexpr Γ TBool := PEVar (MThere MHere).

Definition invariant_arguments :
    pexpr_list Γ (Assertion.invariant_args counter_invariant) :=
  ltac:(vm_compute; exact (PECons x PENil)).

Definition read_arguments :
    pexpr_list Γ (Assertion.procedure_args read_procedure) :=
  ltac:(vm_compute; exact (PECons x PENil)).

Definition allocate : stmt Γ := TFold counter_invariant invariant_arguments.

Definition access : stmt Γ :=
  TSeq (TUnfold counter_invariant invariant_arguments)
    (TFold counter_invariant invariant_arguments).

Definition call_read : stmt Γ :=
  TCall read_procedure read_arguments CTDiscard.

Definition allocate_then : stmt Γ := TIf b allocate TDone.
Definition allocate_else : stmt Γ := TIf b TDone allocate.
Definition allocate_both : stmt Γ := TIf b allocate allocate.

Definition closed (available : gset inv_id) : Atomicity.analysis_state :=
  Atomicity.AnalysisState available ∅ false false.

(** Allocation in one branch is accepted; its credit is absent after the
    join. *)
Lemma allocate_then_accepted :
  Atomicity.analyze_lifo (closed ∅) allocate_then = Some (closed ∅).
Proof. vm_compute. reflexivity. Qed.

Lemma allocate_else_accepted :
  Atomicity.analyze_lifo (closed ∅) allocate_else = Some (closed ∅).
Proof. vm_compute. reflexivity. Qed.

Lemma allocate_both_accepted :
  Atomicity.analyze_lifo (closed ∅) allocate_both =
    Some (closed {[counter_invariant]}).
Proof. vm_compute. reflexivity. Qed.

(** Branches that differ only in an allocation already available join to
    the entry mask. *)
Lemma allocate_available_accepted :
  Atomicity.analyze_lifo (closed {[counter_invariant]}) allocate_then =
    Some (closed {[counter_invariant]}).
Proof. vm_compute. reflexivity. Qed.

(** Opening after a one-branch allocation is rejected by the joined mask. *)
Lemma access_after_allocate_then_rejected :
  Atomicity.analyze (closed ∅) (TSeq allocate_then access) =
    inl (Atomicity.MissingInvariant counter_invariant).
Proof. vm_compute. reflexivity. Qed.

Lemma access_after_allocate_both_accepted :
  Atomicity.analyze_lifo (closed ∅) (TSeq allocate_both access) =
    Some (closed {[counter_invariant]}).
Proof. vm_compute. reflexivity. Qed.

(** A call requiring the invariant sees the joined mask as well. *)
Lemma call_after_allocate_then_rejected :
  Atomicity.analyze (closed ∅) (TSeq allocate_then call_read) =
    inl Atomicity.MissingProcedureMask.
Proof. vm_compute. reflexivity. Qed.

Lemma call_after_allocate_both_accepted :
  Atomicity.analyze_lifo (closed ∅) (TSeq allocate_both call_read) =
    Some (closed {[counter_invariant]}).
Proof. vm_compute. reflexivity. Qed.

(** The one-branch program is in the fragment handled by normalization, and
    its footprint is covered by its allocations. *)
Lemma allocate_then_restricted :
  NormalizationBase.restricted_fragment_accepted allocate_then.
Proof. vm_compute. reflexivity. Qed.

Lemma allocate_then_allocations :
  Atomicity.statement_allocations allocate_then = {[counter_invariant]}.
Proof. vm_compute. reflexivity. Qed.

Lemma allocate_then_footprint :
  Atomicity.certificate_footprint
    (projT1 (Atomicity.analyze_lifo_builds_certificate (closed ∅)
      allocate_then (closed ∅) allocate_then_accepted)) ⊆
    {[counter_invariant]}.
Proof.
  etrans; [apply Atomicity.certificate_footprint_allocations|].
  rewrite allocate_then_allocations. cbn. set_solver.
Qed.

End ConditionalMasks.
