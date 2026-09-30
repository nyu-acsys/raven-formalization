From Coq Require Import List PArith.
From stdpp Require Import gmap.

From raven Require Import analysis.structured_certificates
  verification.expressions verification.assertions verification.ir
  verification.masks soundness.runtime_model soundness.rule_validity
  examples.mono_nat_ra examples.counter_monotonic.

Import ListNotations.

(** Focused regressions for inferred call effects and for the local writes
    which invalidate instance keys. *)
Module MaskEffects.
Import CounterMonotonic.
Import Core IR IR.Core.

#[local] Existing Instances CounterRAConfig.ra_config counter_logic.
#[local] Instance test_contracts :
  RuleValidity.Hoare.ResourceHoare.ResourceContractEnv :=
  RuleValidity.Hoare.module_contracts counter_module.

Module Atomicity := RuleValidity.GenericRegions.Atomicity.
Module Effects := Runtime.CertifiedRegions.

(** If an actual argument is not representable by an analyzer atom, a
    required keyed instance is conservatively widened to its declaration. *)
Lemma inexpressible_requirement_widens :
  Effects.instantiate_requirement [None]
      (counter_invariant, Some [Masks.TemplateFormal 0]) =
    (counter_invariant, None).
Proof. reflexivity. Qed.

(** Grants cannot soundly be widened: if their result or actual argument is
    inexpressible, the keyed grant is omitted. *)
Lemma inexpressible_formal_grant_dropped :
  Effects.instantiate_grant [None] None
      (counter_invariant, Some [Masks.TemplateFormal 0]) = None.
Proof. reflexivity. Qed.

Lemma inexpressible_return_grant_dropped :
  Effects.instantiate_grant [] None
      (counter_invariant, Some [Masks.TemplateReturn]) = None.
Proof. reflexivity. Qed.

(** Spawning checks the inferred requirements just like calling, without
    returning grants to the spawning thread. *)
Notation Gspawn := [runtime_val TRef].

Definition spawn_arguments :
    rexpr_list Gspawn (Assertion.procedure_args read_procedure) :=
  ltac:(vm_compute; exact (PECons (PEVar (LHere eq_refl)) PENil)).

Definition spawn_read : stmt Gspawn :=
  TSpawn read_procedure spawn_arguments.

Definition spawn_instance : Atomicity.mask_entry :=
  (counter_invariant, Some [Atomicity.AtomLevel 0]).

Lemma spawn_missing_requirement_rejected :
  Atomicity.analyze (Atomicity.closed_state ∅) spawn_read =
    inl Atomicity.MissingProcedureMask.
Proof. vm_compute. reflexivity. Qed.

Lemma spawn_exact_requirement_accepted :
  Atomicity.analyze (Atomicity.closed_state {[spawn_instance]}) spawn_read =
    inr (Atomicity.closed_state {[spawn_instance]}).
Proof. vm_compute. reflexivity. Qed.

(** Every statement which stores into a local reports that local to the
    analyzer.  These checks prevent a new physical leaf from silently
    bypassing stale-key invalidation. *)
Notation Gassign := [runtime_var TRef; runtime_val TRef].

Definition assign_leaf : stmt Gassign :=
  TAssign false (LHere (d := runtime_var TRef) eq_refl)
    (PEVar (LThere (LHere (d := runtime_val TRef) eq_refl))).

Lemma assignment_reports_write :
  RegionSyntax.write assign_leaf = Some 1.
Proof. reflexivity. Qed.

Notation Gread := [runtime_var TInt; runtime_val TRef].

Definition field_read_leaf : stmt Gread :=
  TFieldRead false counter_field
    (LHere (d := runtime_var TInt) eq_refl)
    (PEVar (LThere (LHere (d := runtime_val TRef) eq_refl))).

Lemma field_read_reports_write :
  RegionSyntax.write field_read_leaf = Some 1.
Proof. reflexivity. Qed.

Notation Galloc := [runtime_var TRef].

Definition allocation_leaf : stmt Galloc :=
  TAlloc false (LHere (d := runtime_var TRef) eq_refl) [].

Lemma allocation_reports_write :
  RegionSyntax.write allocation_leaf = Some 0.
Proof. reflexivity. Qed.

Definition call_store_leaf : stmt Gread :=
  TCall read_procedure
    ltac:(vm_compute;
      exact (PECons
        (PEVar (LThere (LHere (d := runtime_val TRef) eq_refl))) PENil))
    (CTStore false (LHere (d := runtime_var TInt) eq_refl)).

Lemma call_store_reports_write :
  RegionSyntax.write call_store_leaf = Some 1.
Proof. reflexivity. Qed.

(** The reported write has the intended semantic effect: an instance key
    mentioning the target is removed.  The constructor-specific lemmas above
    ensure this common check applies to every write-producing leaf. *)
Definition target_instance : Atomicity.mask_entry :=
  (counter_invariant, Some [Atomicity.AtomLevel 1]).

Lemma write_invalidates_target_instance :
  Atomicity.take_leaf Atomicity.AtomicStep (Some 1)
      (Atomicity.closed_state {[target_instance]}) =
    inr (Atomicity.closed_state ∅).
Proof. vm_compute. reflexivity. Qed.

Lemma assignment_invalidates_target_instance :
  Atomicity.analyze (Atomicity.closed_state {[target_instance]}) assign_leaf =
    inr (Atomicity.closed_state ∅).
Proof. vm_compute. reflexivity. Qed.

Lemma field_read_invalidates_target_instance :
  Atomicity.analyze (Atomicity.closed_state {[target_instance]})
      field_read_leaf =
    inr (Atomicity.closed_state ∅).
Proof. vm_compute. reflexivity. Qed.

Definition allocation_target_instance : Atomicity.mask_entry :=
  (counter_invariant, Some [Atomicity.AtomLevel 0]).

Lemma allocation_invalidates_target_instance :
  Atomicity.analyze
      (Atomicity.closed_state {[allocation_target_instance]}) allocation_leaf =
    inr (Atomicity.closed_state ∅).
Proof. vm_compute. reflexivity. Qed.

Definition call_argument_instance : Atomicity.mask_entry :=
  (counter_invariant, Some [Atomicity.AtomLevel 0]).

Lemma call_store_invalidates_target_instance :
  Atomicity.analyze
      (Atomicity.closed_state
        {[target_instance; call_argument_instance]}) call_store_leaf =
    inr (Atomicity.closed_state {[call_argument_instance]}).
Proof. vm_compute. reflexivity. Qed.

End MaskEffects.
