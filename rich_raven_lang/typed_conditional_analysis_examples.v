From Coq Require Import Bool List PArith.
From stdpp Require Import gmap.

From raven_iris.rich_raven_lang Require Import
  typed_core typed_assertion typed_ir typed_atomicity.

(** Executable regression examples for the conditional part of the real
    typed atomicity analyzer.  This file deliberately stops at certificates
    and their LIFO witnesses: it has no Hoare-logic or Iris assumptions. *)
Module TypedConditionalAnalysisExamples.

Module UnitRA := TypedCoreExamples.UnitRA.

Module TinyLogic <: TypedAssertion.LOGIC_SIGNATURE.
  Definition field_type (_ : TypedCore.field_id) := TypedCore.TInt.
  Definition predicate_args (_ : TypedCore.pred_id) : TypedCore.context := [].
  Definition invariant_args (_ : TypedCore.inv_id) : TypedCore.context := [].
End TinyLogic.

Module Analyzer := TypedAtomicity.Make UnitRA TinyLogic.
Module A := Analyzer.ViewAnalysis.
Import TypedCore Analyzer.Core Analyzer.IR.

Definition inv : inv_id := 1%positive.
Definition initial : A.analysis_state :=
  A.AnalysisState {[inv]} ∅ false false.
Definition finished : A.analysis_state :=
  A.AnalysisState {[inv]} ∅ false false.

Definition no_arguments : pexpr_list [] [] := PENil.
Definition condition : pexpr [] TBool := PEVal (VBool true).

Definition unfold_inv (node : node_id) : stmt [] :=
  TUnfold node inv no_arguments.
Definition fold_inv (node : node_id) : stmt [] :=
  TFold node inv no_arguments.

(** Leaves represent the physical fragments of the slice. *)
Definition physical (node : node_id) : stmt [] := TSkip node.

Definition cost : A.cost_model := fun _ statement =>
  match statement with
  | TSkip _ => A.AtomicStep
  | _ => A.NoStep
  end.

Definition seq (node : node_id) (first second : stmt []) : stmt [] :=
  TSeq node first second.

(** Both arms close the same access, but their preserving prefixes differ. *)
Definition asymmetric_close : stmt [] :=
  seq 10%positive (unfold_inv 11%positive)
    (TIf 12%positive condition
      (seq 13%positive (physical 14%positive) (fold_inv 15%positive))
      (seq 16%positive (TSkip 17%positive) (fold_inv 18%positive))).

Example asymmetric_close_analysis :
  A.analyze cost initial asymmetric_close = inr finished.
Proof. reflexivity. Qed.

Definition asymmetric_close_certificate :
    A.statement_certificate cost initial asymmetric_close finished.
Proof.
  apply A.analyze_builds_certificate. exact asymmetric_close_analysis.
Defined.

(** Post-close physical work remains local to each arm. *)
Definition branch_local_tail : stmt [] :=
  seq 20%positive (unfold_inv 21%positive)
    (TIf 22%positive condition
      (seq 23%positive (fold_inv 24%positive) (physical 25%positive))
      (seq 26%positive
        (seq 27%positive (physical 28%positive) (fold_inv 29%positive))
        (physical 30%positive))).

Example branch_local_tail_analysis :
  A.analyze cost initial branch_local_tail = inr finished.
Proof. reflexivity. Qed.

Definition branch_local_tail_certificate :
    A.statement_certificate cost initial branch_local_tail finished.
Proof.
  apply A.analyze_builds_certificate. exact branch_local_tail_analysis.
Defined.

(** The critical close/reopen regression: the then arm first closes the
    focused access, opens it again, and closes it a second time.  Equal input
    and output stacks therefore do not imply preservation of the focus. *)
Definition close_reopen : stmt [] :=
  seq 40%positive (unfold_inv 41%positive)
    (TIf 42%positive condition
      (seq 43%positive (fold_inv 44%positive)
        (seq 45%positive (unfold_inv 46%positive)
          (seq 47%positive (physical 48%positive) (fold_inv 49%positive))))
      (seq 50%positive (physical 51%positive) (fold_inv 52%positive))).

Example close_reopen_analysis :
  A.analyze cost initial close_reopen = inr finished.
Proof. reflexivity. Qed.

Definition close_reopen_certificate :
    A.statement_certificate cost initial close_reopen finished.
Proof.
  apply A.analyze_builds_certificate. exact close_reopen_analysis.
Defined.

(** Nested conditionals may close the same focused access at different
    syntactic depths. *)
Definition nested_close : stmt [] :=
  seq 60%positive (unfold_inv 61%positive)
    (TIf 62%positive condition
      (TIf 63%positive condition
        (seq 64%positive (physical 65%positive) (fold_inv 66%positive))
        (seq 67%positive (fold_inv 68%positive) (physical 69%positive)))
      (fold_inv 70%positive)).

Example nested_close_analysis :
  A.analyze cost initial nested_close = inr finished.
Proof. reflexivity. Qed.

Definition nested_close_certificate :
    A.statement_certificate cost initial nested_close finished.
Proof.
  apply A.analyze_builds_certificate. exact nested_close_analysis.
Defined.

End TypedConditionalAnalysisExamples.
