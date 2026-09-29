From Coq Require Import List String Program.Equality.
From stdpp Require Import base decidable gmap sets.

From raven Require Import surface.syntax verification.expressions verification.assertions
  verification.resources verification.ir verification.hoare_rules.

Import ListNotations.
Open Scope list_scope.

(** Invariant-argument snapshots.  Every [unfold I(args)] with arguments that
    heads a sequence is rewritten to

      ghost val g := args; unfold I(g); ...; fold I(g); assert (g == args'); ...

    where [fold I(args')] is the matching fold on each path.  Both
    applications then name the opened instance through ghost [val]s, which
    no statement writes; the assertion obliges the derivation to show that
    the fold as written closes that instance.  The rewrite is proof-only:
    its erasure is the source's ([snapshot_erasure.v]). *)
Module Snapshots.
Import Core IR.
Module RH := ResourceHoare.

Section WithSignature.
Context {RAs : RAValueConfig} {Logic : Assertion.LogicSignature}.

(** ** Renaming *)

Definition lvar_renaming (D D' : decl_context) :=
  forall keep t, lvar keep D t -> lvar keep D' t.

Definition lift_renaming {D D'} d (renaming : lvar_renaming D D') :
    lvar_renaming (d :: D) (d :: D') :=
  fun keep t variable =>
    match variable in lvar _ D0 t0
      return match D0 with
             | [] => unit
             | d0 :: D1 =>
                 (lvar keep D1 t0 -> lvar keep D' t0) -> lvar keep (d0 :: D') t0
             end
    with
    | LHere Hkeep => fun _ => LHere Hkeep
    | LThere variable' => fun rename => LThere (rename variable')
    end (renaming keep t).

Fixpoint pexpr_rename {keep D D' t} (renaming : lvar_renaming D D')
    (expression : pexpr keep D t) : pexpr keep D' t :=
  match expression with
  | PEVar variable => PEVar (renaming _ _ variable)
  | PEVal value => PEVal value
  | PEUnOp op operand => PEUnOp op (pexpr_rename renaming operand)
  | PEBinOp op operand1 operand2 =>
      PEBinOp op (pexpr_rename renaming operand1)
        (pexpr_rename renaming operand2)
  end.

Fixpoint pexpr_list_rename {keep D D' ts} (renaming : lvar_renaming D D')
    (expressions : pexpr_list keep D ts) : pexpr_list keep D' ts :=
  match expressions with
  | PENil => PENil
  | PECons expression tail =>
      PECons (pexpr_rename renaming expression)
        (pexpr_list_rename renaming tail)
  end.

Definition field_init_rename {D D'} (renaming : lvar_renaming D D')
    (initialization : field_init D) : field_init D' :=
  match initialization with
  | FieldInit field value => FieldInit field (pexpr_rename renaming value)
  end.

Definition call_target_rename {D D' t} (renaming : lvar_renaming D D')
    (target : call_target D t) : call_target D' t :=
  match target with
  | CTDiscard => CTDiscard
  | CTStore init target' => CTStore init (renaming _ _ target')
  end.

Fixpoint stmt_rename {D D'} (renaming : lvar_renaming D D')
    (statement : stmt D) : stmt D' :=
  match statement with
  | TDone => TDone
  | TAssert condition => TAssert (pexpr_rename renaming condition)
  | TAssign init target value =>
      TAssign init (renaming _ _ target) (pexpr_rename renaming value)
  | TFieldRead init field target base =>
      TFieldRead init field (renaming _ _ target) (pexpr_rename renaming base)
  | TFieldWrite field base value =>
      TFieldWrite field (pexpr_rename renaming base)
        (pexpr_rename renaming value)
  | TAlloc init target fields =>
      TAlloc init (renaming _ _ target)
        (map (field_init_rename renaming) fields)
  | TGhostUpdate field base old_value new_value =>
      TGhostUpdate field (pexpr_rename renaming base)
        (pexpr_rename renaming old_value) (pexpr_rename renaming new_value)
  | TCall procedure arguments target =>
      TCall procedure (pexpr_list_rename renaming arguments)
        (call_target_rename renaming target)
  | TSpawn procedure arguments =>
      TSpawn procedure (pexpr_list_rename renaming arguments)
  | TUnfold invariant arguments =>
      TUnfold invariant (pexpr_list_rename renaming arguments)
  | TFold invariant arguments =>
      TFold invariant (pexpr_list_rename renaming arguments)
  | TPredicateUnfold predicate arguments =>
      TPredicateUnfold predicate (pexpr_list_rename renaming arguments)
  | TPredicateFold predicate arguments =>
      TPredicateFold predicate (pexpr_list_rename renaming arguments)
  | TInvAccess invariant arguments body =>
      TInvAccess invariant (pexpr_list_rename renaming arguments)
        (stmt_rename renaming body)
  | TIf condition then_branch else_branch =>
      TIf (pexpr_rename renaming condition) (stmt_rename renaming then_branch)
        (stmt_rename renaming else_branch)
  | TSeq first second =>
      TSeq (stmt_rename renaming first) (stmt_rename renaming second)
  | TAtomic body => TAtomic (stmt_rename renaming body)
  | TGhostVal name t initializer body =>
      TGhostVal name t (pexpr_rename renaming initializer)
        (stmt_rename (lift_renaming _ renaming) body)
  end.

(** ** Snapshots *)

Definition snapshot_name : source_name := "#snapshot"%string.
Definition guard_snapshot_name : source_name := "#guard"%string.

Definition shift_renaming {D} d : lvar_renaming D (d :: D) :=
  fun _ _ variable => LThere variable.

Definition pexpr_list_nil {keep D ts} (expressions : pexpr_list keep D ts) :
    bool :=
  match expressions with PENil => true | PECons _ _ => false end.

Definition pexpr_list_head {keep D t ts}
    (expressions : pexpr_list keep D (t :: ts)) : pexpr keep D t :=
  match expressions in pexpr_list _ _ ts0
    return match ts0 with [] => unit | t0 :: _ => pexpr keep D t0 end
  with
  | PENil => tt
  | PECons expression _ => expression
  end.

Definition pexpr_list_tail {keep D t ts}
    (expressions : pexpr_list keep D (t :: ts)) : pexpr_list keep D ts :=
  match expressions in pexpr_list _ _ ts0
    return match ts0 with [] => unit | _ :: ts1 => pexpr_list keep D ts1 end
  with
  | PENil => tt
  | PECons _ tail => tail
  end.

(** [left == right], componentwise. *)
Fixpoint snapshot_equalities {D ts} (left : gexpr_list D ts) :
    gexpr_list D ts -> gexpr D TBool :=
  match left in pexpr_list _ _ ts0 return gexpr_list D ts0 -> gexpr D TBool with
  | PENil => fun _ => PEVal (VBool true)
  | PECons expression tail => fun right =>
      let head := PEBinOp (BEq _) expression (pexpr_list_head right) in
      if pexpr_list_nil tail then head
      else PEBinOp BAnd head (snapshot_equalities tail (pexpr_list_tail right))
  end.

(** Binds one ghost [val] per argument, innermost last, and hands the
    continuation the renaming into the extended context together with the
    snapshot variables. *)
Fixpoint snapshot_arguments {D0 D ts} (renaming : lvar_renaming D0 D)
    (arguments : gexpr_list D0 ts)
    (continuation : forall D', lvar_renaming D D' -> gexpr_list D' ts -> stmt D') :
    stmt D :=
  match arguments in pexpr_list _ _ ts0
    return (forall D', lvar_renaming D D' -> gexpr_list D' ts0 -> stmt D') -> stmt D
  with
  | PENil => fun continuation => continuation D (fun _ _ variable => variable) PENil
  | @PECons _ _ _ t ts' argument tail => fun continuation =>
      TGhostVal snapshot_name t (pexpr_rename renaming argument)
        (snapshot_arguments (fun keep u variable => LThere (renaming keep u variable))
          tail
          (fun D' renaming' snapshots =>
            continuation D' (fun keep u variable => renaming' keep u (LThere variable))
              (PECons (PEVar (renaming' keep_all t
                (LHere (d := ghost_val t) (D := D) eq_refl))) snapshots)))
  end continuation.

(** The matching fold, if [statement] is a fold of [invariant]: the fold at
    the snapshot and the check that the written arguments name it. *)
Definition matching_fold {D} invariant
    (snapshots : gexpr_list D (Assertion.invariant_args invariant))
    (statement : stmt D) : option (stmt D * stmt D) :=
  match statement with
  | TFold invariant' arguments =>
      match decide (invariant' = invariant) with
      | left Heq =>
          Some (TFold invariant snapshots,
            TAssert (snapshot_equalities snapshots
              (eq_rect _ (fun invariant0 =>
                gexpr_list D (Assertion.invariant_args invariant0))
                arguments _ Heq)))
      | right _ => None
      end
  | _ => None
  end.

(** Rewrites the first fold of [invariant] on each path; the flag records
    whether every path through [statement] closed the access.  A conditional
    with a branch-local fold also saves its control result in a ghost [val]
    at its evaluation point. *)
Fixpoint close_access {D} invariant
    (snapshots : gexpr_list D (Assertion.invariant_args invariant))
    (statement : stmt D) : stmt D * bool :=
  match statement with
  | TSeq first second =>
      match matching_fold invariant snapshots first with
      | Some (closing, check) => (TSeq closing (TSeq check second), true)
      | None =>
          let (first', closed) := close_access invariant snapshots first in
          if closed then (TSeq first' second, true)
          else
            let (second', closed') := close_access invariant snapshots second in
            (TSeq first' second', closed')
      end
  | TFold _ _ =>
      match matching_fold invariant snapshots statement with
      | Some (closing, check) => (TSeq closing check, true)
      | None => (statement, false)
      end
  | TIf condition then_branch else_branch =>
      let (then_branch', then_closed) :=
        close_access invariant snapshots then_branch in
      let (else_branch', else_closed) :=
        close_access invariant snapshots else_branch in
      if then_closed || else_closed then
        (TGhostVal guard_snapshot_name TBool (pexpr_forget condition)
          (TIf (pexpr_rename (shift_renaming _) condition)
            (stmt_rename (shift_renaming _) then_branch')
            (stmt_rename (shift_renaming _) else_branch')),
         then_closed && else_closed)
      else (TIf condition then_branch' else_branch', then_closed && else_closed)
  | TAtomic body =>
      let (body', closed) := close_access invariant snapshots body in
      (TAtomic body', closed)
  | TInvAccess invariant' arguments body =>
      let (body', closed) := close_access invariant snapshots body in
      (TInvAccess invariant' arguments body', closed)
  | TGhostVal name t initializer body =>
      let (body', closed) :=
        close_access invariant (pexpr_list_shift snapshots) body in
      (TGhostVal name t initializer body', closed)
  | _ => (statement, false)
  end.

Definition snapshot_access {D} invariant
    (arguments : gexpr_list D (Assertion.invariant_args invariant))
    (rest : stmt D) : stmt D :=
  snapshot_arguments (fun _ _ variable => variable) arguments
    (fun D' renaming snapshots =>
      TSeq (TUnfold invariant snapshots)
        (fst (close_access invariant snapshots (stmt_rename renaming rest)))).

Fixpoint snapshot_accesses {D} (statement : stmt D) : stmt D :=
  match statement with
  | TSeq first second =>
      let second' := snapshot_accesses second in
      match first with
      | TUnfold invariant arguments =>
          if pexpr_list_nil arguments then TSeq first second'
          else snapshot_access invariant arguments second'
      | _ => TSeq (snapshot_accesses first) second'
      end
  | TIf condition then_branch else_branch =>
      TIf condition (snapshot_accesses then_branch)
        (snapshot_accesses else_branch)
  | TAtomic body => TAtomic (snapshot_accesses body)
  | TInvAccess invariant arguments body =>
      TInvAccess invariant arguments (snapshot_accesses body)
  | TGhostVal name t initializer body =>
      TGhostVal name t initializer (snapshot_accesses body)
  | _ => statement
  end.

(** ** Stability

    Snapshots are ghost slots, and statements write only runtime slots, so
    no statement can change a snapshot. *)

Lemma lvar_index_runtime {keep D t} `{!RuntimeKeep keep}
    (variable : lvar keep D t) :
  exists d, D !! lvar_index variable = Some d /\ keep_runtime d = true.
Proof.
  destruct (lvar_index_spec variable) as (d & Hd & Hkeep & _).
  exists d. split; [exact Hd | exact (runtime_keep _ Hkeep)].
Qed.

Lemma statement_writes_runtime {D} (statement : stmt D) slot :
  slot ∈ RH.statement_writes statement ->
  exists d, D !! slot = Some d /\ keep_runtime d = true.
Proof.
  revert slot. induction statement; intros slot Hslot;
    cbn [RH.statement_writes] in Hslot.
  all: try (apply elem_of_singleton in Hslot as ->; apply lvar_index_runtime).
  all: try (destruct target as [|init u target];
    [set_solver | apply elem_of_singleton in Hslot as ->;
      apply lvar_index_runtime]).
  all: try (apply elem_of_union in Hslot as [Hslot | Hslot];
    [exact (IHstatement1 slot Hslot) | exact (IHstatement2 slot Hslot)]).
  all: try exact (IHstatement slot Hslot).
  all: try (apply RH.elem_of_unshift_slots in Hslot;
    exact (IHstatement (S slot) Hslot)).
  all: set_solver.
Qed.

(** Arguments that read only ghost slots. *)
Definition ghost_arguments {D keep ts} (arguments : pexpr_list keep D ts) :
    Prop :=
  forall slot, slot ∈ RH.pexpr_list_dependencies arguments ->
    exists d, D !! slot = Some d /\ keep_runtime d = false.

Lemma ghost_arguments_stable {D keep ts} (arguments : pexpr_list keep D ts)
    (statement : stmt D) :
  ghost_arguments arguments ->
  RH.pexpr_list_dependencies arguments ## RH.statement_writes statement.
Proof.
  intros Hghost slot Hread Hwritten.
  destruct (Hghost slot Hread) as (d & Hd & Hphase).
  destruct (statement_writes_runtime statement slot Hwritten)
    as (d' & Hd' & Hphase').
  congruence.
Qed.

End WithSignature.
End Snapshots.
