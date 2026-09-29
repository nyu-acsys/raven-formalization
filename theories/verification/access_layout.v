From Coq Require Import List Bool Program.Equality.
From stdpp Require Import base decidable.

From raven Require Import verification.expressions verification.assertions
  verification.ir.

Import ListNotations.

(** Layout of invariant accesses.  The statements of
    [unfold I(a); s1; ...; sn] up to the access's close are grouped into
    one body or prefix, and a conditional closing the access in both
    branches,

      unfold I(a); [q;] if b { [tp;] fold I(a)[; tc] } else { ... }[; r],

    is given its canonical form

      (unfold I(a); q; if b { tp; fold I(a); tc } else { ep; fold I(a); ec }); r,

    with [done] for each missing piece.  Groupings are made only where they
    keep the runtime erasure ([access_layout_erasure] in
    [conditional_erasure.v]). *)
Module AccessLayout.
Import Core IR.

Section WithSignature.
Context {RAs : RAValueConfig} {Logic : Assertion.LogicSignature}.

(** ** Argument keys

    Arguments are compared through their variable indices; an argument that
    is not a variable has no key. *)
Fixpoint argument_variable_indices {keep Γ ts}
    (expressions : pexpr_list keep Γ ts) : option (list nat) :=
  match expressions with
  | PENil => Some []
  | PECons expression tail =>
      match expression, argument_variable_indices tail with
      | PEVar variable, Some indices =>
          Some (lvar_index variable :: indices)
      | _, _ => None
      end
  end.

Definition arguments_eqb {keep Γ ts}
    (left right : pexpr_list keep Γ ts) : bool :=
  match argument_variable_indices left, argument_variable_indices right with
  | Some left_indices, Some right_indices =>
      bool_decide (left_indices = right_indices)
  | _, _ => false
  end.

Lemma argument_variable_indices_injective {keep Γ ts}
    (left right : pexpr_list keep Γ ts) indices :
  argument_variable_indices left = Some indices ->
  argument_variable_indices right = Some indices ->
  left = right.
Proof.
  revert right indices.
  induction left; intros right indices Hleft Hright;
    dependent destruction right.
  - cbn in Hleft, Hright. congruence.
  - cbn in Hleft, Hright.
    destruct p; try discriminate.
    destruct p0; try discriminate.
    destruct (argument_variable_indices left) as [left_indices|]
      eqn:Hleft_indices; try discriminate.
    destruct (argument_variable_indices right) as [right_indices|]
      eqn:Hright_indices; try discriminate.
    inversion Hleft; inversion Hright; subst.
    f_equal.
    + f_equal. apply lvar_index_injective. congruence.
    + eapply IHleft; [reflexivity|].
      rewrite Hright_indices. f_equal. congruence.
Qed.

Lemma arguments_eqb_sound {keep Γ ts} (left right : pexpr_list keep Γ ts) :
  arguments_eqb left right = true -> left = right.
Proof.
  unfold arguments_eqb.
  destruct (argument_variable_indices left) as [left_indices|] eqn:Hleft;
    try discriminate.
  destruct (argument_variable_indices right) as [right_indices|] eqn:Hright;
    try discriminate.
  intro Hequal. apply bool_decide_eq_true in Hequal. subst right_indices.
  eapply argument_variable_indices_injective; eauto.
Qed.

(** ** Branch views *)

(** Whether [statement] is [fold invariant(arguments)]. *)
Definition fold_is {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (statement : stmt Γ) : bool :=
  match statement with
  | TFold invariant' arguments' =>
      match decide (invariant' = invariant) with
      | left Heq =>
          arguments_eqb (eq_rect _ (fun invariant0 =>
            gexpr_list Γ (Assertion.invariant_args invariant0))
            arguments' _ Heq) arguments
      | right _ => false
      end
  | _ => false
  end.

Lemma fold_is_sound {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (statement : stmt Γ) :
  fold_is invariant arguments statement = true ->
  statement = TFold invariant arguments.
Proof.
  destruct statement; cbn; try discriminate.
  destruct (decide (invariant0 = invariant)) as [Heq|]; [|discriminate].
  destruct Heq. cbn. intros Hequal.
  apply arguments_eqb_sound in Hequal. subst. reflexivity.
Qed.

(** ** Sequences

    A statement's sequence is the list of statements along its right
    spine.  Regrouping a list of statements is exact on runtime erasure
    when at most one of them is physical ([at_most_one_physical]). *)

Fixpoint sequence {Γ} (statement : stmt Γ) : list (stmt Γ) :=
  match statement with
  | TSeq first second => first :: sequence second
  | _ => [statement]
  end.

Fixpoint rebuild {Γ} (statements : list (stmt Γ)) : stmt Γ :=
  match statements with
  | [] => TDone
  | [statement] => statement
  | statement :: rest => TSeq statement (rebuild rest)
  end.

Lemma rebuild_sequence {Γ} (statement : stmt Γ) :
  rebuild (sequence statement) = statement.
Proof.
  induction statement; try reflexivity.
  cbn [sequence]. rewrite <- IHstatement2 at 2.
  destruct statement2; reflexivity.
Qed.

Fixpoint at_most_one_physical {Γ} (statements : list (stmt Γ)) : bool :=
  match statements with
  | [] => true
  | statement :: rest =>
      if proof_onlyb statement then at_most_one_physical rest
      else forallb proof_onlyb rest
  end.

(** The first statement of a list satisfying [test], with the statements
    before and after it. *)
Fixpoint split_first {Γ} (test : stmt Γ -> bool) (statements : list (stmt Γ)) :
    option (list (stmt Γ) * stmt Γ * list (stmt Γ)) :=
  match statements with
  | [] => None
  | statement :: rest =>
      if test statement then Some ([], statement, rest)
      else match split_first test rest with
        | Some (before, found, after) => Some (statement :: before, found, after)
        | None => None
        end
  end.

Lemma split_first_sound {Γ} (test : stmt Γ -> bool) statements before found
    after :
  split_first test statements = Some (before, found, after) ->
  statements = before ++ found :: after /\ test found = true.
Proof.
  revert before. induction statements as [|statement rest IH]; cbn;
    intros before; [discriminate|].
  destruct (test statement) eqn:Htest.
  - intros H. injection H as <- <- <-. auto.
  - destruct (split_first test rest) as [[[before' found'] after']|] eqn:Hsplit;
      [|discriminate].
    intros H. injection H as <- <- <-.
    destruct (IH before' eq_refl) as [-> Hfound]. auto.
Qed.

(** ** Branches *)

(** The prefix and continuation of a branch around its closing fold. *)
Definition branch_view {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (branch : stmt Γ) : option (stmt Γ * stmt Γ) :=
  match split_first (fold_is invariant arguments) (sequence branch) with
  | Some (before, _, after) =>
      if at_most_one_physical before then Some (rebuild before, rebuild after)
      else None
  | None => None
  end.

Definition canonical_branch {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix continuation : stmt Γ) : stmt Γ :=
  TSeq prefix (TSeq (TFold invariant arguments) continuation).

(** The canonical conditional under an open access, if both branches close
    it. *)
Definition layout_conditional {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (conditional : stmt Γ) : option (stmt Γ) :=
  let laid_out make then_branch else_branch :=
    match branch_view invariant arguments then_branch,
        branch_view invariant arguments else_branch with
    | Some (then_prefix, then_continuation),
        Some (else_prefix, else_continuation) =>
        Some (make
          (canonical_branch invariant arguments then_prefix then_continuation)
          (canonical_branch invariant arguments else_prefix else_continuation))
    | _, _ => None
    end in
  match conditional with
  | TIf condition then_branch else_branch =>
      laid_out (TIf condition) then_branch else_branch
  | TGhostIf condition then_branch else_branch =>
      laid_out (TGhostIf condition) then_branch else_branch
  | _ => None
  end.

(** Whether [statement] closes the access: a matching fold, or a
    conditional closing it in both branches. *)
Definition closes {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (statement : stmt Γ) : bool :=
  fold_is invariant arguments statement ||
  match layout_conditional invariant arguments statement with
  | Some _ => true
  | None => false
  end.

(** ** Accesses

    [layout_unfold invariant arguments rest] replaces
    [unfold invariant(arguments); rest].  The statements before the close
    are grouped into the access body or prefix; a closing conditional
    followed by further statements is grouped with the access, and the
    statements after it follow the group. *)
Definition layout_unfold {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (rest : stmt Γ) : stmt Γ :=
  let opening := TUnfold invariant arguments in
  match split_first (closes invariant arguments) (sequence rest) with
  | Some (before, closing, after) =>
      if at_most_one_physical before then
        if fold_is invariant arguments closing then
          TSeq opening (TSeq (rebuild before)
            match after with
            | [] => TFold invariant arguments
            | _ => TSeq (TFold invariant arguments) (rebuild after)
            end)
        else
          match layout_conditional invariant arguments closing with
          | Some conditional =>
              match after with
              | [] => TSeq opening (TSeq (rebuild before) conditional)
              | _ =>
                  if proof_onlyb (rebuild before) || proof_onlyb conditional ||
                      proof_onlyb (rebuild after)
                  then TSeq (TSeq opening (TSeq (rebuild before) conditional))
                    (rebuild after)
                  else TSeq opening rest
              end
          | None => TSeq opening rest
          end
      else TSeq opening rest
  | None => TSeq opening rest
  end.

(** ** Accesses inside trusted atomic blocks

    [hoist_atomic body] replaces [atomic { body }].  An access spanning the
    whole block, possibly followed by proof-only statements, is moved around
    it: the invariant is then held across the block's single physical step.
    Ghost values scoping the access are moved out with it. *)
Fixpoint hoist_atomic {Γ} (body : stmt Γ) : stmt Γ :=
  match body with
  | TGhostVal name t initializer inner =>
      TGhostVal name t initializer (hoist_atomic inner)
  | TSeq (TUnfold invariant arguments) (TSeq inner closing) =>
      match closing with
      | TFold _ _ =>
          if fold_is invariant arguments closing
          then TSeq (TUnfold invariant arguments)
            (TSeq (hoist_atomic inner) closing)
          else TAtomic body
      | TSeq fold rest =>
          if fold_is invariant arguments fold && proof_onlyb rest
          then TSeq (TUnfold invariant arguments)
            (TSeq (hoist_atomic inner) (TSeq fold rest))
          else TAtomic body
      | _ => TAtomic body
      end
  | _ => TAtomic body
  end.

Fixpoint layout_accesses {Γ} (statement : stmt Γ) : stmt Γ :=
  match statement with
  | TSeq first second =>
      let second' := layout_accesses second in
      match first with
      | TUnfold invariant arguments => layout_unfold invariant arguments second'
      | _ => TSeq (layout_accesses first) second'
      end
  | TIf condition then_branch else_branch =>
      TIf condition (layout_accesses then_branch) (layout_accesses else_branch)
  | TAtomic body => hoist_atomic (layout_accesses body)
  | TInvAccess invariant arguments body =>
      TInvAccess invariant arguments (layout_accesses body)
  | TGhostVal name t initializer body =>
      TGhostVal name t initializer (layout_accesses body)
  | TGhostIf condition then_branch else_branch =>
      TGhostIf condition (layout_accesses then_branch)
        (layout_accesses else_branch)
  | _ => statement
  end.

End WithSignature.
End AccessLayout.
