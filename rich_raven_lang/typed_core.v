From Coq Require Import String ZArith List PArith Program.Equality.
From stdpp Require Import base countable.

From raven_iris.rich_raven_lang Require Import surface_syntax.

Import ListNotations.
Open Scope list_scope.

(** Typed foundations for the elaborated Raven verification IR.  This module
    is intentionally independent of the existing [rrl_lang] while the new
    representation is validated. *)
Module TypedCore.

Inductive typ :=
| TBool
| TInt
| TRef
| TUnit
| TRA (resource_algebra : source_name).

Scheme Equality for typ.

Global Instance typ_eq : EqDecision typ := typ_eq_dec.

Definition context := list typ.
Definition proc_id := positive.
Definition node_id := positive.
Definition field_id := positive.
Definition pred_id := positive.
Definition inv_id := positive.

(** Type-correct references into a declaration/binder context. *)
Inductive member : context -> typ -> Type :=
| MHere Γ t : member (t :: Γ) t
| MThere Γ t u : member Γ t -> member (u :: Γ) t.

Arguments MHere {_ _}.
Arguments MThere {_ _ _} _.

Definition pvar := member.
Definition formal := member.
Definition bvar := member.

Inductive member_view {Γ head} : forall t, member (head :: Γ) t -> Type :=
| MVHere : member_view head MHere
| MVThere t (variable : member Γ t) : member_view t (MThere variable).

Arguments MVHere {_ _}.
Arguments MVThere {_ _ _} _.

Definition view_member {Γ head t} (variable : member (head :: Γ) t) :
    member_view t variable.
Proof.
  dependent destruction variable.
  - exact MVHere.
  - exact (MVThere variable).
Defined.

Lemma view_member_here {Γ head} :
  @view_member Γ head head MHere = MVHere.
Proof.
  remember (@view_member Γ head head MHere) as viewed eqn:Hview.
  dependent destruction viewed. reflexivity.
Qed.

Lemma view_member_there {Γ head t} (variable : member Γ t) :
  @view_member Γ head t (MThere variable) = MVThere variable.
Proof.
  remember (@view_member Γ head t (MThere variable)) as viewed eqn:Hview.
  dependent destruction viewed. reflexivity.
Qed.

Fixpoint member_index {Γ t} (variable : member Γ t) : nat :=
  match variable with
  | MHere => 0
  | MThere variable' => S (member_index variable')
  end.

(** Stable symbolic identities allocated by elaboration.  [atom t] is a
    genuinely distinct record type at each [t], even though its compact
    runtime payload is just a positive identifier.  Entry/result/proof origin
    information belongs in the elaboration and presentation tables rather
    than in the semantic identity itself. *)
Record atom (t : typ) := Atom {
  atom_id : positive;
}.

Arguments Atom {_} _.
Arguments atom_id {_} _.

Global Instance atom_eq_dec t : EqDecision (atom t).
Proof. solve_decision. Defined.

Global Instance atom_countable t : Countable (atom t).
Proof.
  refine (inj_countable atom_id (fun id => Some (Atom id)) _).
  intros [id]. reflexivity.
Qed.

(** Resource-algebra carriers remain supplied by the program's RA
    configuration.  All non-RA values are intrinsically typed here. *)
Module Type RA_VALUE_CONFIG.
  Parameter ra_carrier : source_name -> Type.
  Parameter ra_eqb : forall r, ra_carrier r -> ra_carrier r -> bool.
  Parameter ra_eqb_eq : forall r (left right : ra_carrier r),
    ra_eqb r left right = true <-> left = right.
End RA_VALUE_CONFIG.

Module Make (RAs : RA_VALUE_CONFIG).

Inductive tval : typ -> Type :=
| VBool (b : bool) : tval TBool
| VInt (z : Z) : tval TInt
| VRef (location : Z) : tval TRef
| VUnit : tval TUnit
| VRA r (value : RAs.ra_carrier r) : tval (TRA r).

Arguments VRA {_} _.

Definition tval_eqb (t : typ) (left right : tval t) : bool.
Proof.
  destruct t;
    dependent destruction left;
    dependent destruction right.
  - exact (Bool.eqb b b0).
  - exact (Z.eqb z z0).
  - exact (Z.eqb location location0).
  - exact true.
  - exact (RAs.ra_eqb resource_algebra value value0).
Defined.

Lemma tval_eqb_eq t (left right : tval t) :
  tval_eqb t left right = true <-> left = right.
Proof.
  destruct t; dependent destruction left; dependent destruction right; simpl.
  - rewrite Bool.eqb_true_iff. split; intro H; [subst | inversion H]; reflexivity.
  - rewrite Z.eqb_eq. split; intro H; [subst | inversion H]; reflexivity.
  - rewrite Z.eqb_eq. split; intro H; [subst | inversion H]; reflexivity.
  - split; intros; reflexivity.
  - change (RAs.ra_eqb resource_algebra value value0 = true <->
      VRA value = VRA value0).
    rewrite RAs.ra_eqb_eq. split.
    + intros ->. reflexivity.
    + intros H. inversion H.
      apply (Eqdep_dec.inj_pair2_eq_dec string String.string_dec) in H1.
      exact H1.
Qed.

(** References available to a symbolic store or typed logical expression.
    Each namespace has a distinct constructor, so formal substitution,
    binder weakening, and atom renaming cannot interfere with one another. *)
Inductive value_ref (F Δ : context) : typ -> Type :=
| RefFormal t (x : formal F t) : value_ref F Δ t
| RefBound t (x : bvar Δ t) : value_ref F Δ t
| RefAtom t (x : atom t) : value_ref F Δ t.

Arguments RefFormal {_ _ _} _.
Arguments RefBound {_ _ _} _.
Arguments RefAtom {_ _ _} _.

Inductive unop : typ -> typ -> Type :=
| UNot : unop TBool TBool
| UNeg : unop TInt TInt.

Inductive binop : typ -> typ -> typ -> Type :=
| BAdd : binop TInt TInt TInt
| BSub : binop TInt TInt TInt
| BMul : binop TInt TInt TInt
| BDiv : binop TInt TInt TInt
| BMod : binop TInt TInt TInt
| BLt : binop TInt TInt TBool
| BLe : binop TInt TInt TBool
| BGt : binop TInt TInt TBool
| BGe : binop TInt TInt TBool
| BEq t : binop t t TBool
| BNe t : binop t t TBool
| BAnd : binop TBool TBool TBool
| BOr : binop TBool TBool TBool.

Inductive expr (F Δ : context) : typ -> Type :=
| ERef t (reference : value_ref F Δ t) : expr F Δ t
| EVal t (value : tval t) : expr F Δ t
| EUnOp input output (op : unop input output)
    (operand : expr F Δ input) : expr F Δ output
| EBinOp left right output (op : binop left right output)
    (operand1 : expr F Δ left) (operand2 : expr F Δ right) : expr F Δ output.

Arguments ERef {_ _ _} _.
Arguments EVal {_ _ _} _.
Arguments EUnOp {_ _ _ _} _ _.
Arguments EBinOp {_ _ _ _ _} _ _ _.

(** Typed environments need no analogue of [env_typ_well_defined]. *)
Definition formal_env (F : context) := forall t, formal F t -> tval t.
Definition binder_env (Δ : context) := forall t, bvar Δ t -> tval t.

Definition atom_env := forall t, atom t -> tval t.

Definition interp_ref {F Δ t}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (reference : value_ref F Δ t) : tval t :=
  match reference with
  | RefFormal x => formals _ x
  | RefBound x => binders _ x
  | RefAtom x => atoms _ x
  end.

Definition interp_unop {input output} (op : unop input output) :
    tval input -> tval output :=
  match op with
  | UNot => fun value =>
      match value with VBool b => VBool (negb b) end
  | UNeg => fun value =>
      match value with VInt z => VInt (-z) end
  end.

(** Typed binary operations follow Raven's operational semantics.  In
    particular, integer division and modulus use Rocq's total [Z.div]/[Z.mod].
    Type mismatch is impossible. *)
Definition interp_binop {left right output}
    (op : binop left right output) :
    tval left -> tval right -> option (tval output) :=
  match op with
  | BAdd => fun value1 value2 =>
      match value1, value2 with VInt x, VInt y => Some (VInt (x + y)) end
  | BSub => fun value1 value2 =>
      match value1, value2 with VInt x, VInt y => Some (VInt (x - y)) end
  | BMul => fun value1 value2 =>
      match value1, value2 with VInt x, VInt y => Some (VInt (x * y)) end
  | BDiv => fun value1 value2 =>
      match value1, value2 with VInt x, VInt y => Some (VInt (Z.div x y)) end
  | BMod => fun value1 value2 =>
      match value1, value2 with VInt x, VInt y => Some (VInt (Z.modulo x y)) end
  | BLt => fun value1 value2 =>
      match value1, value2 with VInt x, VInt y => Some (VBool (Z.ltb x y)) end
  | BLe => fun value1 value2 =>
      match value1, value2 with VInt x, VInt y => Some (VBool (Z.leb x y)) end
  | BGt => fun value1 value2 =>
      match value1, value2 with VInt x, VInt y => Some (VBool (Z.ltb y x)) end
  | BGe => fun value1 value2 =>
      match value1, value2 with VInt x, VInt y => Some (VBool (Z.leb y x)) end
  | BEq t => fun value1 value2 =>
      Some (VBool (tval_eqb t value1 value2))
  | BNe t => fun value1 value2 =>
      Some (VBool (negb (tval_eqb t value1 value2)))
  | BAnd => fun value1 value2 =>
      match value1, value2 with VBool x, VBool y => Some (VBool (andb x y)) end
  | BOr => fun value1 value2 =>
      match value1, value2 with VBool x, VBool y => Some (VBool (orb x y)) end
  end.

Fixpoint interp_expr {F Δ t}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (expression : expr F Δ t) : option (tval t) :=
  match expression with
  | ERef reference => Some (interp_ref formals binders atoms reference)
  | EVal value => Some value
  | EUnOp op operand =>
      match interp_expr formals binders atoms operand with
      | Some value => Some (interp_unop op value)
      | None => None
      end
  | EBinOp op operand1 operand2 =>
      match interp_expr formals binders atoms operand1,
            interp_expr formals binders atoms operand2 with
      | Some value1, Some value2 => interp_binop op value1 value2
      | _, _ => None
      end
  end.

Lemma interp_expr_total {F Δ t} (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) (expression : expr F Δ t) :
  exists value, interp_expr formals binders atoms expression = Some value.
Proof.
  induction expression.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - destruct IHexpression as [value Hvalue]. simpl. rewrite Hvalue.
    eexists. reflexivity.
  - destruct IHexpression1 as [value1 Hvalue1].
    destruct IHexpression2 as [value2 Hvalue2].
    simpl. rewrite Hvalue1, Hvalue2. destruct op; dependent destruction value1;
      dependent destruction value2; eexists; reflexivity.
Qed.

(** A typed symbolic store is aligned structurally with the program-variable
    context.  This makes lookup and update compute without dependent equality
    transports. *)
Inductive store_data (F Δ : context) : context -> Type :=
| StoreNil : store_data F Δ []
| StoreCons t Γ : value_ref F Δ t -> store_data F Δ Γ ->
    store_data F Δ (t :: Γ).

Arguments StoreNil {_ _}.
Arguments StoreCons {_ _ _ _} _ _.

Definition symbolic_store (Γ F Δ : context) := store_data F Δ Γ.

Fixpoint lookup_store {Γ F Δ} (store : symbolic_store Γ F Δ) :
    forall t, pvar Γ t -> value_ref F Δ t.
Proof.
  destruct store as [| head_type tail_context value tail].
  - intros t variable. dependent destruction variable.
  - intros t variable. dependent destruction variable.
    + exact value.
    + exact (@lookup_store tail_context F Δ tail _ variable).
Defined.

(** Extending the binder context is structural. *)
Definition weaken_bvar {Δ t u} (x : bvar Δ t) : bvar (u :: Δ) t :=
  MThere x.

Fixpoint weaken_member_right {Γ t} (x : member Γ t) (suffix : context) :
    member (Γ ++ suffix) t :=
  match x with
  | MHere => MHere
  | MThere x' => MThere (weaken_member_right x' suffix)
  end.

End Make.
End TypedCore.

(** Executable examples for the typed expression layer. *)
Module TypedCoreExamples.

Module UnitRA <: TypedCore.RA_VALUE_CONFIG.
  Definition ra_carrier (_ : source_name) : Type := unit.
  Definition ra_eqb (_ : source_name) (_ _ : unit) : bool := true.
  Lemma ra_eqb_eq r (left right : unit) :
    ra_eqb r left right = true <-> left = right.
  Proof. destruct left, right. split; reflexivity. Qed.
End UnitRA.

Module Core := TypedCore.Make UnitRA.
Import TypedCore Core.

Definition empty_formals : formal_env [] :=
  fun t variable => match variable with end.

Definition empty_binders : binder_env [] :=
  fun t variable => match variable with end.

Definition arbitrary_atoms : atom_env :=
  fun t variable =>
    match t as result return tval result with
    | TBool => VBool false
    | TInt => VInt 0
    | TRef => VRef 0
    | TUnit => VUnit
    | TRA r => VRA tt
    end.

Definition one_plus_two : expr [] [] TInt :=
  EBinOp BAdd (EVal (VInt 1)) (EVal (VInt 2)).

Example interp_one_plus_two :
  interp_expr empty_formals empty_binders arbitrary_atoms one_plus_two =
    Some (VInt 3).
Proof. reflexivity. Qed.

Definition ill_typed_addition_cannot_be_constructed : Type :=
  expr [] [] TInt.

End TypedCoreExamples.
