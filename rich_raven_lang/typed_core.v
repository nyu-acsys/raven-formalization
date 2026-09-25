From Coq Require Import String ZArith List PArith Program.Equality
  Logic.FunctionalExtensionality.
From stdpp Require Import base countable.

From raven_iris.rich_raven_lang Require Import surface_syntax.

Import ListNotations.
Open Scope list_scope.

(** Typed foundations for the elaborated Raven verification IR. *)
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

Lemma member_index_here {Γ t} :
  member_index (@MHere Γ t) = O.
Proof. reflexivity. Qed.

Lemma member_index_there {Γ head t} (variable : member Γ t) :
  member_index (@MThere Γ t head variable) = S (member_index variable).
Proof. reflexivity. Qed.

Lemma member_index_injective {Γ t} (left right : member Γ t) :
  member_index left = member_index right -> left = right.
Proof.
  revert right. induction left; intros right Heq; dependent destruction right;
    cbn [member_index] in Heq; try discriminate.
  - reflexivity.
  - f_equal. apply IHleft. lia.
Qed.

Lemma member_index_sig_injective {Γ}
    (left right : { t : typ & member Γ t }) :
  member_index (projT2 left) = member_index (projT2 right) -> left = right.
Proof.
  destruct left as [left_type left], right as [right_type right].
  revert right_type right. induction left; intros right_type right Heq;
    dependent destruction right; cbn [member_index] in Heq; try discriminate.
  - reflexivity.
  - specialize (IHleft _ right (Nat.succ_inj _ _ Heq)).
    inversion IHleft. reflexivity.
Qed.

(** Stable symbolic identities.  Statement-result atoms retain their compact
    positive identifier, while procedure-entry atoms are generated from the
    procedure and frame slot.  Keeping the origins disjoint makes canonical
    entry stores collision-free by construction. *)
Inductive atom (t : typ) :=
| Atom (id : positive)
| ProcedureEntryAtom (procedure : proc_id) (slot : nat).

Arguments Atom {_} _.
Arguments ProcedureEntryAtom {_} _ _.

Global Instance atom_eq_dec t : EqDecision (atom t).
Proof. solve_decision. Defined.

Global Instance atom_countable t : Countable (atom t).
Proof.
  refine (inj_countable'
    (fun symbolic : atom t =>
      match symbolic with
      | Atom id => inl id
      | ProcedureEntryAtom procedure slot => inr (procedure, slot)
      end)
    (fun encoded =>
      match encoded with
      | inl id => Atom id
      | inr (procedure, slot) => ProcedureEntryAtom procedure slot
      end) _).
  intros []; reflexivity.
Qed.

(** Resource-algebra carriers remain supplied by the program's RA
    configuration.  All non-RA values are intrinsically typed here. *)
Module Type RA_VALUE_CONFIG.
  Parameter ra_carrier : source_name -> Type.
  Parameter ra_eqb : forall r, ra_carrier r -> ra_carrier r -> bool.
  Parameter ra_eqb_eq : forall r (left right : ra_carrier r),
    ra_eqb r left right = true <-> left = right.
  Parameter ra_id : forall r, ra_carrier r.
  Parameter ra_of_int : forall r, Z -> ra_carrier r.
  Parameter ra_valid : forall r, ra_carrier r -> Prop.
  Parameter ra_fpu_allowed : forall r, ra_carrier r -> ra_carrier r -> Prop.
End RA_VALUE_CONFIG.

Module Make (RAs : RA_VALUE_CONFIG).

Inductive tval : typ -> Type :=
| VBool (b : bool) : tval TBool
| VInt (z : Z) : tval TInt
| VRef (location : Z) : tval TRef
| VUnit : tval TUnit
| VRA r (value : RAs.ra_carrier r) : tval (TRA r).

Arguments VRA {_} _.

(** Raven's value sorts denote inhabited SMT sorts.  Keep the corresponding
    language-level witness explicit: proof transformations may need a witness
    for a logical binder on a branch where that binder is otherwise unused. *)
Definition default_tval (t : typ) : tval t :=
  match t as result return tval result with
  | TBool => VBool false
  | TInt => VInt 0
  | TRef => VRef 0
  | TUnit => VUnit
  | TRA r => VRA (RAs.ra_id r)
  end.

Global Instance tval_inhabited (t : typ) : Inhabited (tval t) :=
  populate (default_tval t).

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

Definition tval_fpu_allowed {t : typ} (old_value new_value : tval t) : Prop.
Proof.
  destruct t; dependent destruction old_value; dependent destruction new_value.
  - exact False.
  - exact False.
  - exact False.
  - exact False.
  - exact (RAs.ra_fpu_allowed resource_algebra value value0).
Defined.

Definition tval_ra_valid {t : typ} (value : tval t) : Prop.
Proof.
  destruct t; dependent destruction value.
  - exact True.
  - exact True.
  - exact True.
  - exact True.
  - exact (RAs.ra_valid resource_algebra value).
Defined.

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
| UNeg : unop TInt TInt
| URAOfInt r : unop TInt (TRA r).

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

Definition default_expr {F Δ} (t : typ) : expr F Δ t :=
  EVal (default_tval t).

(* ------------------------------------------------------------------ *)
(** ** Decidable equality for typed expressions.

    The normalization layer's access-argument side condition is a
    syntactic equality between symbolized invariant arguments, so a
    producer that recognizes a matched invariant access has to *decide*
    it rather than assume it.

    Comparison is defined heterogeneously -- [expr F Δ t1] against
    [expr F Δ t2] -- so that the definitions themselves need no
    dependent transports.  Only [member] is special: its context is an
    index rather than a parameter, so a two-way [match] cannot refine
    both sides at once, and it is compared through [member_index]
    instead.  Nothing here needs an axiom: every index is a [typ], and
    [typ] already has decidable equality. *)

Definition source_name_eqb (left right : source_name) : bool :=
  if String.string_dec left right then true else false.

Lemma source_name_eqb_refl name : source_name_eqb name name = true.
Proof.
  unfold source_name_eqb. destruct (String.string_dec name name) as [_ | Hne].
  - reflexivity.
  - exact (match Hne eq_refl with end).
Qed.

Lemma source_name_eqb_eq left right :
  source_name_eqb left right = true -> left = right.
Proof.
  unfold source_name_eqb. destruct (String.string_dec left right) as [Heq | _].
  - intros _. exact Heq.
  - discriminate.
Qed.

Definition typ_eqb (left right : typ) : bool :=
  if typ_eq_dec left right then true else false.

Lemma typ_eqb_refl t : typ_eqb t t = true.
Proof.
  unfold typ_eqb. destruct (typ_eq_dec t t) as [_ | Hne].
  - reflexivity.
  - exact (match Hne eq_refl with end).
Qed.

Lemma typ_eqb_eq left right : typ_eqb left right = true -> left = right.
Proof.
  unfold typ_eqb. destruct (typ_eq_dec left right) as [Heq | _].
  - intros _. exact Heq.
  - discriminate.
Qed.

Definition member_eqb {Γ t1} (x : member Γ t1) {t2} (y : member Γ t2) : bool :=
  Nat.eqb (member_index x) (member_index y).

Lemma member_eqb_refl {Γ t} (x : member Γ t) : member_eqb x x = true.
Proof. unfold member_eqb. apply Nat.eqb_refl. Qed.

Lemma member_eqb_eq {Γ t} (x y : member Γ t) : member_eqb x y = true -> x = y.
Proof.
  revert y. induction x; intros y; dependent destruction y;
    unfold member_eqb in *; simpl; try (intros Hbad; discriminate).
  - reflexivity.
  - intros Heq. f_equal. exact (IHx y Heq).
Qed.

Global Instance member_eq_dec Γ t : EqDecision (member Γ t).
Proof.
  intros x y. destruct (member_eqb x y) eqn:Heq.
  - left. exact (member_eqb_eq x y Heq).
  - right. intros ->. rewrite member_eqb_refl in Heq. discriminate.
Defined.

Definition atom_eqb {t1} (left : atom t1) {t2} (right : atom t2) : bool :=
  match left, right with
  | Atom left_id, Atom right_id => Pos.eqb left_id right_id
  | ProcedureEntryAtom left_procedure left_slot,
      ProcedureEntryAtom right_procedure right_slot =>
      Pos.eqb left_procedure right_procedure && Nat.eqb left_slot right_slot
  | _, _ => false
  end.

Lemma atom_eqb_refl t (symbolic : atom t) : atom_eqb symbolic symbolic = true.
Proof. destruct symbolic; simpl; now rewrite ?Pos.eqb_refl, ?Nat.eqb_refl. Qed.

Lemma atom_eqb_eq t (left right : atom t) :
  atom_eqb left right = true -> left = right.
Proof.
  destruct left, right; simpl; try discriminate.
  - intros Heq. apply Pos.eqb_eq in Heq. now subst.
  - rewrite andb_true_iff, Pos.eqb_eq, Nat.eqb_eq.
    intros [-> ->]. reflexivity.
Qed.

Definition value_ref_eqb {F Δ t1} (r1 : value_ref F Δ t1)
    {t2} (r2 : value_ref F Δ t2) : bool :=
  match r1, r2 with
  | RefFormal x, RefFormal y => member_eqb x y
  | RefBound x, RefBound y => member_eqb x y
  | RefAtom x, RefAtom y => atom_eqb x y
  | _, _ => false
  end.

Lemma value_ref_eqb_refl {F Δ t} (r : value_ref F Δ t) :
  value_ref_eqb r r = true.
Proof.
  dependent destruction r; simpl.
  - exact (member_eqb_refl x).
  - exact (member_eqb_refl x).
  - exact (atom_eqb_refl _ x).
Qed.

Lemma value_ref_eqb_eq {F Δ t} (r1 r2 : value_ref F Δ t) :
  value_ref_eqb r1 r2 = true -> r1 = r2.
Proof.
  dependent destruction r1; dependent destruction r2; simpl;
    try (intros Hbad; discriminate).
  - intros Heq. f_equal. exact (member_eqb_eq _ _ Heq).
  - intros Heq. f_equal. exact (member_eqb_eq _ _ Heq).
  - intros Heq. f_equal. exact (atom_eqb_eq _ _ _ Heq).
Qed.

Global Instance value_ref_eq_dec F Δ t : EqDecision (value_ref F Δ t).
Proof.
  intros r1 r2. destruct (value_ref_eqb r1 r2) eqn:Heq.
  - left. exact (value_ref_eqb_eq r1 r2 Heq).
  - right. intros ->. rewrite value_ref_eqb_refl in Heq. discriminate.
Defined.

(** A heterogeneous comparison for values, so that [expr]'s [EVal] case
    needs no transport. *)
Definition tval_eqb_het {t1} (v1 : tval t1) {t2} (v2 : tval t2) : bool :=
  match v1, v2 with
  | VBool b1, VBool b2 => Bool.eqb b1 b2
  | VInt z1, VInt z2 => Z.eqb z1 z2
  | VRef l1, VRef l2 => Z.eqb l1 l2
  | VUnit, VUnit => true
  | @VRA r1 w1, @VRA r2 w2 =>
      match String.string_dec r1 r2 with
      | left equality =>
          RAs.ra_eqb r2 (eq_rect r1 RAs.ra_carrier w1 r2 equality) w2
      | right _ => false
      end
  | _, _ => false
  end.

Lemma tval_eqb_het_refl {t} (v : tval t) : tval_eqb_het v v = true.
Proof.
  dependent destruction v; simpl.
  - exact (Bool.eqb_reflx b).
  - exact (Z.eqb_refl z).
  - exact (Z.eqb_refl location).
  - reflexivity.
  - destruct (String.string_dec r r) as [equality | Hne];
      [| exact (match Hne eq_refl with end)].
    rewrite (Eqdep_dec.UIP_dec String.string_dec equality eq_refl). simpl.
    apply RAs.ra_eqb_eq. reflexivity.
Qed.

Lemma tval_eqb_het_eq {t} (v1 v2 : tval t) :
  tval_eqb_het v1 v2 = true -> v1 = v2.
Proof.
  dependent destruction v1; dependent destruction v2; simpl;
    try (intros Hbad; discriminate).
  - intros Heq. apply Bool.eqb_prop in Heq. subst b0. reflexivity.
  - intros Heq. apply Z.eqb_eq in Heq. subst z0. reflexivity.
  - intros Heq. apply Z.eqb_eq in Heq. subst location0. reflexivity.
  - intros _. reflexivity.
  - destruct (String.string_dec r r) as [equality | Hne];
      [| intros Hbad; discriminate].
    rewrite (Eqdep_dec.UIP_dec String.string_dec equality eq_refl). simpl.
    intros Heq. apply RAs.ra_eqb_eq in Heq. subst value0. reflexivity.
Qed.

(** [unop] and [binop] are small enough to compare directly; both
    comparisons are heterogeneous in the operand types. *)
Definition unop_eqb {input1 output1} (op1 : unop input1 output1)
    {input2 output2} (op2 : unop input2 output2) : bool :=
  match op1, op2 with
  | UNot, UNot => true
  | UNeg, UNeg => true
  | URAOfInt r1, URAOfInt r2 => source_name_eqb r1 r2
  | _, _ => false
  end.

Definition binop_eqb {left1 right1 output1} (op1 : binop left1 right1 output1)
    {left2 right2 output2} (op2 : binop left2 right2 output2) : bool :=
  match op1, op2 with
  | BAdd, BAdd | BSub, BSub | BMul, BMul | BDiv, BDiv | BMod, BMod
  | BLt, BLt | BLe, BLe | BGt, BGt | BGe, BGe
  | BAnd, BAnd | BOr, BOr => true
  | BEq t1, BEq t2 => typ_eqb t1 t2
  | BNe t1, BNe t2 => typ_eqb t1 t2
  | _, _ => false
  end.

Lemma unop_eqb_refl {input output} (op : unop input output) :
  unop_eqb op op = true.
Proof.
  destruct op; simpl; [reflexivity | reflexivity | apply source_name_eqb_refl].
Qed.

Lemma binop_eqb_refl {left right output} (op : binop left right output) :
  binop_eqb op op = true.
Proof. destruct op; simpl; try reflexivity; apply typ_eqb_refl. Qed.

Lemma unop_eqb_input {input1 input2 output} (op1 : unop input1 output)
    (op2 : unop input2 output) : unop_eqb op1 op2 = true -> input1 = input2.
Proof.
  destruct op1; dependent destruction op2; simpl;
    try (intros Hbad; discriminate); intros _; reflexivity.
Qed.

Lemma unop_eqb_eq {input output} (op1 op2 : unop input output) :
  unop_eqb op1 op2 = true -> op1 = op2.
Proof.
  dependent destruction op1; dependent destruction op2; simpl;
    try (intros Hbad; discriminate); intros _; reflexivity.
Qed.

Lemma binop_eqb_operands {left1 right1 left2 right2 output}
    (op1 : binop left1 right1 output) (op2 : binop left2 right2 output) :
  binop_eqb op1 op2 = true -> left1 = left2 /\ right1 = right2.
Proof.
  destruct op1; dependent destruction op2; simpl;
    try (intros Hbad; discriminate);
    try (intros _; split; reflexivity);
    intros Heq; apply typ_eqb_eq in Heq; subst; split; reflexivity.
Qed.

Lemma binop_eqb_eq {left right output} (op1 op2 : binop left right output) :
  binop_eqb op1 op2 = true -> op1 = op2.
Proof.
  dependent destruction op1; dependent destruction op2; simpl;
    try (intros Hbad; discriminate); intros _; reflexivity.
Qed.

Fixpoint expr_eqb {F Δ t1} (e1 : expr F Δ t1) {t2} (e2 : expr F Δ t2)
    {struct e1} : bool :=
  match e1, e2 with
  | ERef r1, ERef r2 => value_ref_eqb r1 r2
  | EVal v1, EVal v2 => tval_eqb_het v1 v2
  | EUnOp op1 operand1, EUnOp op2 operand2 =>
      unop_eqb op1 op2 && expr_eqb operand1 operand2
  | EBinOp op1 first1 second1, EBinOp op2 first2 second2 =>
      binop_eqb op1 op2 && expr_eqb first1 first2 && expr_eqb second1 second2
  | _, _ => false
  end.

Lemma expr_eqb_refl {F Δ t} (e : expr F Δ t) : expr_eqb e e = true.
Proof.
  induction e; simpl.
  - exact (value_ref_eqb_refl reference).
  - exact (tval_eqb_het_refl value).
  - rewrite unop_eqb_refl. exact IHe.
  - rewrite binop_eqb_refl. rewrite IHe1. exact IHe2.
Qed.

Lemma expr_eqb_eq {F Δ} : forall {t} (e1 e2 : expr F Δ t),
  expr_eqb e1 e2 = true -> e1 = e2.
Proof.
  intros t e1. induction e1; intros e2; dependent destruction e2; simpl;
    try (intros Hbad; discriminate).
  - intros Heq. f_equal. exact (value_ref_eqb_eq _ _ Heq).
  - intros Heq. f_equal. exact (tval_eqb_het_eq _ _ Heq).
  - intros Heq. apply andb_prop in Heq as [Hop Hoperand].
    pose proof (unop_eqb_input op op0 Hop) as Hinput. subst input0.
    rewrite (unop_eqb_eq op op0 Hop). f_equal. exact (IHe1 _ Hoperand).
  - intros Heq. apply andb_prop in Heq as [Heq Hsecond].
    apply andb_prop in Heq as [Hop Hfirst].
    pose proof (binop_eqb_operands op op0 Hop) as [Hleft Hright].
    subst left0. subst right0.
    rewrite (binop_eqb_eq op op0 Hop). f_equal.
    + exact (IHe1_1 _ Hfirst).
    + exact (IHe1_2 _ Hsecond).
Qed.

Global Instance expr_eq_dec F Δ t : EqDecision (expr F Δ t).
Proof.
  intros e1 e2. destruct (expr_eqb e1 e2) eqn:Heq.
  - left. exact (expr_eqb_eq e1 e2 Heq).
  - right. intros ->. rewrite expr_eqb_refl in Heq. discriminate.
Defined.

(** Typed environments need no analogue of [env_typ_well_defined]. *)
Definition formal_env (F : context) := forall t, formal F t -> tval t.
Definition binder_env (Δ : context) := forall t, bvar Δ t -> tval t.

Definition atom_env := forall t, atom t -> tval t.

(** Procedure-entry atoms are generated by the verifier and interpreted
    afresh at every call.  Environments that agree on ordinary atoms may
    therefore differ on these call-local placeholders. *)
Definition stable_atoms_agree (left right : atom_env) : Prop :=
  forall t (symbolic : atom t),
    match symbolic with
    | Atom _ => left t symbolic = right t symbolic
    | ProcedureEntryAtom _ _ => True
    end.

Definition stable_atom_env (environment : atom_env) : atom_env :=
  fun t symbolic =>
    match symbolic with
    | Atom id => environment t (Atom id)
    | ProcedureEntryAtom _ _ => default_tval t
    end.

Lemma stable_atom_env_agree left right :
  stable_atoms_agree left right ->
  stable_atom_env left = stable_atom_env right.
Proof.
  intros Hagree. apply functional_extensionality_dep. intros t.
  apply functional_extensionality. intros symbolic.
  destruct symbolic as [id | procedure slot]; simpl;
    first exact (Hagree _ (Atom id)).
  reflexivity.
Qed.

Definition atom_stable {t} (symbolic : atom t) : Prop :=
  match symbolic with Atom _ => True | ProcedureEntryAtom _ _ => False end.

Definition ref_entry_free {F Δ t} (reference : value_ref F Δ t) : Prop :=
  match reference with
  | RefAtom symbolic => atom_stable symbolic
  | _ => True
  end.

Fixpoint expr_entry_free {F Δ t} (expression : expr F Δ t) : Prop :=
  match expression with
  | ERef reference => ref_entry_free reference
  | EVal _ => True
  | EUnOp _ operand => expr_entry_free operand
  | EBinOp _ first second =>
      expr_entry_free first /\ expr_entry_free second
  end.

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
  | URAOfInt r => fun value =>
      match value with VInt z => VRA (RAs.ra_of_int r z) end
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

Lemma interp_ref_stable_atoms {F Δ t}
    (formals : formal_env F) (binders : binder_env Δ)
    (left right : atom_env) (reference : value_ref F Δ t) :
  stable_atoms_agree left right -> ref_entry_free reference ->
  interp_ref formals binders left reference =
    interp_ref formals binders right reference.
Proof.
  intros Hagree Hfree. destruct reference; simpl; try reflexivity.
  destruct x as [id | procedure slot].
  - exact (Hagree _ (Atom id)).
  - contradiction.
Qed.

Lemma interp_expr_stable_atoms {F Δ t}
    (formals : formal_env F) (binders : binder_env Δ)
    (left right : atom_env) (expression : expr F Δ t) :
  stable_atoms_agree left right -> expr_entry_free expression ->
  interp_expr formals binders left expression =
  interp_expr formals binders right expression.
Proof.
  intros Hagree. induction expression; intros Hfree.
  - cbn [expr_entry_free interp_expr] in Hfree |-.
    destruct reference; simpl in Hfree |-; try reflexivity.
    destruct x as [id | procedure slot].
    + change (Some (left t (Atom id)) = Some (right t (Atom id))).
      apply f_equal. exact (Hagree _ (Atom id)).
    + contradiction.
  - reflexivity.
  - cbn [expr_entry_free] in Hfree.
    cbn [interp_expr]. rewrite (IHexpression Hfree). reflexivity.
  - cbn [expr_entry_free] in Hfree. destruct Hfree as [Hleft Hright].
    cbn [interp_expr].
    rewrite (IHexpression1 Hleft), (IHexpression2 Hright).
    reflexivity.
Qed.

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
  Definition ra_id (_ : source_name) : unit := tt.
  Definition ra_of_int (_ : source_name) (_ : Z) : unit := tt.
  Definition ra_valid (_ : source_name) (_ : unit) : Prop := True.
  Definition ra_fpu_allowed (_ : source_name) (_ _ : unit) : Prop := True.
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
