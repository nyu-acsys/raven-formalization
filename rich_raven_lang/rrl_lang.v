From stdpp Require Export binders strings.
From stdpp Require Import countable.
Require Import Eqdep_dec.
From stdpp Require Import gmap list sets coPset.
From stdpp Require Import namespaces.

From iris Require Import options.
From iris.algebra Require Import ofe cmra agree.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import ghost_map.
From iris.base_logic.lib Require Import invariants.

From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.proofmode Require Import tactics.

From raven_iris.simp_raven_lang Require Export lang lifting ghost_state.
From raven_iris.simp_raven_lang Require Import ghost_state.

From Coq.Program Require Import Wf.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Program.Equality.
Require Import Coq.Init.Datatypes.

Class inGs {I : Type} (Σ : gFunctors) (Gs : I → cmra) := {
  inGs_inG : ∀ i, inG Σ (Gs i)
}.

Context {I : Type}.
Context (Gs : I → cmra).
Context `{!inGs Σ Gs}. 

Context `{!simpLangG Σ}.

Definition lvar := string.

Definition proc_name := string.
Global Parameter proc_set : gset proc_name.

Definition pred_name := string.
Global Parameter pred_set : gset pred_name.

Definition inv_name := string.
Global Parameter inv_set : gset inv_name.

Class ResourceAlgebra (A: Type) := {
  comp : A -> A -> A;
  frame : A -> A -> A;
  valid : A -> Prop;
  fpuValid : A -> A -> Prop;
  fpuAxiom : forall x y, fpuValid x y -> valid x /\ valid y /\ forall c, (valid (comp x c) -> valid (comp y c));
}.


Record RA_Pack := {
  RA_carrier :> Type;
  RA_carrier_eqdec :> EqDecision RA_carrier;
  RA_inst :> ResourceAlgebra RA_carrier;
}.

Parameter fld_set : gset lang.fld_name.

Record fld := Fld { fld_name_val : fld_name; fld_typ : typ }.

Parameter ghost_map : loc -> fld_name -> gname.

Inductive val :=
| LitBool (b: bool) | LitInt (i: Z) | LitUnit | LitLoc (l: loc).

(* TODO: Figure out how to incorporate RA values *)
Inductive LitRAElem (r : RA_Pack) (x : RA_carrier r): Type. 

Scheme Equality for val.

Inductive LExpr :=
| LVar (x : lvar)
| LVal (v : val)
| LUnOp (op : un_op) (e : LExpr)
| LBinOp (op : bin_op) (e1 e2 : LExpr)
(* | LIfE  *)
| LIfE (e1 e2 e3 : LExpr)
| LStuck
.

(* Free variables of a logical expression *)
Fixpoint lexpr_fvars (e : LExpr) : gset lvar :=
  match e with
  | LVar x => {[x]}
  | LVal _ => ∅
  | LUnOp _ e => lexpr_fvars e
  | LBinOp _ e1 e2 => lexpr_fvars e1 ∪ lexpr_fvars e2
  | LIfE e1 e2 e3 => lexpr_fvars e1 ∪ lexpr_fvars e2 ∪ lexpr_fvars e3
  | LStuck => ∅
  end.

(* Free variables in all values of a map *)
Definition lexpr_map_fvars (M : gmap lvar LExpr) : gset lvar :=
  map_fold (λ (_ : lvar) (e : LExpr) (acc : gset lvar), lexpr_fvars e ∪ acc) ∅ M.

Lemma lexpr_map_fvars_spec (M : gmap lvar LExpr) (v : lvar) :
  v ∉ lexpr_map_fvars M ↔ ∀ k e, M !! k = Some e → v ∉ lexpr_fvars e.
Proof.
  unfold lexpr_map_fvars.
  induction M using map_ind.
  - rewrite map_fold_empty. split.
    + intros _ k e. rewrite lookup_empty. discriminate.
    + intros _. apply not_elem_of_empty.
  - rewrite map_fold_insert.
    2: { intros. set_solver. }
    2: { exact H. }
    rewrite not_elem_of_union. rewrite IHM.
    split.
    + intros [Hfv Hacc] k' e' Hk'.
      destruct (decide (k' = i)) as [-> | Hne].
      * rewrite lookup_insert in Hk'. injection Hk' as <-. exact Hfv.
      * rewrite lookup_insert_ne in Hk'; [| congruence].
        exact (Hacc k' e' Hk').
    + intro Hall. split.
      * eapply Hall. apply lookup_insert.
      * intros k' e' Hk'. apply (Hall k' e').
        destruct (decide (k' = i)) as [-> | Hne].
        { rewrite Hk' in H. discriminate. }
        { rewrite lookup_insert_ne; [exact Hk' | congruence]. }
Qed.

Definition symb_map : Type := lvar -> val.

Fixpoint interp_lexpr (le : LExpr) (mp : symb_map) : option val :=
  match le with
  | LVar x => Some (mp x)
  
  | LVal v => Some v

  | LUnOp op e =>
    match op with
    | NotBoolOp =>
      match interp_lexpr e mp with
      | Some (LitBool b) => Some (LitBool (negb b))
      | _ => None
      end
    | NegOp =>
      match interp_lexpr e mp with
      | Some (LitInt i) => Some (LitInt (-i))
      | _ => None
      end
    end
  
  | LBinOp op e1 e2 =>
    match op with
    | AddOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 + i2))
      | _, _ => None
      end

    | SubOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 - i2))
      | _, _ => None
      end

    | MulOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 * i2))
      | _, _ => None  
      end

    | DivOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 / i2))
      | _, _ => None
      end

    | ModOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 mod i2))
      | _, _ => None
      end

    | EqOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some v1, Some v2 => Some (LitBool (val_beq v1 v2))
      | _, _ => None
      end

    | NeOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some v1, Some v2 => Some (LitBool (negb (val_beq v1 v2)))
      | _, _ => None
      end

    | LtOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (Z.ltb i1 i2))
      | _, _ => None
      end

    | GtOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (Z.ltb i2 i1))
      | _, _ => None
      end

    | LeOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (Z.leb i1 i2))
      | _, _ => None
      end

    | GeOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (Z.leb i2 i1))
      | _, _ => None
      end

    | AndOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitBool b1), Some (LitBool b2) => Some (LitBool (b1 && b2))
      | _, _ => None
      end

    | OrOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitBool b1), Some (LitBool b2) => Some (LitBool (b1 || b2))
      | _, _ => None
      end
    end

  | LIfE e1 e2 e3 =>
    match interp_lexpr e1 mp with
    | Some (LitBool true) => interp_lexpr e2 mp
    | Some (LitBool false) => interp_lexpr e3 mp
    | _ => None
    end 

  | LStuck => None
  end.


Definition LExpr_holds (le : LExpr) (mp : symb_map) : Prop :=
  match interp_lexpr le mp with
  | Some v => v = LitBool true
  | None => False
  end.

Definition trnsl_val (v: lang.val) : val :=
match v with
| lang.LitBool b => LitBool b
| lang.LitInt i => LitInt i
| lang.LitUnit => LitUnit
| lang.LitLoc l => LitLoc l
end.

Lemma trnsl_val_inj : forall v1 v2, trnsl_val v1 = trnsl_val v2 -> v1 = v2.
Proof.
  destruct v1, v2; simpl; try discriminate; intros H; inversion H; subst; auto.
Qed.

(* Updating a symb_map at v does not affect interp_lexpr when v ∉ lexpr_fvars e *)
Lemma interp_lexpr_stable (e : LExpr) (q : symb_map) (v : lvar) (v' : val) :
  v ∉ lexpr_fvars e →
  interp_lexpr e (fun y => if (y =? v)%string then v' else q y) = interp_lexpr e q.
Proof.
  induction e; simpl; intro H.
  - (* LVar x: need x ≠ v *)
    apply not_elem_of_singleton in H.
    destruct (String.eqb_spec x v) as [Heq | Hne].
    + exfalso. exact (H (eq_sym Heq)).
    + reflexivity.
  - (* LVal *) reflexivity.
  - (* LUnOp *) rewrite IHe; [reflexivity | exact H].
  - (* LBinOp *)
    rewrite IHe1; [| set_solver]. rewrite IHe2; [| set_solver]. reflexivity.
  - (* LIfE *)
    rewrite IHe1; [| set_solver].
    destruct (interp_lexpr e1 q); try reflexivity.
    destruct v0; try reflexivity.
    destruct b.
    + rewrite IHe2; [reflexivity | set_solver].
    + rewrite IHe3; [reflexivity | set_solver].
  - (* LStuck *) reflexivity.
Qed.

Fixpoint lexpr_subst (expr : LExpr) (subst_map : gmap var LExpr) :=
match expr with
| LVar x => match subst_map !! x with
    | None => LVar x
    | Some e => e
    end
| LVal v => LVal v
| LUnOp op e => LUnOp op (lexpr_subst e subst_map)
| LBinOp op e1 e2 => LBinOp op (lexpr_subst e1 subst_map) (lexpr_subst e2 subst_map)
| LIfE e1 e2 e3 => LIfE (lexpr_subst e1 subst_map) (lexpr_subst e2 subst_map) (lexpr_subst e3 subst_map)
| LStuck => LStuck
end.

Global Instance ra_carrier_eqdec_instance (r : RA_Pack) : EqDecision (RA_carrier r) :=
  RA_carrier_eqdec r.

Global Instance val_eq : EqDecision val.
Proof.
  refine (fun x y =>
    match x, y with
    | LitBool b1, LitBool b2 => cast_if (decide (b1 = b2))
    | LitInt i1, LitInt i2 => cast_if (decide (i1 = i2))
    | LitUnit, LitUnit => left eq_refl
    | LitLoc l1, LitLoc l2 => cast_if (decide (l1 = l2))
    | _, _ => right _
    end). 
  all: try by f_equal.
  all: try intros Heq; inversion Heq; auto.
Qed.

Global Instance val_countable : Countable val.
Proof.
  refine (inj_countable'
    (λ v : val, match v with
      | LitBool b => inl b
      | LitInt i  => inr (inl i)
      | LitUnit   => inr (inr (inl tt))
      | LitLoc l  => inr (inr (inr l))
    end)
    (λ x : bool + (Z + (unit + loc)), match x with
      | inl b             => LitBool b
      | inr (inl i)       => LitInt i
      | inr (inr (inl _)) => LitUnit
      | inr (inr (inr l)) => LitLoc l
    end) _).
  intro v; destruct v; done.
Qed.

Global Instance LExpr_Eq : EqDecision LExpr.
Proof. solve_decision. Qed.

Global Instance LExpr_Countable : Countable LExpr.
Proof.
  (* lvar + val + un_op + bin_op is left-associative:
     = ((lvar + val) + un_op) + bin_op
     lvar x   ↦ inl (inl (inl x))
     val v    ↦ inl (inl (inr v))
     un_op op ↦ inl (inr op)
     bin_op op ↦ inr op *)
  set (enc := fix enc (e : LExpr) : gen_tree (lvar + val + un_op + bin_op) :=
    match e with
    | LVar x          => GenLeaf (inl (inl (inl x)))
    | LVal v          => GenLeaf (inl (inl (inr v)))
    | LUnOp op e      => GenNode 0 [GenLeaf (inl (inr op)); enc e]
    | LBinOp op e1 e2 => GenNode 1 [GenLeaf (inr op); enc e1; enc e2]
    | LIfE e1 e2 e3   => GenNode 2 [enc e1; enc e2; enc e3]
    | LStuck          => GenNode 3 []
    end).
  set (dec := fix dec (t : gen_tree (lvar + val + un_op + bin_op)) : option LExpr :=
    match t with
    | GenLeaf (inl (inl (inl x)))             => Some (LVar x)
    | GenLeaf (inl (inl (inr v)))             => Some (LVal v)
    | GenNode 0 [GenLeaf (inl (inr op)); t']  =>
        match dec t' with
        | Some e' => Some (LUnOp op e')
        | None    => None
        end
    | GenNode 1 [GenLeaf (inr op); t1; t2]   =>
        match dec t1 with
        | Some e1 => match dec t2 with
                     | Some e2 => Some (LBinOp op e1 e2)
                     | None    => None
                     end
        | None    => None
        end
    | GenNode 2 [t1; t2; t3]                 =>
        match dec t1 with
        | Some e1 => match dec t2 with
                     | Some e2 => match dec t3 with
                                  | Some e3 => Some (LIfE e1 e2 e3)
                                  | None    => None
                                  end
                     | None    => None
                     end
        | None    => None
        end
    | GenNode 3 []                            => Some LStuck
    | _                                       => None
    end).
  refine (inj_countable enc dec _).
  intro e; induction e; simpl; try done.
  - rewrite IHe. done.
  - rewrite IHe1; rewrite IHe2. done.
  - rewrite IHe1; rewrite IHe2; rewrite IHe3. done.
Qed.

Definition pvar_typs : Type := var -> typ.
Definition lvar_typs : Type := lvar -> typ.

Inductive stmt :=
| Seq (s1 s2 : stmt)
(* | Return (e : lang.expr) *)
| IfS (e : lang.expr) (s1 s2 : stmt)
| Assign (v : lang.var) (e : lang.expr)
(* | Free (e : lang.expr) *)
| SkipS
| StuckS (* stuck statement *)
(* | ExprS (e : lang.expr) *)
| Call (v : lang.var) (proc : proc_name) (args : list lang.expr)
| FldWr (v : lang.var) (fld : fld_name) (e2 : lang.expr)
| FldRd (v : lang.var) (e : lang.expr) (fld : fld_name)
| CAS (v : lang.var) (e1 : lang.expr) (fld : fld_name) (e2 : lang.expr) (e3 : lang.expr)
| Alloc (v : lang.var) (fs: list (lang.fld_name * lang.val))
| Spawn (proc : proc_name) (args : list lang.expr)
| UnfoldPred (pred : pred_name) (args : list lang.expr)
| FoldPred (pred : pred_name) (args : list lang.expr)
| InvAccessBlock (inv: inv_name) (args : list lang.expr) (body : stmt)
(* | UnfoldInv (inv: inv_name) (args : list lang.expr)
| FoldInv (inv: inv_name) (args : list lang.expr) *)
| Fpu (e : lang.expr) (fld : fld_name) (RAPack : RA_Pack) (old_val : RA_carrier RAPack) (new_val : RA_carrier RAPack)
.

Inductive assertion :=
| LProc (proc_name : proc_name) (proc_entry : ProcRecord)
| LStack (σ : gmap lang.var lvar)
| LExprA (p: LExpr)
| LPure (p : Prop)
| LOwn (e: LExpr) (fld: fld_name) (chunk: val)
| LGhostOwn (e: LExpr) (fld: fld_name) (RAPack: RA_Pack) (chunk: RA_carrier RAPack)
| LForall (v : var) (body : assertion)
| LExists (v : var) (body : assertion)
| LImpl (cond : LExpr) (body : assertion)
| LInv (inv_name : inv_name) (args : list LExpr)
| LPred (pred_name : pred_name) (args : list LExpr)
| LAnd (assert1 : assertion) (assert2 : assertion)

with ProcRecord := | Proc 
  (proc_args: list (var * typ))
  (proc_local_vars: list (var * typ))
  (proc_precond : assertion)
  (proc_postcond : assertion)
  (body : stmt).

Definition proc_args_of (p : ProcRecord) :=
  match p with Proc args _ _ _ _ => args end.

Definition proc_locals_of (p : ProcRecord) :=
  match p with Proc _ locs _ _ _ => locs end.

Definition proc_precond_of (p : ProcRecord) :=
  match p with Proc _ _ pre _ _ => pre end.

Definition proc_postcond_of (p : ProcRecord) :=
  match p with Proc _ _ _ post _ => post end.

Definition proc_body_of (p : ProcRecord) :=
  match p with Proc _ _ _ _ body => body end.

Fixpoint subst (ra: assertion) (mp: gmap var LExpr) : assertion := match ra with
| LProc p p_e => LProc p p_e
| LStack σ => LStack σ
| LExprA e => LExprA (lexpr_subst e mp)
| LPure p => LPure p
| LOwn e fld chunk => LOwn (lexpr_subst e mp) fld chunk
| LGhostOwn e fld RAPack chunk => LGhostOwn (lexpr_subst e mp) fld RAPack chunk
| LForall vars body => LForall vars (subst body mp)
| LExists vars body => LExists vars (subst body mp)
| LImpl cond body => LImpl (lexpr_subst cond mp) (subst body mp)
| LInv inv_name args => 
    LInv inv_name (map (fun expr => lexpr_subst expr mp) args)
| LPred pred_name args =>
    LPred pred_name (map (fun expr => lexpr_subst expr mp) args)
| LAnd a1 a2 => LAnd (subst a1 mp) (subst a2 mp)
end.

(* Builds an association gmap out of a key list zipped positionally against
   a value list -- the one low-level pattern every symbolic stack (var ->
   lvar), stack frame (var -> val / lvar -> val), and substitution map
   below ultimately reduces to. *)
Definition assoc_map `{Countable K} {V : Type} (ks : list K) (vs : list V) : gmap K V :=
  list_to_map (zip ks vs).

(* The two recurring shapes of substitution map built out of a name list
   paired positionally with either lvars (symbolic, used in preconditions
   naming the entry lvars of a fresh call frame) or concrete values
   (ghost/logical, used when the map is meant to evaluate away): factors
   out the zip/list_to_map/map boilerplate at every subst call site that
   builds one from a procedure's, invariant's, or predicate's argument
   names. *)
Definition lvar_subst_map (names : list var) (lvs : list lvar) : gmap var LExpr :=
  assoc_map names (map LVar lvs).
Definition val_subst_map (names : list var) (vals : list lang.val) : gmap var LExpr :=
  assoc_map names (map (fun v => LVal (trnsl_val v)) vals).

Record InvRecord := Inv {
  inv_args: list var;
  inv_body: assertion;
}.

(* Well-formedness: the body only references its formal argument variables,
   so substitution commutes with argument substitution. *)
Definition InvBodyWF (r : InvRecord) : Prop :=
  forall (args : list LExpr) (M : gmap var LExpr),
    length args = length r.(inv_args) →
    subst (r.(inv_body))
      (list_to_map (zip (r.(inv_args)) (map (fun e => lexpr_subst e M) args))) =
    subst (subst (r.(inv_body))
      (list_to_map (zip (r.(inv_args)) args))) M.

Global Parameter inv_map : gmap inv_name InvRecord.

Record PredRecord := Pred {
  pred_args: list var;
  pred_body: assertion;
}.

(* Well-formedness: analogous condition for predicate bodies. *)
Definition PredBodyWF (r : PredRecord) : Prop :=
  forall (args : list LExpr) (M : gmap var LExpr),
    length args = length r.(pred_args) →
    subst (r.(pred_body))
      (list_to_map (zip (r.(pred_args)) (map (fun e => lexpr_subst e M) args))) =
    subst (subst (r.(pred_body))
      (list_to_map (zip (r.(pred_args)) args))) M.

Global Parameter pred_map : gmap pred_name PredRecord.

Inductive StackFree : assertion → Prop :=
| SF_Proc proc_name proc_entry :
    StackFree (LProc proc_name proc_entry)
| SF_Expr p :
    StackFree (LExprA p)
| SF_Pure p :
    StackFree (LPure p)
| SF_Own e fld chunk :
    StackFree (LOwn e fld chunk)
| SF_GhostOwn e fld RAPAck chunk :
    StackFree (LGhostOwn e fld RAPAck chunk)
| SF_Forall v body :
    StackFree body →
    StackFree (LForall v body)
| SF_Exists v body :
    StackFree body →
    StackFree (LExists v body)
| SF_Impl cond body :
    StackFree body →
    StackFree (LImpl cond body)
| SF_And a1 a2 :
    StackFree a1 →
    StackFree a2 →
    StackFree (LAnd a1 a2)
| SF_Inv inv_name args inv_record :
    inv_map !! inv_name = Some inv_record →
    length args = length inv_record.(inv_args) →
    StackFree (subst (inv_record.(inv_body)) (list_to_map (zip inv_record.(inv_args) args))) →
    StackFree (LInv inv_name args)
| SF_Pred pred_name args pred_record :
    pred_map !! pred_name = Some pred_record →
    length args = length pred_record.(pred_args) →
    StackFree (subst (pred_record.(pred_body)) (list_to_map (zip pred_record.(pred_args) args))) →
    StackFree (LPred pred_name args).

Global Parameter proc_map : gmap proc_name ProcRecord.


(* LExists binder variables of an assertion (does NOT descend into LInv/LPred bodies) *)
Fixpoint assertion_exists_binders (a : assertion) : gset lvar :=
  match a with
  | LExists v body => {[v]} ∪ assertion_exists_binders body
  | LForall _ body => assertion_exists_binders body
  | LImpl _ body => assertion_exists_binders body
  | LAnd a1 a2 => assertion_exists_binders a1 ∪ assertion_exists_binders a2
  | _ => ∅
  end.

(* Free variables appearing in LExpr nodes of an assertion (does NOT descend into LInv/LPred bodies) *)
Fixpoint assertion_lexpr_fvars (a : assertion) : gset lvar :=
  match a with
  | LExprA e => lexpr_fvars e
  | LOwn e _ _ => lexpr_fvars e
  | LGhostOwn e _ _ _ => lexpr_fvars e
  | LForall _ body => assertion_lexpr_fvars body
  | LExists _ body => assertion_lexpr_fvars body
  | LImpl cond body => lexpr_fvars cond ∪ assertion_lexpr_fvars body
  | LInv _ args => ⋃ (lexpr_fvars <$> args)
  | LPred _ args => ⋃ (lexpr_fvars <$> args)
  | LAnd a1 a2 => assertion_lexpr_fvars a1 ∪ assertion_lexpr_fvars a2
  | _ => ∅
  end.

Lemma assertion_exists_binders_subst (a : assertion) (M : gmap lvar LExpr) :
  assertion_exists_binders (subst a M) = assertion_exists_binders a.
Proof.
  induction a; simpl; try reflexivity.
  - rewrite IHa. reflexivity.
  - rewrite IHa. reflexivity.
  - rewrite IHa. reflexivity.
  - rewrite IHa1 IHa2. reflexivity.
Qed.

(* Substitution composes: if all fvars of e are in dom σ, then substituting
   via (fmap (fun e => lexpr_subst e M) σ) equals substituting σ then M. *)
Lemma lexpr_subst_compose (e : LExpr) (σ M : gmap var LExpr) :
  lexpr_fvars e ⊆ dom σ →
  lexpr_subst e (fmap (fun e' => lexpr_subst e' M) σ) = lexpr_subst (lexpr_subst e σ) M.
Proof.
  induction e; simpl; intro Hfv.
  - (* LVar x *)
    have Hx : x ∈ dom σ. { set_solver. }
    apply elem_of_dom in Hx as [ex Hx].
    rewrite lookup_fmap Hx /=. done.
  - done.
  - have := IHe Hfv. congruence.
  - have H1 := IHe1 ltac:(set_solver). have H2 := IHe2 ltac:(set_solver). congruence.
  - have H1 := IHe1 ltac:(set_solver). have H2 := IHe2 ltac:(set_solver).
    have H3 := IHe3 ltac:(set_solver). congruence.
  - done.
Qed.

(* Zipping keys with a mapped list equals fmapping the list_to_map. *)
Lemma list_to_map_zip_fmap (ks : list var) (vs : list LExpr) (M : gmap var LExpr) :
  (list_to_map (zip ks (map (fun e => lexpr_subst e M) vs)) : gmap var LExpr) =
  fmap (fun e => lexpr_subst e M) (list_to_map (zip ks vs) : gmap var LExpr).
Proof.
  revert vs. induction ks as [| k ks' IH]; intro vs.
  - done.
  - destruct vs as [| v vs']; [done |].
    simpl. rewrite IH fmap_insert. done.
Qed.

(* When lengths match, dom of list_to_map(zip) equals list_to_set of keys. *)
Lemma dom_list_to_map_zip (args : list var) (vals : list LExpr) :
  length args = length vals →
  dom (list_to_map (zip args vals) : gmap var LExpr) = list_to_set args.
Proof.
  revert vals. induction args as [| a args' IH]; intros vals Hlen.
  - done.
  - destruct vals as [| v vals']; [simpl in Hlen; lia |].
    simpl. rewrite dom_insert_L IH; [done | simpl in Hlen; lia].
Qed.

(* Assertion substitution composes: if all lvar fvars of a are in dom σ, then
   subst a (fmap (fun e => lexpr_subst e M) σ) = subst (subst a σ) M. *)
Lemma assertion_subst_compose (a : assertion) (σ M : gmap var LExpr) :
  assertion_lexpr_fvars a ⊆ dom σ →
  subst a (fmap (fun e => lexpr_subst e M) σ) = subst (subst a σ) M.
Proof.
  induction a; simpl; intro Hfv; try done.
  - f_equal. apply lexpr_subst_compose. exact Hfv.
  - f_equal. apply lexpr_subst_compose. exact Hfv.
  - f_equal. apply lexpr_subst_compose. exact Hfv.
  - f_equal. apply IHa. exact Hfv.
  - f_equal. apply IHa. exact Hfv.
  - f_equal; [apply lexpr_subst_compose | apply IHa]; set_solver.
  - (* LInv *) f_equal. rewrite map_map. apply Forall_fmap_ext_1.
    apply Forall_forall. intros e He.
    apply lexpr_subst_compose.
    have Hsub : lexpr_fvars e ⊆ ⋃ (lexpr_fvars <$> args). {
      intros x Hx. apply elem_of_union_list. exists (lexpr_fvars e).
      split; [apply elem_of_list_fmap; exists e; split; [done | exact He] | exact Hx].
    }
    set_solver.
  - (* LPred *) f_equal. rewrite map_map. apply Forall_fmap_ext_1.
    apply Forall_forall. intros e He.
    apply lexpr_subst_compose.
    have Hsub : lexpr_fvars e ⊆ ⋃ (lexpr_fvars <$> args). {
      intros x Hx. apply elem_of_union_list. exists (lexpr_fvars e).
      split; [apply elem_of_list_fmap; exists e; split; [done | exact He] | exact Hx].
    }
    set_solver.
  - f_equal; [apply IHa1 | apply IHa2]; set_solver.
Qed.

(* InvBodyWF follows from the simple well-scopedness condition. *)
Lemma inv_body_wf_from_scoped (r : InvRecord) :
  assertion_lexpr_fvars r.(inv_body) ⊆ list_to_set r.(inv_args) →
  InvBodyWF r.
Proof.
  intros Hscoped args M Hlen.
  have Hdom : dom (list_to_map (zip r.(inv_args) args) : gmap var LExpr) = list_to_set r.(inv_args).
  { apply dom_list_to_map_zip. lia. }
  have Hfv : assertion_lexpr_fvars r.(inv_body) ⊆ dom (list_to_map (zip r.(inv_args) args) : gmap var LExpr).
  { rewrite Hdom. exact Hscoped. }
  rewrite list_to_map_zip_fmap.
  exact (assertion_subst_compose r.(inv_body) _ M Hfv).
Qed.

(* PredBodyWF follows from the simple well-scopedness condition. *)
Lemma pred_body_wf_from_scoped (r : PredRecord) :
  assertion_lexpr_fvars r.(pred_body) ⊆ list_to_set r.(pred_args) →
  PredBodyWF r.
Proof.
  intros Hscoped args M Hlen.
  have Hdom : dom (list_to_map (zip r.(pred_args) args) : gmap var LExpr) = list_to_set r.(pred_args).
  { apply dom_list_to_map_zip. lia. }
  have Hfv : assertion_lexpr_fvars r.(pred_body) ⊆ dom (list_to_map (zip r.(pred_args) args) : gmap var LExpr).
  { rewrite Hdom. exact Hscoped. }
  rewrite list_to_map_zip_fmap.
  exact (assertion_subst_compose r.(pred_body) _ M Hfv).
Qed.

(* Mapping from invariant names to Iris namespaces, supplied by the user. *)
Parameter inv_namespace_map : inv_name -> namespace.

(* Well-formedness predicate for a program (proc_map, inv_map, pred_map).
   Bundles all structural side-conditions required by the translation theorem.
   A user of rrl_validity must supply one ProgramWF witness for their concrete program. *)
Record ProgramWF : Prop := {
  (* ── Procedure map ───────────────────────────────────────────────────── *)
  (* Argument names of every procedure are distinct. *)
  pwf_proc_args_unique :
    map_Forall (λ _ r, NoDup (proc_args_of r).*1) proc_map;

  (* "#ret_val" is a reserved name, never a formal argument: keeps the
     operationally-appended "#ret_val" slot (see lang.v's RTCallStep) from
     ever colliding with a real argument. *)
  pwf_proc_ret_val_fresh :
    map_Forall (λ _ r, "#ret_val" ∉ (proc_args_of r).*1) proc_map;

  (* Local-variable names of every procedure are distinct. *)
  pwf_proc_locals_unique :
    map_Forall (λ _ r, NoDup (proc_locals_of r).*1) proc_map;

  (* Formal-argument and local-variable names never collide -- both get their
     own pre-allocated slot in a fresh stack frame (see lang.v's
     RTCallStep/SpawnStep). *)
  pwf_proc_args_locals_disjoint :
    map_Forall (λ _ r, (proc_args_of r).*1 ## (proc_locals_of r).*1) proc_map;

  (* "#ret_val" is declared as one of the procedure's own local variables,
     with whatever type its associated proc_record gives it -- it is
     initialized (like every other local) to a non-deterministically chosen
     value of that type, then read out again at the return point. *)
  pwf_proc_ret_val_declared :
    map_Forall (λ _ r, "#ret_val" ∈ (proc_locals_of r).*1) proc_map;

  (* Pre- and postconditions of every procedure are stack-free. *)
  pwf_proc_stack_free :
    map_Forall (λ _ r,
      StackFree (proc_precond_of r) ∧ StackFree (proc_postcond_of r)) proc_map;

  (* LExpr free variables in pre/post are bounded by the formal argument names. *)
  pwf_proc_fvars_bounded :
    map_Forall (λ _ r,
      assertion_lexpr_fvars (proc_precond_of r) ⊆ list_to_set (proc_args_of r).*1 ∧
      assertion_lexpr_fvars (proc_postcond_of r) ⊆ {["#ret_val"]} ∪ list_to_set (proc_args_of r).*1) proc_map;

  (* LExists binders in pre/post are disjoint from the free vars of any lexpr map. *)
  pwf_proc_binders_fresh :
    ∀ proc_nm r M, proc_map !! proc_nm = Some r →
      assertion_exists_binders (proc_precond_of r) ## lexpr_map_fvars M ∧
      assertion_exists_binders (proc_postcond_of r) ## lexpr_map_fvars M;

  (* ── Invariant map ───────────────────────────────────────────────────── *)
  (* LExpr fvars of an invariant body are bounded by its formal argument names. *)
  pwf_inv_fvars_scoped :
    map_Forall (λ _ r, assertion_lexpr_fvars r.(inv_body) ⊆ list_to_set r.(inv_args)) inv_map;

  (* LExpr fvars of a substituted invariant body are bounded by the argument fvars. *)
  pwf_inv_fvars_bounded :
    ∀ inv_nm r args, inv_map !! inv_nm = Some r →
      assertion_lexpr_fvars (subst r.(inv_body) (list_to_map (zip r.(inv_args) args))) ⊆
        ⋃ (lexpr_fvars <$> args);

  (* LExists binders in an invariant body are disjoint from any lexpr map's fvars. *)
  pwf_inv_binders_fresh :
    ∀ inv_nm r M, inv_map !! inv_nm = Some r →
      assertion_exists_binders r.(inv_body) ## lexpr_map_fvars M;

  (* ── Predicate map ───────────────────────────────────────────────────── *)
  (* LExpr fvars of a predicate body are bounded by its formal argument names. *)
  pwf_pred_fvars_scoped :
    map_Forall (λ _ r, assertion_lexpr_fvars r.(pred_body) ⊆ list_to_set r.(pred_args)) pred_map;

  (* LExpr fvars of a substituted predicate body are bounded by the argument fvars. *)
  pwf_pred_fvars_bounded :
    ∀ pred_nm r args, pred_map !! pred_nm = Some r →
      assertion_lexpr_fvars (subst r.(pred_body) (list_to_map (zip r.(pred_args) args))) ⊆
        ⋃ (lexpr_fvars <$> args);

  (* LExists binders in a predicate body are disjoint from any lexpr map's fvars. *)
  pwf_pred_binders_fresh :
    ∀ pred_nm r M, pred_map !! pred_nm = Some r →
      assertion_exists_binders r.(pred_body) ## lexpr_map_fvars M;

  (* ── Invariant namespaces ─────────────────────────────────────────────── *)
  (* Namespaces assigned to invariants are pairwise disjoint. *)
  pwf_inv_namespace_disjoint :
    ∀ inv1 inv2 : inv_name,
      inv1 ∈ inv_set → inv2 ∈ inv_set →
        (inv_namespace_map inv1) ## (inv_namespace_map inv2);
}.

(* Type inference for expressions---placed here so expr_well_defined can use it. *)
Definition typeOf (v: lang.val) : typ :=
match v with
| lang.LitBool _ => TpBool
| lang.LitInt _ => TpInt
| lang.LitUnit => TpUnit
| lang.LitLoc _ => TpLoc
end.

Lemma typeOf_val_has_typ v t : typeOf v = t <-> lang.val_has_typ v t.
Proof. destruct v, t; simpl; split; done. Qed.

Fixpoint inf_expr (ρ: pvar_typs) (e: lang.expr) : option typ :=
match e with
| Var x => Some (ρ x)
| Val v => Some (typeOf v)
| UnOp NotBoolOp e =>
  match inf_expr ρ e with
  | Some TpBool => Some TpBool
  | _ => None
  end
| UnOp NegOp e =>
  match inf_expr ρ e with
  | Some TpInt => Some TpInt
  | _ => None
  end
| BinOp (AddOp | SubOp | MulOp | DivOp | ModOp) e1 e2 =>
  match inf_expr ρ e1, inf_expr ρ e2 with
  | Some TpInt, Some TpInt => Some TpInt
  | _, _ => None
  end
| BinOp (LtOp | GtOp | LeOp | GeOp) e1 e2 =>
  match inf_expr ρ e1, inf_expr ρ e2 with
  | Some TpInt, Some TpInt => Some TpBool
  | _, _ => None
  end
| BinOp (AndOp | OrOp) e1 e2 =>
  match inf_expr ρ e1, inf_expr ρ e2 with
  | Some TpBool, Some TpBool => Some TpBool
  | _, _ => None
  end
| BinOp (EqOp | NeOp) e1 e2 =>
  match inf_expr ρ e1, inf_expr ρ e2 with
  | Some tp1, Some tp2 => if typ_beq tp1 tp2 then Some TpBool else None
  | _, _ => None
  end
| IfE e1 e2 e3 =>
  match inf_expr ρ e1, inf_expr ρ e2, inf_expr ρ e3 with
  | Some TpBool, Some tp2, Some tp3 => if typ_beq tp2 tp3 then Some tp2 else None
  | _, _, _ => None
  end
| _ => None
end.

(* An expression is well-defined under type context ρ iff type inference succeeds. *)
Definition expr_well_defined (ρ : pvar_typs) (e : lang.expr) : Prop :=
  ∃ tp, inf_expr ρ e = Some tp.

(* Separate type-checking judgment for procedure-call arguments: each argument
   expression's inferred type must match the corresponding formal parameter's
   declared type. Kept independent of RavenHoareTriple/stmt_well_defined's other
   rules so type-checking and verification stay cleanly separated. *)
Definition proc_call_args_well_typed (ρ : pvar_typs) (args : list lang.expr) (proc_entry : ProcRecord) : Prop :=
  Forall2 (fun arg arg_decl => inf_expr ρ arg = Some (snd arg_decl)) args (proc_args_of proc_entry).

Inductive stmt_well_defined : pvar_typs -> stmt -> Prop :=
| SeqTp ρ s1 s2 :
  stmt_well_defined ρ s1 ->
  stmt_well_defined ρ s2 ->
  stmt_well_defined ρ (Seq s1 s2)
(* | ReturnTp e :
    expr_well_defined ρ e ->
    stmt_well_defined (Return e) *)
| IfSTp ρ e s1 s2 :
    expr_well_defined ρ e ->
    stmt_well_defined ρ s1 ->
    stmt_well_defined ρ s2 ->
    stmt_well_defined ρ (IfS e s1 s2)
| AssignTp ρ v e:
    expr_well_defined ρ e ->
    stmt_well_defined ρ (Assign v e)
(* | FreeTp e:
    expr_well_defined ρ e ->
    stmt_well_defined (Free e) *)
| SkipSTp ρ : stmt_well_defined ρ (SkipS)
| StuckSTp ρ : stmt_well_defined ρ (StuckS)
(* | ExprSTp e:
    expr_well_defined ρ e ->
    stmt_well_defined (ExprS e) *)
| CallTp ρ v proc proc_entry args:
    proc ∈ proc_set ->
    proc_map !! proc = Some proc_entry ->
    length args = length (proc_args_of proc_entry) ->
    (Forall (fun arg => expr_well_defined ρ arg) args) ->
    proc_call_args_well_typed ρ args proc_entry ->
    stmt_well_defined ρ (Call v proc args)
| FldWrTp ρ v fld e2:
    (fld ∈ fld_set) ->
    expr_well_defined ρ e2 ->
    stmt_well_defined ρ (FldWr v fld e2)
| FldRdTp ρ v e fld:
    fld ∈ fld_set ->
    expr_well_defined ρ e ->
    stmt_well_defined ρ (FldRd v e fld)
| CASTp ρ v e1 fld e2 e3:
    fld ∈ fld_set ->
    expr_well_defined ρ e1 ->
    expr_well_defined ρ e2 ->
    expr_well_defined ρ e3 ->
    stmt_well_defined ρ (CAS v e1 fld e2 e3)
| AllocTp ρ v fs:
    Forall (fun fld_v => (fst fld_v) ∈ fld_set) fs ->
    stmt_well_defined ρ (Alloc v fs)
| SpawnTp ρ proc args:
    proc ∈ proc_set ->
    Forall (fun arg => expr_well_defined ρ arg) args ->
    stmt_well_defined ρ (Spawn proc args)
| UnfoldPredTp ρ pred args :
    pred ∈ pred_set ->
    Forall (fun arg => expr_well_defined ρ arg) args ->
    stmt_well_defined ρ (UnfoldPred pred args)
| FoldPredTp ρ pred args :
    pred ∈ pred_set ->
    Forall (fun arg => expr_well_defined ρ arg) args ->
    stmt_well_defined ρ (FoldPred pred args)
| InvAccessBlockTp ρ inv args stmt:
    inv ∈ inv_set ->
    Forall (fun arg => expr_well_defined ρ arg) args ->
    stmt_well_defined ρ stmt ->
    stmt_well_defined ρ (InvAccessBlock inv args stmt)

(* | UnfoldInvTp inv args :
    inv ∈ inv_set ->
    Forall (fun arg => expr_well_defined ρ arg) args ->
    stmt_well_defined (UnfoldInv inv args)
| FoldInvTp inv args :
    inv ∈ inv_set ->
    Forall (fun arg => expr_well_defined ρ arg) args ->
    stmt_well_defined (FoldInv inv args) *)
| FpuTp ρ e fld RAPack old_val new_val :
    fld ∈ fld_set ->
    expr_well_defined ρ e ->
    stmt_well_defined ρ (Fpu e fld RAPack  old_val new_val)
.

Lemma alloc_stmt_well_defined ρ x fld val fld_vals : 
  stmt_well_defined ρ (Alloc x ((fld, val) :: fld_vals)) -> stmt_well_defined ρ (Alloc x fld_vals).
Proof.
  intros H.
  inversion H.
  apply (AllocTp ρ x fld_vals).
  inversion H2. exact H7.
Qed.

Section AtomicAnnotations.
  Inductive AtomicStep : Type :=
  | Closed
  | Opened (S : list (inv_name * list LExpr))
  | Stepped (S : list (inv_name * list LExpr))
  .

  Definition AtomicAnnotation : Type := (gset inv_name * AtomicStep).

  Definition maskAnnot : Type := gset inv_name.

End AtomicAnnotations.

Section Translation.

    Definition trnsl_lval (v: val) : lang.val :=
    match v with
    | LitBool b => (lang.LitBool b) 
    | LitInt i => (lang.LitInt i)
    | LitUnit => (lang.LitUnit)
    | LitLoc l => (lang.LitLoc (lang.Loc l.(loc_car)))
    (* | LitRAElem _ _ => None *)
    end.

    Lemma trnsl_lval_injective v1 v2 : trnsl_lval v1 = trnsl_lval v2 -> v1 = v2.
    Proof.
      destruct v1 eqn:Hv1, v2 eqn:Hv2; try discriminate.
      - simpl; intros; inversion H. done.
      - simpl; intros; inversion H. done.
      - simpl; intros; inversion H. done.
      - simpl; intros. inversion H. destruct l, l0. simpl in H1; subst loc_car0. done.
    Qed. 

    Lemma trnsl_lval_trnsl_val_inverse y: trnsl_lval (trnsl_val y) = y.
    Proof.
      destruct y eqn:Hy; try simpl; try done.
      destruct l. simpl. done.
    Qed.

    (* Every rrl val v satisfies: trnsl_val (trnsl_lval v) = v *)
    Lemma trnsl_val_trnsl_lval_inverse (v : val) : trnsl_val (trnsl_lval v) = v.
    Proof.
      destruct v; simpl; try done.
      destruct l. simpl. done.
    Qed.

    (* val_beq and bool_decide agree modulo trnsl_lval *)
    Lemma val_beq_bool_decide (v1 v2 : val) :
      val_beq v1 v2 = bool_decide (trnsl_lval v1 = trnsl_lval v2).
    Proof.
      destruct (val_beq v1 v2) eqn:Hbeq.
      - symmetry. apply bool_decide_true.
        apply internal_val_dec_bl in Hbeq. rewrite Hbeq. done.
      - symmetry. apply bool_decide_false.
        intro Heq. apply trnsl_lval_injective in Heq.
        apply internal_val_dec_lb in Heq. rewrite Heq in Hbeq. discriminate.
    Qed.

    Definition stack: Type := gmap lang.var lvar.

    Definition symb_stk_to_stk_frm (stk : stack) (mp : symb_map) : stack_frame :=
      StackFrame (fmap (λ v, trnsl_lval (mp v)) stk).

    (* Given a richness guarantee on σ (enough distinct lvars of any type,
       avoiding any finite exclusion set), pick a list of distinct lvars
       matching a list of declared types -- used to synthesize a procedure's
       own entry stack out of fresh (not globally shared) lvar names, one per
       formal arg / local variable, so that different procedures' same-named
       parameters no longer need to agree on a single global type via σ. *)
    Lemma fresh_lvars_list (σ : lvar_typs)
        (Hrich : ∀ (t : typ) (excl : gset lvar), ∃ lv, lv ∉ excl ∧ σ lv = t)
        (decls : list (var * typ)) (excl0 : gset lvar) :
      ∃ lvs : list lvar,
        length lvs = length decls ∧
        Forall2 (fun decl lv => σ lv = snd decl) decls lvs ∧
        NoDup lvs ∧
        Forall (fun lv => lv ∉ excl0) lvs.
    Proof.
      revert excl0. induction decls as [| [v tp] decls IH]; intros excl0.
      - exists []. repeat split; try constructor.
      - destruct (Hrich tp excl0) as [lv [Hlv_notin Hlv_typ]].
        destruct (IH ({[lv]} ∪ excl0)) as [lvs [Hlen [HF2 [Hnodup Hexcl]]]].
        exists (lv :: lvs). repeat split.
        + simpl. lia.
        + constructor; [exact Hlv_typ | exact HF2].
        + constructor.
          * intro Hin. eapply (proj1 (Forall_forall _ _)) in Hexcl; [| exact Hin]. set_solver.
          * exact Hnodup.
        + constructor.
          * exact Hlv_notin.
          * eapply Forall_impl; [exact Hexcl |]. intros lv' Hlv'. set_solver.
    Qed.

    (* A pair of lvar lists that is a legal fresh entry-stack for calling
       proc_record under σ: right length and σ-typed against proc_record's
       args/locals declarations, each list duplicate-free, and the two
       mutually disjoint. Parametric in σ and proc_record so that every
       well-formedness condition a synthesized "args ⊎ locals" entry stack
       must satisfy for that specific call lives in the type itself, rather
       than as separate side-conditions threaded wherever such a pair is
       used. *)
    Record proc_entry_lvars (σ : lvar_typs) (proc_record : ProcRecord) := ProcEntryLvars {
      dll_args : list lvar;
      dll_locals : list lvar;
      dll_args_len : length dll_args = length (proc_args_of proc_record);
      dll_locals_len : length dll_locals = length (proc_locals_of proc_record);
      dll_args_typed : Forall2 (fun decl lv => σ lv = snd decl) (proc_args_of proc_record) dll_args;
      dll_locals_typed : Forall2 (fun decl lv => σ lv = snd decl) (proc_locals_of proc_record) dll_locals;
      dll_args_nodup : NoDup dll_args;
      dll_locals_nodup : NoDup dll_locals;
      dll_disjoint : ∀ lv, lv ∈ dll_args → lv ∉ dll_locals;
    }.
    Global Arguments dll_args {_ _}.
    Global Arguments dll_locals {_ _}.
    Global Arguments dll_args_len {_ _}.
    Global Arguments dll_locals_len {_ _}.
    Global Arguments dll_args_typed {_ _}.
    Global Arguments dll_locals_typed {_ _}.
    Global Arguments dll_args_nodup {_ _}.
    Global Arguments dll_locals_nodup {_ _}.
    Global Arguments dll_disjoint {_ _}.

    (* fresh_lvars_list, applied twice (locals avoiding the args' own
       choices) and packaged into a proc_entry_lvars for proc_record. *)
    Lemma fresh_proc_entry_lvars (σ : lvar_typs)
        (Hrich : ∀ (t : typ) (excl : gset lvar), ∃ lv, lv ∉ excl ∧ σ lv = t)
        (proc_record : ProcRecord) :
      ∃ dll : proc_entry_lvars σ proc_record, Logic.True.
    Proof.
      destruct (fresh_lvars_list σ Hrich (proc_args_of proc_record) ∅)
        as (args_lvs & Hargs_len & Hargs_typed & Hargs_nodup & _).
      destruct (fresh_lvars_list σ Hrich (proc_locals_of proc_record) (list_to_set args_lvs))
        as (locals_lvs & Hlocals_len & Hlocals_typed & Hlocals_nodup & Hlocals_excl).
      have Hdisjoint : ∀ lv, lv ∈ args_lvs → lv ∉ locals_lvs.
      { intros lv Hin1 Hin2.
        pose proof (proj1 (Forall_forall (λ lv0, lv0 ∉ list_to_set args_lvs) locals_lvs) Hlocals_excl lv Hin2) as Hcontra.
        apply Hcontra. rewrite elem_of_list_to_set. exact Hin1. }
      exists (ProcEntryLvars σ proc_record args_lvs locals_lvs Hargs_len Hlocals_len Hargs_typed Hlocals_typed
                Hargs_nodup Hlocals_nodup Hdisjoint).
      exact Logic.I.
    Qed.

    (* Reconstructs the exact operational stack_frame -- the frame a fresh
       call/spawn produces (see lang.v's RTCallStep/SpawnStep) -- from a
       synthesized entry stack built out of fresh, distinct lvars: given
       names/lvs/vals aligned positionally, LStack (list_to_map (zip names
       lvs)) read through the mp overridden at each lv to the corresponding
       (translated) val equals exactly StackFrame (list_to_map (zip names
       vals)). *)
    Lemma symb_stk_to_stk_frm_general
        (names : list var) (lvs : list lvar) (vals : list lang.val) (mp : symb_map)
        (Hnodup_names : NoDup names) (Hnodup_lvs : NoDup lvs)
        (Hlen1 : length names = length lvs) (Hlen2 : length names = length vals) :
      symb_stk_to_stk_frm (assoc_map names lvs)
        (fun lv => match (assoc_map lvs vals : gmap lvar lang.val) !! lv with
                   | Some v => trnsl_val v | None => mp lv end)
      = StackFrame (assoc_map names vals).
    Proof.
      unfold symb_stk_to_stk_frm. f_equal.
      apply map_eq. intro v.
      rewrite lookup_fmap.
      destruct ((list_to_map (zip names lvs) : gmap var lvar) !! v) as [lv|] eqn:Hstk0.
      - rewrite Hstk0.
        have Hstk0' := Hstk0.
        apply elem_of_list_to_map_2 in Hstk0'.
        apply elem_of_list_lookup_1 in Hstk0' as [i Hi].
        rewrite lookup_zip_with in Hi.
        destruct (names !! i) as [v'|] eqn:Hnv; [| discriminate].
        destruct (lvs !! i) as [lv'|] eqn:Hlvi; [| discriminate].
        simpl in Hi. injection Hi as Heq1 Heq2. subst v'. subst lv'.
        have Hval_i : is_Some (vals !! i).
        { apply lookup_lt_is_Some_2. rewrite <- Hlen2. eapply (lookup_lt_Some names). exact Hnv. }
        destruct Hval_i as [valv Hval_i].
        have Hlv_lookup : (list_to_map (zip lvs vals) : gmap lvar lang.val) !! lv = Some valv.
        { apply elem_of_list_to_map_1.
          - rewrite (fst_zip _ _ (Nat.eq_le_incl _ _ (eq_trans (eq_sym Hlen1) Hlen2))). exact Hnodup_lvs.
          - apply (elem_of_list_lookup_2 _ i). rewrite lookup_zip_with Hlvi Hval_i. done. }
        simpl. rewrite Hlv_lookup. simpl. rewrite trnsl_lval_trnsl_val_inverse.
        symmetry. apply elem_of_list_to_map_1.
        + rewrite (fst_zip _ _ (Nat.eq_le_incl _ _ Hlen2)). exact Hnodup_names.
        + apply (elem_of_list_lookup_2 _ i). rewrite lookup_zip_with Hnv Hval_i. done.
      - rewrite Hstk0. simpl.
        symmetry. apply not_elem_of_list_to_map_1.
        rewrite (fst_zip _ _ (Nat.eq_le_incl _ _ Hlen2)).
        apply not_elem_of_list_to_map_2 in Hstk0.
        rewrite (fst_zip _ _ (Nat.eq_le_incl _ _ Hlen1)) in Hstk0.
        exact Hstk0.
    Qed.

    (* Constructively extracts a list of witness values (with their typing)
       from a "every declared name has some value of the right shape" fact --
       no choice axiom needed since decls is a concrete, finite list. *)
    Lemma extract_present_vals (decls : list (var * typ)) (frm_locals : gmap var lang.val) :
      (∀ v tp, (v, tp) ∈ decls -> ∃ val, frm_locals !! v = Some val ∧ typeOf val = tp) ->
      ∃ vals : list lang.val,
        Forall2 (fun decl val => frm_locals !! (fst decl) = Some val) decls vals ∧
        Forall2 (fun decl val => typeOf val = snd decl) decls vals.
    Proof.
      induction decls as [| [v tp] rest IH]; intros Hpresent.
      - exists []. split; constructor.
      - destruct (Hpresent v tp (elem_of_list_here _ _)) as [val [Hval Hty]].
        have IHpremise : ∀ v' tp', (v', tp') ∈ rest -> ∃ val, frm_locals !! v' = Some val ∧ typeOf val = tp'.
        { intros v' tp' Hin. apply (Hpresent v' tp'). apply elem_of_cons. right. exact Hin. }
        destruct (IH IHpremise) as [vals [HF2 HF2ty]].
        exists (val :: vals). split; constructor; try done.
    Qed.

    (* Combines two Forall2 facts sharing the same left-hand list, pointwise,
       into a single Forall2 relating their right-hand lists. *)
    Lemma Forall2_combine {A B C : Type} (P1 : A -> B -> Prop) (P2 : A -> C -> Prop) (Q : B -> C -> Prop)
        (decls : list A) (xs : list B) (ys : list C) :
      (∀ a b c, P1 a b -> P2 a c -> Q b c) ->
      Forall2 P1 decls xs -> Forall2 P2 decls ys -> Forall2 Q xs ys.
    Proof.
      intros HQ HF1. revert ys. induction HF1 as [| a b decls' xs' Hp1 Hrest IH]; intros ys HF2.
      - apply Forall2_nil_inv_l in HF2. subst ys. constructor.
      - destruct ys as [| c ys']; [exfalso; exact (Forall2_cons_nil_inv _ _ _ HF2) |].
        apply Forall2_cons_1 in HF2 as [Hp2 Hrest2].
        constructor; [exact (HQ a b c Hp1 Hp2) | exact (IH ys' Hrest2)].
    Qed.


  Fixpoint trnsl_expr_lExpr (stk: stack) (e: lang.expr) :=
  match e with
  | Var x => match stk !! x with
             | Some v => Some (LVar v)
             | None => None
             end
  | Val v => Some (LVal (trnsl_val v))
  | UnOp op e => 
      match trnsl_expr_lExpr stk e with
      | Some le => Some (LUnOp op le)
      | None => None
      end
  | BinOp op e1 e2 => 
    match (trnsl_expr_lExpr stk e1), (trnsl_expr_lExpr stk e2) with
    | Some le1, Some le2 => Some (LBinOp op le1 le2)
    | _, _ => None
    end

  | IfE e1 e2 e3 =>
    match (trnsl_expr_lExpr stk e1), (trnsl_expr_lExpr stk e2), (trnsl_expr_lExpr stk e3) with
    | Some le1, Some le2, Some le3 => Some (LIfE le1 le2 le3)
    | _, _, _ => None
    end

  | StuckE => Some LStuck
  end.

  (* Free variables of a translated expression are contained in range(stk) *)
  Lemma trnsl_expr_lExpr_fvars_range (stk : stack) (e : lang.expr) (le : LExpr) :
    trnsl_expr_lExpr stk e = Some le →
    ∀ v, v ∈ lexpr_fvars le → ∃ k, stk !! k = Some v.
  Proof.
    revert le.
    induction e; simpl; intros le Htrnsl lv Hlv.
    - destruct (stk !! x) as [lv'|] eqn:Hstk; [| discriminate].
      injection Htrnsl as <-. simpl in Hlv. apply elem_of_singleton in Hlv. subst lv'. eauto.
    - injection Htrnsl as <-. simpl in Hlv. exfalso. exact (not_elem_of_empty _ Hlv).
    - destruct (trnsl_expr_lExpr stk e) as [le'|] eqn:Hle'; [| discriminate].
      injection Htrnsl as <-. simpl in Hlv. exact (IHe le' eq_refl lv Hlv).
    - destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [| discriminate].
      destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [| discriminate].
      injection Htrnsl as <-. simpl in Hlv.
      apply elem_of_union in Hlv as [Hlv1 | Hlv2].
      + exact (IHe1 le1 eq_refl lv Hlv1).
      + exact (IHe2 le2 eq_refl lv Hlv2).
    - destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [| discriminate].
      destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [| discriminate].
      destruct (trnsl_expr_lExpr stk e3) as [le3|] eqn:Hle3; [| discriminate].
      injection Htrnsl as <-. simpl in Hlv.
      apply elem_of_union in Hlv as [Hlv12 | Hlv3].
      + apply elem_of_union in Hlv12 as [Hlv1 | Hlv2].
        * exact (IHe1 le1 eq_refl lv Hlv1).
        * exact (IHe2 le2 eq_refl lv Hlv2).
      + exact (IHe3 le3 eq_refl lv Hlv3).
    - injection Htrnsl as <-. simpl in Hlv. exfalso. exact (not_elem_of_empty _ Hlv).
  Qed.

  Inductive trnsl_stmt_ret :=
  | None'
  | Error
  | Some' (s: lang.stmt).
  
  Fixpoint trnsl_atomic_block (body : stmt) (step_taken : bool) : trnsl_stmt_ret * bool := 
  match body, step_taken with
  | Seq s1 s2, _ =>
    match trnsl_atomic_block s1 step_taken with
    | (None', step_taken') => trnsl_atomic_block s2 step_taken'
    | (Some' s1, step_taken') => 
      match trnsl_atomic_block s2 step_taken' with
      | (None', step_taken'') => (Some' s1, step_taken'')
      | (Some' s2, step_taken'') => (Some' (lang.Seq s1 s2), step_taken'')
      | (Error, _) => (Error, step_taken')
      end
    | (Error, _) => (Error, step_taken)
    end

  | IfS e s1 s2, _ =>
    match trnsl_atomic_block s1 step_taken, trnsl_atomic_block s2 step_taken with
    | (None', step_taken'), (None', step_taken'') => (None', step_taken' || step_taken'')
    | (None', step_taken'), (Some' s2, step_taken'') => (Some' (lang.IfS e lang.SkipS s2), step_taken' || step_taken'')
    | (Some' s1, step_taken'), (None', step_taken'') => (Some' (lang.IfS e s1 lang.SkipS), step_taken' || step_taken'')
    | (Some' s1, step_taken'), (Some' s2, step_taken'') => (Some' (lang.IfS e s1 s2), step_taken' || step_taken'')
    | (Error, _), _ | _, (Error, _) => (Error, step_taken)
    end

  | Assign v e, false => (Some' (lang.Assign v e), true)
  | Assign v e, true => (Error, true)

  | SkipS, false => (Some' lang.SkipS, true)
  | SkipS, true => (Error, true)

  | StuckS, false => (Some' lang.StuckS, true)
  | StuckS, true => (Error, true)

  | Call v proc args, _ => (Error, true)

  | FldWr v fld e2, false => (Some' (lang.FldWr v fld e2), true)
  | FldWr v fld e2, true => (Error, true)

  | FldRd v e fld, false => (Some' (lang.FldRd v e fld), true)
  | FldRd v e fld, true => (Error, true)

  | CAS v e1 fld e2 e3, false => (Some' (lang.CAS v e1 fld e2 e3), true)
  | CAS v e1 fld e2 e3, true => (Error, true)

  | Alloc v fs, false => (Some' (lang.Alloc v fs), true)
  | Alloc v fs, true => (Error, true)

  | Spawn proc args, false => (Some' (lang.Spawn proc args), true)
  | Spawn proc args, true => (Error, true)
  | InvAccessBlock inv args body, _ => trnsl_atomic_block body step_taken
  | _, _ => (None', step_taken)
  end.

  Fixpoint trnsl_stmt (s : stmt) : trnsl_stmt_ret := match s with
  | Seq s1 s2 => 
    match trnsl_stmt s1, trnsl_stmt s2 with
    | None', None' => None'
    | Some' s1, None' => Some' s1
    | None', Some' s2 => Some' s2
    | Some' s1', Some' s2' => Some' (stmt_append s1' s2' )
    | Error, _
    | _, Error => Error
    end

  | IfS e s1 s2 => 
      match (trnsl_stmt s1), (trnsl_stmt s2) with
      | None', None' => None'
      | Some' s1, None' => Some' (lang.IfS e s1 lang.SkipS)
      | None', Some' s2 => Some' (lang.IfS e lang.SkipS s2 )
      | Some' s1, Some' s2 => Some' (lang.IfS e s1 s2) 
      | Error, _ | _, Error => Error
      end

  | Assign v e => Some' (lang.Assign v e)
  | SkipS => Some' (lang.SkipS)
  | StuckS => Some' lang.StuckS
  | Call v proc args => Some' (lang.Call v proc args)
  | FldWr v fld e2 => Some' (lang.FldWr v fld e2)
  
  | FldRd v e1 fld => Some' (lang.FldRd v e1 fld)
  | CAS v e1 fld e2 e3 => Some' (lang.CAS v e1 fld e2 e3)
  | Alloc v fs => Some' (lang.Alloc v fs)
  | Spawn proc args => Some' (lang.Spawn proc args)
  
  | UnfoldPred pred args => None'
  | FoldPred pred args => None'
  | InvAccessBlock inv args body => (trnsl_atomic_block body false).1

  (* | UnfoldInv inv args => None'
  | FoldInv inv args => None' *)
  | Fpu e fld RAPack old_val new_val => None'
  end.

  Ltac proj_fst H := (apply f_equal with (f := fst) in H).
  Ltac proj_snd H := (apply f_equal with (f := snd) in H).

  (* Monotonicity for Some' *)
  Lemma trnsl_atomic_step_monotone (s : stmt)  :
    (forall stmt1 stmt2 stp1 stp2, 
        trnsl_atomic_block s true = (stmt1, stp1) ->
        trnsl_atomic_block s false = (stmt2, stp2) ->
        not (stmt1 = Error) ->
        stmt1 = stmt2 /\ (stp2 -> stp1)).
  Proof.
    induction s.
    all: intros.

    1: { (* Seq *)
      simpl in H, H0.

      destruct (trnsl_atomic_block s1 true) eqn:E1;
      destruct (trnsl_atomic_block s1 false) eqn:E2.
      specialize (IHs1 t t0 b b0 eq_refl eq_refl).

      destruct t eqn:Ht, t0 eqn:Ht0.
        all:
          try (specialize (IHs1 ltac:(intros Htemp'; discriminate)) as [IHs1stmt IHs1stp]; try done).
        all:
          try (inversion H; subst; contradiction).

      - destruct b, b0.
        ** rewrite H  in H0. inversion H0; subst. done.
        ** specialize (IHs2 stmt1 stmt2 stp1 stp2 H H0 H1) as IHs2Sp. done.
        ** exfalso. apply IHs1stp. done.
        ** rewrite H in H0. inversion H0; subst. done.

      - destruct b, b0; inversion IHs1stmt; subst.
        ** rewrite H in H0. inversion H0. done.
        ** destruct (trnsl_atomic_block s2 true) eqn:Htrnsl_s2;
          destruct (trnsl_atomic_block s2 false) eqn:Htrnsl_s2'.

          specialize (IHs2 t t0 b b0 eq_refl eq_refl).
          
          destruct t eqn:Ht, t0 eqn:Ht0. 
          all: 
            inversion H; inversion H0; subst; 
            try (specialize (IHs2 ltac:(intros Htemp; discriminate)) as [IHs2Stmt IHs2stp]; split; try done); 
            try done.
          
          inversion IHs2Stmt; subst. done.

        ** exfalso. apply IHs1stp; done.
        ** destruct (trnsl_atomic_block s2 false) eqn:Htrnsl_s2.
          destruct (trnsl_atomic_block s2 true) eqn:Htrnsl_s2'.

          specialize (IHs2 t0 t b0 b eq_refl eq_refl).

          destruct t0 eqn:Ht0, t eqn:Ht. 
          all: 
            inversion H; inversion H0; subst; 
            try (specialize (IHs2 ltac:(intros [Htemp Htemp']; discriminate)) as [IHs2Stmt IHs2stp]; split; try done); 
            try done.
    }

    1: { (* IfS *)
      simpl in H, H0.

        destruct (trnsl_atomic_block s1 true) eqn: E1.
        destruct (trnsl_atomic_block s1 false) eqn:E2.

        specialize (IHs1 t t0 b b0 eq_refl eq_refl).

        destruct t eqn:Ht, t0 eqn:Ht0.
        all:
          try (specialize (IHs1 ltac:(intros Htemp'; discriminate)) as [IHs1stmt IHs1stp]; try done).
        
        all:
          (destruct (trnsl_atomic_block s2 true) eqn:F1;
          destruct (trnsl_atomic_block s2 false) eqn:F2;
          specialize (IHs2 t1 t2 b1 b2 eq_refl eq_refl);  
          destruct t1 eqn:Ht1, t2 eqn:Ht2;
          try (specialize (IHs2 ltac:(intros Htemp; discriminate)) as [IHs2stmt IHs2stp]; try done)
          ).

        all:
            (inversion H; inversion H0; subst; split; try done).
        + destruct b0, b; intuition.
        + inversion IHs2stmt; subst; done.
        + destruct b0, b2; intuition.
        + inversion IHs1stmt; subst; done.
        + destruct b0, b2; auto.
        + inversion IHs1stmt; inversion IHs2stmt; subst; done.
        + destruct b0, b2; auto.
    }

    all: simpl in *; inversion H; inversion H0; subst; try done.
    
    apply IHs; done.
  Qed.

  Definition P_some (c : stmt) :=
    forall stmt' step_taken,
      (trnsl_atomic_block c step_taken).1 = Some' stmt' ->
      trnsl_stmt c = Some' stmt'.

  Definition P_none (c : stmt) :=
    forall step_taken,
      (trnsl_atomic_block c step_taken).1 = None' ->
      trnsl_stmt c = None'.

  Lemma trnsl_stmt_trnsl_atomic_block_some_none_mutual :
    forall c, (P_some c /\ P_none c).
  Proof.
    apply (stmt_ind (fun c => P_some c /\ P_none c)).
    all: intros; simpl in *.

    Ltac solve_split_case :=
      split;
      [ (* P_some *)
        intros stmt' step_taken H;
        simpl in H;
        destruct step_taken; try discriminate H; rewrite <- H; try done
      | (* P_none *)
        intros step_taken H;
        simpl in H;
        destruct step_taken; try discriminate H; try done
      ].

    (* All atomic steps *)
    all: try (solve_split_case).
        
    1: { (* Seq*)
      destruct H as [IHsome1 IHnone1].
      destruct H0 as [IHsome2 IHnone2].
      split.
      + (* --- P_some --- *)
        intros stmt' step_taken H.
        simpl in H.
        destruct (trnsl_atomic_block s1 step_taken) as [[| | ] step1] eqn:H1;
        simpl in H.
        ++ (* case (None', step1) *)
          unfold P_none in IHnone1. 
          proj_fst H1.
          specialize (IHnone1 step_taken H1) as Hs1.
          simpl. 
          rewrite Hs1.
          unfold P_some in IHsome2. apply IHsome2 in H. rewrite H. done.

        ++ discriminate H.
        
        ++ (* case (Some' s1', step1) *)
          unfold P_some in IHsome1.
          proj_fst H1.
          specialize (IHsome1 s step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_some in IHsome2. 
          destruct (trnsl_atomic_block s2 step1) as [[| | ] step2] eqn:H2.
          ** proj_fst H2. 
            specialize (IHnone2 step1 H2) as Hs2. rewrite Hs2. done.

          ** discriminate H.

          **  proj_fst H2. specialize (IHsome2 s0 step1 H2) as Hs2. rewrite Hs2.
          simpl in H. rewrite H. done.

      + (* --- P_none --- *)
        intros step_taken H.
        simpl in H.
        destruct (trnsl_atomic_block s1 step_taken) as [[| | ] step1] eqn:H1;
        simpl in H.
        ++ (* case (None', step1) *)
          unfold P_none in IHnone1.
          proj_fst H1.
          specialize (IHnone1 step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_none in IHnone2.
          apply IHnone2 in H. rewrite H. done.

        ++ (* case (Error, step1) *)
          discriminate H.

        ++ (* case (Some' s1', step1) *)
          unfold P_some in IHsome1.
          proj_fst H1.
          specialize (IHsome1 s step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          destruct (trnsl_atomic_block s2 step1) as [[| | ] step2] eqn:H2;
          simpl in H.
          ** (* (None', step2) *)
              unfold P_none in IHnone2.
              proj_fst H2.
              specialize (IHnone2 step1 H2) as Hs2.
              rewrite Hs2. done.
          ** discriminate H.
          ** discriminate H.
    }
      
    1: { (* IfS *)
      destruct H as [IHsome1 IHnone1].
      destruct H0 as [IHsome2 IHnone2].
      split.

      + (* --- P_some --- *)
        intros stmt' step_taken H.
        simpl in H.
        destruct (trnsl_atomic_block s1 step_taken) as [[| | ] step1] eqn:H1;
        destruct (trnsl_atomic_block s2 step_taken) as [[| | ] step2] eqn:H2;
        simpl in H.

        ++ (* case: s1 = None', s2 = None' *)
          unfold P_none in IHnone1. proj_fst H1. specialize (IHnone1 step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_none in IHnone2. proj_fst H2. specialize (IHnone2 step_taken H2) as Hs2.
          rewrite Hs2. simpl.
          rewrite H. reflexivity.

        ++ (* case: s1 = None', s2 = Error *) 
          discriminate H.
        
        ++ (* case: s1 = None', s2 = Some' s2' *)
          unfold P_none in IHnone1. proj_fst H1. specialize (IHnone1 step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_some in IHsome2. proj_fst H2. specialize (IHsome2 s step_taken H2) as Hs2.
          rewrite Hs2. simpl. rewrite H. reflexivity.

        ++ (* case: s1 = Error, s2 = None' *)
          discriminate H.

        ++ (* case: s1 = Error, s2 = Error *)
          discriminate H.
        
        ++ (* case: s1 = Error, s2 = Some' s *)
          discriminate H.

        ++ (* case: s1 = Some' s1', s2 = None' *)
          unfold P_some in IHsome1. proj_fst H1. specialize (IHsome1 s step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_none in IHnone2. proj_fst H2. specialize (IHnone2 step_taken H2) as Hs2.
          rewrite Hs2. simpl. rewrite H. reflexivity.

        ++ (* case: s1 = Some' s1', s2 = Error *)
          discriminate H.

        ++ (* case: s1 = Some' s, s2 = Some' s0 *)
          unfold P_some in IHsome1. proj_fst H1. specialize (IHsome1 s step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_some in IHsome2. proj_fst H2. specialize (IHsome2 s0 step_taken H2) as Hs2.
          rewrite Hs2. simpl. rewrite H. reflexivity.

      + (* --- P_none --- *)
        intros step_taken H.
        simpl in H.
        destruct (trnsl_atomic_block s1 step_taken) as [[| | ] step1] eqn:H1;
        destruct (trnsl_atomic_block s2 step_taken) as [[| | ] step2] eqn:H2;
        simpl in H; try discriminate H. simpl.
        unfold P_none in IHnone1. unfold P_none in IHnone2.
        proj_fst H1. proj_fst H2.

        specialize (IHnone1 step_taken H1).
        specialize (IHnone2 step_taken H2).
        rewrite IHnone1. rewrite IHnone2. done.
    }

    1: { (* InvAccessBlock *)
      split.
      + (* P_some *)
        intros stmt' step_taken H1.
        simpl.
        simpl in H1.
        destruct step_taken; try discriminate H.
        * rewrite <- H1. simpl.
          destruct (trnsl_atomic_block body true) eqn:Hb1.
          destruct (trnsl_atomic_block body false) eqn:Hb2.
          simpl in H1.

          pose proof (trnsl_atomic_step_monotone body t t0 b b0 Hb1 Hb2) as HMono.
          specialize (HMono ltac:(intros Htemp; rewrite H1 in Htemp; discriminate)) as [Hbody _]. simpl. done.
        * rewrite <- H1. simpl. done.

      + (* P_none *) 
        intros step_taken H1.
        simpl in H1.
        simpl.
        destruct H as [HIndSome HIndNone].
        unfold P_none in HIndNone.
        destruct step_taken; rewrite <- H1; simpl; try done.
        * 
          destruct (trnsl_atomic_block body true) eqn:Hb1.
          destruct (trnsl_atomic_block body false) eqn:Hb2.
          simpl in H1.

          pose proof (trnsl_atomic_step_monotone body t t0 b b0 Hb1 Hb2) as HMono.
          specialize (HMono ltac:(intros Htemp; rewrite H1 in Htemp; discriminate)) as [Hbody _]. simpl. done.
    }
  Qed.

  Lemma trnsl_stmt_trnsl_atomic_block_some c stmt :
    (trnsl_atomic_block c false).1 = Some' stmt -> trnsl_stmt c = Some' stmt.
  Proof.
    pose proof (trnsl_stmt_trnsl_atomic_block_some_none_mutual c) as [Hsome _].
    unfold P_some in Hsome.
    specialize (Hsome stmt false). done.
  Qed.

  Lemma trnsl_stmt_trnsl_atomic_block_none c :
    (trnsl_atomic_block c false).1 = None' -> trnsl_stmt c = None'.
  Proof.
    pose proof (trnsl_stmt_trnsl_atomic_block_some_none_mutual c) as [_ Hnone].
    unfold P_none in Hnone.
    specialize (Hnone false). done.
  Qed.

  Lemma trnsl_atomic_block_true_conserved stmt:
    (trnsl_atomic_block stmt true).2 = true.
  Proof.
    induction stmt. 

    all: simpl in *; try done.
    - simpl. destruct (trnsl_atomic_block stmt1 true) eqn:Hstmt1.
      destruct t; try done.
      + simpl in *. subst. done.
      + simpl in *; subst.
        destruct (trnsl_atomic_block stmt2 true) eqn:Hstmt2.
        simpl in *; subst.
        destruct t; simpl; done.
    
    - simpl in *. destruct (trnsl_atomic_block stmt1 true) eqn:Hstmt1.
      destruct t; try done.
      + simpl in *; subst.
        destruct (trnsl_atomic_block stmt2 true) eqn:Hstmt2.
        simpl in *; subst. destruct t; done.
      
      + simpl in *; subst.
        destruct (trnsl_atomic_block stmt2 true) eqn:Hstmt2.
        simpl in *; subst. destruct t; done.

  Qed.

  Lemma trnsl_atomic_block_true_conserved' stmt t b:
    trnsl_atomic_block stmt true = (t, b) -> b = true.
  Proof.
    intros.
    proj_snd H.
    pose proof (trnsl_atomic_block_true_conserved stmt). rewrite H in H0. simpl in *. done.
  Qed.

  Lemma trnsl_atomic_block_non_constant_step b stmt output:
    trnsl_atomic_block stmt b = (output, b) -> (output = None' \/ output = Error).
  Proof.
    revert b output.
    induction stmt; intros.

    all: 
      try (simpl in *;
      destruct b; inversion H; [subst; right; done]).
    - simpl in *.
      destruct (trnsl_atomic_block stmt1 b) eqn:Hstmt1.
      destruct (trnsl_atomic_block stmt2 b) eqn:Hstmt2.
      destruct b0.
      + destruct t.
        ++ pose proof (trnsl_atomic_block_true_conserved stmt2).
          destruct b.
          * specialize (IHstmt2 true output H). done.
          * proj_snd H. rewrite H in H0. discriminate.

        ++ right. proj_fst H. simpl in *. subst. done.

        ++ destruct (trnsl_atomic_block stmt2 true) eqn:Hstmt2'.
          pose proof (trnsl_atomic_block_true_conserved stmt2).
          destruct b0; destruct b.
          * specialize (IHstmt1 true (Some' s) Hstmt1). destruct IHstmt1; discriminate.
          * destruct t; discriminate.
          * proj_snd Hstmt2'. rewrite Hstmt2' in H0. discriminate.
          * proj_snd Hstmt2'. rewrite Hstmt2' in H0. discriminate.
      + destruct t.
        ++ destruct b.
          * pose proof (trnsl_atomic_block_true_conserved' stmt1 None' false Hstmt1); discriminate.
          * specialize (IHstmt2 false output H). done.

        ++ inversion H; subst. right; done.

        ++ destruct b.
          * pose proof (trnsl_atomic_block_true_conserved' stmt1 (Some' s) false Hstmt1); discriminate.
          * specialize (IHstmt1 false (Some' s) Hstmt1). destruct IHstmt1; discriminate.

    - destruct (trnsl_atomic_block stmt1 b) eqn:Hstmt1.
      destruct (trnsl_atomic_block stmt2 b) eqn:Hstmt2.
      destruct b.
      + simpl in H. rewrite Hstmt1 Hstmt2 in H.
        pose proof (trnsl_atomic_block_true_conserved' stmt1 t b0 Hstmt1); subst.
        pose proof (trnsl_atomic_block_true_conserved' stmt2 t0 b1 Hstmt2); subst.
        specialize (IHstmt1 true t Hstmt1). specialize (IHstmt2 true t0 Hstmt2).
        destruct IHstmt1, IHstmt2; subst; inversion H; subst; try (left; done); try (right; done).
      
      + destruct b0, b1.
        ++ simpl in H; rewrite Hstmt1 Hstmt2 in H.
          destruct t, t0; try discriminate; inversion H; subst.
          all: try (left; done); try (right; done).

        ++ simpl in H; rewrite Hstmt1 Hstmt2 in H.
          destruct t, t0; try discriminate; inversion H; subst.
          all: try (left; done); try (right; done).

        ++ simpl in H; rewrite Hstmt1 Hstmt2 in H.
          destruct t, t0; try discriminate; inversion H; subst.
          all: try (left; done); try (right; done).
        
        ++ simpl in H; rewrite Hstmt1 Hstmt2 in H.
          destruct t, t0; try discriminate; inversion H; subst.
          all: try (left; done); try (right; done).
          * specialize (IHstmt2 false (Some' s) Hstmt2). destruct IHstmt2; discriminate.
          * specialize (IHstmt1 false (Some' s) Hstmt1). destruct IHstmt1; discriminate.
          * specialize (IHstmt1 false (Some' s) Hstmt1). destruct IHstmt1; discriminate.

    - simpl in *.
      destruct b; inversion H; left; done.

    -  simpl in *.
      destruct b; inversion H; left; done.

    - simpl in *. apply (IHstmt b). apply H.

    - simpl in *.
      destruct b; inversion H; left; done.
  Qed.

  Lemma trnsl_atomic_block_atomicity stmt s stk_id:
    (trnsl_atomic_block stmt false).1 = Some' s -> Atomic WeaklyAtomic (to_rtstmt stk_id s).
  Proof.
    revert s.
    induction stmt.
    1: {
      intros. simpl in *.
      destruct (trnsl_atomic_block stmt1 false) eqn:Hstmt1.
      destruct (trnsl_atomic_block stmt2 b) eqn:Hstmt2.
      destruct b.
      - pose proof (trnsl_atomic_block_true_conserved' stmt2 t0 b0 Hstmt2); subst.
        pose proof (trnsl_atomic_block_non_constant_step true stmt2 t0 Hstmt2).
        destruct H0; subst.
        + destruct t; try discriminate. simpl in *. apply IHstmt1. apply H.
        + destruct t; discriminate.

      - pose proof (trnsl_atomic_block_non_constant_step false stmt1 t Hstmt1).
        destruct H0; subst.
        + simpl in *; subst. proj_fst Hstmt2. apply IHstmt2. apply Hstmt2.
        + simpl in *; discriminate.
     }

    1: {
      intros. simpl in *. 
      destruct (trnsl_atomic_block stmt1 false) eqn:Hstmt1;
      destruct (trnsl_atomic_block stmt2 false) eqn:Hstmt2.

      destruct t eqn:Ht, t0 eqn:Ht0; simpl in *; try discriminate.
      - inversion H; subst. simpl in *.
        specialize (IHstmt2 s0 eq_refl).
        unfold Atomic. intros.
        inversion H0; simpl in *.
        pose proof (fill_if_empty K e1' _ _ _ _ H1) as HK; subst. simpl in *. symmetry in H1. subst.
        inversion H3; subst.
        + destruct H13 as [e1' [e2'0 [K [Hs1 [Hs2 Hrtm]]]]].
          pose proof (fill_atomic_empty K e1' (RTSkipS stk_id) ltac:(simpl; done) Hs1); subst. simpl in *. symmetry in Hs1; subst.
          inversion Hrtm; subst. apply val_irreducible. done.

        + unfold Atomic in IHstmt2.
          specialize (IHstmt2 σ e2' [] σ' efs).
          destruct H13 as [e1' [e2'0 [K [Hs1 [Hs2 Hrtm]]]]].
          assert (prim_step (to_rtstmt stk_id s0) σ [] e2' σ' efs).
          { apply (Ectx_step K e1' e2'0); try done.  }
          specialize (IHstmt2 H1). done.

        + destruct b1 eqn:Hb1, (to_rtstmt stk_id s0) eqn:Hs0; try (exfalso; done).
          apply val_irreducible; done.

      - inversion H; subst. simpl in *.
        specialize (IHstmt1 s0 eq_refl).
        unfold Atomic. intros.
        inversion H0; simpl in *.
        pose proof (fill_if_empty K e1' _ _ _ _ H1) as HK; subst. simpl in *. symmetry in H1; subst.
        inversion H3; subst.
        + unfold Atomic in IHstmt1.
          specialize (IHstmt1 σ e2' [] σ' efs).
          destruct H13 as [e1' [e2'0 [K [Hs1 [Hs2 Hrtm]]]]].
          assert (prim_step (to_rtstmt stk_id s0) σ [] e2' σ' efs).
          { apply (Ectx_step K e1' e2'0); try done.  }
          specialize (IHstmt1 H1). done.

        + destruct H13 as [e1' [e2'0 [K [Hs1 [Hs2 Hrtm]]]]].
          pose proof (fill_atomic_empty K e1' (RTSkipS stk_id) ltac:(simpl; done) Hs1); subst. simpl in *. symmetry in Hs1; subst.
          inversion Hrtm; subst. apply val_irreducible. done.

        + destruct b1 eqn:Hb1, (to_rtstmt stk_id s0) eqn:Hs0; try (exfalso; done).
          apply val_irreducible; done.

      - inversion H; subst. simpl in *.
        specialize (IHstmt1 s0 eq_refl).
        specialize (IHstmt2 s1 eq_refl).
        unfold Atomic. intros.
        inversion H0; simpl in *.
        pose proof (fill_if_empty K e1' _ _ _ _ H1) as HK; subst. simpl in *. symmetry in H1; subst.
        inversion H3; subst.
        + unfold Atomic in IHstmt1.
          specialize (IHstmt1 σ e2' [] σ' efs).
          destruct H13 as [e1' [e2'0 [K [Hs1 [Hs2 Hrtm]]]]].
          assert (prim_step (to_rtstmt stk_id s0) σ [] e2' σ' efs).
          { apply (Ectx_step K e1' e2'0); try done.  }
          specialize (IHstmt1 H1). done.
          
        + unfold Atomic in IHstmt2.
          specialize (IHstmt2 σ e2' [] σ' efs).
          destruct H13 as [e1' [e2'0 [K [Hs1 [Hs2 Hrtm]]]]].
          assert (prim_step (to_rtstmt stk_id s1) σ [] e2' σ' efs).
          { apply (Ectx_step K e1' e2'0); try done.  }
          specialize (IHstmt2 H1). done.

        + destruct b1 eqn:Hb1.
          * destruct (to_rtstmt stk_id s0) eqn:Hs0; try (exfalso; done).
            apply val_irreducible; done.
            
          * destruct (to_rtstmt stk_id s1) eqn:Hs1; try (exfalso; done).
            apply val_irreducible; done.

    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_assign.
    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_skip.
    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_stuck.
    }

    1: { 
      intros. simpl in *. inversion H; subst.
    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_fld_wr.
    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_fld_rd.
    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_cas.
    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_alloc.
    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_spawn.
    }

    1: { 
      intros. simpl in *. inversion H; subst.
    }

    1: { 
      intros. simpl in *. inversion H; subst.
    }

    1: { 
      intros. simpl in *. apply IHstmt. apply H.
    }

    1: { 
      intros. simpl in *. inversion H; subst.
    }
  Qed.

  Definition transport {A B : Type} (H : A = B) (x : A) : B :=
    eq_rect A id x _ H.

  Lemma transport_sym : forall (A B : Type) (H : A = B) (x : B),
     (transport H (transport (eq_sym H) x)) = x.
  Proof.
    intros. unfold transport. destruct H. simpl. reflexivity.
  Qed.

  Lemma transport_cancel : forall (A B : Type) (H : A = B) (x : A),
    transport (eq_sym H) (transport H x) = x.
  Proof.
    intros. unfold transport. destruct H. simpl. reflexivity.
  Qed.

  Lemma eq_rect_transport_comp : forall (R: RA_Pack) (U : Type) (Heq_car : (RA_carrier R) = U) (x : (RA_carrier R)) (c : U),
  eq_rect (RA_carrier R) (λ T : Type, T → T → T) (RA_inst R).(comp) U Heq_car (transport Heq_car x) c = 
  transport Heq_car ((RA_inst R).(comp) x (transport (eq_sym Heq_car) c)).
Proof.
  intros. unfold transport. destruct Heq_car. simpl. reflexivity.
Qed.


  Lemma eq_rect_transport_valid : forall (R: RA_Pack) (U: Type) (Heq_car : (RA_carrier R) = U) (x : (RA_carrier R)),
    eq_rect (RA_carrier R) (λ T : Type, T -> Prop) (RA_inst R).(valid) U Heq_car (transport Heq_car x) ->
    (RA_inst R).(valid) x.
  Proof.
    intros. unfold transport in *. destruct Heq_car. simpl in *. done.
  Qed.

  Lemma eq_rect_transport_valid_inv : forall (R: RA_Pack) (U: Type) (Heq_car : (RA_carrier R) = U) (x : (RA_carrier R)),
    (RA_inst R).(valid) x ->
    eq_rect (RA_carrier R) (λ T : Type, T -> Prop) (RA_inst R).(valid) U Heq_car (transport Heq_car x).
    
  Proof.
    intros. unfold transport in *. destruct Heq_car. simpl in *. done.
  Qed.

  Lemma eq_rect_transport_inv_comp_valid : forall (R: RA_Pack) (U: Type) (Heq_car : (RA_carrier R) = U) (y : (RA_carrier R)) (c: U),
    (RA_inst R).(valid) ((RA_inst R).(comp) y (transport (eq_sym Heq_car) c)) ->
    eq_rect (RA_carrier R) (λ T : Type, T → Prop) (RA_inst R).(valid) U Heq_car (transport Heq_car ((RA_inst R).(comp) y (transport (eq_sym Heq_car) c))).
  Proof.
    intros. unfold transport in *. destruct Heq_car. simpl in *. done.
  Qed.

  Definition Γ_type := forall R : RA_Pack,
  { i : I & { U : ucmra |
      CmraDiscrete U /\
      { Heq_car : RA_carrier R = ucmra_car U | 
          ucmra_cmraR U = Gs i /\ 
          ucmra_op U = eq_rect (RA_carrier R) (fun T => T -> T -> T) ((RA_inst R).(comp)) (ucmra_car U) Heq_car /\
          ucmra_valid U = eq_rect (RA_carrier R) (fun T => T -> Prop) ((RA_inst R).(valid)) (ucmra_car U) Heq_car
      }
  } } .

  Lemma RAPack_fpuValid (Γ: Γ_type) :
    forall R : RA_Pack,
      forall x y : RA_carrier R,
        (* let '(existT i (existT U (exist _ Hdis Heq_car (conj Hind (conj Hcomp Hvalid))))) := Γ R in *)
        let '(existT i (exist _ U (conj Hdis (exist _ Heq_car (conj Hcmra (conj Hop Hvalid)))))) := Γ R in
        (RA_inst R).(fpuValid) x y -> (transport Heq_car x) ~~> (transport Heq_car y).
  Proof.
    intros R x y.
    destruct (Γ R) as [i [U [Hdisc [Heq_car [Hindx [Hcomp Hval]]]]]].
    intros Hfpu.
    
    intros n c Hvalid.
    destruct c as [c|].

    - simpl in *. 

    (* make the dot-notation explicit so we can rewrite the op *)
    change (transport Heq_car x ⋅ c) with (ucmra_op U (transport Heq_car x) c) in Hvalid.
    rewrite Hcomp in Hvalid.
    (* bring the context back to the R-side by destructing the equality *)
    apply cmra_discrete_valid_iff.
    apply cmra_discrete_valid_iff in Hvalid.
    change (✓ (transport Heq_car y ⋅ c)) with (ucmra_valid U (transport Heq_car y ⋅ c)).
    rewrite Hval.
    unfold transport.

    set (cR := transport (eq_sym Heq_car) c).
    assert ((RA_inst R).(valid) ((RA_inst R).(comp) y cR)). {
      apply (fpuAxiom x y); [done | ].

      rewrite eq_rect_transport_comp in Hvalid.
      unfold cR.
      change (✓ transport Heq_car (comp x (transport (eq_sym Heq_car) c))) with ((ucmra_valid U) (transport Heq_car ((RA_inst R).(comp) x (transport (eq_sym Heq_car) c)))) in Hvalid.
      
      rewrite Hval in Hvalid.
      apply (eq_rect_transport_valid R (ucmra_car U) Heq_car). done.
    }

    subst cR.

    change (eq_rect (RA_carrier R) (λ T : Type, T → Prop) (RA_inst R).(valid) U Heq_car ((ucmra_op U) (eq_rect (RA_carrier R) id y U Heq_car) c)).

    rewrite Hcomp.
    rewrite eq_rect_transport_comp.

    apply eq_rect_transport_inv_comp_valid.
    done.

    - simpl in *. apply cmra_discrete_valid_iff. apply cmra_discrete_valid_iff in Hvalid.

    apply (fpuAxiom x y) in Hfpu.
    destruct Hfpu as [_ [HvVal _]].
    change (@cmra.valid (cmra_car (ucmra_cmraR U)) (cmra_valid (ucmra_cmraR U))) with (ucmra_valid U).
    rewrite Hval.
    apply eq_rect_transport_valid_inv. done.
  Qed.


  Global Parameter Γ : Γ_type.

  Fixpoint trnsl_assertion_str (F : assertion -d> stack_id -d> symb_map -d> (iPropO Σ)) 
    (a: assertion) (stk_id: stack_id) (mp: symb_map) : 
     (iPropO Σ) :=      
      match a with
    | LProc p p_e => 
      match p_e with
        Proc args locals pre post body => 
          match trnsl_stmt body with
          | None' =>
            (proc_tbl_chunk p (
              lang.Proc p args locals lang.SkipS
            ))
          | Some' stmt =>
            (proc_tbl_chunk p (
              lang.Proc p args locals stmt
            ))
          | Error => 
            (False)%I
          end
      end
    | LStack σ => (stack_frame_own stk_id (symb_stk_to_stk_frm σ mp))
    | LExprA l_expr => 
      (⌜LExpr_holds l_expr mp⌝%I)
    
    | LPure p => (⌜ p ⌝%I)
    | LOwn l_expr fld chunk => 
      (∃ l: lang.loc, (
        ⌜LExpr_holds (LBinOp EqOp l_expr (LVal (LitLoc l))) mp⌝ ∗ 
        (l#fld ↦{ 1 } (trnsl_lval chunk))
        )%I)%I

    | LGhostOwn l_expr fld RAPack chunk => 
      let '(existT i (exist _ U (conj Hdis (exist _ Heq_car (conj Heq_cmra (conj Hop Hvalid)))))) := Γ RAPack in
      let chunkU := transport (Heq_car) chunk in
      let chunkGs := transport (f_equal cmra_car Heq_cmra) chunkU in 
      let HinG := inGs_inG i in

      (∃ l : lang.loc, (⌜LExpr_holds (LBinOp EqOp l_expr (LVal (LitLoc l))) mp⌝ ∗ (own (ghost_map l fld) chunkGs (inG0 := HinG)))%I)%I
    | LForall v body => 
       (∀ v':lang.val, (trnsl_assertion_str F body stk_id mp))%I

    | LExists v body => 
      (∃ v': val,
           (trnsl_assertion_str F body stk_id (λ x, if String.eqb x v then v' else mp x))
    )%I
    
    | LImpl cnd body => 
      (⌜LExpr_holds cnd mp⌝ -∗  (trnsl_assertion_str F body stk_id mp))%I

    | LInv inv' args => 
        match inv_map !! inv' with
        | Some inv_record => 
          let subst_map := list_to_map (zip inv_record.(inv_args) args) in

          (inv (inv_namespace_map inv') (F (subst inv_record.(inv_body) subst_map) stk_id mp))
        | None => True%I
        end

    | LPred pred args => 
        match pred_map !! pred with 
        | Some pred_record =>
          let subst_map := list_to_map (zip pred_record.(pred_args) args) in

          (▷ (F (subst pred_record.(pred_body) subst_map) stk_id mp))%I
        | None => True%I
        end

    | LAnd a1 a2 => 
      ( ((trnsl_assertion_str F a1 stk_id mp) ∗ (trnsl_assertion_str F a2 stk_id mp)))%I
    end.

  Definition trnsl_assertion_pre (F : assertion -d> stack_id -d> symb_map -d> (iPropO Σ)) :
     assertion -d> stack_id -d> symb_map -d> (iPropO Σ) := λ a stk_id mp, trnsl_assertion_str F a stk_id mp.

(* --- main contractiveness instance --- *)
Global Instance trnsl_assertion_pre_contractive : Contractive trnsl_assertion_pre.
Proof.
  intros n F G HFG a stk_id mp.
  unfold trnsl_assertion_pre.
  revert mp.
  induction a; simpl; try solve [reflexivity | repeat f_equiv; auto].
  -  (* LForall case *)
    intros mp. do 1 f_equiv. intros v'. apply IHa.
  - (* LExists case *)
    intros mp. do 1 f_equiv. intros v'. apply IHa.
  - (* LImpl case *)
    intros mp. f_equiv. apply IHa.
  - (* LInv case *)
    intros mp. 
    destruct (inv_map !! inv_name0); try reflexivity.
    apply inv_contractive.
    constructor.
    intros m Hlt.
    apply (dist_later_lt _ _ _ HFG _ Hlt).
  -  (* LPred case *)
    intros mp. 
    destruct (pred_map !! pred_name0); try reflexivity.
    (* Don't do f_equiv yet, work with the later directly *)
    apply later_contractive.
    constructor.
    intros m Hlt.
    apply (dist_later_lt _ _ _ HFG _ Hlt).
  - intros mp. f_equiv. { apply IHa1. } {apply IHa2. }
Qed.

Definition trnsl_assertion' := fixpoint trnsl_assertion_pre. 

Lemma trnsl_assertion_unfold a stk mp :
  trnsl_assertion' a stk mp ≡ trnsl_assertion_pre trnsl_assertion' a stk mp.
Proof. apply (fixpoint_unfold trnsl_assertion_pre a stk mp). Qed.

Lemma trnsl_inv_validity' inv' args stk mp :
  match inv_map !! inv' with
  | Some inv_rec =>
      let subst_map := list_to_map (zip inv_rec.(inv_args) args) in
      inv (inv_namespace_map inv')
          (trnsl_assertion' (subst inv_rec.(inv_body) subst_map) stk mp)
      ⊣⊢ trnsl_assertion' (LInv inv' args) stk mp
  | None => true
  end.
  Proof.
    destruct (inv_map !! inv') eqn:HInv; try done.
    simpl.
    setoid_rewrite trnsl_assertion_unfold.
  simpl. rewrite HInv. setoid_rewrite <- trnsl_assertion_unfold. done.
Qed.


Lemma trnsl_pred_validity' pred args stk_id mp :
  match pred_map !! pred with
  | Some pred_rec => 
    let subst_map := list_to_map (zip pred_rec.(pred_args) args) in

    (▷ (trnsl_assertion' (subst pred_rec.(pred_body) subst_map) stk_id mp))%I ≡ trnsl_assertion' (LPred pred args) stk_id mp
  | None => true
  end
.
Proof.
  destruct (pred_map !! pred) eqn:HPred; try done.
  simpl.
  setoid_rewrite trnsl_assertion_unfold.
  simpl. rewrite HPred. setoid_rewrite <- trnsl_assertion_unfold. done.
Qed.  

Definition trnsl_assertion := trnsl_assertion'.


  Definition entails P Q := forall stk_id mp, ∃ P' Q', trnsl_assertion P stk_id mp = P' /\ trnsl_assertion Q stk_id mp = Q' /\ (P' ⊢  Q')%I.

End Translation.

Definition fresh_lvar (stk: stack) v := forall v', not (stk !! v' = Some v).

(* A fresh lvar is not in lexpr_fvars of any translated expression *)
Lemma trnsl_expr_lExpr_fresh_lvar (stk : stack) (e : lang.expr) (le : LExpr) (lv : lvar) :
  trnsl_expr_lExpr stk e = Some le →
  fresh_lvar stk lv →
  lv ∉ lexpr_fvars le.
Proof.
  intros Htrnsl Hfresh Hv.
  destruct (trnsl_expr_lExpr_fvars_range stk e le Htrnsl lv Hv) as [k Hk].
  exact (Hfresh k Hk).
Qed.

Section TypeInf.
    Definition stk_type_compat (ρ : pvar_typs) (σ : lvar_typs) (stk : stack) := forall v lv, (stk !! v = Some lv) -> ρ v = σ lv.

  (* typeOf and inf_expr are now defined globally above, before expr_well_defined. *)

  Fixpoint inf_lexpr (σ: lvar_typs) (le: LExpr) : option typ := 
  match le with
  | LVar x => Some (σ x)
  | LVal v => Some (typeOf (trnsl_lval v))
  | LUnOp NotBoolOp e =>
    match inf_lexpr σ e with
    | Some TpBool => Some TpBool
    | _ => None
    end
  | LUnOp NegOp e =>
    match inf_lexpr σ e with
    | Some TpInt => Some TpInt
    | _ => None
    end

  | LBinOp (AddOp | SubOp | MulOp | DivOp | ModOp) e1 e2 =>
    match inf_lexpr σ e1, inf_lexpr σ e2 with
    | Some TpInt, Some TpInt => Some TpInt
    | _, _ => None
    end

  | LBinOp (LtOp | GtOp | LeOp | GeOp) e1 e2 =>
    match inf_lexpr σ e1, inf_lexpr σ e2 with
    | Some TpInt, Some TpInt => Some TpBool
    | _, _ => None
    end

  | LBinOp (AndOp | OrOp) e1 e2 =>
    match inf_lexpr σ e1, inf_lexpr σ e2 with
    | Some TpBool, Some TpBool => Some TpBool
    | _, _ => None
    end

  | LBinOp (EqOp | NeOp) e1 e2 =>
    match inf_lexpr σ e1, inf_lexpr σ e2 with
    | Some tp1, Some tp2 => if typ_beq tp1 tp2 then Some TpBool else None
    | _, _ => None
    end

  | LIfE e1 e2 e3 =>
    match inf_lexpr σ e1, inf_lexpr σ e2, inf_lexpr σ e3 with
    | Some TpBool, Some tp2, Some tp3 => if typ_beq tp2 tp3 then Some tp2 else None
    | _, _, _ => None
    end

  | _ => None
  end.


  Definition env_typ_well_defined (σ : lvar_typs) (mp : symb_map) :=
      forall lv, 
      match (σ lv), (mp lv) with
      | TpBool, LitBool b => True
      | TpInt, LitInt i => True
      | TpLoc, LitLoc l => True
      | TpUnit, LitUnit => True
      | _, _ => False
      end.


  Lemma lexpr_expr_typ_compat ρ σ stk e le tp :
    stk_type_compat ρ σ stk ->
    trnsl_expr_lExpr stk e = Some le ->
    inf_expr ρ e = Some tp ->
    inf_lexpr σ le = Some tp.
  Proof.
    intros Hstk H2 H3. revert le tp H2 H3.
    induction e; intros le tp H2 H3; simpl in *.
    - (* Var x *)
      destruct (stk !! x) as [lv|] eqn:Hstk_x; [|discriminate H2].
      injection H2 as <-. injection H3 as <-.
      simpl. apply Hstk in Hstk_x. rewrite <- Hstk_x. reflexivity.
    - (* Val v *)
      injection H2 as <-. injection H3 as <-.
      simpl. rewrite trnsl_lval_trnsl_val_inverse. reflexivity.
    - (* UnOp op e *)
      destruct (trnsl_expr_lExpr stk e) as [le'|] eqn:Hle'; [|discriminate H2].
      injection H2 as <-. simpl.
      destruct op; simpl in H3;
        [ destruct (inf_expr ρ e) as [[]|] eqn:Htp_e; try discriminate H3;
          injection H3 as <-; rewrite (IHe le' TpBool eq_refl eq_refl); reflexivity
        | destruct (inf_expr ρ e) as [[]|] eqn:Htp_e; try discriminate H3;
          injection H3 as <-; rewrite (IHe le' TpInt eq_refl eq_refl); reflexivity ].
    - (* BinOp op e1 e2 *)
      destruct (trnsl_expr_lExpr stk e1) as [le1'|] eqn:Hle1'; [|discriminate H2].
      destruct (trnsl_expr_lExpr stk e2) as [le2'|] eqn:Hle2'; [|discriminate H2].
      injection H2 as <-. simpl.
      destruct op; simpl in H3;
        try (destruct (inf_expr ρ e1) as [[]|] eqn:Htp1; try discriminate H3;
             destruct (inf_expr ρ e2) as [[]|] eqn:Htp2; try discriminate H3;
             injection H3 as <-;
             rewrite (IHe1 le1' TpInt eq_refl eq_refl);
             rewrite (IHe2 le2' TpInt eq_refl eq_refl); reflexivity);
        try (destruct (inf_expr ρ e1) as [[]|] eqn:Htp1; try discriminate H3;
             destruct (inf_expr ρ e2) as [[]|] eqn:Htp2; try discriminate H3;
             injection H3 as <-;
             rewrite (IHe1 le1' TpBool eq_refl eq_refl);
             rewrite (IHe2 le2' TpBool eq_refl eq_refl); reflexivity);
        try (destruct (inf_expr ρ e1) as [tp1|] eqn:Htp1; try discriminate H3;
             destruct (inf_expr ρ e2) as [tp2|] eqn:Htp2; try discriminate H3;
             destruct (typ_beq tp1 tp2) eqn:Htyp; try discriminate H3;
             injection H3 as <-;
             rewrite (IHe1 le1' tp1 eq_refl eq_refl);
             rewrite (IHe2 le2' tp2 eq_refl eq_refl);
             rewrite Htyp; reflexivity).
    - (* IfE e1 e2 e3 *)
      destruct (trnsl_expr_lExpr stk e1) as [le1'|] eqn:Hle1'; [|discriminate H2].
      destruct (trnsl_expr_lExpr stk e2) as [le2'|] eqn:Hle2'; [|discriminate H2].
      destruct (trnsl_expr_lExpr stk e3) as [le3'|] eqn:Hle3'; [|discriminate H2].
      injection H2 as <-. simpl.
      destruct (inf_expr ρ e1) as [[]|] eqn:Htp1; try discriminate H3.
      destruct (inf_expr ρ e2) as [tp2|] eqn:Htp2; try discriminate H3.
      destruct (inf_expr ρ e3) as [tp3|] eqn:Htp3; try discriminate H3.
      destruct (typ_beq tp2 tp3) eqn:Htyp; try discriminate H3.
      injection H3 as <-.
      rewrite (IHe1 le1' TpBool eq_refl eq_refl).
      rewrite (IHe2 le2' tp2 eq_refl eq_refl).
      rewrite (IHe3 le3' tp3 eq_refl eq_refl).
      rewrite Htyp. reflexivity.
    - (* StuckE *)
      discriminate H3.
  Qed.

  (* Combined lemma: a well-typed expression always evaluates and the result has
     the inferred type. Proved by structural induction; both corollaries follow. *)
  Local Lemma interp_lexpr_well_typed σ le mp tp :
    env_typ_well_defined σ mp →
    inf_lexpr σ le = Some tp →
    ∃ val, interp_lexpr le mp = Some val ∧ typeOf (trnsl_lval val) = tp.
  Proof.
    intros Hwf. revert tp.
    induction le; intros tp Hinf; simpl in *.
    - (* LVar x *)
      injection Hinf as <-. exists (mp x). split; [done|].
      specialize (Hwf x).
      destruct (σ x), (mp x); simpl in *; try contradiction; done.
    - (* LVal v *)
      injection Hinf as <-. eauto.
    - (* LUnOp *)
      destruct op.
      + (* NotBoolOp *)
        destruct (inf_lexpr σ le) as [[]|]; try discriminate Hinf.
        injection Hinf as <-.
        destruct (IHle TpBool eq_refl) as (v & Hv & Htyp).
        destruct v; simpl in Htyp; try discriminate Htyp.
        eexists. rewrite Hv. split; done.
      + (* NegOp *)
        destruct (inf_lexpr σ le) as [[]|]; try discriminate Hinf.
        injection Hinf as <-.
        destruct (IHle TpInt eq_refl) as (v & Hv & Htyp).
        destruct v; simpl in Htyp; try discriminate Htyp.
        eexists. rewrite Hv. split; done.
    - (* LBinOp: arithmetic/comparison (TpInt × TpInt) and boolean (TpBool × TpBool) share structure *)
      destruct op; simpl in Hinf;
      (* AddOp | SubOp | MulOp | DivOp | ModOp | LtOp | GtOp | LeOp | GeOp:
         both subexprs must be TpInt; note after simpl the IH sees the reduced value *)
      try (
        destruct (inf_lexpr σ le1) as [[]|]; try discriminate Hinf;
        destruct (inf_lexpr σ le2) as [[]|]; try discriminate Hinf;
        injection Hinf as <-;
        destruct (IHle1 TpInt eq_refl) as (v1 & Hv1 & Htyp1);
        destruct (IHle2 TpInt eq_refl) as (v2 & Hv2 & Htyp2);
        destruct v1; simpl in Htyp1; try discriminate Htyp1;
        destruct v2; simpl in Htyp2; try discriminate Htyp2;
        eexists; rewrite Hv1 Hv2; split; done);
      (* EqOp | NeOp: subexprs must have the same (any) type *)
      try (
        destruct (inf_lexpr σ le1) as [tp1|]; try discriminate Hinf;
        destruct (inf_lexpr σ le2) as [tp2|]; try discriminate Hinf;
        destruct (typ_beq tp1 tp2); try discriminate Hinf;
        injection Hinf as <-;
        destruct (IHle1 tp1 eq_refl) as (v1 & Hv1 & _);
        destruct (IHle2 tp2 eq_refl) as (v2 & Hv2 & _);
        eexists; rewrite Hv1 Hv2; split; done);
      (* AndOp | OrOp: both subexprs must be TpBool *)
      try (
        destruct (inf_lexpr σ le1) as [[]|]; try discriminate Hinf;
        destruct (inf_lexpr σ le2) as [[]|]; try discriminate Hinf;
        injection Hinf as <-;
        destruct (IHle1 TpBool eq_refl) as (v1 & Hv1 & Htyp1);
        destruct (IHle2 TpBool eq_refl) as (v2 & Hv2 & Htyp2);
        destruct v1; simpl in Htyp1; try discriminate Htyp1;
        destruct v2; simpl in Htyp2; try discriminate Htyp2;
        eexists; rewrite Hv1 Hv2; split; done).
    - (* LIfE *)
      destruct (inf_lexpr σ le1) as [[]|]; try discriminate Hinf.
      destruct (inf_lexpr σ le2) as [tp2|] eqn:He2; try discriminate Hinf.
      destruct (inf_lexpr σ le3) as [tp3|] eqn:He3; try discriminate Hinf.
      destruct (typ_beq tp2 tp3) eqn:Hbeq; try discriminate Hinf.
      injection Hinf as <-.
      apply internal_typ_dec_bl in Hbeq. subst tp3.
      destruct (IHle1 TpBool eq_refl) as (v1 & Hv1 & Htyp1).
      destruct v1; simpl in Htyp1; try discriminate Htyp1.
      rewrite Hv1. destruct b.
      + exact (IHle2 tp2 eq_refl).
      + exact (IHle3 tp2 eq_refl).
    - (* LStuck *)
      discriminate Hinf.
  Qed.

  Lemma interp_lexpr_typ_compat σ le tp val mp :
    env_typ_well_defined σ mp ->
    inf_lexpr σ le = Some tp ->
    (interp_lexpr le mp) = Some val ->
    typeOf (trnsl_lval val) = tp.
  Proof.
    intros Hwf Hinf Heval.
    destruct (interp_lexpr_well_typed σ le mp tp Hwf Hinf) as (val' & Hval' & Htyp).
    rewrite Hval' in Heval. injection Heval as <-. exact Htyp.
  Qed.

  Lemma lexpr_typcheck_well_defined σ mp le tp :
    env_typ_well_defined σ mp ->
    inf_lexpr σ le = Some tp ->
    ∃ val, interp_lexpr le mp = Some val.
  Proof.
    intros Hwf Hinf.
    destruct (interp_lexpr_well_typed σ le mp tp Hwf Hinf) as (val & Hval & _).
    eauto.
  Qed.

  (* Substituting a variable-named lvar map that just maps each name back to itself
     is a no-op: this is used to view an assertion's "unsubstituted" translation
     (evaluated directly via mp) as a degenerate case of the substitution lemmas. *)
  Lemma lexpr_subst_id_map (args : list var) e :
    lexpr_subst e (list_to_map (zip args (map LVar args)) : gmap var LExpr) = e.
  Proof.
    induction e; simpl; try (f_equal; done).
    destruct (list_to_map (zip args (map LVar args)) !! x) as [e'|] eqn:Hx; [ | done].
    apply elem_of_list_to_map_2 in Hx.
    apply elem_of_list_lookup_1 in Hx as [i Hi].
    apply lookup_zip_with_Some in Hi as (a & le & Heq & Ha & Hle).
    injection Heq as <- <-.
    rewrite list_lookup_fmap in Hle. rewrite Ha in Hle. simpl in Hle.
    injection Hle as <-. done.
  Qed.

  Lemma subst_id_map (args : list var) a :
    subst a (list_to_map (zip args (map LVar args)) : gmap var LExpr) = a.
  Proof.
    induction a; simpl;
      repeat match goal with
      | |- context [lexpr_subst ?e (list_to_map (zip args (map LVar args)))] =>
          rewrite (lexpr_subst_id_map args e)
      | H : subst ?a _ = ?a |- context [subst ?a (list_to_map (zip args (map LVar args)))] =>
          rewrite H
      end;
      try done.
    - f_equal. induction args0; simpl; [done|]. f_equal; [apply lexpr_subst_id_map | done].
    - f_equal. induction args0; simpl; [done|]. f_equal; [apply lexpr_subst_id_map | done].
  Qed.

  (* If mp' agrees with the zipped (args,arg_vals) pairs, then the "identity lexprs"
     (mapping each formal-arg name back to LVar itself) evaluate under mp' to exactly
     those values — the fact needed to instantiate trnsl_assertion's substitution
     lemmas at an mp that already "bakes in" the substitution directly. *)
  Lemma eval_lvar_identity_map_agrees (args : list var) (arg_vals : list lang.val) (mp' : symb_map) :
    length args = length arg_vals →
    (∀ v val, (v, val) ∈ zip args arg_vals → mp' v = trnsl_val val) →
    Forall2 (λ expr val0, interp_lexpr expr mp' = Some (trnsl_val val0)) (map LVar args) arg_vals.
  Proof.
    revert arg_vals. induction args as [| a args IH]; intros [| v vals] Hlen Hagree;
      simpl in Hlen; try discriminate Hlen; simpl; [constructor |].
    constructor.
    - simpl. rewrite (Hagree a v (elem_of_list_here _ _)). done.
    - apply IH; [lia |]. intros v' val' Hin. apply Hagree. right. exact Hin.
  Qed.

  Lemma zip_id_map_lookup_arg (xs : list var) (lv : var) :
    NoDup xs → lv ∈ xs →
    (list_to_map (zip xs (map LVar xs)) : gmap var LExpr) !! lv = Some (LVar lv).
  Proof.
    induction xs as [| x xs IH]; intros Hnodup Hin.
    - inversion Hin.
    - simpl. apply elem_of_cons in Hin as [-> | Hin'].
      + rewrite lookup_insert. done.
      + rewrite lookup_insert_ne.
        * apply IH; [by inversion Hnodup | exact Hin'].
        * intro Heq. subst lv. inversion Hnodup; subst. contradiction.
  Qed.

  Lemma zip_val_map_lookup_arg (xs : list var) (vals : list lang.val) (lv : var) (v : lang.val) :
    NoDup xs → (lv, v) ∈ zip xs vals →
    (list_to_map (zip xs (map (λ val, LVal (trnsl_val val)) vals)) : gmap var LExpr) !! lv = Some (LVal (trnsl_val v)).
  Proof.
    revert vals. induction xs as [| x xs IH]; intros vals Hnodup Hin.
    - inversion Hin.
    - destruct vals as [| val vals]; [inversion Hin |].
      simpl in Hin. apply elem_of_cons in Hin as [Heq | Hin'].
      + injection Heq as <- <-. simpl. rewrite lookup_insert. done.
      + simpl. rewrite lookup_insert_ne.
        * apply IH; [by inversion Hnodup | exact Hin'].
        * intro Heq. subst lv. apply elem_of_zip_l in Hin'. inversion Hnodup; subst. contradiction.
  Qed.

  (* Generalizes zip_id_map_lookup_arg / zip_val_map_lookup_arg: whatever the
     wrapping function f, a zipped (name, y) pair looks up correctly in the
     map obtained after wrapping every y with f. Used both for a genuine
     lvar-renaming (f := LVar) and for value-substitution (f := LVal ∘
     trnsl_val), matching xs against fresh, non-identity lvars rather than
     reusing the program variable names themselves. *)
  Lemma zip_wrap_map_lookup_arg {A : Type} (xs : list var) (ys : list A) (f : A -> LExpr) (x : var) (y : A) :
    NoDup xs → (x, y) ∈ zip xs ys →
    (list_to_map (zip xs (map f ys)) : gmap var LExpr) !! x = Some (f y).
  Proof.
    revert ys. induction xs as [| x0 xs IH]; intros ys Hnodup Hin.
    - inversion Hin.
    - destruct ys as [| y0 ys]; [inversion Hin |].
      simpl in Hin. apply elem_of_cons in Hin as [Heq | Hin'].
      + injection Heq as <- <-. simpl. rewrite lookup_insert. done.
      + simpl. rewrite lookup_insert_ne.
        * apply IH; [by inversion Hnodup | exact Hin'].
        * intro Heq. subst x0. apply elem_of_zip_l in Hin'. inversion Hnodup; subst. contradiction.
  Qed.

  (* Overriding mp at a list of lvar names with well-typed values (per σ) preserves
     env_typ_well_defined, as long as it held for the original mp. *)
  Lemma env_typ_well_defined_override σ mp (args : list var) (arg_vals : list lang.val) :
    Forall2 (λ v val, typeOf val = σ v) args arg_vals ->
    env_typ_well_defined σ mp ->
    env_typ_well_defined σ
      (fun lv => match (list_to_map (zip args arg_vals) : gmap var lang.val) !! lv with
                 | Some v => trnsl_val v
                 | None => mp lv
                 end).
  Proof.
    intros HF2 Henv lv.
    destruct ((list_to_map (zip args arg_vals) : gmap var lang.val) !! lv) as [v|] eqn:Hlv;
      [ | exact (Henv lv) ].
    apply elem_of_list_to_map_2 in Hlv.
    apply elem_of_list_lookup_1 in Hlv as [i Hi].
    apply lookup_zip_with_Some in Hi as (x & y & Heq & Hargs & Hvals).
    injection Heq as <- <-.
    pose proof (Forall2_lookup_lr _ _ _ _ _ _ HF2 Hargs Hvals) as Htyp.
    rewrite <- Htyp. simpl.
    destruct v; simpl; done.
  Qed.

  (* Connects the static proc_call_args_well_typed check on the caller's argument
     expressions to the runtime types of the resulting argument values, threading
     through the existing lexpr translation/interpretation type-soundness lemmas. *)
  Lemma proc_call_args_typed_result ρ σ stk mp args lexprs arg_vals proc_entry :
    stk_type_compat ρ σ stk ->
    env_typ_well_defined σ mp ->
    proc_call_args_well_typed ρ args proc_entry ->
    map (fun arg => trnsl_expr_lExpr stk arg) args = map (fun le => Some le) lexprs ->
    Forall2 (fun le val0 => interp_lexpr le mp = Some (trnsl_val val0)) lexprs arg_vals ->
    Forall2 (fun arg_decl val => typeOf val = snd arg_decl) (proc_args_of proc_entry) arg_vals.
  Proof.
    unfold proc_call_args_well_typed.
    intros Hstk Henv Htyped.
    revert lexprs arg_vals.
    induction Htyped as [| a arg_decl args params Htp Htyped IH];
      intros lexprs arg_vals Hmap HF2.
    - simpl in Hmap. destruct lexprs; [ | discriminate]. inversion HF2. constructor.
    - simpl in Hmap. destruct lexprs as [| le lexprs']; [discriminate |].
      injection Hmap as Hhd Htl.
      inversion HF2 as [| l0 v0 ls vs Hinterp HF2']; subst.
      constructor.
      + pose proof (lexpr_expr_typ_compat ρ σ stk a le (snd arg_decl) Hstk Hhd Htp) as Hinf_le.
        pose proof (interp_lexpr_typ_compat σ le (snd arg_decl) (trnsl_val v0) mp Henv Hinf_le Hinterp) as Htyp.
        rewrite trnsl_lval_trnsl_val_inverse in Htyp. exact Htyp.
      + exact (IH lexprs' vs Htl HF2').
  Qed.


End TypeInf.


Section RavenLogic.

  Fixpoint field_list_to_assertion lexpr fld_vals  := match fld_vals with
  | [] => LPure true
  | (fld,val) :: fld_vals => LAnd (LOwn lexpr fld (trnsl_val val)) (field_list_to_assertion lexpr fld_vals)
  end.

  Inductive RavenHoareTriple : 
  pvar_typs -> lvar_typs ->
  assertion -> nat ->
      stmt -> maskAnnot ->
  assertion -> nat ->  Prop :=

  | VarAssignmentRule ρ σ ι stk mask v lv e lexpr :
    trnsl_expr_lExpr stk e = Some lexpr ->
    fresh_lvar stk lv ->
    stk_type_compat ρ σ stk -> 
    RavenHoareTriple ρ σ 
      (LStack stk) ι
        (Assign v e) mask 
      (LExists lv 
        (LAnd 
          (LStack (<[v := lv]> stk))
          (LExprA (LBinOp EqOp (LVar lv) lexpr))
        )
      ) (ι+1)
  
  | HeapReadRule ρ σ ι stk mask x e val fld lexpr_e lvar_x  :
    trnsl_expr_lExpr stk e = Some lexpr_e ->
    fresh_lvar stk lvar_x ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LOwn lexpr_e fld val)) ι
        (FldRd x e fld) mask
      (LExists lvar_x (LAnd 
        (LStack (<[x := lvar_x]> stk)) 
        (LAnd 
          (LOwn lexpr_e fld val) 
          (LExprA (LBinOp EqOp (LVar lvar_x) (LVal val)))
        )
      )) (ι+1)

  | HeapWriteRule ρ σ ι stk mask v fld e old_val new_val lv :
    stk !! v = Some lv ->
    trnsl_expr_lExpr stk e = Some (LVal new_val) ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LOwn (LVar lv) fld old_val)) ι
        (FldWr v fld e) mask
      (LAnd (LStack stk) (LOwn (LVar lv) fld new_val)) (ι+1)
  
    
  | HeapAllocRule ρ σ ι stk mask x fld_vals lvar_x :
    fresh_lvar stk lvar_x ->
    NoDup fld_vals.*1 ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
       (LStack stk) ι
        (Alloc x fld_vals) mask
      (LExists lvar_x (LAnd (LStack (<[x := lvar_x]> stk)) (field_list_to_assertion (LVar lvar_x) fld_vals))) (ι+1)

  | ProcCallRuleRet ρ σ ι stk mask x proc_name args lexprs lvar_x proc_record :
    fresh_lvar stk lvar_x ->
    proc_map !! proc_name = Some proc_record ->
    length args = length (proc_args_of proc_record) ->
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    stk_type_compat ρ σ stk ->
    let subst_map := list_to_map (zip (proc_args_of proc_record).*1 lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LAnd (LProc proc_name proc_record) (subst (proc_precond_of proc_record) subst_map))) ι
        (Call x proc_name args) mask
      (LExists lvar_x (LAnd (LStack (<[x := lvar_x]> stk)) (subst (proc_postcond_of proc_record) (<[ "#ret_val" := LVar lvar_x]> subst_map)))) (ι+1)

  | SequenceRule ρ σ mask ι1 ι2 ι3 a1 c1 a2 c2 a3 :
    RavenHoareTriple ρ σ
      a1 ι1
        c1 mask
      a2 ι2
    ->
    RavenHoareTriple ρ σ
      a2 ι2
        c2 mask
      a3 ι3
    ->
    RavenHoareTriple ρ σ
      a1 ι1
        (Seq c1 c2) mask
      a3 ι3

  | CondRule ρ σ ι1 ι2 ι3 stk1 stk2 mask e s1 s2 p q lexpr :
    trnsl_expr_lExpr stk1 e = Some lexpr ->
    inf_expr ρ e = Some TpBool ->
    stk_type_compat ρ σ stk1 ->
    stk_type_compat ρ σ stk2 ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk1) (LAnd p (LExprA (lexpr))) ) ι1
        s1 mask
      (LAnd (LStack stk2) q) ι2
    ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk1) (LAnd p (LExprA (LUnOp NotBoolOp lexpr)))) ι1
        s2 mask
      (LAnd (LStack stk2) q) ι3
    ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk1) p) ι1
        (IfS e s1 s2) mask
      (LAnd (LStack stk2) q) (Nat.min ι2 ι3)

  | InvAccessBlockRule ρ σ ι1 ι2 stk mask inv args stmt inv_record p q lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    inv ∈ mask ->
    inv_map !! inv = Some inv_record ->
    stk_type_compat ρ σ stk ->
    ι1 > 0 ->
    let subst_map := list_to_map (zip inv_record.(inv_args) lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LAnd (subst inv_record.(inv_body) subst_map) p)) (ι1-1)
        stmt (mask ∖ {[inv]})
      (LAnd (LStack stk) (LAnd (subst inv_record.(inv_body) subst_map) q)) ι2 ->
    
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LAnd (LInv inv lexprs) p)) ι1
        (InvAccessBlock inv args stmt ) mask
      (LAnd (LStack stk) (LAnd (LInv inv lexprs) q)) ι2

  (* | InvUnfoldRule stk  mask1 inv args inv_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    match i1, i2 with
      | Closed, Opened s => s = [ (inv, lexprs) ]
      | Opened s1, Opened s2 => s2 = (inv, lexprs) :: s1
      | Stepped s1, Stepped s2 => s2 = (inv, lexprs) :: s1
      | _, _ => False
    end
    ->
    inv ∈ mask1 ->
    inv_map !! inv = Some inv_record ->
    let subst_map := list_to_map (zip inv_record.(inv_args) lexprs) in
    RavenHoareTriple
      stk (LInv inv lexprs) (mask1, i1)
        (UnfoldInv inv args) 
      stk (subst inv_record.(inv_body) subst_map) (mask1 ∖ {[inv]}, i2) *)

  (* | InvFoldRule stk  mask1 inv args inv_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    match i1, i2 with
    | Opened s, Closed => s = [ (inv, lexprs) ]
    | Stepped s, Closed => s = [ (inv, lexprs) ]
    | Opened s1, Opened s2 => s1 = (inv, lexprs) :: s2 /\ ¬(s2 = [])
    | Stepped s1, Stepped s2 => s1 = (inv, lexprs) :: s2 /\ ¬(s2 = [])
    | _, _ => False
    end
    ->
    inv ∉ mask1 ->
    inv_map !! inv = Some inv_record ->
    let subst_map := list_to_map (zip inv_record.(inv_args) lexprs) in
    RavenHoareTriple
      stk (subst inv_record.(inv_body) subst_map) (mask1, i1)
        (UnfoldInv inv args) 
      stk (LInv inv lexprs) (mask1 ∪ {[inv]}, i2) *)

  | PredUnfoldRule ρ σ ι stk mask pred args pred_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs)
    ->
    pred_map !! pred = Some pred_record ->
    stk_type_compat ρ σ stk ->
    let subst_map := list_to_map (zip pred_record.(pred_args) lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LPred pred lexprs)) (ι+1)
        (UnfoldPred pred args) mask
      (LAnd (LStack stk) (subst pred_record.(pred_body) subst_map)) ι

  | PredFoldRule ρ σ ι stk mask pred args pred_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs)
    ->
    stk_type_compat ρ σ stk ->
    pred_map !! pred = Some pred_record ->
    let subst_map := list_to_map (zip pred_record.(pred_args) lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (subst pred_record.(pred_body) subst_map)) ι
        (FoldPred pred args) mask
      (LAnd (LStack stk) (LPred pred lexprs)) ι

  | FPURule ρ σ ι stk mask e l_expr fld RAPack old_val new_val :
    trnsl_expr_lExpr stk e = Some l_expr ->
    (RAPack.(RA_inst) ).(fpuValid) old_val new_val ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LGhostOwn l_expr fld RAPack old_val)) ι
        (Fpu e fld RAPack old_val new_val) mask
        (LAnd (LStack stk) (LGhostOwn l_expr fld RAPack new_val)) ι

  | FrameRule ρ σ mask ι1 ι2 s p q r :
    RavenHoareTriple ρ σ
      p ι1
        s mask
      q ι2
    ->
    RavenHoareTriple ρ σ
      (LAnd p r) ι1
        s mask
      (LAnd q r) ι2
  
  | WeakeningRule ρ σ mask ι1 ι2 p p' q q' c :
    RavenHoareTriple ρ σ
      p ι1
        c mask
      q ι2
    ->
    entails p' p ->
    entails q q' ->

    RavenHoareTriple ρ σ
      p' ι1
        c mask
      q' ι2

  | SkipRule ρ σ ι stk mask p :
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) p) ι
        SkipS mask
      (LAnd (LStack stk) p) (1+ι)

  | CASSuccRule ρ σ ι stk mask v e1 fld e2 e3 lvar_v lexpr1 old_val new_val :
    fresh_lvar stk lvar_v ->
    inf_expr ρ e1 = Some (TpLoc) ->
    trnsl_expr_lExpr stk e1 = Some lexpr1 ->
    trnsl_expr_lExpr stk e2 = Some (LVal old_val) ->
    trnsl_expr_lExpr stk e3 = Some (LVal new_val) ->
    stk_type_compat ρ σ stk ->
      RavenHoareTriple ρ σ
        (LAnd (LStack stk) (LOwn lexpr1 fld old_val)) ι
          (CAS v e1 fld e2 e3) mask
        (LExists lvar_v (LAnd (LStack (<[v := lvar_v]> stk)) (LAnd (LOwn lexpr1 fld new_val) (LExprA (LBinOp EqOp (LVar lvar_v) (LVal (LitBool true)))))) ) (ι+1)

  | CASFailRule ρ σ ι stk mask v e1 fld e2 e3 lvar_v lexpr1 old_val old_val2 :
    fresh_lvar stk lvar_v ->
    inf_expr ρ e1 = Some (TpLoc) ->
    trnsl_expr_lExpr stk e1 = Some lexpr1 ->
    trnsl_expr_lExpr stk e2 = Some (LVal old_val2) ->
    stk_type_compat ρ σ stk ->
      RavenHoareTriple ρ σ
        (LAnd (LStack stk) (LAnd (LOwn lexpr1 fld old_val) (LExprA (LUnOp NotBoolOp (LBinOp EqOp (LVal old_val) (LVal old_val2)))))) ι
          (CAS v e1 fld e2 e3) mask
        (LExists lvar_v (LAnd (LStack (<[v := lvar_v]> stk)) (LAnd (LOwn lexpr1 fld old_val) (LExprA (LBinOp EqOp (LVar lvar_v) (LVal (LitBool false))))))) (ι+1)
  .

End RavenLogic.

Section LExpr_embed.
  (* TODO: Figure out the right way to do this deep embedding *)
  Definition EqOp_refl : forall a b mp, LExpr_holds (LBinOp EqOp a b) mp -> LExpr_holds (LBinOp EqOp b a) mp.
  Proof.
    intros a b mp H.
    unfold LExpr_holds.
    destruct (interp_lexpr b mp) as [vb|] eqn:Hb;
    destruct (interp_lexpr a mp) as [va|] eqn:Ha.
    - (* Both Some: need val_beq vb va = true from val_beq va vb = true *)
      assert (Hba : interp_lexpr (LBinOp EqOp b a) mp =
                    Some (LitBool (val_beq vb va))).
      { simpl. rewrite Hb. rewrite Ha. done. }
      assert (Hab : interp_lexpr (LBinOp EqOp a b) mp =
                    Some (LitBool (val_beq va vb))).
      { simpl. rewrite Ha. rewrite Hb. done. }
      rewrite Hba. simpl.
      unfold LExpr_holds in H. rewrite Hab in H. simpl in H.
      destruct (val_beq va vb) eqn:Hvavb.
      + apply internal_val_dec_bl in Hvavb. subst.
        rewrite (internal_val_dec_lb vb vb eq_refl). done.
      + discriminate H.
    - (* vb = Some, va = None: EqOp a b evaluates to None, H is False *)
      assert (Hab_none : interp_lexpr (LBinOp EqOp a b) mp = None).
      { simpl. rewrite Ha. done. }
      unfold LExpr_holds in H. rewrite Hab_none in H. contradiction.
    - (* vb = None, va = Some: EqOp a b evaluates to None, H is False *)
      assert (Hab_none : interp_lexpr (LBinOp EqOp a b) mp = None).
      { simpl. rewrite Ha. rewrite Hb. done. }
      unfold LExpr_holds in H. rewrite Hab_none in H. contradiction.
    - (* Both None: EqOp a b evaluates to None, H is False *)
      assert (Hab_none : interp_lexpr (LBinOp EqOp a b) mp = None).
      { simpl. rewrite Ha. done. }
      unfold LExpr_holds in H. rewrite Hab_none in H. contradiction.
  Qed.

  Definition EqOp_trans : forall a b c mp, LExpr_holds (LBinOp EqOp a b) mp -> LExpr_holds (LBinOp EqOp b c) mp -> LExpr_holds (LBinOp EqOp a c) mp.
  Proof.
    intros a b c mp Hab Hbc.
    unfold LExpr_holds in *.
    destruct (interp_lexpr b mp) as [vb|] eqn:Hb.
    2: { (* b = None: Hab is False *)
      assert (Hab_none : interp_lexpr (LBinOp EqOp a b) mp = None).
      { simpl. rewrite Hb. destruct (interp_lexpr a mp); done. }
      rewrite Hab_none in Hab. contradiction. }
    destruct (interp_lexpr a mp) as [va|] eqn:Ha.
    2: { assert (Hab_none : interp_lexpr (LBinOp EqOp a b) mp = None).
      { simpl. rewrite Ha. done. }
      rewrite Hab_none in Hab. contradiction. }
    destruct (interp_lexpr c mp) as [vc|] eqn:Hc.
    2: { assert (Hbc_none : interp_lexpr (LBinOp EqOp b c) mp = None).
      { simpl. rewrite Hb. rewrite Hc. done. }
      rewrite Hbc_none in Hbc. contradiction. }
    (* All Some case *)
    assert (Hab_eq : interp_lexpr (LBinOp EqOp a b) mp = Some (LitBool (val_beq va vb))).
    { simpl. rewrite Ha. rewrite Hb. done. }
    assert (Hbc_eq : interp_lexpr (LBinOp EqOp b c) mp = Some (LitBool (val_beq vb vc))).
    { simpl. rewrite Hb. rewrite Hc. done. }
    assert (Hac_eq : interp_lexpr (LBinOp EqOp a c) mp = Some (LitBool (val_beq va vc))).
    { simpl. rewrite Ha. rewrite Hc. done. }
    rewrite Hab_eq in Hab. simpl in Hab.
    rewrite Hbc_eq in Hbc. simpl in Hbc.
    rewrite Hac_eq. simpl.
    injection Hab as Hab'. injection Hbc as Hbc'.
    apply internal_val_dec_bl in Hab'. subst vb.
    apply internal_val_dec_bl in Hbc'. subst vc.
    rewrite (internal_val_dec_lb va va eq_refl). done.
  Qed.

  (* Helper: substituting an evaluating expression preserves interp_lexpr up to map update. *)
  Lemma interp_lexpr_subst_some : forall var (le : LExpr) mp (v_le : val),
    interp_lexpr le mp = Some v_le ->
    forall e, interp_lexpr (lexpr_subst e (<[var := le]> ∅)) mp =
              interp_lexpr e (fun x => if (x =? var)%string then v_le else mp x).
  Proof.
    intros var le mp v_le Hle e. induction e; simpl;
      [| reflexivity | rewrite IHe; reflexivity | rewrite IHe1; rewrite IHe2; reflexivity
       | rewrite IHe1; rewrite IHe2; rewrite IHe3; reflexivity | reflexivity].
    destruct (decide (x = var)) as [-> | Hne].
    - rewrite lookup_insert. simpl. rewrite Hle. rewrite String.eqb_refl. reflexivity.
    - rewrite lookup_insert_ne; [|intro H; apply Hne; exact (eq_sym H)].
      rewrite lookup_empty. simpl.
      rewrite <- String.eqb_neq in Hne. rewrite Hne. reflexivity.
  Qed.

  (* Helper: substituting a None-evaluating expression gives None or same result. *)
  Lemma interp_lexpr_subst_none_eval : forall var (le : LExpr) mp,
    interp_lexpr le mp = None ->
    forall e, interp_lexpr (lexpr_subst e (<[var := le]> ∅)) mp = None \/
              interp_lexpr (lexpr_subst e (<[var := le]> ∅)) mp = interp_lexpr e mp.
  Proof.
    intros var le mp Hle e. induction e; simpl;
      [ (* LVar *)
      | (* LVal *) right; reflexivity
      | (* LUnOp *) destruct IHe as [H|H]; rewrite H; [left; destruct op; reflexivity | right; reflexivity]
      | (* LBinOp *)
        destruct IHe1 as [H1|H1]; destruct IHe2 as [H2|H2];
        [ left; rewrite H1; destruct op; reflexivity
        | left; rewrite H1; destruct op; reflexivity
        | left; rewrite H1; rewrite H2; destruct op; destruct (interp_lexpr e1 mp) as [v1|]; try reflexivity; destruct v1; reflexivity
        | right; rewrite H1; rewrite H2; reflexivity ]
      | (* LIfE *)
        destruct IHe1 as [H1|H1];
        [ left; rewrite H1; reflexivity
        | rewrite H1; destruct (interp_lexpr e1 mp) as [v|];
          [ destruct v as [b|i| |l];
            [ destruct b;
              [ destruct IHe2 as [H2|H2]; [left; exact H2 | right; exact H2]
              | destruct IHe3 as [H3|H3]; [left; exact H3 | right; exact H3] ]
            | left; reflexivity | left; reflexivity | left; reflexivity ]
          | left; reflexivity ] ]
      | (* LStuck *) left; reflexivity ].
    destruct (decide (x = var)) as [-> | Hne].
    - rewrite lookup_insert. simpl. left. exact Hle.
    - rewrite lookup_insert_ne; [|intro H; apply Hne; exact (eq_sym H)].
      rewrite lookup_empty. simpl. right. reflexivity.
  Qed.

  Definition EqOp_subst : forall var le e mp, LExpr_holds (LBinOp EqOp (LVar var) le) mp -> LExpr_holds e mp -> LExpr_holds (lexpr_subst e (<[ var := le]> ∅)) mp.
  Proof.
    intros var le e mp H1 H2.
    unfold LExpr_holds in *.
    destruct (interp_lexpr le mp) as [v_le|] eqn:Hle.
    - (* Some case: extract mp var = v_le from H1 *)
      simpl in H1; rewrite Hle in H1; simpl in H1.
      destruct (val_beq (mp var) v_le) eqn:Hbeq; [|discriminate H1].
      apply internal_val_dec_bl in Hbeq; subst v_le.
      assert (Hmap : (fun x => if (x =? var)%string then mp var else mp x) = mp)
        by (apply FunctionalExtensionality.functional_extensionality; intro x;
            destruct (String.eqb_spec x var) as [->|_]; reflexivity).
      rewrite (interp_lexpr_subst_some var le mp (mp var) Hle e); rewrite Hmap; exact H2.
    - (* None case: H1 is False since LBinOp EqOp (LVar var) le evaluates to None *)
      assert (H1_none : interp_lexpr (LBinOp EqOp (LVar var) le) mp = None).
      { simpl. rewrite Hle. done. }
      rewrite H1_none in H1. contradiction.
  Qed.

  Definition EqpOp_LVal : forall v1 v2 mp, LExpr_holds (LBinOp EqOp (LVal v1) (LVal v2)) mp -> v1 = v2.
  Proof.
    intros v1 v2 mp H.
    unfold LExpr_holds in H. simpl in H.
    destruct (val_beq v1 v2) eqn:Heq.
    - apply internal_val_dec_bl. exact Heq.
    - discriminate H.
  Qed.

End LExpr_embed.


Section AssertionsProperties.

  (* Effective value of a logical variable under substitution map M and symbolic map mp:
     either interprets the substituted expression, or returns the raw symbolic value. *)
  Definition eval_lvar (M : gmap lvar LExpr) (mp : symb_map) (x : lvar) : option val :=
    match M !! x with
    | Some e => interp_lexpr e mp
    | None => Some (mp x)
    end.

  (* Helper: push interp_lexpr inside a lookup-driven match. Needed because the kernel
     won't reduce `interp_lexpr (match M!!x with …) mp` propositionally without a case split. *)
  Lemma interp_lexpr_lookup_match (M : gmap lvar LExpr) (x : lvar) (mp : symb_map) :
    interp_lexpr (match M !! x with Some e => e | None => LVar x end) mp =
    match M !! x with Some e => interp_lexpr e mp | None => Some (mp x) end.
  Proof. destruct (M !! x); reflexivity. Qed.

  (* If two (M, mp) pairs agree on eval_lvar, lexpr_subst produces the same interp_lexpr result. *)
  Lemma interp_lexpr_lexpr_subst_eval_lvar_congr (e : LExpr) (M1 M2 : gmap lvar LExpr)
      (mp1 mp2 : symb_map) :
    (∀ x, eval_lvar M1 mp1 x = eval_lvar M2 mp2 x) →
    interp_lexpr (lexpr_subst e M1) mp1 = interp_lexpr (lexpr_subst e M2) mp2.
  Proof.
    intro Hbase. induction e; simpl.
    - (* LVar x: rewrite the interp_lexpr-over-match to the distributed form, then use Hbase. *)
      rewrite !interp_lexpr_lookup_match.
      exact (Hbase x).
    - (* LVal *) reflexivity.
    - (* LUnOp *) rewrite IHe. reflexivity.
    - (* LBinOp *) rewrite IHe1; rewrite IHe2. reflexivity.
    - (* LIfE *)
      rewrite IHe1.
      destruct (interp_lexpr (lexpr_subst e1 M2) mp2) as [[b| | |]|]; try reflexivity.
      destruct b; [exact IHe2 | exact IHe3].
    - (* LStuck *) reflexivity.
  Qed.

  (* Updating q at v leaves eval_lvar M q x unchanged when x ∈ dom M or x ≠ v *)
  Lemma eval_lvar_update_stable (M : gmap lvar LExpr) (q : symb_map) (v : lvar) (v' : val) (x : lvar) :
    v ∉ lexpr_map_fvars M →
    (x ∈ dom M ∨ x ≠ v) →
    eval_lvar M (fun y => if (y =? v)%string then v' else q y) x = eval_lvar M q x.
  Proof.
    intros Hfresh Hcases.
    unfold eval_lvar.
    destruct (M !! x) as [le|] eqn:HMx.
    - (* x ∈ dom M: use interp_lexpr_stable *)
      apply interp_lexpr_stable.
      exact (proj1 (lexpr_map_fvars_spec M v) Hfresh x le HMx).
    - (* x ∉ dom M: x ≠ v by hypothesis *)
      destruct Hcases as [Hdom | Hne].
      + (* x ∈ dom M contradicts M !! x = None *)
        exfalso. rewrite <- not_elem_of_dom in HMx. exact (HMx Hdom).
      + destruct (String.eqb_spec x v) as [Heq | _].
        * exfalso. exact (Hne Heq).
        * reflexivity.
  Qed.

  (* Restricted version: lexpr_fvars e ⊆ dom M1 → Hbase restricted to dom M1 suffices *)
  Lemma interp_lexpr_lexpr_subst_eval_lvar_congr_dom (e : LExpr) (M1 M2 : gmap lvar LExpr)
      (mp1 mp2 : symb_map) :
    lexpr_fvars e ⊆ dom M1 →
    (∀ x, x ∈ dom M1 → eval_lvar M1 mp1 x = eval_lvar M2 mp2 x) →
    interp_lexpr (lexpr_subst e M1) mp1 = interp_lexpr (lexpr_subst e M2) mp2.
  Proof.
    intros Hdom Hbase. induction e; simpl.
    - rewrite !interp_lexpr_lookup_match.
      apply Hbase. apply Hdom. set_solver.
    - reflexivity.
    - simpl in Hdom. rewrite (IHe Hdom). reflexivity.
    - simpl in Hdom.
      have Hd1 : lexpr_fvars e1 ⊆ dom M1. { set_solver. }
      have Hd2 : lexpr_fvars e2 ⊆ dom M1. { set_solver. }
      rewrite (IHe1 Hd1). rewrite (IHe2 Hd2). reflexivity.
    - simpl in Hdom.
      have Hd1 : lexpr_fvars e1 ⊆ dom M1. { set_solver. }
      have Hd2 : lexpr_fvars e2 ⊆ dom M1. { set_solver. }
      have Hd3 : lexpr_fvars e3 ⊆ dom M1. { set_solver. }
      rewrite (IHe1 Hd1).
      destruct (interp_lexpr (lexpr_subst e1 M2) mp2) as [[b| | |]|]; try reflexivity.
      destruct b.
      + rewrite (IHe2 Hd2). reflexivity.
      + rewrite (IHe3 Hd3). reflexivity.
    - reflexivity.
  Qed.

  (* Common generalization:
     If (M1, mp1) and (M2, mp2) agree on eval_lvar for x ∈ dom M1 (Hbase),
     and eval_lvar agreement is preserved under mp updates at v ∉ lexpr_map_fvars M (Hstab),
     then translating the same StackFree assertion under both maps yields equivalent props.
     Additional well-formedness conditions:
     - dom M1 = dom M2
     - spec LExpr fvars ⊆ dom M1
     - spec LExists binders ∉ lexpr_map_fvars M1 ∪ M2 *)
  Lemma trnsl_assertion_subst_congr
    (Hwf : ProgramWF)
    (a : assertion) (M1 M2 : gmap lvar LExpr) stk_id (mp1 mp2 : symb_map) :
    StackFree a →
    assertion_exists_binders a ## lexpr_map_fvars M1 →
    assertion_exists_binders a ## lexpr_map_fvars M2 →
    assertion_lexpr_fvars a ⊆ dom M1 →
    dom M1 = dom M2 →
    (* Hstab: restricted eval_lvar agreement preserved under mp updates at v ∉ lexpr_map_fvars M *)
    (∀ (q1 q2 : symb_map),
      (∀ x, x ∈ dom M1 → eval_lvar M1 q1 x = eval_lvar M2 q2 x) →
      ∀ (v : lvar), v ∉ lexpr_map_fvars M1 → v ∉ lexpr_map_fvars M2 →
      ∀ (v' : val) (x : lvar), x ∈ dom M1 →
      eval_lvar M1 (fun y => if (y =? v)%string then v' else q1 y) x =
      eval_lvar M2 (fun y => if (y =? v)%string then v' else q2 y) x) →
    (* Hbase: restricted eval_lvar agreement for the given mp1 and mp2. *)
    (∀ x, x ∈ dom M1 → eval_lvar M1 mp1 x = eval_lvar M2 mp2 x) →
    trnsl_assertion (subst a M1) stk_id mp1 ≡ trnsl_assertion (subst a M2) stk_id mp2.
  Proof.
    intros HSF HbA_M1 HbA_M2 HfvA HdomEq Hstab Hbase.
    unfold trnsl_assertion, trnsl_assertion'.
    cut (∀ (a0 : assertion) (M1' M2' : gmap lvar LExpr) stk_id' (mp1' mp2' : symb_map),
      StackFree a0 →
      assertion_exists_binders a0 ## lexpr_map_fvars M1' →
      assertion_exists_binders a0 ## lexpr_map_fvars M2' →
      assertion_lexpr_fvars a0 ⊆ dom M1' →
      dom M1' = dom M2' →
      (∀ (q1 q2 : symb_map),
        (∀ x, x ∈ dom M1' → eval_lvar M1' q1 x = eval_lvar M2' q2 x) →
        ∀ (v : lvar), v ∉ lexpr_map_fvars M1' → v ∉ lexpr_map_fvars M2' →
        ∀ (v' : val) (x : lvar), x ∈ dom M1' →
        eval_lvar M1' (fun y => if (y =? v)%string then v' else q1 y) x =
        eval_lvar M2' (fun y => if (y =? v)%string then v' else q2 y) x) →
      (∀ x, x ∈ dom M1' → eval_lvar M1' mp1' x = eval_lvar M2' mp2' x) →
      fixpoint trnsl_assertion_pre (subst a0 M1') stk_id' mp1' ≡
      fixpoint trnsl_assertion_pre (subst a0 M2') stk_id' mp2').
    { intro H. exact (H a M1 M2 stk_id mp1 mp2 HSF HbA_M1 HbA_M2 HfvA HdomEq Hstab Hbase). }
    apply (@fixpoint_ind natSI
      (assertion -d> stack_id -d> symb_map -d> iPropO Σ)
      _ _ trnsl_assertion_pre trnsl_assertion_pre_contractive
      (fun F =>
        ∀ (a0 : assertion) (M1' M2' : gmap lvar LExpr) stk_id' (mp1' mp2' : symb_map),
          StackFree a0 →
          assertion_exists_binders a0 ## lexpr_map_fvars M1' →
          assertion_exists_binders a0 ## lexpr_map_fvars M2' →
          assertion_lexpr_fvars a0 ⊆ dom M1' →
          dom M1' = dom M2' →
          (∀ (q1 q2 : symb_map),
            (∀ x, x ∈ dom M1' → eval_lvar M1' q1 x = eval_lvar M2' q2 x) →
            ∀ (v : lvar), v ∉ lexpr_map_fvars M1' → v ∉ lexpr_map_fvars M2' →
            ∀ (v' : val) (x : lvar), x ∈ dom M1' →
            eval_lvar M1' (fun y => if (y =? v)%string then v' else q1 y) x =
            eval_lvar M2' (fun y => if (y =? v)%string then v' else q2 y) x) →
          (∀ x, x ∈ dom M1' → eval_lvar M1' mp1' x = eval_lvar M2' mp2' x) →
          F (subst a0 M1') stk_id' mp1' ≡ F (subst a0 M2') stk_id' mp2')).
    - (* Proper *)
      intros F G HFG HF a0 M1' M2' stk_id' mp1' mp2' Ha0 HbA1 HbA2 Hfv Hdom Hstab' Hbase'.
      etransitivity. { symmetry. exact (HFG (subst a0 M1') stk_id' mp1'). }
      etransitivity. { exact (HF a0 M1' M2' stk_id' mp1' mp2' Ha0 HbA1 HbA2 Hfv Hdom Hstab' Hbase'). }
      exact (HFG (subst a0 M2') stk_id' mp2').
    - (* lower bound *)
      exists inhabitant. intros; reflexivity.
    - (* step: structural induction on a0, using fixpoint IH for LInv/LPred *)
      intros F IH.
      induction a0; intros M1' M2' stk_id' mp1' mp2' Hsf HbA1 HbA2 HfvA' HdomEq' Hstab' Hbase';
        simpl in HbA1, HbA2, HfvA'.
      + (* LProc: both sides independent of M and mp *) reflexivity.
      + (* LStack: not StackFree *) inversion Hsf.
      + (* LExprA p *)
        apply bi.pure_proper. unfold LExpr_holds.
        rewrite (interp_lexpr_lexpr_subst_eval_lvar_congr_dom p M1' M2' mp1' mp2' HfvA' Hbase'). tauto.
      + (* LPure p *) reflexivity.
      + (* LOwn e fld chunk *)
        apply bi.exist_proper. intro l. apply bi.sep_proper; [| reflexivity].
        apply bi.pure_proper. unfold LExpr_holds.
        have Hfv_dom : lexpr_fvars (LBinOp EqOp e (LVal (LitLoc l))) ⊆ dom M1'.
        { simpl. set_solver. }
        have Hcongr := interp_lexpr_lexpr_subst_eval_lvar_congr_dom
          (LBinOp EqOp e (LVal (LitLoc l))) M1' M2' mp1' mp2' Hfv_dom Hbase'.
        simpl in Hcongr |- *. rewrite Hcongr. tauto.
      + (* LGhostOwn e fld RAPack chunk *)
        simpl.
        generalize (Γ RAPack).
        intros [i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]].
        apply bi.exist_proper. intro l. apply bi.sep_proper; [| reflexivity].
        apply bi.pure_proper. unfold LExpr_holds.
        have Hfv_dom : lexpr_fvars (LBinOp EqOp e (LVal (LitLoc l))) ⊆ dom M1'.
        { simpl. set_solver. }
        have Hcongr := interp_lexpr_lexpr_subst_eval_lvar_congr_dom
          (LBinOp EqOp e (LVal (LitLoc l))) M1' M2' mp1' mp2' Hfv_dom Hbase'.
        simpl in Hcongr |- *. rewrite Hcongr. tauto.
      + (* LForall v body: LForall does not update mp *)
        inversion Hsf.
        apply bi.forall_proper. intro v'.
        exact (IHa0 M1' M2' stk_id' mp1' mp2' H0 HbA1 HbA2 HfvA' HdomEq' Hstab' Hbase').
      + (* LExists v body: LExists updates mp with v ↦ v'; freshness from HbA1 *)
        inversion Hsf. subst.
        apply bi.exist_proper. intro v'.
        have Hv1 : v ∉ lexpr_map_fvars M1'. { set_solver. }
        have Hv2 : v ∉ lexpr_map_fvars M2'. { set_solver. }
        have HbA1_sub : assertion_exists_binders a0 ## lexpr_map_fvars M1'. { set_solver. }
        have HbA2_sub : assertion_exists_binders a0 ## lexpr_map_fvars M2'. { set_solver. }
        apply (IHa0 M1' M2' stk_id'
          (fun y => if (y =? v)%string then v' else mp1' y)
          (fun y => if (y =? v)%string then v' else mp2' y)
          H0 HbA1_sub HbA2_sub HfvA' HdomEq' Hstab').
        intros x Hx. exact (Hstab' mp1' mp2' Hbase' v Hv1 Hv2 v' x Hx).
      + (* LImpl cond body *)
        inversion Hsf. subst.
        have Hfv_cond : lexpr_fvars cond ⊆ dom M1'. { set_solver. }
        have Hfv_body : assertion_lexpr_fvars a0 ⊆ dom M1'. { set_solver. }
        apply bi.wand_proper.
        * apply bi.pure_proper. unfold LExpr_holds.
          rewrite (interp_lexpr_lexpr_subst_eval_lvar_congr_dom cond M1' M2' mp1' mp2' Hfv_cond Hbase'). tauto.
        * exact (IHa0 M1' M2' stk_id' mp1' mp2' H0 HbA1 HbA2 Hfv_body HdomEq' Hstab' Hbase').
      + (* LInv: prove InvBodyWF from scoped condition, use it to rewrite *)
        destruct (inv_map !! inv_name0) as [r|] eqn:Hr.
        2: { simpl. rewrite Hr. reflexivity. }
        have HinvBodyWF := inv_body_wf_from_scoped r (Hwf.(pwf_inv_fvars_scoped) inv_name0 r Hr).
        inversion Hsf. rewrite Hr in H1. inversion H1. subst inv_record.
        simpl. rewrite Hr.
        rewrite (HinvBodyWF args M1' H2); rewrite (HinvBodyWF args M2' H2).
        f_equiv.
        apply (IH (subst r.(inv_body) (list_to_map (zip r.(inv_args) args)))
          M1' M2' stk_id' mp1' mp2' H3).
        * rewrite assertion_exists_binders_subst.
          exact (Hwf.(pwf_inv_binders_fresh) inv_name0 r M1' Hr).
        * rewrite assertion_exists_binders_subst.
          exact (Hwf.(pwf_inv_binders_fresh) inv_name0 r M2' Hr).
        * etransitivity.
          { exact (Hwf.(pwf_inv_fvars_bounded) inv_name0 r args Hr). }
          { exact HfvA'. }
        * exact HdomEq'.
        * exact Hstab'.
        * exact Hbase'.
      + (* LPred: prove PredBodyWF from scoped condition, use it to rewrite *)
        destruct (pred_map !! pred_name0) as [r|] eqn:Hr.
        2: { simpl. rewrite Hr. reflexivity. }
        have HPredBodyWF := pred_body_wf_from_scoped r (Hwf.(pwf_pred_fvars_scoped) pred_name0 r Hr).
        inversion Hsf. rewrite Hr in H1. inversion H1. subst pred_record.
        simpl. rewrite Hr.
        rewrite (HPredBodyWF args M1' H2); rewrite (HPredBodyWF args M2' H2).
        f_equiv.
        apply (IH (subst r.(pred_body) (list_to_map (zip r.(pred_args) args)))
          M1' M2' stk_id' mp1' mp2' H3).
        * rewrite assertion_exists_binders_subst.
          exact (Hwf.(pwf_pred_binders_fresh) pred_name0 r M1' Hr).
        * rewrite assertion_exists_binders_subst.
          exact (Hwf.(pwf_pred_binders_fresh) pred_name0 r M2' Hr).
        * etransitivity.
          { exact (Hwf.(pwf_pred_fvars_bounded) pred_name0 r args Hr). }
          { exact HfvA'. }
        * exact HdomEq'.
        * exact Hstab'.
        * exact Hbase'.
      + (* LAnd a0_1 a0_2 *)
        inversion Hsf. subst.
        have HbA1_1 : assertion_exists_binders a0_1 ## lexpr_map_fvars M1'. { set_solver. }
        have HbA2_1 : assertion_exists_binders a0_1 ## lexpr_map_fvars M2'. { set_solver. }
        have HbA1_2 : assertion_exists_binders a0_2 ## lexpr_map_fvars M1'. { set_solver. }
        have HbA2_2 : assertion_exists_binders a0_2 ## lexpr_map_fvars M2'. { set_solver. }
        have Hfv1 : assertion_lexpr_fvars a0_1 ⊆ dom M1'. { set_solver. }
        have Hfv2 : assertion_lexpr_fvars a0_2 ⊆ dom M1'. { set_solver. }
        apply bi.sep_proper.
        * exact (IHa0_1 M1' M2' stk_id' mp1' mp2' H1 HbA1_1 HbA2_1 Hfv1 HdomEq' Hstab' Hbase').
        * exact (IHa0_2 M1' M2' stk_id' mp1' mp2' H2 HbA1_2 HbA2_2 Hfv2 HdomEq' Hstab' Hbase').
    - (* LimitPreserving *)
      apply limit_preserving_forall. intro a0.
      apply limit_preserving_forall. intro M1'.
      apply limit_preserving_forall. intro M2'.
      apply limit_preserving_forall. intro stk_id'.
      apply limit_preserving_forall. intro mp1'.
      apply limit_preserving_forall. intro mp2'.
      apply limit_preserving_impl'. { intros F G _. tauto. }
      apply limit_preserving_impl'. { intros F G _. tauto. }
      apply limit_preserving_impl'. { intros F G _. tauto. }
      apply limit_preserving_impl'. { intros F G _. tauto. }
      apply limit_preserving_impl'. { intros F G _. tauto. }
      apply limit_preserving_impl'. { intros F G _. tauto. }
      apply limit_preserving_impl'. { intros F G _. tauto. }
      refine (@limit_preserving_equiv natSI
        (assertion -d> stack_id -d> symb_map -d> iPropO Σ) _ nat_sidx_finite
        (iPropO Σ) _
        (fun F => F (subst a0 M1') stk_id' mp1')
        (fun F => F (subst a0 M2') stk_id' mp2')
        _ _).
      + intros n F G HFG. exact (HFG (subst a0 M1') stk_id' mp1').
      + intros n F G HFG. exact (HFG (subst a0 M2') stk_id' mp2').
      Unshelve. all: typeclasses eauto.
  Qed.

  (* Helper: eval_lvar agreement holds for list_to_map (zip args lexprs) vs
     list_to_map (zip args (map LVal arg_vals)) when lexprs and arg_vals are Forall2-related. *)
  Lemma eval_lvar_list_to_map_zip_forall2 (args : list lvar) (lexprs : list LExpr)
      (arg_vals : list lang.val) (mp : symb_map) :
    Forall2 (fun le v => interp_lexpr le mp = Some (trnsl_val v)) lexprs arg_vals →
    ∀ x,
    eval_lvar (list_to_map (zip args lexprs)) mp x =
    eval_lvar (list_to_map (zip args (map (fun v : lang.val => LVal (trnsl_val v)) arg_vals))) mp x.
  Proof.
    intro HF2. unfold eval_lvar.
    revert args.
    induction HF2 as [| le v lexprs' arg_vals' Hle HF2' IH]; intro args.
    - simpl. destruct args; simpl; reflexivity.
    - destruct args as [| a args']; simpl.
      + intro x. reflexivity.
      + intro x.
        destruct (decide (x = a)) as [-> | Hne].
        * rewrite !lookup_insert. simpl. exact Hle.
        * rewrite !lookup_insert_ne; [| by intro H; apply Hne; exact (eq_sym H) | by intro H; apply Hne; exact (eq_sym H)].
          exact (IH args' x).
  Qed.

  (* Helper: every value in list_to_map (zip ks vs) is in vs. *)
  Lemma lookup_list_to_map_zip_in_snd {B : Type} (ks : list lvar) (vs : list B) (k : lvar) v :
    (list_to_map (zip ks vs) : gmap lvar B) !! k = Some v → v ∈ vs.
  Proof.
    revert vs. induction ks as [| k' ks' IH]; intros vs Hk.
    - rewrite lookup_empty in Hk. discriminate.
    - destruct vs as [| v' vs'].
      + rewrite lookup_empty in Hk. discriminate.
      + simpl in Hk.
        destruct (decide (k = k')) as [-> | Hne].
        * rewrite lookup_insert in Hk. injection Hk as <-.
          apply elem_of_cons. left. reflexivity.
        * rewrite lookup_insert_ne in Hk; [| congruence].
          apply elem_of_cons. right. exact (IH vs' Hk).
  Qed.

  (* Helper: if lv is fresh w.r.t. stk, and lexprs are translations of args via trnsl_expr_lExpr,
     then lv ∉ lexpr_map_fvars of any zip map over lexprs. *)
  Lemma fresh_lvar_not_in_lexpr_map_fvars_zip (stk : stack) (args : list lang.expr)
      (lexprs : list LExpr) (arg_names : list lvar) (lv : lvar) :
    map (fun arg => trnsl_expr_lExpr stk arg) args = map Some lexprs →
    fresh_lvar stk lv →
    lv ∉ lexpr_map_fvars (list_to_map (zip arg_names lexprs)).
  Proof.
    intros H2 Hfresh.
    apply (proj2 (lexpr_map_fvars_spec _ _)).
    intros k e Hke.
    apply lookup_list_to_map_zip_in_snd in Hke.
    apply elem_of_list_lookup_1 in Hke as [i Hi].
    have H2i : map (fun arg => trnsl_expr_lExpr stk arg) args !! i = Some (Some e).
    { rewrite H2. rewrite list_lookup_fmap. rewrite Hi. reflexivity. }
    rewrite list_lookup_fmap in H2i.
    destruct (args !! i) as [arg|] eqn:Harg.
    - simpl in H2i. injection H2i as He.
      exact (trnsl_expr_lExpr_fresh_lvar stk arg e lv He Hfresh).
    - discriminate.
  Qed.

  Lemma hstab_lexpr_subst_fwd (args : list lvar) (lexprs : list LExpr)
      (arg_vals : list lang.val)
      (HdomEq : dom (list_to_map (zip args lexprs) : gmap lvar LExpr) =
                dom (list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals)) : gmap lvar LExpr)) :
    ∀ (q1 q2 : symb_map),
    (∀ x, x ∈ dom (list_to_map (zip args lexprs) : gmap lvar LExpr) →
           eval_lvar (list_to_map (zip args lexprs)) q1 x =
           eval_lvar (list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))) q2 x) →
    ∀ (v : lvar),
    v ∉ lexpr_map_fvars (list_to_map (zip args lexprs)) →
    v ∉ lexpr_map_fvars (list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))) →
    ∀ (v' : val) (x : lvar), x ∈ dom (list_to_map (zip args lexprs) : gmap lvar LExpr) →
    eval_lvar (list_to_map (zip args lexprs)) (fun y => if (y =? v)%string then v' else q1 y) x =
    eval_lvar (list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))) (fun y => if (y =? v)%string then v' else q2 y) x.
  Proof.
    intros q1 q2 Hbase v Hv1 Hv2 v' x Hx.
    rewrite (eval_lvar_update_stable _ q1 v v' x Hv1 (or_introl Hx)).
    rewrite (Hbase x Hx).
    have Hx2 : x ∈ dom (list_to_map (zip args (map (λ w, LVal (trnsl_val w)) arg_vals)) : gmap lvar LExpr).
    { rewrite <- HdomEq. exact Hx. }
    exact (eq_sym (eval_lvar_update_stable _ q2 v v' x Hv2 (or_introl Hx2))).
  Qed.

  Lemma hstab_lexpr_subst_r (args : list lvar) (lexprs : list LExpr)
      (arg_vals : list lang.val) (lvar_x : lvar) (ret_val : lang.val)
      (HdomEq : dom (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) =
                dom (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))) : gmap lvar LExpr)) :
    ∀ (q1 q2 : symb_map),
    (∀ x, x ∈ dom (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) →
           eval_lvar (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs))) q1 x =
           eval_lvar (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals)))) q2 x) →
    ∀ (v : lvar),
    v ∉ lexpr_map_fvars (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs))) →
    v ∉ lexpr_map_fvars (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals)))) →
    ∀ (v' : val) (x : lvar), x ∈ dom (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) →
    eval_lvar (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs))) (fun y => if (y =? v)%string then v' else q1 y) x =
    eval_lvar (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals)))) (fun y => if (y =? v)%string then v' else q2 y) x.
  Proof.
    intros q1 q2 Hbase v Hv1 Hv2 v' x Hx.
    rewrite (eval_lvar_update_stable _ q1 v v' x Hv1 (or_introl Hx)).
    rewrite (Hbase x Hx).
    have Hx2 : x ∈ dom (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))) : gmap lvar LExpr).
    { rewrite <- HdomEq. exact Hx. }
    exact (eq_sym (eval_lvar_update_stable _ q2 v v' x Hv2 (or_introl Hx2))).
  Qed.

  Lemma hbase_lexpr_subst_r (args : list lvar) (lexprs : list LExpr)
      (arg_vals : list lang.val) (lvar_x : lvar) (ret_val : lang.val) (mp : symb_map) :
    lvar_x ∉ lexpr_map_fvars (list_to_map (zip args lexprs)) →
    Forall2 (λ expr val0, interp_lexpr expr mp = Some (trnsl_val val0)) lexprs arg_vals →
    ∀ x, x ∈ dom (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) →
    eval_lvar (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)))
      (λ x0, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0) x =
    eval_lvar (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))))
      mp x.
  Proof.
    intros Hfresh HF2 x Hdom.
    destruct (decide (x = "#ret_val")) as [-> | Hne].
    - unfold eval_lvar. rewrite !lookup_insert. simpl. rewrite String.eqb_refl. reflexivity.
    - have Hne' : "#ret_val" ≠ x := fun H => Hne (eq_sym H).
      have Hdomx : x ∈ dom (list_to_map (zip args lexprs) : gmap lvar LExpr).
      { rewrite dom_insert in Hdom. set_solver. }
      unfold eval_lvar.
      rewrite (lookup_insert_ne _ _ _ _ Hne').
      rewrite (lookup_insert_ne _ _ _ _ Hne').
      have Hcongr : eval_lvar (list_to_map (zip args lexprs)) mp x =
                    eval_lvar (list_to_map (zip args (map (λ w, LVal (trnsl_val w)) arg_vals))) mp x :=
        eval_lvar_list_to_map_zip_forall2 args lexprs arg_vals mp HF2 x.
      unfold eval_lvar in Hcongr.
      destruct (list_to_map (zip args lexprs) !! x) as [le|] eqn:Hle.
      + have Hle_fresh : lvar_x ∉ lexpr_fvars le :=
          proj1 (lexpr_map_fvars_spec _ _) Hfresh x le Hle.
        rewrite Hle. simpl. simpl in Hcongr.
        etransitivity.
        { exact (interp_lexpr_stable le mp lvar_x (trnsl_val ret_val) Hle_fresh). }
        exact Hcongr.
      + exfalso. rewrite elem_of_dom in Hdomx. destruct Hdomx as [le' Hle']. congruence.
  Qed.

  Lemma trnsl_assertion_w_lexpr_subst assertion lexprs args arg_vals stk_id mp p1 p2
      (Hwf : ProgramWF)
      (HSF : StackFree assertion)
      (HbA_M1 : assertion_exists_binders assertion ## lexpr_map_fvars (list_to_map (zip args lexprs)))
      (HbA_M2 : assertion_exists_binders assertion ## lexpr_map_fvars (list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))))
      (HfvA : assertion_lexpr_fvars assertion ⊆ dom (list_to_map (zip args lexprs) : gmap lvar LExpr))
      (HdomEq : dom (list_to_map (zip args lexprs) : gmap lvar LExpr) = dom (list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr)) :
    Forall2 (λ expr val0, interp_lexpr expr mp = Some (trnsl_val val0)) lexprs arg_vals →
    trnsl_assertion (subst assertion (list_to_map (zip args lexprs))) stk_id mp ≡ p1 →
    trnsl_assertion (subst assertion (list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)))) stk_id mp ≡ p2 →
    p1 -∗ p2.
  Proof.
    intros HF2 Hp1 Hp2.
    have Hbase : ∀ x, x ∈ dom (list_to_map (zip args lexprs) : gmap lvar LExpr) →
                       eval_lvar (list_to_map (zip args lexprs)) mp x =
                       eval_lvar (list_to_map (zip args (map (λ val, LVal (trnsl_val val)) arg_vals))) mp x.
    { intros x _. exact (eval_lvar_list_to_map_zip_forall2 args lexprs arg_vals mp HF2 x). }
    have Hstab := hstab_lexpr_subst_fwd args lexprs arg_vals HdomEq.
    have Heq := trnsl_assertion_subst_congr Hwf assertion _ _ stk_id mp mp
      HSF HbA_M1 HbA_M2 HfvA HdomEq Hstab Hbase.
    rewrite <- Hp1. rewrite Heq. rewrite Hp2.
    iIntros "H". iExact "H".
  Qed.

  Lemma trnsl_assertion_w_lexpr_subst_r assertion lexprs args arg_vals lvar_x ret_val stk stk_id mp p1 p2
      (Hwf : ProgramWF)
      (HSF : StackFree assertion)
      (HbA_M1 : assertion_exists_binders assertion ## lexpr_map_fvars (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs))))
      (HbA_M2 : assertion_exists_binders assertion ## lexpr_map_fvars (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)))))
      (HfvA : assertion_lexpr_fvars assertion ⊆ dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr))
      (HdomEq : dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) = dom (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))) : gmap lvar LExpr))
      (Hfresh_base : lvar_x ∉ lexpr_map_fvars (list_to_map (zip args lexprs))) :
    fresh_lvar stk lvar_x →
    Forall2 (λ expr val0, interp_lexpr expr mp = Some (trnsl_val val0)) lexprs arg_vals →
    trnsl_assertion (subst assertion (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)))) stk_id
      (λ x0, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0) ≡ p1 →
    trnsl_assertion (subst assertion (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))))) stk_id mp ≡ p2 →
    p2 -∗ p1.
  Proof.
    intros _Hfresh HF2 Hp1 Hp2.
    have Hstab_r := hstab_lexpr_subst_r args lexprs arg_vals lvar_x ret_val HdomEq.
    have Hbase_r : ∀ x, x ∈ dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) →
      eval_lvar (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)))
        (λ x0, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0) x =
      eval_lvar (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val, LVal (trnsl_val val)) arg_vals))))
        mp x.
    { intros x Hx. exact (hbase_lexpr_subst_r args lexprs arg_vals lvar_x ret_val mp Hfresh_base HF2 x Hx). }
    have Heq := trnsl_assertion_subst_congr Hwf assertion _ _ stk_id
      (λ x0, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0) mp
      HSF HbA_M1 HbA_M2 HfvA HdomEq Hstab_r Hbase_r.
    rewrite <- Hp2. rewrite <- Heq. rewrite Hp1.
    iIntros "H". iExact "H".
  Qed.



  Definition stack_free_prop (F : assertion -d> stack_id -d> symb_map -d> iPropO Σ) :=
  ∀ a stk stk' mp,
    StackFree a →
    trnsl_assertion_str F a stk mp = trnsl_assertion_str F a stk' mp.

  Lemma stack_free_prop_closed :
  ∀ F, stack_free_prop F → stack_free_prop (trnsl_assertion_pre F).
  Proof.
    intros F IH a.
    (* unfold trnsl_assertion_pre. *)
    (* simpl. *)
    induction a; intros stk stk' mp Hsf; simpl in *; try reflexivity; try done.
      (* try (destruct (StackFree a1 && StackFree a2) eqn:Hsf2; simpl in *; ...). *)
    - inversion Hsf.
    - (* LForall*) apply f_equal.   (* LInv *)
      inversion Hsf.
      rewrite (IHa stk stk' mp H0). done.
    - (* LExists *) apply f_equal. extensionality v'.
    inversion Hsf.
      rewrite (IHa stk stk' (λ x : lvar, if (x =? v)%string then v' else mp x) H0). done.
      
    - inversion Hsf. (* LImpl *) rewrite (IHa stk stk' mp H0). done.
    - (* LInv *) 
      destruct (inv_map !! inv_name0) as [inv_record|] eqn:Hinv; simpl; [|reflexivity].
      unfold trnsl_assertion_pre.

      rewrite (IH (subst inv_record.(inv_body) _ ) stk stk' mp); auto.
      inversion Hsf. rewrite Hinv in H1. inversion H1. subst inv_record0. exact H3.

    - (* LPred *)
      rewrite /trnsl_assertion_str.
      destruct (pred_map !! pred_name0) as [pred_record|] eqn:Hpred; simpl; [|reflexivity].
      unfold trnsl_assertion_pre.
      rewrite (IH (subst pred_record.(pred_body) _) stk stk' mp); auto.
      inversion Hsf. rewrite Hpred in H1. inversion H1. subst pred_record0. exact H3.

    - (* LAnd *)    
      inversion Hsf; subst a0 a3.
      rewrite (IHa1 stk stk' mp H1) (IHa2 stk stk' mp H2). reflexivity.
  Qed.

  Lemma stack_free_assertion_trnsl assertion stk_id stk_id' mp :
    StackFree assertion ->
    trnsl_assertion assertion stk_id mp ≡ trnsl_assertion assertion stk_id' mp.
  Proof.
    intros HSF.
    unfold trnsl_assertion, trnsl_assertion'.
    cut (forall (a : rrl_lang.assertion) stk stk' mp0, StackFree a →
        fixpoint trnsl_assertion_pre a stk mp0 ≡ fixpoint trnsl_assertion_pre a stk' mp0).
    { intros H. exact (H assertion stk_id stk_id' mp HSF). }
    apply (@fixpoint_ind natSI
      (rrl_lang.assertion -d> stack_id -d> symb_map -d> iPropO Σ)
      _ _ trnsl_assertion_pre trnsl_assertion_pre_contractive
      (fun F => forall a stk stk' mp0, StackFree a -> F a stk mp0 ≡ F a stk' mp0)).
    - (* Proper *)
      intros F G HFG HF a stk stk' mp0 Ha.
      etransitivity. { symmetry. exact (HFG a stk mp0). }
      etransitivity. { exact (HF a stk stk' mp0 Ha). }
      exact (HFG a stk' mp0).
    - (* ∃ x, P x *)
      exists inhabitant. intros a stk stk' mp0 _. reflexivity.
    - (* Step *)
      intros F IH a.
      induction a; intros stk stk' mp0 Hsf; simpl in *; try reflexivity.
      + inversion Hsf.
      + inversion Hsf. apply bi.forall_proper. intro v'. exact (IHa stk stk' mp0 H0).
      + inversion Hsf. apply bi.exist_proper. intro v'.
        exact (IHa stk stk' (λ x, if (x =? v)%string then v' else mp0 x) H0).
      + inversion Hsf. apply bi.wand_proper. { reflexivity. } exact (IHa stk stk' mp0 H0).
      + destruct (inv_map !! inv_name0) as [r|] eqn:Hr; [|reflexivity].
        simpl. f_equiv. apply IH.
        inversion Hsf. rewrite Hr in H1. inversion H1. subst. exact H3.
      + destruct (pred_map !! pred_name0) as [r|] eqn:Hr; [|reflexivity].
        simpl. f_equiv. apply IH.
        inversion Hsf. rewrite Hr in H1. inversion H1. subst. exact H3.
      + inversion Hsf. subst a0 a3. apply bi.sep_proper.
        { exact (IHa1 stk stk' mp0 H1). } exact (IHa2 stk stk' mp0 H2).
    - (* LimitPreserving *)
      apply limit_preserving_forall. intro a.
      apply limit_preserving_forall. intro stk.
      apply limit_preserving_forall. intro stk'.
      apply limit_preserving_forall. intro mp0.
      apply limit_preserving_impl'. { intros F G _. tauto. }
      refine (@limit_preserving_equiv natSI
        (rrl_lang.assertion -d> stack_id -d> symb_map -d> iPropO Σ) _ nat_sidx_finite
        (iPropO Σ) _
        (fun (F : rrl_lang.assertion -d> stack_id -d> symb_map -d> iPropO Σ) => F a stk mp0)
        (fun (F : rrl_lang.assertion -d> stack_id -d> symb_map -d> iPropO Σ) => F a stk' mp0)
        _ _).
      + intros n F G HFG. exact (HFG a stk mp0).
      + intros n F G HFG. exact (HFG a stk' mp0).
      Unshelve. all: typeclasses eauto.
  Qed.

  Lemma stack_free_assertion_subst
    (Hwf : ProgramWF)
    assertion subst_map :
    StackFree assertion -> StackFree (subst assertion subst_map).
  Proof.
    intros HSF. induction HSF; simpl; try constructor; try assumption.
    - (* SF_Inv *)
      have Hbwf := inv_body_wf_from_scoped inv_record (Hwf.(pwf_inv_fvars_scoped) _ _ H).
      eapply SF_Inv. { exact H. } { rewrite map_length. exact H0. }
      rewrite (Hbwf args subst_map H0). exact IHHSF.
    - (* SF_Pred *)
      have Hbwf := pred_body_wf_from_scoped pred_record (Hwf.(pwf_pred_fvars_scoped) _ _ H).
      eapply SF_Pred. { exact H. } { rewrite map_length. exact H0. }
      rewrite (Hbwf args subst_map H0). exact IHHSF.
  Qed.
  

End AssertionsProperties.

Lemma transport_cmra_update {A B} (p : A = B) (x y : (cmra_car A)) :
  x ~~> y → transport (f_equal cmra_car p) x ~~> transport (f_equal cmra_car p) y.
Proof.
  intros Hxy. subst. done.
Qed.

