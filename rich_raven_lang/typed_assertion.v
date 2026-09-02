From Coq Require Import List PArith Program.Equality ZArith.

From raven_iris.rich_raven_lang Require Import typed_core.

Import ListNotations.
Open Scope list_scope.

(** Scoped assertions over the typed expression foundation. *)
Module TypedAssertion.

Module Type LOGIC_SIGNATURE.
  Parameter field_type : TypedCore.field_id -> TypedCore.typ.
  Parameter predicate_args : TypedCore.pred_id -> TypedCore.context.
  Parameter invariant_args : TypedCore.inv_id -> TypedCore.context.
End LOGIC_SIGNATURE.

Module Make (RAs : TypedCore.RA_VALUE_CONFIG) (Logic : LOGIC_SIGNATURE).
Module Core := TypedCore.Make RAs.
Import TypedCore Core.

(** A heterogeneous vector of expressions whose types are described by a
    declaration context. *)
Inductive expr_list (F Δ : context) : context -> Type :=
| ExprNil : expr_list F Δ []
| ExprCons t ts : expr F Δ t -> expr_list F Δ ts -> expr_list F Δ (t :: ts).

Arguments ExprNil {_ _}.
Arguments ExprCons {_ _ _ _} _ _.

Fixpoint lookup_expr_list {F Δ ts t} (expressions : expr_list F Δ ts)
    (variable : member ts t) : expr F Δ t.
Proof.
  destruct expressions.
  - inversion variable.
  - dependent destruction variable.
    + exact e.
    + exact (@lookup_expr_list F Δ _ _ expressions variable).
Defined.

Inductive assertion (Γ F Δ : context) : Type :=
| AStack (store : symbolic_store Γ F Δ)
| AExpr (condition : expr F Δ TBool)
| APure (proposition : Prop)
| AOwn (field : field_id) (location : expr F Δ TRef)
    (chunk : expr F Δ (Logic.field_type field))
| AExists t (body : assertion Γ F (t :: Δ))
| AForall t (body : assertion Γ F (t :: Δ))
| AIte (condition : expr F Δ TBool)
    (then_branch else_branch : assertion Γ F Δ)
| AInvariant (invariant : inv_id)
    (args : expr_list F Δ (Logic.invariant_args invariant))
| APredicate (predicate : pred_id)
    (args : expr_list F Δ (Logic.predicate_args predicate))
| AAnd (left right : assertion Γ F Δ).

Arguments AStack {_ _ _} _.
Arguments AExpr {_ _ _} _.
Arguments APure {_ _ _} _.
Arguments AOwn {_ _ _} _ _ _.
Arguments AExists {_ _ _} _ _.
Arguments AForall {_ _ _} _ _.
Arguments AIte {_ _ _} _ _ _.
Arguments AInvariant {_ _ _} _ _.
Arguments APredicate {_ _ _} _ _.
Arguments AAnd {_ _ _} _ _.

(** Binder weakening changes only bound-variable references.  Formal
    references and stable atoms are definitionally unaffected. *)
Definition weaken_ref {F Δ t u}
    (reference : value_ref F Δ t) : value_ref F (u :: Δ) t :=
  match reference with
  | RefFormal x => RefFormal x
  | RefBound x => RefBound (MThere x)
  | RefAtom x => RefAtom x
  end.

Fixpoint weaken_expr {F Δ t u} (expression : expr F Δ t) :
    expr F (u :: Δ) t :=
  match expression with
  | ERef reference => ERef (weaken_ref reference)
  | EVal value => EVal value
  | EUnOp op operand => EUnOp op (weaken_expr operand)
  | EBinOp op operand1 operand2 =>
      EBinOp op (weaken_expr operand1) (weaken_expr operand2)
  end.

Fixpoint weaken_expr_list {F Δ ts u} (expressions : expr_list F Δ ts) :
    expr_list F (u :: Δ) ts :=
  match expressions with
  | ExprNil => ExprNil
  | ExprCons expression expressions' =>
      ExprCons (weaken_expr expression) (weaken_expr_list expressions')
  end.

Fixpoint weaken_store {Γ F Δ u}
    (store : symbolic_store Γ F Δ) : symbolic_store Γ F (u :: Δ) :=
  match store with
  | StoreNil => StoreNil
  | StoreCons reference tail =>
      StoreCons (weaken_ref reference) (weaken_store tail)
  end.

(** General binder substitution.  Its source and target contexts are
    explicit, so lifting it through nested quantifiers is structural. *)
Definition bound_subst (F : context) (Δ Δ' : context) :=
  forall t, bvar Δ t -> expr F Δ' t.

Definition empty_bound_subst {F Δ} : bound_subst F [] Δ :=
  fun _ variable => match variable with end.

Definition subst_bound_ref {F Δ Δ' t}
    (substitution : bound_subst F Δ Δ') (reference : value_ref F Δ t) :
    expr F Δ' t :=
  match reference in value_ref _ _ result return expr F Δ' result with
  | RefFormal variable => ERef (RefFormal variable)
  | RefBound variable => substitution _ variable
  | RefAtom symbolic => ERef (RefAtom symbolic)
  end.

Fixpoint subst_bound_expr {F Δ Δ' t}
    (substitution : bound_subst F Δ Δ') (expression : expr F Δ t) :
    expr F Δ' t :=
  match expression with
  | ERef reference => subst_bound_ref substitution reference
  | EVal value => EVal value
  | EUnOp op operand => EUnOp op (subst_bound_expr substitution operand)
  | EBinOp op operand1 operand2 =>
      EBinOp op (subst_bound_expr substitution operand1)
        (subst_bound_expr substitution operand2)
  end.

Definition lift_bound_subst {F Δ Δ' u}
    (substitution : bound_subst F Δ Δ') :
    bound_subst F (u :: Δ) (u :: Δ') :=
  fun t variable =>
    match view_member variable with
    | MVHere => ERef (RefBound MHere)
    | MVThere variable' => weaken_expr (substitution _ variable')
    end.

Definition head_bound_subst {F Δ t} (witness : expr F Δ t) :
    bound_subst F (t :: Δ) Δ :=
  fun u variable =>
    match view_member variable with
    | MVHere => witness
    | MVThere variable' => ERef (RefBound variable')
    end.

Lemma interp_subst_bound_expr {F Δ Δ' t}
    (substitution : bound_subst F Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (Hsubstitution : forall t (variable : bvar Δ t),
      interp_expr formals target_binders atoms (substitution t variable) =
        Some (source_binders t variable))
    (expression : expr F Δ t) :
  interp_expr formals target_binders atoms
      (subst_bound_expr substitution expression) =
    interp_expr formals source_binders atoms expression.
Proof.
  induction expression; simpl.
  - destruct reference; simpl; try reflexivity. apply Hsubstitution.
  - reflexivity.
  - rewrite IHexpression. reflexivity.
  - rewrite IHexpression1, IHexpression2. reflexivity.
Qed.

Definition bound_renaming (Δ Δ' : context) :=
  forall t, bvar Δ t -> bvar Δ' t.

Definition rename_bound_ref {F Δ Δ' t}
    (renaming : bound_renaming Δ Δ') (reference : value_ref F Δ t) :
    value_ref F Δ' t :=
  match reference in value_ref _ _ result return value_ref F Δ' result with
  | RefFormal variable => RefFormal variable
  | RefBound variable => RefBound (renaming _ variable)
  | RefAtom symbolic => RefAtom symbolic
  end.

Fixpoint rename_bound_expr {F Δ Δ' t}
    (renaming : bound_renaming Δ Δ') (expression : expr F Δ t) :
    expr F Δ' t :=
  match expression with
  | ERef reference => ERef (rename_bound_ref renaming reference)
  | EVal value => EVal value
  | EUnOp op operand => EUnOp op (rename_bound_expr renaming operand)
  | EBinOp op operand1 operand2 =>
      EBinOp op (rename_bound_expr renaming operand1)
        (rename_bound_expr renaming operand2)
  end.

Definition lift_bound_renaming {Δ Δ' u}
    (renaming : bound_renaming Δ Δ') :
    bound_renaming (u :: Δ) (u :: Δ') :=
  fun t variable =>
    match view_member variable with
    | MVHere => MHere
    | MVThere variable' => MThere (renaming _ variable')
    end.

Definition weaken_bound_renaming {Δ u} : bound_renaming Δ (u :: Δ) :=
  fun t variable => MThere variable.

(** Embed a canonical one-binder procedure return context at the head of a
    caller's existing binder context. *)
Definition return_bound_renaming {Δ t} : bound_renaming [t] (t :: Δ) :=
  fun u variable =>
    match view_member variable with
    | MVHere => MHere
    | MVThere impossible => match impossible with end
    end.

Lemma interp_rename_bound_expr {F Δ Δ' t}
    (renaming : bound_renaming Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (Hrenaming : forall t (variable : bvar Δ t),
      target_binders t (renaming t variable) = source_binders t variable)
    (expression : expr F Δ t) :
  interp_expr formals target_binders atoms
      (rename_bound_expr renaming expression) =
    interp_expr formals source_binders atoms expression.
Proof.
  induction expression; simpl.
  - destruct reference; simpl; try reflexivity. rewrite Hrenaming. reflexivity.
  - reflexivity.
  - rewrite IHexpression. reflexivity.
  - rewrite IHexpression1, IHexpression2. reflexivity.
Qed.

Fixpoint rename_bound_expr_list {F Δ Δ' ts}
    (renaming : bound_renaming Δ Δ') (expressions : expr_list F Δ ts) :
    expr_list F Δ' ts :=
  match expressions with
  | ExprNil => ExprNil
  | ExprCons expression expressions' =>
      ExprCons (rename_bound_expr renaming expression)
        (rename_bound_expr_list renaming expressions')
  end.

Fixpoint rename_bound_store {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ') (store : symbolic_store Γ F Δ) :
    symbolic_store Γ F Δ' :=
  match store with
  | StoreNil => StoreNil
  | StoreCons reference tail =>
      StoreCons (rename_bound_ref renaming reference)
        (rename_bound_store renaming tail)
  end.

(** Typed simultaneous instantiation of a formal context.  Actual arguments
    are expressions rather than values, matching Raven contracts. *)
Definition formal_subst (F F' Δ : context) :=
  forall t, formal F t -> expr F' Δ t.

(** Actual arguments, viewed as the simultaneous substitution for the
    callee's canonical formal context. *)
Definition expr_list_formal_subst {F Δ ts}
    (expressions : expr_list F Δ ts) : formal_subst ts F Δ :=
  fun _ variable => lookup_expr_list expressions variable.

Definition subst_formals_ref {F F' Δ t}
    (substitution : formal_subst F F' Δ) (reference : value_ref F Δ t) :
    expr F' Δ t :=
  match reference in value_ref _ _ result return expr F' Δ result with
  | RefFormal variable => substitution _ variable
  | RefBound variable => ERef (RefBound variable)
  | RefAtom symbolic => ERef (RefAtom symbolic)
  end.

Fixpoint subst_formals_expr {F F' Δ t}
    (substitution : formal_subst F F' Δ) (expression : expr F Δ t) :
    expr F' Δ t :=
  match expression with
  | ERef reference => subst_formals_ref substitution reference
  | EVal value => EVal value
  | EUnOp op operand => EUnOp op (subst_formals_expr substitution operand)
  | EBinOp op operand1 operand2 =>
      EBinOp op (subst_formals_expr substitution operand1)
        (subst_formals_expr substitution operand2)
  end.

Definition lift_formal_subst {F F' Δ u}
    (substitution : formal_subst F F' Δ) :
    formal_subst F F' (u :: Δ) :=
  fun t variable => weaken_expr (substitution t variable).

Lemma interp_subst_formals_expr {F F' Δ t}
    (substitution : formal_subst F F' Δ)
    (source_formals : formal_env F) (target_formals : formal_env F')
    (binders : binder_env Δ) (atoms : atom_env)
    (Hsubstitution : forall t (variable : formal F t),
      interp_expr target_formals binders atoms (substitution t variable) =
        Some (source_formals t variable))
    (expression : expr F Δ t) :
  interp_expr target_formals binders atoms
      (subst_formals_expr substitution expression) =
    interp_expr source_formals binders atoms expression.
Proof.
  induction expression; simpl.
  - destruct reference; simpl; try reflexivity.
    apply Hsubstitution.
  - reflexivity.
  - rewrite IHexpression. reflexivity.
  - rewrite IHexpression1, IHexpression2. reflexivity.
Qed.

Definition identity_formal_subst {F Δ} : formal_subst F F Δ :=
  fun t variable => ERef (RefFormal variable).

Lemma subst_formals_expr_identity {F Δ t} (expression : expr F Δ t) :
  subst_formals_expr identity_formal_subst expression = expression.
Proof.
  induction expression; simpl; try congruence.
  destruct reference; reflexivity.
Qed.

Definition compose_formal_subst {F1 F2 F3 Δ}
    (outer : formal_subst F2 F3 Δ) (inner : formal_subst F1 F2 Δ) :
    formal_subst F1 F3 Δ :=
  fun t variable => subst_formals_expr outer (inner t variable).

Lemma subst_formals_expr_compose {F1 F2 F3 Δ t}
    (outer : formal_subst F2 F3 Δ) (inner : formal_subst F1 F2 Δ)
    (expression : expr F1 Δ t) :
  subst_formals_expr outer (subst_formals_expr inner expression) =
    subst_formals_expr (compose_formal_subst outer inner) expression.
Proof.
  induction expression; simpl; try congruence.
  destruct reference; reflexivity.
Qed.

(** Atom renaming is deliberately independent of formal instantiation. *)
Definition atom_renaming := forall t, atom t -> atom t.

Definition rename_atom_ref {F Δ t} (renaming : atom_renaming)
    (reference : value_ref F Δ t) : value_ref F Δ t :=
  match reference in value_ref _ _ result return value_ref F Δ result with
  | RefFormal variable => RefFormal variable
  | RefBound variable => RefBound variable
  | RefAtom symbolic => RefAtom (renaming _ symbolic)
  end.

Fixpoint rename_atoms_expr {F Δ t} (renaming : atom_renaming)
    (expression : expr F Δ t) : expr F Δ t :=
  match expression with
  | ERef reference => ERef (rename_atom_ref renaming reference)
  | EVal value => EVal value
  | EUnOp op operand => EUnOp op (rename_atoms_expr renaming operand)
  | EBinOp op operand1 operand2 =>
      EBinOp op (rename_atoms_expr renaming operand1)
        (rename_atoms_expr renaming operand2)
  end.

Lemma interp_rename_atoms_expr {F Δ t} (renaming : atom_renaming)
    (formals : formal_env F) (binders : binder_env Δ)
    (source_atoms target_atoms : atom_env)
    (Hrenaming : forall t (symbolic : atom t),
      target_atoms t (renaming t symbolic) = source_atoms t symbolic)
    (expression : expr F Δ t) :
  interp_expr formals binders target_atoms (rename_atoms_expr renaming expression) =
    interp_expr formals binders source_atoms expression.
Proof.
  induction expression; simpl.
  - destruct reference; simpl; try reflexivity.
    rewrite Hrenaming. reflexivity.
  - reflexivity.
  - rewrite IHexpression. reflexivity.
  - rewrite IHexpression1, IHexpression2. reflexivity.
Qed.

(** Insert a binder immediately below the current innermost binder. *)
Definition insert_member_after_head {Δ t u v}
    (variable : member (v :: Δ) t) : member (v :: u :: Δ) t.
Proof.
  dependent destruction variable.
  - exact MHere.
  - exact (MThere (MThere variable)).
Defined.

(** Weakening under a new outer binder.  Bound-variable zero continues to
    denote the nested binder; all older variables move across the inserted
    binder. *)
Definition lift_ref_under {F Δ t u v}
    (reference : value_ref F (v :: Δ) t) : value_ref F (v :: u :: Δ) t :=
  match reference with
  | RefFormal x => RefFormal x
  | RefBound x => RefBound (insert_member_after_head x)
  | RefAtom x => RefAtom x
  end.

(** A syntactic predicate identifying assertions independent of the symbolic
    stack.  Formal instantiation of contracts and invariant/predicate bodies
    will initially target this fragment, avoiding an unsound substitution
    operation on [AStack]. *)
Inductive stack_free {Γ F Δ} : assertion Γ F Δ -> Prop :=
| SFExpr condition : stack_free (AExpr condition)
| SFPure proposition : stack_free (APure proposition)
| SFOwn field location chunk : stack_free (AOwn field location chunk)
| SFExists t body : stack_free body -> stack_free (AExists t body)
| SFForall t body : stack_free body -> stack_free (AForall t body)
| SFIte condition then_branch else_branch :
    stack_free then_branch -> stack_free else_branch ->
    stack_free (AIte condition then_branch else_branch)
| SFInvariant invariant args : stack_free (AInvariant invariant args)
| SFPredicate predicate args : stack_free (APredicate predicate args)
| SFAnd left right :
    stack_free left -> stack_free right -> stack_free (AAnd left right).

(** Structural change of the phantom program-variable context for contracts.
    There deliberately is no [AStack] case: procedure contracts are required
    to be stack-free. *)
Inductive reindex_stack_context {F Δ} :
    forall {Γ Γ'}, assertion Γ F Δ -> assertion Γ' F Δ -> Prop :=
| RSCExpr Γ Γ' condition :
    reindex_stack_context (@AExpr Γ F Δ condition)
      (@AExpr Γ' F Δ condition)
| RSCPure Γ Γ' proposition :
    reindex_stack_context (@APure Γ F Δ proposition)
      (@APure Γ' F Δ proposition)
| RSCOwn Γ Γ' field location chunk :
    reindex_stack_context (@AOwn Γ F Δ field location chunk)
      (@AOwn Γ' F Δ field location chunk)
| RSCExists Γ Γ' t body body' :
    @reindex_stack_context F (t :: Δ) Γ Γ' body body' ->
    reindex_stack_context (AExists t body) (AExists t body')
| RSCForall Γ Γ' t body body' :
    @reindex_stack_context F (t :: Δ) Γ Γ' body body' ->
    reindex_stack_context (AForall t body) (AForall t body')
| RSCIte Γ Γ' condition (then_branch else_branch : assertion Γ F Δ)
    (then_branch' else_branch' : assertion Γ' F Δ) :
    reindex_stack_context then_branch then_branch' ->
    reindex_stack_context else_branch else_branch' ->
    reindex_stack_context (AIte condition then_branch else_branch)
      (AIte condition then_branch' else_branch')
| RSCInvariant Γ Γ' invariant args :
    reindex_stack_context (@AInvariant Γ F Δ invariant args)
      (@AInvariant Γ' F Δ invariant args)
| RSCPredicate Γ Γ' predicate args :
    reindex_stack_context (@APredicate Γ F Δ predicate args)
      (@APredicate Γ' F Δ predicate args)
| RSCAnd Γ Γ' (left right : assertion Γ F Δ)
    (left' right' : assertion Γ' F Δ) :
    reindex_stack_context left left' ->
    reindex_stack_context right right' ->
    reindex_stack_context (AAnd left right) (AAnd left' right').

Fixpoint rename_bound_assertion {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ') (formula : assertion Γ F Δ) :
    assertion Γ F Δ' :=
  match formula with
  | AStack store => AStack (rename_bound_store renaming store)
  | AExpr condition => AExpr (rename_bound_expr renaming condition)
  | APure proposition => APure proposition
  | AOwn field location chunk =>
      AOwn field (rename_bound_expr renaming location)
        (rename_bound_expr renaming chunk)
  | AExists t body =>
      AExists t (rename_bound_assertion (lift_bound_renaming renaming) body)
  | AForall t body =>
      AForall t (rename_bound_assertion (lift_bound_renaming renaming) body)
  | AIte condition then_branch else_branch =>
      AIte (rename_bound_expr renaming condition)
        (rename_bound_assertion renaming then_branch)
        (rename_bound_assertion renaming else_branch)
  | AInvariant invariant args =>
      AInvariant invariant (rename_bound_expr_list renaming args)
  | APredicate predicate args =>
      APredicate predicate (rename_bound_expr_list renaming args)
  | AAnd left_formula right_formula =>
      AAnd (rename_bound_assertion renaming left_formula)
        (rename_bound_assertion renaming right_formula)
  end.

Definition weaken_assertion {Γ F Δ u} (formula : assertion Γ F Δ) :
    assertion Γ F (u :: Δ) :=
  rename_bound_assertion weaken_bound_renaming formula.

Fixpoint subst_bound_expr_list {F Δ Δ' ts}
    (substitution : bound_subst F Δ Δ') (expressions : expr_list F Δ ts) :
    expr_list F Δ' ts :=
  match expressions with
  | ExprNil => ExprNil
  | ExprCons expression expressions' =>
      ExprCons (subst_bound_expr substitution expression)
        (subst_bound_expr_list substitution expressions')
  end.

(** Substitution by arbitrary expressions is partial only at [AStack], for
    the same reason as formal contract instantiation.  Binder renaming and
    weakening above remain total on stack assertions. *)
Fixpoint subst_bound_assertion {Γ F Δ Δ'}
    (substitution : bound_subst F Δ Δ') (formula : assertion Γ F Δ) :
    option (assertion Γ F Δ') :=
  match formula with
  | AStack _ => None
  | AExpr condition => Some (AExpr (subst_bound_expr substitution condition))
  | APure proposition => Some (APure proposition)
  | AOwn field location chunk =>
      Some (AOwn field (subst_bound_expr substitution location)
        (subst_bound_expr substitution chunk))
  | AExists t body =>
      match subst_bound_assertion (lift_bound_subst substitution) body with
      | Some body' => Some (AExists t body')
      | None => None
      end
  | AForall t body =>
      match subst_bound_assertion (lift_bound_subst substitution) body with
      | Some body' => Some (AForall t body')
      | None => None
      end
  | AIte condition then_branch else_branch =>
      match subst_bound_assertion substitution then_branch,
            subst_bound_assertion substitution else_branch with
      | Some then_branch', Some else_branch' =>
          Some (AIte (subst_bound_expr substitution condition)
            then_branch' else_branch')
      | _, _ => None
      end
  | AInvariant invariant args =>
      Some (AInvariant invariant (subst_bound_expr_list substitution args))
  | APredicate predicate args =>
      Some (APredicate predicate (subst_bound_expr_list substitution args))
  | AAnd left_formula right_formula =>
      match subst_bound_assertion substitution left_formula,
            subst_bound_assertion substitution right_formula with
      | Some left_formula', Some right_formula' =>
          Some (AAnd left_formula' right_formula')
      | _, _ => None
      end
  end.

Definition instantiate_bound_assertion {Γ F Δ t}
    (witness : expr F Δ t) (body : assertion Γ F (t :: Δ)) :
    option (assertion Γ F Δ) :=
  subst_bound_assertion (head_bound_subst witness) body.

Lemma stack_free_subst_bound {Γ F Δ Δ'}
    (substitution : bound_subst F Δ Δ') (formula : assertion Γ F Δ) :
  stack_free formula ->
  exists formula', subst_bound_assertion substitution formula = Some formula'.
Proof.
  intros Hfree. revert Δ' substitution.
  induction Hfree; intros Δ' substitution; simpl; eauto.
  - destruct (IHHfree _ (lift_bound_subst substitution)) as [body' ->]. eauto.
  - destruct (IHHfree _ (lift_bound_subst substitution)) as [body' ->]. eauto.
  - destruct (IHHfree1 _ substitution) as [then_branch' ->].
    destruct (IHHfree2 _ substitution) as [else_branch' ->]. eauto.
  - destruct (IHHfree1 _ substitution) as [left' ->].
    destruct (IHHfree2 _ substitution) as [right' ->]. eauto.
Qed.

Fixpoint subst_formals_expr_list {F F' Δ ts}
    (substitution : formal_subst F F' Δ) (expressions : expr_list F Δ ts) :
    expr_list F' Δ ts :=
  match expressions with
  | ExprNil => ExprNil
  | ExprCons expression expressions' =>
      ExprCons (subst_formals_expr substitution expression)
        (subst_formals_expr_list substitution expressions')
  end.

(** Contract instantiation is intentionally partial on [AStack].  A stack
    maps program variables to references, while actual formal arguments are
    arbitrary expressions.  Contracts are required to be [stack_free], so
    silently inventing a lossy substitution operation for proof-state stacks
    would buy no expressiveness and would weaken the representation. *)
Fixpoint subst_formals_assertion {Γ F F' Δ}
    (substitution : formal_subst F F' Δ) (formula : assertion Γ F Δ) :
    option (assertion Γ F' Δ) :=
  match formula with
  | AStack _ => None
  | AExpr condition => Some (AExpr (subst_formals_expr substitution condition))
  | APure proposition => Some (APure proposition)
  | AOwn field location chunk =>
      Some (AOwn field (subst_formals_expr substitution location)
        (subst_formals_expr substitution chunk))
  | AExists t body =>
      match subst_formals_assertion (lift_formal_subst substitution) body with
      | Some body' => Some (AExists t body')
      | None => None
      end
  | AForall t body =>
      match subst_formals_assertion (lift_formal_subst substitution) body with
      | Some body' => Some (AForall t body')
      | None => None
      end
  | AIte condition then_branch else_branch =>
      match subst_formals_assertion substitution then_branch,
            subst_formals_assertion substitution else_branch with
      | Some then_branch', Some else_branch' =>
          Some (AIte (subst_formals_expr substitution condition)
            then_branch' else_branch')
      | _, _ => None
      end
  | AInvariant invariant args =>
      Some (AInvariant invariant (subst_formals_expr_list substitution args))
  | APredicate predicate args =>
      Some (APredicate predicate (subst_formals_expr_list substitution args))
  | AAnd left_formula right_formula =>
      match subst_formals_assertion substitution left_formula,
            subst_formals_assertion substitution right_formula with
      | Some left_formula', Some right_formula' =>
          Some (AAnd left_formula' right_formula')
      | _, _ => None
      end
  end.

Lemma stack_free_subst_formals {Γ F F' Δ}
    (substitution : formal_subst F F' Δ) (formula : assertion Γ F Δ) :
  stack_free formula ->
  exists formula', subst_formals_assertion substitution formula = Some formula'.
Proof.
  intros Hfree. revert F' substitution.
  induction Hfree; intros F' substitution; simpl; eauto.
  - destruct (IHHfree _ (lift_formal_subst substitution)) as [body' ->].
    eauto.
  - destruct (IHHfree _ (lift_formal_subst substitution)) as [body' ->].
    eauto.
  - destruct (IHHfree1 _ substitution) as [then_branch' ->].
    destruct (IHHfree2 _ substitution) as [else_branch' ->]. eauto.
  - destruct (IHHfree1 _ substitution) as [left' ->].
    destruct (IHHfree2 _ substitution) as [right' ->]. eauto.
Qed.

End Make.
End TypedAssertion.

Module TypedAssertionExamples.

Module UnitRA := TypedCoreExamples.UnitRA.

Module TinyLogic <: TypedAssertion.LOGIC_SIGNATURE.
  Definition field_type (_ : TypedCore.field_id) := TypedCore.TInt.
  Definition predicate_args (_ : TypedCore.pred_id) :=
    [TypedCore.TRef; TypedCore.TInt].
  Definition invariant_args (_ : TypedCore.inv_id) :=
    [TypedCore.TRef].
End TinyLogic.

Module Assertions := TypedAssertion.Make UnitRA TinyLogic.
Import TypedCore Assertions.Core Assertions.

Definition empty_store : symbolic_store [] [] [] :=
  StoreNil.

Definition scoped_existential : assertion [] [] [] :=
  AExists TInt
    (AExpr
      (EBinOp (BEq TInt)
        (ERef (RefBound MHere))
        (EVal (VInt 0%Z)))).

Example scoped_existential_is_stack_free :
  stack_free scoped_existential.
Proof. repeat constructor. Qed.

End TypedAssertionExamples.
