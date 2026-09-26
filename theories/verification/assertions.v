From Coq Require Import List PArith Program.Equality ProofIrrelevance
  Logic.FunctionalExtensionality String ZArith Lia.

From raven Require Import verification.expressions.

Import ListNotations.
Open Scope list_scope.

(** Scoped assertions over the typed expression foundation. *)
Module TypedAssertion.

Module Type LOGIC_SIGNATURE.
  Parameter field_type : TypedCore.field_id -> TypedCore.typ.
  Parameter predicate_args : TypedCore.pred_id -> TypedCore.context.
  Parameter invariant_args : TypedCore.inv_id -> TypedCore.context.
  (** A procedure identifier determines its argument context and return
      type, exactly as an invariant or predicate identifier determines its
      argument context.  This lets [TCall] and [TSpawn] force arity the way
      [TUnfold] already does, and makes a table entry's formals
      definitionally the declared ones. *)
  Parameter procedure_args : TypedCore.proc_id -> TypedCore.context.
  Parameter procedure_return : TypedCore.proc_id -> TypedCore.typ.
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

Fixpoint expr_list_entry_free {F Δ ts}
    (expressions : expr_list F Δ ts) : Prop :=
  match expressions with
  | ExprNil => True
  | ExprCons head tail => expr_entry_free head /\ expr_list_entry_free tail
  end.

Fixpoint expr_list_append {F Δ left_types right_types}
    (left : expr_list F Δ left_types) (right : expr_list F Δ right_types) :
    expr_list F Δ (left_types ++ right_types) :=
  match left with
  | ExprNil => right
  | ExprCons expression tail =>
      ExprCons expression (expr_list_append tail right)
  end.

Fixpoint lookup_expr_list {F Δ ts t} (expressions : expr_list F Δ ts)
    (variable : member ts t) : expr F Δ t.
Proof.
  destruct expressions.
  - inversion variable.
  - dependent destruction variable.
    + exact e.
    + exact (@lookup_expr_list F Δ _ _ expressions variable).
Defined.

Lemma lookup_expr_list_here {F Δ t ts} (expression : expr F Δ t)
    (expressions : expr_list F Δ ts) :
  lookup_expr_list (ExprCons expression expressions) MHere = expression.
Proof.
  unfold lookup_expr_list, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl).
  reflexivity.
Defined.

(** Decidable equality for argument vectors, lifted from [expr_eqb].  The
    comparison is heterogeneous in the declaration context so that a
    two-way [match] never has to refine both sides at once; the
    characterisation lemma is stated at a single context, which is the
    only form the normalization layer needs. *)
Fixpoint expr_list_eqb {F Δ ts1} (l1 : expr_list F Δ ts1)
    {ts2} (l2 : expr_list F Δ ts2) {struct l1} : bool :=
  match l1, l2 with
  | ExprNil, ExprNil => true
  | ExprCons head1 rest1, ExprCons head2 rest2 =>
      expr_eqb head1 head2 && expr_list_eqb rest1 rest2
  | _, _ => false
  end.

Lemma expr_list_eqb_refl {F Δ ts} (l : expr_list F Δ ts) :
  expr_list_eqb l l = true.
Proof.
  induction l; simpl; [reflexivity |].
  rewrite expr_eqb_refl. exact IHl.
Qed.

Lemma expr_list_eqb_eq {F Δ ts} (l1 l2 : expr_list F Δ ts) :
  expr_list_eqb l1 l2 = true -> l1 = l2.
Proof.
  revert l2. induction l1; intros l2; dependent destruction l2; simpl;
    [ intros _; reflexivity |].
  intros Heq. apply andb_prop in Heq as [Hhead Hrest].
  rewrite (expr_eqb_eq _ _ Hhead). f_equal. exact (IHl1 _ Hrest).
Qed.

Global Instance expr_list_eq_dec F Δ ts :
    stdpp.base.EqDecision (expr_list F Δ ts).
Proof.
  intros l1 l2. destruct (expr_list_eqb l1 l2) eqn:Heq.
  - left. exact (expr_list_eqb_eq l1 l2 Heq).
  - right. intros ->. rewrite expr_list_eqb_refl in Heq. discriminate.
Defined.

Inductive assertion (Γ F Δ : context) : Type :=
| AStack (store : symbolic_store Γ F Δ)
| AExpr (condition : expr F Δ TBool)
| APure (proposition : Prop)
| AOwn (field : field_id) (location : expr F Δ TRef)
    (chunk : expr F Δ (Logic.field_type field))
| AGhostOwn (field : field_id) (location : expr F Δ TRef)
    (chunk : expr F Δ (Logic.field_type field))
| AFpuAllowed t (old_chunk new_chunk : expr F Δ t)
| ARAValid t (chunk : expr F Δ t)
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
Arguments AGhostOwn {_ _ _} _ _ _.
Arguments AFpuAllowed {_ _ _} _ _ _.
Arguments ARAValid {_ _ _} _ _.
Arguments AExists {_ _ _} _ _.
Arguments AForall {_ _ _} _ _.
Arguments AIte {_ _ _} _ _ _.
Arguments AInvariant {_ _ _} _ _.
Arguments APredicate {_ _ _} _ _.
Arguments AAnd {_ _ _} _ _.

Fixpoint store_entry_free {Γ F Δ}
    (store : symbolic_store Γ F Δ) : Prop :=
  match store with
  | StoreNil => True
  | StoreCons reference tail =>
      ref_entry_free reference /\ store_entry_free tail
  end.

Fixpoint assertion_entry_free {Γ F Δ}
    (formula : assertion Γ F Δ) : Prop :=
  match formula with
  | AStack store => store_entry_free store
  | AExpr condition => expr_entry_free condition
  | APure _ => True
  | AOwn _ location chunk | AGhostOwn _ location chunk =>
      expr_entry_free location /\ expr_entry_free chunk
  | AFpuAllowed _ old_chunk new_chunk =>
      expr_entry_free old_chunk /\ expr_entry_free new_chunk
  | ARAValid _ chunk => expr_entry_free chunk
  | AExists _ body | AForall _ body => assertion_entry_free body
  | AIte condition then_branch else_branch =>
      expr_entry_free condition /\ assertion_entry_free then_branch /\
        assertion_entry_free else_branch
  | AInvariant _ args | APredicate _ args => expr_list_entry_free args
  | AAnd left_formula right_formula =>
      assertion_entry_free left_formula /\ assertion_entry_free right_formula
  end.

(** An assertion with an explicit outer existential telescope.  The residual
    assertion may still contain existentials below genuine normalization
    barriers (currently universal binders); the prenex normalizer only moves
    the accessible existential prefix represented here. *)
Inductive existential_prenex (Γ F Δ : context) : Type :=
| PrenexBody (body : assertion Γ F Δ)
| PrenexExists t (body : existential_prenex Γ F (t :: Δ)).

Arguments PrenexBody {_ _ _} _.
Arguments PrenexExists {_ _ _} _ _.

Fixpoint interp_existential_prenex {Γ F Δ}
    (prenex : existential_prenex Γ F Δ) : assertion Γ F Δ :=
  match prenex with
  | PrenexBody body => body
  | PrenexExists t body => AExists t (interp_existential_prenex body)
  end.

(** The number of owned symbolic stacks in an assertion.  Conditional
    branches are alternatives, so their contribution is their maximum rather
    than their sum. *)
Fixpoint assertion_stack_count {Γ F Δ} (formula : assertion Γ F Δ) : nat :=
  match formula with
  | AStack _ => 1
  | AExpr _ | APure _ | AOwn _ _ _ | AGhostOwn _ _ _
  | AFpuAllowed _ _ _ | ARAValid _ _ | AInvariant _ _ | APredicate _ _ => 0
  | AExists _ body | AForall _ body => assertion_stack_count body
  | AIte _ then_branch else_branch =>
      Nat.max (assertion_stack_count then_branch)
        (assertion_stack_count else_branch)
  | AAnd left_formula right_formula =>
      assertion_stack_count left_formula + assertion_stack_count right_formula
  end.

Definition assertion_stack_linear {Γ F Δ} (formula : assertion Γ F Δ) : Prop :=
  assertion_stack_count formula <= 1.

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

Definition singleton_bound_subst {F Δ t}
    (reference : value_ref F Δ t) : bound_subst F [t] Δ.
Proof.
  intros u variable.
  refine (match view_member variable in member_view u' variable'
    return expr F Δ u' with
  | MVHere => ERef reference
  | MVThere impossible => match impossible with end
  end).
Defined.

Lemma singleton_bound_subst_here {F Δ t}
    (reference : value_ref F Δ t) :
  singleton_bound_subst reference t MHere = ERef reference.
Proof.
  unfold singleton_bound_subst. rewrite view_member_here. reflexivity.
Qed.

Global Opaque singleton_bound_subst.

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

Lemma lift_bound_subst_ext {F Δ Δ' u}
    (left right : bound_subst F Δ Δ')
    (Hequal : forall t (variable : bvar Δ t),
      left t variable = right t variable) :
  forall t (variable : bvar (u :: Δ) t),
    lift_bound_subst left t variable = lift_bound_subst right t variable.
Proof.
  intros t variable. dependent destruction variable.
  - unfold lift_bound_subst. rewrite view_member_here. reflexivity.
  - unfold lift_bound_subst. rewrite view_member_there.
    rewrite Hequal. reflexivity.
Qed.

Lemma subst_bound_ref_ext {F Δ Δ' t}
    (left right : bound_subst F Δ Δ')
    (Hequal : forall t (variable : bvar Δ t),
      left t variable = right t variable)
    (reference : value_ref F Δ t) :
  subst_bound_ref left reference = subst_bound_ref right reference.
Proof. destruct reference; simpl; try reflexivity. apply Hequal. Qed.

Lemma subst_bound_ref_singleton_here {F Δ t}
    (reference : value_ref F Δ t) :
  subst_bound_ref (singleton_bound_subst reference) (RefBound MHere) =
    ERef reference.
Proof. simpl. apply singleton_bound_subst_here. Qed.

Lemma subst_bound_expr_ext {F Δ Δ' t}
    (left right : bound_subst F Δ Δ')
    (Hequal : forall t (variable : bvar Δ t),
      left t variable = right t variable)
    (expression : expr F Δ t) :
  subst_bound_expr left expression = subst_bound_expr right expression.
Proof.
  induction expression; simpl.
  - apply subst_bound_ref_ext. exact Hequal.
  - reflexivity.
  - rewrite IHexpression. reflexivity.
  - rewrite IHexpression1, IHexpression2. reflexivity.
Qed.

Lemma subst_bound_expr_singleton_here {F Δ t}
    (reference : value_ref F Δ t) :
  subst_bound_expr (singleton_bound_subst reference)
    (ERef (RefBound MHere)) = ERef reference.
Proof. apply subst_bound_ref_singleton_here. Qed.

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

(** Exchange two adjacent logical binders.  This is the structural operation
    needed to choose a canonical order for heterogeneous prenex telescopes. *)
Definition exchange_bound_renaming {Δ t u} :
    bound_renaming (t :: u :: Δ) (u :: t :: Δ) :=
  fun result variable =>
    match view_member variable with
    | MVHere => MThere MHere
    | MVThere variable' =>
        match view_member variable' with
        | MVHere => MHere
        | MVThere variable'' => MThere (MThere variable'')
        end
    end.

Lemma exchange_bound_renaming_here {Δ t u} :
  @exchange_bound_renaming Δ t u t MHere = MThere MHere.
Proof.
  unfold exchange_bound_renaming. rewrite view_member_here. reflexivity.
Qed.

Lemma exchange_bound_renaming_there_here {Δ t u} :
  @exchange_bound_renaming Δ t u u (MThere MHere) = MHere.
Proof.
  unfold exchange_bound_renaming.
  rewrite view_member_there, view_member_here. reflexivity.
Qed.

Lemma exchange_bound_renaming_there_there {Δ t u result}
    (variable : bvar Δ result) :
  @exchange_bound_renaming Δ t u result (MThere (MThere variable)) =
    MThere (MThere variable).
Proof.
  unfold exchange_bound_renaming. rewrite !view_member_there. reflexivity.
Qed.

(** Total, stack-safe existential instantiation by a bound variable. *)
Definition head_bound_renaming {Δ t} (witness : bvar Δ t) :
    bound_renaming (t :: Δ) Δ :=
  fun u variable =>
    match view_member variable with
    | MVHere => witness
    | MVThere variable' => variable'
    end.

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

Definition bound_renaming_injective {Δ Δ'}
    (renaming : bound_renaming Δ Δ') : Prop :=
  forall t (left right : bvar Δ t),
    renaming t left = renaming t right -> left = right.

(** Equality of two argument vectors under a boolean side condition.
    Used by invariant-instance agreement; independent of any calculus. *)
Inductive expr_list_equal_assuming {F Δ}
    (condition : expr F Δ TBool) : forall ts,
    expr_list F Δ ts -> expr_list F Δ ts -> Prop :=
| ExprListEqualNil : expr_list_equal_assuming condition [] ExprNil ExprNil
| ExprListEqualCons t ts
    (left_head right_head : expr F Δ t)
    (left_tail right_tail : expr_list F Δ ts) :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms condition = Some (VBool true) ->
      interp_expr formals binders atoms left_head =
        interp_expr formals binders atoms right_head) ->
    expr_list_equal_assuming condition ts left_tail right_tail ->
    expr_list_equal_assuming condition (t :: ts)
      (ExprCons left_head left_tail) (ExprCons right_head right_tail).

Lemma expr_list_equal_assuming_sym {F Δ ts}
    (condition : expr F Δ TBool) (left right : expr_list F Δ ts) :
  expr_list_equal_assuming condition ts left right ->
  expr_list_equal_assuming condition ts right left.
Proof.
  intros Hequal. induction Hequal.
  - apply ExprListEqualNil.
  - apply ExprListEqualCons.
    + intros formals binders atoms Hcondition.
      symmetry. apply H. exact Hcondition.
    + exact IHHequal.
Qed.

(** Composition and identity for binder renamings, kept with
    [rename_bound_expr] and [rename_bound_store] so the resource core can
    reuse them directly. *)

Lemma lift_bound_renaming_here {Δ Δ' u}
    (renaming : bound_renaming Δ Δ') :
  lift_bound_renaming renaming u MHere = MHere.
Proof.
  unfold lift_bound_renaming. rewrite view_member_here. reflexivity.
Qed.

Lemma lift_bound_renaming_there {Δ Δ' u t}
    (renaming : bound_renaming Δ Δ') (variable : bvar Δ t) :
  lift_bound_renaming (u := u) renaming t (MThere variable) =
    MThere (renaming t variable).
Proof.
  unfold lift_bound_renaming. rewrite view_member_there. reflexivity.
Qed.

Definition compose_bound_renaming {Δ Δ' Δ''}
    (first : bound_renaming Δ Δ') (second : bound_renaming Δ' Δ'') :
    bound_renaming Δ Δ'' :=
  fun t variable => second t (first t variable).

Lemma lift_bound_renaming_compose {Δ Δ' Δ'' u}
    (first : bound_renaming Δ Δ') (second : bound_renaming Δ' Δ'') :
  compose_bound_renaming (lift_bound_renaming (u := u) first)
      (lift_bound_renaming second) =
    lift_bound_renaming (compose_bound_renaming first second).
Proof.
  apply functional_extensionality_dep; intro t.
  apply functional_extensionality; intro variable.
  dependent destruction variable.
  - unfold compose_bound_renaming, lift_bound_renaming.
    rewrite !view_member_here. reflexivity.
  - unfold compose_bound_renaming, lift_bound_renaming.
    rewrite !view_member_there. reflexivity.
Qed.

Lemma rename_bound_ref_compose {F Δ Δ' Δ'' t}
    (first : bound_renaming Δ Δ') (second : bound_renaming Δ' Δ'')
    (reference : value_ref F Δ t) :
  rename_bound_ref second (rename_bound_ref first reference) =
    rename_bound_ref (compose_bound_renaming first second) reference.
Proof. destruct reference; reflexivity. Qed.

Lemma rename_bound_expr_compose {F Δ Δ' Δ'' t}
    (first : bound_renaming Δ Δ') (second : bound_renaming Δ' Δ'')
    (expression : expr F Δ t) :
  rename_bound_expr second (rename_bound_expr first expression) =
    rename_bound_expr (compose_bound_renaming first second) expression.
Proof.
  induction expression; cbn [rename_bound_expr]; f_equal; auto.
  apply rename_bound_ref_compose.
Qed.

Lemma rename_bound_expr_list_compose {F Δ Δ' Δ'' ts}
    (first : bound_renaming Δ Δ') (second : bound_renaming Δ' Δ'')
    (expressions : expr_list F Δ ts) :
  rename_bound_expr_list second (rename_bound_expr_list first expressions) =
    rename_bound_expr_list (compose_bound_renaming first second) expressions.
Proof.
  induction expressions; cbn [rename_bound_expr_list]; f_equal; auto using
    rename_bound_expr_compose.
Qed.

Lemma rename_bound_store_compose {Γ F Δ Δ' Δ''}
    (first : bound_renaming Δ Δ') (second : bound_renaming Δ' Δ'')
    (store : symbolic_store Γ F Δ) :
  rename_bound_store second (rename_bound_store first store) =
    rename_bound_store (compose_bound_renaming first second) store.
Proof.
  induction store; cbn [rename_bound_store]; f_equal; auto using
    rename_bound_ref_compose.
Qed.

Definition identity_bound_renaming {Δ} : bound_renaming Δ Δ :=
  fun _ variable => variable.

Lemma lift_identity_bound_renaming {Δ u} :
    lift_bound_renaming (@identity_bound_renaming Δ) =
    (@identity_bound_renaming (u :: Δ)).
Proof.
  apply functional_extensionality_dep. intros t.
  apply functional_extensionality. intro variable.
  dependent destruction variable.
  - unfold lift_bound_renaming, identity_bound_renaming.
    rewrite view_member_here. reflexivity.
  - unfold lift_bound_renaming, identity_bound_renaming.
    rewrite view_member_there. reflexivity.
Qed.

Lemma rename_bound_ref_identity {F Δ t}
    (reference : value_ref F Δ t) :
  rename_bound_ref identity_bound_renaming reference = reference.
Proof. destruct reference; reflexivity. Qed.

Lemma rename_bound_expr_identity {F Δ t}
    (expression : expr F Δ t) :
  rename_bound_expr identity_bound_renaming expression = expression.
Proof.
  induction expression; cbn [rename_bound_expr identity_bound_renaming];
    try reflexivity.
  all: f_equal; auto using rename_bound_ref_identity.
Qed.

Lemma rename_bound_expr_list_identity {F Δ ts}
    (expressions : expr_list F Δ ts) :
  rename_bound_expr_list identity_bound_renaming expressions = expressions.
Proof.
  induction expressions; cbn [rename_bound_expr_list];
    try reflexivity.
  rewrite rename_bound_expr_identity, IHexpressions. reflexivity.
Qed.

Lemma rename_bound_store_identity {Γ F Δ}
    (store : symbolic_store Γ F Δ) :
  rename_bound_store identity_bound_renaming store = store.
Proof.
  induction store; cbn [rename_bound_store]; try reflexivity.
  rewrite rename_bound_ref_identity, IHstore. reflexivity.
Qed.

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
| SFGhostOwn field location chunk :
    stack_free (AGhostOwn field location chunk)
| SFFpuAllowed r old_chunk new_chunk :
    stack_free (AFpuAllowed r old_chunk new_chunk)
| SFRAValid t chunk : stack_free (ARAValid t chunk)
| SFExists t body : stack_free body -> stack_free (AExists t body)
| SFForall t body : stack_free body -> stack_free (AForall t body)
| SFIte condition then_branch else_branch :
    stack_free then_branch -> stack_free else_branch ->
    stack_free (AIte condition then_branch else_branch)
| SFInvariant invariant args : stack_free (AInvariant invariant args)
| SFPredicate predicate args : stack_free (APredicate predicate args)
| SFAnd left right :
    stack_free left -> stack_free right -> stack_free (AAnd left right).

Lemma stack_free_assertion_stack_count {Γ F Δ}
    (formula : assertion Γ F Δ) :
  stack_free formula -> assertion_stack_count formula = 0.
Proof.
  intro Hfree.
  induction Hfree; cbn; try reflexivity.
  - exact IHHfree.
  - exact IHHfree.
  - rewrite IHHfree1, IHHfree2. reflexivity.
  - rewrite IHHfree1, IHHfree2. reflexivity.
Qed.

Lemma assertion_stack_count_stack_free {Γ F Δ}
    (formula : assertion Γ F Δ) :
  assertion_stack_count formula = 0 -> stack_free formula.
Proof.
  induction formula; cbn; intro Hcount.
  - discriminate Hcount.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor. apply IHformula. exact Hcount.
  - constructor. apply IHformula. exact Hcount.
  - constructor.
    + apply IHformula1. lia.
    + apply IHformula2. lia.
  - constructor.
  - constructor.
  - constructor.
    + apply IHformula1. lia.
    + apply IHformula2. lia.
Qed.

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
| RSCGhostOwn Γ Γ' field location chunk :
    reindex_stack_context (@AGhostOwn Γ F Δ field location chunk)
      (@AGhostOwn Γ' F Δ field location chunk)
| RSCFpuAllowed Γ Γ' r old_chunk new_chunk :
    reindex_stack_context (@AFpuAllowed Γ F Δ r old_chunk new_chunk)
      (@AFpuAllowed Γ' F Δ r old_chunk new_chunk)
| RSCRAValid Γ Γ' t chunk :
    reindex_stack_context (@ARAValid Γ F Δ t chunk)
      (@ARAValid Γ' F Δ t chunk)
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

Lemma reindex_stack_context_functional {F Δ Γ Γ'}
    (source : assertion Γ F Δ) (right1 right2 : assertion Γ' F Δ) :
  reindex_stack_context source right1 ->
  reindex_stack_context source right2 ->
  right1 = right2.
Proof.
  intros H1.
  induction H1; intros H2;
    dependent destruction H2; try reflexivity.
  all: f_equal; eauto.
Qed.

Lemma reindex_stack_context_stack_free {F Δ Γ Γ'}
    (source : assertion Γ F Δ) (target : assertion Γ' F Δ) :
  reindex_stack_context source target -> stack_free source -> stack_free target.
Proof.
  intros Hreindex. induction Hreindex; intro Hfree;
    dependent destruction Hfree; constructor; eauto.
Qed.

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
  | AGhostOwn field location chunk =>
      AGhostOwn field (rename_bound_expr renaming location)
        (rename_bound_expr renaming chunk)
  | AFpuAllowed r old_chunk new_chunk =>
      AFpuAllowed r (rename_bound_expr renaming old_chunk)
        (rename_bound_expr renaming new_chunk)
  | ARAValid t chunk => ARAValid t (rename_bound_expr renaming chunk)
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

Lemma stack_free_rename_bound_assertion {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ') (formula : assertion Γ F Δ) :
  stack_free formula -> stack_free (rename_bound_assertion renaming formula).
Proof.
  intro Hfree. revert Δ' renaming.
  induction Hfree; intros Δ' renaming; cbn; constructor; eauto.
Qed.

Definition weaken_assertion {Γ F Δ u} (formula : assertion Γ F Δ) :
    assertion Γ F (u :: Δ) :=
  rename_bound_assertion weaken_bound_renaming formula.

Fixpoint rename_bound_existential_prenex {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (prenex : existential_prenex Γ F Δ) : existential_prenex Γ F Δ' :=
  match prenex with
  | PrenexBody body => PrenexBody (rename_bound_assertion renaming body)
  | PrenexExists t body =>
      PrenexExists t
        (rename_bound_existential_prenex
          (lift_bound_renaming renaming) body)
  end.

Definition weaken_existential_prenex {Γ F Δ u}
    (prenex : existential_prenex Γ F Δ) :
    existential_prenex Γ F (u :: Δ) :=
  rename_bound_existential_prenex weaken_bound_renaming prenex.

Lemma interp_rename_bound_existential_prenex {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (prenex : existential_prenex Γ F Δ) :
  interp_existential_prenex
      (rename_bound_existential_prenex renaming prenex) =
  rename_bound_assertion renaming (interp_existential_prenex prenex).
Proof.
  revert Δ' renaming.
  induction prenex; intros Δ' renaming; cbn.
  - reflexivity.
  - now rewrite (IHprenex _ (lift_bound_renaming renaming)).
Qed.

(** Pull the accessible existential prefix of the right operand across a
    fixed left operand. *)
Fixpoint existential_prenex_and_right {Γ F Δ}
    (left : assertion Γ F Δ) (right : existential_prenex Γ F Δ) :
    existential_prenex Γ F Δ :=
  match right with
  | PrenexBody right_body => PrenexBody (AAnd left right_body)
  | PrenexExists t right_body =>
      PrenexExists t
        (existential_prenex_and_right (weaken_assertion left) right_body)
  end.

(** Merge two existential prefixes in deterministic source order: binders
    originating in the left operand precede those from the right operand. *)
Fixpoint existential_prenex_and {Γ F Δ}
    (left right : existential_prenex Γ F Δ) :
    existential_prenex Γ F Δ :=
  match left with
  | PrenexBody left_body => existential_prenex_and_right left_body right
  | PrenexExists t left_body =>
      PrenexExists t
        (existential_prenex_and left_body
          (weaken_existential_prenex right))
  end.

Fixpoint existential_prenex_ite_else {Γ F Δ}
    (condition : expr F Δ TBool) (then_branch : assertion Γ F Δ)
    (else_branch : existential_prenex Γ F Δ) :
    existential_prenex Γ F Δ :=
  match else_branch with
  | PrenexBody else_body => PrenexBody (AIte condition then_branch else_body)
  | PrenexExists t else_body =>
      PrenexExists t
        (existential_prenex_ite_else (weaken_expr condition)
          (weaken_assertion then_branch) else_body)
  end.

(** Merge conditional branch prefixes in deterministic source order.  The
    then-branch binders precede the else-branch binders. *)
Fixpoint existential_prenex_ite {Γ F Δ}
    (condition : expr F Δ TBool)
    (then_branch else_branch : existential_prenex Γ F Δ) :
    existential_prenex Γ F Δ :=
  match then_branch with
  | PrenexBody then_body =>
      existential_prenex_ite_else condition then_body else_branch
  | PrenexExists t then_body =>
      PrenexExists t
        (existential_prenex_ite (weaken_expr condition) then_body
          (weaken_existential_prenex else_branch))
  end.

(** Existential-front normalization.  Universal binders are genuine barriers:
    their bodies are normalized recursively, but their existential prefixes
    are not moved across the universal. *)
Fixpoint normalize_existential_prenex {Γ F Δ}
    (formula : assertion Γ F Δ) : existential_prenex Γ F Δ :=
  match formula with
  | AExists t body => PrenexExists t (normalize_existential_prenex body)
  | AForall t body =>
      PrenexBody (AForall t
        (interp_existential_prenex (normalize_existential_prenex body)))
  | AIte condition then_branch else_branch =>
      existential_prenex_ite condition
        (normalize_existential_prenex then_branch)
        (normalize_existential_prenex else_branch)
  | AAnd left_formula right_formula =>
      existential_prenex_and
        (normalize_existential_prenex left_formula)
        (normalize_existential_prenex right_formula)
  | other => PrenexBody other
  end.

Lemma rename_bound_assertion_stack_count {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ') (formula : assertion Γ F Δ) :
  assertion_stack_count (rename_bound_assertion renaming formula) =
    assertion_stack_count formula.
Proof.
  revert Δ' renaming.
  induction formula; intros Δ' renaming; cbn; try reflexivity.
  - rewrite IHformula. reflexivity.
  - rewrite IHformula. reflexivity.
  - rewrite IHformula1, IHformula2. reflexivity.
  - rewrite IHformula1, IHformula2. reflexivity.
Qed.

Lemma weaken_assertion_stack_count {Γ F Δ u}
    (formula : assertion Γ F Δ) :
  assertion_stack_count (weaken_assertion (u := u) formula) =
    assertion_stack_count formula.
Proof.
  apply rename_bound_assertion_stack_count.
Qed.

Fixpoint subst_bound_expr_list {F Δ Δ' ts}
    (substitution : bound_subst F Δ Δ') (expressions : expr_list F Δ ts) :
    expr_list F Δ' ts :=
  match expressions with
  | ExprNil => ExprNil
  | ExprCons expression expressions' =>
      ExprCons (subst_bound_expr substitution expression)
        (subst_bound_expr_list substitution expressions')
  end.

Lemma subst_bound_expr_list_ext {F Δ Δ' ts}
    (left right : bound_subst F Δ Δ')
    (Hequal : forall t (variable : bvar Δ t),
      left t variable = right t variable)
    (expressions : expr_list F Δ ts) :
  subst_bound_expr_list left expressions =
    subst_bound_expr_list right expressions.
Proof.
  induction expressions as [|t ts expression expressions IH]; simpl;
    first reflexivity.
  rewrite (subst_bound_expr_ext left right Hequal expression).
  rewrite IH. reflexivity.
Qed.

Lemma subst_bound_expr_list_singleton_here {F Δ t}
    (reference : value_ref F Δ t) :
  subst_bound_expr_list (singleton_bound_subst reference)
    (ExprCons (ERef (RefBound MHere)) ExprNil) =
  ExprCons (ERef reference) ExprNil.
Proof.
  cbn [subst_bound_expr_list].
  rewrite subst_bound_expr_singleton_here. reflexivity.
Qed.

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
  | AGhostOwn field location chunk =>
      Some (AGhostOwn field (subst_bound_expr substitution location)
        (subst_bound_expr substitution chunk))
  | AFpuAllowed r old_chunk new_chunk =>
      Some (AFpuAllowed r (subst_bound_expr substitution old_chunk)
        (subst_bound_expr substitution new_chunk))
  | ARAValid t chunk =>
      Some (ARAValid t (subst_bound_expr substitution chunk))
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

Lemma subst_bound_assertion_ext {Γ F Δ Δ'}
    (left right : bound_subst F Δ Δ')
    (Hequal : forall t (variable : bvar Δ t),
      left t variable = right t variable)
    (formula : assertion Γ F Δ) :
  subst_bound_assertion left formula = subst_bound_assertion right formula.
Proof.
  revert Δ' left right Hequal.
  induction formula; intros Δ' left right Hequal; simpl.
  - reflexivity.
  - rewrite (subst_bound_expr_ext left right Hequal). reflexivity.
  - reflexivity.
  - rewrite !(subst_bound_expr_ext left right Hequal). reflexivity.
  - rewrite !(subst_bound_expr_ext left right Hequal). reflexivity.
  - rewrite !(subst_bound_expr_ext left right Hequal). reflexivity.
  - rewrite (subst_bound_expr_ext left right Hequal). reflexivity.
  - rewrite (IHformula _ (lift_bound_subst left) (lift_bound_subst right)).
    + reflexivity.
    + apply lift_bound_subst_ext. exact Hequal.
  - rewrite (IHformula _ (lift_bound_subst left) (lift_bound_subst right)).
    + reflexivity.
    + apply lift_bound_subst_ext. exact Hequal.
  - rewrite (subst_bound_expr_ext left right Hequal).
    rewrite (IHformula1 _ left right Hequal).
    rewrite (IHformula2 _ left right Hequal). reflexivity.
  - rewrite (subst_bound_expr_list_ext left right Hequal). reflexivity.
  - rewrite (subst_bound_expr_list_ext left right Hequal). reflexivity.
  - rewrite (IHformula1 _ left right Hequal).
    rewrite (IHformula2 _ left right Hequal). reflexivity.
Qed.

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

Lemma stack_free_subst_bound_result {Γ F Δ Δ'}
    (substitution : bound_subst F Δ Δ') (formula : assertion Γ F Δ) :
  stack_free formula ->
  forall target,
    subst_bound_assertion substitution formula = Some target ->
    stack_free target.
Proof.
  intro Hfree. revert Δ' substitution.
  induction Hfree; intros Δ' substitution target Hresult; simpl in Hresult.
  - inversion Hresult. constructor.
  - inversion Hresult. constructor.
  - inversion Hresult. constructor.
  - inversion Hresult. constructor.
  - inversion Hresult. constructor.
  - inversion Hresult. constructor.
  - destruct (subst_bound_assertion (lift_bound_subst substitution) body)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target. constructor.
    eapply IHHfree; eauto.
  - destruct (subst_bound_assertion (lift_bound_subst substitution) body)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target. constructor.
    eapply IHHfree; eauto.
  - destruct (subst_bound_assertion substitution then_branch)
      as [then_branch'|] eqn:Hthen; [|discriminate].
    destruct (subst_bound_assertion substitution else_branch)
      as [else_branch'|] eqn:Helse; [|discriminate].
    inversion Hresult; subst target. constructor.
    + eapply IHHfree1; eauto.
    + eapply IHHfree2; eauto.
  - inversion Hresult. constructor.
  - inversion Hresult. constructor.
  - destruct (subst_bound_assertion substitution left)
      as [left'|] eqn:Hleft; [|discriminate].
    destruct (subst_bound_assertion substitution right)
      as [right'|] eqn:Hright; [|discriminate].
    inversion Hresult; subst target. constructor.
    + eapply IHHfree1; eauto.
    + eapply IHHfree2; eauto.
Qed.

(** Bound substitution is deliberately undefined on [AStack].  Consequently,
    a successful logical instantiation certifies that both its source and its
    result are stack-free.  The source direction is useful when ruling out a
    proof-only existential introduction at a physical access boundary. *)
Lemma successful_subst_source_stack_free {Γ F Δ Δ'}
    (substitution : bound_subst F Δ Δ')
    (formula : assertion Γ F Δ) (target : assertion Γ F Δ') :
  subst_bound_assertion substitution formula = Some target ->
  stack_free formula.
Proof.
  revert Δ' substitution target.
  induction formula; intros Δ' substitution target Hresult;
    cbn [subst_bound_assertion] in Hresult.
  - discriminate.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct (subst_bound_assertion (lift_bound_subst substitution) formula)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target. constructor.
    eapply IHformula; eauto.
  - destruct (subst_bound_assertion (lift_bound_subst substitution) formula)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target. constructor.
    eapply IHformula; eauto.
  - destruct (subst_bound_assertion substitution formula1)
      as [then_branch'|] eqn:Hthen; [|discriminate].
    destruct (subst_bound_assertion substitution formula2)
      as [else_branch'|] eqn:Helse; [|discriminate].
    inversion Hresult; subst target. constructor.
    + eapply IHformula1; eauto.
    + eapply IHformula2; eauto.
  - constructor.
  - constructor.
  - destruct (subst_bound_assertion substitution formula1)
      as [left'|] eqn:Hleft; [|discriminate].
    destruct (subst_bound_assertion substitution formula2)
      as [right'|] eqn:Hright; [|discriminate].
    inversion Hresult; subst target. constructor.
    + eapply IHformula1; eauto.
    + eapply IHformula2; eauto.
Qed.

Lemma successful_subst_source_stack_count {Γ F Δ Δ'}
    (substitution : bound_subst F Δ Δ')
    (formula : assertion Γ F Δ) (target : assertion Γ F Δ') :
  subst_bound_assertion substitution formula = Some target ->
  assertion_stack_count formula = 0.
Proof.
  intro Hresult. apply stack_free_assertion_stack_count.
  eapply successful_subst_source_stack_free. exact Hresult.
Qed.

Lemma subst_bound_assertion_stack_count {Γ F Δ Δ'}
    (substitution : bound_subst F Δ Δ') (formula : assertion Γ F Δ)
    (target : assertion Γ F Δ') :
  subst_bound_assertion substitution formula = Some target ->
  assertion_stack_count target = assertion_stack_count formula.
Proof.
  revert Δ' substitution target.
  induction formula; intros Δ' substitution target Hresult;
    simpl in Hresult.
  - discriminate.
  - inversion Hresult. reflexivity.
  - inversion Hresult. reflexivity.
  - inversion Hresult. reflexivity.
  - inversion Hresult. reflexivity.
  - inversion Hresult. reflexivity.
  - inversion Hresult. reflexivity.
  - destruct (subst_bound_assertion (lift_bound_subst substitution) formula)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target. simpl.
    eapply IHformula; eauto.
  - destruct (subst_bound_assertion (lift_bound_subst substitution) formula)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target. simpl.
    eapply IHformula; eauto.
  - destruct (subst_bound_assertion substitution formula1)
      as [then_branch'|] eqn:Hthen; [|discriminate].
    destruct (subst_bound_assertion substitution formula2)
      as [else_branch'|] eqn:Helse; [|discriminate].
    inversion Hresult; subst target. simpl.
    rewrite (IHformula1 _ substitution _ Hthen),
      (IHformula2 _ substitution _ Helse). reflexivity.
  - inversion Hresult. reflexivity.
  - inversion Hresult. reflexivity.
  - destruct (subst_bound_assertion substitution formula1)
      as [left'|] eqn:Hleft; [|discriminate].
    destruct (subst_bound_assertion substitution formula2)
      as [right'|] eqn:Hright; [|discriminate].
    inversion Hresult; subst target. simpl.
    rewrite (IHformula1 _ substitution _ Hleft),
      (IHformula2 _ substitution _ Hright). reflexivity.
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
  | AGhostOwn field location chunk =>
      Some (AGhostOwn field (subst_formals_expr substitution location)
        (subst_formals_expr substitution chunk))
  | AFpuAllowed r old_chunk new_chunk =>
      Some (AFpuAllowed r (subst_formals_expr substitution old_chunk)
        (subst_formals_expr substitution new_chunk))
  | ARAValid t chunk =>
      Some (ARAValid t (subst_formals_expr substitution chunk))
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

Lemma stack_free_subst_formals_result {Γ F F' Δ}
    (substitution : formal_subst F F' Δ) (formula : assertion Γ F Δ) :
  stack_free formula ->
  forall target,
    subst_formals_assertion substitution formula = Some target ->
    stack_free target.
Proof.
  intro Hfree. revert F' substitution.
  induction Hfree; intros F' substitution target Hresult; simpl in Hresult.
  - inversion Hresult. constructor.
  - inversion Hresult. constructor.
  - inversion Hresult. constructor.
  - inversion Hresult. constructor.
  - inversion Hresult. constructor.
  - inversion Hresult. constructor.
  - destruct (subst_formals_assertion (lift_formal_subst substitution) body)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target. constructor.
    eapply IHHfree; eauto.
  - destruct (subst_formals_assertion (lift_formal_subst substitution) body)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target. constructor.
    eapply IHHfree; eauto.
  - destruct (subst_formals_assertion substitution then_branch)
      as [then_branch'|] eqn:Hthen; [|discriminate].
    destruct (subst_formals_assertion substitution else_branch)
      as [else_branch'|] eqn:Helse; [|discriminate].
    inversion Hresult; subst target. constructor.
    + eapply IHHfree1; eauto.
    + eapply IHHfree2; eauto.
  - inversion Hresult. constructor.
  - inversion Hresult. constructor.
  - destruct (subst_formals_assertion substitution left)
      as [left'|] eqn:Hleft; [|discriminate].
    destruct (subst_formals_assertion substitution right)
      as [right'|] eqn:Hright; [|discriminate].
    inversion Hresult; subst target. constructor.
    + eapply IHHfree1; eauto.
    + eapply IHHfree2; eauto.
Qed.


(* ------------------------------------------------------------------ *)
(** ** Structural entailment on assertions

    Moved here from [TypedHoare]: these rules mention only the assertion
    grammar, which the Hoare calculus of [hoare_rules.v]
    needs. *)



Inductive entailment_step {Γ F Δ} :
    assertion Γ F Δ -> assertion Γ F Δ -> Prop :=
| ESAndComm left right :
    entailment_step (AAnd left right) (AAnd right left)
| ESAndAssocR first second third :
    entailment_step (AAnd (AAnd first second) third)
      (AAnd first (AAnd second third))
| ESAndAssocL first second third :
    entailment_step (AAnd first (AAnd second third))
      (AAnd (AAnd first second) third)
| ESAndElimL left right : entailment_step (AAnd left right) left
| ESAndElimR left right : entailment_step (AAnd left right) right
| ESAndTrueIntro formula :
    entailment_step formula (AAnd formula (APure True))
| ESTrueIntro formula : entailment_step formula (APure True)
| ESPure (left right : Prop) :
    (left -> right) -> entailment_step (APure left) (APure right)
| ESIteTrue condition then_branch else_branch :
    entailment_step (AAnd (AIte condition then_branch else_branch)
      (AExpr condition)) then_branch
| ESIteFalse condition then_branch else_branch :
    entailment_step
      (AAnd (AIte condition then_branch else_branch)
        (AExpr (EUnOp UNot condition))) else_branch
| ESIteIntroTrue condition then_branch else_branch :
    stack_free else_branch ->
    entailment_step (AAnd then_branch (AExpr condition))
      (AIte condition then_branch else_branch)
| ESIteIntroFalse condition then_branch else_branch :
    stack_free then_branch ->
    entailment_step
      (AAnd else_branch (AExpr (EUnOp UNot condition)))
      (AIte condition then_branch else_branch)
| ESIteBoolTrue condition then_branch else_branch indicator :
    entailment_step
      (AAnd
        (AIte condition
          (AAnd then_branch
            (AExpr (EBinOp (BEq TBool) indicator (EVal (VBool true)))))
          (AAnd else_branch
            (AExpr (EBinOp (BEq TBool) indicator (EVal (VBool false))))))
        (AExpr indicator))
      (AAnd then_branch (AExpr condition))
| ESIteBoolFalse condition then_branch else_branch indicator :
    entailment_step
      (AAnd
        (AIte condition
          (AAnd then_branch
            (AExpr (EBinOp (BEq TBool) indicator (EVal (VBool true)))))
          (AAnd else_branch
            (AExpr (EBinOp (BEq TBool) indicator (EVal (VBool false))))))
        (AExpr (EUnOp UNot indicator)))
      else_branch
| ESExprImpl (left right : expr F Δ TBool) :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms left = Some (VBool true) ->
      interp_expr formals binders atoms right = Some (VBool true)) ->
    entailment_step (AExpr left) (AExpr right)
| ESExprTrue (expression : expr F Δ TBool) :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms expression = Some (VBool true)) ->
    entailment_step (APure True) (AExpr expression)
| ESRAValidTrue t (expression : expr F Δ t) :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env) value,
      interp_expr formals binders atoms expression = Some value ->
      tval_ra_valid value) ->
    entailment_step (APure True) (ARAValid t expression)
| ESFpuAllowedTrue t (old_expression new_expression : expr F Δ t) :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env) old_value new_value,
      interp_expr formals binders atoms old_expression = Some old_value ->
      interp_expr formals binders atoms new_expression = Some new_value ->
      tval_fpu_allowed old_value new_value) ->
    entailment_step (APure True)
      (AFpuAllowed t old_expression new_expression)
| ESOwnChunkEq field location left_chunk right_chunk :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms left_chunk =
        interp_expr formals binders atoms right_chunk) ->
    entailment_step (AOwn field location left_chunk)
      (AOwn field location right_chunk)
| ESGhostOwnChunkEq field location left_chunk right_chunk :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms left_chunk =
        interp_expr formals binders atoms right_chunk) ->
    entailment_step (AGhostOwn field location left_chunk)
      (AGhostOwn field location right_chunk)
| ESOwnChunkEqAssume field location left_chunk right_chunk condition :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms condition = Some (VBool true) ->
      interp_expr formals binders atoms left_chunk =
        interp_expr formals binders atoms right_chunk) ->
    entailment_step
      (AAnd (AOwn field location left_chunk) (AExpr condition))
      (AOwn field location right_chunk)
| ESGhostOwnChunkEqAssume field location left_chunk right_chunk condition :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms condition = Some (VBool true) ->
      interp_expr formals binders atoms left_chunk =
        interp_expr formals binders atoms right_chunk) ->
    entailment_step
      (AAnd (AGhostOwn field location left_chunk) (AExpr condition))
      (AGhostOwn field location right_chunk)
| ESInvariantArgumentsEqAssume invariant
    (left_arguments right_arguments :
      expr_list F Δ (Logic.invariant_args invariant))
    (condition : expr F Δ TBool) :
    expr_list_equal_assuming condition _ left_arguments right_arguments ->
    entailment_step
      (AAnd (AInvariant invariant left_arguments) (AExpr condition))
      (AInvariant invariant right_arguments)
| ESPredicateArgumentsEqAssume predicate
    (left_arguments right_arguments :
      expr_list F Δ (Logic.predicate_args predicate))
    (condition : expr F Δ TBool) :
    expr_list_equal_assuming condition _ left_arguments right_arguments ->
    entailment_step
      (AAnd (APredicate predicate left_arguments) (AExpr condition))
      (APredicate predicate right_arguments)
(** A thread's local stack is represented by an exclusive RA fragment.
    Expose that semantic fact to structural consequence reasoning so an
    impossible assertion containing two stack owners can close any branch. *)
| ESStackExclusive (left right : symbolic_store Γ F Δ) :
    entailment_step (AAnd (AStack left) (AStack right)) (APure False).

Inductive assertion_entails {Γ F} : forall {Δ},
    assertion Γ F Δ -> assertion Γ F Δ -> Prop :=
| EntailsRefl {Δ : context} (formula : assertion Γ F Δ) :
    assertion_entails formula formula
| EntailsStep {Δ : context} (left right : assertion Γ F Δ) :
    entailment_step left right ->
    assertion_entails left right
| EntailsTrans {Δ : context}
    (first second third : assertion Γ F Δ) :
    assertion_entails first second -> assertion_entails second third ->
    assertion_entails first third
| EntailsAndMono {Δ : context}
    (left left' right right' : assertion Γ F Δ) :
    assertion_entails left left' -> assertion_entails right right' ->
    assertion_entails (AAnd left right) (AAnd left' right')
| EntailsExistsMono {Δ : context} t (body body' : assertion Γ F (t :: Δ)) :
    assertion_entails body body' ->
    assertion_entails (AExists t body) (AExists t body')
| EntailsExistsIntro {Δ : context} t
    (body : assertion Γ F (t :: Δ)) witness
    (instantiated : assertion Γ F Δ) :
    instantiate_bound_assertion witness body = Some instantiated ->
    assertion_entails instantiated (AExists t body)
| EntailsExistsElim {Δ : context} t
    (body : assertion Γ F (t :: Δ))
    (conclusion : assertion Γ F Δ) :
    assertion_entails body (weaken_assertion conclusion) ->
    assertion_entails (AExists t body) conclusion
| EntailsExistsAndRight {Δ : context} t
    (body : assertion Γ F (t :: Δ)) (frame : assertion Γ F Δ) :
    assertion_entails
      (AAnd (AExists t body) frame)
      (AExists t (AAnd body (weaken_assertion frame)))
| EntailsExistsAndRightOut {Δ : context} t
    (body : assertion Γ F (t :: Δ)) (frame : assertion Γ F Δ) :
    assertion_entails
      (AExists t (AAnd body (weaken_assertion frame)))
      (AAnd (AExists t body) frame)
| EntailsAndExistsLeft {Δ : context} t (frame : assertion Γ F Δ)
    (body : assertion Γ F (t :: Δ)) :
    assertion_entails
      (AAnd frame (AExists t body))
      (AExists t (AAnd (weaken_assertion frame) body))
| EntailsIteMono {Δ : context} (condition : expr F Δ TBool)
    (then_branch then_branch' else_branch else_branch' : assertion Γ F Δ) :
    assertion_entails then_branch then_branch' ->
    assertion_entails else_branch else_branch' ->
    assertion_entails (AIte condition then_branch else_branch)
      (AIte condition then_branch' else_branch')
| EntailsExistsVacuousIntro {Δ : context} t
    (formula : assertion Γ F Δ) :
    assertion_entails formula (AExists t (weaken_assertion formula))
| EntailsExistsIteOut {Δ : context} t (condition : expr F Δ TBool)
    (then_branch else_branch : assertion Γ F (t :: Δ)) :
    assertion_entails
      (AExists t
        (AIte (weaken_expr condition) then_branch else_branch))
      (AIte condition (AExists t then_branch) (AExists t else_branch))
| EntailsIteExistsIn {Δ : context} t (condition : expr F Δ TBool)
    (then_branch else_branch : assertion Γ F (t :: Δ)) :
    assertion_entails
      (AIte condition (AExists t then_branch) (AExists t else_branch))
      (AExists t
        (AIte (weaken_expr condition) then_branch else_branch))
| EntailsExistsSwap {Δ : context} t u
    (body : assertion Γ F (u :: t :: Δ)) :
    assertion_entails
      (AExists t (AExists u body))
      (AExists u (AExists t
        (rename_bound_assertion
          (@exchange_bound_renaming Δ u t) body)))
| EntailsForallMono {Δ : context} t
    (body body' : assertion Γ F (t :: Δ)) :
    assertion_entails body body' ->
    assertion_entails (AForall t body) (AForall t body').

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
  Definition procedure_args (_ : TypedCore.proc_id) : TypedCore.context :=
    [TypedCore.TRef].
  Definition procedure_return (_ : TypedCore.proc_id) : TypedCore.typ :=
    TypedCore.TUnit.
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
