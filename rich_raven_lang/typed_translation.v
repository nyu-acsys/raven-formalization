From Coq Require Import List String Program.Equality Logic.FunctionalExtensionality.

From iris.bi Require Import bi derived_laws.
From iris.bi.lib Require Import fixpoint_mono.
From iris.proofmode Require Import tactics.

From raven_iris.rich_raven_lang Require Import
  typed_core typed_assertion typed_ir typed_hoare.

Import ListNotations.
Open Scope list_scope.

(** Iris interpretation of the typed Raven assertion language.

    This layer deliberately factors the binding-independent semantic bridge
    (physical heap ownership, invariant tokens, and predicate bodies) out of
    the syntax translation.  A concrete Raven model supplies that bridge;
    typed environments and binder extension are handled here. *)
Module TypedTranslation.

Import TypedCore TypedIR.

Module Make (RAs : RA_VALUE_CONFIG) (Logic : TypedAssertion.LOGIC_SIGNATURE).
Module Hoare := TypedHoare.Make RAs Logic.
Module IR := Hoare.IR.
Module Resource := IR.Resource.
Module Core := IR.Core.
Module Assertions := IR.Assertions.
Import Core Assertions IR.

Inductive tval_list : context -> Type :=
| TVNil : tval_list []
| TVCons t ts : tval t -> tval_list ts -> tval_list (t :: ts).

Arguments TVCons {_ _} _ _.

Fixpoint tval_list_append {left_types right_types}
    (left : tval_list left_types) (right : tval_list right_types) :
    tval_list (left_types ++ right_types) :=
  match left with
  | TVNil => right
  | TVCons value tail => TVCons value (tval_list_append tail right)
  end.

Lemma tval_list_append_injective {left_types right_types}
    (left left' : tval_list left_types)
    (right right' : tval_list right_types) :
  tval_list_append left right = tval_list_append left' right' ->
  left = left' /\ right = right'.
Proof.
  revert left' right right'. induction left as [|t ts value tail IH];
    intros left' right right' Hequal.
  - dependent destruction left'. split; [reflexivity | exact Hequal].
  - dependent destruction left'. simpl in Hequal.
    dependent destruction Hequal.
    destruct (IH left' right right' x) as [-> ->]. split; reflexivity.
Qed.

Inductive concrete_store : context -> Type :=
| ConcreteNil : concrete_store []
| ConcreteCons t Γ : tval t -> concrete_store Γ -> concrete_store (t :: Γ).

Arguments ConcreteCons {_ _} _ _.

Definition binder_cons {Δ t} (head : tval t) (tail : binder_env Δ) :
    binder_env (t :: Δ) :=
  fun u variable =>
    match view_member variable with
    | MVHere => head
    | MVThere variable' => tail _ variable'
    end.

Lemma binder_cons_here {Δ t} (head : tval t) (tail : binder_env Δ) :
  binder_cons head tail t MHere = head.
Proof. unfold binder_cons. rewrite view_member_here. reflexivity. Qed.

Lemma binder_cons_there {Δ t u} (head : tval u) (tail : binder_env Δ)
    (variable : bvar Δ t) :
  binder_cons head tail t (MThere variable) = tail t variable.
Proof. unfold binder_cons. rewrite view_member_there. reflexivity. Qed.

Lemma binder_cons_eta {Δ t} (binders : binder_env (t :: Δ)) :
  binder_cons (binders t MHere)
    (fun u (variable : bvar Δ u) => binders u (MThere variable)) = binders.
Proof.
  apply functional_extensionality_dep. intro u.
  apply functional_extensionality. intro variable.
  unfold binder_cons.
  destruct (view_member variable); reflexivity.
Qed.

Fixpoint interp_expr_list {F Δ ts}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (expressions : expr_list F Δ ts) : option (tval_list ts) :=
  match expressions with
  | ExprNil => Some TVNil
  | ExprCons expression expressions' =>
      match interp_expr formals binders atoms expression,
            interp_expr_list formals binders atoms expressions' with
      | Some value, Some values => Some (TVCons value values)
      | _, _ => None
      end
  end.

Lemma interp_expr_list_stable_atoms {F Δ ts}
    (formals : formal_env F) (binders : binder_env Δ)
    (left_atoms right_atoms : atom_env)
    (expressions : expr_list F Δ ts) :
  stable_atoms_agree left_atoms right_atoms ->
  Assertions.expr_list_entry_free expressions ->
  interp_expr_list formals binders left_atoms expressions =
    interp_expr_list formals binders right_atoms expressions.
Proof.
  intros Hagree Hfree.
  induction expressions as [|t ts expression expressions IH]; first reflexivity.
  destruct Hfree as [Hexpression Hexpressions]. simpl.
  rewrite (interp_expr_stable_atoms formals binders left_atoms right_atoms
    expression Hagree Hexpression).
  rewrite (IH Hexpressions). reflexivity.
Qed.

Lemma interp_expr_list_append {F Δ left_types right_types}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (left : expr_list F Δ left_types) (right : expr_list F Δ right_types) :
  interp_expr_list formals binders atoms
      (Assertions.expr_list_append left right) =
    match interp_expr_list formals binders atoms left,
          interp_expr_list formals binders atoms right with
    | Some left_values, Some right_values =>
        Some (tval_list_append left_values right_values)
    | _, _ => None
    end.
Proof.
  induction left as [|t ts expression tail IH]; simpl.
  - destruct (interp_expr_list formals binders atoms right); reflexivity.
  - rewrite IH.
    destruct (interp_expr formals binders atoms expression),
      (interp_expr_list formals binders atoms tail),
      (interp_expr_list formals binders atoms right); reflexivity.
Qed.

Lemma interp_expr_list_append_some {F Δ left_types right_types}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (left : expr_list F Δ left_types) (right : expr_list F Δ right_types)
    (left_values : tval_list left_types)
    (right_values : tval_list right_types) :
  interp_expr_list formals binders atoms left = Some left_values ->
  interp_expr_list formals binders atoms right = Some right_values ->
  interp_expr_list formals binders atoms
      (Assertions.expr_list_append left right) =
    Some (tval_list_append left_values right_values).
Proof.
  intros Hleft Hright. rewrite interp_expr_list_append Hleft Hright.
  reflexivity.
Qed.

Lemma interp_expr_list_append_some_inv {F Δ left_types right_types}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (left : expr_list F Δ left_types) (right : expr_list F Δ right_types)
    (left_values : tval_list left_types)
    (right_values : tval_list right_types) :
  interp_expr_list formals binders atoms
      (Assertions.expr_list_append left right) =
      Some (tval_list_append left_values right_values) ->
  interp_expr_list formals binders atoms left = Some left_values /\
  interp_expr_list formals binders atoms right = Some right_values.
Proof.
  rewrite interp_expr_list_append.
  destruct (interp_expr_list formals binders atoms left) as
    [actual_left |] eqn:Hleft; [|discriminate].
  destruct (interp_expr_list formals binders atoms right) as
    [actual_right |] eqn:Hright; [|discriminate].
  intro Hequal. injection Hequal as Hvalues.
  apply tval_list_append_injective in Hvalues as [-> ->].
  split; reflexivity.
Qed.

Lemma interp_expr_list_equal_assuming {F Δ ts}
    (condition : expr F Δ TBool) (left right : expr_list F Δ ts)
    (Hequal : Assertions.expr_list_equal_assuming condition ts left right)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (Hcondition : interp_expr formals binders atoms condition =
      Some (VBool true)) :
  interp_expr_list formals binders atoms left =
    interp_expr_list formals binders atoms right.
Proof.
  induction Hequal; simpl; first reflexivity.
  rewrite (H formals binders atoms Hcondition).
  rewrite IHHequal. reflexivity.
Qed.

Lemma interp_expr_list_total {F Δ ts} (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env)
    (expressions : expr_list F Δ ts) :
  exists values, interp_expr_list formals binders atoms expressions =
    Some values.
Proof.
  induction expressions as [|t ts expression expressions IH].
  - exists TVNil. reflexivity.
  - destruct (interp_expr_total formals binders atoms expression) as
      [value Hvalue].
    destruct IH as [values Hvalues].
    exists (TVCons value values). simpl. rewrite Hvalue. rewrite Hvalues.
    reflexivity.
Qed.

Fixpoint interp_store {Γ F Δ}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) : concrete_store Γ :=
  match store with
  | StoreNil => ConcreteNil
  | StoreCons reference tail =>
      ConcreteCons (interp_ref formals binders atoms reference)
        (interp_store formals binders atoms tail)
  end.

Lemma interp_store_stable_atoms {Γ F Δ}
    (formals : formal_env F) (binders : binder_env Δ)
    (left_atoms right_atoms : atom_env)
    (store : symbolic_store Γ F Δ) :
  stable_atoms_agree left_atoms right_atoms ->
  Assertions.store_entry_free store ->
  interp_store formals binders left_atoms store =
    interp_store formals binders right_atoms store.
Proof.
  intros Hagree Hfree.
  induction store as [|t Γ reference tail IH]; first reflexivity.
  destruct Hfree as [Hreference Htail]. simpl.
  rewrite (interp_ref_stable_atoms formals binders left_atoms right_atoms
    reference Hagree Hreference).
  rewrite (IH Htail). reflexivity.
Qed.

Definition interp_program_expr {Γ F Δ t}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (expression : pexpr Γ t) :
    option (tval t) :=
  interp_expr formals binders atoms (IR.symbolize_expr store expression).

Definition interp_program_expr_list {Γ F Δ ts}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (expressions : pexpr_list Γ ts) :
    option (tval_list ts) :=
  interp_expr_list formals binders atoms
    (IR.symbolize_expr_list store expressions).

(** Program-expression interpretation depends on a symbolic store only
    through the concrete store it denotes.  These extensionality lemmas are
    the semantic bridge used when a proof-only symbolic-store rewrite occurs
    at an invariant boundary. *)
Lemma interp_lookup_store_ext {Γ F Δ}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (left right : symbolic_store Γ F Δ) :
  interp_store formals binders atoms left =
    interp_store formals binders atoms right ->
  forall t (variable : pvar Γ t),
    interp_ref formals binders atoms (lookup_store left t variable) =
    interp_ref formals binders atoms (lookup_store right t variable).
Proof.
  intro Hstore. induction variable.
  - dependent destruction left. dependent destruction right.
    cbn in Hstore. injection Hstore as Hhead _.
    rewrite !lookup_store_here. exact Hhead.
  - dependent destruction left. dependent destruction right.
    cbn in Hstore. injection Hstore as _ Htail.
    rewrite !lookup_store_there. apply IHvariable.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ Htail).
Qed.

Lemma interp_program_expr_store_ext {Γ F Δ t}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (left right : symbolic_store Γ F Δ) (expression : pexpr Γ t) :
  interp_store formals binders atoms left =
    interp_store formals binders atoms right ->
  interp_program_expr formals binders atoms left expression =
    interp_program_expr formals binders atoms right expression.
Proof.
  intro Hstore. induction expression; cbn [interp_program_expr].
  - unfold interp_program_expr. cbn [IR.symbolize_expr interp_expr].
    f_equal. apply interp_lookup_store_ext. exact Hstore.
  - reflexivity.
  - unfold interp_program_expr in *.
    cbn [IR.symbolize_expr interp_expr] in *. now rewrite IHexpression.
  - unfold interp_program_expr in *.
    cbn [IR.symbolize_expr interp_expr] in *.
    rewrite IHexpression1. rewrite IHexpression2. reflexivity.
Qed.

Lemma interp_program_expr_list_store_ext {Γ F Δ ts}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (left right : symbolic_store Γ F Δ) (expressions : pexpr_list Γ ts) :
  interp_store formals binders atoms left =
    interp_store formals binders atoms right ->
  interp_program_expr_list formals binders atoms left expressions =
    interp_program_expr_list formals binders atoms right expressions.
Proof.
  intro Hstore. induction expressions; cbn [interp_program_expr_list].
  - reflexivity.
  - unfold interp_program_expr_list in *.
    cbn [IR.symbolize_expr_list interp_expr_list].
    pose proof (interp_program_expr_store_ext formals binders atoms left right
      p Hstore) as Hexpr.
    unfold interp_program_expr in Hexpr.
    rewrite Hexpr. rewrite IHexpressions. reflexivity.
Qed.

Fixpoint formal_env_of_values {F} (values : tval_list F) : formal_env F :=
  match values with
  | TVNil => fun t variable => match variable with end
  | TVCons head tail => fun t variable =>
      match view_member variable with
      | MVHere => head
      | MVThere variable' => formal_env_of_values tail _ variable'
      end
  end.

Lemma formal_env_of_values_here {t F} (head : tval t)
    (tail : tval_list F) :
  formal_env_of_values (TVCons head tail) t MHere = head.
Proof. rewrite /formal_env_of_values view_member_here. reflexivity. Qed.

Lemma formal_env_of_values_there {head_type t F} (head : tval head_type)
    (tail : tval_list F) (variable : formal F t) :
  formal_env_of_values (TVCons head tail) t (MThere variable) =
    formal_env_of_values tail t variable.
Proof. rewrite /formal_env_of_values view_member_there. reflexivity. Qed.

Lemma interp_expr_list_formal_subst_of_values {F Δ ts}
    (arguments : expr_list F Δ ts) (values : tval_list ts)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env) :
  interp_expr_list formals binders atoms arguments = Some values ->
  forall t (variable : formal ts t),
    interp_expr formals binders atoms
      (expr_list_formal_subst arguments t variable) =
    Some (formal_env_of_values values t variable).
Proof.
  revert values. induction arguments; intros values Harguments u variable;
    dependent destruction values; simpl in Harguments.
  - dependent destruction variable.
  - destruct (interp_expr formals binders atoms e) eqn:Hhead;
      [|discriminate].
    destruct (interp_expr_list formals binders atoms arguments) eqn:Htail;
      [|discriminate].
    inversion Harguments; subst. dependent destruction H1.
    dependent destruction variable.
    + unfold expr_list_formal_subst. cbn [lookup_expr_list formal_env_of_values].
      unfold simplification_heq.
      rewrite (Eqdep_dec.UIP_dec
        (fun left right : context => decide (left = right))
        (@JMeq_eq context (t :: ts) (t :: ts) JMeq_refl) eq_refl).
      rewrite view_member_here. exact Hhead.
    + unfold expr_list_formal_subst at 1.
      cbn [lookup_expr_list formal_env_of_values].
      unfold simplification_heq.
      rewrite (Eqdep_dec.UIP_dec
        (fun left right : context => decide (left = right))
        (@JMeq_eq context (t :: ts) (t :: ts) JMeq_refl) eq_refl).
      rewrite view_member_there.
      apply IHarguments. reflexivity.
Qed.

Definition empty_binder_env : binder_env [] :=
  fun t variable => match variable with end.

Lemma interp_singleton_bound_subst {F Δ t}
    (reference : value_ref F Δ t) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env) u
    (variable : bvar [t] u) :
  interp_expr formals binders atoms
      (singleton_bound_subst reference u variable) =
    Some (binder_cons (interp_ref formals binders atoms reference)
      empty_binder_env u variable).
Proof.
  dependent destruction variable.
  - rewrite singleton_bound_subst_here. cbn [interp_expr].
    unfold binder_cons. rewrite view_member_here. reflexivity.
  - dependent destruction variable.
Qed.

Module Type DEFINITION_ENV.
  Parameter predicate_body : forall predicate,
    assertion [] (Logic.predicate_args predicate) [].
  Parameter predicate_body_stack_free : forall predicate,
    stack_free (predicate_body predicate).

  Parameter invariant_body : forall invariant,
    assertion [] (Logic.invariant_args invariant) [].
  Parameter invariant_body_stack_free : forall invariant,
    stack_free (invariant_body invariant).
End DEFINITION_ENV.

Lemma interp_rename_bound_expr_list {F Δ Δ' ts}
    (renaming : bound_renaming Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (Hrenaming : forall t (variable : bvar Δ t),
      target_binders t (renaming t variable) = source_binders t variable)
    (expressions : expr_list F Δ ts) :
  interp_expr_list formals target_binders atoms
      (rename_bound_expr_list renaming expressions) =
    interp_expr_list formals source_binders atoms expressions.
Proof.
  induction expressions; simpl; [reflexivity|].
  erewrite interp_rename_bound_expr; [rewrite IHexpressions; reflexivity|].
  exact Hrenaming.
Qed.

Lemma interp_subst_bound_expr_list {F Δ Δ' ts}
    (substitution : bound_subst F Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (Hsubstitution : forall t (variable : bvar Δ t),
      interp_expr formals target_binders atoms (substitution t variable) =
        Some (source_binders t variable))
    (expressions : expr_list F Δ ts) :
  interp_expr_list formals target_binders atoms
      (subst_bound_expr_list substitution expressions) =
    interp_expr_list formals source_binders atoms expressions.
Proof.
  induction expressions; simpl; [reflexivity|].
  erewrite interp_subst_bound_expr; [rewrite IHexpressions; reflexivity|].
  exact Hsubstitution.
Qed.

Lemma interp_subst_formals_expr_list {F F' Δ ts}
    (substitution : formal_subst F F' Δ)
    (source_formals : formal_env F) (target_formals : formal_env F')
    (binders : binder_env Δ) (atoms : atom_env)
    (Hsubstitution : forall t (variable : formal F t),
      interp_expr target_formals binders atoms (substitution t variable) =
        Some (source_formals t variable))
    (expressions : expr_list F Δ ts) :
  interp_expr_list target_formals binders atoms
      (subst_formals_expr_list substitution expressions) =
    interp_expr_list source_formals binders atoms expressions.
Proof.
  induction expressions; simpl; [reflexivity|].
  erewrite interp_subst_formals_expr; [rewrite IHexpressions; reflexivity|].
  exact Hsubstitution.
Qed.

Lemma interp_rename_bound_store {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (Hrenaming : forall t (variable : bvar Δ t),
      target_binders t (renaming t variable) = source_binders t variable)
    (store : symbolic_store Γ F Δ) :
  interp_store formals target_binders atoms
      (rename_bound_store renaming store) =
    interp_store formals source_binders atoms store.
Proof.
  induction store; simpl; [reflexivity|].
  rewrite IHstore. destruct v; simpl; try reflexivity.
  rewrite Hrenaming. reflexivity.
Qed.

(** *** Reference substitution in the symbolic store

    The store is a list of [value_ref]s, so substituting references into
    it is interpreted by substituting the corresponding values into the
    binder environment.  This is the store-side half of [RPEIntro]. *)
Lemma interp_subst_bound_value_ref {F Δ Δ' t}
    (substitution : Resource.bound_ref_subst F Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (Hsubstitution : forall u (variable : bvar Δ u),
      interp_ref formals target_binders atoms (substitution u variable) =
        source_binders u variable)
    (reference : value_ref F Δ t) :
  interp_ref formals target_binders atoms
      (Resource.subst_bound_value_ref substitution reference) =
    interp_ref formals source_binders atoms reference.
Proof.
  destruct reference; simpl; try reflexivity. apply Hsubstitution.
Qed.

Lemma interp_subst_bound_store {Γ F Δ Δ'}
    (substitution : Resource.bound_ref_subst F Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (Hsubstitution : forall u (variable : bvar Δ u),
      interp_ref formals target_binders atoms (substitution u variable) =
        source_binders u variable)
    (store : symbolic_store Γ F Δ) :
  interp_store formals target_binders atoms
      (Resource.subst_bound_store substitution store) =
    interp_store formals source_binders atoms store.
Proof.
  induction store; simpl; [reflexivity |].
  rewrite IHstore.
  rewrite (interp_subst_bound_value_ref substitution formals source_binders
    target_binders atoms Hsubstitution). reflexivity.
Qed.

(** The head reference substitution interprets as consing the witness's
    value onto the binder environment. *)
Lemma interp_head_bound_ref_subst {F Δ t}
    (witness : value_ref F Δ t)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env) :
  forall u (variable : bvar (t :: Δ) u),
    interp_ref formals binders atoms
        (Resource.head_bound_ref_subst witness u variable) =
      binder_cons (interp_ref formals binders atoms witness) binders u
        variable.
Proof.
  intros u variable. destruct (view_member variable) eqn:Hview.
  - unfold Resource.head_bound_ref_subst, binder_cons. rewrite Hview.
    repeat rewrite view_member_here. reflexivity.
  - unfold Resource.head_bound_ref_subst, binder_cons. rewrite Hview.
    repeat rewrite view_member_there. reflexivity.
Qed.

Lemma binder_cons_lift_bound_renaming {Δ Δ' t}
    (renaming : bound_renaming Δ Δ') (value : tval t)
    (source_binders : binder_env Δ) (target_binders : binder_env Δ')
    (Hrenaming : forall u (variable : bvar Δ u),
      target_binders u (renaming u variable) = source_binders u variable) :
  forall u (variable : bvar (t :: Δ) u),
    binder_cons value target_binders u
        (lift_bound_renaming renaming u variable) =
      binder_cons value source_binders u variable.
Proof.
  intros u variable. destruct (view_member variable) eqn:Hview.
  - unfold lift_bound_renaming, binder_cons.
    rewrite Hview. repeat rewrite view_member_here. reflexivity.
  - unfold lift_bound_renaming, binder_cons.
    rewrite Hview. repeat rewrite view_member_there. apply Hrenaming.
Qed.

Lemma binder_cons_weaken {Δ t u} (head : tval u) (tail : binder_env Δ)
    (variable : bvar Δ t) :
  binder_cons head tail t (weaken_bound_renaming t variable) =
    tail t variable.
Proof.
  unfold binder_cons, weaken_bound_renaming.
  rewrite view_member_there. reflexivity.
Qed.

Lemma binder_cons_exchange {Δ t u}
    (t_value : tval t) (u_value : tval u) (tail : binder_env Δ) :
  forall result (variable : bvar (u :: t :: Δ) result),
    binder_cons t_value (binder_cons u_value tail) result
      (@exchange_bound_renaming Δ u t result variable) =
    binder_cons u_value (binder_cons t_value tail) result variable.
Proof.
  intros result variable. destruct (view_member variable) eqn:Houter.
  - unfold exchange_bound_renaming, binder_cons. rewrite Houter.
    rewrite view_member_there. rewrite view_member_here. reflexivity.
  - destruct (view_member variable) eqn:Hinner.
    + unfold exchange_bound_renaming, binder_cons. rewrite Houter. rewrite Hinner.
      rewrite view_member_here. reflexivity.
    + unfold exchange_bound_renaming, binder_cons. rewrite Houter. rewrite Hinner.
      rewrite !view_member_there. reflexivity.
Qed.

Lemma binder_cons_return_bound_renaming {Δ t}
    (value : tval t) (binders : binder_env Δ) :
  forall u (variable : bvar [t] u),
    binder_cons value binders u (return_bound_renaming u variable) =
    binder_cons value empty_binder_env u variable.
Proof.
  intros u variable. destruct (view_member variable) eqn:Hview.
  - unfold return_bound_renaming, binder_cons. rewrite Hview.
    repeat rewrite view_member_here. reflexivity.
  - dependent destruction variable.
Qed.

Lemma weaken_expr_as_renaming {F Δ t u} (expression : expr F Δ t) :
  weaken_expr (u := u) expression =
    rename_bound_expr weaken_bound_renaming expression.
Proof.
  induction expression; simpl; try congruence.
  destruct reference; reflexivity.
Qed.

Lemma interp_weaken_expr {F Δ t u}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (head : tval u) (expression : expr F Δ t) :
  interp_expr formals (binder_cons head binders) atoms (weaken_expr expression) =
    interp_expr formals binders atoms expression.
Proof.
  rewrite weaken_expr_as_renaming.
  apply interp_rename_bound_expr. intros v variable.
  apply binder_cons_weaken.
Qed.

Lemma interp_weaken_expr_list {F Δ ts u}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (head : tval u) (expressions : expr_list F Δ ts) :
  interp_expr_list formals (binder_cons head binders) atoms
      (weaken_expr_list expressions) =
    interp_expr_list formals binders atoms expressions.
Proof.
  induction expressions; simpl; [reflexivity|].
  rewrite interp_weaken_expr. rewrite IHexpressions. reflexivity.
Qed.

Lemma interp_weaken_ref {F Δ t u}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (head : tval u) (reference : value_ref F Δ t) :
  interp_ref formals (binder_cons head binders) atoms
      (weaken_ref reference) =
    interp_ref formals binders atoms reference.
Proof.
  destruct reference; simpl; try reflexivity.
  apply binder_cons_weaken.
Qed.

Lemma interp_weaken_store {Γ F Δ u}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (head : tval u) (store : symbolic_store Γ F Δ) :
  interp_store formals (binder_cons head binders) atoms
      (weaken_store store) =
    interp_store formals binders atoms store.
Proof.
  induction store; simpl; [reflexivity|].
  rewrite interp_weaken_ref. rewrite IHstore. reflexivity.
Qed.

Lemma binder_cons_lift_bound_subst {F Δ Δ' t}
    (substitution : bound_subst F Δ Δ') (value : tval t)
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (Hsubstitution : forall u (variable : bvar Δ u),
      interp_expr formals target_binders atoms (substitution u variable) =
        Some (source_binders u variable)) :
  forall u (variable : bvar (t :: Δ) u),
    interp_expr formals (binder_cons value target_binders) atoms
        (lift_bound_subst substitution u variable) =
      Some (binder_cons value source_binders u variable).
Proof.
  intros u variable. destruct (view_member variable) eqn:Hview.
  - unfold lift_bound_subst. rewrite Hview. simpl.
    unfold binder_cons. repeat rewrite view_member_here. reflexivity.
  - unfold lift_bound_subst. rewrite Hview.
    unfold binder_cons. repeat rewrite view_member_there.
    rewrite interp_weaken_expr. apply Hsubstitution.
Qed.

Module Type SEMANTIC_CONFIG.
  Parameter PROP : bi.
  Parameter bi_affine : BiAffine PROP.

  Parameter stack_context : context -> Type.
  Parameter empty_stack_context : stack_context [].
  Parameter stack_own : forall Γ,
    stack_context Γ -> concrete_store Γ -> bi_car PROP.
  Parameter stack_own_exclusive : forall Γ runtime
    (left right : concrete_store Γ),
    stack_own Γ runtime left ∗ stack_own Γ runtime right ⊢ False.
  Parameter field_own : forall field,
    tval TRef -> tval (Logic.field_type field) -> bi_car PROP.
  Parameter ghost_own : forall field,
    tval TRef -> tval (Logic.field_type field) -> bi_car PROP.
  Parameter invariant_own : forall invariant,
    tval_list (Logic.invariant_args invariant) -> bi_car PROP.
End SEMANTIC_CONFIG.

(** Term-level counterpart of [SEMANTIC_CONFIG].  Unlike a Rocq module, a
    value of this record may depend on ghost names allocated inside an Iris
    adequacy proof.  The module interface remains below as a compatibility
    adapter while runtime clients migrate. *)
Record semantic_config_data (PROP : bi) : Type := SemanticConfigData {
  data_bi_affine : BiAffine PROP;
  data_stack_context : context -> Type;
  data_empty_stack_context : data_stack_context [];
  data_stack_own : forall Γ,
    data_stack_context Γ -> concrete_store Γ -> bi_car PROP;
  data_stack_own_exclusive : forall Γ runtime
    (left right : concrete_store Γ),
    data_stack_own Γ runtime left ∗ data_stack_own Γ runtime right ⊢ False;
  data_field_own : forall field,
    tval TRef -> tval (Logic.field_type field) -> bi_car PROP;
  data_ghost_own : forall field,
    tval TRef -> tval (Logic.field_type field) -> bi_car PROP;
  data_invariant_own : forall invariant,
    tval_list (Logic.invariant_args invariant) -> bi_car PROP;
}.

Arguments data_stack_context {_} _ _.
Arguments data_empty_stack_context {_} _.
Arguments data_stack_own {_} _ {_} _ _.
Arguments data_stack_own_exclusive {_} _ {_} _ _ _.
Arguments data_field_own {_} _ _ _ _.
Arguments data_ghost_own {_} _ _ _ _.
Arguments data_invariant_own {_} _ _ _.

Module TermSemantics.
Section WithModel.
Context {PROP : bi} (Model : semantic_config_data PROP).
Local Existing Instance data_bi_affine.
Local Notation iProp := (bi_car PROP).

Definition predicate_semantics := forall predicate,
  tval_list (Logic.predicate_args predicate) -> iProp.

Fixpoint interp_assertion {Γ F Δ}
    (predicates : predicate_semantics)
    (runtime : data_stack_context Model Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (formula : assertion Γ F Δ) : iProp :=
  match formula with
  | AStack store =>
      data_stack_own Model runtime (interp_store formals binders atoms store)
  | AExpr condition =>
      ⌜interp_expr formals binders atoms condition = Some (VBool true)⌝%I
  | APure proposition => ⌜proposition⌝%I
  | AOwn field location chunk =>
      (∃ concrete_location concrete_chunk,
        ⌜interp_expr formals binders atoms location = Some concrete_location⌝ ∗
        ⌜interp_expr formals binders atoms chunk = Some concrete_chunk⌝ ∗
        data_field_own Model field concrete_location concrete_chunk)%I
  | AGhostOwn field location chunk =>
      (∃ concrete_location concrete_chunk,
        ⌜interp_expr formals binders atoms location = Some concrete_location⌝ ∗
        ⌜interp_expr formals binders atoms chunk = Some concrete_chunk⌝ ∗
        data_ghost_own Model field concrete_location concrete_chunk)%I
  | AFpuAllowed t old_chunk new_chunk =>
      (⌜exists old_value new_value,
        interp_expr formals binders atoms old_chunk = Some old_value /\
        interp_expr formals binders atoms new_chunk = Some new_value /\
        tval_fpu_allowed old_value new_value⌝)%I
  | ARAValid t chunk =>
      (⌜exists value, interp_expr formals binders atoms chunk = Some value /\
        tval_ra_valid value⌝)%I
  | AExists t body =>
      (∃ value : tval t,
        interp_assertion predicates runtime formals
          (binder_cons value binders) atoms body)%I
  | AForall t body =>
      (∀ value : tval t,
        interp_assertion predicates runtime formals
          (binder_cons value binders) atoms body)%I
  | AIte condition then_branch else_branch =>
      ((⌜interp_expr formals binders atoms condition = Some (VBool true)⌝ -∗
          interp_assertion predicates runtime formals binders atoms
            then_branch) ∧
       (⌜interp_expr formals binders atoms condition <> Some (VBool true)⌝ -∗
          interp_assertion predicates runtime formals binders atoms
            else_branch))%I
  | AInvariant invariant args =>
      (∃ values,
        ⌜interp_expr_list formals binders atoms args = Some values⌝ ∗
        data_invariant_own Model invariant values)%I
  | APredicate predicate args =>
      (∃ values,
        ⌜interp_expr_list formals binders atoms args = Some values⌝ ∗
        predicates predicate values)%I
  | AAnd left_formula right_formula =>
      (interp_assertion predicates runtime formals binders atoms left_formula ∗
       interp_assertion predicates runtime formals binders atoms right_formula)%I
  end.

Lemma interp_assertion_stable_atoms {Γ F Δ}
    (left_predicates right_predicates : predicate_semantics)
    (Hpredicates : forall predicate values,
      left_predicates predicate values ≡ right_predicates predicate values)
    (runtime : data_stack_context Model Γ)
    (formals : formal_env F) (binders : binder_env Δ)
    (left_atoms right_atoms : atom_env)
    (formula : assertion Γ F Δ) :
  stable_atoms_agree left_atoms right_atoms ->
  assertion_entry_free formula ->
  interp_assertion left_predicates runtime formals binders left_atoms formula ≡
    interp_assertion right_predicates runtime formals binders right_atoms formula.
Proof.
  intros Hagree Hfree.
  induction formula; simpl in Hfree |- *.
  - rewrite (interp_store_stable_atoms _ _ _ _ _ Hagree Hfree). reflexivity.
  - rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hfree). reflexivity.
  - reflexivity.
  - destruct Hfree as [Hlocation Hchunk].
    rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hlocation).
    rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hchunk). reflexivity.
  - destruct Hfree as [Hlocation Hchunk].
    rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hlocation).
    rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hchunk). reflexivity.
  - destruct Hfree as [Hold Hnew].
    rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hold).
    rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hnew). reflexivity.
  - rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hfree). reflexivity.
  - apply bi.exist_proper. intro value.
    exact (IHformula (binder_cons value binders) Hfree).
  - apply bi.forall_proper. intro value.
    exact (IHformula (binder_cons value binders) Hfree).
  - destruct Hfree as [Hcondition [Hthen Helse]].
    rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hcondition).
    rewrite (IHformula1 binders Hthen). rewrite (IHformula2 binders Helse).
    reflexivity.
  - rewrite (interp_expr_list_stable_atoms _ _ _ _ _ Hagree Hfree).
    reflexivity.
  - rewrite (interp_expr_list_stable_atoms _ _ _ _ _ Hagree Hfree).
    apply bi.exist_proper. intro values. rewrite Hpredicates. reflexivity.
  - destruct Hfree as [Hleft Hright].
    rewrite (IHformula1 binders Hleft). rewrite (IHformula2 binders Hright).
    reflexivity.
Qed.

Lemma interp_assertion_stack {Γ F Δ} predicates runtime formals binders atoms
    (store : symbolic_store Γ F Δ) :
  interp_assertion predicates runtime formals binders atoms (AStack store) ≡
    data_stack_own Model runtime (interp_store formals binders atoms store).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** *** Interpretation of the resource core

    The interpretation of a resource state is definitionally the expected
    decomposition, [interp_stack ∗ interp_core].  Compare
    [interp_assertion] above, where the [AStack] case can occur anywhere in
    the recursion, so "this assertion owns exactly one stack" is a semantic
    fact that has to be re-established after every rule.  Here it is the
    shape of the definition. *)

Fixpoint interp_core {F Δ}
    (predicates : predicate_semantics)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (formula : Resource.core_assertion F Δ) : iProp :=
  match formula with
  | Resource.CExpr condition =>
      ⌜interp_expr formals binders atoms condition = Some (VBool true)⌝%I
  | Resource.CPure proposition => ⌜proposition⌝%I
  | Resource.COwn field location chunk =>
      (∃ concrete_location concrete_chunk,
        ⌜interp_expr formals binders atoms location = Some concrete_location⌝ ∗
        ⌜interp_expr formals binders atoms chunk = Some concrete_chunk⌝ ∗
        data_field_own Model field concrete_location concrete_chunk)%I
  | Resource.CGhostOwn field location chunk =>
      (∃ concrete_location concrete_chunk,
        ⌜interp_expr formals binders atoms location = Some concrete_location⌝ ∗
        ⌜interp_expr formals binders atoms chunk = Some concrete_chunk⌝ ∗
        data_ghost_own Model field concrete_location concrete_chunk)%I
  | Resource.CFpuAllowed t old_chunk new_chunk =>
      (⌜exists old_value new_value,
        interp_expr formals binders atoms old_chunk = Some old_value /\
        interp_expr formals binders atoms new_chunk = Some new_value /\
        tval_fpu_allowed old_value new_value⌝)%I
  | Resource.CRAValid t chunk =>
      (⌜exists value, interp_expr formals binders atoms chunk = Some value /\
        tval_ra_valid value⌝)%I
  | Resource.CExists t body =>
      (∃ value : tval t,
        interp_core predicates formals (binder_cons value binders) atoms
          body)%I
  | Resource.CForall t body =>
      (∀ value : tval t,
        interp_core predicates formals (binder_cons value binders) atoms
          body)%I
  | Resource.CIte condition then_branch else_branch =>
      ((⌜interp_expr formals binders atoms condition = Some (VBool true)⌝ -∗
          interp_core predicates formals binders atoms then_branch) ∧
       (⌜interp_expr formals binders atoms condition <> Some (VBool true)⌝ -∗
          interp_core predicates formals binders atoms else_branch))%I
  | Resource.CInvariant invariant args =>
      (∃ values,
        ⌜interp_expr_list formals binders atoms args = Some values⌝ ∗
        data_invariant_own Model invariant values)%I
  | Resource.CPredicate predicate args =>
      (∃ values,
        ⌜interp_expr_list formals binders atoms args = Some values⌝ ∗
        predicates predicate values)%I
  | Resource.CAnd left_formula right_formula =>
      (interp_core predicates formals binders atoms left_formula ∗
       interp_core predicates formals binders atoms right_formula)%I
  end.

Lemma interp_core_stable_atoms {F Δ}
    (left_predicates right_predicates : predicate_semantics)
    (Hpredicates : forall predicate values,
      left_predicates predicate values ≡ right_predicates predicate values)
    (formals : formal_env F) (binders : binder_env Δ)
    (left_atoms right_atoms : atom_env)
    (formula : Resource.core_assertion F Δ) :
  stable_atoms_agree left_atoms right_atoms ->
  Resource.core_entry_free formula ->
  interp_core left_predicates formals binders left_atoms formula ≡
    interp_core right_predicates formals binders right_atoms formula.
Proof.
  intros Hagree Hfree.
  induction formula; simpl in Hfree |- *.
  - rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hfree). reflexivity.
  - reflexivity.
  - destruct Hfree as [Hlocation Hchunk].
    rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hlocation).
    rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hchunk). reflexivity.
  - destruct Hfree as [Hlocation Hchunk].
    rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hlocation).
    rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hchunk). reflexivity.
  - destruct Hfree as [Hold Hnew].
    rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hold).
    rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hnew). reflexivity.
  - rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hfree). reflexivity.
  - apply bi.exist_proper. intro value.
    exact (IHformula (binder_cons value binders) Hfree).
  - apply bi.forall_proper. intro value.
    exact (IHformula (binder_cons value binders) Hfree).
  - destruct Hfree as [Hcondition [Hthen Helse]].
    rewrite (interp_expr_stable_atoms _ _ _ _ _ Hagree Hcondition).
    rewrite (IHformula1 binders Hthen). rewrite (IHformula2 binders Helse).
    reflexivity.
  - rewrite (interp_expr_list_stable_atoms _ _ _ _ _ Hagree Hfree).
    reflexivity.
  - rewrite (interp_expr_list_stable_atoms _ _ _ _ _ Hagree Hfree).
    apply bi.exist_proper. intro values. rewrite Hpredicates. reflexivity.
  - destruct Hfree as [Hleft Hright].
    rewrite (IHformula1 binders Hleft). rewrite (IHformula2 binders Hright).
    reflexivity.
Qed.

Definition interp_resource {Γ F Δ}
    (predicates : predicate_semantics)
    (runtime : data_stack_context Model Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (state : Resource.resource_assertion Γ F Δ) : iProp :=
  (data_stack_own Model runtime
     (interp_store formals binders atoms (Resource.resource_stack state)) ∗
   interp_core predicates formals binders atoms
     (Resource.resource_body state))%I.

Fixpoint interp_resource_prenex {Γ F Δ}
    (predicates : predicate_semantics)
    (runtime : data_stack_context Model Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (prenex : Resource.resource_prenex Γ F Δ) {struct prenex} : iProp :=
  match prenex in Resource.resource_prenex _ _ Δ0
    return binder_env Δ0 -> iProp with
  | Resource.ResourceBody state =>
      fun binders0 =>
        interp_resource predicates runtime formals binders0 atoms state
  | Resource.ResourceExists t rest =>
      fun binders0 =>
        (∃ value : tval t,
          interp_resource_prenex predicates runtime formals
            (binder_cons value binders0) atoms rest)%I
  end binders.

(** The stack/core decomposition, holding by [reflexivity]. *)
Lemma interp_resource_split {Γ F Δ} predicates runtime formals binders atoms
    (store : symbolic_store Γ F Δ) (body : Resource.core_assertion F Δ) :
  interp_resource predicates runtime formals binders atoms
      (Resource.ResourceState store body) ≡
    (data_stack_own Model runtime (interp_store formals binders atoms store) ∗
     interp_core predicates formals binders atoms body)%I.
Proof. reflexivity. Qed.

Lemma interp_resource_prenex_exists {Γ F Δ} predicates runtime formals binders
    atoms t (rest : Resource.resource_prenex Γ F (t :: Δ)) :
  interp_resource_prenex predicates runtime formals binders atoms
      (Resource.ResourceExists t rest) ≡
    (∃ value : tval t,
      interp_resource_prenex predicates runtime formals
        (binder_cons value binders) atoms rest)%I.
Proof. reflexivity. Qed.

Lemma interp_assertion_and {Γ F Δ} predicates runtime formals binders atoms
    (left right : assertion Γ F Δ) :
  interp_assertion predicates runtime formals binders atoms (AAnd left right) ≡
    (interp_assertion predicates runtime formals binders atoms left ∗
     interp_assertion predicates runtime formals binders atoms right)%I.
Proof. reflexivity. Qed.

Lemma interp_assertion_exists {Γ F Δ} predicates runtime formals binders atoms t
    (body : assertion Γ F (t :: Δ)) :
  interp_assertion predicates runtime formals binders atoms (AExists t body) ≡
    (∃ value : tval t,
      interp_assertion predicates runtime formals
        (binder_cons value binders) atoms body)%I.
Proof. reflexivity. Qed.

Lemma interp_assertion_forall {Γ F Δ} predicates runtime formals binders atoms t
    (body : assertion Γ F (t :: Δ)) :
  interp_assertion predicates runtime formals binders atoms (AForall t body) ≡
    (∀ value : tval t,
      interp_assertion predicates runtime formals
        (binder_cons value binders) atoms body)%I.
Proof. reflexivity. Qed.

Lemma interp_assertion_ite {Γ F Δ} predicates runtime formals binders atoms
    (condition : expr F Δ TBool) (then_branch else_branch : assertion Γ F Δ) :
  interp_assertion predicates runtime formals binders atoms
      (AIte condition then_branch else_branch) ≡
    ((⌜interp_expr formals binders atoms condition = Some (VBool true)⌝ -∗
        interp_assertion predicates runtime formals binders atoms then_branch) ∧
     (⌜interp_expr formals binders atoms condition <> Some (VBool true)⌝ -∗
        interp_assertion predicates runtime formals binders atoms else_branch))%I.
Proof. reflexivity. Qed.

Theorem interp_rename_bound_assertion {Γ F Δ Δ'} predicates
    (renaming : bound_renaming Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (runtime : data_stack_context Model Γ)
    (Hrenaming : forall t (variable : bvar Δ t),
      target_binders t (renaming t variable) = source_binders t variable)
    (formula : assertion Γ F Δ) :
  interp_assertion predicates runtime formals target_binders atoms
      (rename_bound_assertion renaming formula) ≡
    interp_assertion predicates runtime formals source_binders atoms formula.
Proof.
  revert Δ' renaming source_binders target_binders Hrenaming.
  induction formula; intros Δ' renaming source_binders target_binders
      Hrenaming; simpl.
  - rewrite (interp_rename_bound_store renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - reflexivity.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming).
    rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming).
    rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming).
    rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - apply bi.exist_proper. intros value.
    apply IHformula. apply binder_cons_lift_bound_renaming. exact Hrenaming.
  - apply bi.forall_proper. intros value.
    apply IHformula. apply binder_cons_lift_bound_renaming. exact Hrenaming.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming).
    apply bi.and_proper; apply bi.wand_proper; try reflexivity.
    + apply IHformula1. exact Hrenaming.
    + apply IHformula2. exact Hrenaming.
  - rewrite (interp_rename_bound_expr_list renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - rewrite (interp_rename_bound_expr_list renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - apply bi.sep_proper.
    + apply IHformula1. exact Hrenaming.
    + apply IHformula2. exact Hrenaming.
Qed.

Corollary interp_weaken_assertion {Γ F Δ u} predicates
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (runtime : data_stack_context Model Γ)
    (head : tval u) (formula : assertion Γ F Δ) :
  interp_assertion predicates runtime formals (binder_cons head binders) atoms
      (weaken_assertion formula) ≡
    interp_assertion predicates runtime formals binders atoms formula.
Proof.
  apply interp_rename_bound_assertion.
  intros t variable. apply binder_cons_weaken.
Qed.

(** *** Renaming and weakening for the resource core.  Same induction as
    [interp_rename_bound_assertion], one case shorter. *)
Theorem interp_rename_bound_core {F Δ Δ'} predicates
    (renaming : bound_renaming Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (Hrenaming : forall t (variable : bvar Δ t),
      target_binders t (renaming t variable) = source_binders t variable)
    (formula : Resource.core_assertion F Δ) :
  interp_core predicates formals target_binders atoms
      (Resource.rename_bound_core renaming formula) ≡
    interp_core predicates formals source_binders atoms formula.
Proof.
  revert Δ' renaming source_binders target_binders Hrenaming.
  induction formula; intros Δ' renaming source_binders target_binders
      Hrenaming; simpl.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - reflexivity.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming).
    rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming).
    rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming).
    rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - apply bi.exist_proper. intros value.
    apply IHformula. apply binder_cons_lift_bound_renaming. exact Hrenaming.
  - apply bi.forall_proper. intros value.
    apply IHformula. apply binder_cons_lift_bound_renaming. exact Hrenaming.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming).
    apply bi.and_proper; apply bi.wand_proper; try reflexivity.
    + apply IHformula1. exact Hrenaming.
    + apply IHformula2. exact Hrenaming.
  - rewrite (interp_rename_bound_expr_list renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - rewrite (interp_rename_bound_expr_list renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - apply bi.sep_proper.
    + apply IHformula1. exact Hrenaming.
    + apply IHformula2. exact Hrenaming.
Qed.

Corollary interp_weaken_core {F Δ u} predicates
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (head : tval u) (formula : Resource.core_assertion F Δ) :
  interp_core predicates formals (binder_cons head binders) atoms
      (Resource.weaken_core formula) ≡
    interp_core predicates formals binders atoms formula.
Proof.
  apply interp_rename_bound_core.
  intros t variable. apply binder_cons_weaken.
Qed.

(** *** Renaming and weakening for resource states and prenex telescopes.

    Stated directly over [interp_resource] / [interp_resource_prenex] so
    that the resource calculus's validity proofs never have to detour
    through the old grammar. *)
Lemma interp_rename_bound_resource {Γ F Δ Δ'} predicates
    (renaming : bound_renaming Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (runtime : data_stack_context Model Γ)
    (Hrenaming : forall t (variable : bvar Δ t),
      target_binders t (renaming t variable) = source_binders t variable)
    (state : Resource.resource_assertion Γ F Δ) :
  interp_resource predicates runtime formals target_binders atoms
      (Resource.rename_bound_resource renaming state) ≡
    interp_resource predicates runtime formals source_binders atoms state.
Proof.
  destruct state as [store body]. unfold interp_resource.
  cbn [Resource.rename_bound_resource Resource.resource_stack
       Resource.resource_body].
  rewrite (interp_rename_bound_store renaming formals source_binders
    target_binders atoms Hrenaming).
  apply bi.sep_proper; [reflexivity |].
  apply interp_rename_bound_core. exact Hrenaming.
Qed.

Theorem interp_rename_resource_prenex {Γ F Δ} predicates
    (prenex : Resource.resource_prenex Γ F Δ) :
  forall Δ' (renaming : bound_renaming Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (runtime : data_stack_context Model Γ),
  (forall t (variable : bvar Δ t),
    target_binders t (renaming t variable) = source_binders t variable) ->
  interp_resource_prenex predicates runtime formals target_binders atoms
      (Resource.rename_resource_prenex prenex _ renaming) ≡
    interp_resource_prenex predicates runtime formals source_binders atoms
      prenex.
Proof.
  induction prenex; intros Δ' renaming formals source_binders target_binders
      atoms runtime Hrenaming;
    cbn [Resource.rename_resource_prenex interp_resource_prenex].
  - apply interp_rename_bound_resource. exact Hrenaming.
  - apply bi.exist_proper. intros value. apply IHprenex.
    apply binder_cons_lift_bound_renaming. exact Hrenaming.
Qed.

Corollary interp_weaken_resource_prenex {Γ F Δ u} predicates
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (runtime : data_stack_context Model Γ)
    (head : tval u) (prenex : Resource.resource_prenex Γ F Δ) :
  interp_resource_prenex predicates runtime formals
      (binder_cons head binders) atoms
      (Resource.weaken_resource_prenex prenex) ≡
    interp_resource_prenex predicates runtime formals binders atoms prenex.
Proof.
  apply interp_rename_resource_prenex.
  intros t variable. apply binder_cons_weaken.
Qed.

(** *** Agreement with the embedding into the old grammar

    This is the bridge that lets the existing Iris validity proofs be
    reused for the resource calculus: interpreting an embedded resource
    telescope is interpreting the telescope. *)
Lemma interp_core_to_assertion {Γ F Δ} predicates runtime formals binders atoms
    (formula : Resource.core_assertion F Δ) :
  interp_assertion predicates runtime formals binders atoms
      (@Resource.core_to_assertion Γ F Δ formula) ≡
    interp_core predicates formals binders atoms formula.
Proof.
  revert binders.
  induction formula; intro binders; cbn [Resource.core_to_assertion
    interp_assertion interp_core]; try reflexivity.
  - apply bi.exist_proper; intro value. apply IHformula.
  - apply bi.forall_proper; intro value. apply IHformula.
  - apply bi.and_proper; apply bi.wand_proper;
      [reflexivity | apply IHformula1 | reflexivity | apply IHformula2].
  - apply bi.sep_proper; [apply IHformula1 | apply IHformula2].
Qed.

Lemma interp_resource_to_assertion {Γ F Δ} predicates runtime formals binders
    atoms (state : Resource.resource_assertion Γ F Δ) :
  interp_assertion predicates runtime formals binders atoms
      (Resource.resource_to_assertion state) ≡
    interp_resource predicates runtime formals binders atoms state.
Proof.
  destruct state as [store body].
  cbn [Resource.resource_to_assertion Resource.resource_stack
    Resource.resource_body interp_assertion].
  unfold interp_resource. cbn.
  apply bi.sep_proper; [reflexivity | apply interp_core_to_assertion].
Qed.

Lemma interp_prenex_to_assertion {Γ F Δ} predicates runtime formals atoms
    (prenex : Resource.resource_prenex Γ F Δ) :
  forall (binders : binder_env Δ),
  interp_assertion predicates runtime formals binders atoms
      (Resource.prenex_to_assertion prenex) ≡
    interp_resource_prenex predicates runtime formals binders atoms prenex.
Proof.
  induction prenex as [Δ state | Δ t rest IH]; intro binders;
    cbn [Resource.prenex_to_assertion interp_assertion
      interp_resource_prenex].
  - apply interp_resource_to_assertion.
  - apply bi.exist_proper; intro value. apply IH.
Qed.

(** Conjoining a core frame under a telescope is separating conjunction,
    at every depth. *)
Lemma interp_prenex_and {Γ F Δ} predicates runtime formals atoms
    (prenex : Resource.resource_prenex Γ F Δ) :
  forall (binders : binder_env Δ) (frame : Resource.core_assertion F Δ),
  interp_resource_prenex predicates runtime formals binders atoms
      (Resource.prenex_and prenex frame) ⊣⊢
    (interp_resource_prenex predicates runtime formals binders atoms prenex ∗
     interp_core predicates formals binders atoms frame)%I.
Proof.
  induction prenex as [Δ state | Δ t rest IH];
    intros binders frame;
    cbn [Resource.prenex_and interp_resource_prenex].
  - destruct state as [store body]. unfold interp_resource. cbn.
    rewrite -assoc. reflexivity.
  - rewrite bi.sep_exist_r. apply bi.exist_proper; intro value.
    rewrite IH. apply bi.sep_proper; [reflexivity |].
    apply interp_weaken_core.
Qed.

Theorem interp_subst_bound_assertion {Γ F Δ Δ'} predicates
    (substitution : bound_subst F Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (runtime : data_stack_context Model Γ)
    (Hsubstitution : forall t (variable : bvar Δ t),
      interp_expr formals target_binders atoms (substitution t variable) =
        Some (source_binders t variable))
    (formula : assertion Γ F Δ) (formula' : assertion Γ F Δ') :
  subst_bound_assertion substitution formula = Some formula' ->
  interp_assertion predicates runtime formals target_binders atoms formula' ≡
    interp_assertion predicates runtime formals source_binders atoms formula.
Proof.
  revert Δ' substitution target_binders formula' Hsubstitution.
  induction formula; intros Δ' substitution target_binders formula'
      Hsubstitution Hresult; simpl in Hresult.
  - discriminate Hresult.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution).
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution).
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution).
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - destruct (subst_bound_assertion (lift_bound_subst substitution) formula)
      as [body'|] eqn:Hbody; [|discriminate Hresult].
    inversion Hresult; subst. simpl. apply bi.exist_proper. intros value.
    eapply IHformula; [|exact Hbody].
    apply binder_cons_lift_bound_subst. exact Hsubstitution.
  - destruct (subst_bound_assertion (lift_bound_subst substitution) formula)
      as [body'|] eqn:Hbody; [|discriminate Hresult].
    inversion Hresult; subst. simpl. apply bi.forall_proper. intros value.
    eapply IHformula; [|exact Hbody].
    apply binder_cons_lift_bound_subst. exact Hsubstitution.
  - destruct (subst_bound_assertion substitution formula1) as [then'|]
      eqn:Hthen; [|discriminate Hresult].
    destruct (subst_bound_assertion substitution formula2) as [else'|]
      eqn:Helse; [|discriminate Hresult].
    inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution).
    apply bi.and_proper; apply bi.wand_proper; try reflexivity.
    + eapply IHformula1; eauto.
    + eapply IHformula2; eauto.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr_list substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr_list substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - destruct (subst_bound_assertion substitution formula1) as [left'|]
      eqn:Hleft; [|discriminate Hresult].
    destruct (subst_bound_assertion substitution formula2) as [right'|]
      eqn:Hright; [|discriminate Hresult].
    inversion Hresult; subst. simpl. apply bi.sep_proper.
    + eapply IHformula1; eauto.
    + eapply IHformula2; eauto.
Qed.

Lemma interp_head_bound_subst {F Δ t}
    (witness : expr F Δ t) (value : tval t)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (Hwitness : interp_expr formals binders atoms witness = Some value) :
  forall u (variable : bvar (t :: Δ) u),
    interp_expr formals binders atoms (head_bound_subst witness u variable) =
      Some (binder_cons value binders u variable).
Proof.
  intros u variable. destruct (view_member variable) eqn:Hview.
  - unfold head_bound_subst, binder_cons. rewrite Hview.
    repeat rewrite view_member_here. exact Hwitness.
  - unfold head_bound_subst, binder_cons. rewrite Hview.
    repeat rewrite view_member_there. reflexivity.
Qed.

Corollary interp_instantiate_bound_assertion {Γ F Δ t} predicates
    (witness : expr F Δ t) (value : tval t)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (runtime : data_stack_context Model Γ)
    (body : assertion Γ F (t :: Δ)) (formula : assertion Γ F Δ)
    (Hwitness : interp_expr formals binders atoms witness = Some value)
    (Hinstantiate : instantiate_bound_assertion witness body = Some formula) :
  interp_assertion predicates runtime formals binders atoms formula ≡
    interp_assertion predicates runtime formals (binder_cons value binders)
      atoms body.
Proof.
  eapply interp_subst_bound_assertion; [|exact Hinstantiate].
  apply interp_head_bound_subst. exact Hwitness.
Qed.

(** Core counterpart of [interp_subst_bound_assertion].  [subst_bound_core]
    is total, so there is no [Some]-plumbing and no [AStack] case: the proof
    is a plain equational induction. *)
Theorem interp_subst_bound_core {F Δ Δ'} predicates
    (substitution : bound_subst F Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (Hsubstitution : forall t (variable : bvar Δ t),
      interp_expr formals target_binders atoms (substitution t variable) =
        Some (source_binders t variable))
    (formula : Resource.core_assertion F Δ) :
  interp_core predicates formals target_binders atoms
      (Resource.subst_bound_core substitution formula) ≡
    interp_core predicates formals source_binders atoms formula.
Proof.
  revert Δ' substitution target_binders Hsubstitution.
  induction formula; intros Δ' substitution target_binders Hsubstitution;
    cbn [Resource.subst_bound_core interp_core].
  - rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - reflexivity.
  - rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution).
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution).
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution).
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - apply bi.exist_proper. intros value. apply IHformula.
    apply binder_cons_lift_bound_subst. exact Hsubstitution.
  - apply bi.forall_proper. intros value. apply IHformula.
    apply binder_cons_lift_bound_subst. exact Hsubstitution.
  - rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution).
    apply bi.and_proper; apply bi.wand_proper; try reflexivity.
    + apply IHformula1. exact Hsubstitution.
    + apply IHformula2. exact Hsubstitution.
  - rewrite (interp_subst_bound_expr_list substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - rewrite (interp_subst_bound_expr_list substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - apply bi.sep_proper.
    + apply IHformula1. exact Hsubstitution.
    + apply IHformula2. exact Hsubstitution.
Qed.

Corollary interp_instantiate_bound_core {F Δ t} predicates
    (witness : expr F Δ t) (value : tval t)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (body : Resource.core_assertion F (t :: Δ))
    (Hwitness : interp_expr formals binders atoms witness = Some value) :
  interp_core predicates formals binders atoms
      (Resource.instantiate_bound_core witness body) ≡
    interp_core predicates formals (binder_cons value binders) atoms body.
Proof.
  apply interp_subst_bound_core.
  apply interp_head_bound_subst. exact Hwitness.
Qed.

Lemma binder_cons_lift_formal_subst {F F' Δ t}
    (substitution : formal_subst F F' Δ) (value : tval t)
    (source_formals : formal_env F) (target_formals : formal_env F')
    (binders : binder_env Δ) (atoms : atom_env)
    (Hsubstitution : forall u (variable : formal F u),
      interp_expr target_formals binders atoms (substitution u variable) =
        Some (source_formals u variable)) :
  forall u (variable : formal F u),
    interp_expr target_formals (binder_cons value binders) atoms
        (lift_formal_subst substitution u variable) =
      Some (source_formals u variable).
Proof.
  intros u variable. unfold lift_formal_subst.
  rewrite interp_weaken_expr. apply Hsubstitution.
Qed.

Theorem interp_subst_formals_assertion {Γ F F' Δ} predicates
    (substitution : formal_subst F F' Δ)
    (source_formals : formal_env F) (target_formals : formal_env F')
    (binders : binder_env Δ) (atoms : atom_env)
    (runtime : data_stack_context Model Γ)
    (Hsubstitution : forall t (variable : formal F t),
      interp_expr target_formals binders atoms (substitution t variable) =
        Some (source_formals t variable))
    (formula : assertion Γ F Δ) (formula' : assertion Γ F' Δ) :
  subst_formals_assertion substitution formula = Some formula' ->
  interp_assertion predicates runtime target_formals binders atoms formula' ≡
    interp_assertion predicates runtime source_formals binders atoms formula.
Proof.
  revert F' substitution target_formals formula' Hsubstitution.
  induction formula; intros F' substitution target_formals formula'
      Hsubstitution Hresult; simpl in Hresult.
  - discriminate Hresult.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution).
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution).
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution).
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - destruct (subst_formals_assertion (lift_formal_subst substitution) formula)
      as [body'|] eqn:Hbody; [|discriminate Hresult].
    inversion Hresult; subst. simpl. apply bi.exist_proper. intros value.
    eapply IHformula; [|exact Hbody].
    apply binder_cons_lift_formal_subst. exact Hsubstitution.
  - destruct (subst_formals_assertion (lift_formal_subst substitution) formula)
      as [body'|] eqn:Hbody; [|discriminate Hresult].
    inversion Hresult; subst. simpl. apply bi.forall_proper. intros value.
    eapply IHformula; [|exact Hbody].
    apply binder_cons_lift_formal_subst. exact Hsubstitution.
  - destruct (subst_formals_assertion substitution formula1) as [then'|]
      eqn:Hthen; [|discriminate Hresult].
    destruct (subst_formals_assertion substitution formula2) as [else'|]
      eqn:Helse; [|discriminate Hresult].
    inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution).
    apply bi.and_proper; apply bi.wand_proper; try reflexivity.
    + eapply IHformula1; eauto.
    + eapply IHformula2; eauto.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr_list substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr_list substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - destruct (subst_formals_assertion substitution formula1) as [left'|]
      eqn:Hleft; [|discriminate Hresult].
    destruct (subst_formals_assertion substitution formula2) as [right'|]
      eqn:Hright; [|discriminate Hresult].
    inversion Hresult; subst. simpl. apply bi.sep_proper.
    + eapply IHformula1; eauto.
    + eapply IHformula2; eauto.
Qed.

(** Opening a closed core assertion into an ambient binder context.  The
    substitution is empty, so the hypothesis is vacuous. *)
Corollary interp_weaken_core_to {F Δ} predicates
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (formula : Resource.core_assertion F []) :
  interp_core predicates formals binders atoms
      (Resource.weaken_core_to Δ formula) ≡
    interp_core predicates formals empty_binder_env atoms formula.
Proof.
  apply interp_subst_bound_core.
  intros t variable. clear formula. dependent destruction variable.
Qed.

(** Core counterpart of [interp_subst_formals_assertion].
    [subst_formals_core] is total, so there is no [Some]-plumbing, and
    there is no [AStack] case -- which is also why the core version needs
    no [interp_reindex_stack_context] companion: a core assertion has no
    stack context to reindex. *)
Theorem interp_subst_formals_core {F F' Δ} predicates
    (substitution : formal_subst F F' Δ)
    (source_formals : formal_env F) (target_formals : formal_env F')
    (binders : binder_env Δ) (atoms : atom_env)
    (Hsubstitution : forall t (variable : formal F t),
      interp_expr target_formals binders atoms (substitution t variable) =
        Some (source_formals t variable))
    (formula : Resource.core_assertion F Δ) :
  interp_core predicates target_formals binders atoms
      (Resource.subst_formals_core substitution formula) ≡
    interp_core predicates source_formals binders atoms formula.
Proof.
  revert F' substitution target_formals Hsubstitution.
  induction formula; intros F' substitution target_formals Hsubstitution;
    cbn [Resource.subst_formals_core interp_core].
  - rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - reflexivity.
  - rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution).
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution).
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution).
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - apply bi.exist_proper. intros value. apply IHformula.
    apply binder_cons_lift_formal_subst. exact Hsubstitution.
  - apply bi.forall_proper. intros value. apply IHformula.
    apply binder_cons_lift_formal_subst. exact Hsubstitution.
  - rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution).
    apply bi.and_proper; apply bi.wand_proper; try reflexivity.
    + apply IHformula1. exact Hsubstitution.
    + apply IHformula2. exact Hsubstitution.
  - rewrite (interp_subst_formals_expr_list substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - rewrite (interp_subst_formals_expr_list substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - apply bi.sep_proper.
    + apply IHformula1. exact Hsubstitution.
    + apply IHformula2. exact Hsubstitution.
Qed.

Lemma interp_reindex_stack_context {Γ Γ' F Δ} predicates
    (formula : assertion Γ F Δ) (formula' : assertion Γ' F Δ)
    (Hreindex : reindex_stack_context formula formula') :
  forall (runtime : data_stack_context Model Γ)
    (runtime' : data_stack_context Model Γ')
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env),
    interp_assertion predicates runtime formals binders atoms formula ≡
      interp_assertion predicates runtime' formals binders atoms formula'.
Proof.
  induction Hreindex; intros runtime runtime' formals binders atoms; simpl;
    try reflexivity.
  - apply bi.exist_proper. intros value. apply IHHreindex.
  - apply bi.forall_proper. intros value. apply IHHreindex.
  - apply bi.and_proper; apply bi.wand_proper; try reflexivity.
    + apply IHHreindex1.
    + apply IHHreindex2.
  - apply bi.sep_proper.
    + apply IHHreindex1.
    + apply IHHreindex2.
Qed.

Lemma interp_assertion_mono
    (predicates1 predicates2 : predicate_semantics) {Γ F Δ}
    (formula : assertion Γ F Δ) :
  forall (runtime : data_stack_context Model Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env),
  □ (∀ predicate, ∀ values,
      predicates1 predicate values -∗ predicates2 predicate values) ⊢
  interp_assertion predicates1 runtime formals binders atoms formula -∗
  interp_assertion predicates2 runtime formals binders atoms formula.
Proof.
  induction formula; intros runtime formals binders atoms; simpl.
  - iIntros "_ H". iExact "H".
  - iIntros "_ H". iExact "H".
  - iIntros "_ H". iExact "H".
  - iIntros "_ H". iExact "H".
  - iIntros "_ H". iExact "H".
  - iIntros "_ H". iExact "H".
  - iIntros "_ H". iExact "H".
  - iIntros "#Hmon H". iDestruct "H" as (value) "H".
    iExists value. iApply (IHformula with "Hmon H").
  - iIntros "#Hmon H" (value). iApply (IHformula with "Hmon").
    iApply ("H" $! value).
  - iIntros "#Hmon H". iSplit.
    + iIntros "Hcondition". iApply (IHformula1 with "Hmon").
      iDestruct "H" as "[H _]". iApply "H". iExact "Hcondition".
    + iIntros "Hcondition". iApply (IHformula2 with "Hmon").
      iDestruct "H" as "[_ H]". iApply "H". iExact "Hcondition".
  - iIntros "_ H". iExact "H".
  - iIntros "#Hmon H". iDestruct "H" as (values) "[Hargs Hpredicate]".
    iExists values. iSplitL "Hargs"; first iExact "Hargs".
    iApply ("Hmon" $! predicate values). iExact "Hpredicate".
  - iIntros "#Hmon [Hleft Hright]". iSplitL "Hleft".
    + iApply (IHformula1 with "Hmon Hleft").
    + iApply (IHformula2 with "Hmon Hright").
Qed.

End WithModel.
End TermSemantics.

Module Semantics (Model : SEMANTIC_CONFIG).
Existing Instance Model.bi_affine.
Local Notation iProp := (bi_car Model.PROP).

Definition model_data : semantic_config_data Model.PROP := {|
  data_bi_affine := Model.bi_affine;
  data_stack_context := Model.stack_context;
  data_empty_stack_context := Model.empty_stack_context;
  data_stack_own := Model.stack_own;
  data_stack_own_exclusive := Model.stack_own_exclusive;
  data_field_own := Model.field_own;
  data_ghost_own := Model.ghost_own;
  data_invariant_own := Model.invariant_own;
|}.

Definition predicate_semantics := forall predicate,
  tval_list (Logic.predicate_args predicate) -> iProp.

Section WithPredicates.
Context (predicates : predicate_semantics).

Fixpoint interp_assertion {Γ F Δ}
    (runtime : Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (formula : assertion Γ F Δ) : iProp :=
  match formula with
  | AStack store =>
      Model.stack_own Γ runtime (interp_store formals binders atoms store)
  | AExpr condition =>
      ⌜interp_expr formals binders atoms condition = Some (VBool true)⌝%I
  | APure proposition => ⌜proposition⌝%I
  | AOwn field location chunk =>
      (∃ concrete_location concrete_chunk,
        ⌜interp_expr formals binders atoms location = Some concrete_location⌝ ∗
        ⌜interp_expr formals binders atoms chunk = Some concrete_chunk⌝ ∗
        Model.field_own field concrete_location concrete_chunk)%I
  | AGhostOwn field location chunk =>
      (∃ concrete_location concrete_chunk,
        ⌜interp_expr formals binders atoms location = Some concrete_location⌝ ∗
        ⌜interp_expr formals binders atoms chunk = Some concrete_chunk⌝ ∗
        Model.ghost_own field concrete_location concrete_chunk)%I
  | AFpuAllowed t old_chunk new_chunk =>
      (⌜exists old_value new_value,
        interp_expr formals binders atoms old_chunk = Some old_value /\
        interp_expr formals binders atoms new_chunk = Some new_value /\
        tval_fpu_allowed old_value new_value⌝)%I
  | ARAValid t chunk =>
      (⌜exists value, interp_expr formals binders atoms chunk = Some value /\
        tval_ra_valid value⌝)%I
  | AExists t body =>
      (∃ value : tval t,
        interp_assertion runtime formals (binder_cons value binders) atoms body)%I
  | AForall t body =>
      (∀ value : tval t,
        interp_assertion runtime formals (binder_cons value binders) atoms body)%I
  | AIte condition then_branch else_branch =>
      ((⌜interp_expr formals binders atoms condition = Some (VBool true)⌝ -∗
          interp_assertion runtime formals binders atoms then_branch) ∧
       (⌜interp_expr formals binders atoms condition <> Some (VBool true)⌝ -∗
          interp_assertion runtime formals binders atoms else_branch))%I
  | AInvariant invariant args =>
      (∃ values,
        ⌜interp_expr_list formals binders atoms args = Some values⌝ ∗
        Model.invariant_own invariant values)%I
  | APredicate predicate args =>
      (∃ values,
        ⌜interp_expr_list formals binders atoms args = Some values⌝ ∗
        predicates predicate values)%I
  | AAnd left_formula right_formula =>
      (interp_assertion runtime formals binders atoms left_formula ∗
       interp_assertion runtime formals binders atoms right_formula)%I
  end.

Lemma interp_assertion_stack {Γ F Δ} runtime formals binders atoms
    (store : symbolic_store Γ F Δ) :
  interp_assertion runtime formals binders atoms (AStack store) ≡
    Model.stack_own Γ runtime (interp_store formals binders atoms store).
Proof. reflexivity. Qed.

Lemma interp_assertion_and {Γ F Δ} runtime formals binders atoms
    (left right : assertion Γ F Δ) :
  interp_assertion runtime formals binders atoms (AAnd left right) ≡
    (interp_assertion runtime formals binders atoms left ∗
     interp_assertion runtime formals binders atoms right)%I.
Proof. reflexivity. Qed.

Lemma interp_assertion_exists {Γ F Δ} runtime formals binders atoms t
    (body : assertion Γ F (t :: Δ)) :
  interp_assertion runtime formals binders atoms (AExists t body) ≡
    (∃ value : tval t,
      interp_assertion runtime formals (binder_cons value binders) atoms body)%I.
Proof. reflexivity. Qed.

Lemma interp_assertion_forall {Γ F Δ} runtime formals binders atoms t
    (body : assertion Γ F (t :: Δ)) :
  interp_assertion runtime formals binders atoms (AForall t body) ≡
    (∀ value : tval t,
      interp_assertion runtime formals (binder_cons value binders) atoms body)%I.
Proof. reflexivity. Qed.

Lemma interp_assertion_ite {Γ F Δ} runtime formals binders atoms
    (condition : expr F Δ TBool) (then_branch else_branch : assertion Γ F Δ) :
  interp_assertion runtime formals binders atoms
      (AIte condition then_branch else_branch) ≡
    ((⌜interp_expr formals binders atoms condition = Some (VBool true)⌝ -∗
        interp_assertion runtime formals binders atoms then_branch) ∧
     (⌜interp_expr formals binders atoms condition <> Some (VBool true)⌝ -∗
        interp_assertion runtime formals binders atoms else_branch))%I.
Proof. reflexivity. Qed.

Theorem interp_rename_bound_assertion {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (runtime : Model.stack_context Γ)
    (Hrenaming : forall t (variable : bvar Δ t),
      target_binders t (renaming t variable) = source_binders t variable)
    (formula : assertion Γ F Δ) :
  interp_assertion runtime formals target_binders atoms
      (rename_bound_assertion renaming formula) ≡
    interp_assertion runtime formals source_binders atoms formula.
Proof.
  revert Δ' renaming source_binders target_binders Hrenaming.
  induction formula; intros Δ' renaming source_binders target_binders Hrenaming;
    simpl.
  - rewrite (interp_rename_bound_store renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - reflexivity.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming).
    rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming).
    rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming).
    rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - apply bi.exist_proper. intros value. apply IHformula.
    apply binder_cons_lift_bound_renaming. exact Hrenaming.
  - apply bi.forall_proper. intros value. apply IHformula.
    apply binder_cons_lift_bound_renaming. exact Hrenaming.
  - rewrite (interp_rename_bound_expr renaming formals source_binders
      target_binders atoms Hrenaming).
    apply bi.and_proper; apply bi.wand_proper; try reflexivity.
    + apply IHformula1. exact Hrenaming.
    + apply IHformula2. exact Hrenaming.
  - rewrite (interp_rename_bound_expr_list renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - rewrite (interp_rename_bound_expr_list renaming formals source_binders
      target_binders atoms Hrenaming). reflexivity.
  - apply bi.sep_proper.
    + apply IHformula1. exact Hrenaming.
    + apply IHformula2. exact Hrenaming.
Qed.

Corollary interp_weaken_assertion {Γ F Δ u}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (runtime : Model.stack_context Γ)
    (head : tval u) (formula : assertion Γ F Δ) :
  interp_assertion runtime formals (binder_cons head binders) atoms
      (weaken_assertion formula) ≡
    interp_assertion runtime formals binders atoms formula.
Proof.
  apply interp_rename_bound_assertion.
  intros t variable. apply binder_cons_weaken.
Qed.

Theorem interp_subst_bound_assertion {Γ F Δ Δ'}
    (substitution : bound_subst F Δ Δ')
    (formals : formal_env F) (source_binders : binder_env Δ)
    (target_binders : binder_env Δ') (atoms : atom_env)
    (runtime : Model.stack_context Γ)
    (Hsubstitution : forall t (variable : bvar Δ t),
      interp_expr formals target_binders atoms (substitution t variable) =
        Some (source_binders t variable))
    (formula : assertion Γ F Δ) (formula' : assertion Γ F Δ') :
  subst_bound_assertion substitution formula = Some formula' ->
  interp_assertion runtime formals target_binders atoms formula' ≡
    interp_assertion runtime formals source_binders atoms formula.
Proof.
  revert Δ' substitution target_binders formula' Hsubstitution.
  induction formula; intros Δ' substitution target_binders formula'
      Hsubstitution Hresult; simpl in Hresult.
  - discriminate Hresult.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution).
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution).
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution).
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - destruct (subst_bound_assertion (lift_bound_subst substitution) formula)
      as [body'|] eqn:Hbody; [|discriminate Hresult].
    inversion Hresult; subst. simpl. apply bi.exist_proper. intros value.
    eapply IHformula; [|exact Hbody].
    apply binder_cons_lift_bound_subst. exact Hsubstitution.
  - destruct (subst_bound_assertion (lift_bound_subst substitution) formula)
      as [body'|] eqn:Hbody; [|discriminate Hresult].
    inversion Hresult; subst. simpl. apply bi.forall_proper. intros value.
    eapply IHformula; [|exact Hbody].
    apply binder_cons_lift_bound_subst. exact Hsubstitution.
  - destruct (subst_bound_assertion substitution formula1) as [then'|]
      eqn:Hthen; [|discriminate Hresult].
    destruct (subst_bound_assertion substitution formula2) as [else'|]
      eqn:Helse; [|discriminate Hresult].
    inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr substitution formals source_binders
      target_binders atoms Hsubstitution).
    apply bi.and_proper; apply bi.wand_proper; try reflexivity.
    + eapply IHformula1; eauto.
    + eapply IHformula2; eauto.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr_list substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_bound_expr_list substitution formals source_binders
      target_binders atoms Hsubstitution). reflexivity.
  - destruct (subst_bound_assertion substitution formula1) as [left'|]
      eqn:Hleft; [|discriminate Hresult].
    destruct (subst_bound_assertion substitution formula2) as [right'|]
      eqn:Hright; [|discriminate Hresult].
    inversion Hresult; subst. simpl. apply bi.sep_proper.
    + eapply IHformula1; eauto.
    + eapply IHformula2; eauto.
Qed.

Lemma interp_head_bound_subst {F Δ t}
    (witness : expr F Δ t) (value : tval t)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (Hwitness : interp_expr formals binders atoms witness = Some value) :
  forall u (variable : bvar (t :: Δ) u),
    interp_expr formals binders atoms (head_bound_subst witness u variable) =
      Some (binder_cons value binders u variable).
Proof.
  intros u variable. destruct (view_member variable) eqn:Hview.
  - unfold head_bound_subst, binder_cons. rewrite Hview.
    repeat rewrite view_member_here. exact Hwitness.
  - unfold head_bound_subst, binder_cons. rewrite Hview.
    repeat rewrite view_member_there. reflexivity.
Qed.

Corollary interp_instantiate_bound_assertion {Γ F Δ t}
    (witness : expr F Δ t) (value : tval t)
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (runtime : Model.stack_context Γ)
    (body : assertion Γ F (t :: Δ)) (formula : assertion Γ F Δ)
    (Hwitness : interp_expr formals binders atoms witness = Some value)
    (Hinstantiate : instantiate_bound_assertion witness body = Some formula) :
  interp_assertion runtime formals binders atoms formula ≡
    interp_assertion runtime formals (binder_cons value binders) atoms body.
Proof.
  eapply interp_subst_bound_assertion; [|exact Hinstantiate].
  apply interp_head_bound_subst. exact Hwitness.
Qed.

Lemma binder_cons_lift_formal_subst {F F' Δ t}
    (substitution : formal_subst F F' Δ) (value : tval t)
    (source_formals : formal_env F) (target_formals : formal_env F')
    (binders : binder_env Δ) (atoms : atom_env)
    (Hsubstitution : forall u (variable : formal F u),
      interp_expr target_formals binders atoms (substitution u variable) =
        Some (source_formals u variable)) :
  forall u (variable : formal F u),
    interp_expr target_formals (binder_cons value binders) atoms
        (lift_formal_subst substitution u variable) =
      Some (source_formals u variable).
Proof.
  intros u variable. unfold lift_formal_subst.
  rewrite interp_weaken_expr. apply Hsubstitution.
Qed.

Theorem interp_subst_formals_assertion {Γ F F' Δ}
    (substitution : formal_subst F F' Δ)
    (source_formals : formal_env F) (target_formals : formal_env F')
    (binders : binder_env Δ) (atoms : atom_env)
    (runtime : Model.stack_context Γ)
    (Hsubstitution : forall t (variable : formal F t),
      interp_expr target_formals binders atoms (substitution t variable) =
        Some (source_formals t variable))
    (formula : assertion Γ F Δ) (formula' : assertion Γ F' Δ) :
  subst_formals_assertion substitution formula = Some formula' ->
  interp_assertion runtime target_formals binders atoms formula' ≡
    interp_assertion runtime source_formals binders atoms formula.
Proof.
  revert F' substitution target_formals formula' Hsubstitution.
  induction formula; intros F' substitution target_formals formula'
      Hsubstitution Hresult; simpl in Hresult.
  - discriminate Hresult.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution).
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution).
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution).
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - destruct (subst_formals_assertion (lift_formal_subst substitution) formula)
      as [body'|] eqn:Hbody; [|discriminate Hresult].
    inversion Hresult; subst. simpl. apply bi.exist_proper. intros value.
    eapply IHformula; [|exact Hbody].
    apply binder_cons_lift_formal_subst. exact Hsubstitution.
  - destruct (subst_formals_assertion (lift_formal_subst substitution) formula)
      as [body'|] eqn:Hbody; [|discriminate Hresult].
    inversion Hresult; subst. simpl. apply bi.forall_proper. intros value.
    eapply IHformula; [|exact Hbody].
    apply binder_cons_lift_formal_subst. exact Hsubstitution.
  - destruct (subst_formals_assertion substitution formula1) as [then'|]
      eqn:Hthen; [|discriminate Hresult].
    destruct (subst_formals_assertion substitution formula2) as [else'|]
      eqn:Helse; [|discriminate Hresult].
    inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr substitution source_formals
      target_formals binders atoms Hsubstitution).
    apply bi.and_proper; apply bi.wand_proper; try reflexivity.
    + eapply IHformula1; eauto.
    + eapply IHformula2; eauto.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr_list substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - inversion Hresult; subst. simpl.
    rewrite (interp_subst_formals_expr_list substitution source_formals
      target_formals binders atoms Hsubstitution). reflexivity.
  - destruct (subst_formals_assertion substitution formula1) as [left'|]
      eqn:Hleft; [|discriminate Hresult].
    destruct (subst_formals_assertion substitution formula2) as [right'|]
      eqn:Hright; [|discriminate Hresult].
    inversion Hresult; subst. simpl. apply bi.sep_proper.
    + eapply IHformula1; eauto.
    + eapply IHformula2; eauto.
Qed.

(** Procedure contracts contain no [AStack] assertion, so changing their
    phantom program-variable context cannot affect their interpretation.
    This is the semantic counterpart of [reindex_stack_context], used when a
    canonical callee contract is instantiated in a caller's stack context. *)
Lemma interp_reindex_stack_context {Γ Γ' F Δ}
    (formula : assertion Γ F Δ) (formula' : assertion Γ' F Δ)
    (Hreindex : reindex_stack_context formula formula') :
  forall (runtime : Model.stack_context Γ)
    (runtime' : Model.stack_context Γ')
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env),
    interp_assertion runtime formals binders atoms formula ≡
      interp_assertion runtime' formals binders atoms formula'.
Proof.
  induction Hreindex; intros runtime runtime' formals binders atoms; simpl;
    try reflexivity.
  - apply bi.exist_proper. intros value.
    apply IHHreindex.
  - apply bi.forall_proper. intros value.
    apply IHHreindex.
  - apply bi.and_proper; apply bi.wand_proper; try reflexivity.
    + apply IHHreindex1.
    + apply IHHreindex2.
  - apply bi.sep_proper.
    + apply IHHreindex1.
    + apply IHHreindex2.
Qed.

End WithPredicates.

Lemma interp_assertion_mono
    (predicates1 predicates2 : predicate_semantics) {Γ F Δ}
    (formula : assertion Γ F Δ) :
  forall (runtime : Model.stack_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (atoms : atom_env),
  □ (∀ predicate, ∀ values,
      predicates1 predicate values -∗ predicates2 predicate values) ⊢
  interp_assertion predicates1 runtime formals binders atoms formula -∗
  interp_assertion predicates2 runtime formals binders atoms formula.
Proof.
  induction formula; intros runtime formals binders atoms; simpl.
  - iIntros "_ H". iExact "H".
  - iIntros "_ H". iExact "H".
  - iIntros "_ H". iExact "H".
  - iIntros "_ H". iExact "H".
  - iIntros "_ H". iExact "H".
  - iIntros "_ H". iExact "H".
  - iIntros "_ H". iExact "H".
  - iIntros "#Hmon H". iDestruct "H" as (value) "H".
    iExists value. iApply (IHformula with "Hmon H").
  - iIntros "#Hmon H" (value). iApply (IHformula with "Hmon").
    iApply ("H" $! value).
  - iIntros "#Hmon H". iSplit.
    + iIntros "Hcondition". iApply (IHformula1 with "Hmon").
      iDestruct "H" as "[H _]". iApply "H". iExact "Hcondition".
    + iIntros "Hcondition". iApply (IHformula2 with "Hmon").
      iDestruct "H" as "[_ H]". iApply "H". iExact "Hcondition".
  - iIntros "_ H". iExact "H".
  - iIntros "#Hmon H". iDestruct "H" as (values) "[Hargs Hpredicate]".
    iExists values. iSplitL "Hargs"; first iExact "Hargs".
    iApply ("Hmon" $! predicate values).
    iExact "Hpredicate".
  - iIntros "#Hmon [Hleft Hright]". iSplitL "Hleft".
    + iApply (IHformula1 with "Hmon Hleft").
    + iApply (IHformula2 with "Hmon Hright").
Qed.

End Semantics.
End Make.
End TypedTranslation.
