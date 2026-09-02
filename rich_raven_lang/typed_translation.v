From Coq Require Import List Program.Equality.

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
Module Core := IR.Core.
Module Assertions := IR.Assertions.
Import Core Assertions IR.

Inductive tval_list : context -> Type :=
| TVNil : tval_list []
| TVCons t ts : tval t -> tval_list ts -> tval_list (t :: ts).

Arguments TVCons {_ _} _ _.

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

Fixpoint interp_store {Γ F Δ}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) : concrete_store Γ :=
  match store with
  | StoreNil => ConcreteNil
  | StoreCons reference tail =>
      ConcreteCons (interp_ref formals binders atoms reference)
        (interp_store formals binders atoms tail)
  end.

Definition interp_program_expr {Γ F Δ t}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (expression : pexpr Γ t) :
    option (tval t) :=
  interp_expr formals binders atoms (Hoare.symbolize_expr store expression).

Definition interp_program_expr_list {Γ F Δ ts}
    (formals : formal_env F) (binders : binder_env Δ) (atoms : atom_env)
    (store : symbolic_store Γ F Δ) (expressions : pexpr_list Γ ts) :
    option (tval_list ts) :=
  interp_expr_list formals binders atoms
    (Hoare.symbolize_expr_list store expressions).

Fixpoint formal_env_of_values {F} (values : tval_list F) : formal_env F :=
  match values with
  | TVNil => fun t variable => match variable with end
  | TVCons head tail => fun t variable =>
      match view_member variable with
      | MVHere => head
      | MVThere variable' => formal_env_of_values tail _ variable'
      end
  end.

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
  Parameter field_own : forall field,
    tval TRef -> tval (Logic.field_type field) -> bi_car PROP.
  Parameter invariant_own : forall invariant,
    tval_list (Logic.invariant_args invariant) -> bi_car PROP.
End SEMANTIC_CONFIG.

Module Semantics (Model : SEMANTIC_CONFIG).
Existing Instance Model.bi_affine.
Local Notation iProp := (bi_car Model.PROP).

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

Module Definitions (Defs : DEFINITION_ENV).

Inductive predicate_call : Type :=
| PredicateCall predicate :
    tval_list (Logic.predicate_args predicate) -> predicate_call.

Definition predicate_curry
  (interpretation : leibnizO predicate_call -> iProp) :
    predicate_semantics :=
  fun predicate values => interpretation (PredicateCall predicate values).

Definition predicate_F (atoms : atom_env)
    (interpretation : leibnizO predicate_call -> iProp) :
    leibnizO predicate_call -> iProp :=
  fun call =>
    match call with
    | PredicateCall predicate values =>
        interp_assertion (predicate_curry interpretation)
          Model.empty_stack_context (formal_env_of_values values)
          empty_binder_env atoms
          (Defs.predicate_body predicate)
    end.

Local Lemma predicate_call_ne
    (interpretation : leibnizO predicate_call -> iProp) :
  NonExpansive interpretation.
Proof. intros n left right Heq. change (left = right) in Heq. by subst. Qed.

Global Instance predicate_F_mono atoms : BiMonoPred (predicate_F atoms).
Proof.
  split; last first.
  { intros interpretation _ n left right Heq.
    change (left = right) in Heq. by subst. }
  intros interpretation1 interpretation2 Hne1 Hne2.
  iIntros "#Hmon" ([predicate values]).
  rewrite /predicate_F /=.
  iApply interp_assertion_mono.
  iIntros "!>" (predicate' values') "Hpredicate".
  iApply ("Hmon" $! (PredicateCall predicate' values')).
  iExact "Hpredicate".
Qed.

Definition predicate_interp (atoms : atom_env) : predicate_semantics :=
  fun predicate values =>
    bi_least_fixpoint (predicate_F atoms) (PredicateCall predicate values).

Lemma predicate_interp_unfold atoms predicate values :
  predicate_interp atoms predicate values ≡
    interp_assertion (predicate_interp atoms)
      Model.empty_stack_context (formal_env_of_values values)
      empty_binder_env atoms
      (Defs.predicate_body predicate).
Proof.
  exact (least_fixpoint_unfold (predicate_F atoms)
    (PredicateCall predicate values)).
Qed.

Lemma interp_assertion_predicate_unfold {Γ F Δ} atoms
    (runtime : Model.stack_context Γ)
    (formals : formal_env F) (binders : binder_env Δ)
    (predicate : pred_id)
    (args : expr_list F Δ (Logic.predicate_args predicate)) :
  interp_assertion (predicate_interp atoms) runtime formals binders atoms
      (APredicate (Γ := Γ) predicate args) ≡
    (∃ values,
      ⌜interp_expr_list formals binders atoms args = Some values⌝ ∗
      interp_assertion (predicate_interp atoms)
        Model.empty_stack_context (formal_env_of_values values)
        empty_binder_env atoms
        (Defs.predicate_body predicate))%I.
Proof.
  simpl. apply bi.exist_proper. intros values. apply bi.sep_proper.
  - reflexivity.
  - apply predicate_interp_unfold.
Qed.

Definition invariant_body_interp (atoms : atom_env) invariant
    (values : tval_list (Logic.invariant_args invariant)) : iProp :=
  interp_assertion (predicate_interp atoms)
    Model.empty_stack_context (formal_env_of_values values)
    empty_binder_env atoms
    (Defs.invariant_body invariant).

Lemma invariant_body_interp_unfold atoms invariant values :
  invariant_body_interp atoms invariant values ≡
    interp_assertion (predicate_interp atoms)
      Model.empty_stack_context (formal_env_of_values values)
      empty_binder_env atoms
      (Defs.invariant_body invariant).
Proof. reflexivity. Qed.

End Definitions.

End Semantics.
End Make.
End TypedTranslation.
