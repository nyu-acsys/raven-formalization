From Coq Require Import List String Program.Equality ZArith Lia
  Logic.ProofIrrelevance Logic.FunctionalExtensionality.
From stdpp Require Import gmap sets.

From raven Require Import verification.expressions verification.assertions verification.ir verification.hoare_rules.

Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

(** The typed Raven Hoare calculus.  This module contains only
    syntax-directed proof rules; their semantic validation is a separate
    concern. *)
Module Hoare.

Import Core IR.


Module ResourceHoare := ResourceHoare.
Module IR := ResourceHoare.IR.
Module Core := IR.Core.
Module Assertions := IR.Assertions.
Module Resource := IR.Resource.
Import Core Assertions IR.

Section WithSignature.
Context {RAs : RAValueConfig} {Logic : LogicSignature}.

Definition mask := gset inv_id.


Fixpoint allocated_physical_fields_assertion {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
    assertion Γ F (TRef :: Δ) :=
  match fields with
  | [] => APure True
  | FieldInit field value :: fields' =>
      AAnd (AOwn field (ERef (RefBound MHere))
        (weaken_expr (symbolize_expr store value)))
        (allocated_physical_fields_assertion store fields')
  end.

Fixpoint allocated_ghost_fields_assertion {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) :
    assertion Γ F (TRef :: Δ) :=
  match fields with
  | [] => APure True
  | GhostFieldInit resource field Hfield value :: fields' =>
      AAnd
        (AGhostOwn field (ERef (RefBound MHere))
          (eq_rect (TRA resource) (expr F (TRef :: Δ))
            (weaken_expr (symbolize_expr store value))
            (field_type field) (eq_sym Hfield)))
        (allocated_ghost_fields_assertion store fields')
  end.

Definition allocated_fields_assertion {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
  assertion Γ F (TRef :: Δ) :=
  AAnd
    (allocated_physical_fields_assertion store
      (physical_field_initializers fields))
    (allocated_ghost_fields_assertion store (ghost_field_initializers fields)).

Fixpoint ghost_initializers_valid_assertion {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) :
    assertion Γ F Δ :=
  match fields with
  | [] => APure True
  | GhostFieldInit resource _ _ value :: fields' =>
      AAnd (ARAValid (TRA resource) (symbolize_expr store value))
        (ghost_initializers_valid_assertion store fields')
  end.

Lemma allocated_physical_fields_assertion_stack_free {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
  stack_free (allocated_physical_fields_assertion store fields).
Proof.
  induction fields as [|[field value] fields IH]; cbn.
  - constructor.
  - constructor; [constructor|exact IH].
Qed.

Lemma allocated_ghost_fields_assertion_stack_free {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) :
  stack_free (allocated_ghost_fields_assertion store fields).
Proof.
  induction fields as [|[resource field Hfield value] fields IH]; cbn.
  - constructor.
  - constructor; [constructor|exact IH].
Qed.

Lemma allocated_fields_assertion_stack_free {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
  stack_free (allocated_fields_assertion store fields).
Proof.
  unfold allocated_fields_assertion.
  constructor.
  - apply allocated_physical_fields_assertion_stack_free.
  - apply allocated_ghost_fields_assertion_stack_free.
Qed.

Lemma ghost_initializers_valid_assertion_stack_free {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) :
  stack_free (ghost_initializers_valid_assertion store fields).
Proof.
  induction fields as [|[resource field Hfield value] fields IH]; cbn.
  - constructor.
  - constructor; [constructor|exact IH].
Qed.

Lemma allocated_physical_fields_assertion_stack_count {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
  assertion_stack_count (allocated_physical_fields_assertion store fields) = 0.
Proof.
  apply stack_free_assertion_stack_count.
  apply allocated_physical_fields_assertion_stack_free.
Qed.

Lemma allocated_ghost_fields_assertion_stack_count {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) :
  assertion_stack_count (allocated_ghost_fields_assertion store fields) = 0.
Proof.
  apply stack_free_assertion_stack_count.
  apply allocated_ghost_fields_assertion_stack_free.
Qed.

Lemma ghost_initializers_valid_assertion_stack_count {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (ghost_field_init Γ)) :
  assertion_stack_count (ghost_initializers_valid_assertion store fields) = 0.
Proof.
  apply stack_free_assertion_stack_count.
  apply ghost_initializers_valid_assertion_stack_free.
Qed.


(** One-step entailments contain only semantic/structural primitives.
    Reflexivity, transitivity, and congruence are factored into the closure
    below instead of repeated as domain-specific constructors. *)

(** Proof-relevant identity of one invariant instance.  The declaration ID
    remains separate because today's executable mask analysis is ID-based;
    the argument vector is retained so a future per-instance analysis can use
    the complete key without changing normalization or semantic rule
    interfaces. *)
Record invariant_instance_key {F Δ} (invariant : inv_id) : Type := {
  invariant_instance_arguments :
    expr_list F Δ (invariant_args invariant);
}.

(** Equality certificate generated by the combined atomicity/Hoare
    certification pass.  Equality is conditional on an ordinary Raven
    assertion, exactly matching the frontend's stability-assertion scheme.
    A ghost-snapshot extension changes only [condition] and the expressions
    stored in the keys. *)
Record invariant_instance_equality {F Δ} (invariant : inv_id)
    (opening closing : invariant_instance_key invariant) : Type := {
  invariant_instance_equality_condition : expr F Δ TBool;
  invariant_instance_equal_assuming :
    expr_list_equal_assuming invariant_instance_equality_condition _
      (invariant_instance_arguments invariant closing)
      (invariant_instance_arguments invariant opening);
}.

Definition invariant_instance_key_of_arguments {F Δ invariant}
    (arguments : expr_list F Δ (invariant_args invariant)) :
    @invariant_instance_key F Δ invariant :=
  {| invariant_instance_arguments := arguments |}.

(** Store-indexed boundary evidence consumed by normalization.  Source
    annotations and symbolic stores are retained independently: explicit
    equality assertions may justify different expressions, and a future
    snapshot pass may replace either side without changing this interface. *)
Record invariant_access_boundary_equality {Γ F Δ} (invariant : inv_id)
    (opening_arguments closing_arguments :
      gexpr_list Γ (invariant_args invariant))
    (opening_store closing_store : symbolic_store Γ F Δ) : Type := {
  invariant_boundary_instance_equality :
    invariant_instance_equality invariant
      (invariant_instance_key_of_arguments
        (symbolize_expr_list opening_store opening_arguments))
      (invariant_instance_key_of_arguments
        (symbolize_expr_list closing_store closing_arguments));
}.


Lemma weaken_bound_renaming_injective {Δ u} :
  bound_renaming_injective (@weaken_bound_renaming Δ u).
Proof.
  intros t left right Hequal.
  unfold weaken_bound_renaming in Hequal.
  dependent destruction Hequal. reflexivity.
Qed.

Lemma lift_bound_renaming_injective {Δ Δ' u}
    (renaming : bound_renaming Δ Δ') :
  bound_renaming_injective renaming ->
  bound_renaming_injective (lift_bound_renaming (u := u) renaming).
Proof.
  intro Hinjective. intros t left right Hequal.
  dependent destruction left; dependent destruction right;
    unfold lift_bound_renaming in Hequal;
    rewrite ?view_member_here, ?view_member_there in Hequal;
    try discriminate; try reflexivity.
  injection Hequal as Hrenamed. f_equal.
  apply Hinjective. dependent destruction Hrenamed.
  match goal with H : renaming _ _ = renaming _ _ |- _ => exact H end.
Qed.

(** Generic renaming / substitution algebra, independent of procedure and
    resource contracts. *)
End WithSignature.
Module RenamingFacts.

Section WithSignature.
Context {RAs : RAValueConfig} {Logic : LogicSignature}.
(** Formal substitution commutes with a change of the ambient binder
    context.  These small syntactic facts are kept here, next to contract
    instantiation, since they are needed when an invariant instance is
    carried under an additional logical binder. *)
Definition rename_formal_subst {F F' Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (substitution : formal_subst F F' Δ) : formal_subst F F' Δ' :=
  fun t variable => rename_bound_expr renaming (substitution t variable).

Lemma rename_bound_expr_lift_weaken {F Δ Δ' t u}
    (renaming : bound_renaming Δ Δ')
    (expression : expr F Δ t) :
  rename_bound_expr (lift_bound_renaming renaming)
      (weaken_expr (u := u) expression) =
    weaken_expr (rename_bound_expr renaming expression).
Proof.
  induction expression; cbn [rename_bound_expr weaken_expr
    rename_bound_ref weaken_ref lift_bound_renaming].
  - destruct reference; cbn [rename_bound_ref weaken_ref]; try reflexivity.
    unfold lift_bound_renaming. rewrite view_member_there. reflexivity.
  - reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma rename_bound_expr_list_lift_weaken {F Δ Δ' ts u}
    (renaming : bound_renaming Δ Δ')
    (expressions : expr_list F Δ ts) :
  rename_bound_expr_list (lift_bound_renaming renaming)
      (weaken_expr_list (u := u) expressions) =
    weaken_expr_list (rename_bound_expr_list renaming expressions).
Proof.
  induction expressions; cbn [rename_bound_expr_list weaken_expr_list].
  - reflexivity.
  - f_equal; auto using rename_bound_expr_lift_weaken.
Qed.

Lemma rename_formal_subst_lift {F F' Δ Δ'} (u : typ)
    (renaming : bound_renaming Δ Δ')
    (substitution : formal_subst F F' Δ) :
  rename_formal_subst (lift_bound_renaming (u := u) renaming)
      (lift_formal_subst substitution) =
    lift_formal_subst (u := u) (rename_formal_subst renaming substitution).
Proof.
  apply functional_extensionality_dep; intro result_type.
  apply functional_extensionality; intro variable.
  apply rename_bound_expr_lift_weaken.
Qed.

Lemma subst_formals_expr_rename {F F' Δ Δ' t}
    (renaming : bound_renaming Δ Δ')
    (substitution : formal_subst F F' Δ)
    (expression : expr F Δ t) :
  subst_formals_expr (rename_formal_subst renaming substitution)
      (rename_bound_expr renaming expression) =
    rename_bound_expr renaming (subst_formals_expr substitution expression).
Proof.
  induction expression; cbn [subst_formals_expr subst_formals_ref
    rename_bound_expr rename_bound_ref]; try reflexivity.
  - destruct reference; cbn; try reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma subst_formals_expr_list_rename {F F' Δ Δ' ts}
    (renaming : bound_renaming Δ Δ')
    (substitution : formal_subst F F' Δ)
    (expressions : expr_list F Δ ts) :
  subst_formals_expr_list (rename_formal_subst renaming substitution)
      (rename_bound_expr_list renaming expressions) =
    rename_bound_expr_list renaming
      (subst_formals_expr_list substitution expressions).
Proof.
  induction expressions; cbn [subst_formals_expr_list rename_bound_expr_list].
  - reflexivity.
  - f_equal; [apply subst_formals_expr_rename|exact IHexpressions].
Qed.

Lemma subst_formals_assertion_rename {Γ F F' Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (substitution : formal_subst F F' Δ)
    (formula : assertion Γ F Δ) :
  forall target,
    subst_formals_assertion substitution formula = Some target ->
    subst_formals_assertion (rename_formal_subst renaming substitution)
      (rename_bound_assertion renaming formula) =
    Some (rename_bound_assertion renaming target).
Proof.
  revert Δ' renaming substitution.
  induction formula as [store | condition | proposition | field location chunk
    | field location chunk | r old_chunk new_chunk | t chunk
    | t body IHbody | t body IHbody | condition then_branch else_branch
      IHthen IHelse | invariant args | predicate args
    | left right IHleft IHright]; intros Δ' renaming substitution target Hresult;
    cbn in Hresult |- *.
  - discriminate.
  - inversion Hresult; subst target. cbn.
    rewrite subst_formals_expr_rename. reflexivity.
  - inversion Hresult; reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_formals_expr_rename renaming substitution chunk).
    rewrite (subst_formals_expr_rename renaming substitution chunk0). reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_formals_expr_rename renaming substitution chunk).
    rewrite (subst_formals_expr_rename renaming substitution chunk0). reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_formals_expr_rename renaming substitution new_chunk).
    rewrite (subst_formals_expr_rename renaming substitution new_chunk0). reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_formals_expr_rename renaming substitution chunk0). reflexivity.
  - destruct (subst_formals_assertion (lift_formal_subst substitution) IHbody)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target.
    rewrite <- rename_formal_subst_lift.
    rewrite (IHIHbody (body :: Δ')
      (lift_bound_renaming (u := body) renaming)
      (lift_formal_subst substitution) body' Hbody). reflexivity.
  - destruct (subst_formals_assertion (lift_formal_subst substitution) IHbody)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target.
    rewrite <- rename_formal_subst_lift.
    rewrite (IHIHbody (body :: Δ')
      (lift_bound_renaming (u := body) renaming)
      (lift_formal_subst substitution) body' Hbody). reflexivity.
  - destruct (subst_formals_assertion substitution else_branch)
      as [formula1'|] eqn:Hfirst; [|discriminate].
    destruct (subst_formals_assertion substitution IHelse)
      as [formula2'|] eqn:Hsecond; [|discriminate].
    inversion Hresult; subst target.
    cbn.
    rewrite (subst_formals_expr_rename renaming substitution then_branch).
    rewrite (IHthen Δ' renaming substitution formula1' Hfirst),
      (IHIHelse Δ' renaming substitution formula2' Hsecond). reflexivity.
  - rewrite subst_formals_expr_list_rename. inversion Hresult. reflexivity.
  - rewrite subst_formals_expr_list_rename. inversion Hresult. reflexivity.
  - destruct (subst_formals_assertion substitution right)
      as [formula1'|] eqn:Hfirst; [|discriminate].
    destruct (subst_formals_assertion substitution IHright)
      as [formula2'|] eqn:Hsecond; [|discriminate].
    inversion Hresult; subst target.
    rewrite (IHleft Δ' renaming substitution formula1' Hfirst),
      (IHIHright Δ' renaming substitution formula2' Hsecond). reflexivity.
Qed.

(** The corresponding operation for a bound substitution changes only its
    target binder context; the source context of the assertion is unchanged. *)
Definition rename_bound_subst {F Δ Δ' Δ''}
    (renaming : bound_renaming Δ' Δ'')
    (substitution : bound_subst F Δ Δ') : bound_subst F Δ Δ'' :=
  fun t variable => rename_bound_expr renaming (substitution t variable).

Lemma rename_bound_subst_lift {F Δ Δ' Δ''} (u : typ)
    (renaming : bound_renaming Δ' Δ'')
    (substitution : bound_subst F Δ Δ') :
  rename_bound_subst (lift_bound_renaming (u := u) renaming)
      (lift_bound_subst substitution) =
    lift_bound_subst (u := u) (rename_bound_subst renaming substitution).
Proof.
  apply functional_extensionality_dep; intro result_type.
  apply functional_extensionality; intro variable.
  dependent destruction variable.
  - unfold rename_bound_subst, lift_bound_subst.
    rewrite view_member_here.
    cbn [rename_bound_expr rename_bound_ref].
    unfold lift_bound_renaming. rewrite view_member_here. reflexivity.
  - unfold rename_bound_subst, lift_bound_subst.
    rewrite view_member_there.
    apply rename_bound_expr_lift_weaken.
Qed.

Lemma subst_bound_expr_rename {F Δ Δ' Δ'' t}
    (renaming : bound_renaming Δ' Δ'')
    (substitution : bound_subst F Δ Δ')
    (expression : expr F Δ t) :
  subst_bound_expr (rename_bound_subst renaming substitution) expression =
    rename_bound_expr renaming (subst_bound_expr substitution expression).
Proof.
  induction expression; cbn [subst_bound_expr subst_bound_ref
    rename_bound_expr rename_bound_ref]; try reflexivity.
  - destruct reference; cbn; try reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma subst_bound_expr_list_rename {F Δ Δ' Δ'' ts}
    (renaming : bound_renaming Δ' Δ'')
    (substitution : bound_subst F Δ Δ')
    (expressions : expr_list F Δ ts) :
  subst_bound_expr_list (rename_bound_subst renaming substitution) expressions =
    rename_bound_expr_list renaming
      (subst_bound_expr_list substitution expressions).
Proof.
  induction expressions; cbn [subst_bound_expr_list rename_bound_expr_list].
  - reflexivity.
  - f_equal; [apply subst_bound_expr_rename|exact IHexpressions].
Qed.

Lemma subst_bound_assertion_rename {Γ F Δ Δ' Δ''}
    (renaming : bound_renaming Δ' Δ'')
    (substitution : bound_subst F Δ Δ')
    (formula : assertion Γ F Δ) :
  forall target,
    subst_bound_assertion substitution formula = Some target ->
    subst_bound_assertion (rename_bound_subst renaming substitution) formula =
    Some (rename_bound_assertion renaming target).
Proof.
  revert Δ' Δ'' renaming substitution.
  induction formula as [store | condition | proposition | field location chunk
    | field location chunk | r old_chunk new_chunk | t chunk
    | t body IHbody | t body IHbody | condition then_branch else_branch
      IHthen IHelse | invariant args | predicate args
    | left right IHleft IHright]; intros Δ' Δ'' renaming substitution target Hresult;
    cbn in Hresult |- *.
  - discriminate.
  - inversion Hresult; subst target. cbn.
    rewrite subst_bound_expr_rename. reflexivity.
  - inversion Hresult; reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_bound_expr_rename renaming substitution chunk).
    rewrite (subst_bound_expr_rename renaming substitution chunk0). reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_bound_expr_rename renaming substitution chunk).
    rewrite (subst_bound_expr_rename renaming substitution chunk0). reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_bound_expr_rename renaming substitution new_chunk).
    rewrite (subst_bound_expr_rename renaming substitution new_chunk0). reflexivity.
  - inversion Hresult; subst target. cbn.
    rewrite (subst_bound_expr_rename renaming substitution chunk0). reflexivity.
  - destruct (subst_bound_assertion (lift_bound_subst substitution) IHbody)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target.
    rewrite <- rename_bound_subst_lift.
    rewrite (IHIHbody (body :: Δ') (body :: Δ'')
      (lift_bound_renaming (u := body) renaming)
      (lift_bound_subst substitution) body' Hbody). reflexivity.
  - destruct (subst_bound_assertion (lift_bound_subst substitution) IHbody)
      as [body'|] eqn:Hbody; [|discriminate].
    inversion Hresult; subst target.
    rewrite <- rename_bound_subst_lift.
    rewrite (IHIHbody (body :: Δ') (body :: Δ'')
      (lift_bound_renaming (u := body) renaming)
      (lift_bound_subst substitution) body' Hbody). reflexivity.
  - destruct (subst_bound_assertion substitution else_branch)
      as [formula1'|] eqn:Hfirst; [|discriminate].
    destruct (subst_bound_assertion substitution IHelse)
      as [formula2'|] eqn:Hsecond; [|discriminate].
    inversion Hresult; subst target.
    rewrite (subst_bound_expr_rename renaming substitution then_branch).
    rewrite (IHthen Δ' Δ'' renaming substitution formula1' Hfirst),
      (IHIHelse Δ' Δ'' renaming substitution formula2' Hsecond). reflexivity.
  - rewrite subst_bound_expr_list_rename. inversion Hresult. reflexivity.
  - rewrite subst_bound_expr_list_rename. inversion Hresult. reflexivity.
  - destruct (subst_bound_assertion substitution right)
      as [formula1'|] eqn:Hfirst; [|discriminate].
    destruct (subst_bound_assertion substitution IHright)
      as [formula2'|] eqn:Hsecond; [|discriminate].
    inversion Hresult; subst target.
    rewrite (IHleft Δ' Δ'' renaming substitution formula1' Hfirst),
      (IHIHright Δ' Δ'' renaming substitution formula2' Hsecond). reflexivity.
Qed.

Lemma reindex_stack_context_rename {F Δ Δ' Γ Γ'}
    (renaming : bound_renaming Δ Δ')
    (source : assertion Γ F Δ) (target : assertion Γ' F Δ) :
  reindex_stack_context source target ->
  reindex_stack_context (rename_bound_assertion renaming source)
    (rename_bound_assertion renaming target).
Proof.
  intro Hreindex.
  revert Δ' renaming.
  induction Hreindex; intros Δ' renaming;
    cbn [rename_bound_assertion]; try constructor; eauto.
Qed.

Lemma rename_empty_bound_subst {F Δ u} :
  rename_bound_subst (@weaken_bound_renaming Δ u)
      (@empty_bound_subst _ F Δ) =
    @empty_bound_subst _ F (u :: Δ).
Proof.
  apply functional_extensionality_dep; intro result_type.
  apply functional_extensionality; intro variable.
  dependent destruction variable.
Qed.

Lemma rename_empty_bound_subst_general {F Δ Δ'}
    (renaming : bound_renaming Δ Δ') :
  rename_bound_subst renaming (@empty_bound_subst _ F Δ) =
    @empty_bound_subst _ F Δ'.
Proof.
  apply functional_extensionality_dep; intro result_type.
  apply functional_extensionality; intro variable.
  dependent destruction variable.
Qed.

Lemma lookup_expr_list_there {F Δ t ts u}
    (expression : expr F Δ t) (expressions : expr_list F Δ ts)
    (variable : member ts u) :
  lookup_expr_list (ExprCons expression expressions) (MThere variable) =
    lookup_expr_list expressions variable.
Proof.
  unfold lookup_expr_list, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl).
  reflexivity.
Qed.

Lemma rename_formal_subst_expr_list {F Δ Δ' ts}
    (renaming : bound_renaming Δ Δ')
    (arguments : expr_list F Δ ts) :
  rename_formal_subst renaming (expr_list_formal_subst arguments) =
    expr_list_formal_subst (rename_bound_expr_list renaming arguments).
Proof.
  apply functional_extensionality_dep; intro result_type.
  apply functional_extensionality; intro variable.
  induction arguments as [|head_type tail head arguments IH].
  - dependent destruction variable.
  - dependent destruction variable.
    + unfold rename_formal_subst, expr_list_formal_subst.
      rewrite lookup_expr_list_here.
      cbn [rename_bound_expr_list].
      rewrite lookup_expr_list_here. reflexivity.
    + unfold rename_formal_subst, expr_list_formal_subst.
      rewrite lookup_expr_list_there.
      cbn [rename_bound_expr_list].
      rewrite lookup_expr_list_there. apply IH.
Qed.

Lemma rename_bound_expr_weaken {F Δ t u}
    (expression : expr F Δ t) :
  rename_bound_expr (@weaken_bound_renaming Δ u) expression =
    weaken_expr (u := u) expression.
Proof.
  induction expression; cbn [rename_bound_expr rename_bound_ref
    weaken_expr weaken_ref weaken_bound_renaming]; try reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma rename_bound_expr_list_weaken {F Δ ts u}
    (expressions : expr_list F Δ ts) :
  rename_bound_expr_list (@weaken_bound_renaming Δ u) expressions =
    weaken_expr_list (u := u) expressions.
Proof.
  induction expressions; cbn [rename_bound_expr_list weaken_expr_list].
  - reflexivity.
  - f_equal; [apply rename_bound_expr_weaken | exact IHexpressions].
Qed.
Lemma rename_bound_assertion_compose {Γ F Δ Δ' Δ''}
    (first : bound_renaming Δ Δ') (second : bound_renaming Δ' Δ'')
    (formula : assertion Γ F Δ) :
  rename_bound_assertion second (rename_bound_assertion first formula) =
    rename_bound_assertion (compose_bound_renaming first second) formula.
Proof.
  revert Δ' Δ'' first second.
  induction formula; intros; cbn [rename_bound_assertion];
    try (f_equal; eauto using rename_bound_expr_compose,
      rename_bound_expr_list_compose, rename_bound_store_compose).
  all: rewrite <- lift_bound_renaming_compose; apply IHformula.
Qed.

(** Renaming the caller's binder context leaves the callee's return-binder
    injection unchanged: [return_bound_renaming] targets binder zero, and
    [lift_bound_renaming] fixes binder zero.  Needed by a CONTRACT_ENV
    implementation to discharge [instantiated_post_value_rename]. *)
Lemma compose_return_bound_renaming {Δ Δ' t} (renaming : bound_renaming Δ Δ') :
  compose_bound_renaming (@return_bound_renaming Δ t)
    (lift_bound_renaming renaming) = @return_bound_renaming Δ' t.
Proof.
  apply functional_extensionality_dep; intro u.
  apply functional_extensionality; intro variable.
  unfold compose_bound_renaming, return_bound_renaming.
  dependent destruction variable.
  - rewrite view_member_here. apply lift_bound_renaming_here.
  - dependent destruction variable.
Qed.

(** The identity renaming is useful when a bound variable is temporarily
    exposed as an existential witness and then reintroduced at the head of
    the surrounding context. *)
Lemma compose_exchange_bound_renaming {Δ t u} :
  compose_bound_renaming
    (@exchange_bound_renaming Δ t u)
    (@exchange_bound_renaming Δ u t) =
  (@identity_bound_renaming (t :: u :: Δ)).
Proof.
  apply functional_extensionality_dep. intro result.
  apply functional_extensionality. intro variable.
  dependent destruction variable.
  - unfold compose_bound_renaming, identity_bound_renaming.
    rewrite exchange_bound_renaming_here,
      exchange_bound_renaming_there_here. reflexivity.
  - dependent destruction variable.
    + unfold compose_bound_renaming, identity_bound_renaming.
      rewrite exchange_bound_renaming_there_here,
        exchange_bound_renaming_here. reflexivity.
    + unfold compose_bound_renaming, identity_bound_renaming.
      rewrite !exchange_bound_renaming_there_there. reflexivity.
Qed.

Lemma exchange_bound_renaming_injective {Δ t u} :
  bound_renaming_injective (@exchange_bound_renaming Δ t u).
Proof.
  intros result left right Hequal.
  pose proof (f_equal
    (@exchange_bound_renaming Δ u t result) Hequal) as Hinverse.
  change
    (compose_bound_renaming (@exchange_bound_renaming Δ t u)
      (@exchange_bound_renaming Δ u t) result left =
     compose_bound_renaming (@exchange_bound_renaming Δ t u)
      (@exchange_bound_renaming Δ u t) result right) in Hinverse.
  rewrite compose_exchange_bound_renaming in Hinverse. exact Hinverse.
Qed.

Lemma rename_bound_assertion_identity {Γ F Δ}
    (formula : assertion Γ F Δ) :
  rename_bound_assertion identity_bound_renaming formula = formula.
Proof.
  induction formula; cbn [rename_bound_assertion identity_bound_renaming];
    try reflexivity.
  - rewrite rename_bound_store_identity. reflexivity.
  - rewrite rename_bound_expr_identity. reflexivity.
  - rewrite rename_bound_expr_identity, rename_bound_expr_identity. reflexivity.
  - rewrite rename_bound_expr_identity, rename_bound_expr_identity. reflexivity.
  - rewrite rename_bound_expr_identity, rename_bound_expr_identity. reflexivity.
  - rewrite rename_bound_expr_identity. reflexivity.
  - rewrite lift_identity_bound_renaming, IHformula. reflexivity.
  - rewrite lift_identity_bound_renaming, IHformula. reflexivity.
  - rewrite rename_bound_expr_identity, IHformula1, IHformula2. reflexivity.
  - rewrite rename_bound_expr_list_identity. reflexivity.
  - rewrite rename_bound_expr_list_identity. reflexivity.
  - rewrite IHformula1, IHformula2. reflexivity.
Qed.

Lemma compose_bound_renaming_lift_weaken_head_current {Δ t} :
    compose_bound_renaming
      (lift_bound_renaming (@weaken_bound_renaming Δ t))
      (head_bound_renaming MHere) =
    (@identity_bound_renaming (t :: Δ)).
Proof.
  apply functional_extensionality_dep. intros u.
  apply functional_extensionality. intro variable.
  dependent destruction variable.
  - unfold compose_bound_renaming, lift_bound_renaming,
      weaken_bound_renaming, head_bound_renaming,
      identity_bound_renaming.
    rewrite !view_member_here. reflexivity.
  - unfold compose_bound_renaming, lift_bound_renaming,
      weaken_bound_renaming, head_bound_renaming,
      identity_bound_renaming.
    rewrite !view_member_there. reflexivity.
Qed.

Lemma rename_bound_assertion_lift_weaken_head_current {Γ F Δ t}
    (body : assertion Γ F (t :: Δ)) :
  rename_bound_assertion (head_bound_renaming MHere)
      (rename_bound_assertion
        (lift_bound_renaming (@weaken_bound_renaming Δ t)) body) = body.
Proof.
  rewrite rename_bound_assertion_compose.
  rewrite compose_bound_renaming_lift_weaken_head_current.
  apply rename_bound_assertion_identity.
Qed.

Lemma allocated_physical_fields_assertion_rename {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (store : symbolic_store Γ F Δ) fields :
  rename_bound_assertion (lift_bound_renaming renaming)
      (allocated_physical_fields_assertion store fields) =
    allocated_physical_fields_assertion
      (rename_bound_store renaming store) fields.
Proof.
  induction fields as [|[field value] fields IH]; cbn.
  - reflexivity.
  - unfold lift_bound_renaming at 1. rewrite view_member_here.
    rewrite symbolize_expr_rename_bound_store.
    rewrite rename_bound_expr_lift_weaken.
    rewrite IH. reflexivity.
Qed.

Lemma allocated_ghost_fields_assertion_rename {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (store : symbolic_store Γ F Δ) fields :
  rename_bound_assertion (lift_bound_renaming renaming)
      (allocated_ghost_fields_assertion store fields) =
    allocated_ghost_fields_assertion
      (rename_bound_store renaming store) fields.
Proof.
  induction fields as [|[resource field Hfield value] fields IH]; cbn.
  - reflexivity.
  - unfold lift_bound_renaming at 1. rewrite view_member_here.
    rewrite symbolize_expr_rename_bound_store.
    destruct Hfield.
    cbn.
    rewrite rename_bound_expr_lift_weaken.
    rewrite IH. reflexivity.
Qed.

Lemma allocated_fields_assertion_rename {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (store : symbolic_store Γ F Δ) fields :
  rename_bound_assertion (lift_bound_renaming renaming)
      (allocated_fields_assertion store fields) =
    allocated_fields_assertion (rename_bound_store renaming store) fields.
Proof.
  unfold allocated_fields_assertion. cbn.
  rewrite allocated_physical_fields_assertion_rename.
  rewrite allocated_ghost_fields_assertion_rename. reflexivity.
Qed.

Lemma ghost_initializers_valid_assertion_rename {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (store : symbolic_store Γ F Δ) fields :
  rename_bound_assertion renaming
      (ghost_initializers_valid_assertion store fields) =
    ghost_initializers_valid_assertion
      (rename_bound_store renaming store) fields.
Proof.
  induction fields as [|[resource field Hfield value] fields IH]; cbn.
  - reflexivity.
  - rewrite symbolize_expr_rename_bound_store.
    rewrite IH. reflexivity.
Qed.

Lemma reindex_stack_context_stack_free {F Δ Γ Γ'}
    (source : assertion Γ F Δ) (target : assertion Γ' F Δ) :
  reindex_stack_context source target ->
  stack_free source ->
  stack_free target.
Proof.
  intro Hreindex.
  induction Hreindex; intro Hfree;
    dependent destruction Hfree; try constructor; eauto.
Qed.
(** Renaming algebra for the resource core.  Contract-independent, and
    needed both by the erasure and by concrete contract environments. *)
Lemma subst_formals_core_rename {F F' Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (substitution : formal_subst F F' Δ) (formula : Resource.core_assertion F Δ) :
  Resource.subst_formals_core (rename_formal_subst renaming substitution)
      (Resource.rename_bound_core renaming formula) =
    Resource.rename_bound_core renaming (Resource.subst_formals_core substitution formula).
Proof.
  revert F' Δ' renaming substitution.
  induction formula; intros F' Δ' renaming substitution;
    cbn [Resource.subst_formals_core Resource.rename_bound_core];
    rewrite ?subst_formals_expr_rename,
            ?subst_formals_expr_list_rename;
    try reflexivity.
  all: f_equal.
  all: try (rewrite <- rename_formal_subst_lift; apply IHformula).
  all: eauto.
Qed.

Lemma subst_bound_core_rename {F Δ Δ' Δ''}
    (renaming : bound_renaming Δ' Δ'')
    (substitution : bound_subst F Δ Δ') (formula : Resource.core_assertion F Δ) :
  Resource.subst_bound_core (rename_bound_subst renaming substitution)
      formula =
    Resource.rename_bound_core renaming (Resource.subst_bound_core substitution formula).
Proof.
  revert Δ' Δ'' renaming substitution.
  induction formula; intros Δ' Δ'' renaming substitution;
    cbn [Resource.subst_bound_core Resource.rename_bound_core];
    rewrite ?subst_bound_expr_rename,
            ?subst_bound_expr_list_rename;
    try reflexivity.
  all: f_equal.
  all: try (rewrite <- rename_bound_subst_lift; apply IHformula).
  all: eauto.
Qed.

(** Lifting a closed body into a binder context is renaming-invariant:
    there are no bound variables to rename. *)
Lemma weaken_core_to_rename {F Δ Δ'} (renaming : bound_renaming Δ Δ')
    (formula : Resource.core_assertion F []) :
  Resource.rename_bound_core renaming (Resource.weaken_core_to Δ formula) =
    Resource.weaken_core_to Δ' formula.
Proof.
  unfold Resource.weaken_core_to. rewrite <- subst_bound_core_rename.
  apply Resource.subst_bound_core_ext. intros t variable.
  dependent destruction variable.
Qed.

End WithSignature.
End RenamingFacts.

Section WithSignature.
Context {RAs : RAValueConfig} {Logic : LogicSignature}.
(** Canonical instantiation of a selected procedure contract in the caller's
    logical context. *)
Definition procedure_pre_instantiation {callee_variables identity}
    (procedure : typed_procedure callee_variables identity)
    {F Δ}
    (arguments : expr_list F Δ (procedure_args identity)) :
    Resource.core_assertion F Δ :=
  Resource.subst_formals_core (expr_list_formal_subst arguments)
    (Resource.weaken_core_to Δ (procedure_precondition _ _ procedure)).

(** Close every ambient logical binder existentially. *)
Fixpoint existentially_close_assertion {Γ F Δ}
    (formula : assertion Γ F Δ) : assertion Γ F [] :=
  match Δ as Δ0 return assertion Γ F Δ0 -> assertion Γ F [] with
  | [] => fun formula => formula
  | t :: tail => fun formula =>
      @existentially_close_assertion Γ F tail (AExists t formula)
  end formula.

Fixpoint existentially_close_prenex_at {Γ F} (Δ : context)
    (prenex : Resource.resource_prenex Γ F Δ) :
    Resource.resource_prenex Γ F [] :=
  match Δ as Δ0 return Resource.resource_prenex Γ F Δ0 ->
      Resource.resource_prenex Γ F [] with
  | [] => fun prenex => prenex
  | t :: tail => fun prenex =>
      existentially_close_prenex_at tail (Resource.ResourceExists t prenex)
  end prenex.

Definition existentially_close_prenex {Γ F Δ}
    (prenex : Resource.resource_prenex Γ F Δ) :
    Resource.resource_prenex Γ F [] :=
  existentially_close_prenex_at Δ prenex.

(** Canonical resource assertions at a procedure boundary. *)
Definition procedure_body_pre {Γ identity}
    (procedure : typed_procedure Γ identity) :
    Resource.resource_prenex Γ (procedure_args identity) [] :=
  Resource.RState (procedure_entry_store _ _ procedure)
    (procedure_precondition _ _ procedure).

Definition procedure_body_post {Γ identity Δ}
    (procedure : typed_procedure Γ identity)
    (exit_store : symbolic_store Γ (procedure_args identity) Δ)
    (return_reference : value_ref (procedure_args identity) Δ
      (procedure_return identity)) :
    Resource.resource_prenex Γ (procedure_args identity) [] :=
  existentially_close_prenex
    (Resource.RState exit_store
      (Resource.subst_bound_core
        (singleton_bound_subst return_reference)
        (procedure_postcondition _ _ procedure))).

(** Coherence between the authoritative resource-contract environment and
    the typed procedure table.  The environment identifies the logical
    contract of each procedure (its masks are inferred from it); this
    interface connects those declarations to the concrete typed procedure
    selected by the executable table. *)
Section WithContracts.
Context {Contracts : ResourceHoare.ResourceContractEnv}.
Class ProcedureContractCoherence := ProcedureContractCoherenceData {
  coherent_procedures : typed_procedure_environment;

  (** Every procedure admitted by the contract environment has a typed
      declaration in the executable table.  The dependent witness can be
      obtained by the computable lookup [lookup_typed_procedure_at]. *)
  procedure_selects : forall identity,
    ResourceHoare.procedure_verified identity ->
    { callee_variables : decl_context &
      { procedure : typed_procedure callee_variables identity |
        lookup_typed_procedure coherent_procedures identity =
          Some (pack_typed_procedure procedure) } };

  (** The declared contract *is* the callee's contract.  Both are core
      assertions at the same indices, so these are equations. *)
  contract_pre_coherent : forall callee_variables identity
      (procedure : typed_procedure callee_variables identity),
    lookup_typed_procedure coherent_procedures identity =
      Some (pack_typed_procedure procedure) ->
    ResourceHoare.contract_pre identity = procedure_precondition _ _ procedure;
  contract_post_coherent : forall callee_variables identity
      (procedure : typed_procedure callee_variables identity),
    lookup_typed_procedure coherent_procedures identity =
      Some (pack_typed_procedure procedure) ->
    ResourceHoare.contract_post identity = procedure_postcondition _ _ procedure;
}.
End WithContracts.

(** ** Decidable side conditions

    Entry-freedom and procedure well-formedness are decidable; the boolean
    checks below let a module's side conditions be established by
    computation. *)
Definition ref_entry_freeb {F Δ t} (reference : value_ref F Δ t) : bool :=
  match reference with
  | RefSymbol (ProcedureEntrySymbol _ _) => false
  | _ => true
  end.

Fixpoint expr_entry_freeb {F Δ t} (expression : expr F Δ t) : bool :=
  match expression with
  | ERef reference => ref_entry_freeb reference
  | EVal _ => true
  | EUnOp _ operand => expr_entry_freeb operand
  | EBinOp _ first second => expr_entry_freeb first && expr_entry_freeb second
  end.

Fixpoint expr_list_entry_freeb {F Δ ts} (expressions : expr_list F Δ ts) :
    bool :=
  match expressions with
  | ExprNil => true
  | ExprCons head tail => expr_entry_freeb head && expr_list_entry_freeb tail
  end.

Fixpoint core_entry_freeb {F Δ} (formula : Resource.core_assertion F Δ) :
    bool :=
  match formula with
  | Resource.CExpr condition => expr_entry_freeb condition
  | Resource.CPure _ => true
  | Resource.COwn _ location chunk | Resource.CGhostOwn _ location chunk =>
      expr_entry_freeb location && expr_entry_freeb chunk
  | Resource.CFpuAllowed _ old_chunk new_chunk =>
      expr_entry_freeb old_chunk && expr_entry_freeb new_chunk
  | Resource.CRAValid _ chunk => expr_entry_freeb chunk
  | Resource.CExists _ body | Resource.CForall _ body => core_entry_freeb body
  | Resource.CIte condition then_branch else_branch =>
      expr_entry_freeb condition && core_entry_freeb then_branch &&
        core_entry_freeb else_branch
  | Resource.CInvariant _ args | Resource.CPredicate _ args =>
      expr_list_entry_freeb args
  | Resource.CAnd left_formula right_formula =>
      core_entry_freeb left_formula && core_entry_freeb right_formula
  end.

Lemma expr_entry_freeb_sound {F Δ t} (expression : expr F Δ t) :
  expr_entry_freeb expression = true -> expr_entry_free expression.
Proof.
  induction expression as [t reference | | | ]; simpl.
  - destruct reference as [| | t [] ]; simpl; done.
  - done.
  - done.
  - rewrite andb_true_iff. tauto.
Qed.

Lemma expr_list_entry_freeb_sound {F Δ ts} (expressions : expr_list F Δ ts) :
  expr_list_entry_freeb expressions = true -> expr_list_entry_free expressions.
Proof.
  induction expressions; simpl; [done |].
  rewrite andb_true_iff. intros [Hhead Htail].
  split; [apply expr_entry_freeb_sound |]; auto.
Qed.

Lemma core_entry_freeb_sound {F Δ} (formula : Resource.core_assertion F Δ) :
  core_entry_freeb formula = true -> Resource.core_entry_free formula.
Proof.
  induction formula; simpl; rewrite ?andb_true_iff;
    intuition eauto using expr_entry_freeb_sound, expr_list_entry_freeb_sound.
Qed.

Local Instance in_nat_decision (index : nat) (indices : list nat) :
  Decision (In index indices) := in_dec Nat.eq_dec index indices.

Local Instance in_string_decision (name : string) (names : list string) :
  Decision (In name names) := in_dec string_dec name names.

Definition procedure_wfb {Γ identity} (procedure : typed_procedure Γ identity) :
    bool :=
  bool_decide (NoDup (named_context_names (procedure_variables _ _ procedure))) &&
  bool_decide (~ List.In "#ret_val"
    (named_context_names (procedure_variables _ _ procedure))) &&
  bool_decide (NoDup (pvar_list_indices
    (procedure_formal_variables _ _ procedure))) &&
  bool_decide (~ In (lvar_index (procedure_return_variable _ _ procedure))
    (pvar_list_indices (procedure_formal_variables _ _ procedure))) &&
  core_entry_freeb (procedure_precondition _ _ procedure) &&
  core_entry_freeb (procedure_postcondition _ _ procedure) &&
  forallb keep_runtime Γ.

Lemma procedure_wfb_sound {Γ identity} (procedure : typed_procedure Γ identity) :
  procedure_wfb procedure = true -> procedure_wf procedure.
Proof.
  unfold procedure_wfb. rewrite !andb_true_iff, !bool_decide_eq_true.
  intros [[[[[[Hnames Hreserved] Hformals] Hreturn] Hpre] Hpost] Hruntime].
  constructor.
  - apply NoDup_ListNoDup. exact Hnames.
  - exact Hreserved.
  - apply NoDup_ListNoDup. exact Hformals.
  - exact Hreturn.
  - apply core_entry_freeb_sound. exact Hpre.
  - apply core_entry_freeb_sound. exact Hpost.
  - exact Hruntime.
Qed.

Definition packed_procedure_wfb (procedure : packed_typed_procedure) : bool :=
  procedure_wfb (projT2 (projT2 procedure)).

Lemma packed_procedures_wfb_sound procedures :
  forallb packed_procedure_wfb procedures = true ->
  Forall packed_procedure_wf procedures.
Proof.
  rewrite forallb_forall, Forall_forall.
  intros Hwf procedure Hin. apply procedure_wfb_sound, Hwf. apply elem_of_list_In, Hin.
Qed.

(** A procedure table from its entries, when their identities are distinct
    and every entry is well formed. *)
Definition procedure_table (procedures : list packed_typed_procedure) :
    option typed_procedure_environment :=
  match bool_decide (NoDup (map packed_procedure_id procedures)) as ids,
        forallb packed_procedure_wfb procedures as wf
    return bool_decide (NoDup (map packed_procedure_id procedures)) = ids ->
      forallb packed_procedure_wfb procedures = wf ->
      option typed_procedure_environment with
  | true, true => fun Hids Hwf =>
      Some (TypedProcedureEnvironment procedures
        (proj1 (NoDup_ListNoDup _) (bool_decide_eq_true_1 _ Hids))
        (packed_procedures_wfb_sound _ Hwf)
        (procedure_signature_coherent_of_nodup _
          (proj1 (NoDup_ListNoDup _) (bool_decide_eq_true_1 _ Hids))))
  | _, _ => fun _ _ => None
  end eq_refl eq_refl.

(** ** Modules

    A module is its procedure table together with its predicates and
    invariants and their bodies.  Its contract environment and the coherence
    of that environment with the table are derived: a procedure's contract
    is the one its table entry declares. *)
Definition procedure_contract_invariants_declared
    (predicates : list pred_id)
    (predicate_body : forall predicate,
      Resource.core_assertion (predicate_args predicate) [])
    (invariants : list inv_id) (packed : packed_typed_procedure) : Prop :=
  match packed with
  | existT _ (existT _ procedure) =>
      ResourceHoare.contract_invariants predicate_body predicates
        (procedure_precondition _ _ procedure) ⊆ list_to_set invariants /\
      ResourceHoare.contract_invariants predicate_body predicates
        (procedure_postcondition _ _ procedure) ⊆ list_to_set invariants
  end.

#[global] Instance procedure_contract_invariants_declared_decision
    predicates predicate_body invariants packed :
    Decision (procedure_contract_invariants_declared
      predicates predicate_body invariants packed).
Proof. destruct packed as [Γ [identity procedure]]. apply _. Defined.

Record module := ModuleData {
  module_procedures : typed_procedure_environment;
  module_predicates : list pred_id;
  module_predicate_body : forall predicate,
    Resource.core_assertion (predicate_args predicate) [];
  module_predicate_body_entry_free : forall predicate,
    Resource.core_entry_free (module_predicate_body predicate);
  module_invariants : list inv_id;
  module_invariant_body : forall invariant,
    Resource.core_assertion (invariant_args invariant) [];
  module_invariant_body_entry_free : forall invariant,
    Resource.core_entry_free (module_invariant_body invariant);
  module_contract_invariants_declared :
    Forall (procedure_contract_invariants_declared module_predicates
      module_predicate_body module_invariants)
      (procedure_entries module_procedures);
}.

Section WithModule.
Variable M : module.

(** Undeclared procedures are never verified, so their placeholder contracts
    are never consulted. *)
Definition module_contract_pre (procedure : proc_id) :
    Resource.core_assertion (procedure_args procedure) [] :=
  match lookup_typed_procedure_at procedure
          (procedure_entries (module_procedures M)) with
  | Some (existT _ callee) => procedure_precondition _ _ callee
  | None => Resource.CPure True
  end.

Definition module_contract_post (procedure : proc_id) :
    Resource.core_assertion (procedure_args procedure)
      (return_context (procedure_return procedure)) :=
  match lookup_typed_procedure_at procedure
          (procedure_entries (module_procedures M)) with
  | Some (existT _ callee) => procedure_postcondition _ _ callee
  | None => Resource.CPure True
  end.

Definition module_procedure_verified (procedure : proc_id) : Prop :=
  lookup_typed_procedure (module_procedures M) procedure <> None.

Definition module_contracts : ResourceHoare.ResourceContractEnv :=
  ResourceHoare.ResourceContractEnvData (module_predicates M)
    (module_predicate_body M) (module_predicate_body_entry_free M)
    (module_invariant_body M) (module_invariant_body_entry_free M)
    module_contract_pre module_contract_post module_procedure_verified.

Definition module_procedure_selects identity :
    module_procedure_verified identity ->
    { callee_variables : decl_context &
      { procedure : typed_procedure callee_variables identity |
        lookup_typed_procedure (module_procedures M) identity =
          Some (pack_typed_procedure procedure) } }.
Proof.
  intros Hverified.
  pose proof (lookup_typed_procedure_at_spec identity
    (procedure_entries (module_procedures M))) as Hspec.
  destruct (lookup_typed_procedure_at identity
    (procedure_entries (module_procedures M)))
    as [[callee_variables callee] |].
  - exists callee_variables, callee. exact Hspec.
  - exfalso. apply Hverified. exact Hspec.
Defined.

Lemma module_lookup_at {Γ identity} (procedure : typed_procedure Γ identity) :
  lookup_typed_procedure (module_procedures M) identity =
    Some (pack_typed_procedure procedure) ->
  lookup_typed_procedure_at identity
      (procedure_entries (module_procedures M)) =
    Some (existT Γ procedure).
Proof.
  intros Hlookup.
  pose proof (lookup_typed_procedure_at_spec identity
    (procedure_entries (module_procedures M))) as Hspec.
  destruct (lookup_typed_procedure_at identity
    (procedure_entries (module_procedures M)))
    as [[callee_variables callee] |].
  - assert (Hpack : pack_typed_procedure callee =
      pack_typed_procedure procedure).
    { apply (lookup_packed_procedure_unique identity
        (procedure_entries (module_procedures M))).
      - exact (procedure_ids_unique (module_procedures M)).
      - exact Hspec.
      - exact Hlookup. }
    dependent destruction Hpack. reflexivity.
  - unfold lookup_typed_procedure in Hlookup.
    rewrite Hlookup in Hspec. discriminate Hspec.
Qed.

Lemma module_contract_pre_coherent callee_variables identity
    (procedure : typed_procedure callee_variables identity) :
  lookup_typed_procedure (module_procedures M) identity =
    Some (pack_typed_procedure procedure) ->
  module_contract_pre identity = procedure_precondition _ _ procedure.
Proof.
  intros Hlookup. unfold module_contract_pre.
  rewrite (module_lookup_at procedure Hlookup). reflexivity.
Qed.

Lemma module_contract_post_coherent callee_variables identity
    (procedure : typed_procedure callee_variables identity) :
  lookup_typed_procedure (module_procedures M) identity =
    Some (pack_typed_procedure procedure) ->
  module_contract_post identity = procedure_postcondition _ _ procedure.
Proof.
  intros Hlookup. unfold module_contract_post.
  rewrite (module_lookup_at procedure Hlookup). reflexivity.
Qed.

Definition module_coherence :
    @ProcedureContractCoherence module_contracts :=
  @ProcedureContractCoherenceData module_contracts
    (module_procedures M) module_procedure_selects
    module_contract_pre_coherent module_contract_post_coherent.
End WithModule.

(** Declared bodies, looked up by identity.  Undeclared invariants are
    trivial and undeclared predicates are false; a body that is not
    entry-free is replaced by the default, which the elaborator never
    produces. *)
Fixpoint lookup_invariant_body
    (bodies : list { invariant : inv_id &
      Resource.core_assertion (invariant_args invariant) [] })
    (invariant : inv_id) : Resource.core_assertion (invariant_args invariant) [] :=
  match bodies with
  | [] => Resource.CPure True
  | existT declared body :: bodies' =>
      match decide (declared = invariant) with
      | left equal =>
          if core_entry_freeb body
          then eq_rect declared
            (fun invariant => Resource.core_assertion (invariant_args invariant) [])
            body invariant equal
          else Resource.CPure True
      | right _ => lookup_invariant_body bodies' invariant
      end
  end.

Fixpoint lookup_predicate_body
    (bodies : list { predicate : pred_id &
      Resource.core_assertion (predicate_args predicate) [] })
    (predicate : pred_id) : Resource.core_assertion (predicate_args predicate) [] :=
  match bodies with
  | [] => Resource.CPure False
  | existT declared body :: bodies' =>
      match decide (declared = predicate) with
      | left equal =>
          if core_entry_freeb body
          then eq_rect declared
            (fun predicate => Resource.core_assertion (predicate_args predicate) [])
            body predicate equal
          else Resource.CPure False
      | right _ => lookup_predicate_body bodies' predicate
      end
  end.

Lemma lookup_invariant_body_entry_free bodies invariant :
  Resource.core_entry_free (lookup_invariant_body bodies invariant).
Proof.
  induction bodies as [| [declared body] bodies' IH]; simpl; [exact I |].
  destruct (decide (declared = invariant)) as [-> |]; [| exact IH].
  destruct (core_entry_freeb body) eqn:Hfree; [| exact I].
  exact (core_entry_freeb_sound _ Hfree).
Qed.

Lemma lookup_predicate_body_entry_free bodies predicate :
  Resource.core_entry_free (lookup_predicate_body bodies predicate).
Proof.
  induction bodies as [| [declared body] bodies' IH]; simpl; [exact I |].
  destruct (decide (declared = predicate)) as [-> |]; [| exact IH].
  destruct (core_entry_freeb body) eqn:Hfree; [| exact I].
  exact (core_entry_freeb_sound _ Hfree).
Qed.

Definition make_module (procedures : typed_procedure_environment)
    (predicates : list { predicate : pred_id &
      Resource.core_assertion (predicate_args predicate) [] })
    (invariants : list { invariant : inv_id &
      Resource.core_assertion (invariant_args invariant) [] })
    (Hdeclared : Forall (procedure_contract_invariants_declared
      (map (@projT1 _ _) predicates) (lookup_predicate_body predicates)
      (map (@projT1 _ _) invariants)) (procedure_entries procedures)) : module :=
  ModuleData procedures (map (@projT1 _ _) predicates)
    (lookup_predicate_body predicates)
    (lookup_predicate_body_entry_free predicates)
    (map (@projT1 _ _) invariants)
    (lookup_invariant_body invariants)
    (lookup_invariant_body_entry_free invariants) Hdeclared.

(** The typed procedure a module declares under an identifier. *)
Definition module_procedure (M : module) (identity : proc_id) :
    option { Γ : decl_context & typed_procedure Γ identity } :=
  lookup_typed_procedure_at identity (procedure_entries (module_procedures M)).

End WithSignature.

End Hoare.
