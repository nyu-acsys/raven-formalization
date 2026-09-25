From Coq Require Import List PArith Program.Equality ProofIrrelevance
  Logic.FunctionalExtensionality String ZArith Lia.

From raven_iris.rich_raven_lang Require Import typed_core typed_assertion.

Import ListNotations.
Open Scope list_scope.

(** * Resource states: an explicit symbolic stack beside a stack-free core

    The assertion grammar of [typed_assertion.v] allows [AStack] below
    conjunctions, conditionals and quantifiers, even though the logic
    intends stack ownership to be exclusive and every useful resource
    triple to carry exactly one symbolic stack.  Here that intent becomes a
    typing invariant: [core_assertion] has no stack constructor, and a
    [resource_assertion] pairs exactly one symbolic store with one core
    assertion.

    The structural observation that makes this work: in [assertion Γ F Δ]
    the program-variable context [Γ] occurs in exactly one constructor,
    [AStack].  Dropping that constructor drops the index, so
    [core_assertion] is indexed by [F] and [Δ] only.  Three consequences
    are visible in the signatures below.

    - [reindex_stack_context] has no counterpart: there is no [Γ] to move.
    - [subst_bound_core] and [subst_formals_core] are TOTAL.  Their
      counterparts [subst_bound_assertion] (typed_assertion.v) and
      [subst_formals_assertion] are [option]-valued, and in both the
      [AStack] branch is the sole source of [None].
    - Contract bodies stop carrying a phantom stack context.

    This module is deliberately independent of the Hoare calculus: the
    representation and its laws stand on their own, before the rules that
    use them. *)

Module TypedResource.

Module Make (RAs : TypedCore.RA_VALUE_CONFIG)
    (Logic : TypedAssertion.LOGIC_SIGNATURE).
Module Assertions := TypedAssertion.Make RAs Logic.
Module Core := Assertions.Core.
Import TypedCore Core Assertions.

(* ------------------------------------------------------------------ *)
(** ** 1. Syntax *)

(** The assertion grammar minus [AStack] — and so minus the [Γ] index. *)
Inductive core_assertion (F Δ : context) : Type :=
| CExpr (condition : expr F Δ TBool)
| CPure (proposition : Prop)
| COwn (field : field_id) (location : expr F Δ TRef)
    (chunk : expr F Δ (Logic.field_type field))
| CGhostOwn (field : field_id) (location : expr F Δ TRef)
    (chunk : expr F Δ (Logic.field_type field))
| CFpuAllowed t (old_chunk new_chunk : expr F Δ t)
| CRAValid t (chunk : expr F Δ t)
| CExists t (body : core_assertion F (t :: Δ))
| CForall t (body : core_assertion F (t :: Δ))
| CIte (condition : expr F Δ TBool)
    (then_branch else_branch : core_assertion F Δ)
| CInvariant (invariant : inv_id)
    (args : expr_list F Δ (Logic.invariant_args invariant))
| CPredicate (predicate : pred_id)
    (args : expr_list F Δ (Logic.predicate_args predicate))
| CAnd (left right : core_assertion F Δ).

Arguments CExpr {_ _} _.
Arguments CPure {_ _} _.
Arguments COwn {_ _} _ _ _.
Arguments CGhostOwn {_ _} _ _ _.
Arguments CFpuAllowed {_ _} _ _ _.
Arguments CRAValid {_ _} _ _.
Arguments CExists {_ _} _ _.
Arguments CForall {_ _} _ _.
Arguments CIte {_ _} _ _ _.
Arguments CInvariant {_ _} _ _.
Arguments CPredicate {_ _} _ _.
Arguments CAnd {_ _} _ _.

(** User-facing resource assertions cannot observe verifier-generated
    procedure-entry atoms.  This is what permits each invocation to choose
    an interpretation matching its freshly-created concrete frame. *)
Fixpoint core_entry_free {F Δ} (formula : core_assertion F Δ) : Prop :=
  match formula with
  | CExpr condition => expr_entry_free condition
  | CPure _ => True
  | COwn _ location chunk | CGhostOwn _ location chunk =>
      expr_entry_free location /\ expr_entry_free chunk
  | CFpuAllowed _ old_chunk new_chunk =>
      expr_entry_free old_chunk /\ expr_entry_free new_chunk
  | CRAValid _ chunk => expr_entry_free chunk
  | CExists _ body | CForall _ body => core_entry_free body
  | CIte condition then_branch else_branch =>
      expr_entry_free condition /\ core_entry_free then_branch /\
        core_entry_free else_branch
  | CInvariant _ args | CPredicate _ args => expr_list_entry_free args
  | CAnd left_formula right_formula =>
      core_entry_free left_formula /\ core_entry_free right_formula
  end.

Definition CTrue {F Δ} : core_assertion F Δ := CPure True.

(** Exactly one symbolic stack, by construction. *)
Record resource_assertion (Γ F Δ : context) : Type := ResourceState {
  resource_stack : symbolic_store Γ F Δ;
  resource_body : core_assertion F Δ;
}.

Arguments ResourceState {_ _ _} _ _.
Arguments resource_stack {_ _ _} _.
Arguments resource_body {_ _ _} _.

(** Binders that may occur in the symbolic stack live outside the pair.
    Ordinary existentials whose variable occurs only in [resource_body]
    stay as [CExists].  Only existential resource binders are provided: a
    resource-level universal is not added speculatively. *)
Inductive resource_prenex (Γ F : context) : context -> Type :=
| ResourceBody (Δ : context) (state : resource_assertion Γ F Δ) :
    resource_prenex Γ F Δ
| ResourceExists (Δ : context) (t : typ)
    (rest : resource_prenex Γ F (t :: Δ)) :
    resource_prenex Γ F Δ.

Arguments ResourceBody {_ _ _} _.
Arguments ResourceExists {_ _ _} _ _.

Definition RState {Γ F Δ} (store : symbolic_store Γ F Δ)
    (body : core_assertion F Δ) : resource_prenex Γ F Δ :=
  ResourceBody (ResourceState store body).

(* ------------------------------------------------------------------ *)
(** ** 2. Renaming and weakening *)

Fixpoint rename_bound_core {F Δ Δ'} (renaming : bound_renaming Δ Δ')
    (formula : core_assertion F Δ) : core_assertion F Δ' :=
  match formula with
  | CExpr condition => CExpr (rename_bound_expr renaming condition)
  | CPure proposition => CPure proposition
  | COwn field location chunk =>
      COwn field (rename_bound_expr renaming location)
        (rename_bound_expr renaming chunk)
  | CGhostOwn field location chunk =>
      CGhostOwn field (rename_bound_expr renaming location)
        (rename_bound_expr renaming chunk)
  | CFpuAllowed t old_chunk new_chunk =>
      CFpuAllowed t (rename_bound_expr renaming old_chunk)
        (rename_bound_expr renaming new_chunk)
  | CRAValid t chunk => CRAValid t (rename_bound_expr renaming chunk)
  | CExists t body =>
      CExists t (rename_bound_core (lift_bound_renaming renaming) body)
  | CForall t body =>
      CForall t (rename_bound_core (lift_bound_renaming renaming) body)
  | CIte condition then_branch else_branch =>
      CIte (rename_bound_expr renaming condition)
        (rename_bound_core renaming then_branch)
        (rename_bound_core renaming else_branch)
  | CInvariant invariant args =>
      CInvariant invariant (rename_bound_expr_list renaming args)
  | CPredicate predicate args =>
      CPredicate predicate (rename_bound_expr_list renaming args)
  | CAnd left_formula right_formula =>
      CAnd (rename_bound_core renaming left_formula)
        (rename_bound_core renaming right_formula)
  end.

Definition weaken_core {F Δ u} (formula : core_assertion F Δ) :
    core_assertion F (u :: Δ) :=
  rename_bound_core weaken_bound_renaming formula.

(** Existential-front normal form for the stack-free half of a resource
    assertion.  Universal binders remain barriers.  This is the resource
    counterpart of [existential_prenex], but it contains no stack index: the
    unique symbolic store is attached only after this telescope has been
    computed. *)
Inductive core_existential_prenex (F Δ : context) : Type :=
| CorePrenexBody (body : core_assertion F Δ)
| CorePrenexExists t (body : core_existential_prenex F (t :: Δ)).

Arguments CorePrenexBody {_ _} _.
Arguments CorePrenexExists {_ _} _ _.

Fixpoint interp_core_existential_prenex {F Δ}
    (prenex : core_existential_prenex F Δ) : core_assertion F Δ :=
  match prenex with
  | CorePrenexBody body => body
  | CorePrenexExists t body =>
      CExists t (interp_core_existential_prenex body)
  end.

Fixpoint rename_core_existential_prenex {F Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (prenex : core_existential_prenex F Δ) :
    core_existential_prenex F Δ' :=
  match prenex with
  | CorePrenexBody body => CorePrenexBody (rename_bound_core renaming body)
  | CorePrenexExists t body =>
      CorePrenexExists t
        (rename_core_existential_prenex
          (lift_bound_renaming renaming) body)
  end.

Definition weaken_core_existential_prenex {F Δ u}
    (prenex : core_existential_prenex F Δ) :
    core_existential_prenex F (u :: Δ) :=
  rename_core_existential_prenex weaken_bound_renaming prenex.

Lemma interp_rename_core_existential_prenex {F Δ Δ'}
    (renaming : bound_renaming Δ Δ')
    (prenex : core_existential_prenex F Δ) :
  interp_core_existential_prenex
      (rename_core_existential_prenex renaming prenex) =
  rename_bound_core renaming (interp_core_existential_prenex prenex).
Proof.
  revert Δ' renaming.
  induction prenex; intros Δ' renaming; cbn.
  - reflexivity.
  - now rewrite (IHprenex _ (lift_bound_renaming renaming)).
Qed.

Fixpoint core_existential_prenex_and_right {F Δ}
    (left : core_assertion F Δ)
    (right : core_existential_prenex F Δ) :
    core_existential_prenex F Δ :=
  match right with
  | CorePrenexBody right_body => CorePrenexBody (CAnd left right_body)
  | CorePrenexExists t right_body =>
      CorePrenexExists t
        (core_existential_prenex_and_right (weaken_core left) right_body)
  end.

Fixpoint core_existential_prenex_and {F Δ}
    (left right : core_existential_prenex F Δ) :
    core_existential_prenex F Δ :=
  match left with
  | CorePrenexBody left_body =>
      core_existential_prenex_and_right left_body right
  | CorePrenexExists t left_body =>
      CorePrenexExists t
        (core_existential_prenex_and left_body
          (weaken_core_existential_prenex right))
  end.

Fixpoint core_existential_prenex_ite_else {F Δ}
    (condition : expr F Δ TBool) (then_branch : core_assertion F Δ)
    (else_branch : core_existential_prenex F Δ) :
    core_existential_prenex F Δ :=
  match else_branch with
  | CorePrenexBody else_body =>
      CorePrenexBody (CIte condition then_branch else_body)
  | CorePrenexExists t else_body =>
      CorePrenexExists t
        (core_existential_prenex_ite_else (weaken_expr condition)
          (weaken_core then_branch) else_body)
  end.

Fixpoint core_existential_prenex_ite {F Δ}
    (condition : expr F Δ TBool)
    (then_branch else_branch : core_existential_prenex F Δ) :
    core_existential_prenex F Δ :=
  match then_branch with
  | CorePrenexBody then_body =>
      core_existential_prenex_ite_else condition then_body else_branch
  | CorePrenexExists t then_body =>
      CorePrenexExists t
        (core_existential_prenex_ite (weaken_expr condition) then_body
          (weaken_core_existential_prenex else_branch))
  end.

Fixpoint normalize_core_existential_prenex {F Δ}
    (formula : core_assertion F Δ) : core_existential_prenex F Δ :=
  match formula with
  | CExists t body =>
      CorePrenexExists t (normalize_core_existential_prenex body)
  | CForall t body =>
      CorePrenexBody (CForall t
        (interp_core_existential_prenex
          (normalize_core_existential_prenex body)))
  | CIte condition then_branch else_branch =>
      core_existential_prenex_ite condition
        (normalize_core_existential_prenex then_branch)
        (normalize_core_existential_prenex else_branch)
  | CAnd left_formula right_formula =>
      core_existential_prenex_and
        (normalize_core_existential_prenex left_formula)
        (normalize_core_existential_prenex right_formula)
  | other => CorePrenexBody other
  end.

Definition rename_bound_resource {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ') (state : resource_assertion Γ F Δ) :
    resource_assertion Γ F Δ' :=
  ResourceState (rename_bound_store renaming (resource_stack state))
    (rename_bound_core renaming (resource_body state)).

Fixpoint rename_resource_prenex {Γ F Δ} (prenex : resource_prenex Γ F Δ) :
    forall Δ', bound_renaming Δ Δ' -> resource_prenex Γ F Δ' :=
  match prenex in resource_prenex _ _ Δ0
    return forall Δ', bound_renaming Δ0 Δ' -> resource_prenex Γ F Δ' with
  | ResourceBody state =>
      fun Δ' renaming => ResourceBody (rename_bound_resource renaming state)
  | ResourceExists t rest =>
      fun Δ' renaming =>
        ResourceExists t
          (rename_resource_prenex rest _ (lift_bound_renaming renaming))
  end.

Definition weaken_resource_prenex {Γ F Δ u}
    (prenex : resource_prenex Γ F Δ) : resource_prenex Γ F (u :: Δ) :=
  rename_resource_prenex prenex _ (@weaken_bound_renaming Δ u).

(* ------------------------------------------------------------------ *)
(** ** 3. Substitution

    Total, unlike [subst_bound_assertion] and [subst_formals_assertion]. *)

Fixpoint subst_bound_core {F Δ Δ'} (substitution : bound_subst F Δ Δ')
    (formula : core_assertion F Δ) : core_assertion F Δ' :=
  match formula with
  | CExpr condition => CExpr (subst_bound_expr substitution condition)
  | CPure proposition => CPure proposition
  | COwn field location chunk =>
      COwn field (subst_bound_expr substitution location)
        (subst_bound_expr substitution chunk)
  | CGhostOwn field location chunk =>
      CGhostOwn field (subst_bound_expr substitution location)
        (subst_bound_expr substitution chunk)
  | CFpuAllowed t old_chunk new_chunk =>
      CFpuAllowed t (subst_bound_expr substitution old_chunk)
        (subst_bound_expr substitution new_chunk)
  | CRAValid t chunk => CRAValid t (subst_bound_expr substitution chunk)
  | CExists t body =>
      CExists t (subst_bound_core (lift_bound_subst substitution) body)
  | CForall t body =>
      CForall t (subst_bound_core (lift_bound_subst substitution) body)
  | CIte condition then_branch else_branch =>
      CIte (subst_bound_expr substitution condition)
        (subst_bound_core substitution then_branch)
        (subst_bound_core substitution else_branch)
  | CInvariant invariant args =>
      CInvariant invariant (subst_bound_expr_list substitution args)
  | CPredicate predicate args =>
      CPredicate predicate (subst_bound_expr_list substitution args)
  | CAnd left_formula right_formula =>
      CAnd (subst_bound_core substitution left_formula)
        (subst_bound_core substitution right_formula)
  end.

(** Instantiating the head binder at an arbitrary expression witness.
    Total, where [instantiate_bound_assertion] (typed_assertion.v) is
    [option]-valued. *)
Definition instantiate_bound_core {F Δ t} (witness : expr F Δ t)
    (body : core_assertion F (t :: Δ)) : core_assertion F Δ :=
  subst_bound_core (head_bound_subst witness) body.

(** Lifting a closed contract body into the caller's binder context.  This
    replaces the [subst_bound_assertion (@empty_bound_subst args Δ)] stage
    of [CONTRACT_ENV.instantiated_definition], and cannot fail. *)
Definition weaken_core_to {F} (Δ : context) (formula : core_assertion F []) :
    core_assertion F Δ :=
  subst_bound_core (@empty_bound_subst F Δ) formula.

Fixpoint subst_formals_core {F F' Δ} (substitution : formal_subst F F' Δ)
    (formula : core_assertion F Δ) : core_assertion F' Δ :=
  match formula with
  | CExpr condition => CExpr (subst_formals_expr substitution condition)
  | CPure proposition => CPure proposition
  | COwn field location chunk =>
      COwn field (subst_formals_expr substitution location)
        (subst_formals_expr substitution chunk)
  | CGhostOwn field location chunk =>
      CGhostOwn field (subst_formals_expr substitution location)
        (subst_formals_expr substitution chunk)
  | CFpuAllowed t old_chunk new_chunk =>
      CFpuAllowed t (subst_formals_expr substitution old_chunk)
        (subst_formals_expr substitution new_chunk)
  | CRAValid t chunk => CRAValid t (subst_formals_expr substitution chunk)
  | CExists t body =>
      CExists t (subst_formals_core (lift_formal_subst substitution) body)
  | CForall t body =>
      CForall t (subst_formals_core (lift_formal_subst substitution) body)
  | CIte condition then_branch else_branch =>
      CIte (subst_formals_expr substitution condition)
        (subst_formals_core substitution then_branch)
        (subst_formals_core substitution else_branch)
  | CInvariant invariant args =>
      CInvariant invariant (subst_formals_expr_list substitution args)
  | CPredicate predicate args =>
      CPredicate predicate (subst_formals_expr_list substitution args)
  | CAnd left_formula right_formula =>
      CAnd (subst_formals_core substitution left_formula)
        (subst_formals_core substitution right_formula)
  end.

(* ------------------------------------------------------------------ *)
(** ** 4. The substitution discipline

    Splitting the stack out does not make arbitrary substitution into a
    symbolic store valid: store slots hold [value_ref]s, while a logical
    existential may be instantiated by an arbitrary expression.  The
    compatible fragment is a *reference* substitution, and only that is
    allowed to touch a resource state. *)

Definition bound_ref_subst (F Δ Δ' : context) :=
  forall t, bvar Δ t -> value_ref F Δ' t.

Definition subst_bound_value_ref {F Δ Δ' t}
    (substitution : bound_ref_subst F Δ Δ')
    (reference : value_ref F Δ t) : value_ref F Δ' t :=
  match reference in value_ref _ _ result return value_ref F Δ' result with
  | RefFormal variable => RefFormal variable
  | RefBound variable => substitution _ variable
  | RefAtom variable => RefAtom variable
  end.

Fixpoint subst_bound_store {Γ F Δ Δ'}
    (substitution : bound_ref_subst F Δ Δ') (store : symbolic_store Γ F Δ) :
    symbolic_store Γ F Δ' :=
  match store with
  | StoreNil => StoreNil
  | StoreCons reference tail =>
      StoreCons (subst_bound_value_ref substitution reference)
        (subst_bound_store substitution tail)
  end.

(** A reference substitution is in particular an expression substitution. *)
Definition bound_subst_of_refs {F Δ Δ'}
    (substitution : bound_ref_subst F Δ Δ') : bound_subst F Δ Δ' :=
  fun t variable => ERef (substitution t variable).

Definition subst_bound_resource {Γ F Δ Δ'}
    (substitution : bound_ref_subst F Δ Δ')
    (state : resource_assertion Γ F Δ) : resource_assertion Γ F Δ' :=
  ResourceState (subst_bound_store substitution (resource_stack state))
    (subst_bound_core (bound_subst_of_refs substitution)
      (resource_body state)).

Definition head_bound_ref_subst {F Δ t} (witness : value_ref F Δ t) :
    bound_ref_subst F (t :: Δ) Δ :=
  fun u variable =>
    match view_member variable with
    | MVHere => witness
    | MVThere tail => RefBound tail
    end.

(** Instantiating a resource binder is [subst_bound_resource] at a
    [head_bound_ref_subst] witness.  Deliberately no telescope-level
    "instantiate the head binder of a [resource_prenex]" operation is
    provided: pushing a witness underneath an intervening [ResourceExists]
    needs a binder exchange, which is not structurally recursive on the
    telescope.  The entailment rule instantiates the innermost binder
    instead, which composes with telescope monotonicity to reach any
    binder and keeps this module free of a well-founded recursion. *)

(* ------------------------------------------------------------------ *)
(** ** 5. Conjoining a core frame under a telescope *)

Fixpoint prenex_and {Γ F Δ} (prenex : resource_prenex Γ F Δ)
    (frame : core_assertion F Δ) {struct prenex} : resource_prenex Γ F Δ :=
  match prenex in resource_prenex _ _ Δ0
    return core_assertion F Δ0 -> resource_prenex Γ F Δ0 with
  | ResourceBody state =>
      fun frame0 =>
        ResourceBody (ResourceState (resource_stack state)
          (CAnd (resource_body state) frame0))
  | ResourceExists t rest =>
      fun frame0 => ResourceExists t (prenex_and rest (weaken_core frame0))
  end frame.

(** Attach the unique symbolic store below a normalized core telescope.
    Each binder weakens the store; no branch ever acquires a second store. *)
Fixpoint resource_of_core_existential_prenex {Γ F Δ}
    (store : symbolic_store Γ F Δ)
    (prenex : core_existential_prenex F Δ) : resource_prenex Γ F Δ :=
  match prenex with
  | CorePrenexBody body => RState store body
  | CorePrenexExists t body =>
      ResourceExists t
        (resource_of_core_existential_prenex (weaken_store store) body)
  end.

Fixpoint normalize_resource_prenex {Γ F Δ}
    (prenex : resource_prenex Γ F Δ) : resource_prenex Γ F Δ :=
  match prenex with
  | ResourceBody state =>
      resource_of_core_existential_prenex (resource_stack state)
        (normalize_core_existential_prenex (resource_body state))
  | ResourceExists t rest =>
      ResourceExists t (normalize_resource_prenex rest)
  end.

(* ------------------------------------------------------------------ *)
(** ** 6. Functorial laws

    These are what the Hoare calculus relies on when it pushes a renaming
    or a substitution through a resource state. *)

(** The two missing expression-list laws.  Their scalar counterparts are
    [subst_formals_expr_identity] and [subst_formals_expr_compose] in
    typed_assertion.v; the list versions are needed here for [CInvariant]
    and [CPredicate] argument vectors. *)
Lemma subst_formals_expr_list_identity {F Δ ts}
    (expressions : expr_list F Δ ts) :
  subst_formals_expr_list identity_formal_subst expressions = expressions.
Proof.
  induction expressions as [| t ts head tail IH];
    cbn [subst_formals_expr_list]; [reflexivity |].
  rewrite subst_formals_expr_identity, IH. reflexivity.
Qed.

Lemma subst_formals_expr_list_compose {F1 F2 F3 Δ ts}
    (outer : formal_subst F2 F3 Δ) (inner : formal_subst F1 F2 Δ)
    (expressions : expr_list F1 Δ ts) :
  subst_formals_expr_list outer (subst_formals_expr_list inner expressions) =
    subst_formals_expr_list (compose_formal_subst outer inner) expressions.
Proof.
  induction expressions as [| t ts head tail IH];
    cbn [subst_formals_expr_list]; [reflexivity |].
  rewrite subst_formals_expr_compose, IH. reflexivity.
Qed.

(** Weakening the binder context commutes with formal substitution: the
    two act on disjoint parts of an expression. *)
Lemma weaken_subst_formals_expr {F F' Δ u t}
    (substitution : formal_subst F F' Δ) (expression : expr F Δ t) :
  @weaken_expr F' Δ t u (subst_formals_expr substitution expression) =
    subst_formals_expr (lift_formal_subst substitution)
      (@weaken_expr F Δ t u expression).
Proof.
  induction expression; cbn [weaken_expr subst_formals_expr];
    try congruence.
  destruct reference; reflexivity.
Qed.

Lemma weaken_subst_formals_expr_list {F F' Δ u ts}
    (substitution : formal_subst F F' Δ) (expressions : expr_list F Δ ts) :
  @weaken_expr_list F' Δ ts u (subst_formals_expr_list substitution expressions)
    = subst_formals_expr_list (lift_formal_subst substitution)
        (@weaken_expr_list F Δ ts u expressions).
Proof.
  induction expressions as [| t ts head tail IH];
    cbn [weaken_expr_list subst_formals_expr_list]; [reflexivity |].
  rewrite weaken_subst_formals_expr, IH. reflexivity.
Qed.

Lemma lift_identity_formal_subst {F Δ u} :
  @lift_formal_subst F F Δ u identity_formal_subst = identity_formal_subst.
Proof.
  apply functional_extensionality_dep; intro t.
  apply functional_extensionality; intro variable. reflexivity.
Qed.

Lemma lift_formal_subst_compose {F1 F2 F3 Δ u}
    (outer : formal_subst F2 F3 Δ) (inner : formal_subst F1 F2 Δ) :
  @lift_formal_subst F1 F3 Δ u (compose_formal_subst outer inner) =
    compose_formal_subst (lift_formal_subst outer) (lift_formal_subst inner).
Proof.
  apply functional_extensionality_dep; intro t.
  apply functional_extensionality; intro variable.
  unfold lift_formal_subst, compose_formal_subst.
  apply weaken_subst_formals_expr.
Qed.

(** *** Renaming is functorial on core assertions. *)
Lemma rename_bound_core_identity {F Δ} (formula : core_assertion F Δ) :
  rename_bound_core identity_bound_renaming formula = formula.
Proof.
  induction formula; cbn [rename_bound_core];
    rewrite ?rename_bound_expr_identity, ?rename_bound_expr_list_identity;
    rewrite ?lift_identity_bound_renaming; congruence.
Qed.

Lemma rename_bound_core_compose {F Δ Δ' Δ''}
    (first : bound_renaming Δ Δ') (second : bound_renaming Δ' Δ'')
    (formula : core_assertion F Δ) :
  rename_bound_core second (rename_bound_core first formula) =
    rename_bound_core (compose_bound_renaming first second) formula.
Proof.
  revert Δ' Δ'' first second.
  induction formula; intros Δ' Δ'' first second; cbn [rename_bound_core];
    rewrite ?rename_bound_expr_compose, ?rename_bound_expr_list_compose;
    try reflexivity.
  - rewrite IHformula, lift_bound_renaming_compose. reflexivity.
  - rewrite IHformula, lift_bound_renaming_compose. reflexivity.
  - rewrite IHformula1, IHformula2. reflexivity.
  - rewrite IHformula1, IHformula2. reflexivity.
Qed.

(** *** Renaming is functorial on resource states and telescopes.  This is
    where the record split pays: the two components rename independently,
    and there is no stack to locate inside the logical part. *)
Lemma rename_bound_resource_identity {Γ F Δ}
    (state : resource_assertion Γ F Δ) :
  rename_bound_resource identity_bound_renaming state = state.
Proof.
  destruct state as [store body]. unfold rename_bound_resource. cbn.
  rewrite rename_bound_store_identity, rename_bound_core_identity.
  reflexivity.
Qed.

Lemma rename_bound_resource_compose {Γ F Δ Δ' Δ''}
    (first : bound_renaming Δ Δ') (second : bound_renaming Δ' Δ'')
    (state : resource_assertion Γ F Δ) :
  rename_bound_resource second (rename_bound_resource first state) =
    rename_bound_resource (compose_bound_renaming first second) state.
Proof.
  destruct state as [store body]. unfold rename_bound_resource. cbn.
  rewrite rename_bound_store_compose, rename_bound_core_compose.
  reflexivity.
Qed.

Lemma rename_resource_prenex_identity {Γ F Δ}
    (prenex : resource_prenex Γ F Δ) :
  rename_resource_prenex prenex _ identity_bound_renaming = prenex.
Proof.
  induction prenex as [Δ state | Δ t rest IH];
    cbn [rename_resource_prenex].
  - rewrite rename_bound_resource_identity. reflexivity.
  - rewrite lift_identity_bound_renaming, IH. reflexivity.
Qed.

Lemma rename_resource_prenex_compose {Γ F Δ}
    (prenex : resource_prenex Γ F Δ) :
  forall Δ' Δ'' (first : bound_renaming Δ Δ') (second : bound_renaming Δ' Δ''),
  rename_resource_prenex (rename_resource_prenex prenex _ first) _ second =
    rename_resource_prenex prenex _ (compose_bound_renaming first second).
Proof.
  induction prenex as [Δ state | Δ t rest IH];
    intros Δ' Δ'' first second; cbn [rename_resource_prenex].
  - rewrite rename_bound_resource_compose. reflexivity.
  - rewrite IH, lift_bound_renaming_compose. reflexivity.
Qed.

Lemma weaken_core_rename_natural {F Δ Δ' u}
    (renaming : bound_renaming Δ Δ') (formula : core_assertion F Δ) :
  weaken_core (u := u) (rename_bound_core renaming formula) =
    rename_bound_core (lift_bound_renaming renaming)
      (weaken_core (u := u) formula).
Proof.
  unfold weaken_core.
  rewrite !rename_bound_core_compose.
  f_equal.
  apply functional_extensionality_dep. intro t.
  apply functional_extensionality. intro variable.
  unfold compose_bound_renaming, weaken_bound_renaming,
    lift_bound_renaming.
  rewrite view_member_there. reflexivity.
Qed.

Lemma prenex_and_rename {Γ F Δ} (prenex : resource_prenex Γ F Δ) :
  forall Δ' (renaming : bound_renaming Δ Δ')
    (frame : core_assertion F Δ),
  prenex_and (rename_resource_prenex prenex _ renaming)
      (rename_bound_core renaming frame) =
    rename_resource_prenex (prenex_and prenex frame) _ renaming.
Proof.
  induction prenex as [Δ state | Δ t rest IH];
    intros Δ' renaming frame; cbn [prenex_and rename_resource_prenex].
  - reflexivity.
  - f_equal. rewrite weaken_core_rename_natural. apply IH.
Qed.

Lemma prenex_and_weaken {Γ F Δ u}
    (prenex : resource_prenex Γ F Δ) (frame : core_assertion F Δ) :
  prenex_and (weaken_resource_prenex (u := u) prenex)
      (weaken_core frame) =
    weaken_resource_prenex (u := u) (prenex_and prenex frame).
Proof. apply prenex_and_rename. Qed.

(** *** Substitution is extensional and functorial on core assertions. *)
Lemma subst_bound_core_ext {F Δ Δ'} (left right : bound_subst F Δ Δ')
    (Hequal : forall t (variable : bvar Δ t),
      left t variable = right t variable)
    (formula : core_assertion F Δ) :
  subst_bound_core left formula = subst_bound_core right formula.
Proof.
  revert Δ' left right Hequal.
  induction formula; intros Δ' left right Hequal; cbn [subst_bound_core];
    rewrite ?(subst_bound_expr_ext left right Hequal),
            ?(subst_bound_expr_list_ext left right Hequal);
    try reflexivity.
  - rewrite (IHformula _ (lift_bound_subst left) (lift_bound_subst right)
      (lift_bound_subst_ext left right Hequal)). reflexivity.
  - rewrite (IHformula _ (lift_bound_subst left) (lift_bound_subst right)
      (lift_bound_subst_ext left right Hequal)). reflexivity.
  - rewrite (IHformula1 _ left right Hequal), (IHformula2 _ left right Hequal).
    reflexivity.
  - rewrite (IHformula1 _ left right Hequal), (IHformula2 _ left right Hequal).
    reflexivity.
Qed.

Lemma subst_formals_core_identity {F Δ} (formula : core_assertion F Δ) :
  subst_formals_core identity_formal_subst formula = formula.
Proof.
  induction formula; cbn [subst_formals_core];
    rewrite ?subst_formals_expr_identity, ?subst_formals_expr_list_identity,
            ?lift_identity_formal_subst;
    congruence.
Qed.

Lemma subst_formals_core_compose {F1 F2 F3 Δ}
    (outer : formal_subst F2 F3 Δ) (inner : formal_subst F1 F2 Δ)
    (formula : core_assertion F1 Δ) :
  subst_formals_core outer (subst_formals_core inner formula) =
    subst_formals_core (compose_formal_subst outer inner) formula.
Proof.
  revert F2 F3 outer inner.
  induction formula; intros F2 F3 outer inner; cbn [subst_formals_core];
    rewrite ?subst_formals_expr_compose, ?subst_formals_expr_list_compose;
    try reflexivity.
  - rewrite IHformula, lift_formal_subst_compose. reflexivity.
  - rewrite IHformula, lift_formal_subst_compose. reflexivity.
  - rewrite IHformula1, IHformula2. reflexivity.
  - rewrite IHformula1, IHformula2. reflexivity.
Qed.

(** *** Weakening is renaming, definitionally. *)
Lemma weaken_core_rename {F Δ u} (formula : core_assertion F Δ) :
  @weaken_core F Δ u formula =
    rename_bound_core weaken_bound_renaming formula.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** 7. Embedding into the assertion grammar

    The bridge used by the validity slice.  A core assertion is an
    assertion that happens to use no [AStack]; a resource state is
    [AAnd (AStack store) _]; a telescope is a prefix of [AExists].

    This is a migration device, not an architecture: it lets the existing
    Iris validity proofs be reused verbatim for the resource-based
    calculus while both representations exist side by side. *)

Fixpoint core_to_assertion {Γ F Δ} (formula : core_assertion F Δ) :
    assertion Γ F Δ :=
  match formula with
  | CExpr condition => AExpr condition
  | CPure proposition => APure proposition
  | COwn field location chunk => AOwn field location chunk
  | CGhostOwn field location chunk => AGhostOwn field location chunk
  | CFpuAllowed t old_chunk new_chunk => AFpuAllowed t old_chunk new_chunk
  | CRAValid t chunk => ARAValid t chunk
  | CExists t body => AExists t (core_to_assertion body)
  | CForall t body => AForall t (core_to_assertion body)
  | CIte condition then_branch else_branch =>
      AIte condition (core_to_assertion then_branch)
        (core_to_assertion else_branch)
  | CInvariant invariant args => AInvariant invariant args
  | CPredicate predicate args => APredicate predicate args
  | CAnd left_formula right_formula =>
      AAnd (core_to_assertion left_formula) (core_to_assertion right_formula)
  end.

Lemma core_to_assertion_entry_free {Γ F Δ}
    (formula : core_assertion F Δ) :
  core_entry_free formula -> assertion_entry_free (@core_to_assertion Γ F Δ formula).
Proof.
  induction formula; simpl; intros Hfree; try exact Hfree;
    try (destruct Hfree as [Hleft Hright]; split; auto);
    try (destruct Hfree as [Hcondition [Hthen Helse]];
      repeat split; auto).
  all: try (apply IHformula; exact Hfree).
  all: try (destruct Hfree as [Hleft Hright]; split;
    [apply IHformula1 | apply IHformula2]; assumption).
  all: split; [apply IHformula1 | apply IHformula2]; tauto.
Qed.

Definition resource_to_assertion {Γ F Δ}
    (state : resource_assertion Γ F Δ) : assertion Γ F Δ :=
  AAnd (AStack (resource_stack state))
    (core_to_assertion (resource_body state)).

Fixpoint prenex_to_assertion {Γ F Δ}
    (prenex : resource_prenex Γ F Δ) : assertion Γ F Δ :=
  match prenex with
  | ResourceBody state => resource_to_assertion state
  | ResourceExists t rest => AExists t (prenex_to_assertion rest)
  end.

(** The embedding lands in the stack-free fragment — by construction, which
    is the whole point: what the old development had to prove after every
    rule is here a property of the image. *)
Lemma core_to_assertion_stack_free {Γ F Δ} (formula : core_assertion F Δ) :
  stack_free (@core_to_assertion Γ F Δ formula).
Proof.
  induction formula; cbn [core_to_assertion]; constructor; assumption.
Qed.

(** Renaming and weakening commute with the embedding, so a transported
    proof may be pushed under a binder. *)
Lemma core_to_assertion_rename {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ') (formula : core_assertion F Δ) :
  @core_to_assertion Γ F Δ' (rename_bound_core renaming formula) =
    rename_bound_assertion renaming (core_to_assertion formula).
Proof.
  revert Δ' renaming.
  induction formula; intros Δ' renaming;
    cbn [core_to_assertion rename_bound_core rename_bound_assertion];
    congruence.
Qed.

Lemma core_to_assertion_weaken {Γ F Δ u} (formula : core_assertion F Δ) :
  @core_to_assertion Γ F (u :: Δ) (weaken_core formula) =
    weaken_assertion (core_to_assertion formula).
Proof. apply core_to_assertion_rename. Qed.



(** Substitution commutes with the embedding — and in particular the
    [option] of [subst_bound_assertion] never fires on the image, which is
    the syntactic form of "[AStack] was its only failure case". *)
Lemma subst_bound_core_to_assertion {Γ F Δ Δ'}
    (substitution : bound_subst F Δ Δ') (formula : core_assertion F Δ) :
  subst_bound_assertion substitution (@core_to_assertion Γ F Δ formula) =
    Some (core_to_assertion (subst_bound_core substitution formula)).
Proof.
  revert Δ' substitution.
  induction formula; intros Δ' substitution;
    cbn [core_to_assertion subst_bound_assertion subst_bound_core];
    try reflexivity.
  - rewrite IHformula. reflexivity.
  - rewrite IHformula. reflexivity.
  - rewrite IHformula1, IHformula2. reflexivity.
  - rewrite IHformula1, IHformula2. reflexivity.
Qed.

Lemma instantiate_bound_core_to_assertion {Γ F Δ t}
    (witness : expr F Δ t) (formula : core_assertion F (t :: Δ)) :
  instantiate_bound_assertion witness (@core_to_assertion Γ F (t :: Δ) formula)
    = Some (core_to_assertion (instantiate_bound_core witness formula)).
Proof. apply subst_bound_core_to_assertion. Qed.

Lemma subst_formals_core_to_assertion {Γ F F' Δ}
    (substitution : formal_subst F F' Δ) (formula : core_assertion F Δ) :
  subst_formals_assertion substitution (@core_to_assertion Γ F Δ formula) =
    Some (core_to_assertion (subst_formals_core substitution formula)).
Proof.
  revert F' substitution.
  induction formula; intros F' substitution;
    cbn [core_to_assertion subst_formals_assertion subst_formals_core];
    try reflexivity.
  - rewrite IHformula. reflexivity.
  - rewrite IHformula. reflexivity.
  - rewrite IHformula1, IHformula2. reflexivity.
  - rewrite IHformula1, IHformula2. reflexivity.
Qed.

(** The embedding at two different program-variable contexts is related by
    [reindex_stack_context] — which is the old development's way of saying
    "this assertion does not depend on [Γ]".  For a core assertion that is
    true by construction. *)
Lemma core_to_assertion_reindex {Γ Γ' F Δ} (formula : core_assertion F Δ) :
  reindex_stack_context (@core_to_assertion Γ F Δ formula)
    (@core_to_assertion Γ' F Δ formula).
Proof.
  induction formula; cbn [core_to_assertion]; constructor; auto.
Qed.

(** Renaming commutes with the embedding, at every layer. *)
Lemma resource_to_assertion_rename {Γ F Δ Δ'}
    (renaming : bound_renaming Δ Δ') (state : resource_assertion Γ F Δ) :
  resource_to_assertion (rename_bound_resource renaming state) =
    rename_bound_assertion renaming (resource_to_assertion state).
Proof.
  destruct state as [store body].
  unfold resource_to_assertion, rename_bound_resource.
  cbn [resource_stack resource_body rename_bound_assertion].
  rewrite core_to_assertion_rename. reflexivity.
Qed.

Lemma prenex_to_assertion_rename {Γ F Δ} (prenex : resource_prenex Γ F Δ) :
  forall Δ' (renaming : bound_renaming Δ Δ'),
  prenex_to_assertion (rename_resource_prenex prenex _ renaming) =
    rename_bound_assertion renaming (prenex_to_assertion prenex).
Proof.
  induction prenex as [Δ state | Δ t rest IH]; intros Δ' renaming;
    cbn [rename_resource_prenex prenex_to_assertion rename_bound_assertion].
  - apply resource_to_assertion_rename.
  - f_equal. apply IH.
Qed.

Lemma prenex_to_assertion_weaken {Γ F Δ u} (prenex : resource_prenex Γ F Δ) :
  prenex_to_assertion (@weaken_resource_prenex Γ F Δ u prenex) =
    weaken_assertion (prenex_to_assertion prenex).
Proof. apply prenex_to_assertion_rename. Qed.

(** [prenex_and] pushes a core frame under the telescope, so it is not the
    syntactic [AAnd] of the embeddings — but the two are interderivable in
    the legacy entailment, which is what the erasure of [RTFrame] needs. *)
Lemma prenex_and_to_assertion_in {Γ F Δ} (prenex : resource_prenex Γ F Δ) :
  forall (frame : core_assertion F Δ),
  assertion_entails
    (AAnd (prenex_to_assertion prenex) (@core_to_assertion Γ F Δ frame))
    (prenex_to_assertion (prenex_and prenex frame)).
Proof.
  induction prenex as [Δ state | Δ t rest IH]; intro frame;
    cbn [prenex_and prenex_to_assertion].
  - destruct state as [store body].
    cbn [resource_to_assertion resource_stack resource_body
      core_to_assertion].
    eapply EntailsTrans; [apply EntailsStep, ESAndAssocR | apply EntailsRefl].
  - eapply EntailsTrans; [apply EntailsExistsAndRight |].
    apply EntailsExistsMono.
    replace (weaken_assertion (core_to_assertion frame))
      with (@core_to_assertion Γ F (t :: Δ) (weaken_core frame))
      by apply core_to_assertion_weaken.
    apply IH.
Qed.

Lemma prenex_and_to_assertion_out {Γ F Δ} (prenex : resource_prenex Γ F Δ) :
  forall (frame : core_assertion F Δ),
  assertion_entails
    (prenex_to_assertion (prenex_and prenex frame))
    (AAnd (prenex_to_assertion prenex) (@core_to_assertion Γ F Δ frame)).
Proof.
  induction prenex as [Δ state | Δ t rest IH]; intro frame;
    cbn [prenex_and prenex_to_assertion].
  - destruct state as [store body].
    cbn [resource_to_assertion resource_stack resource_body
      core_to_assertion].
    apply EntailsStep, ESAndAssocL.
  - eapply EntailsTrans; [| apply EntailsExistsAndRightOut].
    apply EntailsExistsMono.
    replace (weaken_assertion (core_to_assertion frame))
      with (@core_to_assertion Γ F (t :: Δ) (weaken_core frame))
      by apply core_to_assertion_weaken.
    apply IH.
Qed.

End Make.
End TypedResource.
