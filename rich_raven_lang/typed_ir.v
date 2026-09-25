From Coq Require Import List String ZArith PArith Program.Equality
  ProofIrrelevance Lia.

From raven_iris.rich_raven_lang Require Import
  surface_syntax typed_core typed_assertion typed_resource.

Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope list_scope.

(** Typed statements, procedures, and their elaboration. *)
Module TypedIR.

Import TypedCore.

(** Source names decorate a typed context but do not occur in the resulting
    references.  The head is the most recently declared variable. *)
Inductive named_context : context -> Type :=
| NCNil : named_context []
| NCCons Γ (name : source_name) (t : typ) :
    named_context Γ -> named_context (t :: Γ).

Arguments NCCons {_} _ _ _.

Fixpoint lookup_named {Γ} (declarations : named_context Γ)
    (name : source_name) : option { t : typ & pvar Γ t } :=
  match declarations with
  | NCNil => None
  | NCCons declared_name declared_type tail =>
      if String.eqb name declared_name then
        Some (existT declared_type MHere)
      else
        match lookup_named tail name with
        | Some (existT t variable) => Some (existT t (MThere variable))
        | None => None
        end
  end.

(** A type-preserving embedding of one context into another.  Procedure
    entries use this to say which variables of the body frame receive the
    formal arguments.  Unlike a list of source names, this layout cannot
    refer to a missing or ill-typed body slot. *)
Inductive pvar_list (Γ : context) : context -> Type :=
| PVNil : pvar_list Γ []
| PVCons F t : pvar Γ t -> pvar_list Γ F -> pvar_list Γ (t :: F).

Arguments PVNil {_}.
Arguments PVCons {_ _ _} _ _.

Fixpoint pvar_list_indices {Γ F} (variables : pvar_list Γ F) : list nat :=
  match variables with
  | PVNil => []
  | PVCons variable tail => member_index variable :: pvar_list_indices tail
  end.

Fixpoint lookup_pvar_list {Γ F t} (variables : pvar_list Γ F)
    (formal_variable : member F t) : pvar Γ t.
Proof.
  destruct variables as [|F head_type variable tail].
  - dependent destruction formal_variable.
  - dependent destruction formal_variable.
    + exact variable.
    + exact (@lookup_pvar_list Γ F t tail formal_variable).
Defined.

Lemma lookup_pvar_list_here {Γ F t} (variable : pvar Γ t)
    (tail : pvar_list Γ F) :
  lookup_pvar_list (PVCons variable tail) MHere = variable.
Proof.
  unfold lookup_pvar_list, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl).
  reflexivity.
Qed.

Lemma lookup_pvar_list_there {Γ F head t} (variable : pvar Γ head)
    (tail : pvar_list Γ F) (formal_variable : formal F t) :
  lookup_pvar_list (PVCons variable tail) (MThere formal_variable) =
    lookup_pvar_list tail formal_variable.
Proof.
  unfold lookup_pvar_list, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl).
  reflexivity.
Qed.

Lemma pvar_list_index_member {Γ F t} (variables : pvar_list Γ F)
    (variable : pvar Γ t) :
  In (member_index variable) (pvar_list_indices variables) ->
  exists formal_variable : formal F t,
    lookup_pvar_list variables formal_variable = variable.
Proof.
  induction variables as [| F head_type program_variable tail IH]; simpl.
  - contradiction.
  - intros [Hhead | Htail].
    + assert (Hsigma : @existT typ (fun u => pvar Γ u) head_type program_variable =
          @existT typ (fun u => pvar Γ u) t variable).
      { apply member_index_sig_injective. exact Hhead. }
      dependent destruction Hsigma.
      exists MHere. exact (lookup_pvar_list_here variable tail).
    + destruct (IH Htail) as (formal_variable & Hlookup).
      exists (MThere formal_variable).
      transitivity (lookup_pvar_list tail formal_variable).
      * exact (lookup_pvar_list_there program_variable tail formal_variable).
      * exact Hlookup.
Qed.

Fixpoint named_context_names {Γ} (declarations : named_context Γ) :
    list source_name :=
  match declarations with
  | NCNil => []
  | NCCons name _ tail => name :: named_context_names tail
  end.

Lemma named_context_names_length {Γ} (declarations : named_context Γ) :
  List.length (named_context_names declarations) = List.length Γ.
Proof. induction declarations; simpl; congruence. Qed.

Record field_decl := FieldDecl {
  field_source_name : source_name;
  field_identity : field_id;
}.

(** Elaboration entries carry only what elaboration cannot derive: the
    surface name and the identifier it resolves to.  Arities and return
    types are *not* repeated here.  [Logic] is the single source of truth
    for them, and elaboration reads them from
    [Logic.procedure_args], [Logic.procedure_return],
    [Logic.invariant_args] and [Logic.predicate_args].  Duplicating them in
    the surface environment would be silently ignored data that can
    contradict [Logic] -- the same forgeability argument that rejected a
    carried procedure signature in [TCall]. *)
Record procedure_signature := ProcedureSignature {
  signature_source_name : source_name;
  signature_identity : proc_id;
}.

Record invariant_signature := InvariantSignature {
  invariant_source_name : source_name;
  invariant_identity : inv_id;
}.

Record predicate_signature := PredicateSignature {
  predicate_source_name : source_name;
  predicate_identity : pred_id;
}.

Record elaboration_environment := ElaborationEnvironment {
  elaboration_fields : list field_decl;
  elaboration_procedures : list procedure_signature;
  elaboration_invariants : list invariant_signature;
  elaboration_predicates : list predicate_signature;
}.

Fixpoint lookup_field (name : source_name) (fields : list field_decl) :
    option field_decl :=
  match fields with
  | [] => None
  | field :: fields' =>
      if String.eqb name (field_source_name field)
      then Some field else lookup_field name fields'
  end.

Fixpoint lookup_procedure (name : source_name)
    (procedures : list procedure_signature) : option procedure_signature :=
  match procedures with
  | [] => None
  | procedure :: procedures' =>
      if String.eqb name (signature_source_name procedure)
      then Some procedure else lookup_procedure name procedures'
  end.

Fixpoint lookup_invariant (name : source_name)
    (invariants : list invariant_signature) : option invariant_signature :=
  match invariants with
  | [] => None
  | invariant :: invariants' =>
      if String.eqb name (invariant_source_name invariant)
      then Some invariant else lookup_invariant name invariants'
  end.

Fixpoint lookup_predicate (name : source_name)
    (predicates : list predicate_signature) : option predicate_signature :=
  match predicates with
  | [] => None
  | predicate :: predicates' =>
      if String.eqb name (predicate_source_name predicate)
      then Some predicate else lookup_predicate name predicates'
  end.

Module Make (RAs : RA_VALUE_CONFIG) (Logic : TypedAssertion.LOGIC_SIGNATURE).
(** The resource core is applied once, here, and projected downstream: the
    functor body declares inductives, so a second application would create
    a generative copy whose [core_assertion] is a different type. *)
Module Resource := TypedResource.Make RAs Logic.
Module Assertions := Resource.Assertions.
Module Core := Assertions.Core.
Import Core Assertions.

(** Runtime program expressions use program variables.  Logical expressions
    use [value_ref]; the symbolic Hoare rules will connect the two through a
    typed [symbolic_store]. *)
Inductive pexpr (Γ : context) : typ -> Type :=
| PEVar t (variable : pvar Γ t) : pexpr Γ t
| PEVal t (value : tval t) : pexpr Γ t
| PEUnOp input output (op : unop input output) :
    pexpr Γ input -> pexpr Γ output
| PEBinOp left right output (op : binop left right output) :
    pexpr Γ left -> pexpr Γ right -> pexpr Γ output.

Arguments PEVar {_ _} _.
Arguments PEVal {_ _} _.
Arguments PEUnOp {_ _ _} _ _.
Arguments PEBinOp {_ _ _ _} _ _ _.

(** Evidence that a conditional guard may be evaluated before opening an
    invariant.  Program expressions in the current typed fragment mention
    only runtime stack variables and values, so every such guard is movable.

    This indexed witness is intentionally narrower than a boolean classifier:
    normalization must receive evidence for the particular guard it moves.
    Future proof-only ghost guards and executable guards requiring an explicit
    control result will extend the conditional syntax and their normalization
    cases; they are not silently classified as movable here. *)
Inductive guard_mobility {Γ} (condition : pexpr Γ TBool) : Type :=
| GuardMovable : guard_mobility condition.

Definition current_guard_mobility {Γ} (condition : pexpr Γ TBool) :
    guard_mobility condition := GuardMovable condition.

Inductive pexpr_list (Γ : context) : context -> Type :=
| PENil : pexpr_list Γ []
| PECons t ts : pexpr Γ t -> pexpr_list Γ ts -> pexpr_list Γ (t :: ts).

Arguments PENil {_}.
Arguments PECons {_ _ _} _ _.

Fixpoint pexpr_list_append {Γ left_types right_types}
    (left : pexpr_list Γ left_types) (right : pexpr_list Γ right_types) :
    pexpr_list Γ (left_types ++ right_types) :=
  match left with
  | PENil => right
  | PECons expression tail =>
      PECons expression (pexpr_list_append tail right)
  end.

Inductive field_init (Γ : context) : Type :=
| FieldInit field : pexpr Γ (Logic.field_type field) -> field_init Γ.

Arguments FieldInit {_} _ _.

Definition field_init_id {Γ} (initialization : field_init Γ) : field_id :=
  match initialization with FieldInit field _ => field end.

Definition field_init_is_ghost {Γ} (initialization : field_init Γ) : bool :=
  match initialization with
  | FieldInit field _ =>
      match Logic.field_type field with TRA _ => true | _ => false end
  end.

Inductive ghost_field_init (Γ : context) : Type :=
| GhostFieldInit resource field
    (field_type : Logic.field_type field = TRA resource)
    (value : pexpr Γ (TRA resource)).

Arguments GhostFieldInit {_} _ _ _ _.

Definition ghost_field_init_id {Γ} (initialization : ghost_field_init Γ) :
    field_id :=
  match initialization with GhostFieldInit _ field _ _ => field end.

Definition physical_field_initializers {Γ} (fields : list (field_init Γ)) :
    list (field_init Γ) := filter (fun field => negb (field_init_is_ghost field)) fields.

Fixpoint ghost_field_initializers {Γ} (fields : list (field_init Γ)) :
    list (ghost_field_init Γ) :=
  match fields with
  | [] => []
  | FieldInit field value :: fields' =>
      match Logic.field_type field as field_type
        return Logic.field_type field = field_type -> pexpr Γ field_type ->
          list (ghost_field_init Γ) with
      | TRA resource => fun Heq chunk =>
          GhostFieldInit resource field Heq chunk ::
            ghost_field_initializers fields'
      | _ => fun _ _ => ghost_field_initializers fields'
      end eq_refl value
  end.

Definition ghost_initializers_require_physical {Γ}
    (fields : list (field_init Γ)) : Prop :=
  ghost_field_initializers fields <> [] -> physical_field_initializers fields <> [].

Lemma physical_field_initializers_ids_nodup {Γ}
    (fields : list (field_init Γ)) :
    NoDup (map field_init_id fields) ->
    NoDup (map field_init_id (physical_field_initializers fields)).
Proof.
  induction fields as [| initialization fields IH]; simpl; auto.
  intros Hnodup.
  inversion_clear Hnodup as [| id ids Hnotin Htail].
  destruct (field_init_is_ghost initialization) eqn:Hghost; simpl.
  - apply IH; exact Htail.
  - constructor.
    + intro Hin.
      apply Hnotin.
      apply in_map_iff in Hin.
      destruct Hin as [initialization' [Heq Hin]].
      apply in_map_iff.
      exists initialization'; split; [exact Heq |].
      apply filter_In in Hin.
      exact (proj1 Hin).
    + apply IH; exact Htail.
Qed.

Definition return_context (return_type : typ) : context := [return_type].

Inductive return_slot : forall return_type t,
    member (return_context return_type) t -> Type :=
| ReturnSlot return_type :
    return_slot return_type return_type MHere.

Inductive call_target (Γ : context) : typ -> Type :=
| CTDiscard t : call_target Γ t
| CTStore t (target : pvar Γ t) : call_target Γ t.

Arguments CTDiscard {_ _}.
Arguments CTStore {_ _} _.

Inductive stmt (Γ : context) : Type :=
| TDone
| TAssert (condition : pexpr Γ TBool)
| TAssign t (target : pvar Γ t) (value : pexpr Γ t)
| TFieldRead (field : field_id)
    (target : pvar Γ (Logic.field_type field)) (base : pexpr Γ TRef)
| TFieldWrite (field : field_id) (base : pexpr Γ TRef)
    (value : pexpr Γ (Logic.field_type field))
| TAlloc (target : pvar Γ TRef)
    (fields : list (field_init Γ))
| TGhostUpdate (field : field_id) (base : pexpr Γ TRef)
    (old_value new_value : pexpr Γ (Logic.field_type field))
| TCall (procedure : proc_id)
    (arguments : pexpr_list Γ (Logic.procedure_args procedure))
    (target : call_target Γ (Logic.procedure_return procedure))
| TSpawn (procedure : proc_id)
    (arguments : pexpr_list Γ (Logic.procedure_args procedure))
| TUnfold (invariant : inv_id)
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
| TFold (invariant : inv_id)
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
| TPredicateUnfold (predicate : pred_id)
    (arguments : pexpr_list Γ (Logic.predicate_args predicate))
| TPredicateFold (predicate : pred_id)
    (arguments : pexpr_list Γ (Logic.predicate_args predicate))
| TInvAccess (invariant : inv_id)
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
    (body : stmt Γ)
| TIf (condition : pexpr Γ TBool)
    (then_branch else_branch : stmt Γ)
| TSeq (first second : stmt Γ)
| TAtomic (body : stmt Γ).

Arguments TDone {_}.
Arguments TAssert {_} _.
Arguments TAssign {_ _} _ _.
Arguments TFieldRead {_} _ _ _.
Arguments TFieldWrite {_} _ _ _.
Arguments TAlloc {_} _ _.
Arguments TGhostUpdate {_} _ _ _ _.
Arguments TCall {_} _ _ _.
Arguments TSpawn {_} _ _.
Arguments TUnfold {_} _ _.
Arguments TFold {_} _ _.
Arguments TPredicateUnfold {_} _ _.
Arguments TPredicateFold {_} _ _.
Arguments TInvAccess {_} _ _ _.
Arguments TIf {_} _ _ _.
Arguments TSeq {_} _ _.
Arguments TAtomic {_} _.

(** Canonical procedure-entry stores.  Every frame slot starts as a fresh
    procedure-local symbolic atom; installing the formal-variable embedding
    then replaces exactly the argument slots by their corresponding formal
    references. *)
Fixpoint procedure_local_entry_store_from {Γ F}
    (identity : proc_id) (slot : nat) : symbolic_store Γ F [] :=
  match Γ with
  | [] => StoreNil
  | t :: Γ' =>
      StoreCons (RefAtom (ProcedureEntryAtom identity slot))
        (@procedure_local_entry_store_from Γ' F identity (S slot))
  end.

Fixpoint set_store_reference {Γ F Δ t}
    (store : symbolic_store Γ F Δ) (variable : pvar Γ t)
    (reference : value_ref F Δ t) : symbolic_store Γ F Δ.
Proof.
  destruct store as [|head_type tail_context head tail].
  - dependent destruction variable.
  - dependent destruction variable.
    + exact (StoreCons reference tail).
    + exact (StoreCons head
        (@set_store_reference tail_context F Δ t tail variable reference)).
Defined.

Lemma set_store_reference_here {F Δ head_type tail_context}
    (head : value_ref F Δ head_type)
    (tail : symbolic_store tail_context F Δ)
    (reference : value_ref F Δ head_type) :
  set_store_reference (StoreCons head tail) MHere reference =
    StoreCons reference tail.
Proof.
  unfold set_store_reference, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl).
  reflexivity.
Qed.

Lemma set_store_reference_there {F Δ head_type tail_context t}
    (head : value_ref F Δ head_type)
    (tail : symbolic_store tail_context F Δ) (variable : pvar tail_context t)
    (reference : value_ref F Δ t) :
  set_store_reference (StoreCons head tail) (MThere variable) reference =
    StoreCons head (set_store_reference tail variable reference).
Proof.
  unfold set_store_reference, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl).
  reflexivity.
Qed.

Fixpoint install_procedure_formals {Γ F Full}
    (variables : pvar_list Γ F)
    (embed : forall t, formal F t -> formal Full t)
    (store : symbolic_store Γ Full []) : symbolic_store Γ Full [] :=
  match variables in pvar_list _ F0
      return (forall t, formal F0 t -> formal Full t) ->
        symbolic_store Γ Full [] -> symbolic_store Γ Full [] with
  | PVNil => fun _ store => store
  | @PVCons _ tail t variable rest => fun embed store =>
      install_procedure_formals rest
        (fun u formal => embed u (MThere formal))
        (set_store_reference store variable (RefFormal (embed t MHere)))
  end embed store.

Definition canonical_entry_store_from {Γ F} (identity : proc_id)
    (formal_variables : pvar_list Γ F) : symbolic_store Γ F [] :=
  install_procedure_formals formal_variables (fun _ formal => formal)
    (procedure_local_entry_store_from identity 0).

Definition canonical_procedure_entry_store {Γ identity}
    (formal_variables : pvar_list Γ (Logic.procedure_args identity)) :
    symbolic_store Γ (Logic.procedure_args identity) [] :=
  canonical_entry_store_from identity formal_variables.

(** Indexed by the declared identity rather than by a free formal context:
    the formals and return type are read off [Logic].  The
    [procedure_identity] and [procedure_return_type] fields are the index
    and a projection of it respectively, and are kept below as definitions
    so that existing [procedure_identity _ _ procedure] uses continue to
    read. *)
Record typed_procedure (Γ : context) (identity : proc_id) := TypedProcedure {
  procedure_variables : named_context Γ;
  procedure_formals : named_context (Logic.procedure_args identity);
  procedure_formal_variables : pvar_list Γ (Logic.procedure_args identity);
  procedure_return_variable : pvar Γ (Logic.procedure_return identity);
  (** Core assertions, not [assertion]: a procedure's contract must not
      mention the caller's stack, and with the resource separation that is
      a typing fact rather than the two [stack_free] side conditions
      [procedure_wf] used to carry.  Note the absent [Γ]. *)
  procedure_precondition :
    Resource.core_assertion (Logic.procedure_args identity) [];
  procedure_postcondition :
    Resource.core_assertion (Logic.procedure_args identity)
      (return_context (Logic.procedure_return identity));
  procedure_body : stmt Γ;
}.

Arguments TypedProcedure {_ _} _ _ _ _ _ _ _.

Definition procedure_entry_store (Γ : context) (identity : proc_id)
    (procedure : typed_procedure Γ identity) :
    symbolic_store Γ (Logic.procedure_args identity) [] :=
  canonical_procedure_entry_store
    (procedure_formal_variables _ _ procedure).

Definition procedure_identity (Γ : context) (identity : proc_id)
    (_ : typed_procedure Γ identity) : proc_id := identity.

Definition procedure_return_type (Γ : context) (identity : proc_id)
    (_ : typed_procedure Γ identity) : typ := Logic.procedure_return identity.

(** [procedure_precondition_stack_free] and
    [procedure_postcondition_stack_free] are gone: the contract fields are
    [core_assertion]s, which cannot mention a stack at all. *)
Record procedure_wf {Γ F} (procedure : typed_procedure Γ F) : Prop := {
  procedure_variable_names_unique :
    NoDup (named_context_names (procedure_variables _ _ procedure));
  procedure_formal_slots_unique :
    NoDup (pvar_list_indices (procedure_formal_variables _ _ procedure));
  procedure_return_slot_local :
    ~ In (member_index (procedure_return_variable _ _ procedure))
        (pvar_list_indices (procedure_formal_variables _ _ procedure));
  procedure_precondition_entry_free :
    Resource.core_entry_free (procedure_precondition _ _ procedure);
  procedure_postcondition_entry_free :
    Resource.core_entry_free (procedure_postcondition _ _ procedure);
}.

(** A procedure table must be heterogeneous: procedures may have different
    stack contexts, formal contexts, and return types.  The existential
    package below keeps those indices available when an entry is selected,
    while allowing the table itself to be an ordinary finite list. *)
Definition packed_typed_procedure :=
  { Γ : context & { identity : proc_id & typed_procedure Γ identity } }.

Definition pack_typed_procedure {Γ identity}
    (procedure : typed_procedure Γ identity) : packed_typed_procedure :=
  @existT context (fun variables =>
    { identity : proc_id & typed_procedure variables identity }) Γ
    (@existT proc_id (typed_procedure Γ) identity procedure).

Definition packed_procedure_id (procedure : packed_typed_procedure) : proc_id :=
  projT1 (projT2 procedure).

Definition packed_procedure_wf (procedure : packed_typed_procedure) : Prop :=
  @procedure_wf _ _ (projT2 (projT2 procedure)).

Record typed_procedure_signature := TypedProcedureSignature {
  typed_signature_identity : proc_id;
  typed_signature_arguments : context;
  typed_signature_return : typ;
}.

Definition packed_procedure_signature
    (procedure : packed_typed_procedure) : typed_procedure_signature :=
  TypedProcedureSignature (packed_procedure_id procedure)
    (Logic.procedure_args (packed_procedure_id procedure))
    (Logic.procedure_return (packed_procedure_id procedure)).

Fixpoint lookup_packed_procedure (identity : proc_id)
    (procedures : list packed_typed_procedure) :
    option packed_typed_procedure :=
  match procedures with
  | [] => None
  | procedure :: procedures' =>
      if Pos.eqb identity (packed_procedure_id procedure)
      then Some procedure
      else lookup_packed_procedure identity procedures'
  end.

(** Dependent lookup: the caller receives a procedure already at the
    requested identity, so the identity equality is consumed here instead
    of escaping into every client.  This is what makes
    [PROCEDURE_CONTRACT_COHERENCE.instantiated_pre_selects] unnecessary:
    recovering the callee no longer requires inverting a [Prop], and so no
    longer requires classical choice. *)
Fixpoint lookup_typed_procedure_at (identity : proc_id)
    (procedures : list packed_typed_procedure) :
    option { Γ : context & typed_procedure Γ identity } :=
  match procedures with
  | [] => None
  | existT Γ (existT declared body) :: procedures' =>
      match Pos.eq_dec identity declared with
      | left equality =>
          Some (existT Γ
            (eq_rect declared (typed_procedure Γ) body identity
              (eq_sym equality)))
      | right _ => lookup_typed_procedure_at identity procedures'
      end
  end.

(** The dependent lookup agrees with the packed one. *)
Lemma lookup_typed_procedure_at_spec (identity : proc_id)
    (procedures : list packed_typed_procedure) :
  match lookup_typed_procedure_at identity procedures with
  | Some (existT _ body) =>
      lookup_packed_procedure identity procedures =
        Some (pack_typed_procedure body)
  | None => lookup_packed_procedure identity procedures = None
  end.
Proof.
  induction procedures as [| entry procedures' IH]; [reflexivity |].
  destruct entry as [Γ [declared body]].
  cbn [lookup_typed_procedure_at lookup_packed_procedure packed_procedure_id
    projT1 projT2].
  destruct (Pos.eq_dec identity declared) as [equality | Hneq].
  - subst declared. cbn. rewrite Pos.eqb_refl. reflexivity.
  - rewrite ((proj2 (Pos.eqb_neq identity declared)) Hneq). exact IH.
Qed.

Definition procedure_signature_coherent
    (procedures : list packed_typed_procedure) : Prop :=
  forall first second,
    In first procedures -> In second procedures ->
    packed_procedure_id first = packed_procedure_id second ->
    packed_procedure_signature first = packed_procedure_signature second.

Record typed_procedure_environment := TypedProcedureEnvironment {
  procedure_entries : list packed_typed_procedure;
  procedure_ids_unique : NoDup (map packed_procedure_id procedure_entries);
  procedure_entries_wf : Forall packed_procedure_wf procedure_entries;
  procedure_signatures_coherent : procedure_signature_coherent procedure_entries;
}.

Lemma procedure_signature_coherent_of_nodup procedures :
  NoDup (map packed_procedure_id procedures) ->
  procedure_signature_coherent procedures.
Proof.
  intros Hnodup.
  revert Hnodup.
  induction procedures as [| head tail IH];
    intros Hnodup first second Hfirst Hsecond Hids.
  - contradiction.
  - simpl in Hnodup, Hfirst, Hsecond.
    destruct Hfirst as [<- | Hfirst].
    + destruct Hsecond as [<- | Hsecond].
      * reflexivity.
      * exfalso. inversion Hnodup as [| id ids Hnot Htail]. apply Hnot.
        rewrite Hids. eapply in_map. exact Hsecond.
    + destruct Hsecond as [<- | Hsecond].
      * exfalso. inversion Hnodup as [| id ids Hnot Htail]. apply Hnot.
        rewrite <- Hids. eapply in_map. exact Hfirst.
      * apply IH; [inversion Hnodup; assumption | exact Hfirst |
          exact Hsecond | exact Hids].
Qed.

Definition lookup_typed_procedure (environment : typed_procedure_environment)
    (identity : proc_id) : option packed_typed_procedure :=
  lookup_packed_procedure identity (procedure_entries environment).

Lemma lookup_packed_procedure_id identity procedures procedure :
  lookup_packed_procedure identity procedures = Some procedure ->
  packed_procedure_id procedure = identity.
Proof.
  revert identity procedure.
  induction procedures as [| head tail IH]; intros identity procedure Hlookup;
    simpl in Hlookup.
  - discriminate.
  - destruct (Pos.eqb identity (packed_procedure_id head)) eqn:Heq.
    + inversion Hlookup. subst procedure.
      apply Pos.eqb_eq in Heq. symmetry; exact Heq.
    + eapply IH; eauto.
Qed.

Lemma lookup_packed_procedure_member identity procedures procedure :
  lookup_packed_procedure identity procedures = Some procedure ->
  List.In procedure procedures.
Proof.
  induction procedures as [|head tail IH]; simpl; [discriminate|].
  destruct (Pos.eqb identity (packed_procedure_id head)); intros Hlookup.
  - inversion Hlookup; subst. now left.
  - right. now apply IH.
Qed.

Lemma lookup_typed_procedure_member environment identity procedure :
  lookup_typed_procedure environment identity = Some procedure ->
  List.In procedure (procedure_entries environment).
Proof. apply lookup_packed_procedure_member. Qed.

Lemma lookup_typed_procedure_wf environment identity procedure :
  lookup_typed_procedure environment identity = Some procedure ->
  packed_procedure_wf procedure.
Proof.
  intro Hlookup.
  eapply Forall_forall.
  - exact (procedure_entries_wf environment).
  - now apply lookup_typed_procedure_member in Hlookup.
Qed.

Lemma lookup_packed_procedure_unique identity procedures first second :
  NoDup (map packed_procedure_id procedures) ->
  lookup_packed_procedure identity procedures = Some first ->
  lookup_packed_procedure identity procedures = Some second ->
  first = second.
Proof.
  revert identity first second.
  induction procedures as [| head tail IH];
    intros identity first second Hnodup Hfirst Hsecond; simpl in *.
  - discriminate.
  - destruct (Pos.eqb identity (packed_procedure_id head)) eqn:Heq.
    + inversion Hfirst; inversion Hsecond; subst first; subst second; reflexivity.
    + eapply IH; [inversion Hnodup; assumption | exact Hfirst | exact Hsecond].
Qed.

Inductive elaboration_error :=
| EEUnknownVariable (name : source_name)
| EEUnknownField (name : source_name)
| EEUnknownProcedure (name : source_name)
| EEUnknownInvariant (name : source_name)
| EETypeMismatch (expected actual : typ)
| EEExpectedReference
| EEArgumentCount
| EEReturnTarget
| EEUnsupportedExpression
| EEUnsupportedStatement.

Definition packed_pexpr Γ := { t : typ & pexpr Γ t }.

Definition expect_pexpr {Γ} (expected : typ) (expression : packed_pexpr Γ) :
    elaboration_error + pexpr Γ expected.
Proof.
  destruct expression as [actual expression].
  destruct (typ_eq_dec expected actual) as [<- | Hneq].
  - exact (inr expression).
  - exact (inl (EETypeMismatch expected actual)).
Defined.

(** Raven permits integer syntax where an RA-valued ghost field is expected;
    the elaborator inserts the resource algebra's canonical embedding.  The
    coercion is deliberately used only at field initialization and ghost
    update sites, so ordinary expression typing remains explicit. *)
Definition expect_field_chunk {Γ} (expected : typ)
    (expression : packed_pexpr Γ) : elaboration_error + pexpr Γ expected.
Proof.
  destruct expression as [actual expression].
  destruct (typ_eq_dec expected actual) as [Heq | Hneq].
  - subst actual. exact (inr expression).
  - destruct expected as [| | | | resource].
    + exact (inl (EETypeMismatch TBool actual)).
    + exact (inl (EETypeMismatch TInt actual)).
    + exact (inl (EETypeMismatch TRef actual)).
    + exact (inl (EETypeMismatch TUnit actual)).
    + destruct actual as [| | | | actual_resource].
      * exact (inl (EETypeMismatch (TRA resource) TBool)).
      * exact (inr (PEUnOp (URAOfInt resource) expression)).
      * exact (inl (EETypeMismatch (TRA resource) TRef)).
      * exact (inl (EETypeMismatch (TRA resource) TUnit)).
      * exact (inl (EETypeMismatch (TRA resource) (TRA actual_resource))).
Defined.

Definition expect_pvar {Γ} (expected : typ)
    (variable : { t : typ & pvar Γ t }) :
    elaboration_error + pvar Γ expected.
Proof.
  destruct variable as [actual variable].
  destruct (typ_eq_dec expected actual) as [<- | Hneq].
  - exact (inr variable).
  - exact (inl (EETypeMismatch expected actual)).
Defined.

Definition elaborate_int_binop {Γ} (op : binop TInt TInt TInt)
    (left_expression right_expression : packed_pexpr Γ) :
    elaboration_error + packed_pexpr Γ :=
  match expect_pexpr TInt left_expression, expect_pexpr TInt right_expression with
  | inr left', inr right' => inr (existT TInt (PEBinOp op left' right'))
  | inl error, _ | _, inl error => inl error
  end.

Definition elaborate_int_comparison {Γ} (op : binop TInt TInt TBool)
    (left_expression right_expression : packed_pexpr Γ) :
    elaboration_error + packed_pexpr Γ :=
  match expect_pexpr TInt left_expression, expect_pexpr TInt right_expression with
  | inr left', inr right' => inr (existT TBool (PEBinOp op left' right'))
  | inl error, _ | _, inl error => inl error
  end.

Definition elaborate_bool_binop {Γ} (op : binop TBool TBool TBool)
    (left_expression right_expression : packed_pexpr Γ) :
    elaboration_error + packed_pexpr Γ :=
  match expect_pexpr TBool left_expression, expect_pexpr TBool right_expression with
  | inr left', inr right' => inr (existT TBool (PEBinOp op left' right'))
  | inl error, _ | _, inl error => inl error
  end.

Definition elaborate_equality {Γ} (negated : bool)
    (left_expression right_expression : packed_pexpr Γ) :
    elaboration_error + packed_pexpr Γ.
Proof.
  destruct left_expression as [left_type left_expression].
  destruct right_expression as [right_type right_expression].
  destruct (typ_eq_dec left_type right_type) as [<- | Hneq].
  - refine (inr (existT TBool (PEBinOp _ left_expression right_expression))).
    exact (if negated then BNe left_type else BEq left_type).
  - exact (inl (EETypeMismatch left_type right_type)).
Defined.

Fixpoint elaborate_expr {Γ} (variables : named_context Γ)
    (expression : source_expr) : elaboration_error + packed_pexpr Γ :=
  match expression with
  | SEVar name =>
      match lookup_named variables name with
      | Some (existT t variable) => inr (existT t (PEVar variable))
      | None => inl (EEUnknownVariable name)
      end
  | SEVal (SVBool value) => inr (existT TBool (PEVal (VBool value)))
  | SEVal (SVInt value) => inr (existT TInt (PEVal (VInt value)))
  | SEVal SVUnit => inr (existT TUnit (PEVal VUnit))
  | SEUnOp SUNot operand =>
      match elaborate_expr variables operand with
      | inl error => inl error
      | inr operand' =>
          match expect_pexpr TBool operand' with
          | inl error => inl error
          | inr operand'' => inr (existT TBool (PEUnOp UNot operand''))
          end
      end
  | SEUnOp SUNeg operand =>
      match elaborate_expr variables operand with
      | inl error => inl error
      | inr operand' =>
          match expect_pexpr TInt operand' with
          | inl error => inl error
          | inr operand'' => inr (existT TInt (PEUnOp UNeg operand''))
          end
      end
  | SEBinOp op left_expression right_expression =>
      match elaborate_expr variables left_expression,
            elaborate_expr variables right_expression with
      | inl error, _ | _, inl error => inl error
      | inr left', inr right' =>
          match op with
          | SBAdd => elaborate_int_binop BAdd left' right'
          | SBSub => elaborate_int_binop BSub left' right'
          | SBMul => elaborate_int_binop BMul left' right'
          | SBDiv => elaborate_int_binop BDiv left' right'
          | SBMod => elaborate_int_binop BMod left' right'
          | SBLt => elaborate_int_comparison BLt left' right'
          | SBLe => elaborate_int_comparison BLe left' right'
          | SBGt => elaborate_int_comparison BGt left' right'
          | SBGe => elaborate_int_comparison BGe left' right'
          | SBAnd => elaborate_bool_binop BAnd left' right'
          | SBOr => elaborate_bool_binop BOr left' right'
          | SBEq => elaborate_equality false left' right'
          | SBNe => elaborate_equality true left' right'
          end
      end
  | SEField _ _ | SECall _ _ => inl EEUnsupportedExpression
  end.

Fixpoint elaborate_expr_list {Γ} (variables : named_context Γ)
    (types : context) (expressions : list source_expr) :
    elaboration_error + pexpr_list Γ types :=
  match types, expressions with
  | [], [] => inr PENil
  | expected :: types', expression :: expressions' =>
      match elaborate_expr variables expression,
            elaborate_expr_list variables types' expressions' with
      | inr expression', inr expressions'' =>
          match expect_pexpr expected expression' with
          | inr expression'' => inr (PECons expression'' expressions'')
          | inl error => inl error
          end
      | inl error, _ | _, inl error => inl error
      end
  | _, _ => inl EEArgumentCount
  end.

Fixpoint elaborate_field_inits {Γ} (environment : elaboration_environment)
    (variables : named_context Γ)
    (fields : list (source_name * source_expr)) :
    elaboration_error + list (field_init Γ) :=
  match fields with
  | [] => inr []
  | (field_name, value) :: fields' =>
      match lookup_field field_name (elaboration_fields environment),
            elaborate_expr variables value,
            elaborate_field_inits environment variables fields' with
      | Some field, inr value', inr fields'' =>
          match expect_field_chunk
              (Logic.field_type (field_identity field)) value' with
          | inr value'' => inr (FieldInit (field_identity field) value'' :: fields'')
          | inl error => inl error
          end
      | None, _, _ => inl (EEUnknownField field_name)
      | _, inl error, _ | _, _, inl error => inl error
      end
  end.

Fixpoint elaborate_stmt {Γ} (environment : elaboration_environment)
    (variables : named_context Γ) (statement : source_stmt) :
    elaboration_error + stmt Γ :=
  match statement with
  | SSDone => inr TDone
  | SSAssert condition =>
      match elaborate_expr variables condition with
      | inl error => inl error
      | inr condition' =>
          match expect_pexpr TBool condition' with
          | inl error => inl error
          | inr condition'' => inr (TAssert condition'')
          end
      end
  | SSAssign target (SEField base field_name)
  | SSFieldRead target base field_name =>
      match lookup_named variables target,
            elaborate_expr variables base,
            lookup_field field_name (elaboration_fields environment) with
      | Some (existT target_type target'), inr base', Some field =>
          match expect_pexpr TRef base' with
          | inl error => inl error
          | inr base'' =>
              match expect_pvar (Logic.field_type (field_identity field))
                      (existT target_type target') with
              | inr target'' =>
                  inr (TFieldRead (field_identity field)
                    target'' base'')
              | inl error => inl error
              end
          end
      | None, _, _ => inl (EEUnknownVariable target)
      | _, inl error, _ => inl error
      | _, _, None => inl (EEUnknownField field_name)
      end
  | SSAssign target value =>
      match lookup_named variables target, elaborate_expr variables value with
      | Some (existT target_type target'), inr value' =>
          match expect_pexpr target_type value' with
          | inl error => inl error
          | inr value'' =>
              inr (TAssign target' value'')
          end
      | None, _ => inl (EEUnknownVariable target)
      | _, inl error => inl error
      end
  | SSFieldWrite base field_name value =>
      match elaborate_expr variables base,
            elaborate_expr variables value,
            lookup_field field_name (elaboration_fields environment) with
      | inr base', inr value', Some field =>
          match expect_pexpr TRef base',
                expect_pexpr (Logic.field_type (field_identity field)) value' with
          | inr base'', inr value'' =>
              inr (TFieldWrite (field_identity field) base'' value'')
          | inl error, _ | _, inl error => inl error
          end
      | inl error, _, _ | _, inl error, _ => inl error
      | _, _, None => inl (EEUnknownField field_name)
      end
  | SSAlloc target fields =>
      match lookup_named variables target,
            elaborate_field_inits environment variables fields with
      | Some (existT target_type target'), inr fields' =>
          match expect_pvar TRef (existT target_type target') with
          | inr target'' => inr (TAlloc target'' fields')
          | inl error => inl error
          end
      | None, _ => inl (EEUnknownVariable target)
      | _, inl error => inl error
      end
  | SSGhostUpdate base field_name old_value new_value =>
      match lookup_field field_name (elaboration_fields environment),
            elaborate_expr variables base,
            elaborate_expr variables old_value,
            elaborate_expr variables new_value with
      | Some field, inr base', inr old_value', inr new_value' =>
          match expect_pexpr TRef base',
                expect_field_chunk
                  (Logic.field_type (field_identity field)) old_value',
                expect_field_chunk
                  (Logic.field_type (field_identity field)) new_value' with
          | inr base'', inr old_value'', inr new_value'' =>
              inr (TGhostUpdate (field_identity field) base''
                old_value'' new_value'')
          | inl error, _, _ | _, inl error, _ | _, _, inl error => inl error
          end
      | None, _, _, _ => inl (EEUnknownField field_name)
      | _, inl error, _, _ | _, _, inl error, _ | _, _, _, inl error => inl error
      end
  | SSCall target procedure_name arguments =>
      match lookup_procedure procedure_name
              (elaboration_procedures environment) with
      | None => inl (EEUnknownProcedure procedure_name)
      | Some procedure =>
          match elaborate_expr_list variables
                  (Logic.procedure_args (signature_identity procedure)) arguments with
          | inl error => inl error
          | inr arguments' =>
              match target with
              | None =>
                  inr (TCall (signature_identity procedure)
                    arguments' (@CTDiscard Γ (Logic.procedure_return (signature_identity procedure))))
              | Some target_name =>
                  match lookup_named variables target_name with
                  | None => inl (EEUnknownVariable target_name)
                  | Some (existT target_type target') =>
                      match typ_eq_dec target_type
                          (Logic.procedure_return
                            (signature_identity procedure)) with
                      | left equality =>
                          (* Transport the target slot to the declared
                             return type.  This is a genuine check on the
                             surface program, not bookkeeping: the user's
                             target variable must have the callee's return
                             type. *)
                          inr (TCall (signature_identity procedure)
                            arguments'
                            (CTStore (eq_rect target_type
                              (fun result => pvar Γ result) target' _
                              equality)))
                      | right _ => inl (EETypeMismatch target_type
                          (Logic.procedure_return
                            (signature_identity procedure)))
                      end
                  end
              end
          end
      end
  | SSSpawn procedure_name arguments =>
      match lookup_procedure procedure_name
              (elaboration_procedures environment) with
      | None => inl (EEUnknownProcedure procedure_name)
      | Some procedure =>
          match elaborate_expr_list variables
                  (Logic.procedure_args (signature_identity procedure)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TSpawn (signature_identity procedure) arguments')
          end
      end
  | SSUnfold name arguments =>
      match lookup_invariant name (elaboration_invariants environment),
            lookup_predicate name (elaboration_predicates environment) with
      | Some invariant, _ =>
          match elaborate_expr_list variables
                  (Logic.invariant_args (invariant_identity invariant)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TUnfold (invariant_identity invariant) arguments')
          end
      | None, Some predicate =>
          match elaborate_expr_list variables
                  (Logic.predicate_args (predicate_identity predicate)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TPredicateUnfold (predicate_identity predicate) arguments')
          end
      | None, None => inl (EEUnknownInvariant name)
      end
  | SSFold name arguments =>
      match lookup_invariant name (elaboration_invariants environment),
            lookup_predicate name (elaboration_predicates environment) with
      | Some invariant, _ =>
          match elaborate_expr_list variables
                  (Logic.invariant_args (invariant_identity invariant)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TFold (invariant_identity invariant) arguments')
          end
      | None, Some predicate =>
          match elaborate_expr_list variables
                  (Logic.predicate_args (predicate_identity predicate)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TPredicateFold (predicate_identity predicate) arguments')
          end
      | None, None => inl (EEUnknownInvariant name)
      end
  | SSSeq first second =>
      match elaborate_stmt environment variables first with
      | inl error => inl error
      | inr first' =>
          match elaborate_stmt environment variables second with
          | inl error => inl error
          | inr second' =>
              inr (TSeq first' second')
          end
      end
  | SSIf condition then_branch else_branch =>
      match elaborate_expr variables condition with
      | inl error => inl error
      | inr condition' =>
          match expect_pexpr TBool condition' with
          | inl error => inl error
          | inr condition'' =>
              match elaborate_stmt environment variables then_branch with
              | inl error => inl error
              | inr then_branch' =>
                  match elaborate_stmt environment variables else_branch with
                  | inl error => inl error
                  | inr else_branch' =>
                      inr (TIf condition'' then_branch' else_branch')
                  end
              end
          end
      end
  | SSAtomic body =>
      match elaborate_stmt environment variables body with
      | inl error => inl error
      | inr body' => inr (TAtomic body')
      end
  end.

(** Whether elaboration produced a statement. *)
Definition elaboration_succeeded {Γ} (result : elaboration_error + stmt Γ)
    : Prop :=
  match result with inl _ => False | inr _ => True end.

(** The statement an elaboration produced, given evidence that it succeeded.
    The failure branch is discharged by that evidence rather than by an
    arbitrary placeholder statement, so a program whose source does not
    elaborate is rejected where it is defined instead of silently becoming
    some other program. *)
Definition elaborated_body {Γ} (result : elaboration_error + stmt Γ)
    (succeeded : elaboration_succeeded result) : stmt Γ :=
  match result as result' return elaboration_succeeded result' -> stmt Γ with
  | inl _ => fun impossible => match impossible with end
  | inr body => fun _ => body
  end succeeded.

Lemma elaborated_body_spec {Γ} (result : elaboration_error + stmt Γ)
    (succeeded : elaboration_succeeded result) :
  result = inr (elaborated_body result succeeded).
Proof. destruct result; [destruct succeeded | reflexivity]. Qed.

(* ------------------------------------------------------------------ *)
(** ** Program syntax against a symbolic store

    These mediate between program expressions and the logical expression
    language, so they belong with the store rather than with any one Hoare
    calculus.  They were in [TypedHoare.Make], which put them out of reach
    of the resource calculus of [typed_resource_hoare.v]. *)

Fixpoint symbolize_expr {Γ F Δ t} (store : symbolic_store Γ F Δ)
    (expression : pexpr Γ t) : expr F Δ t :=
  match expression with
  | PEVar variable => ERef (lookup_store store _ variable)
  | PEVal value => EVal value
  | PEUnOp op operand => EUnOp op (symbolize_expr store operand)
  | PEBinOp op operand1 operand2 =>
      EBinOp op (symbolize_expr store operand1) (symbolize_expr store operand2)
  end.

Fixpoint symbolize_expr_list {Γ F Δ ts}
    (store : symbolic_store Γ F Δ) (expressions : pexpr_list Γ ts) :
    expr_list F Δ ts :=
  match expressions with
  | PENil => ExprNil
  | PECons expression expressions' =>
      ExprCons (symbolize_expr store expression)
        (symbolize_expr_list store expressions')
  end.

Lemma symbolize_expr_list_append {Γ F Δ left_types right_types}
    (store : symbolic_store Γ F Δ)
    (left : pexpr_list Γ left_types) (right : pexpr_list Γ right_types) :
  symbolize_expr_list store (pexpr_list_append left right) =
    Assertions.expr_list_append (symbolize_expr_list store left)
      (symbolize_expr_list store right).
Proof.
  induction left; simpl; [reflexivity | now rewrite IHleft].
Qed.

(** Updating a typed symbolic store is structural: the selected slot receives
    bound variable zero and every other slot is weakened across that binder. *)
Fixpoint update_store_with_bound {Γ F Δ t}
    (store : store_data F Δ Γ) (target : pvar Γ t) {struct store} :
    store_data F (t :: Δ) Γ.
Proof.
  destruct store as [| head_type tail_context value tail].
  - dependent destruction target.
  - dependent destruction target.
    + exact (StoreCons (RefBound MHere) (weaken_store tail)).
    + exact (StoreCons (weaken_ref value)
        (@update_store_with_bound tail_context F Δ t tail target)).
Defined.

Lemma lookup_store_here {F Δ head_type tail_context}
    (head : value_ref F Δ head_type)
    (tail : symbolic_store tail_context F Δ) :
  lookup_store (StoreCons head tail) _ MHere = head.
Proof.
  unfold lookup_store, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl). reflexivity.
Qed.

Lemma lookup_store_there {F Δ head_type tail_context t}
    (head : value_ref F Δ head_type)
    (tail : symbolic_store tail_context F Δ)
    (variable : pvar tail_context t) :
  lookup_store (StoreCons head tail) _ (MThere variable) =
    lookup_store tail _ variable.
Proof.
  unfold lookup_store, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl). reflexivity.
Qed.

Lemma lookup_set_store_reference_same {Γ F Δ t}
    (store : symbolic_store Γ F Δ) (variable : pvar Γ t)
    (reference : value_ref F Δ t) :
  lookup_store (set_store_reference store variable reference) t variable =
    reference.
Proof.
  induction store; dependent destruction variable.
  - rewrite set_store_reference_here, lookup_store_here. reflexivity.
  - rewrite set_store_reference_there, lookup_store_there. apply IHstore.
Qed.

Lemma lookup_set_store_reference_other {Γ F Δ t u}
    (store : symbolic_store Γ F Δ) (target : pvar Γ t)
    (reference : value_ref F Δ t) (variable : pvar Γ u) :
  member_index target <> member_index variable ->
  lookup_store (set_store_reference store target reference) u variable =
    lookup_store store u variable.
Proof.
  revert t target reference u variable. induction store;
    intros target_type target reference variable_type variable Hne;
    dependent destruction target; dependent destruction variable.
  - exfalso. apply Hne. reflexivity.
  - rewrite set_store_reference_here, !lookup_store_there. reflexivity.
  - rewrite set_store_reference_there, !lookup_store_here. reflexivity.
  - rewrite set_store_reference_there, !lookup_store_there.
    apply IHstore. cbn [member_index] in Hne. lia.
Qed.

Lemma lookup_procedure_local_entry_store_from {Γ F} identity slot t
    (variable : pvar Γ t) :
  lookup_store (@procedure_local_entry_store_from Γ F identity slot)
      t variable =
    RefAtom (ProcedureEntryAtom identity (slot + member_index variable)).
Proof.
  revert slot. induction variable; intros slot;
    cbn [procedure_local_entry_store_from member_index].
  - rewrite lookup_store_here.
    replace (slot + 0)%nat with slot by lia. reflexivity.
  - rewrite lookup_store_there, IHvariable.
    replace (slot + S (member_index variable))%nat with
      (S slot + member_index variable)%nat by lia. reflexivity.
Qed.

Lemma lookup_install_procedure_formals_absent {Γ F Full}
    (variables : pvar_list Γ F)
    (embed : forall t, formal F t -> formal Full t)
    (store : symbolic_store Γ Full []) t (variable : pvar Γ t) :
  ~ In (member_index variable) (pvar_list_indices variables) ->
  lookup_store (install_procedure_formals variables embed store) t variable =
    lookup_store store t variable.
Proof.
  revert embed store t variable. induction variables;
    intros embed store value_type variable Hnot; simpl in *; first reflexivity.
  rewrite IHvariables.
  - apply lookup_set_store_reference_other. intros Heq.
    apply Hnot. left. exact Heq.
  - intros Hin. apply Hnot. now right.
Qed.

Lemma lookup_install_procedure_formals_present {Γ F Full}
    (variables : pvar_list Γ F)
    (embed : forall t, formal F t -> formal Full t)
    (store : symbolic_store Γ Full []) :
  NoDup (pvar_list_indices variables) ->
  forall t (formal_variable : formal F t),
    lookup_store (install_procedure_formals variables embed store) t
      (lookup_pvar_list variables formal_variable) =
    RefFormal (embed t formal_variable).
Proof.
  revert embed store. induction variables;
    intros embed store Hnodup value_type formal_variable;
    dependent destruction formal_variable;
    cbn [pvar_list_indices install_procedure_formals] in *.
  - inversion Hnodup as [|? ? Hfresh Htail].
    rewrite lookup_pvar_list_here.
    rewrite lookup_install_procedure_formals_absent.
    + apply lookup_set_store_reference_same.
    + exact Hfresh.
  - inversion Hnodup as [|? ? Hfresh Htail].
    rewrite lookup_pvar_list_there.
    apply IHvariables. exact Htail.
Qed.

Lemma lookup_canonical_entry_store_present {Γ F} identity
    (variables : pvar_list Γ F) :
  NoDup (pvar_list_indices variables) ->
  forall t (formal_variable : formal F t),
    lookup_store (canonical_entry_store_from identity variables) t
      (lookup_pvar_list variables formal_variable) =
    RefFormal formal_variable.
Proof.
  intros Hnodup t formal_variable. unfold canonical_entry_store_from.
  apply lookup_install_procedure_formals_present. exact Hnodup.
Qed.

Lemma lookup_canonical_entry_store_absent {Γ F} identity
    (variables : pvar_list Γ F) t (variable : pvar Γ t) :
  ~ In (member_index variable) (pvar_list_indices variables) ->
  lookup_store (canonical_entry_store_from identity variables) t variable =
    RefAtom (ProcedureEntryAtom identity (member_index variable)).
Proof.
  intros Hnot. unfold canonical_entry_store_from.
  rewrite lookup_install_procedure_formals_absent by exact Hnot.
  rewrite lookup_procedure_local_entry_store_from. f_equal.
Qed.

Lemma lookup_canonical_procedure_entry_store_singleton
    {Γ t identity} (variable : pvar Γ t) :
  lookup_store
      (canonical_entry_store_from identity (PVCons variable PVNil)) t variable =
    RefFormal MHere.
Proof.
  unfold canonical_entry_store_from.
  change (lookup_store
    (set_store_reference
      (procedure_local_entry_store_from identity 0) variable
      (RefFormal (@MHere [] t))) t variable =
        RefFormal (@MHere [] t)).
  apply lookup_set_store_reference_same.
Qed.

Lemma lookup_weaken_store {Γ F Δ u t}
    (store : symbolic_store Γ F Δ) (variable : pvar Γ t) :
  lookup_store (weaken_store (u := u) store) t variable =
    weaken_ref (lookup_store store t variable).
Proof.
  induction store; dependent destruction variable; cbn [weaken_store].
  - rewrite !lookup_store_here. reflexivity.
  - rewrite !lookup_store_there. apply IHstore.
Qed.

Lemma lookup_rename_bound_store {Γ F Δ Δ' t}
    (renaming : bound_renaming Δ Δ') (store : symbolic_store Γ F Δ)
    (variable : pvar Γ t) :
  lookup_store (rename_bound_store renaming store) t variable =
    rename_bound_ref renaming (lookup_store store t variable).
Proof.
  induction store; dependent destruction variable; cbn [rename_bound_store].
  - rewrite !lookup_store_here. reflexivity.
  - rewrite !lookup_store_there. exact (IHstore _).
Qed.

Lemma symbolize_expr_rename_bound_store {Γ F Δ Δ' t}
    (renaming : bound_renaming Δ Δ') (store : symbolic_store Γ F Δ)
    (expression : pexpr Γ t) :
  symbolize_expr (rename_bound_store renaming store) expression =
    rename_bound_expr renaming (symbolize_expr store expression).
Proof.
  induction expression; cbn; f_equal; auto using lookup_rename_bound_store.
Qed.

Lemma symbolize_expr_list_rename_bound_store {Γ F Δ Δ' ts}
    (renaming : bound_renaming Δ Δ') (store : symbolic_store Γ F Δ)
    (expressions : pexpr_list Γ ts) :
  symbolize_expr_list (rename_bound_store renaming store) expressions =
    rename_bound_expr_list renaming (symbolize_expr_list store expressions).
Proof.
  induction expressions; cbn; f_equal;
    auto using symbolize_expr_rename_bound_store.
Qed.

Lemma lookup_subst_bound_store {Γ F Δ Δ' t}
    (substitution : Resource.bound_ref_subst F Δ Δ')
    (store : symbolic_store Γ F Δ) (variable : pvar Γ t) :
  lookup_store (Resource.subst_bound_store substitution store) t variable =
    Resource.subst_bound_value_ref substitution
      (lookup_store store t variable).
Proof.
  induction store; dependent destruction variable;
    cbn [Resource.subst_bound_store].
  - rewrite !lookup_store_here. reflexivity.
  - rewrite !lookup_store_there. exact (IHstore _).
Qed.

Lemma symbolize_expr_subst_bound_store {Γ F Δ Δ' t}
    (substitution : Resource.bound_ref_subst F Δ Δ')
    (store : symbolic_store Γ F Δ) (expression : pexpr Γ t) :
  symbolize_expr (Resource.subst_bound_store substitution store) expression =
    subst_bound_expr (Resource.bound_subst_of_refs substitution)
      (symbolize_expr store expression).
Proof.
  induction expression; cbn.
  - rewrite lookup_subst_bound_store.
    destruct (lookup_store store t variable); reflexivity.
  - reflexivity.
  - rewrite IHexpression. reflexivity.
  - rewrite IHexpression1. rewrite IHexpression2. reflexivity.
Qed.

Lemma symbolize_expr_list_subst_bound_store {Γ F Δ Δ' ts}
    (substitution : Resource.bound_ref_subst F Δ Δ')
    (store : symbolic_store Γ F Δ)
    (expressions : pexpr_list Γ ts) :
  symbolize_expr_list (Resource.subst_bound_store substitution store)
      expressions =
    subst_bound_expr_list (Resource.bound_subst_of_refs substitution)
      (symbolize_expr_list store expressions).
Proof.
  induction expressions; cbn; [reflexivity|].
  rewrite symbolize_expr_subst_bound_store. rewrite IHexpressions. reflexivity.
Qed.

Lemma rename_bound_store_lift_weaken {Γ F Δ Δ' t}
    (renaming : bound_renaming Δ Δ') (store : symbolic_store Γ F Δ) :
  rename_bound_store (lift_bound_renaming (u := t) renaming)
    (weaken_store (u := t) store) =
  weaken_store (u := t) (rename_bound_store renaming store).
Proof.
  induction store; cbn [rename_bound_store weaken_store].
  - reflexivity.
  - f_equal; auto.
    dependent destruction v; cbn [rename_bound_ref weaken_ref];
      try reflexivity.
  unfold lift_bound_renaming. rewrite view_member_there. reflexivity.
Qed.

Lemma update_store_with_bound_here {F Δ head_type tail_context}
    (head : value_ref F Δ head_type)
    (tail : symbolic_store tail_context F Δ) :
  update_store_with_bound (StoreCons head tail) MHere =
    StoreCons (RefBound MHere) (weaken_store tail).
Proof.
  unfold update_store_with_bound, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl). reflexivity.
Qed.

Lemma update_store_with_bound_there {F Δ head_type tail_context t}
    (head : value_ref F Δ head_type)
    (tail : symbolic_store tail_context F Δ)
    (target : pvar tail_context t) :
  update_store_with_bound (StoreCons head tail) (MThere target) =
    StoreCons (weaken_ref head) (update_store_with_bound tail target).
Proof.
  unfold update_store_with_bound, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl). reflexivity.
Qed.

(** Updating one program slot weakens every other symbolic reference and
    leaves its denotation unchanged under the extended binder environment. *)
Lemma lookup_update_store_with_bound_other {Γ F Δ target_type value_type}
    (store : symbolic_store Γ F Δ) (target : pvar Γ target_type)
    (variable : pvar Γ value_type) :
  member_index variable <> member_index target ->
  lookup_store (update_store_with_bound store target) value_type variable =
    weaken_ref (lookup_store store value_type variable).
Proof.
  revert target variable.
  induction store; intros target variable Hneq;
    dependent destruction target; dependent destruction variable.
  - exfalso. apply Hneq. reflexivity.
  - rewrite update_store_with_bound_here.
    rewrite (lookup_store_there (RefBound MHere) (weaken_store store)
      variable).
    rewrite (lookup_store_there v store variable).
    exact (@lookup_weaken_store Γ F Δ t t0 store variable).
  - rewrite update_store_with_bound_there.
    rewrite lookup_store_here. rewrite lookup_store_here. reflexivity.
  - rewrite update_store_with_bound_there.
    rewrite !lookup_store_there. apply IHstore.
    cbn [member_index] in Hneq. lia.
Qed.

Lemma rename_bound_store_update_store_with_bound {Γ F Δ Δ' t}
    (renaming : bound_renaming Δ Δ') (store : symbolic_store Γ F Δ)
    (target : pvar Γ t) :
  rename_bound_store (lift_bound_renaming (u := t) renaming)
    (update_store_with_bound store target) =
  update_store_with_bound (rename_bound_store renaming store) target.
Proof.
  induction store; dependent destruction target; cbn [rename_bound_store].
  - rewrite !update_store_with_bound_here. cbn [rename_bound_store].
    f_equal.
    + cbn [rename_bound_ref]. unfold lift_bound_renaming.
      rewrite view_member_here. reflexivity.
    + apply rename_bound_store_lift_weaken.
  - rewrite !update_store_with_bound_there. cbn [rename_bound_store].
    f_equal; auto.
    dependent destruction v; cbn [rename_bound_ref weaken_ref];
      try reflexivity.
    unfold lift_bound_renaming. rewrite view_member_there. reflexivity.
Qed.

End Make.
End TypedIR.

Module TypedIRExamples.

Module UnitRA := TypedCoreExamples.UnitRA.

Module TinyLogic <: TypedAssertion.LOGIC_SIGNATURE.
  Definition field_type (_ : TypedCore.field_id) := TypedCore.TInt.
  Definition predicate_args (_ : TypedCore.pred_id) : TypedCore.context := [].
  Definition invariant_args (_ : TypedCore.inv_id) := [TypedCore.TRef].
  Definition procedure_args (_ : TypedCore.proc_id) : TypedCore.context :=
    [TypedCore.TRef].
  Definition procedure_return (_ : TypedCore.proc_id) : TypedCore.typ :=
    TypedCore.TUnit.
End TinyLogic.

Module IR := TypedIR.Make UnitRA TinyLogic.
Import TypedCore IR.

Definition variables : TypedIR.named_context [TInt; TRef] :=
  TypedIR.NCCons "v" TInt (TypedIR.NCCons "c" TRef TypedIR.NCNil).

Definition environment : TypedIR.elaboration_environment :=
  TypedIR.ElaborationEnvironment
    [TypedIR.FieldDecl "value" 1%positive]
    []
    [TypedIR.InvariantSignature "counter" 1%positive]
    [].

Definition source_body : source_stmt :=
  SSSeq
    (SSUnfold "counter" [SEVar "c"])
    (SSSeq
      (SSAssign "v" (SEField (SEVar "c") "value"))
      (SSAtomic
        (SSFieldWrite (SEVar "c") "value"
          (SEBinOp SBAdd (SEVar "v") (SEVal (SVInt 1)))))).

Example source_body_elaborates :
  exists result, elaborate_stmt environment variables source_body =
    inr result.
Proof.
  eexists. reflexivity.
Qed.

Example ill_typed_assignment_is_rejected :
  elaborate_stmt environment variables
      (SSAssign "v" (SEVal (SVBool true))) =
    inl (EETypeMismatch TInt TBool).
Proof. reflexivity. Qed.

Example allocation_elaborates :
  exists result,
    elaborate_stmt environment variables
      (SSAlloc "c" [("value", SEVal (SVInt 0))]) = inr result.
Proof. eexists. reflexivity. Qed.

Example ghost_update_elaborates :
  exists result,
    elaborate_stmt environment variables
      (SSGhostUpdate (SEVar "c") "value"
        (SEVal (SVInt 0)) (SEVal (SVInt 1))) = inr result.
Proof. eexists. reflexivity. Qed.

End TypedIRExamples.
