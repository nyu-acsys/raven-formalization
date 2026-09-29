From Coq Require Import List String ZArith PArith Program.Equality
  ProofIrrelevance Lia.

From raven Require Import surface.syntax verification.expressions verification.assertions verification.resources.

Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope list_scope.

(** Typed statements and procedures. *)
Module IR.

Import Core.

(** Source names decorate a declaration context but do not occur in the
    resulting references.  The head is the most recently declared local. *)
Inductive named_context : decl_context -> Type :=
| NCNil : named_context []
| NCCons D (name : source_name) (d : decl) :
    named_context D -> named_context (d :: D).

Arguments NCCons {_} _ _ _.

Fixpoint lookup_named {D} (declarations : named_context D)
    (name : source_name) : option { t : typ & pvar D t } :=
  match declarations with
  | NCNil => None
  | NCCons declared_name declared tail =>
      if String.eqb name declared_name then
        Some (existT (decl_type declared) (LHere eq_refl))
      else
        match lookup_named tail name with
        | Some (existT t variable) => Some (existT t (LThere variable))
        | None => None
        end
  end.

(** Source names for a type context (formals and logical binders). *)
Inductive named_types : context -> Type :=
| NTNil : named_types []
| NTCons Γ (name : source_name) (t : typ) :
    named_types Γ -> named_types (t :: Γ).

Arguments NTCons {_} _ _ _.

Fixpoint lookup_named_type {Γ} (declarations : named_types Γ)
    (name : source_name) : option { t : typ & member Γ t } :=
  match declarations with
  | NTNil => None
  | NTCons declared_name declared_type tail =>
      if String.eqb name declared_name then
        Some (existT declared_type MHere)
      else
        match lookup_named_type tail name with
        | Some (existT t variable) => Some (existT t (MThere variable))
        | None => None
        end
  end.

Fixpoint named_types_names {Γ} (declarations : named_types Γ) :
    list source_name :=
  match declarations with
  | NTNil => []
  | NTCons name _ tail => name :: named_types_names tail
  end.

(** A type-preserving embedding of a formal context into the locals.
    Procedure entries use this to say which locals receive the formal
    arguments. *)
Inductive pvar_list (D : decl_context) : context -> Type :=
| PVNil : pvar_list D []
| PVCons F t : pvar D t -> pvar_list D F -> pvar_list D (t :: F).

Arguments PVNil {_}.
Arguments PVCons {_ _ _} _ _.

Fixpoint pvar_list_indices {D F} (variables : pvar_list D F) : list nat :=
  match variables with
  | PVNil => []
  | PVCons variable tail => lvar_index variable :: pvar_list_indices tail
  end.

Fixpoint lookup_pvar_list {D F t} (variables : pvar_list D F)
    (formal_variable : member F t) : pvar D t.
Proof.
  destruct variables as [|F head_type variable tail].
  - dependent destruction formal_variable.
  - dependent destruction formal_variable.
    + exact variable.
    + exact (@lookup_pvar_list D F t tail formal_variable).
Defined.

Lemma lookup_pvar_list_here {D F t} (variable : pvar D t)
    (tail : pvar_list D F) :
  lookup_pvar_list (PVCons variable tail) MHere = variable.
Proof.
  unfold lookup_pvar_list, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl).
  reflexivity.
Qed.

Lemma lookup_pvar_list_there {D F head t} (variable : pvar D head)
    (tail : pvar_list D F) (formal_variable : formal F t) :
  lookup_pvar_list (PVCons variable tail) (MThere formal_variable) =
    lookup_pvar_list tail formal_variable.
Proof.
  unfold lookup_pvar_list, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl).
  reflexivity.
Qed.

Lemma pvar_list_index_member {D F t} (variables : pvar_list D F)
    (variable : pvar D t) :
  In (lvar_index variable) (pvar_list_indices variables) ->
  exists formal_variable : formal F t,
    lookup_pvar_list variables formal_variable = variable.
Proof.
  induction variables as [| F head_type program_variable tail IH]; simpl.
  - contradiction.
  - intros [Hhead | Htail].
    + assert (Hsigma : @existT typ (fun u => pvar D u) head_type program_variable =
          @existT typ (fun u => pvar D u) t variable).
      { apply lvar_index_sig_injective. exact Hhead. }
      dependent destruction Hsigma.
      exists MHere. exact (lookup_pvar_list_here variable tail).
    + destruct (IH Htail) as (formal_variable & Hlookup).
      exists (MThere formal_variable).
      transitivity (lookup_pvar_list tail formal_variable).
      * exact (lookup_pvar_list_there program_variable tail formal_variable).
      * exact Hlookup.
Qed.

Fixpoint named_context_names {D} (declarations : named_context D) :
    list source_name :=
  match declarations with
  | NCNil => []
  | NCCons name _ tail => name :: named_context_names tail
  end.

Lemma named_context_names_length {D} (declarations : named_context D) :
  List.length (named_context_names declarations) = List.length D.
Proof. induction declarations; simpl; congruence. Qed.

Module Resource := Resource.
Module Assertions := Assertion.
Module Core := Core.
Import Core Assertions.

Section WithSignature.
Context {RAs : RAValueConfig} {Logic : LogicSignature}.

(** Program expressions read the locals admitted by [keep]: runtime
    expressions ([keep_runtime]) are evaluated by the program, ghost
    expressions ([keep_all]) only by proof-only statements.  Logical
    expressions use [value_ref]; the symbolic Hoare rules connect the two
    through a typed [symbolic_store]. *)
Inductive pexpr (keep : decl -> bool) (D : decl_context) : typ -> Type :=
| PEVar t (variable : lvar keep D t) : pexpr keep D t
| PEVal t (value : tval t) : pexpr keep D t
| PEUnOp input output (op : unop input output) :
    pexpr keep D input -> pexpr keep D output
| PEBinOp left right output (op : binop left right output) :
    pexpr keep D left -> pexpr keep D right -> pexpr keep D output.

#[global] Arguments PEVar {_ _ _} & _.
#[global] Arguments PEVal {_ _ _} & _.
#[global] Arguments PEUnOp {_ _ _ _} & _ _.
#[global] Arguments PEBinOp {_ _ _ _ _} & _ _ _.

Notation rexpr := (pexpr keep_runtime).
Notation gexpr := (pexpr keep_all).

(** Evidence that a conditional guard may be evaluated before opening an
    invariant.  Guards are runtime expressions, so every guard is movable. *)
Inductive guard_mobility {D} (condition : rexpr D TBool) : Type :=
| GuardMovable : guard_mobility condition.

Definition current_guard_mobility {D} (condition : rexpr D TBool) :
    guard_mobility condition := GuardMovable condition.

Inductive pexpr_list (keep : decl -> bool) (D : decl_context) :
    context -> Type :=
| PENil : pexpr_list keep D []
| PECons t ts : pexpr keep D t -> pexpr_list keep D ts ->
    pexpr_list keep D (t :: ts).

#[global] Arguments PENil {_ _}.
#[global] Arguments PECons {_ _ _ _} & _ _.

Notation rexpr_list := (pexpr_list keep_runtime).
Notation gexpr_list := (pexpr_list keep_all).

Fixpoint pexpr_list_append {keep D left_types right_types}
    (left : pexpr_list keep D left_types)
    (right : pexpr_list keep D right_types) :
    pexpr_list keep D (left_types ++ right_types) :=
  match left with
  | PENil => right
  | PECons expression tail =>
      PECons expression (pexpr_list_append tail right)
  end.

(** Runtime expressions are readable by proof-only constructs. *)
Fixpoint pexpr_forget {keep D t} (expression : pexpr keep D t) : gexpr D t :=
  match expression with
  | PEVar variable => PEVar (lvar_forget variable)
  | PEVal value => PEVal value
  | PEUnOp op operand => PEUnOp op (pexpr_forget operand)
  | PEBinOp op operand1 operand2 =>
      PEBinOp op (pexpr_forget operand1) (pexpr_forget operand2)
  end.

Fixpoint pexpr_list_forget {keep D ts} (expressions : pexpr_list keep D ts) :
    gexpr_list D ts :=
  match expressions with
  | PENil => PENil
  | PECons expression tail =>
      PECons (pexpr_forget expression) (pexpr_list_forget tail)
  end.

(** Reading the same locals under one more declaration. *)
Fixpoint pexpr_shift {keep d D t} (expression : pexpr keep D t) :
    pexpr keep (d :: D) t :=
  match expression with
  | PEVar variable => PEVar (LThere variable)
  | PEVal value => PEVal value
  | PEUnOp op operand => PEUnOp op (pexpr_shift operand)
  | PEBinOp op operand1 operand2 =>
      PEBinOp op (pexpr_shift operand1) (pexpr_shift operand2)
  end.

Fixpoint pexpr_list_shift {keep d D ts} (expressions : pexpr_list keep D ts) :
    pexpr_list keep (d :: D) ts :=
  match expressions with
  | PENil => PENil
  | PECons expression tail =>
      PECons (pexpr_shift expression) (pexpr_list_shift tail)
  end.

Inductive field_init (D : decl_context) : Type :=
| FieldInit field : rexpr D (field_type field) -> field_init D.

#[global] Arguments FieldInit {_} & _ _.

Definition field_init_id {D} (initialization : field_init D) : field_id :=
  match initialization with FieldInit field _ => field end.

Definition field_init_is_ghost {D} (initialization : field_init D) : bool :=
  match initialization with
  | FieldInit field _ =>
      match field_type field with TRA _ => true | _ => false end
  end.

Inductive ghost_field_init (D : decl_context) : Type :=
| GhostFieldInit resource field
    (field_is_resource : field_type field = TRA resource)
    (value : rexpr D (TRA resource)).

#[global] Arguments GhostFieldInit {_} _ _ _ _.

Definition ghost_field_init_id {D} (initialization : ghost_field_init D) :
    field_id :=
  match initialization with GhostFieldInit _ field _ _ => field end.

Definition physical_field_initializers {D} (fields : list (field_init D)) :
    list (field_init D) := filter (fun field => negb (field_init_is_ghost field)) fields.

Fixpoint ghost_field_initializers {D} (fields : list (field_init D)) :
    list (ghost_field_init D) :=
  match fields with
  | [] => []
  | FieldInit field value :: fields' =>
      match field_type field as chunk_type
        return field_type field = chunk_type -> rexpr D chunk_type ->
          list (ghost_field_init D) with
      | TRA resource => fun Heq chunk =>
          GhostFieldInit resource field Heq chunk ::
            ghost_field_initializers fields'
      | _ => fun _ _ => ghost_field_initializers fields'
      end eq_refl value
  end.

Definition ghost_initializers_require_physical {D}
    (fields : list (field_init D)) : Prop :=
  ghost_field_initializers fields <> [] -> physical_field_initializers fields <> [].

Lemma physical_field_initializers_ids_nodup {D}
    (fields : list (field_init D)) :
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

(** Locals a runtime statement may write. *)
Notation write_target init := (lvar (keep_write init)).

Inductive call_target (D : decl_context) : typ -> Type :=
| CTDiscard t : call_target D t
| CTStore (init : bool) t (target : write_target init D t) : call_target D t.

#[global] Arguments CTDiscard {_ _}.
#[global] Arguments CTStore {_} _ {_} & _.

Inductive stmt (D : decl_context) : Type :=
| TDone
| TAssert (condition : gexpr D TBool)
| TAssign (init : bool) t (target : write_target init D t) (value : rexpr D t)
| TFieldRead (init : bool) (field : field_id)
    (target : write_target init D (field_type field)) (base : rexpr D TRef)
| TFieldWrite (field : field_id) (base : rexpr D TRef)
    (value : rexpr D (field_type field))
| TAlloc (init : bool) (target : write_target init D TRef)
    (fields : list (field_init D))
| TGhostUpdate (field : field_id) (base : gexpr D TRef)
    (old_value new_value : gexpr D (field_type field))
| TCall (procedure : proc_id)
    (arguments : rexpr_list D (procedure_args procedure))
    (target : call_target D (procedure_return procedure))
| TSpawn (procedure : proc_id)
    (arguments : rexpr_list D (procedure_args procedure))
| TUnfold (invariant : inv_id)
    (arguments : gexpr_list D (invariant_args invariant))
| TFold (invariant : inv_id)
    (arguments : gexpr_list D (invariant_args invariant))
| TPredicateUnfold (predicate : pred_id)
    (arguments : gexpr_list D (predicate_args predicate))
| TPredicateFold (predicate : pred_id)
    (arguments : gexpr_list D (predicate_args predicate))
| TInvAccess (invariant : inv_id)
    (arguments : gexpr_list D (invariant_args invariant))
    (body : stmt D)
| TIf (condition : rexpr D TBool)
    (then_branch else_branch : stmt D)
| TSeq (first second : stmt D)
| TAtomic (body : stmt D)
(** A ghost value scoped over [body], initialized once and never written. *)
| TGhostVal (name : source_name) t (initializer : gexpr D t)
    (body : stmt (ghost_val t :: D))
(** A proof-only conditional: its guard may read ghost locals, and its
    branches must be proof-only ([proof_onlyb]). *)
| TGhostIf (condition : gexpr D TBool) (then_branch else_branch : stmt D).

#[global] Arguments TDone {_}.
#[global] Arguments TAssert {_} & _.
#[global] Arguments TAssign {_} _ {_} & _ _.
#[global] Arguments TFieldRead {_} _ & _ _ _.
#[global] Arguments TFieldWrite {_} & _ _ _.
#[global] Arguments TAlloc {_} _ & _ _.
#[global] Arguments TGhostUpdate {_} & _ _ _ _.
#[global] Arguments TCall {_} & _ _ _.
#[global] Arguments TSpawn {_} & _ _.
#[global] Arguments TUnfold {_} & _ _.
#[global] Arguments TFold {_} & _ _.
#[global] Arguments TPredicateUnfold {_} & _ _.
#[global] Arguments TPredicateFold {_} & _ _.
#[global] Arguments TInvAccess {_} & _ _ _.
#[global] Arguments TIf {_} & _ _ _.
#[global] Arguments TSeq {_} & _ _.
#[global] Arguments TAtomic {_} & _.
#[global] Arguments TGhostVal {_} & _ _ _ _.
#[global] Arguments TGhostIf {_} & _ _ _.

(** Statements without runtime effect: they erase to the terminal
    statement. *)
Fixpoint proof_onlyb {D} (statement : stmt D) : bool :=
  match statement with
  | TDone | TAssert _ | TGhostUpdate _ _ _ _ | TUnfold _ _ | TFold _ _
  | TPredicateUnfold _ _ | TPredicateFold _ _ => true
  | TInvAccess _ _ body => proof_onlyb body
  | TGhostVal _ _ _ body => proof_onlyb body
  | TIf _ then_branch else_branch | TGhostIf _ then_branch else_branch
  | TSeq then_branch else_branch =>
      proof_onlyb then_branch && proof_onlyb else_branch
  | _ => false
  end.

(** Canonical procedure-entry stores.  Every frame slot starts as a fresh
    procedure-local symbolic symbol; installing the formal-variable embedding
    then replaces exactly the argument slots by their corresponding formal
    references. *)
Fixpoint procedure_local_entry_store_from {D F}
    (identity : proc_id) (slot : nat) : symbolic_store D F [] :=
  match D with
  | [] => StoreNil
  | d :: D' =>
      StoreCons (d := d) (RefSymbol (ProcedureEntrySymbol identity slot))
        (@procedure_local_entry_store_from D' F identity (S slot))
  end.

Fixpoint set_store_reference {D F Δ keep t} (variable : lvar keep D t) :
    symbolic_store D F Δ -> value_ref F Δ t -> symbolic_store D F Δ :=
  match variable in lvar _ D0 t0 return
    symbolic_store D0 F Δ -> value_ref F Δ t0 -> symbolic_store D0 F Δ
  with
  | LHere _ => fun store reference => StoreCons reference (store_tail store)
  | LThere variable' => fun store reference =>
      StoreCons (store_head store)
        (set_store_reference variable' (store_tail store) reference)
  end.

Fixpoint install_procedure_formals {D F Full}
    (variables : pvar_list D F)
    (embed : forall t, formal F t -> formal Full t)
    (store : symbolic_store D Full []) : symbolic_store D Full [] :=
  match variables in pvar_list _ F0
      return (forall t, formal F0 t -> formal Full t) ->
        symbolic_store D Full [] -> symbolic_store D Full [] with
  | PVNil => fun _ store => store
  | @PVCons _ tail t variable rest => fun embed store =>
      install_procedure_formals rest
        (fun u formal => embed u (MThere formal))
        (set_store_reference variable store (RefFormal (embed t MHere)))
  end embed store.

Definition canonical_entry_store_from {D F} (identity : proc_id)
    (formal_variables : pvar_list D F) : symbolic_store D F [] :=
  install_procedure_formals formal_variables (fun _ formal => formal)
    (procedure_local_entry_store_from identity 0).

Definition canonical_procedure_entry_store {D identity}
    (formal_variables : pvar_list D (procedure_args identity)) :
    symbolic_store D (procedure_args identity) [] :=
  canonical_entry_store_from identity formal_variables.

(** Indexed by the declared identity rather than by a free formal context:
    the formals and return type are read off [Logic].  The
    [procedure_identity] and [procedure_return_type] fields are the index
    and a projection of it respectively, and are kept below as definitions
    so that existing [procedure_identity _ _ procedure] uses continue to
    read. *)
Record typed_procedure (Γ : decl_context) (identity : proc_id) := TypedProcedure {
  procedure_variables : named_context Γ;
  procedure_formals : named_types (procedure_args identity);
  procedure_formal_variables : pvar_list Γ (procedure_args identity);
  procedure_return_variable : pvar Γ (procedure_return identity);
  (** Core assertions, not [assertion]: a procedure's contract must not
      mention the caller's stack, and with the resource separation that is
      a typing fact rather than the two [stack_free] side conditions
      [procedure_wf] used to carry.  Note the absent [Γ]. *)
  procedure_precondition :
    Resource.core_assertion (procedure_args identity) [];
  procedure_postcondition :
    Resource.core_assertion (procedure_args identity)
      (return_context (procedure_return identity));
  procedure_body : stmt Γ;
}.

#[global] Arguments TypedProcedure {_ _} _ _ _ _ _ _ _.

Definition procedure_entry_store (Γ : decl_context) (identity : proc_id)
    (procedure : typed_procedure Γ identity) :
    symbolic_store Γ (procedure_args identity) [] :=
  canonical_procedure_entry_store
    (procedure_formal_variables _ _ procedure).

Definition procedure_identity (Γ : decl_context) (identity : proc_id)
    (_ : typed_procedure Γ identity) : proc_id := identity.

Definition procedure_return_type (Γ : decl_context) (identity : proc_id)
    (_ : typed_procedure Γ identity) : typ := procedure_return identity.

(** [procedure_precondition_stack_free] and
    [procedure_postcondition_stack_free] are gone: the contract fields are
    [core_assertion]s, which cannot mention a stack at all. *)
Record procedure_wf {Γ F} (procedure : typed_procedure Γ F) : Prop := {
  procedure_variable_names_unique :
    NoDup (named_context_names (procedure_variables _ _ procedure));
  procedure_reserved_return_fresh :
    ~ List.In "#ret_val"
      (named_context_names (procedure_variables _ _ procedure));
  procedure_formal_slots_unique :
    NoDup (pvar_list_indices (procedure_formal_variables _ _ procedure));
  procedure_return_slot_local :
    ~ In (lvar_index (procedure_return_variable _ _ procedure))
        (pvar_list_indices (procedure_formal_variables _ _ procedure));
  procedure_precondition_entry_free :
    Resource.core_entry_free (procedure_precondition _ _ procedure);
  procedure_postcondition_entry_free :
    Resource.core_entry_free (procedure_postcondition _ _ procedure);
  procedure_locals_runtime : forallb keep_runtime Γ = true;
}.

(** A procedure table must be heterogeneous: procedures may have different
    stack contexts, formal contexts, and return types.  The existential
    package below keeps those indices available when an entry is selected,
    while allowing the table itself to be an ordinary finite list. *)
Definition packed_typed_procedure :=
  { Γ : decl_context & { identity : proc_id & typed_procedure Γ identity } }.

Definition pack_typed_procedure {Γ identity}
    (procedure : typed_procedure Γ identity) : packed_typed_procedure :=
  @existT decl_context (fun variables =>
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
    (procedure_args (packed_procedure_id procedure))
    (procedure_return (packed_procedure_id procedure)).

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
    option { Γ : decl_context & typed_procedure Γ identity } :=
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

Lemma lookup_packed_procedure_of_member procedures procedure :
  NoDup (map packed_procedure_id procedures) ->
  List.In procedure procedures ->
  lookup_packed_procedure (packed_procedure_id procedure) procedures =
    Some procedure.
Proof.
  intros Hnodup Hin.
  induction procedures as [|head tail IH]; [contradiction|].
  inversion Hnodup as [|? ? Hfresh Htail]; subst.
  destruct Hin as [-> | Hin].
  - simpl. rewrite Pos.eqb_refl. reflexivity.
  - simpl. destruct (Pos.eqb (packed_procedure_id procedure)
      (packed_procedure_id head)) eqn:Heq.
    + apply Pos.eqb_eq in Heq. exfalso. apply Hfresh.
      rewrite <- Heq. apply in_map. exact Hin.
    + exact (IH Htail Hin).
Qed.

Lemma lookup_typed_procedure_of_member environment procedure :
  List.In procedure (procedure_entries environment) ->
  lookup_typed_procedure environment (packed_procedure_id procedure) =
    Some procedure.
Proof.
  apply lookup_packed_procedure_of_member.
  exact (procedure_ids_unique environment).
Qed.

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

(* ------------------------------------------------------------------ *)
(** ** Program syntax against a symbolic store

    These mediate between program expressions and the logical expression
    language, so they belong with the store rather than with any one Hoare
    calculus. *)

Fixpoint symbolize_expr {D F Δ keep t} (store : symbolic_store D F Δ)
    (expression : pexpr keep D t) : expr F Δ t :=
  match expression with
  | PEVar variable => ERef (lookup_store store _ variable)
  | PEVal value => EVal value
  | PEUnOp op operand => EUnOp op (symbolize_expr store operand)
  | PEBinOp op operand1 operand2 =>
      EBinOp op (symbolize_expr store operand1) (symbolize_expr store operand2)
  end.

Fixpoint symbolize_expr_list {D F Δ keep ts}
    (store : symbolic_store D F Δ) (expressions : pexpr_list keep D ts) :
    expr_list F Δ ts :=
  match expressions with
  | PENil => ExprNil
  | PECons expression expressions' =>
      ExprCons (symbolize_expr store expression)
        (symbolize_expr_list store expressions')
  end.

Lemma symbolize_expr_list_append {D F Δ keep left_types right_types}
    (store : symbolic_store D F Δ)
    (left : pexpr_list keep D left_types)
    (right : pexpr_list keep D right_types) :
  symbolize_expr_list store (pexpr_list_append left right) =
    Assertions.expr_list_append (symbolize_expr_list store left)
      (symbolize_expr_list store right).
Proof.
  induction left; cbn [pexpr_list_append symbolize_expr_list
    Assertions.expr_list_append]; [reflexivity|].
  f_equal. exact IHleft.
Qed.

Lemma lookup_store_forget {D F Δ keep t} (store : symbolic_store D F Δ)
    (variable : lvar keep D t) :
  lookup_store store t (lvar_forget variable) = lookup_store store t variable.
Proof.
  unfold lookup_store. revert store.
  induction variable; intros store; simpl; auto.
Qed.

Lemma symbolize_expr_forget {D F Δ keep t} (store : symbolic_store D F Δ)
    (expression : pexpr keep D t) :
  symbolize_expr store (pexpr_forget expression) =
    symbolize_expr store expression.
Proof.
  induction expression; simpl; f_equal; auto using lookup_store_forget.
Qed.

Lemma symbolize_expr_list_forget {D F Δ keep ts}
    (store : symbolic_store D F Δ) (expressions : pexpr_list keep D ts) :
  symbolize_expr_list store (pexpr_list_forget expressions) =
    symbolize_expr_list store expressions.
Proof.
  induction expressions; simpl; f_equal; auto using symbolize_expr_forget.
Qed.

Lemma symbolize_expr_shift {d D F Δ keep t}
    (store : symbolic_store (d :: D) F Δ) (expression : pexpr keep D t) :
  symbolize_expr store (pexpr_shift expression) =
    symbolize_expr (store_tail store) expression.
Proof. induction expression; simpl; congruence. Qed.

Lemma symbolize_expr_list_shift {d D F Δ keep ts}
    (store : symbolic_store (d :: D) F Δ) (expressions : pexpr_list keep D ts) :
  symbolize_expr_list store (pexpr_list_shift expressions) =
    symbolize_expr_list (store_tail store) expressions.
Proof.
  induction expressions; simpl; f_equal; auto using symbolize_expr_shift.
Qed.

(** Updating a typed symbolic store is structural: the selected slot receives
    bound variable zero and every other slot is weakened across that binder. *)
Fixpoint update_store_with_bound {D F Δ keep t} (store : store_data F Δ D)
    (target : lvar keep D t) : store_data F (t :: Δ) D :=
  match target in lvar _ D0 t0 return
    store_data F Δ D0 -> store_data F (t0 :: Δ) D0
  with
  | LHere _ => fun store =>
      StoreCons (RefBound MHere) (weaken_store (store_tail store))
  | LThere target' => fun store =>
      StoreCons (weaken_ref (store_head store))
        (update_store_with_bound (store_tail store) target')
  end store.

Lemma lookup_store_here {F Δ keep d D}
    (head : value_ref F Δ (decl_type d))
    (tail : symbolic_store D F Δ) (Hkeep : keep d = true) :
  lookup_store (StoreCons head tail) _ (LHere Hkeep) = head.
Proof. reflexivity. Qed.

Lemma lookup_store_there {F Δ keep d D t}
    (head : value_ref F Δ (decl_type d))
    (tail : symbolic_store D F Δ) (variable : lvar keep D t) :
  lookup_store (StoreCons head tail) _ (LThere variable) =
    lookup_store tail _ variable.
Proof. reflexivity. Qed.

Lemma lookup_set_store_reference_same {D F Δ keep keep' t}
    (store : symbolic_store D F Δ) (target : lvar keep D t)
    (variable : lvar keep' D t) (reference : value_ref F Δ t) :
  lvar_index target = lvar_index variable ->
  lookup_store (set_store_reference target store reference) t variable =
    reference.
Proof.
  revert store variable. induction target as [d D Hkeep | d D t target IH];
    intros store variable Hindex; dependent destruction variable;
    cbn [lvar_index] in Hindex; try discriminate; simpl.
  - reflexivity.
  - apply IH. congruence.
Qed.

Lemma lookup_set_store_reference_other {D F Δ keep keep' t u}
    (store : symbolic_store D F Δ) (target : lvar keep D t)
    (reference : value_ref F Δ t) (variable : lvar keep' D u) :
  lvar_index target <> lvar_index variable ->
  lookup_store (set_store_reference target store reference) u variable =
    lookup_store store u variable.
Proof.
  revert store variable. induction target as [d D Hkeep | d D t target IH];
    intros store variable Hne; dependent destruction variable;
    cbn [lvar_index] in Hne; simpl.
  - exfalso. apply Hne. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IH. congruence.
Qed.

Lemma lookup_procedure_local_entry_store_from {D F keep} identity slot t
    (variable : lvar keep D t) :
  lookup_store (@procedure_local_entry_store_from D F identity slot)
      t variable =
    RefSymbol (ProcedureEntrySymbol identity (slot + lvar_index variable)).
Proof.
  revert slot. induction variable; intros slot; simpl.
  - replace (slot + 0)%nat with slot by lia. reflexivity.
  - unfold lookup_store in IHvariable |- *. simpl. rewrite IHvariable.
    replace (slot + S (lvar_index variable))%nat with
      (S slot + lvar_index variable)%nat by lia. reflexivity.
Qed.

Lemma lookup_install_procedure_formals_absent {D F Full keep}
    (variables : pvar_list D F)
    (embed : forall t, formal F t -> formal Full t)
    (store : symbolic_store D Full []) t (variable : lvar keep D t) :
  ~ In (lvar_index variable) (pvar_list_indices variables) ->
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

Lemma lookup_install_procedure_formals_present {D F Full}
    (variables : pvar_list D F)
    (embed : forall t, formal F t -> formal Full t)
    (store : symbolic_store D Full []) :
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
    + apply lookup_set_store_reference_same. reflexivity.
    + exact Hfresh.
  - inversion Hnodup as [|? ? Hfresh Htail].
    rewrite lookup_pvar_list_there.
    apply IHvariables. exact Htail.
Qed.

Lemma lookup_canonical_entry_store_present {D F} identity
    (variables : pvar_list D F) :
  NoDup (pvar_list_indices variables) ->
  forall t (formal_variable : formal F t),
    lookup_store (canonical_entry_store_from identity variables) t
      (lookup_pvar_list variables formal_variable) =
    RefFormal formal_variable.
Proof.
  intros Hnodup t formal_variable. unfold canonical_entry_store_from.
  apply lookup_install_procedure_formals_present. exact Hnodup.
Qed.

Lemma lookup_canonical_entry_store_absent {D F keep} identity
    (variables : pvar_list D F) t (variable : lvar keep D t) :
  ~ In (lvar_index variable) (pvar_list_indices variables) ->
  lookup_store (canonical_entry_store_from identity variables) t variable =
    RefSymbol (ProcedureEntrySymbol identity (lvar_index variable)).
Proof.
  intros Hnot. unfold canonical_entry_store_from.
  rewrite lookup_install_procedure_formals_absent by exact Hnot.
  rewrite lookup_procedure_local_entry_store_from. f_equal.
Qed.

Lemma lookup_canonical_procedure_entry_store_singleton
    {D t identity} (variable : pvar D t) :
  lookup_store
      (canonical_entry_store_from identity (PVCons variable PVNil)) t variable =
    RefFormal MHere.
Proof.
  unfold canonical_entry_store_from.
  change (lookup_store
    (set_store_reference variable
      (procedure_local_entry_store_from identity 0)
      (RefFormal (@MHere [] t))) t variable =
        RefFormal (@MHere [] t)).
  apply lookup_set_store_reference_same. reflexivity.
Qed.

Lemma lookup_weaken_store {D F Δ u keep t}
    (store : symbolic_store D F Δ) (variable : lvar keep D t) :
  lookup_store (weaken_store (u := u) store) t variable =
    weaken_ref (lookup_store store t variable).
Proof.
  unfold lookup_store. revert store.
  induction variable; intros store; dependent destruction store;
    simpl; auto.
Qed.

Lemma lookup_rename_bound_store {D F Δ Δ' keep t}
    (renaming : bound_renaming Δ Δ') (store : symbolic_store D F Δ)
    (variable : lvar keep D t) :
  lookup_store (rename_bound_store renaming store) t variable =
    rename_bound_ref renaming (lookup_store store t variable).
Proof.
  unfold lookup_store. revert store.
  induction variable; intros store; dependent destruction store;
    simpl; auto.
Qed.

Lemma symbolize_expr_rename_bound_store {D F Δ Δ' keep t}
    (renaming : bound_renaming Δ Δ') (store : symbolic_store D F Δ)
    (expression : pexpr keep D t) :
  symbolize_expr (rename_bound_store renaming store) expression =
    rename_bound_expr renaming (symbolize_expr store expression).
Proof.
  induction expression; cbn; f_equal; auto using lookup_rename_bound_store.
Qed.

Lemma symbolize_expr_list_rename_bound_store {D F Δ Δ' keep ts}
    (renaming : bound_renaming Δ Δ') (store : symbolic_store D F Δ)
    (expressions : pexpr_list keep D ts) :
  symbolize_expr_list (rename_bound_store renaming store) expressions =
    rename_bound_expr_list renaming (symbolize_expr_list store expressions).
Proof.
  induction expressions; cbn; f_equal;
    auto using symbolize_expr_rename_bound_store.
Qed.

Lemma lookup_subst_bound_store {D F Δ Δ' keep t}
    (substitution : Resource.bound_ref_subst F Δ Δ')
    (store : symbolic_store D F Δ) (variable : lvar keep D t) :
  lookup_store (Resource.subst_bound_store substitution store) t variable =
    Resource.subst_bound_value_ref substitution
      (lookup_store store t variable).
Proof.
  unfold lookup_store. revert store.
  induction variable; intros store; dependent destruction store;
    simpl; auto.
Qed.

Lemma symbolize_expr_subst_bound_store {D F Δ Δ' keep t}
    (substitution : Resource.bound_ref_subst F Δ Δ')
    (store : symbolic_store D F Δ) (expression : pexpr keep D t) :
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

Lemma symbolize_expr_list_subst_bound_store {D F Δ Δ' keep ts}
    (substitution : Resource.bound_ref_subst F Δ Δ')
    (store : symbolic_store D F Δ)
    (expressions : pexpr_list keep D ts) :
  symbolize_expr_list (Resource.subst_bound_store substitution store)
      expressions =
    subst_bound_expr_list (Resource.bound_subst_of_refs substitution)
      (symbolize_expr_list store expressions).
Proof.
  induction expressions; cbn; [reflexivity|].
  rewrite symbolize_expr_subst_bound_store. rewrite IHexpressions. reflexivity.
Qed.

Lemma rename_bound_store_lift_weaken {D F Δ Δ' t}
    (renaming : bound_renaming Δ Δ') (store : symbolic_store D F Δ) :
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

Lemma update_store_with_bound_here {F Δ keep d D}
    (head : value_ref F Δ (decl_type d))
    (tail : symbolic_store D F Δ) (Hkeep : keep d = true) :
  update_store_with_bound (StoreCons head tail) (LHere Hkeep) =
    StoreCons (RefBound MHere) (weaken_store tail).
Proof. reflexivity. Qed.

Lemma update_store_with_bound_there {F Δ keep d D t}
    (head : value_ref F Δ (decl_type d))
    (tail : symbolic_store D F Δ) (target : lvar keep D t) :
  update_store_with_bound (StoreCons head tail) (LThere target) =
    StoreCons (weaken_ref head) (update_store_with_bound tail target).
Proof. reflexivity. Qed.

(** Updating one program slot weakens every other symbolic reference and
    leaves its denotation unchanged under the extended binder environment. *)
Lemma lookup_update_store_with_bound_other {D F Δ keep keep' target_type
    value_type}
    (store : symbolic_store D F Δ) (target : lvar keep D target_type)
    (variable : lvar keep' D value_type) :
  lvar_index variable <> lvar_index target ->
  lookup_store (update_store_with_bound store target) value_type variable =
    weaken_ref (lookup_store store value_type variable).
Proof.
  revert store variable.
  induction target as [d D Hkeep | d D t target IH];
    intros store variable Hneq; dependent destruction store;
    dependent destruction variable; cbn [lvar_index] in Hneq.
  - exfalso. apply Hneq. reflexivity.
  - exact (lookup_weaken_store store variable).
  - reflexivity.
  - apply IH. congruence.
Qed.

Lemma rename_bound_store_update_store_with_bound {D F Δ Δ' keep t}
    (renaming : bound_renaming Δ Δ') (store : symbolic_store D F Δ)
    (target : lvar keep D t) :
  rename_bound_store (lift_bound_renaming (u := t) renaming)
    (update_store_with_bound store target) =
  update_store_with_bound (rename_bound_store renaming store) target.
Proof.
  revert store. induction target as [d D Hkeep | d D t target IH];
    intros store; dependent destruction store; simpl.
  - f_equal.
    + cbn [rename_bound_ref]. unfold lift_bound_renaming.
      rewrite view_member_here. reflexivity.
    + apply rename_bound_store_lift_weaken.
  - f_equal; auto.
    dependent destruction v; cbn [rename_bound_ref weaken_ref];
      try reflexivity.
    unfold lift_bound_renaming. rewrite view_member_there. reflexivity.
Qed.

End WithSignature.

Notation rexpr := (pexpr keep_runtime).
Notation gexpr := (pexpr keep_all).
Notation rexpr_list := (pexpr_list keep_runtime).
Notation gexpr_list := (pexpr_list keep_all).
Notation write_target init := (lvar (keep_write init)).
End IR.
