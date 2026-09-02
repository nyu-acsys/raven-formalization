From Coq Require Import List String ZArith PArith Program.Equality Lia.

From raven_iris.rich_raven_lang Require Import
  surface_syntax typed_core typed_assertion.

Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope list_scope.

(** Typed statements, procedures, and the first executable elaboration slice.
    This module remains parallel to [rrl_lang] until the replacement logic
    reaches adequacy. *)
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

Record procedure_signature := ProcedureSignature {
  signature_source_name : source_name;
  signature_identity : proc_id;
  signature_arguments : context;
  signature_return : typ;
}.

Record invariant_signature := InvariantSignature {
  invariant_source_name : source_name;
  invariant_identity : inv_id;
  invariant_arguments : context;
}.

Record predicate_signature := PredicateSignature {
  predicate_source_name : source_name;
  predicate_identity : pred_id;
  predicate_arguments : context;
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
Module Assertions := TypedAssertion.Make RAs Logic.
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

Inductive pexpr_list (Γ : context) : context -> Type :=
| PENil : pexpr_list Γ []
| PECons t ts : pexpr Γ t -> pexpr_list Γ ts -> pexpr_list Γ (t :: ts).

Arguments PENil {_}.
Arguments PECons {_ _ _} _ _.

Inductive field_init (Γ : context) : Type :=
| FieldInit field : pexpr Γ (Logic.field_type field) -> field_init Γ.

Arguments FieldInit {_} _ _.

Definition field_init_id {Γ} (initialization : field_init Γ) : field_id :=
  match initialization with FieldInit field _ => field end.

Inductive result_kind :=
| RKAssignment
| RKFieldRead
| RKAllocation
| RKCall.

Record result_origin (t : typ) := ResultOrigin {
  result_node : node_id;
  result_origin_kind : result_kind;
  result_symbol : atom t;
}.

Arguments ResultOrigin {_} _ _ _.

Definition canonical_result {t} (node : node_id) (kind : result_kind) :
    result_origin t := ResultOrigin node kind (Atom node).

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
| TSkip (node : node_id)
| TAssert (node : node_id) (condition : pexpr Γ TBool)
| TAssign t (node : node_id) (target : pvar Γ t) (value : pexpr Γ t)
| TFieldRead (node : node_id) (field : field_id)
    (target : pvar Γ (Logic.field_type field)) (base : pexpr Γ TRef)
| TFieldWrite (node : node_id) (field : field_id) (base : pexpr Γ TRef)
    (value : pexpr Γ (Logic.field_type field))
| TAlloc (node : node_id) (target : pvar Γ TRef)
    (fields : list (field_init Γ))
| TGhostUpdate (node : node_id) (field : field_id) (base : pexpr Γ TRef)
    (old_value new_value : pexpr Γ (Logic.field_type field))
| TCall args return_type (node : node_id) (procedure : proc_id)
    (arguments : pexpr_list Γ args) (target : call_target Γ return_type)
| TSpawn args (node : node_id) (procedure : proc_id)
    (arguments : pexpr_list Γ args)
| TUnfold (node : node_id) (invariant : inv_id)
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
| TFold (node : node_id) (invariant : inv_id)
    (arguments : pexpr_list Γ (Logic.invariant_args invariant))
| TPredicateUnfold (node : node_id) (predicate : pred_id)
    (arguments : pexpr_list Γ (Logic.predicate_args predicate))
| TPredicateFold (node : node_id) (predicate : pred_id)
    (arguments : pexpr_list Γ (Logic.predicate_args predicate))
| TIf (node : node_id) (condition : pexpr Γ TBool)
    (then_branch else_branch : stmt Γ)
| TSeq (node : node_id) (first second : stmt Γ)
| TAtomic (node : node_id) (body : stmt Γ).

Arguments TSkip {_} _.
Arguments TAssert {_} _ _.
Arguments TAssign {_ _} _ _ _.
Arguments TFieldRead {_} _ _ _ _.
Arguments TFieldWrite {_} _ _ _ _.
Arguments TAlloc {_} _ _ _.
Arguments TGhostUpdate {_} _ _ _ _ _.
Arguments TCall {_ _ _} _ _ _ _.
Arguments TSpawn {_ _} _ _ _.
Arguments TUnfold {_} _ _ _.
Arguments TFold {_} _ _ _.
Arguments TPredicateUnfold {_} _ _ _.
Arguments TPredicateFold {_} _ _ _.
Arguments TIf {_} _ _ _ _.
Arguments TSeq {_} _ _ _.
Arguments TAtomic {_} _ _.

Fixpoint stmt_nodes {Γ} (statement : stmt Γ) : list node_id :=
  match statement with
  | TSkip node | TAssert node _ | TAssign node _ _
  | TFieldRead node _ _ _ | TFieldWrite node _ _ _
  | TAlloc node _ _ | TGhostUpdate node _ _ _ _
  | TCall node _ _ _ | TSpawn node _ _
  | TUnfold node _ _ | TFold node _ _
  | TPredicateUnfold node _ _ | TPredicateFold node _ _ => [node]
  | TIf node _ then_branch else_branch =>
      node :: stmt_nodes then_branch ++ stmt_nodes else_branch
  | TSeq node first second => node :: stmt_nodes first ++ stmt_nodes second
  | TAtomic node body => node :: stmt_nodes body
  end.

Fixpoint stmt_results {Γ} (statement : stmt Γ) : list positive :=
  match statement with
  | TAssign node _ _ | TFieldRead node _ _ _ | TAlloc node _ _ => [node]
  | TCall node _ _ (CTStore _) => [node]
  | TIf _ _ then_branch else_branch =>
      stmt_results then_branch ++ stmt_results else_branch
  | TSeq _ first second => stmt_results first ++ stmt_results second
  | TAtomic _ body => stmt_results body
  | _ => []
  end.

Record typed_procedure (Γ F : context) := TypedProcedure {
  procedure_identity : proc_id;
  procedure_variables : named_context Γ;
  procedure_formals : named_context F;
  procedure_return_type : typ;
  procedure_formal_variables : pvar_list Γ F;
  procedure_return_variable : pvar Γ procedure_return_type;
  procedure_entry_store : symbolic_store Γ F [];
  procedure_precondition : assertion Γ F [];
  procedure_postcondition : assertion Γ F (return_context procedure_return_type);
  procedure_body : stmt Γ;
}.

Arguments TypedProcedure {_ _} _ _ _ _ _ _ _ _ _ _.

Record procedure_wf {Γ F} (procedure : typed_procedure Γ F) : Prop := {
  procedure_variable_names_unique :
    NoDup (named_context_names (procedure_variables _ _ procedure));
  procedure_formal_slots_unique :
    NoDup (pvar_list_indices (procedure_formal_variables _ _ procedure));
  procedure_return_slot_local :
    ~ In (member_index (procedure_return_variable _ _ procedure))
        (pvar_list_indices (procedure_formal_variables _ _ procedure));
  procedure_nodes_unique : NoDup (stmt_nodes (procedure_body _ _ procedure));
  procedure_results_unique : NoDup (stmt_results (procedure_body _ _ procedure));
  procedure_results_are_nodes :
    forall result, In result (stmt_results (procedure_body _ _ procedure)) ->
      In result (stmt_nodes (procedure_body _ _ procedure));
}.

(** A procedure table must be heterogeneous: procedures may have different
    stack contexts, formal contexts, and return types.  The existential
    package below keeps those indices available when an entry is selected,
    while allowing the table itself to be an ordinary finite list. *)
Definition packed_typed_procedure :=
  { Γ : context & { F : context & typed_procedure Γ F } }.

Definition pack_typed_procedure {Γ F} (procedure : typed_procedure Γ F) :
    packed_typed_procedure :=
  @existT context (fun variables =>
    { formals : context & typed_procedure variables formals }) Γ
    (@existT context (typed_procedure Γ) F procedure).

Definition packed_procedure_id (procedure : packed_typed_procedure) : proc_id :=
  @procedure_identity _ _ (projT2 (projT2 procedure)).

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
    (projT1 (projT2 procedure))
    (@procedure_return_type _ _ (projT2 (projT2 procedure))).

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
  | SEField _ _ => inl EEUnsupportedExpression
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
          match expect_pexpr (Logic.field_type (field_identity field)) value' with
          | inr value'' => inr (FieldInit (field_identity field) value'' :: fields'')
          | inl error => inl error
          end
      | None, _, _ => inl (EEUnknownField field_name)
      | _, inl error, _ | _, _, inl error => inl error
      end
  end.

Definition node_successor (node : node_id) : node_id := Pos.succ node.

(** Elaboration returns the next unused node ID.  The current slice handles
    assignment, field read/write, assertion, sequencing, conditionals, and
    atomic blocks; calls and fold/unfold await their typed declaration
    tables. *)
Fixpoint elaborate_stmt {Γ} (environment : elaboration_environment)
    (variables : named_context Γ) (next : node_id) (statement : source_stmt) :
    elaboration_error + (stmt Γ * node_id) :=
  let next' := node_successor next in
  match statement with
  | SSSkip => inr (TSkip next, next')
  | SSAssert condition =>
      match elaborate_expr variables condition with
      | inl error => inl error
      | inr condition' =>
          match expect_pexpr TBool condition' with
          | inl error => inl error
          | inr condition'' => inr (TAssert next condition'', next')
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
                  inr (TFieldRead next (field_identity field)
                    target'' base'', next')
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
              inr (TAssign next target' value'', next')
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
              inr (TFieldWrite next (field_identity field) base'' value'', next')
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
          | inr target'' => inr (TAlloc next target'' fields', next')
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
                expect_pexpr (Logic.field_type (field_identity field)) old_value',
                expect_pexpr (Logic.field_type (field_identity field)) new_value' with
          | inr base'', inr old_value'', inr new_value'' =>
              inr (TGhostUpdate next (field_identity field) base''
                old_value'' new_value'', next')
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
                  (signature_arguments procedure) arguments with
          | inl error => inl error
          | inr arguments' =>
              match target with
              | None =>
                  inr (TCall next (signature_identity procedure)
                    arguments' (@CTDiscard Γ (signature_return procedure)),
                    next')
              | Some target_name =>
                  match lookup_named variables target_name with
                  | None => inl (EEUnknownVariable target_name)
                  | Some (existT target_type target') =>
                      match typ_eq_dec target_type
                          (signature_return procedure) with
                      | left equality =>
                          match equality in _ = actual_return
                                return elaboration_error + (stmt Γ * node_id) with
                          | eq_refl =>
                              inr (TCall next (signature_identity procedure)
                                arguments' (CTStore target'), next')
                          end
                      | right _ => inl (EETypeMismatch target_type
                          (signature_return procedure))
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
                  (signature_arguments procedure) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TSpawn next (signature_identity procedure) arguments', next')
          end
      end
  | SSUnfold invariant_name arguments =>
      match lookup_invariant invariant_name
              (elaboration_invariants environment) with
      | None => inl (EEUnknownInvariant invariant_name)
      | Some invariant =>
          match elaborate_expr_list variables
                  (Logic.invariant_args (invariant_identity invariant)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TUnfold next (invariant_identity invariant) arguments', next')
          end
      end
  | SSFold invariant_name arguments =>
      match lookup_invariant invariant_name
              (elaboration_invariants environment) with
      | None => inl (EEUnknownInvariant invariant_name)
      | Some invariant =>
          match elaborate_expr_list variables
                  (Logic.invariant_args (invariant_identity invariant)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TFold next (invariant_identity invariant) arguments', next')
          end
      end
  | SSPredicateUnfold predicate_name arguments =>
      match lookup_predicate predicate_name
              (elaboration_predicates environment) with
      | None => inl EEUnsupportedStatement
      | Some predicate =>
          match elaborate_expr_list variables
                  (Logic.predicate_args (predicate_identity predicate)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TPredicateUnfold next (predicate_identity predicate)
                arguments', next')
          end
      end
  | SSPredicateFold predicate_name arguments =>
      match lookup_predicate predicate_name
              (elaboration_predicates environment) with
      | None => inl EEUnsupportedStatement
      | Some predicate =>
          match elaborate_expr_list variables
                  (Logic.predicate_args (predicate_identity predicate)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TPredicateFold next (predicate_identity predicate)
                arguments', next')
          end
      end
  | SSSeq first second =>
      match elaborate_stmt environment variables next' first with
      | inl error => inl error
      | inr (first', after_first) =>
          match elaborate_stmt environment variables after_first second with
          | inl error => inl error
          | inr (second', after_second) =>
              inr (TSeq next first' second', after_second)
          end
      end
  | SSIf condition then_branch else_branch =>
      match elaborate_expr variables condition with
      | inl error => inl error
      | inr condition' =>
          match expect_pexpr TBool condition' with
          | inl error => inl error
          | inr condition'' =>
              match elaborate_stmt environment variables next' then_branch with
              | inl error => inl error
              | inr (then_branch', after_then) =>
                  match elaborate_stmt environment variables after_then else_branch with
                  | inl error => inl error
                  | inr (else_branch', after_else) =>
                      inr (TIf next condition'' then_branch' else_branch', after_else)
                  end
              end
          end
      end
  | SSAtomic body =>
      match elaborate_stmt environment variables next' body with
      | inl error => inl error
      | inr (body', after_body) => inr (TAtomic next body', after_body)
      end
  end.

Fixpoint source_node_count (statement : source_stmt) : nat :=
  match statement with
  | SSSeq first second =>
      S (source_node_count first + source_node_count second)
  | SSIf _ then_branch else_branch =>
      S (source_node_count then_branch + source_node_count else_branch)
  | SSAtomic body => S (source_node_count body)
  | _ => 1
  end.

Fixpoint iterate_node (count : nat) (first : node_id) : node_id :=
  match count with
  | O => first
  | S count' => iterate_node count' (node_successor first)
  end.

Fixpoint node_range (first : node_id) (count : nat) : list node_id :=
  match count with
  | O => []
  | S count' => first :: node_range (node_successor first) count'
  end.

Lemma iterate_node_succ count first :
  iterate_node count (node_successor first) =
    node_successor (iterate_node count first).
Proof.
  revert first. induction count; intros first; simpl.
  - reflexivity.
  - rewrite IHcount. reflexivity.
Qed.

Lemma iterate_node_add left right first :
  iterate_node (left + right) first =
    iterate_node right (iterate_node left first).
Proof.
  revert first. induction left; intros first; simpl.
  - reflexivity.
  - rewrite IHleft. reflexivity.
Qed.

Lemma node_range_add left right first :
  node_range first (left + right) =
    node_range first left ++ node_range (iterate_node left first) right.
Proof.
  revert first. induction left; intros first; simpl.
  - reflexivity.
  - rewrite IHleft. reflexivity.
Qed.

Lemma iterate_node_Z count first :
  Z.pos (iterate_node count first) = Z.pos first + Z.of_nat count.
Proof.
  revert first. induction count; intros first; simpl.
  - lia.
  - rewrite IHcount, Pos2Z.inj_succ, Nat2Z.inj_succ. lia.
Qed.

Lemma in_node_range first count node :
  In node (node_range first count) ->
  (Z.pos first <= Z.pos node < Z.pos first + Z.of_nat count)%Z.
Proof.
  revert first. induction count; intros first Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [<- | Hin].
    + rewrite Nat2Z.inj_succ. lia.
    + specialize (IHcount (node_successor first) Hin).
      rewrite Pos2Z.inj_succ in IHcount.
      rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma node_range_nodup first count : NoDup (node_range first count).
Proof.
  revert first. induction count; intros first; simpl.
  - constructor.
  - constructor.
    + intro Hin. pose proof (in_node_range _ _ _ Hin).
      rewrite Pos2Z.inj_succ in H. lia.
    + apply IHcount.
Qed.

Inductive list_subsequence {A : Type} : list A -> list A -> Prop :=
| SubsequenceNil : list_subsequence [] []
| SubsequenceKeep x xs ys :
    list_subsequence xs ys -> list_subsequence (x :: xs) (x :: ys)
| SubsequenceDrop x xs ys :
    list_subsequence xs ys -> list_subsequence xs (x :: ys).

Arguments SubsequenceNil {_}.
Arguments SubsequenceKeep {_ _ _ _} _.
Arguments SubsequenceDrop {_ _ _ _} _.

Lemma list_subsequence_app {A} (xs xs' ys ys' : list A) :
  list_subsequence xs ys -> list_subsequence xs' ys' ->
  list_subsequence (xs ++ xs') (ys ++ ys').
Proof.
  intros Hsub. revert xs' ys'. induction Hsub; intros xs' ys' Hsub'; simpl.
  - exact Hsub'.
  - constructor. apply IHHsub. exact Hsub'.
  - constructor. apply IHHsub. exact Hsub'.
Qed.

Lemma list_subsequence_in {A} (xs ys : list A) (x : A) :
  list_subsequence xs ys -> In x xs -> In x ys.
Proof.
  intros Hsub. induction Hsub; intros Hin; simpl in *.
  - contradiction.
  - destruct Hin as [<- | Hin]; auto.
  - right. apply IHHsub. exact Hin.
Qed.

Lemma list_subsequence_nodup {A} (xs ys : list A) :
  list_subsequence xs ys -> NoDup ys -> NoDup xs.
Proof.
  intros Hsub. induction Hsub; intros Hnodup.
  - constructor.
  - inversion Hnodup as [| ? ? Hnotin Htail]. constructor.
    + intro Hin. apply Hnotin. eapply list_subsequence_in; eauto.
    + apply IHHsub. exact Htail.
  - inversion Hnodup. apply IHHsub. assumption.
Qed.

Lemma stmt_results_subsequence {Γ} (statement : stmt Γ) :
  list_subsequence (stmt_results statement) (stmt_nodes statement).
Proof.
  induction statement; simpl.
  all: try (constructor; constructor).
  - destruct target; constructor; constructor.
  - constructor. apply list_subsequence_app; assumption.
  - constructor. apply list_subsequence_app; assumption.
  - constructor. assumption.
Qed.

Corollary stmt_results_nodup {Γ} (statement : stmt Γ) :
  NoDup (stmt_nodes statement) -> NoDup (stmt_results statement).
Proof.
  apply list_subsequence_nodup. apply stmt_results_subsequence.
Qed.

Corollary stmt_result_is_node {Γ} (statement : stmt Γ) result :
  In result (stmt_results statement) -> In result (stmt_nodes statement).
Proof.
  eapply list_subsequence_in. apply stmt_results_subsequence.
Qed.

Theorem elaborate_stmt_node_range {Γ}
    (environment : elaboration_environment) (variables : named_context Γ)
    (source : source_stmt) (first finish : node_id) (core : stmt Γ) :
  elaborate_stmt environment variables first source = inr (core, finish) ->
  stmt_nodes core = node_range first (source_node_count source) /\
  finish = iterate_node (source_node_count source) first.
Proof.
  revert first finish core.
  induction source; intros first finish core Helaborates;
    cbn [elaborate_stmt source_node_count] in Helaborates.
  all: repeat match type of Helaborates with
       | context [match ?scrutinee with _ => _ end] =>
           destruct scrutinee eqn:?Hscrutinee
       end; try discriminate.
  all: try (injection Helaborates as <- <-; split; reflexivity).
  - injection Helaborates as <- <-.
    destruct (IHsource1 _ _ _ Hscrutinee1) as [Hnodes1 Hfinish1].
    destruct (IHsource2 _ _ _ Hscrutinee3) as [Hnodes2 Hfinish2].
    subst n n0. simpl. rewrite Hnodes1, Hnodes2.
    split.
    + f_equal. symmetry. apply node_range_add.
    + symmetry. apply iterate_node_add.
  - injection Helaborates as <- <-.
    destruct (IHsource1 _ _ _ Hscrutinee) as [Hnodes1 Hfinish1].
    destruct (IHsource2 _ _ _ Hscrutinee1) as [Hnodes2 Hfinish2].
    subst n n0. simpl. rewrite Hnodes1, Hnodes2.
    split.
    + f_equal. symmetry. apply node_range_add.
    + symmetry. apply iterate_node_add.
  - injection Helaborates as <- <-.
    destruct (IHsource _ _ _ Hscrutinee) as [Hnodes Hfinish].
    subst n. simpl. rewrite Hnodes. split; reflexivity.
Qed.

Corollary elaborate_stmt_wf {Γ}
    (environment : elaboration_environment) (variables : named_context Γ)
    (source : source_stmt) (first finish : node_id) (core : stmt Γ) :
  elaborate_stmt environment variables first source = inr (core, finish) ->
  NoDup (stmt_nodes core) /\
  NoDup (stmt_results core) /\
  (forall result, In result (stmt_results core) ->
    In result (stmt_nodes core)).
Proof.
  intro Helaborates.
  pose proof (elaborate_stmt_node_range environment variables source
    first finish core Helaborates) as [Hnodes _].
  assert (NoDup (stmt_nodes core)) as Hnodes_unique.
  { rewrite Hnodes. apply node_range_nodup. }
  split; [exact Hnodes_unique |]. split.
  - apply stmt_results_nodup. exact Hnodes_unique.
  - intros result Hin. apply stmt_result_is_node. exact Hin.
Qed.

Theorem procedure_wf_of_elaboration {Γ F}
    (environment : elaboration_environment) (source : source_stmt)
    (first finish : node_id) (procedure : typed_procedure Γ F) :
  NoDup (named_context_names (procedure_variables _ _ procedure)) ->
  NoDup (pvar_list_indices (procedure_formal_variables _ _ procedure)) ->
  ~ In (member_index (procedure_return_variable _ _ procedure))
      (pvar_list_indices (procedure_formal_variables _ _ procedure)) ->
  elaborate_stmt environment (procedure_variables _ _ procedure) first source =
      inr (procedure_body _ _ procedure, finish) ->
  procedure_wf procedure.
Proof.
  intros Hnames Hformals Hreturn Helaborates.
  destruct (elaborate_stmt_wf environment
    (procedure_variables _ _ procedure) source first finish
    (procedure_body _ _ procedure) Helaborates)
    as [Hnodes [Hresults Hlive]].
  constructor; assumption.
Qed.

End Make.
End TypedIR.

Module TypedIRExamples.

Module UnitRA := TypedCoreExamples.UnitRA.

Module TinyLogic <: TypedAssertion.LOGIC_SIGNATURE.
  Definition field_type (_ : TypedCore.field_id) := TypedCore.TInt.
  Definition predicate_args (_ : TypedCore.pred_id) : TypedCore.context := [].
  Definition invariant_args (_ : TypedCore.inv_id) := [TypedCore.TRef].
End TinyLogic.

Module IR := TypedIR.Make UnitRA TinyLogic.
Import TypedCore IR.

Definition variables : TypedIR.named_context [TInt; TRef] :=
  TypedIR.NCCons "v" TInt (TypedIR.NCCons "c" TRef TypedIR.NCNil).

Definition environment : TypedIR.elaboration_environment :=
  TypedIR.ElaborationEnvironment
    [TypedIR.FieldDecl "value" 1%positive]
    []
    [TypedIR.InvariantSignature "counter" 1%positive [TRef]]
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
  exists result, elaborate_stmt environment variables 1%positive source_body =
    inr result.
Proof.
  eexists. reflexivity.
Qed.

Example ill_typed_assignment_is_rejected :
  elaborate_stmt environment variables 1%positive
      (SSAssign "v" (SEVal (SVBool true))) =
    inl (EETypeMismatch TInt TBool).
Proof. reflexivity. Qed.

Example allocation_elaborates :
  exists result,
    elaborate_stmt environment variables 1%positive
      (SSAlloc "c" [("value", SEVal (SVInt 0))]) = inr result.
Proof. eexists. reflexivity. Qed.

Example ghost_update_elaborates :
  exists result,
    elaborate_stmt environment variables 1%positive
      (SSGhostUpdate (SEVar "c") "value"
        (SEVal (SVInt 0)) (SEVal (SVInt 1))) = inr result.
Proof. eexists. reflexivity. Qed.

End TypedIRExamples.
