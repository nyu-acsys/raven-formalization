From Coq Require Import List String ZArith PArith Program.Equality
  ProofIrrelevance Lia.
From stdpp Require Import sets.

From raven Require Import surface.syntax verification.expressions verification.assertions verification.resources verification.ir verification.procedures verification.snapshots verification.access_layout
  verification.masks.

Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

(** Elaboration of Raven surface syntax into typed statements. *)
Module Elaboration.

Import Core IR.

Record field_decl := FieldDecl {
  field_source_name : source_name;
  field_identity : field_id;
}.

(** Elaboration entries carry only what elaboration cannot derive: the
    surface name and the identifier it resolves to.  Arities and return
    types are *not* repeated here.  [Logic] is the single source of truth
    for them, and elaboration reads them from
    [procedure_args], [procedure_return],
    [invariant_args] and [predicate_args].  Duplicating them in
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

Import Assertion.

Definition elaborate_typ (t : source_typ) : typ :=
  match t with
  | SBool => TBool
  | SInt => TInt
  | SRef => TRef
  | SUnit => TUnit
  | SNamed resource => TRA resource
  end.

(** ** Signatures and environments of modules

    A module's declarations are numbered in order: the [n]-th field,
    predicate, invariant or procedure has identifier [n].  The logic
    signature and the elaboration environment are read off the
    declarations. *)
Definition declaration_types (declarations : list source_var_decl) : context :=
  map (fun declaration => elaborate_typ (source_var_type declaration))
    declarations.

Definition declared {A} (declarations : list A) (identity : positive) :
    option A :=
  nth_error declarations (pred (Pos.to_nat identity)).

Definition lookup_declared {A} (default : A) (entries : list A)
    (identity : positive) : A :=
  match declared entries identity with
  | Some entry => entry
  | None => default
  end.

(** The per-declaration types are computed first and then looked up, so a
    computed signature answers each identifier with a literal type. *)
Definition module_signature (module : source_module) : LogicSignature :=
  LogicSignatureData
    (lookup_declared TInt (map (fun declaration =>
      elaborate_typ (source_field_type declaration))
      (source_module_fields module)))
    (lookup_declared [] (map (fun declaration =>
      declaration_types (source_pred_args declaration))
      (source_module_predicates module)))
    (lookup_declared [] (map (fun declaration =>
      declaration_types (source_inv_args declaration))
      (source_module_invariants module)))
    (lookup_declared [] (map (fun declaration =>
      declaration_types (source_proc_args declaration))
      (source_module_procedures module)))
    (lookup_declared TUnit (map (fun declaration =>
      match source_proc_return declaration with
      | Some return_declaration =>
          elaborate_typ (source_var_type return_declaration)
      | None => TUnit
      end) (source_module_procedures module))).

Fixpoint numbered_from {A B} (make : A -> positive -> B) (next : positive)
    (declarations : list A) : list B :=
  match declarations with
  | [] => []
  | declaration :: declarations' =>
      make declaration next :: numbered_from make (Pos.succ next) declarations'
  end.

Definition numbered {A B} (make : A -> positive -> B) (declarations : list A) :
    list B :=
  numbered_from make 1%positive declarations.

Definition module_environment (module : source_module) :
    elaboration_environment :=
  ElaborationEnvironment
    (numbered (fun declaration => FieldDecl (source_field_name declaration))
      (source_module_fields module))
    (numbered (fun declaration =>
      ProcedureSignature (source_proc_name declaration))
      (source_module_procedures module))
    (numbered (fun declaration =>
      InvariantSignature (source_inv_name declaration))
      (source_module_invariants module))
    (numbered (fun declaration =>
      PredicateSignature (source_pred_name declaration))
      (source_module_predicates module)).

(** The identifier of a declaration, by name. *)
Definition field_identity_of (module : source_module) (name : source_name) :
    field_id :=
  match lookup_field name (elaboration_fields (module_environment module)) with
  | Some declaration => field_identity declaration
  | None => 1%positive
  end.
Definition procedure_identity_of (module : source_module) (name : source_name) :
    proc_id :=
  match lookup_procedure name (elaboration_procedures (module_environment module)) with
  | Some declaration => signature_identity declaration
  | None => 1%positive
  end.
Definition invariant_identity_of (module : source_module) (name : source_name) :
    inv_id :=
  match lookup_invariant name (elaboration_invariants (module_environment module)) with
  | Some declaration => invariant_identity declaration
  | None => 1%positive
  end.
Definition predicate_identity_of (module : source_module) (name : source_name) :
    pred_id :=
  match lookup_predicate name (elaboration_predicates (module_environment module)) with
  | Some declaration => predicate_identity declaration
  | None => 1%positive
  end.

Section WithSignature.
Context {RAs : RAValueConfig} {Logic : LogicSignature}.

Inductive elaboration_error :=
| EEUnknownVariable (name : source_name)
| EEInaccessibleVariable (name : source_name)
| EEUnknownField (name : source_name)
| EEUnknownProcedure (name : source_name)
| EEUnknownInvariant (name : source_name)
| EETypeMismatch (expected actual : typ)
| EEExpectedReference
| EEArgumentCount
| EEReturnTarget
| EEUnsupportedExpression
| EEUnsupportedStatement
| EEUnsupportedAssertion
| EEIllFormedModule
| EEUndeclaredProcedure
(** A conditional whose guard reads a ghost local has a branch with runtime
    effect. *)
| EEGhostGuard.

Definition packed_pexpr keep Γ := { t : typ & pexpr keep Γ t }.

Definition expect_pexpr {keep Γ} (expected : typ)
    (expression : packed_pexpr keep Γ) :
    elaboration_error + pexpr keep Γ expected.
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
Definition expect_field_chunk {keep Γ} (expected : typ)
    (expression : packed_pexpr keep Γ) :
    elaboration_error + pexpr keep Γ expected.
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

Definition expect_lvar {keep Γ} (expected : typ)
    (variable : { t : typ & lvar keep Γ t }) :
    elaboration_error + lvar keep Γ expected.
Proof.
  destruct variable as [actual variable].
  destruct (typ_eq_dec expected actual) as [<- | Hneq].
  - exact (inr variable).
  - exact (inl (EETypeMismatch expected actual)).
Defined.

(** The same local, if its declaration satisfies [keep]. *)
Fixpoint lvar_restrict (keep : decl -> bool) {keep' D t}
    (variable : lvar keep' D t) : option (lvar keep D t) :=
  match variable with
  | @LHere _ d D' _ =>
      match keep d as selected return
        keep d = selected -> option (lvar keep (d :: D') (decl_type d))
      with
      | true => fun Hkeep => Some (LHere Hkeep)
      | false => fun _ => None
      end eq_refl
  | LThere variable' =>
      match lvar_restrict keep variable' with
      | Some restricted => Some (LThere restricted)
      | None => None
      end
  end.

(** A named local usable where [keep] is required. *)
Definition lookup_variable {Γ} (keep : decl -> bool)
    (variables : named_context Γ) (name : source_name) :
    elaboration_error + { t : typ & lvar keep Γ t } :=
  match lookup_named variables name with
  | None => inl (EEUnknownVariable name)
  | Some (existT t variable) =>
      match lvar_restrict keep variable with
      | Some restricted => inr (existT t restricted)
      | None => inl (EEInaccessibleVariable name)
      end
  end.

Definition elaborate_int_binop {keep Γ} (op : binop TInt TInt TInt)
    (left_expression right_expression : packed_pexpr keep Γ) :
    elaboration_error + packed_pexpr keep Γ :=
  match expect_pexpr TInt left_expression, expect_pexpr TInt right_expression with
  | inr left', inr right' => inr (existT TInt (PEBinOp op left' right'))
  | inl error, _ | _, inl error => inl error
  end.

Definition elaborate_int_comparison {keep Γ} (op : binop TInt TInt TBool)
    (left_expression right_expression : packed_pexpr keep Γ) :
    elaboration_error + packed_pexpr keep Γ :=
  match expect_pexpr TInt left_expression, expect_pexpr TInt right_expression with
  | inr left', inr right' => inr (existT TBool (PEBinOp op left' right'))
  | inl error, _ | _, inl error => inl error
  end.

Definition elaborate_bool_binop {keep Γ} (op : binop TBool TBool TBool)
    (left_expression right_expression : packed_pexpr keep Γ) :
    elaboration_error + packed_pexpr keep Γ :=
  match expect_pexpr TBool left_expression, expect_pexpr TBool right_expression with
  | inr left', inr right' => inr (existT TBool (PEBinOp op left' right'))
  | inl error, _ | _, inl error => inl error
  end.

Definition elaborate_equality {keep Γ} (negated : bool)
    (left_expression right_expression : packed_pexpr keep Γ) :
    elaboration_error + packed_pexpr keep Γ.
Proof.
  destruct left_expression as [left_type left_expression].
  destruct right_expression as [right_type right_expression].
  destruct (typ_eq_dec left_type right_type) as [<- | Hneq].
  - refine (inr (existT TBool (PEBinOp _ left_expression right_expression))).
    exact (if negated then BNe left_type else BEq left_type).
  - exact (inl (EETypeMismatch left_type right_type)).
Defined.

(** Expressions over the locals admitted by [keep]. *)
Fixpoint elaborate_expr {Γ} (keep : decl -> bool)
    (variables : named_context Γ) (expression : source_expr) :
    elaboration_error + packed_pexpr keep Γ :=
  match expression with
  | SEVar name =>
      match lookup_variable keep variables name with
      | inr (existT t variable) => inr (existT t (PEVar variable))
      | inl error => inl error
      end
  | SEVal (SVBool value) => inr (existT TBool (PEVal (VBool value)))
  | SEVal (SVInt value) => inr (existT TInt (PEVal (VInt value)))
  | SEVal SVUnit => inr (existT TUnit (PEVal VUnit))
  | SEUnOp SUNot operand =>
      match elaborate_expr keep variables operand with
      | inl error => inl error
      | inr operand' =>
          match expect_pexpr TBool operand' with
          | inl error => inl error
          | inr operand'' => inr (existT TBool (PEUnOp UNot operand''))
          end
      end
  | SEUnOp SUNeg operand =>
      match elaborate_expr keep variables operand with
      | inl error => inl error
      | inr operand' =>
          match expect_pexpr TInt operand' with
          | inl error => inl error
          | inr operand'' => inr (existT TInt (PEUnOp UNeg operand''))
          end
      end
  | SEBinOp op left_expression right_expression =>
      match elaborate_expr keep variables left_expression,
            elaborate_expr keep variables right_expression with
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

Fixpoint elaborate_expr_list {Γ} (keep : decl -> bool)
    (variables : named_context Γ) (types : context)
    (expressions : list source_expr) :
    elaboration_error + pexpr_list keep Γ types :=
  match types, expressions with
  | [], [] => inr PENil
  | expected :: types', expression :: expressions' =>
      match elaborate_expr keep variables expression,
            elaborate_expr_list keep variables types' expressions' with
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
            elaborate_expr keep_runtime variables value,
            elaborate_field_inits environment variables fields' with
      | Some field, inr value', inr fields'' =>
          match expect_field_chunk
              (field_type (field_identity field)) value' with
          | inr value'' => inr (FieldInit (field_identity field) value'' :: fields'')
          | inl error => inl error
          end
      | None, _, _ => inl (EEUnknownField field_name)
      | _, inl error, _ | _, _, inl error => inl error
      end
  end.

(** Statements.  With [init] set, the statement's write is an initializing
    write, whose target may be a runtime [val]. *)
Fixpoint elaborate_stmt_init {Γ} (init : bool)
    (environment : elaboration_environment)
    (variables : named_context Γ) (statement : source_stmt) :
    elaboration_error + stmt Γ :=
  match statement with
  | SSDone => inr TDone
  | SSAssert condition =>
      match elaborate_expr keep_all variables condition with
      | inl error => inl error
      | inr condition' =>
          match expect_pexpr TBool condition' with
          | inl error => inl error
          | inr condition'' => inr (TAssert condition'')
          end
      end
  | SSAssign target (SEField base field_name)
  | SSFieldRead target base field_name =>
      match lookup_variable (keep_write init) variables target,
            elaborate_expr keep_runtime variables base,
            lookup_field field_name (elaboration_fields environment) with
      | inr target', inr base', Some field =>
          match expect_pexpr TRef base' with
          | inl error => inl error
          | inr base'' =>
              match expect_lvar (field_type (field_identity field)) target' with
              | inr target'' =>
                  inr (TFieldRead init (field_identity field)
                    target'' base'')
              | inl error => inl error
              end
          end
      | inl error, _, _ => inl error
      | _, inl error, _ => inl error
      | _, _, None => inl (EEUnknownField field_name)
      end
  | SSAssign target value =>
      match lookup_variable (keep_write init) variables target,
            elaborate_expr keep_runtime variables value with
      | inr (existT target_type target'), inr value' =>
          match expect_pexpr target_type value' with
          | inl error => inl error
          | inr value'' =>
              inr (TAssign init target' value'')
          end
      | inl error, _ => inl error
      | _, inl error => inl error
      end
  | SSFieldWrite base field_name value =>
      match elaborate_expr keep_runtime variables base,
            elaborate_expr keep_runtime variables value,
            lookup_field field_name (elaboration_fields environment) with
      | inr base', inr value', Some field =>
          match expect_pexpr TRef base',
                expect_pexpr (field_type (field_identity field)) value' with
          | inr base'', inr value'' =>
              inr (TFieldWrite (field_identity field) base'' value'')
          | inl error, _ | _, inl error => inl error
          end
      | inl error, _, _ | _, inl error, _ => inl error
      | _, _, None => inl (EEUnknownField field_name)
      end
  | SSAlloc target fields =>
      match lookup_variable (keep_write init) variables target,
            elaborate_field_inits environment variables fields with
      | inr target', inr fields' =>
          match expect_lvar TRef target' with
          | inr target'' => inr (TAlloc init target'' fields')
          | inl error => inl error
          end
      | inl error, _ => inl error
      | _, inl error => inl error
      end
  | SSGhostUpdate base field_name old_value new_value =>
      match lookup_field field_name (elaboration_fields environment),
            elaborate_expr keep_all variables base,
            elaborate_expr keep_all variables old_value,
            elaborate_expr keep_all variables new_value with
      | Some field, inr base', inr old_value', inr new_value' =>
          match expect_pexpr TRef base',
                expect_field_chunk
                  (field_type (field_identity field)) old_value',
                expect_field_chunk
                  (field_type (field_identity field)) new_value' with
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
          match elaborate_expr_list keep_runtime variables
                  (procedure_args (signature_identity procedure)) arguments with
          | inl error => inl error
          | inr arguments' =>
              match target with
              | None =>
                  inr (TCall (signature_identity procedure)
                    arguments' (@CTDiscard Γ (procedure_return (signature_identity procedure))))
              | Some target_name =>
                  match lookup_variable (keep_write init) variables target_name with
                  | inl error => inl error
                  | inr (existT target_type target') =>
                      match typ_eq_dec target_type
                          (procedure_return
                            (signature_identity procedure)) with
                      | left equality =>
                          (* The target must have the callee's return type. *)
                          inr (TCall (signature_identity procedure)
                            arguments'
                            (CTStore init (eq_rect target_type
                              (fun result => write_target init Γ result) target' _
                              equality)))
                      | right _ => inl (EETypeMismatch target_type
                          (procedure_return
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
          match elaborate_expr_list keep_runtime variables
                  (procedure_args (signature_identity procedure)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TSpawn (signature_identity procedure) arguments')
          end
      end
  | SSUnfold name arguments =>
      match lookup_invariant name (elaboration_invariants environment),
            lookup_predicate name (elaboration_predicates environment) with
      | Some invariant, _ =>
          match elaborate_expr_list keep_all variables
                  (invariant_args (invariant_identity invariant)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TUnfold (invariant_identity invariant) arguments')
          end
      | None, Some predicate =>
          match elaborate_expr_list keep_all variables
                  (predicate_args (predicate_identity predicate)) arguments with
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
          match elaborate_expr_list keep_all variables
                  (invariant_args (invariant_identity invariant)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TFold (invariant_identity invariant) arguments')
          end
      | None, Some predicate =>
          match elaborate_expr_list keep_all variables
                  (predicate_args (predicate_identity predicate)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TPredicateFold (predicate_identity predicate) arguments')
          end
      | None, None => inl (EEUnknownInvariant name)
      end
  | SSSeq first second =>
      match elaborate_stmt_init false environment variables first with
      | inl error => inl error
      | inr first' =>
          match elaborate_stmt_init false environment variables second with
          | inl error => inl error
          | inr second' =>
              inr (TSeq first' second')
          end
      end
  | SSIf condition then_branch else_branch =>
      match elaborate_stmt_init false environment variables then_branch,
            elaborate_stmt_init false environment variables else_branch with
      | inl error, _ | _, inl error => inl error
      | inr then_branch', inr else_branch' =>
          match elaborate_expr keep_runtime variables condition with
          | inr condition' =>
              match expect_pexpr TBool condition' with
              | inl error => inl error
              | inr condition'' => inr (TIf condition'' then_branch' else_branch')
              end
          | inl runtime_error =>
              (* A guard that reads a ghost local makes a proof-only
                 conditional. *)
              match elaborate_expr keep_all variables condition with
              | inl _ => inl runtime_error
              | inr condition' =>
                  match expect_pexpr TBool condition' with
                  | inl error => inl error
                  | inr condition'' =>
                      if proof_onlyb then_branch' && proof_onlyb else_branch'
                      then inr (TGhostIf condition'' then_branch' else_branch')
                      else inl EEGhostGuard
                  end
              end
          end
      end
  | SSAtomic body =>
      match elaborate_stmt_init false environment variables body with
      | inl error => inl error
      | inr body' => inr (TAtomic body')
      end
  | SSGhostVal name annotation initializer body =>
      match elaborate_expr keep_all variables initializer with
      | inl error => inl error
      | inr (existT t initializer') =>
          match annotation with
          | Some annotated =>
              if typ_eq_dec (elaborate_typ annotated) t then
                match elaborate_stmt_init false environment
                    (NCCons name (ghost_val t) variables) body with
                | inl error => inl error
                | inr body' => inr (TGhostVal name t initializer' body')
                end
              else inl (EETypeMismatch (elaborate_typ annotated) t)
          | None =>
              match elaborate_stmt_init false environment
                  (NCCons name (ghost_val t) variables) body with
              | inl error => inl error
              | inr body' => inr (TGhostVal name t initializer' body')
              end
          end
      end
  | SSInit write => elaborate_stmt_init true environment variables write
  end.

Definition elaborate_stmt {Γ} (environment : elaboration_environment)
    (variables : named_context Γ) (statement : source_stmt) :
    elaboration_error + stmt Γ :=
  elaborate_stmt_init false environment variables statement.

(** ** Assertions

    Expressions inside assertions are elaborated as program expressions over
    the bound variables followed by the formals, and then read back as
    logical expressions: a variable of the bound prefix becomes a bound
    reference, one of the formal suffix a formal reference.  Bound names
    therefore shadow formals. *)

(** The locals standing for the names of a type context. *)
Fixpoint runtime_decls (types : context) : decl_context :=
  match types with
  | [] => []
  | t :: types' => runtime_var t :: runtime_decls types'
  end.

Fixpoint named_of_types {Γ} (names : named_types Γ) :
    named_context (runtime_decls Γ) :=
  match names with
  | NTNil => NCNil
  | NTCons name t tail => NCCons name (runtime_var t) (named_of_types tail)
  end.

Fixpoint append_named {Δ F} (bound : named_types Δ)
    (formals : named_types F) : named_context (runtime_decls (Δ ++ F)%list) :=
  match bound with
  | NTNil => named_of_types formals
  | NTCons name t tail => NCCons name (runtime_var t) (append_named tail formals)
  end.

Fixpoint append_types {A B} (left : named_types A) (right : named_types B) :
    named_types (A ++ B)%list :=
  match left with
  | NTNil => right
  | NTCons name t tail => NTCons name t (append_types tail right)
  end.

Definition lvar_nil_elim {keep t} (variable : lvar keep [] t) : False :=
  match variable in lvar _ D0 _ return
    match D0 with [] => False | _ => True end
  with
  | LHere _ => I
  | LThere _ => I
  end.

Definition lvar_case {keep d D t} (variable : lvar keep (d :: D) t) :
    (decl_type d = t) + lvar keep D t :=
  match variable in lvar _ D0 t0 return
    match D0 with
    | [] => unit
    | d0 :: D1 => (decl_type d0 = t0) + lvar keep D1 t0
    end
  with
  | LHere _ => inl eq_refl
  | LThere variable' => inr variable'
  end.

Fixpoint lvar_member (F : context) {keep t} :
    lvar keep (runtime_decls F) t -> member F t :=
  match F with
  | [] => fun variable => match lvar_nil_elim variable with end
  | u :: F' => fun variable =>
      match lvar_case variable with
      | inl equal => eq_rect u (member (u :: F')) MHere t equal
      | inr variable' => MThere (lvar_member F' variable')
      end
  end.

Fixpoint split_lvar (Δ : context) {F keep t} :
    lvar keep (runtime_decls (Δ ++ F)%list) t -> member Δ t + member F t :=
  match Δ with
  | [] => fun variable => inr (lvar_member F variable)
  | u :: Δ' => fun variable =>
      match lvar_case variable with
      | inl equal => inl (eq_rect u (member (u :: Δ')) MHere t equal)
      | inr variable' =>
          match split_lvar Δ' variable' with
          | inl bound => inl (MThere bound)
          | inr formal => inr formal
          end
      end
  end.

Definition logical_ref {Δ F keep t}
    (variable : lvar keep (runtime_decls (Δ ++ F)%list) t) :
    value_ref F Δ t :=
  match split_lvar Δ variable with
  | inl bound => RefBound bound
  | inr formal => RefFormal formal
  end.

Fixpoint logical_expr {Δ F keep t}
    (expression : pexpr keep (runtime_decls (Δ ++ F)%list) t) : expr F Δ t :=
  match expression with
  | PEVar variable => ERef (logical_ref variable)
  | PEVal value => EVal value
  | PEUnOp op operand => EUnOp op (logical_expr operand)
  | PEBinOp op operand1 operand2 =>
      EBinOp op (logical_expr operand1) (logical_expr operand2)
  end.

Fixpoint logical_expr_list {Δ F keep ts}
    (expressions : pexpr_list keep (runtime_decls (Δ ++ F)%list) ts) :
    expr_list F Δ ts :=
  match expressions with
  | PENil => ExprNil
  | PECons expression expressions' =>
      ExprCons (logical_expr expression) (logical_expr_list expressions')
  end.

Fixpoint elaborate_assertion {F Δ} (environment : elaboration_environment)
    (formals : named_types F) (bound : named_types Δ)
    (assertion : source_assertion) :
    elaboration_error + Resource.core_assertion F Δ :=
  let variables := append_named bound formals in
  match assertion with
  | SATrue => inr (Resource.CPure True)
  | SAFalse => inr (Resource.CPure False)
  | SAPure condition =>
      match elaborate_expr keep_all variables condition with
      | inl error => inl error
      | inr condition' =>
          match expect_pexpr TBool condition' with
          | inl error => inl error
          | inr condition'' => inr (Resource.CExpr (logical_expr condition''))
          end
      end
  | SAOwn (SEField base field_name) chunk None =>
      match lookup_field field_name (elaboration_fields environment),
            elaborate_expr keep_all variables base,
            elaborate_expr keep_all variables chunk with
      | None, _, _ => inl (EEUnknownField field_name)
      | _, inl error, _ | _, _, inl error => inl error
      | Some field, inr base', inr chunk' =>
          let identity := field_identity field in
          match expect_pexpr TRef base',
                expect_field_chunk (field_type identity) chunk' with
          | inl error, _ | _, inl error => inl error
          | inr base'', inr chunk'' =>
              inr ((match field_type identity with
                    | TRA _ => @Resource.CGhostOwn _ _ F Δ
                    | _ => @Resource.COwn _ _ F Δ
                    end) identity (logical_expr base'') (logical_expr chunk''))
          end
      end
  | SAOwn _ _ _ => inl EEUnsupportedAssertion
  | SAPredicate name arguments =>
      match lookup_invariant name (elaboration_invariants environment),
            lookup_predicate name (elaboration_predicates environment) with
      | Some invariant, _ =>
          match elaborate_expr_list keep_all variables
                  (invariant_args (invariant_identity invariant)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (Resource.CInvariant (invariant_identity invariant)
                (logical_expr_list arguments'))
          end
      | None, Some predicate =>
          match elaborate_expr_list keep_all variables
                  (predicate_args (predicate_identity predicate)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (Resource.CPredicate (predicate_identity predicate)
                (logical_expr_list arguments'))
          end
      | None, None => inl (EEUnknownInvariant name)
      end
  | SAExists name binder_type body =>
      match elaborate_assertion environment formals
              (NTCons name (elaborate_typ binder_type) bound) body with
      | inl error => inl error
      | inr body' => inr (Resource.CExists (elaborate_typ binder_type) body')
      end
  | SAForall name binder_type body =>
      match elaborate_assertion environment formals
              (NTCons name (elaborate_typ binder_type) bound) body with
      | inl error => inl error
      | inr body' => inr (Resource.CForall (elaborate_typ binder_type) body')
      end
  | SAAnd left_assertion right_assertion =>
      match elaborate_assertion environment formals bound left_assertion,
            elaborate_assertion environment formals bound right_assertion with
      | inl error, _ | _, inl error => inl error
      | inr left', inr right' => inr (Resource.CAnd left' right')
      end
  end.

(** ** Procedures

    A procedure's variables are laid out as its arguments, then its locals,
    then its return variable, all runtime [var]s.  The arguments are the
    formals, and their declared types must match the procedure's signature
    in [Logic]. *)
Fixpoint elaborate_formals (types : context) (declarations : list source_var_decl) :
    elaboration_error + named_types types :=
  match types, declarations with
  | [], [] => inr NTNil
  | t :: types', declaration :: declarations' =>
      if typ_eq_dec (elaborate_typ (source_var_type declaration)) t then
        match elaborate_formals types' declarations' with
        | inl error => inl error
        | inr formals => inr (NTCons (source_var_name declaration) t formals)
        end
      else inl (EETypeMismatch t (elaborate_typ (source_var_type declaration)))
  | _, _ => inl EEArgumentCount
  end.


Definition elaborate_mutability (mutability : source_mutability) :
    Core.mutability :=
  match mutability with SMVal => MVal | SMVar => MVar end.

(** Procedure locals are runtime locals of their declared mutability. *)
Definition local_decl (local : source_local) : decl :=
  Decl PRuntime (elaborate_mutability (source_local_mutability local))
    (elaborate_typ (source_var_type (source_local_decl local))).

Fixpoint elaborate_locals (locals : list source_local) :
    named_context (map local_decl locals) :=
  match locals with
  | [] => NCNil
  | local :: locals' =>
      NCCons (source_var_name (source_local_decl local)) (local_decl local)
        (elaborate_locals locals')
  end.

Fixpoint append_named_context {A B} (left : named_context A)
    (right : named_context B) : named_context (A ++ B)%list :=
  match left with
  | NCNil => right
  | NCCons name d tail => NCCons name d (append_named_context tail right)
  end.

Fixpoint pvar_list_there {D F d} (variables : pvar_list D F) :
    pvar_list (d :: D) F :=
  match variables with
  | PVNil => PVNil
  | PVCons variable variables' =>
      PVCons (LThere variable) (pvar_list_there variables')
  end.

Fixpoint prefix_variables (A : context) (R : decl_context) :
    pvar_list (runtime_decls A ++ R)%list A :=
  match A with
  | [] => PVNil
  | t :: A' =>
      PVCons (D := (runtime_decls (t :: A') ++ R)%list)
        (LHere (keep := keep_all) (d := runtime_var t) eq_refl)
        (pvar_list_there (prefix_variables A' R))
  end.

Fixpoint lvar_app_right (A : decl_context) {keep R t}
    (variable : lvar keep R t) : lvar keep (A ++ R)%list t :=
  match A with
  | [] => variable
  | _ :: A' => LThere (lvar_app_right A' variable)
  end.

(** A procedure without a [returns] clause returns [Unit] through a hidden
    variable, which the source cannot mention. *)
Definition hidden_return_name : source_name := "#return".

Definition elaborate_procedure (environment : elaboration_environment)
    (procedure : source_proc) : elaboration_error + packed_typed_procedure :=
  match lookup_procedure (source_proc_name procedure)
          (elaboration_procedures environment) with
  | None => inl (EEUnknownProcedure (source_proc_name procedure))
  | Some signature =>
      let identity := signature_identity signature in
      let return_type := procedure_return identity in
      let return_declaration :=
        match source_proc_return procedure with
        | Some declaration => declaration
        | None => SourceVarDecl hidden_return_name SUnit
        end in
      match elaborate_formals (procedure_args identity)
              (source_proc_args procedure) with
      | inl error => inl error
      | inr formals =>
          if typ_eq_dec (elaborate_typ (source_var_type return_declaration))
              return_type then
            let return_binder :=
              NTCons (source_var_name return_declaration) return_type NTNil in
            let variables := append_named_context (named_of_types formals)
              (append_named_context
                (elaborate_locals (source_proc_locals procedure))
                (named_of_types return_binder)) in
            match elaborate_assertion environment formals NTNil
                    (source_proc_pre procedure),
                  elaborate_assertion environment formals return_binder
                    (source_proc_post procedure),
                  elaborate_stmt environment variables
                    (source_proc_body procedure) with
            | inl error, _, _ | _, inl error, _ | _, _, inl error => inl error
            | inr precondition, inr postcondition, inr body =>
                inr (pack_typed_procedure
                  (@TypedProcedure _ _ _ identity variables formals
                    (prefix_variables _ _)
                    (lvar_app_right _ (lvar_app_right _
                      (LHere (keep := keep_all) (d := runtime_var return_type)
                        (D := []) eq_refl)))
                    precondition postcondition
                    (AccessLayout.layout_accesses
                      (Snapshots.snapshot_accesses body))))
            end
          else inl (EETypeMismatch return_type
            (elaborate_typ (source_var_type return_declaration)))
      end
  end.

(** ** Modules

    Invariant and predicate bodies are elaborated over their formals.  A
    module elaborates when its procedure table is well formed:
    distinct procedure identities, distinct variable names, and contracts
    free of procedure-entry symbols. *)
Definition elaborate_invariant (environment : elaboration_environment)
    (declaration : source_inv) :
    elaboration_error + { invariant : inv_id &
      Resource.core_assertion (invariant_args invariant) [] } :=
  match lookup_invariant (source_inv_name declaration)
          (elaboration_invariants environment) with
  | None => inl (EEUnknownInvariant (source_inv_name declaration))
  | Some signature =>
      let identity := invariant_identity signature in
      match elaborate_formals (invariant_args identity)
              (source_inv_args declaration) with
      | inl error => inl error
      | inr formals =>
          match elaborate_assertion environment formals NTNil
                  (source_inv_body declaration) with
          | inl error => inl error
          | inr body => inr (existT identity body)
          end
      end
  end.

Definition elaborate_predicate (environment : elaboration_environment)
    (declaration : source_pred) :
    elaboration_error + { predicate : pred_id &
      Resource.core_assertion (predicate_args predicate) [] } :=
  match lookup_predicate (source_pred_name declaration)
          (elaboration_predicates environment) with
  | None => inl (EEUnknownInvariant (source_pred_name declaration))
  | Some signature =>
      let identity := predicate_identity signature in
      match elaborate_formals (predicate_args identity)
              (source_pred_args declaration) with
      | inl error => inl error
      | inr formals =>
          match elaborate_assertion environment formals NTNil
                  (source_pred_body declaration) with
          | inl error => inl error
          | inr body => inr (existT identity body)
          end
      end
  end.

Fixpoint elaborate_all {A B} (elaborate : A -> elaboration_error + B)
    (declarations : list A) : elaboration_error + list B :=
  match declarations with
  | [] => inr []
  | declaration :: declarations' =>
      match elaborate declaration, elaborate_all elaborate declarations' with
      | inl error, _ | _, inl error => inl error
      | inr result, inr results => inr (result :: results)
      end
  end.

Definition elaborate_module_in (environment : elaboration_environment)
    (module : source_module) : elaboration_error + Hoare.module :=
  match elaborate_all (elaborate_predicate environment)
          (source_module_predicates module),
        elaborate_all (elaborate_invariant environment)
          (source_module_invariants module),
        elaborate_all (elaborate_procedure environment)
          (source_module_procedures module) with
  | inl error, _, _ | _, inl error, _ | _, _, inl error => inl error
  | inr predicates, inr invariants, inr procedures =>
      match Hoare.procedure_table procedures with
      | None => inl EEIllFormedModule
      | Some table =>
          if bool_decide (Forall (Hoare.procedure_masks_declared
              (Masks.Declarations (map (@projT1 _ _) predicates)
                (Hoare.lookup_predicate_body predicates)
                (map (@projT1 _ _) invariants)
                (Hoare.lookup_invariant_body invariants)))
              (procedure_entries table))
          then inr (Hoare.make_module table predicates invariants)
          else inl EEIllFormedModule
      end
  end.

(** Elaborate a module in the environment determined by its declarations. *)
Definition elaborate_module (module : source_module) :
    elaboration_error + Hoare.module :=
  elaborate_module_in (module_environment module) module.

(** A procedure of an elaborated module, by identifier. *)
Definition declared_procedure (M : Hoare.module) (identity : proc_id) :
    elaboration_error + { Γ : decl_context & typed_procedure Γ identity } :=
  match Hoare.module_procedure M identity with
  | Some procedure => inr procedure
  | None => inl EEUndeclaredProcedure
  end.

(** ** Results *)

(** Whether elaboration produced a result. *)
Definition elaboration_succeeded {A} (result : elaboration_error + A) : Prop :=
  match result with inl _ => False | inr _ => True end.

(** The result of an elaboration, given evidence that it succeeded.  The
    failure branch is discharged by that evidence rather than by an arbitrary
    placeholder, so a source that does not elaborate is rejected where it is
    used instead of silently becoming a default. *)
Definition elaborated {A} (result : elaboration_error + A)
    (succeeded : elaboration_succeeded result) : A :=
  match result as result' return elaboration_succeeded result' -> A with
  | inl _ => fun impossible => match impossible with end
  | inr value => fun _ => value
  end succeeded.

Lemma elaborated_spec {A} (result : elaboration_error + A)
    (succeeded : elaboration_succeeded result) :
  result = inr (elaborated result succeeded).
Proof. destruct result; [destruct succeeded | reflexivity]. Qed.

End WithSignature.
End Elaboration.

Module ElaborationExamples.

Module UnitRA := CoreExamples.UnitRA.

Module TinyLogic.
  Definition field_type (_ : Core.field_id) := Core.TInt.
  Definition predicate_args (_ : Core.pred_id) : Core.context := [].
  Definition invariant_args (_ : Core.inv_id) := [Core.TRef].
  Definition procedure_args (_ : Core.proc_id) : Core.context :=
    [Core.TRef].
  Definition procedure_return (_ : Core.proc_id) : Core.typ :=
    Core.TUnit.
  Definition logic : Assertion.LogicSignature :=
    Assertion.LogicSignatureData field_type predicate_args invariant_args
      procedure_args procedure_return.
End TinyLogic.

#[local] Existing Instances UnitRA.ra_values TinyLogic.logic.
Import Core IR Elaboration.

Definition variables : IR.named_context [runtime_var TInt; runtime_var TRef] :=
  IR.NCCons "v" (runtime_var TInt) (IR.NCCons "c" (runtime_var TRef) IR.NCNil).

Definition environment : Elaboration.elaboration_environment :=
  Elaboration.ElaborationEnvironment
    [Elaboration.FieldDecl "value" 1%positive]
    []
    [Elaboration.InvariantSignature "counter" 1%positive]
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

Example ghost_val_elaborates :
  exists result,
    elaborate_stmt environment variables
      (SSGhostVal "g" (Some SRef) (SEVar "c")
        (SSSeq (SSUnfold "counter" [SEVar "g"])
          (SSFold "counter" [SEVar "g"]))) = inr result.
Proof. eexists. reflexivity. Qed.

Example ghost_val_is_immutable :
  elaborate_stmt environment variables
      (SSGhostVal "g" None (SEVar "v") (SSAssign "g" (SEVal (SVInt 1)))) =
    inl (EEInaccessibleVariable "g").
Proof. reflexivity. Qed.

Example ghost_val_is_not_runtime :
  elaborate_stmt environment variables
      (SSGhostVal "g" None (SEVar "v") (SSAssign "v" (SEVar "g"))) =
    inl (EEInaccessibleVariable "g").
Proof. reflexivity. Qed.

Definition val_variables :
    IR.named_context [runtime_val TRef; runtime_var TInt] :=
  IR.NCCons "r" (runtime_val TRef) (IR.NCCons "v" (runtime_var TInt) IR.NCNil).

Example val_initialization_elaborates :
  exists result,
    elaborate_stmt environment val_variables
      (SSInit (SSAlloc "r" [("value", SEVal (SVInt 0))])) = inr result.
Proof. eexists. reflexivity. Qed.

Example val_is_immutable :
  elaborate_stmt environment val_variables
      (SSAlloc "r" [("value", SEVal (SVInt 0))]) =
    inl (EEInaccessibleVariable "r").
Proof. reflexivity. Qed.

Example val_is_readable :
  exists result,
    elaborate_stmt environment val_variables
      (SSFieldRead "v" (SEVar "r") "value") = inr result.
Proof. eexists. reflexivity. Qed.

Example ghost_conditional_elaborates :
  exists result,
    elaborate_stmt environment variables
      (SSGhostVal "g" None (SEVar "v")
        (SSIf (SEBinOp SBEq (SEVar "g") (SEVal (SVInt 0)))
          (SSAssert (SEBinOp SBEq (SEVar "v") (SEVal (SVInt 0)))) SSDone)) =
    inr result.
Proof. eexists. reflexivity. Qed.

Example ghost_guard_is_proof_only :
  elaborate_stmt environment variables
      (SSGhostVal "g" None (SEVar "v")
        (SSIf (SEBinOp SBEq (SEVar "g") (SEVal (SVInt 0)))
          (SSAssign "v" (SEVal (SVInt 1))) SSDone)) =
    inl EEGhostGuard.
Proof. reflexivity. Qed.

End ElaborationExamples.
