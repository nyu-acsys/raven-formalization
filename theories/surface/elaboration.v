From Coq Require Import List String ZArith PArith Program.Equality
  ProofIrrelevance Lia.

From raven Require Import surface.syntax verification.expressions verification.assertions verification.resources verification.ir.

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

Section WithSignature.
Context {RAs : RAValueConfig} {Logic : LogicSignature}.

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
              (field_type (field_identity field)) value' with
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
              match expect_pvar (field_type (field_identity field))
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
                expect_pexpr (field_type (field_identity field)) value' with
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
          match elaborate_expr_list variables
                  (procedure_args (signature_identity procedure)) arguments with
          | inl error => inl error
          | inr arguments' =>
              match target with
              | None =>
                  inr (TCall (signature_identity procedure)
                    arguments' (@CTDiscard Γ (procedure_return (signature_identity procedure))))
              | Some target_name =>
                  match lookup_named variables target_name with
                  | None => inl (EEUnknownVariable target_name)
                  | Some (existT target_type target') =>
                      match typ_eq_dec target_type
                          (procedure_return
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
          match elaborate_expr_list variables
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
          match elaborate_expr_list variables
                  (invariant_args (invariant_identity invariant)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TUnfold (invariant_identity invariant) arguments')
          end
      | None, Some predicate =>
          match elaborate_expr_list variables
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
          match elaborate_expr_list variables
                  (invariant_args (invariant_identity invariant)) arguments with
          | inl error => inl error
          | inr arguments' =>
              inr (TFold (invariant_identity invariant) arguments')
          end
      | None, Some predicate =>
          match elaborate_expr_list variables
                  (predicate_args (predicate_identity predicate)) arguments with
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

Definition variables : IR.named_context [TInt; TRef] :=
  IR.NCCons "v" TInt (IR.NCCons "c" TRef IR.NCNil).

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

End ElaborationExamples.
