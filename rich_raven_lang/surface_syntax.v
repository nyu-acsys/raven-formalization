From Coq Require Import String ZArith List.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** A lightweight, named surface language for writing examples in a form
    close to Raven source.  Names are deliberately strings here: this is the
    input to elaboration, not the binding representation of the typed core. *)
Module SurfaceSyntax.

Definition source_name := string.

Definition name (s : string) : source_name := s.

Inductive source_typ :=
| SBool
| SInt
| SRef
| SUnit
| SNamed (name : source_name).

Inductive source_value :=
| SVBool (b : bool)
| SVInt (z : Z)
| SVUnit.

Inductive source_unop :=
| SUNot
| SUNeg.

Inductive source_binop :=
| SBAdd | SBSub | SBMul | SBDiv | SBMod
| SBLt | SBLe | SBGt | SBGe
| SBEq | SBNe
| SBAnd | SBOr.

Inductive source_expr :=
| SEVar (x : source_name)
| SEVal (v : source_value)
| SEUnOp (op : source_unop) (e : source_expr)
| SEBinOp (op : source_binop) (e1 e2 : source_expr)
| SEField (base : source_expr) (field : source_name).

Inductive source_assertion :=
| SATrue
| SAFalse
| SAPure (e : source_expr)
| SAPointsTo (location chunk : source_expr)
| SAPredicate (predicate : source_name) (args : list source_expr)
| SAInvariant (invariant : source_name) (args : list source_expr)
| SAExists (binder : source_name) (binder_type : source_typ)
    (body : source_assertion)
| SAForall (binder : source_name) (binder_type : source_typ)
    (body : source_assertion)
| SAAnd (left right : source_assertion).

Inductive source_stmt :=
| SSSkip
| SSAssert (condition : source_expr)
| SSAssign (target : source_name) (value : source_expr)
| SSFieldRead (target : source_name) (base : source_expr)
    (field : source_name)
| SSFieldWrite (base : source_expr) (field : source_name)
    (value : source_expr)
| SSAlloc (target : source_name) (fields : list (source_name * source_expr))
| SSGhostUpdate (base : source_expr) (field : source_name)
    (old_value new_value : source_expr)
| SSCall (target : option source_name) (procedure : source_name)
    (args : list source_expr)
| SSSpawn (procedure : source_name) (args : list source_expr)
| SSIf (condition : source_expr) (then_branch else_branch : source_stmt)
| SSSeq (first second : source_stmt)
| SSUnfold (invariant : source_name) (args : list source_expr)
| SSFold (invariant : source_name) (args : list source_expr)
| SSPredicateUnfold (predicate : source_name) (args : list source_expr)
| SSPredicateFold (predicate : source_name) (args : list source_expr)
| SSAtomic (body : source_stmt).

Record source_var_decl := SourceVarDecl {
  source_var_name : source_name;
  source_var_type : source_typ;
}.

Record source_proc := SourceProc {
  source_proc_name : source_name;
  source_proc_args : list source_var_decl;
  source_proc_locals : list source_var_decl;
  source_proc_return : option source_var_decl;
  source_proc_pre : source_assertion;
  source_proc_post : source_assertion;
  source_proc_body : source_stmt;
}.

(** Atomic surface forms are overloaded so ordinary Rocq identifiers of type
    [source_name], numerals, and Booleans can all be written without quoting.
    A program file declares its readable names once, e.g.
    [Definition c := name "c".], after which the custom syntax prints [c]. *)
Class IntoSourceExpr (A : Type) :=
  into_source_expr : A -> source_expr.

Global Instance source_name_into_expr : IntoSourceExpr source_name := SEVar.
Global Instance nat_into_expr : IntoSourceExpr nat :=
  fun n => SEVal (SVInt (Z.of_nat n)).
Global Instance Z_into_expr : IntoSourceExpr Z :=
  fun z => SEVal (SVInt z).
Global Instance bool_into_expr : IntoSourceExpr bool :=
  fun b => SEVal (SVBool b).
Global Instance unit_into_expr : IntoSourceExpr unit :=
  fun _ => SEVal SVUnit.

Definition source_atom {A : Type} `{IntoSourceExpr A} (x : A) : source_expr :=
  into_source_expr x.

Declare Custom Entry raven_expr.
Declare Custom Entry raven_exprs.
Declare Custom Entry raven_assert.
Declare Custom Entry raven_stmt.
Declare Custom Entry raven_init.
Declare Custom Entry raven_inits.

Notation "'raven_expr' '{{' e '}}'" := e
  (e custom raven_expr at level 99).
Notation "'raven_assert' '{{' a '}}'" := a
  (a custom raven_assert at level 99).
Notation "'raven_stmt' '{{' s '}}'" := s
  (s custom raven_stmt at level 99).

(* Expressions.  Rocq lexes [x.f] as a qualified identifier, so field access
   is written [x . f] with spaces in the notation layer. *)
Notation "x" := (source_atom x)
  (in custom raven_expr at level 0, x constr at level 0).
Notation "'(' e ')'" := e
  (in custom raven_expr at level 0, e custom raven_expr at level 99).
Notation "e . f" := (SEField e f)
  (in custom raven_expr at level 1, left associativity,
   e custom raven_expr, f constr at level 0).
Notation "'!' e" := (SEUnOp SUNot e)
  (in custom raven_expr at level 35, right associativity,
   e custom raven_expr at level 35).
Notation "'-' e" := (SEUnOp SUNeg e)
  (in custom raven_expr at level 35, right associativity,
   e custom raven_expr at level 35).
Notation "x * y" := (SEBinOp SBMul x y)
  (in custom raven_expr at level 40, left associativity,
   x custom raven_expr, y custom raven_expr at level 41).
Notation "x / y" := (SEBinOp SBDiv x y)
  (in custom raven_expr at level 40, left associativity,
   x custom raven_expr, y custom raven_expr at level 41).
Notation "x % y" := (SEBinOp SBMod x y)
  (in custom raven_expr at level 40, left associativity,
   x custom raven_expr, y custom raven_expr at level 41).
Notation "x + y" := (SEBinOp SBAdd x y)
  (in custom raven_expr at level 50, left associativity,
   x custom raven_expr, y custom raven_expr at level 51).
Notation "x - y" := (SEBinOp SBSub x y)
  (in custom raven_expr at level 50, left associativity,
   x custom raven_expr, y custom raven_expr at level 51).
Notation "x < y" := (SEBinOp SBLt x y)
  (in custom raven_expr at level 60, no associativity,
   x custom raven_expr, y custom raven_expr).
Notation "x <= y" := (SEBinOp SBLe x y)
  (in custom raven_expr at level 60, no associativity,
   x custom raven_expr, y custom raven_expr).
Notation "x > y" := (SEBinOp SBGt x y)
  (in custom raven_expr at level 60, no associativity,
   x custom raven_expr, y custom raven_expr).
Notation "x >= y" := (SEBinOp SBGe x y)
  (in custom raven_expr at level 60, no associativity,
   x custom raven_expr, y custom raven_expr).
Notation "x == y" := (SEBinOp SBEq x y)
  (in custom raven_expr at level 65, no associativity,
   x custom raven_expr, y custom raven_expr).
Notation "x != y" := (SEBinOp SBNe x y)
  (in custom raven_expr at level 65, no associativity,
   x custom raven_expr, y custom raven_expr).
Notation "x && y" := (SEBinOp SBAnd x y)
  (in custom raven_expr at level 70, right associativity,
   x custom raven_expr, y custom raven_expr at level 70).
Notation "x || y" := (SEBinOp SBOr x y)
  (in custom raven_expr at level 75, right associativity,
   x custom raven_expr, y custom raven_expr at level 75).

(* Nonempty comma-separated expression lists.  Empty calls/applications have
   dedicated statement/assertion productions below. *)
Notation "e , .. , en" := (cons e .. (cons en nil) ..)
  (in custom raven_exprs at level 0,
   e custom raven_expr at level 99,
   en custom raven_expr at level 99).

(* Assertions. *)
Notation "'true'" := SATrue (in custom raven_assert at level 0).
Notation "'false'" := SAFalse (in custom raven_assert at level 0).
Notation "'pure' '(' e ')'" := (SAPure e)
  (in custom raven_assert at level 0, e custom raven_expr at level 99).
Notation "p '(' ')'" := (SAPredicate p [])
  (in custom raven_assert at level 0, p constr at level 0).
Notation "p '(' args ')'" := (SAPredicate p args)
  (in custom raven_assert at level 0, p constr at level 0,
   args custom raven_exprs at level 1).
Notation "'inv' p '(' ')'" := (SAInvariant p [])
  (in custom raven_assert at level 0, p constr at level 0).
Notation "'inv' p '(' args ')'" := (SAInvariant p args)
  (in custom raven_assert at level 0, p constr at level 0,
   args custom raven_exprs at level 1).
Notation "'own' '(' e ',' chunk ')'" := (SAPointsTo e chunk)
  (in custom raven_assert at level 30,
   e custom raven_expr at level 99, chunk custom raven_expr at level 99).
Notation "a '&&' b" := (SAAnd a b)
  (in custom raven_assert at level 80, right associativity,
   a custom raven_assert, b custom raven_assert at level 80).
Notation "'(' a ')'" := a
  (in custom raven_assert at level 0, a custom raven_assert at level 99).

(* Statements. *)
Notation "'skip'" := SSSkip (in custom raven_stmt at level 10).
Notation "'assert' e" := (SSAssert e)
  (in custom raven_stmt at level 10, e custom raven_expr at level 99).
Notation "x ':=' e" := (SSAssign x e)
  (in custom raven_stmt at level 10, x constr at level 0,
   e custom raven_expr at level 99).
Notation "base . f ':=' value" :=
  (SSFieldWrite (source_atom base) f value)
  (in custom raven_stmt at level 10,
   base constr at level 0, f constr at level 0,
   value custom raven_expr at level 99).
Notation "f ':' e" := (f, e)
  (in custom raven_init at level 0,
   f constr at level 0, e custom raven_expr at level 99).
Notation "i , .. , j" := (cons i .. (cons j nil) ..)
  (in custom raven_inits at level 0,
   i custom raven_init at level 0,
   j custom raven_init at level 0).
Notation "x ':=' 'new' '(' ')'" := (SSAlloc x [])
  (in custom raven_stmt at level 10, x constr at level 0).
Notation "x ':=' 'new' '(' fields ')'" := (SSAlloc x fields)
  (in custom raven_stmt at level 10, x constr at level 0,
   fields custom raven_inits at level 1).
Notation "'fpu' '(' e . f ',' old_value ',' new_value ')'" :=
  (SSGhostUpdate e f old_value new_value)
  (in custom raven_stmt at level 10,
   e custom raven_expr at level 0, f constr at level 0,
   old_value custom raven_expr at level 99,
   new_value custom raven_expr at level 99).
Notation "p '(' ')'" := (SSCall None p [])
  (in custom raven_stmt at level 10, p constr at level 0).
Notation "p '(' args ')'" := (SSCall None p args)
  (in custom raven_stmt at level 10, p constr at level 0,
   args custom raven_exprs at level 1).
Notation "'call' x ':=' p '(' ')'" := (SSCall (Some x) p [])
  (in custom raven_stmt at level 10,
   x constr at level 0, p constr at level 0).
Notation "'call' x ':=' p '(' args ')'" := (SSCall (Some x) p args)
  (in custom raven_stmt at level 10,
   x constr at level 0, p constr at level 0,
   args custom raven_exprs at level 1).
Notation "'spawn' p '(' ')'" := (SSSpawn p [])
  (in custom raven_stmt at level 10, p constr at level 0).
Notation "'spawn' p '(' args ')'" := (SSSpawn p args)
  (in custom raven_stmt at level 10, p constr at level 0,
   args custom raven_exprs at level 1).
Notation "'unfold' p '(' ')'" := (SSUnfold p [])
  (in custom raven_stmt at level 10, p constr at level 0).
Notation "'unfold' p '(' args ')'" := (SSUnfold p args)
  (in custom raven_stmt at level 10, p constr at level 0,
   args custom raven_exprs at level 1).
Notation "'fold' p '(' ')'" := (SSFold p [])
  (in custom raven_stmt at level 10, p constr at level 0).
Notation "'fold' p '(' args ')'" := (SSFold p args)
  (in custom raven_stmt at level 10, p constr at level 0,
   args custom raven_exprs at level 1).
Notation "'unfold_pred' p '(' ')'" := (SSPredicateUnfold p [])
  (in custom raven_stmt at level 10, p constr at level 0).
Notation "'unfold_pred' p '(' args ')'" := (SSPredicateUnfold p args)
  (in custom raven_stmt at level 10, p constr at level 0,
   args custom raven_exprs at level 1).
Notation "'fold_pred' p '(' ')'" := (SSPredicateFold p [])
  (in custom raven_stmt at level 10, p constr at level 0).
Notation "'fold_pred' p '(' args ')'" := (SSPredicateFold p args)
  (in custom raven_stmt at level 10, p constr at level 0,
   args custom raven_exprs at level 1).
Notation "'atomic' '{' body '}'" := (SSAtomic body)
  (in custom raven_stmt at level 10,
   body custom raven_stmt at level 99).
Notation "'if' condition '{' then_branch '}' 'else' '{' else_branch '}'" :=
  (SSIf condition then_branch else_branch)
  (in custom raven_stmt at level 10,
   condition custom raven_expr at level 99,
   then_branch custom raven_stmt at level 99,
   else_branch custom raven_stmt at level 99).
Notation "first ; second" := (SSSeq first second)
  (in custom raven_stmt at level 90, right associativity,
   first custom raven_stmt, second custom raven_stmt at level 90).
Notation "'(' s ')'" := s
  (in custom raven_stmt at level 10, s custom raven_stmt at level 99).

End SurfaceSyntax.

Export SurfaceSyntax.

(** Parsing and pretty-printing smoke tests. *)
Module SurfaceSyntaxExamples.

Definition c := name "c".
Definition v := name "v".
Definition value := name "value".
Definition counter := name "counter".

Definition arithmetic_example : source_expr :=
  raven_expr {{ v + 1 }}.

Definition assertion_example : source_assertion :=
  raven_assert {{ own(c . value, v) }}.

Definition ghost_update_example : source_stmt :=
  raven_stmt {{ fpu(c . value, v, v + 1) }}.

Definition statement_example : source_stmt :=
  raven_stmt {{
    unfold counter(c);
    v := c . value;
    c . value := v + 1;
    c := new(value: v);
    fold counter(c)
  }}.

End SurfaceSyntaxExamples.
