From Coq Require Import String ZArith List.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** A lightweight, named surface language for writing examples in a form
    close to Raven source.  Names are deliberately strings here: this is the
    input to elaboration, not the binding representation of the typed core.

    Notation reference.  Programs are written [raven_stmt {{ ... }}],
    assertions [raven_assert {{ ... }}], expressions [raven_expr {{ ... }}].

    - Expressions: variables and literals, [x . f] (field access), [!e],
      [-e], [* / % + -], [< <= > >= == !=], [&&], [||].
    - Statements: [x := e]; [x := y . f] (field read); [x . f := e]
      (field write); [x := new(f: e, ...)]; [x := p(args)] and [p(args)]
      (calls); [spawn p(args)]; [fpu(x . f, old, new)]; [unfold p(args)] and
      [fold p(args)] (invariant or predicate, resolved by name);
      [atomic { s }]; [if (e) { s } else { s }] and [if (e) { s }];
      [assert e]; [s1; s2]; [done].
    - Assertions: [true], [false], [pure(e)], [own(x . f, v, q)] (heap
      field with fraction [q]), [own(x . f, v)] (ghost field), [p(args)]
      (invariant or predicate), [a && b].

    Deviations from Raven's concrete syntax: field access needs spaces
    ([x . f]) because Rocq lexes [x.f] as a qualified name; [done] (the
    empty continuation) has no Raven spelling; local variables and procedure
    headers ([var], [proc ... requires ... ensures]) are not part of this
    notation and are given as typed declarations instead; and assertions are
    not yet elaborated into the typed core. *)
Module SurfaceSyntax.

Definition source_name := string.

Definition name (s : string) : source_name := s.

Inductive source_typ :=
| SBool
| SInt
| SRef
| SUnit
| SNamed (name : source_name).

(** Type names for binder annotations, as written in Raven. *)
Definition Int := SInt.
Definition Bool := SBool.
Definition Ref := SRef.
Definition Unit := SUnit.

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
| SEField (base : source_expr) (field : source_name)
(** A procedure call.  Calls are statements, but [x := p(args)] is parsed
    through the expression grammar (see [source_assign]); a call anywhere
    else in an expression is rejected by the elaborator. *)
| SECall (procedure : source_name) (args : list source_expr).

Inductive source_assertion :=
| SATrue
| SAFalse
| SAPure (e : source_expr)
(** [own(x.f, v, q)] for a heap field (with fraction [q]) and [own(x.f, v)]
    for a ghost field, as in Raven. *)
| SAOwn (location chunk : source_expr) (fraction : option source_expr)
(** An invariant or predicate instance [p(args)]; which one is resolved by
    name. *)
| SAPredicate (predicate : source_name) (args : list source_expr)
| SAExists (binder : source_name) (binder_type : source_typ)
    (body : source_assertion)
| SAForall (binder : source_name) (binder_type : source_typ)
    (body : source_assertion)
| SAAnd (left right : source_assertion).

Inductive source_stmt :=
| SSDone
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
(** [unfold p(args)] / [fold p(args)] for an invariant or a predicate; the
    elaborator resolves [p] by name. *)
| SSUnfold (name : source_name) (args : list source_expr)
| SSFold (name : source_name) (args : list source_expr)
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

(** Invariant and predicate declarations: a name, formal parameters, and a
    body. *)
Record source_inv := SourceInv {
  source_inv_name : source_name;
  source_inv_args : list source_var_decl;
  source_inv_body : source_assertion;
}.

Record source_pred := SourcePred {
  source_pred_name : source_name;
  source_pred_args : list source_var_decl;
  source_pred_body : source_assertion;
}.

(** A field declaration.  A field whose type is a resource algebra is a
    ghost field. *)
Record source_field := SourceField {
  source_field_name : source_name;
  source_field_type : source_typ;
}.

(** A Raven module: its fields, predicates, invariants and procedures. *)
Record source_module := SourceModule {
  source_module_fields : list source_field;
  source_module_predicates : list source_pred;
  source_module_invariants : list source_inv;
  source_module_procedures : list source_proc;
}.

(** A procedure body: its local declarations and its statement. *)
Definition source_body_var (name : source_name) (t : source_typ)
    (body : list source_var_decl * source_stmt) :
    list source_var_decl * source_stmt :=
  (SourceVarDecl name t :: fst body, snd body).

(** A procedure header clause.  As in Raven, the clauses may come in any
    order: several [requires] (or [ensures]) clauses are conjoined, a missing
    one is [true], and a procedure without [returns] returns nothing. *)
Inductive source_clause :=
| SCReturns (declaration : source_var_decl)
| SCRequires (condition : source_assertion)
| SCEnsures (condition : source_assertion).

Definition clauses_return (clauses : list source_clause) :
    option source_var_decl :=
  fold_right (fun clause result =>
    match clause with SCReturns declaration => Some declaration | _ => result end)
    None clauses.

Definition clauses_conjunction
    (select : source_clause -> option source_assertion)
    (clauses : list source_clause) : source_assertion :=
  fold_right (fun clause result =>
    match select clause with
    | Some condition =>
        match result with SATrue => condition | _ => SAAnd condition result end
    | None => result
    end) SATrue clauses.

Definition source_procedure (name : source_name)
    (args : list source_var_decl) (clauses : list source_clause)
    (body : list source_var_decl * source_stmt) : source_proc :=
  SourceProc name args (fst body) (clauses_return clauses)
    (clauses_conjunction
      (fun clause => match clause with SCRequires c => Some c | _ => None end)
      clauses)
    (clauses_conjunction
      (fun clause => match clause with SCEnsures c => Some c | _ => None end)
      clauses)
    (snd body).

(** A module-level declaration, as written in a module body. *)
Inductive source_declaration :=
| SDField (declaration : source_field)
| SDPredicate (declaration : source_pred)
| SDInvariant (declaration : source_inv)
| SDProcedure (declaration : source_proc).

(** A module from its declarations, in any order. *)
Definition source_module_of
    (declarations : list source_declaration) : source_module :=
  SourceModule
    (flat_map (fun d => match d with SDField f => [f] | _ => [] end)
      declarations)
    (flat_map (fun d => match d with SDPredicate p => [p] | _ => [] end)
      declarations)
    (flat_map (fun d => match d with SDInvariant i => [i] | _ => [] end)
      declarations)
    (flat_map (fun d => match d with SDProcedure p => [p] | _ => [] end)
      declarations).

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

(** [x := e] is a call when [e] is a call expression and an assignment
    otherwise; this lets both share the [x :=] prefix in the grammar. *)
Definition source_assign (target : source_name) (value : source_expr) :
    source_stmt :=
  match value with
  | SECall procedure args => SSCall (Some target) procedure args
  | _ => SSAssign target value
  end.

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
Declare Custom Entry raven_var_decl.
Declare Custom Entry raven_var_decls.
Declare Custom Entry raven_body.
Declare Custom Entry raven_proc.
Declare Custom Entry raven_clause.
Notation "'raven_proc' '{{' p '}}'" := p
  (p custom raven_proc at level 200).
Declare Custom Entry raven_decl.
Notation "'raven_decl' '{{' d '}}'" := d
  (d custom raven_decl at level 200).
Notation "'raven_module' '{{' d .. e '}}'" :=
  (source_module_of (cons d .. (cons e nil) ..))
  (d custom raven_decl at level 0, e custom raven_decl at level 0).


(* Expressions.  Rocq lexes [x.f] as a qualified identifier, so field access
   is written [x . f] with spaces in the notation layer. *)
Notation "x" := (source_atom x)
  (in custom raven_expr at level 0, x constr at level 0).
Notation "'(' e ')'" := e
  (in custom raven_expr at level 0, e custom raven_expr at level 99).
Notation "e . f" := (SEField e f)
  (in custom raven_expr at level 1, left associativity,
   e custom raven_expr, f constr at level 0).
Notation "p '(' ')'" := (SECall p [])
  (in custom raven_expr at level 0, p constr at level 0).
Notation "p '(' args ')'" := (SECall p args)
  (in custom raven_expr at level 0, p constr at level 0,
   args custom raven_exprs at level 1).
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
Notation "'own' '(' e ',' chunk ')'" := (SAOwn e chunk None)
  (in custom raven_assert at level 30,
   e custom raven_expr at level 99, chunk custom raven_expr at level 99).
Notation "'own' '(' e ',' chunk ',' q ')'" := (SAOwn e chunk (Some q))
  (in custom raven_assert at level 30,
   e custom raven_expr at level 99, chunk custom raven_expr at level 99,
   q custom raven_expr at level 99).
Notation "'exists' x ':' T '::' a" := (SAExists x T a)
  (in custom raven_assert at level 90,
   x constr at level 0, T constr at level 0, a custom raven_assert at level 90).
Notation "'forall' x ':' T '::' a" := (SAForall x T a)
  (in custom raven_assert at level 90,
   x constr at level 0, T constr at level 0, a custom raven_assert at level 90).
Notation "a '&&' b" := (SAAnd a b)
  (in custom raven_assert at level 80, right associativity,
   a custom raven_assert, b custom raven_assert at level 80).
Notation "'(' a ')'" := a
  (in custom raven_assert at level 0, a custom raven_assert at level 99).

(* Field, invariant and predicate declarations. *)
Notation "'field' f ':' T" := (SDField (SourceField f T))
  (in custom raven_decl at level 0, f constr at level 0, T constr at level 0).
Notation "'inv' p '(' args ')' '{' body '}'" := (SDInvariant (SourceInv p args body))
  (in custom raven_decl at level 0, p constr at level 0,
   args custom raven_var_decls, body custom raven_assert at level 99).
Notation "'pred' p '(' args ')' '{' body '}'" := (SDPredicate (SourcePred p args body))
  (in custom raven_decl at level 0, p constr at level 0,
   args custom raven_var_decls, body custom raven_assert at level 99).

(* Procedures. *)
Notation "x ':' T" := (SourceVarDecl x T)
  (in custom raven_var_decl at level 0, x constr at level 0, T constr at level 0).
Notation "d , .. , e" := (cons d .. (cons e nil) ..)
  (in custom raven_var_decls at level 0,
   d custom raven_var_decl at level 0, e custom raven_var_decl at level 0).
Notation "'var' x ':' T ';' body" := (source_body_var x T body)
  (in custom raven_body at level 100,
   x constr at level 0, T constr at level 0, body custom raven_body at level 100).
Notation "s" := ([], s)
  (in custom raven_body at level 100, s custom raven_stmt at level 99).
Notation "'returns' '(' r ')'" := (SCReturns r)
  (in custom raven_clause at level 0, r custom raven_var_decl).
Notation "'requires' condition" := (SCRequires condition)
  (in custom raven_clause at level 0, condition custom raven_assert at level 99).
Notation "'ensures' condition" := (SCEnsures condition)
  (in custom raven_clause at level 0, condition custom raven_assert at level 99).
Notation "'proc' p '(' ')' c .. c' '{' body '}'" :=
  (source_procedure p [] (cons c .. (cons c' nil) ..) body)
  (in custom raven_proc at level 0, p constr at level 0,
   c custom raven_clause at level 0, c' custom raven_clause at level 0,
   body custom raven_body at level 100).
Notation "'proc' p '(' ')' '{' body '}'" :=
  (source_procedure p [] [] body)
  (in custom raven_proc at level 0, p constr at level 0,
   body custom raven_body at level 100).
Notation "'proc' p '()' c .. c' '{' body '}'" :=
  (source_procedure p [] (cons c .. (cons c' nil) ..) body)
  (in custom raven_proc at level 0, p constr at level 0,
   c custom raven_clause at level 0, c' custom raven_clause at level 0,
   body custom raven_body at level 100).
Notation "'proc' p '()' '{' body '}'" :=
  (source_procedure p [] [] body)
  (in custom raven_proc at level 0, p constr at level 0,
   body custom raven_body at level 100).
Notation "'proc' p '(' args ')' c .. c' '{' body '}'" :=
  (source_procedure p args (cons c .. (cons c' nil) ..) body)
  (in custom raven_proc at level 0, p constr at level 0, args custom raven_var_decls,
   c custom raven_clause at level 0, c' custom raven_clause at level 0,
   body custom raven_body at level 100).
Notation "'proc' p '(' args ')' '{' body '}'" :=
  (source_procedure p args [] body)
  (in custom raven_proc at level 0, p constr at level 0, args custom raven_var_decls,
   body custom raven_body at level 100).

Notation "'proc' p '(' ')' c .. c' '{' body '}'" :=
  (SDProcedure (source_procedure p [] (cons c .. (cons c' nil) ..) body))
  (in custom raven_decl at level 0, p constr at level 0,
   c custom raven_clause at level 0, c' custom raven_clause at level 0,
   body custom raven_body at level 100).
Notation "'proc' p '(' ')' '{' body '}'" :=
  (SDProcedure (source_procedure p [] [] body))
  (in custom raven_decl at level 0, p constr at level 0,
   body custom raven_body at level 100).
Notation "'proc' p '()' c .. c' '{' body '}'" :=
  (SDProcedure (source_procedure p [] (cons c .. (cons c' nil) ..) body))
  (in custom raven_decl at level 0, p constr at level 0,
   c custom raven_clause at level 0, c' custom raven_clause at level 0,
   body custom raven_body at level 100).
Notation "'proc' p '()' '{' body '}'" :=
  (SDProcedure (source_procedure p [] [] body))
  (in custom raven_decl at level 0, p constr at level 0,
   body custom raven_body at level 100).
Notation "'proc' p '(' args ')' c .. c' '{' body '}'" :=
  (SDProcedure (source_procedure p args (cons c .. (cons c' nil) ..) body))
  (in custom raven_decl at level 0, p constr at level 0, args custom raven_var_decls,
   c custom raven_clause at level 0, c' custom raven_clause at level 0,
   body custom raven_body at level 100).
Notation "'proc' p '(' args ')' '{' body '}'" :=
  (SDProcedure (source_procedure p args [] body))
  (in custom raven_decl at level 0, p constr at level 0, args custom raven_var_decls,
   body custom raven_body at level 100).

(* Statements. *)
Notation "'done'" := SSDone (in custom raven_stmt at level 10).
Notation "'assert' e" := (SSAssert e)
  (in custom raven_stmt at level 10, e custom raven_expr at level 99).
Notation "x ':=' e" := (source_assign x e)
  (in custom raven_stmt at level 10, x constr at level 0,
   e custom raven_expr at level 99).
Notation "x ':=' p '(' ')'" := (SSCall (Some x) p [])
  (in custom raven_stmt at level 10,
   x constr at level 0, p constr at level 0, only printing).
Notation "x ':=' p '(' args ')'" := (SSCall (Some x) p args)
  (in custom raven_stmt at level 10,
   x constr at level 0, p constr at level 0,
   args custom raven_exprs at level 1, only printing).
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
Notation "'atomic' '{' body '}'" := (SSAtomic body)
  (in custom raven_stmt at level 10,
   body custom raven_stmt at level 99).
Notation "'if' '(' condition ')' '{' then_branch '}'" :=
  (SSIf condition then_branch SSDone)
  (in custom raven_stmt at level 10,
   condition custom raven_expr at level 99,
   then_branch custom raven_stmt at level 99).
Notation "'if' '(' condition ')' '{' then_branch '}' 'else' '{' else_branch '}'" :=
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
  raven_assert {{ own(c . value, v, 1) && counter(c) }}.

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

(** The notations build the intended surface terms. *)
Example assign_is_assignment :
  raven_stmt {{ v := v + 1 }} = SSAssign v (SEBinOp SBAdd (SEVar v) (SEVal (SVInt 1))).
Proof. reflexivity. Qed.

Example assign_of_call_is_call :
  raven_stmt {{ v := counter(c) }} = SSCall (Some v) counter [SEVar c].
Proof. reflexivity. Qed.

Example if_without_else :
  raven_stmt {{ if (v == 0) { v := 1 } }} =
    SSIf (SEBinOp SBEq (SEVar v) (SEVal (SVInt 0)))
      (SSAssign v (SEVal (SVInt 1))) SSDone.
Proof. reflexivity. Qed.

Example heap_and_ghost_ownership :
  raven_assert {{ own(c . value, v, 1) && own(c . value, v) }} =
    SAAnd (SAOwn (SEField (SEVar c) value) (SEVar v) (Some (SEVal (SVInt 1))))
      (SAOwn (SEField (SEVar c) value) (SEVar v) None).
Proof. reflexivity. Qed.

Example existential_ownership :
  raven_assert {{ exists v : Int :: own(c . value, v) && counter(c) }} =
    SAExists v SInt
      (SAAnd (SAOwn (SEField (SEVar c) value) (SEVar v) None)
        (SAPredicate counter [SEVar c])).
Proof. reflexivity. Qed.

Example procedure_declaration :
  raven_proc {{
    proc counter(c : Ref) returns (v : Int)
      requires true
      ensures true
    {
      var value : Int;
      v := c . value
    }
  }} =
    SourceProc counter [SourceVarDecl c SRef] [SourceVarDecl value SInt]
      (Some (SourceVarDecl v SInt)) SATrue SATrue
      (SSAssign v (SEField (SEVar c) value)).
Proof. reflexivity. Qed.

Example procedure_without_result :
  raven_proc {{
    proc counter(c : Ref) requires counter(c) requires true {
      c . value := 1
    }
  }} =
    SourceProc counter [SourceVarDecl c SRef] [] None
      (SAPredicate counter [SEVar c]) SATrue
      (SSFieldWrite (SEVar c) value (SEVal (SVInt 1))).
Proof. reflexivity. Qed.

End SurfaceSyntaxExamples.
