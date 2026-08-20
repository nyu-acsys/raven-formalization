From stdpp Require Export strings.
From stdpp Require Import gmap list sets countable.
Require Import Eqdep_dec.
From iris.program_logic Require Export language ectx_language ectxi_language.

Inductive bin_op : Set :=
| AddOp | SubOp | MulOp | DivOp | ModOp
| EqOp | NeOp | LtOp
| GtOp | LeOp | GeOp
| AndOp | OrOp
(* comp/frame : RA * RA -> RA; fpuValid : RA * RA -> Bool -- see ResourceAlgebra below *)
| RACompOp | RAFrameOp | RAFpuValidOp.

Inductive un_op : Set :=
| NotBoolOp | NegOp
(* valid : RA -> Bool *)
| RAValidOp.

(* Resource algebras usable as RA-typed program values (see typ/val below).
   Defined here, at the base of the language, rather than in the ghost/spec
   layer: RA elements are ordinary values a real program variable can hold
   and manipulate via RACompOp/RAFrameOp/RAValidOp/RAFpuValidOp, tracked by
   the real stack frame like any other value -- not a separate ghost-only
   bookkeeping structure. *)
Class ResourceAlgebra (A: Type) := {
  comp : A -> A -> A;
  frame : A -> A -> A;
  valid : A -> Prop;
  valid_dec :: forall x : A, Decision (valid x);
  fpuValid : A -> A -> Prop;
  fpuValid_dec :: forall x y : A, Decision (fpuValid x y);
  fpuAxiom : forall x y, fpuValid x y -> valid x /\ valid y /\ forall c, (valid (comp x c) -> valid (comp y c));
  (* The identity/unit element, and its defining left-identity law -- matches
     how Raven's own RA formalization presents an RA (id together with
     comp), and gives canonical_val below a natural witness value. *)
  ra_id : A;
  ra_id_comp : forall x, comp ra_id x = x;
}.

Record RA_Pack := {
  RA_carrier :> Type;
  RA_carrier_eqdec :> EqDecision RA_carrier;
  RA_carrier_countable :> Countable RA_carrier;
  RA_inst :> ResourceAlgebra RA_carrier;
}.

(* RA_Pack's fields use plain Record coercion (:>), not Class instance
   fields, so they aren't picked up by typeclass search automatically --
   register them explicitly. *)
Global Instance ra_carrier_eqdec_instance (r : RA_Pack) : EqDecision (RA_carrier r) :=
  RA_carrier_eqdec r.
Global Instance ra_carrier_countable_instance (r : RA_Pack) : Countable (RA_carrier r) :=
  RA_carrier_countable r.
Global Instance ra_inst_instance (r : RA_Pack) : ResourceAlgebra (RA_carrier r) :=
  RA_inst r.

(* Every RA usable in an RA-typed expression is looked up by name out of a
   fixed, total registry -- mirrors fld_map/pred_map/inv_map in the ghost
   layer. Naming RAs (rather than embedding RA_Pack values inline in
   typ/val) is what makes equality of RA-typed values decidable: ra_name is
   just a string, whereas RA_Pack bundles an arbitrary Type that isn't. *)
Definition ra_name := string.
Global Parameter ra_set : gset ra_name.
Global Parameter ra_map : ra_name -> RA_Pack.

(* A concrete element of some named RA, its name bundled alongside it --
   the payload of val's LitRAElem case below. *)
Definition ra_elem : Type := {r : ra_name & RA_carrier (ra_map r)}.

Global Instance ra_elem_eq_dec : EqDecision ra_elem.
Proof.
  intros [r1 x1] [r2 x2].
  destruct (decide (r1 = r2)) as [<-|Hne].
  - destruct (decide (x1 = x2)) as [->|Hne]; [left; reflexivity | ].
    right. intro HH. apply Hne.
    exact (Eqdep_dec.inj_pair2_eq_dec ra_name (fun a b => decide (a = b)) _ r1 x1 x2 HH).
  - right. intro HH. apply Hne. exact (f_equal (@projT1 ra_name _) HH).
Qed.

Global Instance ra_elem_countable : Countable ra_elem.
Proof.
  apply (inj_countable
    (fun p : ra_elem => let 'existT r x := p in (r, encode x) : ra_name * positive)
    (fun rp : ra_name * positive => let '(r, xp) := rp in
       match decode xp : option (RA_carrier (ra_map r)) with
       | Some x => Some (existT r x)
       | None => None
       end)).
  intros [r x]. simpl. rewrite decode_encode. reflexivity.
Qed.

Section expr.

Inductive typ :=
| TpInt | TpLoc | TpBool | TpUnit | TpRA (r : ra_name).

Global Instance bin_op_eq_decision : EqDecision bin_op.
Proof. solve_decision. Qed.

Global Instance bin_op_countable : Countable bin_op.
Proof.
  refine (inj_countable'
    (λ op, match op with
      | AddOp => 0 | SubOp => 1 | MulOp => 2 | DivOp => 3 | ModOp => 4
      | EqOp => 5 | NeOp => 6 | LtOp => 7 | GtOp => 8 | LeOp => 9 | GeOp => 10
      | AndOp => 11 | OrOp => 12
      | RACompOp => 13 | RAFrameOp => 14 | RAFpuValidOp => 15
    end : nat)
    (λ n, match n with
      | 0 => AddOp | 1 => SubOp | 2 => MulOp | 3 => DivOp | 4 => ModOp
      | 5 => EqOp | 6 => NeOp | 7 => LtOp | 8 => GtOp | 9 => LeOp | 10 => GeOp
      | 11 => AndOp | 12 => OrOp | 13 => RACompOp | 14 => RAFrameOp | _ => RAFpuValidOp
    end) _).
  intros []; done.
Qed.

Global Instance un_op_eq_decision : EqDecision un_op.
Proof. solve_decision. Qed.

Global Instance un_op_countable : Countable un_op.
Proof.
  refine (inj_countable'
    (λ op, match op with NotBoolOp => 0 | NegOp => 1 | RAValidOp => 2 end : nat)
    (λ n, match n with 0 => NotBoolOp | 1 => NegOp | _ => RAValidOp end) _).
  intros []; done.
Qed.

Global Instance typ_eq_decision : EqDecision typ.
Proof. solve_decision. Qed.

Scheme Equality for typ.

Record loc := Loc { loc_car : Z }.

(* Type class instances for loc *)
Global Instance loc_eq_decision : EqDecision loc.
Proof.
  solve_decision.
Qed.

Global Instance loc_countable : Countable loc.
Proof.
  refine (inj_countable' loc_car (λ x, Loc x) _).
  intros [x]. simpl. f_equal.
Qed.

Definition fld_name := string.
Record fld := Fld { fld_name_val : fld_name; fld_typ : typ }.

Definition var := string.
Definition proc_name := string.

Inductive expr :=
| Var (x : var)
| Val (v : val)
| UnOp (op : un_op) (e : expr)
| BinOp (op : bin_op) (e1 e2 : expr)
| IfE (e1 e2 e3 : expr)
| StuckE (* stuck expression *)
with
val :=
| LitBool (b: bool) | LitInt (i: Z) | LitUnit | LitLoc (l: loc)
| LitRAElem (p : ra_elem).

Global Instance val_dec_eq : EqDecision val.
Proof.
  solve_decision.
Qed.

(* Whether a value inhabits a declared type -- used to non-deterministically
   pick well-typed placeholder values for a fresh stack frame's local
   variables (see RTCallStep/SpawnStep). *)
Definition val_has_typ (v : val) (t : typ) : Prop :=
  match v, t with
  | LitBool _, TpBool | LitInt _, TpInt | LitUnit, TpUnit | LitLoc _, TpLoc => True
  | LitRAElem (existT r _), TpRA r' => r = r'
  | _, _ => False
  end.

(* A fixed witness inhabitant of each type, used only to exhibit that a step
   filling in non-deterministic local values is always possible. For TpRA,
   ra_id is exactly this witness -- the RA's own identity element. *)
Definition canonical_val (t : typ) : val :=
  match t with
  | TpInt => LitInt 0 | TpBool => LitBool false | TpUnit => LitUnit | TpLoc => LitLoc (Loc 0)
  | TpRA r => LitRAElem (existT r ra_id)
  end.

Lemma canonical_val_has_typ t : val_has_typ (canonical_val t) t.
Proof. destruct t; simpl; done. Qed.

End expr.

Inductive stmt :=
| Seq (s1 s2 : stmt)
(* | Return (e : expr) *)
| IfS (e : expr) (s1 s2 : stmt)
| Assign (v : var) (e : expr)
(* | Free (e : expr) *)
| SkipS
| StuckS (* stuck statement *)
(* | ExprS (e : expr) *)
| Call (v : var) (proc : proc_name) (args : list expr)
| FldWr (v : var) (fld : fld_name) (e2 : expr) 
| FldRd (v : var) (e : expr) (fld : fld_name)
| CAS (v : var) (e1 : expr) (fld : fld_name) (e2 : expr) (e3 : expr)
| Alloc (v : var) (fs: list (fld_name * val))
| Spawn (proc : proc_name) (args : list expr)
.

Definition stmt_append (s1 s2 : stmt) : stmt :=
  Seq s1 s2.


Section state.

Inductive heap_addr :=
| heap_addr_constr:  loc -> fld_name -> heap_addr.

Global Instance heap_addr_eq : EqDecision heap_addr.
Proof. solve_decision. Qed.

Global Instance heap_addr_countable : Countable heap_addr.
Proof.
  refine (inj_countable'
    (λ a, match a with heap_addr_constr l f => (l, f) end)
    (λ '(l, f), heap_addr_constr l f) _).
  intros [l f]. done.
Qed.

(* Heap maps locations to field-value pairs *)
Definition heap := gmap heap_addr val.

(* Stack frame contains local variables and current statement *)



Definition stack_id := Z.

Record stack_frame := StackFrame {
  locals : gmap var val;
  (* curr_stmt : stmt; *)
  (* ret_var : option var; *)
  (* ret_stack := stack_id; *)
}.

Definition stack_map := gmap stack_id stack_frame.

Record proc := Proc {
  proc_name_val : proc_name;
  proc_args : list (var * typ);
  proc_local_vars : list (var * typ);
  proc_stmt : stmt;
}.

(* Global state combines heap and stack *)
Record state := State {
  global_heap : heap;
  (* stack : list stack_frame;  *)
  (* moving stack frames from state to runtime_expr *)
  procs : gmap proc_name proc;
  stack : gmap stack_id stack_frame;
  max_stack_id : Z;
}.

Definition fresh_stk_id (σ : state) := (Z.to_nat (σ.(max_stack_id)) + 1, State σ.(global_heap) σ.(procs) σ.(stack) (1 + σ.(max_stack_id))).

(* Empty state *)
Definition empty_state : state := State ∅ ∅ ∅ 0.

(* Helper functions for state manipulation *)
Definition update_heap (σ : state) (l : loc) (f : fld_name) (v : val) : state :=
  let h := σ.(global_heap) in

  (* let fields := default ∅ (h !! l) in
  let new_fields := <[f := v]> fields in *)
  State (<[heap_addr_constr l f := v]> h) σ.(procs) σ.(stack) σ.(max_stack_id).

(* Definition stack := list stack_frame. *)

Definition lookup_heap (σ : state) (l : loc) (f : fld_name) : option val :=
  σ.(global_heap) !! (heap_addr_constr l f).

  
Definition update_frame_lvar (frame : stack_frame) (x : var) (v : val) : stack_frame :=
  StackFrame (<[x := v]> frame.(locals)) .

Definition update_lvar (σ : state) (x : var) (stk_id : stack_id) (v : val) : state :=
  match σ.(stack) !! stk_id with
  | None => σ
  | Some stk_frm =>
    State σ.(global_heap) σ.(procs)
      (<[stk_id := update_frame_lvar stk_frm x v]> σ.(stack))
      σ.(max_stack_id)
  end.

Definition lookup_lvar (σ : state) (x : var) (stk_id : stack_id) : option val :=
  match σ.(stack) !! stk_id with
  | Some stk_frame => stk_frame.(locals) !! x
  | None => None
  end.

Definition update_stack (σ : state) (stk_id : stack_id) (frame : stack_frame) :=
  State σ.(global_heap) σ.(procs) (<[stk_id := frame]> σ.(stack)) σ.(max_stack_id).

Definition lookup_proc (σ : state) (pr_name : proc_name) : option proc :=
  σ.(procs) !! pr_name.

(* Substitute formal arguments with actual expressions *)
Fixpoint subst_expr (e : expr) (subst : list (var * expr)) : expr :=
  match e with
  | Var x => match find (λ p, bool_decide (p.1 = x)) subst with
             | Some (_, e') => e'
             | None => Var x
             end
  | Val v => Val v
  | UnOp op e => UnOp op (subst_expr e subst)
  | BinOp op e1 e2 => BinOp op (subst_expr e1 subst) (subst_expr e2 subst)
  | IfE e1 e2 e3 => IfE (subst_expr e1 subst) (subst_expr e2 subst) (subst_expr e3 subst)
  | StuckE => StuckE
  end.


  (* Assuming that local variables of each procedure are disjoint *)
Fixpoint subst_stmt (s : stmt) (subst : list (var * expr)) : stmt :=
  match s with
  | Seq s1 s2 => Seq (subst_stmt s1 subst) (subst_stmt s2 subst)
  (* | Return e => Return (subst_expr e subst) *)
  | IfS e s1 s2 => IfS (subst_expr e subst) (subst_stmt s1 subst) (subst_stmt s2 subst)
  | Assign v e => Assign v (subst_expr e subst)
  (* | Free e => Free (subst_expr e subst) *)
  | SkipS => SkipS
  | StuckS => StuckS
  (* | ExprS e => ExprS (subst_expr e subst) *)
  | Call v proc args => Call v proc (map (λ e, subst_expr e subst) args)
  | FldWr v f e2 => FldWr v f (subst_expr e2 subst)
  | FldRd v e f => FldRd v e f
  | CAS vr e1 f e2 e3 => CAS vr (subst_expr e1 subst) f (subst_expr e2 subst) (subst_expr e3 subst)
  | Alloc v fs => Alloc v fs
  | Spawn proc args => Spawn proc (map (λ e, subst_expr e subst) args)
  end.
End state.

Definition fresh_loc (h : heap) : loc :=
  Loc (Z.of_nat (size h)).

(* Operational Semantics *)
Section semantics.

Inductive runtime_stmt :=
| RTSeq (s1 s2 : runtime_stmt)
| RTIfS (e : expr) (s1 s2 : runtime_stmt) (stk_id : stack_id)
| RTAssign (v : var) (e : expr) (stk_id : stack_id)
(* | RTFree (e : expr) (stk_id : stack_id) *)
| RTSkipS (stk_id : stack_id)
| RTStuckS
| RTVal (v : val)
| RTCall (v : var) (proc : proc_name) (args : list expr) (stk_id : stack_id)
| RTActiveCall (v : var) (s : runtime_stmt) (callee_stk_id : stack_id) (caller_stk_id : stack_id) 
| RTFldWr (v : var) (fld : fld_name) (e : expr) (stk_id : stack_id)
| RTFldRd (v : var) (e : expr) (fld : fld_name) (stk_id : stack_id)
| RTCAS (v : var) (e1 : expr) (fld : fld_name) (e2 : expr) (e3 : expr) (stk_id : stack_id)
| RTAlloc (v : var) (fs : list (fld_name * val)) (stk_id : stack_id)
| RTSpawn (proc : proc_name) (args : list expr) (stk_id : stack_id)
.

Definition of_val v := RTVal v.
Definition to_val (e : runtime_stmt) := match e with
| RTVal v => Some v
| _ => None
end.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Inductive ectx_item :=
| SeqCtx (s : runtime_stmt)
| ActiveCallCtx (v : var) (c_id : stack_id) (cr_id : stack_id).

Definition fill_item (Ki : ectx_item) (s : runtime_stmt) : runtime_stmt :=
  match Ki with
  | SeqCtx s1 => RTSeq s s1
  | ActiveCallCtx v c_id cr_id => RTActiveCall v s c_id cr_id
  end.

Fixpoint to_rtstmt (stk_id : stack_id) (s : stmt) :=
match s with
| Seq s1 s2 => RTSeq (to_rtstmt stk_id s1) (to_rtstmt stk_id s2)
(* | Return (e : expr) *)
| IfS e s1 s2 => RTIfS e (to_rtstmt stk_id s1) (to_rtstmt stk_id s2) stk_id
| Assign v e => RTAssign v e stk_id
(* | Free (e : expr) *)
| SkipS => RTSkipS stk_id
| StuckS => RTStuckS (* stuck statement *)
(* | ExprS (e : expr) *)
| Call v proc args => RTCall v proc args stk_id 
| FldWr v fld e => RTFldWr v fld e stk_id
| FldRd v e fld => RTFldRd v e fld stk_id
| CAS v e1 fld e2 e3 => RTCAS v e1 fld e2 e3 stk_id
| Alloc v fs => RTAlloc v fs stk_id
| Spawn proc args => RTSpawn proc args stk_id
end
.

Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NotBoolOp, LitBool b => Some (LitBool (negb b))
  | NegOp, LitInt i => Some (LitInt (-i))
  | RAValidOp, LitRAElem (existT r x) => Some (LitBool (bool_decide (valid x)))
  | _, _ => None
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  match op, v1, v2 with
  | AddOp, LitInt i1, LitInt i2 => Some (LitInt (i1 + i2))
  | SubOp, LitInt i1, LitInt i2 => Some (LitInt (i1 - i2))
  | MulOp, LitInt i1, LitInt i2 => Some (LitInt (i1 * i2))
  | DivOp, LitInt i1, LitInt i2 => Some (LitInt (i1 / i2))
  | ModOp, LitInt i1, LitInt i2 => Some (LitInt (i1 mod i2))
  | EqOp, v1, v2 => Some (LitBool (bool_decide (v1 = v2)))
  | NeOp, v1, v2 => Some (LitBool (bool_decide (v1 ≠ v2)))
  | LtOp, LitInt i1, LitInt i2 => Some (LitBool (Z.ltb i1 i2))
  | GtOp, LitInt i1, LitInt i2 => Some (LitBool (Z.ltb i2 i1))
  | LeOp, LitInt i1, LitInt i2 => Some (LitBool (Z.leb i1 i2))
  | GeOp, LitInt i1, LitInt i2 => Some (LitBool (Z.leb i2 i1))
  | AndOp, LitBool b1, LitBool b2 => Some (LitBool (b1 && b2))
  | OrOp, LitBool b1, LitBool b2 => Some (LitBool (b1 || b2))
  | RACompOp, LitRAElem (existT r1 x1), LitRAElem (existT r2 x2) =>
      match decide (r1 = r2) with
      | left Heq => Some (LitRAElem (existT r1 (comp x1 (eq_rect r2 (fun n => RA_carrier (ra_map n)) x2 r1 (eq_sym Heq)))))
      | right _ => None
      end
  | RAFrameOp, LitRAElem (existT r1 x1), LitRAElem (existT r2 x2) =>
      match decide (r1 = r2) with
      | left Heq => Some (LitRAElem (existT r1 (frame x1 (eq_rect r2 (fun n => RA_carrier (ra_map n)) x2 r1 (eq_sym Heq)))))
      | right _ => None
      end
  | RAFpuValidOp, LitRAElem (existT r1 x1), LitRAElem (existT r2 x2) =>
      match decide (r1 = r2) with
      | left Heq => Some (LitBool (bool_decide (fpuValid x1 (eq_rect r2 (fun n => RA_carrier (ra_map n)) x2 r1 (eq_sym Heq)))))
      | right _ => None
      end
  | _, _, _ => None
  end.

(* "Same RA" closed-form reductions of un_op_eval/bin_op_eval, for when both
   operands are already known to share one concrete r (as opposed to two
   independently-destructed r1/r2 that merely happen to be propositionally
   equal): un_op_eval/bin_op_eval's own `decide (r1 = r2)` doesn't reduce by
   computation on an abstract r, since decide needs concrete arguments to
   run -- UIP_dec is what lets an arbitrary proof of r = r collapse the
   eq_rect regardless. *)
Lemma un_op_eval_ra_valid (r : ra_name) (x : RA_carrier (ra_map r)) :
  un_op_eval RAValidOp (LitRAElem (existT r x)) = Some (LitBool (bool_decide (valid x))).
Proof. reflexivity. Qed.

Lemma bin_op_eval_ra_comp (r : ra_name) (x1 x2 : RA_carrier (ra_map r)) :
  bin_op_eval RACompOp (LitRAElem (existT r x1)) (LitRAElem (existT r x2))
  = Some (LitRAElem (existT r (comp x1 x2))).
Proof.
  simpl. destruct (decide (r = r)) as [Heq | Hne]; [ | exfalso; apply Hne; reflexivity].
  rewrite (Eqdep_dec.UIP_dec (fun a b => decide (a = b)) Heq eq_refl). reflexivity.
Qed.

Lemma bin_op_eval_ra_frame (r : ra_name) (x1 x2 : RA_carrier (ra_map r)) :
  bin_op_eval RAFrameOp (LitRAElem (existT r x1)) (LitRAElem (existT r x2))
  = Some (LitRAElem (existT r (frame x1 x2))).
Proof.
  simpl. destruct (decide (r = r)) as [Heq | Hne]; [ | exfalso; apply Hne; reflexivity].
  rewrite (Eqdep_dec.UIP_dec (fun a b => decide (a = b)) Heq eq_refl). reflexivity.
Qed.

Lemma bin_op_eval_ra_fpuvalid (r : ra_name) (x1 x2 : RA_carrier (ra_map r)) :
  bin_op_eval RAFpuValidOp (LitRAElem (existT r x1)) (LitRAElem (existT r x2))
  = Some (LitBool (bool_decide (fpuValid x1 x2))).
Proof.
  simpl. destruct (decide (r = r)) as [Heq | Hne]; [ | exfalso; apply Hne; reflexivity].
  rewrite (Eqdep_dec.UIP_dec (fun a b => decide (a = b)) Heq eq_refl). reflexivity.
Qed.

(* Expression evaluation *)
Inductive expr_step : expr → stack_frame → expr → Prop :=
| ExprRefl e stk_frame :
  expr_step e stk_frame e
| VarStep stk_frame x v :
    stk_frame.(locals) !! x = Some v ->
    expr_step (Var x) stk_frame ((Val v))
| UnOpStep stk_frame op e v v' :
    expr_step e stk_frame (Val v) ->
    un_op_eval op v = Some v' ->
    expr_step (UnOp op e) stk_frame ((Val v'))
| BinOpStep stk_frame op e1 e2 v1 v2 v :
    expr_step e1 stk_frame (Val v1) ->
    expr_step e2 stk_frame (Val v2) ->
    bin_op_eval op v1 v2 = Some v ->
    expr_step (BinOp op e1 e2) stk_frame ((Val v))
| IfETrueStep stk_frame v e1 e2 :
    v = (LitBool true) ->
    expr_step (IfE (Val v) e1 e2) stk_frame (e1)
| IfEFalseStep stk_frame v e1 e2 :
    v = (LitBool false) ->
    expr_step (IfE (Val v) e1 e2) stk_frame (e2)
| IfETrueEvalStep stk_frame e1 e2 e3 v2 :
    expr_step e1 stk_frame (Val (LitBool true)) ->
    expr_step e2 stk_frame (Val v2) ->
    expr_step (IfE e1 e2 e3) stk_frame (Val v2)
| IfEFalseEvalStep stk_frame e1 e2 e3 v3 :
    expr_step e1 stk_frame (Val (LitBool false)) ->
    expr_step e3 stk_frame (Val v3) ->
    expr_step (IfE e1 e2 e3) stk_frame (Val v3).

(* Pairs a declaration list's names with a same-length value list,
   positionally -- the shape a fresh stack frame's association list is
   built out of, whether from a procedure's args or its locals. *)
Definition decls_zip_vals {A} (decls : list (var * typ)) (vals : list A) : list (var * A) :=
  zip (map fst decls) vals.

Inductive runtime_step : runtime_stmt → state → list Empty_set → runtime_stmt → state → list runtime_stmt → Prop :=
| RTIfTStep σ stk_id stk_frm e s1 s2 s_next σ' efs:
  σ.(stack) !! stk_id = Some stk_frm ->
  expr_step e stk_frm (Val (LitBool true)) ->
  (∃ e1' e2' K, s1 = foldl (flip fill_item) e1' K /\ s_next = foldl (flip fill_item) e2' K /\ runtime_step e1' σ [] e2' σ' efs)  ->
  (* prim_step s1 σ [] s_next σ' ls -> *)
  runtime_step (RTIfS e s1 s2 stk_id) σ [] s_next σ' efs

| RTIfFStep σ stk_id stk_frm e s1 s2 s_next σ' efs:
  σ.(stack) !! stk_id = Some stk_frm ->
  expr_step e stk_frm (Val (LitBool false)) ->
  (∃ e1' e2' K, s2 = foldl (flip fill_item) e1' K /\ s_next = foldl (flip fill_item) e2' K /\ runtime_step e1' σ [] e2' σ' efs)  ->
  (* prim_step s2 σ [] s_next σ' ls -> *)
  runtime_step (RTIfS e s1 s2 stk_id) σ [] s_next σ' efs

| RTIfValStep σ stk_id stk_frm e s1 s2 b: 
  σ.(stack) !! stk_id = Some stk_frm ->
  expr_step e stk_frm (Val (LitBool b)) ->
  (match b, s1, s2 with
  | true, RTVal _, _ => True
  | false, _, RTVal _ => True
  | _, _, _ => False
  end) ->
  runtime_step (RTIfS e s1 s2 stk_id) σ [] (if b then s1 else s2) σ []
  
(* | RTIfSStep σ stk_id stk_frm e s1 s2 b :
  σ.(stack) !! stk_id = Some stk_frm ->
  expr_step e stk_frm (Val (LitBool b)) ->
  runtime_step (RTIfS e s1 s2 stk_id) σ [] (if b then s1 else s2) σ [] *)

| RTAssignStep σ stk_id stk_frm var e v :
  σ.(stack) !! stk_id = Some stk_frm ->
  expr_step e stk_frm (Val v) ->
  let σ' := update_lvar σ var  stk_id v in
  runtime_step (RTAssign var e stk_id) σ [] (RTVal LitUnit) σ' []

| RTSkipStep σ stk_id :
  runtime_step (RTSkipS stk_id) σ [] (RTVal LitUnit) σ []

| RTCallStep σ stk_id stk_frm v proc args arg_vals procedure local_vals :
  σ.(stack) !! stk_id = Some stk_frm ->
  σ.(procs) !! proc = Some procedure ->
  length procedure.(proc_args) = length args ->
  Forall2 (fun expr val => expr_step expr stk_frm (Val val)) args arg_vals ->
  "#ret_val" ∈ (map fst procedure.(proc_local_vars)) ->
  Forall2 (fun decl val => val_has_typ val (snd decl)) procedure.(proc_local_vars) local_vals ->
  let (new_stk_id, σ') := fresh_stk_id σ in
  (* Every local variable (including "#ret_val") is present, with some
     non-deterministically chosen value of its declared type, in every stack
     frame from the moment it is created -- the frame's variable slots are
     fixed for the whole body, so they must all be allocated up front; the
     body is expected to overwrite each before it is actually read. Args are
     listed first so a (disallowed) name clash would still favor the
     caller-supplied argument value. *)
  let new_stk_frame := StackFrame
      (list_to_map (decls_zip_vals procedure.(proc_args) arg_vals
                    ++ decls_zip_vals procedure.(proc_local_vars) local_vals))
    in
  let σ'' := update_stack σ' new_stk_id new_stk_frame in
  let new_stmt := to_rtstmt new_stk_id procedure.(proc_stmt) in
  runtime_step (RTCall v proc args stk_id) σ []
  (RTActiveCall v new_stmt new_stk_id stk_id) σ'' []

| FldWrStep σ stk_id stk_frm v fld e l val:
  σ.(stack) !! stk_id = Some stk_frm ->
  stk_frm.(locals) !! v = Some (LitLoc l) ->
  expr_step e stk_frm (Val val) ->
  let σ' := update_heap σ l fld val in
  runtime_step (RTFldWr v fld e stk_id) σ [] (RTVal LitUnit) σ' []

| FldRdStep σ stk_id stk_frm v e fld l v2 :
  σ.(stack) !! stk_id = Some stk_frm ->
  expr_step e stk_frm (Val (LitLoc l)) ->
  lookup_heap σ l fld = Some v2 ->
  let σ' := update_lvar σ v stk_id v2 in
  runtime_step (RTFldRd v e fld stk_id) σ [] (RTVal LitUnit) σ' []

| CASSuccStep σ stk_id stk_frm v e1 fld e2 e3 l v2 v3 :
  σ.(stack) !! stk_id = Some stk_frm ->
  expr_step e1 stk_frm (Val (LitLoc l)) ->
  expr_step e2 stk_frm (Val v2) ->
  expr_step e3 stk_frm (Val v3) ->
  lookup_heap σ l fld = Some v2 ->
  let σ' := update_heap σ l fld v3 in
  let σ'' := update_lvar σ' v stk_id (LitBool true) in
  runtime_step (RTCAS v e1 fld e2 e3 stk_id) σ [] (RTVal LitUnit) σ'' []

| CASFailStep σ stk_id stk_frm v e1 fld e2 e3 l v0 v2 :
  σ.(stack) !! stk_id = Some stk_frm ->expr_step e1 stk_frm (Val (LitLoc l)) ->
  expr_step e2 stk_frm (Val v2) ->
  lookup_heap σ l fld = Some v0 ->
  not (v0 = v2) ->
  let σ' := update_lvar σ v stk_id (LitBool false) in
  runtime_step (RTCAS v e1 fld e2 e3 stk_id) σ [] (RTVal LitUnit) σ' []

| AllocStep σ stk_id v fs :
  let l := fresh_loc σ.(global_heap) in
  let σ' := (foldr (fun f_v acc => update_heap acc l (fst f_v) (snd f_v)) σ fs) in
  let σ'' := update_lvar σ' v stk_id (LitLoc l) in
  runtime_step (RTAlloc v fs stk_id) σ [] (RTVal LitUnit) σ'' []

| SpawnStep σ stk_id stk_frm proc args arg_vals procedure local_vals :
  σ.(stack) !! stk_id = Some stk_frm ->
  σ.(procs) !! proc = Some procedure ->
  length procedure.(proc_args) = length args ->
  Forall2 (fun expr val => expr_step expr stk_frm (Val val)) args arg_vals ->
  "#ret_val" ∈ (map fst procedure.(proc_local_vars)) ->
  Forall2 (fun decl val => val_has_typ val (snd decl)) procedure.(proc_local_vars) local_vals ->
  let (new_stk_id, σ') := fresh_stk_id σ in
  let new_stk_frame := StackFrame
      (list_to_map (decls_zip_vals procedure.(proc_args) arg_vals
                    ++ decls_zip_vals procedure.(proc_local_vars) local_vals))
  in
  let new_stmt := to_rtstmt new_stk_id procedure.(proc_stmt) in
  let σ'' := update_stack σ' new_stk_id new_stk_frame in
  runtime_step (RTSpawn proc args stk_id) σ [] (RTVal LitUnit) σ'' [new_stmt]

| ActiveCallStep σ callee_stk_id caller_stk_id var value callee_stack ret_val:
  σ.(stack) !! callee_stk_id = Some callee_stack ->
  callee_stack.(locals) !! "#ret_val" = Some ret_val ->
  let σ' := update_lvar σ var caller_stk_id ret_val in
  runtime_step (RTActiveCall var (RTVal value) callee_stk_id caller_stk_id) σ []
  (RTVal LitUnit) σ' []

| SeqStep σ v s2:
  runtime_step (RTSeq (RTVal v) s2) σ [] s2 σ []

  .

End semantics.

Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma val_base_stuck e1 σ1 κ e2 σ2 efs : runtime_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma base_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  runtime_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof. destruct Ki1, Ki2; naive_solver eauto with f_equal. Qed.

Lemma simp_lang_mixin : EctxiLanguageMixin of_val to_val fill_item runtime_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_base_stuck,
    fill_item_val, fill_item_no_val_inj, base_ctx_step_val.
Qed.

Canonical Structure simp_ectxi_lang := EctxiLanguage simp_lang_mixin.
Canonical Structure simp_ectx_lang := EctxLanguageOfEctxi simp_ectxi_lang.
Canonical Structure simp_lang := LanguageOfEctx simp_ectx_lang.

(* Check (@step simp_lang).

Eval compute in cfg simp_lang. *)

Canonical Structure valO := leibnizO val.
Canonical Structure stack_frameO := leibnizO stack_frame.

Lemma expr_step_val_unique e stk_frm v v0:
  expr_step e stk_frm (Val v) ->
  expr_step e stk_frm (Val v0) ->
  v = v0.
Proof.
  (* High-level plan: structural induction on expression e.
     For each syntactic form, we invert both derivations H1 and H2.
     The key observations are:
       - ExprRefl can only produce a Val output when e itself is a Val,
         making both outputs trivially equal.
       - VarStep is deterministic: the same local-variable lookup returns
         the same value.
       - UnOpStep/BinOpStep: determinism follows from the IH on the
         sub-expression(s), combined with the fact that un_op_eval /
         bin_op_eval are total functions (no side-effects or non-det).
       - IfETrueStep/IfEFalseStep: the condition is already fully evaluated
         to a concrete LitBool, so both H1 and H2 must take the same
         branch.  A cross-branch pair (true in H1, false in H2) is
         impossible because it would require LitBool true = LitBool false.
       - StuckE: ExprRefl would require StuckE = Val _, a contradiction
         that Rocq closes automatically on inversion. *)
  rename v into vA. rename v0 into vB.
  revert stk_frm vA vB.
  induction e; intros stk_frm vA vB H1 H2.

  - (* Var x: ExprRefl would give Var x = Val _, impossible.
       Both derivations must be VarStep, looking up the same key
       in the same frame, so the results are equal by congruence. *)
    inversion H1; subst.
    inversion H2; subst.
    congruence.

  - (* Val v: only ExprRefl applies (no other rule matches Val _),
       giving vA = v and vB = v, hence vA = vB. *)
    inversion H1; subst.
    inversion H2; subst.
    reflexivity.

  - (* UnOp op e_inner: only UnOpStep can produce a Val output
       (ExprRefl would give UnOp _ _ = Val _, impossible).
       Both derivations evaluate the inner expression to some val;
       the IH shows those inner vals agree.  Since un_op_eval is a
       function, the outer results also agree. *)
    inversion H1; subst.
    inversion H2; subst.
    assert (Hinner : v = v0) by (eapply IHe; eassumption).
    subst. congruence.

  - (* BinOp op e1 e2: only BinOpStep applies.
       Apply IHe1 and IHe2 to unify the two pairs of operand values,
       then bin_op_eval being a function closes the goal. *)
    inversion H1; subst.
    inversion H2; subst.
    assert (Hl : v1 = v0) by (eapply IHe1; eassumption).
    assert (Hr : v2 = v3) by (eapply IHe2; eassumption).
    subst. congruence.

  - (* IfE e1 e2 e3:
       Possible Val-producing rules: IfETrueStep, IfEFalseStep,
       IfETrueEvalStep, IfEFalseEvalStep.
       Cross-branch cases are contradicted by IHe1 (condition uniqueness).
       Same-branch cases use the IH on the chosen branch. *)
    inversion H1; subst.
    + (* H1: IfETrueStep — e1 = Val (LitBool true), e2 = Val vA *)
      inversion H2; subst.
      * reflexivity.
      * discriminate.
      * (* IfETrueEvalStep: expr_step e2 frm (Val vB) *)
        eapply IHe2; [apply ExprRefl | eassumption].
      * (* IfEFalseEvalStep: expr_step (Val (LitBool true)) frm (Val (LitBool false)) *)
        exfalso.
        assert (LitBool true = LitBool false) by (eapply IHe1; [apply ExprRefl | eassumption]).
        discriminate.
    + (* H1: IfEFalseStep — e1 = Val (LitBool false), e3 = Val vA *)
      inversion H2; subst.
      * discriminate.
      * reflexivity.
      * (* IfETrueEvalStep: expr_step (Val (LitBool false)) frm (Val (LitBool true)) *)
        exfalso.
        assert (LitBool false = LitBool true) by (eapply IHe1; [apply ExprRefl | eassumption]).
        discriminate.
      * (* IfEFalseEvalStep: expr_step e3 frm (Val vB) *)
        eapply IHe3; [apply ExprRefl | eassumption].
    + (* H1: IfETrueEvalStep — eval e1 → true, eval e2 → vA *)
      inversion H2; subst.
      * (* IfETrueStep: e1 = Val true, e2 = Val vB *)
        eapply IHe2; [eassumption | apply ExprRefl].
      * (* IfEFalseStep: e1 = Val false, contradicts true *)
        exfalso.
        assert (LitBool true = LitBool false) by (eapply IHe1; [eassumption | apply ExprRefl]).
        discriminate.
      * (* IfETrueEvalStep *)
        eapply IHe2; eassumption.
      * (* IfEFalseEvalStep: condition evaluates to both true and false *)
        exfalso.
        assert (LitBool true = LitBool false) by (eapply IHe1; eassumption).
        discriminate.
    + (* H1: IfEFalseEvalStep — eval e1 → false, eval e3 → vA *)
      inversion H2; subst.
      * (* IfETrueStep: e1 = Val true, contradicts false *)
        exfalso.
        assert (LitBool false = LitBool true) by (eapply IHe1; [eassumption | apply ExprRefl]).
        discriminate.
      * (* IfEFalseStep: e1 = Val false, e3 = Val vB *)
        eapply IHe3; [eassumption | apply ExprRefl].
      * (* IfETrueEvalStep: condition evaluates to both false and true *)
        exfalso.
        assert (LitBool false = LitBool true) by (eapply IHe1; eassumption).
        discriminate.
      * (* IfEFalseEvalStep *)
        eapply IHe3; eassumption.

  - (* StuckE: ExprRefl would require StuckE = Val vA, a contradiction.
       Rocq resolves this automatically on inversion. *)
    inversion H1; subst.
Qed.


Lemma Forall2_expr_step_val_unique :
  ∀ args stk_frm vals1 vals2,
  Forall2 (λ e v, expr_step e stk_frm (Val v)) args vals1 →
  Forall2 (λ e v, expr_step e stk_frm (Val v)) args vals2 →
  vals1 = vals2.
Proof.
  induction args; intros stk_frm vals1 vals2 H1 H2.
  - inversion H1; inversion H2; reflexivity.
  - inversion H1; inversion H2; subst.
    f_equal.
    + eapply expr_step_val_unique; eauto.
    + eapply IHargs; eauto.
Qed.

Lemma fill_not_if e1 e0 s e s1 s2 stk_id:
  fill e1 (fill_item e0 s) <> (RTIfS e s1 s2 stk_id).
Proof.
    revert e0 s. 
    induction e1.
    - intros. destruct e0; try discriminate; try contradiction.
    - simpl in *. intros. apply IHe1.
Qed. 

Lemma fill_if_empty K e1' e s1 s2 stk_id:
  RTIfS e s1 s2 stk_id = fill K e1' -> K = [].
Proof.
  intros.
  destruct K; try done.
  simpl in *. 
  pose proof (fill_not_if K e0 e1' e s1 s2 stk_id). symmetry in H. contradiction.
Qed.

Lemma fill_not_val e1 e0 s v1:
    fill e1 (fill_item e0 s) <> (RTVal v1).
  Proof.
      revert e0 s. 
      induction e1.
      - intros. destruct e0; try discriminate; try contradiction.
      - simpl in *. intros. apply IHe1.
  Qed.

Lemma fill_val_empty K e1' v:
  RTVal v = fill K e1' -> K = [].
Proof.
  intros.
  destruct K; try done.
  simpl in *. 
  pose proof (fill_not_val K e e1' v). symmetry in H. contradiction.
Qed.

Definition is_atomic_redex (r : runtime_stmt) : Prop :=
  match r with
  | RTAssign _ _ _ => True
  | RTSkipS _ => True
  | RTStuckS => True
  | RTFldWr _ _ _ _ => True
  | RTFldRd _ _ _ _ => True
  | RTCAS _ _ _ _ _ _ => True
  | RTAlloc _ _ _ => True
  | RTSpawn _ _ _ => True
  | _ => False
  end.

Lemma fill_not_atomic e1 e0 s r:
  is_atomic_redex r ->
  fill e1 (fill_item e0 s) <> r.
Proof. 
  revert e0 s. 
  induction e1.
  - intros. destruct e0; destruct r; simpl in *; try discriminate; try contradiction.
  - simpl in *. intros. apply IHe1. apply H.
Qed.

Lemma fill_atomic_empty K e1 r:
  is_atomic_redex r ->
  r = fill K e1 -> K = [].
Proof.
  intros.
  destruct K; try done.
  simpl in *. 
  pose proof (fill_not_atomic K e e1 r H). symmetry in H0. contradiction.
Qed.


Lemma atomic_assign x e stk_id :
  Atomic WeaklyAtomic (RTAssign x e stk_id).
Proof.
  unfold Atomic. intros.
  inversion H.

  destruct K.
  + simpl in *; subst. inversion H2. apply val_irreducible. simpl. done.
  + simpl in *.
    pose proof (fill_not_atomic K e0 e1' (RTAssign x e stk_id)).
    simpl in H3.
    specialize (H3 I).
    symmetry in H0. contradiction.
Qed.

Lemma atomic_fld_wr v fld e stk_id : 
  Atomic WeaklyAtomic (to_rtstmt stk_id (lang.FldWr v fld e)).
Proof.
  unfold Atomic. intros.
  inversion H.

  (* inversion H2; try discriminate. *)
  destruct K eqn:HK.
  + simpl in *. subst. inversion H2. apply val_irreducible. simpl. done.
  + simpl in *.
    pose proof (fill_not_atomic e1 e0 e1' (RTFldWr v fld e stk_id)); simpl in *.
    specialize (H3 I).
    symmetry in H0. contradiction.
Qed.

Lemma atomic_skip stk_id :
  Atomic WeaklyAtomic (RTSkipS stk_id).
Proof.
  unfold Atomic. intros.
  inversion H.

  destruct K.
  + simpl in *; subst. inversion H2. apply val_irreducible. simpl. done.
  + simpl in *.
    pose proof (fill_not_atomic K e e1' (RTSkipS stk_id)).
    simpl in H3.
    specialize (H3 I).
    symmetry in H0. contradiction.
Qed.

Lemma atomic_stuck :
  Atomic WeaklyAtomic RTStuckS.
Proof.
  unfold Atomic. intros.
  inversion H.

  destruct K.
  + simpl in *; subst. inversion H2.
  + simpl in *.
    pose proof (fill_not_atomic K e e1' RTStuckS).
    simpl in H3.
    specialize (H3 I).
    symmetry in H0. contradiction.
Qed.

Lemma atomic_fld_rd v e fld stk_id :
  Atomic WeaklyAtomic (RTFldRd v e fld stk_id).
Proof.
  unfold Atomic. intros.
  inversion H.

  destruct K.
  + simpl in *; subst. inversion H2. apply val_irreducible. simpl. done.
  + simpl in *.
    pose proof (fill_not_atomic K e0 e1' (RTFldRd v e fld stk_id)).
    simpl in H3.
    specialize (H3 I).
    symmetry in H0. contradiction.
Qed.

Lemma atomic_cas v e1 fld e2 e3 stk_id :
  Atomic WeaklyAtomic (RTCAS v e1 fld e2 e3 stk_id).
Proof.
  unfold Atomic. intros.
  inversion H.

  destruct K.
  + simpl in *; subst. inversion H2.
    ++ apply val_irreducible. simpl. done.
    ++ apply val_irreducible. simpl. done.
  + simpl in *.
    pose proof (fill_not_atomic K e e1' (RTCAS v e1 fld e2 e3 stk_id)).
    simpl in H3.
    specialize (H3 I).
    symmetry in H0. contradiction.
Qed.

Lemma atomic_alloc v fs stk_id :
  Atomic WeaklyAtomic (RTAlloc v fs stk_id).
Proof.
  unfold Atomic. intros.
  inversion H.

  destruct K.
  + simpl in *; subst. inversion H2. apply val_irreducible. simpl. done.
  + simpl in *.
    pose proof (fill_not_atomic K e e1' (RTAlloc v fs stk_id)).
    simpl in H3.
    specialize (H3 I).
    symmetry in H0. contradiction.
Qed.

Lemma atomic_spawn proc args stk_id :
  Atomic WeaklyAtomic (RTSpawn proc args stk_id).
Proof.
  unfold Atomic. intros.
  inversion H.

  destruct K.
  + simpl in *; subst. inversion H2. apply val_irreducible. simpl. done.
  + simpl in *.
    pose proof (fill_not_atomic K e e1' (RTSpawn proc args stk_id)).
    simpl in H3.
    specialize (H3 I).
    symmetry in H0. contradiction.
Qed.

Lemma obs_list_empty s1 σ x e' σ' efs: @prim_step simp_ectx_lang  s1 σ x e' σ' efs -> x = [].
Proof.
  intros.
  destruct H.
  destruct H1; done.
Qed.