From Coq Require Import Ascii ClassicalEpsilon List String ZArith
  Program.Equality.
From stdpp Require Import namespaces sets.
From iris.base_logic.lib Require iprop invariants fancy_updates.
From iris.proofmode Require proofmode.

From raven Require Import runtime.erasure analysis.structured_certificates examples.mono_nat_ra surface.syntax surface.elaboration verification.expressions verification.assertions verification.ir verification.procedures analysis.normalization_base analysis.normalization soundness.runtime_model soundness.rule_validity soundness.procedure_validity soundness.adequacy verification.snapshots.

Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

(** The monotonic counter, verified end to end.

    This file deliberately starts from Raven-like surface syntax; the typed
    Hoare derivations, analysis, normalization, and procedure-validity
    witnesses below are all stated against the elaborated module. *)
Module CounterMonotonic.

Definition x := name "x".
Definition v1 := name "v1".
Definition v2 := name "v2".
Definition new_v1 := name "new_v1".
Definition res := name "res".
Definition call_res := name "call_res".
Definition ret := name "ret".
Definition c := name "c".
Definition h := name "h".
Definition v := name "v".
Definition counterInv := name "counterInv".
Definition incr := name "incr".

Definition read := name "read".
Definition make := name "make".
Definition client := name "client".

(** The counter module, in Raven syntax.  Everything the verification needs
    is derived from it: the logic signature, the elaboration environment, the
    identifiers, the typed procedures with their variable layouts and
    contracts, the procedure table and the contract environment.

    In [incr], the second access is closed in each branch of the
    conditional after the atomic block: after the ghost update on success,
    and before the retry on failure. *)
Definition CounterRA : source_typ := SNamed h_ra.

Definition counter_declarations : source_module :=
  raven_module {{
      field c : Int
      field h : CounterRA

      inv counterInv(x : Ref) {
        exists v : Int :: own(x . h, v) && own(x . c, v)
      }

      proc read(x : Ref) returns (ret : Int)
        requires counterInv(x)
      {
        var v1 : Int;
        atomic {
          unfold counterInv(x);
          v1 := x . c;
          fold counterInv(x)
        };
        ret := v1
      }

      proc incr(x : Ref)
        requires counterInv(x)
      {
        var v1 : Int;
        var new_v1 : Int;
        var v2 : Int;
        var res : Bool;
        var call_res : Unit;
        unfold counterInv(x);
        v1 := x . c;
        fold counterInv(x);
        new_v1 := v1 + 1;
        unfold counterInv(x);
        atomic {
          v2 := x . c;
          if (v2 == v1) {
            x . c := new_v1;
            res := true
          } else {
            res := false
          }
        };
        if (res) {
          fpu(x . h, v1, v1 + 1);
          fold counterInv(x)
        } else {
          fold counterInv(x);
          incr(x)
        }
      }

      proc make() returns (ret : Ref)
        ensures counterInv(ret)
      {
        val x : Ref := new(c: 0, h: 0);
        fold counterInv(x);
        ret := x
      }

      proc client() returns (ret : Ref)
        ensures true
      {
        var v1 : Int;
        ret := make();
        spawn incr(ret);
        v1 := read(ret)
      }
  }}.

(** The logic signature, the elaboration environment, and the identifiers
    used below are read off the declarations. *)
Definition counter_logic : Assertion.LogicSignature :=
  Eval vm_compute in Elaboration.module_signature counter_declarations.
Definition counter_environment : Elaboration.elaboration_environment :=
  Elaboration.module_environment counter_declarations.

Definition counter_field : Core.field_id :=
  Eval vm_compute in Elaboration.field_identity_of counter_declarations c.
Definition ghost_field : Core.field_id :=
  Eval vm_compute in Elaboration.field_identity_of counter_declarations h.
Definition counter_invariant : Core.inv_id :=
  Eval vm_compute in
    Elaboration.invariant_identity_of counter_declarations counterInv.
Definition read_procedure : Core.proc_id :=
  Eval vm_compute in Elaboration.procedure_identity_of counter_declarations read.
Definition incr_procedure : Core.proc_id :=
  Eval vm_compute in Elaboration.procedure_identity_of counter_declarations incr.
Definition make_procedure : Core.proc_id :=
  Eval vm_compute in Elaboration.procedure_identity_of counter_declarations make.
Definition client_procedure : Core.proc_id :=
  Eval vm_compute in
    Elaboration.procedure_identity_of counter_declarations client.

Lemma counter_field_type_eq :
  @Assertion.field_type counter_logic counter_field = Core.TInt.
Proof. reflexivity. Qed.

Lemma ghost_field_type_eq :
  @Assertion.field_type counter_logic ghost_field = Core.TRA h_ra.
Proof. reflexivity. Qed.

Module IR := RuleValidity.IR.
Module Resource := IR.Resource.
#[local] Existing Instances CounterRAConfig.ra_config counter_logic.
Import Core IR IR.Core IR.Assertions Elaboration.

(** The elaborated module, and the typed procedures it declares. *)
Definition counter_module : RuleValidity.Hoare.module :=
  Eval vm_compute in elaborated
    (elaborate_module counter_declarations)
    ltac:(vm_compute; exact I).

Definition read_typed_procedure : typed_procedure (runtime_decls [TRef; TInt; TInt]) read_procedure :=
  Eval vm_compute in projT2 (elaborated
    (declared_procedure counter_module read_procedure) ltac:(vm_compute; exact I)).

Definition incr_typed_procedure :
    typed_procedure (runtime_decls [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit]) incr_procedure :=
  Eval vm_compute in projT2 (elaborated
    (declared_procedure counter_module incr_procedure) ltac:(vm_compute; exact I)).

Definition make_typed_procedure : typed_procedure ([runtime_val TRef; runtime_var TRef]) make_procedure :=
  Eval vm_compute in projT2 (elaborated
    (declared_procedure counter_module make_procedure) ltac:(vm_compute; exact I)).

Definition client_typed_procedure : typed_procedure (runtime_decls [TInt; TRef]) client_procedure :=
  Eval vm_compute in projT2 (elaborated
    (declared_procedure counter_module client_procedure) ltac:(vm_compute; exact I)).

Definition incr_variables := procedure_variables _ _ incr_typed_procedure.
Definition read_typed_body := procedure_body _ _ read_typed_procedure.
Definition incr_typed_body := procedure_body _ _ incr_typed_procedure.
Definition make_typed_body := procedure_body _ _ make_typed_procedure.
Definition client_typed_body := procedure_body _ _ client_typed_procedure.

Definition counter_token_core {F Δ} (location : expr F Δ TRef) :
    Resource.core_assertion F Δ :=
  Resource.CInvariant counter_invariant (ExprCons location ExprNil).

Definition counter_invariant_body_core : Resource.core_assertion [TRef] [] :=
  Eval vm_compute in
    RuleValidity.Hoare.module_invariant_body counter_module counter_invariant.

(** The atomic block is the trusted hardware component.  Its body describes
    the desired CAS behavior in Raven itself; atomicity of that whole body is
    supplied by the module contract, not derived from its small steps. *)
Definition cas_source : source_stmt :=
  raven_stmt {{
    v2 := x . c;
    if (v2 == v1) {
      x . c := new_v1;
      res := true
    } else {
      res := false
    }
  }}.

(** The sole trusted hardware component used by this program: the body of
    [incr]'s atomic block. *)
Definition cas_typed_body :
    stmt (runtime_decls [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit]) :=
  elaborated
    (elaborate_stmt counter_environment incr_variables cas_source)
    ltac:(vm_compute; exact I).

(** An explicit atomic block is Raven's trust declaration; the resource
    rule for [TAtomic] has no separate per-block trust premise to
    discharge. *)

(** Cache the intrinsic syntax produced by elaboration.  Structural proofs
    below can unfold this VM-normalized term without re-running the surface
    elaborator at every constructor boundary. *)
Definition incr_typed_body_normalized := Eval vm_compute in incr_typed_body.

Lemma incr_typed_body_normalized_eq :
  incr_typed_body = incr_typed_body_normalized.
Proof. vm_compute. reflexivity. Qed.

(** Readable aliases for the canonical stores derived from each procedure's
    formal layout.  They are definitions, not program-supplied data. *)
Definition read_entry_store :=
  procedure_entry_store _ _ read_typed_procedure.
Definition incr_entry_store :=
  procedure_entry_store _ _ incr_typed_procedure.
Definition make_entry_store :=
  procedure_entry_store _ _ make_typed_procedure.
Definition client_entry_store :=
  procedure_entry_store _ _ client_typed_procedure.

Definition counter_mask : RuleValidity.Hoare.mask := {[counter_invariant]}.

#[local] Definition counter_contracts :=
  RuleValidity.Hoare.module_contracts counter_module.
#[local] Definition counter_coherence :=
  RuleValidity.Hoare.module_coherence counter_module.
#[local] Existing Instances counter_contracts counter_coherence.

Lemma counter_invariant_body_eq :
  RuleValidity.Hoare.ResourceHoare.invariant_body counter_invariant =
    counter_invariant_body_core.
Proof. vm_compute. reflexivity. Qed.

(** Mask inference unfolds predicates.  The counter declares none, so this
    checks the mechanism on a small hypothetical declaration: predicate 1
    mentions itself and predicate 2, whose body depends on the counter
    invariant.  Each predicate is unfolded at most once along a path, so the
    recursion terminates and still finds the invariant through the nesting;
    an undeclared predicate contributes nothing. *)
Section MaskInferenceExamples.
Let bodies (predicate : pred_id) :
    Resource.core_assertion (Assertion.predicate_args predicate) [] :=
  if Pos.eqb predicate 1%positive then
    Resource.CAnd (Resource.CPredicate 1%positive ExprNil)
      (Resource.CPredicate 2%positive ExprNil)
  else Resource.CExists TRef (counter_token_core (ERef (RefBound MHere))).

Example contract_invariants_through_predicates :
  RuleValidity.Hoare.ResourceHoare.contract_invariants bodies [1%positive; 2%positive]
    (Resource.CPredicate (F := []) (Δ := []) 1%positive ExprNil) = {[counter_invariant]}.
Proof. vm_compute. reflexivity. Qed.

Example contract_invariants_undeclared_predicate :
  RuleValidity.Hoare.ResourceHoare.contract_invariants bodies [1%positive]
    (Resource.CPredicate (F := []) (Δ := []) 1%positive ExprNil) = ∅.
Proof. vm_compute. reflexivity. Qed.
End MaskInferenceExamples.

(** The generic initialized soundness theorem specialized to the counter's
    concrete names and procedure-contract table.  The remaining witnesses
    below are all program data for this single module. *)

Import RuleValidity.Hoare.

Lemma counter_formal_location_subst {F Δ}
    (location : expr F Δ TRef) :
  subst_formals_expr
      (@lift_formal_subst _ [TRef] F Δ TInt
        (expr_list_formal_subst (ExprCons location ExprNil)))
      (subst_bound_expr
        (lift_bound_subst (@empty_bound_subst _ [TRef] Δ))
        (ERef (RefFormal MHere))) =
    weaken_expr location.
Proof.
  cbn [subst_bound_expr subst_bound_ref subst_formals_expr
    subst_formals_ref].
  unfold lift_formal_subst, expr_list_formal_subst.
  rewrite lookup_expr_list_here.
  reflexivity.
Qed.

(** The body of [read] runs under the snapshot of its invariant argument,
    whose slot holds the formal once the snapshot equality is used. *)
Definition read_body_decls : decl_context :=
  ghost_val TRef :: runtime_decls [TRef; TInt; TInt].

Definition read_snapshot_store : symbolic_store read_body_decls [TRef] [] :=
  StoreCons (RefFormal MHere) read_entry_store.

Lemma read_snapshot_arguments {keep} (Hkeep : keep _ = true) :
  RuleValidity.IR.symbolize_expr_list read_snapshot_store
      (PECons (PEVar (LHere Hkeep)) PENil) =
    ExprCons (ERef (RefFormal MHere)) ExprNil.
Proof. reflexivity. Qed.

Lemma incr_entry_arguments {keep} (Hkeep : keep _ = true) :
  RuleValidity.IR.symbolize_expr_list incr_entry_store
      (PECons (PEVar (LHere Hkeep)) PENil) =
    ExprCons (ERef (RefFormal MHere)) ExprNil.
Proof. reflexivity. Qed.

Definition read_open_store : symbolic_store read_body_decls [TRef] [TInt] :=
  weaken_store read_snapshot_store.

Lemma read_open_location {keep} (Hkeep : keep _ = true) :
  RuleValidity.IR.symbolize_expr read_open_store (PEVar (LThere (LHere Hkeep))) =
    ERef (RefFormal MHere).
Proof. reflexivity. Qed.

Definition read_field_store :
    symbolic_store read_body_decls [TRef] [TInt; TInt] :=
  RuleValidity.IR.update_store_with_bound (keep := keep_runtime_var)
    read_open_store (LThere (LThere (LHere eq_refl))).

Lemma rename_bound_store_weaken_store {Γ F Δ u}
    (store : symbolic_store Γ F Δ) :
  rename_bound_store (@weaken_bound_renaming Δ u) store =
    weaken_store store.
Proof.
  induction store; cbn [rename_bound_store weaken_store].
  - reflexivity.
  - f_equal. exact IHstore.
Qed.

Lemma read_field_location {keep} (Hkeep : keep _ = true) :
  RuleValidity.IR.symbolize_expr read_field_store (PEVar (LHere Hkeep)) =
    ERef (RefFormal MHere).
Proof. reflexivity. Qed.
Lemma counter_mask_close :
  (counter_mask ∖ {[counter_invariant]}) ∪ {[counter_invariant]} =
    counter_mask.
Proof.
  unfold counter_mask. set_solver.
Qed.
Definition read_body_exit_store :
    symbolic_store read_body_decls [TRef] [TInt; TInt; TInt] :=
  RuleValidity.IR.update_store_with_bound (keep := keep_runtime_var)
    read_field_store (LThere (LThere (LThere (LHere eq_refl)))).

Definition read_exit_store :
    symbolic_store (runtime_decls [TRef; TInt; TInt]) [TRef] [TInt; TInt; TInt] :=
  store_tail read_body_exit_store.
Lemma interp_equality_same {F Δ t} (formals : formal_env F)
    (binders : binder_env Δ) valuation (expression : expr F Δ t) :
  interp_expr formals binders valuation (EBinOp (BEq t) expression expression) =
    Some (VBool true).
Proof.
  cbn [interp_expr].
  destruct (interp_expr_total formals binders valuation expression)
    as [value ->].
  cbn [interp_binop]. rewrite (proj2 (tval_eqb_eq t value value) eq_refl).
  reflexivity.
Qed.

Lemma interp_typed_equality_true_early {F Δ t}
    (formals : formal_env F) (binders : binder_env Δ) valuation
    (left right : expr F Δ t) :
  interp_expr formals binders valuation (EBinOp (BEq t) left right) =
    Some (VBool true) ->
  interp_expr formals binders valuation left =
    interp_expr formals binders valuation right.
Proof.
  cbn [interp_expr interp_binop].
  destruct (interp_expr formals binders valuation left) as [left_value|]
    eqn:Hleft; [|discriminate].
  destruct (interp_expr formals binders valuation right) as [right_value|]
    eqn:Hright; [|discriminate].
  intros Heq. injection Heq as Heq.
  fold (tval_eqb t left_value right_value) in Heq.
  apply tval_eqb_eq in Heq. subst right_value. congruence.
Qed.
Module HoareRules := RuleValidity.CertifiedNormalization.RavenHoareRules.
Module RH := RuleValidity.Hoare.ResourceHoare.

(** The Hoare rules and entailment steps at the counter's instances. *)
Module Rules.
  Notation CEntailsAndMono := (RH.CEntailsAndMono (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CEntailsExistsAndRight := (RH.CEntailsExistsAndRight (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CEntailsExistsIntro := (RH.CEntailsExistsIntro (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CEntailsRefl := (RH.CEntailsRefl (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CEntailsStep := (RH.CEntailsStep (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CEntailsTrans := (RH.CEntailsTrans (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESAndAssocL := (RH.CESAndAssocL (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESAndAssocR := (RH.CESAndAssocR (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESAndComm := (RH.CESAndComm (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESAndElimL := (RH.CESAndElimL (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESAndTrueIntro := (RH.CESAndTrueIntro (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESExprImpl := (RH.CESExprImpl (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESFpuAllowedTrue := (RH.CESFpuAllowedTrue (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESGhostOwnChunkEqAssume := (RH.CESGhostOwnChunkEqAssume (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESInvariantArgumentsEqAssume := (RH.CESInvariantArgumentsEqAssume (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESIteFalse := (RH.CESIteFalse (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESIteIntroFalse := (RH.CESIteIntroFalse (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESIteIntroTrue := (RH.CESIteIntroTrue (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESIteTrue := (RH.CESIteTrue (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESRAValidTrue := (RH.CESRAValidTrue (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESTrueIntro := (RH.CESTrueIntro (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation resource_prenex_entails_refl := (RH.resource_prenex_entails_refl (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation RPEBody := (RH.RPEBody (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation RPEMono := (RH.RPEMono (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation RPEOpenCoreExists := (RH.RPEOpenCoreExists (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation RPETrans := (RH.RPETrans (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation RPEVacuous := (RH.RPEVacuous (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation RTAlloc := (HoareRules.RTAlloc (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTAssign := (HoareRules.RTAssign (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTAtomicBlock := (HoareRules.RTAtomicBlock (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTCallStore := (HoareRules.RTCallStore (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTSpawn := (HoareRules.RTSpawn (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation CESDuplicate := (RH.CESDuplicate (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation CESAndElimR := (RH.CESAndElimR (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic)).
  Notation RTCallDiscard := (HoareRules.RTCallDiscard (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTConsequence := (HoareRules.RTConsequence (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTDone := (HoareRules.RTDone (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTFieldRead := (HoareRules.RTFieldRead (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTFieldWrite := (HoareRules.RTFieldWrite (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTFoldInvariant := (HoareRules.RTFoldInvariant (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTFrame := (HoareRules.RTFrame (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTGhostUpdate := (HoareRules.RTGhostUpdate (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTIf := (HoareRules.RTIf (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTPostOpenCoreExists := (HoareRules.RTPostOpenCoreExists (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTAssertTrue := (HoareRules.RTAssertTrue (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTGhostValVar := (HoareRules.RTGhostValVar (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTGhostVal := (HoareRules.RTGhostVal (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTStackRewrite := (HoareRules.RTStackRewrite (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTBoundWeaken := (HoareRules.RTBoundWeaken (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTPrenexConsequence := (HoareRules.RTPrenexConsequence (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTPrenexPreserve := (HoareRules.RTPrenexPreserve (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTSeq := (HoareRules.RTSeq (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation RTUnfoldInvariant := (HoareRules.RTUnfoldInvariant (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := counter_logic) (Contracts := counter_contracts)).
  Notation COwn := (Resource.COwn (Logic := counter_logic)).
  Notation CGhostOwn := (Resource.CGhostOwn (Logic := counter_logic)).
End Rules.

(** Binder zero is untouched by a lifted substitution.  Local renaming
    algebra; [view_member] does not reduce on its own. *)
Lemma lift_bound_subst_here {F Δ Δ' u}
    (substitution : Resource.Assertions.bound_subst F Δ Δ') :
  Resource.Assertions.lift_bound_subst (u := u) substitution u MHere =
    ERef (RefBound MHere).
Proof.
  unfold Resource.Assertions.lift_bound_subst.
  rewrite view_member_here. reflexivity.
Qed.

Lemma counter_invariant_instantiated {F Δ}
    (location : expr F Δ TRef) :
  HoareRules.instantiated_invariant counter_invariant
      (ExprCons location ExprNil) =
    Resource.CExists TInt
      (Resource.CAnd
        (Rules.CGhostOwn ghost_field (weaken_expr location)
          (EUnOp (URAOfInt h_ra) (ERef (RefBound MHere))))
        (Rules.COwn counter_field (weaken_expr location)
          (ERef (RefBound MHere)))).
Proof.
  unfold HoareRules.instantiated_invariant.
  rewrite counter_invariant_body_eq.
  unfold counter_invariant_body_core, Resource.weaken_core_to.
  cbn [Resource.subst_bound_core Resource.subst_formals_core].
  rewrite !counter_formal_location_subst.
  cbn [Assertion.field_type counter_logic counter_field
    Resource.Assertions.subst_bound_expr
    Resource.Assertions.subst_bound_ref].
  rewrite !lift_bound_subst_here.
  cbn [Resource.Assertions.subst_formals_expr
    Resource.Assertions.subst_formals_ref].
  reflexivity.
Qed.

(** The core body the counter invariant unfolds to, one binder in. *)
Definition read_open_core : Resource.core_assertion [TRef] [TInt] :=
  Resource.CAnd
    (Rules.CGhostOwn ghost_field (ERef (RefFormal MHere))
      (EUnOp (URAOfInt h_ra) (ERef (RefBound MHere))))
    (Rules.COwn counter_field (ERef (RefFormal MHere))
      (ERef (RefBound MHere))).

Lemma counter_invariant_at_formal :
  HoareRules.instantiated_invariant (F := [TRef]) (Δ := [])
      counter_invariant (ExprCons (ERef (RefFormal MHere)) ExprNil) =
    Resource.CExists TInt read_open_core.
Proof.
  rewrite (counter_invariant_instantiated (ERef (RefFormal MHere))).
  reflexivity.
Qed.

(** Slice, direction one: unfolding the invariant produces a core
    existential, which [RTPostOpenCoreExists] moves into the telescope so
    that the rest of the body can be derived under the binder. *)
Lemma read_unfold_open :
  HoareRules.RavenHoareTriple
    (Resource.RState read_snapshot_store
      (counter_token_core (ERef (RefFormal MHere))))
    (TUnfold counter_invariant (PECons (PEVar (LHere eq_refl)) PENil))
    (Resource.ResourceExists TInt
      (Resource.RState read_open_store read_open_core)).
Proof.
  unfold read_open_store.
  apply Rules.RTPostOpenCoreExists.
  unfold counter_token_core.
  change (Assertion.procedure_args read_procedure) with ([TRef] : context).
  rewrite <- counter_invariant_at_formal.
  rewrite <- (read_snapshot_arguments (keep := keep_all) eq_refl).
  apply Rules.RTUnfoldInvariant.
Qed.

(** Slice, direction two: everything after the unfold is derived *under*
    the telescope binder, by [RTPrenexPreserve].  The physical read adds a
    second binder, so the fold and the assignment run two binders in. *)
Definition read_field_core : Resource.core_assertion [TRef] [TInt; TInt] :=
  Resource.CAnd
    (Resource.CAnd
      (Rules.COwn counter_field (ERef (RefFormal MHere))
        (ERef (RefBound (MThere MHere))))
      (Resource.CExpr (EBinOp (BEq TInt) (ERef (RefBound MHere))
        (ERef (RefBound (MThere MHere))))))
    (Rules.CGhostOwn ghost_field (ERef (RefFormal MHere))
      (EUnOp (URAOfInt h_ra) (ERef (RefBound (MThere MHere))))).

Lemma read_field_read :
  HoareRules.RavenHoareTriple
    (Resource.RState read_open_store read_open_core)
    (TFieldRead false counter_field (LThere (LThere (LHere eq_refl)))
      (PEVar (LThere (LHere eq_refl))))
    (Resource.ResourceExists TInt
      (Resource.RState read_field_store read_field_core)).
Proof.
  unfold read_open_core, read_field_core, read_field_store.
  eapply Rules.RTConsequence with
    (pre_body := Resource.CAnd
      (Rules.COwn counter_field (ERef (RefFormal MHere))
        (ERef (RefBound MHere)))
      (Rules.CGhostOwn ghost_field (ERef (RefFormal MHere))
        (EUnOp (URAOfInt h_ra) (ERef (RefBound MHere))))).
  - eapply Rules.RTFrame.
    change (Assertion.field_type counter_field) with TInt.
    rewrite <- (read_open_location (keep := keep_runtime) eq_refl).
    eapply Rules.RTFieldRead.
  - apply Rules.CEntailsStep. apply Rules.CESAndComm.
  - rewrite read_open_location. apply Rules.resource_prenex_entails_refl.
Qed.
Lemma counter_invariant_at_formal_two :
  HoareRules.instantiated_invariant (F := [TRef]) (Δ := [TInt; TInt])
      counter_invariant (ExprCons (ERef (RefFormal MHere)) ExprNil) =
    Resource.CExists TInt
      (Resource.CAnd
        (Rules.CGhostOwn ghost_field (ERef (RefFormal MHere))
          (EUnOp (URAOfInt h_ra) (ERef (RefBound MHere))))
        (Rules.COwn counter_field (ERef (RefFormal MHere))
          (ERef (RefBound MHere)))).
Proof.
  rewrite (counter_invariant_instantiated (ERef (RefFormal MHere))).
  reflexivity.
Qed.

(** Refolding the invariant instantiates its binder at the *old* value,
    which after the physical read sits one binder in. *)
Lemma read_fold_instantiate :
  Resource.instantiate_bound_core
      (@ERef _ [TRef] [TInt; TInt] TInt (RefBound (MThere MHere)))
      (Resource.CAnd
        (Rules.CGhostOwn ghost_field (ERef (RefFormal MHere))
          (EUnOp (URAOfInt h_ra) (ERef (RefBound MHere))))
        (Rules.COwn counter_field (ERef (RefFormal MHere))
          (ERef (RefBound MHere)))) =
    Resource.CAnd
      (Rules.CGhostOwn ghost_field (ERef (RefFormal MHere))
        (EUnOp (URAOfInt h_ra) (ERef (RefBound (MThere MHere)))))
      (Rules.COwn counter_field (ERef (RefFormal MHere))
        (ERef (RefBound (MThere MHere)))).
Proof.
  unfold Resource.instantiate_bound_core.
  cbn [Resource.subst_bound_core Resource.Assertions.subst_bound_expr
    Resource.Assertions.subst_bound_ref].
  unfold Resource.Assertions.head_bound_subst.
  rewrite !view_member_here.
  reflexivity.
Qed.

Lemma read_fold :
  HoareRules.RavenHoareTriple
    (Resource.RState read_field_store read_field_core)
    (TFold counter_invariant (PECons (PEVar (LHere eq_refl)) PENil))
    (Resource.RState read_field_store
      (counter_token_core (ERef (RefFormal MHere)))).
Proof.
  eapply Rules.RTConsequence; [eapply Rules.RTFoldInvariant | | ].
  - cbn [RuleValidity.IR.symbolize_expr_list]. rewrite read_field_location.
    try change (Assertion.procedure_args read_procedure) with ([TRef] : context).
    rewrite counter_invariant_at_formal_two.
    eapply Rules.CEntailsTrans;
      [| apply (Rules.CEntailsExistsIntro TInt _
           (@ERef _ [TRef] [TInt; TInt] TInt (RefBound (MThere MHere))))].
    rewrite read_fold_instantiate. unfold read_field_core.
    eapply Rules.CEntailsTrans;
      [apply Rules.CEntailsAndMono;
        [apply Rules.CEntailsStep; apply Rules.CESAndElimL | apply Rules.CEntailsRefl] |].
    apply Rules.CEntailsStep. apply Rules.CESAndComm.
  - cbn [RuleValidity.IR.symbolize_expr_list]. rewrite read_field_location.
    unfold counter_token_core. apply Rules.resource_prenex_entails_refl.
Qed.

(** The generated check that the fold names the opened instance. *)
Definition read_snapshot_check : stmt read_body_decls :=
  TAssert (PEBinOp (BEq TRef) (PEVar (LHere eq_refl))
    (PEVar (LThere (LHere eq_refl)))).

(** The access, hoisted around the atomic block: the invariant is held
    across the block's one physical step. *)
Lemma read_access_derivation :
  HoareRules.RavenHoareTriple
    (Resource.RState read_snapshot_store
      (counter_token_core (ERef (RefFormal MHere))))
    (TSeq (TUnfold counter_invariant (PECons (PEVar (LHere eq_refl)) PENil))
      (TSeq
        (TAtomic (TFieldRead false counter_field (LThere (LThere (LHere eq_refl)))
          (PEVar (LThere (LHere eq_refl)))))
        (TSeq
          (TFold counter_invariant (PECons (PEVar (LHere eq_refl)) PENil))
          read_snapshot_check)))
    (Resource.ResourceExists TInt
      (Resource.ResourceExists TInt
        (Resource.RState read_field_store
          (counter_token_core (ERef (RefFormal MHere)))))).
Proof.
  eapply Rules.RTSeq; [exact read_unfold_open |].
  apply Rules.RTPrenexPreserve.
  eapply Rules.RTSeq; [apply Rules.RTAtomicBlock; exact read_field_read |].
  apply Rules.RTPrenexPreserve.
  eapply Rules.RTSeq; [exact read_fold |].
  apply Rules.RTAssertTrue. intros formals binders valuation.
  apply interp_equality_same.
Qed.

Lemma read_assign :
  HoareRules.RavenHoareTriple
    (Resource.RState (store_tail read_field_store)
      (counter_token_core (ERef (RefFormal MHere))))
    (TAssign false (LThere (LThere (LHere eq_refl)))
      (PEVar (LThere (LHere eq_refl))))
    (Resource.ResourceExists TInt
      (Resource.RState read_exit_store Resource.CTrue)).
Proof.
  eapply Rules.RTConsequence; [eapply Rules.RTAssign | | ].
  - apply Rules.CEntailsStep. apply Rules.CESTrueIntro.
  - apply Rules.RPEMono. apply Rules.RPEBody.
    split; [reflexivity | apply Rules.CEntailsStep; apply Rules.CESTrueIntro].
Qed.

Lemma read_resource_body_derivation :
  HoareRules.RavenHoareTriple
    (RuleValidity.Hoare.procedure_body_pre read_typed_procedure)
    read_typed_body
    (RuleValidity.Hoare.procedure_body_post read_typed_procedure read_exit_store
      (RefBound MHere)).
Proof.
  unfold RuleValidity.Hoare.procedure_body_pre, RuleValidity.Hoare.procedure_body_post,
    read_typed_procedure, read_typed_body.
  cbn [elaborate_stmt procedure_entry_store procedure_precondition
    procedure_postcondition RuleValidity.Hoare.existentially_close_prenex
    RuleValidity.Hoare.existentially_close_prenex_at
    Resource.subst_bound_core].
  eapply Rules.RTPrenexConsequence;
    [| apply Rules.resource_prenex_entails_refl |].
  - eapply Rules.RTSeq;
      [apply Rules.RTGhostValVar; exact read_access_derivation |].
    cbn [Resource.drop_head_prenex].
    apply Rules.RTPrenexPreserve. apply Rules.RTPrenexPreserve.
    exact read_assign.
  - apply Rules.resource_prenex_entails_refl.
Qed.

Module CounterAtomicity := RuleValidity.GenericRegions.Atomicity.

Definition counter_closed_state (available : RuleValidity.Hoare.mask) :
    CounterAtomicity.analysis_state :=
  CounterAtomicity.AnalysisState
    (CounterAtomicity.declaration_entries available) [] false false.

Definition read_exit_state : CounterAtomicity.analysis_state :=
  counter_closed_state
    ((counter_mask ∖ {[counter_invariant]}) ∪ {[counter_invariant]}).
(** The allocation in [make] creates the concrete and ghost halves of a
    fresh counter at zero. *)
Definition make_initializers : list (field_init ([runtime_val TRef; runtime_var TRef])) :=
  [FieldInit counter_field (PEVal (VInt 0%Z));
   FieldInit ghost_field
     (PEUnOp (URAOfInt h_ra) (PEVal (VInt 0%Z)))].

Definition make_alloc_store :
    symbolic_store ([runtime_val TRef; runtime_var TRef]) [] [TRef] :=
  RuleValidity.IR.update_store_with_bound (keep := keep_write true)
    make_entry_store (LHere eq_refl).

Lemma make_alloc_location {keep} (Hkeep : keep _ = true) :
  RuleValidity.IR.symbolize_expr make_alloc_store (PEVar (LHere Hkeep)) =
    ERef (RefBound MHere).
Proof. reflexivity. Qed.
Definition make_exit_store :
    symbolic_store ([runtime_val TRef; runtime_var TRef]) [] [TRef; TRef] :=
  RuleValidity.IR.update_store_with_bound (keep := keep_runtime_var) make_alloc_store (LThere (LHere eq_refl)).
Lemma make_ghost_initializers_valid :
  RH.core_entails (@Resource.CTrue _ _ [] [])
    (RH.ghost_initializers_valid_core make_entry_store
      (ghost_field_initializers make_initializers)).
Proof.
  unfold ghost_field_initializers, make_initializers.
  cbn [RH.ghost_initializers_valid_core RuleValidity.IR.symbolize_expr].
  eapply Rules.CEntailsTrans;
    [| apply Rules.CEntailsStep; apply Rules.CESAndTrueIntro].
  apply Rules.CEntailsStep. apply Rules.CESRAValidTrue.
  intros formals binders valuation value Hvalue.
  cbn in Hvalue. inversion Hvalue; subst.
  unfold RuleValidity.IR.Core.tval_ra_valid.
  cbn [mn_of_int mn_valid].
  eexists. reflexivity.
Qed.

Lemma make_alloc :
  HoareRules.RavenHoareTriple
    (Resource.RState make_entry_store Resource.CTrue)
    (TAlloc true (LHere eq_refl) make_initializers)
    (Resource.ResourceExists TRef
      (Resource.RState make_alloc_store
        (RH.allocated_fields_core make_entry_store make_initializers))).
Proof.
  unfold make_alloc_store.
  eapply Rules.RTConsequence; [eapply Rules.RTAlloc | | ].
  { unfold make_initializers, counter_field, ghost_field. cbn.
    repeat first [constructor | apply NoDup_nil | set_solver]. }
  { unfold make_initializers, ghost_field_initializers. cbn.
    repeat first [constructor | apply NoDup_nil | set_solver]. }
  { unfold ghost_initializers_require_physical, make_initializers,
      ghost_field_initializers, physical_field_initializers.
    cbn. intros _. discriminate. }
  { exact make_ghost_initializers_valid. }
  apply Rules.resource_prenex_entails_refl.
Qed.

Lemma make_allocated_to_invariant :
  RH.core_entails
    (RH.allocated_fields_core make_entry_store make_initializers)
    (HoareRules.instantiated_invariant (F := []) (Δ := [TRef])
      counter_invariant (ExprCons (ERef (RefBound MHere)) ExprNil)).
Proof.
  rewrite (counter_invariant_instantiated (ERef (RefBound MHere))).
  unfold RH.allocated_fields_core, RH.allocated_physical_fields_core,
    RH.allocated_ghost_fields_core, physical_field_initializers,
    ghost_field_initializers, make_initializers.
  cbn.
  eapply Rules.CEntailsTrans;
    [apply Rules.CEntailsAndMono; apply Rules.CEntailsStep;
     apply Rules.CESAndElimL |].
  eapply Rules.CEntailsTrans; [apply Rules.CEntailsStep; apply Rules.CESAndComm |].
  eapply Rules.CEntailsTrans;
    [| apply (Rules.CEntailsExistsIntro TInt _ (EVal (VInt 0%Z)))].
  unfold Resource.instantiate_bound_core.
  cbn [Resource.subst_bound_core Resource.Assertions.subst_bound_expr
    Resource.Assertions.subst_bound_ref].
  unfold Resource.Assertions.head_bound_subst.
  rewrite !view_member_here. rewrite !view_member_there.
  apply Rules.CEntailsRefl.
Qed.

Lemma make_fold_assign :
  HoareRules.RavenHoareTriple
    (Resource.RState make_alloc_store
      (RH.allocated_fields_core make_entry_store make_initializers))
    (TSeq
      (TFold counter_invariant (PECons (PEVar (LHere eq_refl)) PENil))
      (TAssign false (LThere (LHere eq_refl)) (PEVar (LHere eq_refl))))
    (Resource.ResourceExists TRef
      (Resource.RState make_exit_store
        (counter_token_core (ERef (RefBound MHere))))).
Proof.
  eapply Rules.RTSeq with
    (middle := Resource.RState make_alloc_store
      (counter_token_core (ERef (RefBound MHere)))).
  - eapply Rules.RTConsequence; [eapply Rules.RTFoldInvariant | | ].
    + cbn [RuleValidity.IR.symbolize_expr_list]. rewrite make_alloc_location.
      exact make_allocated_to_invariant.
    + cbn [RuleValidity.IR.symbolize_expr_list]. rewrite make_alloc_location.
      unfold counter_token_core. apply Rules.resource_prenex_entails_refl.
  - unfold make_exit_store, counter_token_core.
    eapply Rules.RTConsequence;
      [eapply Rules.RTFrame; eapply Rules.RTAssign | | ].
    + eapply Rules.CEntailsTrans;
        [apply Rules.CEntailsStep; apply Rules.CESAndTrueIntro |].
      apply Rules.CEntailsStep. apply Rules.CESAndComm.
    + rewrite make_alloc_location.
      cbn [RuleValidity.Hoare.ResourceHoare.Resource.prenex_and
        RuleValidity.Hoare.ResourceHoare.Resource.weaken_core
        RuleValidity.Hoare.ResourceHoare.Assertions.weaken_expr_list
        RuleValidity.Hoare.ResourceHoare.Assertions.weaken_expr
        RuleValidity.Hoare.ResourceHoare.Assertions.weaken_ref].
      apply Rules.RPEMono. apply Rules.RPEBody. split; [reflexivity |].
      eapply Rules.CEntailsTrans; [apply Rules.CEntailsStep; apply Rules.CESAndComm |].
      cbn [RuleValidity.Hoare.ResourceHoare.Resource.resource_body
        RuleValidity.Hoare.ResourceHoare.Resource.weaken_core
        RuleValidity.Hoare.ResourceHoare.Assertions.weaken_expr_list
        RuleValidity.Hoare.ResourceHoare.Assertions.weaken_expr
        RuleValidity.Hoare.ResourceHoare.Assertions.weaken_ref].
      apply Rules.CEntailsStep. apply Rules.CESInvariantArgumentsEqAssume.
      apply ExprListEqualCons.
      { intros formals binders valuation Hequality. symmetry.
        eapply interp_typed_equality_true_early. exact Hequality. }
      apply ExprListEqualNil.
Qed.

Lemma make_resource_body_derivation :
  HoareRules.RavenHoareTriple
    (RuleValidity.Hoare.procedure_body_pre make_typed_procedure)
    make_typed_body
    (RuleValidity.Hoare.procedure_body_post make_typed_procedure make_exit_store
      (RefBound MHere)).
Proof.
  unfold RuleValidity.Hoare.procedure_body_pre, RuleValidity.Hoare.procedure_body_post,
    make_typed_procedure, make_typed_body.
  cbn [elaborate_stmt procedure_entry_store procedure_precondition
    procedure_postcondition RuleValidity.Hoare.existentially_close_prenex
    RuleValidity.Hoare.existentially_close_prenex_at].
  cbn [IR.Resource.subst_bound_core Assertions.subst_bound_expr_list
    Assertions.subst_bound_expr Assertions.subst_bound_ref].
  rewrite Assertions.singleton_bound_subst_here.
  eapply Rules.RTSeq; [exact make_alloc |].
  apply Rules.RTPrenexPreserve.
  exact make_fold_assign.
Qed.
(** The body of [incr] runs under the snapshots of its two accesses'
    arguments; each snapshot slot holds the formal. *)
Definition incr_body1_decls : decl_context :=
  ghost_val TRef :: runtime_decls [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit].
Definition incr_body2_decls : decl_context := ghost_val TRef :: incr_body1_decls.

Definition incr_snapshot1_store : symbolic_store incr_body1_decls [TRef] [] :=
  StoreCons (RefFormal MHere) incr_entry_store.

Lemma incr_snapshot1_arguments {keep} (Hkeep : keep _ = true) :
  RuleValidity.IR.symbolize_expr_list incr_snapshot1_store
      (PECons (PEVar (LHere Hkeep)) PENil) =
    ExprCons (ERef (RefFormal MHere)) ExprNil.
Proof. reflexivity. Qed.

Definition incr_open1_store : symbolic_store incr_body1_decls [TRef] [TInt] :=
  weaken_store incr_snapshot1_store.

Definition incr_read1_store :
    symbolic_store incr_body1_decls [TRef] [TInt; TInt] :=
  RuleValidity.IR.update_store_with_bound (keep := keep_runtime_var)
    incr_open1_store (LThere (LThere (LHere eq_refl))).

Definition incr_new_store :
    symbolic_store incr_body1_decls [TRef] [TInt; TInt; TInt] :=
  RuleValidity.IR.update_store_with_bound (keep := keep_runtime_var)
    incr_read1_store (LThere (LThere (LThere (LHere eq_refl)))).

Definition incr_snapshot2_store :
    symbolic_store incr_body2_decls [TRef] [TInt; TInt; TInt] :=
  StoreCons (RefFormal MHere) incr_new_store.

Definition incr_open2_store :
    symbolic_store incr_body2_decls [TRef] [TInt; TInt; TInt; TInt] :=
  weaken_store incr_snapshot2_store.

Definition incr_cas_read_store :
    symbolic_store incr_body2_decls [TRef] [TInt; TInt; TInt; TInt; TInt] :=
  RuleValidity.IR.update_store_with_bound (keep := keep_runtime_var)
    incr_open2_store (LThere (LThere (LThere (LThere (LThere (LHere eq_refl)))))).

Definition incr_res_store :
    symbolic_store incr_body2_decls [TRef] [TBool; TInt; TInt; TInt; TInt; TInt] :=
  RuleValidity.IR.update_store_with_bound (keep := keep_runtime_var)
    incr_cas_read_store (LThere (LThere (LThere (LThere (LThere (LThere (LHere eq_refl))))))).

Lemma incr_open1_location {keep} (Hkeep : keep _ = true) :
  RuleValidity.Translation.IR.symbolize_expr incr_open1_store (PEVar (LHere Hkeep)) =
    ERef (RefFormal MHere).
Proof. reflexivity. Qed.

Lemma incr_read1_location {keep} (Hkeep : keep _ = true) :
  RuleValidity.Translation.IR.symbolize_expr incr_read1_store (PEVar (LHere Hkeep)) =
    ERef (RefFormal MHere).
Proof. reflexivity. Qed.

Lemma incr_snapshot2_location {keep} (Hkeep : keep _ = true) :
  RuleValidity.Translation.IR.symbolize_expr incr_snapshot2_store
      (PEVar (LHere Hkeep)) =
    ERef (RefFormal MHere).
Proof. reflexivity. Qed.

(** [x] itself, one slot below the snapshot of each access. *)
Lemma incr_open1_x_location {keep} (Hkeep : keep _ = true) :
  RuleValidity.Translation.IR.symbolize_expr incr_open1_store
      (PEVar (LThere (LHere Hkeep))) =
    ERef (RefFormal MHere).
Proof. reflexivity. Qed.

Lemma incr_open2_x_location {keep} (Hkeep : keep _ = true) :
  RuleValidity.Translation.IR.symbolize_expr incr_open2_store
      (PEVar (LThere (LThere (LHere Hkeep)))) =
    ERef (RefFormal MHere).
Proof. reflexivity. Qed.

Lemma incr_cas_read_x_location {keep} (Hkeep : keep _ = true) :
  RuleValidity.Translation.IR.symbolize_expr incr_cas_read_store
      (PEVar (LThere (LThere (LHere Hkeep)))) =
    ERef (RefFormal MHere).
Proof. reflexivity. Qed.

Lemma incr_res_x_location {keep} (Hkeep : keep _ = true) :
  RuleValidity.Translation.IR.symbolize_expr incr_res_store
      (PEVar (LThere (LThere (LHere Hkeep)))) =
    ERef (RefFormal MHere).
Proof. reflexivity. Qed.

Lemma incr_open2_location {keep} (Hkeep : keep _ = true) :
  RuleValidity.Translation.IR.symbolize_expr incr_open2_store (PEVar (LHere Hkeep)) =
    ERef (RefFormal MHere).
Proof. reflexivity. Qed.

Lemma incr_cas_read_location {keep} (Hkeep : keep _ = true) :
  RuleValidity.Translation.IR.symbolize_expr incr_cas_read_store (PEVar (LHere Hkeep)) =
    ERef (RefFormal MHere).
Proof. reflexivity. Qed.

Lemma incr_res_location {keep} (Hkeep : keep _ = true) :
  RuleValidity.Translation.IR.symbolize_expr incr_res_store (PEVar (LHere Hkeep)) =
    ERef (RefFormal MHere).
Proof. reflexivity. Qed.
Lemma incr_unfold1_open :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_snapshot1_store
      (counter_token_core (ERef (RefFormal MHere))))
    (TUnfold counter_invariant (PECons (PEVar (LHere eq_refl)) PENil))
    (Resource.ResourceExists TInt
      (Resource.RState incr_open1_store read_open_core)).
Proof.
  unfold incr_open1_store.
  apply Rules.RTPostOpenCoreExists.
  unfold counter_token_core.
  try change (Assertion.procedure_args incr_procedure) with ([TRef] : context).
  rewrite <- counter_invariant_at_formal.
  rewrite <- (incr_snapshot1_arguments (keep := keep_all) eq_refl).
  apply Rules.RTUnfoldInvariant.
Qed.

Lemma incr_field1_read :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_open1_store read_open_core)
    (TFieldRead false counter_field (LThere (LThere (LHere eq_refl))) (PEVar (LThere (LHere eq_refl))))
    (Resource.ResourceExists TInt
      (Resource.RState incr_read1_store read_field_core)).
Proof.
  unfold read_open_core, read_field_core, incr_read1_store.
  eapply Rules.RTConsequence with
    (pre_body := Resource.CAnd
      (Rules.COwn counter_field (ERef (RefFormal MHere))
        (ERef (RefBound MHere)))
      (Rules.CGhostOwn ghost_field (ERef (RefFormal MHere))
        (EUnOp (URAOfInt h_ra) (ERef (RefBound MHere))))).
  - eapply Rules.RTFrame.
    change (Assertion.field_type counter_field) with TInt.
    rewrite <- (incr_open1_x_location (keep := keep_runtime) eq_refl).
    eapply Rules.RTFieldRead.
  - apply Rules.CEntailsStep. apply Rules.CESAndComm.
  - rewrite incr_open1_x_location. apply Rules.resource_prenex_entails_refl.
Qed.

Lemma incr_fold1 :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_read1_store read_field_core)
    (TFold counter_invariant (PECons (PEVar (LHere eq_refl)) PENil))
    (Resource.RState incr_read1_store
      (counter_token_core (ERef (RefFormal MHere)))).
Proof.
  eapply Rules.RTConsequence; [eapply Rules.RTFoldInvariant | | ].
  - cbn [RuleValidity.IR.symbolize_expr_list]. rewrite incr_read1_location.
    try change (Assertion.procedure_args incr_procedure) with ([TRef] : context).
    rewrite counter_invariant_at_formal_two.
    eapply Rules.CEntailsTrans;
      [| apply (Rules.CEntailsExistsIntro TInt _
           (@ERef _ [TRef] [TInt; TInt] TInt (RefBound (MThere MHere))))].
    rewrite read_fold_instantiate. unfold read_field_core.
    eapply Rules.CEntailsTrans;
      [apply Rules.CEntailsAndMono;
        [apply Rules.CEntailsStep; apply Rules.CESAndElimL | apply Rules.CEntailsRefl] |].
    apply Rules.CEntailsStep. apply Rules.CESAndComm.
  - cbn [RuleValidity.IR.symbolize_expr_list]. rewrite incr_read1_location.
    unfold counter_token_core. apply Rules.resource_prenex_entails_refl.
Qed.

(** The generated checks that each fold names the opened instance. *)
Lemma incr_check1 :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_read1_store
      (counter_token_core (ERef (RefFormal MHere))))
    (TAssert (PEBinOp (BEq TRef) (PEVar (LHere eq_refl)) (PEVar (LThere (LHere eq_refl)))))
    (Resource.RState incr_read1_store
      (counter_token_core (ERef (RefFormal MHere)))).
Proof. apply Rules.RTAssertTrue. intros. apply interp_equality_same. Qed.

(** *** Step 2: [new_v1 := v1 + 1], carrying the closed invariant token *)

(** The opened invariant body, at any ambient binder context.  [read]'s
    [read_open_core] is its instance at the empty one. *)
Definition counter_open_core {Delta : context} :
    Resource.core_assertion [TRef] (TInt :: Delta) :=
  Resource.CAnd
    (Rules.CGhostOwn ghost_field (ERef (RefFormal MHere))
      (EUnOp (URAOfInt h_ra) (ERef (RefBound MHere))))
    (Rules.COwn counter_field (ERef (RefFormal MHere))
      (ERef (RefBound MHere))).

Definition incr_new_equality_core :
    expr [TRef] [TInt; TInt; TInt] TBool :=
  EBinOp (BEq TInt) (ERef (RefBound MHere))
    (weaken_expr (RuleValidity.IR.symbolize_expr (keep := keep_runtime) incr_read1_store
      (PEBinOp BAdd (PEVar (LThere (LThere (LHere eq_refl)))) (PEVal (VInt 1%Z))))).

Lemma incr_assign_new :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_read1_store
      (counter_token_core (ERef (RefFormal MHere))))
    (TAssign false (LThere (LThere (LThere (LHere eq_refl))))
      (PEBinOp BAdd (PEVar (LThere (LThere (LHere eq_refl)))) (PEVal (VInt 1%Z))))
    (Resource.ResourceExists TInt
      (Resource.RState incr_new_store
        (Resource.CAnd (Resource.CExpr incr_new_equality_core)
          (counter_token_core (ERef (RefFormal MHere)))))).
Proof.
  unfold incr_new_store, incr_new_equality_core, counter_token_core.
  eapply Rules.RTConsequence;
    [eapply Rules.RTFrame; eapply Rules.RTAssign | | ].
  - eapply Rules.CEntailsTrans;
      [apply Rules.CEntailsStep; apply Rules.CESAndTrueIntro |].
    apply Rules.CEntailsStep. apply Rules.CESAndComm.
  - cbn [RuleValidity.Hoare.ResourceHoare.Resource.prenex_and
      RuleValidity.Hoare.ResourceHoare.Resource.weaken_core
      RuleValidity.Hoare.ResourceHoare.Assertions.weaken_expr_list
      RuleValidity.Hoare.ResourceHoare.Assertions.weaken_expr
      RuleValidity.Hoare.ResourceHoare.Assertions.weaken_ref].
    apply Rules.resource_prenex_entails_refl.
Qed.

(** *** Step 3: the second unfold, under the carried equality *)

Lemma incr_unfold2 :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_snapshot2_store
      (Resource.CAnd (Resource.CExpr incr_new_equality_core)
        (counter_token_core (ERef (RefFormal MHere)))))
    (TUnfold counter_invariant (PECons (PEVar (LHere eq_refl)) PENil))
    (Resource.ResourceExists TInt
      (Resource.RState incr_open2_store
        (Resource.CAnd (@counter_open_core [TInt; TInt; TInt])
          (Resource.CExpr (weaken_expr incr_new_equality_core))))).
Proof.
  unfold incr_open2_store.
  eapply Rules.RTConsequence;
    [eapply Rules.RTFrame; eapply Rules.RTUnfoldInvariant | | ].
  - cbn [RuleValidity.IR.symbolize_expr_list]. rewrite incr_snapshot2_location.
    unfold counter_token_core.
    apply Rules.CEntailsStep. apply Rules.CESAndComm.
  - eapply Rules.RPETrans; [| apply Rules.RPEOpenCoreExists].
    cbn [RuleValidity.Hoare.ResourceHoare.Resource.prenex_and].
    apply Rules.RPEBody. split; [reflexivity |].
    cbn [RuleValidity.Hoare.ResourceHoare.Resource.resource_body
      RuleValidity.Hoare.ResourceHoare.Resource.resource_stack].
    cbn [RuleValidity.IR.symbolize_expr_list]. rewrite incr_snapshot2_location.
    try change (Assertion.procedure_args incr_procedure) with ([TRef] : context).
    rewrite (counter_invariant_instantiated (ERef (RefFormal MHere))).
    unfold counter_open_core.
    exact (Rules.CEntailsExistsAndRight TInt _
      (Resource.CExpr incr_new_equality_core)).
Qed.
Definition incr_cas_old_core :
    expr [TRef] [TInt; TInt; TInt; TInt; TInt] TInt :=
  ERef (RefBound (MThere MHere)).

Definition incr_cas_new_core :
    expr [TRef] [TInt; TInt; TInt; TInt; TInt] TInt :=
  RuleValidity.IR.symbolize_expr (keep := keep_runtime) incr_cas_read_store
    (PEVar (LThere (LThere (LThere (LThere (LHere eq_refl)))))).

Definition incr_cas_expected_core :
    expr [TRef] [TInt; TInt; TInt; TInt; TInt] TInt :=
  RuleValidity.IR.symbolize_expr (keep := keep_runtime) incr_cas_read_store
    (PEVar (LThere (LThere (LThere (LHere eq_refl))))).

(** The block's own read lands [v2] in binder zero. *)
Definition incr_cas_failure_core :
    Resource.core_assertion [TRef] [TInt; TInt; TInt; TInt; TInt] :=
  Resource.CAnd
    (Rules.CGhostOwn ghost_field (ERef (RefFormal MHere))
      (EUnOp (URAOfInt h_ra) incr_cas_old_core))
    (Rules.COwn counter_field (ERef (RefFormal MHere)) incr_cas_old_core).

Definition incr_cas_success_core :
    Resource.core_assertion [TRef] [TInt; TInt; TInt; TInt; TInt] :=
  Resource.CAnd
    (Rules.CGhostOwn ghost_field (ERef (RefFormal MHere))
      (EUnOp (URAOfInt h_ra) incr_cas_expected_core))
    (Rules.COwn counter_field (ERef (RefFormal MHere)) incr_cas_new_core).

(** The state just after the block's own field read: the cell, the
    observed equality, and the ghost chunk that the read framed off. *)
Definition incr_cas_read_core :
    Resource.core_assertion [TRef] [TInt; TInt; TInt; TInt; TInt] :=
  Resource.CAnd
    (Resource.CAnd
      (Rules.COwn counter_field (ERef (RefFormal MHere)) incr_cas_old_core)
      (Resource.CExpr (EBinOp (BEq TInt) (ERef (RefBound MHere))
        incr_cas_old_core)))
    (Rules.CGhostOwn ghost_field (ERef (RefFormal MHere))
      (EUnOp (URAOfInt h_ra) incr_cas_old_core)).

(** The joined post of the block, discriminated by the result bit. *)
Definition incr_cas_join_prenex :
    Resource.resource_prenex incr_body2_decls [TRef] [TInt; TInt; TInt; TInt] :=
  Resource.ResourceExists TInt
    (Resource.ResourceExists TBool
      (Resource.RState incr_res_store
        (Resource.CIte (ERef (RefBound MHere))
          (Resource.weaken_core incr_cas_success_core)
          (Resource.weaken_core incr_cas_failure_core)))).

Lemma incr_cas_read :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_open2_store counter_open_core)
    (TFieldRead false counter_field (LThere (LThere (LThere (LThere (LThere (LHere eq_refl))))))
      (PEVar (LThere (LThere (LHere eq_refl)))))
    (Resource.ResourceExists TInt
      (Resource.RState incr_cas_read_store incr_cas_read_core)).
Proof.
  unfold counter_open_core, incr_cas_read_core, incr_cas_read_store,
    incr_cas_old_core.
  eapply Rules.RTConsequence with
    (pre_body := Resource.CAnd
      (Rules.COwn counter_field (ERef (RefFormal MHere))
        (ERef (RefBound MHere)))
      (Rules.CGhostOwn ghost_field (ERef (RefFormal MHere))
        (EUnOp (URAOfInt h_ra) (ERef (RefBound MHere))))).
  - eapply Rules.RTFrame.
    change (Assertion.field_type counter_field) with TInt.
    rewrite <- (incr_open2_x_location (keep := keep_runtime) eq_refl).
    eapply Rules.RTFieldRead.
  - apply Rules.CEntailsStep. apply Rules.CESAndComm.
  - rewrite incr_open2_x_location. apply Rules.resource_prenex_entails_refl.
Qed.

Lemma incr_cas_success_branch :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_cas_read_store
      (Resource.CAnd incr_cas_read_core
        (Resource.CExpr (RuleValidity.IR.symbolize_expr (keep := keep_runtime) incr_cas_read_store
          (PEBinOp (BEq TInt) (PEVar (LThere (LThere (LThere (LThere (LThere (LHere eq_refl)))))))
            (PEVar (LThere (LThere (LThere (LHere eq_refl))))))))))
    (TSeq
      (TFieldWrite counter_field (PEVar (LThere (LThere (LHere eq_refl))))
        (PEVar (LThere (LThere (LThere (LThere (LHere eq_refl)))))))
      (TAssign false (LThere (LThere (LThere (LThere (LThere (LThere (LHere eq_refl)))))))
        (PEVal (VBool true))))
    (Resource.ResourceExists TBool
      (Resource.RState incr_res_store
        (Resource.CIte (ERef (RefBound MHere))
          (Resource.weaken_core incr_cas_success_core)
          (Resource.weaken_core incr_cas_failure_core)))).
Proof.
  eapply Rules.RTConsequence with
    (pre_body := Resource.CAnd
      (Rules.COwn counter_field (ERef (RefFormal MHere)) incr_cas_old_core)
      (Rules.CGhostOwn ghost_field (ERef (RefFormal MHere))
        (EUnOp (URAOfInt h_ra) incr_cas_expected_core))).
  3: { apply Rules.resource_prenex_entails_refl. }
  (** The ghost chunk must travel from the value found in the cell to the
      value the caller expected.  Two equalities are needed -- the block's
      own read equality and the branch condition -- and
      [CESGhostOwnChunkEqAssume] admits one guard at a time, so it is
      applied twice in sequence.  Nothing has to be duplicated: each step
      consumes exactly one of them. *)
  2: { unfold incr_cas_read_core.
       eapply Rules.CEntailsTrans;
         [apply Rules.CEntailsStep; apply Rules.CESAndAssocR |].
       eapply Rules.CEntailsTrans;
         [apply Rules.CEntailsStep; apply Rules.CESAndAssocR |].
       apply Rules.CEntailsAndMono; [apply Rules.CEntailsRefl |].
       eapply Rules.CEntailsTrans;
         [apply Rules.CEntailsStep; apply Rules.CESAndAssocL |].
       eapply Rules.CEntailsTrans;
         [apply Rules.CEntailsAndMono;
           [apply Rules.CEntailsStep; apply Rules.CESAndComm
           | apply Rules.CEntailsRefl] |].
       eapply Rules.CEntailsTrans;
         [apply Rules.CEntailsAndMono; [| apply Rules.CEntailsRefl] |].
       1: { apply Rules.CEntailsStep.
            apply (Rules.CESGhostOwnChunkEqAssume ghost_field
              (ERef (RefFormal MHere))
              (EUnOp (URAOfInt h_ra) incr_cas_old_core)
              (EUnOp (URAOfInt h_ra) (ERef (RefBound MHere)))).
            intros formals binders valuation Heq.
            pose proof (interp_typed_equality_true_early formals binders valuation
              _ _ Heq) as Hvalue.
            cbn [interp_expr]. cbn [interp_expr] in Hvalue.
            rewrite <- Hvalue. reflexivity. }
       apply Rules.CEntailsStep. apply Rules.CESGhostOwnChunkEqAssume.
       intros formals binders valuation Heq.
       pose proof (interp_typed_equality_true_early formals binders valuation
         _ _ Heq) as Hvalue.
       unfold incr_cas_expected_core, RuleValidity.IR.symbolize_expr.
       unfold incr_cas_read_store in Hvalue |- *.
       cbn [lookup_store lookup_variable RuleValidity.IR.update_store_with_bound
         store_head store_tail] in Hvalue |- *.
       cbn [interp_expr] in Hvalue |- *.
       injection Hvalue as Hvalue.
       cbn [RH.Core.interp_ref] in Hvalue |- *.
       rewrite Hvalue. reflexivity. }
  eapply Rules.RTSeq with
    (middle := Resource.RState incr_cas_read_store
      (Resource.CAnd
        (Rules.COwn counter_field (ERef (RefFormal MHere))
          incr_cas_new_core)
        (Rules.CGhostOwn ghost_field (ERef (RefFormal MHere))
          (EUnOp (URAOfInt h_ra) incr_cas_expected_core)))).
  - eapply Rules.RTConsequence;
      [eapply Rules.RTFrame; eapply Rules.RTFieldWrite | | ].
    + rewrite <- (incr_cas_read_x_location (keep := keep_runtime) eq_refl).
      apply Rules.CEntailsRefl.
    + unfold incr_cas_new_core.
      cbn [RuleValidity.Hoare.ResourceHoare.Resource.prenex_and].
      rewrite <- (incr_cas_read_x_location (keep := keep_runtime) eq_refl).
      apply Rules.resource_prenex_entails_refl.
  - unfold incr_res_store.
    eapply Rules.RTConsequence;
      [eapply Rules.RTFrame; eapply Rules.RTAssign | | ].
    + eapply Rules.CEntailsTrans;
        [apply Rules.CEntailsStep; apply Rules.CESAndTrueIntro |].
      apply Rules.CEntailsStep. apply Rules.CESAndComm.
    + cbn [RuleValidity.Hoare.ResourceHoare.Resource.prenex_and].
      apply Rules.RPEMono. apply Rules.RPEBody. split; [reflexivity |].
      cbn [RuleValidity.Hoare.ResourceHoare.Resource.resource_body
        RuleValidity.Hoare.ResourceHoare.Resource.resource_stack].
      eapply Rules.CEntailsTrans; [apply Rules.CEntailsStep; apply Rules.CESAndComm |].
      eapply Rules.CEntailsTrans;
        [apply Rules.CEntailsAndMono
        | apply Rules.CEntailsStep; apply Rules.CESIteIntroTrue].
      * unfold incr_cas_success_core.
        apply Rules.CEntailsStep. apply Rules.CESAndComm.
      * apply Rules.CEntailsStep. apply Rules.CESExprImpl.
        intros formals binders valuation Heq.
        pose proof (interp_typed_equality_true_early formals binders valuation
          _ _ Heq) as Hvalue.
        cbn [RuleValidity.IR.symbolize_expr interp_expr interp_ref
          RuleValidity.Hoare.ResourceHoare.Assertions.weaken_expr] in Hvalue.
        cbn [interp_expr interp_ref].
        injection Hvalue as Hvalue. rewrite Hvalue. reflexivity.
Qed.

Lemma incr_cas_failure_branch :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_cas_read_store
      (Resource.CAnd incr_cas_read_core
        (Resource.CExpr (EUnOp UNot
          (RuleValidity.IR.symbolize_expr (keep := keep_runtime) incr_cas_read_store
            (PEBinOp (BEq TInt) (PEVar (LThere (LThere (LThere (LThere (LThere (LHere eq_refl)))))))
              (PEVar (LThere (LThere (LThere (LHere eq_refl)))))))))))
    (TAssign false (LThere (LThere (LThere (LThere (LThere (LThere (LHere eq_refl)))))))
      (PEVal (VBool false)))
    (Resource.ResourceExists TBool
      (Resource.RState incr_res_store
        (Resource.CIte (ERef (RefBound MHere))
          (Resource.weaken_core incr_cas_success_core)
          (Resource.weaken_core incr_cas_failure_core)))).
Proof.
  unfold incr_res_store.
  eapply Rules.RTConsequence;
    [eapply Rules.RTFrame; eapply Rules.RTAssign | | ].
  - unfold incr_cas_read_core, incr_cas_failure_core.
    eapply Rules.CEntailsTrans;
      [apply Rules.CEntailsStep; apply Rules.CESAndElimL |].
    eapply Rules.CEntailsTrans;
      [apply Rules.CEntailsAndMono;
        [apply Rules.CEntailsStep; apply Rules.CESAndElimL | apply Rules.CEntailsRefl] |].
    eapply Rules.CEntailsTrans;
      [apply Rules.CEntailsStep; apply Rules.CESAndComm |].
    eapply Rules.CEntailsTrans;
      [apply Rules.CEntailsStep; apply Rules.CESAndTrueIntro |].
    apply Rules.CEntailsStep. apply Rules.CESAndComm.
  - cbn [RuleValidity.Hoare.ResourceHoare.Resource.prenex_and].
    apply Rules.RPEMono. apply Rules.RPEBody. split; [reflexivity |].
    cbn [RuleValidity.Hoare.ResourceHoare.Resource.resource_body
      RuleValidity.Hoare.ResourceHoare.Resource.resource_stack].
    eapply Rules.CEntailsTrans; [apply Rules.CEntailsStep; apply Rules.CESAndComm |].
    eapply Rules.CEntailsTrans;
      [apply Rules.CEntailsAndMono; [apply Rules.CEntailsRefl |] |].
    2: { apply Rules.CEntailsStep. apply Rules.CESIteIntroFalse. }
    apply Rules.CEntailsStep. apply Rules.CESExprImpl.
    intros formals binders valuation Heq.
    pose proof (interp_typed_equality_true_early formals binders valuation _ _ Heq)
      as Hvalue.
    cbn [RuleValidity.IR.symbolize_expr interp_expr interp_ref
      RuleValidity.Hoare.ResourceHoare.Assertions.weaken_expr] in Hvalue.
    cbn [interp_expr interp_ref interp_unop].
    injection Hvalue as Hvalue. rewrite Hvalue. reflexivity.
Qed.

(** The trusted block as it appears under the two snapshots. *)
Definition cas_snapshot_body : stmt incr_body2_decls :=
  Eval vm_compute in
    snapshots.Snapshots.stmt_rename (fun _ _ variable => LThere (LThere variable))
      cas_typed_body.

Lemma incr_cas_body :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_open2_store counter_open_core)
    cas_snapshot_body incr_cas_join_prenex.
Proof.
  unfold cas_snapshot_body, incr_cas_join_prenex.
  eapply Rules.RTSeq; [apply incr_cas_read |].
  apply Rules.RTPrenexPreserve.
  eapply Rules.RTIf;
    [apply incr_cas_success_branch
    | apply incr_cas_failure_branch].
Qed.

Lemma incr_atomic_cas :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_open2_store counter_open_core)
    (TAtomic cas_snapshot_body) incr_cas_join_prenex.
Proof.
  apply Rules.RTAtomicBlock. exact incr_cas_body.
Qed.

(** *** The ghost update after a successful CAS

    The ghost values before and after the increment, and the
    frame-preserving update between them. *)

Definition incr_fpu_old_core :
    expr [TRef] [TBool; TInt; TInt; TInt; TInt; TInt] (TRA h_ra) :=
  EUnOp (URAOfInt h_ra)
    (RuleValidity.IR.symbolize_expr (keep := keep_runtime) incr_res_store
      (PEVar (LThere (LThere (LThere (LHere eq_refl)))))).

Definition incr_fpu_new_core :
    expr [TRef] [TBool; TInt; TInt; TInt; TInt; TInt] (TRA h_ra) :=
  EUnOp (URAOfInt h_ra)
    (EBinOp BAdd
      (RuleValidity.IR.symbolize_expr (keep := keep_runtime) incr_res_store
        (PEVar (LThere (LThere (LThere (LHere eq_refl))))))
      (EVal (VInt 1%Z))).

Lemma incr_fpu_allowed :
  RH.core_entails
    (@Resource.CTrue _ _ [TRef] [TBool; TInt; TInt; TInt; TInt; TInt])
    (Resource.CFpuAllowed (TRA h_ra) incr_fpu_old_core incr_fpu_new_core).
Proof.
  apply Rules.CEntailsStep. apply Rules.CESFpuAllowedTrue.
  intros formals binders valuation old_value new_value Hold Hnew.
  unfold incr_fpu_old_core, incr_fpu_new_core in Hold, Hnew.
  cbn [interp_expr interp_ref interp_unop interp_binop] in Hold, Hnew.
  cbn in Hold, Hnew.
  match type of Hold with
  | context [binders ?t ?variable] => generalize dependent (binders t variable)
  end.
  intros current_value Hold Hnew.
  dependent destruction current_value.
  cbn in Hold, Hnew.
  inversion Hold; subst. inversion Hnew; subst.
  cbn [tval_fpu_allowed RuntimeErasure.RAValues.ra_fpu_allowed].
  apply h_ra_fpuValid_mono. reflexivity.
Qed.

(** *** Slot equations

    Every symbolic slot the post-CAS reasoning mentions, resolved to an
    explicit binder reference.  Each holds by computation through the store
    sequence built by the body. *)

(** *** Step 5: the post-CAS conditional

    Each branch reaches the *unfolded* invariant body before its fold.
    Success reaches it at [new_v1] and failure at the value the block
    observed; the carried equality is what identifies [ghost(v1 + 1)] with
    [ghost(new_v1)] on the success side, which is why the frame around the
    atomic block has to extend over this conditional as well. *)

Definition incr_threaded_equality_core :
    Resource.core_assertion [TRef] [TBool; TInt; TInt; TInt; TInt; TInt] :=
  Resource.weaken_core (Resource.weaken_core
    (Resource.CExpr (weaken_expr incr_new_equality_core))).

Definition incr_post_cas_core :
    Resource.core_assertion [TRef] [TBool; TInt; TInt; TInt; TInt; TInt] :=
  Resource.CExists TInt
    (@counter_open_core [TBool; TInt; TInt; TInt; TInt; TInt]).

Definition incr_cas_result_core :
    Resource.core_assertion [TRef] [TBool; TInt; TInt; TInt; TInt; TInt] :=
  Resource.CAnd
    (Resource.CIte (ERef (RefBound MHere))
      (Resource.weaken_core incr_cas_success_core)
      (Resource.weaken_core incr_cas_failure_core))
    incr_threaded_equality_core.

Lemma incr_fpu_branch :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_res_store
      (Resource.CAnd incr_cas_result_core
        (Resource.CExpr (ERef (RefBound MHere)))))
    (TGhostUpdate ghost_field (PEVar (LThere (LThere (LHere eq_refl))))
      (PEUnOp (URAOfInt h_ra) (PEVar (LThere (LThere (LThere (LHere eq_refl))))))
      (PEUnOp (URAOfInt h_ra)
        (PEBinOp BAdd (PEVar (LThere (LThere (LThere (LHere eq_refl))))) (PEVal (VInt 1%Z)))))
    (Resource.RState incr_res_store incr_post_cas_core).
Proof.
  eapply Rules.RTConsequence;
    [eapply Rules.RTFrame; eapply Rules.RTGhostUpdate | | ].
  (** [CESIteTrue] selects the success shape while the threaded equality
      rides along; the ghost is then put in the form [RTGhostUpdate]
      demands and the [CFpuAllowed] conjunct is introduced from [CPure
      True]. *)
  1: { unfold incr_cas_result_core, incr_cas_success_core.
       eapply Rules.CEntailsTrans;
         [apply Rules.CEntailsStep; apply Rules.CESAndAssocR |].
       eapply Rules.CEntailsTrans;
         [apply Rules.CEntailsAndMono;
           [apply Rules.CEntailsRefl
           | apply Rules.CEntailsStep; apply Rules.CESAndComm] |].
       eapply Rules.CEntailsTrans;
         [apply Rules.CEntailsStep; apply Rules.CESAndAssocL |].
       eapply Rules.CEntailsTrans;
         [apply Rules.CEntailsAndMono;
           [apply Rules.CEntailsStep; apply Rules.CESIteTrue
           | apply Rules.CEntailsRefl] |].
       cbn [Resource.weaken_core].
       eapply Rules.CEntailsTrans;
         [apply Rules.CEntailsStep; apply Rules.CESAndAssocR |].
       apply Rules.CEntailsAndMono; [| apply Rules.CEntailsRefl].
       cbn [Resource.Assertions.rename_bound_expr
         Resource.Assertions.rename_bound_ref].
       change (Resource.Assertions.rename_bound_expr
         Resource.Assertions.weaken_bound_renaming incr_cas_expected_core)
         with (weaken_expr (u := TBool) incr_cas_expected_core).
       unfold incr_cas_expected_core.
       change (Assertion.field_type ghost_field) with (TRA h_ra).
       eapply Rules.CEntailsTrans;
         [apply Rules.CEntailsStep; apply Rules.CESAndTrueIntro |].
       apply Rules.CEntailsAndMono;
         [apply Rules.CEntailsRefl | apply incr_fpu_allowed]. }
  (** The advanced chunk is [v1 + 1]; the threaded equality identifies it
      with [new_v1], which is the witness the invariant body is closed
      at. *)
  cbn [RuleValidity.Hoare.ResourceHoare.Resource.prenex_and].
  apply Rules.RPEBody. split; [reflexivity |].
  cbn [RuleValidity.Hoare.ResourceHoare.Resource.resource_body
    RuleValidity.Hoare.ResourceHoare.Resource.resource_stack].
  unfold incr_post_cas_core.
  eapply Rules.CEntailsTrans;
    [| apply (Rules.CEntailsExistsIntro TInt _
         (weaken_expr (u := TBool) incr_cas_new_core))].
  unfold Resource.instantiate_bound_core, counter_open_core.
  cbn [Resource.subst_bound_core Resource.Assertions.subst_bound_expr
    Resource.Assertions.subst_bound_ref].
  unfold Resource.Assertions.head_bound_subst.
  rewrite !view_member_here.
  cbn [Resource.Assertions.rename_bound_expr
    Resource.Assertions.rename_bound_ref].
  eapply Rules.CEntailsTrans;
    [apply Rules.CEntailsAndMono;
      [apply Rules.CEntailsRefl | apply Rules.CEntailsStep; apply Rules.CESAndComm] |].
  eapply Rules.CEntailsTrans; [apply Rules.CEntailsStep; apply Rules.CESAndAssocL |].
  apply Rules.CEntailsAndMono; [| apply Rules.CEntailsRefl].
  unfold incr_threaded_equality_core, incr_new_equality_core.
  cbn [Resource.weaken_core].
  rewrite <- (incr_res_x_location (keep := keep_runtime) eq_refl).
  apply Rules.CEntailsStep. apply Rules.CESGhostOwnChunkEqAssume.
  intros formals binders valuation Heq.
  pose proof (interp_typed_equality_true_early formals binders valuation _ _ Heq)
    as Hvalue.
  cbn in Hvalue |- *.
  unfold Resource.Assertions.weaken_bound_renaming in Hvalue.
  rewrite <- Hvalue. reflexivity.
Qed.

Lemma incr_done_branch :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_res_store
      (Resource.CAnd incr_cas_result_core
        (Resource.CExpr (EUnOp UNot (ERef (RefBound MHere))))))
    TDone
    (Resource.RState incr_res_store incr_post_cas_core).
Proof.
  eapply Rules.RTConsequence;
    [eapply Rules.RTDone | | apply Rules.resource_prenex_entails_refl].
  unfold incr_cas_result_core, incr_post_cas_core.
  eapply Rules.CEntailsTrans; [apply Rules.CEntailsStep; apply Rules.CESAndAssocR |].
  eapply Rules.CEntailsTrans;
    [apply Rules.CEntailsAndMono;
      [apply Rules.CEntailsRefl | apply Rules.CEntailsStep; apply Rules.CESAndComm] |].
  eapply Rules.CEntailsTrans; [apply Rules.CEntailsStep; apply Rules.CESAndAssocL |].
  eapply Rules.CEntailsTrans;
    [apply Rules.CEntailsAndMono;
      [apply Rules.CEntailsStep; apply Rules.CESIteFalse | apply Rules.CEntailsRefl] |].
  eapply Rules.CEntailsTrans; [apply Rules.CEntailsStep; apply Rules.CESAndElimL |].
  eapply Rules.CEntailsTrans;
    [| apply (Rules.CEntailsExistsIntro TInt _ (weaken_expr incr_cas_old_core))].
  unfold Resource.instantiate_bound_core, counter_open_core,
    incr_cas_failure_core.
  cbn [Resource.subst_bound_core Resource.Assertions.subst_bound_expr
    Resource.Assertions.subst_bound_ref Resource.weaken_core
    Resource.Assertions.weaken_expr Resource.Assertions.weaken_ref].
  unfold Resource.Assertions.head_bound_subst.
  rewrite !view_member_here.
  apply Rules.CEntailsRefl.
Qed.

(** *** Steps 6-8: the second fold in each branch, and the retry *)

Lemma incr_fold2 :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_res_store incr_post_cas_core)
    (TFold counter_invariant (PECons (PEVar (LHere eq_refl)) PENil))
    (Resource.RState incr_res_store
      (counter_token_core (ERef (RefFormal MHere)))).
Proof.
  eapply Rules.RTConsequence; [eapply Rules.RTFoldInvariant | | ].
  - cbn [RuleValidity.IR.symbolize_expr_list]. rewrite incr_res_location.
    try change (Assertion.procedure_args incr_procedure) with ([TRef] : context).
    rewrite (counter_invariant_instantiated (ERef (RefFormal MHere))).
    unfold incr_post_cas_core, counter_open_core.
    cbn [Resource.Assertions.weaken_expr Resource.Assertions.weaken_ref
      Resource.Assertions.rename_bound_expr
      Resource.Assertions.rename_bound_ref].
    apply Rules.CEntailsRefl.
  - cbn [RuleValidity.IR.symbolize_expr_list]. rewrite incr_res_location.
    unfold counter_token_core. apply Rules.resource_prenex_entails_refl.
Qed.

Lemma incr_check2 :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_res_store
      (counter_token_core (ERef (RefFormal MHere))))
    (TAssert (PEBinOp (BEq TRef) (PEVar (LHere eq_refl)) (PEVar (LThere (LThere (LHere eq_refl))))))
    (Resource.RState incr_res_store
      (counter_token_core (ERef (RefFormal MHere)))).
Proof. apply Rules.RTAssertTrue. intros. apply interp_equality_same. Qed.

Lemma counter_resource_instantiated_pre {F Delta : context}
    (location : expr F Delta TRef) :
  HoareRules.instantiated_pre incr_procedure
      (ExprCons location ExprNil) =
    Resource.CInvariant counter_invariant (ExprCons location ExprNil).
Proof.
  unfold HoareRules.instantiated_pre.
  assert (Hpre : HoareRules.contract_pre incr_procedure
    = counter_token_core (ERef (RefFormal MHere))) by reflexivity.
  rewrite Hpre.
  unfold counter_token_core, Resource.weaken_core_to.
  cbn [Resource.subst_bound_core Resource.subst_formals_core].
  change (Assertion.procedure_args incr_procedure) with ([TRef] : context).
  cbn [Resource.Assertions.subst_bound_expr_list
    Resource.Assertions.subst_formals_expr_list
    Resource.Assertions.subst_bound_expr Resource.Assertions.subst_bound_ref
    Resource.Assertions.subst_formals_expr
    Resource.Assertions.subst_formals_ref].
  assert (Hhead : forall (t : typ) (ts : context)
      (e : Core.expr F Delta t)
      (es : RH.Assertions.expr_list F Delta ts),
    RH.Assertions.expr_list_formal_subst (RH.Assertions.ExprCons e es)
      t MHere = e);
    [intros; unfold RH.Assertions.expr_list_formal_subst;
     apply lookup_expr_list_here |].
  rewrite Hhead. reflexivity.
Qed.

Lemma incr_retry_call :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_res_store
      (counter_token_core (ERef (RefFormal MHere))))
    (TCall incr_procedure (PECons (PEVar (LThere (LThere (LHere eq_refl)))) PENil)
      (@CTDiscard _ TUnit))
    (Resource.RState incr_res_store Resource.CTrue).
Proof.
  eapply Rules.RTConsequence; [eapply Rules.RTCallDiscard | | ].
  3: { eapply Rules.RPETrans;
         [| apply (Rules.RPEVacuous TUnit
              (Resource.RState incr_res_store Resource.CTrue))].
       apply Rules.RPEMono.
       unfold Resource.weaken_resource_prenex, Resource.RState.
       cbn [Resource.rename_resource_prenex].
       unfold RH.Resource.rename_bound_resource.
       cbn [RH.Resource.resource_stack RH.Resource.resource_body].
       rewrite rename_bound_store_weaken_store.
       apply Rules.RPEBody. split;
         [reflexivity | apply Rules.CEntailsStep; apply Rules.CESTrueIntro]. }
  2: { cbn [RuleValidity.IR.symbolize_expr_list]. rewrite incr_res_x_location.
       rewrite counter_resource_instantiated_pre.
       unfold counter_token_core. apply Rules.CEntailsRefl. }
  vm_compute. discriminate.
Qed.

(** The success branch ends with the snapshot check; the postcondition
    drops the token. *)
Lemma incr_success_check :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_res_store
      (counter_token_core (ERef (RefFormal MHere))))
    (TAssert (PEBinOp (BEq TRef) (PEVar (LHere eq_refl)) (PEVar (LThere (LThere (LHere eq_refl))))))
    (Resource.RState incr_res_store Resource.CTrue).
Proof.
  eapply Rules.RTPrenexConsequence;
    [apply incr_check2 | apply Rules.resource_prenex_entails_refl |].
  apply Rules.RPEBody. split;
    [reflexivity | apply Rules.CEntailsStep; apply Rules.CESTrueIntro].
Qed.

Definition incr_exit_store := store_tail (store_tail incr_res_store).

(** [incr] returns nothing: its hidden return slot keeps whatever it holds
    at exit. *)
Definition incr_return_reference :
    value_ref [TRef] [TBool; TInt; TInt; TInt; TInt; TInt] TUnit :=
  lookup_store incr_exit_store _
    (procedure_return_variable _ _ incr_typed_procedure).

(** *** Step 9: assembly

    The carried equality is framed around the atomic block alone: the
    post-CAS conditional consumes it, so it has to be visible in the
    conditional's body.  [prenex_and] weakens it once per binder the block
    introduces, which is exactly [incr_threaded_equality_core]. *)

Lemma incr_resource_body_derivation :
  HoareRules.RavenHoareTriple
    (RuleValidity.Hoare.procedure_body_pre incr_typed_procedure)
    incr_typed_body
    (RuleValidity.Hoare.procedure_body_post incr_typed_procedure
      incr_exit_store incr_return_reference).
Proof.
  unfold RuleValidity.Hoare.procedure_body_pre, RuleValidity.Hoare.procedure_body_post,
    incr_typed_procedure.
  cbn [procedure_entry_store procedure_precondition procedure_postcondition
    RuleValidity.Hoare.existentially_close_prenex
    RuleValidity.Hoare.existentially_close_prenex_at].
  cbn [IR.Resource.subst_bound_core].
  rewrite incr_typed_body_normalized_eq.
  unfold incr_typed_body_normalized.
  eapply Rules.RTPrenexConsequence;
    [| apply Rules.resource_prenex_entails_refl |].
  { apply Rules.RTGhostValVar.
    eapply Rules.RTSeq; [apply incr_unfold1_open |].
    apply Rules.RTPrenexPreserve.
    eapply Rules.RTSeq; [apply incr_field1_read |].
    apply Rules.RTPrenexPreserve.
    eapply Rules.RTSeq; [apply incr_fold1 |].
    eapply Rules.RTSeq; [apply incr_check1 |].
    eapply Rules.RTSeq; [apply incr_assign_new |].
    apply Rules.RTPrenexPreserve.
    apply Rules.RTGhostValVar.
    eapply Rules.RTSeq; [apply incr_unfold2 |].
    apply Rules.RTPrenexPreserve.
    eapply Rules.RTSeq; [eapply Rules.RTFrame; apply incr_atomic_cas |].
    apply Rules.RTPrenexPreserve. apply Rules.RTPrenexPreserve.
    eapply (Rules.RTIf incr_res_store incr_cas_result_core
      (PEVar (LThere (LThere (LThere (LThere (LThere (LThere (LHere eq_refl)))))))) _ _ _).
    - eapply Rules.RTSeq; [exact incr_fpu_branch |].
      eapply Rules.RTSeq; [apply incr_fold2 | apply incr_success_check].
    - eapply Rules.RTSeq; [exact incr_done_branch |].
      eapply Rules.RTSeq; [apply incr_fold2 |].
      eapply Rules.RTSeq; [apply incr_check2 | apply incr_retry_call]. }
  apply Rules.resource_prenex_entails_refl.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [client]

    [client] allocates a counter with [make], spawns an [incr] thread on
    it, and reads it.  The invariant token [make] returns is duplicated
    twice: one copy goes to the spawned thread, one to [read], and one is
    returned to the caller. *)

Lemma make_instantiated_pre {F Delta : context} :
  HoareRules.instantiated_pre (F := F) (Δ := Delta) make_procedure ExprNil =
    Resource.CTrue.
Proof. reflexivity. Qed.

Lemma make_instantiated_post {F Delta : context} :
  HoareRules.instantiated_post (F := F) (Δ := Delta) make_procedure ExprNil =
    counter_token_core (ERef (RefBound MHere)).
Proof.
  unfold HoareRules.instantiated_post.
  assert (Hpost : HoareRules.contract_post make_procedure
    = counter_token_core (ERef (RefBound MHere))) by reflexivity.
  rewrite Hpost.
  unfold counter_token_core.
  cbn [Resource.rename_bound_core Resource.subst_formals_core
    Resource.Assertions.rename_bound_expr_list
    Resource.Assertions.rename_bound_expr Resource.Assertions.rename_bound_ref
    Resource.Assertions.subst_formals_expr_list
    Resource.Assertions.subst_formals_expr
    Resource.Assertions.subst_formals_ref].
  unfold Resource.Assertions.return_bound_renaming.
  rewrite view_member_here. reflexivity.
Qed.

Lemma read_instantiated_pre {F Delta : context}
    (location : expr F Delta TRef) :
  HoareRules.instantiated_pre read_procedure (ExprCons location ExprNil) =
    counter_token_core location.
Proof.
  unfold HoareRules.instantiated_pre.
  assert (Hpre : HoareRules.contract_pre read_procedure
    = counter_token_core (ERef (RefFormal MHere))) by reflexivity.
  rewrite Hpre.
  unfold counter_token_core, Resource.weaken_core_to.
  cbn [Resource.subst_bound_core Resource.subst_formals_core].
  change (Assertion.procedure_args read_procedure) with ([TRef] : context).
  cbn [Resource.Assertions.subst_bound_expr_list
    Resource.Assertions.subst_formals_expr_list
    Resource.Assertions.subst_bound_expr Resource.Assertions.subst_bound_ref
    Resource.Assertions.subst_formals_expr
    Resource.Assertions.subst_formals_ref].
  unfold RH.Assertions.expr_list_formal_subst.
  rewrite lookup_expr_list_here. reflexivity.
Qed.

Definition client_made_store :
    symbolic_store (runtime_decls [TInt; TRef]) (procedure_args client_procedure) [TRef] :=
  RuleValidity.IR.update_store_with_bound (keep := keep_runtime_var) client_entry_store (LThere (LHere eq_refl)).

Definition client_exit_store :
    symbolic_store (runtime_decls [TInt; TRef]) (procedure_args client_procedure) [TInt; TRef] :=
  RuleValidity.IR.update_store_with_bound (keep := keep_runtime_var) client_made_store (LHere eq_refl).

Lemma client_made_location {keep} (Hkeep : keep _ = true) :
  RuleValidity.IR.symbolize_expr client_made_store (PEVar (LThere (LHere Hkeep))) =
    ERef (RefBound MHere).
Proof. reflexivity. Qed.

Lemma client_exit_return :
  lookup_store client_exit_store _ (LThere (LHere (keep := keep_all) eq_refl)) =
    RefBound (MThere MHere).
Proof. reflexivity. Qed.

Lemma client_make_call :
  HoareRules.RavenHoareTriple
    (Resource.RState client_entry_store Resource.CTrue)
    (TCall make_procedure PENil (CTStore false (LThere (LHere eq_refl))))
    (Resource.ResourceExists TRef
      (Resource.RState client_made_store
        (counter_token_core (ERef (RefBound MHere))))).
Proof.
  eapply Rules.RTConsequence; [eapply Rules.RTCallStore | | ].
  3: { cbn [RuleValidity.IR.symbolize_expr_list
         RH.Assertions.weaken_expr_list].
       rewrite make_instantiated_post.
       apply Rules.resource_prenex_entails_refl. }
  2: { cbn [RuleValidity.IR.symbolize_expr_list].
       rewrite make_instantiated_pre. apply Rules.CEntailsRefl. }
  vm_compute. discriminate.
Qed.

Lemma client_spawn :
  HoareRules.RavenHoareTriple
    (Resource.RState client_made_store
      (counter_token_core (ERef (RefBound MHere))))
    (TSpawn incr_procedure (PECons (PEVar (LThere (LHere eq_refl))) PENil))
    (Resource.RState client_made_store
      (counter_token_core (ERef (RefBound MHere)))).
Proof.
  eapply Rules.RTConsequence;
    [eapply Rules.RTFrame; eapply Rules.RTSpawn | | ].
  2: { cbn [RuleValidity.IR.symbolize_expr_list]. rewrite client_made_location.
       rewrite counter_resource_instantiated_pre.
       apply Rules.CEntailsStep. apply Rules.CESDuplicate. reflexivity. }
  2: { cbn [RH.Resource.prenex_and].
       apply Rules.RPEBody. split; [reflexivity |].
       apply Rules.CEntailsStep. apply Rules.CESAndElimR. }
  vm_compute. discriminate.
Qed.

Lemma client_read_call :
  HoareRules.RavenHoareTriple
    (Resource.RState client_made_store
      (counter_token_core (ERef (RefBound MHere))))
    (TCall read_procedure (PECons (PEVar (LThere (LHere eq_refl))) PENil)
      (CTStore false (LHere eq_refl)))
    (Resource.ResourceExists TInt
      (Resource.RState client_exit_store
        (counter_token_core (ERef (RefBound (MThere MHere)))))).
Proof.
  eapply Rules.RTConsequence;
    [eapply Rules.RTFrame; eapply Rules.RTCallStore | | ].
  2: { cbn [RuleValidity.IR.symbolize_expr_list].
       change (Assertion.procedure_return read_procedure) with TInt.
       rewrite client_made_location, read_instantiated_pre.
       apply Rules.CEntailsStep. apply Rules.CESDuplicate. reflexivity. }
  2: { cbn [RH.Resource.prenex_and RH.Resource.weaken_core
         RH.Assertions.weaken_expr_list RH.Assertions.weaken_expr
         RH.Assertions.weaken_ref].
       apply Rules.RPEMono. apply Rules.RPEBody. split; [reflexivity |].
       apply Rules.CEntailsStep. apply Rules.CESAndElimR. }
  vm_compute. discriminate.
Qed.

Lemma client_resource_body_derivation :
  HoareRules.RavenHoareTriple
    (RuleValidity.Hoare.procedure_body_pre client_typed_procedure)
    client_typed_body
    (RuleValidity.Hoare.procedure_body_post client_typed_procedure
      client_exit_store (RefBound (MThere MHere))).
Proof.
  unfold RuleValidity.Hoare.procedure_body_pre,
    RuleValidity.Hoare.procedure_body_post,
    client_typed_procedure, client_typed_body.
  cbn [procedure_entry_store procedure_precondition
    procedure_postcondition RuleValidity.Hoare.existentially_close_prenex
    RuleValidity.Hoare.existentially_close_prenex_at].
  cbn [IR.Resource.subst_bound_core Assertions.subst_bound_expr_list
    Assertions.subst_bound_expr Assertions.subst_bound_ref].
  eapply Rules.RTSeq; [exact client_make_call |].
  apply Rules.RTPrenexPreserve.
  eapply Rules.RTSeq; [exact client_spawn |].
  eapply Rules.RTConsequence; [exact client_read_call | |].
  - apply Rules.CEntailsRefl.
  - apply Rules.RPEMono. apply Rules.RPEBody. split; [reflexivity |].
    apply Rules.CEntailsStep. apply Rules.CESTrueIntro.
Qed.

Lemma read_restricted_fragment_accepted :
  NormalizationBase.restricted_fragment_accepted read_typed_body.
Proof. vm_compute. reflexivity. Qed.

Lemma incr_restricted_fragment_accepted :
  NormalizationBase.restricted_fragment_accepted incr_typed_body.
Proof. vm_compute. reflexivity. Qed.

Lemma make_restricted_fragment_accepted :
  NormalizationBase.restricted_fragment_accepted make_typed_body.
Proof. vm_compute. reflexivity. Qed.

Lemma client_restricted_fragment_accepted :
  NormalizationBase.restricted_fragment_accepted client_typed_body.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** The analyzed procedure bodies

    [analyzed_triple] wants three things: an analysis certificate
    (under the framework's [contract_cost_model]), the [RavenHoareRules]
    derivation, and the executable restricted-fragment check.  Nothing else -- no alignment,
    no normalization.  The certificate comes from
    [analyze_builds_certificate], so it never has to be inspected. *)

Module CN := RuleValidity.CertifiedNormalization.

Lemma read_analysis :
  CounterAtomicity.analyze
      (counter_closed_state counter_mask) read_typed_body =
    inr read_exit_state.
Proof. reflexivity. Qed.

Lemma incr_analysis :
  CounterAtomicity.analyze
      (counter_closed_state counter_mask) incr_typed_body =
    inr (counter_closed_state counter_mask).
Proof. reflexivity. Qed.

(** [make] exits with the instance it allocated, named by the level of its
    local. *)
Definition make_exit_state : CounterAtomicity.analysis_state :=
  CounterAtomicity.AnalysisState
    {[(counter_invariant, Some [CounterAtomicity.AtomLevel 1])]} [] false false.

Lemma make_analysis :
  CounterAtomicity.analyze
      (counter_closed_state ∅) make_typed_body =
    inr make_exit_state.
Proof. reflexivity. Qed.

Lemma client_analysis :
  CounterAtomicity.analyze
      (counter_closed_state ∅) client_typed_body =
    inr (counter_closed_state counter_mask).
Proof. reflexivity. Qed.

Definition client_analyzed_certificate :=
  CounterAtomicity.analyze_builds_certificate
    (counter_closed_state ∅) client_typed_body
    (counter_closed_state counter_mask) client_analysis.

Definition read_analyzed_certificate :=
  CounterAtomicity.analyze_builds_certificate
    (counter_closed_state counter_mask) read_typed_body
    read_exit_state read_analysis.

Definition incr_analyzed_certificate :=
  CounterAtomicity.analyze_builds_certificate
    (counter_closed_state counter_mask) incr_typed_body
    (counter_closed_state counter_mask) incr_analysis.

Definition make_analyzed_certificate :=
  CounterAtomicity.analyze_builds_certificate
    (counter_closed_state ∅) make_typed_body
    make_exit_state make_analysis.

Definition read_analyzed_body :
  ProcedureValidity.analyzed_body_valid read_typed_procedure.
Proof.
  unfold ProcedureValidity.analyzed_body_valid.
  unshelve refine (@ProcedureValidity.AnalyzedBodyCertificate _ _ _
    (runtime_decls [TRef; TInt; TInt]) read_procedure read_typed_procedure counter_mask
    (counter_closed_state counter_mask) read_exit_state
    [TInt; TInt; TInt] read_exit_store (RefBound MHere)
    _ _ _ _ _ _ _ _).
  8: { refine {| CN.analyzed_certificate := read_analyzed_certificate;
                 CN.analyzed_hoare := read_resource_body_derivation;
                 CN.analyzed_restricted :=
                   read_restricted_fragment_accepted |}. }
  - reflexivity.
  - constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold read_exit_state. simpl. rewrite counter_mask_close. set_solver.
Defined.

Definition incr_analyzed_body :
  ProcedureValidity.analyzed_body_valid incr_typed_procedure.
Proof.
  unfold ProcedureValidity.analyzed_body_valid.
  unshelve refine (@ProcedureValidity.AnalyzedBodyCertificate _ _ _
    (runtime_decls [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit]) incr_procedure
    incr_typed_procedure counter_mask
    (counter_closed_state counter_mask)
    (counter_closed_state counter_mask)
    [TBool; TInt; TInt; TInt; TInt; TInt] incr_exit_store
    incr_return_reference _ _ _ _ _ _ _ _).
  8: { refine {| CN.analyzed_certificate := incr_analyzed_certificate;
                 CN.analyzed_hoare := incr_resource_body_derivation;
                 CN.analyzed_restricted :=
                   incr_restricted_fragment_accepted |}. }
  - reflexivity.
  - constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. set_solver.
Defined.

Definition make_analyzed_body :
  ProcedureValidity.analyzed_body_valid make_typed_procedure.
Proof.
  unfold ProcedureValidity.analyzed_body_valid.
  unshelve refine (@ProcedureValidity.AnalyzedBodyCertificate _ _ _
    ([runtime_val TRef; runtime_var TRef]) make_procedure make_typed_procedure ∅
    (counter_closed_state ∅)
    make_exit_state
    [TRef; TRef] make_exit_store (RefBound MHere) _ _ _ _ _ _ _ _).
  8: { refine {| CN.analyzed_certificate := make_analyzed_certificate;
                 CN.analyzed_hoare := make_resource_body_derivation;
                 CN.analyzed_restricted :=
                   make_restricted_fragment_accepted |}. }
  - reflexivity.
  - constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. set_solver.
Defined.

Definition client_analyzed_body :
  ProcedureValidity.analyzed_body_valid client_typed_procedure.
Proof.
  unfold ProcedureValidity.analyzed_body_valid.
  unshelve refine (@ProcedureValidity.AnalyzedBodyCertificate _ _ _
    (runtime_decls [TInt; TRef]) client_procedure client_typed_procedure ∅
    (counter_closed_state ∅)
    (counter_closed_state counter_mask)
    [TInt; TRef] client_exit_store (RefBound (MThere MHere))
    _ _ _ _ _ _ _ _).
  8: { refine {| CN.analyzed_certificate := client_analyzed_certificate;
                 CN.analyzed_hoare := client_resource_body_derivation;
                 CN.analyzed_restricted :=
                   client_restricted_fragment_accepted |}. }
  - exact client_exit_return.
  - constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. set_solver.
Defined.

(** The module-soundness instantiation below is stated in Iris; its proof
    mode is imported only here, so the proofs above keep the standard
    [rewrite]. *)
Import iris.base_logic.lib.iprop iris.base_logic.lib.invariants
  iris.base_logic.lib.fancy_updates iris.proofmode.proofmode.

(* ================================================================== *)
(** * Instantiating the analyzed adequacy boundary

    [raven_module_soundness] is stated for the elaborated module and is
    parameterized over a ghost-resource factory and analyzed-module
    certificates.  This section
    supplies them for the monotonic counter. *)

Section CounterGhostFactory.
Context {Sigma : iris.base_logic.lib.iprop.gFunctors}.
Context `{!invGS Sigma}.

(** ** The ghost-resource factory

    The factory interface is indexed by the concrete [simpLangG], so a
    faithful implementation may now connect the allocation rule's
    [ghost_dom_frag] witness to exclusive ownership of a ghost cell.  The
    counter still uses the smaller validity-only
    interpretation: its currently declared contracts are [CPure True], so
    the example does not yet rely on that exclusivity. *)
Definition counter_ghost_own
    (_ : RuleValidity.RuntimeLifting.simpLangG Sigma) (_ : unit)
    (field : Core.field_id)
    (location : RuleValidity.IR.Core.tval Core.TRef)
    (chunk : RuleValidity.IR.Core.tval (IR.Assertions.field_type field)) :
    iProp Sigma :=
  (⌜RuleValidity.IR.Core.tval_ra_valid chunk⌝)%I.

Definition counter_ghost_factory :
  Runtime.runtime_ghost_resource_factory Sigma
    RuntimeErasure.ghost_heap_namespace.
Proof.
  unshelve econstructor.
  { exact (fun _ => unit). }
  { exact counter_ghost_own. }
  - abstract (intros; unfold counter_ghost_own; apply _).
  - abstract (intros simpLangG0 resource E field resource_name field_name
      address chunk Hfield HE Hvalid;
    iIntros "_"; iModIntro; unfold counter_ghost_own; iPureIntro;
    set (t := IR.Assertions.field_type field) in *; clearbody t;
    generalize (eq_sym Hfield); clear Hfield; intro Heq; destruct Heq;
    exact Hvalid).
  - abstract (intros simpLangG0 resource E field location old_chunk new_chunk
      Hfpu;
    unfold counter_ghost_own; iIntros "_"; iModIntro; iPureIntro;
    revert Hfpu;
    set (t := IR.Assertions.field_type field) in *; clearbody t;
    destruct t; dependent destruction old_chunk;
      dependent destruction new_chunk; cbn; try contradiction;
    intro Hfpu;
    apply (proj1 (proj2 (mono_nat_ra.mn_fpuAxiom _ _ Hfpu)))).
  - abstract (intros simpLangG0; iModIntro; iExists tt; stdpp.tactics.done).
Defined.

End CounterGhostFactory.

(* ================================================================== *)
(** * The analyzed module certificate, and the module boundary *)

(** Which body answers for which registered procedure.  Membership is a
    [Prop], so the body is selected by choice from the fact that one exists
    for each registered procedure. *)
Definition counter_analyzed_bodies packed
    (Hin : List.In packed
      (procedure_entries
        (RuleValidity.Hoare.module_procedures counter_module))) :
    ProcedureValidity.packed_analyzed_body packed.
Proof.
  apply (fun Hexists => proj1_sig (constructive_indefinite_description
    (fun _ : ProcedureValidity.packed_analyzed_body packed => True) Hexists)).
  simpl in Hin.
  destruct Hin as [Hin | [Hin | [Hin | [Hin | []]]]];
    dependent destruction Hin.
  - exists read_analyzed_body. exact I.
  - exists incr_analyzed_body. exact I.
  - exists make_analyzed_body. exact I.
  - exists client_analyzed_body. exact I.
Defined.

(** Every invariant a procedure requires or may allocate is declared. *)
Lemma counter_allocations_declared packed
    (Hin : List.In packed
      (procedure_entries
        (RuleValidity.Hoare.module_procedures counter_module))) :
  Adequacy.packed_allocations_declared counter_module packed.
Proof.
  simpl in Hin.
  destruct Hin as [Hin | [Hin | [Hin | [Hin | []]]]];
    dependent destruction Hin; vm_compute; set_solver.
Qed.

Definition counter_analyzed_module :
  Adequacy.module_analysis counter_module :=
  {| Adequacy.module_analysis_bodies := counter_analyzed_bodies;
     Adequacy.module_analysis_declared := counter_allocations_declared |}.

(** ** The module boundary, instantiated

    Everything [raven_module_soundness] is parameterized over is supplied
    by this example: the module, the ghost-resource factory, and the analyzed
    module certificate.  Runtime registration is derived from the module. *)
Section CounterModuleSoundness.
Context {Sigma : iris.base_logic.lib.iprop.gFunctors}.
Context `{!invGS Sigma}.
Context `{!RuleValidity.RuntimeGhost.heapGpreS Sigma}.
Context `{!RuleValidity.RuntimeModel.invTokenGpreS Sigma}.
Definition counter_module_soundness :=
  Adequacy.raven_module_soundness counter_module
    counter_ghost_factory counter_analyzed_module.

End CounterModuleSoundness.

End CounterMonotonic.
