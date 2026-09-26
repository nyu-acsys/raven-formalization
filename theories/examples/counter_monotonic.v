From Coq Require Import Ascii ClassicalEpsilon List String ZArith
  Program.Equality.
From stdpp Require Import namespaces sets.

From raven Require Import runtime.erasure analysis.structured_certificates examples.mono_nat_ra surface.syntax surface.elaboration verification.expressions verification.assertions verification.ir verification.procedures analysis.normalization_base analysis.normalization soundness.runtime_model soundness.rule_validity soundness.procedure_validity soundness.adequacy.

Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

(** The monotonic counter, verified end to end.

    This file deliberately starts from Raven-like surface syntax; the typed
    Hoare derivations, analysis, normalization, and procedure-validity
    witnesses below are all stated against the elaborated program. *)
Module CounterMonotonic.

Module CounterValues.
  Definition ra_carrier (_ : source_name) : Type := MonoNat.
  Definition ra_eqb (_ : source_name) (left right : MonoNat) : bool :=
    match left, right with
    | Some left', Some right' => Nat.eqb left' right'
    | None, None => true
    | _, _ => false
    end.
  Lemma ra_eqb_eq r (left right : ra_carrier r) :
    ra_eqb r left right = true <-> left = right.
  Proof.
    destruct left as [left |], right as [right |]; simpl.
    - rewrite Nat.eqb_eq. split; [intros -> | intros H]; [reflexivity |].
      by injection H as ->.
    - split; discriminate.
    - split; discriminate.
    - split; reflexivity.
  Qed.
  Definition ra_id (_ : source_name) : MonoNat := Some 0%nat.
  Definition ra_of_int (_ : source_name) (value : Z) : MonoNat :=
    mn_of_int value.
  Definition ra_valid (_ : source_name) : MonoNat -> Prop := mn_valid.
  Definition ra_fpu_allowed (_ : source_name) : MonoNat -> MonoNat -> Prop :=
    mn_fpuValid.
  Definition ra_values : Core.RAValueConfig :=
    Core.RAValueConfigData ra_carrier ra_eqb ra_eqb_eq ra_id ra_of_int
      ra_valid ra_fpu_allowed.
End CounterValues.

Definition counter_field : Core.field_id := 1%positive.
Definition ghost_field : Core.field_id := 2%positive.
Definition counter_invariant : Core.inv_id := 1%positive.
Definition read_procedure : Core.proc_id := 1%positive.
Definition incr_procedure : Core.proc_id := 2%positive.
Definition make_procedure : Core.proc_id := 3%positive.

Module CounterLogic.
  Definition field_type (field : Core.field_id) :=
    if Pos.eqb field ghost_field
    then Core.TRA h_ra
    else Core.TInt.
  Definition predicate_args (_ : Core.pred_id) : Core.context := [].
  Definition invariant_args (_ : Core.inv_id) : Core.context :=
    [Core.TRef].
  (** [read] and [incr] take the counter reference; [make] takes none. *)
  Definition procedure_args (procedure : Core.proc_id) :
      Core.context :=
    if Pos.eqb procedure make_procedure then [] else [Core.TRef].
  Definition procedure_return (procedure : Core.proc_id) :
      Core.typ :=
    if Pos.eqb procedure read_procedure then Core.TInt
    else if Pos.eqb procedure make_procedure then Core.TRef
    else Core.TUnit.
  Definition logic : Assertion.LogicSignature :=
    Assertion.LogicSignatureData field_type predicate_args invariant_args
      procedure_args procedure_return.
End CounterLogic.

Lemma counter_field_type_eq : CounterLogic.field_type counter_field =
    Core.TInt.
Proof. reflexivity. Qed.

Lemma ghost_field_type_eq : CounterLogic.field_type ghost_field =
    Core.TRA h_ra.
Proof. reflexivity. Qed.


(** The executable runtime is parameterized by a resource-independent naming
    configuration.  We use unary strings here: their lengths are the natural
    number represented by the positive identifier, giving a small but fully
    constructive injective encoding.  Namespace prefixes keep the three
    program name spaces separate, while [ndot_ne_disjoint] supplies the
    required invariant and ghost-heap separation. *)
Module RuntimeConfiguration.
  Fixpoint repeat_name (n : nat) : string :=
    match n with
    | O => EmptyString
    | S n' => String "x"%char (repeat_name n')
    end.

  Definition positive_name (p : positive) : string :=
    repeat_name (Pos.to_nat p).

  Lemma repeat_name_length n : String.length (repeat_name n) = n.
  Proof. induction n; simpl; congruence. Qed.

  Lemma string_length_app (left right : string) :
      String.length (left ++ right) =
        Nat.add (String.length left) (String.length right).
  Proof. induction left; simpl; auto. Qed.

  Lemma positive_name_injective : Inj (=) (=) positive_name.
  Proof.
    intros left right Heq.
    apply Pos2Nat.inj.
    unfold positive_name in Heq.
    apply f_equal with (f := String.length) in Heq.
    now rewrite !repeat_name_length in Heq.
  Qed.

  Definition field_name (field : Core.field_id) : string :=
    "field_" ++ positive_name field.
  Definition invariant_name (invariant : Core.inv_id) : string :=
    "invariant_" ++ positive_name invariant.
  Definition procedure_name (procedure : Core.proc_id) : string :=
    "procedure_" ++ positive_name procedure.

  Lemma prefixed_positive_name_injective prefix :
      Inj (=) (=) (fun p : positive => prefix ++ positive_name p).
  Proof.
    intros left right Heq.
    apply Pos2Nat.inj.
    apply f_equal with (f := String.length) in Heq.
    rewrite !string_length_app in Heq.
    unfold positive_name in Heq.
    rewrite !repeat_name_length in Heq.
    lia.
  Qed.

  Definition invariant_namespace (invariant : Core.inv_id) : namespace :=
    nroot .@ ("invariant_" ++ positive_name invariant).
  Definition ghost_heap_namespace : namespace := nroot .@ "ghost_heap".

  Definition field_name_injective := prefixed_positive_name_injective "field_".
  Definition invariant_name_injective :=
    prefixed_positive_name_injective "invariant_".
  Definition procedure_name_injective :=
    prefixed_positive_name_injective "procedure_".

  Lemma invariant_suffix_ne_ghost invariant :
      ("invariant_" ++ positive_name invariant) <> "ghost_heap".
  Proof. intro Heq; discriminate Heq. Qed.

  Definition invariant_namespaces_disjoint :=
    fun left right Hneq =>
      ndot_ne_disjoint nroot
        ("invariant_" ++ positive_name left)
        ("invariant_" ++ positive_name right)
        (fun Heq => Hneq
          (prefixed_positive_name_injective "invariant_" left right Heq)).

  Definition invariant_ghost_namespace_disjoint :=
    fun invariant =>
      ndot_ne_disjoint nroot
        ("invariant_" ++ positive_name invariant) "ghost_heap"
        (invariant_suffix_ne_ghost invariant).

  Definition config : RuntimeErasure.RuntimeConfiguration :=
    RuntimeErasure.RuntimeConfigurationData field_name field_name_injective
      invariant_name invariant_name_injective invariant_namespace
      invariant_namespaces_disjoint ghost_heap_namespace
      invariant_ghost_namespace_disjoint procedure_name
      procedure_name_injective.
End RuntimeConfiguration.

Module IR := RuleValidity.IR.
Module Resource := IR.Resource.
#[local] Existing Instances CounterRAConfig.ra_config CounterLogic.logic
  RuntimeConfiguration.config.
Import Core IR IR.Core IR.Assertions Elaboration.

Definition counter_environment : Elaboration.elaboration_environment :=
  Elaboration.ElaborationEnvironment
    [Elaboration.FieldDecl "c" counter_field;
     Elaboration.FieldDecl "h" ghost_field]
    [Elaboration.ProcedureSignature "read" read_procedure;
     Elaboration.ProcedureSignature "incr" incr_procedure;
     Elaboration.ProcedureSignature "make" make_procedure]
    [Elaboration.InvariantSignature "counterInv" counter_invariant]
    [].

Definition x := name "x".
Definition v1 := name "v1".
Definition v2 := name "v2".
Definition new_v1 := name "new_v1".
Definition res := name "res".
Definition call_res := name "call_res".
Definition ret := name "ret".
Definition c := name "c".
Definition h := name "h".
Definition counterInv := name "counterInv".
Definition incr := name "incr".

Definition read_variables : IR.named_context [TRef; TInt; TInt] :=
  IR.NCCons "x" TRef
    (IR.NCCons "v1" TInt (IR.NCCons "ret" TInt IR.NCNil)).

Definition incr_variables :
    IR.named_context [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit] :=
  IR.NCCons "x" TRef
    (IR.NCCons "v1" TInt
      (IR.NCCons "new_v1" TInt
        (IR.NCCons "v2" TInt
          (IR.NCCons "res" TBool
            (IR.NCCons "call_res" TUnit
              (IR.NCCons "ret" TUnit IR.NCNil)))))).

Definition make_variables : IR.named_context [TRef; TRef] :=
  IR.NCCons "x" TRef
    (IR.NCCons "ret" TRef IR.NCNil).

Definition read_source : source_stmt :=
  raven_stmt {{
    unfold counterInv(x);
    v1 := x . c;
    fold counterInv(x);
    ret := v1
  }}.

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
    [incr_source]'s atomic block. *)
Definition cas_typed_body :
    stmt [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit] :=
  elaborated_body
    (elaborate_stmt counter_environment incr_variables cas_source)
    ltac:(vm_compute; exact I).

(** An explicit atomic block is Raven's trust declaration; the resource
    rule for [TAtomic] has no separate per-block trust premise to
    discharge. *)

(** Superseded source shape, retained as documentation while the generic
    normalizer does not yet implement branch-local closes followed by
    branch-local continuations.

Definition incr_source_branch_local_close : source_stmt :=
  raven_stmt {{
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
    if (! res) {
      fold counterInv(x);
      incr(x)
    } else {
      fpu(x . h, v1, v1 + 1);
      fold counterInv(x)
    };
    ret := tt
  }}.
*)

(** Baseline-equivalent formulation used by the first end-to-end library
    proof.  The invariant is closed once, after the success-only ghost
    update, and retry is selected only after the close.  This moves no
    physical step across the fold: the second conditional contains only the
    recursive call (or no-op), while the first conditional is entirely
    inside the trusted atomic access. *)
Definition incr_source : source_stmt :=
  raven_stmt {{
    unfold counterInv(x);
    v1 := x . c;
    fold counterInv(x);
    new_v1 := v1 + 1;
    unfold counterInv(x);
    (atomic {
       v2 := x . c;
       if (v2 == v1) {
         x . c := new_v1;
         res := true
       } else {
         res := false
       }
     };
     if (res) {
       fpu(x . h, v1, v1 + 1)
     });
    fold counterInv(x);
    if (! res) {
      incr(x)
    };
    ret := tt
  }}.

Definition make_source : source_stmt :=
  raven_stmt {{
    x := new(c: 0, h: 0);
    fold counterInv(x);
    ret := x
  }}.

(** Intrinsic bodies are definitionally the successful elaboration results.
    Keeping the equations named lets later certificates rewrite back to the
    readable source without depending on reduction through the elaborator. *)
Definition read_typed_body : stmt [TRef; TInt; TInt] :=
  elaborated_body
    (elaborate_stmt counter_environment read_variables read_source)
    ltac:(vm_compute; exact I).

Definition incr_typed_body :
    stmt [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit] :=
  elaborated_body
    (elaborate_stmt counter_environment incr_variables incr_source)
    ltac:(vm_compute; exact I).

(** Cache the intrinsic syntax produced by elaboration.  Structural proofs
    below can unfold this VM-normalized term without re-running the surface
    elaborator at every constructor boundary. *)
Definition incr_typed_body_normalized := Eval vm_compute in incr_typed_body.

Lemma incr_typed_body_normalized_eq :
  incr_typed_body = incr_typed_body_normalized.
Proof. vm_compute. reflexivity. Qed.

Definition make_typed_body : stmt [TRef; TRef] :=
  elaborated_body
    (elaborate_stmt counter_environment make_variables make_source)
    ltac:(vm_compute; exact I).




Definition read_formals : IR.pvar_list [TRef; TInt; TInt] [TRef] :=
  IR.PVCons MHere IR.PVNil.
Definition incr_formals :
    IR.pvar_list [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit] [TRef] :=
  IR.PVCons MHere IR.PVNil.
Definition make_formals : IR.pvar_list [TRef; TRef] [] :=
  IR.PVNil.
Definition counter_token_core {F Δ} (location : expr F Δ TRef) :
    Resource.core_assertion F Δ :=
  Resource.CInvariant counter_invariant (ExprCons location ExprNil).

Definition counter_invariant_body {Γ} : assertion Γ [TRef] [] :=
  AExists TInt
    (AAnd
      (AGhostOwn ghost_field (ERef (RefFormal MHere))
        (EUnOp (URAOfInt h_ra) (ERef (RefBound MHere))))
      (AOwn counter_field (ERef (RefFormal MHere))
        (ERef (RefBound MHere)))).

Definition read_typed_procedure :
    typed_procedure [TRef; TInt; TInt] read_procedure :=
  @TypedProcedure _ _ [TRef; TInt; TInt] read_procedure read_variables
    (IR.NCCons "x" TRef IR.NCNil) read_formals
    (MThere (MThere MHere))
    (counter_token_core (ERef (RefFormal MHere)))
    (Resource.CPure True) read_typed_body.

Definition incr_typed_procedure :
    typed_procedure [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit]
      incr_procedure :=
  @TypedProcedure _ _ [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit] incr_procedure
    incr_variables
    (IR.NCCons "x" TRef IR.NCNil) incr_formals
    (MThere (MThere (MThere (MThere (MThere (MThere MHere))))))
    (counter_token_core (ERef (RefFormal MHere)))
    (Resource.CPure True) incr_typed_body.

Definition make_typed_procedure :
    typed_procedure [TRef; TRef] make_procedure :=
  @TypedProcedure _ _ [TRef; TRef] make_procedure make_variables IR.NCNil make_formals
    (MThere MHere) (Resource.CPure True)
    (counter_token_core (ERef (RefBound MHere))) make_typed_body.

(** Readable aliases for the canonical stores derived from each procedure's
    formal layout.  They are definitions, not program-supplied data. *)
Definition read_entry_store :=
  procedure_entry_store _ _ read_typed_procedure.
Definition incr_entry_store :=
  procedure_entry_store _ _ incr_typed_procedure.
Definition make_entry_store :=
  procedure_entry_store _ _ make_typed_procedure.

Lemma read_typed_procedure_wf : procedure_wf read_typed_procedure.
Proof.
  constructor.
  - simpl. repeat constructor; set_solver.
  - simpl. repeat constructor; tauto.
  - vm_compute. intros [H | []]. discriminate H.
  - simpl. repeat split; exact I.
  - simpl. repeat split; exact I.
Qed.

Lemma incr_typed_procedure_wf : procedure_wf incr_typed_procedure.
Proof.
  constructor.
  - simpl. repeat constructor; set_solver.
  - simpl. repeat constructor; tauto.
  - vm_compute. intros [H | []]. discriminate H.
  - simpl. repeat split; exact I.
  - simpl. repeat split; exact I.
Qed.

Lemma make_typed_procedure_wf : procedure_wf make_typed_procedure.
Proof.
  constructor.
  - simpl. repeat constructor; set_solver.
  - simpl. constructor.
  - simpl. tauto.
  - simpl. repeat split; exact I.
  - simpl. repeat split; exact I.
Qed.

Definition counter_typed_procedures : typed_procedure_environment.
Proof.
  refine (TypedProcedureEnvironment
    [pack_typed_procedure read_typed_procedure;
     pack_typed_procedure incr_typed_procedure;
     pack_typed_procedure make_typed_procedure] _ _ _).
  - simpl. repeat constructor; set_solver.
  - constructor.
    + exact read_typed_procedure_wf.
    + constructor.
      * exact incr_typed_procedure_wf.
      * constructor.
        -- exact make_typed_procedure_wf.
        -- constructor.
  - apply procedure_signature_coherent_of_nodup.
    simpl. repeat constructor; set_solver.
Defined.

Definition counter_mask : RuleValidity.Hoare.mask := {[counter_invariant]}.

(** The contract environment for the counter module.  The
    procedure half is read straight off the typed table: with contracts
    core-shaped, [procedure_precondition] and [procedure_postcondition]
    already have exactly the types [RESOURCE_CONTRACT_ENV] asks for, so
    there is nothing to translate.  The [None] branches are unreachable
    for the three declared procedures and are filled with [CPure True],
    which is well-typed at every index. *)
Definition counter_invariant_body_core : Resource.core_assertion [TRef] [] :=
  Resource.CExists TInt
    (Resource.CAnd
      (Resource.CGhostOwn ghost_field (ERef (RefFormal MHere))
        (EUnOp (URAOfInt h_ra) (ERef (RefBound MHere))))
      (Resource.COwn counter_field (ERef (RefFormal MHere))
        (ERef (RefBound MHere)))).

Lemma counter_invariant_body_core_erases {Γ} :
  Resource.core_to_assertion counter_invariant_body_core =
    @counter_invariant_body Γ.
Proof. reflexivity. Qed.

Module CounterResourceContracts.

  (** The counter declares no predicates.  Its procedure masks are
      inferred from the contracts below. *)
  Definition declared_predicates : list pred_id := [].

  Definition predicate_body (_ : pred_id) :
      Resource.core_assertion [] [] := Resource.CPure False.
  Lemma predicate_body_entry_free predicate :
    Resource.core_entry_free (predicate_body predicate).
  Proof. simpl. exact I. Qed.

  Definition invariant_body (_ : inv_id) :
      Resource.core_assertion [TRef] [] := counter_invariant_body_core.
  Lemma invariant_body_entry_free invariant :
    Resource.core_entry_free (invariant_body invariant).
  Proof. simpl. repeat split; exact I. Qed.

  Definition contract_pre (procedure : proc_id) :
      Resource.core_assertion (CounterLogic.procedure_args procedure) [] :=
    match lookup_typed_procedure_at procedure
            (procedure_entries counter_typed_procedures) with
    | Some (existT _ callee) => procedure_precondition _ _ callee
    | None => Resource.CPure True
    end.

  Definition contract_post (procedure : proc_id) :
      Resource.core_assertion (CounterLogic.procedure_args procedure)
        (return_context (CounterLogic.procedure_return procedure)) :=
    match lookup_typed_procedure_at procedure
            (procedure_entries counter_typed_procedures) with
    | Some (existT _ callee) => procedure_postcondition _ _ callee
    | None => Resource.CPure True
    end.

  (** The callee has a declaration with a verified body. *)
  Definition procedure_verified (procedure : proc_id) : Prop :=
    lookup_typed_procedure counter_typed_procedures procedure <> None.

  Definition contracts : RuleValidity.Hoare.ResourceHoare.ResourceContractEnv :=
    RuleValidity.Hoare.ResourceHoare.ResourceContractEnvData declared_predicates
      predicate_body predicate_body_entry_free invariant_body
      invariant_body_entry_free contract_pre contract_post
      procedure_verified.
End CounterResourceContracts.
#[local] Existing Instance CounterResourceContracts.contracts.

Module CounterProcedureContracts.
  Import RuleValidity.Hoare.

  Definition procedures := counter_typed_procedures.

  (** Section 11: the callee is produced by the computable dependent
      lookup [lookup_typed_procedure_at], not extracted from a [Prop].
      The previous proof needed [constructive_indefinite_description];
      this one uses no axiom at all. *)
  Definition procedure_selects : forall identity,
    CounterResourceContracts.procedure_verified identity ->
    { callee_variables : context &
      { procedure : typed_procedure callee_variables identity |
        lookup_typed_procedure procedures identity =
          Some (pack_typed_procedure procedure) } }.
  Proof.
    intros identity Hverified.
    destruct (lookup_typed_procedure_at identity (procedure_entries procedures))
      as [[callee_variables callee] |] eqn:Hdep.
    - exists callee_variables, callee.
      pose proof (lookup_typed_procedure_at_spec identity
        (procedure_entries procedures)) as Hspec.
      rewrite Hdep in Hspec. exact Hspec.
    - exfalso. apply Hverified.
      pose proof (lookup_typed_procedure_at_spec identity
        (procedure_entries procedures)) as Hspec.
      rewrite Hdep in Hspec. exact Hspec.
  Defined.

  (** Both declared contracts are read off the table by construction, so
      coherence is a property of [lookup_typed_procedure_at] rather than
      of the individual procedures. *)
  Lemma lookup_at_of_lookup {Γ} {identity : proc_id}
      (procedure : typed_procedure Γ identity) :
    lookup_typed_procedure procedures identity =
      Some (pack_typed_procedure procedure) ->
    lookup_typed_procedure_at identity
        (procedure_entries counter_typed_procedures) =
      Some (existT Γ procedure).
  Proof.
    intro Hlookup.
    change counter_typed_procedures with procedures.
    pose proof (lookup_typed_procedure_at_spec identity
      (procedure_entries procedures)) as Hspec.
    destruct (lookup_typed_procedure_at identity
      (procedure_entries procedures)) as [[callee_variables callee] |]
      eqn:Hdep.
    - assert (Hpack : pack_typed_procedure callee =
        pack_typed_procedure procedure).
      { apply (lookup_packed_procedure_unique identity
          (procedure_entries procedures)).
        - exact (procedure_ids_unique procedures).
        - exact Hspec.
        - unfold lookup_typed_procedure in Hlookup. exact Hlookup. }
      dependent destruction Hpack. reflexivity.
    - unfold lookup_typed_procedure in Hlookup.
      rewrite Hlookup in Hspec. discriminate Hspec.
  Qed.

  Lemma contract_pre_coherent : forall callee_variables identity
      (procedure : typed_procedure callee_variables identity),
    lookup_typed_procedure procedures identity =
      Some (pack_typed_procedure procedure) ->
    CounterResourceContracts.contract_pre identity =
      procedure_precondition _ _ procedure.
  Proof.
    intros callee_variables identity procedure Hlookup.
    unfold CounterResourceContracts.contract_pre.
    rewrite (lookup_at_of_lookup procedure Hlookup). reflexivity.
  Qed.

  Lemma contract_post_coherent : forall callee_variables identity
      (procedure : typed_procedure callee_variables identity),
    lookup_typed_procedure procedures identity =
      Some (pack_typed_procedure procedure) ->
    CounterResourceContracts.contract_post identity =
      procedure_postcondition _ _ procedure.
  Proof.
    intros callee_variables identity procedure Hlookup.
    unfold CounterResourceContracts.contract_post.
    rewrite (lookup_at_of_lookup procedure Hlookup). reflexivity.
  Qed.

  Definition coherence : RuleValidity.Hoare.ProcedureContractCoherence :=
    RuleValidity.Hoare.ProcedureContractCoherenceData procedures procedure_selects
      contract_pre_coherent contract_post_coherent.
End CounterProcedureContracts.
#[local] Existing Instance CounterProcedureContracts.coherence.

(** Mask inference unfolds predicates.  The counter declares none, so this
    checks the mechanism on a small hypothetical declaration: predicate 1
    mentions itself and predicate 2, whose body depends on the counter
    invariant.  Each predicate is unfolded at most once along a path, so the
    recursion terminates and still finds the invariant through the nesting;
    an undeclared predicate contributes nothing. *)
Section MaskInferenceExamples.
Let bodies (predicate : pred_id) :
    Resource.core_assertion (CounterLogic.predicate_args predicate) [] :=
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
Lemma read_entry_location :
  RuleValidity.IR.symbolize_expr read_entry_store (PEVar MHere) =
    ERef (RefFormal MHere).
Proof.
  unfold read_entry_store, procedure_entry_store,
    canonical_procedure_entry_store, RuleValidity.IR.symbolize_expr.
  apply f_equal.
  apply lookup_canonical_procedure_entry_store_singleton.
Qed.

Lemma read_entry_arguments :
  RuleValidity.IR.symbolize_expr_list read_entry_store
      (PECons (PEVar MHere) PENil) =
    ExprCons (ERef (RefFormal MHere)) ExprNil.
Proof.
  cbn [RuleValidity.IR.symbolize_expr_list].
  rewrite read_entry_location.
  reflexivity.
Qed.

Lemma incr_entry_location :
  RuleValidity.IR.symbolize_expr incr_entry_store (PEVar MHere) =
    ERef (RefFormal MHere).
Proof.
  unfold incr_entry_store, procedure_entry_store,
    canonical_procedure_entry_store, RuleValidity.IR.symbolize_expr.
  apply f_equal.
  apply lookup_canonical_procedure_entry_store_singleton.
Qed.
Lemma incr_entry_arguments :
  RuleValidity.IR.symbolize_expr_list incr_entry_store
      (PECons (PEVar MHere) PENil) =
    ExprCons (ERef (RefFormal MHere)) ExprNil.
Proof.
  cbn [RuleValidity.IR.symbolize_expr_list].
  rewrite incr_entry_location.
  reflexivity.
Qed.

Definition read_open_store :
    symbolic_store [TRef; TInt; TInt] [TRef] [TInt] :=
  weaken_store read_entry_store.

Lemma read_open_location :
  RuleValidity.IR.symbolize_expr read_open_store (PEVar MHere) =
    ERef (RefFormal MHere).
Proof.
  pose proof read_entry_location as Hentry.
  unfold RuleValidity.IR.symbolize_expr in Hentry.
  injection Hentry as Hlookup.
  unfold symbolize_expr, read_open_store.
  rewrite RuleValidity.IR.lookup_weaken_store.
  f_equal.
  assert (Hweaken : forall
      (reference : value_ref [TRef] [] TRef),
      reference = RefFormal MHere ->
      @weaken_ref [TRef] [] TRef TInt reference = RefFormal MHere).
  { intros reference Hreference.
    dependent destruction reference; cbn in Hreference |-; try discriminate.
    inversion Hreference. reflexivity. }
  apply Hweaken, Hlookup.
Qed.

Definition read_field_store :
    symbolic_store [TRef; TInt; TInt] [TRef] [TInt; TInt] :=
  RuleValidity.IR.update_store_with_bound read_open_store (MThere MHere).

Lemma update_store_there {F Δ head_type tail_context t}
    (head : value_ref F Δ head_type)
    (tail : symbolic_store tail_context F Δ)
    (target : pvar tail_context t) :
  RuleValidity.IR.update_store_with_bound
      (StoreCons head tail) (MThere target) =
    StoreCons (weaken_ref head)
      (RuleValidity.IR.update_store_with_bound tail target).
Proof.
  unfold RuleValidity.IR.update_store_with_bound,
    Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl).
  reflexivity.
Qed.

Lemma lookup_store_here {F Δ head_type tail_context}
    (head : value_ref F Δ head_type)
    (tail : symbolic_store tail_context F Δ) :
  lookup_store (StoreCons head tail) _ MHere = head.
Proof.
  unfold lookup_store, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl).
  reflexivity.
Qed.

Lemma lookup_store_there {F Δ head_type tail_context t}
    (head : value_ref F Δ head_type)
    (tail : symbolic_store tail_context F Δ)
    (target : pvar tail_context t) :
  lookup_store (StoreCons head tail) _ (MThere target) =
    lookup_store tail _ target.
Proof.
  unfold lookup_store, Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl).
  reflexivity.
Qed.

Lemma update_store_here {F Δ head_type tail_context}
    (head : value_ref F Δ head_type)
    (tail : symbolic_store tail_context F Δ) :
  RuleValidity.IR.update_store_with_bound (StoreCons head tail) MHere =
    StoreCons (RefBound MHere) (weaken_store tail).
Proof.
  unfold RuleValidity.IR.update_store_with_bound,
    Equality.simplification_heq.
  rewrite (proof_irrelevance _ (JMeq_eq JMeq_refl) eq_refl).
  reflexivity.
Qed.

Lemma lookup_update_store_same {Γ F Δ t}
    (store : symbolic_store Γ F Δ) (target : pvar Γ t) :
  lookup_store (RuleValidity.IR.update_store_with_bound store target) _ target =
    RefBound MHere.
Proof.
  induction store; dependent destruction target.
  - rewrite update_store_here, lookup_store_here. reflexivity.
  - rewrite update_store_there, lookup_store_there. apply IHstore.
Qed.

Lemma lookup_update_store_preserves_second
    {tail_context F Δ first_type second_type target_type}
    (store : symbolic_store (first_type :: second_type :: tail_context) F Δ)
    (target : pvar tail_context target_type) :
  lookup_store
      (RuleValidity.IR.update_store_with_bound store
        (MThere (MThere target))) second_type (MThere MHere) =
    weaken_ref (lookup_store store second_type (MThere MHere)).
Proof.
  dependent destruction store. dependent destruction store.
  rewrite !update_store_there, !lookup_store_there, !lookup_store_here.
  reflexivity.
Qed.

Lemma lookup_weaken_store {Γ F Δ t u}
    (store : symbolic_store Γ F Δ) (variable : pvar Γ t) :
  lookup_store (@weaken_store Γ F Δ u store) t variable =
    @weaken_ref F Δ t u (lookup_store store t variable).
Proof.
  induction store; dependent destruction variable.
  - cbn [weaken_store]. rewrite !lookup_store_here. reflexivity.
  - cbn [weaken_store]. rewrite !lookup_store_there. apply IHstore.
Qed.

(** Updating one stack slot leaves every other slot alone, modulo the
    binder the update introduces.  Stating the disequality on
    [member_index] keeps it homogeneous, so the induction needs no
    heterogeneous-equality reasoning.  [lookup_update_store_same] and
    [lookup_update_store_preserves_second] are the two special cases that
    predate it. *)
(** Weakening never disturbs a formal reference, so a slot known to hold
    one keeps holding it after any number of binder introductions.  Stated
    as an implication so [apply] can absorb the index differences the
    canonical entry stores introduce. *)
Lemma weaken_ref_formal_eq {F Δ t u}
    (reference : value_ref F Δ t) (variable : formal F t) :
  reference = RefFormal variable ->
  @weaken_ref F Δ t u reference = RefFormal variable.
Proof. intros ->. reflexivity. Qed.

Lemma lookup_update_store_other {Γ F Δ t u}
    (store : symbolic_store Γ F Δ) (target : pvar Γ u) (variable : pvar Γ t) :
  member_index target <> member_index variable ->
  lookup_store (RuleValidity.IR.update_store_with_bound store target) t variable =
    weaken_ref (lookup_store store t variable).
Proof.
  revert u target t variable.
  induction store as [| head_type tail_context head tail IH];
    intros u target t variable Hne.
  - dependent destruction target.
  - dependent destruction target; dependent destruction variable.
    + exfalso. apply Hne. reflexivity.
    + rewrite update_store_here, !lookup_store_there.
      apply lookup_weaken_store.
    + rewrite update_store_there, !lookup_store_here. reflexivity.
    + rewrite update_store_there, !lookup_store_there.
      apply IH. cbn in Hne. congruence.
Qed.

Lemma rename_bound_store_weaken_store {Γ F Δ u}
    (store : symbolic_store Γ F Δ) :
  rename_bound_store (@weaken_bound_renaming Δ u) store =
    weaken_store store.
Proof.
  induction store; cbn [rename_bound_store weaken_store].
  - reflexivity.
  - f_equal. exact IHstore.
Qed.

Lemma lookup_update_store_preserves_third
    {tail_context F Δ first_type second_type third_type target_type}
    (store : symbolic_store
      (first_type :: second_type :: third_type :: tail_context) F Δ)
    (target : pvar tail_context target_type) :
  lookup_store
      (RuleValidity.IR.update_store_with_bound store
        (MThere (MThere (MThere target)))) third_type
      (MThere (MThere MHere)) =
    weaken_ref (lookup_store store third_type (MThere (MThere MHere))).
Proof.
  dependent destruction store. dependent destruction store.
  dependent destruction store.
  rewrite !update_store_there, !lookup_store_there, !lookup_store_here.
  reflexivity.
Qed.

Lemma read_field_location :
  RuleValidity.IR.symbolize_expr read_field_store (PEVar MHere) =
    ERef (RefFormal MHere).
Proof.
  pose proof read_open_location as Hopen.
  unfold RuleValidity.IR.symbolize_expr in Hopen. injection Hopen as Hopen.
  unfold RuleValidity.IR.symbolize_expr, read_field_store.
  rewrite lookup_update_store_other by (cbn; congruence).
  rewrite Hopen. reflexivity.
Qed.
Lemma counter_mask_close :
  (counter_mask ∖ {[counter_invariant]}) ∪ {[counter_invariant]} =
    counter_mask.
Proof.
  unfold counter_mask. set_solver.
Qed.
Definition read_exit_store :
    symbolic_store [TRef; TInt; TInt] [TRef] [TInt; TInt; TInt] :=
  RuleValidity.IR.update_store_with_bound read_field_store
    (MThere (MThere MHere)).
Lemma interp_typed_equality_true_early {F Δ t}
    (formals : formal_env F) (binders : binder_env Δ) atoms
    (left right : expr F Δ t) :
  interp_expr formals binders atoms (EBinOp (BEq t) left right) =
    Some (VBool true) ->
  interp_expr formals binders atoms left =
    interp_expr formals binders atoms right.
Proof.
  cbn [interp_expr interp_binop].
  destruct (interp_expr formals binders atoms left) as [left_value|]
    eqn:Hleft; [|discriminate].
  destruct (interp_expr formals binders atoms right) as [right_value|]
    eqn:Hright; [|discriminate].
  intros Heq. injection Heq as Heq.
  fold (tval_eqb t left_value right_value) in Heq.
  apply tval_eqb_eq in Heq. subst right_value. congruence.
Qed.
Module HoareRules := RuleValidity.CertifiedNormalization.RavenHoareRules.
Module RH := RuleValidity.Hoare.ResourceHoare.

(** The Hoare rules and entailment steps at the counter's configuration. *)
Module Rules.
  Notation CEntailsAndMono := (RH.CEntailsAndMono (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CEntailsExistsAndRight := (RH.CEntailsExistsAndRight (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CEntailsExistsIntro := (RH.CEntailsExistsIntro (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CEntailsRefl := (RH.CEntailsRefl (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CEntailsStep := (RH.CEntailsStep (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CEntailsTrans := (RH.CEntailsTrans (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESAndAssocL := (RH.CESAndAssocL (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESAndAssocR := (RH.CESAndAssocR (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESAndComm := (RH.CESAndComm (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESAndElimL := (RH.CESAndElimL (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESAndTrueIntro := (RH.CESAndTrueIntro (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESExprImpl := (RH.CESExprImpl (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESFpuAllowedTrue := (RH.CESFpuAllowedTrue (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESGhostOwnChunkEqAssume := (RH.CESGhostOwnChunkEqAssume (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESInvariantArgumentsEqAssume := (RH.CESInvariantArgumentsEqAssume (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESIteFalse := (RH.CESIteFalse (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESIteIntroFalse := (RH.CESIteIntroFalse (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESIteIntroTrue := (RH.CESIteIntroTrue (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESIteTrue := (RH.CESIteTrue (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESRAValidTrue := (RH.CESRAValidTrue (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation CESTrueIntro := (RH.CESTrueIntro (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation resource_prenex_entails_refl := (RH.resource_prenex_entails_refl (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation RPEBody := (RH.RPEBody (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation RPEMono := (RH.RPEMono (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation RPEOpenCoreExists := (RH.RPEOpenCoreExists (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation RPETrans := (RH.RPETrans (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation RPEVacuous := (RH.RPEVacuous (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic)).
  Notation RTAlloc := (HoareRules.RTAlloc (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTAssign := (HoareRules.RTAssign (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTAtomicBlock := (HoareRules.RTAtomicBlock (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTCallDiscard := (HoareRules.RTCallDiscard (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTConsequence := (HoareRules.RTConsequence (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTDone := (HoareRules.RTDone (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTFieldRead := (HoareRules.RTFieldRead (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTFieldWrite := (HoareRules.RTFieldWrite (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTFoldInvariant := (HoareRules.RTFoldInvariant (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTFrame := (HoareRules.RTFrame (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTGhostUpdate := (HoareRules.RTGhostUpdate (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTIf := (HoareRules.RTIf (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTPostOpenCoreExists := (HoareRules.RTPostOpenCoreExists (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTPrenexPreserve := (HoareRules.RTPrenexPreserve (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTSeq := (HoareRules.RTSeq (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation RTUnfoldInvariant := (HoareRules.RTUnfoldInvariant (RAs := RuntimeErasure.RAValues.ra_values (RAs := CounterRAConfig.ra_config)) (Logic := CounterLogic.logic) (Contracts := CounterResourceContracts.contracts)).
  Notation COwn := (Resource.COwn (Logic := CounterLogic.logic)).
  Notation CGhostOwn := (Resource.CGhostOwn (Logic := CounterLogic.logic)).
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
  unfold HoareRules.instantiated_invariant, CounterResourceContracts.contracts.
  cbn [HoareRules.invariant_body].
  unfold CounterResourceContracts.invariant_body, counter_invariant_body_core,
    Resource.weaken_core_to.
  cbn [Resource.subst_bound_core Resource.subst_formals_core].
  rewrite !counter_formal_location_subst.
  cbn [Assertion.field_type CounterLogic.logic CounterLogic.field_type counter_field
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
    (Resource.RState read_entry_store
      (counter_token_core (ERef (RefFormal MHere))))
    (TUnfold counter_invariant (PECons (PEVar MHere) PENil))
    (Resource.ResourceExists TInt
      (Resource.RState read_open_store read_open_core)).
Proof.
  unfold read_open_store.
  apply Rules.RTPostOpenCoreExists.
  unfold counter_token_core.
  change (Assertion.procedure_args read_procedure) with ([TRef] : context).
  rewrite <- counter_invariant_at_formal.
  rewrite <- read_entry_arguments.
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
    (TFieldRead counter_field (MThere MHere) (PEVar MHere))
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
    rewrite <- read_open_location.
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
    (TFold counter_invariant (PECons (PEVar MHere) PENil))
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

Lemma read_assign :
  HoareRules.RavenHoareTriple
    (Resource.RState read_field_store
      (counter_token_core (ERef (RefFormal MHere))))
    (TAssign (MThere (MThere MHere)) (PEVar (MThere MHere)))
    (Resource.ResourceExists TInt
      (Resource.RState read_exit_store Resource.CTrue)).
Proof.
  unfold read_exit_store.
  eapply Rules.RTConsequence; [eapply Rules.RTAssign | | ].
  - apply Rules.CEntailsStep. apply Rules.CESTrueIntro.
  - apply Rules.RPEMono. apply Rules.RPEBody.
    split; [reflexivity | apply Rules.CEntailsStep; apply Rules.CESTrueIntro].
Qed.

Lemma read_rest :
  HoareRules.RavenHoareTriple
    (Resource.RState read_open_store read_open_core)
    (TSeq
      (TFieldRead counter_field (MThere MHere) (PEVar MHere))
      (TSeq
        (TFold counter_invariant (PECons (PEVar MHere) PENil))
        (TAssign (MThere (MThere MHere))
          (PEVar (MThere MHere)))))
    (Resource.ResourceExists TInt
      (Resource.ResourceExists TInt
        (Resource.RState read_exit_store Resource.CTrue))).
Proof.
  eapply Rules.RTSeq.
  - exact read_field_read.
  - apply Rules.RTPrenexPreserve.
    eapply Rules.RTSeq.
    + exact read_fold.
    + exact read_assign.
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
  eapply Rules.RTSeq; [exact read_unfold_open |].
  apply Rules.RTPrenexPreserve.
  exact read_rest.
Qed.

Module CounterAtomicity := RuleValidity.GenericRegions.Atomicity.

Definition counter_closed_state (available : RuleValidity.Hoare.mask) :
    CounterAtomicity.analysis_state :=
  CounterAtomicity.AnalysisState available ∅ false false.

Definition read_exit_state : CounterAtomicity.analysis_state :=
  counter_closed_state
    ((counter_mask ∖ {[counter_invariant]}) ∪ {[counter_invariant]}).
(** The allocation in [make] creates the concrete and ghost halves of a
    fresh counter at zero. *)
Definition make_initializers : list (field_init [TRef; TRef]) :=
  [FieldInit counter_field (PEVal (VInt 0%Z));
   FieldInit ghost_field
     (PEUnOp (URAOfInt h_ra) (PEVal (VInt 0%Z)))].

Definition make_alloc_store :
    symbolic_store [TRef; TRef] [] [TRef] :=
  RuleValidity.IR.update_store_with_bound make_entry_store MHere.

Lemma make_alloc_location :
  RuleValidity.IR.symbolize_expr make_alloc_store (PEVar MHere) =
    ERef (RefBound MHere).
Proof.
  unfold make_alloc_store, RuleValidity.IR.symbolize_expr.
  f_equal. apply lookup_update_store_same.
Qed.
Definition make_exit_store :
    symbolic_store [TRef; TRef] [] [TRef; TRef] :=
  RuleValidity.IR.update_store_with_bound make_alloc_store (MThere MHere).
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
  intros formals binders atoms value Hvalue.
  cbn in Hvalue. inversion Hvalue; subst.
  unfold RuleValidity.IR.Core.tval_ra_valid.
  cbn [CounterValues.ra_valid CounterValues.ra_of_int mn_of_int mn_valid].
  eexists. reflexivity.
Qed.

Lemma make_alloc :
  HoareRules.RavenHoareTriple
    (Resource.RState make_entry_store Resource.CTrue)
    (TAlloc MHere make_initializers)
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
      (TFold counter_invariant (PECons (PEVar MHere) PENil))
      (TAssign (MThere MHere) (PEVar MHere)))
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
      { intros formals binders atoms Hequality. symmetry.
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
  unfold counter_token_core.
  cbn [IR.Resource.subst_bound_core Assertions.subst_bound_expr_list
    Assertions.subst_bound_expr Assertions.subst_bound_ref].
  rewrite Assertions.singleton_bound_subst_here.
  eapply Rules.RTSeq; [exact make_alloc |].
  apply Rules.RTPrenexPreserve.
  exact make_fold_assign.
Qed.
Definition incr_open1_store :
    symbolic_store [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit]
      [TRef] [TInt] :=
  weaken_store incr_entry_store.

Definition incr_read1_store :
    symbolic_store [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit]
      [TRef] [TInt; TInt] :=
  RuleValidity.IR.update_store_with_bound incr_open1_store (MThere MHere).

Definition incr_new_store :
    symbolic_store [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit]
      [TRef] [TInt; TInt; TInt] :=
  RuleValidity.IR.update_store_with_bound incr_read1_store
    (MThere (MThere MHere)).

Definition incr_open2_store :
    symbolic_store [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit]
      [TRef] [TInt; TInt; TInt; TInt] :=
  weaken_store incr_new_store.

Definition incr_cas_read_store :
    symbolic_store [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit]
      [TRef] [TInt; TInt; TInt; TInt; TInt] :=
  RuleValidity.IR.update_store_with_bound incr_open2_store
    (MThere (MThere (MThere MHere))).

Definition incr_res_store :
    symbolic_store [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit]
      [TRef] [TBool; TInt; TInt; TInt; TInt; TInt] :=
  RuleValidity.IR.update_store_with_bound incr_cas_read_store
    (MThere (MThere (MThere (MThere MHere)))).

Lemma incr_open1_location :
  RuleValidity.Translation.IR.symbolize_expr incr_open1_store (PEVar MHere) =
    ERef (RefFormal MHere).
Proof.
  pose proof incr_entry_location as Hentry.
  unfold RuleValidity.Translation.IR.symbolize_expr in Hentry.
  injection Hentry as Hlookup.
  unfold symbolize_expr, incr_open1_store.
  rewrite RuleValidity.IR.lookup_weaken_store.
  f_equal.
  assert (Hweaken : forall (reference : value_ref [TRef] [] TRef),
      reference = RefFormal MHere ->
      @weaken_ref [TRef] [] TRef TInt reference = RefFormal MHere).
  { intros reference Hreference.
    dependent destruction reference; cbn in Hreference |-; try discriminate.
    inversion Hreference. reflexivity. }
  apply Hweaken, Hlookup.
Qed.

Lemma incr_read1_location :
  RuleValidity.Translation.IR.symbolize_expr incr_read1_store (PEVar MHere) =
    ERef (RefFormal MHere).
Proof.
  pose proof incr_open1_location as Hopen.
  unfold RuleValidity.Translation.IR.symbolize_expr in Hopen.
  injection Hopen as Hopen.
  unfold RuleValidity.Translation.IR.symbolize_expr, incr_read1_store.
  rewrite lookup_update_store_other by (cbn; congruence).
  rewrite Hopen. reflexivity.
Qed.

Lemma incr_new_location :
  RuleValidity.Translation.IR.symbolize_expr incr_new_store (PEVar MHere) =
    ERef (RefFormal MHere).
Proof.
  pose proof incr_read1_location as Hread.
  unfold RuleValidity.Translation.IR.symbolize_expr in Hread.
  injection Hread as Hread.
  unfold RuleValidity.Translation.IR.symbolize_expr, incr_new_store.
  rewrite lookup_update_store_other by (cbn; congruence).
  rewrite Hread. reflexivity.
Qed.

Lemma incr_open2_location :
  RuleValidity.Translation.IR.symbolize_expr incr_open2_store (PEVar MHere) =
    ERef (RefFormal MHere).
Proof.
  pose proof incr_new_location as Hnew.
  unfold RuleValidity.Translation.IR.symbolize_expr in Hnew.
  injection Hnew as Hlookup.
  unfold symbolize_expr, incr_open2_store.
  rewrite RuleValidity.IR.lookup_weaken_store.
  f_equal. apply weaken_ref_formal_eq, Hlookup.
Qed.

Lemma incr_cas_read_location :
  RuleValidity.Translation.IR.symbolize_expr incr_cas_read_store (PEVar MHere) =
    ERef (RefFormal MHere).
Proof.
  pose proof incr_open2_location as Hopen.
  unfold RuleValidity.Translation.IR.symbolize_expr in Hopen.
  injection Hopen as Hlookup.
  unfold symbolize_expr, incr_cas_read_store.
  rewrite lookup_update_store_other by (cbn; congruence).
  f_equal. apply weaken_ref_formal_eq, Hlookup.
Qed.

Lemma incr_res_location :
  RuleValidity.Translation.IR.symbolize_expr incr_res_store (PEVar MHere) =
    ERef (RefFormal MHere).
Proof.
  pose proof incr_cas_read_location as Hcas.
  unfold RuleValidity.Translation.IR.symbolize_expr in Hcas.
  injection Hcas as Hlookup.
  unfold symbolize_expr, incr_res_store.
  rewrite lookup_update_store_other by (cbn; congruence).
  f_equal. apply weaken_ref_formal_eq, Hlookup.
Qed.
Lemma incr_unfold1_open :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_entry_store
      (counter_token_core (ERef (RefFormal MHere))))
    (TUnfold counter_invariant (PECons (PEVar MHere) PENil))
    (Resource.ResourceExists TInt
      (Resource.RState incr_open1_store read_open_core)).
Proof.
  unfold incr_open1_store.
  apply Rules.RTPostOpenCoreExists.
  unfold counter_token_core.
  try change (Assertion.procedure_args incr_procedure) with ([TRef] : context).
  rewrite <- counter_invariant_at_formal.
  rewrite <- incr_entry_arguments.
  apply Rules.RTUnfoldInvariant.
Qed.

Lemma incr_field1_read :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_open1_store read_open_core)
    (TFieldRead counter_field (MThere MHere) (PEVar MHere))
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
    rewrite <- incr_open1_location.
    eapply Rules.RTFieldRead.
  - apply Rules.CEntailsStep. apply Rules.CESAndComm.
  - rewrite incr_open1_location. apply Rules.resource_prenex_entails_refl.
Qed.

Lemma incr_fold1 :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_read1_store read_field_core)
    (TFold counter_invariant (PECons (PEVar MHere) PENil))
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
    (weaken_expr (RuleValidity.IR.symbolize_expr incr_read1_store
      (PEBinOp BAdd (PEVar (MThere MHere)) (PEVal (VInt 1%Z))))).

Lemma incr_assign_new :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_read1_store
      (counter_token_core (ERef (RefFormal MHere))))
    (TAssign (MThere (MThere MHere))
      (PEBinOp BAdd (PEVar (MThere MHere)) (PEVal (VInt 1%Z))))
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
    (Resource.RState incr_new_store
      (Resource.CAnd (Resource.CExpr incr_new_equality_core)
        (counter_token_core (ERef (RefFormal MHere)))))
    (TUnfold counter_invariant (PECons (PEVar MHere) PENil))
    (Resource.ResourceExists TInt
      (Resource.RState incr_open2_store
        (Resource.CAnd (@counter_open_core [TInt; TInt; TInt])
          (Resource.CExpr (weaken_expr incr_new_equality_core))))).
Proof.
  unfold incr_open2_store.
  eapply Rules.RTConsequence;
    [eapply Rules.RTFrame; eapply Rules.RTUnfoldInvariant | | ].
  - cbn [RuleValidity.IR.symbolize_expr_list]. rewrite incr_new_location.
    unfold counter_token_core.
    apply Rules.CEntailsStep. apply Rules.CESAndComm.
  - eapply Rules.RPETrans; [| apply Rules.RPEOpenCoreExists].
    cbn [RuleValidity.Hoare.ResourceHoare.Resource.prenex_and].
    apply Rules.RPEBody. split; [reflexivity |].
    cbn [RuleValidity.Hoare.ResourceHoare.Resource.resource_body
      RuleValidity.Hoare.ResourceHoare.Resource.resource_stack].
    cbn [RuleValidity.IR.symbolize_expr_list]. rewrite incr_new_location.
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
  RuleValidity.IR.symbolize_expr incr_cas_read_store
    (PEVar (MThere (MThere MHere))).

Definition incr_cas_expected_core :
    expr [TRef] [TInt; TInt; TInt; TInt; TInt] TInt :=
  RuleValidity.IR.symbolize_expr incr_cas_read_store (PEVar (MThere MHere)).

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
    Resource.resource_prenex [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit]
      [TRef] [TInt; TInt; TInt; TInt] :=
  Resource.ResourceExists TInt
    (Resource.ResourceExists TBool
      (Resource.RState incr_res_store
        (Resource.CIte (ERef (RefBound MHere))
          (Resource.weaken_core incr_cas_success_core)
          (Resource.weaken_core incr_cas_failure_core)))).

Lemma incr_cas_read :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_open2_store counter_open_core)
    (TFieldRead counter_field (MThere (MThere (MThere MHere)))
      (PEVar MHere))
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
    rewrite <- incr_open2_location.
    eapply Rules.RTFieldRead.
  - apply Rules.CEntailsStep. apply Rules.CESAndComm.
  - rewrite incr_open2_location. apply Rules.resource_prenex_entails_refl.
Qed.

Lemma incr_cas_success_branch :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_cas_read_store
      (Resource.CAnd incr_cas_read_core
        (Resource.CExpr (RuleValidity.IR.symbolize_expr incr_cas_read_store
          (PEBinOp (BEq TInt) (PEVar (MThere (MThere (MThere MHere))))
            (PEVar (MThere MHere)))))))
    (TSeq
      (TFieldWrite counter_field (PEVar MHere)
        (PEVar (MThere (MThere MHere))))
      (TAssign (MThere (MThere (MThere (MThere MHere))))
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
            intros formals binders atoms Heq.
            pose proof (interp_typed_equality_true_early formals binders atoms
              _ _ Heq) as Hvalue.
            cbn [interp_expr]. cbn [interp_expr] in Hvalue.
            rewrite <- Hvalue. reflexivity. }
       apply Rules.CEntailsStep. apply Rules.CESGhostOwnChunkEqAssume.
       intros formals binders atoms Heq.
       pose proof (interp_typed_equality_true_early formals binders atoms
         _ _ Heq) as Hvalue.
       unfold incr_cas_expected_core, RuleValidity.IR.symbolize_expr.
       unfold incr_cas_read_store in Hvalue |- *.
       rewrite lookup_update_store_same in Hvalue.
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
    + rewrite <- incr_cas_read_location. apply Rules.CEntailsRefl.
    + unfold incr_cas_new_core.
      cbn [RuleValidity.Hoare.ResourceHoare.Resource.prenex_and].
      rewrite <- incr_cas_read_location.
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
        intros formals binders atoms Heq.
        pose proof (interp_typed_equality_true_early formals binders atoms
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
          (RuleValidity.IR.symbolize_expr incr_cas_read_store
            (PEBinOp (BEq TInt) (PEVar (MThere (MThere (MThere MHere))))
              (PEVar (MThere MHere))))))))
    (TAssign (MThere (MThere (MThere (MThere MHere))))
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
    intros formals binders atoms Heq.
    pose proof (interp_typed_equality_true_early formals binders atoms _ _ Heq)
      as Hvalue.
    cbn [RuleValidity.IR.symbolize_expr interp_expr interp_ref
      RuleValidity.Hoare.ResourceHoare.Assertions.weaken_expr] in Hvalue.
    cbn [interp_expr interp_ref interp_unop].
    injection Hvalue as Hvalue. rewrite Hvalue. reflexivity.
Qed.

Lemma incr_cas_body :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_open2_store counter_open_core)
    cas_typed_body incr_cas_join_prenex.
Proof.
  unfold cas_typed_body, incr_cas_join_prenex.
  cbn [elaborate_stmt].
  eapply Rules.RTSeq; [apply incr_cas_read |].
  apply Rules.RTPrenexPreserve.
  eapply Rules.RTIf;
    [apply incr_cas_success_branch
    | apply incr_cas_failure_branch].
Qed.

Lemma incr_atomic_cas :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_open2_store counter_open_core)
    (TAtomic cas_typed_body) incr_cas_join_prenex.
Proof.
  apply Rules.RTAtomicBlock. exact incr_cas_body.
Qed.

(** *** The ghost update after a successful CAS

    The ghost values before and after the increment, and the
    frame-preserving update between them. *)

Definition incr_fpu_old_core :
    expr [TRef] [TBool; TInt; TInt; TInt; TInt; TInt] (TRA h_ra) :=
  EUnOp (URAOfInt h_ra)
    (RuleValidity.IR.symbolize_expr incr_res_store (PEVar (MThere MHere))).

Definition incr_fpu_new_core :
    expr [TRef] [TBool; TInt; TInt; TInt; TInt; TInt] (TRA h_ra) :=
  EUnOp (URAOfInt h_ra)
    (EBinOp BAdd
      (RuleValidity.IR.symbolize_expr incr_res_store (PEVar (MThere MHere)))
      (EVal (VInt 1%Z))).

Lemma incr_fpu_allowed :
  RH.core_entails
    (@Resource.CTrue _ _ [TRef] [TBool; TInt; TInt; TInt; TInt; TInt])
    (Resource.CFpuAllowed (TRA h_ra) incr_fpu_old_core incr_fpu_new_core).
Proof.
  apply Rules.CEntailsStep. apply Rules.CESFpuAllowedTrue.
  intros formals binders atoms old_value new_value Hold Hnew.
  unfold incr_fpu_old_core, incr_fpu_new_core in Hold, Hnew.
  cbn [interp_expr interp_ref interp_unop interp_binop] in Hold, Hnew.
  remember (interp_expr formals binders atoms
    (RuleValidity.IR.symbolize_expr incr_res_store
      (PEVar (MThere MHere)))) as current_result.
  destruct current_result as [current_value |]; [| discriminate].
  dependent destruction current_value.
  cbn in Hold, Hnew.
  inversion Hold; subst. inversion Hnew; subst.
  cbn [tval_fpu_allowed RuntimeErasure.RAValues.ra_fpu_allowed].
  apply h_ra_fpuValid_mono. reflexivity.
Qed.

(** The result assignment does not disturb [v1]'s slot. *)
Lemma incr_v1_weaken :
  weaken_expr
      (RuleValidity.IR.symbolize_expr incr_cas_read_store (PEVar (MThere MHere))) =
    RuleValidity.IR.symbolize_expr incr_res_store (PEVar (MThere MHere)).
Proof.
  unfold incr_res_store, RuleValidity.IR.symbolize_expr.
  cbn [weaken_expr].
  f_equal. symmetry. apply lookup_update_store_preserves_second.
Qed.

(** *** Slot equations

    Every symbolic slot the post-CAS reasoning mentions, resolved to an
    explicit binder reference.  All five are chains of
    [lookup_update_store_other], [lookup_update_store_same] and
    [lookup_weaken_store] through the store sequence built by the body. *)

Lemma incr_read1_v1_slot :
  RuleValidity.IR.symbolize_expr incr_read1_store (PEVar (MThere MHere)) =
    ERef (RefBound MHere).
Proof.
  unfold incr_read1_store, RuleValidity.IR.symbolize_expr.
  f_equal. apply lookup_update_store_same.
Qed.

Lemma incr_cas_read_new_v1_slot :
  RuleValidity.IR.symbolize_expr incr_cas_read_store
      (PEVar (MThere (MThere MHere))) =
    ERef (RefBound (MThere (MThere MHere))).
Proof.
  unfold incr_cas_read_store, incr_open2_store, incr_new_store,
    RuleValidity.IR.symbolize_expr.
  f_equal.
  rewrite lookup_update_store_other by (cbn; congruence).
  rewrite lookup_weaken_store.
  rewrite lookup_update_store_same.
  reflexivity.
Qed.
Lemma incr_res_v1_slot :
  RuleValidity.IR.symbolize_expr incr_res_store (PEVar (MThere MHere)) =
    ERef (RefBound (MThere (MThere (MThere (MThere MHere))))).
Proof.
  unfold incr_res_store, incr_cas_read_store, incr_open2_store,
    incr_new_store, RuleValidity.IR.symbolize_expr.
  f_equal.
  rewrite lookup_update_store_other by (cbn; congruence).
  rewrite lookup_update_store_other by (cbn; congruence).
  rewrite lookup_weaken_store.
  rewrite lookup_update_store_other by (cbn; congruence).
  change (RuleValidity.IR.Core.lookup_store incr_read1_store TInt (MThere MHere))
    with (RuleValidity.IR.Core.lookup_store incr_read1_store TInt (MThere MHere)).
  pose proof incr_read1_v1_slot as Hslot.
  unfold RuleValidity.IR.symbolize_expr in Hslot.
  injection Hslot as Hslot. rewrite Hslot. reflexivity.
Qed.

(** *** Step 5: the post-CAS conditional

    The two branches join on the *unfolded* invariant body, ready for the
    second fold.  Success reaches it at [new_v1] and failure at the value
    the block observed; the carried equality is what identifies
    [ghost(v1 + 1)] with [ghost(new_v1)] on the success side, which is why
    the frame around the atomic block has to extend over this conditional
    as well. *)

Lemma incr_res_slot :
  RuleValidity.IR.symbolize_expr incr_res_store
      (PEVar (MThere (MThere (MThere (MThere MHere))))) =
    ERef (RefBound MHere).
Proof.
  unfold incr_res_store, RuleValidity.IR.symbolize_expr.
  f_equal. apply lookup_update_store_same.
Qed.

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
    (TGhostUpdate ghost_field (PEVar MHere)
      (PEUnOp (URAOfInt h_ra) (PEVar (MThere MHere)))
      (PEUnOp (URAOfInt h_ra)
        (PEBinOp BAdd (PEVar (MThere MHere)) (PEVal (VInt 1%Z)))))
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
       rewrite incr_v1_weaken.
       rewrite <- incr_res_location.
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
  rewrite <- incr_res_location.
  apply Rules.CEntailsStep. apply Rules.CESGhostOwnChunkEqAssume.
  intros formals binders atoms Heq.
  change (RuleValidity.IR.symbolize_expr incr_read1_store
    (PEBinOp BAdd (PEVar (MThere MHere)) (PEVal (VInt 1%Z))))
    with (EBinOp BAdd
      (RuleValidity.IR.symbolize_expr incr_read1_store (PEVar (MThere MHere)))
      (EVal (VInt 1%Z))) in Heq.
  rewrite incr_read1_v1_slot in Heq.
  unfold weaken_expr in Heq.
  cbn [Resource.Assertions.rename_bound_expr
    Resource.Assertions.rename_bound_ref] in Heq.
  change (RuleValidity.IR.symbolize_expr incr_res_store
    (PEUnOp (URAOfInt h_ra)
      (PEBinOp BAdd (PEVar (MThere MHere)) (PEVal (VInt 1%Z)))))
    with (EUnOp (URAOfInt h_ra) (EBinOp BAdd
      (RuleValidity.IR.symbolize_expr incr_res_store (PEVar (MThere MHere)))
      (EVal (VInt 1%Z)))).
  rewrite incr_res_v1_slot.
  unfold incr_cas_new_core.
  rewrite incr_cas_read_new_v1_slot.
  unfold weaken_expr.
  cbn [Resource.Assertions.rename_bound_expr
    Resource.Assertions.rename_bound_ref].
  cbn [Resource.Assertions.rename_bound_ref weaken_ref
    Resource.Assertions.weaken_ref] in Heq |- *.
  unfold Resource.Assertions.weaken_bound_renaming in Heq |- *.
  pose proof (interp_typed_equality_true_early formals binders atoms _ _ Heq)
    as Hvalue.
  cbn [interp_expr interp_ref] in Hvalue |- *.
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

(** *** Steps 6-8: the second fold, the retry conditional, the return *)

Lemma incr_fold2 :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_res_store incr_post_cas_core)
    (TFold counter_invariant (PECons (PEVar MHere) PENil))
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

Lemma counter_resource_instantiated_pre {Delta : context}
    (location : expr [TRef] Delta TRef) :
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
      (e : Core.expr [TRef] Delta t)
      (es : RH.Assertions.expr_list [TRef] Delta ts),
    RH.Assertions.expr_list_formal_subst (RH.Assertions.ExprCons e es)
      t MHere = e);
    [intros; unfold RH.Assertions.expr_list_formal_subst;
     apply lookup_expr_list_here |].
  rewrite Hhead. reflexivity.
Qed.

Lemma incr_retry_call :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_res_store
      (Resource.CAnd (counter_token_core (ERef (RefFormal MHere)))
        (Resource.CExpr (EUnOp UNot (ERef (RefBound MHere))))))
    (TCall incr_procedure (PECons (PEVar MHere) PENil)
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
  2: { cbn [RuleValidity.IR.symbolize_expr_list]. rewrite incr_res_location.
       rewrite counter_resource_instantiated_pre.
       unfold counter_token_core.
       apply Rules.CEntailsStep. apply Rules.CESAndElimL. }
  cbv [HoareRules.procedure_verified CounterResourceContracts.contracts
    CounterResourceContracts.procedure_verified]. cbn. discriminate.
Qed.

Lemma incr_retry_done :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_res_store
      (Resource.CAnd (counter_token_core (ERef (RefFormal MHere)))
        (Resource.CExpr (EUnOp UNot
          (EUnOp UNot (ERef (RefBound MHere)))))))
    TDone
    (Resource.RState incr_res_store Resource.CTrue).
Proof.
  eapply Rules.RTConsequence;
    [eapply Rules.RTDone | apply Rules.CEntailsRefl |].
  apply Rules.RPEBody. split;
    [reflexivity | apply Rules.CEntailsStep; apply Rules.CESTrueIntro].
Qed.

Definition incr_exit_store :
    symbolic_store [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit] [TRef]
      [TUnit; TBool; TInt; TInt; TInt; TInt; TInt] :=
  RuleValidity.IR.update_store_with_bound incr_res_store
    (MThere (MThere (MThere (MThere (MThere (MThere MHere)))))).

Lemma incr_return :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_res_store Resource.CTrue)
    (TAssign (MThere (MThere (MThere (MThere (MThere (MThere MHere))))))
      (PEVal VUnit))
    (Resource.ResourceExists TUnit
      (Resource.RState incr_exit_store Resource.CTrue)).
Proof.
  unfold incr_exit_store.
  eapply Rules.RTConsequence;
    [eapply Rules.RTAssign | apply Rules.CEntailsRefl |].
  apply Rules.RPEMono. apply Rules.RPEBody. split;
    [reflexivity | apply Rules.CEntailsStep; apply Rules.CESTrueIntro].
Qed.

(** *** Step 9: assembly

    The carried equality is framed around the atomic block alone, not
    around the group: the post-CAS conditional consumes it, so it has to
    be visible in the conditional's body.  [prenex_and] weakens it once
    per binder the block introduces, which is exactly
    [incr_threaded_equality_core]. *)

Lemma incr_retry_conditional :
  HoareRules.RavenHoareTriple
    (Resource.RState incr_res_store
      (counter_token_core (ERef (RefFormal MHere))))
    (TIf (PEUnOp UNot (PEVar (MThere (MThere (MThere (MThere MHere))))))
      (TCall incr_procedure (PECons (PEVar MHere) PENil)
        (@CTDiscard _ TUnit))
      TDone)
    (Resource.RState incr_res_store Resource.CTrue).
Proof.
  eapply Rules.RTIf.
  - change (RuleValidity.IR.symbolize_expr incr_res_store
      (PEUnOp UNot (PEVar (MThere (MThere (MThere (MThere MHere)))))))
      with (EUnOp UNot (RuleValidity.IR.symbolize_expr incr_res_store
        (PEVar (MThere (MThere (MThere (MThere MHere))))))).
    rewrite incr_res_slot.
    apply incr_retry_call.
  - change (RuleValidity.IR.symbolize_expr incr_res_store
      (PEUnOp UNot (PEVar (MThere (MThere (MThere (MThere MHere)))))))
      with (EUnOp UNot (RuleValidity.IR.symbolize_expr incr_res_store
        (PEVar (MThere (MThere (MThere (MThere MHere))))))).
    rewrite incr_res_slot.
    apply incr_retry_done.
Qed.

Lemma incr_resource_body_derivation :
  HoareRules.RavenHoareTriple
    (RuleValidity.Hoare.procedure_body_pre incr_typed_procedure)
    incr_typed_body
    (RuleValidity.Hoare.procedure_body_post incr_typed_procedure
      incr_exit_store (RefBound MHere)).
Proof.
  unfold RuleValidity.Hoare.procedure_body_pre, RuleValidity.Hoare.procedure_body_post,
    incr_typed_procedure.
  cbn [procedure_entry_store procedure_precondition procedure_postcondition
    RuleValidity.Hoare.existentially_close_prenex
    RuleValidity.Hoare.existentially_close_prenex_at].
  cbn [IR.Resource.subst_bound_core].
  rewrite incr_typed_body_normalized_eq.
  unfold incr_typed_body_normalized.
  eapply Rules.RTSeq; [apply incr_unfold1_open |].
  apply Rules.RTPrenexPreserve.
  eapply Rules.RTSeq; [apply incr_field1_read |].
  apply Rules.RTPrenexPreserve.
  eapply Rules.RTSeq; [apply incr_fold1 |].
  eapply Rules.RTSeq; [apply incr_assign_new |].
  apply Rules.RTPrenexPreserve.
  eapply Rules.RTSeq; [apply incr_unfold2 |].
  apply Rules.RTPrenexPreserve.
  eapply Rules.RTSeq.
  - eapply Rules.RTSeq.
    + eapply Rules.RTFrame. apply incr_atomic_cas.
    + apply Rules.RTPrenexPreserve. apply Rules.RTPrenexPreserve.
      eapply (Rules.RTIf incr_res_store incr_cas_result_core
        (PEVar (MThere (MThere (MThere (MThere MHere))))) _ _ _).
      * rewrite incr_res_slot. apply incr_fpu_branch.
      * rewrite incr_res_slot. apply incr_done_branch.
  - apply Rules.RTPrenexPreserve. apply Rules.RTPrenexPreserve.
    eapply Rules.RTSeq; [apply incr_fold2 |].
    eapply Rules.RTSeq; [apply incr_retry_conditional |].
    apply incr_return.
Qed.

Definition counter_runtime_procedure_statement
    (packed : packed_typed_procedure) : RuleValidity.RuntimeLang.stmt :=
  match packed with
  | existT Γ (existT F procedure) =>
      default RuleValidity.RuntimeLang.StuckS
        (RuleValidity.RuntimeLang.reify_runtime_stmt 0
          (@RuntimeErasure.runtime_stmt _ _ _ Γ
            (@RuntimeErasure.runtime_procedure_names _ _
              Γ F procedure) 0 (procedure_body Γ F procedure)))
  end.

Lemma counter_runtime_procedure_statement_nonvalue packed :
  List.In packed (procedure_entries CounterProcedureContracts.procedures) ->
  forall stack,
  RuleValidity.RuntimeLang.to_val (RuleValidity.RuntimeLang.to_rtstmt stack
    (counter_runtime_procedure_statement packed)) = None.
Proof.
  intros Hin stack.
  simpl in Hin.
  destruct Hin as [Hin | [Hin | [Hin | []]]].
  - dependent destruction Hin. reflexivity.
  - dependent destruction Hin. reflexivity.
  - dependent destruction Hin. reflexivity.
Qed.

Lemma counter_runtime_procedure_layout packed :
  List.In packed (procedure_entries CounterProcedureContracts.procedures) ->
  match packed with
  | existT Γ (existT F procedure) =>
      procedure_wf procedure /\
      ~ List.In "#ret_val" (IR.named_context_names
        (procedure_variables Γ F procedure)) /\
      forall stack,
        @RuntimeErasure.runtime_stmt _ _ _ Γ
          (@RuntimeErasure.runtime_procedure_names _ _
            Γ F procedure) stack (procedure_body Γ F procedure) =
        RuleValidity.RuntimeLang.to_rtstmt stack
          (counter_runtime_procedure_statement packed)
  end.
Proof.
  intros Hin. simpl in Hin.
  destruct Hin as [Hin | [Hin | [Hin | []]]].
  - dependent destruction Hin. split; first exact read_typed_procedure_wf.
    split.
    + simpl. intros [H | [H | [H | []]]]; discriminate.
    + intros stack. reflexivity.
  - dependent destruction Hin. split; first exact incr_typed_procedure_wf.
    split.
    + simpl. intuition discriminate.
    + intros stack. reflexivity.
  - dependent destruction Hin. split; first exact make_typed_procedure_wf.
    split.
    + simpl. intuition discriminate.
    + intros stack. reflexivity.
Qed.

Definition counter_program_registration :
    RuleValidity.certified_program_registration :=
  RuleValidity.CertifiedProgramRegistration
    {[counter_invariant]}
    counter_runtime_procedure_statement
    counter_runtime_procedure_statement_nonvalue
    counter_runtime_procedure_layout.
Lemma read_restricted_fragment_accepted :
  NormalizationBase.restricted_fragment_accepted read_typed_body.
Proof. vm_compute. reflexivity. Qed.

Lemma incr_restricted_fragment_accepted :
  NormalizationBase.restricted_fragment_accepted incr_typed_body.
Proof. vm_compute. reflexivity. Qed.

Lemma make_restricted_fragment_accepted :
  NormalizationBase.restricted_fragment_accepted make_typed_body.
Proof. vm_compute. reflexivity. Qed.

Lemma read_restricted_normalization_computes :
  exists normalized,
    NormalizationBase.restricted_analyze_and_normalize read_typed_body =
      Some normalized.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma incr_restricted_normalization_computes :
  exists normalized,
    NormalizationBase.restricted_analyze_and_normalize incr_typed_body =
      Some normalized.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma make_restricted_normalization_computes :
  exists normalized,
    NormalizationBase.restricted_analyze_and_normalize make_typed_body =
      Some normalized.
Proof. vm_compute. eexists. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** The three analyzed procedure bodies

    [analyzed_triple] wants three things: an analysis certificate
    (under the framework's [contract_cost_model]), the [RavenHoareRules]
    derivation, and the executable restricted-fragment check.  Nothing else -- no alignment,
    no LIFO witness, no normalization.  Taking the certificate from
    [analyze_coherent_lifo_builds_certificate] means the record's
    branch-coherence field comes packaged with it, so the certificate
    itself never has to be inspected. *)

Module CN := RuleValidity.CertifiedNormalization.

Lemma read_analysis_coherent :
  CounterAtomicity.analyze_coherent_lifo
      (counter_closed_state counter_mask) read_typed_body =
    Some read_exit_state.
Proof. reflexivity. Qed.

Lemma incr_analysis_coherent :
  CounterAtomicity.analyze_coherent_lifo
      (counter_closed_state counter_mask) incr_typed_body =
    Some (counter_closed_state counter_mask).
Proof. reflexivity. Qed.

Lemma make_analysis_coherent :
  CounterAtomicity.analyze_coherent_lifo
      (counter_closed_state ∅) make_typed_body =
    Some (counter_closed_state counter_mask).
Proof. reflexivity. Qed.

Definition read_coherent_run :=
  CounterAtomicity.analyze_coherent_lifo_builds_certificate
    (counter_closed_state counter_mask) read_typed_body
    read_exit_state read_analysis_coherent.

Definition incr_coherent_run :=
  CounterAtomicity.analyze_coherent_lifo_builds_certificate
    (counter_closed_state counter_mask) incr_typed_body
    (counter_closed_state counter_mask) incr_analysis_coherent.

Definition make_coherent_run :=
  CounterAtomicity.analyze_coherent_lifo_builds_certificate
    (counter_closed_state ∅) make_typed_body
    (counter_closed_state counter_mask) make_analysis_coherent.

Definition read_analyzed_certificate :=
  CounterAtomicity.coherent_flat_certificate
    (projT1 read_coherent_run).
Definition incr_analyzed_certificate :=
  CounterAtomicity.coherent_flat_certificate
    (projT1 incr_coherent_run).
Definition make_analyzed_certificate :=
  CounterAtomicity.coherent_flat_certificate
    (projT1 make_coherent_run).

Definition read_analyzed_body :
  ProcedureValidity.analyzed_body_valid read_typed_procedure.
Proof.
  unfold ProcedureValidity.analyzed_body_valid.
  unshelve refine (@ProcedureValidity.AnalyzedBodyCertificate _ _ _
    [TRef; TInt; TInt] read_procedure read_typed_procedure counter_mask
    (counter_closed_state counter_mask) read_exit_state
    [TInt; TInt; TInt] read_exit_store (RefBound MHere)
    _ _ _ _ _ _ _ _ _).
  1: { refine {| CN.analyzed_certificate := read_analyzed_certificate;
                 CN.analyzed_hoare := read_resource_body_derivation;
                 CN.analyzed_restricted :=
                   read_restricted_fragment_accepted |}. }
  - apply lookup_update_store_same.
  - unfold CounterAtomicity.state_wf, counter_closed_state. simpl. set_solver.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold read_exit_state. simpl. rewrite counter_mask_close. set_solver.
  - exact (CounterAtomicity.coherent_conditional_masks
      (projT1 read_coherent_run)).
Defined.

Definition incr_analyzed_body :
  ProcedureValidity.analyzed_body_valid incr_typed_procedure.
Proof.
  unfold ProcedureValidity.analyzed_body_valid.
  unshelve refine (@ProcedureValidity.AnalyzedBodyCertificate _ _ _
    [TRef; TInt; TInt; TInt; TBool; TUnit; TUnit] incr_procedure
    incr_typed_procedure counter_mask
    (counter_closed_state counter_mask)
    (counter_closed_state counter_mask)
    [TUnit; TBool; TInt; TInt; TInt; TInt; TInt] incr_exit_store
    (RefBound MHere) _ _ _ _ _ _ _ _ _).
  1: { refine {| CN.analyzed_certificate := incr_analyzed_certificate;
                 CN.analyzed_hoare := incr_resource_body_derivation;
                 CN.analyzed_restricted :=
                   incr_restricted_fragment_accepted |}. }
  - apply lookup_update_store_same.
  - unfold CounterAtomicity.state_wf, counter_closed_state. simpl. set_solver.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. set_solver.
  - exact (CounterAtomicity.coherent_conditional_masks
      (projT1 incr_coherent_run)).
Defined.

Definition make_analyzed_body :
  ProcedureValidity.analyzed_body_valid make_typed_procedure.
Proof.
  unfold ProcedureValidity.analyzed_body_valid.
  unshelve refine (@ProcedureValidity.AnalyzedBodyCertificate _ _ _
    [TRef; TRef] make_procedure make_typed_procedure ∅
    (counter_closed_state ∅)
    (counter_closed_state counter_mask)
    [TRef; TRef] make_exit_store (RefBound MHere) _ _ _ _ _ _ _ _ _).
  1: { refine {| CN.analyzed_certificate := make_analyzed_certificate;
                 CN.analyzed_hoare := make_resource_body_derivation;
                 CN.analyzed_restricted :=
                   make_restricted_fragment_accepted |}. }
  - apply lookup_update_store_same.
  - unfold CounterAtomicity.state_wf, counter_closed_state. simpl. set_solver.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. set_solver.
  - exact (CounterAtomicity.coherent_conditional_masks
      (projT1 make_coherent_run)).
Defined.
End CounterMonotonic.
