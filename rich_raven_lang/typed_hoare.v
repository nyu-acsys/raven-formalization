From Coq Require Import List Program.Equality ZArith.
From stdpp Require Import gmap sets.

From raven_iris.rich_raven_lang Require Import
  typed_core typed_assertion typed_ir.

Import ListNotations.
Open Scope list_scope.

(** The typed Raven Hoare calculus.  Its semantic validation is Phase 6;
    this module contains only syntax-directed proof rules. *)
Module TypedHoare.

Import TypedCore TypedIR.

Module Make (RAs : RA_VALUE_CONFIG) (Logic : TypedAssertion.LOGIC_SIGNATURE).
Module IR := TypedIR.Make RAs Logic.
Module Core := IR.Core.
Module Assertions := IR.Assertions.
Import Core Assertions IR.

Definition mask := gset inv_id.

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

Fixpoint allocated_fields_assertion {Γ F Δ}
    (store : symbolic_store Γ F Δ) (fields : list (field_init Γ)) :
    assertion Γ F (TRef :: Δ) :=
  match fields with
  | [] => APure True
  | FieldInit field value :: fields' =>
      AAnd
        (AOwn field (ERef (RefBound MHere))
          (weaken_expr (symbolize_expr store value)))
        (allocated_fields_assertion store fields')
  end.

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

(** One-step entailments contain only semantic/structural primitives.
    Reflexivity, transitivity, and congruence are factored into the closure
    below instead of repeated as domain-specific constructors. *)
Inductive entailment_step {Γ F Δ} :
    assertion Γ F Δ -> assertion Γ F Δ -> Prop :=
| ESAndComm left right :
    entailment_step (AAnd left right) (AAnd right left)
| ESAndAssocR first second third :
    entailment_step (AAnd (AAnd first second) third)
      (AAnd first (AAnd second third))
| ESAndAssocL first second third :
    entailment_step (AAnd first (AAnd second third))
      (AAnd (AAnd first second) third)
| ESAndElimL left right : entailment_step (AAnd left right) left
| ESAndElimR left right : entailment_step (AAnd left right) right
| ESAndTrueIntro formula :
    entailment_step formula (AAnd formula (APure True))
| ESTrueIntro formula : entailment_step formula (APure True)
| ESPure (left right : Prop) :
    (left -> right) -> entailment_step (APure left) (APure right)
| ESIteTrue condition then_branch else_branch :
    entailment_step (AAnd (AIte condition then_branch else_branch)
      (AExpr condition)) then_branch
| ESIteFalse condition then_branch else_branch :
    entailment_step
      (AAnd (AIte condition then_branch else_branch)
        (AExpr (EUnOp UNot condition))) else_branch
| ESIteBoolTrue condition then_branch else_branch indicator :
    entailment_step
      (AAnd
        (AIte condition
          (AAnd then_branch
            (AExpr (EBinOp (BEq TBool) indicator (EVal (VBool true)))))
          (AAnd else_branch
            (AExpr (EBinOp (BEq TBool) indicator (EVal (VBool false))))))
        (AExpr indicator))
      (AAnd then_branch (AExpr condition))
| ESIteBoolFalse condition then_branch else_branch indicator :
    entailment_step
      (AAnd
        (AIte condition
          (AAnd then_branch
            (AExpr (EBinOp (BEq TBool) indicator (EVal (VBool true)))))
          (AAnd else_branch
            (AExpr (EBinOp (BEq TBool) indicator (EVal (VBool false))))))
        (AExpr (EUnOp UNot indicator)))
      else_branch
| ESExprImpl (left right : expr F Δ TBool) :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms left = Some (VBool true) ->
      interp_expr formals binders atoms right = Some (VBool true)) ->
    entailment_step (AExpr left) (AExpr right)
| ESExprTrue (expression : expr F Δ TBool) :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms expression = Some (VBool true)) ->
    entailment_step (APure True) (AExpr expression)
| ESOwnChunkEq field location left_chunk right_chunk :
    (forall (formals : formal_env F) (binders : binder_env Δ)
      (atoms : atom_env),
      interp_expr formals binders atoms left_chunk =
        interp_expr formals binders atoms right_chunk) ->
    entailment_step (AOwn field location left_chunk)
      (AOwn field location right_chunk).

Inductive assertion_entails {Γ F Δ} :
    assertion Γ F Δ -> assertion Γ F Δ -> Prop :=
| EntailsRefl formula : assertion_entails formula formula
| EntailsStep left right : entailment_step left right ->
    assertion_entails left right
| EntailsTrans first second third :
    assertion_entails first second -> assertion_entails second third ->
    assertion_entails first third
| EntailsAndMono left left' right right' :
    assertion_entails left left' -> assertion_entails right right' ->
    assertion_entails (AAnd left right) (AAnd left' right')
| EntailsExistsMono t (body body' : assertion Γ F (t :: Δ)) :
    assertion_entails body body' ->
    assertion_entails (AExists t body) (AExists t body')
| EntailsExistsIntro t (body : assertion Γ F (t :: Δ)) witness instantiated :
    instantiate_bound_assertion witness body = Some instantiated ->
    assertion_entails instantiated (AExists t body)
| EntailsExistsElim t (body : assertion Γ F (t :: Δ)) conclusion :
    assertion_entails body (weaken_assertion conclusion) ->
    assertion_entails (AExists t body) conclusion
| EntailsExistsAndRight t (body : assertion Γ F (t :: Δ)) frame :
    assertion_entails
      (AAnd (AExists t body) frame)
      (AExists t (AAnd body (weaken_assertion frame)))
| EntailsAndExistsLeft t frame (body : assertion Γ F (t :: Δ)) :
    assertion_entails
      (AAnd frame (AExists t body))
      (AExists t (AAnd (weaken_assertion frame) body))
| EntailsForallMono t (body body' : assertion Γ F (t :: Δ)) :
    assertion_entails body body' ->
    assertion_entails (AForall t body) (AForall t body').

Lemma entails_and_true_elim {Γ F Δ} (formula : assertion Γ F Δ) :
  assertion_entails (AAnd formula (APure True)) formula.
Proof. apply EntailsStep. apply ESAndElimL. Qed.

Lemma entails_and_comm {Γ F Δ} (left right : assertion Γ F Δ) :
  assertion_entails (AAnd left right) (AAnd right left).
Proof. apply EntailsStep. apply ESAndComm. Qed.

Lemma entails_and_assoc_r {Γ F Δ}
    (first second third : assertion Γ F Δ) :
  assertion_entails (AAnd (AAnd first second) third)
    (AAnd first (AAnd second third)).
Proof. apply EntailsStep. apply ESAndAssocR. Qed.

Lemma entails_and_assoc_l {Γ F Δ}
    (first second third : assertion Γ F Δ) :
  assertion_entails (AAnd first (AAnd second third))
    (AAnd (AAnd first second) third).
Proof. apply EntailsStep. apply ESAndAssocL. Qed.

(** Procedure contracts are already instantiated into the caller's typed
    formal/binder context.  Phase 6 will validate implementations of this
    interface using [subst_formals_assertion] and assertion interpretation. *)
Module Type CONTRACT_ENV.
  Parameter required_mask : proc_id -> mask.
  Parameter granted_mask : proc_id -> mask.
  Parameter trusted_atomic : forall Γ, stmt Γ -> Prop.
  Parameter instantiated_pre : forall Γ F Δ args,
    proc_id -> expr_list F Δ args -> assertion Γ F Δ -> Prop.
  Parameter instantiated_post_value : forall Γ F Δ args t,
    proc_id -> expr_list F Δ args -> expr F Δ t -> assertion Γ F Δ -> Prop.
  Parameter instantiated_invariant : forall Γ F Δ args,
    inv_id -> expr_list F Δ args -> assertion Γ F Δ -> Prop.
  Parameter instantiated_predicate : forall Γ F Δ args,
    pred_id -> expr_list F Δ args -> assertion Γ F Δ -> Prop.
  Parameter valid_ghost_update : forall F Δ field,
    expr F Δ (Logic.field_type field) ->
    expr F Δ (Logic.field_type field) -> Prop.
End CONTRACT_ENV.

(** Canonical instantiation of a selected typed procedure contract.  Formal
    arguments are substituted simultaneously; the canonical contract has no
    ambient binders at entry, and its phantom stack context is then changed
    to the caller's context. *)
Definition procedure_pre_instantiation {callee_variables callee_formals}
    (procedure : typed_procedure callee_variables callee_formals)
    {Γ F Δ} (arguments : expr_list F Δ callee_formals)
    (contract : assertion Γ F Δ) : Prop :=
  exists after_binders after_formals,
    subst_bound_assertion empty_bound_subst
      (procedure_precondition _ _ procedure) = Some after_binders /\
    subst_formals_assertion (expr_list_formal_subst arguments) after_binders =
      Some after_formals /\
    reindex_stack_context after_formals contract.

(** Canonical assertions used to verify a procedure body in its own typed
    frame.  For a value-returning procedure, the logical return binder is
    eliminated by reading the distinguished return program variable through
    the body's final symbolic store. *)
Definition procedure_body_pre {Γ F} (procedure : typed_procedure Γ F) :
    assertion Γ F [] :=
  AAnd (AStack (procedure_entry_store _ _ procedure))
    (procedure_precondition _ _ procedure).

Definition procedure_body_post {Γ F} (procedure : typed_procedure Γ F)
    (exit_store : symbolic_store Γ F []) : option (assertion Γ F []) :=
  option_map (AAnd (AStack exit_store))
    (subst_bound_assertion
      (head_bound_subst
        (ERef (lookup_store exit_store _
          (procedure_return_variable _ _ procedure))))
      (procedure_postcondition _ _ procedure)).

(** Phase-7 coherence between the syntax-directed contract oracle and the
    canonical declarations selected from a typed procedure table.  Required
    and granted masks are declaration metadata because [typed_procedure]
    intentionally contains only the typed body and its logical contract. *)
Module Type PROCEDURE_CONTRACT_COHERENCE (Contracts : CONTRACT_ENV).
  Parameter procedures : typed_procedure_environment.
  Parameter declared_required_mask : packed_typed_procedure -> mask.
  Parameter declared_granted_mask : packed_typed_procedure -> mask.

  (** Every usable contract instance selects a declaration with exactly the
      argument telescope carried by the typed call syntax. *)
  Parameter instantiated_pre_selects : forall Γ F Δ args identity
      (arguments : expr_list F Δ args) contract,
    Contracts.instantiated_pre Γ F Δ args identity arguments contract ->
    { callee_variables : context &
      { procedure : typed_procedure callee_variables args |
        lookup_typed_procedure procedures identity =
          Some (pack_typed_procedure procedure) } }.

  Parameter required_mask_coherent : forall identity procedure,
    lookup_typed_procedure procedures identity = Some procedure ->
    Contracts.required_mask identity = declared_required_mask procedure.
  Parameter granted_mask_coherent : forall identity procedure,
    lookup_typed_procedure procedures identity = Some procedure ->
    Contracts.granted_mask identity = declared_granted_mask procedure.

  Parameter instantiated_pre_coherent :
    forall callee_variables callee_formals
      (procedure : typed_procedure callee_variables callee_formals)
      Γ F Δ (arguments : expr_list F Δ callee_formals) contract,
    lookup_typed_procedure procedures (procedure_identity _ _ procedure) =
      Some (pack_typed_procedure procedure) ->
    (Contracts.instantiated_pre Γ F Δ callee_formals
      (procedure_identity _ _ procedure) arguments contract <->
      procedure_pre_instantiation procedure arguments contract).

  Parameter instantiated_post_value_coherent :
    forall callee_variables callee_formals
      (procedure : typed_procedure callee_variables callee_formals)
      Γ F caller_binders t
      (arguments : expr_list F (t :: caller_binders) callee_formals)
      (result : expr F (t :: caller_binders) t)
      (contract : assertion Γ F (t :: caller_binders)),
    lookup_typed_procedure procedures (procedure_identity _ _ procedure) =
      Some (pack_typed_procedure procedure) ->
    (Contracts.instantiated_post_value Γ F (t :: caller_binders)
      callee_formals t
      (procedure_identity _ _ procedure) arguments result contract <->
      exists (Hreturn : procedure_return_type _ _ procedure = t)
        after_formals,
        subst_formals_assertion (expr_list_formal_subst arguments)
          (rename_bound_assertion return_bound_renaming
            (eq_rect _ (fun result_type =>
              assertion callee_variables callee_formals
                (return_context result_type))
              (procedure_postcondition _ _ procedure) t Hreturn)) =
          Some after_formals /\
        reindex_stack_context after_formals contract).
End PROCEDURE_CONTRACT_COHERENCE.

Module LogicRules (Contracts : CONTRACT_ENV).

Inductive mask_transition : mask -> mask -> Prop :=
| MaskUnchanged current_mask : mask_transition current_mask current_mask
| MaskGrant procedure current_mask :
    mask_transition current_mask
      (current_mask ∪ Contracts.granted_mask procedure)
| MaskOpen invariant current_mask :
    mask_transition current_mask (current_mask ∖ {[invariant]})
| MaskClose invariant current_mask :
    mask_transition current_mask (current_mask ∪ {[invariant]})
| MaskCompose first middle last :
    mask_transition first middle -> mask_transition middle last ->
    mask_transition first last.

Inductive RavenHoareTriple {Γ F Δ} :
    assertion Γ F Δ -> stmt Γ -> mask -> mask -> assertion Γ F Δ -> Prop :=
| SkipRule node store frame current_mask :
    RavenHoareTriple
      (AAnd (AStack store) frame) (TSkip node) current_mask current_mask
      (AAnd (AStack store) frame)
| AssertRule node store frame condition current_mask :
    RavenHoareTriple
      (AAnd (AStack store) (AAnd frame (AExpr (symbolize_expr store condition))))
      (TAssert node condition) current_mask current_mask
      (AAnd (AStack store) (AAnd frame (AExpr (symbolize_expr store condition))))
| AssignmentRule t node store target value current_mask :
    RavenHoareTriple (AStack store) (TAssign node target value)
      current_mask current_mask
      (AExists t (AAnd (AStack (update_store_with_bound store target))
        (AExpr (EBinOp (BEq t) (ERef (RefBound MHere))
          (weaken_expr (symbolize_expr store value))))))
| FieldReadRule node store field
    (target : pvar Γ (Logic.field_type field)) base chunk current_mask :
    RavenHoareTriple
      (AAnd (AStack store) (AOwn field (symbolize_expr store base) chunk))
      (TFieldRead node field target base) current_mask current_mask
      (AExists (Logic.field_type field)
        (AAnd (AStack (update_store_with_bound store target))
        (AAnd
          (AOwn field (weaken_expr (symbolize_expr store base))
            (weaken_expr chunk))
          (AExpr (EBinOp (BEq (Logic.field_type field)) (ERef (RefBound MHere))
            (weaken_expr chunk))))))
| FieldWriteRule node store field base
    (value : pexpr Γ (Logic.field_type field)) old_chunk current_mask :
    RavenHoareTriple
      (AAnd (AStack store) (AOwn field (symbolize_expr store base) old_chunk))
      (TFieldWrite node field base value) current_mask current_mask
      (AAnd (AStack store)
        (AOwn field (symbolize_expr store base) (symbolize_expr store value)))
| AllocationRule node store target fields current_mask :
    NoDup (map field_init_id fields) ->
    RavenHoareTriple
      (AStack store) (TAlloc node target fields) current_mask current_mask
      (AExists TRef
        (AAnd (AStack (update_store_with_bound store target))
          (allocated_fields_assertion store fields)))
| GhostUpdateRule node store field base old_value new_value current_mask :
    Contracts.valid_ghost_update F Δ field
      (symbolize_expr store old_value) (symbolize_expr store new_value) ->
    RavenHoareTriple
      (AAnd (AStack store)
        (AOwn field (symbolize_expr store base)
          (symbolize_expr store old_value)))
      (TGhostUpdate node field base old_value new_value)
      current_mask current_mask
      (AAnd (AStack store)
        (AOwn field (symbolize_expr store base)
          (symbolize_expr store new_value)))
| SequenceRule node pre middle post first second mask1 mask2 mask3 :
    RavenHoareTriple pre first mask1 mask2 middle ->
    RavenHoareTriple middle second mask2 mask3 post ->
    RavenHoareTriple pre (TSeq node first second) mask1 mask3 post
| ConditionalRule node store frame condition then_branch else_branch post
    mask_pre mask_post :
    RavenHoareTriple
      (AAnd (AStack store)
        (AAnd frame (AExpr (symbolize_expr store condition))))
      then_branch mask_pre mask_post post ->
    RavenHoareTriple
      (AAnd (AStack store)
        (AAnd frame (AExpr (EUnOp UNot (symbolize_expr store condition)))))
      else_branch mask_pre mask_post post ->
    RavenHoareTriple (AAnd (AStack store) frame)
      (TIf node condition then_branch else_branch)
      mask_pre mask_post post
| FrameRule pre post frame statement mask_pre mask_post :
    RavenHoareTriple pre statement mask_pre mask_post post ->
    RavenHoareTriple (AAnd pre frame) statement mask_pre mask_post
      (AAnd post frame)
| ConsequenceRule pre pre' post post' statement mask_pre mask_post :
    RavenHoareTriple pre statement mask_pre mask_post post ->
    assertion_entails pre' pre -> assertion_entails post post' ->
    RavenHoareTriple pre' statement mask_pre mask_post post'
| ExistsElimRule t (body : assertion Γ F (t :: Δ)) post statement
    mask_pre mask_post :
    RavenHoareTriple (Δ := t :: Δ) body statement mask_pre mask_post
      (weaken_assertion post) ->
    RavenHoareTriple (AExists t body) statement mask_pre mask_post post
| ExistsPreserveRule t (body post : assertion Γ F (t :: Δ)) statement
    mask_pre mask_post :
    RavenHoareTriple (Δ := t :: Δ) body statement mask_pre mask_post post ->
    RavenHoareTriple (AExists t body) statement mask_pre mask_post
      (AExists t post)
| AtomicBlockRule node pre post body mask_pre mask_post :
    Contracts.trusted_atomic Γ body ->
    RavenHoareTriple pre body mask_pre mask_post post ->
    RavenHoareTriple pre (TAtomic node body) mask_pre mask_post post
| CallDiscardRule args t node procedure arguments store contract_pre
    contract_post current_mask :
    Contracts.instantiated_pre Γ F Δ args procedure
      (symbolize_expr_list store arguments) contract_pre ->
    Contracts.instantiated_post_value Γ F (t :: Δ) args t procedure
      (weaken_expr_list (symbolize_expr_list store arguments))
      (ERef (RefBound MHere)) contract_post ->
    Contracts.required_mask procedure ⊆ current_mask ->
    RavenHoareTriple
      (AAnd (AStack store) contract_pre)
      (TCall node procedure arguments (@CTDiscard Γ t))
      current_mask (current_mask ∪ Contracts.granted_mask procedure)
      (AExists t (AAnd (AStack (weaken_store store)) contract_post))
| CallStoreRule args t node procedure arguments store target
    contract_pre contract_post current_mask :
    Contracts.instantiated_pre Γ F Δ args procedure
      (symbolize_expr_list store arguments) contract_pre ->
    Contracts.instantiated_post_value Γ F (t :: Δ) args t procedure
      (weaken_expr_list (symbolize_expr_list store arguments))
      (ERef (RefBound MHere)) contract_post ->
    Contracts.required_mask procedure ⊆ current_mask ->
    RavenHoareTriple
      (AAnd (AStack store) contract_pre)
      (TCall node procedure arguments (CTStore target))
      current_mask (current_mask ∪ Contracts.granted_mask procedure)
      (AExists t
        (AAnd (AStack (update_store_with_bound store target)) contract_post))
| UnfoldInvariantRule node invariant arguments store body current_mask :
    invariant ∈ current_mask ->
    Contracts.instantiated_invariant Γ F Δ (Logic.invariant_args invariant) invariant
      (symbolize_expr_list store arguments) body ->
    RavenHoareTriple
      (AAnd (AStack store)
        (AInvariant invariant (symbolize_expr_list store arguments)))
      (TUnfold node invariant arguments)
      current_mask (current_mask ∖ {[invariant]})
      (AAnd (AStack store) body)
| FoldInvariantRule node invariant arguments store body current_mask :
    Contracts.instantiated_invariant Γ F Δ (Logic.invariant_args invariant) invariant
      (symbolize_expr_list store arguments) body ->
    RavenHoareTriple
      (AAnd (AStack store) body)
      (TFold node invariant arguments)
      current_mask (current_mask ∪ {[invariant]})
      (AAnd (AStack store)
        (AInvariant invariant (symbolize_expr_list store arguments)))
| UnfoldPredicateRule node predicate arguments store body current_mask :
    Contracts.instantiated_predicate Γ F Δ (Logic.predicate_args predicate)
      predicate (symbolize_expr_list store arguments) body ->
    RavenHoareTriple
      (AAnd (AStack store)
        (APredicate predicate (symbolize_expr_list store arguments)))
      (TPredicateUnfold node predicate arguments) current_mask current_mask
      (AAnd (AStack store) body)
| FoldPredicateRule node predicate arguments store body current_mask :
    Contracts.instantiated_predicate Γ F Δ (Logic.predicate_args predicate)
      predicate (symbolize_expr_list store arguments) body ->
    RavenHoareTriple
      (AAnd (AStack store) body)
      (TPredicateFold node predicate arguments) current_mask current_mask
      (AAnd (AStack store)
        (APredicate predicate (symbolize_expr_list store arguments)))
| SpawnRule args node procedure arguments store contract_pre current_mask :
    Contracts.instantiated_pre Γ F Δ args procedure
      (symbolize_expr_list store arguments) contract_pre ->
    Contracts.required_mask procedure ⊆ current_mask ->
    RavenHoareTriple
      (AAnd (AStack store) contract_pre)
      (TSpawn node procedure arguments) current_mask current_mask
      (AStack store)
| StackConsequenceRule store body body' post post' statement mask_pre mask_post :
    RavenHoareTriple (AAnd (AStack store) body) statement mask_pre mask_post post ->
    assertion_entails body' body -> assertion_entails post post' ->
    RavenHoareTriple (AAnd (AStack store) body') statement mask_pre mask_post
      post'.

(** The compatibility-stage resource relation.  Unlike [RavenHoareTriple],
    this relation deliberately has no analyzer-owned mask state. *)
Inductive RavenResourceTriple {Γ F Δ} :
    assertion Γ F Δ -> stmt Γ -> assertion Γ F Δ -> Prop :=
| ResourceSkipRule node store frame :
    RavenResourceTriple
      (AAnd (AStack store) frame) (TSkip node)
      (AAnd (AStack store) frame)
| ResourceAssertRule node store frame condition :
    RavenResourceTriple
      (AAnd (AStack store) (AAnd frame (AExpr (symbolize_expr store condition))))
      (TAssert node condition)
      (AAnd (AStack store) (AAnd frame (AExpr (symbolize_expr store condition))))
| ResourceAssignmentRule t node store target value :
    RavenResourceTriple (AStack store) (TAssign node target value)
      (AExists t (AAnd (AStack (update_store_with_bound store target))
        (AExpr (EBinOp (BEq t) (ERef (RefBound MHere))
          (weaken_expr (symbolize_expr store value))))))
| ResourceFieldReadRule node store field
    (target : pvar Γ (Logic.field_type field)) base chunk :
    RavenResourceTriple
      (AAnd (AStack store) (AOwn field (symbolize_expr store base) chunk))
      (TFieldRead node field target base)
      (AExists (Logic.field_type field)
        (AAnd (AStack (update_store_with_bound store target))
        (AAnd
          (AOwn field (weaken_expr (symbolize_expr store base))
            (weaken_expr chunk))
          (AExpr (EBinOp (BEq (Logic.field_type field)) (ERef (RefBound MHere))
            (weaken_expr chunk))))))
| ResourceFieldWriteRule node store field base
    (value : pexpr Γ (Logic.field_type field)) old_chunk :
    RavenResourceTriple
      (AAnd (AStack store) (AOwn field (symbolize_expr store base) old_chunk))
      (TFieldWrite node field base value)
      (AAnd (AStack store)
        (AOwn field (symbolize_expr store base) (symbolize_expr store value)))
| ResourceAllocationRule node store target fields :
    NoDup (map field_init_id fields) ->
    RavenResourceTriple
      (AStack store) (TAlloc node target fields)
      (AExists TRef
        (AAnd (AStack (update_store_with_bound store target))
          (allocated_fields_assertion store fields)))
| ResourceGhostUpdateRule node store field base old_value new_value :
    Contracts.valid_ghost_update F Δ field
      (symbolize_expr store old_value) (symbolize_expr store new_value) ->
    RavenResourceTriple
      (AAnd (AStack store)
        (AOwn field (symbolize_expr store base)
          (symbolize_expr store old_value)))
      (TGhostUpdate node field base old_value new_value)
      (AAnd (AStack store)
        (AOwn field (symbolize_expr store base)
          (symbolize_expr store new_value)))
| ResourceSequenceRule node pre middle post first second :
    RavenResourceTriple pre first middle ->
    RavenResourceTriple middle second post ->
    RavenResourceTriple pre (TSeq node first second) post
| ResourceConditionalRule node store frame condition then_branch else_branch post :
    RavenResourceTriple
      (AAnd (AStack store)
        (AAnd frame (AExpr (symbolize_expr store condition))))
      then_branch post ->
    RavenResourceTriple
      (AAnd (AStack store)
        (AAnd frame (AExpr (EUnOp UNot (symbolize_expr store condition)))))
      else_branch post ->
    RavenResourceTriple (AAnd (AStack store) frame)
      (TIf node condition then_branch else_branch) post
| ResourceFrameRule pre post frame statement :
    RavenResourceTriple pre statement post ->
    RavenResourceTriple (AAnd pre frame) statement (AAnd post frame)
| ResourceConsequenceRule pre pre' post post' statement :
    RavenResourceTriple pre statement post ->
    assertion_entails pre' pre -> assertion_entails post post' ->
    RavenResourceTriple pre' statement post'
| ResourceExistsElimRule t (body : assertion Γ F (t :: Δ)) post statement :
    RavenResourceTriple (Δ := t :: Δ) body statement
      (weaken_assertion post) ->
    RavenResourceTriple (AExists t body) statement post
| ResourceExistsPreserveRule t (body post : assertion Γ F (t :: Δ)) statement :
    RavenResourceTriple (Δ := t :: Δ) body statement post ->
    RavenResourceTriple (AExists t body) statement (AExists t post)
| ResourceAtomicBlockRule node pre post body :
    Contracts.trusted_atomic Γ body ->
    RavenResourceTriple pre body post ->
    RavenResourceTriple pre (TAtomic node body) post
| ResourceCallDiscardRule args t node procedure arguments store contract_pre
    contract_post :
    Contracts.instantiated_pre Γ F Δ args procedure
      (symbolize_expr_list store arguments) contract_pre ->
    Contracts.instantiated_post_value Γ F (t :: Δ) args t procedure
      (weaken_expr_list (symbolize_expr_list store arguments))
      (ERef (RefBound MHere)) contract_post ->
    RavenResourceTriple
      (AAnd (AStack store) contract_pre)
      (TCall node procedure arguments (@CTDiscard Γ t))
      (AExists t (AAnd (AStack (weaken_store store)) contract_post))
| ResourceCallStoreRule args t node procedure arguments store target
    contract_pre contract_post :
    Contracts.instantiated_pre Γ F Δ args procedure
      (symbolize_expr_list store arguments) contract_pre ->
    Contracts.instantiated_post_value Γ F (t :: Δ) args t procedure
      (weaken_expr_list (symbolize_expr_list store arguments))
      (ERef (RefBound MHere)) contract_post ->
    RavenResourceTriple
      (AAnd (AStack store) contract_pre)
      (TCall node procedure arguments (CTStore target))
      (AExists t
        (AAnd (AStack (update_store_with_bound store target)) contract_post))
| ResourceUnfoldInvariantRule node invariant arguments store body :
    Contracts.instantiated_invariant Γ F Δ (Logic.invariant_args invariant) invariant
      (symbolize_expr_list store arguments) body ->
    RavenResourceTriple
      (AAnd (AStack store)
        (AInvariant invariant (symbolize_expr_list store arguments)))
      (TUnfold node invariant arguments)
      (AAnd (AStack store) body)
| ResourceFoldInvariantRule node invariant arguments store body :
    Contracts.instantiated_invariant Γ F Δ (Logic.invariant_args invariant) invariant
      (symbolize_expr_list store arguments) body ->
    RavenResourceTriple
      (AAnd (AStack store) body)
      (TFold node invariant arguments)
      (AAnd (AStack store)
        (AInvariant invariant (symbolize_expr_list store arguments)))
| ResourceUnfoldPredicateRule node predicate arguments store body :
    Contracts.instantiated_predicate Γ F Δ (Logic.predicate_args predicate)
      predicate (symbolize_expr_list store arguments) body ->
    RavenResourceTriple
      (AAnd (AStack store)
        (APredicate predicate (symbolize_expr_list store arguments)))
      (TPredicateUnfold node predicate arguments)
      (AAnd (AStack store) body)
| ResourceFoldPredicateRule node predicate arguments store body :
    Contracts.instantiated_predicate Γ F Δ (Logic.predicate_args predicate)
      predicate (symbolize_expr_list store arguments) body ->
    RavenResourceTriple
      (AAnd (AStack store) body)
      (TPredicateFold node predicate arguments)
      (AAnd (AStack store)
        (APredicate predicate (symbolize_expr_list store arguments)))
| ResourceSpawnRule args node procedure arguments store contract_pre :
    Contracts.instantiated_pre Γ F Δ args procedure
      (symbolize_expr_list store arguments) contract_pre ->
    RavenResourceTriple
      (AAnd (AStack store) contract_pre)
      (TSpawn node procedure arguments) (AStack store)
| ResourceStackConsequenceRule store body body' post post' statement :
    RavenResourceTriple (AAnd (AStack store) body) statement post ->
    assertion_entails body' body -> assertion_entails post post' ->
    RavenResourceTriple (AAnd (AStack store) body') statement post'.

Theorem RavenHoareTriple_erases_resource {Γ F Δ}
    (pre : assertion Γ F Δ) statement mask_pre mask_post
    (post : assertion Γ F Δ) :
  RavenHoareTriple pre statement mask_pre mask_post post ->
  RavenResourceTriple pre statement post.
Proof.
  intro Htriple. induction Htriple;
    eauto using ResourceSkipRule, ResourceAssertRule,
      ResourceAssignmentRule, ResourceFieldReadRule,
      ResourceFieldWriteRule, ResourceAllocationRule,
      ResourceGhostUpdateRule, ResourceSequenceRule,
      ResourceConditionalRule, ResourceFrameRule,
      ResourceConsequenceRule, ResourceExistsElimRule,
      ResourceExistsPreserveRule, ResourceAtomicBlockRule,
      ResourceCallDiscardRule, ResourceCallStoreRule,
      ResourceUnfoldInvariantRule, ResourceFoldInvariantRule,
      ResourceUnfoldPredicateRule, ResourceFoldPredicateRule,
      ResourceSpawnRule, ResourceStackConsequenceRule.
Qed.

Theorem RavenHoareTriple_mask_transition {Γ F Δ}
    (pre post : assertion Γ F Δ) statement mask_pre mask_post :
  RavenHoareTriple pre statement mask_pre mask_post post ->
  mask_transition mask_pre mask_post.
Proof.
  intro Htriple. induction Htriple;
    eauto using mask_transition.
Qed.

End LogicRules.
End Make.
End TypedHoare.

Module TypedHoareExamples.

Module UnitRA := TypedCoreExamples.UnitRA.

Module TinyLogic <: TypedAssertion.LOGIC_SIGNATURE.
  Definition field_type (_ : TypedCore.field_id) := TypedCore.TInt.
  Definition predicate_args (_ : TypedCore.pred_id) : TypedCore.context := [].
  Definition invariant_args (_ : TypedCore.inv_id) : TypedCore.context := [].
End TinyLogic.

Module Hoare := TypedHoare.Make UnitRA TinyLogic.
Import TypedCore Hoare.Core Hoare.Assertions Hoare.IR Hoare.

Module EmptyContracts <: Hoare.CONTRACT_ENV.
  Definition required_mask (_ : proc_id) : mask := ∅.
  Definition granted_mask (_ : proc_id) : mask := ∅.
  Definition trusted_atomic {Γ} (_ : stmt Γ) : Prop := True.
  Definition instantiated_pre Γ F Δ args (_ : proc_id)
      (_ : expr_list F Δ args) (_ : assertion Γ F Δ) : Prop := False.
  Definition instantiated_post_value Γ F Δ args t (_ : proc_id)
      (_ : expr_list F Δ args) (_ : expr F Δ t)
      (_ : assertion Γ F Δ) : Prop := False.
  Definition instantiated_invariant Γ F Δ args (_ : inv_id)
      (_ : expr_list F Δ args) (_ : assertion Γ F Δ) : Prop := False.
  Definition instantiated_predicate Γ F Δ args (_ : pred_id)
      (_ : expr_list F Δ args) (_ : assertion Γ F Δ) : Prop := False.
  Definition valid_ghost_update F Δ field
      (_ _ : expr F Δ (TinyLogic.field_type field)) : Prop := False.
End EmptyContracts.

Module Rules := Hoare.LogicRules EmptyContracts.
Import Rules.

Definition empty_store : symbolic_store [] [] [] :=
  StoreNil.

Example typed_skip_derivation :
  RavenHoareTriple
    (AAnd (AStack empty_store) (APure True))
    (TSkip 1%positive)
    ∅ ∅
    (AAnd (AStack empty_store) (APure True)).
Proof.
  apply SkipRule.
Qed.

Definition program_store : symbolic_store [TInt; TRef] [TInt; TRef] [] :=
  StoreCons (RefFormal MHere)
    (StoreCons (RefFormal (MThere MHere)) StoreNil).

Definition integer_target : pvar [TInt; TRef] TInt := MHere.
Definition reference_variable : pvar [TInt; TRef] TRef := MThere MHere.
Definition reference_expression : pexpr [TInt; TRef] TRef :=
  PEVar reference_variable.

Example typed_assignment_derivation :
  RavenHoareTriple
    (AStack program_store)
    (TAssign 1%positive integer_target (PEVal (VInt 1%Z)))
    ∅ ∅
    (AExists TInt
      (AAnd (AStack (update_store_with_bound program_store integer_target))
        (AExpr (EBinOp (BEq TInt) (ERef (RefBound MHere))
          (weaken_expr
            (symbolize_expr program_store (PEVal (VInt 1%Z)))))))).
Proof. apply AssignmentRule. Qed.

Example typed_field_read_derivation :
  RavenHoareTriple
    (AAnd (AStack program_store)
      (AOwn 1%positive (symbolize_expr program_store reference_expression)
        (EVal (VInt 0%Z))))
    (TFieldRead 2%positive 1%positive integer_target reference_expression)
    ∅ ∅
    (AExists TInt
      (AAnd (AStack (update_store_with_bound program_store integer_target))
        (AAnd
          (AOwn 1%positive
            (weaken_expr (symbolize_expr program_store reference_expression))
            (weaken_expr (EVal (VInt 0%Z))))
          (AExpr (EBinOp (BEq TInt) (ERef (RefBound MHere))
            (weaken_expr (EVal (VInt 0%Z)))))))).
Proof. apply FieldReadRule. Qed.

Definition initial_fields : list (field_init [TInt; TRef]) :=
  [FieldInit 1%positive (PEVal (VInt 0%Z))].

Example typed_allocation_derivation :
  RavenHoareTriple
    (AStack program_store)
    (TAlloc 4%positive reference_variable initial_fields)
    ∅ ∅
    (AExists TRef
      (AAnd
        (AStack (update_store_with_bound program_store reference_variable))
        (allocated_fields_assertion program_store initial_fields))).
Proof.
  apply AllocationRule. unfold initial_fields. simpl.
  constructor.
  - set_solver.
  - constructor.
Qed.

Definition owned_zero : assertion [TInt; TRef] [TInt; TRef] [] :=
  AOwn 1%positive (symbolize_expr program_store reference_expression)
    (EVal (VInt 0%Z)).

Definition assignment_post : assertion [TInt; TRef] [TInt; TRef] [] :=
  AExists TInt
    (AAnd (AStack (update_store_with_bound program_store integer_target))
      (AExpr (EBinOp (BEq TInt) (ERef (RefBound MHere))
        (weaken_expr
          (symbolize_expr program_store (PEVal (VInt 1%Z))))))).

Definition read_store : symbolic_store [TInt; TRef] [TInt; TRef] [TInt] :=
  update_store_with_bound program_store integer_target.

Definition read_owned : assertion [TInt; TRef] [TInt; TRef] [TInt] :=
  AOwn 1%positive
    (weaken_expr (symbolize_expr program_store reference_expression))
    (weaken_expr (EVal (VInt 0%Z))).

Definition inner_assignment_post :
    assertion [TInt; TRef] [TInt; TRef] [TInt] :=
  AExists TInt
    (AAnd (AStack (update_store_with_bound read_store integer_target))
      (AExpr (EBinOp (BEq TInt) (ERef (RefBound MHere))
        (weaken_expr
          (symbolize_expr read_store (PEVal (VInt 1%Z))))))).

Definition read_then_assign_post : assertion [TInt; TRef] [TInt; TRef] [] :=
  AExists TInt (AAnd inner_assignment_post read_owned).

Example typed_read_then_assign_derivation :
  RavenHoareTriple
    (AAnd (AStack program_store) owned_zero)
    (TSeq 3%positive
      (TFieldRead 2%positive 1%positive integer_target reference_expression)
      (TAssign 1%positive integer_target (PEVal (VInt 1%Z))))
    ∅ ∅ read_then_assign_post.
Proof.
  eapply SequenceRule.
  - apply FieldReadRule.
  - apply ExistsPreserveRule.
    eapply ConsequenceRule.
    + apply FrameRule. apply AssignmentRule.
    + apply EntailsAndMono.
      * apply EntailsRefl.
      * apply EntailsStep. apply ESAndElimL.
    + apply EntailsRefl.
Qed.

End TypedHoareExamples.
