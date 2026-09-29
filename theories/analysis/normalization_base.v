From Coq Require Import ClassicalEpsilon FunctionalExtensionality Lia
  Program.Equality.
From stdpp Require Import gmap sets.

From raven Require Import runtime.erasure analysis.structured_certificates verification.expressions analysis.atomicity verification.assertions verification.ir soundness.runtime_model
  verification.access_layout verification.conditional_derivations.

(** Certified source-to-source normalization for typed Raven programs. *)
Module NormalizationBase.

Module Hoare := Runtime.Validation.Hoare.
Module Assertions := Runtime.Translation.Assertions.
Module Core := Runtime.Core.
Module IR := Runtime.IR.
Module GenericRegions := Runtime.GenericRegions.
Module Atom := GenericRegions.Atomicity.
Import Core IR Runtime IR Core Runtime.Translation.
Import StructuredCertificates.
Import ConditionalDerivations.
Import AccessLayout (canonical_branch).

Notation pexpr_dependencies :=
  Hoare.ResourceHoare.pexpr_dependencies.
Notation pexpr_list_dependencies :=
  Hoare.ResourceHoare.pexpr_list_dependencies.
Notation statement_writes := Hoare.ResourceHoare.statement_writes.

Section WithSignature.
Context {RAs : ra_base.RAConfig} {Logic : Assertion.LogicSignature}
  {Cost : AnalysisView.LeafCost}.

Fixpoint unfold_free {Γ} (statement : stmt Γ) : Prop :=
  match statement with
  | TUnfold _ _ => False
  | TInvAccess _ _ body | TAtomic body => unfold_free body
  | TGhostVal _ _ _ body => unfold_free body
  | TIf _ then_branch else_branch | TGhostIf _ then_branch else_branch =>
      unfold_free then_branch /\ unfold_free else_branch
  | TSeq first second => unfold_free first /\ unfold_free second
  | _ => True
  end.

Fixpoint access_neutral {Γ} (statement : stmt Γ) : Prop :=
  match statement with
  | TUnfold _ _ | TFold _ _ => False
  | TInvAccess _ _ body | TAtomic body => access_neutral body
  | TGhostVal _ _ _ body => access_neutral body
  | TIf _ then_branch else_branch | TGhostIf _ then_branch else_branch =>
      access_neutral then_branch /\ access_neutral else_branch
  | TSeq first second => access_neutral first /\ access_neutral second
  | _ => True
  end.

(** Syntactic acceptance certificate for the first end-to-end normalizer.
    It records only the deliberately supported source layouts; it is not an
    execution semantics or a second interpretation of statements.  The
    analyzer certificate remains responsible for all LIFO and atomic-step
    facts, while assertion alignment recovers invariant instances.  A
    [nested] statement lies inside an open access (an access body or branch
    prefix): it folds only the invariants it unfolds. *)
Inductive baseline_normalizable {Γ} : bool -> stmt Γ -> Type :=
| BaselineUnfoldFree (nested : bool) (statement : stmt Γ) :
    (if nested then access_neutral statement else unfold_free statement) ->
    baseline_normalizable nested statement
| BaselineSequence nested first second :
    access_neutral first ->
    baseline_normalizable nested second ->
    baseline_normalizable nested (TSeq first second)
| BaselineBalancedSequence nested first second :
    baseline_normalizable nested first ->
    baseline_normalizable nested second ->
    baseline_normalizable nested (TSeq first second)
| BaselineConditional nested condition then_branch else_branch :
    baseline_normalizable nested then_branch ->
    baseline_normalizable nested else_branch ->
    baseline_normalizable nested (TIf condition then_branch else_branch)
| BaselineTerminalAccess nested
    invariant opening_arguments closing_arguments body :
    baseline_normalizable true body ->
    opening_arguments = closing_arguments ->
    pexpr_list_dependencies opening_arguments ## statement_writes body ->
    baseline_normalizable nested
      (TSeq (TUnfold invariant opening_arguments)
        (TSeq body
          (TFold invariant closing_arguments)))
| BaselineAccessThen nested
    invariant opening_arguments closing_arguments
    body work :
    baseline_normalizable true body ->
    opening_arguments = closing_arguments ->
    pexpr_list_dependencies opening_arguments ## statement_writes body ->
    baseline_normalizable nested work ->
    baseline_normalizable nested
      (TSeq (TUnfold invariant opening_arguments)
        (TSeq body
          (TSeq
            (TFold invariant closing_arguments) work)))
| BaselineGhostVal nested name t initializer body :
    @baseline_normalizable (ghost_val t :: Γ) nested body ->
    baseline_normalizable nested (TGhostVal name t initializer body)
| BaselineGhostConditional nested condition then_branch else_branch :
    baseline_normalizable nested then_branch ->
    baseline_normalizable nested else_branch ->
    baseline_normalizable nested (TGhostIf condition then_branch else_branch)
(** A conditional access whose prefix is proof-only is distributed into the
    branches. *)
| BaselineDistributedAccess nested invariant arguments prefix guard
    then_prefix then_continuation else_prefix else_continuation :
    AccessLayout.fold_is invariant arguments (TFold invariant arguments) = true ->
    baseline_normalizable true prefix ->
    baseline_normalizable true then_prefix ->
    baseline_normalizable true else_prefix ->
    proof_onlyb prefix = true ->
    guard_proof_only guard
      (canonical_branch invariant arguments then_prefix then_continuation)
      (canonical_branch invariant arguments else_prefix else_continuation) =
      true ->
    pexpr_list_dependencies arguments ##
      statement_writes (TSeq prefix (TSeq TDone then_prefix)) ->
    pexpr_list_dependencies arguments ##
      statement_writes (TSeq prefix (TSeq TDone else_prefix)) ->
    baseline_normalizable nested then_continuation ->
    baseline_normalizable nested else_continuation ->
    baseline_normalizable nested
      (conditional_access invariant arguments prefix guard then_prefix
        then_continuation else_prefix else_continuation)
(** Otherwise the branch prefixes are proof-only and the access is factored
    out of the conditional. *)
| BaselineFactoredAccess nested invariant arguments prefix guard
    then_prefix then_continuation else_prefix else_continuation :
    AccessLayout.fold_is invariant arguments (TFold invariant arguments) = true ->
    baseline_normalizable true prefix ->
    access_neutral then_prefix -> access_neutral else_prefix ->
    proof_onlyb prefix = false ->
    proof_onlyb then_prefix = true -> proof_onlyb else_prefix = true ->
    guard_proof_only guard then_continuation else_continuation = true ->
    pexpr_list_dependencies arguments ##
      statement_writes (TSeq prefix (TSeq TDone then_prefix)) ->
    pexpr_list_dependencies arguments ##
      statement_writes (TSeq prefix (TSeq TDone else_prefix)) ->
    baseline_normalizable nested then_continuation ->
    baseline_normalizable nested else_continuation ->
    baseline_normalizable nested
      (conditional_access invariant arguments prefix guard then_prefix
        then_continuation else_prefix else_continuation).

(** Executable recognizers for the source-shape portion of the restricted
    analysis.  Argument stability and write effects are intentionally not
    decided here: Step 3 enriches the access stack with precisely that
    information. *)
Fixpoint unfold_freeb {Γ} (statement : stmt Γ) : bool :=
  match statement with
  | TUnfold _ _ => false
  | TInvAccess _ _ body | TAtomic body => unfold_freeb body
  | TGhostVal _ _ _ body => unfold_freeb body
  | TIf _ then_branch else_branch | TGhostIf _ then_branch else_branch =>
      unfold_freeb then_branch && unfold_freeb else_branch
  | TSeq first second => unfold_freeb first && unfold_freeb second
  | _ => true
  end.

Fixpoint access_neutralb {Γ} (statement : stmt Γ) : bool :=
  match statement with
  | TUnfold _ _ | TFold _ _ => false
  | TInvAccess _ _ body | TAtomic body => access_neutralb body
  | TGhostVal _ _ _ body => access_neutralb body
  | TIf _ then_branch else_branch | TGhostIf _ then_branch else_branch =>
      access_neutralb then_branch && access_neutralb else_branch
  | TSeq first second => access_neutralb first && access_neutralb second
  | _ => true
  end.

(** The shape conditions of a canonical conditional access
    ([conditional_access]), given its closing statements. *)
Definition conditional_access_shapeb {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_closing then_continuation
      else_prefix else_closing else_continuation : stmt Γ) : bool :=
  AccessLayout.fold_is invariant arguments then_closing &&
  AccessLayout.fold_is invariant arguments else_closing &&
  (if proof_onlyb prefix
   then guard_proof_only guard
     (canonical_branch invariant arguments then_prefix then_continuation)
     (canonical_branch invariant arguments else_prefix else_continuation)
   else access_neutralb then_prefix && access_neutralb else_prefix &&
     proof_onlyb then_prefix && proof_onlyb else_prefix &&
     guard_proof_only guard then_continuation else_continuation).

(** The invariant arguments are stable across each branch's access body. *)
Definition conditional_access_stableb {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix then_prefix else_prefix : stmt Γ) : bool :=
  bool_decide (pexpr_list_dependencies arguments ##
    statement_writes (TSeq prefix (TSeq TDone then_prefix))) &&
  bool_decide (pexpr_list_dependencies arguments ##
    statement_writes (TSeq prefix (TSeq TDone else_prefix))).

(** Conservative executable check for the source layouts handled by the
    baseline normalizer.  A raw unfold is accepted only when its enclosing
    sequence exposes the matching fold, or is a canonical conditional access
    ([conditional_access]); access bodies and prefixes are checked as
    [nested] statements.  For linear accesses the equality test is only for
    invariant identities; argument compatibility is deferred to the
    effect-aware pass. *)
Fixpoint restricted_fragment_shape_check {Γ} (nested : bool)
    (statement : stmt Γ) : bool :=
  match statement with
  | TUnfold _ _ => false
  | TFold _ _ => negb nested
  | TInvAccess _ _ body | TAtomic body =>
      if nested then access_neutralb body else unfold_freeb body
  | TGhostVal _ _ _ body => restricted_fragment_shape_check nested body
  | TIf _ then_branch else_branch | TGhostIf _ then_branch else_branch =>
      restricted_fragment_shape_check nested then_branch &&
        restricted_fragment_shape_check nested else_branch
  | TSeq first second =>
      match first, second with
      | TUnfold opening_invariant _,
          TSeq body (TFold closing_invariant _) =>
          bool_decide (opening_invariant = closing_invariant) &&
            restricted_fragment_shape_check true body
      | TUnfold opening_invariant _,
          TSeq body (TSeq (TFold closing_invariant _) work) =>
          bool_decide (opening_invariant = closing_invariant) &&
            restricted_fragment_shape_check true body &&
            restricted_fragment_shape_check nested work
      | TUnfold invariant arguments,
          TSeq prefix (TIf condition then_branch else_branch) =>
          match then_branch, else_branch with
          | TSeq then_prefix (TSeq then_closing then_continuation),
              TSeq else_prefix (TSeq else_closing else_continuation) =>
              conditional_access_shapeb invariant arguments prefix
                (GuardRuntime condition) then_prefix then_closing then_continuation
                else_prefix else_closing else_continuation &&
              restricted_fragment_shape_check true prefix &&
              restricted_fragment_shape_check true then_prefix &&
              restricted_fragment_shape_check true else_prefix &&
              restricted_fragment_shape_check nested then_continuation &&
              restricted_fragment_shape_check nested else_continuation
          | _, _ => false
          end
      | TUnfold invariant arguments,
          TSeq prefix (TGhostIf condition then_branch else_branch) =>
          match then_branch, else_branch with
          | TSeq then_prefix (TSeq then_closing then_continuation),
              TSeq else_prefix (TSeq else_closing else_continuation) =>
              conditional_access_shapeb invariant arguments prefix
                (GuardGhost condition) then_prefix then_closing then_continuation
                else_prefix else_closing else_continuation &&
              restricted_fragment_shape_check true prefix &&
              restricted_fragment_shape_check true then_prefix &&
              restricted_fragment_shape_check true else_prefix &&
              restricted_fragment_shape_check nested then_continuation &&
              restricted_fragment_shape_check nested else_continuation
          | _, _ => false
          end
      | _, _ =>
          restricted_fragment_shape_check nested first &&
            restricted_fragment_shape_check nested second
      end
  | _ => true
  end.

Definition restricted_fragment_shape {Γ} (statement : stmt Γ) : Prop :=
  restricted_fragment_shape_check false statement = true.

Lemma normalization_lookup_weaken_store {Γ F Δ keep t u}
    (store : symbolic_store Γ F Δ) (variable : lvar keep Γ t) :
  lookup_store (@Assertions.weaken_store Γ F Δ u store) t variable =
    @Assertions.weaken_ref F Δ t u (lookup_store store t variable).
Proof. apply IR.lookup_weaken_store. Qed.

Lemma symbolize_expr_weaken_store {Γ F Δ keep t u}
    (store : symbolic_store Γ F Δ) (expression : pexpr keep Γ t) :
  IR.symbolize_expr (@Assertions.weaken_store Γ F Δ u store) expression =
    Assertions.weaken_expr (IR.symbolize_expr store expression).
Proof.
  induction expression; cbn [IR.symbolize_expr Assertions.weaken_expr].
  - f_equal. apply normalization_lookup_weaken_store.
  - reflexivity.
  - f_equal. exact IHexpression.
  - f_equal; assumption.
Qed.

Lemma symbolize_expr_list_weaken_store {Γ F Δ keep ts u}
    (store : symbolic_store Γ F Δ) (expressions : pexpr_list keep Γ ts) :
  IR.symbolize_expr_list (@Assertions.weaken_store Γ F Δ u store)
    expressions =
    Assertions.weaken_expr_list (IR.symbolize_expr_list store expressions).
Proof.
  induction expressions; cbn [IR.symbolize_expr_list
    Assertions.weaken_expr_list].
  - reflexivity.
  - f_equal; auto using symbolize_expr_weaken_store.
Qed.

Definition restricted_access_boundary_check {Γ invariant}
    (opening_arguments closing_arguments :
      gexpr_list Γ (Assertion.invariant_args invariant))
    (body : stmt Γ) : bool :=
  AccessLayout.arguments_eqb opening_arguments closing_arguments &&
    bool_decide (pexpr_list_dependencies opening_arguments ##
      statement_writes body).

Lemma restricted_access_boundary_check_sound {Γ invariant}
    (opening_arguments closing_arguments :
      gexpr_list Γ (Assertion.invariant_args invariant)) body :
  restricted_access_boundary_check opening_arguments closing_arguments body =
    true ->
  opening_arguments = closing_arguments /\
  pexpr_list_dependencies opening_arguments ## statement_writes body.
Proof.
  unfold restricted_access_boundary_check.
  rewrite Bool.andb_true_iff. intros [Harguments Hwrites].
  split.
  - now apply AccessLayout.arguments_eqb_sound.
  - now apply bool_decide_eq_true in Hwrites.
Qed.

(** Effect-only component of the restricted pass.  Structural admissibility
    remains the independent executable decision above. *)
Fixpoint restricted_access_effect_check {Γ} (statement : stmt Γ) : bool :=
  match statement with
  | TInvAccess _ _ body | TAtomic body => restricted_access_effect_check body
  | TGhostVal _ _ _ body => restricted_access_effect_check body
  | TIf _ then_branch else_branch | TGhostIf _ then_branch else_branch =>
      restricted_access_effect_check then_branch &&
        restricted_access_effect_check else_branch
  | TSeq first second =>
      match first, second with
      | TUnfold opening_invariant opening_arguments,
          TSeq body (TFold closing_invariant closing_arguments) =>
          match decide (opening_invariant = closing_invariant) with
          | left Heq =>
              restricted_access_boundary_check opening_arguments
                (eq_rect _ (fun invariant =>
                  gexpr_list Γ (Assertion.invariant_args invariant))
                  closing_arguments _ (eq_sym Heq)) body &&
                restricted_access_effect_check body
          | right _ => false
          end
      | TUnfold opening_invariant opening_arguments,
          TSeq body
            (TSeq (TFold closing_invariant closing_arguments) work) =>
          match decide (opening_invariant = closing_invariant) with
          | left Heq =>
              restricted_access_boundary_check opening_arguments
                (eq_rect _ (fun invariant =>
                  gexpr_list Γ (Assertion.invariant_args invariant))
                  closing_arguments _ (eq_sym Heq)) body &&
                restricted_access_effect_check body &&
                restricted_access_effect_check work
          | right _ => false
          end
      | TUnfold invariant arguments,
          TSeq prefix (TIf _ then_branch else_branch)
      | TUnfold invariant arguments,
          TSeq prefix (TGhostIf _ then_branch else_branch) =>
          match then_branch, else_branch with
          | TSeq then_prefix (TSeq _ then_continuation),
              TSeq else_prefix (TSeq _ else_continuation) =>
              conditional_access_stableb invariant arguments prefix then_prefix
                else_prefix &&
              restricted_access_effect_check prefix &&
              restricted_access_effect_check then_prefix &&
              restricted_access_effect_check else_prefix &&
              restricted_access_effect_check then_continuation &&
              restricted_access_effect_check else_continuation
          | _, _ => false
          end
      | _, _ =>
          restricted_access_effect_check first &&
            restricted_access_effect_check second
      end
  | _ => true
  end.

Definition restricted_fragment_check {Γ} (statement : stmt Γ) : bool :=
  restricted_fragment_shape_check false statement &&
    restricted_access_effect_check statement.

Definition restricted_fragment_accepted {Γ} (statement : stmt Γ) : Prop :=
  restricted_fragment_check statement = true.

Fixpoint normalization_statement_size {Γ} (statement : stmt Γ) : nat :=
  match statement with
  | TInvAccess _ _ body | TAtomic body =>
      S (normalization_statement_size body)
  | TGhostVal _ _ _ body => S (normalization_statement_size body)
  | TIf _ then_branch else_branch | TGhostIf _ then_branch else_branch
  | TSeq then_branch else_branch =>
      S (normalization_statement_size then_branch +
        normalization_statement_size else_branch)
  | _ => 1
  end.

(** The worker's step for a canonical conditional access: distribute when
    the prefix is proof-only, factor otherwise. *)
Definition restricted_normalize_conditional_access {Γ}
    (normalize : stmt Γ -> option (stmt Γ)) invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_closing then_continuation
      else_prefix else_closing else_continuation : stmt Γ) : option (stmt Γ) :=
  if AccessLayout.fold_is invariant arguments then_closing &&
      AccessLayout.fold_is invariant arguments else_closing &&
      conditional_access_stableb invariant arguments prefix then_prefix
        else_prefix
  then
    match normalize prefix, normalize then_prefix, normalize else_prefix,
        normalize then_continuation, normalize else_continuation with
    | Some prefix', Some then_prefix', Some else_prefix',
        Some then_continuation', Some else_continuation' =>
        Some ((if proof_onlyb prefix then distributed_access else factored_access)
          invariant arguments prefix' guard then_prefix' then_continuation'
          else_prefix' else_continuation')
    | _, _, _, _, _ => None
    end
  else None.

(** Proof-irrelevant source-to-source worker.  Its private budget is only a
    termination device for the nested [AccessThen] continuation and never
    appears in an analysis certificate or theorem interface. *)
Fixpoint restricted_normalize_statement_fuel {Γ} (fuel : nat)
    (statement : stmt Γ) : option (stmt Γ) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match statement with
      | TUnfold _ _ => None
      | TInvAccess invariant arguments body =>
          match restricted_normalize_statement_fuel fuel' body with
          | Some normalized_body =>
              Some (TInvAccess invariant arguments normalized_body)
          | None => None
          end
      | TAtomic body =>
          match restricted_normalize_statement_fuel fuel' body with
          | Some normalized_body => Some (TAtomic normalized_body)
          | None => None
          end
      | TGhostVal name t initializer body =>
          match restricted_normalize_statement_fuel fuel' body with
          | Some normalized_body =>
              Some (TGhostVal name t initializer normalized_body)
          | None => None
          end
      | TIf condition then_branch else_branch =>
          match restricted_normalize_statement_fuel fuel' then_branch,
              restricted_normalize_statement_fuel fuel' else_branch with
          | Some normalized_then, Some normalized_else =>
              Some (TIf condition normalized_then normalized_else)
          | _, _ => None
          end
      | TGhostIf condition then_branch else_branch =>
          match restricted_normalize_statement_fuel fuel' then_branch,
              restricted_normalize_statement_fuel fuel' else_branch with
          | Some normalized_then, Some normalized_else =>
              Some (TGhostIf condition normalized_then normalized_else)
          | _, _ => None
          end
      | TSeq first second =>
          match first, second with
          | TUnfold opening_invariant opening_arguments,
              TSeq body (TFold closing_invariant closing_arguments) =>
              match decide (opening_invariant = closing_invariant) with
              | left Heq =>
                  if restricted_access_boundary_check opening_arguments
                    (eq_rect _ (fun invariant =>
                      gexpr_list Γ (Assertion.invariant_args invariant))
                      closing_arguments _ (eq_sym Heq)) body
                  then
                    match restricted_normalize_statement_fuel fuel' body with
                    | Some normalized_body =>
                        Some (TInvAccess opening_invariant opening_arguments
                          normalized_body)
                    | None => None
                    end
                  else None
              | right _ => None
              end
          | TUnfold opening_invariant opening_arguments,
              TSeq body
                (TSeq (TFold closing_invariant closing_arguments) work) =>
              match decide (opening_invariant = closing_invariant) with
              | left Heq =>
                  if restricted_access_boundary_check opening_arguments
                    (eq_rect _ (fun invariant =>
                      gexpr_list Γ (Assertion.invariant_args invariant))
                      closing_arguments _ (eq_sym Heq)) body
                  then
                    match restricted_normalize_statement_fuel fuel' body,
                        restricted_normalize_statement_fuel fuel' work with
                    | Some normalized_body, Some normalized_work =>
                        Some (TSeq
                          (TInvAccess opening_invariant opening_arguments
                            normalized_body)
                          normalized_work)
                    | _, _ => None
                    end
                  else None
              | right _ => None
              end
          | TUnfold invariant arguments,
              TSeq prefix (TIf condition then_branch else_branch) =>
              match then_branch, else_branch with
              | TSeq then_prefix (TSeq then_closing then_continuation),
                  TSeq else_prefix (TSeq else_closing else_continuation) =>
                  restricted_normalize_conditional_access
                    (restricted_normalize_statement_fuel fuel') invariant
                    arguments prefix (GuardRuntime condition) then_prefix
                    then_closing then_continuation else_prefix else_closing
                    else_continuation
              | _, _ => None
              end
          | TUnfold invariant arguments,
              TSeq prefix (TGhostIf condition then_branch else_branch) =>
              match then_branch, else_branch with
              | TSeq then_prefix (TSeq then_closing then_continuation),
                  TSeq else_prefix (TSeq else_closing else_continuation) =>
                  restricted_normalize_conditional_access
                    (restricted_normalize_statement_fuel fuel') invariant
                    arguments prefix (GuardGhost condition) then_prefix
                    then_closing then_continuation else_prefix else_closing
                    else_continuation
              | _, _ => None
              end
          | _, _ =>
              match restricted_normalize_statement_fuel fuel' first,
                  restricted_normalize_statement_fuel fuel' second with
              | Some normalized_first, Some normalized_second =>
                  Some (TSeq normalized_first normalized_second)
              | _, _ => None
              end
          end
      | _ => Some statement
      end
  end.

Definition restricted_analyze_and_normalize {Γ}
    (statement : stmt Γ) : option (stmt Γ) :=
  if restricted_fragment_check statement
  then restricted_normalize_statement_fuel
    (S (normalization_statement_size statement)) statement
  else None.

Lemma unfold_freeb_spec {Γ} (statement : stmt Γ) :
  unfold_freeb statement = true <-> unfold_free statement.
Proof.
  induction statement; cbn;
    rewrite ?Bool.andb_true_iff, ?IHstatement, ?IHstatement1, ?IHstatement2;
    intuition congruence.
Qed.

Lemma access_neutralb_spec {Γ} (statement : stmt Γ) :
  access_neutralb statement = true <-> access_neutral statement.
Proof.
  induction statement; cbn;
    rewrite ?Bool.andb_true_iff, ?IHstatement, ?IHstatement1, ?IHstatement2;
    intuition congruence.
Qed.

Lemma restricted_fragment_check_refines_shape {Γ} (statement : stmt Γ) :
  restricted_fragment_accepted statement -> restricted_fragment_shape statement.
Proof.
  unfold restricted_fragment_accepted, restricted_fragment_check,
    restricted_fragment_shape.
  rewrite Bool.andb_true_iff. tauto.
Qed.

Lemma conditional_access_shapeb_closings {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_closing then_continuation
      else_prefix else_closing else_continuation : stmt Γ) :
  conditional_access_shapeb invariant arguments prefix guard then_prefix
    then_closing then_continuation else_prefix else_closing else_continuation =
    true ->
  then_closing = TFold invariant arguments /\
  else_closing = TFold invariant arguments.
Proof.
  unfold conditional_access_shapeb. intros Hshape.
  repeat apply andb_prop in Hshape as [Hshape ?].
  split; apply AccessLayout.fold_is_sound; assumption.
Qed.

Lemma conditional_access_baseline {Γ} nested invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ) :
  conditional_access_shapeb invariant arguments prefix guard then_prefix
    (TFold invariant arguments) then_continuation else_prefix
    (TFold invariant arguments) else_continuation = true ->
  conditional_access_stableb invariant arguments prefix then_prefix
    else_prefix = true ->
  baseline_normalizable true prefix ->
  baseline_normalizable true then_prefix ->
  baseline_normalizable true else_prefix ->
  baseline_normalizable nested then_continuation ->
  baseline_normalizable nested else_continuation ->
  baseline_normalizable nested
    (conditional_access invariant arguments prefix guard then_prefix
      then_continuation else_prefix else_continuation).
Proof.
  unfold conditional_access_shapeb, conditional_access_stableb.
  intros Hshape Hstable Hprefix Hthen_prefix Helse_prefix Hthen Helse.
  apply andb_prop in Hstable as [Hthen_stable Helse_stable].
  apply bool_decide_eq_true in Hthen_stable, Helse_stable.
  apply andb_prop in Hshape as [Hshape Hproof].
  apply andb_prop in Hshape as [Hfold _].
  destruct (proof_onlyb prefix) eqn:Hprefix_proof.
  - apply BaselineDistributedAccess; assumption.
  - repeat apply andb_prop in Hproof as [Hproof ?].
    apply access_neutralb_spec in Hproof.
    match goal with H : access_neutralb else_prefix = true |- _ =>
      apply access_neutralb_spec in H end.
    apply BaselineFactoredAccess; assumption.
Qed.

Lemma access_neutralb_unfold_freeb {Γ} (statement : stmt Γ) :
  access_neutralb statement = true -> unfold_freeb statement = true.
Proof.
  induction statement; cbn; intros H; try discriminate; try reflexivity;
    rewrite ?Bool.andb_true_iff in *; intuition.
Qed.

Lemma shape_sequence_unfold_free {Γ} nested (first second : stmt Γ) :
  unfold_freeb first = true ->
  restricted_fragment_shape_check nested (TSeq first second) =
    restricted_fragment_shape_check nested first &&
    restricted_fragment_shape_check nested second.
Proof. destruct first; cbn; try discriminate; reflexivity. Qed.

Lemma shape_sequence_split {Γ} nested (first second : stmt Γ) :
  (forall invariant arguments, first <> TUnfold invariant arguments) ->
  restricted_fragment_shape_check nested (TSeq first second) =
    restricted_fragment_shape_check nested first &&
    restricted_fragment_shape_check nested second.
Proof.
  intros Hfirst. destruct first; try reflexivity.
  exfalso. eapply Hfirst. reflexivity.
Qed.

Lemma effect_sequence_split {Γ} (first second : stmt Γ) :
  (forall invariant arguments, first <> TUnfold invariant arguments) ->
  restricted_access_effect_check (TSeq first second) =
    restricted_access_effect_check first &&
    restricted_access_effect_check second.
Proof.
  intros Hfirst. destruct first; try reflexivity.
  exfalso. eapply Hfirst. reflexivity.
Qed.

(** Unfold-free statements accepted in a nested position contain no fold. *)
Lemma nested_shape_unfold_free_neutral {Γ} (statement : stmt Γ) :
  unfold_freeb statement = true ->
  restricted_fragment_shape_check true statement = true ->
  access_neutral statement.
Proof.
  induction statement; intros Hfree Hshape; cbn in Hfree |- *;
    try exact I; try discriminate.
  - cbn in Hshape. apply access_neutralb_spec. exact Hshape.
  - cbn in Hshape. rewrite Bool.andb_true_iff in Hfree, Hshape. intuition.
  - apply andb_prop in Hfree as [Hfirst Hsecond].
    rewrite shape_sequence_unfold_free in Hshape by exact Hfirst.
    apply andb_prop in Hshape as [? ?]. split; auto.
  - cbn in Hshape. apply access_neutralb_spec. exact Hshape.
  - cbn in Hshape. auto.
  - cbn in Hshape. rewrite Bool.andb_true_iff in Hfree, Hshape. intuition.
Qed.

Lemma restricted_unfold_head_shape_sound {Γ} nested invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (second : stmt Γ) :
  (forall nested' (smaller : stmt Γ),
    normalization_statement_size smaller <
      normalization_statement_size (TSeq (TUnfold invariant arguments) second) ->
    restricted_fragment_shape_check nested' smaller = true ->
    restricted_access_effect_check smaller = true ->
    baseline_normalizable nested' smaller) ->
  restricted_fragment_shape_check nested
    (TSeq (TUnfold invariant arguments) second) = true ->
  restricted_access_effect_check (TSeq (TUnfold invariant arguments) second) =
    true ->
  baseline_normalizable nested (TSeq (TUnfold invariant arguments) second).
Proof.
  intros IH Hcheck Heffects.
  destruct second as [| | | | | | | | | | | | | | | current2_1 current2_2 | | |];
    cbn in Hcheck; try discriminate.
  destruct current2_2; cbn in Hcheck; try discriminate.
  - apply Bool.andb_true_iff in Hcheck as [Hinvariant Hbody];
      apply bool_decide_eq_true in Hinvariant. subst invariant0.
    cbn in Heffects.
    destruct (decide (invariant = invariant) : Decision (invariant = invariant))
      as [Heq|Hneq]; last contradiction.
    replace Heq with (@eq_refl inv_id invariant) in Heffects
      by apply ProofIrrelevance.proof_irrelevance.
    cbn in Heffects.
    apply Bool.andb_true_iff in Heffects as [Hboundary Hbody_effects].
    apply restricted_access_boundary_check_sound in Hboundary as
      [Harguments Hdisjoint].
    apply BaselineTerminalAccess; [| exact Harguments | exact Hdisjoint].
    apply IH; [cbn; lia | exact Hbody | exact Hbody_effects].
  - destruct current2_2_1; cbn in Hcheck; try discriminate.
    destruct current2_2_1_2; cbn in Hcheck; try discriminate.
    destruct current2_2_2; cbn in Hcheck; try discriminate.
    destruct current2_2_2_2; cbn in Hcheck; try discriminate.
    cbn in Heffects.
    do 5 (apply andb_prop in Hcheck as [Hcheck ?]).
    do 5 (apply andb_prop in Heffects as [Heffects ?]).
    destruct (conditional_access_shapeb_closings _ _ _ _ _ _ _ _ _ _ Hcheck)
      as [-> ->].
    change (baseline_normalizable nested (conditional_access invariant arguments
      current2_1 (GuardRuntime condition) current2_2_1_1 current2_2_1_2_2
      current2_2_2_1 current2_2_2_2_2)).
    apply conditional_access_baseline; [exact Hcheck | exact Heffects | ..];
      (apply IH; [cbn; lia | assumption | assumption]).
  - destruct current2_2_1; cbn in Hcheck; try discriminate.
    apply Bool.andb_true_iff in Hcheck as [Hprefix Hwork].
    apply Bool.andb_true_iff in Hprefix as [Hinvariant Hbody].
    apply bool_decide_eq_true in Hinvariant. subst invariant0.
    cbn in Heffects.
    destruct (decide (invariant = invariant) : Decision (invariant = invariant))
      as [Heq|Hneq]; last contradiction.
    replace Heq with (@eq_refl inv_id invariant) in Heffects
      by apply ProofIrrelevance.proof_irrelevance.
    cbn in Heffects.
    apply Bool.andb_true_iff in Heffects as [Heffects Hwork_effects].
    apply Bool.andb_true_iff in Heffects as [Hboundary Hbody_effects].
    apply restricted_access_boundary_check_sound in Hboundary as
      [Harguments Hdisjoint].
    apply BaselineAccessThen; [| exact Harguments | exact Hdisjoint |].
    + apply IH; [cbn; lia | exact Hbody | exact Hbody_effects].
    + apply IH; [cbn; lia | exact Hwork | exact Hwork_effects].
  - destruct current2_2_1; cbn in Hcheck; try discriminate.
    destruct current2_2_1_2; cbn in Hcheck; try discriminate.
    destruct current2_2_2; cbn in Hcheck; try discriminate.
    destruct current2_2_2_2; cbn in Hcheck; try discriminate.
    cbn in Heffects.
    do 5 (apply andb_prop in Hcheck as [Hcheck ?]).
    do 5 (apply andb_prop in Heffects as [Heffects ?]).
    destruct (conditional_access_shapeb_closings _ _ _ _ _ _ _ _ _ _ Hcheck)
      as [-> ->].
    change (baseline_normalizable nested (conditional_access invariant arguments
      current2_1 (GuardGhost condition) current2_2_1_1 current2_2_1_2_2
      current2_2_2_1 current2_2_2_2_2)).
    apply conditional_access_baseline; [exact Hcheck | exact Heffects | ..];
      (apply IH; [cbn; lia | assumption | assumption]).
Qed.

(** The executable shape check is sound for the proof-producing baseline
    grammar.  Strengthening it with effects can only reject programs; it
    cannot admit a source layout unsupported by the normalization
    theorem. *)
Lemma restricted_fragment_shape_check_sound_at {Γ} nested
    (statement : stmt Γ) :
  restricted_fragment_shape_check nested statement = true ->
  restricted_access_effect_check statement = true ->
  baseline_normalizable nested statement.
Proof.
  enough (Hsized : forall n Γ nested (current : stmt Γ),
    normalization_statement_size current < n ->
    restricted_fragment_shape_check nested current = true ->
    restricted_access_effect_check current = true ->
    baseline_normalizable nested current) by eauto.
  intros n. induction n as [|n IHn];
    intros Γ' nested' current Hsize Hcheck Heffects; [lia|].
  assert (IH : forall Γ'' nested'' (smaller : stmt Γ''),
    normalization_statement_size smaller <
      normalization_statement_size current ->
    restricted_fragment_shape_check nested'' smaller = true ->
    restricted_access_effect_check smaller = true ->
    baseline_normalizable nested'' smaller).
  { intros Γ'' nested'' smaller Hsmaller. apply IHn. lia. }
  clear IHn Hsize.
  destruct (unfold_freeb current) eqn:Hfree.
  { apply BaselineUnfoldFree. destruct nested'.
    - apply nested_shape_unfold_free_neutral; assumption.
    - apply unfold_freeb_spec. exact Hfree. }
  destruct current; cbn in Hfree; try discriminate.
  - cbn in Hcheck. destruct nested'.
    + apply access_neutralb_unfold_freeb in Hcheck. congruence.
    + congruence.
  - cbn in Hcheck, Heffects.
    apply andb_prop in Hcheck as [Hthen Helse].
    apply andb_prop in Heffects as [Hthen_effects Helse_effects].
    apply BaselineConditional; (apply IH; [cbn; lia | assumption | assumption]).
  - destruct current1.
    all: try (rewrite shape_sequence_split in Hcheck
        by (intros ? ? ?; discriminate);
      rewrite effect_sequence_split in Heffects
        by (intros ? ? ?; discriminate);
      apply andb_prop in Hcheck as [Hfirst Hsecond];
      apply andb_prop in Heffects as [Hfirst_effects Hsecond_effects];
      apply BaselineBalancedSequence;
        (apply IH; [cbn; lia | assumption | assumption])).
    apply restricted_unfold_head_shape_sound; [| exact Hcheck | exact Heffects].
    intros nested'' smaller Hsmaller. apply IH. exact Hsmaller.
  - cbn in Hcheck. destruct nested'.
    + apply access_neutralb_unfold_freeb in Hcheck. congruence.
    + congruence.
  - cbn in Hcheck, Heffects. apply BaselineGhostVal.
    apply IH; [cbn; lia | assumption | assumption].
  - cbn in Hcheck, Heffects.
    apply andb_prop in Hcheck as [Hthen Helse].
    apply andb_prop in Heffects as [Hthen_effects Helse_effects].
    apply BaselineGhostConditional;
      (apply IH; [cbn; lia | assumption | assumption]).
Qed.

Lemma restricted_fragment_shape_check_sound {Γ} (statement : stmt Γ) :
  restricted_fragment_shape statement ->
  restricted_access_effect_check statement = true ->
  baseline_normalizable false statement.
Proof. apply restricted_fragment_shape_check_sound_at. Qed.

Corollary restricted_fragment_check_sound {Γ} (statement : stmt Γ) :
  restricted_fragment_accepted statement -> baseline_normalizable false statement.
Proof.
  intro Haccepted.
  unfold restricted_fragment_accepted, restricted_fragment_check in Haccepted.
  apply Bool.andb_true_iff in Haccepted as [Hshape Heffects].
  eapply restricted_fragment_shape_check_sound; eauto.
Qed.

Lemma restricted_access_neutral_unfold_free {Γ} (statement : stmt Γ) :
  access_neutral statement -> unfold_free statement.
Proof.
  induction statement; cbn; intuition.
Qed.

Lemma unfold_free_normalize_statement_succeeds_with_fuel {Γ}
    (statement : stmt Γ) fuel :
  unfold_free statement ->
  normalization_statement_size statement < fuel ->
  exists normalized,
    restricted_normalize_statement_fuel fuel statement = Some normalized.
Proof.
  revert fuel.
  induction statement; intros fuel Hfree Hfuel.
  all: destruct fuel as [|fuel].
  all: try (cbn in Hfuel; lia).
  all: cbn [unfold_free normalization_statement_size
    restricted_normalize_statement_fuel] in Hfree, Hfuel |- *.
  all: try contradiction.
  all: try (eexists; reflexivity).
  - destruct (IHstatement fuel Hfree ltac:(lia)) as
      [normalized Hnormalized].
    rewrite Hnormalized. eexists; reflexivity.
  - destruct Hfree as [Hfree1 Hfree2].
    destruct (IHstatement1 fuel Hfree1 ltac:(lia)) as
      [normalized1 Hnormalized1].
    destruct (IHstatement2 fuel Hfree2 ltac:(lia)) as
      [normalized2 Hnormalized2].
    rewrite Hnormalized1, Hnormalized2. eexists; reflexivity.
  - destruct Hfree as [Hfree1 Hfree2].
    destruct (IHstatement1 fuel Hfree1 ltac:(lia)) as
      [normalized1 Hnormalized1].
    destruct (IHstatement2 fuel Hfree2 ltac:(lia)) as
      [normalized2 Hnormalized2].
    destruct statement1; cbn [unfold_free] in Hfree1;
      try contradiction;
      cbn [restricted_normalize_statement_fuel] in Hnormalized1 |- *;
      rewrite Hnormalized1, Hnormalized2;
      eexists; reflexivity.
  - destruct (IHstatement fuel Hfree ltac:(lia)) as
      [normalized Hnormalized].
    rewrite Hnormalized. eexists; reflexivity.
  - destruct (IHstatement fuel Hfree ltac:(lia)) as
      [normalized Hnormalized].
    rewrite Hnormalized. eexists; reflexivity.
  - destruct Hfree as [Hfree1 Hfree2].
    destruct (IHstatement1 fuel Hfree1 ltac:(lia)) as
      [normalized1 Hnormalized1].
    destruct (IHstatement2 fuel Hfree2 ltac:(lia)) as
      [normalized2 Hnormalized2].
    rewrite Hnormalized1, Hnormalized2. eexists; reflexivity.
Qed.

Corollary unfold_free_normalize_statement_succeeds {Γ}
    (statement : stmt Γ) :
  unfold_free statement ->
  exists normalized,
    restricted_normalize_statement_fuel
      (S (normalization_statement_size statement)) statement =
      Some normalized.
Proof.
  intro Hfree.
  eapply unfold_free_normalize_statement_succeeds_with_fuel; [exact Hfree|lia].
Qed.

Lemma unfold_free_normalize_statement_identity {Γ} (statement : stmt Γ)
    fuel normalized :
  unfold_free statement ->
  restricted_normalize_statement_fuel fuel statement = Some normalized ->
  normalized = statement.
Proof.
  revert fuel normalized.
  induction statement; intros fuel normalized Hfree Hworker;
    destruct fuel; cbn [unfold_free restricted_normalize_statement_fuel]
      in Hfree, Hworker; try contradiction; try congruence.
  - destruct (restricted_normalize_statement_fuel fuel statement) eqn:Hbody;
      try discriminate.
    inversion Hworker; subst. f_equal. eapply IHstatement; eauto.
  - destruct Hfree as [Hthen Helse].
    destruct (restricted_normalize_statement_fuel fuel statement1)
      eqn:Hworker1; try discriminate.
    destruct (restricted_normalize_statement_fuel fuel statement2)
      eqn:Hworker2; try discriminate.
    inversion Hworker; subst. f_equal; eauto.
  - destruct Hfree as [Hfirst Hsecond].
    remember (restricted_normalize_statement_fuel fuel statement1)
      as first_result eqn:Hfirst_result.
    remember (restricted_normalize_statement_fuel fuel statement2)
      as second_result eqn:Hsecond_result.
    destruct statement1; cbn [unfold_free] in Hfirst; try contradiction;
      cbn [restricted_normalize_statement_fuel] in Hworker.
    all: destruct first_result; try discriminate;
      destruct second_result; try discriminate;
      inversion Hworker; subst; f_equal;
      eauto using eq_sym.
  - destruct (restricted_normalize_statement_fuel fuel statement) eqn:Hbody;
      try discriminate.
    inversion Hworker; subst. f_equal. eapply IHstatement; eauto.
  - destruct (restricted_normalize_statement_fuel fuel statement) eqn:Hbody;
      try discriminate.
    injection Hworker as <-. f_equal. eapply IHstatement; eauto.
  - destruct Hfree as [Hthen Helse].
    destruct (restricted_normalize_statement_fuel fuel statement1)
      eqn:Hworker1; try discriminate.
    destruct (restricted_normalize_statement_fuel fuel statement2)
      eqn:Hworker2; try discriminate.
    inversion Hworker; subst. f_equal; eauto.
Qed.

Lemma restricted_normalize_terminal_access {Γ} fuel
    invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (body normalized_body : stmt Γ) :
  restricted_access_boundary_check arguments arguments body = true ->
  restricted_normalize_statement_fuel fuel body = Some normalized_body ->
  restricted_normalize_statement_fuel (S fuel)
    (TSeq (TUnfold invariant arguments)
      (TSeq body (TFold invariant arguments))) =
    Some (TInvAccess invariant arguments normalized_body).
Proof.
  intros Hboundary Hbody. cbn [restricted_normalize_statement_fuel].
  destruct (decide (invariant = invariant)) as [Heq | Hneq];
    [| contradiction].
  replace Heq with (@eq_refl inv_id invariant) by apply ProofIrrelevance.proof_irrelevance.
  cbn. now rewrite Hboundary, Hbody.
Qed.

Lemma restricted_normalize_continued_access {Γ} fuel
    invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (body work normalized_body normalized_work : stmt Γ) :
  restricted_access_boundary_check arguments arguments body = true ->
  restricted_normalize_statement_fuel fuel body = Some normalized_body ->
  restricted_normalize_statement_fuel fuel work = Some normalized_work ->
  restricted_normalize_statement_fuel (S fuel)
    (TSeq (TUnfold invariant arguments)
      (TSeq body
        (TSeq (TFold invariant arguments)
          work))) =
    Some (TSeq (TInvAccess invariant arguments normalized_body)
      normalized_work).
Proof.
  intros Hboundary Hbody Hwork. cbn [restricted_normalize_statement_fuel].
  destruct (decide (invariant = invariant)) as [Heq | Hneq];
    [| contradiction].
  replace Heq with (@eq_refl inv_id invariant) by apply ProofIrrelevance.proof_irrelevance.
  cbn. now rewrite Hboundary, Hbody, Hwork.
Qed.

Lemma restricted_normalize_conditional_access_inv {Γ}
    (normalize : stmt Γ -> option (stmt Γ)) invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_closing then_continuation
      else_prefix else_closing else_continuation normalized : stmt Γ) :
  restricted_normalize_conditional_access normalize invariant arguments prefix
    guard then_prefix then_closing then_continuation else_prefix else_closing
    else_continuation = Some normalized ->
  exists prefix' then_prefix' else_prefix' then_continuation'
      else_continuation',
    normalize prefix = Some prefix' /\
    normalize then_prefix = Some then_prefix' /\
    normalize else_prefix = Some else_prefix' /\
    normalize then_continuation = Some then_continuation' /\
    normalize else_continuation = Some else_continuation' /\
    then_closing = TFold invariant arguments /\
    else_closing = TFold invariant arguments /\
    conditional_access_stableb invariant arguments prefix then_prefix
      else_prefix = true /\
    normalized =
      (if proof_onlyb prefix then distributed_access else factored_access)
        invariant arguments prefix' guard then_prefix' then_continuation'
        else_prefix' else_continuation'.
Proof.
  unfold restricted_normalize_conditional_access.
  destruct (AccessLayout.fold_is invariant arguments then_closing) eqn:Hthen;
    [|discriminate].
  destruct (AccessLayout.fold_is invariant arguments else_closing) eqn:Helse;
    [|discriminate].
  destruct (conditional_access_stableb invariant arguments prefix then_prefix
    else_prefix) eqn:Hstable; [|discriminate].
  cbn.
  destruct (normalize prefix) as [prefix'|] eqn:Hq; [|discriminate].
  destruct (normalize then_prefix) as [then_prefix'|] eqn:Htp; [|discriminate].
  destruct (normalize else_prefix) as [else_prefix'|] eqn:Hep; [|discriminate].
  destruct (normalize then_continuation) as [then_continuation'|] eqn:Htc;
    [|discriminate].
  destruct (normalize else_continuation) as [else_continuation'|] eqn:Hec;
    [|discriminate].
  intros Hworker. injection Hworker as <-.
  exists prefix', then_prefix', else_prefix', then_continuation',
    else_continuation'.
  repeat split; auto using AccessLayout.fold_is_sound.
Qed.

Lemma restricted_normalize_conditional_access_step {Γ} fuel invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ) :
  restricted_normalize_statement_fuel (S fuel)
    (conditional_access invariant arguments prefix guard then_prefix
      then_continuation else_prefix else_continuation) =
  restricted_normalize_conditional_access
    (restricted_normalize_statement_fuel fuel) invariant arguments prefix guard
    then_prefix (TFold invariant arguments) then_continuation else_prefix
    (TFold invariant arguments) else_continuation.
Proof. destruct guard; reflexivity. Qed.

Lemma restricted_normalize_conditional_access_succeeds {Γ}
    (normalize : stmt Γ -> option (stmt Γ)) invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation
      prefix' then_prefix' else_prefix' then_continuation'
      else_continuation' : stmt Γ) :
  conditional_access_shapeb invariant arguments prefix guard then_prefix
    (TFold invariant arguments) then_continuation else_prefix
    (TFold invariant arguments) else_continuation = true ->
  conditional_access_stableb invariant arguments prefix then_prefix
    else_prefix = true ->
  normalize prefix = Some prefix' ->
  normalize then_prefix = Some then_prefix' ->
  normalize else_prefix = Some else_prefix' ->
  normalize then_continuation = Some then_continuation' ->
  normalize else_continuation = Some else_continuation' ->
  restricted_normalize_conditional_access normalize invariant arguments prefix
    guard then_prefix (TFold invariant arguments) then_continuation else_prefix
    (TFold invariant arguments) else_continuation =
  Some ((if proof_onlyb prefix then distributed_access else factored_access)
    invariant arguments prefix' guard then_prefix' then_continuation'
    else_prefix' else_continuation').
Proof.
  unfold conditional_access_shapeb, restricted_normalize_conditional_access.
  intros Hshape Hstable Hq Htp Hep Htc Hec.
  apply andb_prop in Hshape as [Hshape _].
  apply andb_prop in Hshape as [Hthen Helse].
  rewrite Hthen, Hstable. cbn. rewrite Hq, Htp, Hep, Htc, Hec.
  reflexivity.
Qed.

Lemma conditional_access_target_proof_only {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation
      prefix' then_prefix' else_prefix' then_continuation'
      else_continuation' : stmt Γ) :
  proof_onlyb prefix' = proof_onlyb prefix ->
  proof_onlyb then_prefix' = proof_onlyb then_prefix ->
  proof_onlyb else_prefix' = proof_onlyb else_prefix ->
  proof_onlyb then_continuation' = proof_onlyb then_continuation ->
  proof_onlyb else_continuation' = proof_onlyb else_continuation ->
  proof_onlyb
    ((if proof_onlyb prefix then distributed_access else factored_access)
      invariant arguments prefix' guard then_prefix' then_continuation'
      else_prefix' else_continuation') =
  proof_onlyb
    (conditional_access invariant arguments prefix guard then_prefix
      then_continuation else_prefix else_continuation).
Proof.
  intros Hq Htp Hep Hthen Helse.
  destruct guard, (proof_onlyb prefix) eqn:Hprefix;
    cbn [distributed_access factored_access conditional_access guard_if
      canonical_branch proof_onlyb];
    rewrite Hq, Htp, Hep, Hthen, Helse, ?Hprefix;
    destruct (proof_onlyb then_prefix), (proof_onlyb else_prefix),
      (proof_onlyb then_continuation), (proof_onlyb else_continuation);
    reflexivity.
Qed.

Lemma conditional_access_target_writes {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation
      prefix' then_prefix' else_prefix' then_continuation'
      else_continuation' : stmt Γ) :
  statement_writes prefix' = statement_writes prefix ->
  statement_writes then_prefix' = statement_writes then_prefix ->
  statement_writes else_prefix' = statement_writes else_prefix ->
  statement_writes then_continuation' = statement_writes then_continuation ->
  statement_writes else_continuation' = statement_writes else_continuation ->
  statement_writes
    ((if proof_onlyb prefix then distributed_access else factored_access)
      invariant arguments prefix' guard then_prefix' then_continuation'
      else_prefix' else_continuation') =
  statement_writes
    (conditional_access invariant arguments prefix guard then_prefix
      then_continuation else_prefix else_continuation).
Proof.
  intros Hq Htp Hep Hthen Helse.
  destruct guard, (proof_onlyb prefix);
    cbn [distributed_access factored_access conditional_access guard_if
      canonical_branch statement_writes];
    rewrite Hq, Htp, Hep, Hthen, Helse; set_solver.
Qed.

Lemma restricted_normalize_statement_proof_only {Γ} fuel
    (statement normalized : stmt Γ) :
  restricted_normalize_statement_fuel fuel statement = Some normalized ->
  proof_onlyb normalized = proof_onlyb statement.
Proof.
  revert Γ statement normalized. induction fuel as [|fuel IH];
    intros Γ statement normalized Hworker; [discriminate|].
  destruct statement; cbn [restricted_normalize_statement_fuel] in Hworker;
    try (injection Hworker as <-; reflexivity); try discriminate.
  - destruct (restricted_normalize_statement_fuel fuel statement) eqn:Hbody;
      [|discriminate].
    injection Hworker as <-. cbn. exact (IH _ _ _ Hbody).
  - destruct (restricted_normalize_statement_fuel fuel statement1) eqn:Hthen;
      [|discriminate].
    destruct (restricted_normalize_statement_fuel fuel statement2) eqn:Helse;
      [|discriminate].
    injection Hworker as <-. cbn. rewrite (IH _ _ _ Hthen), (IH _ _ _ Helse).
    reflexivity.
  - destruct statement1;
      try (destruct (restricted_normalize_statement_fuel fuel _) eqn:Hfirst
             in Hworker; [|discriminate];
           destruct (restricted_normalize_statement_fuel fuel statement2)
             eqn:Hsecond; [|discriminate];
           injection Hworker as <-; cbn;
           rewrite (IH _ _ _ Hfirst), (IH _ _ _ Hsecond); reflexivity).
    assert (Hunfold : forall fuel', restricted_normalize_statement_fuel fuel'
      (TUnfold invariant arguments) = None) by (intros []; reflexivity).
    destruct statement2; try (rewrite Hunfold in Hworker; discriminate).
    destruct statement2_2; try (rewrite Hunfold in Hworker; discriminate).
    2, 4: destruct statement2_2_1; try discriminate;
      destruct statement2_2_1_2; try discriminate;
      destruct statement2_2_2; try discriminate;
      destruct statement2_2_2_2; try discriminate;
      destruct (restricted_normalize_conditional_access_inv _ _ _ _ _ _ _ _ _ _
        _ _ Hworker) as (prefix' & then_prefix' & else_prefix' &
          then_continuation' & else_continuation' & Hq & Htp & Hep & Hthen &
          Helse & -> & -> & _ & ->);
      match type of Hworker with
      | context [restricted_normalize_conditional_access _ _ _ _ ?guard] =>
          exact (conditional_access_target_proof_only invariant arguments statement2_1
            guard statement2_2_1_1 statement2_2_1_2_2
            statement2_2_2_1 statement2_2_2_2_2 _ _ _ _ _ (IH _ _ _ Hq)
            (IH _ _ _ Htp) (IH _ _ _ Hep) (IH _ _ _ Hthen) (IH _ _ _ Helse))
      end.
    + destruct (decide (invariant = invariant0)); [|discriminate].
      destruct (restricted_access_boundary_check _ _ _); [|discriminate].
      destruct (restricted_normalize_statement_fuel fuel statement2_1)
        eqn:Hbody; [|discriminate].
      injection Hworker as <-. cbn. rewrite (IH _ _ _ Hbody), Bool.andb_true_r. reflexivity.
    + destruct statement2_2_1; try (rewrite Hunfold in Hworker; discriminate).
      destruct (decide (invariant = invariant0)); [|discriminate].
      destruct (restricted_access_boundary_check _ _ _); [|discriminate].
      destruct (restricted_normalize_statement_fuel fuel statement2_1)
        eqn:Hbody; [|discriminate].
      destruct (restricted_normalize_statement_fuel fuel statement2_2_2)
        eqn:Hwork; [|discriminate].
      injection Hworker as <-. cbn. rewrite (IH _ _ _ Hbody), (IH _ _ _ Hwork). reflexivity.
  - destruct (restricted_normalize_statement_fuel fuel statement) eqn:Hbody;
      [|discriminate].
    injection Hworker as <-. reflexivity.
  - destruct (restricted_normalize_statement_fuel fuel statement) eqn:Hbody;
      [|discriminate].
    injection Hworker as <-. cbn. exact (IH _ _ _ Hbody).
  - destruct (restricted_normalize_statement_fuel fuel statement1) eqn:Hthen;
      [|discriminate].
    destruct (restricted_normalize_statement_fuel fuel statement2) eqn:Helse;
      [|discriminate].
    injection Hworker as <-. cbn. rewrite (IH _ _ _ Hthen), (IH _ _ _ Helse).
    reflexivity.
Qed.

(** The worker writes exactly the locals the source writes. *)
Lemma restricted_normalize_statement_writes {Γ} fuel
    (statement normalized : stmt Γ) :
  restricted_normalize_statement_fuel fuel statement = Some normalized ->
  statement_writes normalized = statement_writes statement.
Proof.
  revert Γ statement normalized. induction fuel as [|fuel IH];
    intros Γ statement normalized Hworker; [discriminate|].
  destruct statement; cbn [restricted_normalize_statement_fuel] in Hworker;
    try (injection Hworker as <-; reflexivity); try discriminate.
  - destruct (restricted_normalize_statement_fuel fuel statement) eqn:Hbody;
      [|discriminate].
    injection Hworker as <-. cbn. exact (IH _ _ _ Hbody).
  - destruct (restricted_normalize_statement_fuel fuel statement1) eqn:Hthen;
      [|discriminate].
    destruct (restricted_normalize_statement_fuel fuel statement2) eqn:Helse;
      [|discriminate].
    injection Hworker as <-. cbn. rewrite (IH _ _ _ Hthen), (IH _ _ _ Helse).
    reflexivity.
  - destruct statement1;
      try (destruct (restricted_normalize_statement_fuel fuel _) eqn:Hfirst
             in Hworker; [|discriminate];
           destruct (restricted_normalize_statement_fuel fuel statement2)
             eqn:Hsecond; [|discriminate];
           injection Hworker as <-; cbn;
           rewrite (IH _ _ _ Hfirst), (IH _ _ _ Hsecond); reflexivity).
    assert (Hunfold : forall fuel', restricted_normalize_statement_fuel fuel'
      (TUnfold invariant arguments) = None) by (intros []; reflexivity).
    destruct statement2; try (rewrite Hunfold in Hworker; discriminate).
    destruct statement2_2; try (rewrite Hunfold in Hworker; discriminate).
    2, 4: destruct statement2_2_1; try discriminate;
      destruct statement2_2_1_2; try discriminate;
      destruct statement2_2_2; try discriminate;
      destruct statement2_2_2_2; try discriminate;
      destruct (restricted_normalize_conditional_access_inv _ _ _ _ _ _ _ _ _ _
        _ _ Hworker) as (prefix' & then_prefix' & else_prefix' &
          then_continuation' & else_continuation' & Hq & Htp & Hep & Hthen &
          Helse & -> & -> & _ & ->);
      match type of Hworker with
      | context [restricted_normalize_conditional_access _ _ _ _ ?guard] =>
          exact (conditional_access_target_writes invariant arguments statement2_1
            guard statement2_2_1_1 statement2_2_1_2_2
            statement2_2_2_1 statement2_2_2_2_2 _ _ _ _ _ (IH _ _ _ Hq)
            (IH _ _ _ Htp) (IH _ _ _ Hep) (IH _ _ _ Hthen) (IH _ _ _ Helse))
      end.
    + destruct (decide (invariant = invariant0)); [|discriminate].
      destruct (restricted_access_boundary_check _ _ _); [|discriminate].
      destruct (restricted_normalize_statement_fuel fuel statement2_1)
        eqn:Hbody; [|discriminate].
      injection Hworker as <-. cbn. rewrite (IH _ _ _ Hbody). set_solver.
    + destruct statement2_2_1; try (rewrite Hunfold in Hworker; discriminate).
      destruct (decide (invariant = invariant0)); [|discriminate].
      destruct (restricted_access_boundary_check _ _ _); [|discriminate].
      destruct (restricted_normalize_statement_fuel fuel statement2_1)
        eqn:Hbody; [|discriminate].
      destruct (restricted_normalize_statement_fuel fuel statement2_2_2)
        eqn:Hwork; [|discriminate].
      injection Hworker as <-. cbn. rewrite (IH _ _ _ Hbody), (IH _ _ _ Hwork). set_solver.
  - destruct (restricted_normalize_statement_fuel fuel statement) eqn:Hbody;
      [|discriminate].
    injection Hworker as <-. cbn. exact (IH _ _ _ Hbody).
  - destruct (restricted_normalize_statement_fuel fuel statement) eqn:Hbody;
      [|discriminate].
    injection Hworker as <-. cbn. rewrite (IH _ _ _ Hbody). reflexivity.
  - destruct (restricted_normalize_statement_fuel fuel statement1) eqn:Hthen;
      [|discriminate].
    destruct (restricted_normalize_statement_fuel fuel statement2) eqn:Helse;
      [|discriminate].
    injection Hworker as <-. cbn. rewrite (IH _ _ _ Hthen), (IH _ _ _ Helse).
    reflexivity.
Qed.

Lemma restricted_normalize_sequence_step {Γ} fuel (first second : stmt Γ) :
  (forall invariant arguments, first <> TUnfold invariant arguments) ->
  restricted_normalize_statement_fuel (S fuel) (TSeq first second) =
    match restricted_normalize_statement_fuel fuel first,
        restricted_normalize_statement_fuel fuel second with
    | Some normalized_first, Some normalized_second =>
        Some (TSeq normalized_first normalized_second)
    | _, _ => None
    end.
Proof.
  intros Hfirst. destruct first; try reflexivity.
  exfalso. eapply Hfirst. reflexivity.
Qed.

(** Successful admission is sufficient for the proof-irrelevant normalizer
    to produce a target at its private size bound. *)
Lemma restricted_normalize_statement_succeeds_at {Γ} nested
    (statement : stmt Γ) fuel :
  restricted_fragment_shape_check nested statement = true ->
  restricted_access_effect_check statement = true ->
  normalization_statement_size statement < fuel ->
  exists normalized,
    restricted_normalize_statement_fuel fuel statement = Some normalized.
Proof.
  revert fuel.
  enough (Hsized : forall n Γ nested (current : stmt Γ),
    normalization_statement_size current < n -> forall fuel,
    restricted_fragment_shape_check nested current = true ->
    restricted_access_effect_check current = true ->
    normalization_statement_size current < fuel ->
    exists normalized,
      restricted_normalize_statement_fuel fuel current = Some normalized)
    by eauto.
  intros n. induction n as [|n IHn];
    intros Γ' nested' current Hsize fuel Hshape Heffect Hfuel; [lia|].
  assert (IH : forall Γ'' nested'' (smaller : stmt Γ''),
    normalization_statement_size smaller <
      normalization_statement_size current -> forall fuel,
    restricted_fragment_shape_check nested'' smaller = true ->
    restricted_access_effect_check smaller = true ->
    normalization_statement_size smaller < fuel ->
    exists normalized,
      restricted_normalize_statement_fuel fuel smaller = Some normalized).
  { intros Γ'' nested'' smaller Hsmaller. apply IHn. lia. }
  clear IHn Hsize.
  destruct (unfold_freeb current) eqn:Hfree.
  { apply unfold_free_normalize_statement_succeeds_with_fuel;
      [apply unfold_freeb_spec; exact Hfree | exact Hfuel]. }
  destruct fuel as [|fuel]; [cbn in Hfuel; lia|].
  destruct current; cbn in Hfree; try discriminate.
  - cbn in Hshape. destruct nested'.
    + apply access_neutralb_unfold_freeb in Hshape. congruence.
    + congruence.
  - cbn in Hshape, Heffect, Hfuel.
    apply andb_prop in Hshape as [Hthen Helse].
    apply andb_prop in Heffect as [Hthen_effect Helse_effect].
    destruct (IH _ _ current1 ltac:(cbn; lia) fuel Hthen Hthen_effect
      ltac:(cbn in *; lia)) as [then' Hthen'].
    destruct (IH _ _ current2 ltac:(cbn; lia) fuel Helse Helse_effect
      ltac:(cbn in *; lia)) as [else' Helse'].
    cbn [restricted_normalize_statement_fuel]. rewrite Hthen', Helse'.
    eexists; reflexivity.
  - destruct current1.
    all: try (rewrite shape_sequence_split in Hshape
        by (intros ? ? ?; discriminate);
      rewrite effect_sequence_split in Heffect
        by (intros ? ? ?; discriminate);
      apply andb_prop in Hshape as [Hfirst Hsecond];
      apply andb_prop in Heffect as [Hfirst_effect Hsecond_effect];
      cbn in Hfuel;
      match goal with
      | |- context [restricted_normalize_statement_fuel _
            (TSeq ?first ?second)] =>
          destruct (IH _ _ first ltac:(cbn; lia) fuel Hfirst Hfirst_effect
            ltac:(cbn in *; lia)) as [first' Hfirst'];
          destruct (IH _ _ second ltac:(cbn; lia) fuel Hsecond Hsecond_effect
            ltac:(cbn in *; lia)) as [second' Hsecond']
      end;
      rewrite restricted_normalize_sequence_step
        by (intros ? ? ?; discriminate);
      rewrite Hfirst', Hsecond'; eexists; reflexivity).
    cbn in Hfuel.
    destruct current2; cbn in Hshape; try discriminate.
    destruct current2_2; cbn in Hshape; try discriminate.
    + (* terminal access *)
      apply andb_prop in Hshape as [Hinvariant Hbody].
      apply bool_decide_eq_true in Hinvariant. subst invariant0.
      cbn in Heffect.
      destruct (decide (invariant = invariant)) as [Heq | Hneq];
        [|contradiction].
      replace Heq with (@eq_refl inv_id invariant) in Heffect
        by apply ProofIrrelevance.proof_irrelevance.
      cbn in Heffect.
      apply andb_prop in Heffect as [Hboundary Hbody_effect].
      destruct (IH _ _ current2_1 ltac:(cbn; lia) fuel Hbody Hbody_effect
        ltac:(cbn in *; lia)) as [body' Hbody'].
      pose proof (restricted_access_boundary_check_sound _ _ _ Hboundary)
        as [Harguments _].
      subst.
      erewrite restricted_normalize_terminal_access; [eexists; reflexivity | |];
        eassumption.
    + (* runtime conditional access *)
      destruct current2_2_1; cbn in Hshape; try discriminate.
      destruct current2_2_1_2; cbn in Hshape; try discriminate.
      destruct current2_2_2; cbn in Hshape; try discriminate.
      destruct current2_2_2_2; cbn in Hshape; try discriminate.
      cbn in Heffect.
      do 5 (apply andb_prop in Hshape as [Hshape ?]).
      do 5 (apply andb_prop in Heffect as [Heffect ?]).
      destruct (conditional_access_shapeb_closings _ _ _ _ _ _ _ _ _ _ Hshape)
        as [-> ->].
      repeat match goal with
      | Hs : restricted_fragment_shape_check ?b ?piece = true,
        He : restricted_access_effect_check ?piece = true |- _ =>
          destruct (IH _ b piece ltac:(cbn; lia) fuel Hs He ltac:(cbn in *; lia))
            as [? ?]; clear Hs He
      end.
      cbn [restricted_normalize_statement_fuel].
      erewrite restricted_normalize_conditional_access_succeeds;
        [eexists; reflexivity | eassumption ..].
    + (* continued access *)
      destruct current2_2_1; cbn in Hshape; try discriminate.
      apply andb_prop in Hshape as [Hprefix Hwork_shape].
      apply andb_prop in Hprefix as [Hinvariant Hbody].
      apply bool_decide_eq_true in Hinvariant. subst invariant0.
      cbn in Heffect.
      destruct (decide (invariant = invariant)) as [Heq | Hneq];
        [|contradiction].
      replace Heq with (@eq_refl inv_id invariant) in Heffect
        by apply ProofIrrelevance.proof_irrelevance.
      cbn in Heffect.
      apply andb_prop in Heffect as [Heffect Hwork_effect].
      apply andb_prop in Heffect as [Hboundary Hbody_effect].
      destruct (IH _ _ current2_1 ltac:(cbn; lia) fuel Hbody Hbody_effect
        ltac:(cbn in *; lia)) as [body' Hbody'].
      destruct (IH _ _ current2_2_2 ltac:(cbn; lia) fuel Hwork_shape
        Hwork_effect ltac:(cbn in *; lia)) as [work' Hwork'].
      pose proof (restricted_access_boundary_check_sound _ _ _ Hboundary)
        as [Harguments _].
      subst.
      erewrite restricted_normalize_continued_access;
        [eexists; reflexivity | ..]; eassumption.
    + (* ghost conditional access *)
      destruct current2_2_1; cbn in Hshape; try discriminate.
      destruct current2_2_1_2; cbn in Hshape; try discriminate.
      destruct current2_2_2; cbn in Hshape; try discriminate.
      destruct current2_2_2_2; cbn in Hshape; try discriminate.
      cbn in Heffect.
      do 5 (apply andb_prop in Hshape as [Hshape ?]).
      do 5 (apply andb_prop in Heffect as [Heffect ?]).
      destruct (conditional_access_shapeb_closings _ _ _ _ _ _ _ _ _ _ Hshape)
        as [-> ->].
      repeat match goal with
      | Hs : restricted_fragment_shape_check ?b ?piece = true,
        He : restricted_access_effect_check ?piece = true |- _ =>
          destruct (IH _ b piece ltac:(cbn; lia) fuel Hs He ltac:(cbn in *; lia))
            as [? ?]; clear Hs He
      end.
      cbn [restricted_normalize_statement_fuel].
      erewrite restricted_normalize_conditional_access_succeeds;
        [eexists; reflexivity | eassumption ..].
  - cbn in Hshape. destruct nested'.
    + apply access_neutralb_unfold_freeb in Hshape. congruence.
    + congruence.
  - cbn in Hshape, Heffect, Hfuel.
    destruct (IH _ _ current ltac:(cbn; lia) fuel Hshape Heffect ltac:(cbn in *; lia))
      as [body' Hbody'].
    cbn [restricted_normalize_statement_fuel]. rewrite Hbody'.
    eexists; reflexivity.
  - cbn in Hshape, Heffect, Hfuel.
    apply andb_prop in Hshape as [Hthen Helse].
    apply andb_prop in Heffect as [Hthen_effect Helse_effect].
    destruct (IH _ _ current1 ltac:(cbn; lia) fuel Hthen Hthen_effect
      ltac:(cbn in *; lia)) as [then' Hthen'].
    destruct (IH _ _ current2 ltac:(cbn; lia) fuel Helse Helse_effect
      ltac:(cbn in *; lia)) as [else' Helse'].
    cbn [restricted_normalize_statement_fuel]. rewrite Hthen', Helse'.
    eexists; reflexivity.
Qed.

Lemma restricted_normalize_statement_succeeds_with_fuel {Γ}
    (statement : stmt Γ) fuel :
  restricted_fragment_accepted statement ->
  normalization_statement_size statement < fuel ->
  exists normalized,
    restricted_normalize_statement_fuel fuel statement = Some normalized.
Proof.
  unfold restricted_fragment_accepted, restricted_fragment_check.
  intros Haccepted. apply andb_prop in Haccepted as [Hshape Heffect].
  apply restricted_normalize_statement_succeeds_at with false; assumption.
Qed.

Corollary restricted_normalize_statement_succeeds {Γ} (statement : stmt Γ) :
  restricted_fragment_accepted statement ->
  exists normalized,
    restricted_normalize_statement_fuel
      (S (normalization_statement_size statement)) statement =
      Some normalized.
Proof.
  intro Haccepted.
  eapply restricted_normalize_statement_succeeds_with_fuel;
    [exact Haccepted|lia].
Qed.

Corollary restricted_analyze_and_normalize_succeeds {Γ}
    (statement : stmt Γ) :
  restricted_fragment_accepted statement ->
  exists normalized,
    restricted_analyze_and_normalize statement = Some normalized.
Proof.
  intro Haccepted.
  unfold restricted_analyze_and_normalize.
  rewrite Haccepted.
  now apply restricted_normalize_statement_succeeds.
Qed.

Lemma access_neutral_unfold_free {Γ} (statement : stmt Γ) :
  access_neutral statement -> unfold_free statement.
Proof.
  induction statement; simpl; intuition.
Qed.

(** Access-neutral statements cannot change the auxiliary LIFO stack.  This
    is particularly useful for trusted atomic bodies: their analyzer
    certificates may remain opaque while their lack of invariant operations
    determines the stack behavior completely. *)
Lemma access_neutral_lifo {Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      Γ entry statement exit) stack :
  access_neutral statement ->
  GenericRegions.Atomicity.lifo_certificate certificate stack stack.
Proof.
  revert stack.
  induction certificate; intros stack Hneutral; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hneutral. contradiction.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hneutral. contradiction.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    destruct Hneutral as [Hfirst Hsecond].
    exists stack. split; [apply IHcertificate1 | apply IHcertificate2];
      assumption.
  - destruct statement; cbn in e; try discriminate; inversion e; subst;
      destruct Hneutral as [Hthen Helse];
      (split; [apply IHcertificate1 | apply IHcertificate2]); assumption.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    split; [apply IHcertificate | reflexivity]. exact Hneutral.
  - destruct statement; cbn in e; try discriminate.
    injection e as Hd Hscope_body. subst d.
    apply Eqdep.EqdepTheory.inj_pair2 in Hscope_body. subst body.
    cbn in Hneutral. apply IHcertificate. exact Hneutral.
Qed.

Lemma access_neutral_preserves_open {Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      Γ entry statement exit) :
  access_neutral statement ->
  GenericRegions.Atomicity.analysis_open exit =
    GenericRegions.Atomicity.analysis_open entry.
Proof.
  induction certificate; intros Hneutral.
  - eapply GenericRegions.Atomicity.take_step_preserves_open; eauto.
  - reflexivity.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hneutral. contradiction.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hneutral. contradiction.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hneutral. destruct Hneutral as [Hfirst Hsecond].
    rewrite (IHcertificate2 Hsecond), (IHcertificate1 Hfirst). reflexivity.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    all: cbn in Hneutral; destruct Hneutral as [Hthen _].
    all: exact (IHcertificate1 Hthen).
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    eapply eq_trans; [exact e1|].
    eapply GenericRegions.Atomicity.take_step_preserves_open; eauto.
  - destruct statement; cbn in e; try discriminate.
    injection e as Hd Hscope_body. subst d.
    apply Eqdep.EqdepTheory.inj_pair2 in Hscope_body. subst body.
    cbn in Hneutral. exact (IHcertificate Hneutral).
Qed.

(** An unfold-free analyzed region entered with no open invariant is LIFO
    balanced.  Raw folds are deliberately allowed here: at a closed entry
    they are invariant allocation, hence leave both the analyzer open set
    and the auxiliary access stack unchanged. *)
Lemma unfold_free_closed_lifo {Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      Γ entry statement exit) :
  unfold_free statement ->
  GenericRegions.Atomicity.analysis_open entry = ∅ ->
  GenericRegions.Atomicity.lifo_certificate certificate [] [] /\
    GenericRegions.Atomicity.analysis_open exit = ∅.
Proof.
  induction certificate; intros Hfree Hclosed; simpl in *.
  - split; [reflexivity|].
    rewrite <- Hclosed.
    eapply GenericRegions.Atomicity.take_step_preserves_open; eauto.
  - split; [reflexivity | exact Hclosed].
  - destruct statement; cbn in e; try discriminate.
    cbn in Hfree. contradiction.
  - split.
    + right. split; [reflexivity|]. rewrite Hclosed. apply not_elem_of_empty.
    + destruct (GenericRegions.Atomicity.fold_fresh_invariant invariant state)
        as [_ Hopen].
      * rewrite Hclosed. apply not_elem_of_empty.
      * now rewrite Hopen, Hclosed.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    destruct Hfree as [Hfirst Hsecond].
    destruct (IHcertificate1 Hfirst Hclosed) as [Hlifo1 Hmiddle].
    destruct (IHcertificate2 Hsecond Hmiddle) as [Hlifo2 Hexit].
    split; [eexists; split; eassumption|exact Hexit].
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    all: destruct Hfree as [Hthen Helse].
    all: destruct (IHcertificate1 Hthen Hclosed) as [Hlifo1 Hthen_closed].
    all: destruct (IHcertificate2 Helse Hclosed) as [Hlifo2 Helse_closed].
    all: split; [split; assumption|exact Hthen_closed].
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    pose proof (GenericRegions.Atomicity.take_step_preserves_open _ _ _ e0)
      as Houter.
    rewrite Hclosed in Houter.
    destruct (IHcertificate Hfree Houter) as [Hlifo Hinner].
    split; [split; [exact Hlifo|reflexivity]|exact Hinner].
  - destruct statement; cbn in e; try discriminate.
    injection e as Hd Hscope_body. subst d.
    apply Eqdep.EqdepTheory.inj_pair2 in Hscope_body. subst body.
    cbn in Hfree. exact (IHcertificate Hfree Hclosed).
Qed.

Lemma structured_certificate_unfold_free {Γ entry statement exit}
    (certificate : structured_certificate Γ entry statement exit) :
    unfold_free statement.
Proof.
  induction certificate; simpl; intuition.
  all: destruct statement; cbn in e |- *; try discriminate; exact I.
Qed.

(** Safety condition needed by the Iris interpretation: invariant-access
    regions may contain trusted atomic blocks, but may not themselves occur
    inside one. *)
Fixpoint structured_accesses_outside_atomic
    {Γ entry statement exit}
    (certificate : structured_certificate Γ entry statement exit) : Prop :=
  match certificate with
  | StructuredSequence _ _ _ _ _ _ first second =>
      structured_accesses_outside_atomic first /\
      structured_accesses_outside_atomic second
  | StructuredConditional _ _ _ _ _ _ _ then_branch else_branch _ _ =>
      structured_accesses_outside_atomic then_branch /\
      structured_accesses_outside_atomic else_branch
  | StructuredAtomic _ _ _ _ _ _ body _ =>
      structured_accesses_outside_atomic body
  | StructuredInvAccess _ access_entry _ _ _ _ _ _ body _ =>
      GenericRegions.Atomicity.analysis_in_atomic access_entry = false /\
      structured_accesses_outside_atomic body
  | StructuredGhostVal _ _ _ _ _ _ _ body =>
      structured_accesses_outside_atomic body
  | StructuredGhostConditional _ _ _ _ _ _ _ then_branch else_branch _ _ =>
      structured_accesses_outside_atomic then_branch /\
      structured_accesses_outside_atomic else_branch
  | _ => True
  end.

(** Without an unfold, the LIFO machine can only preserve or pop its input
    stack.  These two small facts let the focused normalizer recognize an
    ordinary, stack-preserving prefix without reconstructing an access trace. *)
Lemma unfold_free_lifo_length_le {Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      Γ entry statement exit) stack_in stack_out :
  unfold_free statement ->
  GenericRegions.Atomicity.lifo_certificate certificate stack_in stack_out ->
  length stack_out <= length stack_in.
Proof.
  revert stack_in stack_out.
  induction certificate; intros stack_in stack_out Hfree Hlifo; simpl in *.
  - subst stack_out. lia.
  - subst stack_out. lia.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hfree. contradiction.
  - destruct Hlifo as [(outer & -> & _)|[-> _]]; simpl; lia.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree. destruct Hfree as [Hfirst_free Hsecond_free].
    destruct Hlifo as (stack_middle & Hfirst & Hsecond).
    specialize (IHcertificate1 _ _ Hfirst_free Hfirst).
    specialize (IHcertificate2 _ _ Hsecond_free Hsecond). lia.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    all: cbn in Hfree. all: destruct Hfree as [Hthen_free Helse_free].
    all: destruct Hlifo as [Hthen _]. all: eauto.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree. destruct Hlifo as [Hbody ->]. eauto.
  - destruct statement; cbn in e; try discriminate.
    injection e as Hd Hscope_body. subst d.
    apply Eqdep.EqdepTheory.inj_pair2 in Hscope_body. subst body.
    cbn in Hfree. eauto.
Qed.

Lemma unfold_free_lifo_same_length {Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      Γ entry statement exit) stack_in stack_out :
  unfold_free statement ->
  GenericRegions.Atomicity.lifo_certificate certificate stack_in stack_out ->
  length stack_out = length stack_in ->
  stack_out = stack_in.
Proof.
  revert stack_in stack_out.
  induction certificate; intros stack_in stack_out Hfree Hlifo Hlength;
    simpl in *.
  - exact Hlifo.
  - exact Hlifo.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hfree. contradiction.
  - destruct Hlifo as [(outer & -> & _)|[-> _]]; [simpl in Hlength; lia|reflexivity].
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree. destruct Hfree as [Hfirst_free Hsecond_free].
    destruct Hlifo as (stack_middle & Hfirst & Hsecond).
    pose proof (unfold_free_lifo_length_le certificate1 _ _
      Hfirst_free Hfirst) as Hfirst_le.
    pose proof (unfold_free_lifo_length_le certificate2 _ _
      Hsecond_free Hsecond) as Hsecond_le.
    assert (length stack_middle = length stack_in) by lia.
    pose proof (IHcertificate1 _ _ Hfirst_free Hfirst ltac:(assumption))
      as Hmiddle. subst stack_middle.
    apply IHcertificate2; assumption.
  - destruct statement; cbn in e; try discriminate; inversion e; subst; clear e.
    all: cbn in Hfree. all: destruct Hfree as [Hthen_free _].
    all: destruct Hlifo as [Hthen _]. all: eauto.
  - destruct statement; cbn in e; try discriminate; inversion e; subst; clear e.
    destruct Hlifo as [Hbody ->]. reflexivity.
  - destruct statement; cbn in e; try discriminate.
    injection e as Hd Hscope_body. subst d.
    apply Eqdep.EqdepTheory.inj_pair2 in Hscope_body. subst body.
    cbn in Hfree. eauto.
Qed.

Definition choose_lifo_sequence_middle
    {Γ entry statement first middle second exit view
      first_certificate second_certificate stack_in stack_out}
    (Hlifo : GenericRegions.Atomicity.lifo_certificate
      (GenericRegions.Atomicity.CertSequence Γ entry statement first
        middle second exit view first_certificate second_certificate)
      stack_in stack_out) :
  { stack_middle : list GenericRegions.Atomicity.access_marker |
    GenericRegions.Atomicity.lifo_certificate first_certificate stack_in
      stack_middle /\
    GenericRegions.Atomicity.lifo_certificate second_certificate stack_middle
      stack_out }.
Proof.
  apply constructive_indefinite_description. exact Hlifo.
Defined.

(** Every accepted baseline region is balanced when entered with no pending
    access marker.  This is the compositional boundary needed to normalize
    two adjacent accepted regions independently: the parent sequence's
    existential LIFO midpoint is forced back to [[]]. *)
(** ** Certificates of canonical conditional accesses *)

Lemma guard_if_view {Γ} (guard : access_guard Γ) (then_branch else_branch : stmt Γ) :
  @AnalysisView.syntax_view _ Γ (guard_if guard then_branch else_branch) =
    AnalysisView.ViewConditional then_branch else_branch.
Proof. destruct guard; reflexivity. Qed.

Definition closing_branch_certificate {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (branch_prefix continuation : stmt Γ) {joined closed exit}
    (prefix_certificate : Atom.analysis_certificate Γ joined branch_prefix closed)
    (continuation_certificate : Atom.analysis_certificate Γ
      (Atom.fold_invariant invariant closed) continuation exit) :
    Atom.analysis_certificate Γ joined
      (canonical_branch invariant arguments branch_prefix continuation) exit :=
  Atom.CertSequence Γ joined
    (canonical_branch invariant arguments branch_prefix continuation)
    branch_prefix closed (TSeq (TFold invariant arguments) continuation) exit
    eq_refl prefix_certificate
    (Atom.CertSequence Γ closed (TSeq (TFold invariant arguments) continuation)
      (TFold invariant arguments)
      (Atom.fold_invariant invariant closed) continuation exit eq_refl
      (Atom.CertFold Γ closed (TFold invariant arguments) invariant eq_refl)
      continuation_certificate).

Definition conditional_access_certificate {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ)
    {entry opened joined then_closed then_exit else_closed else_exit}
    (Hopen : Atom.open_invariant invariant entry = inr opened)
    (prefix_certificate : Atom.analysis_certificate Γ opened prefix joined)
    (then_prefix_certificate :
      Atom.analysis_certificate Γ joined then_prefix then_closed)
    (then_certificate : Atom.analysis_certificate Γ
      (Atom.fold_invariant invariant then_closed) then_continuation then_exit)
    (else_prefix_certificate :
      Atom.analysis_certificate Γ joined else_prefix else_closed)
    (else_certificate : Atom.analysis_certificate Γ
      (Atom.fold_invariant invariant else_closed) else_continuation else_exit)
    (Hopen_equal : Atom.analysis_open then_exit = Atom.analysis_open else_exit)
    (Hatomic_equal :
      Atom.analysis_in_atomic then_exit = Atom.analysis_in_atomic else_exit) :
    Atom.analysis_certificate Γ entry
      (conditional_access invariant arguments prefix guard then_prefix
        then_continuation else_prefix else_continuation)
      (Atom.AnalysisState
        (Atom.analysis_mask then_exit ∩ Atom.analysis_mask else_exit)
        (Atom.analysis_open then_exit)
        (Atom.analysis_step_taken then_exit || Atom.analysis_step_taken else_exit)
        (Atom.analysis_in_atomic then_exit)) :=
  let then_branch :=
    canonical_branch invariant arguments then_prefix then_continuation in
  let else_branch :=
    canonical_branch invariant arguments else_prefix else_continuation in
  let conditional := guard_if guard then_branch else_branch in
  Atom.CertSequence Γ entry
    (conditional_access invariant arguments prefix guard then_prefix
      then_continuation else_prefix else_continuation)
    (TUnfold invariant arguments) opened (TSeq prefix conditional) _ eq_refl
    (Atom.CertUnfold Γ entry (TUnfold invariant arguments) invariant opened
      eq_refl Hopen)
    (Atom.CertSequence Γ opened (TSeq prefix conditional) prefix joined
      conditional _ eq_refl prefix_certificate
      (Atom.CertConditional Γ joined conditional then_branch else_branch
        then_exit else_exit
        (guard_if_view guard _ _)
        (closing_branch_certificate invariant arguments then_prefix
          then_continuation then_prefix_certificate then_certificate)
        (closing_branch_certificate invariant arguments else_prefix
          else_continuation else_prefix_certificate else_certificate)
        Hopen_equal Hatomic_equal)).

Record conditional_access_parts {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ)
    (entry exit : Atom.analysis_state) : Type := {
  cap_opened : Atom.analysis_state;
  cap_joined : Atom.analysis_state;
  cap_then_closed : Atom.analysis_state;
  cap_then_exit : Atom.analysis_state;
  cap_else_closed : Atom.analysis_state;
  cap_else_exit : Atom.analysis_state;
  cap_open : Atom.open_invariant invariant entry = inr cap_opened;
  cap_prefix : Atom.analysis_certificate Γ cap_opened prefix cap_joined;
  cap_then_prefix :
    Atom.analysis_certificate Γ cap_joined then_prefix cap_then_closed;
  cap_then : Atom.analysis_certificate Γ
    (Atom.fold_invariant invariant cap_then_closed) then_continuation
    cap_then_exit;
  cap_else_prefix :
    Atom.analysis_certificate Γ cap_joined else_prefix cap_else_closed;
  cap_else : Atom.analysis_certificate Γ
    (Atom.fold_invariant invariant cap_else_closed) else_continuation
    cap_else_exit;
  cap_open_equal : Atom.analysis_open cap_then_exit =
    Atom.analysis_open cap_else_exit;
  cap_atomic_equal : Atom.analysis_in_atomic cap_then_exit =
    Atom.analysis_in_atomic cap_else_exit;
  cap_exit : exit = Atom.AnalysisState
    (Atom.analysis_mask cap_then_exit ∩ Atom.analysis_mask cap_else_exit)
    (Atom.analysis_open cap_then_exit)
    (Atom.analysis_step_taken cap_then_exit ||
      Atom.analysis_step_taken cap_else_exit)
    (Atom.analysis_in_atomic cap_then_exit);
}.

Ltac view_inversion :=
  match goal with
  | Hview : @AnalysisView.syntax_view _ _ _ = _ |- _ =>
      cbn in Hview; inversion Hview; subst; try clear Hview
  end.

Lemma conditional_access_certificate_parts {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ)
    entry exit
    (certificate : Atom.analysis_certificate Γ entry
      (conditional_access invariant arguments prefix guard then_prefix
        then_continuation else_prefix else_continuation) exit) :
  conditional_access_parts invariant arguments prefix guard then_prefix
    then_continuation else_prefix else_continuation entry exit.
Proof.
  unfold conditional_access in certificate.
  destruct guard; cbn [guard_if] in certificate.
  all: dependent destruction certificate; try discriminate; try view_inversion.
  all: dependent destruction certificate1; try discriminate; try view_inversion.
  all: dependent destruction certificate2; try discriminate; try view_inversion.
  all: dependent destruction certificate2_2; try discriminate; try view_inversion.
  all: dependent destruction certificate2_2_1; try discriminate; try view_inversion.
  all: dependent destruction certificate2_2_1_2; try discriminate;
    try view_inversion.
  all: dependent destruction certificate2_2_1_2_1; try discriminate;
    try view_inversion.
  all: dependent destruction certificate2_2_2; try discriminate; try view_inversion.
  all: dependent destruction certificate2_2_2_2; try discriminate;
    try view_inversion.
  all: dependent destruction certificate2_2_2_2_1; try discriminate;
    try view_inversion.
  all: econstructor; try eassumption; reflexivity.
Qed.

Lemma closing_branch_lifo {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (branch_prefix continuation : stmt Γ) {joined closed exit}
    (prefix_certificate : Atom.analysis_certificate Γ joined branch_prefix closed)
    (continuation_certificate : Atom.analysis_certificate Γ
      (Atom.fold_invariant invariant closed) continuation exit)
    marker_open stack stack_out :
  (forall stack', Atom.lifo_certificate prefix_certificate stack' stack') ->
  Atom.analysis_open closed = Atom.analysis_open joined ->
  invariant ∈ Atom.analysis_open joined ->
  Atom.lifo_certificate (closing_branch_certificate invariant arguments
    branch_prefix continuation prefix_certificate continuation_certificate)
    ((invariant, marker_open) :: stack) stack_out ->
  Atom.lifo_certificate continuation_certificate stack stack_out.
Proof.
  intros Hprefix_lifo Hprefix_open Hopen Hlifo.
  cbn [closing_branch_certificate Atom.lifo_certificate] in Hlifo.
  destruct Hlifo as (prefix_stack & Hprefix & fold_stack & Hfold & Hcontinuation).
  assert (prefix_stack = (invariant, marker_open) :: stack) as ->.
  { eapply Atom.lifo_certificate_functional; [exact Hprefix|].
    apply Hprefix_lifo. }
  destruct Hfold as [(outer_open & Hstack & _)|[_ Hclosed]].
  - inversion Hstack; subst. exact Hcontinuation.
  - exfalso. apply Hclosed. rewrite Hprefix_open. exact Hopen.
Qed.

Lemma closing_branch_lifo_intro {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (branch_prefix continuation : stmt Γ) {joined closed exit}
    (prefix_certificate : Atom.analysis_certificate Γ joined branch_prefix closed)
    (continuation_certificate : Atom.analysis_certificate Γ
      (Atom.fold_invariant invariant closed) continuation exit)
    marker_open stack stack_out :
  (forall stack', Atom.lifo_certificate prefix_certificate stack' stack') ->
  Atom.analysis_open closed = Atom.analysis_open joined ->
  invariant ∉ marker_open ->
  Atom.analysis_open joined = {[invariant]} ∪ marker_open ->
  Atom.lifo_certificate continuation_certificate stack stack_out ->
  Atom.lifo_certificate (closing_branch_certificate invariant arguments
    branch_prefix continuation prefix_certificate continuation_certificate)
    ((invariant, marker_open) :: stack) stack_out.
Proof.
  intros Hprefix_lifo Hclosed_open Hfresh Hjoined Hcontinuation.
  cbn [closing_branch_certificate Atom.lifo_certificate].
  exists ((invariant, marker_open) :: stack). split; [apply Hprefix_lifo|].
  exists stack. split; [|exact Hcontinuation].
  left. exists marker_open. rewrite Hclosed_open, Hjoined.
  repeat split; [set_solver | exact Hfresh].
Qed.

Lemma fold_after_open_closes invariant (outer inner : Atom.analysis_state) :
  invariant ∉ Atom.analysis_open outer ->
  Atom.analysis_open inner = {[invariant]} ∪ Atom.analysis_open outer ->
  Atom.analysis_open (Atom.fold_invariant invariant inner) =
    Atom.analysis_open outer.
Proof.
  intros Hfresh Hinner.
  rewrite (proj2 (Atom.fold_open_invariant invariant inner
    ltac:(rewrite Hinner; set_solver))), Hinner.
  set_solver.
Qed.

(** A piece of a conditional access that keeps any stack and the open set. *)
Definition balanced_piece {Γ} (statement : stmt Γ) : Prop :=
  forall entry exit
    (certificate : Atom.analysis_certificate Γ entry statement exit),
  (forall stack, Atom.lifo_certificate certificate stack stack) /\
  Atom.analysis_open exit = Atom.analysis_open entry.

Lemma access_neutral_balanced {Γ} (statement : stmt Γ) :
  access_neutral statement -> balanced_piece statement.
Proof.
  intros Hneutral entry exit certificate. split.
  - intros. apply access_neutral_lifo. exact Hneutral.
  - exact (access_neutral_preserves_open certificate Hneutral).
Qed.

Lemma conditional_access_balanced {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ) :
  balanced_piece prefix -> balanced_piece then_prefix ->
  balanced_piece else_prefix -> balanced_piece then_continuation ->
  balanced_piece else_continuation ->
  balanced_piece (conditional_access invariant arguments prefix guard
    then_prefix then_continuation else_prefix else_continuation).
Proof.
  intros Hq Htp Hep Htc Hec entry exit certificate.
  destruct (conditional_access_certificate_parts _ _ _ _ _ _ _ _ _ _
    certificate) as [opened joined then_closed then_exit else_closed else_exit
      Hopen cq ctp ctc cep cec Hopen_equal Hatomic_equal Hexit].
  subst exit.
  rewrite (Atom.analysis_certificate_unique certificate
    (conditional_access_certificate _ _ _ _ _ _ _ _ Hopen cq ctp ctc cep cec
      Hopen_equal Hatomic_equal)).
  pose proof (Atom.open_invariant_success _ _ _ Hopen)
    as (Hfresh & _ & _ & Hopened).
  destruct (Hq _ _ cq) as [Hq_lifo Hq_open].
  destruct (Htp _ _ ctp) as [Htp_lifo Htp_open].
  destruct (Hep _ _ cep) as [Hep_lifo Hep_open].
  destruct (Htc _ _ ctc) as [Htc_lifo Htc_open].
  destruct (Hec _ _ cec) as [Hec_lifo Hec_open].
  assert (Hjoined : Atom.analysis_open joined =
    {[invariant]} ∪ Atom.analysis_open entry) by congruence.
  split.
  - intros stack. cbn [conditional_access_certificate Atom.lifo_certificate].
    eexists. split; [reflexivity|].
    eexists. split; [apply Hq_lifo|].
    split; eapply closing_branch_lifo_intro; eauto.
  - cbn [Atom.analysis_open]. rewrite Htc_open.
    apply fold_after_open_closes; [exact Hfresh | congruence].
Qed.

(** A nested statement keeps any access stack and the open set. *)
Lemma baseline_nested_balanced {Γ} nested (statement : stmt Γ)
    (Hbaseline : baseline_normalizable nested statement) :
  nested = true ->
  forall entry exit
    (certificate : Atom.analysis_certificate Γ entry statement exit),
  (forall stack, Atom.lifo_certificate certificate stack stack) /\
  Atom.analysis_open exit = Atom.analysis_open entry.
Proof.
  induction Hbaseline; intros Hnested entry exit certificate; subst nested.
  - exact (access_neutral_balanced _ y _ _ certificate).
  - dependent destruction certificate; try discriminate.
    try view_inversion.
    destruct (IHHbaseline eq_refl _ _ certificate2) as [Hlifo Hopen].
    split.
    + intros stack. exists stack. split; [apply access_neutral_lifo; exact a|].
      apply Hlifo.
    + rewrite Hopen. exact (access_neutral_preserves_open certificate1 a).
  - dependent destruction certificate; try discriminate.
    try view_inversion.
    destruct (IHHbaseline1 eq_refl _ _ certificate1) as [Hlifo1 Hopen1].
    destruct (IHHbaseline2 eq_refl _ _ certificate2) as [Hlifo2 Hopen2].
    split; [intros stack; exists stack; split; auto | congruence].
  - dependent destruction certificate; try discriminate.
    try view_inversion.
    destruct (IHHbaseline1 eq_refl _ _ certificate1) as [Hlifo1 Hopen1].
    destruct (IHHbaseline2 eq_refl _ _ certificate2) as [Hlifo2 Hopen2].
    split; [intros stack; split; auto | exact Hopen1].
  - subst closing_arguments.
    dependent destruction certificate; try discriminate.
    try view_inversion.
    dependent destruction certificate1; try discriminate.
    try view_inversion.
    dependent destruction certificate2; try discriminate.
    try view_inversion.
    dependent destruction certificate2_2; try discriminate.
    try view_inversion.
    pose proof (Atom.open_invariant_success _ _ _ e0)
      as (Hfresh & _ & _ & Hopened).
    destruct (IHHbaseline eq_refl _ _ certificate2_1) as [Hlifo Hopen].
    rewrite Hopened in Hopen.
    split.
    + intros stack. cbn [Atom.lifo_certificate].
      eexists. split; [reflexivity|]. eexists. split; [apply Hlifo|].
      left. eexists. split; [reflexivity|]. rewrite Hopen.
      split; [set_solver|]. split; [exact Hfresh | reflexivity].
    + apply fold_after_open_closes; assumption.
  - subst closing_arguments.
    dependent destruction certificate; try discriminate.
    try view_inversion.
    dependent destruction certificate1; try discriminate.
    try view_inversion.
    dependent destruction certificate2; try discriminate.
    try view_inversion.
    dependent destruction certificate2_2; try discriminate.
    try view_inversion.
    dependent destruction certificate2_2_1; try discriminate.
    try view_inversion.
    pose proof (Atom.open_invariant_success _ _ _ e0)
      as (Hfresh & _ & _ & Hopened).
    destruct (IHHbaseline1 eq_refl _ _ certificate2_1) as [Hlifo Hopen].
    rewrite Hopened in Hopen.
    destruct (IHHbaseline2 eq_refl _ _ certificate2_2_2) as [Hwork_lifo Hwork_open].
    split.
    + intros stack. cbn [Atom.lifo_certificate].
      eexists. split; [reflexivity|]. eexists. split; [apply Hlifo|].
      eexists. split; [|apply Hwork_lifo].
      left. eexists. split; [reflexivity|]. rewrite Hopen.
      split; [set_solver|]. split; [exact Hfresh | reflexivity].
    + rewrite Hwork_open. apply fold_after_open_closes; assumption.
  - dependent destruction certificate; try discriminate.
    match goal with
    | Hview : @AnalysisView.syntax_view _ _ (TGhostVal _ _ _ _) = _ |- _ =>
        cbn in Hview; injection Hview as Hd Hscope_body
    end.
    subst. apply Eqdep.EqdepTheory.inj_pair2 in Hscope_body. subst.
    exact (IHHbaseline eq_refl _ _ certificate).
  - dependent destruction certificate; try discriminate.
    try view_inversion.
    destruct (IHHbaseline1 eq_refl _ _ certificate1) as [Hlifo1 Hopen1].
    destruct (IHHbaseline2 eq_refl _ _ certificate2) as [Hlifo2 Hopen2].
    split; [intros stack; split; auto | exact Hopen1].
  - apply conditional_access_balanced;
      [exact (IHHbaseline1 eq_refl) | exact (IHHbaseline2 eq_refl)
      | exact (IHHbaseline3 eq_refl) | exact (IHHbaseline4 eq_refl)
      | exact (IHHbaseline5 eq_refl)].
  - apply conditional_access_balanced;
      [exact (IHHbaseline1 eq_refl) | apply access_neutral_balanced; assumption
      | apply access_neutral_balanced; assumption
      | exact (IHHbaseline2 eq_refl) | exact (IHHbaseline3 eq_refl)].
Qed.

Lemma conditional_access_empty_output {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ) :
  balanced_piece prefix -> balanced_piece then_prefix ->
  (forall entry exit
    (certificate : Atom.analysis_certificate Γ entry then_continuation exit)
    stack_out,
    Atom.lifo_certificate certificate [] stack_out -> stack_out = []) ->
  forall entry exit
    (certificate : Atom.analysis_certificate Γ entry
      (conditional_access invariant arguments prefix guard then_prefix
        then_continuation else_prefix else_continuation) exit) stack_out,
  Atom.lifo_certificate certificate [] stack_out -> stack_out = [].
Proof.
  intros Hq Htp Htc entry exit certificate stack_out Hlifo.
  destruct (conditional_access_certificate_parts _ _ _ _ _ _ _ _ _ _
    certificate) as [opened joined then_closed then_exit else_closed else_exit
      Hopen cq ctp ctc cep cec Hopen_equal Hatomic_equal Hexit].
  subst exit.
  rewrite (Atom.analysis_certificate_unique certificate
    (conditional_access_certificate _ _ _ _ _ _ _ _ Hopen cq ctp ctc cep cec
      Hopen_equal Hatomic_equal)) in Hlifo.
  pose proof (Atom.open_invariant_success _ _ _ Hopen)
    as (_ & _ & _ & Hopened).
  destruct (Hq _ _ cq) as [Hq_lifo Hq_open].
  destruct (Htp _ _ ctp) as [Htp_lifo Htp_open].
  cbn [conditional_access_certificate Atom.lifo_certificate] in Hlifo.
  destruct Hlifo as (m1 & -> & m2 & Hq_run & Hthen & _).
  assert (m2 = [(invariant, Atom.analysis_open entry)]) as ->
    by (eapply Atom.lifo_certificate_functional; [exact Hq_run | apply Hq_lifo]).
  eapply Htc. eapply closing_branch_lifo; [exact Htp_lifo | exact Htp_open | |
    exact Hthen].
  rewrite Hq_open, Hopened. set_solver.
Qed.

Lemma conditional_access_closed_lifo {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ) :
  balanced_piece prefix -> balanced_piece then_prefix ->
  balanced_piece else_prefix ->
  (forall entry exit
    (certificate : Atom.analysis_certificate Γ entry then_continuation exit),
    Atom.analysis_open entry = ∅ ->
    Atom.lifo_certificate certificate [] [] /\ Atom.analysis_open exit = ∅) ->
  (forall entry exit
    (certificate : Atom.analysis_certificate Γ entry else_continuation exit),
    Atom.analysis_open entry = ∅ ->
    Atom.lifo_certificate certificate [] [] /\ Atom.analysis_open exit = ∅) ->
  forall entry exit
    (certificate : Atom.analysis_certificate Γ entry
      (conditional_access invariant arguments prefix guard then_prefix
        then_continuation else_prefix else_continuation) exit),
  Atom.analysis_open entry = ∅ ->
  Atom.lifo_certificate certificate [] [] /\ Atom.analysis_open exit = ∅.
Proof.
  intros Hq Htp Hep Htc Hec entry exit certificate Hentry.
  destruct (conditional_access_certificate_parts _ _ _ _ _ _ _ _ _ _
    certificate) as [opened joined then_closed then_exit else_closed else_exit
      Hopen cq ctp ctc cep cec Hopen_equal Hatomic_equal Hexit].
  subst exit.
  rewrite (Atom.analysis_certificate_unique certificate
    (conditional_access_certificate _ _ _ _ _ _ _ _ Hopen cq ctp ctc cep cec
      Hopen_equal Hatomic_equal)).
  pose proof (Atom.open_invariant_success _ _ _ Hopen)
    as (Hfresh & _ & _ & Hopened).
  destruct (Hq _ _ cq) as [Hq_lifo Hq_open].
  destruct (Htp _ _ ctp) as [Htp_lifo Htp_open].
  destruct (Hep _ _ cep) as [Hep_lifo Hep_open].
  assert (Hjoined : Atom.analysis_open joined =
    {[invariant]} ∪ Atom.analysis_open entry) by congruence.
  destruct (Htc _ _ ctc) as [Htc_lifo Htc_exit].
  { rewrite (fold_after_open_closes invariant entry); [exact Hentry | exact Hfresh
    | congruence]. }
  destruct (Hec _ _ cec) as [Hec_lifo _].
  { rewrite (fold_after_open_closes invariant entry); [exact Hentry | exact Hfresh
    | congruence]. }
  split; [|exact Htc_exit].
  cbn [conditional_access_certificate Atom.lifo_certificate].
  eexists. split; [reflexivity|].
  eexists. split; [apply Hq_lifo|].
  split; eapply closing_branch_lifo_intro; eauto.
Qed.

Lemma baseline_normalizable_empty_output {Γ} nested (statement : stmt Γ)
    (Hbaseline : baseline_normalizable nested statement) :
  nested = false ->
  forall entry exit
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry statement exit) stack_out,
    GenericRegions.Atomicity.lifo_certificate certificate [] stack_out ->
    stack_out = [].
Proof.
  induction Hbaseline; intros Hnested entry exit certificate stack_out Hlifo;
    subst nested.
  - pose proof (unfold_free_lifo_length_le certificate [] stack_out y Hlifo)
      as Hlength.
    destruct stack_out; [reflexivity|simpl in Hlength; lia].
  - dependent destruction certificate; try discriminate. try view_inversion.
    destruct Hlifo as (middle_stack & Hfirst & Hsecond).
    assert (Hmiddle : middle_stack = []).
    { eapply Atom.lifo_certificate_functional; [exact Hfirst|].
      apply access_neutral_lifo. exact a. }
    subst middle_stack.
    exact (IHHbaseline eq_refl _ _ _ _ Hsecond).
  - dependent destruction certificate; try discriminate. try view_inversion.
    destruct Hlifo as (middle_stack & Hfirst & Hsecond).
    pose proof (IHHbaseline1 eq_refl _ _ _ _ Hfirst). subst middle_stack.
    exact (IHHbaseline2 eq_refl _ _ _ _ Hsecond).
  - dependent destruction certificate; try discriminate. try view_inversion.
    destruct Hlifo as [Hthen _]. exact (IHHbaseline1 eq_refl _ _ _ _ Hthen).
  - subst closing_arguments.
    dependent destruction certificate; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TSeq _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate1; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TUnfold _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TSeq _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2_2; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TFold _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    destruct (baseline_nested_balanced _ _ Hbaseline eq_refl _ _ certificate2_1)
      as [Hbody_lifo Hbody_open].
    destruct Hlifo as (opened_stack & Hopen & Htail).
    destruct Htail as (body_stack & Hbody & Hfold).
    assert (body_stack = opened_stack) as ->
      by (eapply Atom.lifo_certificate_functional; [exact Hbody | apply Hbody_lifo]).
    unfold Atom.lifo_certificate in Hfold.
    destruct Hfold as [(outer_open & Hstack & _)|[Hsame Hclosed]].
    + cbn in Hopen. congruence.
    + exfalso. apply Hclosed. rewrite Hbody_open.
      match goal with
      | Htransition : Atom.open_invariant _ _ = inr _ |- _ =>
          pose proof (Atom.open_invariant_success _ _ _ Htransition)
            as (_ & _ & _ & ->)
      end.
      set_solver.
  - subst closing_arguments.
    dependent destruction certificate; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TSeq _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate1; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TUnfold _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TSeq _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2_2; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TSeq _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    match goal with
    | Hfold_certificate : Atom.analysis_certificate _ _ (TFold _ _) _ |- _ =>
        dependent destruction Hfold_certificate
    end; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TFold _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    destruct (baseline_nested_balanced _ _ Hbaseline1 eq_refl _ _ certificate2_1)
      as [Hbody_lifo Hbody_open].
    destruct Hlifo as (opened_stack & Hopen & Htail).
    destruct Htail as (body_stack & Hbody & Hfold_work).
    assert (body_stack = opened_stack) as ->
      by (eapply Atom.lifo_certificate_functional; [exact Hbody | apply Hbody_lifo]).
    destruct Hfold_work as (closed_stack & Hfold & Hwork).
    unfold Atom.lifo_certificate in Hfold.
    destruct Hfold as [(outer_open & Hstack & _)|[Hsame Hclosed]].
    + cbn in Hopen. subst opened_stack.
      inversion Hstack; subst outer_open closed_stack.
      exact (IHHbaseline2 eq_refl _ _ _ _ Hwork).
    + exfalso. apply Hclosed. rewrite Hbody_open.
      match goal with
      | Htransition : Atom.open_invariant _ _ = inr _ |- _ =>
          pose proof (Atom.open_invariant_success _ _ _ Htransition)
            as (_ & _ & _ & ->)
      end.
      set_solver.
  - dependent destruction certificate; try discriminate.
    match goal with
    | Hview : @AnalysisView.syntax_view _ _ (TGhostVal _ _ _ _) = _ |- _ =>
        cbn in Hview; injection Hview as Hd Hscope_body
    end.
    subst. apply Eqdep.EqdepTheory.inj_pair2 in Hscope_body. subst.
    exact (IHHbaseline eq_refl _ _ _ _ Hlifo).
  - dependent destruction certificate; try discriminate. try view_inversion.
    destruct Hlifo as [Hthen _]. exact (IHHbaseline1 eq_refl _ _ _ _ Hthen).
  - eapply conditional_access_empty_output; [| | | exact Hlifo].
    + exact (baseline_nested_balanced _ _ Hbaseline1 eq_refl).
    + exact (baseline_nested_balanced _ _ Hbaseline2 eq_refl).
    + exact (IHHbaseline4 eq_refl).
  - eapply conditional_access_empty_output; [| | | exact Hlifo].
    + exact (baseline_nested_balanced _ _ Hbaseline1 eq_refl).
    + apply access_neutral_balanced. assumption.
    + exact (IHHbaseline2 eq_refl).
Qed.

(** Accepted source regions are balanced at a closed procedure boundary.
    Unlike the purely syntactic statement, this uses the analyzer entry
    state so that an unmatched raw fold is correctly treated as allocation. *)
Lemma baseline_normalizable_closed_lifo {Γ} nested (statement : stmt Γ)
    (Hbaseline : baseline_normalizable nested statement) :
  nested = false ->
  forall entry exit
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry statement exit),
    GenericRegions.Atomicity.analysis_open entry = ∅ ->
    GenericRegions.Atomicity.lifo_certificate certificate [] [] /\
      GenericRegions.Atomicity.analysis_open exit = ∅.
Proof.
  induction Hbaseline; intros Hnested entry exit certificate Hentry;
    subst nested.
  - now apply unfold_free_closed_lifo.
  - dependent destruction certificate; try discriminate. try view_inversion.
    assert (Hmiddle : Atom.analysis_open middle = ∅).
    { rewrite (access_neutral_preserves_open certificate1 a). exact Hentry. }
    destruct (IHHbaseline eq_refl _ _ certificate2 Hmiddle) as [Hsecond Hexit].
    split; [|exact Hexit]. eexists. split; [|exact Hsecond].
    apply access_neutral_lifo. exact a.
  - dependent destruction certificate; try discriminate. try view_inversion.
    destruct (IHHbaseline1 eq_refl _ _ certificate1 Hentry) as [Hfirst Hmiddle].
    destruct (IHHbaseline2 eq_refl _ _ certificate2 Hmiddle) as [Hsecond Hexit].
    split; [eexists; split; eassumption|exact Hexit].
  - dependent destruction certificate; try discriminate. try view_inversion.
    destruct (IHHbaseline1 eq_refl _ _ certificate1 Hentry) as [Hthen Hthen_exit].
    destruct (IHHbaseline2 eq_refl _ _ certificate2 Hentry) as [Helse Helse_exit].
    split; [split; assumption|exact Hthen_exit].
  - subst closing_arguments.
    dependent destruction certificate; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TSeq _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate1; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TUnfold _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TSeq _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2_2; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TFold _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    pose proof (Atom.open_invariant_success _ _ _ e0)
      as (Hfresh & _ & _ & Hopened).
    destruct (baseline_nested_balanced _ _ Hbaseline eq_refl _ _ certificate2_1)
      as [Hbody_lifo Hbody_open].
    rewrite Hopened in Hbody_open.
    split.
    + cbn [Atom.lifo_certificate]. eexists. split; [reflexivity|].
      eexists. split; [apply Hbody_lifo|].
      left. eexists. split; [reflexivity|]. rewrite Hbody_open.
      split; [set_solver|]. split; [exact Hfresh | reflexivity].
    + rewrite (fold_after_open_closes invariant state); assumption.
  - subst closing_arguments.
    dependent destruction certificate; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TSeq _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate1; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TUnfold _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TSeq _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    dependent destruction certificate2_2; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TSeq _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    match goal with
    | Hfold_certificate : Atom.analysis_certificate _ _ (TFold _ _) _ |- _ =>
        dependent destruction Hfold_certificate
    end; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TFold _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    pose proof (Atom.open_invariant_success _ _ _ e0)
      as (Hfresh & _ & _ & Hopened).
    destruct (baseline_nested_balanced _ _ Hbaseline1 eq_refl _ _ certificate2_1)
      as [Hbody_lifo Hbody_open].
    rewrite Hopened in Hbody_open.
    assert (Hclosed_middle : Atom.analysis_open
      (Atom.fold_invariant invariant state1) = ∅)
      by (rewrite (fold_after_open_closes invariant state); assumption).
    destruct (IHHbaseline2 eq_refl _ _ certificate2_2_2 Hclosed_middle)
      as [Hwork Hexit].
    split; [|exact Hexit].
    cbn [Atom.lifo_certificate]. eexists. split; [reflexivity|].
    eexists. split; [apply Hbody_lifo|].
    eexists. split; [|exact Hwork].
    left. eexists. split; [reflexivity|]. rewrite Hbody_open.
    split; [set_solver|]. split; [exact Hfresh | reflexivity].
  - dependent destruction certificate; try discriminate.
    match goal with
    | Hview : @AnalysisView.syntax_view _ _ (TGhostVal _ _ _ _) = _ |- _ =>
        cbn in Hview; injection Hview as Hd Hscope_body
    end.
    subst. apply Eqdep.EqdepTheory.inj_pair2 in Hscope_body. subst.
    simpl. exact (IHHbaseline eq_refl _ _ _ Hentry).
  - dependent destruction certificate; try discriminate. try view_inversion.
    destruct (IHHbaseline1 eq_refl _ _ certificate1 Hentry) as [Hthen Hthen_exit].
    destruct (IHHbaseline2 eq_refl _ _ certificate2 Hentry) as [Helse Helse_exit].
    split; [split; assumption|exact Hthen_exit].
  - eapply conditional_access_closed_lifo; [| | | | | exact Hentry].
    + exact (baseline_nested_balanced _ _ Hbaseline1 eq_refl).
    + exact (baseline_nested_balanced _ _ Hbaseline2 eq_refl).
    + exact (baseline_nested_balanced _ _ Hbaseline3 eq_refl).
    + exact (IHHbaseline4 eq_refl).
    + exact (IHHbaseline5 eq_refl).
  - eapply conditional_access_closed_lifo; [| | | | | exact Hentry].
    + exact (baseline_nested_balanced _ _ Hbaseline1 eq_refl).
    + apply access_neutral_balanced. assumption.
    + apply access_neutral_balanced. assumption.
    + exact (IHHbaseline2 eq_refl).
    + exact (IHHbaseline3 eq_refl).
Qed.

(** In the focused one-marker traversal, an unfold-free sequence has only
    two possible handoff points: either its first child preserves the focused
    marker, or that child consumes it.  This is the structural dichotomy used
    by the recursive normalizer; in particular, callers never inspect the
    implementation of [lifo_certificate] or redo its length arithmetic. *)
Lemma unfold_free_lifo_sequence_middle_boundary
    {Γ entry first middle second exit marker tail stack_middle}
    (first_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry first middle)
    (second_certificate : GenericRegions.Atomicity.analysis_certificate Γ
      middle second exit)
    (Hfirst_free : unfold_free first)
    (Hsecond_free : unfold_free second)
    (Hfirst : GenericRegions.Atomicity.lifo_certificate first_certificate
      (marker :: tail) stack_middle)
    (Hsecond : GenericRegions.Atomicity.lifo_certificate second_certificate
      stack_middle tail) :
  stack_middle = marker :: tail \/ stack_middle = tail.
Proof.
  pose proof (unfold_free_lifo_length_le first_certificate _ _
    Hfirst_free Hfirst) as Hfirst_length.
  pose proof (unfold_free_lifo_length_le second_certificate _ _
    Hsecond_free Hsecond) as Hsecond_length.
  destruct (Nat.eq_dec (length stack_middle) (S (length tail))) as
    [Hpreserved | Hnot_preserved].
  - left. apply unfold_free_lifo_same_length with first_certificate;
      assumption.
  - right.
    simpl in Hfirst_length.
    assert (Hclosed : length tail = length stack_middle) by lia.
    symmetry. apply unfold_free_lifo_same_length with second_certificate;
      assumption.
Qed.

(** A fold that shortens the focused stack is necessarily the matching fold,
    not the fresh-invariant-allocation alternative of the analyzer rule. *)
Lemma lifo_fold_consumes_focused_marker
    {Γ state invariant arguments}
    {focused : inv_id} {outer_open : gset inv_id}
    {tail : list GenericRegions.Atomicity.access_marker}
    (Hlifo : GenericRegions.Atomicity.lifo_certificate
      (GenericRegions.Atomicity.CertFold Γ state
        (TFold invariant arguments) invariant eq_refl)
      ((focused, outer_open) :: tail) tail) :
  invariant = focused.
Proof.
  simpl in Hlifo.
  destruct Hlifo as
    [(observed_outer & Hstack & _)|[Hstack _]].
  - congruence.
  - apply (f_equal (@length _)) in Hstack. simpl in Hstack. lia.
Qed.

Lemma unfold_free_balanced_structured {Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      Γ entry statement exit) stack :
  unfold_free statement ->
  GenericRegions.Atomicity.lifo_certificate certificate stack stack ->
  structured_certificate Γ entry statement exit.
Proof.
  revert stack.
  induction certificate; intros stack Hfree Hlifo; simpl in *.
  - econstructor; eauto.
  - eapply StructuredDone. exact e.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hfree. contradiction.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    destruct (decide
      (invariant ∈ GenericRegions.Atomicity.analysis_open state)) as
      [Hmember|Hfresh].
    + exfalso. destruct Hlifo as
        [(outer & Hcons & _)|[_ Hnot_member]].
      * apply (f_equal (@length _)) in Hcons. simpl in Hcons. lia.
      * exact (Hnot_member Hmember).
    + apply StructuredFreshFold. exact Hfresh.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree. destruct Hfree as [Hfirst_free Hsecond_free].
    destruct (constructive_indefinite_description _ Hlifo) as
      (stack_middle & Hfirst & Hsecond).
    pose proof (unfold_free_lifo_length_le certificate1 _ _
      Hfirst_free Hfirst) as Hfirst_le.
    pose proof (unfold_free_lifo_length_le certificate2 _ _
      Hsecond_free Hsecond) as Hsecond_le.
    assert (Hmiddle_length : length stack_middle = length stack) by lia.
    pose proof (unfold_free_lifo_same_length certificate1 _ _
      Hfirst_free Hfirst Hmiddle_length) as Hmiddle.
    subst stack_middle. eapply StructuredSequence.
    + apply (IHcertificate1 stack); assumption.
    + apply (IHcertificate2 stack); assumption.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    all: cbn in Hfree. all: destruct Hfree as [Hthen_free Helse_free].
    all: first [eapply StructuredConditional | eapply StructuredGhostConditional];
      eauto using (proj1 Hlifo), (proj2 Hlifo).
  - destruct statement; cbn in e; try discriminate; inversion e; subst; clear e.
    cbn in Hfree. eapply StructuredAtomic; eauto using (proj1 Hlifo).
  - destruct statement; cbn in e; try discriminate.
    injection e as Hd Hscope_body. subst d.
    apply Eqdep.EqdepTheory.inj_pair2 in Hscope_body. subst body.
    cbn in Hfree. apply StructuredGhostVal.
    apply (IHcertificate stack); assumption.
Qed.

(** Footprint-preserving form used by the public dispatcher.  The older
    projection above remains useful to low-level callers that need only a
    structured certificate. *)
Record balanced_structured_result {Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      Γ entry statement exit) : Type := {
  balanced_structured_certificate :
    structured_certificate Γ entry statement exit;
  balanced_structured_footprint :
    structured_certificate_footprint balanced_structured_certificate ⊆
    GenericRegions.Atomicity.certificate_footprint certificate;
  balanced_structured_safe :
    structured_accesses_outside_atomic balanced_structured_certificate;
}.

#[global] Arguments balanced_structured_certificate {_ _ _ _ _} _.
#[global] Arguments balanced_structured_footprint {_ _ _ _ _} _ _ _.
#[global] Arguments balanced_structured_safe {_ _ _ _ _} _.

Lemma unfold_free_balanced_structured_result
    {Γ entry statement exit}
    (certificate : GenericRegions.Atomicity.analysis_certificate
      Γ entry statement exit) stack :
  unfold_free statement ->
  GenericRegions.Atomicity.lifo_certificate certificate stack stack ->
  balanced_structured_result certificate.
Proof.
  revert stack.
  induction certificate; intros stack Hfree Hlifo; simpl in *.
  - refine {| balanced_structured_certificate := StructuredLeaf Γ state
        statement exit e e0 |}.
    intros invariant Hmember. exact Hmember.
    exact I.
  - refine {| balanced_structured_certificate := StructuredDone Γ state
        statement e |}.
    intros invariant Hmember. exact Hmember.
    exact I.
  - destruct statement; cbn in e; try discriminate.
    cbn in Hfree. contradiction.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    destruct (decide
      (invariant ∈ GenericRegions.Atomicity.analysis_open state)) as
      [Hmember|Hfresh].
    + exfalso. destruct Hlifo as
        [(outer & Hcons & _)|[_ Hnot_member]].
      * apply (f_equal (@length _)) in Hcons. simpl in Hcons. lia.
      * exact (Hnot_member Hmember).
    + refine {| balanced_structured_certificate :=
          StructuredFreshFold Γ state invariant arguments Hfresh |}.
      intros candidate Hcandidate. exact Hcandidate.
      exact I.
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree. destruct Hfree as [Hfirst_free Hsecond_free].
    destruct (constructive_indefinite_description _ Hlifo) as
      (stack_middle & Hfirst & Hsecond).
    pose proof (unfold_free_lifo_length_le certificate1 _ _
      Hfirst_free Hfirst) as Hfirst_le.
    pose proof (unfold_free_lifo_length_le certificate2 _ _
      Hsecond_free Hsecond) as Hsecond_le.
    assert (Hmiddle_length : length stack_middle = length stack) by lia.
    pose proof (unfold_free_lifo_same_length certificate1 _ _
      Hfirst_free Hfirst Hmiddle_length) as Hmiddle.
    subst stack_middle.
    pose (first_result := IHcertificate1 stack Hfirst_free Hfirst).
    pose (second_result := IHcertificate2 stack Hsecond_free Hsecond).
    refine {| balanced_structured_certificate :=
        StructuredSequence Γ state first middle second exit
          first_result.(balanced_structured_certificate)
          second_result.(balanced_structured_certificate) |}.
    intros invariant Hmember.
    simpl in Hmember |- *.
    repeat rewrite elem_of_union in Hmember |- *.
    pose proof (first_result.(balanced_structured_footprint) invariant) as
      Hfirst_subset.
    pose proof (second_result.(balanced_structured_footprint) invariant) as
      Hsecond_subset.
    tauto.
    split; [exact first_result.(balanced_structured_safe) |
      exact second_result.(balanced_structured_safe)].
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    all: cbn in Hfree. all: destruct Hfree as [Hthen_free Helse_free].
    all: pose (then_result := IHcertificate1 stack Hthen_free (proj1 Hlifo)).
    all: pose (else_result := IHcertificate2 stack Helse_free (proj2 Hlifo)).
    + refine {| balanced_structured_certificate :=
        StructuredConditional Γ state condition then_branch else_branch
          then_exit else_exit then_result.(balanced_structured_certificate)
          else_result.(balanced_structured_certificate) e0 e1 |}.
      * intros invariant Hmember.
        simpl in Hmember |- *.
        repeat rewrite elem_of_union in Hmember |- *.
        pose proof (then_result.(balanced_structured_footprint) invariant) as
          Hthen_subset.
        pose proof (else_result.(balanced_structured_footprint) invariant) as
          Helse_subset.
        tauto.
      * split; [exact then_result.(balanced_structured_safe) |
          exact else_result.(balanced_structured_safe)].
    + refine {| balanced_structured_certificate :=
        StructuredGhostConditional Γ state condition then_branch else_branch
          then_exit else_exit then_result.(balanced_structured_certificate)
          else_result.(balanced_structured_certificate) e0 e1 |}.
      * intros invariant Hmember.
        simpl in Hmember |- *.
        repeat rewrite elem_of_union in Hmember |- *.
        pose proof (then_result.(balanced_structured_footprint) invariant) as
          Hthen_subset.
        pose proof (else_result.(balanced_structured_footprint) invariant) as
          Helse_subset.
        tauto.
      * split; [exact then_result.(balanced_structured_safe) |
          exact else_result.(balanced_structured_safe)].
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    cbn in Hfree.
    pose (body_result := IHcertificate stack Hfree (proj1 Hlifo)).
    refine {| balanced_structured_certificate :=
        StructuredAtomic Γ state body outer inner e0
          body_result.(balanced_structured_certificate) e1 |}.
    intros invariant Hmember.
    simpl in Hmember |- *.
    repeat rewrite elem_of_union in Hmember |- *.
    pose proof (body_result.(balanced_structured_footprint) invariant) as
      Hbody_subset.
    destruct Hmember as
      [[[[Hentry_mask | Hentry_open] | Hexit_mask] | Hexit_open] | Hbody].
    + simpl. repeat rewrite elem_of_union. tauto.
    + simpl. repeat rewrite elem_of_union. tauto.
    + simpl. repeat rewrite elem_of_union. tauto.
    + simpl. repeat rewrite elem_of_union. tauto.
    + specialize (Hbody_subset Hbody). simpl. tauto.
    + exact body_result.(balanced_structured_safe).
  - destruct statement; cbn in e; try discriminate.
    injection e as Hd Hscope_body. subst d.
    apply Eqdep.EqdepTheory.inj_pair2 in Hscope_body. subst body.
    cbn in Hfree.
    pose (body_result := IHcertificate stack Hfree Hlifo).
    refine {| balanced_structured_certificate :=
        StructuredGhostVal Γ state name t initializer _ exit
          body_result.(balanced_structured_certificate) |}.
    intros invariant Hmember.
    simpl in Hmember |- *.
    repeat rewrite elem_of_union in Hmember |- *.
    pose proof (body_result.(balanced_structured_footprint) invariant) as
      Hbody_subset.
    tauto.
    exact body_result.(balanced_structured_safe).
Defined.

End WithSignature.
End NormalizationBase.
