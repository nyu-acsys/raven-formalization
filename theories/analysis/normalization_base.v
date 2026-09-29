From Coq Require Import ClassicalEpsilon FunctionalExtensionality Lia
  Program.Equality.
From stdpp Require Import gmap sets.

From raven Require Import runtime.erasure analysis.structured_certificates verification.expressions analysis.atomicity verification.assertions verification.ir soundness.runtime_model.

(** Certified source-to-source normalization for typed Raven programs. *)
Module NormalizationBase.

Module Hoare := Runtime.Validation.Hoare.
Module Assertions := Runtime.Translation.Assertions.
Module Core := Runtime.Core.
Module IR := Runtime.IR.
Module GenericRegions := Runtime.GenericRegions.
Import Core IR Runtime IR Core Runtime.Translation.
Import StructuredCertificates.

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
  | TIf _ then_branch else_branch =>
      unfold_free then_branch /\ unfold_free else_branch
  | TSeq first second => unfold_free first /\ unfold_free second
  | _ => True
  end.

Fixpoint access_neutral {Γ} (statement : stmt Γ) : Prop :=
  match statement with
  | TUnfold _ _ | TFold _ _ => False
  | TInvAccess _ _ body | TAtomic body => access_neutral body
  | TGhostVal _ _ _ body => access_neutral body
  | TIf _ then_branch else_branch =>
      access_neutral then_branch /\ access_neutral else_branch
  | TSeq first second => access_neutral first /\ access_neutral second
  | _ => True
  end.

(** Syntactic acceptance certificate for the first end-to-end normalizer.
    It records only the deliberately supported source layouts; it is not an
    execution semantics or a second interpretation of statements.  The
    analyzer certificate remains responsible for all LIFO and atomic-step
    facts, while assertion alignment recovers invariant instances. *)
Inductive baseline_normalizable {Γ} : stmt Γ -> Type :=
| BaselineUnfoldFree statement :
    unfold_free statement -> baseline_normalizable statement
| BaselineSequence first second :
    access_neutral first ->
    baseline_normalizable second ->
    baseline_normalizable (TSeq first second)
| BaselineBalancedSequence first second :
    baseline_normalizable first ->
    baseline_normalizable second ->
    baseline_normalizable (TSeq first second)
| BaselineConditional condition then_branch else_branch :
    baseline_normalizable then_branch ->
    baseline_normalizable else_branch ->
    baseline_normalizable (TIf condition then_branch else_branch)
| BaselineTerminalAccess
    invariant opening_arguments closing_arguments body :
    access_neutral body ->
    opening_arguments = closing_arguments ->
    pexpr_list_dependencies opening_arguments ## statement_writes body ->
    baseline_normalizable
      (TSeq (TUnfold invariant opening_arguments)
        (TSeq body
          (TFold invariant closing_arguments)))
| BaselineAccessThen
    invariant opening_arguments closing_arguments
    body work :
    access_neutral body ->
    opening_arguments = closing_arguments ->
    pexpr_list_dependencies opening_arguments ## statement_writes body ->
    baseline_normalizable work ->
    baseline_normalizable
      (TSeq (TUnfold invariant opening_arguments)
        (TSeq body
          (TSeq
            (TFold invariant closing_arguments) work)))
| BaselineGhostVal name t initializer body :
    @baseline_normalizable (ghost_val t :: Γ) body ->
    baseline_normalizable (TGhostVal name t initializer body).

(** Executable recognizers for the source-shape portion of the restricted
    analysis.  Argument stability and write effects are intentionally not
    decided here: Step 3 enriches the access stack with precisely that
    information. *)
Fixpoint unfold_freeb {Γ} (statement : stmt Γ) : bool :=
  match statement with
  | TUnfold _ _ => false
  | TInvAccess _ _ body | TAtomic body => unfold_freeb body
  | TGhostVal _ _ _ body => unfold_freeb body
  | TIf _ then_branch else_branch =>
      unfold_freeb then_branch && unfold_freeb else_branch
  | TSeq first second => unfold_freeb first && unfold_freeb second
  | _ => true
  end.

Fixpoint access_neutralb {Γ} (statement : stmt Γ) : bool :=
  match statement with
  | TUnfold _ _ | TFold _ _ => false
  | TInvAccess _ _ body | TAtomic body => access_neutralb body
  | TGhostVal _ _ _ body => access_neutralb body
  | TIf _ then_branch else_branch =>
      access_neutralb then_branch && access_neutralb else_branch
  | TSeq first second => access_neutralb first && access_neutralb second
  | _ => true
  end.

(** Conservative executable check for the source layouts handled by the
    baseline normalizer.  A raw unfold is accepted only when its enclosing
    sequence exposes the matching fold and an access-neutral body.  The
    equality test is only for invariant identities; argument compatibility
    is deliberately deferred to the effect-aware pass. *)
Fixpoint restricted_fragment_shape_check {Γ} (statement : stmt Γ) : bool :=
  match statement with
  | TUnfold _ _ => false
  | TInvAccess _ _ body | TAtomic body => unfold_freeb body
  | TGhostVal _ _ _ body => restricted_fragment_shape_check body
  | TIf _ then_branch else_branch =>
      restricted_fragment_shape_check then_branch &&
        restricted_fragment_shape_check else_branch
  | TSeq first second =>
      match first, second with
      | TUnfold opening_invariant _,
          TSeq body (TFold closing_invariant _) =>
          bool_decide (opening_invariant = closing_invariant) &&
            access_neutralb body
      | TUnfold opening_invariant _,
          TSeq body (TSeq (TFold closing_invariant _) work) =>
          bool_decide (opening_invariant = closing_invariant) &&
            access_neutralb body && restricted_fragment_shape_check work
      | _, _ =>
          restricted_fragment_shape_check first &&
            restricted_fragment_shape_check second
      end
  | _ => true
  end.

Definition restricted_fragment_shape {Γ} (statement : stmt Γ) : Prop :=
  restricted_fragment_shape_check statement = true.

(** Executable key for the first conservative argument fragment.  Requiring
    every invariant argument to be a stack variable makes equality reduce to
    ordinary list equality and avoids proof-generated dependent transports.
    Literal and compound keys can be added later without changing callers. *)
Fixpoint restricted_argument_variable_indices {keep Γ ts}
    (expressions : pexpr_list keep Γ ts) : option (list nat) :=
  match expressions with
  | PENil => Some []
  | PECons expression tail =>
      match expression, restricted_argument_variable_indices tail with
      | PEVar variable, Some indices =>
          Some (lvar_index variable :: indices)
      | _, _ => None
      end
  end.

Definition restricted_pexpr_list_eqb {keep Γ ts}
    (left right : pexpr_list keep Γ ts) : bool :=
  match restricted_argument_variable_indices left,
      restricted_argument_variable_indices right with
  | Some left_indices, Some right_indices =>
      bool_decide (left_indices = right_indices)
  | _, _ => false
  end.

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

Lemma restricted_argument_variable_indices_injective {keep Γ ts}
    (left right : pexpr_list keep Γ ts) indices :
  restricted_argument_variable_indices left = Some indices ->
  restricted_argument_variable_indices right = Some indices ->
  left = right.
Proof.
  revert right indices.
  induction left; intros right indices Hleft Hright;
    dependent destruction right.
  - cbn in Hleft, Hright. congruence.
  - cbn in Hleft, Hright.
    destruct p; try discriminate.
    destruct p0; try discriminate.
    destruct (restricted_argument_variable_indices left) as [left_indices|]
      eqn:Hleft_indices; try discriminate.
    destruct (restricted_argument_variable_indices right) as [right_indices|]
      eqn:Hright_indices; try discriminate.
    inversion Hleft; inversion Hright; subst.
    f_equal.
    + f_equal. apply lvar_index_injective. congruence.
    + eapply IHleft; [reflexivity|].
      rewrite Hright_indices. f_equal. congruence.
Qed.

Lemma restricted_pexpr_list_eqb_sound {keep Γ ts}
    (left right : pexpr_list keep Γ ts) :
  restricted_pexpr_list_eqb left right = true -> left = right.
Proof.
  unfold restricted_pexpr_list_eqb.
  destruct (restricted_argument_variable_indices left) as [left_indices|]
    eqn:Hleft; try discriminate.
  destruct (restricted_argument_variable_indices right) as [right_indices|]
    eqn:Hright; try discriminate.
  intro Hequal. apply bool_decide_eq_true in Hequal. subst right_indices.
  eapply restricted_argument_variable_indices_injective; eauto.
Qed.

Definition restricted_access_boundary_check {Γ invariant}
    (opening_arguments closing_arguments :
      gexpr_list Γ (Assertion.invariant_args invariant))
    (body : stmt Γ) : bool :=
  restricted_pexpr_list_eqb opening_arguments closing_arguments &&
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
  - now apply restricted_pexpr_list_eqb_sound.
  - now apply bool_decide_eq_true in Hwrites.
Qed.

(** Effect-only component of the restricted pass.  Structural admissibility
    remains the independent executable decision above. *)
Fixpoint restricted_access_effect_check {Γ} (statement : stmt Γ) : bool :=
  match statement with
  | TInvAccess _ _ body | TAtomic body => restricted_access_effect_check body
  | TGhostVal _ _ _ body => restricted_access_effect_check body
  | TIf _ then_branch else_branch =>
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
                  closing_arguments _ (eq_sym Heq)) body
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
                restricted_access_effect_check work
          | right _ => false
          end
      | _, _ =>
          restricted_access_effect_check first &&
            restricted_access_effect_check second
      end
  | _ => true
  end.

Definition restricted_fragment_check {Γ} (statement : stmt Γ) : bool :=
  restricted_fragment_shape_check statement &&
    restricted_access_effect_check statement.

Definition restricted_fragment_accepted {Γ} (statement : stmt Γ) : Prop :=
  restricted_fragment_check statement = true.

Fixpoint normalization_statement_size {Γ} (statement : stmt Γ) : nat :=
  match statement with
  | TInvAccess _ _ body | TAtomic body =>
      S (normalization_statement_size body)
  | TGhostVal _ _ _ body => S (normalization_statement_size body)
  | TIf _ then_branch else_branch | TSeq then_branch else_branch =>
      S (normalization_statement_size then_branch +
        normalization_statement_size else_branch)
  | _ => 1
  end.

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
                  then Some (TInvAccess opening_invariant opening_arguments body)
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
                    match restricted_normalize_statement_fuel fuel' work with
                    | Some normalized_work =>
                        Some (TSeq
                          (TInvAccess opening_invariant opening_arguments body)
                          normalized_work)
                    | None => None
                    end
                  else None
              | right _ => None
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

(** The executable shape check is sound for the existing proof-producing
    baseline grammar.  Thus later strengthening it with effects can only
    reject programs; it cannot admit a source layout unsupported by the
    normalization theorem. *)
Lemma restricted_fragment_shape_check_sound {Γ} (statement : stmt Γ) :
  restricted_fragment_shape statement ->
  restricted_access_effect_check statement = true ->
  baseline_normalizable statement.
Proof.
  enough (Hsized : forall n Γ (current : stmt Γ),
    normalization_statement_size current < n ->
    restricted_fragment_shape current ->
    restricted_access_effect_check current = true ->
    baseline_normalizable current) by eauto.
  intros n. induction n as [|n IHn];
    intros Γ' current Hsize Hcheck Heffects; [lia|].
  assert (IH : forall Γ'' (smaller : stmt Γ''),
    normalization_statement_size smaller <
      normalization_statement_size current ->
    restricted_fragment_shape smaller ->
    restricted_access_effect_check smaller = true ->
    baseline_normalizable smaller).
  { intros Γ'' smaller Hsmaller. apply IHn. lia. }
  clear IHn Hsize.
  destruct current; cbn [restricted_fragment_shape
    restricted_fragment_shape_check] in Hcheck |- *;
    try (apply BaselineUnfoldFree; cbn; done).
  - apply BaselineUnfoldFree. cbn.
    apply unfold_freeb_spec. exact Hcheck.
  - apply Bool.andb_true_iff in Hcheck as [Hthen Helse].
    apply Bool.andb_true_iff in Heffects as [Hthen_effects Helse_effects].
    apply BaselineConditional.
    + apply IH; [unfold ltof; cbn; lia | exact Hthen | exact Hthen_effects].
    + apply IH; [unfold ltof; cbn; lia | exact Helse | exact Helse_effects].
  - destruct current1; unfold restricted_fragment_shape in Hcheck;
      cbn in Hcheck, Heffects.
    all: try (apply Bool.andb_true_iff in Heffects as
      [Hfirst_effects Hsecond_effects]).
    all: try (apply BaselineSequence;
      [cbn; tauto | apply IH;
        [unfold ltof; cbn; lia | exact Hcheck |
         first [exact Hsecond_effects | exact Heffects]]]).
    2: apply BaselineBalancedSequence;
      [apply BaselineUnfoldFree; cbn; exact I |
       apply IH; [unfold ltof; cbn; lia | exact Hcheck |
         first [exact Hsecond_effects | exact Heffects]]].
    all: try (apply Bool.andb_true_iff in Hcheck as [Hfirst Hsecond]).
    2: apply BaselineBalancedSequence.
    2: apply BaselineUnfoldFree; cbn; apply unfold_freeb_spec; exact Hfirst.
    2: apply IH; [unfold ltof; cbn; lia | exact Hsecond |
      first [exact Hsecond_effects | exact Heffects]].
    2: apply Bool.andb_true_iff in Hfirst as [Hthen Helse].
    2: apply Bool.andb_true_iff in Hfirst_effects as
      [Hthen_effects Helse_effects].
    2: apply BaselineBalancedSequence.
    2: apply BaselineConditional.
    2: apply IH; [unfold ltof; cbn; lia | exact Hthen | exact Hthen_effects].
    2: apply IH; [unfold ltof; cbn; lia | exact Helse | exact Helse_effects].
    2: apply IH; [unfold ltof; cbn; lia | exact Hsecond |
      first [exact Hsecond_effects | exact Heffects]].
    2: apply BaselineBalancedSequence.
    2: apply IH; [unfold ltof; cbn; lia | exact Hfirst | exact Hfirst_effects].
    2: apply IH; [unfold ltof; cbn; lia | exact Hsecond |
      first [exact Hsecond_effects | exact Heffects]].
    2: apply BaselineBalancedSequence.
    2: apply BaselineUnfoldFree; cbn; apply unfold_freeb_spec; exact Hfirst.
    2: apply IH; [unfold ltof; cbn; lia | exact Hsecond |
      first [exact Hsecond_effects | exact Heffects]].
    destruct current2; cbn in Hcheck; try discriminate.
    destruct current2_2; cbn in Hcheck; try discriminate.
    1: apply Bool.andb_true_iff in Hcheck as [Hinvariant Hbody];
      apply bool_decide_eq_true in Hinvariant. subst invariant0.
      apply access_neutralb_spec in Hbody.
      destruct (decide (invariant = invariant) : Decision (invariant = invariant))
        as [Heq|Hneq]; last contradiction.
      replace Heq with (@eq_refl inv_id invariant) in Heffects
        by apply ProofIrrelevance.proof_irrelevance.
      cbn in Heffects.
      apply restricted_access_boundary_check_sound in Heffects as
        [Harguments Hdisjoint].
      apply BaselineTerminalAccess; assumption.
    destruct current2_2_1; cbn in Hcheck; try discriminate.
    apply Bool.andb_true_iff in Hcheck as [Hprefix Hwork].
    apply Bool.andb_true_iff in Hprefix as [Hinvariant Hbody].
    apply bool_decide_eq_true in Hinvariant. subst invariant0.
    apply access_neutralb_spec in Hbody.
    destruct (decide (invariant = invariant) : Decision (invariant = invariant))
      as [Heq|Hneq]; last contradiction.
    replace Heq with (@eq_refl inv_id invariant) in Heffects
      by apply ProofIrrelevance.proof_irrelevance.
    cbn in Heffects.
    apply Bool.andb_true_iff in Heffects as [Hboundary Hwork_effects].
    apply restricted_access_boundary_check_sound in Hboundary as
      [Harguments Hdisjoint].
    apply BaselineAccessThen; [exact Hbody | exact Harguments | exact Hdisjoint |].
    apply IH; [unfold ltof; cbn; lia | exact Hwork | exact Hwork_effects].
    apply BaselineBalancedSequence.
    + apply IH; [unfold ltof; cbn; lia | exact Hfirst | exact Hfirst_effects].
    + apply IH; [unfold ltof; cbn; lia | exact Hsecond | exact Hsecond_effects].
  - apply BaselineUnfoldFree. cbn.
    apply unfold_freeb_spec. exact Hcheck.
  - apply BaselineGhostVal.
    apply IH; [unfold ltof; cbn; lia | exact Hcheck | exact Heffects].
Qed.

Corollary restricted_fragment_check_sound {Γ} (statement : stmt Γ) :
  restricted_fragment_accepted statement -> baseline_normalizable statement.
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
Qed.

Lemma restricted_normalize_terminal_access {Γ} fuel
    invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (body : stmt Γ) :
  restricted_access_boundary_check arguments arguments body = true ->
  restricted_normalize_statement_fuel (S fuel)
    (TSeq (TUnfold invariant arguments)
      (TSeq body (TFold invariant arguments))) =
    Some (TInvAccess invariant arguments body).
Proof.
  intro Hboundary. cbn [restricted_normalize_statement_fuel].
  destruct (decide (invariant = invariant)) as [Heq | Hneq];
    [| contradiction].
  replace Heq with (@eq_refl inv_id invariant) by apply ProofIrrelevance.proof_irrelevance.
  cbn. now rewrite Hboundary.
Qed.

Lemma restricted_normalize_continued_access {Γ} fuel
    invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (body work normalized_work : stmt Γ) :
  restricted_access_boundary_check arguments arguments body = true ->
  restricted_normalize_statement_fuel fuel work = Some normalized_work ->
  restricted_normalize_statement_fuel (S fuel)
    (TSeq (TUnfold invariant arguments)
      (TSeq body
        (TSeq (TFold invariant arguments)
          work))) =
    Some (TSeq (TInvAccess invariant arguments body)
      normalized_work).
Proof.
  intros Hboundary Hwork. cbn [restricted_normalize_statement_fuel].
  destruct (decide (invariant = invariant)) as [Heq | Hneq];
    [| contradiction].
  replace Heq with (@eq_refl inv_id invariant) by apply ProofIrrelevance.proof_irrelevance.
  cbn. now rewrite Hboundary, Hwork.
Qed.

Lemma restricted_terminal_access_accepted_inv {Γ}
    invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (body : stmt Γ) :
  restricted_fragment_accepted
    (TSeq (TUnfold invariant arguments)
      (TSeq body (TFold invariant arguments))) ->
  access_neutral body /\
    restricted_access_boundary_check arguments arguments body = true.
Proof.
  unfold restricted_fragment_accepted, restricted_fragment_check.
  cbn [restricted_fragment_shape_check restricted_access_effect_check].
  destruct (decide (invariant = invariant)) as [Heq | Hneq];
    [| contradiction].
  replace Heq with (@eq_refl inv_id invariant) by apply ProofIrrelevance.proof_irrelevance.
  rewrite bool_decide_true; [| reflexivity].
  cbn. rewrite !Bool.andb_true_iff.
  intros [Hneutral Hboundary]. split.
  - now apply access_neutralb_spec.
  - exact Hboundary.
Qed.

Lemma restricted_continued_access_accepted_inv {Γ}
    invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (body work : stmt Γ) :
  restricted_fragment_accepted
    (TSeq (TUnfold invariant arguments)
      (TSeq body
        (TSeq (TFold invariant arguments)
          work))) ->
  access_neutral body /\
    restricted_access_boundary_check arguments arguments body = true /\
    restricted_fragment_accepted work.
Proof.
  unfold restricted_fragment_accepted, restricted_fragment_check.
  cbn [restricted_fragment_shape_check restricted_access_effect_check].
  destruct (decide (invariant = invariant)) as [Heq | Hneq];
    [| contradiction].
  replace Heq with (@eq_refl inv_id invariant) by apply ProofIrrelevance.proof_irrelevance.
  cbn. rewrite !Bool.andb_true_iff.
  intros [[[_ Hneutral] Hwork_shape] [Hboundary Hwork_effect]].
  split; [now apply access_neutralb_spec|].
  split; [exact Hboundary|].
  split; assumption.
Qed.

Lemma access_neutral_effect_check {Γ} (statement : stmt Γ) :
  access_neutral statement ->
  restricted_access_effect_check statement = true.
Proof.
  induction statement; cbn [access_neutral restricted_access_effect_check];
    intros Hneutral; try contradiction; try reflexivity.
  - now rewrite IHstatement.
  - destruct Hneutral as [Hthen Helse].
    now rewrite IHstatement1, IHstatement2.
  - destruct Hneutral as [Hfirst Hsecond].
    pose proof (IHstatement1 Hfirst) as Hcheck1.
    pose proof (IHstatement2 Hsecond) as Hcheck2.
    destruct statement1; cbn [access_neutral] in Hfirst.
    all: try contradiction.
    all: try (cbn [restricted_access_effect_check] in Hcheck1 |- *;
      rewrite Hcheck1, Hcheck2; reflexivity).
    all: rewrite Hcheck2; exact Hcheck1.
  - now rewrite IHstatement.
  - exact (IHstatement Hneutral).
Qed.

Lemma access_neutral_sequence_effect_check {Γ}
    (first second : stmt Γ) :
  access_neutral first ->
  restricted_access_effect_check (TSeq first second) =
    (restricted_access_effect_check first &&
      restricted_access_effect_check second).
Proof.
  intro Hneutral.
  destruct first; cbn [access_neutral] in Hneutral;
    try contradiction;
    reflexivity.
Qed.

(** Successful admission is sufficient for the proof-irrelevant normalizer
    to produce a target at its private size bound.  This is the first local
    correctness fact for the combined pass: later certificate construction
    may consume the returned statement without evaluating Hoare or alignment
    evidence. *)
Lemma restricted_normalize_statement_succeeds_with_fuel {Γ}
    (statement : stmt Γ) fuel :
  restricted_fragment_accepted statement ->
  normalization_statement_size statement < fuel ->
  exists normalized,
    restricted_normalize_statement_fuel fuel statement = Some normalized.
Proof.
  revert fuel.
  enough (Hsized : forall n Γ (current : stmt Γ),
    normalization_statement_size current < n -> forall fuel,
    restricted_fragment_accepted current ->
    normalization_statement_size current < fuel ->
    exists normalized,
      restricted_normalize_statement_fuel fuel current = Some normalized)
    by eauto.
  intros n. induction n as [|n IHn];
    intros Γ' current Hsize fuel Haccepted Hfuel; [lia|].
  assert (IH : forall Γ'' (smaller : stmt Γ''),
    normalization_statement_size smaller <
      normalization_statement_size current -> forall fuel,
    restricted_fragment_accepted smaller ->
    normalization_statement_size smaller < fuel ->
    exists normalized,
      restricted_normalize_statement_fuel fuel smaller = Some normalized).
  { intros Γ'' smaller Hsmaller. apply IHn. lia. }
  clear IHn Hsize.
  destruct fuel as [|fuel]; [cbn in Hfuel; lia|].
  unfold restricted_fragment_accepted, restricted_fragment_check in Haccepted.
  apply Bool.andb_true_iff in Haccepted as [Hshape Heffect].
  destruct current.
  all: cbn [restricted_fragment_shape_check
    restricted_access_effect_check normalization_statement_size]
    in Hshape, Heffect, Hfuel.
  all: try discriminate.
  all: try (eexists; reflexivity).
  - apply unfold_freeb_spec in Hshape.
    destruct (unfold_free_normalize_statement_succeeds_with_fuel current fuel
      Hshape ltac:(lia)) as [normalized Hnormalized].
    change (exists normalized0,
      match restricted_normalize_statement_fuel fuel current with
      | Some normalized_body =>
          Some (TInvAccess invariant arguments normalized_body)
      | None => None
      end = Some normalized0).
    rewrite Hnormalized. eexists; reflexivity.
  - apply Bool.andb_true_iff in Hshape as [Hshape1 Hshape2].
    apply Bool.andb_true_iff in Heffect as [Heffect1 Heffect2].
    destruct (IH _ current1 ltac:(cbn; lia) fuel
      ltac:(unfold restricted_fragment_accepted, restricted_fragment_check;
        apply Bool.andb_true_iff; auto) ltac:(lia)) as
      [normalized1 Hnormalized1].
    destruct (IH _ current2 ltac:(cbn; lia) fuel
      ltac:(unfold restricted_fragment_accepted, restricted_fragment_check;
        apply Bool.andb_true_iff; auto) ltac:(lia)) as
      [normalized2 Hnormalized2].
    change (exists normalized,
      match restricted_normalize_statement_fuel fuel current1 with
      | Some normalized_then =>
          match restricted_normalize_statement_fuel fuel current2 with
          | Some normalized_else =>
              Some (TIf condition normalized_then normalized_else)
          | None => None
          end
      | None => None
      end = Some normalized).
    rewrite Hnormalized1, Hnormalized2. eexists; reflexivity.
  - destruct current1.
    all: try (apply Bool.andb_true_iff in Hshape as [Hshape1 Hshape2];
      apply Bool.andb_true_iff in Heffect as [Heffect1 Heffect2];
      match goal with
      | |- context [TSeq ?first ?second] =>
          destruct (IH _ first ltac:(cbn; lia) fuel
            ltac:(unfold restricted_fragment_accepted,
              restricted_fragment_check;
              apply Bool.andb_true_iff; auto) ltac:(lia)) as
            [normalized1 Hnormalized1];
          destruct (IH _ second ltac:(cbn; lia) fuel
            ltac:(unfold restricted_fragment_accepted,
              restricted_fragment_check;
              apply Bool.andb_true_iff; auto) ltac:(lia)) as
            [normalized2 Hnormalized2];
          cbn [restricted_normalize_statement_fuel];
          rewrite Hnormalized1, Hnormalized2;
          eexists; reflexivity
      end).
    destruct current2; cbn [restricted_fragment_shape_check
      restricted_access_effect_check] in Hshape, Heffect |- *;
      try discriminate.
    destruct current2_2; cbn [restricted_fragment_shape_check
      restricted_access_effect_check] in Hshape, Heffect |- *;
      try discriminate.
    + apply Bool.andb_true_iff in Hshape as [Hinvariant _].
      apply bool_decide_eq_true in Hinvariant. subst invariant0.
      destruct (decide (invariant = invariant)) as [Heq | Hneq];
        [|contradiction].
      replace Heq with (@eq_refl inv_id invariant) in Heffect |- *
        by apply ProofIrrelevance.proof_irrelevance.
      cbn in Heffect |- *.
      destruct (decide (invariant = invariant)) as [Heq0 | Hneq];
        [|contradiction].
      replace Heq0 with Heq by apply ProofIrrelevance.proof_irrelevance.
      rewrite Heffect. eexists; reflexivity.
    + destruct current2_2_1; cbn [restricted_fragment_shape_check
        restricted_access_effect_check] in Hshape, Heffect |- *;
        try discriminate.
      apply Bool.andb_true_iff in Hshape as [Hprefix Hwork_shape].
      apply Bool.andb_true_iff in Hprefix as [Hinvariant _].
      apply bool_decide_eq_true in Hinvariant. subst invariant0.
      destruct (decide (invariant = invariant)) as [Heq | Hneq];
        [|contradiction].
      replace Heq with (@eq_refl inv_id invariant) in Heffect
        by apply ProofIrrelevance.proof_irrelevance.
      cbn in Heffect.
      apply Bool.andb_true_iff in Heffect as [Hboundary Hwork_effect].
      assert (Hwork_accepted :
        restricted_fragment_accepted current2_2_2).
      { unfold restricted_fragment_accepted, restricted_fragment_check.
        apply Bool.andb_true_iff. split; assumption. }
      assert (Hwork_smaller : normalization_statement_size current2_2_2 <
        normalization_statement_size
          (TSeq (TUnfold invariant arguments)
            (TSeq current2_1
              (TSeq (TFold invariant arguments0)
                current2_2_2)))).
      { cbn. lia. }
      assert (Hwork_fuel :
        normalization_statement_size current2_2_2 < fuel).
      { cbn in Hfuel. lia. }
      destruct (IH _ current2_2_2 Hwork_smaller fuel Hwork_accepted Hwork_fuel)
        as [normalized_work Hwork].
      cbn [restricted_normalize_statement_fuel].
      destruct (decide (invariant = invariant)) as [Heq0 | Hneq];
        [|contradiction].
      replace Heq0 with Heq by apply ProofIrrelevance.proof_irrelevance.
      replace Heq with (@eq_refl inv_id invariant) by apply ProofIrrelevance.proof_irrelevance.
      cbn. rewrite Hboundary, Hwork. eexists; reflexivity.
  - apply unfold_freeb_spec in Hshape.
    destruct (unfold_free_normalize_statement_succeeds_with_fuel current fuel
      Hshape ltac:(lia)) as [normalized Hnormalized].
    change (exists normalized0,
      match restricted_normalize_statement_fuel fuel current with
      | Some normalized_body => Some (TAtomic normalized_body)
      | None => None
      end = Some normalized0).
    rewrite Hnormalized. eexists; reflexivity.
  - destruct (IH _ current ltac:(cbn; lia) fuel
      ltac:(unfold restricted_fragment_accepted, restricted_fragment_check;
        apply Bool.andb_true_iff; auto) ltac:(lia)) as
      [normalized Hnormalized].
    cbn [restricted_normalize_statement_fuel]. rewrite Hnormalized.
    eexists; reflexivity.
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
  - destruct statement; cbn in e; try discriminate; inversion e; subst.
    destruct Hneutral as [Hthen Helse]. split.
    + apply IHcertificate1. exact Hthen.
    + apply IHcertificate2. exact Helse.
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
    cbn in Hneutral. destruct Hneutral as [Hthen _].
    exact (IHcertificate1 Hthen).
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
    destruct Hfree as [Hthen Helse].
    destruct (IHcertificate1 Hthen Hclosed) as [Hlifo1 Hthen_closed].
    destruct (IHcertificate2 Helse Hclosed) as [Hlifo2 Helse_closed].
    split; [split; assumption|exact Hthen_closed].
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
    cbn in Hfree. destruct Hfree as [Hthen_free Helse_free].
    destruct Hlifo as [Hthen _]. eauto.
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
    cbn in Hfree. destruct Hfree as [Hthen_free _]. destruct Hlifo as [Hthen _].
    eauto.
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
Lemma baseline_normalizable_empty_output {Γ} (statement : stmt Γ)
    (Hbaseline : baseline_normalizable statement) :
  forall entry exit
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry statement exit) stack_out,
    GenericRegions.Atomicity.lifo_certificate certificate [] stack_out ->
    stack_out = [].
Proof.
  induction Hbaseline; intros entry exit certificate stack_out Hlifo.
  - pose proof (unfold_free_lifo_length_le certificate [] stack_out u Hlifo)
      as Hlength.
    destruct stack_out; [reflexivity|simpl in Hlength; lia].
  - dependent destruction certificate; try discriminate.
    cbn in e. inversion e; subst.
    destruct Hlifo as (middle_stack & Hfirst & Hsecond).
    assert (Hfirst_closed : GenericRegions.Atomicity.lifo_certificate
      certificate1 [] []).
    { apply access_neutral_lifo. exact a. }
    assert (Hmiddle : middle_stack = []).
    { eapply GenericRegions.Atomicity.lifo_certificate_functional;
        eassumption. }
    subst middle_stack.
    eapply IHHbaseline. exact Hsecond.
  - dependent destruction certificate; try discriminate.
    cbn in e. inversion e; subst.
    destruct Hlifo as (middle_stack & Hfirst & Hsecond).
    assert (Hmiddle : middle_stack = []) by eauto.
    subst middle_stack.
    eauto.
  - dependent destruction certificate; try discriminate.
    cbn in e. inversion e; subst.
    destruct Hlifo as [Hthen _]. eauto.
  - dependent destruction certificate; try discriminate.
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
    destruct Hlifo as (opened_stack & Hopen & Htail).
    destruct Htail as (body_stack & Hbody & Hfold).
    assert (Hbody_same : GenericRegions.Atomicity.lifo_certificate
      certificate2_1 opened_stack opened_stack).
    { apply access_neutral_lifo. exact a. }
    assert (Hbody_stack : body_stack = opened_stack).
    { eapply GenericRegions.Atomicity.lifo_certificate_functional;
        eassumption. }
    subst body_stack.
    unfold GenericRegions.Atomicity.lifo_certificate in Hfold.
    destruct Hfold as [(outer_open & Hstack & _)|[Hsame Hclosed]].
    + cbn in Hopen. congruence.
    + exfalso. apply Hclosed.
      match goal with
      | Htransition : GenericRegions.Atomicity.open_invariant ?opened_invariant
          ?opening_state = inr ?opened_state |- _ =>
          pose proof (GenericRegions.Atomicity.open_invariant_success
            opened_invariant opening_state opened_state Htransition) as
            (_ & _ & _ & Hopened);
          rewrite (access_neutral_preserves_open certificate2_1 a), Hopened;
          apply elem_of_union_l; apply elem_of_singleton_2; reflexivity
      end.
  - dependent destruction certificate; try discriminate.
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
    | Hfold_certificate : GenericRegions.Atomicity.analysis_certificate
        _ _ (TFold _ _) _ |- _ =>
        dependent destruction Hfold_certificate
    end; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TFold _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    destruct Hlifo as (opened_stack & Hopen & Htail).
    destruct Htail as (body_stack & Hbody & Hfold_work).
    assert (Hbody_same : GenericRegions.Atomicity.lifo_certificate
      certificate2_1 opened_stack opened_stack).
    { apply access_neutral_lifo. exact a. }
    assert (Hbody_stack : body_stack = opened_stack).
    { eapply GenericRegions.Atomicity.lifo_certificate_functional;
        eassumption. }
    subst body_stack.
    destruct Hfold_work as (closed_stack & Hfold & Hwork).
    unfold GenericRegions.Atomicity.lifo_certificate in Hfold.
    destruct Hfold as [(outer_open & Hstack & _)|[Hsame Hclosed]].
    + cbn in Hopen. subst opened_stack.
      inversion Hstack; subst outer_open closed_stack.
      eapply IHHbaseline. exact Hwork.
    + exfalso. apply Hclosed.
      match goal with
      | Htransition : GenericRegions.Atomicity.open_invariant ?opened_invariant
          ?opening_state = inr ?opened_state |- _ =>
          pose proof (GenericRegions.Atomicity.open_invariant_success
            opened_invariant opening_state opened_state Htransition) as
            (_ & _ & _ & Hopened);
          rewrite (access_neutral_preserves_open certificate2_1 a), Hopened;
          apply elem_of_union_l; apply elem_of_singleton_2; reflexivity
      end.
  - dependent destruction certificate; try discriminate.
    match goal with
    | Hview : @AnalysisView.syntax_view _ _ (TGhostVal _ _ _ _) = _ |- _ =>
        cbn in Hview; injection Hview as Hd Hscope_body
    end.
    subst. apply Eqdep.EqdepTheory.inj_pair2 in Hscope_body. subst.
    eapply IHHbaseline. exact Hlifo.
Qed.

(** Accepted source regions are balanced at a closed procedure boundary.
    Unlike the purely syntactic statement, this uses the analyzer entry
    state so that an unmatched raw fold is correctly treated as allocation. *)
Lemma baseline_normalizable_closed_lifo {Γ} (statement : stmt Γ)
    (Hbaseline : baseline_normalizable statement) :
  forall entry exit
    (certificate : GenericRegions.Atomicity.analysis_certificate Γ
      entry statement exit),
    GenericRegions.Atomicity.analysis_open entry = ∅ ->
    GenericRegions.Atomicity.lifo_certificate certificate [] [] /\
      GenericRegions.Atomicity.analysis_open exit = ∅.
Proof.
  induction Hbaseline; intros entry exit certificate Hentry.
  - now apply unfold_free_closed_lifo.
  - dependent destruction certificate; try discriminate.
    cbn in e. inversion e; subst.
    assert (Hfirst_lifo : GenericRegions.Atomicity.lifo_certificate
      certificate1 [] []).
    { apply access_neutral_lifo. exact a. }
    assert (Hmiddle : GenericRegions.Atomicity.analysis_open middle = ∅).
    { rewrite (access_neutral_preserves_open certificate1 a). exact Hentry. }
    destruct (IHHbaseline _ _ certificate2 Hmiddle) as [Hsecond Hexit].
    split; [eexists; split; eassumption|exact Hexit].
  - dependent destruction certificate; try discriminate.
    cbn in e. inversion e; subst.
    destruct (IHHbaseline1 _ _ certificate1 Hentry) as [Hfirst Hmiddle].
    destruct (IHHbaseline2 _ _ certificate2 Hmiddle) as [Hsecond Hexit].
    split; [eexists; split; eassumption|exact Hexit].
  - dependent destruction certificate; try discriminate.
    cbn in e. inversion e; subst.
    destruct (IHHbaseline1 _ _ certificate1 Hentry) as [Hthen Hthen_exit].
    destruct (IHHbaseline2 _ _ certificate2 Hentry) as [Helse Helse_exit].
    split; [split; assumption|exact Hthen_exit].
  - dependent destruction certificate; try discriminate.
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
    pose proof (GenericRegions.Atomicity.open_invariant_success _ _ _ e0)
      as (Hfresh & _ & _ & Hopened).
    assert (Hbody : GenericRegions.Atomicity.lifo_certificate
      certificate2_1 [(invariant, GenericRegions.Atomicity.analysis_open state)]
      [(invariant, GenericRegions.Atomicity.analysis_open state)]).
    { apply access_neutral_lifo. exact a. }
    assert (Hbody_open : GenericRegions.Atomicity.analysis_open state1 =
      {[invariant]} ∪ GenericRegions.Atomicity.analysis_open state).
    { rewrite (access_neutral_preserves_open certificate2_1 a). exact Hopened. }
    assert (Hfold : GenericRegions.Atomicity.lifo_certificate
      (GenericRegions.Atomicity.CertFold Γ state1
        (TFold invariant closing_arguments) invariant e3)
      [(invariant, GenericRegions.Atomicity.analysis_open state)] []).
    { left. exists (GenericRegions.Atomicity.analysis_open state).
      repeat split; try reflexivity.
      - rewrite Hbody_open. apply elem_of_union_l, elem_of_singleton_2.
        reflexivity.
      - exact Hfresh.
      - exact Hbody_open. }
    split.
    + eexists. split; [reflexivity|]. eexists. split; [exact Hbody|exact Hfold].
    + destruct (GenericRegions.Atomicity.fold_open_invariant invariant state1)
        as [_ Hclosed].
      * rewrite Hbody_open. apply elem_of_union_l, elem_of_singleton_2.
        reflexivity.
      * rewrite Hclosed, Hbody_open, Hentry.
        set_solver.
  - dependent destruction certificate; try discriminate.
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
    | Hfold_certificate : GenericRegions.Atomicity.analysis_certificate
        _ _ (TFold _ _) _ |- _ =>
        dependent destruction Hfold_certificate
    end; try discriminate.
    match goal with Hview : @AnalysisView.syntax_view _ _ (TFold _ _) = _ |- _ =>
      cbn in Hview; inversion Hview; subst end.
    pose proof (GenericRegions.Atomicity.open_invariant_success _ _ _ e0)
      as (Hfresh & _ & _ & Hopened).
    assert (Hbody : GenericRegions.Atomicity.lifo_certificate
      certificate2_1 [(invariant, GenericRegions.Atomicity.analysis_open state)]
      [(invariant, GenericRegions.Atomicity.analysis_open state)]).
    { apply access_neutral_lifo. exact a. }
    assert (Hbody_open : GenericRegions.Atomicity.analysis_open state1 =
      {[invariant]} ∪ GenericRegions.Atomicity.analysis_open state).
    { rewrite (access_neutral_preserves_open certificate2_1 a). exact Hopened. }
    assert (Hfold : GenericRegions.Atomicity.lifo_certificate
      (GenericRegions.Atomicity.CertFold Γ state1
        (TFold invariant closing_arguments) invariant e3)
      [(invariant, GenericRegions.Atomicity.analysis_open state)] []).
    { left. exists (GenericRegions.Atomicity.analysis_open state).
      repeat split; try reflexivity.
      - rewrite Hbody_open. apply elem_of_union_l, elem_of_singleton_2.
        reflexivity.
      - exact Hfresh.
      - exact Hbody_open. }
    assert (Hclosed_middle : GenericRegions.Atomicity.analysis_open
      (GenericRegions.Atomicity.fold_invariant invariant state1) = ∅).
    { destruct (GenericRegions.Atomicity.fold_open_invariant invariant state1)
        as [_ Hclosed].
      - rewrite Hbody_open. apply elem_of_union_l, elem_of_singleton_2.
        reflexivity.
      - rewrite Hclosed, Hbody_open, Hentry. set_solver. }
    destruct (IHHbaseline _ _ certificate2_2_2 Hclosed_middle)
      as [Hwork Hexit].
    split.
    + eexists. split; [reflexivity|]. eexists. split; [exact Hbody|].
      eexists. split; [exact Hfold|exact Hwork].
    + exact Hexit.
  - dependent destruction certificate; try discriminate.
    match goal with
    | Hview : @AnalysisView.syntax_view _ _ (TGhostVal _ _ _ _) = _ |- _ =>
        cbn in Hview; injection Hview as Hd Hscope_body
    end.
    subst. apply Eqdep.EqdepTheory.inj_pair2 in Hscope_body. subst.
    simpl. exact (IHHbaseline _ _ _ Hentry).
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
    cbn in Hfree. destruct Hfree as [Hthen_free Helse_free].
    eapply StructuredConditional; eauto using (proj1 Hlifo), (proj2 Hlifo).
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
    cbn in Hfree. destruct Hfree as [Hthen_free Helse_free].
    pose (then_result := IHcertificate1 stack Hthen_free (proj1 Hlifo)).
    pose (else_result := IHcertificate2 stack Helse_free (proj2 Hlifo)).
    refine {| balanced_structured_certificate :=
        StructuredConditional Γ state condition then_branch else_branch
          then_exit else_exit then_result.(balanced_structured_certificate)
          else_result.(balanced_structured_certificate) e0 e1 |}.
    intros invariant Hmember.
    simpl in Hmember |- *.
    repeat rewrite elem_of_union in Hmember |- *.
    pose proof (then_result.(balanced_structured_footprint) invariant) as
      Hthen_subset.
    pose proof (else_result.(balanced_structured_footprint) invariant) as
      Helse_subset.
    tauto.
    split; [exact then_result.(balanced_structured_safe) |
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
