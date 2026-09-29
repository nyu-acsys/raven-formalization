From Coq Require Import List Program.Equality.
From stdpp Require Import base sets gmap.

From raven Require Import verification.expressions verification.assertions
  verification.resources verification.ir verification.hoare_rules
  verification.access_layout.

Import ListNotations.

(** Derivation constructions for conditionals inside invariant accesses. *)
Module ConditionalDerivations.
Import Core IR ResourceHoare Resource AccessLayout.
Module Assertions := Assertion.

Section WithSignature.
Context {RAs : RAValueConfig} {Logic : Assertion.LogicSignature}.
Context {Contracts : ResourceContractEnv}.

(** ** Guards at the leaf of a telescope *)

Definition guard_core {F Δ} (positive : bool) (condition : expr F Δ TBool) :
    core_assertion F Δ :=
  CExpr (if positive then condition else EUnOp UNot condition).

(** The guard [condition] (or its negation) at the leaf, read through the
    leaf's store. *)
Fixpoint guard_prenex {Γ F Δ} (positive : bool) (condition : gexpr Γ TBool)
    (prenex : resource_prenex Γ F Δ) : resource_prenex Γ F Δ :=
  match prenex with
  | ResourceBody state =>
      RState (resource_stack state)
        (CAnd (resource_body state)
          (guard_core positive
            (symbolize_expr (resource_stack state) condition)))
  | ResourceExists t rest => ResourceExists t (guard_prenex positive condition rest)
  end.

Lemma guard_prenex_rename {Γ F Δ} positive (condition : gexpr Γ TBool)
    (prenex : resource_prenex Γ F Δ) :
  forall Δ' (renaming : Assertions.bound_renaming Δ Δ'),
  guard_prenex positive condition (rename_resource_prenex prenex Δ' renaming) =
    rename_resource_prenex (guard_prenex positive condition prenex) Δ' renaming.
Proof.
  induction prenex as [Δ [store body] | Δ t rest IH]; intros Δ' renaming.
  - cbn. rewrite symbolize_expr_rename_bound_store.
    destruct positive; reflexivity.
  - cbn. f_equal. apply IH.
Qed.

Lemma guard_prenex_weaken {Γ F Δ u} positive (condition : gexpr Γ TBool)
    (prenex : resource_prenex Γ F Δ) :
  guard_prenex positive condition (weaken_resource_prenex (u := u) prenex) =
    weaken_resource_prenex (guard_prenex positive condition prenex).
Proof. apply guard_prenex_rename. Qed.

(** Guard and frame commute. *)
Lemma guard_prenex_and_entails {Γ F Δ} positive (condition : gexpr Γ TBool)
    (prenex : resource_prenex Γ F Δ) (frame : core_assertion F Δ) :
  resource_prenex_entails
    (guard_prenex positive condition (prenex_and prenex frame))
    (prenex_and (guard_prenex positive condition prenex) frame).
Proof.
  revert frame. induction prenex as [Δ [store body] | Δ t rest IH]; intros frame.
  - apply RPEBody. split; [reflexivity|]. cbn.
    eapply CEntailsTrans; [apply CEntailsStep, CESAndAssocR|].
    eapply CEntailsTrans;
      [apply CEntailsAndMono; [apply CEntailsRefl | apply CEntailsStep, CESAndComm]|].
    apply CEntailsStep, CESAndAssocL.
  - cbn. apply RPEMono. apply IH.
Qed.

(** Guard and tracking commute. *)
Lemma guard_track_prenex_entails {Γ F Δ t} positive (condition : gexpr Γ TBool)
    (expression : gexpr Γ t) (prenex : resource_prenex Γ F Δ) :
  forall value : expr F Δ t,
  resource_prenex_entails
    (guard_prenex positive condition (track_prenex expression prenex value))
    (track_prenex expression (guard_prenex positive condition prenex) value).
Proof.
  induction prenex as [Δ [store body] | Δ u rest IH]; intros value.
  - apply RPEBody. split; [reflexivity|]. cbn.
    eapply CEntailsTrans; [apply CEntailsStep, CESAndAssocR|].
    eapply CEntailsTrans;
      [apply CEntailsAndMono; [apply CEntailsRefl | apply CEntailsStep, CESAndComm]|].
    apply CEntailsStep, CESAndAssocL.
  - cbn. apply RPEMono. apply IH.
Qed.

(** Tracking a guard at a constant yields the guard. *)
Lemma track_constant_guard_entails {Γ F Δ} positive (condition : gexpr Γ TBool)
    (prenex : resource_prenex Γ F Δ) :
  resource_prenex_entails
    (track_prenex condition prenex (EVal (VBool positive)))
    (guard_prenex positive condition prenex).
Proof.
  induction prenex as [Δ [store body] | Δ u rest IH].
  - apply RPEBody. split; [reflexivity|]. cbn.
    apply CEntailsAndMono; [apply CEntailsRefl|].
    apply CEntailsStep, CESExprImpl. intros formals binders valuation.
    destruct (interp_expr_total formals binders valuation
      (symbolize_expr store condition)) as [value Hvalue].
    cbn [interp_expr]. rewrite Hvalue.
    dependent destruction value. cbn. intros Hequal.
    inversion Hequal as [Hb]. apply Bool.eqb_prop in Hb. subst b.
    destruct positive; cbn; rewrite Hvalue; reflexivity.
  - cbn. apply RPEMono. exact IH.
Qed.

(** ** Statements without writes *)

Lemma proof_only_writes {Γ} (statement : stmt Γ) :
  proof_onlyb statement = true -> statement_writes statement = ∅.
Proof.
  induction statement; cbn [proof_onlyb statement_writes]; intros Hproof;
    rewrite ?Bool.andb_true_iff in Hproof; try discriminate; try reflexivity.
  - exact (IHstatement Hproof).
  - destruct Hproof as [H1 H2]. rewrite IHstatement1, IHstatement2 by assumption.
    set_solver.
  - destruct Hproof as [H1 H2]. rewrite IHstatement1, IHstatement2 by assumption.
    set_solver.
  - rewrite IHstatement by assumption. apply set_eq. intros slot.
    rewrite elem_of_unshift_slots. set_solver.
  - destruct Hproof as [H1 H2]. rewrite IHstatement1, IHstatement2 by assumption.
    set_solver.
Qed.

(** ** Inversion of conditionals

    A conditional's derivation is [RTIf] under structural rules.  The rules
    acting on the precondition are carried by a derivation of [TDone]; the
    branches start from the guarded result. *)

Lemma RavenHoareTriple_if_inversion {Γ F Δ} (condition : rexpr Γ TBool)
    (then_branch else_branch : stmt Γ) (pre post : resource_prenex Γ F Δ) :
  RavenHoareTriple pre (TIf condition then_branch else_branch) post ->
  exists middle : resource_prenex Γ F Δ,
    RavenHoareTriple pre TDone middle /\
    RavenHoareTriple (guard_prenex true (pexpr_forget condition) middle)
      then_branch post /\
    RavenHoareTriple (guard_prenex false (pexpr_forget condition) middle)
      else_branch post.
Proof.
  intro derivation.
  dependent induction derivation generalizing condition then_branch else_branch.
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    exists (ResourceExists t middle).
    repeat split; apply RTPrenexPreserve; assumption.
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    exists (weaken_resource_prenex middle).
    rewrite !guard_prenex_weaken.
    repeat split; apply RTBoundWeaken; assumption.
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    exists (ResourceExists t middle). repeat split.
    + apply RTPrenexPreserve. exact Hdone.
    + apply RTPrenexElim. exact Hthen.
    + apply RTPrenexElim. exact Helse.
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    exists middle. repeat split.
    + eapply RTPrenexConsequence;
        [exact Hdone | exact H | apply resource_prenex_entails_refl].
    + eapply RTPrenexConsequence;
        [exact Hthen | apply resource_prenex_entails_refl | exact H0].
    + eapply RTPrenexConsequence;
        [exact Helse | apply resource_prenex_entails_refl | exact H0].
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    exists (prenex_and middle frame). repeat split.
    + apply RTFrame. exact Hdone.
    + eapply RTPrenexConsequence;
        [apply RavenHoareTriple_prenex_frame; exact Hthen
        | apply guard_prenex_and_entails
        | apply resource_prenex_entails_refl].
    + eapply RTPrenexConsequence;
        [apply RavenHoareTriple_prenex_frame; exact Helse
        | apply guard_prenex_and_entails
        | apply resource_prenex_entails_refl].
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    exists middle. repeat split.
    + eapply RTConsequence;
        [exact Hdone | exact H | apply resource_prenex_entails_refl].
    + eapply RTPrenexConsequence;
        [exact Hthen | apply resource_prenex_entails_refl | exact H0].
    + eapply RTPrenexConsequence;
        [exact Helse | apply resource_prenex_entails_refl | exact H0].
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    exists middle. repeat split; [|assumption|assumption].
    eapply RTStackRewrite; eassumption.
  - exists (RState store body). repeat split.
    + apply RTDone.
    + cbn. rewrite symbolize_expr_forget. exact derivation1.
    + cbn. rewrite symbolize_expr_forget. exact derivation2.
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    cbn [statement_writes] in H.
    assert (Hthen_disjoint : pexpr_dependencies expression ##
      statement_writes then_branch) by set_solver.
    assert (Helse_disjoint : pexpr_dependencies expression ##
      statement_writes else_branch) by set_solver.
    exists (track_prenex expression middle value). repeat split.
    + apply RTTrack; [cbn; set_solver | exact Hdone].
    + eapply RTPrenexConsequence;
        [exact (RTTrack _ expression value _ _ _ Hthen_disjoint Hthen)
        | apply guard_track_prenex_entails
        | apply resource_prenex_entails_refl].
    + eapply RTPrenexConsequence;
        [exact (RTTrack _ expression value _ _ _ Helse_disjoint Helse)
        | apply guard_track_prenex_entails
        | apply resource_prenex_entails_refl].
Qed.

Lemma RavenHoareTriple_ghost_if_inversion {Γ F Δ} (condition : gexpr Γ TBool)
    (then_branch else_branch : stmt Γ) (pre post : resource_prenex Γ F Δ) :
  RavenHoareTriple pre (TGhostIf condition then_branch else_branch) post ->
  exists middle : resource_prenex Γ F Δ,
    RavenHoareTriple pre TDone middle /\
    RavenHoareTriple (guard_prenex true condition middle)
      then_branch post /\
    RavenHoareTriple (guard_prenex false condition middle)
      else_branch post.
Proof.
  intro derivation.
  dependent induction derivation generalizing condition then_branch else_branch.
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    exists (ResourceExists t middle).
    repeat split; apply RTPrenexPreserve; assumption.
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    exists (weaken_resource_prenex middle).
    rewrite !guard_prenex_weaken.
    repeat split; apply RTBoundWeaken; assumption.
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    exists (ResourceExists t middle). repeat split.
    + apply RTPrenexPreserve. exact Hdone.
    + apply RTPrenexElim. exact Hthen.
    + apply RTPrenexElim. exact Helse.
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    exists middle. repeat split.
    + eapply RTPrenexConsequence;
        [exact Hdone | exact H | apply resource_prenex_entails_refl].
    + eapply RTPrenexConsequence;
        [exact Hthen | apply resource_prenex_entails_refl | exact H0].
    + eapply RTPrenexConsequence;
        [exact Helse | apply resource_prenex_entails_refl | exact H0].
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    exists (prenex_and middle frame). repeat split.
    + apply RTFrame. exact Hdone.
    + eapply RTPrenexConsequence;
        [apply RavenHoareTriple_prenex_frame; exact Hthen
        | apply guard_prenex_and_entails
        | apply resource_prenex_entails_refl].
    + eapply RTPrenexConsequence;
        [apply RavenHoareTriple_prenex_frame; exact Helse
        | apply guard_prenex_and_entails
        | apply resource_prenex_entails_refl].
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    exists middle. repeat split.
    + eapply RTConsequence;
        [exact Hdone | exact H | apply resource_prenex_entails_refl].
    + eapply RTPrenexConsequence;
        [exact Hthen | apply resource_prenex_entails_refl | exact H0].
    + eapply RTPrenexConsequence;
        [exact Helse | apply resource_prenex_entails_refl | exact H0].
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    exists middle. repeat split; [|assumption|assumption].
    eapply RTStackRewrite; eassumption.
  - exists (RState store body). repeat split.
    + apply RTDone.
    + exact derivation1.
    + exact derivation2.
  - destruct (IHderivation condition then_branch else_branch eq_refl)
      as (middle & Hdone & Hthen & Helse).
    cbn [statement_writes] in H.
    assert (Hthen_disjoint : pexpr_dependencies expression ##
      statement_writes then_branch) by set_solver.
    assert (Helse_disjoint : pexpr_dependencies expression ##
      statement_writes else_branch) by set_solver.
    exists (track_prenex expression middle value). repeat split.
    + apply RTTrack; [cbn; set_solver | exact Hdone].
    + eapply RTPrenexConsequence;
        [exact (RTTrack _ expression value _ _ _ Hthen_disjoint Hthen)
        | apply guard_track_prenex_entails
        | apply resource_prenex_entails_refl].
    + eapply RTPrenexConsequence;
        [exact (RTTrack _ expression value _ _ _ Helse_disjoint Helse)
        | apply guard_track_prenex_entails
        | apply resource_prenex_entails_refl].
Qed.

(** ** Distributing an access over a conditional

    With only proof-only code between the unfold and the conditional, the
    conditional can be tested first; the guard is carried to the original
    test by tracking it through that code. *)

Lemma guard_implies_constant {F Δ} positive (condition : expr F Δ TBool) :
  core_entails (guard_core positive condition)
    (CExpr (EBinOp (BEq TBool) (EVal (VBool positive)) condition)).
Proof.
  apply CEntailsStep, CESExprImpl. intros formals binders valuation.
  destruct (interp_expr_total formals binders valuation condition)
    as [value Hvalue].
  dependent destruction value.
  destruct positive, b; cbn [interp_expr]; rewrite Hvalue; cbn; intros Hguard;
    try reflexivity; inversion Hguard.
Qed.

Lemma RavenHoareTriple_distribute_access_leaf {Γ F Δ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix then_branch else_branch : stmt Γ) (condition : gexpr Γ TBool)
    (store : symbolic_store Γ F Δ) (body : core_assertion F Δ)
    (post : resource_prenex Γ F Δ) positive (branch : stmt Γ) middle :
  proof_onlyb prefix = true ->
  RavenHoareTriple (RState store body) (TUnfold invariant arguments) middle ->
  forall joined,
  RavenHoareTriple middle prefix joined ->
  forall carried,
  RavenHoareTriple joined TDone carried ->
  RavenHoareTriple (guard_prenex positive condition carried) branch post ->
  RavenHoareTriple
    (RState store
      (CAnd body (guard_core positive (symbolize_expr store condition))))
    (TSeq (TUnfold invariant arguments) (TSeq prefix (TSeq TDone branch)))
    post.
Proof.
  intros Hproof Hunfold joined Hprefix carried Hdone Hbranch.
  assert (Hno_writes : forall statement : stmt Γ,
      statement_writes statement = ∅ ->
      pexpr_dependencies condition ## statement_writes statement).
  { intros statement ->. set_solver. }
  eapply RTConsequence;
    [| apply CEntailsAndMono; [apply CEntailsRefl | apply guard_implies_constant]
     | apply resource_prenex_entails_refl].
  change (RState store (CAnd body
      (CExpr (EBinOp (BEq TBool) (EVal (VBool positive))
        (symbolize_expr store condition))))) with
    (track_prenex condition (RState store body) (EVal (VBool positive))).
  eapply RTSeq;
    [exact (RTTrack _ condition _ _ _ _
      (Hno_writes (TUnfold invariant arguments) eq_refl) Hunfold) |].
  eapply RTSeq;
    [exact (RTTrack _ condition _ _ _ _
      (Hno_writes _ (proof_only_writes _ Hproof)) Hprefix) |].
  eapply RTSeq;
    [exact (RTTrack _ condition _ _ _ _ (Hno_writes TDone eq_refl) Hdone) |].
  eapply RTPrenexConsequence;
    [exact Hbranch | apply track_constant_guard_entails
    | apply resource_prenex_entails_refl].
Qed.

Lemma RavenHoareTriple_distribute_access {Γ F Δ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix then_branch else_branch : stmt Γ) (condition : rexpr Γ TBool)
    (pre post : resource_prenex Γ F Δ) :
  proof_onlyb prefix = true ->
  RavenHoareTriple pre
    (TSeq (TUnfold invariant arguments)
      (TSeq prefix (TIf condition then_branch else_branch))) post ->
  RavenHoareTriple pre
    (TIf condition
      (TSeq (TUnfold invariant arguments)
        (TSeq prefix (TSeq TDone then_branch)))
      (TSeq (TUnfold invariant arguments)
        (TSeq prefix (TSeq TDone else_branch)))) post.
Proof.
  intros Hproof. revert post.
  induction pre as [Δ [store body] | Δ t rest IH]; intros post Hsource.
  - destruct (RavenHoareTriple_sequence_decompose _ _ Hsource)
      as (opened & Hunfold & Htail).
    destruct (RavenHoareTriple_sequence_decompose _ _ Htail)
      as (joined & Hprefix & Hif).
    destruct (RavenHoareTriple_if_inversion _ _ _ _ _ Hif)
      as (carried & Hdone & Hthen & Helse).
    apply RTIf.
    + pose proof (RavenHoareTriple_distribute_access_leaf invariant arguments
        prefix then_branch else_branch (pexpr_forget condition) store body post
        true then_branch opened Hproof Hunfold joined Hprefix carried Hdone Hthen)
        as Hbranch.
      cbn [guard_core] in Hbranch. rewrite symbolize_expr_forget in Hbranch.
      exact Hbranch.
    + pose proof (RavenHoareTriple_distribute_access_leaf invariant arguments
        prefix then_branch else_branch (pexpr_forget condition) store body post
        false else_branch opened Hproof Hunfold joined Hprefix carried Hdone Helse)
        as Hbranch.
      cbn [guard_core] in Hbranch. rewrite symbolize_expr_forget in Hbranch.
      exact Hbranch.
  - apply RTPrenexElim. apply IH.
    eapply RavenHoareTriple_under_exists;
      [apply resource_prenex_entails_refl | exact Hsource].
Qed.

Lemma RavenHoareTriple_distribute_ghost_access {Γ F Δ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix then_branch else_branch : stmt Γ) (condition : gexpr Γ TBool)
    (pre post : resource_prenex Γ F Δ) :
  proof_onlyb prefix = true ->
  proof_onlyb then_branch = true ->
  proof_onlyb else_branch = true ->
  RavenHoareTriple pre
    (TSeq (TUnfold invariant arguments)
      (TSeq prefix (TGhostIf condition then_branch else_branch))) post ->
  RavenHoareTriple pre
    (TGhostIf condition
      (TSeq (TUnfold invariant arguments)
        (TSeq prefix (TSeq TDone then_branch)))
      (TSeq (TUnfold invariant arguments)
        (TSeq prefix (TSeq TDone else_branch)))) post.
Proof.
  intros Hproof Hthen_proof Helse_proof. revert post.
  induction pre as [Δ [store body] | Δ t rest IH]; intros post Hsource.
  - destruct (RavenHoareTriple_sequence_decompose _ _ Hsource)
      as (opened & Hunfold & Htail).
    destruct (RavenHoareTriple_sequence_decompose _ _ Htail)
      as (joined & Hprefix & Hif).
    destruct (RavenHoareTriple_ghost_if_inversion _ _ _ _ _ Hif)
      as (carried & Hdone & Hthen & Helse).
    apply RTGhostIf.
    + cbn. rewrite Hproof, Hthen_proof. reflexivity.
    + cbn. rewrite Hproof, Helse_proof. reflexivity.
    + exact (RavenHoareTriple_distribute_access_leaf invariant arguments
        prefix then_branch else_branch condition store body post
        true then_branch opened Hproof Hunfold joined Hprefix carried Hdone Hthen).
    + exact (RavenHoareTriple_distribute_access_leaf invariant arguments
        prefix then_branch else_branch condition store body post
        false else_branch opened Hproof Hunfold joined Hprefix carried Hdone Helse).
  - apply RTPrenexElim. apply IH.
    eapply RavenHoareTriple_under_exists;
      [apply resource_prenex_entails_refl | exact Hsource].
Qed.

(** ** Tracking a whole store

    Proof-only code writes no local, so every slot of the store can be
    tracked across it.  The tracked slot equalities let a later carrier
    rewrite the store back to its original form. *)

Fixpoint all_pvars (D : decl_context) : list { t : typ & pvar D t } :=
  match D with
  | [] => []
  | d :: D' =>
      existT (decl_type d) (LHere (keep := keep_all) (d := d) (D := D') eq_refl)
        :: map (fun variable => existT (projT1 variable) (LThere (projT2 variable)))
             (all_pvars D')
  end.

Lemma all_pvars_complete {D t} (variable : pvar D t) :
  In (existT t variable) (all_pvars D).
Proof.
  induction variable as [d D Hkeep | d D t variable IH]; cbn.
  - left. f_equal. f_equal. apply Eqdep_dec.UIP_dec, Bool.bool_dec.
  - right. apply in_map_iff. exists (existT t variable). split; [reflexivity|].
    exact IH.
Qed.

(** Every listed slot tracked at its value in [store]. *)
Fixpoint track_vars {Γ F Δ} (variables : list { t : typ & pvar Γ t })
    (store : symbolic_store Γ F Δ) (prenex : resource_prenex Γ F Δ) :
    resource_prenex Γ F Δ :=
  match variables with
  | [] => prenex
  | existT t variable :: rest =>
      track_prenex (PEVar variable) (track_vars rest store prenex)
        (ERef (lookup_store store t variable))
  end.

Definition track_store {Γ F Δ} (store : symbolic_store Γ F Δ)
    (prenex : resource_prenex Γ F Δ) : resource_prenex Γ F Δ :=
  track_vars (all_pvars Γ) store prenex.

Lemma RTTrackVars {Γ F Δ} (variables : list { t : typ & pvar Γ t })
    (store : symbolic_store Γ F Δ) (statement : stmt Γ)
    (pre post : resource_prenex Γ F Δ) :
  statement_writes statement = ∅ ->
  RavenHoareTriple pre statement post ->
  RavenHoareTriple (track_vars variables store pre) statement
    (track_vars variables store post).
Proof.
  intros Hwrites Htriple. induction variables as [|[t variable] rest IH];
    cbn [track_vars]; [exact Htriple|].
  apply RTTrack; [rewrite Hwrites; set_solver | exact IH].
Qed.

Lemma track_prenex_exists {Γ F Δ t u} (expression : gexpr Γ t)
    (rest : resource_prenex Γ F (u :: Δ)) (value : expr F Δ t) :
  track_prenex expression (ResourceExists u rest) value =
    ResourceExists u (track_prenex expression rest (Assertions.weaken_expr value)).
Proof. reflexivity. Qed.

Lemma track_vars_exists {Γ F Δ u} (variables : list { t : typ & pvar Γ t })
    (store : symbolic_store Γ F Δ) (rest : resource_prenex Γ F (u :: Δ)) :
  track_vars variables store (ResourceExists u rest) =
    ResourceExists u (track_vars variables (Assertions.weaken_store store) rest).
Proof.
  induction variables as [|[t variable] variables IH]; cbn [track_vars];
    [reflexivity|].
  rewrite IH, track_prenex_exists. cbn [Assertions.weaken_expr].
  rewrite lookup_weaken_store. reflexivity.
Qed.

(** The leaf of a tracked state. *)
Fixpoint track_vars_body {Γ F Δ} (variables : list { t : typ & pvar Γ t })
    (base leaf : symbolic_store Γ F Δ) (body : core_assertion F Δ) :
    core_assertion F Δ :=
  match variables with
  | [] => body
  | existT t variable :: rest =>
      CAnd (track_vars_body rest base leaf body)
        (CExpr (EBinOp (BEq t) (ERef (lookup_store base t variable))
          (ERef (lookup_store leaf t variable))))
  end.

Lemma track_vars_state {Γ F Δ} (variables : list { t : typ & pvar Γ t })
    (base leaf : symbolic_store Γ F Δ) (body : core_assertion F Δ) :
  track_vars variables base (RState leaf body) =
    RState leaf (track_vars_body variables base leaf body).
Proof.
  induction variables as [|[t variable] variables IH]; cbn [track_vars];
    [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma track_vars_body_fact {Γ F Δ} (variables : list { t : typ & pvar Γ t })
    (base leaf : symbolic_store Γ F Δ) (body : core_assertion F Δ) t
    (variable : pvar Γ t) :
  In (existT t variable) variables ->
  core_entails (track_vars_body variables base leaf body)
    (CExpr (EBinOp (BEq t) (ERef (lookup_store base t variable))
      (ERef (lookup_store leaf t variable)))).
Proof.
  induction variables as [|[u other] variables IH]; intros Hin; [contradiction|].
  cbn [track_vars_body]. destruct Hin as [Heq | Hin].
  - dependent destruction Heq. apply CEntailsStep, CESAndElimR.
  - eapply CEntailsTrans; [apply CEntailsStep, CESAndElimL|]. exact (IH Hin).
Qed.

Lemma equality_symmetric_entails {F Δ t} (left right : expr F Δ t) :
  core_entails (CExpr (EBinOp (BEq t) left right))
    (CExpr (EBinOp (BEq t) right left)).
Proof.
  apply CEntailsStep, CESExprImpl. intros formals binders valuation.
  cbn [interp_expr].
  destruct (interp_expr formals binders valuation left) as [left_value|];
    [|discriminate].
  destruct (interp_expr formals binders valuation right) as [right_value|];
    [|discriminate].
  cbn [interp_binop]. intros Hequal. injection Hequal as Hequal.
  apply tval_eqb_eq in Hequal. subst.
  rewrite (proj2 (tval_eqb_eq _ right_value right_value) eq_refl).
  reflexivity.
Qed.

Lemma store_equal_under_lookups {Γ F Δ} (body : core_assertion F Δ)
    (left right : symbolic_store Γ F Δ) :
  (forall t (variable : pvar Γ t),
    core_entails body
      (CExpr (EBinOp (BEq t) (ERef (lookup_store left t variable))
        (ERef (lookup_store right t variable))))) ->
  store_equal_under body Γ left right.
Proof.
  revert right. induction left as [|d Γ reference tail IH]; intros right Hslots;
    dependent destruction right; [apply StoreEqualNil|].
  apply StoreEqualCons.
  - exact (Hslots _ (LHere (keep := keep_all) (d := d) (D := Γ) eq_refl)).
  - apply IH. intros t variable. exact (Hslots _ (LThere variable)).
Qed.

(** Tracked states may exchange their store with the tracked one. *)
Lemma track_store_equal_under {Γ F Δ} (base leaf : symbolic_store Γ F Δ)
    (body extra : core_assertion F Δ) :
  store_equal_under
    (CAnd (track_vars_body (all_pvars Γ) base leaf body) extra) Γ leaf base /\
  store_equal_under
    (CAnd (track_vars_body (all_pvars Γ) base leaf body) extra) Γ base leaf.
Proof.
  split; apply store_equal_under_lookups; intros t variable;
    (eapply CEntailsTrans; [apply CEntailsStep, CESAndElimL|]);
    pose proof (track_vars_body_fact (all_pvars Γ) base leaf body t variable
      (all_pvars_complete variable)) as Hfact.
  - eapply CEntailsTrans; [exact Hfact | apply equality_symmetric_entails].
  - exact Hfact.
Qed.

(** ** Restoring and closing tracked telescopes *)

(** The telescope with its leaf store replaced by [store], weakened across
    the binders. *)
Fixpoint restore_prenex {Γ F Δ} (store : symbolic_store Γ F Δ)
    (prenex : resource_prenex Γ F Δ) : resource_prenex Γ F Δ :=
  match prenex in resource_prenex _ _ Δ0
    return symbolic_store Γ F Δ0 -> resource_prenex Γ F Δ0 with
  | ResourceBody state => fun store => RState store (resource_body state)
  | ResourceExists t rest => fun store =>
      ResourceExists t (restore_prenex (Assertions.weaken_store store) rest)
  end store.

(** The telescope's binders as core existentials. *)
Fixpoint close_core {Γ F Δ} (prenex : resource_prenex Γ F Δ) :
    core_assertion F Δ :=
  match prenex with
  | ResourceBody state => resource_body state
  | ResourceExists t rest => CExists t (close_core rest)
  end.

Lemma restore_close_entails {Γ F Δ} (store : symbolic_store Γ F Δ)
    (prenex : resource_prenex Γ F Δ) :
  resource_prenex_entails (restore_prenex store prenex)
    (RState store (close_core prenex)).
Proof.
  revert store. induction prenex as [Δ [leaf body] | Δ t rest IH]; intros store.
  - apply resource_prenex_entails_refl.
  - cbn. eapply RPETrans; [apply RPEMono, IH | apply RPECloseCoreExists].
Qed.

Lemma close_restore_entails {Γ F Δ} (store : symbolic_store Γ F Δ)
    (prenex : resource_prenex Γ F Δ) :
  resource_prenex_entails (RState store (close_core prenex))
    (restore_prenex store prenex).
Proof.
  revert store. induction prenex as [Δ [leaf body] | Δ t rest IH]; intros store.
  - apply resource_prenex_entails_refl.
  - cbn. eapply RPETrans; [apply RPEOpenCoreExists | apply RPEMono, IH].
Qed.

Lemma close_core_and_out {Γ F Δ} (prenex : resource_prenex Γ F Δ)
    (frame : core_assertion F Δ) :
  core_entails (close_core (prenex_and prenex frame))
    (CAnd (close_core prenex) frame).
Proof.
  revert frame. induction prenex as [Δ [leaf body] | Δ t rest IH]; intros frame.
  - apply CEntailsRefl.
  - cbn. eapply CEntailsTrans;
      [apply CEntailsExistsMono, IH | apply CEntailsExistsAndRightOut].
Qed.

Lemma close_core_and_in {Γ F Δ} (prenex : resource_prenex Γ F Δ)
    (frame : core_assertion F Δ) :
  core_entails (CAnd (close_core prenex) frame)
    (close_core (prenex_and prenex frame)).
Proof.
  revert frame. induction prenex as [Δ [leaf body] | Δ t rest IH]; intros frame.
  - apply CEntailsRefl.
  - cbn. eapply CEntailsTrans;
      [apply CEntailsExistsAndRight | apply CEntailsExistsMono, IH].
Qed.

(** A tracked telescope may exchange its leaf store with the tracked one:
    forward on a carrier, and backward before any statement. *)
Lemma canonicalize_triple {Γ F Δ} (store : symbolic_store Γ F Δ)
    (prenex : resource_prenex Γ F Δ) (frame : core_assertion F Δ) :
  RavenHoareTriple (prenex_and (track_store store prenex) frame) TDone
    (restore_prenex store (prenex_and (track_store store prenex) frame)).
Proof.
  revert store frame.
  induction prenex as [Δ [leaf body] | Δ t rest IH]; intros store frame.
  - change (ResourceBody (ResourceState leaf body)) with (RState leaf body).
    unfold track_store. rewrite track_vars_state. cbn.
    eapply RTStackRewrite; [apply RTDone|].
    exact (proj1 (track_store_equal_under store leaf body frame)).
  - unfold track_store. rewrite track_vars_exists. cbn.
    apply RTPrenexPreserve. apply IH.
Qed.

Lemma uncanonicalize_triple {Γ F Δ} (store : symbolic_store Γ F Δ)
    (prenex : resource_prenex Γ F Δ) (frame : core_assertion F Δ)
    (statement : stmt Γ) (post : resource_prenex Γ F Δ) :
  RavenHoareTriple (prenex_and (track_store store prenex) frame) statement post ->
  RavenHoareTriple
    (restore_prenex store (prenex_and (track_store store prenex) frame))
    statement post.
Proof.
  revert store frame post.
  induction prenex as [Δ [leaf body] | Δ t rest IH]; intros store frame post Htriple.
  - change (ResourceBody (ResourceState leaf body)) with (RState leaf body) in *.
    unfold track_store in *. rewrite track_vars_state in *. cbn in *.
    eapply RTStackRewrite; [exact Htriple|].
    exact (proj2 (track_store_equal_under store leaf body frame)).
  - unfold track_store in *. rewrite track_vars_exists in *. cbn in *.
    apply RTPrenexElim. apply IH.
    eapply RavenHoareTriple_under_exists;
      [apply resource_prenex_entails_refl | exact Htriple].
Qed.

Lemma close_core_restore {Γ F Δ} (store : symbolic_store Γ F Δ)
    (prenex : resource_prenex Γ F Δ) :
  close_core (restore_prenex store prenex) = close_core prenex.
Proof.
  revert store. induction prenex as [Δ [leaf body] | Δ t rest IH]; intros store;
    cbn; [reflexivity | now rewrite IH].
Qed.

(** Tracked facts are trivially true at the tracked store, and may be
    dropped. *)
Lemma equality_refl_true {F Δ t} (expression : expr F Δ t) :
  core_entails (CPure True) (CExpr (EBinOp (BEq t) expression expression)).
Proof.
  apply CEntailsStep, CESExprTrue. intros formals binders valuation.
  cbn [interp_expr].
  destruct (interp_expr_total formals binders valuation expression)
    as [value ->].
  cbn [interp_binop]. rewrite (proj2 (tval_eqb_eq _ value value) eq_refl).
  reflexivity.
Qed.

Lemma track_vars_body_intro {Γ F Δ} (variables : list { t : typ & pvar Γ t })
    (store : symbolic_store Γ F Δ) (body : core_assertion F Δ) :
  core_entails body (track_vars_body variables store store body).
Proof.
  induction variables as [|[t variable] variables IH]; cbn [track_vars_body];
    [apply CEntailsRefl|].
  eapply CEntailsTrans; [apply CEntailsStep, CESAndTrueIntro|].
  apply CEntailsAndMono; [exact IH | apply equality_refl_true].
Qed.

Lemma track_vars_body_elim {Γ F Δ} (variables : list { t : typ & pvar Γ t })
    (base leaf : symbolic_store Γ F Δ) (body : core_assertion F Δ) :
  core_entails (track_vars_body variables base leaf body) body.
Proof.
  induction variables as [|[t variable] variables IH]; cbn [track_vars_body];
    [apply CEntailsRefl|].
  eapply CEntailsTrans; [apply CEntailsStep, CESAndElimL | exact IH].
Qed.

Lemma track_store_elim_entails {Γ F Δ} (store : symbolic_store Γ F Δ)
    (prenex : resource_prenex Γ F Δ) :
  resource_prenex_entails (track_store store prenex) prenex.
Proof.
  revert store. induction prenex as [Δ [leaf body] | Δ t rest IH]; intros store.
  - change (ResourceBody (ResourceState leaf body)) with (RState leaf body).
    unfold track_store. rewrite track_vars_state.
    apply RPEBody. split; [reflexivity|]. apply track_vars_body_elim.
  - unfold track_store in *. rewrite track_vars_exists. apply RPEMono. apply IH.
Qed.

(** ** One branch of a factored access

    A branch [prefix; closing; continuation] with a proof-only [prefix] and
    a writeless [closing] is split at the closing: the state before it is
    tracked, restored to the entry store, and closed into a core assertion,
    so the branches of a conditional can be joined over one store. *)

Definition tracked_core {Γ F Δ} (store : symbolic_store Γ F Δ)
    (prenex : resource_prenex Γ F Δ) : core_assertion F Δ :=
  close_core (track_store store prenex).

Lemma tracked_core_open {Γ F Δ} (store : symbolic_store Γ F Δ)
    (prenex : resource_prenex Γ F Δ) :
  resource_prenex_entails (RState store (tracked_core store prenex))
    (restore_prenex store (prenex_and (track_store store prenex) CTrue)).
Proof.
  eapply RPETrans; [| apply close_restore_entails].
  apply RPEBody. split; [reflexivity|].
  eapply CEntailsTrans; [apply CEntailsStep, CESAndTrueIntro|].
  apply close_core_and_in.
Qed.

Lemma tracked_core_close {Γ F Δ} (store : symbolic_store Γ F Δ)
    (prenex : resource_prenex Γ F Δ) (frame : core_assertion F Δ) :
  resource_prenex_entails
    (restore_prenex store (prenex_and (track_store store prenex) frame))
    (RState store (CAnd (tracked_core store prenex) frame)).
Proof.
  eapply RPETrans; [apply restore_close_entails|].
  apply RPEBody. split; [reflexivity|]. apply close_core_and_out.
Qed.

Lemma branch_split {Γ F Δ} (store : symbolic_store Γ F Δ)
    (body : core_assertion F Δ) (guard : expr F Δ TBool)
    (prefix closing continuation : stmt Γ)
    (joined folded post : resource_prenex Γ F Δ) :
  proof_onlyb prefix = true ->
  statement_writes closing = ∅ ->
  RavenHoareTriple (RState store (CAnd body (CExpr guard))) prefix joined ->
  RavenHoareTriple joined closing folded ->
  RavenHoareTriple folded continuation post ->
  RavenHoareTriple (RState store (CAnd body (CExpr guard))) (TSeq prefix TDone)
    (RState store (CAnd (tracked_core store joined) (CExpr guard))) /\
  RavenHoareTriple (RState store (tracked_core store joined))
    (TSeq closing TDone) (RState store (tracked_core store folded)) /\
  RavenHoareTriple (RState store (tracked_core store folded)) continuation post.
Proof.
  intros Hproof Hclosing_writes Hprefix Hclosing Hcontinuation.
  pose proof (proof_only_writes prefix Hproof) as Hprefix_writes.
  repeat split.
  - pose proof (RavenHoareTriple_prenex_frame _ _ (CExpr guard)
      (RTTrackVars (all_pvars Γ) store prefix _ _ Hprefix_writes Hprefix))
      as Htracked.
    change (track_vars (all_pvars Γ) store) with (track_store (Γ := Γ) store)
      in Htracked.
    eapply RTSeq; [| eapply RTPrenexConsequence;
      [apply canonicalize_triple | apply resource_prenex_entails_refl
      | apply tracked_core_close]].
    unfold track_store at 1 in Htracked.
    rewrite track_vars_state in Htracked. cbn [prenex_and] in Htracked.
    eapply RTConsequence; [exact Htracked | | apply resource_prenex_entails_refl].
    eapply CEntailsTrans;
      [apply CEntailsAndMono;
        [apply CEntailsRefl | apply CEntailsStep, CESDuplicate; reflexivity]|].
    eapply CEntailsTrans; [apply CEntailsStep, CESAndAssocL|].
    apply CEntailsAndMono; [apply track_vars_body_intro | apply CEntailsRefl].
  - eapply RTPrenexConsequence; [| apply tracked_core_open |
      apply resource_prenex_entails_refl].
    pose proof (RavenHoareTriple_prenex_frame _ _ CTrue
      (RTTrackVars (all_pvars Γ) store closing _ _ Hclosing_writes Hclosing))
      as Htracked.
    change (track_vars (all_pvars Γ) store) with (track_store (Γ := Γ) store)
      in Htracked.
    eapply RTSeq; [exact (uncanonicalize_triple _ _ _ _ _ Htracked)|].
    eapply RTPrenexConsequence;
      [apply canonicalize_triple | apply resource_prenex_entails_refl|].
    eapply RPETrans; [apply tracked_core_close|].
    apply RPEBody. split; [reflexivity|]. apply CEntailsStep, CESAndElimL.
  - eapply RTPrenexConsequence; [| apply tracked_core_open |
      apply resource_prenex_entails_refl].
    apply uncanonicalize_triple.
    eapply RTPrenexConsequence; [exact Hcontinuation | |
      apply resource_prenex_entails_refl].
    eapply RPETrans; [apply resource_prenex_entails_frame_true_elim|].
    apply track_store_elim_entails.
Qed.

(** ** Factoring an access out of a conditional

    After a physical step the branch prefixes before the matching folds are
    proof-only.  The conditional runs them inside the access and the
    branch-local folds close it through a ghost conditional; the
    continuations are selected again by the same guard, which proof-only
    code cannot change. *)

Lemma ite_keep_then {F Δ} (condition : expr F Δ TBool)
    (then_branch else_branch : core_assertion F Δ) :
  core_entails (CAnd (CIte condition then_branch else_branch) (CExpr condition))
    (CAnd then_branch (CExpr condition)).
Proof.
  eapply CEntailsTrans;
    [apply CEntailsAndMono;
      [apply CEntailsRefl | apply CEntailsStep, CESDuplicate; reflexivity]|].
  eapply CEntailsTrans; [apply CEntailsStep, CESAndAssocL|].
  apply CEntailsAndMono; [apply CEntailsStep, CESIteTrue | apply CEntailsRefl].
Qed.

Lemma ite_keep_else {F Δ} (condition : expr F Δ TBool)
    (then_branch else_branch : core_assertion F Δ) :
  core_entails
    (CAnd (CIte condition then_branch else_branch)
      (CExpr (EUnOp UNot condition)))
    (CAnd else_branch (CExpr (EUnOp UNot condition))).
Proof.
  eapply CEntailsTrans;
    [apply CEntailsAndMono;
      [apply CEntailsRefl | apply CEntailsStep, CESDuplicate; reflexivity]|].
  eapply CEntailsTrans; [apply CEntailsStep, CESAndAssocL|].
  apply CEntailsAndMono; [apply CEntailsStep, CESIteFalse | apply CEntailsRefl].
Qed.

(** The branches, split and joined over the entry store. *)
Lemma factor_join {Γ F Δ} (store : symbolic_store Γ F Δ)
    (body : core_assertion F Δ) (guard : expr F Δ TBool) (closing : stmt Γ)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ)
    (post : resource_prenex Γ F Δ) :
  proof_onlyb then_prefix = true ->
  proof_onlyb else_prefix = true ->
  statement_writes closing = ∅ ->
  RavenHoareTriple (RState store (CAnd body (CExpr guard)))
    (TSeq then_prefix (TSeq closing then_continuation)) post ->
  RavenHoareTriple (RState store (CAnd body (CExpr (EUnOp UNot guard))))
    (TSeq else_prefix (TSeq closing else_continuation)) post ->
  exists then_open else_open then_closed else_closed,
    RavenHoareTriple (RState store (CAnd body (CExpr guard)))
      (TSeq then_prefix TDone)
      (RState store (CIte guard then_open else_open)) /\
    RavenHoareTriple (RState store (CAnd body (CExpr (EUnOp UNot guard))))
      (TSeq else_prefix TDone)
      (RState store (CIte guard then_open else_open)) /\
    RavenHoareTriple
      (RState store (CAnd (CIte guard then_open else_open) (CExpr guard)))
      (TSeq closing TDone) (RState store (CIte guard then_closed else_closed)) /\
    RavenHoareTriple
      (RState store (CAnd (CIte guard then_open else_open)
        (CExpr (EUnOp UNot guard))))
      (TSeq closing TDone) (RState store (CIte guard then_closed else_closed)) /\
    RavenHoareTriple
      (RState store (CAnd (CIte guard then_closed else_closed) (CExpr guard)))
      then_continuation post /\
    RavenHoareTriple
      (RState store (CAnd (CIte guard then_closed else_closed)
        (CExpr (EUnOp UNot guard))))
      else_continuation post.
Proof.
  intros Hthen_proof Helse_proof Hclosing_writes Hthen Helse.
  destruct (RavenHoareTriple_sequence_decompose _ _ Hthen)
    as (then_joined & Hthen_prefix & Hthen_tail).
  destruct (RavenHoareTriple_sequence_decompose _ _ Hthen_tail)
    as (then_folded & Hthen_closing & Hthen_continuation).
  destruct (RavenHoareTriple_sequence_decompose _ _ Helse)
    as (else_joined & Helse_prefix & Helse_tail).
  destruct (RavenHoareTriple_sequence_decompose _ _ Helse_tail)
    as (else_folded & Helse_closing & Helse_continuation).
  destruct (branch_split store body guard then_prefix closing then_continuation
    then_joined then_folded post Hthen_proof Hclosing_writes Hthen_prefix
    Hthen_closing Hthen_continuation) as (H1t & H2t & H3t).
  destruct (branch_split store body (EUnOp UNot guard) else_prefix closing
    else_continuation else_joined else_folded post Helse_proof Hclosing_writes
    Helse_prefix Helse_closing Helse_continuation) as (H1e & H2e & H3e).
  exists (tracked_core store then_joined), (tracked_core store else_joined),
    (tracked_core store then_folded), (tracked_core store else_folded).
  repeat split.
  - eapply RTPrenexConsequence;
      [exact H1t | apply resource_prenex_entails_refl|].
    apply RPEBody. split; [reflexivity|]. apply CEntailsStep, CESIteIntroTrue.
  - eapply RTPrenexConsequence;
      [exact H1e | apply resource_prenex_entails_refl|].
    apply RPEBody. split; [reflexivity|]. apply CEntailsStep, CESIteIntroFalse.
  - eapply RTConsequence; [| apply ite_keep_then |].
    + apply RTFrame. exact H2t.
    + apply RPEBody. split; [reflexivity|]. apply CEntailsStep, CESIteIntroTrue.
  - eapply RTConsequence; [| apply ite_keep_else |].
    + apply RTFrame. exact H2e.
    + apply RPEBody. split; [reflexivity|]. apply CEntailsStep, CESIteIntroFalse.
  - eapply RTConsequence;
      [exact H3t | | apply resource_prenex_entails_refl].
    apply CEntailsStep, CESIteTrue.
  - eapply RTConsequence;
      [exact H3e | | apply resource_prenex_entails_refl].
    apply CEntailsStep, CESIteFalse.
Qed.

Definition factored_closing {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (condition : gexpr Γ TBool) : stmt Γ :=
  TGhostIf condition (TSeq (TFold invariant arguments) TDone)
    (TSeq (TFold invariant arguments) TDone).

Lemma factor_prenex {Γ F Δ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (condition : rexpr Γ TBool)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ)
    (carried post : resource_prenex Γ F Δ) :
  proof_onlyb then_prefix = true ->
  proof_onlyb else_prefix = true ->
  RavenHoareTriple (guard_prenex true (pexpr_forget condition) carried)
    (TSeq then_prefix (TSeq (TFold invariant arguments) then_continuation))
    post ->
  RavenHoareTriple (guard_prenex false (pexpr_forget condition) carried)
    (TSeq else_prefix (TSeq (TFold invariant arguments) else_continuation))
    post ->
  exists joined,
    RavenHoareTriple carried
      (TIf condition (TSeq then_prefix TDone) (TSeq else_prefix TDone)) joined /\
    RavenHoareTriple joined
      (TSeq (factored_closing invariant arguments (pexpr_forget condition))
        (TIf condition then_continuation else_continuation)) post.
Proof.
  intros Hthen_proof Helse_proof. revert post.
  induction carried as [Δ [store body] | Δ t rest IH]; intros post Hthen Helse.
  - cbn in Hthen, Helse. rewrite symbolize_expr_forget in Hthen, Helse.
    destruct (factor_join store body (symbolize_expr store condition)
      (TFold invariant arguments) then_prefix then_continuation else_prefix
      else_continuation post Hthen_proof Helse_proof eq_refl Hthen Helse)
      as (then_open & else_open & then_closed & else_closed &
        H1t & H1e & H2t & H2e & H3t & H3e).
    exists (RState store
      (CIte (symbolize_expr store condition) then_open else_open)).
    split.
    + apply RTIf; assumption.
    + eapply RTSeq; [| apply RTIf; eassumption].
      unfold factored_closing. apply RTGhostIf; try reflexivity;
        rewrite symbolize_expr_forget; eassumption.
  - cbn in Hthen, Helse.
    destruct (IH (weaken_resource_prenex post)
      (RavenHoareTriple_under_exists _ _ _
        (resource_prenex_entails_refl _) Hthen)
      (RavenHoareTriple_under_exists _ _ _
        (resource_prenex_entails_refl _) Helse)) as (joined & Hinner & Hrest).
    exists (ResourceExists t joined). split.
    + apply RTPrenexPreserve. exact Hinner.
    + apply RTPrenexElim. exact Hrest.
Qed.

Lemma RavenHoareTriple_factor_access {Γ F Δ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix then_prefix then_continuation else_prefix else_continuation : stmt Γ)
    (condition : rexpr Γ TBool) (pre post : resource_prenex Γ F Δ) :
  proof_onlyb then_prefix = true ->
  proof_onlyb else_prefix = true ->
  RavenHoareTriple pre
    (TSeq (TUnfold invariant arguments)
      (TSeq prefix
        (TIf condition
          (TSeq then_prefix (TSeq (TFold invariant arguments) then_continuation))
          (TSeq else_prefix
            (TSeq (TFold invariant arguments) else_continuation))))) post ->
  RavenHoareTriple pre
    (TSeq (TUnfold invariant arguments)
      (TSeq
        (TSeq prefix
          (TSeq TDone
            (TIf condition (TSeq then_prefix TDone) (TSeq else_prefix TDone))))
        (TSeq (factored_closing invariant arguments (pexpr_forget condition))
          (TIf condition then_continuation else_continuation)))) post.
Proof.
  intros Hthen_proof Helse_proof Hsource.
  destruct (RavenHoareTriple_sequence_decompose _ _ Hsource)
    as (opened & Hunfold & Htail).
  destruct (RavenHoareTriple_sequence_decompose _ _ Htail)
    as (joined & Hprefix & Hif).
  destruct (RavenHoareTriple_if_inversion _ _ _ _ _ Hif)
    as (carried & Hdone & Hthen & Helse).
  destruct (factor_prenex invariant arguments condition then_prefix
    then_continuation else_prefix else_continuation carried post Hthen_proof
    Helse_proof Hthen Helse) as (inner & Hinner & Hrest).
  eapply RTSeq; [exact Hunfold|].
  eapply RTSeq; [| exact Hrest].
  eapply RTSeq; [exact Hprefix|].
  eapply RTSeq; [exact Hdone | exact Hinner].
Qed.

Lemma factor_prenex_ghost {Γ F Δ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (condition : gexpr Γ TBool)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ)
    (carried post : resource_prenex Γ F Δ) :
  proof_onlyb then_prefix = true ->
  proof_onlyb else_prefix = true ->
  proof_onlyb then_continuation = true ->
  proof_onlyb else_continuation = true ->
  RavenHoareTriple (guard_prenex true condition carried)
    (TSeq then_prefix (TSeq (TFold invariant arguments) then_continuation))
    post ->
  RavenHoareTriple (guard_prenex false condition carried)
    (TSeq else_prefix (TSeq (TFold invariant arguments) else_continuation))
    post ->
  exists joined,
    RavenHoareTriple carried
      (TGhostIf condition (TSeq then_prefix TDone) (TSeq else_prefix TDone))
      joined /\
    RavenHoareTriple joined
      (TSeq (factored_closing invariant arguments condition)
        (TGhostIf condition then_continuation else_continuation)) post.
Proof.
  intros Hthen_proof Helse_proof Hthen_rest Helse_rest. revert post.
  induction carried as [Δ [store body] | Δ t rest IH]; intros post Hthen Helse.
  - cbn in Hthen, Helse.
    destruct (factor_join store body (symbolize_expr store condition)
      (TFold invariant arguments) then_prefix then_continuation else_prefix
      else_continuation post Hthen_proof Helse_proof eq_refl Hthen Helse)
      as (then_open & else_open & then_closed & else_closed &
        H1t & H1e & H2t & H2e & H3t & H3e).
    exists (RState store
      (CIte (symbolize_expr store condition) then_open else_open)).
    split.
    + apply RTGhostIf; try assumption;
        cbn; rewrite ?Hthen_proof, ?Helse_proof; reflexivity.
    + eapply RTSeq; [| apply RTGhostIf; eassumption].
      unfold factored_closing. apply RTGhostIf; try reflexivity; eassumption.
  - cbn in Hthen, Helse.
    destruct (IH (weaken_resource_prenex post)
      (RavenHoareTriple_under_exists _ _ _
        (resource_prenex_entails_refl _) Hthen)
      (RavenHoareTriple_under_exists _ _ _
        (resource_prenex_entails_refl _) Helse)) as (joined & Hinner & Hrest).
    exists (ResourceExists t joined). split.
    + apply RTPrenexPreserve. exact Hinner.
    + apply RTPrenexElim. exact Hrest.
Qed.

Lemma RavenHoareTriple_factor_ghost_access {Γ F Δ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix then_prefix then_continuation else_prefix else_continuation : stmt Γ)
    (condition : gexpr Γ TBool) (pre post : resource_prenex Γ F Δ) :
  proof_onlyb then_prefix = true ->
  proof_onlyb else_prefix = true ->
  proof_onlyb then_continuation = true ->
  proof_onlyb else_continuation = true ->
  RavenHoareTriple pre
    (TSeq (TUnfold invariant arguments)
      (TSeq prefix
        (TGhostIf condition
          (TSeq then_prefix (TSeq (TFold invariant arguments) then_continuation))
          (TSeq else_prefix
            (TSeq (TFold invariant arguments) else_continuation))))) post ->
  RavenHoareTriple pre
    (TSeq (TUnfold invariant arguments)
      (TSeq
        (TSeq prefix
          (TSeq TDone
            (TGhostIf condition (TSeq then_prefix TDone)
              (TSeq else_prefix TDone))))
        (TSeq (factored_closing invariant arguments condition)
          (TGhostIf condition then_continuation else_continuation)))) post.
Proof.
  intros Hthen_proof Helse_proof Hthen_rest Helse_rest Hsource.
  destruct (RavenHoareTriple_sequence_decompose _ _ Hsource)
    as (opened & Hunfold & Htail).
  destruct (RavenHoareTriple_sequence_decompose _ _ Htail)
    as (joined & Hprefix & Hif).
  destruct (RavenHoareTriple_ghost_if_inversion _ _ _ _ _ Hif)
    as (carried & Hdone & Hthen & Helse).
  destruct (factor_prenex_ghost invariant arguments condition then_prefix
    then_continuation else_prefix else_continuation carried post Hthen_proof
    Helse_proof Hthen_rest Helse_rest Hthen Helse) as (inner & Hinner & Hrest).
  eapply RTSeq; [exact Hunfold|].
  eapply RTSeq; [| exact Hrest].
  eapply RTSeq; [exact Hprefix|].
  eapply RTSeq; [exact Hdone | exact Hinner].
Qed.

(** ** Normalization targets

    A conditional access in canonical layout is normalized either by
    distributing the access into the branches (nothing physical precedes the
    conditional) or by factoring it out (the branch prefixes are
    proof-only). *)

Inductive access_guard (Γ : decl_context) : Type :=
| GuardRuntime (condition : rexpr Γ TBool)
| GuardGhost (condition : gexpr Γ TBool).
#[global] Arguments GuardRuntime {_} _.
#[global] Arguments GuardGhost {_} _.

Definition guard_if {Γ} (guard : access_guard Γ) (then_branch else_branch : stmt Γ) :
    stmt Γ :=
  match guard with
  | GuardRuntime condition => TIf condition then_branch else_branch
  | GuardGhost condition => TGhostIf condition then_branch else_branch
  end.

Definition guard_condition {Γ} (guard : access_guard Γ) : gexpr Γ TBool :=
  match guard with
  | GuardRuntime condition => pexpr_forget condition
  | GuardGhost condition => condition
  end.

(** The branches a ghost guard requires to be proof-only. *)
Definition guard_proof_only {Γ} (guard : access_guard Γ)
    (then_branch else_branch : stmt Γ) : bool :=
  match guard with
  | GuardRuntime _ => true
  | GuardGhost _ => proof_onlyb then_branch && proof_onlyb else_branch
  end.

Definition conditional_access {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ) :
    stmt Γ :=
  TSeq (TUnfold invariant arguments)
    (TSeq prefix
      (guard_if guard
        (canonical_branch invariant arguments then_prefix then_continuation)
        (canonical_branch invariant arguments else_prefix else_continuation))).

Definition distributed_access {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ) :
    stmt Γ :=
  guard_if guard
    (TSeq (TInvAccess invariant arguments (TSeq prefix (TSeq TDone then_prefix)))
      then_continuation)
    (TSeq (TInvAccess invariant arguments (TSeq prefix (TSeq TDone else_prefix)))
      else_continuation).

Definition factored_access {Γ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ) :
    stmt Γ :=
  TSeq
    (TInvAccess invariant arguments
      (TSeq prefix
        (TSeq TDone
          (guard_if guard (TSeq then_prefix TDone) (TSeq else_prefix TDone)))))
    (guard_if guard then_continuation else_continuation).

(** Every derivation of [statement] is one of [statement']. *)
Definition simulates {Γ} (statement statement' : stmt Γ) : Prop :=
  forall F Δ (pre post : resource_prenex Γ F Δ),
  RavenHoareTriple pre statement post -> RavenHoareTriple pre statement' post.

Lemma RavenHoareTriple_guard_if_congruence {Γ F Δ} (guard : access_guard Γ)
    (then_branch else_branch then_branch' else_branch' : stmt Γ)
    (pre post : resource_prenex Γ F Δ) :
  simulates then_branch then_branch' ->
  simulates else_branch else_branch' ->
  statement_writes then_branch' ⊆ statement_writes then_branch ->
  statement_writes else_branch' ⊆ statement_writes else_branch ->
  guard_proof_only guard then_branch' else_branch' = true ->
  RavenHoareTriple pre (guard_if guard then_branch else_branch) post ->
  RavenHoareTriple pre (guard_if guard then_branch' else_branch') post.
Proof.
  intros Hthen Helse Hthen_writes Helse_writes Hproof derivation.
  destruct guard as [condition|condition]; cbn [guard_if guard_proof_only] in *.
  - dependent induction derivation.
    + apply RTPrenexPreserve. eapply IHderivation; eauto.
    + apply RTBoundWeaken. eapply IHderivation; eauto.
    + apply RTPrenexElim. eapply IHderivation; eauto.
    + eapply RTPrenexConsequence; [eapply IHderivation; eauto | eassumption..].
    + apply RTFrame. eapply IHderivation; eauto.
    + eapply RTConsequence; [eapply IHderivation; eauto | eassumption..].
    + eapply RTStackRewrite; [eapply IHderivation; eauto | eassumption].
    + apply RTIf; [apply Hthen | apply Helse]; assumption.
    + apply RTTrack; [cbn [statement_writes] in *; set_solver |].
      eapply IHderivation; eauto.
  - apply andb_prop in Hproof as [Hthen_proof Helse_proof].
    dependent induction derivation.
    + apply RTPrenexPreserve. eapply IHderivation; eauto.
    + apply RTBoundWeaken. eapply IHderivation; eauto.
    + apply RTPrenexElim. eapply IHderivation; eauto.
    + eapply RTPrenexConsequence; [eapply IHderivation; eauto | eassumption..].
    + apply RTFrame. eapply IHderivation; eauto.
    + eapply RTConsequence; [eapply IHderivation; eauto | eassumption..].
    + eapply RTStackRewrite; [eapply IHderivation; eauto | eassumption].
    + apply RTGhostIf; [assumption | assumption | apply Hthen | apply Helse];
        assumption.
    + apply RTTrack; [cbn [statement_writes] in *; set_solver |].
      eapply IHderivation; eauto.
Qed.

Lemma access_closing_factored_complete {Γ F Δ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (condition : gexpr Γ TBool) (body_post external_post : resource_prenex Γ F Δ) :
  RavenHoareTriple body_post (factored_closing invariant arguments condition)
    external_post ->
  exists focus : access_focus invariant arguments Δ,
    access_closing invariant arguments focus body_post external_post.
Proof.
  unfold factored_closing. intro derivation. dependent induction derivation.
  - destruct (IHderivation invariant arguments condition eq_refl)
      as (focus & Hclosing).
    eexists.
    apply AccessClosingPreserve. exact Hclosing.
  - destruct (IHderivation invariant arguments condition eq_refl)
      as (focus & Hclosing).
    eexists.
    apply AccessClosingBoundWeaken. exact Hclosing.
  - destruct (IHderivation invariant arguments condition eq_refl)
      as (focus & Hclosing).
    eexists.
    apply AccessClosingElim. exact Hclosing.
  - destruct (IHderivation invariant arguments condition eq_refl)
      as (focus & Hclosing). exists focus.
    eapply AccessClosingConsequence; eassumption.
  - destruct (IHderivation invariant arguments condition eq_refl)
      as (focus & Hclosing). exists focus.
    change (access_closing invariant arguments focus
      (prenex_and (RState store pre_body) frame) (prenex_and post frame)).
    apply AccessClosingFrame. exact Hclosing.
  - destruct (IHderivation invariant arguments condition eq_refl)
      as (focus & Hclosing). exists focus.
    eapply AccessClosingConsequence with
      (body_post := RState store pre_body) (external_post := post).
    + apply RPEBody. split; [reflexivity|exact H].
    + exact Hclosing.
    + exact H0.
  - destruct (IHderivation invariant arguments condition eq_refl)
      as (focus & Hclosing). exists focus.
    eapply AccessClosingStackRewrite; eassumption.
  - destruct (access_closing_fold_done_complete arguments _ _ derivation1)
      as (focus & Hthen).
    destruct (access_closing_fold_done_complete arguments _ _ derivation2)
      as (else_focus & Helse).
    exists focus. eapply AccessClosingIte; eassumption.
  - destruct (IHderivation invariant arguments condition eq_refl)
      as (focus & Hclosing). exists focus.
    apply AccessClosingTrack. exact Hclosing.
Qed.

Lemma RavenHoareTriple_access_of_raw {Γ F Δ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (body : stmt Γ) (pre post : resource_prenex Γ F Δ) :
  pexpr_list_dependencies arguments ## statement_writes body ->
  RavenHoareTriple pre
    (TSeq (TUnfold invariant arguments) (TSeq body (TFold invariant arguments)))
    post ->
  RavenHoareTriple pre (TInvAccess invariant arguments body) post.
Proof.
  intros Hstable Hraw.
  destruct (RavenHoareTriple_unfold_body_fold_spines invariant arguments body
    pre post Hraw) as (body_pre & body_post & opening_focus & closing_focus &
      Hopening & Hbody & Hclosing).
  eapply RTInvAccessIndependent; eassumption.
Qed.

Lemma RavenHoareTriple_distributed_access {Γ F Δ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation
      prefix' then_prefix' then_continuation' else_prefix'
      else_continuation' : stmt Γ)
    (pre post : resource_prenex Γ F Δ) :
  proof_onlyb prefix = true ->
  guard_proof_only guard
    (canonical_branch invariant arguments then_prefix then_continuation)
    (canonical_branch invariant arguments else_prefix else_continuation) = true ->
  guard_proof_only guard
    (TSeq (TInvAccess invariant arguments (TSeq prefix' (TSeq TDone then_prefix')))
      then_continuation')
    (TSeq (TInvAccess invariant arguments (TSeq prefix' (TSeq TDone else_prefix')))
      else_continuation') = true ->
  pexpr_list_dependencies arguments ##
    statement_writes (TSeq prefix (TSeq TDone then_prefix)) ->
  pexpr_list_dependencies arguments ##
    statement_writes (TSeq prefix (TSeq TDone else_prefix)) ->
  simulates prefix prefix' -> simulates then_prefix then_prefix' ->
  simulates else_prefix else_prefix' ->
  simulates then_continuation then_continuation' ->
  simulates else_continuation else_continuation' ->
  statement_writes prefix' ⊆ statement_writes prefix ->
  statement_writes then_prefix' ⊆ statement_writes then_prefix ->
  statement_writes else_prefix' ⊆ statement_writes else_prefix ->
  statement_writes then_continuation' ⊆ statement_writes then_continuation ->
  statement_writes else_continuation' ⊆ statement_writes else_continuation ->
  RavenHoareTriple pre
    (conditional_access invariant arguments prefix guard then_prefix
      then_continuation else_prefix else_continuation) post ->
  RavenHoareTriple pre
    (distributed_access invariant arguments prefix' guard then_prefix'
      then_continuation' else_prefix' else_continuation') post.
Proof.
  intros Hprefix Hsource_proof Htarget_proof Hthen_stable Helse_stable
    Hq_sim Htp_sim Hep_sim Hthen_sim Helse_sim Hq_writes Htp_writes Hep_writes
    Hthen_writes Helse_writes Hsource.
  assert (Hbranch : forall branch_prefix branch_prefix' continuation
      continuation',
    pexpr_list_dependencies arguments ##
      statement_writes (TSeq prefix (TSeq TDone branch_prefix)) ->
    simulates branch_prefix branch_prefix' ->
    statement_writes branch_prefix' ⊆ statement_writes branch_prefix ->
    simulates continuation continuation' ->
    simulates
      (TSeq (TUnfold invariant arguments) (TSeq prefix (TSeq TDone
        (canonical_branch invariant arguments branch_prefix continuation))))
      (TSeq (TInvAccess invariant arguments
        (TSeq prefix' (TSeq TDone branch_prefix'))) continuation')).
  { intros branch_prefix branch_prefix' continuation continuation' Hstable
      Hp_sim Hp_writes Hsim F' Δ' P Q D.
    unfold canonical_branch in D.
    destruct (RavenHoareTriple_sequence_decompose _ _ D) as (M1 & Hu & D1).
    destruct (RavenHoareTriple_sequence_decompose _ _ D1) as (M2 & Hq & D2).
    destruct (RavenHoareTriple_sequence_decompose _ _ D2) as (M3 & Hd & D3).
    destruct (RavenHoareTriple_sequence_decompose _ _ D3) as (M4 & Hp & D4).
    destruct (RavenHoareTriple_sequence_decompose _ _ D4) as (M5 & Hf & Hc).
    eapply RTSeq; [| exact (Hsim _ _ _ _ Hc)].
    apply RavenHoareTriple_access_of_raw;
      [cbn [statement_writes] in *; set_solver|].
    eapply RTSeq; [exact Hu|].
    eapply RTSeq; [| exact Hf].
    eapply RTSeq; [exact (Hq_sim _ _ _ _ Hq)|].
    eapply RTSeq; [exact Hd | exact (Hp_sim _ _ _ _ Hp)]. }
  assert (Hwrites : forall branch_prefix branch_prefix' continuation
      continuation' : stmt Γ,
    statement_writes branch_prefix' ⊆ statement_writes branch_prefix ->
    statement_writes continuation' ⊆ statement_writes continuation ->
    statement_writes (TSeq (TInvAccess invariant arguments
        (TSeq prefix' (TSeq TDone branch_prefix'))) continuation') ⊆
      statement_writes (TSeq (TUnfold invariant arguments) (TSeq prefix
        (TSeq TDone (canonical_branch invariant arguments branch_prefix
          continuation))))).
  { intros. unfold canonical_branch. cbn [statement_writes]. set_solver. }
  assert (Hdistributed : RavenHoareTriple pre
    (guard_if guard
      (TSeq (TUnfold invariant arguments) (TSeq prefix (TSeq TDone
        (canonical_branch invariant arguments then_prefix then_continuation))))
      (TSeq (TUnfold invariant arguments) (TSeq prefix (TSeq TDone
        (canonical_branch invariant arguments else_prefix else_continuation)))))
    post).
  { destruct guard as [condition|condition];
      cbn [guard_if guard_proof_only] in *.
    - apply RavenHoareTriple_distribute_access; assumption.
    - apply andb_prop in Hsource_proof as [Hthen_proof Helse_proof].
      apply RavenHoareTriple_distribute_ghost_access; assumption. }
  unfold distributed_access.
  refine (RavenHoareTriple_guard_if_congruence guard _ _ _ _ _ _ _ _ _ _ _
    Hdistributed).
  - apply Hbranch; assumption.
  - apply Hbranch; assumption.
  - apply Hwrites; assumption.
  - apply Hwrites; assumption.
  - exact Htarget_proof.
Qed.

Lemma RavenHoareTriple_factored_access {Γ F Δ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation
      prefix' then_continuation' else_continuation' : stmt Γ)
    (pre post : resource_prenex Γ F Δ) :
  proof_onlyb then_prefix = true ->
  proof_onlyb else_prefix = true ->
  guard_proof_only guard then_continuation else_continuation = true ->
  guard_proof_only guard then_continuation' else_continuation' = true ->
  pexpr_list_dependencies arguments ## statement_writes prefix ->
  simulates prefix prefix' ->
  statement_writes prefix' ⊆ statement_writes prefix ->
  simulates then_continuation then_continuation' ->
  simulates else_continuation else_continuation' ->
  statement_writes then_continuation' ⊆ statement_writes then_continuation ->
  statement_writes else_continuation' ⊆ statement_writes else_continuation ->
  RavenHoareTriple pre
    (conditional_access invariant arguments prefix guard then_prefix
      then_continuation else_prefix else_continuation) post ->
  RavenHoareTriple pre
    (factored_access invariant arguments prefix' guard then_prefix
      then_continuation' else_prefix else_continuation') post.
Proof.
  intros Hthen_proof Helse_proof Hsource_proof Htarget_proof Hstable
    Hq_sim Hq_writes Hthen_sim Helse_sim Hthen_writes Helse_writes Hsource.
  assert (Hraw : RavenHoareTriple pre
    (TSeq (TUnfold invariant arguments)
      (TSeq
        (TSeq prefix
          (TSeq TDone
            (guard_if guard (TSeq then_prefix TDone) (TSeq else_prefix TDone))))
        (TSeq (factored_closing invariant arguments (guard_condition guard))
          (guard_if guard then_continuation else_continuation)))) post).
  { destruct guard as [condition|condition];
      cbn [guard_if guard_condition guard_proof_only] in *.
    - apply RavenHoareTriple_factor_access; assumption.
    - apply andb_prop in Hsource_proof as [Hthen_rest Helse_rest].
      apply RavenHoareTriple_factor_ghost_access; assumption. }
  destruct (RavenHoareTriple_sequence_decompose _ _ Hraw)
    as (opened & Hunfold & Htail).
  destruct (RavenHoareTriple_sequence_decompose _ _ Htail)
    as (joined & Hbody & Hrest).
  destruct (RavenHoareTriple_sequence_decompose _ _ Hrest)
    as (closed & Hclosing & Hcontinuation).
  destruct (RavenHoareTriple_sequence_decompose _ _ Hbody)
    as (prefixed & Hprefix & Hbody_rest).
  pose proof (RTSeq _ _ _ _ _ (Hq_sim _ _ _ _ Hprefix) Hbody_rest) as Hbody'.
  destruct (access_opening_complete arguments pre opened Hunfold)
    as (opening_focus & Hopening).
  destruct (access_closing_factored_complete invariant arguments _ joined closed
    Hclosing) as (closing_focus & Hclosed).
  unfold factored_access. eapply RTSeq.
  - eapply RTInvAccessIndependent; [| exact Hopening | exact Hbody' | exact Hclosed].
    pose proof (proof_only_writes _ Hthen_proof).
    pose proof (proof_only_writes _ Helse_proof).
    destruct guard; cbn [guard_if statement_writes] in *; set_solver.
  - eapply RavenHoareTriple_guard_if_congruence; eassumption.
Qed.

(** Every piece of a conditional access has a derivation of its own. *)
Lemma conditional_access_piece_derivations {Γ F Δ} invariant
    (arguments : gexpr_list Γ (Assertion.invariant_args invariant))
    (prefix : stmt Γ) (guard : access_guard Γ)
    (then_prefix then_continuation else_prefix else_continuation : stmt Γ)
    (pre post : resource_prenex Γ F Δ) :
  RavenHoareTriple pre
    (conditional_access invariant arguments prefix guard then_prefix
      then_continuation else_prefix else_continuation) post ->
  (exists P Q : resource_prenex Γ F Δ, RavenHoareTriple P prefix Q) /\
  (exists P Q : resource_prenex Γ F Δ, RavenHoareTriple P then_prefix Q) /\
  (exists P Q : resource_prenex Γ F Δ, RavenHoareTriple P else_prefix Q) /\
  (exists P Q : resource_prenex Γ F Δ,
    RavenHoareTriple P then_continuation Q) /\
  (exists P Q : resource_prenex Γ F Δ,
    RavenHoareTriple P else_continuation Q).
Proof.
  intros Hsource.
  destruct (RavenHoareTriple_sequence_decompose _ _ Hsource)
    as (opened & _ & Htail).
  destruct (RavenHoareTriple_sequence_decompose _ _ Htail)
    as (joined & Hprefix & Hif).
  assert (Hbranches : exists P P' Q Q' : resource_prenex Γ F Δ,
    RavenHoareTriple P
      (canonical_branch invariant arguments then_prefix then_continuation) Q /\
    RavenHoareTriple P'
      (canonical_branch invariant arguments else_prefix else_continuation) Q').
  { destruct guard as [condition|condition]; cbn [guard_if] in Hif.
    - destruct (RavenHoareTriple_if_inversion _ _ _ _ _ Hif)
        as (carried & _ & Hthen & Helse).
      do 4 eexists. split; eassumption.
    - destruct (RavenHoareTriple_ghost_if_inversion _ _ _ _ _ Hif)
        as (carried & _ & Hthen & Helse).
      do 4 eexists. split; eassumption. }
  destruct Hbranches as (P & P' & Q & Q' & Hthen & Helse).
  unfold canonical_branch in Hthen, Helse.
  destruct (RavenHoareTriple_sequence_decompose _ _ Hthen) as (M1 & Htp & Ht).
  destruct (RavenHoareTriple_sequence_decompose _ _ Ht) as (M2 & _ & Htc).
  destruct (RavenHoareTriple_sequence_decompose _ _ Helse) as (N1 & Hep & He).
  destruct (RavenHoareTriple_sequence_decompose _ _ He) as (N2 & _ & Hec).
  repeat split; do 2 eexists; eassumption.
Qed.

End WithSignature.
End ConditionalDerivations.
