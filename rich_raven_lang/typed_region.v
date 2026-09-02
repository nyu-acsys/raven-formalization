From iris.proofmode Require Import tactics.

From raven_iris.rich_raven_lang Require Import
  typed_core typed_analysis_view typed_assertion typed_ir typed_translation
  typed_atomicity.

(** Continuation semantics for certificates emitted by the flat atomicity
    analyzer.  An unfold wraps the complete remaining continuation, so its
    linear Iris close capability can flow to a later fold without appearing
    in Raven assertions or escaping the certified region. *)
Module TypedRegion.

Import TypedCore TypedIR.

Module Generic (Syntax : TypedAnalysisView.ANALYSIS_SYNTAX).
Module Atomicity := TypedAnalysisView.Analysis Syntax.
Import Atomicity.

Module Type REGION_MODEL.
  Parameter PROP : bi.
  Parameter stack_context : context -> Type.
  Parameter ambient_mask : Type.
End REGION_MODEL.

Module Semantics (Model : REGION_MODEL).
Local Notation iProp := (bi_car Model.PROP).

Module Type REGION_PRIMITIVES.
  Parameter operation_wp : forall Γ, Model.stack_context Γ -> Model.ambient_mask ->
    analysis_state -> Syntax.statement Γ -> analysis_state -> iProp -> iProp.
  Parameter branch_wp : forall Γ, Model.stack_context Γ -> Model.ambient_mask ->
    analysis_state -> Syntax.statement Γ -> analysis_state -> analysis_state ->
    iProp -> iProp -> iProp.
  Parameter operation_mono : forall Γ runtime ambient entry statement exit P Q,
    (P ⊢ Q) -> operation_wp Γ runtime ambient entry statement exit P ⊢
      operation_wp Γ runtime ambient entry statement exit Q.
  Parameter operation_frame : forall Γ runtime ambient entry statement exit P R,
    operation_wp Γ runtime ambient entry statement exit P ∗ R ⊢
      operation_wp Γ runtime ambient entry statement exit (P ∗ R).
  Parameter branch_mono : forall Γ runtime ambient entry statement then_exit else_exit
      P P' Q Q',
    (P ⊢ P') -> (Q ⊢ Q') ->
    branch_wp Γ runtime ambient entry statement then_exit else_exit P Q ⊢
      branch_wp Γ runtime ambient entry statement then_exit else_exit P' Q'.
  Parameter branch_frame : forall Γ runtime ambient entry statement then_exit else_exit
      P Q R,
    branch_wp Γ runtime ambient entry statement then_exit else_exit P Q ∗ R ⊢
      branch_wp Γ runtime ambient entry statement then_exit else_exit (P ∗ R) (Q ∗ R).
End REGION_PRIMITIVES.

Module Interpreter (Primitives : REGION_PRIMITIVES).

  Fixpoint region_wp {Γ fuel entry statement exit} {cost : cost_model}
    (certificate : analysis_certificate cost Γ fuel entry statement exit) :
    Model.stack_context Γ -> Model.ambient_mask -> iProp -> iProp :=
  match certificate in analysis_certificate _ Γ' _ entry' statement' exit'
      return Model.stack_context Γ' -> Model.ambient_mask -> iProp -> iProp with
  | @CertLeaf _ Γ' _ entry' statement' exit' _ _ =>
      fun runtime ambient post =>
        Primitives.operation_wp Γ' runtime ambient entry' statement' exit' post
  | @CertUnfold _ Γ' _ entry' statement' _ exit' _ _ =>
      fun runtime ambient post =>
        Primitives.operation_wp Γ' runtime ambient entry' statement' exit' post
  | @CertFold _ Γ' _ entry' statement' invariant _ =>
      fun runtime ambient post => Primitives.operation_wp Γ' runtime ambient entry' statement'
        (fold_invariant invariant entry') post
  | @CertSequence _ _ _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      fun runtime ambient post => region_wp first_certificate runtime ambient
        (region_wp second_certificate runtime ambient post)
  | @CertConditional _ Γ' _ entry' statement' _ _ then_exit else_exit _
      then_certificate else_certificate _ _ =>
      fun runtime ambient post => Primitives.branch_wp Γ' runtime ambient entry' statement'
        then_exit else_exit (region_wp then_certificate runtime ambient post)
        (region_wp else_certificate runtime ambient post)
  | @CertAtomic _ Γ' _ entry' statement' _ outer inner _ _
      body_certificate _ =>
      fun runtime ambient post => Primitives.operation_wp Γ' runtime ambient entry' statement'
        (AnalysisState (analysis_mask inner) (analysis_open inner)
          (analysis_step_taken outer || analysis_step_taken inner)
          (analysis_in_atomic outer))
        (region_wp body_certificate runtime ambient post)
  end.

Lemma region_wp_mono {Γ fuel entry statement exit}
    (runtime : Model.stack_context Γ) (ambient : Model.ambient_mask) {cost : cost_model}
    (certificate : analysis_certificate cost Γ fuel entry statement exit) P Q :
  (P ⊢ Q) -> region_wp certificate runtime ambient P ⊢ region_wp certificate runtime ambient Q.
Proof.
  revert P Q. induction certificate; intros P Q HPQ; simpl.
  - apply Primitives.operation_mono. exact HPQ.
  - apply Primitives.operation_mono. exact HPQ.
  - apply Primitives.operation_mono. exact HPQ.
  - apply IHcertificate1. apply IHcertificate2. exact HPQ.
  - apply Primitives.branch_mono; [apply IHcertificate1|apply IHcertificate2];
      exact HPQ.
  - apply Primitives.operation_mono. apply IHcertificate. exact HPQ.
Qed.

Lemma region_wp_frame {Γ fuel entry statement exit}
    (runtime : Model.stack_context Γ) (ambient : Model.ambient_mask) {cost : cost_model}
    (certificate : analysis_certificate cost Γ fuel entry statement exit) P R :
  region_wp certificate runtime ambient P ∗ R ⊢
    region_wp certificate runtime ambient (P ∗ R).
Proof.
  revert P R. induction certificate; intros P R; simpl.
  - apply Primitives.operation_frame.
  - apply Primitives.operation_frame.
  - apply Primitives.operation_frame.
  - iIntros "[H HR]".
    iPoseProof (IHcertificate1 runtime
      (region_wp certificate2 runtime ambient P) R with "[$H $HR]") as "H".
    iApply (region_wp_mono with "H"). apply (IHcertificate2 runtime).
  - etrans; first apply Primitives.branch_frame.
    apply Primitives.branch_mono;
      [apply (IHcertificate1 runtime)|apply (IHcertificate2 runtime)].
  - etrans; first apply Primitives.operation_frame.
    apply Primitives.operation_mono. apply (IHcertificate runtime).
Qed.

End Interpreter.
End Semantics.
End Generic.

Module Make (RAs : RA_VALUE_CONFIG) (Logic : TypedAssertion.LOGIC_SIGNATURE).
Module Atomicity := TypedAtomicity.Make RAs Logic.
Module IR := Atomicity.IR.
Module Core := Atomicity.Core.
Module Assertions := Atomicity.Assertions.
Import Core Assertions IR Atomicity.

Module CertifiedLogic (Contracts : Hoare.CONTRACT_ENV).
Module Rules := Hoare.LogicRules Contracts.

(** The certificate and proof derivation share the exact typed statement and
    agree on its flat mask transition.  Keeping the pair explicit is useful:
    the certificate controls accessor lifetime and physical-step accounting,
    while the Hoare derivation controls assertion resources. *)
Record CertifiedRavenHoareTriple (cost : cost_model) {Γ F Δ}
    (pre : assertion Γ F Δ) (statement : stmt Γ)
    (entry exit : analysis_state) (post : assertion Γ F Δ) : Type := {
  certified_analysis : analysis_certificate cost Γ entry statement exit;
  certified_hoare : @Rules.RavenHoareTriple Γ F Δ pre statement
    (analysis_mask entry) (analysis_mask exit) post;
}.

Lemma certified_exit_wf cost {Γ F Δ} pre (statement : stmt Γ) entry exit post :
  state_wf entry ->
  CertifiedRavenHoareTriple cost (F := F) (Δ := Δ)
    pre statement entry exit post ->
  state_wf exit.
Proof.
  intros Hwf certified.
  destruct certified as [certificate _].
  eapply analyze_preserves_wf; [exact Hwf|].
  apply certificate_replays. exact certificate.
Qed.

End CertifiedLogic.

Module Type REGION_MODEL.
  Parameter PROP : bi.
  Parameter stack_context : context -> Type.
End REGION_MODEL.

Module Semantics (Model : REGION_MODEL).
Local Notation iProp := (bi_car Model.PROP).

Module Type REGION_PRIMITIVES.
  Parameter leaf_wp : forall Γ, Model.stack_context Γ ->
    analysis_state -> stmt Γ -> analysis_state -> iProp -> iProp.
  Parameter unfold_wp : forall Γ, Model.stack_context Γ ->
    analysis_state -> node_id -> forall invariant,
    pexpr_list Γ (Logic.invariant_args invariant) ->
    analysis_state -> iProp -> iProp.
  Parameter fold_wp : forall Γ, Model.stack_context Γ ->
    analysis_state -> node_id -> forall invariant,
    pexpr_list Γ (Logic.invariant_args invariant) ->
    analysis_state -> iProp -> iProp.
  Parameter branch_wp : forall Γ, Model.stack_context Γ ->
    pexpr Γ TBool -> analysis_state -> analysis_state -> analysis_state ->
    iProp -> iProp -> iProp.
  Parameter atomic_wp : forall Γ, Model.stack_context Γ ->
    analysis_state -> stmt Γ -> analysis_state -> iProp -> iProp.

  Parameter leaf_mono : forall Γ runtime entry statement exit P Q,
    (P ⊢ Q) ->
    leaf_wp Γ runtime entry statement exit P ⊢
      leaf_wp Γ runtime entry statement exit Q.
  Parameter unfold_mono : forall Γ runtime entry node invariant arguments
      exit P Q,
    (P ⊢ Q) ->
    unfold_wp Γ runtime entry node invariant arguments exit P ⊢
      unfold_wp Γ runtime entry node invariant arguments exit Q.
  Parameter fold_mono : forall Γ runtime entry node invariant arguments
      exit P Q,
    (P ⊢ Q) ->
    fold_wp Γ runtime entry node invariant arguments exit P ⊢
      fold_wp Γ runtime entry node invariant arguments exit Q.
  Parameter branch_mono : forall Γ runtime condition entry then_exit else_exit
      P P' Q Q',
    (P ⊢ P') -> (Q ⊢ Q') ->
    branch_wp Γ runtime condition entry then_exit else_exit P Q ⊢
      branch_wp Γ runtime condition entry then_exit else_exit P' Q'.
  Parameter atomic_mono : forall Γ runtime entry body exit P Q,
    (P ⊢ Q) ->
    atomic_wp Γ runtime entry body exit P ⊢
      atomic_wp Γ runtime entry body exit Q.
End REGION_PRIMITIVES.

Module Interpreter (Primitives : REGION_PRIMITIVES).

Fixpoint region_wp {Γ entry statement exit} {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit) :
    Model.stack_context Γ -> iProp -> iProp :=
  match certificate in analysis_certificate _ Γ' entry' statement' exit'
      return Model.stack_context Γ' -> iProp -> iProp with
  | @CertLeaf _ Γ' entry' statement' exit' _ _ =>
      fun runtime post =>
        Primitives.leaf_wp Γ' runtime entry' statement' exit' post
  | @CertUnfold _ Γ' entry' node invariant arguments exit' _ =>
      fun runtime post => Primitives.unfold_wp Γ' runtime entry' node invariant
        arguments exit' post
  | @CertFold _ Γ' entry' node invariant arguments =>
      fun runtime post => Primitives.fold_wp Γ' runtime entry' node invariant
        arguments (fold_invariant invariant entry') post
  | @CertSeq _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      fun runtime post => region_wp first_certificate runtime
        (region_wp second_certificate runtime post)
  | @CertIf _ Γ' entry' _ condition _ _ then_exit else_exit
      then_certificate else_certificate _ _ =>
      fun runtime post => Primitives.branch_wp Γ' runtime condition entry'
        then_exit else_exit
        (region_wp then_certificate runtime post)
        (region_wp else_certificate runtime post)
  | @CertAtomic _ Γ' entry' _ body outer inner _ body_certificate _ =>
      fun runtime post => Primitives.atomic_wp Γ' runtime entry' body
        (AnalysisState (analysis_mask inner) (analysis_open inner)
          (analysis_step_taken outer || analysis_step_taken inner)
          (analysis_in_atomic outer))
        (region_wp body_certificate runtime post)
  end.

Lemma region_wp_mono {Γ entry statement exit}
  (runtime : Model.stack_context Γ) {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit) P Q :
  (P ⊢ Q) -> region_wp certificate runtime P ⊢ region_wp certificate runtime Q.
Proof.
  revert P Q. induction certificate; intros P Q HPQ; simpl.
  - apply Primitives.leaf_mono. exact HPQ.
  - apply Primitives.unfold_mono. exact HPQ.
  - apply Primitives.fold_mono. exact HPQ.
  - apply IHcertificate1. apply IHcertificate2. exact HPQ.
  - apply Primitives.branch_mono; [apply IHcertificate1|apply IHcertificate2];
      exact HPQ.
  - apply Primitives.atomic_mono. apply IHcertificate. exact HPQ.
Qed.

End Interpreter.
End Semantics.
End Make.
End TypedRegion.
