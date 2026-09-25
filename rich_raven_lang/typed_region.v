From iris.proofmode Require Import tactics.

From raven_iris.rich_raven_lang Require Import
  typed_core typed_analysis_view typed_assertion typed_ir typed_translation.

(** Continuation semantics for certificates emitted by the flat atomicity
    analyzer.  An unfold wraps the complete remaining continuation, so its
    linear Iris close capability can flow to a later fold without appearing
    in Raven assertions or escaping the certified region. *)
Module TypedRegion.

Import TypedCore TypedIR.

Module Generic (Syntax : TypedAnalysisView.ANALYSIS_SYNTAX).
Module Atomicity := TypedAnalysisView.Analysis Syntax.
Import Atomicity.

(** Expose certificate proof irrelevance through the generic-region module.
    Rocq does not project declarations of the local [Atomicity] module alias
    through an applied functor path, while clients do share its certificate
    type through that path. *)
Lemma analysis_certificate_unique
    {Γ cost entry statement exit}
    (certificate1 certificate2 :
      Atomicity.analysis_certificate cost Γ entry statement exit) :
  certificate1 = certificate2.
Proof.
  apply Atomicity.analysis_certificate_unique.
Qed.

Module Type REGION_MODEL.
  Parameter PROP : bi.
  Parameter stack_context : context -> Type.
  Parameter ambient_mask : Type.
End REGION_MODEL.

(** Term-level counterpart of [REGION_MODEL].  A value of this record can be
    assembled after an adequacy proof has allocated the runtime ghost names,
    unlike a module-functor argument. *)
Record region_model_data (PROP : bi) : Type := RegionModelData {
  term_region_stack_context : context -> Type;
  term_region_ambient_mask : Type;
}.

Arguments term_region_stack_context {_} _ _.
Arguments term_region_ambient_mask {_} _.

(** Term-level generic-region semantics.  This exactly mirrors the module
    interface [Semantics] below, but all semantic dependencies are explicit
    values. *)
Module TermSemantics.
Section WithModel.
Context {PROP : bi} (Model : region_model_data PROP).
Local Notation iProp := (bi_car PROP).

Record region_primitives_data := RegionPrimitivesData {
  term_region_operation_wp : forall Γ, term_region_stack_context Model Γ ->
    term_region_ambient_mask Model -> analysis_state -> Syntax.statement Γ ->
    analysis_state -> iProp -> iProp;
  term_region_branch_wp : forall Γ, term_region_stack_context Model Γ ->
    term_region_ambient_mask Model -> analysis_state -> Syntax.statement Γ ->
    analysis_state -> analysis_state -> iProp -> iProp -> iProp;
  term_region_operation_mono : forall Γ runtime ambient entry statement exit P Q,
    (P ⊢ Q) ->
    term_region_operation_wp Γ runtime ambient entry statement exit P ⊢
      term_region_operation_wp Γ runtime ambient entry statement exit Q;
  term_region_operation_frame : forall Γ runtime ambient entry statement exit P R,
    term_region_operation_wp Γ runtime ambient entry statement exit P ∗ R ⊢
      term_region_operation_wp Γ runtime ambient entry statement exit (P ∗ R);
  term_region_branch_mono : forall Γ runtime ambient entry statement then_exit
      else_exit P P' Q Q',
    (P ⊢ P') -> (Q ⊢ Q') ->
    term_region_branch_wp Γ runtime ambient entry statement then_exit else_exit P Q ⊢
      term_region_branch_wp Γ runtime ambient entry statement then_exit else_exit P' Q';
  term_region_branch_frame : forall Γ runtime ambient entry statement then_exit
      else_exit P Q R,
    term_region_branch_wp Γ runtime ambient entry statement then_exit else_exit P Q ∗ R ⊢
      term_region_branch_wp Γ runtime ambient entry statement then_exit else_exit (P ∗ R) (Q ∗ R)
}.

Context (Primitives : region_primitives_data).

Fixpoint region_wp {Γ entry statement exit} {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit) :
    term_region_stack_context Model Γ -> term_region_ambient_mask Model ->
      iProp -> iProp :=
  match certificate in analysis_certificate _ Γ' entry' statement' exit'
      return term_region_stack_context Model Γ' ->
        term_region_ambient_mask Model -> iProp -> iProp with
  | @CertLeaf _ Γ' entry' statement' exit' _ _ =>
      fun runtime ambient post =>
        term_region_operation_wp Primitives Γ' runtime ambient entry' statement' exit' post
  (* The empty continuation performs no operation: its meaning is the
     postcondition itself, not an operation that happens to do nothing. *)
  | @CertDone _ _ _ _ _ =>
      fun _ _ post => post
  | @CertUnfold _ Γ' entry' statement' _ exit' _ _ =>
      fun runtime ambient post =>
        term_region_operation_wp Primitives Γ' runtime ambient entry' statement' exit' post
  | @CertFold _ Γ' entry' statement' invariant _ =>
      fun runtime ambient post =>
        term_region_operation_wp Primitives Γ' runtime ambient entry' statement'
          (fold_invariant invariant entry') post
  | @CertSequence _ _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      fun runtime ambient post => region_wp first_certificate runtime ambient
        (region_wp second_certificate runtime ambient post)
  | @CertConditional _ Γ' entry' statement' _ _ then_exit else_exit _
      then_certificate else_certificate _ _ =>
      fun runtime ambient post =>
        term_region_branch_wp Primitives Γ' runtime ambient entry' statement' then_exit
          else_exit (region_wp then_certificate runtime ambient post)
          (region_wp else_certificate runtime ambient post)
  | @CertAtomic _ Γ' entry' statement' _ outer inner _ _ body_certificate _ =>
      fun runtime ambient post =>
        term_region_operation_wp Primitives Γ' runtime ambient entry' statement'
          (AnalysisState (analysis_mask inner) (analysis_open inner)
            (analysis_step_taken outer || analysis_step_taken inner)
            (analysis_in_atomic outer))
          (region_wp body_certificate runtime ambient post)
  end.

Lemma region_wp_mono {Γ entry statement exit}
    (runtime : term_region_stack_context Model Γ)
    (ambient : term_region_ambient_mask Model) {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit) P Q :
  (P ⊢ Q) ->
  region_wp certificate runtime ambient P ⊢ region_wp certificate runtime ambient Q.
Proof.
  revert P Q. induction certificate; intros P Q HPQ; simpl.
  - apply (term_region_operation_mono Primitives). exact HPQ.
  - exact HPQ.
  - apply (term_region_operation_mono Primitives). exact HPQ.
  - apply (term_region_operation_mono Primitives). exact HPQ.
  - apply IHcertificate1. apply IHcertificate2. exact HPQ.
  - apply (term_region_branch_mono Primitives); [apply IHcertificate1|apply IHcertificate2];
      exact HPQ.
  - apply (term_region_operation_mono Primitives). apply IHcertificate. exact HPQ.
Qed.

Lemma region_wp_frame {Γ entry statement exit}
    (runtime : term_region_stack_context Model Γ)
    (ambient : term_region_ambient_mask Model) {cost : cost_model}
    (certificate : analysis_certificate cost Γ entry statement exit) P R :
  region_wp certificate runtime ambient P ∗ R ⊢
    region_wp certificate runtime ambient (P ∗ R).
Proof.
  revert P R. induction certificate; intros P R; simpl.
  - apply (term_region_operation_frame Primitives).
  - reflexivity.
  - apply (term_region_operation_frame Primitives).
  - apply (term_region_operation_frame Primitives).
  - iIntros "[H HR]".
    iPoseProof (IHcertificate1 runtime
      (region_wp certificate2 runtime ambient P) R with "[$H $HR]") as "H".
    iApply (region_wp_mono with "H"). apply (IHcertificate2 runtime).
  - etrans; first apply (term_region_branch_frame Primitives).
    apply (term_region_branch_mono Primitives);
      [apply (IHcertificate1 runtime)|apply (IHcertificate2 runtime)].
  - etrans; first apply (term_region_operation_frame Primitives).
    apply (term_region_operation_mono Primitives). apply (IHcertificate runtime).
Qed.

Record interpreter_data := RegionInterpreterData {
  term_region_wp : forall {Γ entry statement exit} {cost : cost_model},
    analysis_certificate cost Γ entry statement exit ->
    term_region_stack_context Model Γ -> term_region_ambient_mask Model ->
      iProp -> iProp;
  term_region_wp_mono : forall {Γ entry statement exit}
      (runtime : term_region_stack_context Model Γ)
      (ambient : term_region_ambient_mask Model) {cost : cost_model}
      (certificate : analysis_certificate cost Γ entry statement exit) P Q,
    (P ⊢ Q) -> term_region_wp certificate runtime ambient P ⊢
      term_region_wp certificate runtime ambient Q;
  term_region_wp_frame : forall {Γ entry statement exit}
      (runtime : term_region_stack_context Model Γ)
      (ambient : term_region_ambient_mask Model) {cost : cost_model}
      (certificate : analysis_certificate cost Γ entry statement exit) P R,
    term_region_wp certificate runtime ambient P ∗ R ⊢
      term_region_wp certificate runtime ambient (P ∗ R)
}.

Definition interpreter : interpreter_data := {|
  term_region_wp := @region_wp;
  term_region_wp_mono := @region_wp_mono;
  term_region_wp_frame := @region_wp_frame;
|}.
End WithModel.
End TermSemantics.

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
End Semantics.
End Generic.

End TypedRegion.
