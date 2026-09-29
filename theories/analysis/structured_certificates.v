From Coq Require Import List Lia.
From stdpp Require Import gmap sets.

From raven Require Import verification.expressions analysis.atomicity verification.assertions verification.ir.

Import ListNotations.
Open Scope list_scope.

Import Core IR.

(** The typed IR as the analyzer sees it: its control view and size. *)
Module RegionSyntax.
Section WithSignature.
Context {RAs : RAValueConfig} {Logic : Assertion.LogicSignature}.
  Definition statement := IR.stmt.
  Definition region_view {Γ} (statement : statement Γ) :=
    match statement with
    | TUnfold invariant _ => AnalysisView.ViewUnfold invariant
    | TFold invariant _ => AnalysisView.ViewFold invariant
    | TSeq first second => AnalysisView.ViewSequence first second
    | TIf _ then_branch else_branch | TGhostIf _ then_branch else_branch =>
        AnalysisView.ViewConditional then_branch else_branch
    | TInvAccess invariant _ body =>
        AnalysisView.ViewStructuredAccess invariant body
    | TAtomic body => AnalysisView.ViewAtomic body
    | TGhostVal _ t _ body => AnalysisView.ViewScope (ghost_val t) body
    | TDone => AnalysisView.ViewDone
    | _ => AnalysisView.ViewLeaf
    end.
  Fixpoint size {Γ} (statement : statement Γ) : nat :=
    match statement with
    | TSeq first second | TIf _ first second | TGhostIf _ first second =>
        S (size first + size second)
    | TAtomic body => S (size body)
    | TGhostVal _ _ _ body => S (size body)
    | _ => 1
    end.
  Lemma size_positive Γ (statement : statement Γ) : 0 < size statement.
  Proof. induction statement; simpl; lia. Qed.
  Lemma sequence_children_smaller (Γ : decl_context)
      (statement first second : statement Γ) :
    region_view statement = AnalysisView.ViewSequence first second ->
    size first < size statement /\ size second < size statement.
  Proof. destruct statement; cbn; intros Hview; try discriminate.
    inversion Hview; subst. lia. Qed.
  Lemma conditional_children_smaller (Γ : decl_context)
      (statement then_branch else_branch : statement Γ) :
    region_view statement = AnalysisView.ViewConditional then_branch else_branch ->
    size then_branch < size statement /\ size else_branch < size statement.
  Proof. destruct statement; cbn; intros Hview; try discriminate;
    inversion Hview; subst; lia. Qed.
  Lemma atomic_body_smaller (Γ : decl_context) (statement body : statement Γ) :
    region_view statement = AnalysisView.ViewAtomic body ->
    size body < size statement.
  Proof. destruct statement; cbn; intros Hview; try discriminate.
    inversion Hview; subst. lia. Qed.
  Lemma scope_body_smaller (Γ : decl_context) (statement : statement Γ) d
      (body : IR.stmt (d :: Γ)) :
    region_view statement = AnalysisView.ViewScope d body ->
    size body < size statement.
  Proof.
    destruct statement; cbn; intros Hview; try discriminate.
    injection Hview as <- Hbody.
    apply Eqdep.EqdepTheory.inj_pair2 in Hbody. subst body. lia.
  Qed.
  Definition syntax : AnalysisView.AnalysisSyntax :=
    AnalysisView.AnalysisSyntaxData statement (@region_view) (@size) size_positive
      sequence_children_smaller conditional_children_smaller
      atomic_body_smaller scope_body_smaller.
End WithSignature.
(** The control view, as the analyzer sees it. *)
Notation view := (@AnalysisView.syntax_view syntax _).
(** The cost of a leaf, as the analyzer sees it. *)
Notation cost := (@AnalysisView.leaf_cost syntax _).
End RegionSyntax.
#[global] Existing Instance RegionSyntax.syntax.

(** Certificate for normalization output.  There is deliberately no raw
    unfold constructor.  A raw fold is admitted only when it allocates a
    fresh invariant; a fold that closes an open invariant must instead be
    represented by [StructuredInvAccess].  This is static evidence, not an
    operational or Iris interpretation. *)
Module StructuredCertificates.

Section WithSignature.
Context {RAs : RAValueConfig} {Logic : Assertion.LogicSignature}
  {Cost : AnalysisView.LeafCost}.
Inductive structured_certificate :
    forall Γ, AnalysisView.analysis_state -> stmt Γ ->
      AnalysisView.analysis_state -> Type :=
| StructuredLeaf Γ entry statement exit :
    RegionSyntax.view statement = AnalysisView.ViewLeaf ->
    AnalysisView.take_step (AnalysisView.leaf_cost Γ statement) entry = inr exit ->
    structured_certificate Γ entry statement exit
| StructuredDone Γ entry statement :
    RegionSyntax.view statement = AnalysisView.ViewDone ->
    structured_certificate Γ entry statement entry
| StructuredFreshFold Γ entry invariant arguments :
    invariant ∉ AnalysisView.analysis_open entry ->
    structured_certificate Γ entry (TFold invariant arguments)
      (AnalysisView.fold_invariant invariant entry)
| StructuredSequence Γ entry first middle second exit :
    structured_certificate Γ entry first middle ->
    structured_certificate Γ middle second exit ->
    structured_certificate Γ entry (TSeq first second) exit
| StructuredConditional Γ entry condition then_branch else_branch
    then_exit else_exit :
    structured_certificate Γ entry then_branch then_exit ->
    structured_certificate Γ entry else_branch else_exit ->
    AnalysisView.analysis_open then_exit =
      AnalysisView.analysis_open else_exit ->
    AnalysisView.analysis_in_atomic then_exit =
      AnalysisView.analysis_in_atomic else_exit ->
    structured_certificate Γ entry
      (TIf condition then_branch else_branch)
      (AnalysisView.AnalysisState
        (AnalysisView.analysis_mask then_exit ∩
          AnalysisView.analysis_mask else_exit)
        (AnalysisView.analysis_open then_exit)
        (AnalysisView.analysis_step_taken then_exit ||
          AnalysisView.analysis_step_taken else_exit)
        (AnalysisView.analysis_in_atomic then_exit))
| StructuredAtomic Γ entry body outer inner :
    AnalysisView.take_step AnalysisView.AtomicStep entry =
      inr outer ->
    structured_certificate Γ
      (AnalysisView.AnalysisState
        (AnalysisView.analysis_mask outer)
        (AnalysisView.analysis_open outer)
        (AnalysisView.analysis_step_taken outer) true)
      body inner ->
    AnalysisView.analysis_open inner =
      AnalysisView.analysis_open outer ->
    structured_certificate Γ entry (TAtomic body)
      (AnalysisView.AnalysisState
        (AnalysisView.analysis_mask inner)
        (AnalysisView.analysis_open inner)
        (AnalysisView.analysis_step_taken outer ||
          AnalysisView.analysis_step_taken inner)
        (AnalysisView.analysis_in_atomic outer))
| StructuredInvAccess Γ entry invariant arguments body opened inner :
    AnalysisView.open_invariant invariant entry = inr opened ->
    structured_certificate Γ opened body inner ->
    AnalysisView.analysis_open inner =
      AnalysisView.analysis_open opened ->
    structured_certificate Γ entry (TInvAccess invariant arguments body)
      (AnalysisView.fold_invariant invariant inner)
| StructuredGhostVal Γ entry name t initializer body exit :
    structured_certificate (ghost_val t :: Γ) entry body exit ->
    structured_certificate Γ entry (TGhostVal name t initializer body) exit
| StructuredGhostConditional Γ entry condition then_branch else_branch
    then_exit else_exit :
    structured_certificate Γ entry then_branch then_exit ->
    structured_certificate Γ entry else_branch else_exit ->
    AnalysisView.analysis_open then_exit =
      AnalysisView.analysis_open else_exit ->
    AnalysisView.analysis_in_atomic then_exit =
      AnalysisView.analysis_in_atomic else_exit ->
    structured_certificate Γ entry
      (TGhostIf condition then_branch else_branch)
      (AnalysisView.AnalysisState
        (AnalysisView.analysis_mask then_exit ∩
          AnalysisView.analysis_mask else_exit)
        (AnalysisView.analysis_open then_exit)
        (AnalysisView.analysis_step_taken then_exit ||
          AnalysisView.analysis_step_taken else_exit)
        (AnalysisView.analysis_in_atomic then_exit)).

(** Logical Raven masks that may be needed while interpreting a structured
    certificate.  The footprint keeps both the masks and open sets at the
    certificate boundary, and exposes the footprints of every recursively
    certified child. *)
Fixpoint structured_certificate_footprint
    {Γ entry statement exit}
    (certificate : structured_certificate Γ entry statement exit) :
    gset inv_id :=
  AnalysisView.analysis_mask entry ∪
  AnalysisView.analysis_open entry ∪
  AnalysisView.analysis_mask exit ∪
  AnalysisView.analysis_open exit ∪
  match certificate with
  | StructuredSequence _ _ _ _ _ _ first_certificate second_certificate =>
      structured_certificate_footprint first_certificate ∪
      structured_certificate_footprint second_certificate
  | StructuredConditional _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      structured_certificate_footprint then_certificate ∪
      structured_certificate_footprint else_certificate
  | StructuredAtomic _ _ _ _ _ _ body_certificate _ =>
      structured_certificate_footprint body_certificate
  | StructuredInvAccess _ _ _ _ _ _ _ _ body_certificate _ =>
      structured_certificate_footprint body_certificate
  | StructuredGhostVal _ _ _ _ _ _ _ body_certificate =>
      structured_certificate_footprint body_certificate
  | StructuredGhostConditional _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      structured_certificate_footprint then_certificate ∪
      structured_certificate_footprint else_certificate
  | _ => ∅
  end.

Lemma structured_certificate_entry_subset_footprint
    {Γ entry statement exit}
    (certificate : structured_certificate Γ entry statement exit) :
  AnalysisView.analysis_mask entry ⊆
    structured_certificate_footprint certificate.
Proof.
  destruct certificate; simpl; intros candidate Hin.
  all: repeat rewrite elem_of_union; tauto.
Qed.

Lemma structured_certificate_exit_subset_footprint
    {Γ entry statement exit}
    (certificate : structured_certificate Γ entry statement exit) :
  AnalysisView.analysis_mask exit ⊆
    structured_certificate_footprint certificate.
Proof.
  destruct certificate; simpl; intros candidate Hin.
  all: repeat rewrite elem_of_union; tauto.
Qed.

End WithSignature.
End StructuredCertificates.
