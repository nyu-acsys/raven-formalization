From Coq Require Import List Lia Program.Equality.
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
  (** The de Bruijn level of a local. *)
  Definition local_level {keep Γ t} (variable : lvar keep Γ t) : nat :=
    length Γ - S (lvar_index variable).
  (** The atom naming an argument: a local by its level, or a literal. *)
  Definition argument_atom {keep Γ t} (argument : pexpr keep Γ t) :
      option AnalysisView.key_atom :=
    match argument with
    | PEVar variable => Some (AnalysisView.AtomLevel (local_level variable))
    | PEVal value =>
        match value with
        | VBool value => Some (AnalysisView.AtomBool value)
        | VInt value => Some (AnalysisView.AtomInt value)
        | VUnit => Some AnalysisView.AtomUnit
        | _ => None
        end
    | _ => None
    end.
  Fixpoint argument_key {keep Γ ts} (arguments : pexpr_list keep Γ ts) :
      AnalysisView.access_key :=
    match arguments with
    | PENil => Some []
    | PECons argument rest =>
        match argument_atom argument, argument_key rest with
        | Some atom, Some atoms => Some (atom :: atoms)
        | _, _ => None
        end
    end.
  (** Levels, hence atoms and keys, are stable under further declarations. *)
  Lemma argument_atom_shift {keep d Γ t} (argument : pexpr keep Γ t) :
    argument_atom (pexpr_shift (d := d) argument) = argument_atom argument.
  Proof.
    destruct argument; reflexivity.
  Qed.
  Lemma argument_key_shift {keep d Γ ts} (arguments : pexpr_list keep Γ ts) :
    argument_key (pexpr_list_shift (d := d) arguments) = argument_key arguments.
  Proof.
    induction arguments as [|t ts argument rest IH]; cbn; [reflexivity|].
    rewrite argument_atom_shift, IH. reflexivity.
  Qed.
  (** An atom determines its argument. *)
  Lemma argument_atom_injective {keep Γ t} (left right : pexpr keep Γ t) atom :
    argument_atom left = Some atom -> argument_atom right = Some atom ->
    left = right.
  Proof.
    intros Hleft Hright.
    destruct left as [? variable | ? value | | ];
      destruct right as [? variable' | ? value' | | ];
      cbn in Hleft, Hright; try discriminate.
    - rewrite <- Hright in Hleft. injection Hleft as Hlevel.
      unfold local_level in Hlevel.
      pose proof (lvar_index_lt variable).
      pose proof (lvar_index_lt variable').
      f_equal. apply lvar_index_injective. lia.
    - destruct value'; try discriminate; rewrite <- Hright in Hleft;
        discriminate.
    - destruct value; try discriminate; rewrite <- Hright in Hleft;
        discriminate.
    - destruct value; try discriminate; dependent destruction value';
        try discriminate; rewrite <- Hright in Hleft;
        try (injection Hleft as ->); reflexivity.
  Qed.
  Lemma argument_key_injective {keep Γ ts} (left right : pexpr_list keep Γ ts)
      key :
    argument_key left = Some key -> argument_key right = Some key ->
    left = right.
  Proof.
    revert key. induction left as [|t ts argument rest IH]; intros key.
    - dependent destruction right. reflexivity.
    - dependent destruction right. cbn.
      destruct (argument_atom argument) as [atom|] eqn:Hatom; [|discriminate].
      destruct (argument_key rest) as [atoms|] eqn:Hrest; [|discriminate].
      destruct (argument_atom p) as [atom'|] eqn:Hatom'; [|discriminate].
      destruct (argument_key right) as [atoms'|] eqn:Hrest'; [|discriminate].
      intros Hleft Hright. rewrite <- Hright in Hleft.
      injection Hleft as -> ->.
      rewrite (argument_atom_injective argument p atom' Hatom Hatom').
      rewrite (IH right atoms' eq_refl Hrest'). reflexivity.
  Qed.
  (** The atoms of a call's arguments. *)
  Fixpoint argument_atoms {keep Γ ts} (arguments : pexpr_list keep Γ ts) :
      list (option AnalysisView.key_atom) :=
    match arguments with
    | PENil => []
    | PECons argument rest => argument_atom argument :: argument_atoms rest
    end.
  (** The atom of the local a call's result is stored in. *)
  Definition target_atom {Γ t} (target : call_target Γ t) :
      option AnalysisView.key_atom :=
    match target with
    | CTDiscard => None
    | CTStore _ target => Some (AnalysisView.AtomLevel (local_level target))
    end.
  (** The atoms of a procedure's formal slots. *)
  Fixpoint variable_atoms {Γ ts} (variables : pvar_list Γ ts) :
      list (option AnalysisView.key_atom) :=
    match variables with
    | PVNil => []
    | PVCons variable rest =>
        Some (AnalysisView.AtomLevel (local_level variable)) ::
          variable_atoms rest
    end.
  (** [assert (arguments_distinct arguments excluded); unfold I(arguments)]
      opens an instance known to differ from the [excluded] ones. *)
  Definition guarded_unfold {Γ} (first second : statement Γ) :
      option (inv_id * AnalysisView.access_key *
        list AnalysisView.access_key) :=
    match first with
    | TAssert condition =>
        match second with
        | TUnfold invariant arguments =>
            match arguments_distinct_parse arguments condition with
            | Some excluded =>
                Some (invariant, argument_key arguments,
                  map argument_key excluded)
            | None => None
            end
        | _ => None
        end
    | _ => None
    end.
  #[global] Arguments guarded_unfold : simpl nomatch.
  Definition guarded_unfold_some {Γ} (first second : statement Γ) guard :
    guarded_unfold first second = Some guard ->
    { condition : gexpr Γ TBool & { invariant : inv_id &
      { arguments : gexpr_list Γ (Assertion.invariant_args invariant) &
        first = TAssert condition /\ second = TUnfold invariant arguments } } }.
  Proof.
    unfold guarded_unfold.
    destruct first; try discriminate; destruct second; try discriminate.
    intros _. exists condition, invariant, arguments. split; reflexivity.
  Defined.
  Definition region_view {Γ} (statement : statement Γ) :=
    match statement with
    | TUnfold invariant arguments =>
        AnalysisView.ViewUnfold invariant (argument_key arguments) []
    | TFold invariant arguments =>
        AnalysisView.ViewFold invariant (argument_key arguments)
    | TSeq first second =>
        match guarded_unfold first second with
        | Some (invariant, key, excluded) =>
            AnalysisView.ViewUnfold invariant key excluded
        | None => AnalysisView.ViewSequence first second
        end
    | TIf _ then_branch else_branch | TGhostIf _ then_branch else_branch =>
        AnalysisView.ViewConditional then_branch else_branch
    | TInvAccess invariant _ body =>
        AnalysisView.ViewStructuredAccess invariant body
    | TAtomic body => AnalysisView.ViewAtomic body
    | TGhostVal _ t initializer body =>
        AnalysisView.ViewScope (ghost_val t) (argument_atom initializer) body
    | TDone => AnalysisView.ViewDone
    | _ => AnalysisView.ViewLeaf
    end.
  (** A sequence whose second statement is not an unfold is viewed as a
      sequence. *)
  Definition guarded_view_unfold_inv {Γ} (first second : statement Γ)
      invariant key excluded :
    match guarded_unfold first second with
    | Some (invariant, key, excluded) =>
        AnalysisView.ViewUnfold invariant key excluded
    | None => AnalysisView.ViewSequence first second
    end = AnalysisView.ViewUnfold invariant key excluded ->
    { condition : gexpr Γ TBool & { invariant' : inv_id &
      { arguments : gexpr_list Γ (Assertion.invariant_args invariant') &
        first = TAssert condition /\ second = TUnfold invariant' arguments } } }.
  Proof.
    destruct (guarded_unfold first second) as [guard|] eqn:Hguarded;
      intros Hview; [exact (guarded_unfold_some first second guard Hguarded)
      | discriminate].
  Defined.
  Lemma guarded_view_sequence_inv {Γ} (first second first' second' :
      statement Γ) :
    match guarded_unfold first second with
    | Some (invariant, key, excluded) =>
        AnalysisView.ViewUnfold invariant key excluded
    | None => AnalysisView.ViewSequence first second
    end = AnalysisView.ViewSequence first' second' ->
    first = first' /\ second = second'.
  Proof.
    destruct (guarded_unfold first second) as [[[? ?] ?]|];
      intros Hview; [discriminate|]. injection Hview. auto.
  Qed.
  Lemma region_view_unguarded {Γ} (first second : statement Γ) :
    guarded_unfold first second = None ->
    region_view (TSeq first second) =
      AnalysisView.ViewSequence first second.
  Proof. intros Hnone. unfold region_view. rewrite Hnone. reflexivity. Qed.
  Lemma region_view_sequence {Γ} (first second : statement Γ) :
    match second with TUnfold _ _ => False | _ => True end ->
    region_view (TSeq first second) =
      AnalysisView.ViewSequence first second.
  Proof.
    intros Hsecond. unfold region_view, guarded_unfold.
    destruct first; try reflexivity. destruct second; try reflexivity.
    contradiction.
  Qed.
  (** A sequence whose first statement is not an assertion is viewed as a
      sequence. *)
  Lemma region_view_sequence_first {Γ} (first second : statement Γ) :
    match first with TAssert _ => False | _ => True end ->
    region_view (TSeq first second) =
      AnalysisView.ViewSequence first second.
  Proof.
    intros Hfirst. unfold region_view, guarded_unfold.
    destruct first; try reflexivity. contradiction.
  Qed.
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
    destruct (guarded_unfold statement1 statement2) as [[[? ?] ?]|];
      [discriminate|].
    inversion Hview; subst. lia. Qed.
  Lemma conditional_children_smaller (Γ : decl_context)
      (statement then_branch else_branch : statement Γ) :
    region_view statement = AnalysisView.ViewConditional then_branch else_branch ->
    size then_branch < size statement /\ size else_branch < size statement.
  Proof. destruct statement; cbn; intros Hview; try discriminate;
    try (destruct (guarded_unfold _ _) as [[[? ?] ?]|]; discriminate);
    inversion Hview; subst; lia. Qed.
  Lemma atomic_body_smaller (Γ : decl_context) (statement body : statement Γ) :
    region_view statement = AnalysisView.ViewAtomic body ->
    size body < size statement.
  Proof. destruct statement; cbn; intros Hview; try discriminate;
    try (destruct (guarded_unfold _ _) as [[[? ?] ?]|]; discriminate);
    inversion Hview; subst. lia. Qed.
  Lemma scope_body_smaller (Γ : decl_context) (statement : statement Γ) d
      alias (body : IR.stmt (d :: Γ)) :
    region_view statement = AnalysisView.ViewScope d alias body ->
    size body < size statement.
  Proof.
    destruct statement; cbn; intros Hview; try discriminate;
    try (destruct (guarded_unfold _ _) as [[[? ?] ?]|]; discriminate);
    injection Hview as <- _ Hbody.
    apply Eqdep.EqdepTheory.inj_pair2 in Hbody. subst body. lia.
  Qed.
  (** The level of the local a leaf writes, if any. *)
  Definition leaf_write {Γ} (statement : statement Γ) : option nat :=
    match statement with
    | TAssign _ target _ | TFieldRead _ _ target _ | TAlloc _ target _ =>
        Some (local_level target)
    | TCall _ _ (CTStore _ target) => Some (local_level target)
    | _ => None
    end.
  Definition syntax : AnalysisView.AnalysisSyntax :=
    AnalysisView.AnalysisSyntaxData statement (@region_view) (@size) size_positive
      sequence_children_smaller conditional_children_smaller
      atomic_body_smaller scope_body_smaller (@leaf_write).
End WithSignature.
(** The control view, as the analyzer sees it. *)
Notation view := (@AnalysisView.syntax_view syntax _).
(** The cost of a leaf, as the analyzer sees it. *)
Notation cost := (@AnalysisView.leaf_cost syntax _).
(** The local a leaf writes, as the analyzer sees it. *)
Notation write := (@AnalysisView.syntax_leaf_write syntax _).
End RegionSyntax.
#[global] Existing Instance RegionSyntax.syntax.

(** Certificate for normalization output.  There is deliberately no raw
    unfold constructor.  A raw fold is admitted only when it allocates a
    fresh invariant; a fold that closes an open invariant must instead be
    represented by [StructuredInvAccess].  This is static evidence, not an
    operational or Iris interpretation. *)
(** Splits the view of a sequence on whether it is a guarded unfold. *)
Ltac guarded_view_cases :=
  repeat match goal with
  | H : context [AnalysisView.syntax_view] |- _ => progress cbn in H
  | H : context [RegionSyntax.guarded_unfold ?first ?second],
    Hnone : RegionSyntax.guarded_unfold ?first ?second = None |- _ =>
      exfalso; clear - H Hnone; rewrite Hnone in H; discriminate
  | H : context [RegionSyntax.guarded_unfold ?first ?second] |- _ =>
      exfalso; clear - H;
      destruct (RegionSyntax.guarded_unfold first second) as [[[? ?] ?]|];
      discriminate
  | H : context [RegionSyntax.guarded_unfold ?first ?second] |- _ =>
      let Hfirst := fresh "Hfirst" in let Hsecond := fresh "Hsecond" in
      destruct (RegionSyntax.guarded_view_sequence_inv first second _ _ H)
        as [Hfirst Hsecond];
      progress subst
  | H : context [RegionSyntax.guarded_unfold ?first ?second] |- _ =>
      let Hfirst := fresh "Hfirst" in let Hsecond := fresh "Hsecond" in
      destruct (RegionSyntax.guarded_view_unfold_inv first second _ _ _ H)
        as (? & ? & ? & Hfirst & Hsecond);
      first [discriminate Hfirst | discriminate Hsecond | progress subst]
  | H : context [RegionSyntax.guarded_unfold ?first ?second] |- _ =>
      let Hguarded := fresh "Hguarded" in
      destruct (RegionSyntax.guarded_unfold first second) as [[[? ?] ?]|]
        eqn:Hguarded;
      [first
         [congruence
         |apply RegionSyntax.guarded_unfold_some in Hguarded
            as (? & ? & ? & Hguarded_first & Hguarded_second);
          first [discriminate Hguarded_first | discriminate Hguarded_second
                | subst]]
      |clear Hguarded]
  end.

Module StructuredCertificates.

Section WithSignature.
Context {RAs : RAValueConfig} {Logic : Assertion.LogicSignature}
  {Cost : AnalysisView.LeafCost}.
Inductive structured_certificate :
    forall Γ, AnalysisView.analysis_state -> stmt Γ ->
      AnalysisView.analysis_state -> Type :=
| StructuredLeaf Γ entry statement exit :
    RegionSyntax.view statement = AnalysisView.ViewLeaf ->
    AnalysisView.take_leaf (AnalysisView.leaf_cost Γ statement)
      (RegionSyntax.write statement) entry = inr exit ->
    structured_certificate Γ entry statement exit
| StructuredDone Γ entry statement :
    RegionSyntax.view statement = AnalysisView.ViewDone ->
    structured_certificate Γ entry statement entry
| StructuredFreshFold Γ entry invariant arguments :
    invariant ∉ AnalysisView.analysis_open entry ->
    structured_certificate Γ entry (TFold invariant arguments)
      (AnalysisView.fold_invariant invariant
        (RegionSyntax.argument_key arguments) entry)
| StructuredSequence Γ entry first middle second exit :
    structured_certificate Γ entry first middle ->
    structured_certificate Γ middle second exit ->
    structured_certificate Γ entry (TSeq first second) exit
| StructuredConditional Γ entry condition then_branch else_branch
    then_exit else_exit :
    structured_certificate Γ entry then_branch then_exit ->
    structured_certificate Γ entry else_branch else_exit ->
    AnalysisView.analysis_records then_exit =
      AnalysisView.analysis_records else_exit ->
    AnalysisView.analysis_in_atomic then_exit =
      AnalysisView.analysis_in_atomic else_exit ->
    structured_certificate Γ entry
      (TIf condition then_branch else_branch)
      (AnalysisView.join_state then_exit else_exit)
| StructuredAtomic Γ entry body outer inner :
    AnalysisView.take_step AnalysisView.AtomicStep entry =
      inr outer ->
    structured_certificate Γ
      (AnalysisView.atomic_entry outer)
      body inner ->
    AnalysisView.analysis_records inner =
      AnalysisView.analysis_records outer ->
    structured_certificate Γ entry (TAtomic body)
      (AnalysisView.atomic_exit outer inner)
| StructuredInvAccess Γ entry invariant arguments
    (excluded : list (gexpr_list Γ (Assertion.invariant_args invariant)))
    body opened inner :
    AnalysisView.open_access invariant
      (RegionSyntax.argument_key arguments)
      (map RegionSyntax.argument_key excluded) entry = inr opened ->
    structured_certificate Γ opened body inner ->
    AnalysisView.analysis_records inner =
      AnalysisView.analysis_records opened ->
    structured_certificate Γ entry (TInvAccess invariant arguments body)
      (AnalysisView.fold_invariant invariant
        (RegionSyntax.argument_key arguments) inner)
| StructuredGhostVal Γ entry name t initializer body inner :
    structured_certificate (ghost_val t :: Γ)
      (AnalysisView.enter_scope (length Γ)
        (RegionSyntax.argument_atom initializer) entry) body inner ->
    AnalysisView.leave_scope_admissible (length Γ) inner = true ->
    structured_certificate Γ entry (TGhostVal name t initializer body)
      (AnalysisView.leave_scope (length Γ) entry inner)
| StructuredGhostConditional Γ entry condition then_branch else_branch
    then_exit else_exit :
    structured_certificate Γ entry then_branch then_exit ->
    structured_certificate Γ entry else_branch else_exit ->
    AnalysisView.analysis_records then_exit =
      AnalysisView.analysis_records else_exit ->
    AnalysisView.analysis_in_atomic then_exit =
      AnalysisView.analysis_in_atomic else_exit ->
    structured_certificate Γ entry
      (TGhostIf condition then_branch else_branch)
      (AnalysisView.join_state then_exit else_exit).

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
  | StructuredInvAccess _ _ _ _ _ _ _ _ _ body_certificate _ =>
      structured_certificate_footprint body_certificate
  | StructuredGhostVal _ _ _ _ _ _ _ body_certificate _ =>
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
