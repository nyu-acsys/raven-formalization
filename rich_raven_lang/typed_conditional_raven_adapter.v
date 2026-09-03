From Coq Require Import List Program.Equality.
From stdpp Require Import sets coPset.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import tactics.

From raven_iris.simp_raven_lang Require Import ra_base.
From raven_iris.rich_raven_lang Require Import
  typed_core typed_analysis_view typed_assertion typed_runtime
  typed_runtime_certified
  typed_conditional_slice typed_conditional_slice_iris.

Import ListNotations.

(** Structural adapter between Raven's actual analysis certificates and the
    conditional normalization slice.  Sequence and conditional certificates
    are deliberately not chunks: the relation below exposes their children,
    so that a matching close is never hidden inside an opaque certificate. *)
Module Make (LegacyRAs : ra_base.RA_CONFIG)
    (Logic : TypedAssertion.LOGIC_SIGNATURE).

Module Runtime := TypedRuntimeCertified.Make LegacyRAs Logic.
Module WithContracts (Contracts : Runtime.Validation.Hoare.CONTRACT_ENV).
Module Certified := Runtime.CertifiedRegions Contracts.
Module Atomicity := Certified.Atomicity.
Module IR := Runtime.IR.

Import TypedCore IR.

Module Payload.
  Definition state := Atomicity.analysis_state.
  Definition marker := Atomicity.access_marker.

  (** Only analyzer leaves and access operations are indivisible chunks.
      Atomic blocks will be added as opaque balanced chunks once their
      continuous-access theorem is stated at the trusted-module boundary. *)
  Inductive raven_chunk : state -> list marker -> state -> list marker -> Type :=
  | ChunkLeaf (Γ : context) (fuel : nat) (cost : Atomicity.cost_model)
      entry (statement : stmt Γ) exit stack
      (view : Runtime.RegionSyntax.view statement =
        TypedAnalysisView.ViewLeaf)
      (step : Atomicity.take_step (cost Γ statement) entry = inr exit) :
      raven_chunk entry stack exit stack
  | ChunkUnfold (Γ : context) (fuel : nat) (cost : Atomicity.cost_model)
      entry (statement : stmt Γ) invariant exit stack
      (view : Runtime.RegionSyntax.view statement =
        TypedAnalysisView.ViewUnfold invariant)
      (step : Atomicity.open_invariant invariant entry = inr exit) :
      raven_chunk entry stack exit
        ((invariant, Atomicity.analysis_open entry) :: stack)
  | ChunkFold (Γ : context) (fuel : nat) (cost : Atomicity.cost_model)
      entry (statement : stmt Γ) invariant outer tail
      (view : Runtime.RegionSyntax.view statement =
        TypedAnalysisView.ViewFold invariant)
      (member : invariant ∈ Atomicity.analysis_open entry)
      (fresh : invariant ∉ outer)
      (opened : Atomicity.analysis_open entry = {[invariant]} ∪ outer) :
      raven_chunk entry ((invariant, outer) :: tail)
        (Atomicity.fold_invariant invariant entry) tail
  | ChunkFreshFold (Γ : context) (fuel : nat)
      (cost : Atomicity.cost_model) entry (statement : stmt Γ) invariant stack
      (view : Runtime.RegionSyntax.view statement =
        TypedAnalysisView.ViewFold invariant)
      (closed : invariant ∉ Atomicity.analysis_open entry) :
      raven_chunk entry stack (Atomicity.fold_invariant invariant entry) stack
  | ChunkAtomic (Γ : context) (fuel : nat)
      (cost : Atomicity.cost_model) entry (statement body : stmt Γ) outer inner
      stack
      (view : Runtime.RegionSyntax.view statement =
        TypedAnalysisView.ViewAtomic body)
      (step : Atomicity.take_step Atomicity.AtomicStep entry = inr outer)
      (body_certificate : Atomicity.analysis_certificate cost Γ fuel
        (Atomicity.AnalysisState (Atomicity.analysis_mask outer)
          (Atomicity.analysis_open outer)
          (Atomicity.analysis_step_taken outer) true) body inner)
      (open_equal : Atomicity.analysis_open inner =
        Atomicity.analysis_open outer) :
      raven_chunk entry stack
        (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
          (Atomicity.analysis_open inner)
          (Atomicity.analysis_step_taken outer ||
            Atomicity.analysis_step_taken inner)
          (Atomicity.analysis_in_atomic outer)) stack.

  Definition chunk := raven_chunk.

  Definition preserves focused tail entry exit
      (_ : chunk entry (focused :: tail) exit (focused :: tail)) : Prop := True.

  Definition opens focused tail entry exit
      (_ : chunk entry tail exit (focused :: tail)) : Prop := True.

  Definition closes focused tail entry exit
      (_ : chunk entry (focused :: tail) exit tail) : Prop := True.

  Inductive raven_conditional : state -> state -> state -> state -> Type :=
  | RavenConditional (Γ : context) (fuel : nat)
      (cost : Atomicity.cost_model) entry
      (statement then_statement else_statement : stmt Γ)
      then_exit else_exit
      (view : Runtime.RegionSyntax.view statement =
        TypedAnalysisView.ViewConditional then_statement else_statement)
      (then_certificate : Atomicity.analysis_certificate cost Γ fuel entry
        then_statement then_exit)
      (else_certificate : Atomicity.analysis_certificate cost Γ fuel entry
        else_statement else_exit)
      (open_equal : Atomicity.analysis_open then_exit =
        Atomicity.analysis_open else_exit)
      (atomic_equal : Atomicity.analysis_in_atomic then_exit =
        Atomicity.analysis_in_atomic else_exit) :
      raven_conditional entry then_exit else_exit
        (Atomicity.AnalysisState
          (Atomicity.analysis_mask then_exit ∩
            Atomicity.analysis_mask else_exit)
          (Atomicity.analysis_open then_exit)
          (Atomicity.analysis_step_taken then_exit ||
            Atomicity.analysis_step_taken else_exit)
          (Atomicity.analysis_in_atomic then_exit)).
  Definition conditional := raven_conditional.
End Payload.

Module Slice := ConditionalSlice Payload.

(** A heterogeneous certificate zipper.  Adjacent entries share analysis
    states, but may have unrelated fuel indices.  The normalizer flattens a
    source-level sequence into this representation before searching for a
    matching close; consequently an unfold and its fold need not belong to
    the same immediate certificate subtree. *)
Inductive certificate_suffix (cost : Atomicity.cost_model) Γ :
    Atomicity.analysis_state -> Atomicity.analysis_state -> Type :=
| SuffixDone state : certificate_suffix cost Γ state state
| SuffixCons fuel entry statement middle exit
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry
      statement middle)
    (rest : certificate_suffix cost Γ middle exit) :
    certificate_suffix cost Γ entry exit.

Arguments SuffixDone {_ _} _.
Arguments SuffixCons {_ _ _ _ _ _ _} _ _.

Fixpoint suffix_lifo {cost Γ entry exit}
    (suffix : certificate_suffix cost Γ entry exit)
    (stack_in stack_out : list Atomicity.access_marker) : Prop :=
  match suffix with
  | SuffixDone _ => stack_out = stack_in
  | SuffixCons certificate rest =>
      exists stack_middle,
        Atomicity.lifo_certificate certificate stack_in stack_middle /\
        suffix_lifo rest stack_middle stack_out
  end.

(** The operational zipper is defined inside the resource-parametric runtime
    validity functor.  Keep the certificate-only erasure in the corresponding
    adapter functor: it is available precisely at the later semantic bridge,
    without making the syntax normalizer depend on runtime resources. *)
Module WithRuntimeValidity
    (Resources : Runtime.RUNTIME_RESOURCES)
    (ProcedureContracts :
      Runtime.Validation.Hoare.PROCEDURE_CONTRACT_COHERENCE Contracts)
    (Leaf : Runtime.DEFAULT_SEMANTIC_LEAF_CONTRACTS Resources Contracts)
    (Defs : Runtime.Translation.DEFINITION_ENV).
  Module Validity := Runtime.CertifiedRegionValidity Resources Contracts
    ProcedureContracts Leaf Defs.

  Fixpoint certificate_suffix_of_operational_suffix {cost Γ entry exit}
      (suffix : Validity.operational_suffix cost Γ entry exit) :
      certificate_suffix cost Γ entry exit :=
    match suffix with
    | Validity.OperationalDone state => SuffixDone state
    | Validity.OperationalCons certificate rest =>
        SuffixCons certificate
          (certificate_suffix_of_operational_suffix rest)
    end.

  Definition certificate_suffix_of_aligned_operational_suffix
      {cost Γ F Δ entry pre stack_in exit post stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ
        entry pre stack_in exit post stack_out) :
      certificate_suffix cost Γ entry exit :=
    certificate_suffix_of_operational_suffix
      (Validity.erase_aligned_operational_suffix suffix).

  Lemma certificate_suffix_of_operational_suffix_lifo
      {cost Γ entry exit}
      (suffix : Validity.operational_suffix cost Γ entry exit)
      (stack_in stack_out : list Atomicity.access_marker) :
    suffix_lifo (certificate_suffix_of_operational_suffix suffix)
      stack_in stack_out <->
    Validity.operational_suffix_lifo suffix stack_in stack_out.
  Proof.
    revert stack_in stack_out.
    induction suffix; intros stack_in stack_out; simpl.
    - reflexivity.
    - split.
      + intros (stack_middle & Hlifo & Hrest).
        exists stack_middle. split; [exact Hlifo|].
        apply IHsuffix. exact Hrest.
      + intros (stack_middle & Hlifo & Hrest).
        exists stack_middle. split; [exact Hlifo|].
        apply IHsuffix. exact Hrest.
  Qed.

  Lemma certificate_suffix_of_aligned_operational_suffix_lifo
      {cost Γ F Δ entry pre stack_in exit post stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ
        entry pre stack_in exit post stack_out)
      (input output : list Atomicity.access_marker) :
    suffix_lifo (certificate_suffix_of_aligned_operational_suffix suffix)
      input output <->
    Validity.operational_suffix_lifo
      (Validity.erase_aligned_operational_suffix suffix) input output.
  Proof.
    apply certificate_suffix_of_operational_suffix_lifo.
  Qed.

  Lemma certificate_suffix_of_aligned_operational_suffix_has_lifo
      {cost Γ F Δ entry pre stack_in exit post stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ
        entry pre stack_in exit post stack_out) :
    suffix_lifo (certificate_suffix_of_aligned_operational_suffix suffix)
      stack_in stack_out.
  Proof.
    apply (proj2 (certificate_suffix_of_aligned_operational_suffix_lifo
      suffix stack_in stack_out)).
    apply Validity.erase_aligned_operational_suffix_lifo.
  Qed.
End WithRuntimeValidity.

Definition transport_suffix_lifo_out
    {cost Γ entry exit} (suffix : certificate_suffix cost Γ entry exit)
    stack_in stack_out1 stack_out2 (Heq : stack_out1 = stack_out2) :
    suffix_lifo suffix stack_in stack_out1 ->
    suffix_lifo suffix stack_in stack_out2.
Proof. destruct Heq. exact (fun proof => proof). Defined.

Fixpoint append_suffix {cost Γ entry middle}
    (first : certificate_suffix cost Γ entry middle)
    {exit} (second : certificate_suffix cost Γ middle exit) :
    certificate_suffix cost Γ entry exit :=
  match first in certificate_suffix _ _ e m return
      certificate_suffix cost Γ m exit -> certificate_suffix cost Γ e exit
  with
  | SuffixDone _ => fun suffix => suffix
  | SuffixCons certificate rest => fun suffix =>
      SuffixCons certificate (append_suffix rest suffix)
  end second.

Inductive suffix_expands (cost : Atomicity.cost_model) Γ :
    forall entry exit, certificate_suffix cost Γ entry exit ->
      certificate_suffix cost Γ entry exit -> Prop :=
| ExpandsRefl entry exit (suffix : certificate_suffix cost Γ entry exit) :
    suffix_expands cost Γ entry exit suffix suffix
| ExpandsSequence fuel entry statement first middle second next exit
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      first middle)
    (second_certificate : Atomicity.analysis_certificate cost Γ fuel middle
      second next)
    (rest : certificate_suffix cost Γ next exit) :
    suffix_expands cost Γ entry exit
      (SuffixCons first_certificate (SuffixCons second_certificate rest))
      (SuffixCons
        (Atomicity.CertSequence cost Γ fuel entry statement first middle second
          next view first_certificate second_certificate) rest)
| ExpandsCons fuel entry statement middle exit
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle)
    (flat source : certificate_suffix cost Γ middle exit) :
    suffix_expands cost Γ middle exit flat source ->
    suffix_expands cost Γ entry exit (SuffixCons certificate flat)
      (SuffixCons certificate source)
| ExpandsTrans entry exit
    (first middle last : certificate_suffix cost Γ entry exit) :
    suffix_expands cost Γ entry exit first middle ->
    suffix_expands cost Γ entry exit middle last ->
    suffix_expands cost Γ entry exit first last.

Arguments ExpandsRefl {_ _ _ _} _.

Lemma suffix_expands_lifo {cost Γ entry exit}
    {flat source : certificate_suffix cost Γ entry exit} :
  suffix_expands cost Γ entry exit flat source ->
  forall stack_in stack_out,
    suffix_lifo flat stack_in stack_out <->
    suffix_lifo source stack_in stack_out.
Proof.
  intros Hexpansion. induction Hexpansion; intros stack_in stack_out.
  - reflexivity.
  - simpl. firstorder.
  - simpl. split.
    + intros (stack_middle & Hhead & Hflat).
      exists stack_middle. split; [exact Hhead|].
      apply IHHexpansion. exact Hflat.
    + intros (stack_middle & Hhead & Hsource).
      exists stack_middle. split; [exact Hhead|].
      apply IHHexpansion. exact Hsource.
  - etrans; eauto.
Qed.

Lemma suffix_lifo_append {cost Γ entry middle exit}
    (first : certificate_suffix cost Γ entry middle)
    (second : certificate_suffix cost Γ middle exit) stack_in stack_out :
  suffix_lifo (append_suffix first second) stack_in stack_out <->
  exists stack_middle,
    suffix_lifo first stack_in stack_middle /\
    suffix_lifo second stack_middle stack_out.
Proof.
  revert stack_in stack_out.
  induction first as [state|fuel entry statement next middle certificate rest IH];
    intros stack_in stack_out; simpl.
  - split.
    + intros H. exists stack_in. split; [reflexivity|exact H].
    + intros (stack_middle & -> & H). exact H.
  - split.
    + intros (stack_head & Hhead & Happ).
      apply IH in Happ as (stack_middle & Hrest & Hsecond).
      exists stack_middle. split; [|exact Hsecond].
      exists stack_head. split; assumption.
    + intros (stack_middle & (stack_head & Hhead & Hrest) & Hsecond).
      exists stack_head. split; [exact Hhead|].
      apply IH. exists stack_middle. split; assumption.
Qed.

(** Flattening a sequence at the zipper head is definitionally neutral for
    the LIFO analysis, but strictly exposes both children to normalization. *)
Definition expand_sequence_suffix
    {cost Γ fuel entry statement first middle second next exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      first middle)
    (second_certificate : Atomicity.analysis_certificate cost Γ fuel middle
      second next)
    (rest : certificate_suffix cost Γ next exit) :
    certificate_suffix cost Γ entry exit :=
  SuffixCons first_certificate (SuffixCons second_certificate rest).

Lemma expand_sequence_suffix_lifo
    {cost Γ fuel entry statement first middle second next exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      first middle)
    (second_certificate : Atomicity.analysis_certificate cost Γ fuel middle
      second next)
    (rest : certificate_suffix cost Γ next exit) stack_in stack_out :
  suffix_lifo
    (SuffixCons
      (Atomicity.CertSequence cost Γ fuel entry statement first middle second
        next view first_certificate second_certificate) rest)
    stack_in stack_out <->
  suffix_lifo
    (expand_sequence_suffix view first_certificate second_certificate rest)
    stack_in stack_out.
Proof. simpl. firstorder. Qed.

Definition certificate_source_size
    {cost Γ fuel entry statement exit}
    (_ : Atomicity.analysis_certificate cost Γ fuel entry statement exit) : nat :=
  Runtime.RegionSyntax.size statement.

Fixpoint suffix_measure {cost Γ entry exit}
    (suffix : certificate_suffix cost Γ entry exit) : nat :=
  match suffix with
  | SuffixDone _ => 0
  | SuffixCons certificate rest =>
      certificate_source_size certificate + suffix_measure rest
  end.

Lemma suffix_rest_measure_decreases
    {cost Γ fuel entry statement middle exit}
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle) (rest : certificate_suffix cost Γ middle exit) :
  suffix_measure rest < suffix_measure (SuffixCons certificate rest).
Proof.
  simpl. unfold certificate_source_size.
  pose proof (Runtime.RegionSyntax.size_positive Γ statement) as Hpositive.
  lia.
Qed.

Lemma expand_sequence_suffix_measure_decreases
    {cost Γ fuel entry statement first middle second next exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      first middle)
    (second_certificate : Atomicity.analysis_certificate cost Γ fuel middle
      second next)
    (rest : certificate_suffix cost Γ next exit) :
  suffix_measure
      (expand_sequence_suffix view first_certificate second_certificate rest) <
  suffix_measure
      (SuffixCons
        (Atomicity.CertSequence cost Γ fuel entry statement first middle second
          next view first_certificate second_certificate) rest).
Proof.
  unfold expand_sequence_suffix. simpl. unfold certificate_source_size.
  destruct statement; simpl in view; try discriminate.
  inversion view; subst. simpl. lia.
Qed.

Lemma conditional_then_measure_decreases
    {cost Γ fuel entry statement then_statement else_statement
      then_exit else_exit exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewConditional then_statement else_statement)
    (then_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      then_statement then_exit)
    (else_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      else_statement else_exit)
    (open_equal : Atomicity.analysis_open then_exit =
      Atomicity.analysis_open else_exit)
    (atomic_equal : Atomicity.analysis_in_atomic then_exit =
      Atomicity.analysis_in_atomic else_exit)
    (rest : certificate_suffix cost Γ
      (Atomicity.AnalysisState
        (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
        (Atomicity.analysis_open then_exit)
        (Atomicity.analysis_step_taken then_exit ||
          Atomicity.analysis_step_taken else_exit)
        (Atomicity.analysis_in_atomic then_exit)) exit) :
  suffix_measure (SuffixCons then_certificate (SuffixDone then_exit)) <
  suffix_measure
    (SuffixCons
      (Atomicity.CertConditional cost Γ fuel entry statement then_statement
        else_statement then_exit else_exit view then_certificate
        else_certificate open_equal atomic_equal) rest).
Proof.
  simpl. unfold certificate_source_size.
  destruct (Runtime.RegionSyntax.conditional_children_smaller Γ statement
    then_statement else_statement view) as [Hthen _]. lia.
Qed.

Lemma conditional_else_measure_decreases
    {cost Γ fuel entry statement then_statement else_statement
      then_exit else_exit exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewConditional then_statement else_statement)
    (then_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      then_statement then_exit)
    (else_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      else_statement else_exit)
    (open_equal : Atomicity.analysis_open then_exit =
      Atomicity.analysis_open else_exit)
    (atomic_equal : Atomicity.analysis_in_atomic then_exit =
      Atomicity.analysis_in_atomic else_exit)
    (rest : certificate_suffix cost Γ
      (Atomicity.AnalysisState
        (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
        (Atomicity.analysis_open then_exit)
        (Atomicity.analysis_step_taken then_exit ||
          Atomicity.analysis_step_taken else_exit)
        (Atomicity.analysis_in_atomic then_exit)) exit) :
  suffix_measure (SuffixCons else_certificate (SuffixDone else_exit)) <
  suffix_measure
    (SuffixCons
      (Atomicity.CertConditional cost Γ fuel entry statement then_statement
        else_statement then_exit else_exit view then_certificate
        else_certificate open_equal atomic_equal) rest).
Proof.
  simpl. unfold certificate_source_size.
  destruct (Runtime.RegionSyntax.conditional_children_smaller Γ statement
    then_statement else_statement view) as [_ Helse]. lia.
Qed.

Fixpoint append_execution {entry stack_in middle stack_middle}
    (first : Slice.execution entry stack_in middle stack_middle)
    {exit}
    : Slice.execution middle stack_middle exit stack_middle ->
      Slice.execution entry stack_in exit stack_middle :=
  match first in Slice.execution e si m sm return
      Slice.execution m sm exit sm -> Slice.execution e si exit sm
  with
  | Slice.ExecDone _ _ => fun second => second
  | Slice.ExecChunk _ _ _ _ _ head rest =>
      fun second => Slice.ExecChunk _ _ _ _ _ head
        (append_execution rest second)
  | Slice.ExecAccess _ _ _ _ _ _ opening open_ok body rest =>
      fun second => Slice.ExecAccess _ _ _ _ _ _ opening open_ok body
        (append_execution rest second)
  | Slice.ExecFocusedOutcome _ _ _ _ _ _ outcome rest =>
      fun second => Slice.ExecFocusedOutcome _ _ _ _ _ _ outcome
        (append_execution rest second)
  | Slice.ExecFocusedClose _ _ _ _ _ _ body rest =>
      fun second => Slice.ExecFocusedClose _ _ _ _ _ _ body
        (append_execution rest second)
  | Slice.ExecClose _ _ _ _ _ _ closing close_ok rest =>
      fun second => Slice.ExecClose _ _ _ _ _ _ closing close_ok
        (append_execution rest second)
  | Slice.ExecConditional _ _ _ _ _ _ _ test then_branch else_branch rest =>
      fun second => Slice.ExecConditional _ _ _ _ _ _ _ test
        then_branch else_branch
        (append_execution rest second)
  end.

(** Primitive Raven certificates embed without hiding control structure. *)
Definition leaf_piece {cost Γ fuel entry statement exit stack}
    (view : Runtime.RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : Atomicity.take_step (cost Γ statement) entry = inr exit) :
    Payload.chunk entry stack exit stack :=
  Payload.ChunkLeaf Γ fuel cost entry statement exit stack view step.

Definition unfold_piece {cost Γ fuel entry statement invariant exit stack}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewUnfold invariant)
    (step : Atomicity.open_invariant invariant entry = inr exit) :
    Payload.chunk entry stack exit
      ((invariant, Atomicity.analysis_open entry) :: stack) :=
  Payload.ChunkUnfold Γ fuel cost entry statement invariant exit stack
    view step.

Definition fold_piece {cost Γ fuel entry statement invariant outer tail}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    (member : invariant ∈ Atomicity.analysis_open entry)
    (fresh : invariant ∉ outer)
    (opened : Atomicity.analysis_open entry = {[invariant]} ∪ outer) :
    Payload.chunk entry ((invariant, outer) :: tail)
      (Atomicity.fold_invariant invariant entry) tail :=
  Payload.ChunkFold Γ fuel cost entry statement invariant outer tail view
    member fresh opened.

Definition fresh_fold_piece
    {cost Γ fuel entry statement invariant stack}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    (closed : invariant ∉ Atomicity.analysis_open entry) :
    Payload.chunk entry stack (Atomicity.fold_invariant invariant entry) stack :=
  Payload.ChunkFreshFold Γ fuel cost entry statement invariant stack view
    closed.

Definition atomic_piece {cost Γ fuel entry statement body outer inner stack}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewAtomic body)
    (step : Atomicity.take_step Atomicity.AtomicStep entry = inr outer)
    (body_certificate : Atomicity.analysis_certificate cost Γ fuel
      (Atomicity.AnalysisState (Atomicity.analysis_mask outer)
        (Atomicity.analysis_open outer)
        (Atomicity.analysis_step_taken outer) true) body inner)
    (open_equal : Atomicity.analysis_open inner =
      Atomicity.analysis_open outer) :
    Payload.chunk entry stack
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer)) stack :=
  Payload.ChunkAtomic Γ fuel cost entry statement body outer inner stack view
    step body_certificate open_equal.

(** A normalization witness is deliberately a relation rather than a
    certificate-local function.  An unfold has no normalized meaning until a
    later certificate supplies its first matching close.  The relation is
    indexed by the analyzer certificate and its exact LIFO endpoints, making
    it suitable as the target of the aligned-zipper induction. *)
Record normalization {cost Γ fuel entry statement exit stack_in stack_out}
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry
      statement exit) : Type := {
  normalized_lifo : Atomicity.lifo_certificate certificate stack_in stack_out;
  normalized_tree : Slice.execution entry stack_in exit stack_out;
}.

Definition sequence_normalization
    {cost Γ fuel entry statement first middle second exit
      stack_in stack_middle}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      first middle)
    (second_certificate : Atomicity.analysis_certificate cost Γ fuel middle
      second exit)
    (first_normal : @normalization cost Γ fuel entry first middle stack_in
      stack_middle first_certificate)
    (second_normal : @normalization cost Γ fuel middle second exit stack_middle
      stack_middle second_certificate) :
    @normalization cost Γ (S fuel) entry statement exit stack_in stack_middle
      (Atomicity.CertSequence cost Γ fuel entry statement first middle second
        exit view first_certificate second_certificate).
Proof.
  refine {| normalized_tree := append_execution
    (normalized_tree first_certificate first_normal)
    (normalized_tree second_certificate second_normal) |}.
  simpl. exists stack_middle. split.
  - exact (normalized_lifo first_certificate first_normal).
  - exact (normalized_lifo second_certificate second_normal).
Defined.

(** Focused witnesses separate the first close from all subsequent work.
    In particular, [focused_post_close] may reopen the same invariant. *)
Record focused_normalization
    {cost Γ fuel entry statement exit invariant outer tail}
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry
      statement exit) : Type := {
  focused_lifo : Atomicity.lifo_certificate certificate
    ((invariant, outer) :: tail) tail;
  focused_first_close : Atomicity.analysis_state;
  focused_tree : Slice.focused_execution (invariant, outer) tail entry
    focused_first_close;
  focused_post_close : Slice.execution focused_first_close tail exit tail;
}.

(** Zipper-level witnesses are the induction interface used by total
    normalization.  They deliberately mirror the public single-certificate
    records, but do not force sequence nodes to remain nested. *)
Record suffix_normalization
    {cost Γ entry exit stack_in stack_out}
    (suffix : certificate_suffix cost Γ entry exit) : Type := {
  suffix_normalized_lifo : suffix_lifo suffix stack_in stack_out;
  suffix_normalized_tree : Slice.execution entry stack_in exit stack_out;
}.

Record suffix_focused_normalization
    {cost Γ entry exit invariant outer tail}
    (suffix : certificate_suffix cost Γ entry exit) : Type := {
  suffix_focused_lifo : suffix_lifo suffix
    ((invariant, outer) :: tail) tail;
  suffix_first_close : Atomicity.analysis_state;
  suffix_focused_tree : Slice.focused_execution (invariant, outer) tail entry
    suffix_first_close;
  suffix_post_close : Slice.execution suffix_first_close tail exit tail;
}.

Record suffix_close_normalization
    {cost Γ entry exit invariant outer tail stack_out}
    (suffix : certificate_suffix cost Γ entry exit) : Type := {
  suffix_close_lifo : suffix_lifo suffix
    ((invariant, outer) :: tail) stack_out;
  suffix_close_state : Atomicity.analysis_state;
  suffix_close_tree : Slice.focused_execution (invariant, outer) tail entry
    suffix_close_state;
  suffix_after_close : Slice.execution suffix_close_state tail exit stack_out;
}.

(** Proof-relevant first-close decomposition.  Keeping the residual zipper is
    essential for nested access: after closing the nested accessor, the
    normalizer must recurse on exactly this suffix to locate an enclosing
    close. *)
Record suffix_close_split
    {cost Γ entry exit invariant outer tail stack_out}
    (suffix : certificate_suffix cost Γ entry exit) : Type := {
  split_close_state : Atomicity.analysis_state;
  split_prefix : certificate_suffix cost Γ entry split_close_state;
  split_rest : certificate_suffix cost Γ split_close_state exit;
  split_recompose : suffix_expands cost Γ entry exit
    (append_suffix split_prefix split_rest) suffix;
  split_prefix_lifo : suffix_lifo split_prefix
    ((invariant, outer) :: tail) tail;
  split_rest_lifo : suffix_lifo split_rest tail stack_out;
  split_close_tree : Slice.focused_execution (invariant, outer) tail entry
    split_close_state;
  split_rest_tree : Slice.execution split_close_state tail exit stack_out;
}.

Definition close_normalization_of_split
    {cost Γ entry exit invariant outer tail stack_out}
    {suffix : certificate_suffix cost Γ entry exit}
    (split : @suffix_close_split cost Γ entry exit invariant outer tail
      stack_out suffix) :
    @suffix_close_normalization cost Γ entry exit invariant outer tail
      stack_out suffix.
Proof.
  refine {| suffix_close_state := split_close_state _ split;
            suffix_close_tree := split_close_tree _ split;
            suffix_after_close := split_rest_tree _ split |}.
  apply (proj1 (suffix_expands_lifo (split_recompose _ split) _ _)).
  apply suffix_lifo_append. exists tail. split.
  - exact (split_prefix_lifo _ split).
  - exact (split_rest_lifo _ split).
Defined.

Definition normalize_suffix_close_split
    {cost Γ entry exit invariant outer tail stack_out}
    {suffix : certificate_suffix cost Γ entry exit}
    (split : @suffix_close_split cost Γ entry exit invariant outer tail
      stack_out suffix) :
    @suffix_normalization cost Γ entry exit ((invariant, outer) :: tail)
      stack_out suffix.
Proof.
  pose (normal := close_normalization_of_split split).
  refine {| suffix_normalized_lifo := suffix_close_lifo _ normal;
            suffix_normalized_tree :=
              Slice.ExecFocusedClose (invariant, outer) tail entry
                (suffix_close_state _ normal) exit stack_out
                (suffix_close_tree _ normal)
                (suffix_after_close _ normal) |}.
Defined.

Record suffix_outcome_normalization
    {cost Γ entry exit invariant outer tail}
    (suffix : certificate_suffix cost Γ entry exit) : Type := {
  suffix_outcome_lifo : suffix_lifo suffix
    ((invariant, outer) :: tail) ((invariant, outer) :: tail);
  suffix_outcome_tree : Slice.focused_outcome (invariant, outer) tail entry
    exit ((invariant, outer) :: tail);
}.

Record suffix_prefix_normalization
    {cost Γ entry exit invariant outer tail}
    (suffix : certificate_suffix cost Γ entry exit) : Type := {
  suffix_prefix_lifo : suffix_lifo suffix
    ((invariant, outer) :: tail) ((invariant, outer) :: tail);
  suffix_prefix_tree : Slice.focused_prefix (invariant, outer) tail entry exit;
}.

Record suffix_reopen_normalization
    {cost Γ entry exit invariant outer tail}
    (suffix : certificate_suffix cost Γ entry exit) : Type := {
  suffix_reopen_lifo : suffix_lifo suffix tail ((invariant, outer) :: tail);
  suffix_reopen_entry : Atomicity.analysis_state;
  suffix_reopened_state : Atomicity.analysis_state;
  suffix_before_reopen : Slice.execution entry tail suffix_reopen_entry tail;
  suffix_reopen_chunk : Payload.chunk suffix_reopen_entry tail
    suffix_reopened_state ((invariant, outer) :: tail);
  suffix_reopen_ok : Payload.opens (invariant, outer) tail suffix_reopen_entry
    suffix_reopened_state suffix_reopen_chunk;
  suffix_after_reopen : Slice.focused_prefix (invariant, outer) tail
    suffix_reopened_state exit;
}.

Inductive reopen_path (base : list Payload.marker) :
    list Payload.marker -> Payload.state -> Payload.state -> Type :=
| ReopenPathDone entry exit
    (before : Slice.execution entry base exit base) :
    reopen_path base [] entry exit
| ReopenPathPush added marker entry open_entry opened exit
    (before : reopen_path base added entry open_entry)
    (opening : Payload.chunk open_entry (added ++ base) opened
      (marker :: added ++ base))
    (open_ok : Payload.opens marker (added ++ base) open_entry opened opening)
    (after : Slice.focused_prefix marker (added ++ base) opened exit) :
    reopen_path base (marker :: added) entry exit.

(** General normalized executions.  In mode [None], [tail] is the complete
    input stack.  In mode [Some focused], the input is [focused :: tail] and
    the tree records behavior relative to that focus.  Unlike
    [Slice.execution], the output stack is unrestricted, which is essential
    when a nested access closes and its continuation then closes an enclosing
    accessor. *)
Inductive net_tree : option Payload.marker -> list Payload.marker ->
    list Payload.marker -> Payload.state -> Payload.state -> Type :=
| NetOrdinary stack_in stack_out entry exit
    (tree : Slice.execution entry stack_in exit stack_out) :
    net_tree None stack_in stack_out entry exit
| NetChunk stack middle stack_out entry exit
    (head : Payload.chunk entry stack middle stack)
    (rest : net_tree None stack stack_out middle exit) :
    net_tree None stack stack_out entry exit
| NetClose focused tail stack_out entry closed exit
    (closing : Payload.chunk entry (focused :: tail) closed tail)
    (close_ok : Payload.closes focused tail entry closed closing)
    (rest : net_tree None tail stack_out closed exit) :
    net_tree None (focused :: tail) stack_out entry exit
| NetAccess tail stack_out focused entry opened exit
    (opening : Payload.chunk entry tail opened (focused :: tail))
    (open_ok : Payload.opens focused tail entry opened opening)
    (body : net_tree (Some focused) tail stack_out opened exit) :
    net_tree None tail stack_out entry exit
| NetConditional stack_in join_stack stack_out entry then_exit else_exit join
    exit
    (test : Payload.conditional entry then_exit else_exit join)
    (then_net : net_tree None stack_in join_stack entry then_exit)
    (else_net : net_tree None stack_in join_stack entry else_exit)
    (rest : net_tree None join_stack stack_out join exit) :
    net_tree None stack_in stack_out entry exit
| FocusNetClose focused tail stack_out entry closed exit
    (first_close : Slice.focused_execution focused tail entry closed)
    (after_close : net_tree None tail stack_out closed exit) :
    net_tree (Some focused) tail stack_out entry exit
| FocusNetOutcome focused tail entry exit
    (outcome : Slice.focused_outcome focused tail entry exit
      (focused :: tail)) :
    net_tree (Some focused) tail (focused :: tail) entry exit
| FocusNetPrefix focused tail stack_out entry middle exit
    (prefix : Payload.chunk entry (focused :: tail) middle (focused :: tail))
    (prefix_ok : Payload.preserves focused tail entry middle prefix)
    (rest : net_tree (Some focused) tail stack_out middle exit) :
    net_tree (Some focused) tail stack_out entry exit
| FocusNetNested focused tail stack_out nested entry opened exit
    (opening : Payload.chunk entry (focused :: tail) opened
      (nested :: focused :: tail))
    (open_ok : Payload.opens nested (focused :: tail) entry opened opening)
    (body : net_tree (Some nested) (focused :: tail) stack_out opened exit) :
    net_tree (Some focused) tail stack_out entry exit
| FocusNetConditional focused tail join_stack stack_out entry then_exit
    else_exit join exit
    (test : Payload.conditional entry then_exit else_exit join)
    (then_net : net_tree (Some focused) tail join_stack entry then_exit)
    (else_net : net_tree (Some focused) tail join_stack entry else_exit)
    (rest : net_tree None join_stack stack_out join exit) :
    net_tree (Some focused) tail stack_out entry exit
| FocusNetConditionalContinue focused tail stack_out entry then_exit
    else_exit join exit
    (test : Payload.conditional entry then_exit else_exit join)
    (then_net : net_tree (Some focused) tail (focused :: tail) entry then_exit)
    (else_net : net_tree (Some focused) tail (focused :: tail) entry else_exit)
    (rest : net_tree (Some focused) tail stack_out join exit) :
    net_tree (Some focused) tail stack_out entry exit.

Definition normalized_net stack_in stack_out entry exit :=
  net_tree None stack_in stack_out entry exit.

Definition focused_net focused tail stack_out entry exit :=
  net_tree (Some focused) tail stack_out entry exit.

Module NetDenotation (Semantics : CONDITIONAL_SLICE_SEMANTICS Payload).
  Module SliceDenotation :=
    ConditionalSliceDenotation Payload Slice Semantics.

  Import Semantics.

  Fixpoint net_tree_wp {mode tail stack_out entry exit}
      (tree : net_tree mode tail stack_out entry exit)
      (post : formula) : formula :=
    match tree with
    | NetOrdinary _ _ _ _ ordinary =>
        SliceDenotation.execution_wp ordinary post
    | NetChunk _ _ _ _ _ head rest =>
        chunk_wp _ _ _ _ head (net_tree_wp rest post)
    | NetClose _ _ _ _ _ _ closing _ rest =>
        chunk_wp _ _ _ _ closing (net_tree_wp rest post)
    | NetAccess _ _ _ _ _ _ opening _ body =>
        chunk_wp _ _ _ _ opening (net_tree_wp body post)
    | NetConditional _ _ _ _ _ _ _ _ test then_net else_net rest =>
        let shared := net_tree_wp rest post in
        conditional_wp _ _ _ _ test
          (net_tree_wp then_net shared) (net_tree_wp else_net shared)
    | FocusNetClose _ _ _ _ _ _ first_close after_close =>
        SliceDenotation.focused_execution_wp first_close
          (net_tree_wp after_close post)
    | FocusNetOutcome _ _ _ _ outcome =>
        SliceDenotation.focused_outcome_wp outcome post
    | FocusNetPrefix _ _ _ _ _ _ prefix _ rest =>
        chunk_wp _ _ _ _ prefix (net_tree_wp rest post)
    | FocusNetNested _ _ _ _ _ _ _ opening _ body =>
        chunk_wp _ _ _ _ opening (net_tree_wp body post)
    | FocusNetConditional _ _ _ _ _ _ _ _ _ test then_net else_net rest =>
        let shared := net_tree_wp rest post in
        conditional_wp _ _ _ _ test
          (net_tree_wp then_net shared) (net_tree_wp else_net shared)
    | FocusNetConditionalContinue _ _ _ _ _ _ _ _ test then_net else_net rest =>
        let shared := net_tree_wp rest post in
        conditional_wp _ _ _ _ test
          (net_tree_wp then_net shared) (net_tree_wp else_net shared)
    end.
End NetDenotation.

Module NetMonotonicity
    (Semantics : CONDITIONAL_SLICE_SEMANTICS Payload)
    (Order : CONDITIONAL_SLICE_MONOTONE Payload Semantics).
  Module Denotation := NetDenotation Semantics.
  Module SliceMonotonicity :=
    ConditionalSliceMonotonicity Payload Slice Semantics Order.

  Import Semantics Order Denotation.

  Lemma net_tree_wp_mono mode tail stack_out entry exit
      (tree : net_tree mode tail stack_out entry exit) left right :
    entails left right ->
    entails (net_tree_wp tree left) (net_tree_wp tree right).
  Proof.
    revert left right. induction tree; intros left right Hentails; simpl.
    - apply SliceMonotonicity.execution_wp_mono. exact Hentails.
    - apply chunk_wp_mono. apply IHtree. exact Hentails.
    - apply chunk_wp_mono. apply IHtree. exact Hentails.
    - apply chunk_wp_mono. apply IHtree. exact Hentails.
    - apply conditional_wp_mono; [apply IHtree1|apply IHtree2].
      all: apply IHtree3; exact Hentails.
    - apply SliceMonotonicity.focused_execution_wp_mono.
      apply IHtree. exact Hentails.
    - apply SliceMonotonicity.focused_outcome_wp_mono. exact Hentails.
    - apply chunk_wp_mono. apply IHtree. exact Hentails.
    - apply chunk_wp_mono. apply IHtree. exact Hentails.
    - apply conditional_wp_mono; [apply IHtree1|apply IHtree2].
      all: apply IHtree3; exact Hentails.
    - apply conditional_wp_mono; [apply IHtree1|apply IHtree2].
      all: apply IHtree3; exact Hentails.
  Qed.
End NetMonotonicity.

(** Iris specialization.  Concrete Raven runtime resources only need to
    provide the existing chunk and conditional interfaces; the generalized
    net continuation and its monotonicity are derived here. *)
Module IrisNetDenotation
    (IrisSemantics :
      IRIS_CONDITIONAL_SLICE_SEMANTICS Payload).
  Module Base := IrisConditionalSlice Payload Slice IrisSemantics.
  Module Denotation := NetDenotation Base.Semantics.
  Module Monotonicity := NetMonotonicity Base.Semantics Base.Order.
End IrisNetDenotation.

(** Source provenance for normalized payload nodes.  Unlike [Payload.chunk]
    itself, this relation is indexed by the fixed Raven context [Γ], so a
    later runtime interpretation can use one concrete [stack_context Γ]. *)
Inductive chunk_certificate (cost : Atomicity.cost_model) Γ :
    forall fuel entry statement exit stack_in stack_out,
      Atomicity.analysis_certificate cost Γ fuel entry statement exit ->
      Payload.chunk entry stack_in exit stack_out -> Type :=
| ChunkCertificateLeaf fuel entry statement exit stack view step :
    chunk_certificate cost Γ (S fuel) entry statement exit stack stack
      (Atomicity.CertLeaf cost Γ fuel entry statement exit view step)
      (Payload.ChunkLeaf Γ fuel cost entry statement exit stack view step)
| ChunkCertificateUnfold fuel entry statement invariant exit stack view step :
    chunk_certificate cost Γ (S fuel) entry statement exit stack
      ((invariant, Atomicity.analysis_open entry) :: stack)
      (Atomicity.CertUnfold cost Γ fuel entry statement invariant exit view
        step)
      (Payload.ChunkUnfold Γ fuel cost entry statement invariant exit stack
        view step)
| ChunkCertificateFold fuel entry statement invariant outer tail view member
    fresh opened :
    chunk_certificate cost Γ (S fuel) entry statement
      (Atomicity.fold_invariant invariant entry)
      ((invariant, outer) :: tail) tail
      (Atomicity.CertFold cost Γ fuel entry statement invariant view)
      (Payload.ChunkFold Γ fuel cost entry statement invariant outer tail view
        member fresh opened)
| ChunkCertificateFreshFold fuel entry statement invariant stack view closed :
    chunk_certificate cost Γ (S fuel) entry statement
      (Atomicity.fold_invariant invariant entry) stack stack
      (Atomicity.CertFold cost Γ fuel entry statement invariant view)
      (Payload.ChunkFreshFold Γ fuel cost entry statement invariant stack view
        closed)
| ChunkCertificateAtomic fuel entry statement body outer inner stack view step
    body_certificate open_equal :
    chunk_certificate cost Γ (S fuel) entry statement
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer)) stack stack
      (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
        step body_certificate open_equal)
      (Payload.ChunkAtomic Γ fuel cost entry statement body outer inner stack
        view step body_certificate open_equal).

Definition conditional_join (then_exit else_exit : Atomicity.analysis_state) :=
  Atomicity.AnalysisState
    (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
    (Atomicity.analysis_open then_exit)
    (Atomicity.analysis_step_taken then_exit ||
      Atomicity.analysis_step_taken else_exit)
    (Atomicity.analysis_in_atomic then_exit).

Inductive conditional_certificate (cost : Atomicity.cost_model) Γ :
    forall fuel entry statement then_statement else_statement then_exit
      else_exit join,
      Atomicity.analysis_certificate cost Γ fuel entry statement join ->
      Payload.conditional entry then_exit else_exit join -> Type :=
| ConditionalCertificate fuel entry statement then_statement else_statement
    then_exit else_exit view then_certificate else_certificate open_equal
    atomic_equal :
    conditional_certificate cost Γ (S fuel) entry statement then_statement
      else_statement then_exit else_exit
      (Atomicity.AnalysisState
        (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
        (Atomicity.analysis_open then_exit)
        (Atomicity.analysis_step_taken then_exit ||
          Atomicity.analysis_step_taken else_exit)
        (Atomicity.analysis_in_atomic then_exit))
      (Atomicity.CertConditional cost Γ fuel entry statement then_statement
        else_statement then_exit else_exit view then_certificate
        else_certificate open_equal atomic_equal)
      (Payload.RavenConditional Γ fuel cost entry statement then_statement
        else_statement then_exit else_exit view then_certificate
        else_certificate open_equal atomic_equal).

(** Proof-relevant correspondence between a source certificate zipper and
    its normalized continuation tree.  Every semantic node is justified by
    the exact certificate or structural expansion that produced it. *)
Inductive net_trace (cost : Atomicity.cost_model) Γ :
    forall entry exit mode tail stack_out,
      certificate_suffix cost Γ entry exit ->
      net_tree mode tail stack_out entry exit -> Type :=
| TraceDoneNet entry stack :
    net_trace cost Γ entry entry None stack stack
      (SuffixDone entry)
      (@NetOrdinary stack stack entry entry (Slice.ExecDone entry stack))
| TraceDoneFocused entry focused tail :
    net_trace cost Γ entry entry (Some focused) tail (focused :: tail)
      (SuffixDone entry)
      (@FocusNetOutcome focused tail entry entry
        (Slice.OutcomeStillOpen focused tail entry entry
          (Slice.FocusedPrefixDone focused tail entry)))
| TraceChunk fuel entry statement middle exit stack stack_out
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle) (rest : certificate_suffix cost Γ middle exit)
    (head : Payload.chunk entry stack middle stack)
    (Hhead : chunk_certificate cost Γ fuel entry statement middle stack stack
      certificate head)
    (rest_tree : net_tree None stack stack_out middle exit)
    (Hrest : net_trace cost Γ middle exit None stack stack_out rest rest_tree) :
    net_trace cost Γ entry exit None stack stack_out
      (SuffixCons certificate rest)
      (@NetChunk stack middle stack_out entry exit head rest_tree)
| TraceFocusedPrefix fuel entry statement middle exit focused tail stack_out
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle) (rest : certificate_suffix cost Γ middle exit)
    (head : Payload.chunk entry (focused :: tail) middle (focused :: tail))
    (Hhead : chunk_certificate cost Γ fuel entry statement middle
      (focused :: tail) (focused :: tail) certificate head)
    (head_ok : Payload.preserves focused tail entry middle head)
    (rest_tree : net_tree (Some focused) tail stack_out middle exit)
    (Hrest : net_trace cost Γ middle exit (Some focused) tail stack_out rest
      rest_tree) :
    net_trace cost Γ entry exit (Some focused) tail stack_out
      (SuffixCons certificate rest)
      (@FocusNetPrefix focused tail stack_out entry middle exit head head_ok
        rest_tree)
| TraceAccess fuel entry statement opened exit focused tail stack_out
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      opened) (rest : certificate_suffix cost Γ opened exit)
    (opening : Payload.chunk entry tail opened (focused :: tail))
    (Hopening : chunk_certificate cost Γ fuel entry statement opened tail
      (focused :: tail) certificate opening)
    (open_ok : Payload.opens focused tail entry opened opening)
    (body : net_tree (Some focused) tail stack_out opened exit)
    (Hbody : net_trace cost Γ opened exit (Some focused) tail stack_out rest
      body) :
    net_trace cost Γ entry exit None tail stack_out
      (SuffixCons certificate rest)
      (@NetAccess tail stack_out focused entry opened exit opening open_ok body)
| TraceNestedAccess fuel entry statement opened exit focused tail nested
    stack_out
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      opened) (rest : certificate_suffix cost Γ opened exit)
    (opening : Payload.chunk entry (focused :: tail) opened
      (nested :: focused :: tail))
    (Hopening : chunk_certificate cost Γ fuel entry statement opened
      (focused :: tail) (nested :: focused :: tail) certificate opening)
    (open_ok : Payload.opens nested (focused :: tail) entry opened opening)
    (body : net_tree (Some nested) (focused :: tail) stack_out opened exit)
    (Hbody : net_trace cost Γ opened exit (Some nested) (focused :: tail)
      stack_out rest body) :
    net_trace cost Γ entry exit (Some focused) tail stack_out
      (SuffixCons certificate rest)
      (@FocusNetNested focused tail stack_out nested entry opened exit opening
        open_ok body)
| TraceClose fuel entry statement closed exit focused tail stack_out
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      closed) (rest : certificate_suffix cost Γ closed exit)
    (closing : Payload.chunk entry (focused :: tail) closed tail)
    (Hclosing : chunk_certificate cost Γ fuel entry statement closed
      (focused :: tail) tail certificate closing)
    (close_ok : Payload.closes focused tail entry closed closing)
    (rest_tree : net_tree None tail stack_out closed exit)
    (Hrest : net_trace cost Γ closed exit None tail stack_out rest rest_tree) :
    net_trace cost Γ entry exit None (focused :: tail) stack_out
      (SuffixCons certificate rest)
      (@NetClose focused tail stack_out entry closed exit closing close_ok
        rest_tree)
| TraceFocusedClose fuel entry statement closed exit focused tail stack_out
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      closed) (rest : certificate_suffix cost Γ closed exit)
    (closing : Payload.chunk entry (focused :: tail) closed tail)
    (Hclosing : chunk_certificate cost Γ fuel entry statement closed
      (focused :: tail) tail certificate closing)
    (close_ok : Payload.closes focused tail entry closed closing)
    (rest_tree : net_tree None tail stack_out closed exit)
    (Hrest : net_trace cost Γ closed exit None tail stack_out rest rest_tree) :
    net_trace cost Γ entry exit (Some focused) tail stack_out
      (SuffixCons certificate rest)
      (@FocusNetClose focused tail stack_out entry closed exit
        (Slice.FocusedClose focused tail entry closed closing close_ok)
        rest_tree)
| TraceConditional fuel entry statement then_statement else_statement
    then_exit else_exit exit stack_in join_stack stack_out view
    then_certificate else_certificate open_equal atomic_equal rest
    (then_tree : net_tree None stack_in join_stack entry then_exit)
    (else_tree : net_tree None stack_in join_stack entry else_exit)
    (rest_tree : net_tree None join_stack stack_out
      (conditional_join then_exit else_exit) exit)
    (Hthen : net_trace cost Γ entry then_exit None stack_in join_stack
      (SuffixCons then_certificate (SuffixDone then_exit)) then_tree)
    (Helse : net_trace cost Γ entry else_exit None stack_in join_stack
      (SuffixCons else_certificate (SuffixDone else_exit)) else_tree)
    (Hrest : net_trace cost Γ (conditional_join then_exit else_exit) exit None
      join_stack stack_out rest rest_tree) :
    net_trace cost Γ entry exit None stack_in stack_out
      (SuffixCons
        (Atomicity.CertConditional cost Γ fuel entry statement then_statement
          else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal) rest)
      (@NetConditional stack_in join_stack stack_out entry then_exit else_exit
        (conditional_join then_exit else_exit) exit
        (Payload.RavenConditional Γ fuel cost entry statement then_statement
          else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal)
        then_tree else_tree rest_tree)
| TraceFocusedConditional fuel entry statement then_statement else_statement
    then_exit else_exit exit focused tail join_stack stack_out view
    then_certificate else_certificate open_equal atomic_equal rest
    (then_tree : net_tree (Some focused) tail join_stack entry then_exit)
    (else_tree : net_tree (Some focused) tail join_stack entry else_exit)
    (rest_tree : net_tree None join_stack stack_out
      (conditional_join then_exit else_exit) exit)
    (Hthen : net_trace cost Γ entry then_exit (Some focused) tail join_stack
      (SuffixCons then_certificate (SuffixDone then_exit)) then_tree)
    (Helse : net_trace cost Γ entry else_exit (Some focused) tail join_stack
      (SuffixCons else_certificate (SuffixDone else_exit)) else_tree)
    (Hrest : net_trace cost Γ (conditional_join then_exit else_exit) exit None
      join_stack stack_out rest rest_tree) :
    net_trace cost Γ entry exit (Some focused) tail stack_out
      (SuffixCons
        (Atomicity.CertConditional cost Γ fuel entry statement then_statement
          else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal) rest)
      (@FocusNetConditional focused tail join_stack stack_out entry then_exit
        else_exit (conditional_join then_exit else_exit) exit
        (Payload.RavenConditional Γ fuel cost entry statement then_statement
          else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal)
        then_tree else_tree rest_tree)
| TraceFocusedConditionalContinue fuel entry statement then_statement
    else_statement then_exit else_exit exit focused tail stack_out view
    then_certificate else_certificate open_equal atomic_equal rest
    (then_tree : net_tree (Some focused) tail (focused :: tail) entry
      then_exit)
    (else_tree : net_tree (Some focused) tail (focused :: tail) entry
      else_exit)
    (rest_tree : net_tree (Some focused) tail stack_out
      (conditional_join then_exit else_exit) exit)
    (Hthen : net_trace cost Γ entry then_exit (Some focused) tail
      (focused :: tail)
      (SuffixCons then_certificate (SuffixDone then_exit)) then_tree)
    (Helse : net_trace cost Γ entry else_exit (Some focused) tail
      (focused :: tail)
      (SuffixCons else_certificate (SuffixDone else_exit)) else_tree)
    (Hrest : net_trace cost Γ (conditional_join then_exit else_exit) exit
      (Some focused) tail stack_out rest rest_tree) :
    net_trace cost Γ entry exit (Some focused) tail stack_out
      (SuffixCons
        (Atomicity.CertConditional cost Γ fuel entry statement then_statement
          else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal) rest)
      (@FocusNetConditionalContinue focused tail stack_out entry then_exit
        else_exit (conditional_join then_exit else_exit) exit
        (Payload.RavenConditional Γ fuel cost entry statement then_statement
          else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal)
        then_tree else_tree rest_tree)
| TraceExpansion entry exit mode tail stack_out flat source tree
    (expansion : suffix_expands cost Γ entry exit flat source)
    (Hflat : net_trace cost Γ entry exit mode tail stack_out flat tree) :
    net_trace cost Γ entry exit mode tail stack_out source tree.

Definition open_witness marker tail entry opened : Type :=
  { opening : Payload.chunk entry tail opened (marker :: tail) &
    Payload.opens marker tail entry opened opening }.

Definition transport_open_witness marker tail1 tail2 entry opened
    (Heq : tail1 = tail2) :
    open_witness marker tail1 entry opened ->
    open_witness marker tail2 entry opened.
Proof. destruct Heq. exact (fun witness => witness). Defined.

Record suffix_reopen_path_normalization
    {cost Γ entry exit base added}
    (suffix : certificate_suffix cost Γ entry exit) : Type := {
  suffix_reopen_path_lifo : suffix_lifo suffix base (added ++ base);
  suffix_reopen_path_tree : reopen_path base added entry exit;
}.

Record suffix_focused_net_normalization
    {cost Γ entry exit invariant outer tail stack_out}
    (suffix : certificate_suffix cost Γ entry exit) : Type := {
  suffix_focused_net_lifo : suffix_lifo suffix
    ((invariant, outer) :: tail) stack_out;
  suffix_focused_net_tree : focused_net (invariant, outer) tail stack_out
    entry exit;
}.

Record suffix_net_normalization
    {cost Γ entry exit stack_in stack_out}
    (suffix : certificate_suffix cost Γ entry exit) : Type := {
  suffix_net_lifo : suffix_lifo suffix stack_in stack_out;
  suffix_net_tree : normalized_net stack_in stack_out entry exit;
}.

Record traced_suffix_net_normalization
    {cost Γ entry exit stack_in stack_out}
    (suffix : certificate_suffix cost Γ entry exit) : Type := {
  traced_net_normal :
    @suffix_net_normalization cost Γ entry exit stack_in stack_out suffix;
  traced_net_source : net_trace cost Γ entry exit None stack_in stack_out suffix
    (suffix_net_tree _ traced_net_normal);
}.

Record traced_suffix_focused_net_normalization
    {cost Γ entry exit invariant outer tail stack_out}
    (suffix : certificate_suffix cost Γ entry exit) : Type := {
  traced_focused_net_normal : @suffix_focused_net_normalization cost Γ entry
    exit invariant outer tail stack_out suffix;
  traced_focused_net_source : net_trace cost Γ entry exit
    (Some (invariant, outer)) tail stack_out suffix
    (suffix_focused_net_tree _ traced_focused_net_normal);
}.

Definition execution_of_focused_prefix focused tail entry exit
    (prefix : Slice.focused_prefix focused tail entry exit) :
    Slice.execution entry (focused :: tail) exit (focused :: tail).
Proof.
  induction prefix.
  - apply Slice.ExecDone.
  - exact (Slice.ExecChunk entry (focused :: tail) middle exit
      (focused :: tail) prefix IHprefix).
  - exact (Slice.ExecAccess nested (focused :: tail) entry opened nested_closed
      exit open_chunk open_ok nested_body IHprefix).
  - exact (Slice.ExecConditional entry (focused :: tail) then_exit else_exit
      join join (focused :: tail) test IHprefix1 IHprefix2
      (Slice.ExecDone join (focused :: tail))).
Defined.

Definition focused_net_of_close
    focused tail entry closed exit
    (first_close : Slice.focused_execution focused tail entry closed)
    (after_close : Slice.execution closed tail exit tail) :
    focused_net focused tail tail entry exit :=
  @FocusNetClose focused tail tail entry closed exit first_close
    (@NetOrdinary tail tail closed exit after_close).

Definition focused_net_of_outcome focused tail entry exit
    (outcome : Slice.focused_outcome focused tail entry exit
      (focused :: tail)) :
    focused_net focused tail (focused :: tail) entry exit :=
  @FocusNetOutcome focused tail entry exit outcome.

Definition prepend_reopen_path_chunk
    {base added entry middle exit}
    (head : Payload.chunk entry base middle base)
    (path : reopen_path base added middle exit) :
    reopen_path base added entry exit.
Proof.
  revert entry head.
  induction path; intros new_entry head.
  - apply ReopenPathDone.
    exact (Slice.ExecChunk new_entry base entry exit base head before).
  - exact (ReopenPathPush base added marker new_entry open_entry opened exit
      (IHpath new_entry head) opening open_ok after).
Defined.

Definition prepend_reopen_path_normalization
    {cost Γ fuel entry statement middle exit base added}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle} {rest : certificate_suffix cost Γ middle exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate base base)
    (head : Payload.chunk entry base middle base)
    (normal : @suffix_reopen_path_normalization cost Γ middle exit base added
      rest) :
    @suffix_reopen_path_normalization cost Γ entry exit base added
      (SuffixCons certificate rest).
Proof.
  refine {| suffix_reopen_path_tree :=
      prepend_reopen_path_chunk head (suffix_reopen_path_tree _ normal) |}.
  exists base. split; [exact certificate_lifo|].
  exact (suffix_reopen_path_lifo _ normal).
Defined.

Definition reopen_normalization_of_singleton_path
    {cost Γ entry exit invariant outer tail}
    {suffix : certificate_suffix cost Γ entry exit}
    (normal : @suffix_reopen_path_normalization cost Γ entry exit tail
      [(invariant, outer)] suffix) :
    @suffix_reopen_normalization cost Γ entry exit invariant outer tail suffix.
Proof.
  destruct normal as [Hlifo path]. simpl in Hlifo.
  dependent destruction path.
  match goal with
  | lower : reopen_path tail [] _ _ |- _ => dependent destruction lower
  end.
  refine {| suffix_reopen_lifo := Hlifo;
            suffix_reopen_entry := exit0;
            suffix_reopened_state := opened;
            suffix_before_reopen := before;
            suffix_reopen_chunk := opening;
            suffix_reopen_ok := open_ok;
            suffix_after_reopen := after |}.
Defined.

Definition matched_close_rebase_reopen_path
    {added popped base entry closed exit}
    (first_close : Slice.focused_execution popped base entry closed)
    (path : reopen_path base (added ++ [popped]) closed exit) :
    reopen_path (popped :: base) added entry exit.
Proof.
  revert entry closed exit first_close path.
  induction added as [|marker added IH];
    intros entry closed exit first_close path.
  - simpl in path. dependent destruction path.
    match goal with
    | lower : reopen_path base [] _ _ |- _ => dependent destruction lower
    end.
    apply ReopenPathDone.
    eapply Slice.ExecFocusedOutcome.
    + eapply Slice.OutcomeClosedReopened; eauto.
    + apply Slice.ExecDone.
  - simpl in path. dependent destruction path.
    assert (Hstack : (added ++ [popped]) ++ base =
        added ++ popped :: base).
    { rewrite <- app_assoc. reflexivity. }
    pose (transported := transport_open_witness marker _ _ open_entry opened
      Hstack (@existT _
        (fun candidate : Payload.chunk open_entry
          ((added ++ [popped]) ++ base) opened
          (marker :: (added ++ [popped]) ++ base) =>
          Payload.opens marker ((added ++ [popped]) ++ base) open_entry opened
            candidate)
        opening open_ok)).
    destruct transported as [transported_opening transported_ok].
    replace ((added ++ [popped]) ++ base) with
      (added ++ popped :: base) in after by
      (rewrite <- app_assoc; reflexivity).
    eapply ReopenPathPush; eauto using transported_ok.
Defined.

Definition prepend_reopen_execution
    {cost Γ fuel entry statement middle exit invariant outer tail}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle} {rest : certificate_suffix cost Γ middle exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate tail tail)
    (head : Payload.chunk entry tail middle tail)
    (normal : @suffix_reopen_normalization cost Γ middle exit invariant outer
      tail rest) :
    @suffix_reopen_normalization cost Γ entry exit invariant outer tail
      (SuffixCons certificate rest).
Proof.
  refine {| suffix_reopen_entry := suffix_reopen_entry _ normal;
            suffix_reopened_state := suffix_reopened_state _ normal;
            suffix_before_reopen :=
              Slice.ExecChunk entry tail middle (suffix_reopen_entry _ normal)
                tail head (suffix_before_reopen _ normal);
            suffix_reopen_chunk := suffix_reopen_chunk _ normal;
            suffix_reopen_ok := suffix_reopen_ok _ normal;
            suffix_after_reopen := suffix_after_reopen _ normal |}.
  exists tail. split; [exact certificate_lifo|].
  exact (suffix_reopen_lifo _ normal).
Defined.

Definition close_normalization_of_focused
    {cost Γ entry exit invariant outer tail}
    {suffix : certificate_suffix cost Γ entry exit}
    (normal : @suffix_focused_normalization cost Γ entry exit invariant outer
      tail suffix) :
    @suffix_close_normalization cost Γ entry exit invariant outer tail tail
      suffix :=
  {| suffix_close_lifo := suffix_focused_lifo _ normal;
     suffix_close_state := suffix_first_close _ normal;
     suffix_close_tree := suffix_focused_tree _ normal;
     suffix_after_close := suffix_post_close _ normal |}.

Definition outcome_normalization_of_close
    {cost Γ entry exit invariant outer tail}
    {suffix : certificate_suffix cost Γ entry exit}
    (normal : @suffix_close_normalization cost Γ entry exit invariant outer
      tail ((invariant, outer) :: tail) suffix) :
    @suffix_outcome_normalization cost Γ entry exit invariant outer tail
      suffix :=
  {| suffix_outcome_lifo := suffix_close_lifo _ normal;
     suffix_outcome_tree :=
       Slice.OutcomeClosed (invariant, outer) tail entry
         (suffix_close_state _ normal) exit ((invariant, outer) :: tail)
         (suffix_close_tree _ normal) (suffix_after_close _ normal) |}.

Definition outcome_normalization_of_prefix
    {cost Γ entry exit invariant outer tail}
    (suffix : certificate_suffix cost Γ entry exit)
    (lifo : suffix_lifo suffix ((invariant, outer) :: tail)
      ((invariant, outer) :: tail))
    (prefix : Slice.focused_prefix (invariant, outer) tail entry exit) :
    @suffix_outcome_normalization cost Γ entry exit invariant outer tail
      suffix :=
  {| suffix_outcome_lifo := lifo;
     suffix_outcome_tree :=
       Slice.OutcomeStillOpen (invariant, outer) tail entry exit prefix |}.

Definition outcome_normalization_of_prefix_witness
    {cost Γ entry exit invariant outer tail}
    {suffix : certificate_suffix cost Γ entry exit}
    (normal : @suffix_prefix_normalization cost Γ entry exit invariant outer
      tail suffix) :
    @suffix_outcome_normalization cost Γ entry exit invariant outer tail
      suffix :=
  outcome_normalization_of_prefix suffix (suffix_prefix_lifo _ normal)
    (suffix_prefix_tree _ normal).

Definition focused_net_normalization_of_outcome
    {cost Γ entry exit invariant outer tail}
    {suffix : certificate_suffix cost Γ entry exit}
    (normal : @suffix_outcome_normalization cost Γ entry exit invariant outer
      tail suffix) :
    @suffix_focused_net_normalization cost Γ entry exit invariant outer tail
      ((invariant, outer) :: tail) suffix.
Proof.
  refine {| suffix_focused_net_tree := focused_net_of_outcome
      (invariant, outer) tail entry exit (suffix_outcome_tree _ normal) |}.
  exact (suffix_outcome_lifo _ normal).
Defined.

Definition focused_net_normalization_of_close
    {cost Γ entry exit invariant outer tail}
    {suffix : certificate_suffix cost Γ entry exit}
    (normal : suffix_close_normalization (invariant := invariant)
      (outer := outer) (tail := tail) (stack_out := tail) suffix) :
    @suffix_focused_net_normalization cost Γ entry exit invariant outer tail
      tail suffix.
Proof.
  refine {| suffix_focused_net_tree := focused_net_of_close
      (invariant, outer) tail entry (suffix_close_state _ normal) exit
      (suffix_close_tree _ normal) (suffix_after_close _ normal) |}.
  exact (suffix_close_lifo _ normal).
Defined.

Definition normalize_suffix_outcome
    {cost Γ entry exit invariant outer tail}
    {suffix : certificate_suffix cost Γ entry exit}
    (normal : @suffix_outcome_normalization cost Γ entry exit invariant outer
      tail suffix) :
    @suffix_normalization cost Γ entry exit ((invariant, outer) :: tail)
      ((invariant, outer) :: tail) suffix :=
  {| suffix_normalized_lifo := suffix_outcome_lifo _ normal;
     suffix_normalized_tree :=
       Slice.ExecFocusedOutcome (invariant, outer) tail entry exit exit
         ((invariant, outer) :: tail) (suffix_outcome_tree _ normal)
         (Slice.ExecDone exit ((invariant, outer) :: tail)) |}.

Definition focused_same_stack_classification
    {cost Γ entry exit invariant outer tail}
    (suffix : certificate_suffix cost Γ entry exit) : Type :=
  (@suffix_prefix_normalization cost Γ entry exit invariant outer tail suffix +
   @suffix_close_normalization cost Γ entry exit invariant outer tail
     ((invariant, outer) :: tail) suffix)%type.

Definition outcome_of_same_stack_classification
    {cost Γ entry exit invariant outer tail}
    {suffix : certificate_suffix cost Γ entry exit}
    (classification : @focused_same_stack_classification cost Γ entry exit
      invariant outer tail suffix) :
    @suffix_outcome_normalization cost Γ entry exit invariant outer tail
      suffix :=
  match classification with
  | inl prefix => outcome_normalization_of_prefix_witness prefix
  | inr close => outcome_normalization_of_close close
  end.

Definition classify_suffix_done
    {cost Γ entry invariant outer tail} :
    @focused_same_stack_classification cost Γ entry entry invariant outer tail
      (SuffixDone entry).
Proof.
  left. refine {| suffix_prefix_tree :=
    Slice.FocusedPrefixDone (invariant, outer) tail entry |}.
  reflexivity.
Defined.

Definition prepend_preserving_classification
    {cost Γ fuel entry statement middle exit invariant outer tail}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle} {rest : certificate_suffix cost Γ middle exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate
      ((invariant, outer) :: tail) ((invariant, outer) :: tail))
    (prefix : Payload.chunk entry ((invariant, outer) :: tail) middle
      ((invariant, outer) :: tail))
    (prefix_ok : Payload.preserves (invariant, outer) tail entry middle prefix)
    (classification : @focused_same_stack_classification cost Γ middle exit
      invariant outer tail rest) :
    @focused_same_stack_classification cost Γ entry exit invariant outer tail
      (SuffixCons certificate rest).
Proof.
  destruct classification as [normal|normal].
  - left. refine {| suffix_prefix_tree :=
        Slice.FocusedPrefixChunk (invariant, outer) tail entry middle exit
          prefix prefix_ok (suffix_prefix_tree _ normal) |}.
    exists ((invariant, outer) :: tail). split; [exact certificate_lifo|].
    exact (suffix_prefix_lifo _ normal).
  - right. refine {| suffix_close_state := suffix_close_state _ normal;
      suffix_close_tree :=
        Slice.FocusedPrefix (invariant, outer) tail entry middle
          (suffix_close_state _ normal) prefix prefix_ok
          (suffix_close_tree _ normal);
      suffix_after_close := suffix_after_close _ normal |}.
    exists ((invariant, outer) :: tail). split; [exact certificate_lifo|].
    exact (suffix_close_lifo _ normal).
Defined.

Definition prepend_preserving_outcome
    {cost Γ fuel entry statement middle exit invariant outer tail}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle} {rest : certificate_suffix cost Γ middle exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate
      ((invariant, outer) :: tail) ((invariant, outer) :: tail))
    (prefix : Payload.chunk entry ((invariant, outer) :: tail) middle
      ((invariant, outer) :: tail))
    (prefix_ok : Payload.preserves (invariant, outer) tail entry middle prefix)
    (normal : @suffix_outcome_normalization cost Γ middle exit invariant outer
      tail rest) :
    @suffix_outcome_normalization cost Γ entry exit invariant outer tail
      (SuffixCons certificate rest).
Proof.
  refine {| suffix_outcome_tree :=
      Slice.OutcomePrefix (invariant, outer) tail entry middle exit prefix
        prefix_ok (suffix_outcome_tree _ normal) |}.
  exists ((invariant, outer) :: tail). split; [exact certificate_lifo|].
  exact (suffix_outcome_lifo _ normal).
Defined.

Definition prepend_focused_net_chunk
    {cost Γ fuel entry statement middle exit invariant outer tail stack_out}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle} {rest : certificate_suffix cost Γ middle exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate
      ((invariant, outer) :: tail) ((invariant, outer) :: tail))
    (prefix : Payload.chunk entry ((invariant, outer) :: tail) middle
      ((invariant, outer) :: tail))
    (prefix_ok : Payload.preserves (invariant, outer) tail entry middle prefix)
    (normal : @suffix_focused_net_normalization cost Γ middle exit invariant
      outer tail stack_out rest) :
    @suffix_focused_net_normalization cost Γ entry exit invariant outer tail
      stack_out (SuffixCons certificate rest).
Proof.
  refine {| suffix_focused_net_tree := @FocusNetPrefix (invariant, outer) tail
      stack_out entry middle exit prefix prefix_ok
      (suffix_focused_net_tree _ normal) |}.
  exists ((invariant, outer) :: tail). split; [exact certificate_lifo|].
  exact (suffix_focused_net_lifo _ normal).
Defined.

Definition prepend_focused_net_nested_access
    {cost Γ fuel entry statement opened exit invariant outer tail
      nested nested_outer stack_out}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      opened} {rest : certificate_suffix cost Γ opened exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate
      ((invariant, outer) :: tail)
      ((nested, nested_outer) :: (invariant, outer) :: tail))
    (opening : Payload.chunk entry ((invariant, outer) :: tail) opened
      ((nested, nested_outer) :: (invariant, outer) :: tail))
    (open_ok : Payload.opens (nested, nested_outer)
      ((invariant, outer) :: tail) entry opened opening)
    (normal : @suffix_focused_net_normalization cost Γ opened exit nested
      nested_outer ((invariant, outer) :: tail) stack_out rest) :
    @suffix_focused_net_normalization cost Γ entry exit invariant outer tail
      stack_out (SuffixCons certificate rest).
Proof.
  refine {| suffix_focused_net_tree := @FocusNetNested (invariant, outer) tail
      stack_out (nested, nested_outer) entry opened exit opening open_ok
      (suffix_focused_net_tree _ normal) |}.
  exists ((nested, nested_outer) :: (invariant, outer) :: tail).
  split; [exact certificate_lifo|].
  exact (suffix_focused_net_lifo _ normal).
Defined.

Definition prepend_preserving_split
    {cost Γ fuel entry statement middle exit invariant outer tail stack_out}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle} {rest : certificate_suffix cost Γ middle exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate
      ((invariant, outer) :: tail) ((invariant, outer) :: tail))
    (prefix : Payload.chunk entry ((invariant, outer) :: tail) middle
      ((invariant, outer) :: tail))
    (prefix_ok : Payload.preserves (invariant, outer) tail entry middle prefix)
    (split : @suffix_close_split cost Γ middle exit invariant outer tail
      stack_out rest) :
    @suffix_close_split cost Γ entry exit invariant outer tail stack_out
      (SuffixCons certificate rest).
Proof.
  refine {| split_close_state := split_close_state _ split;
            split_prefix := SuffixCons certificate (split_prefix _ split);
            split_rest := split_rest _ split;
            split_close_tree :=
              Slice.FocusedPrefix (invariant, outer) tail entry middle
                (split_close_state _ split) prefix prefix_ok
                (split_close_tree _ split);
            split_rest_tree := split_rest_tree _ split |}.
  - simpl. apply ExpandsCons. exact (split_recompose _ split).
  - exists ((invariant, outer) :: tail). split; [exact certificate_lifo|].
    exact (split_prefix_lifo _ split).
  - exact (split_rest_lifo _ split).
Defined.

Definition singleton_suffix
    {cost Γ fuel entry statement exit}
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      exit) : certificate_suffix cost Γ entry exit :=
  SuffixCons certificate (SuffixDone exit).

Lemma singleton_suffix_lifo
    {cost Γ fuel entry statement exit}
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      exit) stack_in stack_out :
  suffix_lifo (singleton_suffix certificate) stack_in stack_out <->
  Atomicity.lifo_certificate certificate stack_in stack_out.
Proof.
  simpl. split.
  - intros (stack_middle & Hlifo & ->). exact Hlifo.
  - intros Hlifo. exists stack_out. split; [exact Hlifo|reflexivity].
Qed.

Definition focused_normalization_of_singleton
    {cost Γ fuel entry statement exit invariant outer tail}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      exit}
    (normal : @suffix_focused_normalization cost Γ entry exit invariant outer
      tail (singleton_suffix certificate)) :
    @focused_normalization cost Γ fuel entry statement exit invariant outer
      tail certificate.
Proof.
  refine {| focused_lifo := _;
            focused_first_close := suffix_first_close _ normal;
            focused_tree := suffix_focused_tree _ normal;
            focused_post_close := suffix_post_close _ normal |}.
  apply (proj1 (singleton_suffix_lifo certificate _ _)).
  exact (suffix_focused_lifo _ normal).
Defined.

Definition normalize_suffix_done {cost Γ entry stack} :
    @suffix_normalization cost Γ entry entry stack stack
      (SuffixDone entry).
Proof.
  refine {| suffix_normalized_tree := Slice.ExecDone entry stack |}.
  reflexivity.
Defined.

Definition normalize_net_done {cost Γ entry stack} :
    @suffix_net_normalization cost Γ entry entry stack stack
      (SuffixDone entry).
Proof.
  refine {| suffix_net_tree :=
      @NetOrdinary stack stack entry entry (Slice.ExecDone entry stack) |}.
  reflexivity.
Defined.

Definition prepend_net_chunk
    {cost Γ fuel entry statement middle exit stack stack_out}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle} {rest : certificate_suffix cost Γ middle exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate stack stack)
    (head : Payload.chunk entry stack middle stack)
    (normal : @suffix_net_normalization cost Γ middle exit stack stack_out
      rest) :
    @suffix_net_normalization cost Γ entry exit stack stack_out
      (SuffixCons certificate rest).
Proof.
  refine {| suffix_net_tree := @NetChunk stack middle stack_out entry exit
      head (suffix_net_tree _ normal) |}.
  exists stack. split; [exact certificate_lifo|].
  exact (suffix_net_lifo _ normal).
Defined.

Definition traced_normalize_net_done {cost Γ entry stack} :
    @traced_suffix_net_normalization cost Γ entry entry stack stack
      (SuffixDone entry).
Proof.
  refine {| traced_net_normal := normalize_net_done;
            traced_net_source := TraceDoneNet cost Γ entry stack |}.
Defined.

Definition traced_prepend_net_chunk
    {cost Γ fuel entry statement middle exit stack stack_out}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle} {rest : certificate_suffix cost Γ middle exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate stack stack)
    (head : Payload.chunk entry stack middle stack)
    (Hhead : chunk_certificate cost Γ fuel entry statement middle stack stack
      certificate head)
    (normal : @traced_suffix_net_normalization cost Γ middle exit stack
      stack_out rest) :
    @traced_suffix_net_normalization cost Γ entry exit stack stack_out
      (SuffixCons certificate rest).
Proof.
  refine {| traced_net_normal := prepend_net_chunk certificate_lifo head
      (traced_net_normal _ normal) |}.
  exact (TraceChunk cost Γ fuel entry statement middle exit stack stack_out
    certificate rest head Hhead _ (traced_net_source _ normal)).
Defined.

Definition traced_normalize_focused_net_done
    {cost Γ entry invariant outer tail} :
    @traced_suffix_focused_net_normalization cost Γ entry entry invariant outer
      tail ((invariant, outer) :: tail) (SuffixDone entry).
Proof.
  unshelve eexists.
  - unshelve eexists.
    + reflexivity.
    + exact (@FocusNetOutcome (invariant, outer) tail entry entry
        (Slice.OutcomeStillOpen (invariant, outer) tail entry entry
          (Slice.FocusedPrefixDone (invariant, outer) tail entry))).
  - exact (TraceDoneFocused cost Γ entry (invariant, outer) tail).
Defined.

Definition traced_prepend_focused_net_chunk
    {cost Γ fuel entry statement middle exit invariant outer tail stack_out}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle} {rest : certificate_suffix cost Γ middle exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate
      ((invariant, outer) :: tail) ((invariant, outer) :: tail))
    (head : Payload.chunk entry ((invariant, outer) :: tail) middle
      ((invariant, outer) :: tail))
    (Hhead : chunk_certificate cost Γ fuel entry statement middle
      ((invariant, outer) :: tail) ((invariant, outer) :: tail) certificate head)
    (head_ok : Payload.preserves (invariant, outer) tail entry middle head)
    (normal : @traced_suffix_focused_net_normalization cost Γ middle exit
      invariant outer tail stack_out rest) :
    @traced_suffix_focused_net_normalization cost Γ entry exit invariant outer
      tail stack_out (SuffixCons certificate rest).
Proof.
  refine {| traced_focused_net_normal := prepend_focused_net_chunk
      certificate_lifo head head_ok (traced_focused_net_normal _ normal) |}.
  exact (TraceFocusedPrefix cost Γ fuel entry statement middle exit
    (invariant, outer) tail stack_out certificate rest head Hhead head_ok _
    (traced_focused_net_source _ normal)).
Defined.

Definition net_normalization_of_execution
    {cost Γ entry exit stack_in stack_out}
    {suffix : certificate_suffix cost Γ entry exit}
    (normal : @suffix_normalization cost Γ entry exit stack_in stack_out
      suffix) :
    @suffix_net_normalization cost Γ entry exit stack_in stack_out suffix.
Proof.
  refine {| suffix_net_tree := @NetOrdinary stack_in stack_out entry exit
      (suffix_normalized_tree _ normal) |}.
  exact (suffix_normalized_lifo _ normal).
Defined.

Definition normalize_net_access
    {cost Γ fuel entry statement opened exit focused tail stack_out}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      opened} {rest : certificate_suffix cost Γ opened exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate tail
      (focused :: tail))
    (opening : Payload.chunk entry tail opened (focused :: tail))
    (open_ok : Payload.opens focused tail entry opened opening)
    (normal : @suffix_focused_net_normalization cost Γ opened exit
      (fst focused) (snd focused) tail stack_out rest) :
    @suffix_net_normalization cost Γ entry exit tail stack_out
      (SuffixCons certificate rest).
Proof.
  destruct focused as [invariant outer].
  refine {| suffix_net_tree := @NetAccess tail stack_out (invariant, outer)
      entry opened exit opening open_ok (suffix_focused_net_tree _ normal) |}.
  exists ((invariant, outer) :: tail). split; [exact certificate_lifo|].
  exact (suffix_focused_net_lifo _ normal).
Defined.

Definition normalize_net_close
    {cost Γ fuel entry statement closed exit focused tail stack_out}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      closed} {rest : certificate_suffix cost Γ closed exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate
      (focused :: tail) tail)
    (closing : Payload.chunk entry (focused :: tail) closed tail)
    (close_ok : Payload.closes focused tail entry closed closing)
    (normal : @suffix_net_normalization cost Γ closed exit tail stack_out rest) :
    @suffix_net_normalization cost Γ entry exit (focused :: tail) stack_out
      (SuffixCons certificate rest).
Proof.
  refine {| suffix_net_tree := @NetClose focused tail stack_out entry closed
      exit closing close_ok (suffix_net_tree _ normal) |}.
  exists tail. split; [exact certificate_lifo|].
  exact (suffix_net_lifo _ normal).
Defined.

Definition normalize_focused_net_close
    {cost Γ fuel entry statement closed exit focused tail stack_out}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      closed} {rest : certificate_suffix cost Γ closed exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate
      (focused :: tail) tail)
    (closing : Payload.chunk entry (focused :: tail) closed tail)
    (close_ok : Payload.closes focused tail entry closed closing)
    (normal : @suffix_net_normalization cost Γ closed exit tail stack_out rest) :
    @suffix_focused_net_normalization cost Γ entry exit (fst focused)
      (snd focused) tail stack_out (SuffixCons certificate rest).
Proof.
  destruct focused as [invariant outer].
  refine {| suffix_focused_net_tree := @FocusNetClose (invariant, outer) tail
      stack_out entry closed exit
      (Slice.FocusedClose (invariant, outer) tail entry closed closing close_ok)
      (suffix_net_tree _ normal) |}.
  exists tail. split; [exact certificate_lifo|].
  exact (suffix_net_lifo _ normal).
Defined.

Definition traced_normalize_net_access
    {cost Γ fuel entry statement opened exit focused tail stack_out}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      opened} {rest : certificate_suffix cost Γ opened exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate tail
      (focused :: tail))
    (opening : Payload.chunk entry tail opened (focused :: tail))
    (Hopening : chunk_certificate cost Γ fuel entry statement opened tail
      (focused :: tail) certificate opening)
    (open_ok : Payload.opens focused tail entry opened opening)
    (normal : @traced_suffix_focused_net_normalization cost Γ opened exit
      (fst focused) (snd focused) tail stack_out rest) :
    @traced_suffix_net_normalization cost Γ entry exit tail stack_out
      (SuffixCons certificate rest).
Proof.
  destruct focused as [invariant outer].
  refine {| traced_net_normal := normalize_net_access certificate_lifo opening
      open_ok (traced_focused_net_normal _ normal) |}.
  exact (TraceAccess cost Γ fuel entry statement opened exit
    (invariant, outer) tail stack_out certificate rest opening Hopening open_ok
    _ (traced_focused_net_source _ normal)).
Defined.

Definition traced_prepend_focused_net_nested_access
    {cost Γ fuel entry statement opened exit invariant outer tail
      nested nested_outer stack_out}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      opened} {rest : certificate_suffix cost Γ opened exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate
      ((invariant, outer) :: tail)
      ((nested, nested_outer) :: (invariant, outer) :: tail))
    (opening : Payload.chunk entry ((invariant, outer) :: tail) opened
      ((nested, nested_outer) :: (invariant, outer) :: tail))
    (Hopening : chunk_certificate cost Γ fuel entry statement opened
      ((invariant, outer) :: tail)
      ((nested, nested_outer) :: (invariant, outer) :: tail)
      certificate opening)
    (open_ok : Payload.opens (nested, nested_outer)
      ((invariant, outer) :: tail) entry opened opening)
    (normal : @traced_suffix_focused_net_normalization cost Γ opened exit
      nested nested_outer ((invariant, outer) :: tail) stack_out rest) :
    @traced_suffix_focused_net_normalization cost Γ entry exit invariant outer
      tail stack_out (SuffixCons certificate rest).
Proof.
  refine {| traced_focused_net_normal := prepend_focused_net_nested_access
      certificate_lifo opening open_ok (traced_focused_net_normal _ normal) |}.
  exact (TraceNestedAccess cost Γ fuel entry statement opened exit
    (invariant, outer) tail (nested, nested_outer) stack_out certificate rest
    opening Hopening open_ok _ (traced_focused_net_source _ normal)).
Defined.

Definition traced_normalize_net_close
    {cost Γ fuel entry statement closed exit focused tail stack_out}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      closed} {rest : certificate_suffix cost Γ closed exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate
      (focused :: tail) tail)
    (closing : Payload.chunk entry (focused :: tail) closed tail)
    (Hclosing : chunk_certificate cost Γ fuel entry statement closed
      (focused :: tail) tail certificate closing)
    (close_ok : Payload.closes focused tail entry closed closing)
    (normal : @traced_suffix_net_normalization cost Γ closed exit tail
      stack_out rest) :
    @traced_suffix_net_normalization cost Γ entry exit (focused :: tail)
      stack_out (SuffixCons certificate rest).
Proof.
  refine {| traced_net_normal := normalize_net_close certificate_lifo closing
      close_ok (traced_net_normal _ normal) |}.
  exact (TraceClose cost Γ fuel entry statement closed exit focused tail
    stack_out certificate rest closing Hclosing close_ok _
    (traced_net_source _ normal)).
Defined.

Definition traced_normalize_focused_net_close
    {cost Γ fuel entry statement closed exit focused tail stack_out}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      closed} {rest : certificate_suffix cost Γ closed exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate
      (focused :: tail) tail)
    (closing : Payload.chunk entry (focused :: tail) closed tail)
    (Hclosing : chunk_certificate cost Γ fuel entry statement closed
      (focused :: tail) tail certificate closing)
    (close_ok : Payload.closes focused tail entry closed closing)
    (normal : @traced_suffix_net_normalization cost Γ closed exit tail
      stack_out rest) :
    @traced_suffix_focused_net_normalization cost Γ entry exit (fst focused)
      (snd focused) tail stack_out (SuffixCons certificate rest).
Proof.
  destruct focused as [invariant outer].
  refine {| traced_focused_net_normal := normalize_focused_net_close
      certificate_lifo closing close_ok (traced_net_normal _ normal) |}.
  exact (TraceFocusedClose cost Γ fuel entry statement closed exit
    (invariant, outer) tail stack_out certificate rest closing Hclosing
    close_ok _ (traced_net_source _ normal)).
Defined.

Definition contract_net_expansion
    {cost Γ entry exit stack_in stack_out}
    {flat source : certificate_suffix cost Γ entry exit}
    (expansion : suffix_expands cost Γ entry exit flat source)
    (normal : @suffix_net_normalization cost Γ entry exit stack_in stack_out
      flat) :
    @suffix_net_normalization cost Γ entry exit stack_in stack_out source.
Proof.
  refine {| suffix_net_tree := suffix_net_tree _ normal |}.
  apply (proj1 (suffix_expands_lifo expansion stack_in stack_out)).
  exact (suffix_net_lifo _ normal).
Defined.

Definition contract_focused_net_expansion
    {cost Γ entry exit invariant outer tail stack_out}
    {flat source : certificate_suffix cost Γ entry exit}
    (expansion : suffix_expands cost Γ entry exit flat source)
    (normal : @suffix_focused_net_normalization cost Γ entry exit invariant
      outer tail stack_out flat) :
    @suffix_focused_net_normalization cost Γ entry exit invariant outer tail
      stack_out source.
Proof.
  refine {| suffix_focused_net_tree := suffix_focused_net_tree _ normal |}.
  apply (proj1 (suffix_expands_lifo expansion _ _)).
  exact (suffix_focused_net_lifo _ normal).
Defined.

Definition traced_contract_net_expansion
    {cost Γ entry exit stack_in stack_out}
    {flat source : certificate_suffix cost Γ entry exit}
    (expansion : suffix_expands cost Γ entry exit flat source)
    (normal : @traced_suffix_net_normalization cost Γ entry exit stack_in
      stack_out flat) :
    @traced_suffix_net_normalization cost Γ entry exit stack_in stack_out
      source.
Proof.
  refine {| traced_net_normal := contract_net_expansion expansion
      (traced_net_normal _ normal) |}.
  exact (TraceExpansion cost Γ entry exit None stack_in stack_out flat source _
    expansion (traced_net_source _ normal)).
Defined.

Definition traced_contract_focused_net_expansion
    {cost Γ entry exit invariant outer tail stack_out}
    {flat source : certificate_suffix cost Γ entry exit}
    (expansion : suffix_expands cost Γ entry exit flat source)
    (normal : @traced_suffix_focused_net_normalization cost Γ entry exit
      invariant outer tail stack_out flat) :
    @traced_suffix_focused_net_normalization cost Γ entry exit invariant outer
      tail stack_out source.
Proof.
  refine {| traced_focused_net_normal := contract_focused_net_expansion
      expansion (traced_focused_net_normal _ normal) |}.
  exact (TraceExpansion cost Γ entry exit (Some (invariant, outer)) tail
    stack_out flat source _ expansion (traced_focused_net_source _ normal)).
Defined.

Definition normalize_suffix_chunk
    {cost Γ fuel entry statement middle exit stack}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle} {rest : certificate_suffix cost Γ middle exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate stack stack)
    (head : Payload.chunk entry stack middle stack)
    (normal : @suffix_normalization cost Γ middle exit stack stack rest) :
    @suffix_normalization cost Γ entry exit stack stack
      (SuffixCons certificate rest).
Proof.
  refine {| suffix_normalized_lifo := _;
            suffix_normalized_tree := Slice.ExecChunk entry stack middle exit
              stack head (suffix_normalized_tree _ normal) |}.
  exists stack. split; [exact certificate_lifo|].
  exact (suffix_normalized_lifo _ normal).
Defined.

Definition normalize_suffix_access
    {cost Γ fuel entry statement opened exit invariant outer tail}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      opened} {rest : certificate_suffix cost Γ opened exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate tail
      ((invariant, outer) :: tail))
    (opening : Payload.chunk entry tail opened ((invariant, outer) :: tail))
    (open_ok : Payload.opens (invariant, outer) tail entry opened opening)
    (normal : @suffix_focused_normalization cost Γ opened exit
      invariant outer tail rest) :
    @suffix_normalization cost Γ entry exit tail tail
      (SuffixCons certificate rest).
Proof.
  refine {| suffix_normalized_lifo := _;
            suffix_normalized_tree :=
              Slice.ExecAccess (invariant, outer) tail entry opened
                (suffix_first_close _ normal) exit opening open_ok
                (suffix_focused_tree _ normal)
                (suffix_post_close _ normal) |}.
  exists ((invariant, outer) :: tail). split; [exact certificate_lifo|].
  exact (suffix_focused_lifo _ normal).
Defined.

Definition normalize_suffix_focused_close
    {cost Γ fuel entry statement closed exit invariant outer tail}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      closed} {rest : certificate_suffix cost Γ closed exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate
      ((invariant, outer) :: tail) tail)
    (closing : Payload.chunk entry ((invariant, outer) :: tail) closed tail)
    (close_ok : Payload.closes (invariant, outer) tail entry closed closing)
    (normal : @suffix_normalization cost Γ closed exit tail tail rest) :
    @suffix_focused_normalization cost Γ entry exit
      invariant outer tail (SuffixCons certificate rest).
Proof.
  refine {| suffix_focused_lifo := _;
            suffix_first_close := closed;
            suffix_focused_tree :=
              Slice.FocusedClose (invariant, outer) tail entry closed closing
                close_ok;
            suffix_post_close := suffix_normalized_tree _ normal |}.
  exists tail. split; [exact certificate_lifo|].
  exact (suffix_normalized_lifo _ normal).
Defined.

Definition normalize_suffix_focused_prefix
    {cost Γ fuel entry statement middle exit invariant outer tail}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry statement
      middle} {rest : certificate_suffix cost Γ middle exit}
    (certificate_lifo : Atomicity.lifo_certificate certificate
      ((invariant, outer) :: tail) ((invariant, outer) :: tail))
    (prefix : Payload.chunk entry ((invariant, outer) :: tail) middle
      ((invariant, outer) :: tail))
    (prefix_ok : Payload.preserves (invariant, outer) tail entry middle prefix)
    (normal : @suffix_focused_normalization cost Γ middle exit
      invariant outer tail rest) :
    @suffix_focused_normalization cost Γ entry exit
      invariant outer tail (SuffixCons certificate rest).
Proof.
  refine {| suffix_focused_lifo := _;
            suffix_first_close := suffix_first_close _ normal;
            suffix_focused_tree :=
              Slice.FocusedPrefix (invariant, outer) tail entry middle
                (suffix_first_close _ normal) prefix prefix_ok
                (suffix_focused_tree _ normal);
            suffix_post_close := suffix_post_close _ normal |}.
  exists ((invariant, outer) :: tail). split; [exact certificate_lifo|].
  exact (suffix_focused_lifo _ normal).
Defined.

(** Concrete Raven heads.  These lemmas keep the totality proof free of the
    dependent constructor arithmetic of [analysis_certificate]. *)
Definition normalize_leaf_head
    {cost Γ fuel entry statement middle exit stack}
    (view : Runtime.RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : Atomicity.take_step (cost Γ statement) entry = inr middle)
    {rest : certificate_suffix cost Γ middle exit}
    (normal : @suffix_normalization cost Γ middle exit stack stack rest) :
    @suffix_normalization cost Γ entry exit stack stack
      (SuffixCons (Atomicity.CertLeaf cost Γ fuel entry statement middle view
        step) rest).
Proof.
  unshelve refine (@normalize_suffix_chunk cost Γ (S fuel) entry statement middle exit
    stack (Atomicity.CertLeaf cost Γ fuel entry statement middle view step)
    rest _
    (leaf_piece (stack := stack) view step) normal).
  all: simpl; auto.
Defined.

Definition normalize_unfold_head
    {cost Γ fuel entry statement invariant opened exit tail}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewUnfold invariant)
    (step : Atomicity.open_invariant invariant entry = inr opened)
    {rest : certificate_suffix cost Γ opened exit}
    (normal : @suffix_focused_normalization cost Γ opened exit invariant
      (Atomicity.analysis_open entry) tail rest) :
    @suffix_normalization cost Γ entry exit tail tail
      (SuffixCons (Atomicity.CertUnfold cost Γ fuel entry statement invariant
        opened view step) rest).
Proof.
  unshelve refine (@normalize_suffix_access cost Γ (S fuel) entry statement opened exit
    invariant (Atomicity.analysis_open entry) tail
    (Atomicity.CertUnfold cost Γ fuel entry statement invariant opened view
      step) rest _
    (unfold_piece (stack := tail) view step) I normal).
  all: simpl; auto.
Defined.

Definition normalize_matched_fold_head
    {cost Γ fuel entry statement invariant outer tail exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    (member : invariant ∈ Atomicity.analysis_open entry)
    (fresh : invariant ∉ outer)
    (opened : Atomicity.analysis_open entry = {[invariant]} ∪ outer)
    {rest : certificate_suffix cost Γ
      (Atomicity.fold_invariant invariant entry) exit}
    (normal : @suffix_normalization cost Γ
      (Atomicity.fold_invariant invariant entry) exit tail tail rest) :
    @suffix_focused_normalization cost Γ entry exit invariant outer tail
      (SuffixCons (Atomicity.CertFold cost Γ fuel entry statement invariant
        view) rest).
Proof.
  unshelve refine (@normalize_suffix_focused_close cost Γ (S fuel) entry statement
    (Atomicity.fold_invariant invariant entry) exit invariant outer tail
    (Atomicity.CertFold cost Γ fuel entry statement invariant view) rest _
    (fold_piece (tail := tail) view member fresh opened) I normal).
  all: simpl; auto.
  left. exists outer. repeat split; assumption.
Defined.

Definition split_matched_fold_head
    {cost Γ fuel entry statement invariant outer tail exit stack_out}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    (member : invariant ∈ Atomicity.analysis_open entry)
    (fresh : invariant ∉ outer)
    (opened : Atomicity.analysis_open entry = {[invariant]} ∪ outer)
    {rest : certificate_suffix cost Γ
      (Atomicity.fold_invariant invariant entry) exit}
    (normal : @suffix_normalization cost Γ
      (Atomicity.fold_invariant invariant entry) exit tail stack_out rest) :
    @suffix_close_split cost Γ entry exit invariant outer tail stack_out
      (SuffixCons (Atomicity.CertFold cost Γ fuel entry statement invariant
        view) rest).
Proof.
  unshelve refine {| split_close_state := Atomicity.fold_invariant invariant entry;
            split_prefix :=
              singleton_suffix
                (Atomicity.CertFold cost Γ fuel entry statement invariant view);
            split_rest := rest;
            split_close_tree :=
              Slice.FocusedClose (invariant, outer) tail entry
                (Atomicity.fold_invariant invariant entry)
                (fold_piece (cost := cost) (fuel := fuel) (tail := tail) view
                  member fresh opened) I;
            split_rest_tree := suffix_normalized_tree _ normal |}.
  - apply ExpandsRefl.
  - apply (proj2 (singleton_suffix_lifo _ _ _)).
    left. exists outer. repeat split; assumption.
  - exact (suffix_normalized_lifo _ normal).
  all: try exact I.
Defined.

Definition outcome_matched_fold_reopen
    {cost Γ fuel entry statement invariant outer tail exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    (member : invariant ∈ Atomicity.analysis_open entry)
    (fresh : invariant ∉ outer)
    (opened : Atomicity.analysis_open entry = {[invariant]} ∪ outer)
    {rest : certificate_suffix cost Γ
      (Atomicity.fold_invariant invariant entry) exit}
    (normal : @suffix_reopen_normalization cost Γ
      (Atomicity.fold_invariant invariant entry) exit invariant outer tail rest) :
    @suffix_outcome_normalization cost Γ entry exit invariant outer tail
      (SuffixCons (Atomicity.CertFold cost Γ fuel entry statement invariant
        view) rest).
Proof.
  refine {| suffix_outcome_tree :=
      Slice.OutcomeClosedReopened (invariant, outer) tail entry
        (Atomicity.fold_invariant invariant entry)
        (suffix_reopen_entry _ normal) (suffix_reopened_state _ normal) exit
        (Slice.FocusedClose (invariant, outer) tail entry
          (Atomicity.fold_invariant invariant entry)
          (fold_piece (cost := cost) (fuel := fuel) (tail := tail) view member
            fresh opened) I)
        (suffix_before_reopen _ normal) (suffix_reopen_chunk _ normal)
        (suffix_reopen_ok _ normal) (suffix_after_reopen _ normal) |}.
  exists tail. split.
  - left. exists outer. repeat split; assumption.
  - exact (suffix_reopen_lifo _ normal).
Defined.

Definition reopen_path_matched_fold_head
    {cost Γ fuel entry statement invariant outer base added exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    (member : invariant ∈ Atomicity.analysis_open entry)
    (fresh : invariant ∉ outer)
    (opened : Atomicity.analysis_open entry = {[invariant]} ∪ outer)
    {rest : certificate_suffix cost Γ
      (Atomicity.fold_invariant invariant entry) exit}
    (normal : @suffix_reopen_path_normalization cost Γ
      (Atomicity.fold_invariant invariant entry) exit base
      (added ++ [(invariant, outer)]) rest) :
    @suffix_reopen_path_normalization cost Γ entry exit
      ((invariant, outer) :: base) added
      (SuffixCons (Atomicity.CertFold cost Γ fuel entry statement invariant
        view) rest).
Proof.
  refine {| suffix_reopen_path_tree :=
      matched_close_rebase_reopen_path
        (Slice.FocusedClose (invariant, outer) base entry
          (Atomicity.fold_invariant invariant entry)
          (fold_piece (cost := cost) (fuel := fuel) (tail := base) view member
            fresh opened) I)
        (suffix_reopen_path_tree _ normal) |}.
  exists base. split.
  - left. exists outer. repeat split; assumption.
  - assert (Heq : ((added ++ [(invariant, outer)]) ++ base) =
        added ++ (invariant, outer) :: base).
    { rewrite <- app_assoc. reflexivity. }
    exact (eq_rect _ (fun stack => suffix_lifo rest base stack)
      (suffix_reopen_path_lifo _ normal) _ Heq).
Defined.

Definition normalize_fresh_fold_head
    {cost Γ fuel entry statement invariant exit stack}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    (closed : invariant ∉ Atomicity.analysis_open entry)
    {rest : certificate_suffix cost Γ
      (Atomicity.fold_invariant invariant entry) exit}
    (normal : @suffix_normalization cost Γ
      (Atomicity.fold_invariant invariant entry) exit stack stack rest) :
    @suffix_normalization cost Γ entry exit stack stack
      (SuffixCons (Atomicity.CertFold cost Γ fuel entry statement invariant
        view) rest).
Proof.
  unshelve refine (@normalize_suffix_chunk cost Γ (S fuel) entry statement
    (Atomicity.fold_invariant invariant entry) exit stack
    (Atomicity.CertFold cost Γ fuel entry statement invariant view) rest _
    (fresh_fold_piece (stack := stack) view closed) normal).
  all: simpl; auto.
Defined.

Definition normalize_atomic_head
    {cost Γ fuel entry statement body outer inner exit stack}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewAtomic body)
    (step : Atomicity.take_step Atomicity.AtomicStep entry = inr outer)
    (body_certificate : Atomicity.analysis_certificate cost Γ fuel
      (Atomicity.AnalysisState (Atomicity.analysis_mask outer)
        (Atomicity.analysis_open outer)
        (Atomicity.analysis_step_taken outer) true) body inner)
    (open_equal : Atomicity.analysis_open inner =
      Atomicity.analysis_open outer)
    (body_lifo : Atomicity.lifo_certificate body_certificate stack stack)
    {rest : certificate_suffix cost Γ
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer)) exit}
    (normal : @suffix_normalization cost Γ _ exit stack stack rest) :
    @suffix_normalization cost Γ entry exit stack stack
      (SuffixCons (Atomicity.CertAtomic cost Γ fuel entry statement body outer
        inner view step body_certificate open_equal) rest).
Proof.
  unshelve refine (@normalize_suffix_chunk cost Γ (S fuel) entry statement
    (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
      (Atomicity.analysis_open inner)
      (Atomicity.analysis_step_taken outer || Atomicity.analysis_step_taken inner)
      (Atomicity.analysis_in_atomic outer)) exit stack
    (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
      step body_certificate open_equal) rest _
    (atomic_piece (stack := stack) view step body_certificate open_equal)
    normal).
  all: simpl; auto.
Defined.

Definition normalize_balanced_conditional_head
    {cost Γ fuel entry statement then_statement else_statement
      then_exit else_exit exit stack}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewConditional then_statement else_statement)
    (then_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      then_statement then_exit)
    (else_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      else_statement else_exit)
    (open_equal : Atomicity.analysis_open then_exit =
      Atomicity.analysis_open else_exit)
    (atomic_equal : Atomicity.analysis_in_atomic then_exit =
      Atomicity.analysis_in_atomic else_exit)
    (then_normal : @normalization cost Γ fuel entry then_statement then_exit
      stack stack then_certificate)
    (else_normal : @normalization cost Γ fuel entry else_statement else_exit
      stack stack else_certificate)
    {rest : certificate_suffix cost Γ
      (Atomicity.AnalysisState
        (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
        (Atomicity.analysis_open then_exit)
        (Atomicity.analysis_step_taken then_exit ||
          Atomicity.analysis_step_taken else_exit)
        (Atomicity.analysis_in_atomic then_exit)) exit}
    (rest_normal : @suffix_normalization cost Γ _ exit stack stack rest) :
    @suffix_normalization cost Γ entry exit stack stack
      (SuffixCons
        (Atomicity.CertConditional cost Γ fuel entry statement then_statement
          else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal) rest).
Proof.
  refine {| suffix_normalized_tree :=
      Slice.ExecConditional entry stack then_exit else_exit _ exit stack
        (Payload.RavenConditional Γ fuel cost entry statement then_statement
          else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal)
        (normalized_tree then_certificate then_normal)
        (normalized_tree else_certificate else_normal)
        (suffix_normalized_tree _ rest_normal) |}.
  exists stack. split.
  - split; apply normalized_lifo; assumption.
  - exact (suffix_normalized_lifo _ rest_normal).
Defined.

Definition suffix_closed_branch
    {cost Γ entry exit invariant outer tail}
    {suffix : certificate_suffix cost Γ entry exit}
    (normal : @suffix_focused_normalization cost Γ entry exit invariant outer
      tail suffix) :
    Slice.closed_branch (invariant, outer) tail entry
      (suffix_first_close _ normal) exit tail :=
  Slice.ClosedBranch (invariant, outer) tail entry
    (suffix_first_close _ normal) exit tail
    (suffix_focused_tree _ normal) (suffix_post_close _ normal).

Definition normalize_closing_conditional_head
    {cost Γ fuel entry statement then_statement else_statement
      then_exit else_exit exit invariant outer tail}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewConditional then_statement else_statement)
    (then_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      then_statement then_exit)
    (else_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      else_statement else_exit)
    (open_equal : Atomicity.analysis_open then_exit =
      Atomicity.analysis_open else_exit)
    (atomic_equal : Atomicity.analysis_in_atomic then_exit =
      Atomicity.analysis_in_atomic else_exit)
    (then_normal : @suffix_focused_normalization cost Γ entry then_exit
      invariant outer tail (singleton_suffix then_certificate))
    (else_normal : @suffix_focused_normalization cost Γ entry else_exit
      invariant outer tail (singleton_suffix else_certificate))
    {rest : certificate_suffix cost Γ
      (Atomicity.AnalysisState
        (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
        (Atomicity.analysis_open then_exit)
        (Atomicity.analysis_step_taken then_exit ||
          Atomicity.analysis_step_taken else_exit)
        (Atomicity.analysis_in_atomic then_exit)) exit}
    (rest_normal : @suffix_normalization cost Γ _ exit tail tail rest) :
    @suffix_focused_normalization cost Γ entry exit invariant outer tail
      (SuffixCons
        (Atomicity.CertConditional cost Γ fuel entry statement then_statement
          else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal) rest).
Proof.
  refine {| suffix_first_close := exit;
            suffix_focused_tree :=
              Slice.FocusedConditional (invariant, outer) tail entry
                (suffix_first_close _ then_normal) then_exit
                (suffix_first_close _ else_normal) else_exit _ tail exit
                (Payload.RavenConditional Γ fuel cost entry statement
                  then_statement else_statement then_exit else_exit view
                  then_certificate else_certificate open_equal atomic_equal)
                (suffix_closed_branch then_normal)
                (suffix_closed_branch else_normal)
                (suffix_normalized_tree _ rest_normal);
            suffix_post_close := Slice.ExecDone exit tail |}.
  exists tail. split.
  - split.
    + apply (proj1 (singleton_suffix_lifo then_certificate _ _)).
      exact (suffix_focused_lifo _ then_normal).
    + apply (proj1 (singleton_suffix_lifo else_certificate _ _)).
      exact (suffix_focused_lifo _ else_normal).
  - exact (suffix_normalized_lifo _ rest_normal).
Defined.

Definition normalize_continuing_conditional_head
    {cost Γ fuel entry statement then_statement else_statement
      then_exit else_exit exit invariant outer tail}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewConditional then_statement else_statement)
    (then_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      then_statement then_exit)
    (else_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      else_statement else_exit)
    (open_equal : Atomicity.analysis_open then_exit =
      Atomicity.analysis_open else_exit)
    (atomic_equal : Atomicity.analysis_in_atomic then_exit =
      Atomicity.analysis_in_atomic else_exit)
    (then_normal : @suffix_outcome_normalization cost Γ entry then_exit
      invariant outer tail (singleton_suffix then_certificate))
    (else_normal : @suffix_outcome_normalization cost Γ entry else_exit
      invariant outer tail (singleton_suffix else_certificate))
    {rest : certificate_suffix cost Γ
      (Atomicity.AnalysisState
        (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
        (Atomicity.analysis_open then_exit)
        (Atomicity.analysis_step_taken then_exit ||
          Atomicity.analysis_step_taken else_exit)
        (Atomicity.analysis_in_atomic then_exit)) exit}
    (rest_normal : @suffix_focused_normalization cost Γ _ exit invariant outer
      tail rest) :
    @suffix_focused_normalization cost Γ entry exit invariant outer tail
      (SuffixCons
        (Atomicity.CertConditional cost Γ fuel entry statement then_statement
          else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal) rest).
Proof.
  refine {| suffix_first_close := suffix_first_close _ rest_normal;
            suffix_focused_tree :=
              Slice.FocusedConditionalContinue (invariant, outer) tail entry
                then_exit else_exit _ (suffix_first_close _ rest_normal)
                (Payload.RavenConditional Γ fuel cost entry statement
                  then_statement else_statement then_exit else_exit view
                  then_certificate else_certificate open_equal atomic_equal)
                (suffix_outcome_tree _ then_normal)
                (suffix_outcome_tree _ else_normal)
                (suffix_focused_tree _ rest_normal);
            suffix_post_close := suffix_post_close _ rest_normal |}.
  exists ((invariant, outer) :: tail). split.
  - split.
    + apply (proj1 (singleton_suffix_lifo then_certificate _ _)).
      exact (suffix_outcome_lifo _ then_normal).
    + apply (proj1 (singleton_suffix_lifo else_certificate _ _)).
      exact (suffix_outcome_lifo _ else_normal).
  - exact (suffix_focused_lifo _ rest_normal).
Defined.

Definition normalize_outcome_conditional_head
    {cost Γ fuel entry statement then_statement else_statement
      then_exit else_exit exit invariant outer tail}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewConditional then_statement else_statement)
    (then_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      then_statement then_exit)
    (else_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      else_statement else_exit)
    (open_equal : Atomicity.analysis_open then_exit =
      Atomicity.analysis_open else_exit)
    (atomic_equal : Atomicity.analysis_in_atomic then_exit =
      Atomicity.analysis_in_atomic else_exit)
    (then_normal : @suffix_outcome_normalization cost Γ entry then_exit
      invariant outer tail (singleton_suffix then_certificate))
    (else_normal : @suffix_outcome_normalization cost Γ entry else_exit
      invariant outer tail (singleton_suffix else_certificate))
    {rest : certificate_suffix cost Γ
      (Atomicity.AnalysisState
        (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
        (Atomicity.analysis_open then_exit)
        (Atomicity.analysis_step_taken then_exit ||
          Atomicity.analysis_step_taken else_exit)
        (Atomicity.analysis_in_atomic then_exit)) exit}
    (rest_normal : @suffix_outcome_normalization cost Γ _ exit invariant outer
      tail rest) :
    @suffix_outcome_normalization cost Γ entry exit invariant outer tail
      (SuffixCons
        (Atomicity.CertConditional cost Γ fuel entry statement then_statement
          else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal) rest).
Proof.
  refine {| suffix_outcome_tree :=
      Slice.OutcomeConditional (invariant, outer) tail entry then_exit
        else_exit _ exit
        (Payload.RavenConditional Γ fuel cost entry statement then_statement
          else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal)
        (suffix_outcome_tree _ then_normal)
        (suffix_outcome_tree _ else_normal)
        (suffix_outcome_tree _ rest_normal) |}.
  exists ((invariant, outer) :: tail). split.
  - split.
    + apply (proj1 (singleton_suffix_lifo then_certificate _ _)).
      exact (suffix_outcome_lifo _ then_normal).
    + apply (proj1 (singleton_suffix_lifo else_certificate _ _)).
      exact (suffix_outcome_lifo _ else_normal).
  - exact (suffix_outcome_lifo _ rest_normal).
Defined.

(** Conditional arms use [focused_normalization] independently.  Thus their
    first-close states and post-close executions need not agree. *)
Definition focused_branch {cost Γ fuel entry statement exit invariant outer tail}
    {certificate : Atomicity.analysis_certificate cost Γ fuel entry
      statement exit}
    (normal : focused_normalization certificate) :
    Slice.closed_branch (invariant, outer) tail entry
      (focused_first_close certificate normal) exit tail :=
  Slice.ClosedBranch (invariant, outer) tail entry
    (focused_first_close certificate normal) exit tail
    (focused_tree certificate normal) (focused_post_close certificate normal).

Definition focused_conditional_normalization
    {cost Γ fuel entry statement then_statement else_statement
      then_exit else_exit invariant outer tail}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewConditional then_statement else_statement)
    (then_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      then_statement then_exit)
    (else_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      else_statement else_exit)
    (open_equal : Atomicity.analysis_open then_exit =
      Atomicity.analysis_open else_exit)
    (atomic_equal : Atomicity.analysis_in_atomic then_exit =
      Atomicity.analysis_in_atomic else_exit)
    (then_normal : @focused_normalization cost Γ fuel entry then_statement
      then_exit invariant outer tail then_certificate)
    (else_normal : @focused_normalization cost Γ fuel entry else_statement
      else_exit invariant outer tail else_certificate) :
    @focused_normalization cost Γ (S fuel) entry statement
      (Atomicity.AnalysisState
        (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
        (Atomicity.analysis_open then_exit)
        (Atomicity.analysis_step_taken then_exit ||
          Atomicity.analysis_step_taken else_exit)
        (Atomicity.analysis_in_atomic then_exit)) invariant outer tail
      (Atomicity.CertConditional cost Γ fuel entry statement then_statement
        else_statement then_exit else_exit view then_certificate
        else_certificate open_equal atomic_equal).
Proof.
  refine {| focused_first_close :=
       Atomicity.AnalysisState
         (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
         (Atomicity.analysis_open then_exit)
         (Atomicity.analysis_step_taken then_exit ||
           Atomicity.analysis_step_taken else_exit)
         (Atomicity.analysis_in_atomic then_exit);
     focused_tree :=
       Slice.FocusedConditional (invariant, outer) tail entry
         (focused_first_close then_certificate then_normal) then_exit
         (focused_first_close else_certificate else_normal) else_exit _ tail _
         (Payload.RavenConditional Γ fuel cost entry statement then_statement
           else_statement then_exit else_exit view then_certificate
           else_certificate open_equal atomic_equal)
         (focused_branch then_normal) (focused_branch else_normal)
         (Slice.ExecDone _ tail);
     focused_post_close := Slice.ExecDone _ tail |}.
  simpl. split.
  - exact (focused_lifo then_certificate then_normal).
  - exact (focused_lifo else_certificate else_normal).
Defined.

(** The three zipper-level totality statements form the actual acceptance
    criterion.  Their proofs are mutual: empty-stack execution delegates an
    unfold body to focused closing; a nonempty same-stack suffix is classified
    as an outcome; and closing returns its post-close suffix to one of the
    balanced cases. *)
Definition has_suffix_normalization
    {cost Γ entry exit stack_in stack_out}
    (suffix : certificate_suffix cost Γ entry exit) : Prop :=
  exists _ : @suffix_normalization cost Γ entry exit stack_in stack_out suffix,
    True.

Definition has_suffix_outcome_normalization
    {cost Γ entry exit invariant outer tail}
    (suffix : certificate_suffix cost Γ entry exit) : Prop :=
  exists _ : @suffix_outcome_normalization cost Γ entry exit invariant outer
    tail suffix, True.

Definition has_suffix_focused_normalization
    {cost Γ entry exit invariant outer tail}
    (suffix : certificate_suffix cost Γ entry exit) : Prop :=
  exists _ : @suffix_focused_normalization cost Γ entry exit invariant outer
    tail suffix, True.

Definition has_suffix_close_normalization
    {cost Γ entry exit invariant outer tail stack_out}
    (suffix : certificate_suffix cost Γ entry exit) : Prop :=
  exists _ : @suffix_close_normalization cost Γ entry exit invariant outer tail
    stack_out suffix, True.

Definition has_suffix_close_split
    {cost Γ entry exit invariant outer tail stack_out}
    (suffix : certificate_suffix cost Γ entry exit) : Prop :=
  exists _ : @suffix_close_split cost Γ entry exit invariant outer tail
    stack_out suffix, True.

Definition has_suffix_reopen_normalization
    {cost Γ entry exit invariant outer tail}
    (suffix : certificate_suffix cost Γ entry exit) : Prop :=
  exists _ : @suffix_reopen_normalization cost Γ entry exit invariant outer
    tail suffix, True.

Definition has_suffix_reopen_path_normalization
    {cost Γ entry exit base added}
    (suffix : certificate_suffix cost Γ entry exit) : Prop :=
  exists _ : @suffix_reopen_path_normalization cost Γ entry exit base added
    suffix, True.

Definition has_suffix_net_normalization
    {cost Γ entry exit stack_in stack_out}
    (suffix : certificate_suffix cost Γ entry exit) : Prop :=
  exists _ : @suffix_net_normalization cost Γ entry exit stack_in stack_out
    suffix, True.

Definition has_suffix_focused_net_normalization
    {cost Γ entry exit invariant outer tail stack_out}
    (suffix : certificate_suffix cost Γ entry exit) : Prop :=
  exists _ : @suffix_focused_net_normalization cost Γ entry exit invariant
    outer tail stack_out suffix, True.

Definition has_traced_suffix_net_normalization
    {cost Γ entry exit stack_in stack_out}
    (suffix : certificate_suffix cost Γ entry exit) : Prop :=
  exists _ : @traced_suffix_net_normalization cost Γ entry exit stack_in
    stack_out suffix, True.

Definition has_traced_suffix_focused_net_normalization
    {cost Γ entry exit invariant outer tail stack_out}
    (suffix : certificate_suffix cost Γ entry exit) : Prop :=
  exists _ : @traced_suffix_focused_net_normalization cost Γ entry exit
    invariant outer tail stack_out suffix, True.

Definition stack_suffix (small big : list Atomicity.access_marker) : Prop :=
  exists prefix, big = prefix ++ small.

Lemma stack_suffix_refl stack : stack_suffix stack stack.
Proof. exists []. reflexivity. Qed.

Lemma stack_suffix_tail focused tail : stack_suffix tail (focused :: tail).
Proof. exists [focused]. reflexivity. Qed.

Definition empty_suffix_normalization_property : Prop :=
  forall cost Γ entry exit (suffix : certificate_suffix cost Γ entry exit),
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry) [] ->
    suffix_lifo suffix [] [] ->
    @has_suffix_normalization cost Γ entry exit [] [] suffix.

Definition outcome_suffix_normalization_property : Prop :=
  forall cost Γ entry exit (suffix : certificate_suffix cost Γ entry exit)
    invariant outer tail,
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry)
      ((invariant, outer) :: tail) ->
    suffix_lifo suffix ((invariant, outer) :: tail)
      ((invariant, outer) :: tail) ->
    @has_suffix_outcome_normalization cost Γ entry exit invariant outer tail
      suffix.

Definition balanced_suffix_normalization_property : Prop :=
  forall cost Γ entry exit (suffix : certificate_suffix cost Γ entry exit)
    stack,
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry) stack ->
    suffix_lifo suffix stack stack ->
    @has_suffix_normalization cost Γ entry exit stack stack suffix.

Definition focused_suffix_decomposition_property : Prop :=
  forall cost Γ entry exit (suffix : certificate_suffix cost Γ entry exit)
    invariant outer tail,
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry)
      ((invariant, outer) :: tail) ->
    suffix_lifo suffix ((invariant, outer) :: tail) tail ->
    @has_suffix_focused_normalization cost Γ entry exit invariant outer tail
      suffix.

Record suffix_total_normalization
    {cost Γ entry exit} (suffix : certificate_suffix cost Γ entry exit) : Prop := {
  total_empty : Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry) [] ->
    suffix_lifo suffix [] [] ->
    @has_suffix_normalization cost Γ entry exit [] [] suffix;
  total_outcome : forall invariant outer tail,
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry)
      ((invariant, outer) :: tail) ->
    suffix_lifo suffix ((invariant, outer) :: tail)
      ((invariant, outer) :: tail) ->
    @has_suffix_outcome_normalization cost Γ entry exit invariant outer tail
      suffix;
  total_reopen_path : forall added base,
    added <> [] ->
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry) base ->
    suffix_lifo suffix base (added ++ base) ->
    @has_suffix_reopen_path_normalization cost Γ entry exit base added suffix;
  total_reopen : forall invariant outer tail,
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry) tail ->
    suffix_lifo suffix tail ((invariant, outer) :: tail) ->
    @has_suffix_reopen_normalization cost Γ entry exit invariant outer tail
      suffix;
  total_close : forall invariant outer tail stack_out,
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry)
      ((invariant, outer) :: tail) ->
    stack_suffix stack_out tail ->
    suffix_lifo suffix ((invariant, outer) :: tail) stack_out ->
    @has_suffix_close_split cost Γ entry exit invariant outer tail
      stack_out suffix;
}.

(** Stable totality interface for arbitrary LIFO stack effects.  The two
    fields are intentionally mutual: an unfold moves from ordinary mode into
    focused mode, while the matching fold returns to ordinary mode. *)
Record suffix_net_totality
    {cost Γ entry exit} (suffix : certificate_suffix cost Γ entry exit) : Prop := {
  total_net : forall stack_in stack_out,
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry) stack_in ->
    suffix_lifo suffix stack_in stack_out ->
    @has_suffix_net_normalization cost Γ entry exit stack_in stack_out suffix;
  total_focused_net : forall invariant outer tail stack_out,
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry)
      ((invariant, outer) :: tail) ->
    suffix_lifo suffix ((invariant, outer) :: tail) stack_out ->
    @has_suffix_focused_net_normalization cost Γ entry exit invariant outer
      tail stack_out suffix;
}.

Record traced_suffix_net_totality
    {cost Γ entry exit} (suffix : certificate_suffix cost Γ entry exit) : Prop := {
  traced_total_net : forall stack_in stack_out,
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry) stack_in ->
    suffix_lifo suffix stack_in stack_out ->
    @has_traced_suffix_net_normalization cost Γ entry exit stack_in stack_out
      suffix;
  traced_total_focused_net : forall invariant outer tail stack_out,
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry)
      ((invariant, outer) :: tail) ->
    suffix_lifo suffix ((invariant, outer) :: tail) stack_out ->
    @has_traced_suffix_focused_net_normalization cost Γ entry exit invariant
      outer tail stack_out suffix;
}.

Definition total_suffix_normalization_property : Prop :=
  forall cost Γ entry exit (suffix : certificate_suffix cost Γ entry exit),
    suffix_total_normalization suffix.

Lemma total_normalizes_stack_suffix
    {cost Γ entry exit} (suffix : certificate_suffix cost Γ entry exit)
    (total : suffix_total_normalization suffix)
    (stack_in stack_out : list Atomicity.access_marker)
    (Hwf : Atomicity.state_wf entry)
    (Hstack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open entry) stack_in)
    :
  stack_suffix stack_out stack_in ->
  suffix_lifo suffix stack_in stack_out ->
  @has_suffix_normalization cost Γ entry exit stack_in stack_out suffix.
Proof.
  intros (prefix & Hsuffix) Hlifo.
  destruct stack_in as [|[invariant outer] tail].
  - destruct prefix; simpl in Hsuffix; [|discriminate].
    subst stack_out. exact (total_empty suffix total Hwf Hstack Hlifo).
  - destruct prefix as [|focused prefix].
    + simpl in Hsuffix. subst stack_out.
      destruct (total_outcome suffix total invariant outer tail Hwf Hstack Hlifo)
        as [normal _].
      exists (normalize_suffix_outcome normal). exact I.
    + simpl in Hsuffix. inversion Hsuffix; subst focused tail.
      destruct (total_close suffix total invariant outer
        (prefix ++ stack_out) stack_out Hwf Hstack)
        as [split _].
      { exists prefix. reflexivity. }
      { exact Hlifo. }
      exists (normalize_suffix_close_split split). exact I.
Qed.

Definition total_suffix_done
    {cost Γ entry} :
    @suffix_total_normalization cost Γ entry entry (SuffixDone entry).
Proof.
  constructor.
  - intros _ _ _. exists normalize_suffix_done. exact I.
  - intros invariant outer tail _ _ Hlifo.
    unshelve eexists.
    + apply outcome_normalization_of_prefix_witness.
      refine {| suffix_prefix_tree :=
        Slice.FocusedPrefixDone (invariant, outer) tail entry |}.
      exact Hlifo.
    + exact I.
  - intros added base Hnonempty _ _ Hlifo. simpl in Hlifo.
    exfalso.
    pose proof (f_equal (@length Atomicity.access_marker) Hlifo) as Hlength.
    rewrite app_length in Hlength. destruct added; [contradiction|simpl in *; lia].
  - intros invariant outer tail _ _ Hlifo. simpl in Hlifo.
    exfalso.
    pose proof (f_equal (@length Atomicity.access_marker) Hlifo) as Hlength.
    simpl in Hlength. lia.
  - intros invariant outer tail stack_out _ _ Hsuffix Hlifo. simpl in Hlifo.
    exfalso.
    destruct Hsuffix as [prefix Hsuffix].
    pose proof (f_equal (@length Atomicity.access_marker) Hlifo) as Hequal.
    pose proof (f_equal (@length Atomicity.access_marker) Hsuffix) as Hsuffix_len.
    simpl in Hequal, Hsuffix_len. rewrite app_length in Hsuffix_len. lia.
Defined.

Definition net_total_suffix_done
    {cost Γ entry} :
    @suffix_net_totality cost Γ entry entry (SuffixDone entry).
Proof.
  constructor.
  - intros stack_in stack_out _ _ Hlifo. simpl in Hlifo. subst stack_out.
    exists normalize_net_done. exact I.
  - intros invariant outer tail stack_out _ _ Hlifo.
    simpl in Hlifo. subst stack_out.
    unshelve eexists.
    + refine {| suffix_focused_net_tree := @FocusNetOutcome
          (invariant, outer) tail entry entry
          (Slice.OutcomeStillOpen (invariant, outer) tail entry entry
            (Slice.FocusedPrefixDone (invariant, outer) tail entry)) |}.
      reflexivity.
    + exact I.
Defined.

Definition traced_net_total_suffix_done
    {cost Γ entry} :
    @traced_suffix_net_totality cost Γ entry entry (SuffixDone entry).
Proof.
  constructor.
  - intros stack_in stack_out _ _ Hlifo. simpl in Hlifo. subst stack_out.
    exists traced_normalize_net_done. exact I.
  - intros invariant outer tail stack_out _ _ Hlifo.
    simpl in Hlifo. subst stack_out.
    exists traced_normalize_focused_net_done. exact I.
Defined.

Definition total_leaf_head
    {cost Γ fuel entry statement middle exit}
    (view : Runtime.RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : Atomicity.take_step (cost Γ statement) entry = inr middle)
    {rest : certificate_suffix cost Γ middle exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : suffix_total_normalization rest) :
    suffix_total_normalization
      (SuffixCons (Atomicity.CertLeaf cost Γ fuel entry statement middle view
        step) rest).
Proof.
  constructor.
  - intros _ Hstack (stack_middle & Hhead & Hrest). simpl in Hhead.
    pose proof Hhead as Hhead_lifo.
    subst stack_middle.
    assert (Hmiddle_wf : Atomicity.state_wf middle).
    { exact (Atomicity.certificate_preserves_wf cost entry statement middle
        entry_wf (Atomicity.CertLeaf cost Γ fuel entry statement middle view
          step)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open middle) []).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertLeaf cost Γ fuel entry statement middle view step)
        [] [] entry_wf Hhead_lifo Hstack). }
    destruct (total_empty rest rest_total Hmiddle_wf Hmiddle_stack Hrest)
      as [normal _].
    exists (normalize_leaf_head view step normal). exact I.
  - intros invariant outer tail _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo. subst stack_middle.
    assert (Hmiddle_wf : Atomicity.state_wf middle).
    { exact (Atomicity.certificate_preserves_wf cost entry statement middle
        entry_wf (Atomicity.CertLeaf cost Γ fuel entry statement middle view
          step)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open middle) ((invariant, outer) :: tail)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertLeaf cost Γ fuel entry statement middle view step)
        _ _ entry_wf Hhead_lifo Hstack). }
    destruct (total_outcome rest rest_total invariant outer tail Hmiddle_wf
      Hmiddle_stack Hrest)
      as [normal _].
    exists (@prepend_preserving_outcome cost Γ (S fuel) entry statement middle
      exit invariant outer tail
      (Atomicity.CertLeaf cost Γ fuel entry statement middle view step) rest
      eq_refl
      (leaf_piece (fuel := fuel) (stack := (invariant, outer) :: tail)
        view step) I normal).
    exact I.
  - intros added base Hnonempty _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo. subst stack_middle.
    assert (Hmiddle_wf : Atomicity.state_wf middle).
    { exact (Atomicity.certificate_preserves_wf cost entry statement middle
        entry_wf (Atomicity.CertLeaf cost Γ fuel entry statement middle view
          step)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open middle) base).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertLeaf cost Γ fuel entry statement middle view step)
        _ _ entry_wf Hhead_lifo Hstack). }
    destruct (total_reopen_path rest rest_total added base Hnonempty
      Hmiddle_wf Hmiddle_stack Hrest)
      as [normal _].
    exists (@prepend_reopen_path_normalization cost Γ (S fuel) entry statement
      middle exit base added
      (Atomicity.CertLeaf cost Γ fuel entry statement middle view step) rest
      eq_refl (leaf_piece (cost := cost) (fuel := fuel) (stack := base) view
        step) normal).
    exact I.
  - intros invariant outer tail _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo. subst stack_middle.
    assert (Hmiddle_wf : Atomicity.state_wf middle).
    { exact (Atomicity.certificate_preserves_wf cost entry statement middle
        entry_wf (Atomicity.CertLeaf cost Γ fuel entry statement middle view
          step)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open middle) tail).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertLeaf cost Γ fuel entry statement middle view step)
        _ _ entry_wf Hhead_lifo Hstack). }
    destruct (total_reopen rest rest_total invariant outer tail Hmiddle_wf
      Hmiddle_stack Hrest)
      as [normal _].
    exists (@prepend_reopen_execution cost Γ (S fuel) entry statement middle
      exit invariant outer tail
      (Atomicity.CertLeaf cost Γ fuel entry statement middle view step) rest
      eq_refl
      (leaf_piece (fuel := fuel) (stack := tail) view step) normal).
    exact I.
  - intros invariant outer tail stack_out _ Hstack Hsuffix
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo. subst stack_middle.
    assert (Hmiddle_wf : Atomicity.state_wf middle).
    { exact (Atomicity.certificate_preserves_wf cost entry statement middle
        entry_wf (Atomicity.CertLeaf cost Γ fuel entry statement middle view
          step)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open middle) ((invariant, outer) :: tail)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertLeaf cost Γ fuel entry statement middle view step)
        _ _ entry_wf Hhead_lifo Hstack). }
    destruct (total_close rest rest_total invariant outer tail stack_out
      Hmiddle_wf Hmiddle_stack Hsuffix Hrest)
      as [normal _].
    exists (@prepend_preserving_split cost Γ (S fuel) entry statement middle
      exit invariant outer tail stack_out
      (Atomicity.CertLeaf cost Γ fuel entry statement middle view step) rest
      eq_refl
      (leaf_piece (fuel := fuel)
        (stack := (invariant, outer) :: tail) view step) I normal).
    exact I.
Qed.

Definition net_total_leaf_head
    {cost Γ fuel entry statement middle exit}
    (view : Runtime.RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : Atomicity.take_step (cost Γ statement) entry = inr middle)
    {rest : certificate_suffix cost Γ middle exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : suffix_net_totality rest) :
    suffix_net_totality
      (SuffixCons (Atomicity.CertLeaf cost Γ fuel entry statement middle view
        step) rest).
Proof.
  constructor.
  - intros stack_in stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo. subst stack_middle.
    assert (Hmiddle_wf : Atomicity.state_wf middle).
    { exact (Atomicity.certificate_preserves_wf cost entry statement middle
        entry_wf (Atomicity.CertLeaf cost Γ fuel entry statement middle view
          step)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open middle) stack_in).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertLeaf cost Γ fuel entry statement middle view step)
        _ _ entry_wf Hhead_lifo Hstack). }
    destruct (total_net rest rest_total stack_in stack_out Hmiddle_wf
      Hmiddle_stack Hrest) as [normal _].
    exists (@prepend_net_chunk cost Γ (S fuel) entry statement middle exit
      stack_in stack_out
      (Atomicity.CertLeaf cost Γ fuel entry statement middle view step) rest
      eq_refl (leaf_piece (fuel := fuel) (stack := stack_in) view step)
      normal). exact I.
  - intros invariant outer tail stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo. subst stack_middle.
    assert (Hmiddle_wf : Atomicity.state_wf middle).
    { exact (Atomicity.certificate_preserves_wf cost entry statement middle
        entry_wf (Atomicity.CertLeaf cost Γ fuel entry statement middle view
          step)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open middle) ((invariant, outer) :: tail)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertLeaf cost Γ fuel entry statement middle view step)
        _ _ entry_wf Hhead_lifo Hstack). }
    destruct (total_focused_net rest rest_total invariant outer tail stack_out
      Hmiddle_wf Hmiddle_stack Hrest) as [normal _].
    exists (@prepend_focused_net_chunk cost Γ (S fuel) entry statement middle
      exit invariant outer tail stack_out
      (Atomicity.CertLeaf cost Γ fuel entry statement middle view step) rest
      eq_refl
      (leaf_piece (fuel := fuel) (stack := (invariant, outer) :: tail)
        view step) I normal). exact I.
Qed.

Definition traced_net_total_leaf_head
    {cost Γ fuel entry statement middle exit}
    (view : Runtime.RegionSyntax.view statement = TypedAnalysisView.ViewLeaf)
    (step : Atomicity.take_step (cost Γ statement) entry = inr middle)
    {rest : certificate_suffix cost Γ middle exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : traced_suffix_net_totality rest) :
    traced_suffix_net_totality
      (SuffixCons (Atomicity.CertLeaf cost Γ fuel entry statement middle view
        step) rest).
Proof.
  constructor.
  - intros stack_in stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo. subst stack_middle.
    assert (Hmiddle_wf : Atomicity.state_wf middle).
    { exact (Atomicity.certificate_preserves_wf cost entry statement middle
        entry_wf (Atomicity.CertLeaf cost Γ fuel entry statement middle view
          step)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open middle) stack_in).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertLeaf cost Γ fuel entry statement middle view step)
        _ _ entry_wf Hhead_lifo Hstack). }
    destruct (traced_total_net rest rest_total stack_in stack_out Hmiddle_wf
      Hmiddle_stack Hrest) as [normal _].
    exists (@traced_prepend_net_chunk cost Γ (S fuel) entry statement middle
      exit stack_in stack_out
      (Atomicity.CertLeaf cost Γ fuel entry statement middle view step) rest
      eq_refl (leaf_piece (fuel := fuel) (stack := stack_in) view step)
      (ChunkCertificateLeaf cost Γ fuel entry statement middle stack_in view
        step) normal). exact I.
  - intros invariant outer tail stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo. subst stack_middle.
    assert (Hmiddle_wf : Atomicity.state_wf middle).
    { exact (Atomicity.certificate_preserves_wf cost entry statement middle
        entry_wf (Atomicity.CertLeaf cost Γ fuel entry statement middle view
          step)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open middle) ((invariant, outer) :: tail)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertLeaf cost Γ fuel entry statement middle view step)
        _ _ entry_wf Hhead_lifo Hstack). }
    destruct (traced_total_focused_net rest rest_total invariant outer tail
      stack_out Hmiddle_wf Hmiddle_stack Hrest) as [normal _].
    exists (@traced_prepend_focused_net_chunk cost Γ (S fuel) entry statement
      middle exit invariant outer tail stack_out
      (Atomicity.CertLeaf cost Γ fuel entry statement middle view step) rest
      eq_refl
      (leaf_piece (fuel := fuel) (stack := (invariant, outer) :: tail)
        view step)
      (ChunkCertificateLeaf cost Γ fuel entry statement middle
        ((invariant, outer) :: tail) view step) I normal). exact I.
Qed.

Definition net_total_unfold_head
    {cost Γ fuel entry statement invariant opened exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewUnfold invariant)
    (step : Atomicity.open_invariant invariant entry = inr opened)
    {rest : certificate_suffix cost Γ opened exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : suffix_net_totality rest) :
    suffix_net_totality
      (SuffixCons (Atomicity.CertUnfold cost Γ fuel entry statement invariant
        opened view step) rest).
Proof.
  constructor.
  - intros stack_in stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo. subst stack_middle.
    assert (Hopened_wf : Atomicity.state_wf opened).
    { exact (Atomicity.certificate_preserves_wf cost entry statement opened
        entry_wf (Atomicity.CertUnfold cost Γ fuel entry statement invariant
          opened view step)). }
    assert (Hopened_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open opened)
      ((invariant, Atomicity.analysis_open entry) :: stack_in)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertUnfold cost Γ fuel entry statement invariant opened
          view step) _ _ entry_wf Hhead_lifo Hstack). }
    destruct (total_focused_net rest rest_total invariant
      (Atomicity.analysis_open entry) stack_in stack_out Hopened_wf
      Hopened_stack Hrest) as [normal _].
    exists (@normalize_net_access cost Γ (S fuel) entry statement opened exit
      (invariant, Atomicity.analysis_open entry) stack_in stack_out
      (Atomicity.CertUnfold cost Γ fuel entry statement invariant opened view
        step) rest Hhead_lifo
      (unfold_piece (cost := cost) (fuel := fuel) (stack := stack_in)
        view step) I normal). exact I.
  - intros focused outer tail stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo. subst stack_middle.
    assert (Hopened_wf : Atomicity.state_wf opened).
    { exact (Atomicity.certificate_preserves_wf cost entry statement opened
        entry_wf (Atomicity.CertUnfold cost Γ fuel entry statement invariant
          opened view step)). }
    assert (Hopened_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open opened)
      ((invariant, Atomicity.analysis_open entry) ::
        (focused, outer) :: tail)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertUnfold cost Γ fuel entry statement invariant opened
          view step) _ _ entry_wf Hhead_lifo Hstack). }
    destruct (total_focused_net rest rest_total invariant
      (Atomicity.analysis_open entry) ((focused, outer) :: tail) stack_out
      Hopened_wf Hopened_stack Hrest) as [normal _].
    exists (@prepend_focused_net_nested_access cost Γ (S fuel) entry statement
      opened exit focused outer tail invariant
      (Atomicity.analysis_open entry) stack_out
      (Atomicity.CertUnfold cost Γ fuel entry statement invariant opened view
        step) rest Hhead_lifo
      (unfold_piece (cost := cost) (fuel := fuel)
        (stack := (focused, outer) :: tail) view step) I normal).
    exact I.
Qed.

Definition traced_net_total_unfold_head
    {cost Γ fuel entry statement invariant opened exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewUnfold invariant)
    (step : Atomicity.open_invariant invariant entry = inr opened)
    {rest : certificate_suffix cost Γ opened exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : traced_suffix_net_totality rest) :
    traced_suffix_net_totality
      (SuffixCons (Atomicity.CertUnfold cost Γ fuel entry statement invariant
        opened view step) rest).
Proof.
  constructor.
  - intros stack_in stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo. subst stack_middle.
    assert (Hopened_wf : Atomicity.state_wf opened).
    { exact (Atomicity.certificate_preserves_wf cost entry statement opened
        entry_wf (Atomicity.CertUnfold cost Γ fuel entry statement invariant
          opened view step)). }
    assert (Hopened_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open opened)
      ((invariant, Atomicity.analysis_open entry) :: stack_in)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertUnfold cost Γ fuel entry statement invariant opened
          view step) _ _ entry_wf Hhead_lifo Hstack). }
    destruct (traced_total_focused_net rest rest_total invariant
      (Atomicity.analysis_open entry) stack_in stack_out Hopened_wf
      Hopened_stack Hrest) as [normal _].
    exists (@traced_normalize_net_access cost Γ (S fuel) entry statement opened
      exit (invariant, Atomicity.analysis_open entry) stack_in stack_out
      (Atomicity.CertUnfold cost Γ fuel entry statement invariant opened view
        step) rest Hhead_lifo
      (unfold_piece (cost := cost) (fuel := fuel) (stack := stack_in)
        view step)
      (ChunkCertificateUnfold cost Γ fuel entry statement invariant opened
        stack_in view step) I normal). exact I.
  - intros focused outer tail stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo. subst stack_middle.
    assert (Hopened_wf : Atomicity.state_wf opened).
    { exact (Atomicity.certificate_preserves_wf cost entry statement opened
        entry_wf (Atomicity.CertUnfold cost Γ fuel entry statement invariant
          opened view step)). }
    assert (Hopened_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open opened)
      ((invariant, Atomicity.analysis_open entry) ::
        (focused, outer) :: tail)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertUnfold cost Γ fuel entry statement invariant opened
          view step) _ _ entry_wf Hhead_lifo Hstack). }
    destruct (traced_total_focused_net rest rest_total invariant
      (Atomicity.analysis_open entry) ((focused, outer) :: tail) stack_out
      Hopened_wf Hopened_stack Hrest) as [normal _].
    exists (@traced_prepend_focused_net_nested_access cost Γ (S fuel) entry
      statement opened exit focused outer tail invariant
      (Atomicity.analysis_open entry) stack_out
      (Atomicity.CertUnfold cost Γ fuel entry statement invariant opened view
        step) rest Hhead_lifo
      (unfold_piece (cost := cost) (fuel := fuel)
        (stack := (focused, outer) :: tail) view step)
      (ChunkCertificateUnfold cost Γ fuel entry statement invariant opened
        ((focused, outer) :: tail) view step) I normal). exact I.
Qed.

Definition total_matched_fold_head
    {cost Γ fuel entry statement invariant exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    (member : invariant ∈ Atomicity.analysis_open entry)
    {rest : certificate_suffix cost Γ
      (Atomicity.fold_invariant invariant entry) exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : suffix_total_normalization rest) :
    suffix_total_normalization
      (SuffixCons (Atomicity.CertFold cost Γ fuel entry statement invariant
        view) rest).
Proof.
  constructor.
  - intros _ _ (stack_middle & Hhead & Hrest). simpl in Hhead.
    pose proof Hhead as Hhead_lifo.
    destruct Hhead as [(outer & Hstack & _)|[_ Hclosed]].
    + discriminate Hstack.
    + exfalso. exact (Hclosed member).
  - intros focused outer tail _ Hstack_in
      (stack_middle & Hhead & Hrest).
    simpl in Hhead.
    pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as
      [(fold_outer & Hshape & Hhead_lifo & Hfresh & Hopened)|[_ Hclosed]].
    2: { exfalso. exact (Hclosed member). }
    inversion Hshape; subst focused outer stack_middle.
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      tail).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hcertificate_lifo Hstack_in). }
    destruct (total_reopen rest rest_total invariant fold_outer tail Hfold_wf
      Hfold_stack Hrest)
      as [normal _].
    exists (outcome_matched_fold_reopen view member Hfresh Hopened normal).
    exact I.
  - intros added base Hnonempty _ Hstack_in
      (stack_middle & Hhead & Hrest).
    simpl in Hhead.
    pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as
      [(fold_outer & Hshape & Hhead_lifo & Hfresh & Hopened)|[_ Hclosed]].
    2: { exfalso. exact (Hclosed member). }
    destruct base as [|[popped popped_outer] base]; first discriminate Hshape.
    inversion Hshape; subst popped popped_outer stack_middle.
    assert (Heq : ((added ++ [(invariant, fold_outer)]) ++ base) =
        added ++ (invariant, fold_outer) :: base).
    { rewrite <- app_assoc. reflexivity. }
    pose proof (transport_suffix_lifo_out rest base _ _ (eq_sym Heq) Hrest)
      as Hrest_path.
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      base).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hcertificate_lifo Hstack_in). }
    destruct (total_reopen_path rest rest_total
      (added ++ [(invariant, fold_outer)]) base) as [normal _].
    { intros Hempty. apply app_eq_nil in Hempty as [_ Hsingleton].
      discriminate Hsingleton. }
    { exact Hfold_wf. }
    { exact Hfold_stack. }
    { exact Hrest_path. }
    exists (reopen_path_matched_fold_head view member Hfresh Hopened normal).
    exact I.
  - intros focused outer tail _ Hstack_in
      (stack_middle & Hhead & Hrest).
    simpl in Hhead.
    pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as
      [(fold_outer & Hshape & Hhead_lifo & Hfresh & Hopened)|[_ Hclosed]].
    2: { exfalso. exact (Hclosed member). }
    destruct tail as [|[popped popped_outer] base]; first discriminate Hshape.
    inversion Hshape; subst popped popped_outer stack_middle.
    assert (Heq : (([(focused, outer); (invariant, fold_outer)]) ++ base) =
        (focused, outer) :: (invariant, fold_outer) :: base) by reflexivity.
    pose proof (transport_suffix_lifo_out rest base _ _ (eq_sym Heq) Hrest)
      as Hrest_path.
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      base).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hcertificate_lifo Hstack_in). }
    destruct (total_reopen_path rest rest_total
      [(focused, outer); (invariant, fold_outer)] base) as [path_normal _].
    { discriminate. }
    { exact Hfold_wf. }
    { exact Hfold_stack. }
    { exact Hrest_path. }
    pose (rebased := @reopen_path_matched_fold_head cost Γ fuel entry statement
      invariant fold_outer base [(focused, outer)] exit view member Hfresh
      Hopened rest path_normal).
    exists (reopen_normalization_of_singleton_path rebased). exact I.
  - intros focused outer tail stack_out _ Hstack_in Hsuffix
      (stack_middle & Hhead & Hrest). simpl in Hhead.
    pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as
      [(fold_outer & Hshape & Hhead_lifo & Hfresh & Hopened)|[_ Hclosed]].
    2: { exfalso. exact (Hclosed member). }
    inversion Hshape; subst focused outer stack_middle.
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      tail).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hcertificate_lifo Hstack_in). }
    destruct (total_normalizes_stack_suffix rest rest_total tail stack_out
      Hfold_wf Hfold_stack Hsuffix Hrest) as [normal _].
    exists (split_matched_fold_head view member Hfresh Hopened normal). exact I.
Qed.

Definition total_fresh_fold_head
    {cost Γ fuel entry statement invariant exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    (closed : invariant ∉ Atomicity.analysis_open entry)
    {rest : certificate_suffix cost Γ
      (Atomicity.fold_invariant invariant entry) exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : suffix_total_normalization rest) :
    suffix_total_normalization
      (SuffixCons (Atomicity.CertFold cost Γ fuel entry statement invariant
        view) rest).
Proof.
  constructor.
  - intros _ Hstack (stack_middle & Hhead & Hrest). simpl in Hhead.
    pose proof Hhead as Hhead_lifo.
    destruct Hhead as [(outer & _ & Hmember & _)|[-> _]].
    { exfalso. exact (closed Hmember). }
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry)) []).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hhead_lifo Hstack). }
    destruct (total_empty rest rest_total Hfold_wf Hfold_stack Hrest)
      as [normal _].
    exists (normalize_fresh_fold_head view closed normal). exact I.
  - intros focused outer tail _ Hstack_in
      (stack_middle & Hhead & Hrest).
    simpl in Hhead.
    pose proof Hhead as Hhead_lifo.
    destruct Hhead as [(fold_outer & _ & Hmember & _)|[-> _]].
    { exfalso. exact (closed Hmember). }
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      ((focused, outer) :: tail)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hhead_lifo Hstack_in). }
    destruct (total_outcome rest rest_total focused outer tail Hfold_wf
      Hfold_stack Hrest)
      as [normal _].
    exists (@prepend_preserving_outcome cost Γ (S fuel) entry statement
      (Atomicity.fold_invariant invariant entry) exit focused outer tail
      (Atomicity.CertFold cost Γ fuel entry statement invariant view) rest
      (or_intror (conj eq_refl closed))
      (fresh_fold_piece (cost := cost) (fuel := fuel)
        (stack := (focused, outer) :: tail) view closed) I normal).
    exact I.
  - intros added base Hnonempty _ Hstack_in
      (stack_middle & Hhead & Hrest).
    simpl in Hhead.
    pose proof Hhead as Hhead_lifo.
    destruct Hhead as [(fold_outer & _ & Hmember & _)|[-> _]].
    { exfalso. exact (closed Hmember). }
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      base).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hhead_lifo Hstack_in). }
    destruct (total_reopen_path rest rest_total added base Hnonempty Hfold_wf
      Hfold_stack Hrest)
      as [normal _].
    exists (@prepend_reopen_path_normalization cost Γ (S fuel) entry statement
      (Atomicity.fold_invariant invariant entry) exit base added
      (Atomicity.CertFold cost Γ fuel entry statement invariant view) rest
      (or_intror (conj eq_refl closed))
      (fresh_fold_piece (cost := cost) (fuel := fuel) (stack := base) view
        closed) normal).
    exact I.
  - intros focused outer tail _ Hstack_in
      (stack_middle & Hhead & Hrest).
    simpl in Hhead.
    pose proof Hhead as Hhead_lifo.
    destruct Hhead as [(fold_outer & _ & Hmember & _)|[-> _]].
    { exfalso. exact (closed Hmember). }
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      tail).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hhead_lifo Hstack_in). }
    destruct (total_reopen rest rest_total focused outer tail Hfold_wf
      Hfold_stack Hrest)
      as [normal _].
    exists (@prepend_reopen_execution cost Γ (S fuel) entry statement
      (Atomicity.fold_invariant invariant entry) exit focused outer tail
      (Atomicity.CertFold cost Γ fuel entry statement invariant view) rest
      (or_intror (conj eq_refl closed))
      (fresh_fold_piece (cost := cost) (fuel := fuel) (stack := tail) view
        closed) normal).
    exact I.
  - intros focused outer tail stack_out _ Hstack_in Hsuffix
      (stack_middle & Hhead & Hrest). simpl in Hhead.
    pose proof Hhead as Hhead_lifo.
    destruct Hhead as [(fold_outer & _ & Hmember & _)|[-> _]].
    { exfalso. exact (closed Hmember). }
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      ((focused, outer) :: tail)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hhead_lifo Hstack_in). }
    destruct (total_close rest rest_total focused outer tail stack_out Hfold_wf
      Hfold_stack Hsuffix Hrest) as [split _].
    exists (@prepend_preserving_split cost Γ (S fuel) entry statement
      (Atomicity.fold_invariant invariant entry) exit focused outer tail
      stack_out
      (Atomicity.CertFold cost Γ fuel entry statement invariant view) rest
      (or_intror (conj eq_refl closed))
      (fresh_fold_piece (cost := cost) (fuel := fuel)
        (stack := (focused, outer) :: tail) view closed) I split).
    exact I.
Qed.

Definition total_fold_head
    {cost Γ fuel entry statement invariant exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    {rest : certificate_suffix cost Γ
      (Atomicity.fold_invariant invariant entry) exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : suffix_total_normalization rest) :
    suffix_total_normalization
      (SuffixCons (Atomicity.CertFold cost Γ fuel entry statement invariant
        view) rest).
Proof.
  destruct (decide (invariant ∈ Atomicity.analysis_open entry)) as
    [member|closed].
  - exact (total_matched_fold_head view member entry_wf rest_total).
  - exact (total_fresh_fold_head view closed entry_wf rest_total).
Defined.

Definition net_total_matched_fold_head
    {cost Γ fuel entry statement invariant exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    (member : invariant ∈ Atomicity.analysis_open entry)
    {rest : certificate_suffix cost Γ
      (Atomicity.fold_invariant invariant entry) exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : suffix_net_totality rest) :
    suffix_net_totality
      (SuffixCons (Atomicity.CertFold cost Γ fuel entry statement invariant
        view) rest).
Proof.
  constructor.
  - intros stack_in stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as
      [(fold_outer & Hshape & Hmember & Hfresh & Hopened)|[_ Hclosed]].
    2: { exfalso. exact (Hclosed member). }
    subst stack_in.
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      stack_middle).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hcertificate_lifo Hstack). }
    destruct (total_net rest rest_total stack_middle stack_out Hfold_wf
      Hfold_stack Hrest) as [normal _].
    exists (@normalize_net_close cost Γ (S fuel) entry statement
      (Atomicity.fold_invariant invariant entry) exit
      (invariant, fold_outer) stack_middle stack_out
      (Atomicity.CertFold cost Γ fuel entry statement invariant view) rest
      Hcertificate_lifo
      (fold_piece (cost := cost) (fuel := fuel) (tail := stack_middle) view
        Hmember Hfresh Hopened) I normal). exact I.
  - intros focused outer tail stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as
      [(fold_outer & Hshape & Hmember & Hfresh & Hopened)|[_ Hclosed]].
    2: { exfalso. exact (Hclosed member). }
    inversion Hshape; subst focused outer stack_middle.
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      tail).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hcertificate_lifo Hstack). }
    destruct (total_net rest rest_total tail stack_out Hfold_wf Hfold_stack
      Hrest) as [normal _].
    exists (@normalize_focused_net_close cost Γ (S fuel) entry statement
      (Atomicity.fold_invariant invariant entry) exit
      (invariant, fold_outer) tail stack_out
      (Atomicity.CertFold cost Γ fuel entry statement invariant view) rest
      Hcertificate_lifo
      (fold_piece (cost := cost) (fuel := fuel) (tail := tail) view Hmember
        Hfresh Hopened) I normal). exact I.
Qed.

Definition traced_net_total_matched_fold_head
    {cost Γ fuel entry statement invariant exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    (member : invariant ∈ Atomicity.analysis_open entry)
    {rest : certificate_suffix cost Γ
      (Atomicity.fold_invariant invariant entry) exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : traced_suffix_net_totality rest) :
    traced_suffix_net_totality
      (SuffixCons (Atomicity.CertFold cost Γ fuel entry statement invariant
        view) rest).
Proof.
  constructor.
  - intros stack_in stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as
      [(fold_outer & Hshape & Hmember & Hfresh & Hopened)|[_ Hclosed]].
    2: { exfalso. exact (Hclosed member). }
    subst stack_in.
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      stack_middle).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hcertificate_lifo Hstack). }
    destruct (traced_total_net rest rest_total stack_middle stack_out Hfold_wf
      Hfold_stack Hrest) as [normal _].
    exists (@traced_normalize_net_close cost Γ (S fuel) entry statement
      (Atomicity.fold_invariant invariant entry) exit
      (invariant, fold_outer) stack_middle stack_out
      (Atomicity.CertFold cost Γ fuel entry statement invariant view) rest
      Hcertificate_lifo
      (fold_piece (cost := cost) (fuel := fuel) (tail := stack_middle) view
        Hmember Hfresh Hopened)
      (ChunkCertificateFold cost Γ fuel entry statement invariant fold_outer
        stack_middle view Hmember Hfresh Hopened) I normal). exact I.
  - intros focused outer tail stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as
      [(fold_outer & Hshape & Hmember & Hfresh & Hopened)|[_ Hclosed]].
    2: { exfalso. exact (Hclosed member). }
    inversion Hshape; subst focused outer stack_middle.
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      tail).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hcertificate_lifo Hstack). }
    destruct (traced_total_net rest rest_total tail stack_out Hfold_wf
      Hfold_stack Hrest) as [normal _].
    exists (@traced_normalize_focused_net_close cost Γ (S fuel) entry
      statement (Atomicity.fold_invariant invariant entry) exit
      (invariant, fold_outer) tail stack_out
      (Atomicity.CertFold cost Γ fuel entry statement invariant view) rest
      Hcertificate_lifo
      (fold_piece (cost := cost) (fuel := fuel) (tail := tail) view Hmember
        Hfresh Hopened)
      (ChunkCertificateFold cost Γ fuel entry statement invariant fold_outer
        tail view Hmember Hfresh Hopened) I normal). exact I.
Qed.

Definition net_total_fresh_fold_head
    {cost Γ fuel entry statement invariant exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    (closed : invariant ∉ Atomicity.analysis_open entry)
    {rest : certificate_suffix cost Γ
      (Atomicity.fold_invariant invariant entry) exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : suffix_net_totality rest) :
    suffix_net_totality
      (SuffixCons (Atomicity.CertFold cost Γ fuel entry statement invariant
        view) rest).
Proof.
  constructor.
  - intros stack_in stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as [(fold_outer & _ & Hmember & _)|[-> _]].
    { exfalso. exact (closed Hmember). }
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      stack_in).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hcertificate_lifo Hstack). }
    destruct (total_net rest rest_total stack_in stack_out Hfold_wf
      Hfold_stack Hrest) as [normal _].
    exists (@prepend_net_chunk cost Γ (S fuel) entry statement
      (Atomicity.fold_invariant invariant entry) exit stack_in stack_out
      (Atomicity.CertFold cost Γ fuel entry statement invariant view) rest
      Hcertificate_lifo
      (fresh_fold_piece (cost := cost) (fuel := fuel) (stack := stack_in) view
        closed) normal). exact I.
  - intros focused outer tail stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as [(fold_outer & _ & Hmember & _)|[-> _]].
    { exfalso. exact (closed Hmember). }
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      ((focused, outer) :: tail)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hcertificate_lifo Hstack). }
    destruct (total_focused_net rest rest_total focused outer tail stack_out
      Hfold_wf Hfold_stack Hrest) as [normal _].
    exists (@prepend_focused_net_chunk cost Γ (S fuel) entry statement
      (Atomicity.fold_invariant invariant entry) exit focused outer tail
      stack_out
      (Atomicity.CertFold cost Γ fuel entry statement invariant view) rest
      Hcertificate_lifo
      (fresh_fold_piece (cost := cost) (fuel := fuel)
        (stack := (focused, outer) :: tail) view closed) I normal). exact I.
Qed.

Definition net_total_fold_head
    {cost Γ fuel entry statement invariant exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    {rest : certificate_suffix cost Γ
      (Atomicity.fold_invariant invariant entry) exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : suffix_net_totality rest) :
    suffix_net_totality
      (SuffixCons (Atomicity.CertFold cost Γ fuel entry statement invariant
        view) rest).
Proof.
  destruct (decide (invariant ∈ Atomicity.analysis_open entry)) as
    [member|closed].
  - exact (net_total_matched_fold_head view member entry_wf rest_total).
  - exact (net_total_fresh_fold_head view closed entry_wf rest_total).
Defined.

Definition total_atomic_head
    {cost Γ fuel entry statement body outer inner exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewAtomic body)
    (step : Atomicity.take_step Atomicity.AtomicStep entry = inr outer)
    (body_certificate : Atomicity.analysis_certificate cost Γ fuel
      (Atomicity.AnalysisState (Atomicity.analysis_mask outer)
        (Atomicity.analysis_open outer)
        (Atomicity.analysis_step_taken outer) true) body inner)
    (open_equal : Atomicity.analysis_open inner =
      Atomicity.analysis_open outer)
    {rest : certificate_suffix cost Γ
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer)) exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : suffix_total_normalization rest) :
    suffix_total_normalization
      (SuffixCons
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal) rest).
Proof.
  constructor.
  - intros _ Hstack (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo.
    destruct Hhead as [Hbody ->].
    assert (Hmiddle_wf : Atomicity.state_wf
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer))).
    { exact (Atomicity.certificate_preserves_wf cost entry statement _
        entry_wf
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open
        (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
          (Atomicity.analysis_open inner)
          (Atomicity.analysis_step_taken outer ||
            Atomicity.analysis_step_taken inner)
          (Atomicity.analysis_in_atomic outer))) []).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)
        _ _ entry_wf Hhead_lifo Hstack). }
    destruct (total_empty rest rest_total Hmiddle_wf Hmiddle_stack Hrest)
      as [normal _].
    exists (normalize_atomic_head view step body_certificate open_equal Hbody
      normal). exact I.
  - intros invariant access_outer tail
      _ Hstack (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo.
    destruct Hhead as [Hbody ->].
    assert (Hmiddle_wf : Atomicity.state_wf
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer))).
    { exact (Atomicity.certificate_preserves_wf cost entry statement _
        entry_wf
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open
        (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
          (Atomicity.analysis_open inner)
          (Atomicity.analysis_step_taken outer ||
            Atomicity.analysis_step_taken inner)
          (Atomicity.analysis_in_atomic outer)))
      ((invariant, access_outer) :: tail)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)
        _ _ entry_wf Hhead_lifo Hstack). }
    destruct (total_outcome rest rest_total invariant access_outer tail
      Hmiddle_wf Hmiddle_stack Hrest)
      as [normal _].
    exists (@prepend_preserving_outcome cost Γ (S fuel) entry statement _ exit
      invariant access_outer tail
      (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
        step body_certificate open_equal) rest
      (conj Hbody eq_refl)
      (atomic_piece (cost := cost) (fuel := fuel)
        (stack := (invariant, access_outer) :: tail) view step body_certificate
        open_equal) I normal). exact I.
  - intros added base Hnonempty _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo.
    destruct Hhead as [Hbody ->].
    assert (Hmiddle_wf : Atomicity.state_wf
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer))).
    { exact (Atomicity.certificate_preserves_wf cost entry statement _
        entry_wf
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open
        (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
          (Atomicity.analysis_open inner)
          (Atomicity.analysis_step_taken outer ||
            Atomicity.analysis_step_taken inner)
          (Atomicity.analysis_in_atomic outer))) base).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)
        _ _ entry_wf Hhead_lifo Hstack). }
    destruct (total_reopen_path rest rest_total added base Hnonempty Hmiddle_wf
      Hmiddle_stack Hrest)
      as [normal _].
    exists (@prepend_reopen_path_normalization cost Γ (S fuel) entry statement
      _ exit base added
      (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
        step body_certificate open_equal) rest
      (conj Hbody eq_refl)
      (atomic_piece (cost := cost) (fuel := fuel) (stack := base) view step
        body_certificate open_equal) normal). exact I.
  - intros invariant access_outer tail
      _ Hstack (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo.
    destruct Hhead as [Hbody ->].
    assert (Hmiddle_wf : Atomicity.state_wf
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer))).
    { exact (Atomicity.certificate_preserves_wf cost entry statement _
        entry_wf
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open
        (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
          (Atomicity.analysis_open inner)
          (Atomicity.analysis_step_taken outer ||
            Atomicity.analysis_step_taken inner)
          (Atomicity.analysis_in_atomic outer))) tail).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)
        _ _ entry_wf Hhead_lifo Hstack). }
    destruct (total_reopen rest rest_total invariant access_outer tail Hmiddle_wf
      Hmiddle_stack Hrest)
      as [normal _].
    exists (@prepend_reopen_execution cost Γ (S fuel) entry statement _ exit
      invariant access_outer tail
      (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
        step body_certificate open_equal) rest
      (conj Hbody eq_refl)
      (atomic_piece (cost := cost) (fuel := fuel) (stack := tail) view step
        body_certificate open_equal) normal). exact I.
  - intros invariant access_outer tail stack_out _ Hstack Hsuffix
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hhead_lifo.
    destruct Hhead as [Hbody ->].
    assert (Hmiddle_wf : Atomicity.state_wf
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer))).
    { exact (Atomicity.certificate_preserves_wf cost entry statement _
        entry_wf
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open
        (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
          (Atomicity.analysis_open inner)
          (Atomicity.analysis_step_taken outer ||
            Atomicity.analysis_step_taken inner)
          (Atomicity.analysis_in_atomic outer)))
      ((invariant, access_outer) :: tail)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)
        _ _ entry_wf Hhead_lifo Hstack). }
    destruct (total_close rest rest_total invariant access_outer tail stack_out
      Hmiddle_wf Hmiddle_stack Hsuffix Hrest) as [split _].
    exists (@prepend_preserving_split cost Γ (S fuel) entry statement _ exit
      invariant access_outer tail stack_out
      (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
        step body_certificate open_equal) rest
      (conj Hbody eq_refl)
      (atomic_piece (cost := cost) (fuel := fuel)
        (stack := (invariant, access_outer) :: tail) view step body_certificate
        open_equal) I split). exact I.
Qed.

Definition net_total_atomic_head
    {cost Γ fuel entry statement body outer inner exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewAtomic body)
    (step : Atomicity.take_step Atomicity.AtomicStep entry = inr outer)
    (body_certificate : Atomicity.analysis_certificate cost Γ fuel
      (Atomicity.AnalysisState (Atomicity.analysis_mask outer)
        (Atomicity.analysis_open outer)
        (Atomicity.analysis_step_taken outer) true) body inner)
    (open_equal : Atomicity.analysis_open inner =
      Atomicity.analysis_open outer)
    {rest : certificate_suffix cost Γ
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer)) exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : suffix_net_totality rest) :
    suffix_net_totality
      (SuffixCons
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal) rest).
Proof.
  constructor.
  - intros stack_in stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as [Hbody ->].
    assert (Hmiddle_wf : Atomicity.state_wf
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer))).
    { exact (Atomicity.certificate_preserves_wf cost entry statement _
        entry_wf
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open inner) stack_in).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)
        _ _ entry_wf Hcertificate_lifo Hstack). }
    destruct (total_net rest rest_total stack_in stack_out Hmiddle_wf
      Hmiddle_stack Hrest) as [normal _].
    exists (@prepend_net_chunk cost Γ (S fuel) entry statement _ exit stack_in
      stack_out
      (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
        step body_certificate open_equal) rest (conj Hbody eq_refl)
      (atomic_piece (cost := cost) (fuel := fuel) (stack := stack_in) view step
        body_certificate open_equal) normal). exact I.
  - intros invariant access_outer tail stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as [Hbody ->].
    assert (Hmiddle_wf : Atomicity.state_wf
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer))).
    { exact (Atomicity.certificate_preserves_wf cost entry statement _
        entry_wf
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open inner) ((invariant, access_outer) :: tail)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)
        _ _ entry_wf Hcertificate_lifo Hstack). }
    destruct (total_focused_net rest rest_total invariant access_outer tail
      stack_out Hmiddle_wf Hmiddle_stack Hrest) as [normal _].
    exists (@prepend_focused_net_chunk cost Γ (S fuel) entry statement _ exit
      invariant access_outer tail stack_out
      (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
        step body_certificate open_equal) rest (conj Hbody eq_refl)
      (atomic_piece (cost := cost) (fuel := fuel)
        (stack := (invariant, access_outer) :: tail) view step body_certificate
        open_equal) I normal). exact I.
Qed.

Definition traced_net_total_fresh_fold_head
    {cost Γ fuel entry statement invariant exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    (closed : invariant ∉ Atomicity.analysis_open entry)
    {rest : certificate_suffix cost Γ
      (Atomicity.fold_invariant invariant entry) exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : traced_suffix_net_totality rest) :
    traced_suffix_net_totality
      (SuffixCons (Atomicity.CertFold cost Γ fuel entry statement invariant
        view) rest).
Proof.
  constructor.
  - intros stack_in stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as [(fold_outer & _ & Hmember & _)|[-> _]].
    { exfalso. exact (closed Hmember). }
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      stack_in).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hcertificate_lifo Hstack). }
    destruct (traced_total_net rest rest_total stack_in stack_out Hfold_wf
      Hfold_stack Hrest) as [normal _].
    exists (@traced_prepend_net_chunk cost Γ (S fuel) entry statement
      (Atomicity.fold_invariant invariant entry) exit stack_in stack_out
      (Atomicity.CertFold cost Γ fuel entry statement invariant view) rest
      Hcertificate_lifo
      (fresh_fold_piece (cost := cost) (fuel := fuel) (stack := stack_in)
        view closed)
      (ChunkCertificateFreshFold cost Γ fuel entry statement invariant
        stack_in view closed)
      normal). exact I.
  - intros focused_invariant outer tail stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as [(fold_outer & _ & Hmember & _)|[-> _]].
    { exfalso. exact (closed Hmember). }
    assert (Hfold_wf : Atomicity.state_wf
      (Atomicity.fold_invariant invariant entry)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement
        (Atomicity.fold_invariant invariant entry) entry_wf
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)). }
    assert (Hfold_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open (Atomicity.fold_invariant invariant entry))
      ((focused_invariant, outer) :: tail)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertFold cost Γ fuel entry statement invariant view)
        _ _ entry_wf Hcertificate_lifo Hstack). }
    destruct (traced_total_focused_net rest rest_total focused_invariant outer tail
      stack_out Hfold_wf Hfold_stack Hrest) as [normal _].
    exists (@traced_prepend_focused_net_chunk cost Γ (S fuel) entry statement
      (Atomicity.fold_invariant invariant entry) exit focused_invariant outer tail
      stack_out
      (Atomicity.CertFold cost Γ fuel entry statement invariant view) rest
      Hcertificate_lifo
      (fresh_fold_piece (cost := cost) (fuel := fuel)
        (stack := (focused_invariant, outer) :: tail) view closed)
      (ChunkCertificateFreshFold cost Γ fuel entry statement invariant
        ((focused_invariant, outer) :: tail) view closed)
      I normal). exact I.
Qed.

Definition traced_net_total_fold_head
    {cost Γ fuel entry statement invariant exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewFold invariant)
    {rest : certificate_suffix cost Γ
      (Atomicity.fold_invariant invariant entry) exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : traced_suffix_net_totality rest) :
    traced_suffix_net_totality
      (SuffixCons (Atomicity.CertFold cost Γ fuel entry statement invariant
        view) rest).
Proof.
  destruct (decide (invariant ∈ Atomicity.analysis_open entry)) as
    [member|closed].
  - exact (traced_net_total_matched_fold_head view member entry_wf rest_total).
  - exact (traced_net_total_fresh_fold_head view closed entry_wf rest_total).
Defined.

Definition traced_net_total_atomic_head
    {cost Γ fuel entry statement body outer inner exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewAtomic body)
    (step : Atomicity.take_step Atomicity.AtomicStep entry = inr outer)
    (body_certificate : Atomicity.analysis_certificate cost Γ fuel
      (Atomicity.AnalysisState (Atomicity.analysis_mask outer)
        (Atomicity.analysis_open outer)
        (Atomicity.analysis_step_taken outer) true) body inner)
    (open_equal : Atomicity.analysis_open inner =
      Atomicity.analysis_open outer)
    {rest : certificate_suffix cost Γ
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer)) exit}
    (entry_wf : Atomicity.state_wf entry)
    (rest_total : traced_suffix_net_totality rest) :
    traced_suffix_net_totality
      (SuffixCons
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal) rest).
Proof.
  constructor.
  - intros stack_in stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as [Hbody ->].
    assert (Hmiddle_wf : Atomicity.state_wf
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer))).
    { exact (Atomicity.certificate_preserves_wf cost entry statement _
        entry_wf
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open inner) stack_in).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)
        _ _ entry_wf Hcertificate_lifo Hstack). }
    destruct (traced_total_net rest rest_total stack_in stack_out Hmiddle_wf
      Hmiddle_stack Hrest) as [normal _].
    exists (@traced_prepend_net_chunk cost Γ (S fuel) entry statement _ exit
      stack_in stack_out
      (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
        step body_certificate open_equal) rest (conj Hbody eq_refl)
      (atomic_piece (cost := cost) (fuel := fuel) (stack := stack_in) view step
        body_certificate open_equal)
      (ChunkCertificateAtomic cost Γ fuel entry statement body outer inner
        stack_in view step body_certificate open_equal)
      normal). exact I.
  - intros invariant access_outer tail stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    simpl in Hhead. pose proof Hhead as Hcertificate_lifo.
    destruct Hhead as [Hbody ->].
    assert (Hmiddle_wf : Atomicity.state_wf
      (Atomicity.AnalysisState (Atomicity.analysis_mask inner)
        (Atomicity.analysis_open inner)
        (Atomicity.analysis_step_taken outer ||
          Atomicity.analysis_step_taken inner)
        (Atomicity.analysis_in_atomic outer))).
    { exact (Atomicity.certificate_preserves_wf cost entry statement _
        entry_wf
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)). }
    assert (Hmiddle_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open inner) ((invariant, access_outer) :: tail)).
    { exact (Atomicity.lifo_preserves_access_stack_consistency
        (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
          step body_certificate open_equal)
        _ _ entry_wf Hcertificate_lifo Hstack). }
    destruct (traced_total_focused_net rest rest_total invariant access_outer
      tail stack_out Hmiddle_wf Hmiddle_stack Hrest) as [normal _].
    exists (@traced_prepend_focused_net_chunk cost Γ (S fuel) entry statement
      _ exit invariant access_outer tail stack_out
      (Atomicity.CertAtomic cost Γ fuel entry statement body outer inner view
        step body_certificate open_equal) rest (conj Hbody eq_refl)
      (atomic_piece (cost := cost) (fuel := fuel)
        (stack := (invariant, access_outer) :: tail) view step body_certificate
        open_equal)
      (ChunkCertificateAtomic cost Γ fuel entry statement body outer inner
        ((invariant, access_outer) :: tail) view step body_certificate
        open_equal)
      I normal). exact I.
Qed.

Definition net_total_sequence_head
    {cost Γ fuel entry statement first middle second next exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      first middle)
    (second_certificate : Atomicity.analysis_certificate cost Γ fuel middle
      second next)
    (rest : certificate_suffix cost Γ next exit)
    (flat_total : suffix_net_totality
      (expand_sequence_suffix view first_certificate second_certificate rest)) :
    suffix_net_totality
      (SuffixCons
        (Atomicity.CertSequence cost Γ fuel entry statement first middle second
          next view first_certificate second_certificate) rest).
Proof.
  pose (expansion := ExpandsSequence cost Γ fuel entry statement first middle
    second next exit view first_certificate second_certificate rest).
  constructor.
  - intros stack_in stack_out Hwf Hstack Hlifo.
    assert (Hflat_lifo : suffix_lifo
      (expand_sequence_suffix view first_certificate second_certificate rest)
      stack_in stack_out).
    { apply (proj2 (suffix_expands_lifo expansion stack_in stack_out)).
      exact Hlifo. }
    destruct (total_net _ flat_total stack_in stack_out Hwf Hstack Hflat_lifo)
      as [normal _].
    exists (contract_net_expansion expansion normal). exact I.
  - intros invariant outer tail stack_out Hwf Hstack Hlifo.
    assert (Hflat_lifo : suffix_lifo
      (expand_sequence_suffix view first_certificate second_certificate rest)
      ((invariant, outer) :: tail) stack_out).
    { apply (proj2 (suffix_expands_lifo expansion _ _)). exact Hlifo. }
    destruct (total_focused_net _ flat_total invariant outer tail stack_out
      Hwf Hstack Hflat_lifo) as [normal _].
    exists (contract_focused_net_expansion expansion normal). exact I.
Qed.

Definition traced_net_total_sequence_head
    {cost Γ fuel entry statement first middle second next exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewSequence first second)
    (first_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      first middle)
    (second_certificate : Atomicity.analysis_certificate cost Γ fuel middle
      second next)
    (rest : certificate_suffix cost Γ next exit)
    (flat_total : traced_suffix_net_totality
      (expand_sequence_suffix view first_certificate second_certificate rest)) :
    traced_suffix_net_totality
      (SuffixCons
        (Atomicity.CertSequence cost Γ fuel entry statement first middle second
          next view first_certificate second_certificate) rest).
Proof.
  pose (expansion := ExpandsSequence cost Γ fuel entry statement first middle
    second next exit view first_certificate second_certificate rest).
  constructor.
  - intros stack_in stack_out Hwf Hstack Hlifo.
    assert (Hflat_lifo : suffix_lifo
      (expand_sequence_suffix view first_certificate second_certificate rest)
      stack_in stack_out).
    { apply (proj2 (suffix_expands_lifo expansion stack_in stack_out)).
      exact Hlifo. }
    destruct (traced_total_net _ flat_total stack_in stack_out Hwf Hstack
      Hflat_lifo) as [normal _].
    exists (traced_contract_net_expansion expansion normal). exact I.
  - intros invariant outer tail stack_out Hwf Hstack Hlifo.
    assert (Hflat_lifo : suffix_lifo
      (expand_sequence_suffix view first_certificate second_certificate rest)
      ((invariant, outer) :: tail) stack_out).
    { apply (proj2 (suffix_expands_lifo expansion _ _)). exact Hlifo. }
    destruct (traced_total_focused_net _ flat_total invariant outer tail
      stack_out Hwf Hstack Hflat_lifo) as [normal _].
    exists (traced_contract_focused_net_expansion expansion normal). exact I.
Qed.

Definition net_total_conditional_head
    {cost Γ fuel entry statement then_statement else_statement then_exit
      else_exit exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewConditional then_statement else_statement)
    (then_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      then_statement then_exit)
    (else_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      else_statement else_exit)
    (open_equal : Atomicity.analysis_open then_exit =
      Atomicity.analysis_open else_exit)
    (atomic_equal : Atomicity.analysis_in_atomic then_exit =
      Atomicity.analysis_in_atomic else_exit)
    {rest : certificate_suffix cost Γ
      (Atomicity.AnalysisState
        (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
        (Atomicity.analysis_open then_exit)
        (Atomicity.analysis_step_taken then_exit ||
          Atomicity.analysis_step_taken else_exit)
        (Atomicity.analysis_in_atomic then_exit)) exit}
    (entry_wf : Atomicity.state_wf entry)
    (then_total : suffix_net_totality (singleton_suffix then_certificate))
    (else_total : suffix_net_totality (singleton_suffix else_certificate))
    (rest_total : suffix_net_totality rest) :
    suffix_net_totality
      (SuffixCons
        (Atomicity.CertConditional cost Γ fuel entry statement then_statement
          else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal) rest).
Proof.
  pose (join_state :=
    (Atomicity.AnalysisState
      (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
      (Atomicity.analysis_open then_exit)
      (Atomicity.analysis_step_taken then_exit ||
        Atomicity.analysis_step_taken else_exit)
      (Atomicity.analysis_in_atomic then_exit))).
  pose (head_certificate :=
    Atomicity.CertConditional cost Γ fuel entry statement then_statement
      else_statement then_exit else_exit view then_certificate
      else_certificate open_equal atomic_equal).
  constructor.
  - intros stack_in stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    destruct Hhead as [Hthen Helse].
    assert (Hthen_suffix : suffix_lifo (singleton_suffix then_certificate)
      stack_in stack_middle).
    { apply (proj2 (singleton_suffix_lifo then_certificate _ _)). exact Hthen. }
    assert (Helse_suffix : suffix_lifo (singleton_suffix else_certificate)
      stack_in stack_middle).
    { apply (proj2 (singleton_suffix_lifo else_certificate _ _)). exact Helse. }
    destruct (total_net _ then_total stack_in stack_middle entry_wf Hstack
      Hthen_suffix) as [then_normal _].
    destruct (total_net _ else_total stack_in stack_middle entry_wf Hstack
      Helse_suffix) as [else_normal _].
    assert (Hjoin_wf : Atomicity.state_wf join_state).
    { exact (Atomicity.certificate_preserves_wf cost entry statement _ entry_wf
        head_certificate). }
    assert (Hjoin_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open then_exit) stack_middle).
    { exact (Atomicity.lifo_preserves_access_stack_consistency head_certificate
        _ _ entry_wf (conj Hthen Helse) Hstack). }
    destruct (total_net rest rest_total stack_middle stack_out Hjoin_wf
      Hjoin_stack Hrest) as [rest_normal _].
    unshelve eexists.
    + refine {| suffix_net_tree := @NetConditional stack_in stack_middle
          stack_out entry then_exit else_exit join_state exit
          (Payload.RavenConditional Γ fuel cost entry statement then_statement
            else_statement then_exit else_exit view then_certificate
            else_certificate open_equal atomic_equal)
          (suffix_net_tree _ then_normal) (suffix_net_tree _ else_normal)
          (suffix_net_tree _ rest_normal) |}.
      exists stack_middle. split; [exact (conj Hthen Helse)|exact Hrest].
    + exact I.
  - intros invariant outer tail stack_out _ Hstack
      (stack_middle & Hhead & Hrest).
    destruct Hhead as [Hthen Helse].
    assert (Hthen_suffix : suffix_lifo (singleton_suffix then_certificate)
      ((invariant, outer) :: tail) stack_middle).
    { apply (proj2 (singleton_suffix_lifo then_certificate _ _)). exact Hthen. }
    assert (Helse_suffix : suffix_lifo (singleton_suffix else_certificate)
      ((invariant, outer) :: tail) stack_middle).
    { apply (proj2 (singleton_suffix_lifo else_certificate _ _)). exact Helse. }
    destruct (total_focused_net _ then_total invariant outer tail stack_middle
      entry_wf Hstack Hthen_suffix) as [then_normal _].
    destruct (total_focused_net _ else_total invariant outer tail stack_middle
      entry_wf Hstack Helse_suffix) as [else_normal _].
    assert (Hjoin_wf : Atomicity.state_wf join_state).
    { exact (Atomicity.certificate_preserves_wf cost entry statement _ entry_wf
        head_certificate). }
    assert (Hjoin_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open then_exit) stack_middle).
    { exact (Atomicity.lifo_preserves_access_stack_consistency head_certificate
        _ _ entry_wf (conj Hthen Helse) Hstack). }
    destruct (total_net rest rest_total stack_middle stack_out Hjoin_wf
      Hjoin_stack Hrest) as [rest_normal _].
    unshelve eexists.
    + refine {| suffix_focused_net_tree := @FocusNetConditional
          (invariant, outer) tail stack_middle stack_out entry then_exit
          else_exit join_state exit
          (Payload.RavenConditional Γ fuel cost entry statement then_statement
            else_statement then_exit else_exit view then_certificate
            else_certificate open_equal atomic_equal)
          (suffix_focused_net_tree _ then_normal)
          (suffix_focused_net_tree _ else_normal)
          (suffix_net_tree _ rest_normal) |}.
      exists stack_middle. split; [exact (conj Hthen Helse)|exact Hrest].
    + exact I.
Qed.

Definition traced_net_total_conditional_head
    {cost Γ fuel entry statement then_statement else_statement then_exit
      else_exit exit}
    (view : Runtime.RegionSyntax.view statement =
      TypedAnalysisView.ViewConditional then_statement else_statement)
    (then_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      then_statement then_exit)
    (else_certificate : Atomicity.analysis_certificate cost Γ fuel entry
      else_statement else_exit)
    (open_equal : Atomicity.analysis_open then_exit =
      Atomicity.analysis_open else_exit)
    (atomic_equal : Atomicity.analysis_in_atomic then_exit =
      Atomicity.analysis_in_atomic else_exit)
    {rest : certificate_suffix cost Γ (conditional_join then_exit else_exit)
      exit}
    (entry_wf : Atomicity.state_wf entry)
    (then_total : traced_suffix_net_totality
      (singleton_suffix then_certificate))
    (else_total : traced_suffix_net_totality
      (singleton_suffix else_certificate))
    (rest_total : traced_suffix_net_totality rest) :
    traced_suffix_net_totality
      (SuffixCons
        (Atomicity.CertConditional cost Γ fuel entry statement then_statement
          else_statement then_exit else_exit view then_certificate
          else_certificate open_equal atomic_equal) rest).
Proof.
  pose (head_certificate :=
    Atomicity.CertConditional cost Γ fuel entry statement then_statement
      else_statement then_exit else_exit view then_certificate
      else_certificate open_equal atomic_equal).
  constructor.
  - intros stack_in stack_out _ Hstack
      (join_stack & Hhead & Hrest_lifo).
    destruct Hhead as [Hthen Helse].
    assert (Hwhole : suffix_lifo (SuffixCons head_certificate rest) stack_in
      stack_out).
    { exists join_stack. split; [exact (conj Hthen Helse)|exact Hrest_lifo]. }
    assert (Hthen_suffix : suffix_lifo (singleton_suffix then_certificate)
      stack_in join_stack).
    { apply (proj2 (singleton_suffix_lifo then_certificate _ _)). exact Hthen. }
    assert (Helse_suffix : suffix_lifo (singleton_suffix else_certificate)
      stack_in join_stack).
    { apply (proj2 (singleton_suffix_lifo else_certificate _ _)). exact Helse. }
    destruct (traced_total_net _ then_total stack_in join_stack entry_wf Hstack
      Hthen_suffix) as [then_normal _].
    destruct (traced_total_net _ else_total stack_in join_stack entry_wf Hstack
      Helse_suffix) as [else_normal _].
    assert (Hjoin_wf : Atomicity.state_wf
      (conditional_join then_exit else_exit)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement _ entry_wf
        head_certificate). }
    assert (Hjoin_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open then_exit) join_stack).
    { exact (Atomicity.lifo_preserves_access_stack_consistency head_certificate
        _ _ entry_wf (conj Hthen Helse) Hstack). }
    destruct (traced_total_net rest rest_total join_stack stack_out Hjoin_wf
      Hjoin_stack Hrest_lifo) as [rest_normal _].
    refine (ex_intro _ {| traced_net_normal :=
      {| suffix_net_lifo := Hwhole;
         suffix_net_tree := @NetConditional stack_in join_stack stack_out entry
          then_exit else_exit (conditional_join then_exit else_exit) exit
          (Payload.RavenConditional Γ fuel cost entry statement then_statement
            else_statement then_exit else_exit view then_certificate
            else_certificate open_equal atomic_equal)
          (suffix_net_tree _ (traced_net_normal _ then_normal))
          (suffix_net_tree _ (traced_net_normal _ else_normal))
          (suffix_net_tree _ (traced_net_normal _ rest_normal)) |};
      traced_net_source := TraceConditional cost Γ fuel entry statement
        then_statement else_statement then_exit else_exit exit stack_in
        join_stack stack_out view then_certificate else_certificate open_equal
        atomic_equal rest _ _ _ (traced_net_source _ then_normal)
        (traced_net_source _ else_normal) (traced_net_source _ rest_normal) |}
      I).
  - intros invariant outer tail stack_out _ Hstack
      (join_stack & Hhead & Hrest_lifo).
    destruct Hhead as [Hthen Helse].
    assert (Hwhole : suffix_lifo (SuffixCons head_certificate rest)
      ((invariant, outer) :: tail) stack_out).
    { exists join_stack. split; [exact (conj Hthen Helse)|exact Hrest_lifo]. }
    assert (Hthen_suffix : suffix_lifo (singleton_suffix then_certificate)
      ((invariant, outer) :: tail) join_stack).
    { apply (proj2 (singleton_suffix_lifo then_certificate _ _)). exact Hthen. }
    assert (Helse_suffix : suffix_lifo (singleton_suffix else_certificate)
      ((invariant, outer) :: tail) join_stack).
    { apply (proj2 (singleton_suffix_lifo else_certificate _ _)). exact Helse. }
    destruct (traced_total_focused_net _ then_total invariant outer tail
      join_stack entry_wf Hstack Hthen_suffix) as [then_normal _].
    destruct (traced_total_focused_net _ else_total invariant outer tail
      join_stack entry_wf Hstack Helse_suffix) as [else_normal _].
    assert (Hjoin_wf : Atomicity.state_wf
      (conditional_join then_exit else_exit)).
    { exact (Atomicity.certificate_preserves_wf cost entry statement _ entry_wf
        head_certificate). }
    assert (Hjoin_stack : Atomicity.access_stack_consistent
      (Atomicity.analysis_open then_exit) join_stack).
    { exact (Atomicity.lifo_preserves_access_stack_consistency head_certificate
        _ _ entry_wf (conj Hthen Helse) Hstack). }
    destruct (traced_total_net rest rest_total join_stack stack_out Hjoin_wf
      Hjoin_stack Hrest_lifo) as [rest_normal _].
    refine (ex_intro _ {| traced_focused_net_normal :=
      {| suffix_focused_net_lifo := Hwhole;
         suffix_focused_net_tree := @FocusNetConditional (invariant, outer)
          tail join_stack stack_out entry then_exit else_exit
          (conditional_join then_exit else_exit) exit
          (Payload.RavenConditional Γ fuel cost entry statement then_statement
            else_statement then_exit else_exit view then_certificate
            else_certificate open_equal atomic_equal)
          (suffix_focused_net_tree _ (traced_focused_net_normal _ then_normal))
          (suffix_focused_net_tree _ (traced_focused_net_normal _ else_normal))
          (suffix_net_tree _ (traced_net_normal _ rest_normal)) |};
      traced_focused_net_source := TraceFocusedConditional cost Γ fuel entry
        statement then_statement else_statement then_exit else_exit exit
        (invariant, outer) tail join_stack stack_out view then_certificate
        else_certificate open_equal atomic_equal rest _ _ _
        (traced_focused_net_source _ then_normal)
        (traced_focused_net_source _ else_normal)
        (traced_net_source _ rest_normal) |} I).
Qed.

Record packed_suffix (cost : Atomicity.cost_model) (Γ : context) : Type :=
  PackSuffix {
    packed_entry : Atomicity.analysis_state;
    packed_exit : Atomicity.analysis_state;
    packed_tree : certificate_suffix cost Γ packed_entry packed_exit;
  }.

Definition packed_suffix_measure {cost Γ} (packed : packed_suffix cost Γ) : nat :=
  suffix_measure (packed_tree _ _ packed).

Theorem net_totality_complete (cost : Atomicity.cost_model) (Γ : context)
    (packed : packed_suffix cost Γ) :
    Atomicity.state_wf (packed_entry _ _ packed) ->
    suffix_net_totality (packed_tree _ _ packed).
Proof.
  induction packed as [packed IH] using
    (well_founded_induction_type
      (well_founded_ltof (packed_suffix cost Γ) packed_suffix_measure)).
  destruct packed as [entry exit suffix]. simpl in *.
  intros Hwf.
  destruct suffix as [entry|fuel entry statement middle exit certificate rest].
  - exact net_total_suffix_done.
  - dependent destruction certificate.
    all: try match goal with
    | |- suffix_net_totality
        (SuffixCons
          (Atomicity.CertLeaf ?cm ?ctx ?fuel ?entry ?statement ?middle
            ?view ?step) ?rest) =>
        let Hrest_wf := fresh "Hrest_wf" in
        assert (Hrest_wf : Atomicity.state_wf middle) by exact
          (Atomicity.certificate_preserves_wf cm entry statement middle Hwf
            (Atomicity.CertLeaf cm ctx fuel entry statement middle view step));
        let Hrest_total := fresh "Hrest_total" in
        assert (Hrest_total : suffix_net_totality rest) by
          (apply (IH (PackSuffix cm ctx middle exit rest));
           [simpl; exact (suffix_rest_measure_decreases
              (Atomicity.CertLeaf cm ctx fuel entry statement middle view step)
              rest)|exact Hrest_wf]);
        exact (net_total_leaf_head view step Hwf Hrest_total)
    | |- suffix_net_totality
        (SuffixCons
          (Atomicity.CertUnfold ?cm ?ctx ?fuel ?entry ?statement ?invariant
            ?opened ?view ?step) ?rest) =>
        let Hrest_wf := fresh "Hrest_wf" in
        assert (Hrest_wf : Atomicity.state_wf opened) by exact
          (Atomicity.certificate_preserves_wf cm entry statement opened Hwf
            (Atomicity.CertUnfold cm ctx fuel entry statement invariant opened
              view step));
        let Hrest_total := fresh "Hrest_total" in
        assert (Hrest_total : suffix_net_totality rest) by
          (apply (IH (PackSuffix cm ctx opened exit rest));
           [simpl; exact (suffix_rest_measure_decreases
              (Atomicity.CertUnfold cm ctx fuel entry statement invariant
                opened view step) rest)|exact Hrest_wf]);
        exact (net_total_unfold_head view step Hwf Hrest_total)
    | |- suffix_net_totality
        (SuffixCons
          (Atomicity.CertFold ?cm ?ctx ?fuel ?entry ?statement ?invariant
            ?view) ?rest) =>
        let folded := constr:(Atomicity.fold_invariant invariant entry) in
        let Hrest_wf := fresh "Hrest_wf" in
        assert (Hrest_wf : Atomicity.state_wf folded) by exact
          (Atomicity.certificate_preserves_wf cm entry statement folded Hwf
            (Atomicity.CertFold cm ctx fuel entry statement invariant view));
        let Hrest_total := fresh "Hrest_total" in
        assert (Hrest_total : suffix_net_totality rest) by
          (apply (IH (PackSuffix cm ctx folded exit rest));
           [simpl; exact (suffix_rest_measure_decreases
              (Atomicity.CertFold cm ctx fuel entry statement invariant view)
              rest)|exact Hrest_wf]);
        exact (net_total_fold_head view Hwf Hrest_total)
    | |- suffix_net_totality
        (SuffixCons
          (Atomicity.CertSequence ?cm ?ctx ?fuel ?entry ?statement ?first
            ?middle ?second ?next ?view ?first_certificate
            ?second_certificate) ?rest) =>
        let flat := constr:(expand_sequence_suffix view first_certificate
          second_certificate rest) in
        let Hflat_total := fresh "Hflat_total" in
        assert (Hflat_total : suffix_net_totality flat) by
          (apply (IH (PackSuffix cm ctx entry exit flat));
           [simpl; exact (expand_sequence_suffix_measure_decreases view
              first_certificate second_certificate rest)|exact Hwf]);
        exact (net_total_sequence_head view first_certificate
          second_certificate rest Hflat_total)
    | |- suffix_net_totality
        (SuffixCons
          (Atomicity.CertAtomic ?cm ?ctx ?fuel ?entry ?statement ?body ?outer
            ?inner ?view ?step ?body_certificate ?open_equal) ?rest) =>
        let middle_state := constr:(Atomicity.AnalysisState
          (Atomicity.analysis_mask inner) (Atomicity.analysis_open inner)
          (Atomicity.analysis_step_taken outer ||
            Atomicity.analysis_step_taken inner)
          (Atomicity.analysis_in_atomic outer)) in
        let Hrest_wf := fresh "Hrest_wf" in
        assert (Hrest_wf : Atomicity.state_wf middle_state) by exact
          (Atomicity.certificate_preserves_wf cm entry statement middle_state
            Hwf (Atomicity.CertAtomic cm ctx fuel entry statement body outer
              inner view step body_certificate open_equal));
        let Hrest_total := fresh "Hrest_total" in
        assert (Hrest_total : suffix_net_totality rest) by
          (apply (IH (PackSuffix cm ctx middle_state exit rest));
           [simpl; exact (suffix_rest_measure_decreases
              (Atomicity.CertAtomic cm ctx fuel entry statement body outer
                inner view step body_certificate open_equal) rest)
           |exact Hrest_wf]);
        exact (net_total_atomic_head view step body_certificate open_equal Hwf
          Hrest_total)
    | |- suffix_net_totality
        (SuffixCons
          (Atomicity.CertConditional ?cm ?ctx ?fuel ?entry ?statement
            ?then_statement ?else_statement ?then_exit ?else_exit ?view
            ?then_certificate ?else_certificate ?open_equal ?atomic_equal)
          ?rest) =>
        let then_suffix := constr:(singleton_suffix then_certificate) in
        let else_suffix := constr:(singleton_suffix else_certificate) in
        let join_state := constr:(Atomicity.AnalysisState
          (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
          (Atomicity.analysis_open then_exit)
          (Atomicity.analysis_step_taken then_exit ||
            Atomicity.analysis_step_taken else_exit)
          (Atomicity.analysis_in_atomic then_exit)) in
        let Hthen_total := fresh "Hthen_total" in
        assert (Hthen_total : suffix_net_totality then_suffix) by
          (apply (IH (PackSuffix cm ctx entry then_exit then_suffix));
           [simpl; exact (conditional_then_measure_decreases view
              then_certificate else_certificate open_equal atomic_equal rest)
           |exact Hwf]);
        let Helse_total := fresh "Helse_total" in
        assert (Helse_total : suffix_net_totality else_suffix) by
          (apply (IH (PackSuffix cm ctx entry else_exit else_suffix));
           [simpl; exact (conditional_else_measure_decreases view
              then_certificate else_certificate open_equal atomic_equal rest)
           |exact Hwf]);
        let Hrest_wf := fresh "Hrest_wf" in
        assert (Hrest_wf : Atomicity.state_wf join_state) by exact
          (Atomicity.certificate_preserves_wf cm entry statement join_state Hwf
            (Atomicity.CertConditional cm ctx fuel entry statement
              then_statement else_statement then_exit else_exit view
              then_certificate else_certificate open_equal atomic_equal));
        let Hrest_total := fresh "Hrest_total" in
        assert (Hrest_total : suffix_net_totality rest) by
          (apply (IH (PackSuffix cm ctx join_state exit rest));
           [simpl; exact (suffix_rest_measure_decreases
              (Atomicity.CertConditional cm ctx fuel entry statement
                then_statement else_statement then_exit else_exit view
                then_certificate else_certificate open_equal atomic_equal)
              rest)
           |exact Hrest_wf]);
        exact (net_total_conditional_head view then_certificate
          else_certificate open_equal atomic_equal Hwf Hthen_total Helse_total
          Hrest_total)
    end.
Qed.

Theorem traced_net_totality_complete (cost : Atomicity.cost_model)
    (Γ : context) (packed : packed_suffix cost Γ) :
    Atomicity.state_wf (packed_entry _ _ packed) ->
    traced_suffix_net_totality (packed_tree _ _ packed).
Proof.
  induction packed as [packed IH] using
    (well_founded_induction_type
      (well_founded_ltof (packed_suffix cost Γ) packed_suffix_measure)).
  destruct packed as [entry exit suffix]. simpl in *.
  intros Hwf.
  destruct suffix as [entry|fuel entry statement middle exit certificate rest].
  - exact traced_net_total_suffix_done.
  - dependent destruction certificate.
    all: try match goal with
    | |- traced_suffix_net_totality
        (SuffixCons
          (Atomicity.CertLeaf ?cm ?ctx ?fuel ?entry ?statement ?middle
            ?view ?step) ?rest) =>
        let Hrest_wf := fresh "Hrest_wf" in
        assert (Hrest_wf : Atomicity.state_wf middle) by exact
          (Atomicity.certificate_preserves_wf cm entry statement middle Hwf
            (Atomicity.CertLeaf cm ctx fuel entry statement middle view step));
        let Hrest_total := fresh "Hrest_total" in
        assert (Hrest_total : traced_suffix_net_totality rest) by
          (apply (IH (PackSuffix cm ctx middle exit rest));
           [simpl; exact (suffix_rest_measure_decreases
              (Atomicity.CertLeaf cm ctx fuel entry statement middle view step)
              rest)|exact Hrest_wf]);
        exact (traced_net_total_leaf_head view step Hwf Hrest_total)
    | |- traced_suffix_net_totality
        (SuffixCons
          (Atomicity.CertUnfold ?cm ?ctx ?fuel ?entry ?statement ?invariant
            ?opened ?view ?step) ?rest) =>
        let Hrest_wf := fresh "Hrest_wf" in
        assert (Hrest_wf : Atomicity.state_wf opened) by exact
          (Atomicity.certificate_preserves_wf cm entry statement opened Hwf
            (Atomicity.CertUnfold cm ctx fuel entry statement invariant opened
              view step));
        let Hrest_total := fresh "Hrest_total" in
        assert (Hrest_total : traced_suffix_net_totality rest) by
          (apply (IH (PackSuffix cm ctx opened exit rest));
           [simpl; exact (suffix_rest_measure_decreases
              (Atomicity.CertUnfold cm ctx fuel entry statement invariant
                opened view step) rest)|exact Hrest_wf]);
        exact (traced_net_total_unfold_head view step Hwf Hrest_total)
    | |- traced_suffix_net_totality
        (SuffixCons
          (Atomicity.CertFold ?cm ?ctx ?fuel ?entry ?statement ?invariant
            ?view) ?rest) =>
        let folded := constr:(Atomicity.fold_invariant invariant entry) in
        let Hrest_wf := fresh "Hrest_wf" in
        assert (Hrest_wf : Atomicity.state_wf folded) by exact
          (Atomicity.certificate_preserves_wf cm entry statement folded Hwf
            (Atomicity.CertFold cm ctx fuel entry statement invariant view));
        let Hrest_total := fresh "Hrest_total" in
        assert (Hrest_total : traced_suffix_net_totality rest) by
          (apply (IH (PackSuffix cm ctx folded exit rest));
           [simpl; exact (suffix_rest_measure_decreases
              (Atomicity.CertFold cm ctx fuel entry statement invariant view)
              rest)|exact Hrest_wf]);
        exact (traced_net_total_fold_head view Hwf Hrest_total)
    | |- traced_suffix_net_totality
        (SuffixCons
          (Atomicity.CertSequence ?cm ?ctx ?fuel ?entry ?statement ?first
            ?middle ?second ?next ?view ?first_certificate
            ?second_certificate) ?rest) =>
        let flat := constr:(expand_sequence_suffix view first_certificate
          second_certificate rest) in
        let Hflat_total := fresh "Hflat_total" in
        assert (Hflat_total : traced_suffix_net_totality flat) by
          (apply (IH (PackSuffix cm ctx entry exit flat));
           [simpl; exact (expand_sequence_suffix_measure_decreases view
              first_certificate second_certificate rest)|exact Hwf]);
        exact (traced_net_total_sequence_head view first_certificate
          second_certificate rest Hflat_total)
    | |- traced_suffix_net_totality
        (SuffixCons
          (Atomicity.CertAtomic ?cm ?ctx ?fuel ?entry ?statement ?body ?outer
            ?inner ?view ?step ?body_certificate ?open_equal) ?rest) =>
        let middle_state := constr:(Atomicity.AnalysisState
          (Atomicity.analysis_mask inner) (Atomicity.analysis_open inner)
          (Atomicity.analysis_step_taken outer ||
            Atomicity.analysis_step_taken inner)
          (Atomicity.analysis_in_atomic outer)) in
        let Hrest_wf := fresh "Hrest_wf" in
        assert (Hrest_wf : Atomicity.state_wf middle_state) by exact
          (Atomicity.certificate_preserves_wf cm entry statement middle_state
            Hwf (Atomicity.CertAtomic cm ctx fuel entry statement body outer
              inner view step body_certificate open_equal));
        let Hrest_total := fresh "Hrest_total" in
        assert (Hrest_total : traced_suffix_net_totality rest) by
          (apply (IH (PackSuffix cm ctx middle_state exit rest));
           [simpl; exact (suffix_rest_measure_decreases
              (Atomicity.CertAtomic cm ctx fuel entry statement body outer
                inner view step body_certificate open_equal) rest)
           |exact Hrest_wf]);
        exact (traced_net_total_atomic_head view step body_certificate
          open_equal Hwf Hrest_total)
    | |- traced_suffix_net_totality
        (SuffixCons
          (Atomicity.CertConditional ?cm ?ctx ?fuel ?entry ?statement
            ?then_statement ?else_statement ?then_exit ?else_exit ?view
            ?then_certificate ?else_certificate ?open_equal ?atomic_equal)
          ?rest) =>
        let then_suffix := constr:(singleton_suffix then_certificate) in
        let else_suffix := constr:(singleton_suffix else_certificate) in
        let join_state := constr:(Atomicity.AnalysisState
          (Atomicity.analysis_mask then_exit ∩ Atomicity.analysis_mask else_exit)
          (Atomicity.analysis_open then_exit)
          (Atomicity.analysis_step_taken then_exit ||
            Atomicity.analysis_step_taken else_exit)
          (Atomicity.analysis_in_atomic then_exit)) in
        let Hthen_total := fresh "Hthen_total" in
        assert (Hthen_total : traced_suffix_net_totality then_suffix) by
          (apply (IH (PackSuffix cm ctx entry then_exit then_suffix));
           [simpl; exact (conditional_then_measure_decreases view
              then_certificate else_certificate open_equal atomic_equal rest)
           |exact Hwf]);
        let Helse_total := fresh "Helse_total" in
        assert (Helse_total : traced_suffix_net_totality else_suffix) by
          (apply (IH (PackSuffix cm ctx entry else_exit else_suffix));
           [simpl; exact (conditional_else_measure_decreases view
              then_certificate else_certificate open_equal atomic_equal rest)
           |exact Hwf]);
        let Hrest_wf := fresh "Hrest_wf" in
        assert (Hrest_wf : Atomicity.state_wf join_state) by exact
          (Atomicity.certificate_preserves_wf cm entry statement join_state Hwf
            (Atomicity.CertConditional cm ctx fuel entry statement
              then_statement else_statement then_exit else_exit view
              then_certificate else_certificate open_equal atomic_equal));
        let Hrest_total := fresh "Hrest_total" in
        assert (Hrest_total : traced_suffix_net_totality rest) by
          (apply (IH (PackSuffix cm ctx join_state exit rest));
           [simpl; exact (suffix_rest_measure_decreases
              (Atomicity.CertConditional cm ctx fuel entry statement
                then_statement else_statement then_exit else_exit view
                then_certificate else_certificate open_equal atomic_equal)
              rest)
           |exact Hrest_wf]);
        exact (traced_net_total_conditional_head view then_certificate
          else_certificate open_equal atomic_equal Hwf Hthen_total Helse_total
          Hrest_total)
    end.
Qed.

Corollary traced_suffix_net_totality_complete
    {cost Γ entry exit} (suffix : certificate_suffix cost Γ entry exit) :
    Atomicity.state_wf entry -> traced_suffix_net_totality suffix.
Proof.
  exact (traced_net_totality_complete cost Γ
    (PackSuffix cost Γ entry exit suffix)).
Qed.

Corollary suffix_net_totality_complete
    {cost Γ entry exit} (suffix : certificate_suffix cost Γ entry exit) :
    Atomicity.state_wf entry -> suffix_net_totality suffix.
Proof.
  exact (net_totality_complete cost Γ
    (PackSuffix cost Γ entry exit suffix)).
Qed.

(** The first runtime-facing assembly point.  An aligned operational zipper
    already carries its exact LIFO transition; after erasure, traced totality
    therefore produces a normalized net whose source is the very same
    certificate sequence.  Hoare evidence remains in [suffix] for the
    semantic alignment layer below. *)
Module AlignedNormalization
    (Resources : Runtime.RUNTIME_RESOURCES)
    (ProcedureContracts :
      Runtime.Validation.Hoare.PROCEDURE_CONTRACT_COHERENCE Contracts)
    (Leaf : Runtime.DEFAULT_SEMANTIC_LEAF_CONTRACTS Resources Contracts)
    (Defs : Runtime.Translation.DEFINITION_ENV).
  Module Erasure := WithRuntimeValidity Resources ProcedureContracts Leaf Defs.
  Module Validity := Erasure.Validity.
  Module RuntimeCore := Runtime.IR.Core.
  Local Notation iProp := (iProp Resources.Σ).

  (** Concrete CPS interpretation of a normalized trace.  Recursing over the
      provenance proof, rather than over the bare [net_tree], keeps the fixed
      Raven context [Γ] and the exact source statement available to the
      runtime primitives.  A conditional interprets its common continuation
      once and supplies it to both arms. *)
  Fixpoint trace_iris_wp
      {cost Γ entry exit mode tail stack_out source tree}
      (trace : net_trace cost Γ entry exit mode tail stack_out source tree)
      (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (post : iProp) {struct trace} : iProp :=
    match trace with
    | @TraceDoneNet _ _ _ _ => post
    | @TraceDoneFocused _ _ _ _ _ => post
    | @TraceChunk _ _ _ _ _ _ _ _ _ certificate _ _ _ _ Hrest =>
        Validity.Execution.region_wp certificate runtime ambient
          (trace_iris_wp Hrest runtime ambient post)
    | @TraceFocusedPrefix _ _ _ _ _ _ _ _ _ _ certificate _ _ _ _ _
        Hrest =>
        Validity.Execution.region_wp certificate runtime ambient
          (trace_iris_wp Hrest runtime ambient post)
    | @TraceAccess _ _ _ _ _ _ _ _ _ _ certificate _ _ _ _ _ Hbody =>
        Validity.Execution.region_wp certificate runtime ambient
          (trace_iris_wp Hbody runtime ambient post)
    | @TraceNestedAccess _ _ _ _ _ _ _ _ _ _ _ certificate _ _ _ _ _
        Hbody =>
        Validity.Execution.region_wp certificate runtime ambient
          (trace_iris_wp Hbody runtime ambient post)
    | @TraceClose _ _ _ _ _ _ _ _ _ _ certificate _ _ _ _ _ Hrest =>
        Validity.Execution.region_wp certificate runtime ambient
          (trace_iris_wp Hrest runtime ambient post)
    | @TraceFocusedClose _ _ _ _ _ _ _ _ _ _ certificate _ _ _ _ _
        Hrest =>
        Validity.Execution.region_wp certificate runtime ambient
          (trace_iris_wp Hrest runtime ambient post)
    | @TraceConditional _ _ _ entry statement _ _ then_exit else_exit _ _ _
        _ _ _ _ _ _ _ _ _ _ Hthen Helse Hrest =>
        let shared := trace_iris_wp Hrest runtime ambient post in
        Validity.Execution.Primitives.branch_wp runtime ambient entry statement
          then_exit else_exit
          (trace_iris_wp Hthen runtime ambient shared)
          (trace_iris_wp Helse runtime ambient shared)
    | @TraceFocusedConditional _ _ _ entry statement _ _ then_exit else_exit
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hthen Helse Hrest =>
        let shared := trace_iris_wp Hrest runtime ambient post in
        Validity.Execution.Primitives.branch_wp runtime ambient entry statement
          then_exit else_exit
          (trace_iris_wp Hthen runtime ambient shared)
          (trace_iris_wp Helse runtime ambient shared)
    | @TraceFocusedConditionalContinue _ _ _ entry statement _ _ then_exit
        else_exit _ _ _ _ _ _ _ _ _ _ _ _ _ Hthen Helse Hrest =>
        let shared := trace_iris_wp Hrest runtime ambient post in
        Validity.Execution.Primitives.branch_wp runtime ambient entry statement
          then_exit else_exit
          (trace_iris_wp Hthen runtime ambient shared)
          (trace_iris_wp Helse runtime ambient shared)
    | @TraceExpansion _ _ _ _ _ _ _ _ _ _ _ Hflat =>
        trace_iris_wp Hflat runtime ambient post
    end.

  (** Runtime-facing form of the interpretation.  The aligned suffix is an
      explicit argument even though the denotation computes from its trace:
      its proof-relevant Hoare derivations are the evidence consumed by the
      validity theorem, while the normalization index guarantees that both
      objects describe exactly the same certificate zipper. *)
  Definition aligned_trace_iris_wp
      {cost Γ F Δ entry pre stack_in exit post_assertion stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre
        stack_in exit post_assertion stack_out)
      (normal : @traced_suffix_net_normalization cost Γ entry exit stack_in
        stack_out
        (Erasure.certificate_suffix_of_aligned_operational_suffix suffix))
      (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (post : iProp) : iProp :=
    trace_iris_wp (traced_net_source _ normal) runtime ambient post.

  Lemma trace_iris_wp_mono
      {cost Γ entry exit mode tail stack_out source tree}
      (trace : net_trace cost Γ entry exit mode tail stack_out source tree)
      (runtime : Validity.Model.stack_context Γ) ambient (P Q : iProp) :
    (P ⊢ Q) ->
    trace_iris_wp trace runtime ambient P ⊢
      trace_iris_wp trace runtime ambient Q.
  Proof.
    revert P Q. induction trace; intros P Q HPQ; simpl.
    - exact HPQ.
    - exact HPQ.
    - apply Validity.Execution.region_wp_mono.
      exact (IHtrace P Q HPQ).
    - apply Validity.Execution.region_wp_mono.
      exact (IHtrace P Q HPQ).
    - apply Validity.Execution.region_wp_mono.
      exact (IHtrace P Q HPQ).
    - apply Validity.Execution.region_wp_mono.
      exact (IHtrace P Q HPQ).
    - apply Validity.Execution.region_wp_mono.
      exact (IHtrace P Q HPQ).
    - apply Validity.Execution.region_wp_mono.
      exact (IHtrace P Q HPQ).
    - apply Validity.Execution.Primitives.Interface.branch_mono.
      + apply IHtrace1. apply IHtrace3. exact HPQ.
      + apply IHtrace2. apply IHtrace3. exact HPQ.
    - apply Validity.Execution.Primitives.Interface.branch_mono.
      + apply IHtrace1. apply IHtrace3. exact HPQ.
      + apply IHtrace2. apply IHtrace3. exact HPQ.
    - apply Validity.Execution.Primitives.Interface.branch_mono.
      + apply IHtrace1. apply IHtrace3. exact HPQ.
      + apply IHtrace2. apply IHtrace3. exact HPQ.
    - exact (IHtrace P Q HPQ).
  Qed.

  Fixpoint suffix_iris_wp {cost Γ entry exit}
      (suffix : certificate_suffix cost Γ entry exit)
      (runtime : Validity.Model.stack_context Γ) (ambient : coPset)
      (post : iProp) : iProp :=
    match suffix with
    | SuffixDone _ => post
    | SuffixCons certificate rest =>
        Validity.Execution.region_wp certificate runtime ambient
          (suffix_iris_wp rest runtime ambient post)
    end.

  Lemma suffix_expands_iris_wp
      {cost Γ entry exit flat source}
      (expansion : suffix_expands cost Γ entry exit flat source)
      (runtime : Validity.Model.stack_context Γ) ambient post :
    suffix_iris_wp flat runtime ambient post =
      suffix_iris_wp source runtime ambient post.
  Proof.
    induction expansion; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite IHexpansion. reflexivity.
    - rewrite IHexpansion1 IHexpansion2. reflexivity.
  Qed.

  Lemma trace_iris_wp_is_suffix_iris_wp
      {cost Γ entry exit mode tail stack_out source tree}
      (trace : net_trace cost Γ entry exit mode tail stack_out source tree)
      (runtime : Validity.Model.stack_context Γ) ambient post :
    trace_iris_wp trace runtime ambient post =
      suffix_iris_wp source runtime ambient post.
  Proof.
    revert post. induction trace; intros post; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite IHtrace. reflexivity.
    - rewrite IHtrace. reflexivity.
    - rewrite IHtrace. reflexivity.
    - rewrite IHtrace. reflexivity.
    - rewrite IHtrace. reflexivity.
    - rewrite IHtrace. reflexivity.
    - rewrite IHtrace1 IHtrace2 IHtrace3. reflexivity.
    - rewrite IHtrace1 IHtrace2 IHtrace3. reflexivity.
    - rewrite IHtrace1 IHtrace2 IHtrace3. reflexivity.
    - rewrite IHtrace. apply suffix_expands_iris_wp. exact expansion.
  Qed.

  Fixpoint suffix_footprint {cost Γ entry exit}
      (suffix : certificate_suffix cost Γ entry exit) : gset inv_id :=
    match suffix with
    | SuffixDone _ => ∅
    | SuffixCons certificate rest =>
        Atomicity.certificate_footprint certificate ∪ suffix_footprint rest
    end.

  Lemma suffix_footprint_head_subset
      {cost Γ fuel entry statement middle exit}
      (certificate : Atomicity.analysis_certificate cost Γ fuel entry
        statement middle)
      (rest : certificate_suffix cost Γ middle exit) :
    Atomicity.certificate_footprint certificate ⊆
      suffix_footprint (SuffixCons certificate rest).
  Proof. intros invariant Hinvariant. simpl. apply elem_of_union_l. exact Hinvariant. Qed.

  Lemma suffix_footprint_rest_subset
      {cost Γ fuel entry statement middle exit}
      (certificate : Atomicity.analysis_certificate cost Γ fuel entry
        statement middle)
      (rest : certificate_suffix cost Γ middle exit) :
    suffix_footprint rest ⊆
      suffix_footprint (SuffixCons certificate rest).
  Proof. intros invariant Hinvariant. simpl. apply elem_of_union_r. exact Hinvariant. Qed.

  Definition aligned_trace_cps_valid
      {cost Γ F Δ entry pre stack_in exit post_assertion stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre
        stack_in exit post_assertion stack_out)
      (normal : @traced_suffix_net_normalization cost Γ entry exit stack_in
        stack_out
        (Erasure.certificate_suffix_of_aligned_operational_suffix suffix)) :
      Prop :=
    Atomicity.state_wf entry ->
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ) (atoms : Runtime.Core.atom_env)
      (ambient : coPset),
      Validity.Model.runtime_mask
        (suffix_footprint
          (Erasure.certificate_suffix_of_aligned_operational_suffix suffix))
        ⊆ ambient ->
      forall continuation : iProp,
      ((Validity.global_world_context atoms ∗
        Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
          runtime formals binders atoms post_assertion ∗
        Validity.World.access_stack_interp atoms ambient stack_out) ⊢
        continuation) ->
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms pre ∗
       Validity.World.access_stack_interp atoms ambient stack_in) ⊢
      aligned_trace_iris_wp suffix normal runtime ambient continuation.

  Theorem aligned_suffix_iris_wp_valid
      {cost Γ F Δ entry pre stack_in exit post stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre
        stack_in exit post stack_out) :
    Atomicity.state_wf entry ->
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ) (atoms : Runtime.Core.atom_env)
      (ambient : coPset),
      Validity.Model.runtime_mask
        (suffix_footprint
          (Erasure.certificate_suffix_of_aligned_operational_suffix suffix))
        ⊆ ambient ->
      forall continuation : iProp,
      ((Validity.global_world_context atoms ∗
        Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
          runtime formals binders atoms post ∗
        Validity.World.access_stack_interp atoms ambient stack_out) ⊢
        continuation) ->
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms pre ∗
       Validity.World.access_stack_interp atoms ambient stack_in) ⊢
      suffix_iris_wp
        (Erasure.certificate_suffix_of_aligned_operational_suffix suffix)
        runtime ambient continuation.
  Proof.
    induction suffix as [state post stack|fuel entry statement middle pre
      middle_assertion stack_in stack_middle certificate derivation aligned
      lifo final post stack_out rest IHrest].
    - intros _ runtime formals binders atoms ambient _ continuation Hpost.
      simpl. exact Hpost.
    - intros Hwf runtime formals binders atoms ambient Henvelope continuation
        Hpost.
      assert (Hhead_envelope : Validity.Model.runtime_mask
        (Atomicity.certificate_footprint certificate) ⊆ ambient).
      { etrans; last exact Henvelope.
        apply Validity.Model.runtime_mask_mono.
        apply suffix_footprint_head_subset. }
      assert (Hrest_envelope : Validity.Model.runtime_mask
        (suffix_footprint
          (Erasure.certificate_suffix_of_aligned_operational_suffix rest))
        ⊆ ambient).
      { etrans; last exact Henvelope.
        apply Validity.Model.runtime_mask_mono.
        apply suffix_footprint_rest_subset. }
      assert (Hmiddle_wf : Atomicity.state_wf middle).
      { eapply Atomicity.certificate_preserves_wf; eauto. }
      pose proof (Validity.aligned_certificate_valid certificate derivation
        Hwf lifo aligned) as Hhead.
      simpl. iIntros "Hresources".
      iPoseProof (Hhead runtime formals binders atoms ambient Hhead_envelope
        with "Hresources") as "Hhead".
      iApply (Validity.Execution.region_wp_mono with "Hhead").
      iIntros "Hmiddle".
      iApply (IHrest Hmiddle_wf runtime formals binders atoms ambient
        Hrest_envelope continuation Hpost).
      iExact "Hmiddle".
  Qed.

  Theorem aligned_trace_cps_valid_complete
      {cost Γ F Δ entry pre stack_in exit post stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre
        stack_in exit post stack_out)
      (normal : @traced_suffix_net_normalization cost Γ entry exit stack_in
        stack_out
        (Erasure.certificate_suffix_of_aligned_operational_suffix suffix)) :
    aligned_trace_cps_valid suffix normal.
  Proof.
    intros Hwf runtime formals binders atoms ambient Henvelope continuation
      Hpost.
    unfold aligned_trace_iris_wp.
    rewrite trace_iris_wp_is_suffix_iris_wp.
    eapply aligned_suffix_iris_wp_valid; eauto.
  Qed.

  (** The atomic [TraceChunk] case is discharged through the existing
      trusted-atomic certificate rule.  Keeping this helper at the primitive
      operation boundary avoids prematurely committing to the still-pending
      aligned-trace induction (in particular, its sequence-expansion case).
      Its conclusion is definitionally the denotation of a [TraceChunk]
      whose head is [ChunkCertificateAtomic]. *)
  Lemma atomic_trace_chunk_cps_valid
      {cost Γ F Δ fuel entry node body outer inner stack pre post}
      (step : Atomicity.take_step Atomicity.AtomicStep entry = inr outer)
      (body_certificate : Atomicity.analysis_certificate cost Γ fuel
        (Atomicity.AnalysisState (Atomicity.analysis_mask outer)
          (Atomicity.analysis_open outer)
          (Atomicity.analysis_step_taken outer) true) body inner)
      (open_equal : Atomicity.analysis_open inner =
        Atomicity.analysis_open outer)
      (trusted : Contracts.trusted_atomic Γ body)
      (body_valid : Validity.certificate_semantically_valid
        (stack_in := stack) (stack_out := stack) (pre := pre) (post := post)
        body_certificate) :
    forall (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ) (atoms : Runtime.Core.atom_env)
      (ambient : coPset),
      Validity.Model.runtime_mask
        (Atomicity.certificate_footprint
          (Atomicity.CertAtomic cost Γ fuel entry (TAtomic node body) body
            outer inner eq_refl step body_certificate open_equal)) ⊆ ambient ->
      forall continuation : iProp,
      ((Validity.global_world_context atoms ∗
        Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
          runtime formals binders atoms post ∗
        Validity.World.access_stack_interp atoms ambient stack) ⊢
        continuation) ->
      (Validity.global_world_context atoms ∗
       Validity.VSemantics.S.interp_assertion (Leaf.predicates atoms)
         runtime formals binders atoms pre ∗
       Validity.World.access_stack_interp atoms ambient stack) ⊢
      Validity.Execution.region_wp
        (Atomicity.CertAtomic cost Γ fuel entry (TAtomic node body) body
          outer inner eq_refl step body_certificate open_equal)
        runtime ambient continuation.
  Proof.
    intros runtime formals binders atoms ambient Henvelope continuation Hpost.
    pose proof (Validity.atomic_valid (node := node) step body_certificate
      open_equal stack pre post trusted body_valid) as Hatomic.
    iIntros "Hresources".
    iPoseProof (Hatomic runtime formals binders atoms ambient Henvelope
      with "Hresources") as "Hatomic".
    iApply (Validity.Execution.region_wp_mono with "Hatomic").
    iIntros "Hresources". iApply Hpost. iExact "Hresources".
  Qed.

  (** Conditional CPS helper.  The two recursively normalized arms receive
      the *same* continuation; the condition rule only selects an arm and
      does not duplicate or consume that continuation.  Keeping this helper
      at the concrete branch boundary makes it usable for both ordinary and
      focused [TraceConditional] nodes. *)
  Lemma conditional_trace_branch_select
      {Γ F Δ node entry then_statement else_statement then_exit else_exit}
      (runtime : Validity.Model.stack_context Γ)
      (formals : Runtime.Core.formal_env F)
      (binders : Runtime.Core.binder_env Δ)
      (atoms : Runtime.Core.atom_env)
      (store : RuntimeCore.symbolic_store Γ F Δ)
      (frame : iProp)
      (condition : Runtime.IR.pexpr Γ TypedCore.TBool)
      (ambient : coPset) (then_wp else_wp : iProp)
      (Hthen : (Validity.Model.stack_own Γ runtime
          (Runtime.Translation.interp_store formals binders atoms store) ∗ frame ∗
          ⌜RuntimeCore.interp_expr formals binders atoms
            (Runtime.Validation.Hoare.symbolize_expr store condition) =
            Some (RuntimeCore.VBool true)⌝) ⊢ then_wp)
      (Helse : (Validity.Model.stack_own Γ runtime
          (Runtime.Translation.interp_store formals binders atoms store) ∗ frame ∗
          ⌜RuntimeCore.interp_expr formals binders atoms
            (Runtime.Validation.Hoare.symbolize_expr store condition) <>
            Some (RuntimeCore.VBool true)⌝) ⊢ else_wp) :
      (Validity.Model.stack_own Γ runtime
        (Runtime.Translation.interp_store formals binders atoms store) ∗ frame) ⊢
      Validity.Execution.Primitives.branch_wp runtime ambient entry
        (Runtime.IR.TIf node condition then_statement else_statement)
        then_exit else_exit
        then_wp else_wp.
  Proof.
    unfold Validity.Execution.Primitives.branch_wp. simpl.
    apply (Validity.BaseExecution.Primitives.branch_select Γ F Δ runtime
      formals binders atoms store frame condition
      (Atomicity.analysis_mask entry) then_wp else_wp).
    - exact Hthen.
    - exact Helse.
  Qed.

  Definition aligned_suffix_traced_normalization
      {cost Γ F Δ entry pre stack_in exit post stack_out}
      (suffix : Erasure.Validity.aligned_operational_suffix cost Γ F Δ
        entry pre stack_in exit post stack_out) :
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry)
      stack_in ->
    @has_traced_suffix_net_normalization cost Γ entry exit stack_in stack_out
      (Erasure.certificate_suffix_of_aligned_operational_suffix suffix).
  Proof.
    intros Hwf Hstack.
    apply (traced_total_net _
      (traced_suffix_net_totality_complete
        (Erasure.certificate_suffix_of_aligned_operational_suffix suffix) Hwf)
      stack_in stack_out Hwf Hstack).
    exact (Erasure.certificate_suffix_of_aligned_operational_suffix_has_lifo
      suffix).
  Defined.

  Theorem aligned_suffix_has_valid_trace
      {cost Γ F Δ entry pre stack_in exit post stack_out}
      (suffix : Validity.aligned_operational_suffix cost Γ F Δ entry pre
        stack_in exit post stack_out) :
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry)
      stack_in ->
    exists normal : @traced_suffix_net_normalization cost Γ entry exit
      stack_in stack_out
      (Erasure.certificate_suffix_of_aligned_operational_suffix suffix),
      aligned_trace_cps_valid suffix normal.
  Proof.
    intros Hwf Hstack.
    destruct (aligned_suffix_traced_normalization suffix Hwf Hstack)
      as [normal _].
    exists normal. apply aligned_trace_cps_valid_complete.
  Qed.
End AlignedNormalization.

Lemma component_properties_from_total :
  total_suffix_normalization_property ->
  empty_suffix_normalization_property /\
  outcome_suffix_normalization_property /\
  focused_suffix_decomposition_property.
Proof.
  intros Htotal. split.
  - unfold empty_suffix_normalization_property.
    intros cost Γ entry exit suffix Hwf Hstack Hlifo.
    exact (total_empty suffix (Htotal cost Γ entry exit suffix)
      Hwf Hstack Hlifo).
  - split.
    + unfold outcome_suffix_normalization_property.
      intros cost Γ entry exit suffix invariant outer tail Hwf Hstack Hlifo.
      exact (total_outcome suffix (Htotal cost Γ entry exit suffix)
        invariant outer tail Hwf Hstack Hlifo).
    + unfold focused_suffix_decomposition_property.
      intros cost Γ entry exit suffix invariant outer tail Hwf Hstack Hlifo.
      destruct (total_close suffix (Htotal cost Γ entry exit suffix)
        invariant outer tail tail Hwf Hstack (stack_suffix_refl tail) Hlifo)
        as [split _].
      pose (normal := close_normalization_of_split split).
      exists {| suffix_focused_lifo := suffix_close_lifo _ normal;
        suffix_first_close := suffix_close_state _ normal;
        suffix_focused_tree := suffix_close_tree _ normal;
        suffix_post_close := suffix_after_close _ normal |}.
      exact I.
Qed.

Lemma balanced_suffix_from_empty_and_outcome :
  empty_suffix_normalization_property ->
  outcome_suffix_normalization_property ->
  balanced_suffix_normalization_property.
Proof.
  intros Hempty Houtcome cost Γ entry exit suffix stack Hwf Hstack Hlifo.
  destruct stack as [|[invariant outer] tail].
  - apply Hempty; assumption.
  - destruct (Houtcome cost Γ entry exit suffix invariant outer tail
      Hwf Hstack Hlifo)
      as [normal _].
    exists (normalize_suffix_outcome normal). exact I.
Qed.

(** Public single-certificate corollary.  The mixed conditional constructor
    now handles a branch which closes and reopens before the join while the
    other branch remains open until the common continuation. *)
Definition focused_decomposition_property : Prop :=
  forall cost Γ fuel entry statement exit invariant outer tail
    (certificate : Atomicity.analysis_certificate cost Γ fuel entry
      statement exit),
    Atomicity.state_wf entry ->
    Atomicity.access_stack_consistent (Atomicity.analysis_open entry)
      ((invariant, outer) :: tail) ->
    Atomicity.lifo_certificate certificate
      ((invariant, outer) :: tail) tail ->
    exists _ : @focused_normalization cost Γ fuel entry statement exit
      invariant outer tail certificate, True.

Lemma focused_decomposition_from_suffix :
  focused_suffix_decomposition_property -> focused_decomposition_property.
Proof.
  intros Hnormalize cost Γ fuel entry statement exit invariant outer tail
    certificate Hwf Hstack Hlifo.
  destruct (Hnormalize cost Γ entry exit (singleton_suffix certificate)
    invariant outer tail Hwf Hstack) as [normal _].
  { apply (proj2 (singleton_suffix_lifo certificate _ _)). exact Hlifo. }
  exists (focused_normalization_of_singleton normal). exact I.
Qed.

End WithContracts.
End Make.
