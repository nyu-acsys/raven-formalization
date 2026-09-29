From Coq Require Import Lia Program.Equality ProofIrrelevance.
From Coq Require Bool.
From stdpp Require Import gmap countable.

From raven Require Import verification.expressions.

(** A small boundary between an intrinsically typed statement
    family and the atomicity analyzer.  The analyzer never needs the payload
    of leaves or conditions, and names invariant applications only by their
    keys; it needs only this control view while retaining the original
    statement opaquely. *)
Module AnalysisView.

Import Core.

Section Instances.

(** ** Invariant instances

    An invariant argument is named by an atom when it is a local, by its
    de Bruijn level (stable across nested scopes), or a literal.  An
    application with an argument of another form has no key and is covered
    only by a declaration-wide mask entry. *)
Inductive key_atom :=
| AtomLevel (level : nat)
| AtomBool (value : bool)
| AtomInt (value : Z)
| AtomUnit.

#[global] Instance key_atom_eq_decision : EqDecision key_atom.
Proof. solve_decision. Defined.

#[global] Program Instance key_atom_countable : Countable key_atom :=
  inj_countable'
    (fun atom => match atom with
      | AtomLevel level => inl level
      | AtomBool value => inr (inl value)
      | AtomInt value => inr (inr (inl value))
      | AtomUnit => inr (inr (inr ()))
      end)
    (fun code => match code with
      | inl level => AtomLevel level
      | inr (inl value) => AtomBool value
      | inr (inr (inl value)) => AtomInt value
      | inr (inr (inr _)) => AtomUnit
      end) _.
Next Obligation. intros []; reflexivity. Qed.

(** The key of an invariant application, if all its arguments are atoms. *)
Definition access_key : Type := option (list key_atom).

(** An available invariant: [(I, None)] covers every instance of [I],
    [(I, Some key)] exactly the instance [key]. *)
Definition mask_entry : Type := (inv_id * access_key)%type.

(** An open invariant: its declaration and key, and the mask entry consumed
    by opening it. *)
Definition open_record : Type := (inv_id * access_key * mask_entry)%type.

Definition record_invariant (record : open_record) : inv_id := record.1.1.
Definition record_key (record : open_record) : access_key := record.1.2.
Definition record_consumed (record : open_record) : mask_entry := record.2.

Definition key_mentions (level : nat) (key : access_key) : bool :=
  match key with
  | Some atoms => bool_decide (AtomLevel level ∈ atoms)
  | None => false
  end.

Definition entry_mentions (level : nat) (entry : mask_entry) : bool :=
  key_mentions level entry.2.

Definition record_mentions (level : nat) (record : open_record) : bool :=
  key_mentions level (record_key record) ||
  entry_mentions level (record_consumed record).

(** The declarations of a set of entries. *)
Definition entry_declarations (entries : gset mask_entry) : gset inv_id :=
  set_map fst entries.

(** Declaration-wide entries for a set of declarations. *)
Definition declaration_entries (declarations : gset inv_id) :
    gset mask_entry :=
  set_map (fun invariant => (invariant, None)) declarations.

Definition entry_covered (entry : mask_entry) (entries : gset mask_entry) :
    Prop :=
  entry ∈ entries \/ (entry.1, None) ∈ entries.

#[global] Instance entry_covered_decision entry entries :
  Decision (entry_covered entry entries).
Proof. unfold entry_covered. apply _. Defined.

(** The entries available on both sides of a join, each at the more precise
    of the two coverings. *)
Definition entries_meet (left right : gset mask_entry) : gset mask_entry :=
  filter (fun entry => entry_covered entry left /\ entry_covered entry right)
    (left ∪ right).

End Instances.


Inductive statement_view (statement : decl_context -> Type) (Γ : decl_context) : Type :=
| ViewLeaf
(* The empty continuation.  Unlike a leaf it is never charged a cost: it is
   the identity on the analysis state by construction. *)
| ViewDone
| ViewUnfold (invariant : inv_id) (key : access_key)
| ViewFold (invariant : inv_id) (key : access_key)
| ViewSequence (first second : statement Γ)
| ViewConditional (then_branch else_branch : statement Γ)
| ViewStructuredAccess (invariant : inv_id) (body : statement Γ)
| ViewAtomic (body : statement Γ)
(* A scope for a new local; the analysis state is unaffected by it. *)
| ViewScope (d : decl) (body : statement (d :: Γ)).

Arguments ViewLeaf {_ _}.
Arguments ViewDone {_ _}.
Arguments ViewUnfold {_ _} _ _.
Arguments ViewFold {_ _} _ _.
Arguments ViewSequence {_ _} _ _.
Arguments ViewConditional {_ _} _ _.
Arguments ViewStructuredAccess {_ _} _ _.
Arguments ViewAtomic {_ _} _.
Arguments ViewScope {_ _} _ _.

(** A statement family together with its control view: the analyzer's
    whole interface to a language. *)
Class AnalysisSyntax := AnalysisSyntaxData {
  syntax_statement : decl_context -> Type;
  syntax_view : forall Γ, syntax_statement Γ -> statement_view syntax_statement Γ;
  syntax_size : forall Γ, syntax_statement Γ -> nat;
  syntax_size_positive : forall Γ (statement : syntax_statement Γ),
    0 < syntax_size Γ statement;
  syntax_sequence_children_smaller : forall Γ statement first second,
    syntax_view Γ statement = ViewSequence first second ->
    syntax_size Γ first < syntax_size Γ statement /\
    syntax_size Γ second < syntax_size Γ statement;
  syntax_conditional_children_smaller :
    forall Γ statement then_branch else_branch,
    syntax_view Γ statement = ViewConditional then_branch else_branch ->
    syntax_size Γ then_branch < syntax_size Γ statement /\
    syntax_size Γ else_branch < syntax_size Γ statement;
  syntax_atomic_body_smaller : forall Γ statement body,
    syntax_view Γ statement = ViewAtomic body ->
    syntax_size Γ body < syntax_size Γ statement;
  syntax_scope_body_smaller : forall Γ statement d body,
    syntax_view Γ statement = ViewScope d body ->
    syntax_size (d :: Γ) body < syntax_size Γ statement;
}.



Section WithSyntax.
Context {Syntax : AnalysisSyntax}.

Inductive step_cost :=
| NoStep
| AtomicStep
| NonAtomicStep
| ProcedureCallStep (required granted : gset inv_id)
| ProcedureSpawnStep (required : gset inv_id).

Inductive analysis_error :=
| MissingInvariant (invariant : inv_id)
| ReentrantInvariant (invariant : inv_id)
| NonLifoFold (invariant : inv_id)
| SecondAtomicStep
| NonAtomicWhileOpen
| MissingProcedureMask
| ProcedureGrantAlreadyOpen
| AtomicBlockLeaksAccess
| ScopeLeaksAccess
| StructuredAccessRequiresCertificate
| IncompatibleBranches
| FuelExhausted.

(** The analysis state: the available mask entries, the stack of open
    invariants (innermost first), whether the open accesses have taken
    their physical step, and whether the analysis is inside a trusted
    atomic block. *)
Record analysis_state := AnalysisState {
  analysis_entries : gset mask_entry;
  analysis_records : list open_record;
  analysis_step_taken : bool;
  analysis_in_atomic : bool;
}.

(** The open declarations. *)
Definition analysis_open (state : analysis_state) : gset inv_id :=
  list_to_set (map record_invariant (analysis_records state)).

(** The available declarations. *)
Definition analysis_mask (state : analysis_state) : gset inv_id :=
  entry_declarations (analysis_entries state) ∖ analysis_open state.

(** At most one instance of a declaration is open. *)
Definition state_wf state : Prop :=
  NoDup (map record_invariant (analysis_records state)).

(** Replaces the derived declaration sets in the goal by variables, for
    [set_solver]. *)
Ltac abstract_declarations :=
  repeat match goal with
  | |- context [entry_declarations ?entries] =>
      generalize (entry_declarations entries); intro
  | |- context [list_to_set (map record_invariant ?records)] =>
      generalize (list_to_set (map record_invariant records) : gset inv_id);
      intro
  end.

Definition take_plain_step cost state : analysis_error + analysis_state :=
  if analysis_in_atomic state || bool_decide (analysis_open state = ∅) then
    inr state
  else match cost with
  | NoStep => inr state
  | AtomicStep =>
      if analysis_step_taken state then inl SecondAtomicStep
      else inr (AnalysisState (analysis_entries state) (analysis_records state)
        true false)
  | NonAtomicStep => inl NonAtomicWhileOpen
  | ProcedureCallStep _ _ | ProcedureSpawnStep _ => inl NonAtomicWhileOpen
  end.

Definition grant_state (granted : gset inv_id) state : analysis_state :=
  AnalysisState (analysis_entries state ∪ declaration_entries granted)
    (analysis_records state) (analysis_step_taken state)
    (analysis_in_atomic state).

Definition take_step cost state : analysis_error + analysis_state :=
  match cost with
  | ProcedureCallStep required granted =>
      if bool_decide (required ⊆ analysis_mask state) then
        if bool_decide (analysis_open state = ∅) then
          match take_plain_step NonAtomicStep state with
          | inl error => inl error
          | inr stepped =>
              if bool_decide (granted ## analysis_open stepped)
              then inr (grant_state granted stepped)
              else inl ProcedureGrantAlreadyOpen
          end
        else inl NonAtomicWhileOpen
      else inl MissingProcedureMask
  | ProcedureSpawnStep required =>
      if bool_decide (required ⊆ analysis_mask state)
      then if bool_decide (analysis_open state = ∅)
        then take_plain_step NonAtomicStep state
        else inl NonAtomicWhileOpen
      else inl MissingProcedureMask
  | NoStep | AtomicStep | NonAtomicStep => take_plain_step cost state
  end.

#[global] Arguments take_step : simpl never.

(** The entry an opening consumes: the exact instance if available,
    otherwise the declaration-wide entry. *)
Definition select_entry (invariant : inv_id) (key : access_key)
    (entries : gset mask_entry) : option mask_entry :=
  if bool_decide (key <> None /\ (invariant, key) ∈ entries)
  then Some (invariant, key)
  else if bool_decide ((invariant, None) ∈ entries)
  then Some (invariant, None)
  else None.

Definition open_invariant (invariant : inv_id) (key : access_key) state :
    analysis_error + analysis_state :=
  if bool_decide (invariant ∈ analysis_open state) then
    inl (ReentrantInvariant invariant)
  else match select_entry invariant key (analysis_entries state) with
  | Some entry =>
      inr (AnalysisState (analysis_entries state ∖ {[entry]})
        ((invariant, key, entry) :: analysis_records state)
        (analysis_step_taken state) (analysis_in_atomic state))
  | None => inl (MissingInvariant invariant)
  end.

(** A fold closes the innermost open invariant, restoring the entry it
    consumed, or allocates a fresh instance. *)
Definition fold_invariant (invariant : inv_id) (key : access_key) state :
    analysis_state :=
  match analysis_records state with
  | record :: rest =>
      if decide (record_invariant record = invariant) then
        AnalysisState ({[record_consumed record]} ∪ analysis_entries state) rest
          (match rest with [] => false | _ => analysis_step_taken state end)
          (analysis_in_atomic state)
      else AnalysisState ({[(invariant, key)]} ∪ analysis_entries state)
        (analysis_records state) (analysis_step_taken state)
        (analysis_in_atomic state)
  | [] =>
      AnalysisState ({[(invariant, key)]} ∪ analysis_entries state)
        (analysis_records state) (analysis_step_taken state)
        (analysis_in_atomic state)
  end.

(** A fold names the innermost open instance, or an invariant that is not
    open. *)
Definition fold_admissible (invariant : inv_id) (key : access_key) state :
    bool :=
  match analysis_records state with
  | record :: _ =>
      if decide (record_invariant record = invariant)
      then bool_decide (record_key record = key)
      else bool_decide (invariant ∉ analysis_open state)
  | [] => true
  end.

(** Leaving the scope of the local at [level], entered in [outer], forgets
    the entries naming it that were not available on entry; no open
    invariant may name it. *)
Definition leave_scope (level : nat) (outer state : analysis_state) :
    analysis_state :=
  AnalysisState
    (filter (fun entry => entry_mentions level entry = false \/
        entry ∈ analysis_entries outer)
      (analysis_entries state))
    (analysis_records state) (analysis_step_taken state)
    (analysis_in_atomic state).

Definition leave_scope_admissible (level : nat) state : bool :=
  forallb (fun record => negb (record_mentions level record))
    (analysis_records state).

Lemma analysis_open_records (left right : analysis_state) :
  analysis_records left = analysis_records right ->
  analysis_open left = analysis_open right.
Proof. unfold analysis_open. intros ->. reflexivity. Qed.

Lemma analysis_open_cons record rest (state : analysis_state) :
  analysis_records state = record :: rest ->
  analysis_open state =
    {[record_invariant record]} ∪ list_to_set (map record_invariant rest).
Proof. unfold analysis_open. intros ->. reflexivity. Qed.

Lemma analysis_open_empty (state : analysis_state) :
  analysis_open state = ∅ <-> analysis_records state = [].
Proof.
  unfold analysis_open. destruct (analysis_records state) as [|record rest];
    cbn; split; intros H; try reflexivity; try discriminate.
  exfalso. assert (record_invariant record ∈ (∅ : gset inv_id)) as Hin.
  { rewrite <- H. set_solver. }
  set_solver.
Qed.

Lemma take_plain_step_preserves_state cost state exit :
  take_plain_step cost state = inr exit ->
  analysis_entries exit = analysis_entries state /\
  analysis_records exit = analysis_records state.
Proof.
  unfold take_plain_step.
  destruct (analysis_in_atomic state ||
    bool_decide (analysis_open state = ∅)); first by intros [= <-].
  destruct cost; try by intros [= <-]; try discriminate.
  destruct (analysis_step_taken state); first discriminate.
  intros Hinr. inversion Hinr. done.
Qed.

Lemma take_plain_step_preserves_sets cost state exit :
  take_plain_step cost state = inr exit ->
  analysis_mask exit = analysis_mask state /\
  analysis_open exit = analysis_open state.
Proof.
  intros Hstep. apply take_plain_step_preserves_state in Hstep as
    [Hentries Hrecords].
  unfold analysis_mask, analysis_open. rewrite Hentries, Hrecords. done.
Qed.

Lemma take_step_preserves_records cost state exit :
  take_step cost state = inr exit ->
  analysis_records exit = analysis_records state.
Proof.
  unfold take_step.
  destruct cost; try (intros Hstep;
    exact (proj2 (take_plain_step_preserves_state _ _ _ Hstep))).
  - destruct (bool_decide (_ ⊆ _)); last discriminate.
    destruct (bool_decide (analysis_open state = ∅)); last discriminate.
    destruct (take_plain_step NonAtomicStep state) as [error|stepped]
      eqn:Hstep; first discriminate.
    destruct (bool_decide (_ ## _)); last discriminate.
    intros [= <-]. simpl.
    exact (proj2 (take_plain_step_preserves_state _ _ _ Hstep)).
  - destruct (bool_decide (_ ⊆ _)); last discriminate.
    destruct (bool_decide (analysis_open state = ∅)); last discriminate.
    intros Hstep. exact (proj2 (take_plain_step_preserves_state _ _ _ Hstep)).
Qed.

Lemma take_step_preserves_open cost state exit :
  take_step cost state = inr exit ->
  analysis_open exit = analysis_open state.
Proof.
  intros Hstep. apply analysis_open_records.
  exact (take_step_preserves_records _ _ _ Hstep).
Qed.

Lemma take_plain_step_preserves_in_atomic cost state exit :
  take_plain_step cost state = inr exit ->
  analysis_in_atomic exit = analysis_in_atomic state.
Proof.
  unfold take_plain_step.
  destruct (analysis_in_atomic state ||
    bool_decide (analysis_open state = ∅)) eqn:Hallowed;
    first by intros [= <-].
  apply Bool.orb_false_iff in Hallowed as [Hin_atomic _].
  destruct cost; try by intros [= <-]; try discriminate.
  destruct (analysis_step_taken state); first discriminate.
  intros [= <-]. simpl. symmetry. exact Hin_atomic.
Qed.

Lemma take_step_preserves_in_atomic cost state exit :
  take_step cost state = inr exit ->
  analysis_in_atomic exit = analysis_in_atomic state.
Proof.
  unfold take_step. destruct cost;
    try (apply take_plain_step_preserves_in_atomic; assumption).
  - destruct (bool_decide (_ ⊆ _)); last discriminate.
    destruct (bool_decide (analysis_open state = ∅)); last discriminate.
    destruct (take_plain_step NonAtomicStep state) as [error|stepped]
      eqn:Hplain; first discriminate.
    destruct (bool_decide (_ ## _)); last discriminate.
    intros [= <-]. simpl.
    exact (take_plain_step_preserves_in_atomic _ _ _ Hplain).
  - destruct (bool_decide (_ ⊆ _)); last discriminate.
    destruct (bool_decide (analysis_open state = ∅)); last discriminate.
    apply take_plain_step_preserves_in_atomic.
Qed.

Lemma take_step_preserves_wf cost state exit :
  state_wf state -> take_step cost state = inr exit -> state_wf exit.
Proof.
  intros Hwf Hstep. unfold state_wf.
  rewrite (take_step_preserves_records _ _ _ Hstep). exact Hwf.
Qed.

Lemma entry_declarations_union left right :
  entry_declarations (left ∪ right) =
    entry_declarations left ∪ entry_declarations right.
Proof. unfold entry_declarations. apply set_map_union_L. Qed.

Lemma entry_declarations_singleton (entry : mask_entry) :
  entry_declarations {[entry]} = {[entry.1]}.
Proof. unfold entry_declarations. apply set_map_singleton_L. Qed.

Lemma entry_declarations_declaration_entries declarations :
  entry_declarations (declaration_entries declarations) = declarations.
Proof.
  unfold entry_declarations, declaration_entries. apply set_eq.
  intros invariant. split.
  - intros Hin. apply elem_of_map in Hin as (entry & -> & Hentry).
    apply elem_of_map in Hentry as (invariant' & -> & Hin'). exact Hin'.
  - intros Hin. apply elem_of_map. exists (invariant, None).
    split; [reflexivity|]. apply elem_of_map. exists invariant.
    split; [reflexivity|exact Hin].
Qed.

Lemma procedure_call_step_success required granted state exit :
  take_step (ProcedureCallStep required granted) state = inr exit ->
  required ⊆ analysis_mask state /\
  granted ## analysis_open state /\
  analysis_mask exit = analysis_mask state ∪ granted /\
  analysis_open exit = analysis_open state.
Proof.
  unfold take_step.
  destruct (bool_decide (required ⊆ analysis_mask state)) eqn:Hrequired;
    last discriminate.
  apply bool_decide_eq_true in Hrequired.
  destruct (bool_decide (analysis_open state = ∅)) eqn:Hclosed;
    last discriminate.
  apply bool_decide_eq_true in Hclosed.
  destruct (take_plain_step NonAtomicStep state) as [error|stepped]
    eqn:Hplain; first discriminate.
  destruct (bool_decide (granted ## analysis_open stepped)) eqn:Hgrant;
    last discriminate.
  apply bool_decide_eq_true in Hgrant. intros [= <-].
  apply take_plain_step_preserves_state in Hplain as [Hentries Hrecords].
  assert (Hopen : analysis_open stepped = analysis_open state)
    by (apply analysis_open_records; exact Hrecords).
  rewrite Hopen in Hgrant. repeat split; try assumption.
  unfold analysis_mask, grant_state, analysis_open in *. cbn.
  rewrite Hentries, Hrecords, entry_declarations_union,
    entry_declarations_declaration_entries, Hclosed.
  set_solver.
Qed.

Lemma procedure_call_step_success_closed required granted state exit :
  take_step (ProcedureCallStep required granted) state = inr exit ->
  analysis_open state = ∅.
Proof.
  unfold take_step.
  destruct (bool_decide (required ⊆ analysis_mask state)); last discriminate.
  destruct (bool_decide (analysis_open state = ∅)) eqn:Hclosed;
    last discriminate.
  intros _. apply bool_decide_eq_true in Hclosed. exact Hclosed.
Qed.

Lemma procedure_spawn_step_success required state exit :
  take_step (ProcedureSpawnStep required) state = inr exit ->
  required ⊆ analysis_mask state /\
  analysis_mask exit = analysis_mask state /\
  analysis_open exit = analysis_open state.
Proof.
  unfold take_step.
  destruct (bool_decide (required ⊆ analysis_mask state)) eqn:Hrequired;
    last discriminate.
  apply bool_decide_eq_true in Hrequired.
  destruct (bool_decide (analysis_open state = ∅)); last discriminate.
  intros Hplain.
  apply take_plain_step_preserves_sets in Hplain as [Hmask Hopen].
  tauto.
Qed.

Lemma procedure_spawn_step_success_closed required state exit :
  take_step (ProcedureSpawnStep required) state = inr exit ->
  analysis_open state = ∅.
Proof.
  unfold take_step.
  destruct (bool_decide (required ⊆ analysis_mask state)); last discriminate.
  destruct (bool_decide (analysis_open state = ∅)) eqn:Hclosed;
    last discriminate.
  intros _. apply bool_decide_eq_true in Hclosed. exact Hclosed.
Qed.

Lemma atomic_step_preserves_sets state exit :
  take_step AtomicStep state = inr exit ->
  analysis_mask exit = analysis_mask state /\
  analysis_open exit = analysis_open state.
Proof. apply take_plain_step_preserves_sets. Qed.

Lemma atomic_step_preserves_state state exit :
  take_step AtomicStep state = inr exit ->
  analysis_entries exit = analysis_entries state /\
  analysis_records exit = analysis_records state.
Proof. apply take_plain_step_preserves_state. Qed.

Lemma take_step_resources_monotone cost state exit :
  take_step cost state = inr exit ->
  analysis_mask state ∪ analysis_open state ⊆
    analysis_mask exit ∪ analysis_open exit.
Proof.
  intros Hstep. destruct cost.
  1-3: apply take_plain_step_preserves_sets in Hstep as [Hmask Hopen];
    now rewrite Hmask, Hopen.
  - apply procedure_call_step_success in Hstep as
      (_ & _ & Hmask & Hopen).
    rewrite Hmask, Hopen. set_solver.
  - apply procedure_spawn_step_success in Hstep as (_ & Hmask & Hopen).
    now rewrite Hmask, Hopen.
Qed.

Lemma take_plain_non_atomic_rejected state :
  analysis_open state ≠ ∅ -> analysis_in_atomic state = false ->
  take_plain_step NonAtomicStep state = inl NonAtomicWhileOpen.
Proof.
  intros Hopen Hin_atomic. unfold take_plain_step.
  rewrite Hin_atomic. simpl. rewrite bool_decide_false; [reflexivity|exact Hopen].
Qed.

Lemma procedure_call_rejected_while_open required granted state exit :
  analysis_open state ≠ ∅ -> analysis_in_atomic state = false ->
  take_step (ProcedureCallStep required granted) state <> inr exit.
Proof.
  intros Hopen _. unfold take_step.
  destruct (bool_decide (required ⊆ analysis_mask state)); last discriminate.
  rewrite bool_decide_false; [discriminate | exact Hopen].
Qed.

Lemma procedure_spawn_rejected_while_open required state exit :
  analysis_open state ≠ ∅ -> analysis_in_atomic state = false ->
  take_step (ProcedureSpawnStep required) state <> inr exit.
Proof.
  intros Hopen _. unfold take_step.
  destruct (bool_decide (required ⊆ analysis_mask state)); last discriminate.
  rewrite bool_decide_false; [discriminate | exact Hopen].
Qed.

(** ** Opening and closing *)

Lemma select_entry_sound invariant key entries entry :
  select_entry invariant key entries = Some entry ->
  entry ∈ entries /\ entry.1 = invariant.
Proof.
  unfold select_entry.
  destruct (bool_decide (key <> None /\ (invariant, key) ∈ entries)) eqn:Hexact.
  - apply bool_decide_eq_true in Hexact as [_ Hin].
    intros [= <-]. auto.
  - destruct (bool_decide ((invariant, None) ∈ entries)) eqn:Hall;
      [|discriminate].
    apply bool_decide_eq_true in Hall. intros [= <-]. auto.
Qed.

Lemma entry_declarations_remove entries (entry : mask_entry) :
  entry ∈ entries ->
  entry_declarations entries ∖ {[entry.1]} ⊆
    entry_declarations (entries ∖ {[entry]}) /\
  entry_declarations (entries ∖ {[entry]}) ⊆ entry_declarations entries.
Proof.
  intros Hin. unfold entry_declarations. split; intros invariant Hmember.
  - apply elem_of_difference in Hmember as [Hmember Hne].
    apply elem_of_map in Hmember as (other & -> & Hother).
    apply elem_of_map. exists other. split; [reflexivity|].
    apply elem_of_difference. split; [exact Hother|].
    intros Heq. apply elem_of_singleton in Heq. subst other.
    apply Hne, elem_of_singleton. reflexivity.
  - apply elem_of_map in Hmember as (other & -> & Hother).
    apply elem_of_difference in Hother as [Hother _].
    apply elem_of_map. exists other. auto.
Qed.

Lemma open_invariant_records invariant key state exit :
  open_invariant invariant key state = inr exit ->
  exists entry,
    select_entry invariant key (analysis_entries state) = Some entry /\
    exit = AnalysisState (analysis_entries state ∖ {[entry]})
      ((invariant, key, entry) :: analysis_records state)
      (analysis_step_taken state) (analysis_in_atomic state).
Proof.
  unfold open_invariant.
  destruct (bool_decide (invariant ∈ analysis_open state)); first discriminate.
  destruct (select_entry invariant key (analysis_entries state)) as [entry|];
    [|discriminate].
  intros [= <-]. eauto.
Qed.

Lemma open_invariant_success invariant key state exit :
  open_invariant invariant key state = inr exit ->
  invariant ∉ analysis_open state /\
  invariant ∈ analysis_mask state /\
  analysis_mask exit = analysis_mask state ∖ {[invariant]} /\
  analysis_open exit = {[invariant]} ∪ analysis_open state.
Proof.
  intros Hopen. pose proof Hopen as Hrecords.
  unfold open_invariant in Hopen.
  destruct (bool_decide (invariant ∈ analysis_open state)) eqn:Hclosed;
    first discriminate.
  apply bool_decide_eq_false in Hclosed.
  destruct (open_invariant_records _ _ _ _ Hrecords) as (entry & Hselect & ->).
  destruct (select_entry_sound _ _ _ _ Hselect) as [Hin Hdecl].
  destruct (entry_declarations_remove _ _ Hin) as [Hsub1 Hsub2].
  unfold analysis_mask, analysis_open in *. cbn [analysis_entries
    analysis_records map list_to_set record_invariant fst] in *.
  rewrite Hdecl in Hsub1.
  split; [exact Hclosed|]. split.
  { apply elem_of_difference. split; [|exact Hclosed].
    unfold entry_declarations. apply elem_of_map. exists entry. auto. }
  split; [|reflexivity].
  apply set_eq. intros other. split; intros Hother; set_solver.
Qed.

Lemma open_invariant_preserves_in_atomic invariant key state exit :
  open_invariant invariant key state = inr exit ->
  analysis_in_atomic exit = analysis_in_atomic state.
Proof.
  intros Hopen. destruct (open_invariant_records _ _ _ _ Hopen) as (entry & _ & ->).
  reflexivity.
Qed.

Lemma open_invariant_preserves_wf invariant key state exit :
  state_wf state -> open_invariant invariant key state = inr exit ->
  state_wf exit.
Proof.
  intros Hwf Hopen.
  pose proof (proj1 (open_invariant_success _ _ _ _ Hopen)) as Hclosed.
  destruct (open_invariant_records _ _ _ _ Hopen) as (entry & _ & ->).
  unfold state_wf in *. cbn. constructor; [|exact Hwf].
  unfold analysis_open in Hclosed. intros Hin. apply Hclosed.
  apply elem_of_list_to_set. exact Hin.
Qed.

Lemma fold_invariant_preserves_in_atomic invariant key state :
  analysis_in_atomic (fold_invariant invariant key state) =
    analysis_in_atomic state.
Proof.
  unfold fold_invariant.
  destruct (analysis_records state) as [|record rest]; [reflexivity|].
  destruct (decide (record_invariant record = invariant)); reflexivity.
Qed.

Lemma fold_invariant_preserves_wf invariant key state :
  state_wf state -> state_wf (fold_invariant invariant key state).
Proof.
  unfold state_wf, fold_invariant.
  destruct (analysis_records state) as [|record rest]; [done|].
  destruct (decide (record_invariant record = invariant)); cbn; [|done].
  intros Hnodup. inversion Hnodup. assumption.
Qed.

(** Closing the innermost open invariant. *)
Lemma fold_invariant_closes invariant key state record rest :
  analysis_records state = record :: rest ->
  record_invariant record = invariant ->
  fold_invariant invariant key state =
    AnalysisState ({[record_consumed record]} ∪ analysis_entries state) rest
      (match rest with [] => false | _ => analysis_step_taken state end)
      (analysis_in_atomic state).
Proof.
  intros Hrecords Hinvariant. unfold fold_invariant. rewrite Hrecords.
  rewrite decide_True by exact Hinvariant. reflexivity.
Qed.

(** Every open record consumed an entry of its own declaration. *)
Definition records_consume_own (records : list open_record) : Prop :=
  Forall (fun record => (record_consumed record).1 = record_invariant record)
    records.

Lemma fold_open_invariant invariant key state :
  state_wf state -> records_consume_own (analysis_records state) ->
  fold_admissible invariant key state = true ->
  invariant ∈ analysis_open state ->
  analysis_mask (fold_invariant invariant key state) =
    {[invariant]} ∪ analysis_mask state /\
  analysis_open (fold_invariant invariant key state) =
    analysis_open state ∖ {[invariant]}.
Proof.
  intros Hwf Hown Hadmissible Hopen.
  unfold fold_admissible in Hadmissible.
  destruct (analysis_records state) as [|record rest] eqn:Hrecords.
  { unfold analysis_open in Hopen. rewrite Hrecords in Hopen. set_solver. }
  destruct (decide (record_invariant record = invariant)) as [Heq|Hne].
  2: { apply bool_decide_eq_true in Hadmissible. contradiction. }
  rewrite (fold_invariant_closes _ _ _ _ _ Hrecords Heq).
  unfold state_wf in Hwf. rewrite ?Hrecords in Hwf. cbn in Hwf.
  inversion Hwf as [|? ? Hfresh _]. subst.
  unfold records_consume_own in Hown. rewrite ?Hrecords in Hown.
  inversion Hown as [|? ? Hconsumed _]. subst.
  assert (Hrest : record_invariant record ∉
      (list_to_set (map record_invariant rest) : gset inv_id))
    by (rewrite elem_of_list_to_set; exact Hfresh).
  unfold analysis_mask, analysis_open. cbn [analysis_entries analysis_records].
  rewrite Hrecords. cbn [map list_to_set].
  rewrite entry_declarations_union, entry_declarations_singleton, Hconsumed.
  revert Hrest.
  generalize (list_to_set (map record_invariant rest) : gset inv_id) as R.
  generalize (entry_declarations (analysis_entries state)) as D.
  generalize (record_invariant record) as i.
  clear. intros i D R Hrest.
  split; apply set_eq; intros x;
    repeat rewrite ?elem_of_difference, ?elem_of_union, ?elem_of_singleton;
    destruct (decide (x = i)); subst; tauto.
Qed.

Lemma fold_fresh_invariant invariant key state :
  invariant ∉ analysis_open state ->
  analysis_mask (fold_invariant invariant key state) =
    {[invariant]} ∪ analysis_mask state /\
  analysis_open (fold_invariant invariant key state) = analysis_open state.
Proof.
  intros Hclosed.
  assert (Hfresh : fold_invariant invariant key state =
    AnalysisState ({[(invariant, key)]} ∪ analysis_entries state)
      (analysis_records state) (analysis_step_taken state)
      (analysis_in_atomic state)).
  { unfold fold_invariant.
    destruct (analysis_records state) as [|record rest] eqn:Hrecords;
      [reflexivity|].
    destruct (decide (record_invariant record = invariant)) as [Heq|];
      [|reflexivity].
    exfalso. apply Hclosed. unfold analysis_open. rewrite Hrecords.
    cbn. set_solver. }
  rewrite Hfresh. unfold analysis_mask, analysis_open.
  cbn [analysis_entries analysis_records].
  rewrite entry_declarations_union, entry_declarations_singleton.
  unfold analysis_open in Hclosed. split; [|reflexivity].
  apply set_eq; intros other; set_solver.
Qed.

Lemma fold_admissible_fresh invariant key state :
  invariant ∉ analysis_open state -> fold_admissible invariant key state = true.
Proof.
  intros Hclosed. unfold fold_admissible.
  destruct (analysis_records state) as [|record rest] eqn:Hrecords;
    [reflexivity|].
  destruct (decide (record_invariant record = invariant)) as [Heq|].
  - exfalso. apply Hclosed. unfold analysis_open. rewrite Hrecords.
    cbn. set_solver.
  - apply bool_decide_eq_true. exact Hclosed.
Qed.

Lemma fold_fresh_records invariant key state :
  invariant ∉ analysis_open state ->
  analysis_records (fold_invariant invariant key state) = analysis_records state.
Proof.
  intros Hclosed. unfold fold_invariant.
  destruct (analysis_records state) as [|record rest] eqn:Hrecords;
    [reflexivity|].
  destruct (decide (record_invariant record = invariant)) as [Heq|];
    [|reflexivity].
  exfalso. apply Hclosed. unfold analysis_open. rewrite Hrecords.
  cbn. set_solver.
Qed.

(** A fold after an access's unfold, with the records restored in between,
    closes the access. *)
Lemma fold_after_open_records invariant key key' outer opened inner :
  open_invariant invariant key outer = inr opened ->
  analysis_records inner = analysis_records opened ->
  analysis_records (fold_invariant invariant key' inner) =
    analysis_records outer.
Proof.
  intros Hopen Hinner.
  destruct (open_invariant_records _ _ _ _ Hopen) as (entry & _ & ->).
  cbn [analysis_records] in Hinner.
  rewrite (fold_invariant_closes _ _ _ _ _ Hinner eq_refl). reflexivity.
Qed.

Lemma leave_scope_preserves_records level outer state :
  analysis_records (leave_scope level outer state) = analysis_records state.
Proof. reflexivity. Qed.

Lemma leave_scope_preserves_open level outer state :
  analysis_open (leave_scope level outer state) = analysis_open state.
Proof. reflexivity. Qed.

Lemma leave_scope_mask level outer state :
  analysis_mask (leave_scope level outer state) ⊆ analysis_mask state.
Proof.
  unfold analysis_mask, leave_scope, entry_declarations. cbn.
  intros invariant Hin. apply elem_of_difference in Hin as [Hin Hclosed].
  apply elem_of_difference. split; [|exact Hclosed].
  apply elem_of_map in Hin as (entry & -> & Hentry).
  apply elem_of_filter in Hentry as [_ Hentry].
  apply elem_of_map. eauto.
Qed.

(** The cost of each leaf, as the analyzer consults it. *)
Class LeafCost := LeafCostData {
  leaf_cost : forall Γ, syntax_statement Γ -> step_cost;
}.
Context {Cost : LeafCost}.

Fixpoint analyze_fuel {Γ} (fuel : nat)
    (state : analysis_state) (statement : syntax_statement Γ) :
    analysis_error + analysis_state :=
  match fuel with
  | 0 => inl FuelExhausted
  | S fuel' =>
      match syntax_view Γ statement with
      | ViewLeaf => take_step (leaf_cost Γ statement) state
      | ViewDone => inr state
      | ViewUnfold invariant key => open_invariant invariant key state
      | ViewFold invariant key =>
          if fold_admissible invariant key state
          then inr (fold_invariant invariant key state)
          else inl (NonLifoFold invariant)
      | ViewSequence first second =>
          match analyze_fuel fuel' state first with
          | inl error => inl error
          | inr middle => analyze_fuel fuel' middle second
          end
      | ViewConditional then_branch else_branch =>
          match analyze_fuel fuel' state then_branch,
              analyze_fuel fuel' state else_branch with
          | inr then_state, inr else_state =>
              if bool_decide
                  (analysis_records then_state = analysis_records else_state /\
                   analysis_in_atomic then_state = analysis_in_atomic else_state)
              then inr (AnalysisState
                (entries_meet (analysis_entries then_state)
                  (analysis_entries else_state))
                (analysis_records then_state)
                (analysis_step_taken then_state || analysis_step_taken else_state)
                (analysis_in_atomic then_state))
              else inl IncompatibleBranches
          | inl error, _ | _, inl error => inl error
          end
      | ViewStructuredAccess _ _ => inl StructuredAccessRequiresCertificate
      | ViewAtomic body =>
          match take_step AtomicStep state with
          | inl error => inl error
          | inr outer =>
              let inner_entry := AnalysisState (analysis_entries outer)
                (analysis_records outer) (analysis_step_taken outer) true in
              match analyze_fuel fuel' inner_entry body with
              | inl error => inl error
              | inr inner =>
                  if bool_decide (analysis_records inner = analysis_records outer)
                  then inr (AnalysisState (analysis_entries inner)
                    (analysis_records inner)
                    (analysis_step_taken outer || analysis_step_taken inner)
                    (analysis_in_atomic outer))
                  else inl AtomicBlockLeaksAccess
              end
          end
      | ViewScope _ body =>
          match analyze_fuel fuel' state body with
          | inl error => inl error
          | inr inner =>
              if leave_scope_admissible (length Γ) inner
              then inr (leave_scope (length Γ) state inner)
              else inl ScopeLeaksAccess
          end
      end
  end.

Definition analyze {Γ} state (statement : syntax_statement Γ) :=
  analyze_fuel (syntax_size Γ statement) state statement.

Inductive analysis_certificate :
    forall Γ, analysis_state -> syntax_statement Γ ->
      analysis_state -> Type :=
| CertLeaf Γ state statement exit :
    syntax_view Γ statement = ViewLeaf ->
    take_step (leaf_cost Γ statement) state = inr exit ->
    analysis_certificate Γ state statement exit
| CertDone Γ state statement :
    syntax_view Γ statement = ViewDone ->
    analysis_certificate Γ state statement state
| CertUnfold Γ state statement invariant key exit :
    syntax_view Γ statement = ViewUnfold invariant key ->
    open_invariant invariant key state = inr exit ->
    analysis_certificate Γ state statement exit
| CertFold Γ state statement invariant key :
    syntax_view Γ statement = ViewFold invariant key ->
    fold_admissible invariant key state = true ->
    analysis_certificate Γ state statement
      (fold_invariant invariant key state)
| CertSequence Γ state statement first middle second exit :
    syntax_view Γ statement = ViewSequence first second ->
    analysis_certificate Γ state first middle ->
    analysis_certificate Γ middle second exit ->
    analysis_certificate Γ state statement exit
| CertConditional Γ state statement then_branch else_branch
    then_exit else_exit :
    syntax_view Γ statement = ViewConditional then_branch else_branch ->
    analysis_certificate Γ state then_branch then_exit ->
    analysis_certificate Γ state else_branch else_exit ->
    analysis_records then_exit = analysis_records else_exit ->
    analysis_in_atomic then_exit = analysis_in_atomic else_exit ->
    analysis_certificate Γ state statement
      (AnalysisState
        (entries_meet (analysis_entries then_exit) (analysis_entries else_exit))
        (analysis_records then_exit)
        (analysis_step_taken then_exit || analysis_step_taken else_exit)
        (analysis_in_atomic then_exit))
| CertAtomic Γ state statement body outer inner :
    syntax_view Γ statement = ViewAtomic body ->
    take_step AtomicStep state = inr outer ->
    analysis_certificate Γ
      (AnalysisState (analysis_entries outer) (analysis_records outer)
        (analysis_step_taken outer) true) body inner ->
    analysis_records inner = analysis_records outer ->
    analysis_certificate Γ state statement
      (AnalysisState (analysis_entries inner) (analysis_records inner)
        (analysis_step_taken outer || analysis_step_taken inner)
        (analysis_in_atomic outer))
| CertScope Γ state statement d body inner :
    syntax_view Γ statement = ViewScope d body ->
    analysis_certificate (d :: Γ) state body inner ->
    leave_scope_admissible (length Γ) inner = true ->
    analysis_certificate Γ state statement
      (leave_scope (length Γ) state inner).

Lemma analysis_certificate_preserves_in_atomic
    {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  analysis_in_atomic exit = analysis_in_atomic entry.
Proof.
  induction certificate; simpl.
  - eapply take_step_preserves_in_atomic. exact e0.
  - reflexivity.
  - eapply open_invariant_preserves_in_atomic. exact e0.
  - apply fold_invariant_preserves_in_atomic.
  - etrans; eassumption.
  - exact IHcertificate1.
  - eapply take_step_preserves_in_atomic. exact e0.
  - exact IHcertificate.
Qed.

(** Logical Raven masks that may be available anywhere in a certified
    region.  The semantic translation uses this union to choose one ambient
    Iris mask; individual Raven mask transitions do not themselves enlarge
    or shrink that ambient mask. *)
Fixpoint certificate_footprint {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
    gset inv_id :=
  analysis_mask entry ∪ analysis_open entry ∪
  analysis_mask exit ∪ analysis_open exit ∪
  match certificate with
  | CertSequence _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      certificate_footprint first_certificate ∪
      certificate_footprint second_certificate
  | CertConditional _ _ _ _ _ _ _ _
      then_certificate else_certificate _ _ =>
      certificate_footprint then_certificate ∪
      certificate_footprint else_certificate
  | CertAtomic _ _ _ _ _ _ _ _ body_certificate _ =>
      certificate_footprint body_certificate
  | CertScope _ _ _ _ _ _ _ body_certificate _ =>
      certificate_footprint body_certificate
  | _ => ∅
  end.

Lemma certificate_entry_subset_footprint {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  analysis_mask entry ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Lemma certificate_exit_subset_footprint {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  analysis_mask exit ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Lemma certificate_entry_open_subset_footprint
    {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  analysis_open entry ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Lemma certificate_exit_open_subset_footprint
    {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  analysis_open exit ⊆ certificate_footprint certificate.
Proof. destruct certificate; simpl; set_solver. Qed.

Fixpoint certificate_height {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) : nat :=
  match certificate with
  | CertLeaf _ _ _ _ _ _ => 1
  | CertDone _ _ _ _ => 1
  | CertUnfold _ _ _ _ _ _ _ _ => 1
  | CertFold _ _ _ _ _ _ _ => 1
  | CertSequence _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      S (Nat.max (certificate_height first_certificate)
        (certificate_height second_certificate))
  | CertConditional _ _ _ _ _ _ _ _ then_certificate else_certificate _ _ =>
      S (Nat.max (certificate_height then_certificate)
        (certificate_height else_certificate))
  | CertAtomic _ _ _ _ _ _ _ _ body_certificate _ =>
      S (certificate_height body_certificate)
  | CertScope _ _ _ _ _ _ _ body_certificate _ =>
      S (certificate_height body_certificate)
  end.

Lemma analyze_fuel_succ {Γ fuel} state
    (statement : syntax_statement Γ) exit :
  analyze_fuel fuel state statement = inr exit ->
  analyze_fuel (S fuel) state statement = inr exit.
Proof.
  revert Γ state statement exit.
  induction fuel as [|fuel IH]; intros Γ state statement exit Hrun;
    simpl in Hrun |- *; first discriminate.
  destruct (syntax_view Γ statement) eqn:Hview; simpl in Hrun |- *.
  - exact Hrun.
  - exact Hrun.
  - exact Hrun.
  - exact Hrun.
  - destruct (analyze_fuel fuel state first) as [error|middle]
      eqn:Hfirst; try discriminate.
    apply IH in Hfirst. apply IH in Hrun.
    change (analyze_fuel (S fuel) state first = inr middle) in Hfirst.
    change (analyze_fuel (S fuel) middle second = inr exit) in Hrun.
    change (match analyze_fuel (S fuel) state first with
      | inl error => inl error
      | inr middle => analyze_fuel (S fuel) middle second
      end = inr exit).
    rewrite Hfirst. exact Hrun.
  - destruct (analyze_fuel fuel state then_branch) as [error|then_exit]
      eqn:Hthen; try discriminate.
    destruct (analyze_fuel fuel state else_branch) as [error|else_exit]
      eqn:Helse; try discriminate.
    apply IH in Hthen. apply IH in Helse.
    change (analyze_fuel (S fuel) state then_branch = inr then_exit)
      in Hthen.
    change (analyze_fuel (S fuel) state else_branch = inr else_exit)
      in Helse.
    change (match analyze_fuel (S fuel) state then_branch,
      analyze_fuel (S fuel) state else_branch with
      | inr then_state, inr else_state =>
          if bool_decide
            (analysis_records then_state = analysis_records else_state /\
             analysis_in_atomic then_state = analysis_in_atomic else_state)
          then inr (AnalysisState
            (entries_meet (analysis_entries then_state)
              (analysis_entries else_state))
            (analysis_records then_state)
            (analysis_step_taken then_state || analysis_step_taken else_state)
            (analysis_in_atomic then_state))
          else inl IncompatibleBranches
      | inl error, _ | _, inl error => inl error
      end = inr exit).
    rewrite Hthen, Helse. exact Hrun.
  - discriminate.
  - destruct (take_step AtomicStep state) as [error|outer] eqn:Hstep;
      try discriminate.
    destruct (analyze_fuel fuel
      (AnalysisState (analysis_entries outer) (analysis_records outer)
        (analysis_step_taken outer) true) body) as [error|inner]
      eqn:Hbody; try discriminate.
    apply IH in Hbody.
    change (analyze_fuel (S fuel)
      (AnalysisState (analysis_entries outer) (analysis_records outer)
        (analysis_step_taken outer) true) body = inr inner) in Hbody.
    change (match analyze_fuel (S fuel)
      (AnalysisState (analysis_entries outer) (analysis_records outer)
        (analysis_step_taken outer) true) body with
      | inl error => inl error
      | inr inner =>
          if bool_decide (analysis_records inner = analysis_records outer)
          then inr (AnalysisState (analysis_entries inner)
            (analysis_records inner)
            (analysis_step_taken outer || analysis_step_taken inner)
            (analysis_in_atomic outer))
          else inl AtomicBlockLeaksAccess
      end = inr exit).
    rewrite Hbody. exact Hrun.
  - destruct (analyze_fuel fuel state body) as [error|inner] eqn:Hbody;
      try discriminate.
    apply IH in Hbody.
    change (analyze_fuel (S fuel) state body = inr inner) in Hbody.
    change (match analyze_fuel (S fuel) state body with
      | inl error => inl error
      | inr inner =>
          if leave_scope_admissible (length Γ) inner
          then inr (leave_scope (length Γ) state inner)
          else inl ScopeLeaksAccess
      end = inr exit).
    rewrite Hbody. exact Hrun.
Qed.

Lemma analyze_fuel_monotone {Γ fuel target} state
    (statement : syntax_statement Γ) exit :
  fuel <= target ->
  analyze_fuel fuel state statement = inr exit ->
  analyze_fuel target state statement = inr exit.
Proof.
  intros Hle Hrun. induction Hle.
  - exact Hrun.
  - apply analyze_fuel_succ. exact IHHle.
Qed.

Lemma certificate_replays_height {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  analyze_fuel (certificate_height certificate) entry statement = inr exit.
Proof.
  induction certificate; simpl.
  - rewrite e. exact e0.
  - rewrite e. reflexivity.
  - rewrite e. exact e0.
  - rewrite e, e0. reflexivity.
  - rewrite e.
    rewrite (analyze_fuel_monotone _ _ _
      (Nat.le_max_l _ _) IHcertificate1).
    exact (analyze_fuel_monotone _ _ _
      (Nat.le_max_r _ _) IHcertificate2).
  - rewrite e.
    rewrite (analyze_fuel_monotone _ _ _
      (Nat.le_max_l _ _) IHcertificate1).
    rewrite (analyze_fuel_monotone _ _ _
      (Nat.le_max_r _ _) IHcertificate2).
    rewrite bool_decide_true; [reflexivity|]. split; assumption.
  - rewrite e, e0.
    rewrite IHcertificate.
    rewrite bool_decide_true; [reflexivity|exact e1].
  - rewrite e, IHcertificate, e0. reflexivity.
Qed.

Lemma certificate_height_le_size {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  certificate_height certificate <= syntax_size Γ statement.
Proof.
  induction certificate; simpl.
  - pose proof (syntax_size_positive Γ statement). lia.
  - pose proof (syntax_size_positive Γ statement). lia.
  - pose proof (syntax_size_positive Γ statement). lia.
  - pose proof (syntax_size_positive Γ statement). lia.
  - pose proof (syntax_sequence_children_smaller Γ statement first second e)
      as [Hfirst Hsecond].
    lia.
  - pose proof (syntax_conditional_children_smaller Γ statement then_branch
      else_branch e) as [Hthen Helse].
    lia.
  - pose proof (syntax_atomic_body_smaller Γ statement body e) as Hbody.
    lia.
  - pose proof (syntax_scope_body_smaller Γ statement d body e) as Hbody.
    lia.
Qed.

(** Invariants a statement may add to the available mask: fold targets and
    procedure-call grants. *)
Definition step_cost_grants (cost : step_cost) : gset inv_id :=
  match cost with
  | ProcedureCallStep _ granted => granted
  | _ => ∅
  end.

Fixpoint statement_allocations_fuel {Γ} (fuel : nat)
    (statement : syntax_statement Γ) : gset inv_id :=
  match fuel with
  | 0 => ∅
  | S fuel' =>
      match syntax_view Γ statement with
      | ViewLeaf => step_cost_grants (leaf_cost Γ statement)
      | ViewFold invariant _ => {[invariant]}
      | ViewSequence first second =>
          statement_allocations_fuel fuel' first ∪
            statement_allocations_fuel fuel' second
      | ViewConditional then_branch else_branch =>
          statement_allocations_fuel fuel' then_branch ∪
            statement_allocations_fuel fuel' else_branch
      | ViewStructuredAccess _ body | ViewAtomic body =>
          statement_allocations_fuel fuel' body
      | ViewScope _ body => statement_allocations_fuel fuel' body
      | ViewDone | ViewUnfold _ _ => ∅
      end
  end.

Definition statement_allocations {Γ} (statement : syntax_statement Γ) :
    gset inv_id :=
  statement_allocations_fuel (syntax_size Γ statement) statement.

Lemma take_step_resources_bound cost state exit :
  take_step cost state = inr exit ->
  analysis_mask exit ∪ analysis_open exit ⊆
    analysis_mask state ∪ analysis_open state ∪ step_cost_grants cost.
Proof.
  intros Hstep. destruct cost; simpl.
  1-3: apply take_plain_step_preserves_sets in Hstep as [Hmask Hopen];
    rewrite Hmask, Hopen; set_solver.
  - apply procedure_call_step_success in Hstep as (_ & _ & Hmask & Hopen).
    rewrite Hmask, Hopen. set_solver.
  - apply procedure_spawn_step_success in Hstep as (_ & Hmask & Hopen).
    rewrite Hmask, Hopen. set_solver.
Qed.

(** Every declaration named by a state is available or open. *)
Lemma fold_invariant_resources_bound invariant key state :
  records_consume_own (analysis_records state) ->
  analysis_mask (fold_invariant invariant key state) ∪
    analysis_open (fold_invariant invariant key state) ⊆
  analysis_mask state ∪ analysis_open state ∪ {[invariant]}.
Proof.
  intros Hown. unfold fold_invariant.
  destruct (analysis_records state) as [|record rest] eqn:Hrecords.
  - unfold analysis_mask, analysis_open. cbn [analysis_entries analysis_records].
    rewrite Hrecords, entry_declarations_union, entry_declarations_singleton.
    cbn [fst]. abstract_declarations. apply elem_of_subseteq. intros x Hx.
    destruct (decide (x = invariant)); set_solver.
  - unfold records_consume_own in Hown. rewrite ?Hrecords in Hown.
    inversion Hown as [|? ? Hconsumed _]. subst.
    destruct (decide (record_invariant record = invariant));
      unfold analysis_mask, analysis_open; cbn [analysis_entries
        analysis_records]; rewrite Hrecords, entry_declarations_union,
        entry_declarations_singleton; cbn [map list_to_set];
      [rewrite Hconsumed|]; cbn [fst];
      generalize (list_to_set (map record_invariant rest) : gset inv_id) as R;
      generalize (entry_declarations (analysis_entries state)) as D;
      generalize (record_invariant record) as i;
      clear; intros i D R; apply elem_of_subseteq; intros x Hx;
      destruct (decide (x ∈ R)); destruct (decide (x = i));
      destruct (decide (x = invariant)); set_solver.
Qed.

Lemma open_invariant_consume_own invariant key state exit :
  records_consume_own (analysis_records state) ->
  open_invariant invariant key state = inr exit ->
  records_consume_own (analysis_records exit).
Proof.
  intros Hown Hopen.
  destruct (open_invariant_records _ _ _ _ Hopen) as (entry & Hselect & ->).
  destruct (select_entry_sound _ _ _ _ Hselect) as [_ Hdecl].
  constructor; [exact Hdecl | exact Hown].
Qed.

Lemma fold_invariant_consume_own invariant key state :
  records_consume_own (analysis_records state) ->
  records_consume_own
    (analysis_records (fold_invariant invariant key state)).
Proof.
  unfold records_consume_own, fold_invariant.
  destruct (analysis_records state) as [|record rest]; [done|].
  destruct (decide (record_invariant record = invariant)); cbn; [|done].
  intros Hown. inversion Hown. assumption.
Qed.

(** States reached by a certificate keep every open record's consumed entry
    in its own declaration. *)
Theorem certificate_consume_own {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  records_consume_own (analysis_records entry) ->
  records_consume_own (analysis_records exit).
Proof.
  induction certificate; intros Hown; cbn.
  - rewrite (take_step_preserves_records _ _ _ e0). exact Hown.
  - exact Hown.
  - eapply open_invariant_consume_own; eassumption.
  - apply fold_invariant_consume_own. exact Hown.
  - apply IHcertificate2, IHcertificate1, Hown.
  - apply IHcertificate1, Hown.
  - rewrite e1. rewrite (take_step_preserves_records _ _ _ e0). exact Hown.
  - apply IHcertificate, Hown.
Qed.

Lemma certificate_footprint_allocations_fuel {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) fuel :
  records_consume_own (analysis_records entry) ->
  certificate_height certificate <= fuel ->
  certificate_footprint certificate ⊆
    analysis_mask entry ∪ analysis_open entry ∪
      statement_allocations_fuel fuel statement.
Proof.
  revert fuel.
  induction certificate; intros [|fuel] Hown Hheight; simpl in Hheight;
    try lia; cbn [statement_allocations_fuel certificate_footprint];
    rewrite e.
  - pose proof (take_step_resources_bound _ _ _ e0). set_solver.
  - set_solver.
  - apply open_invariant_success in e0 as (_ & Havailable & Hmask & Hopen).
    rewrite Hmask, Hopen. set_solver.
  - pose proof (fold_invariant_resources_bound invariant key state Hown).
    set_solver.
  - pose proof (IHcertificate1 fuel Hown ltac:(lia)) as Hfirst.
    pose proof (IHcertificate2 fuel
      (certificate_consume_own certificate1 Hown) ltac:(lia)) as Hsecond.
    pose proof (certificate_exit_subset_footprint certificate1).
    pose proof (certificate_exit_open_subset_footprint certificate1).
    pose proof (certificate_exit_subset_footprint certificate2).
    pose proof (certificate_exit_open_subset_footprint certificate2).
    set_solver.
  - pose proof (IHcertificate1 fuel Hown ltac:(lia)) as Hthen.
    pose proof (IHcertificate2 fuel Hown ltac:(lia)) as Helse.
    pose proof (certificate_exit_subset_footprint certificate1) as Hexit_mask.
    pose proof (certificate_exit_open_subset_footprint certificate1)
      as Hexit_open.
    assert (Hjoin_open : analysis_open (AnalysisState
        (entries_meet (analysis_entries then_exit) (analysis_entries else_exit))
        (analysis_records then_exit)
        (analysis_step_taken then_exit || analysis_step_taken else_exit)
        (analysis_in_atomic then_exit)) = analysis_open then_exit)
      by reflexivity.
    assert (Hjoin_mask : analysis_mask (AnalysisState
        (entries_meet (analysis_entries then_exit) (analysis_entries else_exit))
        (analysis_records then_exit)
        (analysis_step_taken then_exit || analysis_step_taken else_exit)
        (analysis_in_atomic then_exit)) ⊆ analysis_mask then_exit).
    { unfold analysis_mask, analysis_open, entries_meet, entry_declarations.
      cbn [analysis_entries analysis_records]. intros invariant Hin.
      apply elem_of_difference in Hin as [Hin Hclosed].
      apply elem_of_difference. split; [|exact Hclosed].
      apply elem_of_map in Hin as (entry' & -> & Hentry).
      apply elem_of_filter in Hentry as [[Hleft _] _].
      apply elem_of_map. destruct Hleft as [Hleft|Hleft].
      - exists entry'. auto.
      - exists (entry'.1, None). auto. }
    rewrite Hjoin_open. apply elem_of_subseteq. intros x Hx.
    rewrite !elem_of_union in Hx.
    destruct Hx as [[[[Hx|Hx]|Hx]|Hx]|[Hx|Hx]].
    + clear - Hx. set_solver.
    + clear - Hx. set_solver.
    + apply Hjoin_mask, Hexit_mask, Hthen in Hx. clear - Hx. set_solver.
    + apply Hexit_open, Hthen in Hx. clear - Hx. set_solver.
    + apply Hthen in Hx. clear - Hx. set_solver.
    + apply Helse in Hx. clear - Hx. set_solver.
  - assert (Hbody_own : records_consume_own (analysis_records
      (AnalysisState (analysis_entries outer) (analysis_records outer)
        (analysis_step_taken outer) true))).
    { cbn. rewrite (take_step_preserves_records _ _ _ e0). exact Hown. }
    pose proof (IHcertificate fuel Hbody_own ltac:(lia)) as Hbody.
    apply atomic_step_preserves_sets in e0 as [Hmask Hopen].
    pose proof (certificate_exit_subset_footprint certificate).
    pose proof (certificate_exit_open_subset_footprint certificate).
    unfold analysis_mask, analysis_open in *. simpl in *. set_solver.
  - pose proof (IHcertificate fuel Hown ltac:(lia)) as Hbody.
    pose proof (certificate_exit_subset_footprint certificate).
    pose proof (certificate_exit_open_subset_footprint certificate).
    pose proof (leave_scope_mask (length Γ) state inner).
    rewrite leave_scope_preserves_open. set_solver.
Qed.

(** Every invariant in a certificate footprint is available or open on entry,
    or allocated by the statement.  This bound is independent of how
    conditional joins restrict the exit mask. *)
Lemma certificate_footprint_allocations {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  records_consume_own (analysis_records entry) ->
  certificate_footprint certificate ⊆
    analysis_mask entry ∪ analysis_open entry ∪
      statement_allocations statement.
Proof.
  intros Hown. apply certificate_footprint_allocations_fuel; [exact Hown|].
  apply certificate_height_le_size.
Qed.

Theorem certificate_replays {Γ} state
    (statement : syntax_statement Γ) exit :
  analysis_certificate Γ state statement exit ->
  analyze state statement = inr exit.
Proof.
  intros certificate. unfold analyze.
  eapply analyze_fuel_monotone;
    [exact (certificate_height_le_size certificate)|].
  exact (certificate_replays_height certificate).
Qed.

Lemma analysis_certificate_exit_unique
    {Γ entry statement exit1 exit2}
    (certificate1 : analysis_certificate Γ entry statement exit1)
    (certificate2 : analysis_certificate Γ entry statement exit2) :
  exit1 = exit2.
Proof.
  pose proof (certificate_replays entry statement exit1 certificate1)
    as Hreplay1.
  pose proof (certificate_replays entry statement exit2 certificate2)
    as Hreplay2.
  congruence.
Qed.

Lemma analyze_fuel_certificate_exit {Γ fuel entry statement actual expected} :
  analyze_fuel fuel entry statement = inr actual ->
  analysis_certificate Γ entry statement expected ->
  actual = expected.
Proof.
  intros Hrun certificate.
  pose proof (analyze_fuel_monotone entry statement actual
    (Nat.le_max_l fuel (certificate_height certificate)) Hrun) as Hactual.
  pose proof (analyze_fuel_monotone entry statement expected
    (Nat.le_max_r fuel (certificate_height certificate))
    (certificate_replays_height certificate)) as Hexpected.
  congruence.
Qed.

(** For fixed public indices, successful analyzer certificates carry no additional
    computational choice.  This lets later certified transformations use a
    canonical certificate construction without introducing a parallel plan
    object merely to remember its proof fields. *)
Lemma analysis_certificate_unique
    {Γ entry statement exit}
    (certificate1 certificate2 :
      analysis_certificate Γ entry statement exit) :
  certificate1 = certificate2.
Proof.
  revert certificate2.
  induction certificate1; intros certificate2; dependent destruction certificate2;
    try solve [exfalso; congruence].
  - f_equal; apply proof_irrelevance.
  - f_equal; apply proof_irrelevance.
  - assert (invariant0 = invariant) by congruence. subst invariant0.
    assert (key0 = key) by congruence. subst key0.
    f_equal; apply proof_irrelevance.
  - assert (invariant0 = invariant) by congruence. subst invariant0.
    assert (key0 = key) by congruence. subst key0.
    apply JMeq_eq in x. subst certificate0.
    f_equal; apply proof_irrelevance.
  - assert (first0 = first) by congruence. subst first0.
    assert (second0 = second) by congruence. subst second0.
    pose proof (analysis_certificate_exit_unique certificate1_1
      certificate2_1) as Hmiddle. subst middle0.
    rewrite (IHcertificate1_1 certificate2_1).
    rewrite (IHcertificate1_2 certificate2_2).
    f_equal; apply proof_irrelevance.
  - assert (then_branch0 = then_branch) by congruence. subst then_branch0.
    assert (else_branch0 = else_branch) by congruence. subst else_branch0.
    pose proof (analysis_certificate_exit_unique certificate1_1
      certificate2_1) as Hthen. subst then_exit0.
    pose proof (analysis_certificate_exit_unique certificate1_2
      certificate2_2) as Helse. subst else_exit0.
    apply JMeq_eq in x. subst certificate0.
    rewrite (IHcertificate1_1 certificate2_1).
    rewrite (IHcertificate1_2 certificate2_2).
    f_equal; apply proof_irrelevance.
  - assert (body0 = body) by congruence. subst body0.
    assert (outer0 = outer) by congruence. subst outer0.
    pose proof (analysis_certificate_exit_unique certificate1
      certificate2) as Hinner. subst inner0.
    apply JMeq_eq in x. subst certificate0.
    rewrite (IHcertificate1 certificate2).
    f_equal; apply proof_irrelevance.
  - pose proof (eq_trans (eq_sym e) e1) as Hview.
    injection Hview as <- Hbody.
    apply Eqdep.EqdepTheory.inj_pair2 in Hbody. subst body0.
    pose proof (analysis_certificate_exit_unique certificate1
      certificate2) as Hinner. subst inner0.
    apply JMeq_eq in x. subst certificate0.
    rewrite (IHcertificate1 certificate2).
    f_equal; apply proof_irrelevance.
Qed.

Theorem certificate_preserves_wf {Γ} state
    (statement : syntax_statement Γ) exit :
  state_wf state ->
  analysis_certificate Γ state statement exit ->
  state_wf exit.
Proof.
  intros Hwf certificate. induction certificate.
  - eapply take_step_preserves_wf; eauto.
  - exact Hwf.
  - eapply open_invariant_preserves_wf; eauto.
  - apply fold_invariant_preserves_wf. exact Hwf.
  - apply IHcertificate2. apply IHcertificate1. exact Hwf.
  - exact (IHcertificate1 Hwf).
  - unfold state_wf in *. cbn. rewrite e1.
    rewrite (take_step_preserves_records _ _ _ e0). exact Hwf.
  - exact (IHcertificate Hwf).
Qed.

Theorem analyze_fuel_builds_certificate {Γ fuel} state
    (statement : syntax_statement Γ) exit :
  analyze_fuel fuel state statement = inr exit ->
  analysis_certificate Γ state statement exit.
Proof.
  revert Γ state statement exit.
  induction fuel as [|fuel IH]; intros Γ state statement exit Hanalyze;
    simpl in Hanalyze; first discriminate.
  destruct (syntax_view Γ statement) eqn:Hview.
  - eapply CertLeaf; [exact Hview|exact Hanalyze].
  - inversion Hanalyze; subst exit. eapply CertDone. exact Hview.
  - eapply CertUnfold; [exact Hview|exact Hanalyze].
  - destruct (fold_admissible invariant key state) eqn:Hadmissible;
      [|discriminate].
    inversion Hanalyze; subst exit. eapply CertFold; eassumption.
  - destruct (analyze_fuel fuel state first) as [error|middle] eqn:Hfirst;
      try discriminate.
    eapply CertSequence; [exact Hview|eapply IH|eapply IH]; eauto.
  - destruct (analyze_fuel fuel state then_branch) as [error|then_exit] eqn:Hthen;
      try discriminate.
    destruct (analyze_fuel fuel state else_branch) as [error|else_exit] eqn:Helse;
      try discriminate.
    destruct (bool_decide
      (analysis_records then_exit = analysis_records else_exit /\
       analysis_in_atomic then_exit = analysis_in_atomic else_exit)) eqn:Hjoin;
      last discriminate.
    apply bool_decide_eq_true in Hjoin as [Hrecords Hin_atomic].
    inversion Hanalyze; subst exit.
    eapply CertConditional; eauto.
  - discriminate.
  - destruct (take_step AtomicStep state) as [error|outer] eqn:Hstep;
      try discriminate.
    destruct (analyze_fuel fuel
      (AnalysisState (analysis_entries outer) (analysis_records outer)
        (analysis_step_taken outer) true) body) as [error|inner] eqn:Hbody;
      try discriminate.
    destruct (bool_decide (analysis_records inner = analysis_records outer))
      eqn:Hscope; last discriminate.
    apply bool_decide_eq_true in Hscope.
    inversion Hanalyze; subst exit.
    eapply CertAtomic; eauto.
  - destruct (analyze_fuel fuel state body) as [error|inner] eqn:Hbody;
      try discriminate.
    destruct (leave_scope_admissible (length Γ) inner) eqn:Hadmissible;
      [|discriminate].
    inversion Hanalyze; subst exit.
    eapply CertScope; [exact Hview | eapply IH; exact Hbody | exact Hadmissible].
Defined.

Corollary analyze_builds_certificate {Γ} state
    (statement : syntax_statement Γ) exit :
  analyze state statement = inr exit ->
  analysis_certificate Γ state statement exit.
Proof. apply analyze_fuel_builds_certificate. Defined.

End WithSyntax.
End AnalysisView.
