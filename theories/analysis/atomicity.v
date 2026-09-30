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

(** Resolution through aliases: a ghost value initialized with an atom stands
    for that atom while the atom's local is not written. *)
Definition resolve_atom (aliases : gmap nat key_atom) (atom : key_atom) :
    key_atom :=
  match atom with
  | AtomLevel level => default atom (aliases !! level)
  | _ => atom
  end.

Definition resolve_key (aliases : gmap nat key_atom) (key : access_key) :
    access_key :=
  fmap (map (resolve_atom aliases)) key.

Definition resolve_entry (aliases : gmap nat key_atom) (entry : mask_entry) :
    mask_entry :=
  (entry.1, resolve_key aliases entry.2).

(** The aliases valid on both sides of a join. *)
Definition aliases_meet (left right : gmap nat key_atom) :
    gmap nat key_atom :=
  filter (fun binding => right !! binding.1 = Some binding.2) left.

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
    (excluded : list access_key)
| ViewFold (invariant : inv_id) (key : access_key)
| ViewSequence (first second : statement Γ)
| ViewConditional (then_branch else_branch : statement Γ)
| ViewStructuredAccess (invariant : inv_id) (body : statement Γ)
| ViewAtomic (body : statement Γ)
(* A scope for a new local, with the atom it is initialized with, if any. *)
| ViewScope (d : decl) (alias : option key_atom) (body : statement (d :: Γ)).

Arguments ViewLeaf {_ _}.
Arguments ViewDone {_ _}.
Arguments ViewUnfold {_ _} _ _ _.
Arguments ViewFold {_ _} _ _.
Arguments ViewSequence {_ _} _ _.
Arguments ViewConditional {_ _} _ _.
Arguments ViewStructuredAccess {_ _} _ _.
Arguments ViewAtomic {_ _} _.
Arguments ViewScope {_ _} _ _ _.

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
  syntax_scope_body_smaller : forall Γ statement d alias body,
    syntax_view Γ statement = ViewScope d alias body ->
    syntax_size (d :: Γ) body < syntax_size Γ statement;
  (** The level of the local a leaf writes, if any. *)
  syntax_leaf_write : forall Γ, syntax_statement Γ -> option nat;
}.



Section WithSyntax.
Context {Syntax : AnalysisSyntax}.

Inductive step_cost :=
| NoStep
| AtomicStep
| NonAtomicStep
(* The call site's instances of the callee's required and granted
   entries. *)
| ProcedureCallStep (required granted : gset mask_entry)
| ProcedureSpawnStep (required : gset mask_entry).

Inductive analysis_error :=
| MissingInvariant (invariant : inv_id)
| ReentrantInvariant (invariant : inv_id)
| NonLifoFold (invariant : inv_id)
| SecondAtomicStep
| NonAtomicWhileOpen
| MissingProcedureMask
| AtomicBlockLeaksAccess
| ScopeLeaksAccess
| StructuredAccessRequiresCertificate
| IncompatibleBranches
| FuelExhausted.

(** The analysis state: the available mask entries, the stack of open
    invariants (innermost first), the aliases of the ghost values in scope,
    whether the open accesses have taken their physical step, and whether
    the analysis is inside a trusted atomic block.  Entries are stored with
    their keys resolved through the aliases. *)
Record analysis_state := AnalysisState {
  analysis_entries : gset mask_entry;
  analysis_records : list open_record;
  analysis_aliases : gmap nat key_atom;
  analysis_step_taken : bool;
  analysis_in_atomic : bool;
}.

(** The state after a conditional, the state in which a trusted block's
    body is analyzed, and the state after the block. *)
Notation join_state then_exit else_exit :=
  (AnalysisState
    (entries_meet (analysis_entries then_exit) (analysis_entries else_exit))
    (analysis_records then_exit)
    (aliases_meet (analysis_aliases then_exit) (analysis_aliases else_exit))
    (analysis_step_taken then_exit || analysis_step_taken else_exit)
    (analysis_in_atomic then_exit)).
Notation atomic_entry outer :=
  (AnalysisState (analysis_entries outer) (analysis_records outer)
    (analysis_aliases outer) (analysis_step_taken outer) true).
Notation atomic_exit outer inner :=
  (AnalysisState (analysis_entries inner) (analysis_records inner)
    (analysis_aliases inner)
    (analysis_step_taken outer || analysis_step_taken inner)
    (analysis_in_atomic outer)).

(** The open declarations. *)
Definition analysis_open (state : analysis_state) : gset inv_id :=
  list_to_set (map record_invariant (analysis_records state)).

(** The available declarations. *)
Definition analysis_mask (state : analysis_state) : gset inv_id :=
  entry_declarations (analysis_entries state) ∖ analysis_open state.

(** At most one instance of a declaration is open. *)
Definition state_wf state : Prop :=
  NoDup (map (fun record => (record_invariant record, record_key record))
    (analysis_records state)).

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
        (analysis_aliases state) true false)
  | NonAtomicStep => inl NonAtomicWhileOpen
  | ProcedureCallStep _ _ | ProcedureSpawnStep _ => inl NonAtomicWhileOpen
  end.

(** Every required entry is covered by an available one. *)
Definition entries_available (required : gset mask_entry) state : Prop :=
  set_Forall (fun entry =>
    entry_covered (resolve_entry (analysis_aliases state) entry)
      (analysis_entries state)) required.

Definition take_step cost state : analysis_error + analysis_state :=
  match cost with
  | ProcedureCallStep required _ | ProcedureSpawnStep required =>
      if bool_decide (entries_available required state) then
        if bool_decide (analysis_open state = ∅)
        then take_plain_step NonAtomicStep state
        else inl NonAtomicWhileOpen
      else inl MissingProcedureMask
  | NoStep | AtomicStep | NonAtomicStep => take_plain_step cost state
  end.

#[global] Arguments take_step : simpl never.

(** A write to the local at [level] forgets the entries and aliases naming
    it. *)
Definition invalidate (level : nat) state : analysis_state :=
  AnalysisState
    (filter (fun entry => entry_mentions level entry = false)
      (analysis_entries state))
    (analysis_records state)
    (filter (fun binding => binding.2 <> AtomLevel level)
      (analysis_aliases state))
    (analysis_step_taken state) (analysis_in_atomic state).

Definition grant_state (granted : gset mask_entry) state : analysis_state :=
  AnalysisState
    (analysis_entries state ∪
      set_map (resolve_entry (analysis_aliases state)) granted)
    (analysis_records state) (analysis_aliases state)
    (analysis_step_taken state) (analysis_in_atomic state).

(** A leaf takes its step, then writes its target, then receives the
    entries its callee grants. *)
Definition take_leaf cost (written : option nat) state :
    analysis_error + analysis_state :=
  match take_step cost state with
  | inl error => inl error
  | inr stepped =>
      let written_state :=
        match written with
        | Some level => invalidate level stepped
        | None => stepped
        end in
      inr match cost with
        | ProcedureCallStep _ granted => grant_state granted written_state
        | _ => written_state
        end
  end.

(** The entry an opening consumes: the exact instance if available,
    otherwise the declaration-wide entry. *)
Definition select_entry (invariant : inv_id) (key : access_key)
    (entries : gset mask_entry) : option mask_entry :=
  if bool_decide (key <> None /\ (invariant, key) ∈ entries)
  then Some (invariant, key)
  else if bool_decide ((invariant, None) ∈ entries)
  then Some (invariant, None)
  else None.

(** The entry a record restores: an exact instance under the opening's own
    key, which stays valid when the locals it was resolved to are
    written. *)
Definition consumed_entry (invariant : inv_id) (key : access_key)
    (selected : mask_entry) : mask_entry :=
  (invariant, match selected.2 with Some _ => key | None => None end).

Definition open_invariant (invariant : inv_id) (key : access_key) state :
    analysis_error + analysis_state :=
  if bool_decide (invariant ∈ analysis_open state) then
    inl (ReentrantInvariant invariant)
  else match select_entry invariant
      (resolve_key (analysis_aliases state) key) (analysis_entries state) with
  | Some entry =>
      inr (AnalysisState (analysis_entries state ∖ {[entry]})
        ((invariant, key, consumed_entry invariant key entry) ::
          analysis_records state)
        (analysis_aliases state)
        (analysis_step_taken state) (analysis_in_atomic state))
  | None => inl (MissingInvariant invariant)
  end.

(** A fold closes the innermost open invariant, restoring the entry it
    consumed, or allocates a fresh instance. *)
Definition fold_invariant (invariant : inv_id) (key : access_key) state :
    analysis_state :=
  let fresh :=
    AnalysisState
      ({[resolve_entry (analysis_aliases state) (invariant, key)]} ∪
        analysis_entries state)
      (analysis_records state) (analysis_aliases state)
      (analysis_step_taken state) (analysis_in_atomic state) in
  match analysis_records state with
  | record :: rest =>
      if decide (record_invariant record = invariant) then
        AnalysisState
          ({[resolve_entry (analysis_aliases state) (record_consumed record)]}
            ∪ analysis_entries state) rest (analysis_aliases state)
          (match rest with [] => false | _ => analysis_step_taken state end)
          (analysis_in_atomic state)
      else fresh
  | [] => fresh
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

(** Entering the scope of the local at [level], an alias of [alias] if
    given. *)
Definition enter_scope (level : nat) (alias : option key_atom) state :
    analysis_state :=
  AnalysisState (analysis_entries state) (analysis_records state)
    (match alias with
     | Some atom =>
         <[level := resolve_atom (analysis_aliases state) atom]>
           (analysis_aliases state)
     | None => delete level (analysis_aliases state)
     end)
    (analysis_step_taken state) (analysis_in_atomic state).

(** Leaving the scope of the local at [level], entered in [outer], forgets
    the entries naming it that were not available on entry and restores
    the binding of [level] in [outer]; no open invariant may name it. *)
Definition leave_scope (level : nat) (outer state : analysis_state) :
    analysis_state :=
  AnalysisState
    (filter (fun entry => entry_mentions level entry = false \/
        entry ∈ analysis_entries outer)
      (analysis_entries state))
    (analysis_records state)
    (partial_alter (fun _ => analysis_aliases outer !! level) level
      (analysis_aliases state))
    (analysis_step_taken state) (analysis_in_atomic state).

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
  analysis_records exit = analysis_records state /\
  analysis_aliases exit = analysis_aliases state.
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
    (Hentries & Hrecords & _).
  unfold analysis_mask, analysis_open. rewrite Hentries, Hrecords. done.
Qed.

Lemma take_step_plain cost state exit :
  take_step cost state = inr exit ->
  exists plain, take_plain_step plain state = inr exit.
Proof.
  unfold take_step. destruct cost; eauto.
  all: destruct (bool_decide (entries_available _ _)); last discriminate.
  all: destruct (bool_decide (analysis_open state = ∅)); last discriminate.
  all: eauto.
Qed.

Lemma take_step_preserves_state cost state exit :
  take_step cost state = inr exit ->
  analysis_entries exit = analysis_entries state /\
  analysis_records exit = analysis_records state /\
  analysis_aliases exit = analysis_aliases state.
Proof.
  intros Hstep. destruct (take_step_plain _ _ _ Hstep) as [plain Hplain].
  exact (take_plain_step_preserves_state _ _ _ Hplain).
Qed.

Lemma take_step_preserves_sets cost state exit :
  take_step cost state = inr exit ->
  analysis_mask exit = analysis_mask state /\
  analysis_open exit = analysis_open state.
Proof.
  intros Hstep. destruct (take_step_plain _ _ _ Hstep) as [plain Hplain].
  exact (take_plain_step_preserves_sets _ _ _ Hplain).
Qed.

Lemma take_step_preserves_records cost state exit :
  take_step cost state = inr exit ->
  analysis_records exit = analysis_records state.
Proof. intros Hstep. apply (take_step_preserves_state _ _ _ Hstep). Qed.

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
  intros Hstep. destruct (take_step_plain _ _ _ Hstep) as [plain Hplain].
  exact (take_plain_step_preserves_in_atomic _ _ _ Hplain).
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

Lemma entry_declarations_resolve aliases entries :
  entry_declarations (set_map (resolve_entry aliases) entries) =
    entry_declarations entries.
Proof.
  unfold entry_declarations. apply set_eq. intros invariant.
  rewrite !elem_of_map. split.
  - intros (entry & -> & Hentry). apply elem_of_map in Hentry as
      (original & -> & Horiginal). exists original. auto.
  - intros (entry & -> & Hentry). exists (resolve_entry aliases entry).
    split; [reflexivity|]. apply elem_of_map. eauto.
Qed.

Lemma entry_declarations_filter (P : mask_entry -> Prop)
    `{forall entry, Decision (P entry)} entries :
  entry_declarations (filter P entries) ⊆ entry_declarations entries.
Proof.
  unfold entry_declarations. intros invariant Hin.
  apply elem_of_map in Hin as (entry & -> & Hentry).
  apply elem_of_filter in Hentry as [_ Hentry].
  apply elem_of_map. eauto.
Qed.

(** Every required entry is covered: its declaration is available. *)
Lemma entries_available_mask required state :
  entries_available required state -> analysis_open state = ∅ ->
  entry_declarations required ⊆ analysis_mask state.
Proof.
  intros Havailable Hclosed invariant Hin.
  unfold analysis_mask. rewrite Hclosed, difference_empty_L.
  unfold entry_declarations in *.
  apply elem_of_map in Hin as (entry & -> & Hentry).
  destruct (Havailable entry Hentry) as [Hexact|Hwide];
    apply elem_of_map; eexists; split; [|exact Hexact| |exact Hwide];
    reflexivity.
Qed.

Lemma procedure_call_step_success required granted state exit :
  take_step (ProcedureCallStep required granted) state = inr exit ->
  entries_available required state /\ analysis_open state = ∅ /\
  exit = state.
Proof.
  unfold take_step.
  destruct (bool_decide (entries_available required state)) eqn:Havailable;
    last discriminate.
  apply bool_decide_eq_true in Havailable.
  destruct (bool_decide (analysis_open state = ∅)) eqn:Hclosed;
    last discriminate.
  apply bool_decide_eq_true in Hclosed.
  unfold take_plain_step. rewrite (bool_decide_eq_true_2 _ Hclosed), orb_true_r.
  intros [= <-]. auto.
Qed.

Lemma procedure_spawn_step_success required state exit :
  take_step (ProcedureSpawnStep required) state = inr exit ->
  entries_available required state /\ analysis_open state = ∅ /\
  exit = state.
Proof.
  unfold take_step.
  destruct (bool_decide (entries_available required state)) eqn:Havailable;
    last discriminate.
  apply bool_decide_eq_true in Havailable.
  destruct (bool_decide (analysis_open state = ∅)) eqn:Hclosed;
    last discriminate.
  apply bool_decide_eq_true in Hclosed.
  unfold take_plain_step. rewrite (bool_decide_eq_true_2 _ Hclosed), orb_true_r.
  intros [= <-]. auto.
Qed.

Lemma atomic_step_preserves_sets state exit :
  take_step AtomicStep state = inr exit ->
  analysis_mask exit = analysis_mask state /\
  analysis_open exit = analysis_open state.
Proof. apply take_step_preserves_sets. Qed.

Lemma atomic_step_preserves_state state exit :
  take_step AtomicStep state = inr exit ->
  analysis_entries exit = analysis_entries state /\
  analysis_records exit = analysis_records state /\
  analysis_aliases exit = analysis_aliases state.
Proof. apply take_step_preserves_state. Qed.

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
  intros Hopen _ Hstep.
  apply procedure_call_step_success in Hstep as (_ & Hclosed & _).
  contradiction.
Qed.

Lemma procedure_spawn_rejected_while_open required state exit :
  analysis_open state ≠ ∅ -> analysis_in_atomic state = false ->
  take_step (ProcedureSpawnStep required) state <> inr exit.
Proof.
  intros Hopen _ Hstep.
  apply procedure_spawn_step_success in Hstep as (_ & Hclosed & _).
  contradiction.
Qed.

(** ** Leaves *)

(** The entries a leaf's callee grants. *)
Definition cost_granted (cost : step_cost) : gset mask_entry :=
  match cost with
  | ProcedureCallStep _ granted => granted
  | _ => ∅
  end.

Lemma take_leaf_step cost written state exit :
  take_leaf cost written state = inr exit ->
  exists stepped, take_step cost state = inr stepped /\
    exit = match cost with
      | ProcedureCallStep _ granted =>
          grant_state granted
            match written with
            | Some level => invalidate level stepped
            | None => stepped
            end
      | _ =>
          match written with
          | Some level => invalidate level stepped
          | None => stepped
          end
      end.
Proof.
  unfold take_leaf. destruct (take_step cost state) as [error|stepped];
    [discriminate|]. intros [= <-]. eauto.
Qed.

Lemma take_leaf_step_taken cost written state exit :
  take_leaf cost written state = inr exit ->
  exists stepped, take_step cost state = inr stepped /\
    analysis_step_taken exit = analysis_step_taken stepped.
Proof.
  intros Hleaf. destruct (take_leaf_step _ _ _ _ Hleaf) as
    (stepped & Hstep & ->).
  exists stepped. split; [exact Hstep|]. destruct cost, written; reflexivity.
Qed.

Lemma take_leaf_preserves_records cost written state exit :
  take_leaf cost written state = inr exit ->
  analysis_records exit = analysis_records state.
Proof.
  intros Hleaf. destruct (take_leaf_step _ _ _ _ Hleaf) as
    (stepped & Hstep & ->).
  rewrite <- (take_step_preserves_records _ _ _ Hstep).
  destruct cost, written; reflexivity.
Qed.

Lemma take_leaf_preserves_open cost written state exit :
  take_leaf cost written state = inr exit ->
  analysis_open exit = analysis_open state.
Proof.
  intros Hleaf. apply analysis_open_records.
  exact (take_leaf_preserves_records _ _ _ _ Hleaf).
Qed.

Lemma take_leaf_preserves_in_atomic cost written state exit :
  take_leaf cost written state = inr exit ->
  analysis_in_atomic exit = analysis_in_atomic state.
Proof.
  intros Hleaf. destruct (take_leaf_step _ _ _ _ Hleaf) as
    (stepped & Hstep & ->).
  rewrite <- (take_step_preserves_in_atomic _ _ _ Hstep).
  destruct cost, written; reflexivity.
Qed.

Lemma take_leaf_preserves_wf cost written state exit :
  state_wf state -> take_leaf cost written state = inr exit -> state_wf exit.
Proof.
  intros Hwf Hleaf. unfold state_wf.
  rewrite (take_leaf_preserves_records _ _ _ _ Hleaf). exact Hwf.
Qed.

Lemma invalidate_mask level state :
  analysis_mask (invalidate level state) ⊆ analysis_mask state.
Proof.
  unfold analysis_mask, analysis_open, invalidate. cbn.
  pose proof (entry_declarations_filter
    (fun entry => entry_mentions level entry = false)
    (analysis_entries state)).
  set_solver.
Qed.

Lemma grant_state_mask granted state :
  analysis_mask (grant_state granted state) =
    analysis_mask state ∪ (entry_declarations granted ∖ analysis_open state).
Proof.
  unfold analysis_mask, analysis_open, grant_state. cbn.
  rewrite entry_declarations_union, entry_declarations_resolve. set_solver.
Qed.

(** A leaf makes available at most the declarations its callee grants. *)
Lemma take_leaf_mask cost written state exit :
  take_leaf cost written state = inr exit ->
  analysis_mask exit ⊆
    analysis_mask state ∪ entry_declarations (cost_granted cost).
Proof.
  intros Hleaf. destruct (take_leaf_step _ _ _ _ Hleaf) as
    (stepped & Hstep & ->).
  destruct (take_step_preserves_sets _ _ _ Hstep) as [Hmask Hopen].
  assert (Hwritten : analysis_mask (match written with
      | Some level => invalidate level stepped
      | None => stepped end) ⊆ analysis_mask state).
  { destruct written; [|by rewrite Hmask].
    etrans; [apply invalidate_mask|]. by rewrite Hmask. }
  destruct cost; cbn [cost_granted]; try (etrans; [exact Hwritten|set_solver]).
  rewrite grant_state_mask. set_solver.
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
    select_entry invariant (resolve_key (analysis_aliases state) key)
      (analysis_entries state) = Some entry /\
    exit = AnalysisState (analysis_entries state ∖ {[entry]})
      ((invariant, key, consumed_entry invariant key entry) ::
        analysis_records state)
      (analysis_aliases state)
      (analysis_step_taken state) (analysis_in_atomic state).
Proof.
  unfold open_invariant.
  destruct (bool_decide (invariant ∈ analysis_open state)); first discriminate.
  destruct (select_entry invariant (resolve_key (analysis_aliases state) key)
    (analysis_entries state)) as [entry|]; [|discriminate].
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
  apply elem_of_list_to_set. apply elem_of_list_In in Hin.
  apply in_map_iff in Hin as (record & Hrecord & Hin).
  injection Hrecord as <- _. apply elem_of_list_In, in_map. exact Hin.
Qed.

(** A further instance of an open declaration: its key and the keys of the
    declaration's open instances are atoms, and pairwise distinct. *)
Definition nested_admissible (invariant : inv_id) (key : access_key) state :
    bool :=
  bool_decide (key <> None) &&
  forallb (fun record =>
    if decide (record_invariant record = invariant)
    then bool_decide (record_key record <> None /\ record_key record <> key)
    else true) (analysis_records state).

(** The entry a nested opening consumes: its own, or the declaration-wide
    entry an enclosing opening of the declaration holds. *)
Definition nested_entry (invariant : inv_id) (key : access_key) state :
    option mask_entry :=
  match select_entry invariant (resolve_key (analysis_aliases state) key)
      (analysis_entries state) with
  | Some entry => Some entry
  | None =>
      if existsb (fun record =>
          bool_decide (record_consumed record = (invariant, None)))
        (analysis_records state)
      then Some (invariant, None) else None
  end.

(** Every open instance of [invariant] has an atom key among
    [excluded]. *)
Definition records_covered (invariant : inv_id)
    (excluded : list access_key) (records : list open_record) : bool :=
  forallb (fun record =>
    if decide (record_invariant record = invariant)
    then bool_decide (record_key record <> None /\
      record_key record ∈ excluded)
    else true) records.

(** Opening an instance: of a closed declaration, or a further instance of
    an open one that is known to differ from its open instances, the
    [excluded] ones. *)
Definition open_access (invariant : inv_id) (key : access_key)
    (excluded : list access_key) state :
    analysis_error + analysis_state :=
  if bool_decide (invariant ∈ analysis_open state) then
    if nested_admissible invariant key state &&
      records_covered invariant excluded (analysis_records state) then
      match nested_entry invariant key state with
      | Some entry =>
          inr (AnalysisState (analysis_entries state ∖ {[entry]})
            ((invariant, key, consumed_entry invariant key entry) ::
              analysis_records state)
            (analysis_aliases state)
            (analysis_step_taken state) (analysis_in_atomic state))
      | None => inl (MissingInvariant invariant)
      end
    else inl (ReentrantInvariant invariant)
  else open_invariant invariant key state.

Lemma open_invariant_access invariant key excluded state exit :
  open_invariant invariant key state = inr exit ->
  open_access invariant key excluded state = inr exit.
Proof.
  intros Hopen. unfold open_access.
  rewrite bool_decide_false; [exact Hopen|].
  exact (proj1 (open_invariant_success _ _ _ _ Hopen)).
Qed.

Lemma open_access_fresh invariant key excluded state exit :
  invariant ∉ analysis_open state ->
  open_access invariant key excluded state = inr exit ->
  open_invariant invariant key state = inr exit.
Proof.
  intros Hclosed. unfold open_access. rewrite bool_decide_false; [done|].
  exact Hclosed.
Qed.

Lemma records_covered_nil invariant state :
  invariant ∈ analysis_open state ->
  records_covered invariant [] (analysis_records state) = false.
Proof.
  unfold analysis_open. intros Hin.
  apply elem_of_list_to_set, elem_of_list_In, in_map_iff in Hin
    as (record & Hinvariant & Hrecord).
  unfold records_covered. apply not_true_iff_false. rewrite forallb_forall.
  intros Hall. specialize (Hall record Hrecord).
  rewrite decide_True in Hall by exact Hinvariant.
  apply bool_decide_eq_true in Hall as [_ Hnil].
  apply elem_of_nil in Hnil. exact Hnil.
Qed.

(** Without excluded instances, only a closed declaration is opened. *)
Lemma open_access_nil invariant key state exit :
  open_access invariant key [] state = inr exit ->
  open_invariant invariant key state = inr exit.
Proof.
  intros Hopen.
  destruct (decide (invariant ∈ analysis_open state)) as [Hin|Hout].
  - unfold open_access in Hopen. rewrite bool_decide_true in Hopen by exact Hin.
    rewrite records_covered_nil in Hopen by exact Hin.
    rewrite andb_false_r in Hopen. discriminate.
  - exact (open_access_fresh _ _ _ _ _ Hout Hopen).
Qed.

Lemma open_access_records invariant key excluded state exit :
  open_access invariant key excluded state = inr exit ->
  exists entry,
    exit = AnalysisState (analysis_entries state ∖ {[entry]})
      ((invariant, key, consumed_entry invariant key entry) ::
        analysis_records state)
      (analysis_aliases state)
      (analysis_step_taken state) (analysis_in_atomic state).
Proof.
  unfold open_access.
  destruct (bool_decide (invariant ∈ analysis_open state)).
  - destruct (nested_admissible invariant key state && _); [|discriminate].
    destruct (nested_entry invariant key state) as [entry|]; [|discriminate].
    intros [= <-]. eauto.
  - intros Hopen. destruct (open_invariant_records _ _ _ _ Hopen)
      as (entry & _ & ->). eauto.
Qed.

Lemma open_access_preserves_in_atomic invariant key excluded state exit :
  open_access invariant key excluded state = inr exit ->
  analysis_in_atomic exit = analysis_in_atomic state.
Proof.
  intros Hopen.
  destruct (open_access_records _ _ _ _ _ Hopen) as (entry & ->).
  reflexivity.
Qed.

(** A nested opening leaves the open declarations, hence the mask, alone. *)
Lemma open_access_nested invariant key excluded state exit :
  invariant ∈ analysis_open state ->
  open_access invariant key excluded state = inr exit ->
  nested_admissible invariant key state = true /\
  records_covered invariant excluded (analysis_records state) = true /\
  analysis_open exit = analysis_open state /\
  analysis_mask exit = analysis_mask state.
Proof.
  intros Hopen_state Hopen. pose proof Hopen as Hrecords.
  unfold open_access in Hopen. rewrite bool_decide_true in Hopen;
    [|exact Hopen_state].
  destruct (nested_admissible invariant key state) eqn:Hadmissible;
    [|discriminate].
  destruct (records_covered invariant excluded (analysis_records state))
    eqn:Hcovered; [|discriminate].
  destruct (nested_entry invariant key state) as [entry|] eqn:Hentry;
    [|discriminate].
  injection Hopen as <-.
  assert (Hdeclaration : entry.1 = invariant).
  { unfold nested_entry in Hentry.
    destruct (select_entry invariant _ _) as [selected|] eqn:Hselect.
    - injection Hentry as <-.
      exact (proj2 (select_entry_sound _ _ _ _ Hselect)).
    - destruct (existsb _ _); [|discriminate]. injection Hentry as <-.
      reflexivity. }
  assert (Hopen_exit : analysis_open (AnalysisState
      (analysis_entries state ∖ {[entry]})
      ((invariant, key, consumed_entry invariant key entry) ::
        analysis_records state)
      (analysis_aliases state) (analysis_step_taken state)
      (analysis_in_atomic state)) = analysis_open state).
  { unfold analysis_open in *. cbn. set_solver. }
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hopen_exit|].
  unfold analysis_mask. rewrite Hopen_exit. cbn [analysis_entries].
  apply set_eq. intros other.
  rewrite !elem_of_difference. split.
  - intros [Hin Hclosed]. split; [|exact Hclosed].
    unfold entry_declarations in *. apply elem_of_map in Hin
      as (other_entry & -> & Hother). apply elem_of_map.
    exists other_entry. split; [reflexivity|]. set_solver.
  - intros [Hin Hclosed]. split; [|exact Hclosed].
    unfold entry_declarations in *. apply elem_of_map in Hin
      as (other_entry & -> & Hother). apply elem_of_map.
    exists other_entry. split; [reflexivity|].
    apply elem_of_difference. split; [exact Hother|].
    intros Heq. apply elem_of_singleton in Heq. subst other_entry.
    apply Hclosed. rewrite Hdeclaration. exact Hopen_state.
Qed.

(** Both kinds of opening add the declaration to the open set and remove it
    from the mask. *)
Lemma open_access_success invariant key excluded state exit :
  open_access invariant key excluded state = inr exit ->
  analysis_mask exit = analysis_mask state ∖ {[invariant]} /\
  analysis_open exit = {[invariant]} ∪ analysis_open state.
Proof.
  intros Hopen.
  destruct (decide (invariant ∈ analysis_open state)) as [Hnested|Hclosed].
  - destruct (open_access_nested _ _ _ _ _ Hnested Hopen)
      as (_ & _ & Hopen_exit & Hmask_exit).
    rewrite Hmask_exit, Hopen_exit. split.
    + apply set_eq. intros other. rewrite elem_of_difference, elem_of_singleton.
      split; [|tauto]. intros Hin. split; [exact Hin|]. intros ->.
      unfold analysis_mask in Hin. apply elem_of_difference in Hin as [_ Hin].
      contradiction.
    + set_solver.
  - destruct (open_invariant_success _ _ _ _
      (open_access_fresh _ _ _ _ _ Hclosed Hopen)) as (_ & _ & Hmask & Hopen').
    split; assumption.
Qed.

Lemma open_access_available invariant key excluded state exit :
  open_access invariant key excluded state = inr exit ->
  invariant ∈ analysis_mask state ∪ analysis_open state.
Proof.
  intros Hopen.
  destruct (decide (invariant ∈ analysis_open state)) as [Hnested|Hclosed].
  - apply elem_of_union_r. exact Hnested.
  - apply elem_of_union_l.
    exact (proj1 (proj2 (open_invariant_success _ _ _ _
      (open_access_fresh _ _ _ _ _ Hclosed Hopen)))).
Qed.

Lemma open_access_preserves_wf invariant key excluded state exit :
  state_wf state -> open_access invariant key excluded state = inr exit ->
  state_wf exit.
Proof.
  intros Hwf Hopen.
  destruct (decide (invariant ∈ analysis_open state)) as [Hnested|Hclosed].
  - pose proof (proj1 (open_access_nested _ _ _ _ _ Hnested Hopen))
      as Hadmissible.
    destruct (open_access_records _ _ _ _ _ Hopen) as (entry & ->).
    unfold state_wf in *. cbn. constructor; [|exact Hwf].
    intros Hin. apply elem_of_list_In in Hin.
    apply in_map_iff in Hin as (record & Hrecord & Hin).
    unfold nested_admissible in Hadmissible.
    apply andb_true_iff in Hadmissible as [_ Hall].
    rewrite forallb_forall in Hall. specialize (Hall record Hin).
    injection Hrecord as Hinvariant Hkey.
    rewrite decide_True in Hall; [|exact Hinvariant].
    apply bool_decide_eq_true in Hall as [_ Hdistinct]. contradiction.
  - apply (open_invariant_preserves_wf invariant key state exit Hwf).
    exact (open_access_fresh _ _ _ _ _ Hclosed Hopen).
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
    AnalysisState
      ({[resolve_entry (analysis_aliases state) (record_consumed record)]} ∪
        analysis_entries state) rest (analysis_aliases state)
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
  NoDup (map record_invariant (analysis_records state)) ->
  records_consume_own (analysis_records state) ->
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
  rewrite ?Hrecords in Hwf. cbn in Hwf.
  inversion Hwf as [|? ? Hfresh _]. subst.
  unfold records_consume_own in Hown. rewrite ?Hrecords in Hown.
  inversion Hown as [|? ? Hconsumed _]. subst.
  assert (Hrest : record_invariant record ∉
      (list_to_set (map record_invariant rest) : gset inv_id))
    by (rewrite elem_of_list_to_set; exact Hfresh).
  unfold analysis_mask, analysis_open. cbn [analysis_entries analysis_records].
  rewrite Hrecords. cbn [map list_to_set].
  rewrite entry_declarations_union, entry_declarations_singleton.
  cbn [resolve_entry fst]. rewrite Hconsumed.
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
    AnalysisState
      ({[resolve_entry (analysis_aliases state) (invariant, key)]} ∪
        analysis_entries state)
      (analysis_records state) (analysis_aliases state)
      (analysis_step_taken state) (analysis_in_atomic state)).
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
      | ViewLeaf =>
          take_leaf (leaf_cost Γ statement) (syntax_leaf_write Γ statement)
            state
      | ViewDone => inr state
      | ViewUnfold invariant key excluded =>
          open_access invariant key excluded state
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
              then inr (join_state then_state else_state)
              else inl IncompatibleBranches
          | inl error, _ | _, inl error => inl error
          end
      | ViewStructuredAccess _ _ => inl StructuredAccessRequiresCertificate
      | ViewAtomic body =>
          match take_step AtomicStep state with
          | inl error => inl error
          | inr outer =>
              let inner_entry := atomic_entry outer in
              match analyze_fuel fuel' inner_entry body with
              | inl error => inl error
              | inr inner =>
                  if bool_decide (analysis_records inner = analysis_records outer)
                  then inr (atomic_exit outer inner)
                  else inl AtomicBlockLeaksAccess
              end
          end
      | ViewScope _ alias body =>
          match analyze_fuel fuel' (enter_scope (length Γ) alias state) body with
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
    take_leaf (leaf_cost Γ statement) (syntax_leaf_write Γ statement) state =
      inr exit ->
    analysis_certificate Γ state statement exit
| CertDone Γ state statement :
    syntax_view Γ statement = ViewDone ->
    analysis_certificate Γ state statement state
| CertUnfold Γ state statement invariant key excluded exit :
    syntax_view Γ statement = ViewUnfold invariant key excluded ->
    open_access invariant key excluded state = inr exit ->
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
      (join_state then_exit else_exit)
| CertAtomic Γ state statement body outer inner :
    syntax_view Γ statement = ViewAtomic body ->
    take_step AtomicStep state = inr outer ->
    analysis_certificate Γ
      (atomic_entry outer) body inner ->
    analysis_records inner = analysis_records outer ->
    analysis_certificate Γ state statement
      (atomic_exit outer inner)
| CertScope Γ state statement d alias body inner :
    syntax_view Γ statement = ViewScope d alias body ->
    analysis_certificate (d :: Γ) (enter_scope (length Γ) alias state) body
      inner ->
    leave_scope_admissible (length Γ) inner = true ->
    analysis_certificate Γ state statement
      (leave_scope (length Γ) state inner).

Lemma analysis_certificate_preserves_in_atomic
    {Γ entry statement exit}
    (certificate : analysis_certificate Γ entry statement exit) :
  analysis_in_atomic exit = analysis_in_atomic entry.
Proof.
  induction certificate; simpl.
  - eapply take_leaf_preserves_in_atomic. exact e0.
  - reflexivity.
  - eapply open_access_preserves_in_atomic. exact e0.
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
  | CertScope _ _ _ _ _ _ _ _ body_certificate _ =>
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
  | CertUnfold _ _ _ _ _ _ _ _ _ => 1
  | CertFold _ _ _ _ _ _ _ => 1
  | CertSequence _ _ _ _ _ _ _ _ first_certificate second_certificate =>
      S (Nat.max (certificate_height first_certificate)
        (certificate_height second_certificate))
  | CertConditional _ _ _ _ _ _ _ _ then_certificate else_certificate _ _ =>
      S (Nat.max (certificate_height then_certificate)
        (certificate_height else_certificate))
  | CertAtomic _ _ _ _ _ _ _ _ body_certificate _ =>
      S (certificate_height body_certificate)
  | CertScope _ _ _ _ _ _ _ _ body_certificate _ =>
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
          then inr (join_state then_state else_state)
          else inl IncompatibleBranches
      | inl error, _ | _, inl error => inl error
      end = inr exit).
    rewrite Hthen, Helse. exact Hrun.
  - discriminate.
  - destruct (take_step AtomicStep state) as [error|outer] eqn:Hstep;
      try discriminate.
    destruct (analyze_fuel fuel
      (atomic_entry outer) body) as [error|inner]
      eqn:Hbody; try discriminate.
    apply IH in Hbody.
    change (analyze_fuel (S fuel)
      (atomic_entry outer) body = inr inner) in Hbody.
    change (match analyze_fuel (S fuel)
      (atomic_entry outer) body with
      | inl error => inl error
      | inr inner =>
          if bool_decide (analysis_records inner = analysis_records outer)
          then inr (atomic_exit outer inner)
          else inl AtomicBlockLeaksAccess
      end = inr exit).
    rewrite Hbody. exact Hrun.
  - destruct (analyze_fuel fuel (enter_scope (length Γ) alias state) body)
      as [error|inner] eqn:Hbody; try discriminate.
    apply IH in Hbody.
    change (analyze_fuel (S fuel) (enter_scope (length Γ) alias state) body =
      inr inner) in Hbody.
    change (match analyze_fuel (S fuel) (enter_scope (length Γ) alias state)
      body with
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
  - pose proof (syntax_scope_body_smaller Γ statement d alias body e) as Hbody.
    lia.
Qed.

(** Invariants a statement may add to the available mask: fold targets and
    procedure-call grants. *)
Definition step_cost_grants (cost : step_cost) : gset inv_id :=
  match cost with
  | ProcedureCallStep _ granted => entry_declarations granted
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
      | ViewScope _ _ body => statement_allocations_fuel fuel' body
      | ViewDone | ViewUnfold _ _ _ => ∅
      end
  end.

Definition statement_allocations {Γ} (statement : syntax_statement Γ) :
    gset inv_id :=
  statement_allocations_fuel (syntax_size Γ statement) statement.

Lemma take_leaf_resources_bound cost written state exit :
  take_leaf cost written state = inr exit ->
  analysis_mask exit ∪ analysis_open exit ⊆
    analysis_mask state ∪ analysis_open state ∪ step_cost_grants cost.
Proof.
  intros Hleaf.
  pose proof (take_leaf_mask _ _ _ _ Hleaf) as Hmask.
  rewrite (take_leaf_preserves_open _ _ _ _ Hleaf).
  destruct cost; cbn [cost_granted step_cost_grants] in *; set_solver.
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
    cbn [resolve_entry fst]. abstract_declarations. apply elem_of_subseteq. intros x Hx.
    destruct (decide (x = invariant)); set_solver.
  - unfold records_consume_own in Hown. rewrite ?Hrecords in Hown.
    inversion Hown as [|? ? Hconsumed _]. subst.
    destruct (decide (record_invariant record = invariant));
      unfold analysis_mask, analysis_open; cbn [analysis_entries
        analysis_records]; rewrite Hrecords, entry_declarations_union,
        entry_declarations_singleton; cbn [map list_to_set];
      cbn [resolve_entry fst]; [rewrite Hconsumed|];
      generalize (list_to_set (map record_invariant rest) : gset inv_id) as R;
      generalize (entry_declarations (analysis_entries state)) as D;
      generalize (record_invariant record) as i;
      clear; intros i D R; apply elem_of_subseteq; intros x Hx;
      destruct (decide (x ∈ R)); destruct (decide (x = i));
      destruct (decide (x = invariant)); set_solver.
Qed.

Lemma open_access_consume_own invariant key excluded state exit :
  records_consume_own (analysis_records state) ->
  open_access invariant key excluded state = inr exit ->
  records_consume_own (analysis_records exit).
Proof.
  intros Hown Hopen.
  destruct (open_access_records _ _ _ _ _ Hopen) as (entry & ->).
  constructor; [reflexivity | exact Hown].
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
  - rewrite (take_leaf_preserves_records _ _ _ _ e0). exact Hown.
  - exact Hown.
  - eapply open_access_consume_own; eassumption.
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
  - pose proof (take_leaf_resources_bound _ _ _ _ e0). set_solver.
  - set_solver.
  - pose proof (open_access_available _ _ _ _ _ e0) as Havailable.
    apply open_access_success in e0 as (Hmask & Hopen).
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
    assert (Hjoin_open : analysis_open (join_state then_exit else_exit) = analysis_open then_exit)
      by reflexivity.
    assert (Hjoin_mask : analysis_mask (join_state then_exit else_exit) ⊆ analysis_mask then_exit).
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
      (atomic_entry outer))).
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
    assert (excluded0 = excluded) by congruence. subst excluded0.
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
    injection Hview as <- <- Hbody.
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
  - eapply take_leaf_preserves_wf; eauto.
  - exact Hwf.
  - eapply open_access_preserves_wf; eauto.
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
      (atomic_entry outer) body) as [error|inner] eqn:Hbody;
      try discriminate.
    destruct (bool_decide (analysis_records inner = analysis_records outer))
      eqn:Hscope; last discriminate.
    apply bool_decide_eq_true in Hscope.
    inversion Hanalyze; subst exit.
    eapply CertAtomic; eauto.
  - destruct (analyze_fuel fuel (enter_scope (length Γ) alias state) body)
      as [error|inner] eqn:Hbody; try discriminate.
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

(** The state after a conditional, the state in which a trusted block's
    body is analyzed, and the state after the block. *)
Notation join_state then_exit else_exit :=
  (AnalysisState
    (entries_meet (analysis_entries then_exit) (analysis_entries else_exit))
    (analysis_records then_exit)
    (aliases_meet (analysis_aliases then_exit) (analysis_aliases else_exit))
    (analysis_step_taken then_exit || analysis_step_taken else_exit)
    (analysis_in_atomic then_exit)).
(** A state with the given entries and nothing open. *)
Notation closed_state entries := (AnalysisState entries [] ∅ false false).
Notation atomic_entry outer :=
  (AnalysisState (analysis_entries outer) (analysis_records outer)
    (analysis_aliases outer) (analysis_step_taken outer) true).
Notation atomic_exit outer inner :=
  (AnalysisState (analysis_entries inner) (analysis_records inner)
    (analysis_aliases inner)
    (analysis_step_taken outer || analysis_step_taken inner)
    (analysis_in_atomic outer)).
End AnalysisView.
