From Coq Require Import List Lia ZArith Wellfounded.
From stdpp Require Import gmap sets.

From raven Require Import verification.expressions verification.assertions
  verification.resources.

Import ListNotations.

(** * Mask inference

    The invariant instances a declaration may need, as in Raven: an invariant
    application in a predicate or invariant body, or in a procedure's
    precondition, requires its instance, and a mentioned predicate or
    invariant contributes what its own body requires, with the mention's
    arguments substituted for its formals.  Instances are named by keys over
    the declaration's formals and literals; an application with an argument
    of another form requires every instance of its invariant.  The
    requirements of the predicates and invariants are the least fixed point
    of this dependency, reached within an explicit bound.  A procedure grants
    the instances its postcondition names with arguments over its formals,
    its return value and literals. *)
Module Masks.
Import Core Assertion Resource.

(** An argument as a mask key sees it. *)
Inductive template_atom :=
| TemplateFormal (index : nat)
| TemplateReturn
| TemplateBool (value : bool)
| TemplateInt (value : Z)
| TemplateUnit.

#[global] Instance template_atom_eq_decision : EqDecision template_atom.
Proof. solve_decision. Defined.

#[global] Program Instance template_atom_countable : Countable template_atom :=
  inj_countable'
    (fun atom => match atom with
      | TemplateFormal index => inl index
      | TemplateReturn => inr (inl ())
      | TemplateBool value => inr (inr (inl value))
      | TemplateInt value => inr (inr (inr (inl value)))
      | TemplateUnit => inr (inr (inr (inr ())))
      end)
    (fun code => match code with
      | inl index => TemplateFormal index
      | inr (inl _) => TemplateReturn
      | inr (inr (inl value)) => TemplateBool value
      | inr (inr (inr (inl value))) => TemplateInt value
      | inr (inr (inr (inr _))) => TemplateUnit
      end) _.
Next Obligation. intros []; reflexivity. Qed.

(** [None] names every instance. *)
Definition template_key : Type := option (list template_atom).
Definition template_entry : Type := (inv_id * template_key)%type.
Definition template_mask : Type := gset template_entry.

(** The declarations of a mask. *)
Definition template_declarations (mask : template_mask) : gset inv_id :=
  set_map fst mask.

(** The key of arguments that are all atoms. *)
Fixpoint all_atoms (arguments : list (option template_atom)) : template_key :=
  match arguments with
  | [] => Some []
  | Some atom :: rest => (atom ::.) <$> all_atoms rest
  | None :: _ => None
  end.

(** A key with the arguments of a mention substituted for the mentioned
    declaration's formals. *)
Definition substitute_atom (arguments : list (option template_atom))
    (atom : template_atom) : option template_atom :=
  match atom with
  | TemplateFormal index => mjoin (arguments !! index)
  | TemplateReturn => None
  | _ => Some atom
  end.

Definition substitute_entry (arguments : list (option template_atom))
    (entry : template_entry) : template_entry :=
  (entry.1, entry.2 ≫= fun atoms => all_atoms (map (substitute_atom arguments) atoms)).

(** A predicate or an invariant. *)
Inductive declaration :=
| DeclPredicate (predicate : pred_id)
| DeclInvariant (invariant : inv_id).

#[global] Instance declaration_eq_decision : EqDecision declaration.
Proof. solve_decision. Defined.

#[global] Program Instance declaration_countable : Countable declaration :=
  inj_countable'
    (fun declaration => match declaration with
      | DeclPredicate predicate => inl predicate
      | DeclInvariant invariant => inr invariant
      end)
    (fun code => match code with
      | inl predicate => DeclPredicate predicate
      | inr invariant => DeclInvariant invariant
      end) _.
Next Obligation. intros []; reflexivity. Qed.

(** A predicate or invariant application with its argument atoms. *)
Inductive application :=
| AppInvariant (invariant : inv_id) (arguments : list (option template_atom))
| AppPredicate (predicate : pred_id) (arguments : list (option template_atom)).

(** What each predicate and invariant requires. *)
Notation requirements := (gmap declaration template_mask).

Definition required_by (needs : requirements) (declaration : declaration) :
    template_mask :=
  default ∅ (needs !! declaration).

(** The entries an application requires. *)
Definition application_mask (needs : requirements) (app : application) :
    template_mask :=
  match app with
  | AppInvariant invariant arguments =>
      {[(invariant, all_atoms arguments)]} ∪
        set_map (substitute_entry arguments)
          (required_by needs (DeclInvariant invariant))
  | AppPredicate predicate arguments =>
      set_map (substitute_entry arguments)
        (required_by needs (DeclPredicate predicate))
  end.

Definition applications_mask (needs : requirements)
    (apps : list application) : template_mask :=
  ⋃ (map (application_mask needs) apps).

Section WithSignature.
Context {RAs : RAValueConfig} {Logic : LogicSignature}.

(** The atom of an argument: a formal, the bound variable at level
    [return_level] as the return value, or a literal. *)
Definition expr_atom {F Δ t} (return_level : option nat)
    (argument : expr F Δ t) : option template_atom :=
  match argument with
  | ERef (RefFormal formal) => Some (TemplateFormal (member_index formal))
  | ERef (RefBound bound) =>
      if bool_decide (return_level = Some (length Δ - S (member_index bound)))
      then Some TemplateReturn else None
  | EVal value =>
      match value with
      | VBool value => Some (TemplateBool value)
      | VInt value => Some (TemplateInt value)
      | VUnit => Some TemplateUnit
      | _ => None
      end
  | _ => None
  end.

Fixpoint expr_list_atoms {F Δ ts} (return_level : option nat)
    (arguments : expr_list F Δ ts) : list (option template_atom) :=
  match arguments with
  | ExprNil => []
  | ExprCons argument rest =>
      expr_atom return_level argument :: expr_list_atoms return_level rest
  end.

(** The predicate and invariant applications of an assertion. *)
Fixpoint applications {F Δ} (return_level : option nat)
    (assertion : core_assertion F Δ) : list application :=
  match assertion with
  | CExists _ body | CForall _ body => applications return_level body
  | CIte _ first second | CAnd first second =>
      applications return_level first ++ applications return_level second
  | CInvariant invariant arguments =>
      [AppInvariant invariant (expr_list_atoms return_level arguments)]
  | CPredicate predicate arguments =>
      [AppPredicate predicate (expr_list_atoms return_level arguments)]
  | _ => []
  end.

(** The declarations of a program. *)
Record declarations := Declarations {
  declared_predicates : list pred_id;
  predicate_body : forall predicate,
    core_assertion (predicate_args predicate) [];
  declared_invariants : list inv_id;
  invariant_body : forall invariant,
    core_assertion (invariant_args invariant) [];
}.

Section WithDeclarations.
Variable D : declarations.

Definition declaration_list : list declaration :=
  map DeclPredicate (declared_predicates D) ++
  map DeclInvariant (declared_invariants D).

Definition body_applications (declaration : declaration) : list application :=
  match declaration with
  | DeclPredicate predicate => applications None (predicate_body D predicate)
  | DeclInvariant invariant => applications None (invariant_body D invariant)
  end.

(** One round: every declared predicate and invariant requires what its
    body's applications require. *)
Definition requirements_step (needs : requirements) : requirements :=
  list_to_map (map (fun declaration =>
    (declaration, applications_mask needs (body_applications declaration)))
    declaration_list).


(** ** Monotonicity and leastness *)

Definition requirements_le (left right : requirements) : Prop :=
  forall item,
    required_by left item ⊆ required_by right item.

Lemma lookup_list_to_map_graph {B} (f : declaration -> B)
    (items : list declaration) item :
  (list_to_map (map (fun other => (other, f other)) items)
    : gmap declaration B) !! item =
  if decide (item ∈ items) then Some (f item) else None.
Proof.
  induction items as [|other rest IH]; cbn; [reflexivity|].
  destruct (decide (item = other)) as [->|Hne].
  - rewrite lookup_insert. rewrite decide_True; [reflexivity|left].
  - rewrite lookup_insert_ne by congruence. rewrite IH.
    destruct (decide (item ∈ rest)) as [Hin|Hout],
      (decide (item ∈ other :: rest)) as [Hin'|Hout'];
      try reflexivity; exfalso.
    + apply Hout'. right. exact Hin.
    + apply elem_of_cons in Hin' as [Heq|Hin']; contradiction.
Qed.

Lemma required_by_step needs item :
  required_by (requirements_step needs) item =
  if decide (item ∈ declaration_list)
  then applications_mask needs (body_applications item) else ∅.
Proof.
  unfold required_by, requirements_step.
  rewrite (lookup_list_to_map_graph
    (fun item => applications_mask needs (body_applications item))).
  destruct (decide _); reflexivity.
Qed.

Lemma set_map_mono_entries (f : template_entry -> template_entry)
    (left right : template_mask) :
  left ⊆ right -> set_map (C:=template_mask) (D:=template_mask) f left ⊆ set_map f right.
Proof.
  intros Hle entry Hin. apply elem_of_map in Hin as (source & -> & Hsource).
  apply elem_of_map. exists source. split; [reflexivity|]. apply Hle. exact Hsource.
Qed.

Lemma application_mask_mono left right app :
  requirements_le left right ->
  application_mask left app ⊆ application_mask right app.
Proof.
  intros Hle. destruct app; cbn.
  - apply union_mono_l. apply set_map_mono_entries. apply Hle.
  - apply set_map_mono_entries. apply Hle.
Qed.

Lemma applications_mask_mono left right apps :
  requirements_le left right ->
  applications_mask left apps ⊆ applications_mask right apps.
Proof.
  intros Hle. unfold applications_mask.
  induction apps as [|app apps IH]; cbn; [reflexivity|].
  apply union_mono; [apply application_mask_mono; exact Hle|exact IH].
Qed.

Lemma requirements_step_mono left right :
  requirements_le left right ->
  requirements_le (requirements_step left) (requirements_step right).
Proof.
  intros Hle item. rewrite !required_by_step.
  destruct (decide _); [|reflexivity].
  apply applications_mask_mono. exact Hle.
Qed.

(** The Kleene iterates. *)
Definition requirements_approx (rounds : nat) : requirements :=
  Nat.iter rounds requirements_step ∅.

Lemma requirements_approx_succ rounds :
  requirements_approx (S rounds) =
    requirements_step (requirements_approx rounds).
Proof. reflexivity. Qed.

Lemma requirements_approx_chain rounds :
  requirements_le (requirements_approx rounds)
    (requirements_approx (S rounds)).
Proof.
  induction rounds as [|rounds IH].
  - intros item. change (requirements_approx 0) with (∅ : requirements).
    unfold required_by at 1. rewrite lookup_empty.
    apply empty_subseteq.
  - rewrite !requirements_approx_succ. apply requirements_step_mono.
    exact IH.
Qed.

Lemma requirements_approx_mono rounds rounds' :
  rounds <= rounds' ->
  requirements_le (requirements_approx rounds) (requirements_approx rounds').
Proof.
  induction 1 as [|rounds' _ IH]; [intros ?; reflexivity|].
  intros item. etrans; [apply IH|apply requirements_approx_chain].
Qed.

(** Every closed assignment contains the iterates. *)
Lemma requirements_approx_least needs :
  requirements_le (requirements_step needs) needs ->
  forall rounds, requirements_le (requirements_approx rounds) needs.
Proof.
  intros Hclosed rounds. induction rounds as [|rounds IH].
  - intros item. change (requirements_approx 0) with (∅ : requirements).
    unfold required_by at 1. rewrite lookup_empty.
    apply empty_subseteq.
  - rewrite requirements_approx_succ. intros item.
    etrans; [apply requirements_step_mono; exact IH|apply Hclosed].
Qed.

(** A stable iterate stays. *)
Lemma requirements_approx_stable rounds :
  requirements_step (requirements_approx rounds) = requirements_approx rounds ->
  forall rounds', rounds <= rounds' ->
  requirements_approx rounds' = requirements_approx rounds.
Proof.
  intros Hstable rounds' Hle. induction Hle as [|rounds' _ IH]; [reflexivity|].
  rewrite requirements_approx_succ, IH. exact Hstable.
Qed.


(** ** The universe of entries *)

Definition application_arguments (app : application) :
    list (option template_atom) :=
  match app with
  | AppInvariant _ arguments | AppPredicate _ arguments => arguments
  end.

Definition all_applications : list application :=
  mjoin (map body_applications declaration_list).

Definition literal_atom (atom : template_atom) : Prop :=
  match atom with
  | TemplateFormal _ | TemplateReturn => False
  | _ => True
  end.

#[global] Instance literal_atom_decision atom : Decision (literal_atom atom).
Proof. destruct atom; cbn; apply _. Defined.

(** The literals and invariants the bodies mention. *)
Definition literal_atoms : list template_atom :=
  filter literal_atom
    (omap id (mjoin (map application_arguments all_applications))).

Definition mentioned_invariants : list inv_id :=
  omap (fun app => match app with
    | AppInvariant invariant _ => Some invariant
    | AppPredicate _ _ => None
    end) all_applications.

Definition declaration_arity (item : declaration) : nat :=
  match item with
  | DeclPredicate predicate => length (predicate_args predicate)
  | DeclInvariant invariant => length (invariant_args invariant)
  end.

(** The atoms a declaration's keys may use. *)
Definition declaration_atoms (item : declaration) : list template_atom :=
  map TemplateFormal (seq 0 (declaration_arity item)) ++ literal_atoms.

Fixpoint words (atoms : list template_atom) (length : nat) :
    list (list template_atom) :=
  match length with
  | 0 => [[]]
  | S length' =>
      flat_map (fun atom => map (cons atom) (words atoms length')) atoms
  end.

Definition universe (item : declaration) : template_mask :=
  list_to_set (map (fun invariant => (invariant, None)) mentioned_invariants ++
    flat_map (fun invariant =>
      map (fun word => (invariant, Some word))
        (words (declaration_atoms item)
          (length (invariant_args invariant))))
      mentioned_invariants).

Definition universe_size_bound (item : declaration) : nat :=
  length mentioned_invariants +
  sum_list_with (fun invariant =>
    length (declaration_atoms item) ^ length (invariant_args invariant))
    mentioned_invariants.

(** The number of rounds after which the requirements are stable. *)
Definition requirements_bound : nat :=
  S (sum_list_with universe_size_bound (remove_dups declaration_list)).


Lemma words_spec atoms length' word :
  word ∈ words atoms length' <->
  length word = length' /\ Forall (fun atom => atom ∈ atoms) word.
Proof.
  revert word. induction length' as [|length' IH]; intros word; cbn.
  - rewrite elem_of_list_singleton. split.
    + intros ->. split; [reflexivity|constructor].
    + intros [Hlength _]. destruct word; [reflexivity|discriminate].
  - rewrite elem_of_list_In, in_flat_map. split.
    + intros (atom & Hatom & Hin). apply in_map_iff in Hin as (rest & <- & Hrest).
      apply elem_of_list_In, IH in Hrest as [Hlength Hall].
      split; [cbn; lia|]. constructor; [apply elem_of_list_In; exact Hatom|exact Hall].
    + intros [Hlength Hall]. destruct word as [|atom rest]; [discriminate|].
      inversion Hall as [|? ? Hatom Hrest]; subst.
      exists atom. split; [apply elem_of_list_In; exact Hatom|].
      apply in_map_iff. exists rest. split; [reflexivity|].
      apply elem_of_list_In, IH. split; [cbn in Hlength; lia|exact Hrest].
Qed.

Lemma universe_spec item invariant key :
  (invariant, key) ∈ universe item <->
  invariant ∈ mentioned_invariants /\
  (key = None \/ exists word, key = Some word /\
    length word = length (invariant_args invariant) /\
    Forall (fun atom => atom ∈ declaration_atoms item) word).
Proof.
  unfold universe. rewrite elem_of_list_to_set, elem_of_app, elem_of_list_fmap.
  rewrite elem_of_list_In, in_flat_map. split.
  - intros [(invariant' & [= <- <-] & Hin)|(invariant' & Hin & Hword)].
    + split; [exact Hin|left; reflexivity].
    + apply in_map_iff in Hword as (word & [= <- <-] & Hword).
      apply elem_of_list_In, words_spec in Hword as [Hlength Hall].
      split; [apply elem_of_list_In; exact Hin|right; eauto].
  - intros [Hin [->|(word & -> & Hlength & Hall)]].
    + left. exists invariant. auto.
    + right. exists invariant. split; [apply elem_of_list_In; exact Hin|].
      apply in_map_iff. exists word. split; [reflexivity|].
      apply elem_of_list_In, words_spec. auto.
Qed.

Lemma all_atoms_spec arguments word :
  all_atoms arguments = Some word <-> arguments = map Some word.
Proof.
  revert word. induction arguments as [|[atom|] rest IH]; intros word; cbn.
  - split; [intros [= <-]; reflexivity|].
    destruct word; [reflexivity|discriminate].
  - destruct (all_atoms rest) as [rest_word|] eqn:Hrest; cbn.
    + split.
      * intros [= <-]. cbn. f_equal. apply IH. reflexivity.
      * destruct word as [|atom' word']; [discriminate|]. cbn.
        intros [= -> Hrest_eq]. f_equal. apply IH in Hrest_eq. congruence.
    + split; [discriminate|]. destruct word as [|atom' word']; [discriminate|].
      cbn. intros [= -> Hrest_eq]. apply IH in Hrest_eq. congruence.
  - split; [discriminate|]. destruct word; cbn; discriminate.
Qed.


(** ** The atoms of a body *)

Lemma member_index_lt {Γ t} (variable : member Γ t) :
  member_index variable < length Γ.
Proof. induction variable; cbn; lia. Qed.

(** An atom of a declaration's own body: a formal or a literal. *)
Definition body_atom (arity : nat) (atom : template_atom) : Prop :=
  (exists index, atom = TemplateFormal index /\ index < arity) \/
  literal_atom atom.

Lemma expr_atom_body {F Δ t} (argument : expr F Δ t) atom :
  expr_atom None argument = Some atom -> body_atom (length F) atom.
Proof.
  destruct argument as [t reference|t value| | ]; cbn; try discriminate.
  - destruct reference as [t formal|t bound|t symbol]; cbn; try discriminate.
    all: try (rewrite bool_decide_false by discriminate; discriminate).
    intros [= <-]. left. eexists. split; [reflexivity|].
    apply member_index_lt.
  - destruct value; intros Hatom; try discriminate;
      injection Hatom as <-; right; exact I.
Qed.

Lemma expr_list_atoms_length {F Δ ts} return_level
    (arguments : expr_list F Δ ts) :
  length (expr_list_atoms return_level arguments) = length ts.
Proof. induction arguments; cbn; congruence. Qed.

Lemma expr_list_atoms_body {F Δ ts} (arguments : expr_list F Δ ts) atom :
  Some atom ∈ expr_list_atoms None arguments -> body_atom (length F) atom.
Proof.
  induction arguments as [|t ts argument rest IH]; cbn.
  - intros Hin. apply elem_of_nil in Hin. contradiction.
  - intros Hin. apply elem_of_cons in Hin as [Hhead|Hrest].
    + eapply expr_atom_body. symmetry. exact Hhead.
    + exact (IH Hrest).
Qed.

(** An application's argument count matches its declaration. *)
Definition application_arity_ok (app : application) : Prop :=
  match app with
  | AppInvariant invariant arguments =>
      length arguments = length (invariant_args invariant)
  | AppPredicate predicate arguments =>
      length arguments = length (predicate_args predicate)
  end.

Lemma applications_body {F Δ} (assertion : core_assertion F Δ) app :
  app ∈ applications None assertion ->
  application_arity_ok app /\
  forall atom, Some atom ∈ application_arguments app ->
    body_atom (length F) atom.
Proof.
  induction assertion; cbn; intros Hin;
    try (apply elem_of_nil in Hin; contradiction);
    try (apply elem_of_app in Hin as [Hin|Hin]; auto; fail);
    try auto.
  - apply elem_of_list_singleton in Hin as ->. cbn.
    split; [apply expr_list_atoms_length|apply expr_list_atoms_body].
  - apply elem_of_list_singleton in Hin as ->. cbn.
    split; [apply expr_list_atoms_length|apply expr_list_atoms_body].
Qed.

Lemma all_applications_body item app :
  item ∈ declaration_list -> app ∈ body_applications item ->
  app ∈ all_applications.
Proof.
  intros Hitem Happ. unfold all_applications.
  apply elem_of_list_join. exists (body_applications item).
  split; [exact Happ|]. apply elem_of_list_fmap. eauto.
Qed.

Lemma body_application_facts item app :
  item ∈ declaration_list -> app ∈ body_applications item ->
  application_arity_ok app /\
  (forall atom, Some atom ∈ application_arguments app ->
    atom ∈ declaration_atoms item) /\
  (forall invariant arguments, app = AppInvariant invariant arguments ->
    invariant ∈ mentioned_invariants).
Proof.
  intros Hitem Happ.
  pose proof (all_applications_body _ _ Hitem Happ) as Hall.
  assert (Hbody : application_arity_ok app /\
    forall atom, Some atom ∈ application_arguments app ->
      body_atom (declaration_arity item) atom).
  { destruct item; cbn in Happ |- *; apply (applications_body _ _ Happ). }
  destruct Hbody as [Harity Hatoms].
  split; [exact Harity|]. split.
  - intros atom Hatom. unfold declaration_atoms. apply elem_of_app.
    destruct (Hatoms atom Hatom) as [(index & -> & Hlt)|Hliteral].
    + left. apply elem_of_list_fmap. exists index. split; [reflexivity|].
      apply elem_of_seq. lia.
    + right. unfold literal_atoms. apply elem_of_list_filter.
      split; [exact Hliteral|]. apply elem_of_list_omap. exists (Some atom).
      split; [|reflexivity]. apply elem_of_list_join.
      exists (application_arguments app). split; [exact Hatom|].
      apply elem_of_list_fmap. eauto.
  - intros invariant arguments ->. unfold mentioned_invariants.
    apply elem_of_list_omap. eexists. split; [exact Hall|reflexivity].
Qed.


(** ** The iterates stay within the universe *)

Definition within_universe (needs : requirements) : Prop :=
  forall item, required_by needs item ⊆ universe item.

Lemma literal_atoms_literal atom :
  atom ∈ literal_atoms -> literal_atom atom.
Proof. unfold literal_atoms. rewrite elem_of_list_filter. tauto. Qed.

Lemma declaration_atoms_cases item atom :
  atom ∈ declaration_atoms item ->
  (exists index, atom = TemplateFormal index /\
    index < declaration_arity item) \/
  (atom ∈ literal_atoms /\ literal_atom atom).
Proof.
  unfold declaration_atoms. rewrite elem_of_app, elem_of_list_fmap.
  intros [(index & -> & Hindex)|Hliteral].
  - left. exists index. split; [reflexivity|]. apply elem_of_seq in Hindex. lia.
  - right. split; [exact Hliteral|]. apply literal_atoms_literal. exact Hliteral.
Qed.

Lemma substitute_entry_universe item item' arguments entry :
  (forall atom, Some atom ∈ arguments -> atom ∈ declaration_atoms item) ->
  length arguments = declaration_arity item' ->
  entry ∈ universe item' ->
  substitute_entry arguments entry ∈ universe item.
Proof.
  intros Hatoms Hlength Hentry. destruct entry as [invariant key].
  apply universe_spec in Hentry as [Hinvariant Hkey].
  apply universe_spec. split; [exact Hinvariant|].
  destruct Hkey as [->|(word & -> & Hword_length & Hword)];
    [left; reflexivity|].
  cbn [substitute_entry fst snd mbind option_bind].
  destruct (all_atoms (map (substitute_atom arguments) word)) as [word'|]
    eqn:Hsubstituted; [|left; reflexivity].
  right. exists word'. split; [reflexivity|].
  apply all_atoms_spec in Hsubstituted.
  split.
  - apply (f_equal length) in Hsubstituted. rewrite !map_length in Hsubstituted.
    lia.
  - apply Forall_forall. intros atom Hatom.
    assert (Hsome : Some atom ∈ map (substitute_atom arguments) word).
    { rewrite Hsubstituted. apply elem_of_list_fmap. exists atom.
      split; [reflexivity|exact Hatom]. }
    apply elem_of_list_fmap in Hsome as (source & Hsource & Hin).
    rewrite Forall_forall in Hword.
    destruct (declaration_atoms_cases item' source
      (Hword source Hin))
      as [(index & -> & Hindex)|[Hliteral Hliteral_atom]].
    + cbn in Hsource. destruct (arguments !! index) as [[argument|]|]
        eqn:Hlookup; cbn in Hsource; try discriminate.
      injection Hsource as <-. apply Hatoms.
      apply elem_of_list_lookup_2 in Hlookup. exact Hlookup.
    + destruct source; cbn in Hliteral_atom, Hsource; try contradiction;
        injection Hsource as Heq; subst atom;
        unfold declaration_atoms; apply elem_of_app; right; exact Hliteral.
Qed.

Lemma application_mask_universe needs item app :
  within_universe needs -> item ∈ declaration_list ->
  app ∈ body_applications item ->
  application_mask needs app ⊆ universe item.
Proof.
  intros Hwithin Hitem Happ.
  destruct (body_application_facts _ _ Hitem Happ)
    as (Harity & Hatoms & Hinvariants).
  destruct app as [invariant arguments|predicate arguments]; cbn in *.
  - apply union_least.
    + intros entry Hentry. apply elem_of_singleton in Hentry as ->.
      apply universe_spec. split; [eapply Hinvariants; reflexivity|].
      destruct (all_atoms arguments) as [word|] eqn:Hwords;
        [|left; reflexivity].
      right. exists word. split; [reflexivity|].
      apply all_atoms_spec in Hwords. subst arguments.
      rewrite map_length in Harity. split; [exact Harity|].
      apply Forall_forall. intros atom Hatom. apply Hatoms.
      apply elem_of_list_fmap. exists atom.
      split; [reflexivity|exact Hatom].
    + intros entry Hentry. apply elem_of_map in Hentry as (source & -> & Hsource).
      apply (substitute_entry_universe item (DeclInvariant invariant));
        [exact Hatoms|exact Harity|apply Hwithin; exact Hsource].
  - intros entry Hentry. apply elem_of_map in Hentry as (source & -> & Hsource).
    apply (substitute_entry_universe item (DeclPredicate predicate));
      [exact Hatoms|exact Harity|apply Hwithin; exact Hsource].
Qed.

Lemma requirements_step_universe needs :
  within_universe needs -> within_universe (requirements_step needs).
Proof.
  intros Hwithin item. rewrite required_by_step.
  destruct (decide (item ∈ declaration_list)) as [Hitem|];
    [|apply empty_subseteq].
  unfold applications_mask. intros entry Hentry.
  apply elem_of_union_list in Hentry as (mask & Hmask & Hentry).
  apply elem_of_list_fmap in Hmask as (app & -> & Happ).
  exact (application_mask_universe _ _ _ Hwithin Hitem Happ _ Hentry).
Qed.

Lemma requirements_approx_universe rounds :
  within_universe (requirements_approx rounds).
Proof.
  induction rounds as [|rounds IH].
  - intros item. change (requirements_approx 0) with (∅ : requirements).
    unfold required_by at 1. rewrite lookup_empty. apply empty_subseteq.
  - rewrite requirements_approx_succ. apply requirements_step_universe.
    exact IH.
Qed.

(** ** Stabilization *)

Definition requirements_total (needs : requirements) : nat :=
  sum_list_with (fun item => size (required_by needs item))
    (remove_dups declaration_list).

Lemma sum_list_with_le_pointwise (f g : declaration -> nat) items :
  (forall item, item ∈ items -> f item <= g item) ->
  sum_list_with f items <= sum_list_with g items.
Proof.
  induction items as [|item items IH]; cbn; [lia|]. intros Hle.
  pose proof (Hle item (elem_of_list_here _ _)).
  pose proof (IH (fun other Hother => Hle other (elem_of_list_further _ _ _ Hother))).
  lia.
Qed.

Lemma requirements_total_mono left right :
  requirements_le left right ->
  requirements_total left <= requirements_total right.
Proof.
  intros Hle. apply sum_list_with_le_pointwise. intros item _.
  apply subseteq_size. apply Hle.
Qed.

Lemma requirements_total_equal left right :
  requirements_le left right ->
  requirements_total left = requirements_total right ->
  forall item, item ∈ declaration_list ->
    required_by left item = required_by right item.
Proof.
  intros Hle Htotal item Hitem.
  apply elem_of_remove_dups in Hitem.
  unfold requirements_total in Htotal.
  revert Htotal Hitem. generalize (remove_dups declaration_list) as items.
  induction items as [|other items IH]; cbn; intros Htotal Hitem.
  - apply elem_of_nil in Hitem. contradiction.
  - pose proof (subseteq_size _ _ (Hle other)) as Hother.
    pose proof (sum_list_with_le_pointwise
      (fun item => size (required_by left item))
      (fun item => size (required_by right item)) items
      (fun item _ => subseteq_size _ _ (Hle item))) as Hrest.
    apply elem_of_cons in Hitem as [->|Hitem].
    + apply set_subseteq_size_eq; [apply Hle|lia].
    + apply IH; [lia|exact Hitem].
Qed.

(** Two rounds' results agree when they agree on the declarations. *)
Lemma requirements_step_ext left right :
  (forall item, item ∈ declaration_list ->
    required_by (requirements_step left) item =
      required_by (requirements_step right) item) ->
  requirements_step left = requirements_step right.
Proof.
  intros Hagree. apply map_eq. intros item.
  unfold requirements_step. rewrite !lookup_list_to_map_graph.
  destruct (decide (item ∈ declaration_list)) as [Hitem|]; [|reflexivity].
  f_equal. specialize (Hagree item Hitem).
  rewrite !required_by_step, !decide_True in Hagree by exact Hitem.
  exact Hagree.
Qed.

Lemma size_list_to_set_le (entries : list template_entry) :
  size (list_to_set (C:=template_mask) entries) <= length entries.
Proof.
  induction entries as [|entry entries IH]; cbn.
  - rewrite size_empty. lia.
  - rewrite size_union_alt, size_singleton.
    pose proof (subseteq_size (list_to_set (C:=template_mask) entries ∖
      {[entry]}) (list_to_set entries) ltac:(set_solver)).
    lia.
Qed.

Lemma words_length atoms length' :
  length (words atoms length') = length atoms ^ length'.
Proof.
  induction length' as [|length' IH]; cbn; [reflexivity|].
  rewrite <- IH. clear IH. generalize (words atoms length') as rest.
  induction atoms as [|atom atoms IHatoms]; intros rest; cbn; [reflexivity|].
  rewrite app_length, map_length, IHatoms. reflexivity.
Qed.

Lemma length_flat_map {A B} (f : A -> list B) (items : list A) :
  length (flat_map f items) = sum_list_with (fun item => length (f item)) items.
Proof.
  induction items as [|item items IH]; cbn; [reflexivity|].
  rewrite app_length, IH. reflexivity.
Qed.

Lemma universe_size item : size (universe item) <= universe_size_bound item.
Proof.
  unfold universe, universe_size_bound.
  etrans; [apply size_list_to_set_le|].
  rewrite app_length, map_length, length_flat_map.
  apply Nat.add_le_mono_l.
  induction mentioned_invariants as [|invariant rest IH]; cbn; [lia|].
  rewrite map_length, words_length. lia.
Qed.

Lemma requirements_total_bound needs :
  within_universe needs ->
  requirements_total needs <=
    sum_list_with universe_size_bound (remove_dups declaration_list).
Proof.
  intros Hwithin. apply sum_list_with_le_pointwise. intros item _.
  etrans; [apply subseteq_size, Hwithin|apply universe_size].
Qed.

(** Until the iterates are stable, each round adds an entry. *)
Lemma requirements_approx_progress rounds :
  (exists rounds', rounds' <= rounds /\
    requirements_step (requirements_approx rounds') =
      requirements_approx rounds') \/
  rounds <= requirements_total (requirements_approx (S rounds)).
Proof.
  induction rounds as [|rounds IH]; [right; lia|].
  destruct IH as [(rounds' & Hle & Hstable)|Hprogress].
  { left. exists rounds'. split; [lia|exact Hstable]. }
  destruct (decide (requirements_step (requirements_approx (S rounds)) =
    requirements_approx (S rounds))) as [Hstable|Hunstable].
  { left. exists (S rounds). split; [lia|exact Hstable]. }
  right.
  pose proof (requirements_approx_chain (S rounds)) as Hchain.
  pose proof (requirements_total_mono _ _ Hchain) as Htotal.
  destruct (decide (requirements_total (requirements_approx (S rounds)) =
    requirements_total (requirements_approx (S (S rounds))))) as [Hequal|];
    [|lia].
  exfalso. apply Hunstable.
  rewrite <- requirements_approx_succ. symmetry.
  rewrite !requirements_approx_succ. apply requirements_step_ext.
  intros item Hitem.
  rewrite <- !requirements_approx_succ.
  exact (requirements_total_equal _ _ Hchain Hequal item Hitem).
Qed.

(** The iterates are stable after [requirements_bound] rounds. *)
Theorem requirements_approx_bound_stable :
  requirements_step (requirements_approx requirements_bound) =
    requirements_approx requirements_bound.
Proof.
  destruct (requirements_approx_progress requirements_bound)
    as [(rounds & Hle & Hstable)|Hprogress].
  - rewrite (requirements_approx_stable rounds Hstable _ Hle). exact Hstable.
  - exfalso.
    pose proof (requirements_total_bound _
      (requirements_approx_universe (S requirements_bound))) as Hbound.
    unfold requirements_bound in Hprogress at 1. lia.
Qed.

(** ** The iteration

    The requirements are computed by applying rounds until one changes
    nothing.  A round from an unstable iterate is well-founded, since the
    iterates are stable after [requirements_bound] rounds; the bound occurs
    only in that proof, and the guarded accessibility proof unfolds lazily,
    so evaluation never computes it. *)

(** A round from the [rounds]-th iterate that changes it. *)
Definition unstable_round (next rounds : nat) : Prop :=
  next = S rounds /\
  requirements_step (requirements_approx rounds) <> requirements_approx rounds.

Lemma unstable_round_before_bound next rounds :
  unstable_round next rounds -> rounds < requirements_bound.
Proof.
  intros [_ Hunstable].
  destruct (decide (rounds < requirements_bound)) as [|Hge]; [assumption|].
  exfalso. apply Hunstable.
  rewrite (requirements_approx_stable requirements_bound
    requirements_approx_bound_stable rounds ltac:(lia)).
  exact requirements_approx_bound_stable.
Qed.

Lemma unstable_round_wf : well_founded unstable_round.
Proof.
  apply (wf_incl _ _ (ltof nat (fun rounds => requirements_bound - rounds))).
  - intros next rounds Hround. unfold ltof.
    pose proof (unstable_round_before_bound _ _ Hround).
    destruct Hround as [-> _]. lia.
  - apply well_founded_ltof.
Qed.

Lemma unstable_round_intro rounds (needs : requirements) :
  needs = requirements_approx rounds ->
  requirements_step needs <> needs ->
  unstable_round (S rounds) rounds.
Proof. intros ->. split; [reflexivity|assumption]. Qed.

Fixpoint requirements_iterate (rounds : nat) (needs : requirements)
    (Hneeds : needs = requirements_approx rounds)
    (Hacc : Acc unstable_round rounds) {struct Hacc} : requirements :=
  match decide (requirements_step needs = needs) with
  | left _ => needs
  | right Hunstable =>
      requirements_iterate (S rounds) (requirements_step needs)
        (f_equal requirements_step Hneeds)
        (Acc_inv Hacc (unstable_round_intro rounds needs Hneeds Hunstable))
  end.

(** The requirements of the declared predicates and invariants. *)
Definition declaration_requirements : requirements :=
  requirements_iterate 0 ∅ eq_refl
    (Acc_intro_generator 32 unstable_round_wf 0).

Lemma requirements_iterate_stable rounds needs Hneeds Hacc :
  exists rounds',
    requirements_iterate rounds needs Hneeds Hacc =
      requirements_approx rounds' /\
    requirements_step (requirements_approx rounds') =
      requirements_approx rounds'.
Proof.
  remember (requirements_bound - rounds) as measure eqn:Hmeasure.
  revert rounds needs Hneeds Hacc Hmeasure.
  induction measure as [measure IH] using lt_wf_ind.
  intros rounds needs Hneeds [Hstep] Hmeasure. cbn [requirements_iterate].
  destruct (decide (requirements_step needs = needs)) as [Hstable|Hunstable].
  - exists rounds. subst needs. split; [reflexivity|exact Hstable].
  - pose proof (unstable_round_before_bound _ _
      (unstable_round_intro rounds needs Hneeds Hunstable)) as Hbefore.
    eapply (IH (requirements_bound - S rounds)); [lia|reflexivity].
Qed.

Lemma declaration_requirements_approx :
  exists rounds, declaration_requirements = requirements_approx rounds /\
    requirements_step (requirements_approx rounds) = requirements_approx rounds.
Proof. apply requirements_iterate_stable. Qed.

(** The requirements are closed under the bodies' dependencies ... *)
Theorem declaration_requirements_closed :
  requirements_step declaration_requirements = declaration_requirements.
Proof.
  destruct declaration_requirements_approx as (rounds & -> & Hstable).
  exact Hstable.
Qed.

(** ... and are the least closed requirements. *)
Theorem declaration_requirements_least needs :
  requirements_le (requirements_step needs) needs ->
  requirements_le declaration_requirements needs.
Proof.
  intros Hclosed.
  destruct declaration_requirements_approx as (rounds & -> & _).
  apply requirements_approx_least. exact Hclosed.
Qed.

End WithDeclarations.

(** ** Procedure masks *)

(** A procedure requires what the applications of its precondition
    require. *)
Definition procedure_requirements (D : declarations) {F Δ}
    (pre : core_assertion F Δ) : template_mask :=
  applications_mask (declaration_requirements D) (applications None pre).

Definition grant_entry (app : application) : option template_entry :=
  match app with
  | AppInvariant invariant arguments =>
      (fun key => (invariant, Some key)) <$> all_atoms arguments
  | AppPredicate _ _ => None
  end.

(** A procedure grants the instances its postcondition names with arguments
    over its formals, its return value (the outermost bound variable) and
    literals. *)
Definition procedure_grants {F Δ} (post : core_assertion F Δ) :
    template_mask :=
  list_to_set (omap grant_entry (applications (Some 0) post)).

End WithSignature.
End Masks.
