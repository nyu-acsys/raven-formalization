From Coq Require Import List String ZArith Program.Equality Lia
  Logic.ProofIrrelevance ClassicalEpsilon.
From stdpp Require Import countable gmap namespaces sets strings pretty.

From iris.algebra Require Import auth gset.
From iris.base_logic Require Import fancy_updates.
From iris.base_logic.lib Require Import own invariants ghost_map.

From raven Require Import runtime.lang runtime.invariant_tokens.
From raven Require Import verification.expressions verification.assertions verification.ir soundness.interpretation.

Import ListNotations.
Import weakestpre.
Open Scope list_scope.

Module RuntimeModel := InvTokens.
Module RuntimeLang := raven.runtime.lang.

(** Runtime erasure maps typed statements, expressions, and field
    initializers to their runtime forms. This module also defines the
    runtime resource-algebra values and the runtime names of module
    declarations. *)
Module RuntimeErasure.

Import Core IR Translation.

Module RAValues.
Section WithRAs.
Context {RAs : RAConfig}.
  Definition ra_carrier name :=
    ra_base.RA_carrier (RuntimeLang.ra_map name).

  Definition ra_eqb name
      (left right : ra_carrier name) : bool := bool_decide (left = right).

  Lemma ra_eqb_eq name (left right : ra_carrier name) :
    ra_eqb name left right = true <-> left = right.
  Proof. apply bool_decide_eq_true. Qed.

  Definition ra_id name : ra_carrier name :=
    @ra_base.ra_id (ra_base.RA_carrier (RuntimeLang.ra_map name))
      (ra_base.ra_inst_instance (RuntimeLang.ra_map name)).

  Definition ra_of_int name (value : Z) : ra_carrier name :=
    @ra_base.ra_of_int (ra_base.RA_carrier (RuntimeLang.ra_map name))
      (ra_base.ra_inst_instance (RuntimeLang.ra_map name)) value.

  Definition ra_valid name (value : ra_carrier name) : Prop :=
    @ra_base.valid _ (ra_base.ra_inst_instance (RuntimeLang.ra_map name)) value.

  Definition ra_fpu_allowed name (old_value new_value : ra_carrier name) : Prop :=
    @ra_base.fpuValid _ (ra_base.ra_inst_instance (RuntimeLang.ra_map name))
      old_value new_value.

  Definition ra_values : Core.RAValueConfig :=
    Core.RAValueConfigData ra_carrier ra_eqb ra_eqb_eq ra_id ra_of_int
      ra_valid ra_fpu_allowed.
End WithRAs.
End RAValues.
#[global] Existing Instance RAValues.ra_values.

(** Runtime names and namespaces of module declarations. The proofs
    rely only on the injectivity and disjointness facts below, so the names
    are fixed here rather than chosen separately by each module. *)
Definition field_name (field : field_id) : RuntimeLang.fld_name := pretty field.
Definition invariant_name (invariant : inv_id) : RuntimeModel.inv_name :=
  pretty invariant.
Definition procedure_name (procedure : proc_id) : RuntimeLang.proc_name :=
  pretty procedure.
Definition invariant_namespace (invariant : inv_id) : namespace :=
  nroot .@ "invariant" .@ invariant.
Definition ghost_heap_namespace : namespace := nroot .@ "ghost_heap".

#[global] Instance field_name_injective : Inj (=) (=) field_name := _.
#[global] Instance invariant_name_injective : Inj (=) (=) invariant_name := _.
#[global] Instance procedure_name_injective : Inj (=) (=) procedure_name := _.

Lemma invariant_namespaces_disjoint left right :
  left ≠ right ->
  (↑(invariant_namespace left) : coPset) ## ↑(invariant_namespace right).
Proof. apply ndot_ne_disjoint. Qed.

Lemma invariant_ghost_namespace_disjoint invariant :
  (↑(invariant_namespace invariant) : coPset) ## ↑ghost_heap_namespace.
Proof. apply ndot_preserve_disjoint_l, ndot_ne_disjoint. done. Qed.

(** Runtime representation of Raven's trusted atomic-block primitive.

    Atomic blocks are declarations about the modeled hardware substrate, not
    obligations attached to individual modules. The framework therefore
    supplies their opaque transition uniformly.  Its semantic content is the
    global [term_trusted_atomic_runtime_refinement] assumption at the
    certified Iris boundary; examples neither define this relation nor prove
    a separate progress condition for it. *)
Axiom trusted_atomic_transition : forall {RAs : RAConfig}
    {Logic : Assertion.LogicSignature} {Γ},
  stmt Γ -> RuntimeLang.trusted_atomic_transition.


Section WithSignature.
Context {RAs : RAConfig} {Logic : Assertion.LogicSignature}.
(** The fixed Iris mask envelope in which a certified region executes. *)
Definition ambient_mask : Type := coPset.

Definition tval_to_val {t} (value : tval t) : RuntimeLang.val :=
  match value with
  | VBool boolean => RuntimeLang.LitBool boolean
  | VInt integer => RuntimeLang.LitInt integer
  | VRef location => RuntimeLang.LitLoc (RuntimeLang.Loc location)
  | VUnit => RuntimeLang.LitUnit
  | VRA resource => RuntimeLang.LitRAElem
      (@existT string
        (fun name => ra_base.RA_carrier (RuntimeLang.ra_map name))
        _ resource)
  end.

Definition runtime_type (t : Core.typ) : RuntimeLang.typ :=
  match t with
  | TBool => RuntimeLang.TpBool
  | TInt => RuntimeLang.TpInt
  | TRef => RuntimeLang.TpLoc
  | TUnit => RuntimeLang.TpUnit
  | TRA resource => RuntimeLang.TpRA resource
  end.

(** Every dynamically typed runtime value has a typed representative.  This
    is the bridge used when a freshly-created procedure frame determines the
    interpretation of that invocation's canonical entry valuation. *)
Lemma val_has_typ_tval {t} (value : RuntimeLang.val) :
  RuntimeLang.val_has_typ value (runtime_type t) ->
  exists typed_value : tval t, tval_to_val typed_value = value.
Proof.
  destruct t; destruct value; simpl; intros Htype;
    try contradiction; try (destruct p; contradiction).
  - eexists (VBool _). reflexivity.
  - eexists (VInt _). reflexivity.
  - destruct l. eexists (VRef _). reflexivity.
  - eexists VUnit. reflexivity.
  - destruct p as [resource value]. simpl in Htype.
    subst resource.
    exists (@VRA RAValues.ra_values resource_algebra value). reflexivity.
Qed.

Fixpoint runtime_variables {Γ} (names : named_context Γ) :
    list RuntimeLang.var :=
  match names with
  | NCNil => []
  | NCCons source_name _ tail => source_name :: runtime_variables tail
  end.

Definition runtime_variable {Γ keep t} (names : named_context Γ)
    (variable : lvar keep Γ t) : RuntimeLang.var :=
  default "" (runtime_variables names !! lvar_index variable).

(** The names that occupy a runtime frame: ghost locals have no slot. *)
Fixpoint runtime_frame_names {Γ} (names : named_context Γ) :
    list RuntimeLang.var :=
  match names with
  | NCNil => []
  | NCCons source_name d tail =>
      if keep_runtime d then source_name :: runtime_frame_names tail
      else runtime_frame_names tail
  end.

Lemma runtime_frame_names_all {Γ} (names : named_context Γ) :
  forallb keep_runtime Γ = true ->
  runtime_frame_names names = runtime_variables names.
Proof.
  induction names as [|Γ name d names IH]; simpl; first reflexivity.
  rewrite andb_true_iff. intros [-> Htail]. f_equal. exact (IH Htail).
Qed.

Lemma runtime_variable_forget {Γ keep t} (names : named_context Γ)
    (variable : lvar keep Γ t) :
  runtime_variable names (lvar_forget variable) =
    runtime_variable names variable.
Proof. unfold runtime_variable. rewrite lvar_forget_index. reflexivity. Qed.

(** Runtime procedure frames reserve a fixed return name, but the slot is
    still the procedure's distinguished typed variable.  Rename that one
    decoration in the naming context so body translation and frame ownership
    use exactly the same key as the runtime call machinery. *)
Fixpoint rename_named_context_at {Γ} (names : named_context Γ)
    (replacement : string) (index : nat) : named_context Γ :=
  match names with
  | NCNil => NCNil
  | NCCons name u tail =>
      match index with
      | 0 => NCCons replacement u tail
      | S tail_index =>
          NCCons name u (rename_named_context_at tail replacement tail_index)
      end
  end.

Definition runtime_procedure_names {Γ F}
    (procedure : typed_procedure Γ F) : named_context Γ :=
  rename_named_context_at (procedure_variables _ _ procedure) "#ret_val"
    (lvar_index (procedure_return_variable _ _ procedure)).

Lemma runtime_variables_rename_named_context_at_member {Γ}
    (names : named_context Γ) replacement index name :
  In name (runtime_variables
    (rename_named_context_at names replacement index)) ->
  name = replacement \/ In name (runtime_variables names).
Proof.
  revert index. induction names; intros [|index]; simpl.
  - tauto.
  - tauto.
  - intros [-> | Hin]; [left; reflexivity | right; now right].
  - intros [-> | Hin].
    + right. now left.
    + destruct (IHnames index Hin); [now left | right; now right].
Qed.

Lemma runtime_variables_rename_named_context_at_lookup {Γ}
    (names : named_context Γ) replacement index :
  index < length (runtime_variables names) ->
  runtime_variables (rename_named_context_at names replacement index) !! index =
    Some replacement.
Proof.
  revert index. induction names; intros [|index] Hindex; simpl in *.
  - lia.
  - lia.
  - reflexivity.
  - apply IHnames. lia.
Qed.

Lemma runtime_variables_rename_named_context_at_lookup_other {Γ}
    (names : named_context Γ) replacement index query :
  not (query = index) ->
  runtime_variables (rename_named_context_at names replacement index) !! query =
    runtime_variables names !! query.
Proof.
  revert index query. induction names; intros [|index] [|query] Hother;
    simpl in *; try contradiction; try reflexivity.
  apply IHnames. lia.
Qed.

Lemma runtime_variable_rename_named_context_at_other {Γ keep t}
    (names : named_context Γ) replacement index (variable : lvar keep Γ t) :
  not (lvar_index variable = index) ->
  runtime_variable (rename_named_context_at names replacement index) variable =
    runtime_variable names variable.
Proof.
  revert names index. induction variable; intros names index Hother;
    dependent destruction names; destruct index;
    cbn [lvar_index rename_named_context_at runtime_variable] in *;
    try contradiction; try reflexivity.
  apply IHvariable. lia.
Qed.

Lemma runtime_variables_rename_named_context_at_nodup {Γ}
    (names : named_context Γ) replacement index :
  NoDup (runtime_variables names) ->
  ~ In replacement (runtime_variables names) ->
  NoDup (runtime_variables
    (rename_named_context_at names replacement index)).
Proof.
  revert index. induction names; intros [|index] Hnames Hfresh; simpl in *.
  - constructor.
  - constructor.
  - inversion Hnames as [|? ? Hhead Htail]. constructor.
    + intros Hin. apply elem_of_list_In in Hin.
      apply Hfresh. right; exact Hin.
    + exact Htail.
  - inversion Hnames as [|? ? Hhead Htail]. constructor.
    + intros Hin.
      apply elem_of_list_In in Hin.
      destruct (runtime_variables_rename_named_context_at_member
        names replacement index name Hin) as [Heq | Hin'].
      * apply Hfresh. left. exact Heq.
      * apply Hhead. apply elem_of_list_In. exact Hin'.
    + apply IHnames; [exact Htail|].
      intros Hin. apply Hfresh. right.
      exact Hin.
Qed.

Lemma runtime_procedure_names_nodup {Γ F}
    (procedure : typed_procedure Γ F) :
  procedure_wf procedure ->
  NoDup (runtime_variables (runtime_procedure_names procedure)).
Proof.
  intros Hwf. apply runtime_variables_rename_named_context_at_nodup.
  - change (NoDup
      (named_context_names (procedure_variables _ _ procedure))).
    apply NoDup_ListNoDup. exact (procedure_variable_names_unique _ Hwf).
  - exact (procedure_reserved_return_fresh _ Hwf).
Qed.

Lemma runtime_procedure_frame_names {Γ F}
    (procedure : typed_procedure Γ F) :
  procedure_wf procedure ->
  runtime_frame_names (runtime_procedure_names procedure) =
    runtime_variables (runtime_procedure_names procedure).
Proof.
  intros Hwf. apply runtime_frame_names_all.
  exact (procedure_locals_runtime _ Hwf).
Qed.

Lemma runtime_procedure_frame_names_nodup {Γ F}
    (procedure : typed_procedure Γ F) :
  procedure_wf procedure ->
  NoDup (runtime_frame_names (runtime_procedure_names procedure)).
Proof.
  intros Hwf. rewrite runtime_procedure_frame_names; [|exact Hwf].
  apply runtime_procedure_names_nodup. exact Hwf.
Qed.

(** The runtime procedure record uses untyped declaration lists.  These
    projections are nevertheless generated from the intrinsic frame layout,
    so an argument declaration always names a body slot of the same type. *)
Fixpoint runtime_formal_declarations {Γ F} (names : named_context Γ)
    (variables : pvar_list Γ F) : list (RuntimeLang.var * RuntimeLang.typ) :=
  match variables with
  | PVNil => []
  | @PVCons _ tail t variable variables' =>
      (runtime_variable names variable, runtime_type t) ::
        runtime_formal_declarations names variables'
  end.

Lemma runtime_formal_declarations_rename_other {Γ F}
    (names : named_context Γ) (variables : pvar_list Γ F)
    replacement index :
  ~ In index (pvar_list_indices variables) ->
  runtime_formal_declarations
      (rename_named_context_at names replacement index) variables =
    runtime_formal_declarations names variables.
Proof.
  intros Hnot. induction variables; simpl in *; first reflexivity.
  f_equal.
  - rewrite runtime_variable_rename_named_context_at_other.
    + reflexivity.
    + intros Heq. apply Hnot. left. exact Heq.
  - apply IHvariables. intros Hin. apply Hnot. now right.
Qed.

Fixpoint runtime_local_declarations_from {Γ} (names : named_context Γ)
    (formal_indices : list nat) (return_index index : nat) :
    list (RuntimeLang.var * RuntimeLang.typ) :=
  match names with
  | NCNil => []
  | NCCons name d tail =>
      let tail_declarations := runtime_local_declarations_from tail
        formal_indices return_index (S index) in
      if existsb (Nat.eqb index) formal_indices then tail_declarations
      else
        let runtime_name :=
          if Nat.eqb index return_index then "#ret_val" else name in
        (runtime_name, runtime_type (decl_type d)) :: tail_declarations
  end.

Definition procedure_return_index {Γ F} (procedure : typed_procedure Γ F) :
    nat :=
  lvar_index (procedure_return_variable _ _ procedure).

Definition runtime_procedure_arguments {Γ F}
    (procedure : typed_procedure Γ F) :
    list (RuntimeLang.var * RuntimeLang.typ) :=
  runtime_formal_declarations (procedure_variables _ _ procedure)
    (procedure_formal_variables _ _ procedure).

Definition runtime_procedure_locals {Γ F}
    (procedure : typed_procedure Γ F) :
    list (RuntimeLang.var * RuntimeLang.typ) :=
  runtime_local_declarations_from
    (procedure_variables _ _ procedure)
    (pvar_list_indices (procedure_formal_variables _ _ procedure))
    (procedure_return_index procedure) 0.

Definition runtime_local_name {Γ keep t} (names : named_context Γ)
    (return_index index : nat) (variable : lvar keep Γ t) : RuntimeLang.var :=
  if Nat.eqb (index + lvar_index variable) return_index then "#ret_val"
  else runtime_variable names variable.

Lemma runtime_local_declarations_from_variable {Γ keep}
    (names : named_context Γ) (formal_indices : list nat)
    (return_index index : nat) t (variable : lvar keep Γ t) :
  ~ In (index + lvar_index variable) formal_indices ->
  In (runtime_local_name names return_index index variable, runtime_type t)
    (runtime_local_declarations_from names formal_indices return_index index).
Proof.
  revert index names. induction variable as [d D Hkeep | d D t variable IH];
    intros index names Hnot; dependent destruction names;
    cbn [runtime_local_name lvar_index] in *.
  - replace (index + 0) with index in Hnot by lia.
    destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
    + exfalso. apply Hnot. apply existsb_exists in Hformal.
      destruct Hformal as (candidate & Hin & Heq).
      apply Nat.eqb_eq in Heq. subst candidate.
      exact Hin.
    + cbn [runtime_local_declarations_from]. rewrite Hformal.
      unfold runtime_local_name.
      cbn [lvar_index runtime_variable].
      replace (index + 0) with index by lia.
      assert (Hhead : runtime_variable (NCCons name d names)
          (LHere (keep := keep) Hkeep) = name) by reflexivity.
      rewrite Hhead.
      destruct (Nat.eqb index return_index); apply in_eq.
  - destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
    + cbn [runtime_local_declarations_from]. rewrite Hformal.
      assert (Hname : runtime_local_name (NCCons name d names) return_index
          index (LThere variable) =
          runtime_local_name names return_index (S index) variable).
      { unfold runtime_local_name. cbn [lvar_index runtime_variable].
        replace (index + S (lvar_index variable)) with
          (S index + lvar_index variable) by lia. reflexivity. }
      rewrite Hname.
      apply IH.
      replace (index + S (lvar_index variable)) with
        (S index + lvar_index variable) in Hnot by lia. exact Hnot.
    + cbn [runtime_local_declarations_from]. rewrite Hformal.
      assert (Hname : runtime_local_name (NCCons name d names) return_index
          index (LThere variable) =
          runtime_local_name names return_index (S index) variable).
      { unfold runtime_local_name. cbn [lvar_index runtime_variable].
        replace (index + S (lvar_index variable)) with
          (S index + lvar_index variable) by lia. reflexivity. }
      rewrite Hname.
      apply in_cons. apply IH.
      replace (index + S (lvar_index variable)) with
        (S index + lvar_index variable) in Hnot by lia. exact Hnot.
Qed.

Lemma runtime_local_name_at_result {Γ keep keep' t u}
    (names : named_context Γ)
    (result : lvar keep' Γ u) (variable : lvar keep Γ t) :
  runtime_local_name names (lvar_index result) 0 variable =
  runtime_variable
    (rename_named_context_at names "#ret_val" (lvar_index result)) variable.
Proof.
  revert t variable u result.
  induction names as [| D name d names IH];
    intros value_type variable result_type result;
    dependent destruction variable; dependent destruction result;
    unfold runtime_local_name; cbn [lvar_index rename_named_context_at];
    try reflexivity.
  specialize (IH _ variable _ result). unfold runtime_local_name in IH.
  cbn [runtime_variable lvar_index Nat.eqb Nat.add] in *.
  exact IH.
Qed.

Lemma runtime_local_name_procedure {Γ F keep}
    (procedure : typed_procedure Γ F) t (variable : lvar keep Γ t) :
  runtime_local_name (procedure_variables _ _ procedure)
      (procedure_return_index procedure) 0 variable =
  runtime_variable (runtime_procedure_names procedure) variable.
Proof. apply runtime_local_name_at_result. Qed.

Lemma runtime_procedure_local_declaration {Γ F keep}
    (procedure : typed_procedure Γ F) t (variable : lvar keep Γ t) :
  ~ In (lvar_index variable)
      (pvar_list_indices (procedure_formal_variables _ _ procedure)) ->
  In (runtime_variable (runtime_procedure_names procedure) variable,
      runtime_type t) (runtime_procedure_locals procedure).
Proof.
  intros Hnot. unfold runtime_procedure_locals.
  rewrite <- runtime_local_name_procedure.
  apply runtime_local_declarations_from_variable.
  simpl. exact Hnot.
Qed.

Definition entry_symbol_realizes {Γ} (identity : proc_id)
    (names : named_context Γ) (formal_indices : list nat)
    (frame : RuntimeLang.stack_frame) {t} (symbolic : symbol t)
    (value : tval t) : Prop :=
  forall variable : pvar Γ t,
    symbolic = ProcedureEntrySymbol identity (lvar_index variable) ->
    ~ In (lvar_index variable) formal_indices ->
    frame.(RuntimeLang.locals) !! runtime_variable names variable =
      Some (tval_to_val value).

(** The variable of a given type at a given slot, if there is one. *)
Fixpoint pvar_at (D : decl_context) (t : typ) (slot : nat) :
    option (pvar D t) :=
  match D return option (pvar D t) with
  | [] => None
  | d :: D' =>
      match slot with
      | O =>
          match typ_eq_dec (decl_type d) t with
          | left equal =>
              Some (eq_rect (decl_type d) (fun v => pvar (d :: D') v)
                (LHere eq_refl) t equal)
          | right _ => None
          end
      | S slot' =>
          match pvar_at D' t slot' with
          | Some variable => Some (LThere variable)
          | None => None
          end
      end
  end.

Lemma pvar_at_sound D t slot (variable : pvar D t) :
  pvar_at D t slot = Some variable -> lvar_index variable = slot.
Proof.
  revert slot variable. induction D as [| d D IH]; intros slot variable;
    simpl; [discriminate |].
  destruct slot as [| slot].
  - destruct (typ_eq_dec (decl_type d) t) as [<- |]; [| discriminate].
    intros [= <-]. reflexivity.
  - destruct (pvar_at D t slot) as [variable' |] eqn:Hat; [| discriminate].
    intros [= <-]. simpl. f_equal. exact (IH _ _ Hat).
Qed.

Lemma pvar_at_complete D t (variable : pvar D t) :
  pvar_at D t (lvar_index variable) = Some variable.
Proof.
  induction variable as [d D Hkeep | d D t variable IH]; simpl.
  - destruct (typ_eq_dec (decl_type d) (decl_type d)) as [equal |];
      [| contradiction].
    rewrite (Eqdep_dec.UIP_dec typ_eq_dec equal eq_refl). simpl.
    f_equal. f_equal. apply (Eqdep_dec.UIP_dec Bool.bool_dec).
  - rewrite IH. reflexivity.
Qed.

Definition frame_entry_symbol_valuation {Γ} (caller_valuation : symbol_valuation)
    (identity : proc_id) (names : named_context Γ)
    (formal_indices : list nat) (frame : RuntimeLang.stack_frame)
    (Hrealizable : forall t (symbolic : symbol t),
      exists value : tval t,
        entry_symbol_realizes identity names formal_indices frame symbolic value)
    : symbol_valuation :=
  fun t symbolic =>
    match symbolic as selected return tval _ with
    | ConstantSymbol id => caller_valuation _ (ConstantSymbol id)
    | ProcedureEntrySymbol procedure slot =>
        proj1_sig (constructive_indefinite_description _
          (Hrealizable t (ProcedureEntrySymbol procedure slot)))
    end.

Lemma frame_entry_symbol_valuation_stable {Γ} (caller_valuation : symbol_valuation)
    (identity : proc_id) (names : named_context Γ)
    (formal_indices : list nat) (frame : RuntimeLang.stack_frame)
    Hrealizable :
  constant_symbols_agree caller_valuation
    (frame_entry_symbol_valuation caller_valuation identity names formal_indices frame
      Hrealizable).
Proof. intros t symbolic. destruct symbolic; simpl; reflexivity. Qed.

Lemma frame_entry_symbol_valuation_realize {Γ} (caller_valuation : symbol_valuation)
    (identity : proc_id) (names : named_context Γ)
    (formal_indices : list nat) (frame : RuntimeLang.stack_frame)
  Hrealizable t (symbolic : symbol t) :
  entry_symbol_realizes identity names formal_indices frame symbolic
    (frame_entry_symbol_valuation caller_valuation identity names formal_indices frame
      Hrealizable t symbolic).
Proof.
  destruct symbolic as [id | procedure slot].
  - intros variable Hbad _. discriminate Hbad.
  - unfold frame_entry_symbol_valuation. simpl.
    exact (proj2_sig (constructive_indefinite_description _
      (Hrealizable t (ProcedureEntrySymbol procedure slot)))).
Qed.

Lemma frame_entry_symbol_valuation_exist {Γ} (caller_valuation : symbol_valuation)
    (identity : proc_id) (names : named_context Γ)
    (formal_indices : list nat) (frame : RuntimeLang.stack_frame) :
  (forall t (variable : pvar Γ t),
    ~ In (lvar_index variable) formal_indices ->
    exists value : tval t,
      frame.(RuntimeLang.locals) !! runtime_variable names variable =
        Some (tval_to_val value)) ->
  exists callee_valuation : symbol_valuation,
    constant_symbols_agree caller_valuation callee_valuation /\
    forall t (variable : pvar Γ t),
      ~ In (lvar_index variable) formal_indices ->
      frame.(RuntimeLang.locals) !! runtime_variable names variable =
        Some (tval_to_val
          (callee_valuation t
            (ProcedureEntrySymbol identity (lvar_index variable)))).
Proof.
  intros Htyped.
  assert (Hrealizable : forall t (symbolic : symbol t),
      exists value : tval t,
        entry_symbol_realizes identity names formal_indices frame symbolic value).
  { intros t symbolic.
    destruct symbolic as [id | procedure slot].
    { exists (default_tval t). intros variable Hbad _. discriminate Hbad. }
    destruct (decide (procedure = identity)) as [-> | Hother_procedure].
    2: { exists (default_tval t). intros variable Hsymbolic _.
         injection Hsymbolic as Hprocedure _. contradiction. }
    destruct (pvar_at Γ t slot) as [variable |] eqn:Hat.
    2: { exists (default_tval t). intros variable Hsymbolic _.
         injection Hsymbolic as ->.
         rewrite pvar_at_complete in Hat. discriminate Hat. }
    pose proof (pvar_at_sound _ _ _ _ Hat) as Hslot.
    destruct (in_dec Nat.eq_dec slot formal_indices) as [Hformal | Hnot].
    { exists (default_tval t). intros other Hsymbolic Hother_not.
      injection Hsymbolic as ->. contradiction. }
    subst slot.
    destruct (Htyped t variable Hnot) as (value & Hvalue).
    exists value. intros other Hother Hother_not.
    injection Hother as Hindices.
    have -> : other = variable.
    { apply lvar_index_injective. symmetry. exact Hindices. }
    exact Hvalue.
  }
  exists (frame_entry_symbol_valuation caller_valuation identity names formal_indices frame
    Hrealizable). split.
  - apply frame_entry_symbol_valuation_stable.
  - intros t variable Hnot.
    apply (frame_entry_symbol_valuation_realize caller_valuation identity names formal_indices
      frame Hrealizable t
      (ProcedureEntrySymbol identity (lvar_index variable)) variable
      eq_refl Hnot).
Qed.

Lemma procedure_frame_entry_symbol_valuation_exist {Γ F}
    (caller_valuation : symbol_valuation) (procedure : typed_procedure Γ F)
    (frame : RuntimeLang.stack_frame) :
  (forall variable type,
    (variable, type) ∈ runtime_procedure_locals procedure ->
    exists value,
      frame.(RuntimeLang.locals) !! variable = Some value /\
      RuntimeLang.val_has_typ value type) ->
  exists callee_valuation : symbol_valuation,
    constant_symbols_agree caller_valuation callee_valuation /\
    forall t (variable : pvar Γ t),
      ~ In (lvar_index variable)
        (pvar_list_indices (procedure_formal_variables _ _ procedure)) ->
      frame.(RuntimeLang.locals) !!
          runtime_variable (runtime_procedure_names procedure) variable =
        Some (tval_to_val
          (callee_valuation t (ProcedureEntrySymbol F (lvar_index variable)))).
Proof.
  intros Hlocals. apply frame_entry_symbol_valuation_exist.
  intros t variable Hnot.
  pose proof (runtime_procedure_local_declaration procedure t variable Hnot)
    as Hdeclaration.
  destruct (Hlocals
      (runtime_variable (runtime_procedure_names procedure) variable)
      (runtime_type t) (ltac:(apply elem_of_list_In; exact Hdeclaration)))
    as (raw & Hlookup & Htype).
  destruct (val_has_typ_tval raw Htype) as (value & <-).
  exists value. exact Hlookup.
Qed.

Lemma runtime_formal_declarations_length {Γ F} (names : named_context Γ)
    (variables : pvar_list Γ F) :
  length (runtime_formal_declarations names variables) = length F.
Proof. induction variables; simpl; congruence. Qed.

Lemma runtime_formal_declarations_lookup {Γ F}
    (names : named_context Γ) (variables : pvar_list Γ F) t
    (formal_variable : formal F t) :
  In (runtime_variable names (lookup_pvar_list variables formal_variable),
      runtime_type t) (runtime_formal_declarations names variables).
Proof.
  induction variables; dependent destruction formal_variable.
  - rewrite lookup_pvar_list_here. simpl. left. reflexivity.
  - rewrite lookup_pvar_list_there. simpl. right. apply IHvariables.
Qed.

Lemma runtime_procedure_arguments_length {Γ F}
    (procedure : typed_procedure Γ F) :
  length (runtime_procedure_arguments procedure) =
    length (Assertion.procedure_args F).
Proof. apply runtime_formal_declarations_length. Qed.

Lemma runtime_variables_length {Γ} (names : named_context Γ) :
  length (runtime_variables names) = length Γ.
Proof. induction names; simpl; congruence. Qed.

Lemma runtime_procedure_return_name {Γ F}
    (procedure : typed_procedure Γ F) :
  runtime_variable (runtime_procedure_names procedure)
    (procedure_return_variable _ _ procedure) = "#ret_val".
Proof.
  unfold runtime_variable, runtime_procedure_names.
  rewrite runtime_variables_rename_named_context_at_lookup.
  - reflexivity.
  - rewrite runtime_variables_length. apply lvar_index_lt.
Qed.

Lemma runtime_variable_member {Γ keep} (names : named_context Γ) t
    (variable : lvar keep Γ t) :
  runtime_variable names variable ∈ runtime_variables names.
Proof.
  unfold runtime_variable.
  have Hlookup : is_Some (runtime_variables names !! lvar_index variable).
  { apply lookup_lt_is_Some_2. rewrite runtime_variables_length.
    apply lvar_index_lt. }
  destruct (runtime_variables names !! lvar_index variable) as [name|]
    eqn:Hname.
  - simpl. apply elem_of_list_lookup. exists (lvar_index variable). exact Hname.
  - destruct Hlookup as [name Hsome]. congruence.
Qed.

Lemma runtime_variable_frame_member {Γ keep} (names : named_context Γ) t
    (variable : lvar keep Γ t) :
  lvar_runtime variable = true ->
  runtime_variable names variable ∈ runtime_frame_names names.
Proof.
  revert names. induction variable as [d D Hkeep | d D t variable IH];
    intros names Hruntime; dependent destruction names; simpl in *.
  - rewrite Hruntime. apply elem_of_list_here.
  - specialize (IH names Hruntime).
    change (runtime_variable (NCCons name d names) (LThere variable)) with
      (runtime_variable names variable).
    destruct (keep_runtime d); [apply elem_of_list_further|]; exact IH.
Qed.

Lemma runtime_frame_name_has_variable {Γ} (names : named_context Γ) name :
  In name (runtime_frame_names names) ->
  exists t (variable : lvar keep_runtime Γ t),
    runtime_variable names variable = name.
Proof.
  induction names as [|Γ head d names IH]; simpl; first tauto.
  destruct (keep_runtime d) eqn:Hd.
  - intros [<- | Hin].
    + exists (decl_type d), (LHere Hd). reflexivity.
    + destruct (IH Hin) as (u & variable & Hvariable).
      exists u, (LThere variable). exact Hvariable.
  - intros Hin. destruct (IH Hin) as (u & variable & Hvariable).
    exists u, (LThere variable). exact Hvariable.
Qed.

Lemma runtime_variable_member_inv {Γ} (names : named_context Γ) name :
  In name (runtime_variables names) ->
  exists t (variable : pvar Γ t), runtime_variable names variable = name.
Proof.
  induction names; simpl; first tauto.
  intros [<- | Hin].
  - exists (decl_type d), (LHere eq_refl). reflexivity.
  - destruct (IHnames Hin) as (u & variable & Hvariable).
    exists u, (LThere variable). exact Hvariable.
Qed.

Lemma runtime_variables_are_names {Γ} (names : named_context Γ) :
  runtime_variables names = named_context_names names.
Proof. induction names; simpl; [reflexivity | f_equal; assumption]. Qed.

Lemma runtime_variable_lookup {Γ keep t} (names : named_context Γ)
    (variable : lvar keep Γ t) :
  runtime_variables names !! lvar_index variable =
    Some (runtime_variable names variable).
Proof.
  unfold runtime_variable.
  destruct (runtime_variables names !! lvar_index variable) as [name|]
    eqn:Hlookup; [reflexivity |].
  exfalso. apply lookup_ge_None_1 in Hlookup.
  rewrite runtime_variables_length in Hlookup.
  pose proof (lvar_index_lt variable). lia.
Qed.

Lemma runtime_variable_injective {Γ keep keep' t u} (names : named_context Γ)
    (left : lvar keep Γ t) (right : lvar keep' Γ u) :
  List.NoDup (named_context_names names) ->
  runtime_variable names left = runtime_variable names right ->
  lvar_index left = lvar_index right.
Proof.
  intros Hnames Heq.
  rewrite <- runtime_variables_are_names in Hnames.
  eapply NoDup_lookup;
    [apply NoDup_ListNoDup; exact Hnames | apply runtime_variable_lookup |].
  rewrite Heq. apply runtime_variable_lookup.
Qed.

Lemma runtime_formal_name_index {Γ F} (names : named_context Γ)
    (variables : pvar_list Γ F) name :
  List.In name (runtime_formal_declarations names variables).*1 ->
  exists index, List.In index (pvar_list_indices variables) /\
    runtime_variables names !! index = Some name.
Proof.
  induction variables as [| F t variable variables IH]; simpl.
  - intros Hin. inversion Hin.
  - intros [Heq | Hin].
    + subst name. exists (lvar_index variable). split; [left; reflexivity |].
      apply runtime_variable_lookup.
    + destruct (IH Hin) as (index & Hindex & Hlookup).
      exists index. split; [right; exact Hindex | exact Hlookup].
Qed.

Lemma runtime_formal_names_nodup {Γ F} (names : named_context Γ)
    (variables : pvar_list Γ F) :
  List.NoDup (named_context_names names) ->
  List.NoDup (pvar_list_indices variables) ->
  List.NoDup (runtime_formal_declarations names variables).*1.
Proof.
  intros Hnames Hindices. induction variables as [| F t variable variables IH];
    simpl in *; [constructor |].
  inversion Hindices as [| index indices Hfresh Htail]. constructor.
  - intros Hin. destruct (runtime_formal_name_index names variables _ Hin)
      as (other & Hother & Hlookup).
    apply Hfresh. enough (lvar_index variable = other) by congruence.
    rewrite <- runtime_variables_are_names in Hnames.
    eapply NoDup_lookup;
      [apply NoDup_ListNoDup; exact Hnames | apply runtime_variable_lookup |].
    exact Hlookup.
  - apply IH; assumption.
Qed.

Lemma runtime_procedure_argument_names_nodup {Γ F}
    (procedure : typed_procedure Γ F) :
  procedure_wf procedure ->
  List.NoDup (runtime_procedure_arguments procedure).*1.
Proof.
  intros Hwf. apply runtime_formal_names_nodup.
  - exact (procedure_variable_names_unique _ Hwf).
  - exact (procedure_formal_slots_unique _ Hwf).
Qed.

Lemma runtime_local_declarations_from_source_index {Γ}
    (names : named_context Γ) (formal_indices : list nat)
    (return_index index : nat) name :
  In name (runtime_local_declarations_from names formal_indices return_index
    index).*1 ->
  name = "#ret_val" \/
  exists local_index,
    runtime_variables names !! local_index = Some name /\
    ~ In (index + local_index) formal_indices /\
    not ((index + local_index)%nat = return_index).
Proof.
  revert index.
  induction names as [| Γ name0 t names IH]; intros index; simpl.
  - intros Hin. inversion Hin.
  - destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
    + intros Hin. destruct (IH (S index) Hin) as [Hret | Hsource].
      * left; exact Hret.
      * right. destruct Hsource as (local_index & Hlookup & Hnot & Hreturn).
        exists (S local_index). split.
        { rewrite lookup_cons. simpl. exact Hlookup. }
        split; replace (index + S local_index) with (S index + local_index)
          by lia; assumption.
    + intros Hin. destruct (Nat.eqb index return_index) eqn:Hsame.
      * simpl in Hin. destruct Hin as [Hin | Hin].
        -- left. symmetry. exact Hin.
        -- destruct (IH (S index) Hin) as [Hret | Hsource].
           ++ left; exact Hret.
           ++ right. destruct Hsource as
                (local_index & Hlookup & Hnot & Hreturn).
              exists (S local_index). split.
              { rewrite lookup_cons. simpl. exact Hlookup. }
              split; replace (index + S local_index) with
                (S index + local_index) by lia; assumption.
      * simpl in Hin. destruct Hin as [Hin | Hin].
        -- subst name. right. exists 0. split; [simpl; reflexivity|]. split.
           ++ intro Hinformal.
              rewrite Nat.add_0_r in Hinformal.
              have Htrue : existsb (Nat.eqb index) formal_indices = true.
              { apply (proj2 (existsb_exists (Nat.eqb index)
                    formal_indices)).
                exists index. split; [exact Hinformal|apply Nat.eqb_refl]. }
              congruence.
           ++ rewrite Nat.add_0_r. apply Nat.eqb_neq in Hsame. exact Hsame.
        -- destruct (IH (S index) Hin) as [Hret | Hsource].
           ++ left; exact Hret.
           ++ right. destruct Hsource as
                (local_index & Hlookup & Hnot & Hreturn).
              exists (S local_index). split.
              { rewrite lookup_cons. simpl. exact Hlookup. }
              split; replace (index + S local_index) with
                (S index + local_index) by lia; assumption.
Qed.

Lemma runtime_local_declarations_from_no_return_name {Γ}
    (names : named_context Γ) (formal_indices : list nat)
    (return_index index : nat) :
  ~ List.In "#ret_val" (named_context_names names) ->
  return_index < index ->
  ~ List.In "#ret_val"
    (runtime_local_declarations_from names formal_indices return_index index).*1.
Proof.
  revert index.
  induction names as [| Γ name t names IH]; intros index; simpl.
  - intros _ _ Hin. inversion Hin.
  - intros Hfresh Hbound.
    have Hhead : ~ "#ret_val" = name.
    { intros Heq. subst name. apply Hfresh. simpl. now left. }
    have Htail : ~ List.In "#ret_val" (named_context_names names).
    { intros Hin. apply Hfresh. simpl. now right. }
    destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
    + apply IH; [exact Htail|lia].
    + destruct (Nat.eqb index return_index) eqn:Hsame.
      * apply Nat.eqb_eq in Hsame. subst return_index. lia.
      * intros Hin. simpl in Hin. destruct Hin as [Hin | Hin].
        -- apply Hhead. symmetry. exact Hin.
        -- apply (IH (S index) Htail); [lia|exact Hin].
Qed.

Lemma runtime_local_declarations_from_nodup {Γ}
    (names : named_context Γ) (formal_indices : list nat)
    (return_index index : nat) :
  List.NoDup (named_context_names names) ->
  ~ List.In "#ret_val" (named_context_names names) ->
  NoDup
    (runtime_local_declarations_from names formal_indices return_index index).*1.
Proof.
  revert index.
  induction names as [| Γ name t names IH]; intros index; simpl.
  - constructor.
  - intros Hnames Hfresh.
    inversion Hnames as [| ? ? Hhead Htail].
    have Hfresh_tail : ~ List.In "#ret_val" (named_context_names names).
    { intros Hin. apply Hfresh. simpl. now right. }
    destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
    + apply IH; [exact Htail|exact Hfresh_tail].
    + constructor.
      * intros Hin. destruct (Nat.eqb index return_index) eqn:Hsame.
        -- apply Nat.eqb_eq in Hsame. subst return_index.
           apply (runtime_local_declarations_from_no_return_name names
              formal_indices index (S index) Hfresh_tail); [lia|].
           apply elem_of_list_In. exact Hin.
        -- simpl in Hin. destruct (runtime_local_declarations_from_source_index
             names formal_indices return_index (S index) name
             (ltac:(apply elem_of_list_In; exact Hin)))
             as [Hret | Hsource].
           ++ apply Hfresh. left. exact Hret.
           ++ destruct Hsource as (local_index & Hlookup & Hnot & Hreturn).
              apply Hhead. rewrite <- runtime_variables_are_names.
              apply elem_of_list_In. apply elem_of_list_lookup. exists local_index.
              exact Hlookup.
      * apply IH; [exact Htail|exact Hfresh_tail].
Qed.

Lemma runtime_local_declarations_from_contains_return {Γ}
    (names : named_context Γ) (formal_indices : list nat)
    (result index : nat) :
  index <= result -> result < index + length (runtime_variables names) ->
  ~ In result formal_indices ->
  "#ret_val" ∈
    (runtime_local_declarations_from names formal_indices result index).*1.
Proof.
  revert index.
  induction names as [| Γ name t names IH]; intros index; simpl.
  - intros Hle Hlt _. change (result < index + 0) in Hlt. lia.
  - intros Hle Hlt Hnot.
    destruct (Nat.eqb index result) eqn:Hsame.
    + apply Nat.eqb_eq in Hsame; subst result.
      destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
      * exfalso. apply Hnot.
        apply existsb_exists in Hformal.
        destruct Hformal as (candidate & Hin & Heq).
        apply Nat.eqb_eq in Heq. subst candidate. exact Hin.
      * simpl. apply elem_of_cons. left. reflexivity.
    + apply Nat.eqb_neq in Hsame.
      assert (Hlt_index : index < result) by lia.
      destruct (existsb (Nat.eqb index) formal_indices) eqn:Hformal.
      * apply IH; [lia|lia|exact Hnot].
      * simpl. right. apply IH; [lia|lia|exact Hnot].
Qed.

Lemma runtime_procedure_locals_nodup {Γ F} (procedure : typed_procedure Γ F) :
  procedure_wf procedure ->
  ~ List.In "#ret_val"
      (named_context_names (procedure_variables _ _ procedure)) ->
  NoDup (runtime_procedure_locals procedure).*1.
Proof.
  intros Hwf Hfresh.
  unfold runtime_procedure_locals.
  apply runtime_local_declarations_from_nodup.
  - exact (procedure_variable_names_unique _ Hwf).
  - exact Hfresh.
Qed.

Lemma runtime_procedure_local_source_index {Γ F}
    (procedure : typed_procedure Γ F) name :
  In name (runtime_procedure_locals procedure).*1 ->
  name = "#ret_val" \/
  exists local_index,
    runtime_variables (procedure_variables _ _ procedure) !! local_index =
      Some name /\
    ~ In local_index (pvar_list_indices (procedure_formal_variables _ _ procedure)) /\
    not (local_index = procedure_return_index procedure).
Proof.
  unfold runtime_procedure_locals.
  intros Hin. apply runtime_local_declarations_from_source_index in Hin.
  destruct Hin as [Hret | (local_index & Hlookup & Hnot & Hreturn)].
  - left; exact Hret.
  - right. exists local_index. split; [exact Hlookup|].
    split; simpl in *; assumption.
Qed.

Lemma runtime_procedure_return_local {Γ F} (procedure : typed_procedure Γ F) :
  procedure_wf procedure ->
  ~ List.In "#ret_val"
      (named_context_names (procedure_variables _ _ procedure)) ->
  "#ret_val" ∈ (runtime_procedure_locals procedure).*1.
Proof.
  intros Hwf Hfresh. apply runtime_local_declarations_from_contains_return.
  - lia.
  - rewrite runtime_variables_length. apply lvar_index_lt.
  - exact (procedure_return_slot_local _ Hwf).
Qed.

Lemma runtime_procedure_arguments_locals_disjoint {Γ F}
    (procedure : typed_procedure Γ F) :
  procedure_wf procedure ->
  ~ List.In "#ret_val"
      (named_context_names (procedure_variables _ _ procedure)) ->
  (runtime_procedure_arguments procedure).*1 ##
    (runtime_procedure_locals procedure).*1.
Proof.
  intros Hwf Hfresh name Hargument Hlocal.
  apply elem_of_list_In in Hargument.
  apply elem_of_list_In in Hlocal.
  destruct (runtime_formal_name_index
      (procedure_variables _ _ procedure)
      (procedure_formal_variables _ _ procedure) name Hargument)
    as (formal_index & Hformal_index & Hformal_lookup).
  destruct (runtime_procedure_local_source_index procedure name Hlocal)
    as [Hreturn |
      (local_index & Hlocal_lookup & Hlocal_not_formal & Hlocal_not_return)].
  - subst name. apply Hfresh. rewrite <- runtime_variables_are_names.
    apply elem_of_list_In. apply elem_of_list_lookup.
    exists formal_index. exact Hformal_lookup.
  - have Hindices : formal_index = local_index.
    { have Hnames := procedure_variable_names_unique _ Hwf.
      rewrite <- runtime_variables_are_names in Hnames.
      eapply NoDup_lookup;
        [apply NoDup_ListNoDup; exact Hnames | exact Hformal_lookup |].
      exact Hlocal_lookup. }
    apply Hlocal_not_formal. rewrite <- Hindices. exact Hformal_index.
Qed.

Lemma runtime_procedure_declaration_names_cover {Γ F}
    (procedure : typed_procedure Γ F) :
  procedure_wf procedure ->
  (list_to_set (runtime_procedure_arguments procedure).*1 :
      gset RuntimeLang.var) ∪
      (list_to_set (runtime_procedure_locals procedure).*1 :
        gset RuntimeLang.var) =
    (list_to_set (runtime_variables (runtime_procedure_names procedure)) :
      gset RuntimeLang.var).
Proof.
  intros Hwf. apply set_eq. intro name.
  rewrite elem_of_union. rewrite !elem_of_list_to_set.
  split.
  - intros [Hargument | Hlocal].
    + apply elem_of_list_In in Hargument.
      destruct (runtime_formal_name_index
        (procedure_variables _ _ procedure)
        (procedure_formal_variables _ _ procedure) name Hargument)
        as (index & Hformal & Hlookup).
      apply elem_of_list_lookup. exists index.
      unfold runtime_procedure_names.
      rewrite runtime_variables_rename_named_context_at_lookup_other.
      * exact Hlookup.
      * intros Heq. subst index.
        exact (procedure_return_slot_local _ Hwf Hformal).
    + apply elem_of_list_In in Hlocal.
      destruct (runtime_procedure_local_source_index procedure name Hlocal)
        as [-> | (index & Hlookup & Hnotformal & Hnotreturn)].
      * rewrite <- (runtime_procedure_return_name procedure).
        apply runtime_variable_member.
      * apply elem_of_list_lookup. exists index.
        unfold runtime_procedure_names.
        rewrite runtime_variables_rename_named_context_at_lookup_other;
          assumption.
  - intros Hname.
    apply elem_of_list_In in Hname.
    destruct (runtime_variable_member_inv
      (runtime_procedure_names procedure) name Hname)
      as (t & variable & <-).
    destruct (in_dec Nat.eq_dec (lvar_index variable)
      (pvar_list_indices (procedure_formal_variables _ _ procedure)))
      as [Hformal | Hlocal].
    + left. apply elem_of_list_In.
      destruct (pvar_list_index_member
        (procedure_formal_variables _ _ procedure) variable Hformal)
        as (formal_variable & Hvariable).
      subst variable. apply in_map_iff.
      exists (runtime_variable (procedure_variables _ _ procedure)
        (lookup_pvar_list (procedure_formal_variables _ _ procedure)
          formal_variable), runtime_type t). split.
      * simpl. unfold runtime_procedure_names.
        rewrite runtime_variable_rename_named_context_at_other; first reflexivity.
        intros Heq. apply (procedure_return_slot_local _ Hwf).
        rewrite <- Heq. exact Hformal.
      * apply runtime_formal_declarations_lookup.
    + right. apply elem_of_list_In. apply in_map_iff.
      exists (runtime_variable (runtime_procedure_names procedure) variable,
        runtime_type t). split; first reflexivity.
      apply runtime_procedure_local_declaration. exact Hlocal.
Qed.

Definition runtime_unop {input output} (op : unop input output) :
    un_op :=
  match op with
  | UNot => NotBoolOp
  | UNeg => NegOp
  | URAOfInt resource => RAOfIntOp resource
  end.

Definition runtime_binop {left right output}
    (op : binop left right output) : bin_op :=
  match op with
  | BAdd => AddOp | BSub => SubOp
  | BMul => MulOp | BDiv => DivOp
  | BMod => ModOp | BLt => LtOp
  | BLe => LeOp | BGt => GtOp
  | BGe => GeOp | BEq _ => EqOp
  | BNe _ => NeOp | BAnd => AndOp
  | BOr => OrOp
  end.

Lemma tval_to_val_injective t : Inj (=) (=) (@tval_to_val t).
Proof.
  intros left right Heq.
  destruct t; dependent destruction left; dependent destruction right;
    simpl in Heq; inversion Heq; try reflexivity.
  apply (Eqdep_dec.inj_pair2_eq_dec string String.string_dec) in H0.
  subst. reflexivity.
Qed.

Lemma runtime_unop_sound {input output} (op : unop input output)
    (value : tval input) :
  RuntimeLang.un_op_eval (runtime_unop op) (tval_to_val value) =
    Some (tval_to_val (interp_unop op value)).
Proof. destruct op; dependent destruction value; reflexivity. Qed.

Lemma runtime_eqb_sound t (left right : tval t) :
  bool_decide (tval_to_val left = tval_to_val right) =
    tval_eqb t left right.
Proof.
  destruct (bool_decide (tval_to_val left = tval_to_val right)) eqn:Hvalues_equal,
    (tval_eqb t left right) eqn:Htyped; try reflexivity.
  - apply bool_decide_eq_true in Hvalues_equal.
    apply tval_to_val_injective in Hvalues_equal. subst.
    assert (tval_eqb t right right = true) as Heq.
    { apply Core.tval_eqb_eq. reflexivity. }
    congruence.
  - apply Core.tval_eqb_eq in Htyped. subst.
    assert (bool_decide (tval_to_val right = tval_to_val right) = true) as Heq.
    { apply bool_decide_eq_true. reflexivity. }
    congruence.
Qed.

Lemma runtime_neqb_sound t (left right : tval t) :
  bool_decide (not (tval_to_val left = tval_to_val right)) =
    negb (tval_eqb t left right).
Proof.
  destruct (tval_eqb t left right) eqn:Htyped.
  - apply Core.tval_eqb_eq in Htyped. subst. simpl.
    apply bool_decide_eq_false. intros Hneq. apply Hneq. reflexivity.
  - simpl. apply bool_decide_eq_true. intros Heq.
    apply tval_to_val_injective in Heq. subst.
    assert (tval_eqb t right right = true) as Hrefl.
    { apply Core.tval_eqb_eq. reflexivity. }
    congruence.
Qed.

Lemma runtime_binop_sound {left right output}
    (op : binop left right output) (value1 : tval left)
    (value2 : tval right) (result : tval output) :
  interp_binop op value1 value2 = Some result ->
  RuntimeLang.bin_op_eval (runtime_binop op)
    (tval_to_val value1) (tval_to_val value2) = Some (tval_to_val result).
Proof.
  destruct op.
  all: try solve [simpl; rewrite runtime_eqb_sound;
    intros Heq; inversion Heq; reflexivity].
  all: try solve [simpl; rewrite runtime_neqb_sound;
    intros Heq; inversion Heq; reflexivity].
  all: dependent destruction value1; dependent destruction value2;
    simpl; intros Heq; inversion Heq; subst; reflexivity.
Qed.

Fixpoint runtime_expr {Γ keep t} (names : named_context Γ)
    (expression : pexpr keep Γ t) : RuntimeLang.expr :=
  match expression with
  | PEVar variable => RuntimeLang.Var (runtime_variable names variable)
  | PEVal value => RuntimeLang.Val (tval_to_val value)
  | PEUnOp op operand =>
      RuntimeLang.UnOp (runtime_unop op) (runtime_expr names operand)
  | PEBinOp op operand1 operand2 =>
      RuntimeLang.BinOp (runtime_binop op)
        (runtime_expr names operand1) (runtime_expr names operand2)
  end.

(** A runtime stack frame represents a symbolic typed store when each
    local is bound to the interpretation of its symbolic value.
    Keeping this relation extensional avoids dependent transports in the
    operational simulation proofs. *)
Definition stack_corresponds {Γ F Δ}
    (names : named_context Γ) (formals : formal_env F)
    (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (frame : RuntimeLang.stack_frame) : Prop :=
  forall keep t (variable : lvar keep Γ t),
    lvar_runtime variable = true ->
    frame.(RuntimeLang.locals) !! runtime_variable names variable =
      Some (tval_to_val
        (interp_ref formals binders valuation (lookup_store store t variable))).

Lemma runtime_expr_sound {Γ F Δ t} (names : named_context Γ)
    (formals : formal_env F) (binders : binder_env Δ) (valuation : symbol_valuation)
    (store : symbolic_store Γ F Δ) (frame : RuntimeLang.stack_frame)
    (expression : pexpr keep_runtime Γ t) (value : tval t) :
  stack_corresponds names formals binders valuation store frame ->
  interp_program_expr formals binders valuation store expression = Some value ->
  RuntimeLang.expr_step (runtime_expr names expression) frame
    (RuntimeLang.Val (tval_to_val value)).
Proof.
  intros Hstack. unfold interp_program_expr. induction expression; simpl.
  - intros Heq. inversion Heq. subst. apply RuntimeLang.VarStep.
    apply Hstack. apply (lvar_runtime_keep (keep := keep_runtime)).
  - intros Heq. inversion Heq. subst. apply RuntimeLang.ExprRefl.
  - destruct (interp_expr formals binders valuation
        (IR.symbolize_expr store expression))
      as [operand_value|] eqn:Hoperand; simpl; [|discriminate].
    intros Heq. inversion Heq. subst. eapply RuntimeLang.UnOpStep.
    + apply IHexpression. reflexivity.
    + apply runtime_unop_sound.
  - destruct (interp_expr formals binders valuation
        (IR.symbolize_expr store expression1))
      as [value1|] eqn:Hvalue1; simpl; [|discriminate].
    destruct (interp_expr formals binders valuation
        (IR.symbolize_expr store expression2))
      as [value2|] eqn:Hvalue2; simpl; [|discriminate].
    intros Heq. eapply RuntimeLang.BinOpStep.
    + apply IHexpression1. reflexivity.
    + apply IHexpression2. reflexivity.
    + eapply runtime_binop_sound. exact Heq.
Qed.

Fixpoint runtime_expr_list {Γ keep ts} (names : named_context Γ)
    (expressions : pexpr_list keep Γ ts) : list RuntimeLang.expr :=
  match expressions with
  | PENil => []
  | PECons expression expressions' =>
      runtime_expr names expression :: runtime_expr_list names expressions'
  end.

Lemma runtime_expr_list_length {Γ keep ts} (names : named_context Γ)
    (expressions : pexpr_list keep Γ ts) :
  length (runtime_expr_list names expressions) = length ts.
Proof. induction expressions; simpl; congruence. Qed.

Fixpoint runtime_field_initializers {Γ} (names : named_context Γ)
    (fields : list (field_init Γ)) :
    list (RuntimeLang.fld_name * RuntimeLang.expr) :=
  match fields with
  | [] => []
  | FieldInit field value :: fields' =>
      (field_name field, runtime_expr names value) ::
      runtime_field_initializers names fields'
  end.

Definition runtime_physical_field_initializers {Γ} (names : named_context Γ)
    (fields : list (field_init Γ)) :
    list (RuntimeLang.fld_name * RuntimeLang.expr) :=
  runtime_field_initializers names (physical_field_initializers fields).

Definition runtime_packed_ghost_field_names {Γ}
    (fields : list (ghost_field_init Γ)) : list RuntimeLang.fld_name :=
  map (fun initialization => match initialization with
    | GhostFieldInit _ field _ _ => field_name field
    end) fields.

Definition runtime_ghost_field_names {Γ} (fields : list (field_init Γ)) :
    list RuntimeLang.fld_name :=
  runtime_packed_ghost_field_names (ghost_field_initializers fields).

(** The runtime terminal statement.  Erasure maps the empty continuation
    and every proof-only statement to it; it takes no physical step. *)
Definition runtime_noop : RuntimeLang.runtime_stmt :=
  RuntimeLang.RTVal RuntimeLang.LitUnit.

Definition runtime_is_noop (statement : RuntimeLang.runtime_stmt) : bool :=
  match statement with
  | RuntimeLang.RTVal RuntimeLang.LitUnit => true
  | _ => false
  end.

Lemma runtime_is_noop_spec statement :
  runtime_is_noop statement = true <-> statement = runtime_noop.
Proof.
  split.
  - destruct statement; try discriminate.
    match goal with v : RuntimeLang.val |- _ => destruct v end;
      try discriminate; reflexivity.
  - intros ->. reflexivity.
Qed.

(** Sequencing that drops a terminal operand, so erased proof-only
    statements never contribute an [RTSeq] (and hence a physical step). *)
Definition runtime_seq (first second : RuntimeLang.runtime_stmt) :
    RuntimeLang.runtime_stmt :=
  if runtime_is_noop first then second
  else if runtime_is_noop second then first
  else RuntimeLang.RTSeq first second.

(** A conditional whose arms both erase to the terminal statement is itself
    proof-only: evaluating its pure condition is not observable. *)
Definition runtime_if (condition : RuntimeLang.expr)
    (then_branch else_branch : RuntimeLang.runtime_stmt)
    (stack : RuntimeLang.stack_id) : RuntimeLang.runtime_stmt :=
  if runtime_is_noop then_branch && runtime_is_noop else_branch
  then runtime_noop
  else RuntimeLang.RTIfS condition then_branch else_branch stack.

Lemma runtime_seq_noop_l statement :
  runtime_seq runtime_noop statement = statement.
Proof. reflexivity. Qed.

Lemma runtime_seq_physical first second :
  runtime_is_noop first = false -> runtime_is_noop second = false ->
  runtime_seq first second = RuntimeLang.RTSeq first second.
Proof. intros Hfirst Hsecond. unfold runtime_seq. rewrite Hfirst Hsecond. reflexivity. Qed.

(** Case analysis on the smart constructor, stated for an arbitrary
    predicate so clients can [apply] it without rewriting. *)
Lemma runtime_seq_ind (P : RuntimeLang.runtime_stmt -> Prop) first second :
  (first = runtime_noop -> P second) ->
  (second = runtime_noop -> P first) ->
  (runtime_is_noop first = false -> runtime_is_noop second = false ->
    P (RuntimeLang.RTSeq first second)) ->
  P (runtime_seq first second).
Proof.
  intros Hfirst Hsecond Hboth. unfold runtime_seq.
  destruct (runtime_is_noop first) eqn:Hfirst_noop.
  { apply Hfirst. apply runtime_is_noop_spec. exact Hfirst_noop. }
  destruct (runtime_is_noop second) eqn:Hsecond_noop.
  { apply Hsecond. apply runtime_is_noop_spec. exact Hsecond_noop. }
  apply Hboth; reflexivity.
Qed.

(** Case analysis on the conditional smart constructor. *)
Lemma runtime_if_ind (P : RuntimeLang.runtime_stmt -> Prop)
    condition then_branch else_branch stack :
  (then_branch = runtime_noop -> else_branch = runtime_noop ->
    P runtime_noop) ->
  (runtime_is_noop then_branch && runtime_is_noop else_branch = false ->
    P (RuntimeLang.RTIfS condition then_branch else_branch stack)) ->
  P (runtime_if condition then_branch else_branch stack).
Proof.
  intros Hnoop Hphysical. unfold runtime_if.
  destruct (runtime_is_noop then_branch) eqn:Hthen;
    destruct (runtime_is_noop else_branch) eqn:Helse; simpl;
    [apply Hnoop; apply runtime_is_noop_spec; assumption
    |apply Hphysical; reflexivity ..].
Qed.

Lemma runtime_seq_noop_r statement :
  runtime_seq statement runtime_noop = statement.
Proof.
  unfold runtime_seq. destruct (runtime_is_noop statement) eqn:Hnoop;
    [symmetry; apply runtime_is_noop_spec; exact Hnoop | reflexivity].
Qed.

Fixpoint runtime_stmt {Γ} (names : named_context Γ)
    (stack : RuntimeLang.stack_id) (statement : stmt Γ) :
    RuntimeLang.runtime_stmt :=
  match statement with
  | TDone => runtime_noop
  | TAssert _ => runtime_noop
  | TAssign _ target value =>
      RuntimeLang.RTAssign (runtime_variable names target)
        (runtime_expr names value) stack
  | TFieldRead _ field target base =>
      RuntimeLang.RTFldRd (runtime_variable names target)
        (runtime_expr names base) (field_name field) stack
  | TFieldWrite field base value =>
      RuntimeLang.RTFldWr (runtime_expr names base)
        (field_name field) (runtime_expr names value) stack
  | TAlloc _ target fields =>
      RuntimeLang.RTAlloc (runtime_variable names target)
        (runtime_field_initializers names
          (physical_field_initializers fields)) stack
  | TGhostUpdate _ _ _ _ => runtime_noop
  | TCall procedure arguments target =>
      match target with
      | CTStore _ target' =>
          RuntimeLang.RTCall (runtime_variable names target')
            (procedure_name procedure)
            (runtime_expr_list names arguments) stack
      | CTDiscard =>
          RuntimeLang.RTCallNoStore
            (procedure_name procedure)
            (runtime_expr_list names arguments) stack
      end
  | TSpawn procedure arguments =>
      RuntimeLang.RTSpawn (procedure_name procedure)
        (runtime_expr_list names arguments) stack
  | TUnfold _ _ | TFold _ _
  | TPredicateUnfold _ _ | TPredicateFold _ _ => runtime_noop
  | TInvAccess _ _ body => runtime_stmt names stack body
  | TIf condition then_branch else_branch =>
      runtime_if (runtime_expr names condition)
        (runtime_stmt names stack then_branch)
        (runtime_stmt names stack else_branch) stack
  | TSeq first second =>
      runtime_seq (runtime_stmt names stack first)
        (runtime_stmt names stack second)
  | TAtomic body =>
      RuntimeLang.RTTrustedAtomic (trusted_atomic_transition body) stack
  | TGhostVal name t _ body =>
      runtime_stmt (NCCons name (ghost_val t) names) stack body
  end.

End WithSignature.
(** The trusted substrate observes an atomic block only through its runtime
    behavior.  Consequently, proof-only rewrites with identical erasure
    select the same opaque hardware transition.  Like the refinement law,
    this is a framework property, never a module-specific obligation. *)
Axiom trusted_atomic_transition_runtime_erasure : forall {RAs : RAConfig}
    {Logic : Assertion.LogicSignature} {Γ}
    (body body' : stmt Γ),
  (forall (names : named_context Γ) (stack : RuntimeLang.stack_id),
    runtime_stmt names stack body = runtime_stmt names stack body') ->
  trusted_atomic_transition body = trusted_atomic_transition body'.

Section WithSignature.
Context {RAs : RAConfig} {Logic : Assertion.LogicSignature}.
Lemma runtime_stmt_atomic {Γ} (names : named_context Γ) stack
    (body : stmt Γ) :
  runtime_stmt names stack (TAtomic body) =
    RuntimeLang.RTTrustedAtomic (trusted_atomic_transition body) stack.
Proof. reflexivity. Qed.

(** A proof-only rewrite of an atomic body cannot change its runtime
    statement. No hypothesis about the transition is
    needed -- it simply cannot see the difference. *)
Lemma runtime_stmt_atomic_congruence {Γ} (names : named_context Γ) stack
    (body body' : stmt Γ) :
  (forall (names : named_context Γ) (stack : RuntimeLang.stack_id),
    runtime_stmt names stack body = runtime_stmt names stack body') ->
  runtime_stmt names stack (TAtomic body) =
    runtime_stmt names stack (TAtomic body').
Proof.
  intros Herasure.
  rewrite !runtime_stmt_atomic.
  rewrite (trusted_atomic_transition_runtime_erasure body body' Herasure).
  reflexivity.
Qed.

End WithSignature.
End RuntimeErasure.
