From stdpp Require Export binders strings.
From stdpp Require Import countable.
From stdpp Require Import gmap list sets coPset.
From stdpp Require Import namespaces.

From iris Require Import options.
From iris.algebra Require Import ofe cmra agree auth gset gmap.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import invariants.

From raven Require Export runtime.lang runtime.lifting runtime.ghost_state.
From raven Require Import runtime.ghost_state.

(** Ghost state for Raven's nominal invariant assertions, and the capability
    bundle an adequacy wrapper needs in order to allocate it.

    This layer sits between the operational language and any logic built on
    top of it: it is the runtime backing for "invariant [i] was established
    at argument vector [args]", and it is independent of how a particular
    logic states or proves such a fact. *)
Module InvTokens.

Module Make (RAs : RA_CONFIG).
Module lifting := raven.runtime.lifting.Make RAs.
Module ghost_state := lifting.ghost_state.
Module lang := ghost_state.lang.
Import lang ghost_state lifting.

Set Default Proof Using "Type".

(* The ghost heap's own inG requirement, isolated as a subG-derivable
   capability.  Unlike heapG/invTokenG it bundles no gname alongside the inG
   evidence, so no separate GpreS/GS split is needed -- just this one fact,
   combined into ravenΣ below. *)
Definition ghostHeapInGΣ : gFunctors := #[ GFunctor (authR (gmapUR heap_addr (agreeR gnameO))) ].

Global Instance subG_ghostHeapInG Σ' : subG ghostHeapInGΣ Σ' → inG Σ' (authR (gmapUR heap_addr (agreeR gnameO))).
Proof. solve_inG. Qed.

Definition inv_name := string.

(* The value vector an invariant is established at.  It mirrors [lang.val]
   constructor for constructor, including the [LitRAElem] case, so the
   isomorphism with runtime values extends to RA elements too. *)
Inductive val :=
| LitBool (b: bool) | LitInt (i: Z) | LitUnit | LitLoc (l: loc)
| LitRAElem (p : ra_elem).

Global Instance val_eq : EqDecision val.
Proof.
  refine (fun x y =>
    match x, y with
    | LitBool b1, LitBool b2 => cast_if (decide (b1 = b2))
    | LitInt i1, LitInt i2 => cast_if (decide (i1 = i2))
    | LitUnit, LitUnit => left eq_refl
    | LitLoc l1, LitLoc l2 => cast_if (decide (l1 = l2))
    | LitRAElem p1, LitRAElem p2 => cast_if (decide (p1 = p2))
    | _, _ => right _
    end).
  all: try by f_equal.
  all: try intros Heq; inversion Heq; auto.
Qed.

(* Hand-rolled in place of `Scheme Equality for val`: that command cannot
   derive a comparator for the [LitRAElem] case, whose argument type
   [ra_elem] is a sigma type rather than something the generator recognizes.
   [val_beq] / [internal_val_dec_bl] / [internal_val_dec_lb] keep the exact
   names and statement shapes Scheme Equality would have produced, because
   existing clients depend on them under these names. *)
Definition val_beq (v1 v2 : val) : bool := bool_decide (v1 = v2).

Lemma internal_val_dec_bl : forall v1 v2 : val, val_beq v1 v2 = true -> v1 = v2.
Proof. intros v1 v2 H. unfold val_beq in H. by apply bool_decide_eq_true in H. Qed.

Lemma internal_val_dec_lb : forall v1 v2 : val, v1 = v2 -> val_beq v1 v2 = true.
Proof. intros v1 v2 H. unfold val_beq. by apply bool_decide_eq_true. Qed.

Global Instance val_countable : Countable val.
Proof.
  refine (inj_countable'
    (λ v : val, match v with
      | LitBool b => inl b
      | LitInt i  => inr (inl i)
      | LitUnit   => inr (inr (inl tt))
      | LitLoc l  => inr (inr (inr (inl l)))
      | LitRAElem p => inr (inr (inr (inr p)))
    end)
    (λ x : bool + (Z + (unit + (loc + ra_elem))), match x with
      | inl b             => LitBool b
      | inr (inl i)       => LitInt i
      | inr (inr (inl _)) => LitUnit
      | inr (inr (inr (inl l))) => LitLoc l
      | inr (inr (inr (inr p))) => LitRAElem p
    end) _).
  intro v; destruct v; done.
Qed.

(* Ghost state backing a nominal invariant assertion: a fragment recording
   that the invariant was established at a concrete argument vector.  The
   carrier is discrete (a plain gset of value lists), so the fragment is
   Timeless -- which is what lets an invariant be opened without a later.
   Access exclusivity comes from Iris's mask-changing atomic accessor, not
   from a client-owned ghost lock token. *)
Definition inv_argsUR : ucmra := gsetUR (list val).

Class invTokenG (Σ : gFunctors) := InvTokenG {
  invtoken_inG :: inG Σ (authR inv_argsUR);
  invtoken_names : inv_name -> gname;
}.

(* The camera capability [invTokenG] needs, without the concrete
   [invtoken_names] assignment -- mirroring ghost_state.v's own
   heapGpreS/heapG split.  [invTokenG] bundles a concrete gname-valued
   function together with the inG evidence, so a full instance cannot be
   derived from subG alone; only this "pre" half can.  Producing
   [invtoken_names] is own_alloc work, done once per invariant name a
   program declares, and belongs to the adequacy wrapper. *)
Class invTokenGpreS (Σ : gFunctors) := InvTokenGpreS {
  invtoken_pre_inG :: inG Σ (authR inv_argsUR);
}.

Definition invTokenGΣ : gFunctors := #[ GFunctor (authR inv_argsUR) ].

Global Instance subG_invTokenGpreS Σ' : subG invTokenGΣ Σ' → invTokenGpreS Σ'.
Proof. solve_inG. Qed.

(* The capability list a caller of an adequacy wrapper needs from a single
   subG hypothesis in order to build the instances its own Context expects.
   It deliberately omits two things: the RA/program-specific ambient
   resources, which are picked per the resource algebra being verified
   rather than being a fixed capability, and [simpLangG] itself, which
   bundles concrete gnames rather than just inG evidence and so needs
   own_alloc/wp_adequacy work the caller does separately -- heapGΣ and invΣ
   below cover only the "pre" half of building one.

   subG's transitivity through gFunctors append lets subG_heapGpreS,
   subG_invTokenGpreS, subG_ghostHeapInG and Iris's own subG_invΣ each fire
   straight off `subG ravenΣ Σ'` via solve_inG.  The four lemmas below check
   that directly rather than assuming it, since invGpreS -- unlike the other
   three -- needs an explicit `apply subG_invΣ` first: solve_inG alone does
   not chase through invΣ's own name to find it. *)
Definition ravenΣ : gFunctors := #[ heapGΣ; invTokenGΣ; ghostHeapInGΣ; invΣ ].

Lemma ravenΣ_subG_heapGpreS Σ' `{!subG ravenΣ Σ'} : heapGpreS Σ'.
Proof. solve_inG. Qed.

Lemma ravenΣ_subG_invTokenGpreS Σ' `{!subG ravenΣ Σ'} : invTokenGpreS Σ'.
Proof. solve_inG. Qed.

Lemma ravenΣ_subG_ghostHeapInG Σ' `{!subG ravenΣ Σ'} :
  inG Σ' (authR (gmapUR heap_addr (agreeR gnameO))).
Proof. solve_inG. Qed.

Lemma ravenΣ_subG_invGpreS Σ' `{!subG ravenΣ Σ'} : invGpreS Σ'.
Proof. apply subG_invΣ. solve_inG. Qed.

End Make.

End InvTokens.
