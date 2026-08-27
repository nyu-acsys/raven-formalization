From stdpp Require Export binders strings.
From stdpp Require Import countable.
Require Import Eqdep_dec.
From stdpp Require Import gmap list sets coPset.
From stdpp Require Import namespaces.
From stdpp Require Import pretty.
From Coq Require Import Ascii.

From iris Require Import options.
From iris.algebra Require Import ofe cmra agree auth gset gmap.
From iris.bi.lib Require Import fixpoint_mono.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import ghost_map.
From iris.base_logic.lib Require Import invariants.

From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.proofmode Require Import tactics.

From raven_iris.simp_raven_lang Require Export lang lifting ghost_state.
From raven_iris.simp_raven_lang Require Import ghost_state.

From Coq.Program Require Import Wf.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Program.Equality.
Require Import Coq.Init.Datatypes.

(* "All", not "Type": Coq's "Type" default still tries to minimize which
   section variables each proof closes over, and that minimization gets
   confused by broad-search tactics (naive_solver etc.), spuriously
   rejecting proofs as depending on unrelated section variables. "All"
   unconditionally closes every proof over every variable in scope at
   that point -- harmless here, since we only care that the few
   externally-visible definitions (RavenHoareTriple, raven_soundness,
   ...) end up with the right dependencies, not that internal lemmas have
   minimal signatures. *)
Set Default Proof Using "Type".

Class inGs {I : Type} (Σ : gFunctors) (Gs : I → cmra) := {
  inGs_inG : ∀ i, inG Σ (Gs i)
}.

Section WithProgram.

(* Sigma/Gs/I/simpLangG live *inside* this section (not, as before, ambient
   for the whole file) precisely so End WithProgram discharges them into
   explicit arguments too, same as Program/GhostConfig/Gamma/invTokenG
   already are -- otherwise nothing downstream (trnsl.v's own adequacy
   wrapper, eventually) could ever supply a concrete Sigma at all: a
   Context declared outside any Section that closes within this file is
   permanently fixed, no different from a bare Axiom. *)
Context {I : Type}.
Context (Gs : I → cmra).
Context `{!inGs Σ Gs}.
(* Backing resource for the ghost heap (Wghost, below): one authoritative
   map per ambient RA slot i, keyed by (loc, fld_name) via heap_addr,
   holding elements of the very same Gs i that Γ already embeds RA_carrier
   values into. This lets LGhostOwn's translation reuse Γ's existing
   RA_Pack ↦ i embedding unchanged, just wrapped in one extra
   auth/gmap layer.

   The map only ever stores *gnames* (agreement-typed, never updated after
   insertion), not RA elements directly: each (loc, fld) key names a
   freshly own_alloc'd gname, and the actual RA ownership still lives at
   that gname directly via a bare own, exactly as in the original
   ghost_map design. This keeps FPURule's frame-preserving update a bare
   own_update with no map/auth involvement at all -- updating a map
   fragment in place would need a *local* update accounting for whatever
   else is framed at that key (e.g. an invariant's own share of the same
   RA cell), which a bare RA-level ~~> update doesn't in general provide.
   The map's only job is solving the freshness/naming problem; RA-level
   sharing is entirely delegated back to the RA itself, same as before. *)
Context `{!inG Σ (authR (gmapUR heap_addr (agreeR gnameO)))}.

(* Layer 0: the ghost-heap's own inG requirement, isolated as a
   subG-derivable capability. Unlike
   heapG/invTokenG it doesn't bundle any gname alongside the inG evidence,
   so no separate GpreS/GS split is needed here -- just this one fact,
   combined into ravenΣ below. *)
Definition ghostHeapInGΣ : gFunctors := #[ GFunctor (authR (gmapUR heap_addr (agreeR gnameO))) ].

Global Instance subG_ghostHeapInG Σ' : subG ghostHeapInGΣ Σ' → inG Σ' (authR (gmapUR heap_addr (agreeR gnameO))).
Proof. solve_inG. Qed.

Context `{!simpLangG Σ}.

Definition lvar := string.

Definition proc_name := string.

Definition pred_name := string.

Definition inv_name := string.

(* ResourceAlgebra/RA_Pack/ra_name/ra_set/ra_map/ra_elem live in
   simp_raven_lang/lang.v (re-exported here via `Require Export lang`
   above): RA elements are ordinary program values (typ's TpRA, val's
   LitRAElem below), not a ghost-only concept, so they belong at the base
   of the language rather than in this spec layer. *)

Record fld := Fld { fld_name_val : fld_name; fld_typ : typ }.

(* Ghost heap: one standing authoritative gname->gname map (see Wghost,
   Section GhostHeapWorld below), not a bare per-(loc,fld) gname --
   own_alloc can only ever hand out a fresh, existentially-chosen name,
   never one chosen in advance, so a specific (l, fld) can't be given
   ownership directly. Instead, HeapAllocRule own_alloc's a genuinely
   fresh gname per ghost field and records the (l,fld) -> gname binding by
   growing this one standing authoritative map; the RA ownership itself
   still lives at that freshly-minted gname via a bare own, exactly as in
   the original design, so FPURule's update never touches this map at
   all. *)

(* val mirrors lang.val exactly (see trnsl_lval/trnsl_val below), including
   its LitRAElem case, so that isomorphism extends to RA elements too. *)
Inductive val :=
| LitBool (b: bool) | LitInt (i: Z) | LitUnit | LitLoc (l: loc)
| LitRAElem (p : ra_elem).

(* EqDecision val is needed already by val_beq right below (interp_lexpr's
   EqOp/NeOp cases use val_beq, and interp_lexpr comes before LExpr's other
   infrastructure), so it's placed here rather than alongside LExpr's own
   infrastructure further down (after interp_lexpr/lexpr_subst). *)
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

(* Hand-rolled in place of `Scheme Equality for val`: that command can't
   derive a comparator for the LitRAElem case (its argument type ra_elem is
   a sigma type, not something Scheme Equality's generator recognizes).
   val_beq/internal_val_dec_bl/internal_val_dec_lb keep the exact names and
   statement shapes Scheme Equality would have produced, since ~30 sites in
   this file and trnsl.v already depend on them under these names. *)
Definition val_beq (v1 v2 : val) : bool := bool_decide (v1 = v2).

Lemma internal_val_dec_bl : forall v1 v2 : val, val_beq v1 v2 = true -> v1 = v2.
Proof. intros v1 v2 H. unfold val_beq in H. by apply bool_decide_eq_true in H. Qed.

Lemma internal_val_dec_lb : forall v1 v2 : val, v1 = v2 -> val_beq v1 v2 = true.
Proof. intros v1 v2 H. unfold val_beq. by apply bool_decide_eq_true. Qed.

Inductive LExpr :=
| LVar (x : lvar)
| LVal (v : val)
| LUnOp (op : un_op) (e : LExpr)
| LBinOp (op : bin_op) (e1 e2 : LExpr)
(* | LIfE  *)
| LIfE (e1 e2 e3 : LExpr)
| LStuck
.

(* Free variables of a logical expression *)
Fixpoint lexpr_fvars (e : LExpr) : gset lvar :=
  match e with
  | LVar x => {[x]}
  | LVal _ => ∅
  | LUnOp _ e => lexpr_fvars e
  | LBinOp _ e1 e2 => lexpr_fvars e1 ∪ lexpr_fvars e2
  | LIfE e1 e2 e3 => lexpr_fvars e1 ∪ lexpr_fvars e2 ∪ lexpr_fvars e3
  | LStuck => ∅
  end.

(* Free variables in all values of a map *)
Definition lexpr_map_fvars (M : gmap lvar LExpr) : gset lvar :=
  map_fold (λ (_ : lvar) (e : LExpr) (acc : gset lvar), lexpr_fvars e ∪ acc) ∅ M.

Lemma lexpr_map_fvars_spec (M : gmap lvar LExpr) (v : lvar) :
  v ∉ lexpr_map_fvars M ↔ ∀ k e, M !! k = Some e → v ∉ lexpr_fvars e.
Proof.
  unfold lexpr_map_fvars.
  induction M using map_ind.
  - rewrite map_fold_empty. split.
    + intros _ k e. rewrite lookup_empty. discriminate.
    + intros _. apply not_elem_of_empty.
  - rewrite map_fold_insert.
    2: { intros. set_solver. }
    2: { exact H. }
    rewrite not_elem_of_union. rewrite IHM.
    split.
    + intros [Hfv Hacc] k' e' Hk'.
      destruct (decide (k' = i)) as [-> | Hne].
      * rewrite lookup_insert in Hk'. injection Hk' as <-. exact Hfv.
      * rewrite lookup_insert_ne in Hk'; [| congruence].
        exact (Hacc k' e' Hk').
    + intro Hall. split.
      * eapply Hall. apply lookup_insert.
      * intros k' e' Hk'. apply (Hall k' e').
        destruct (decide (k' = i)) as [-> | Hne].
        { rewrite Hk' in H. discriminate. }
        { rewrite lookup_insert_ne; [exact Hk' | congruence]. }
Qed.

(* Inserting a fresh binding can only grow lexpr_map_fvars by the new
   value's own fvars. *)
Lemma lexpr_map_fvars_insert_subseteq (M : gmap lvar LExpr) (k : lvar) (v : LExpr) :
  lexpr_map_fvars (<[k := v]> M) ⊆ lexpr_fvars v ∪ lexpr_map_fvars M.
Proof.
  intros x Hx.
  destruct (decide (x ∈ lexpr_fvars v)) as [Hv | Hv]; [set_solver |].
  destruct (decide (x ∈ lexpr_map_fvars M)) as [HM | HM]; [set_solver |].
  exfalso.
  have Hn : x ∉ lexpr_map_fvars (<[k := v]> M).
  { apply (proj2 (lexpr_map_fvars_spec _ x)).
    intros k' e' Hk'.
    destruct (decide (k' = k)) as [-> | Hne].
    - rewrite lookup_insert in Hk'. injection Hk' as <-. exact Hv.
    - rewrite lookup_insert_ne in Hk'; [| congruence].
      exact (proj1 (lexpr_map_fvars_spec M x) HM k' e' Hk'). }
  exact (Hn Hx).
Qed.

(* lexpr_map_fvars of a zipped-up substitution map is bounded by the union
   of the values' own fvars -- collapsing duplicate keys via list_to_map
   can only shrink the union, never exceed it. *)
Lemma lexpr_map_fvars_zip_subseteq (ks : list lvar) (vs : list LExpr) :
  lexpr_map_fvars (list_to_map (zip ks vs) : gmap lvar LExpr) ⊆ ⋃ (lexpr_fvars <$> vs).
Proof.
  revert vs. induction ks as [| k ks' IH]; intros vs; simpl.
  - unfold lexpr_map_fvars. rewrite map_fold_empty. set_solver.
  - destruct vs as [| v vs']; simpl.
    + unfold lexpr_map_fvars. rewrite map_fold_empty. set_solver.
    + have := lexpr_map_fvars_insert_subseteq (list_to_map (zip ks' vs')) k v.
      have := IH vs'.
      set_solver.
Qed.

(* Renaming lvar occurrences in a logical expression. Used to transport a
   derivation built against one fresh-lvar stack to any other, via a fixed
   injective ren that is required to be the identity on reserved names --
   see rename_assertion below and its accompanying invariants. *)
Fixpoint rename_lexpr (ren : lvar -> lvar) (e : LExpr) : LExpr :=
  match e with
  | LVar x => LVar (ren x)
  | LVal v => LVal v
  | LUnOp op e => LUnOp op (rename_lexpr ren e)
  | LBinOp op e1 e2 => LBinOp op (rename_lexpr ren e1) (rename_lexpr ren e2)
  | LIfE e1 e2 e3 => LIfE (rename_lexpr ren e1) (rename_lexpr ren e2) (rename_lexpr ren e3)
  | LStuck => LStuck
  end.

(* Renaming an LExpr's free lvars is exactly renaming its fvar set -- the
   fact the rename theorem's freshness-preservation lemmas reduce to. *)
Lemma lexpr_fvars_rename (ren : lvar -> lvar) (e : LExpr) :
  lexpr_fvars (rename_lexpr ren e) = set_map ren (lexpr_fvars e).
Proof.
  induction e; simpl; try set_solver.
Qed.

Definition symb_map : Type := lvar -> val.

Fixpoint interp_lexpr (le : LExpr) (mp : symb_map) : option val :=
  match le with
  | LVar x => Some (mp x)
  
  | LVal v => Some v

  | LUnOp op e =>
    match op with
    | NotBoolOp =>
      match interp_lexpr e mp with
      | Some (LitBool b) => Some (LitBool (negb b))
      | _ => None
      end
    | NegOp =>
      match interp_lexpr e mp with
      | Some (LitInt i) => Some (LitInt (-i))
      | _ => None
      end
    | RAValidOp =>
      match interp_lexpr e mp with
      | Some (LitRAElem (existT r x)) => Some (LitBool (bool_decide (valid x)))
      | _ => None
      end
    | RAOfIntOp r =>
      match interp_lexpr e mp with
      | Some (LitInt z) => Some (LitRAElem (existT r (ra_of_int z)))
      | _ => None
      end
    end
  
  | LBinOp op e1 e2 =>
    match op with
    | AddOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 + i2))
      | _, _ => None
      end

    | SubOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 - i2))
      | _, _ => None
      end

    | MulOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 * i2))
      | _, _ => None  
      end

    | DivOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 / i2))
      | _, _ => None
      end

    | ModOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitInt (i1 mod i2))
      | _, _ => None
      end

    | EqOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some v1, Some v2 => Some (LitBool (val_beq v1 v2))
      | _, _ => None
      end

    | NeOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some v1, Some v2 => Some (LitBool (negb (val_beq v1 v2)))
      | _, _ => None
      end

    | LtOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (Z.ltb i1 i2))
      | _, _ => None
      end

    | GtOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (Z.ltb i2 i1))
      | _, _ => None
      end

    | LeOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (Z.leb i1 i2))
      | _, _ => None
      end

    | GeOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitInt i1), Some (LitInt i2) => Some (LitBool (Z.leb i2 i1))
      | _, _ => None
      end

    | AndOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitBool b1), Some (LitBool b2) => Some (LitBool (b1 && b2))
      | _, _ => None
      end

    | OrOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitBool b1), Some (LitBool b2) => Some (LitBool (b1 || b2))
      | _, _ => None
      end

    | RACompOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitRAElem (existT r1 x1)), Some (LitRAElem (existT r2 x2)) =>
          match decide (r1 = r2) with
          | left Heq => Some (LitRAElem (existT r1 (comp x1 (eq_rect r2 (fun n => RA_carrier (ra_map n)) x2 r1 (eq_sym Heq)))))
          | right _ => None
          end
      | _, _ => None
      end

    | RAFrameOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitRAElem (existT r1 x1)), Some (LitRAElem (existT r2 x2)) =>
          match decide (r1 = r2) with
          | left Heq => Some (LitRAElem (existT r1 (frame x1 (eq_rect r2 (fun n => RA_carrier (ra_map n)) x2 r1 (eq_sym Heq)))))
          | right _ => None
          end
      | _, _ => None
      end

    | RAFpuValidOp =>
      match interp_lexpr e1 mp, interp_lexpr e2 mp with
      | Some (LitRAElem (existT r1 x1)), Some (LitRAElem (existT r2 x2)) =>
          match decide (r1 = r2) with
          | left Heq => Some (LitBool (bool_decide (fpuValid x1 (eq_rect r2 (fun n => RA_carrier (ra_map n)) x2 r1 (eq_sym Heq)))))
          | right _ => None
          end
      | _, _ => None
      end
    end

  | LIfE e1 e2 e3 =>
    match interp_lexpr e1 mp with
    | Some (LitBool true) => interp_lexpr e2 mp
    | Some (LitBool false) => interp_lexpr e3 mp
    | _ => None
    end 

  | LStuck => None
  end.

(* Interpreting a renamed LExpr under mp is the same as interpreting the
   original under mp precomposed with ren -- interp_lexpr only ever reads
   an lvar leaf through mp, and every other case is a function purely of
   its own recursive interp_lexpr sub-results (and, for LUnOp/LBinOp, the
   untouched operator), so rewriting those via IH closes it regardless of
   op, mirroring inf_lexpr_rename. *)
Lemma interp_lexpr_rename (ren : lvar -> lvar) (e : LExpr) (mp : symb_map) :
  interp_lexpr (rename_lexpr ren e) mp = interp_lexpr e (fun x => mp (ren x)).
Proof.
  induction e; simpl;
    try rewrite IHe; try rewrite IHe1; try rewrite IHe2; try rewrite IHe3;
    reflexivity.
Qed.

(* "Same RA" closed-form reductions of interp_lexpr's RA cases -- see
   un_op_eval_ra_valid/bin_op_eval_ra_* in lang.v for why UIP_dec is needed
   here rather than plain computation. *)
Lemma interp_lexpr_ra_valid (r : ra_name) (x : RA_carrier (ra_map r)) (e : LExpr) (mp : symb_map) :
  interp_lexpr e mp = Some (LitRAElem (existT r x)) ->
  interp_lexpr (LUnOp RAValidOp e) mp = Some (LitBool (bool_decide (valid x))).
Proof. intros H. simpl. rewrite H. reflexivity. Qed.

Lemma interp_lexpr_ra_comp (r : ra_name) (x1 x2 : RA_carrier (ra_map r)) (e1 e2 : LExpr) (mp : symb_map) :
  interp_lexpr e1 mp = Some (LitRAElem (existT r x1)) ->
  interp_lexpr e2 mp = Some (LitRAElem (existT r x2)) ->
  interp_lexpr (LBinOp RACompOp e1 e2) mp = Some (LitRAElem (existT r (comp x1 x2))).
Proof.
  intros H1 H2. simpl. rewrite H1 H2.
  destruct (decide (r = r)) as [Heq | Hne]; [ | exfalso; apply Hne; reflexivity].
  rewrite (Eqdep_dec.UIP_dec (fun a b => decide (a = b)) Heq eq_refl). reflexivity.
Qed.

Lemma interp_lexpr_ra_frame (r : ra_name) (x1 x2 : RA_carrier (ra_map r)) (e1 e2 : LExpr) (mp : symb_map) :
  interp_lexpr e1 mp = Some (LitRAElem (existT r x1)) ->
  interp_lexpr e2 mp = Some (LitRAElem (existT r x2)) ->
  interp_lexpr (LBinOp RAFrameOp e1 e2) mp = Some (LitRAElem (existT r (frame x1 x2))).
Proof.
  intros H1 H2. simpl. rewrite H1 H2.
  destruct (decide (r = r)) as [Heq | Hne]; [ | exfalso; apply Hne; reflexivity].
  rewrite (Eqdep_dec.UIP_dec (fun a b => decide (a = b)) Heq eq_refl). reflexivity.
Qed.

Lemma interp_lexpr_ra_fpuvalid (r : ra_name) (x1 x2 : RA_carrier (ra_map r)) (e1 e2 : LExpr) (mp : symb_map) :
  interp_lexpr e1 mp = Some (LitRAElem (existT r x1)) ->
  interp_lexpr e2 mp = Some (LitRAElem (existT r x2)) ->
  interp_lexpr (LBinOp RAFpuValidOp e1 e2) mp = Some (LitBool (bool_decide (fpuValid x1 x2))).
Proof.
  intros H1 H2. simpl. rewrite H1 H2.
  destruct (decide (r = r)) as [Heq | Hne]; [ | exfalso; apply Hne; reflexivity].
  rewrite (Eqdep_dec.UIP_dec (fun a b => decide (a = b)) Heq eq_refl). reflexivity.
Qed.

Definition LExpr_holds (le : LExpr) (mp : symb_map) : Prop :=
  match interp_lexpr le mp with
  | Some v => v = LitBool true
  | None => False
  end.

Lemma LExpr_holds_rename (ren : lvar -> lvar) (e : LExpr) (mp : symb_map) :
  LExpr_holds (rename_lexpr ren e) mp <-> LExpr_holds e (fun x => mp (ren x)).
Proof. unfold LExpr_holds. rewrite interp_lexpr_rename. reflexivity. Qed.

(* Reverse direction of interp_lexpr_ra_fpuvalid: given the LHS's evaluated
   value, extract the RHS's evaluated value (same ra_name, forced by
   RAFpuValidOp's own decide-based mismatch handling) and the underlying
   fpuValid fact, from the assertion-level RAFpuValidOp fact holding. *)
Lemma interp_lexpr_ra_fpuvalid_inv (r : ra_name) (x1 : RA_carrier (ra_map r)) (e1 e2 : LExpr) (mp : symb_map) :
  interp_lexpr e1 mp = Some (LitRAElem (existT r x1)) ->
  LExpr_holds (LBinOp RAFpuValidOp e1 e2) mp ->
  exists x2 : RA_carrier (ra_map r), interp_lexpr e2 mp = Some (LitRAElem (existT r x2)) /\ fpuValid x1 x2.
Proof.
  intros H1 Hholds.
  unfold LExpr_holds in Hholds. simpl in Hholds. rewrite H1 in Hholds.
  destruct (interp_lexpr e2 mp) as [[ | | | |[r2 x2]]|] eqn:He2; try contradiction.
  destruct (decide (r = r2)) as [<-|Hne]; [ | contradiction].
  exists x2. split; [reflexivity | ].
  injection Hholds as Hholds.
  apply bool_decide_eq_true in Hholds. exact Hholds.
Qed.

Definition trnsl_val (v: lang.val) : val :=
match v with
| lang.LitBool b => LitBool b
| lang.LitInt i => LitInt i
| lang.LitUnit => LitUnit
| lang.LitLoc l => LitLoc l
| lang.LitRAElem p => LitRAElem p
end.

Lemma trnsl_val_inj : forall v1 v2, trnsl_val v1 = trnsl_val v2 -> v1 = v2.
Proof.
  destruct v1, v2; simpl; try discriminate; intros H; inversion H; subst; auto.
Qed.

(* Updating a symb_map at v does not affect interp_lexpr when v ∉ lexpr_fvars e *)
Lemma interp_lexpr_stable (e : LExpr) (q : symb_map) (v : lvar) (v' : val) :
  v ∉ lexpr_fvars e →
  interp_lexpr e (fun y => if (y =? v)%string then v' else q y) = interp_lexpr e q.
Proof.
  induction e; simpl; intro H.
  - (* LVar x: need x ≠ v *)
    apply not_elem_of_singleton in H.
    destruct (String.eqb_spec x v) as [Heq | Hne].
    + exfalso. exact (H (eq_sym Heq)).
    + reflexivity.
  - (* LVal *) reflexivity.
  - (* LUnOp *) rewrite IHe; [reflexivity | exact H].
  - (* LBinOp *)
    rewrite IHe1; [| set_solver]. rewrite IHe2; [| set_solver]. reflexivity.
  - (* LIfE *)
    rewrite IHe1; [| set_solver].
    destruct (interp_lexpr e1 q); try reflexivity.
    destruct v0; try reflexivity.
    destruct b.
    + rewrite IHe2; [reflexivity | set_solver].
    + rewrite IHe3; [reflexivity | set_solver].
  - (* LStuck *) reflexivity.
Qed.

Fixpoint lexpr_subst (expr : LExpr) (subst_map : gmap var LExpr) :=
match expr with
| LVar x => match subst_map !! x with
    | None => LVar x
    | Some e => e
    end
| LVal v => LVal v
| LUnOp op e => LUnOp op (lexpr_subst e subst_map)
| LBinOp op e1 e2 => LBinOp op (lexpr_subst e1 subst_map) (lexpr_subst e2 subst_map)
| LIfE e1 e2 e3 => LIfE (lexpr_subst e1 subst_map) (lexpr_subst e2 subst_map) (lexpr_subst e3 subst_map)
| LStuck => LStuck
end.

(* Substituting v with a literal and interpreting under mp is the same as
   interpreting unsubstituted under mp updated at v -- the LExpr-level fact
   backing ExistsElimRule's soundness case. *)
Lemma interp_lexpr_subst_var (e : LExpr) (v : lvar) (v' : val) (mp : symb_map) :
  interp_lexpr (lexpr_subst e (<[v := LVal v']> ∅)) mp =
  interp_lexpr e (fun y => if (y =? v)%string then v' else mp y).
Proof.
  induction e; simpl.
  - (* LVar x *)
    destruct (String.eqb x v) eqn:Hxv.
    + apply String.eqb_eq in Hxv as ->. rewrite lookup_insert. reflexivity.
    + apply String.eqb_neq in Hxv.
      rewrite lookup_insert_ne; [ | congruence]. rewrite lookup_empty. reflexivity.
  - (* LVal *) reflexivity.
  - (* LUnOp *) rewrite IHe. reflexivity.
  - (* LBinOp *) rewrite IHe1 IHe2. reflexivity.
  - (* LIfE *) rewrite IHe1 IHe2 IHe3. reflexivity.
  - (* LStuck *) reflexivity.
Qed.

(* Same statement as interp_lexpr_subst_var, but substituting another lvar
   (its own current mp-value) rather than a fixed literal -- the LExpr-level
   fact backing "swap one already-bound lvar for another, given they're
   co-asserted equal" (see AE_LExpr_Subst_Eq_Congr). *)
Lemma interp_lexpr_subst_lvar (e : LExpr) (v v2 : lvar) (mp : symb_map) :
  interp_lexpr (lexpr_subst e (<[v := LVar v2]> ∅)) mp =
  interp_lexpr e (fun y => if (y =? v)%string then mp v2 else mp y).
Proof.
  induction e; simpl.
  - (* LVar x *)
    destruct (String.eqb x v) eqn:Hxv.
    + apply String.eqb_eq in Hxv as ->. rewrite lookup_insert. reflexivity.
    + apply String.eqb_neq in Hxv.
      rewrite lookup_insert_ne; [ | congruence]. rewrite lookup_empty. reflexivity.
  - (* LVal *) reflexivity.
  - (* LUnOp *) rewrite IHe. reflexivity.
  - (* LBinOp *) rewrite IHe1 IHe2. reflexivity.
  - (* LIfE *) rewrite IHe1 IHe2 IHe3. reflexivity.
  - (* LStuck *) reflexivity.
Qed.

(* Renaming after substituting a single lvar for e0 agrees with substituting
   the renamed lvar for the renamed e0, unconditionally -- unlike
   lexpr_subst_rename (which needs every other free lvar routed through
   dom M or reserved), here M's *key* lv is itself in ren's own domain, so
   both branches of the LVar case go through injectivity alone: x = lv iff
   ren x = ren lv, and the substitution is a no-op identically on both
   sides otherwise. Used by the assertion_entails rules that rebind one
   already-ambient lvar for another (AE_Exists_ValIntro, AE_Exists_Rename_Intro,
   AE_LExpr_Subst_Eq_Congr), as opposed to substituting a program's own
   fixed argument names. *)
Lemma lexpr_subst_singleton_rename (ren : lvar -> lvar) (Hinj : Inj (=) (=) ren)
    (e : LExpr) (lv : lvar) (e0 : LExpr) :
  rename_lexpr ren (lexpr_subst e (<[lv := e0]> ∅)) =
  lexpr_subst (rename_lexpr ren e) (<[ren lv := rename_lexpr ren e0]> ∅).
Proof.
  induction e; simpl.
  - (* LVar x *)
    destruct (String.eqb_spec x lv) as [-> | Hne].
    + rewrite lookup_insert. simpl. rewrite lookup_insert. reflexivity.
    + rewrite lookup_insert_ne; [| congruence]. rewrite lookup_empty. simpl.
      rewrite lookup_insert_ne; [| intros Heq; exact (Hne (Hinj _ _ (eq_sym Heq)))].
      rewrite lookup_empty. reflexivity.
  - (* LVal *) reflexivity.
  - (* LUnOp *) f_equal. exact IHe.
  - (* LBinOp *) f_equal; [exact IHe1 | exact IHe2].
  - (* LIfE *) f_equal; [exact IHe1 | exact IHe2 | exact IHe3].
  - (* LStuck *) reflexivity.
Qed.

(* List-of-args specialization, for LInv/LPred's own argument lists. *)
Lemma map_lexpr_subst_singleton_rename (ren : lvar -> lvar) (Hinj : Inj (=) (=) ren)
    (args : list LExpr) (lv : lvar) (e0 : LExpr) :
  map (rename_lexpr ren) (map (fun e => lexpr_subst e (<[lv := e0]> ∅)) args) =
  map (fun e => lexpr_subst e (<[ren lv := rename_lexpr ren e0]> ∅)) (map (rename_lexpr ren) args).
Proof.
  induction args as [| a args IH]; simpl; [reflexivity |].
  f_equal.
  - apply lexpr_subst_singleton_rename. exact Hinj.
  - exact IH.
Qed.

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

Global Instance LExpr_Eq : EqDecision LExpr.
Proof. solve_decision. Qed.

Global Instance LExpr_Countable : Countable LExpr.
Proof.
  (* lvar + val + un_op + bin_op is left-associative:
     = ((lvar + val) + un_op) + bin_op
     lvar x   ↦ inl (inl (inl x))
     val v    ↦ inl (inl (inr v))
     un_op op ↦ inl (inr op)
     bin_op op ↦ inr op *)
  set (enc := fix enc (e : LExpr) : gen_tree (lvar + val + un_op + bin_op) :=
    match e with
    | LVar x          => GenLeaf (inl (inl (inl x)))
    | LVal v          => GenLeaf (inl (inl (inr v)))
    | LUnOp op e      => GenNode 0 [GenLeaf (inl (inr op)); enc e]
    | LBinOp op e1 e2 => GenNode 1 [GenLeaf (inr op); enc e1; enc e2]
    | LIfE e1 e2 e3   => GenNode 2 [enc e1; enc e2; enc e3]
    | LStuck          => GenNode 3 []
    end).
  set (dec := fix dec (t : gen_tree (lvar + val + un_op + bin_op)) : option LExpr :=
    match t with
    | GenLeaf (inl (inl (inl x)))             => Some (LVar x)
    | GenLeaf (inl (inl (inr v)))             => Some (LVal v)
    | GenNode 0 [GenLeaf (inl (inr op)); t']  =>
        match dec t' with
        | Some e' => Some (LUnOp op e')
        | None    => None
        end
    | GenNode 1 [GenLeaf (inr op); t1; t2]   =>
        match dec t1 with
        | Some e1 => match dec t2 with
                     | Some e2 => Some (LBinOp op e1 e2)
                     | None    => None
                     end
        | None    => None
        end
    | GenNode 2 [t1; t2; t3]                 =>
        match dec t1 with
        | Some e1 => match dec t2 with
                     | Some e2 => match dec t3 with
                                  | Some e3 => Some (LIfE e1 e2 e3)
                                  | None    => None
                                  end
                     | None    => None
                     end
        | None    => None
        end
    | GenNode 3 []                            => Some LStuck
    | _                                       => None
    end).
  refine (inj_countable enc dec _).
  intro e; induction e; simpl; try done.
  - rewrite IHe. done.
  - rewrite IHe1; rewrite IHe2. done.
  - rewrite IHe1; rewrite IHe2; rewrite IHe3. done.
Qed.

(* Ghost state backing [LInv]: an invariant assertion is a *nominal* fact, a
   fragment recording that the invariant was established at a concrete argument
   vector.  The carrier is discrete (a plain gset of value lists), so the
   fragment is Timeless -- which is what lets an invariant be opened without a
   later (see [Winv_open] below). *)
Definition inv_argsUR : ucmra := gsetUR (list val).

Class invTokenG (Σ : gFunctors) := InvTokenG {
  invtoken_inG :: inG Σ (authR inv_argsUR);
  invtoken_names : inv_name -> gname;
}.

(* Layer 0: the camera capability invTokenG needs, without the concrete
   invtoken_names assignment --
   mirrors ghost_state.v's own heapGpreS/heapG split (invTokenG bundles a
   concrete gname-valued function together with the inG evidence, so a
   full invTokenG instance can't be derived from subG alone; only this
   "pre" half can. Producing invtoken_names itself is own_alloc work,
   done once per invariant name a program actually declares -- belongs to
   the adequacy wrapper, not here). *)
Class invTokenGpreS (Σ : gFunctors) := InvTokenGpreS {
  invtoken_pre_inG :: inG Σ (authR inv_argsUR);
}.

Definition invTokenGΣ : gFunctors := #[ GFunctor (authR inv_argsUR) ].

Global Instance subG_invTokenGpreS Σ' : subG invTokenGΣ Σ' → invTokenGpreS Σ'.
Proof. solve_inG. Qed.

(* Combined Layer 0 capability list: everything a caller of the adequacy
   wrapper (raven_soundness, trnsl.v)
   needs from a single subG hypothesis to build the instances its own
   Context expects -- except inGs Σ Gs (inherently RA/program-specific,
   picked per the one ra_name being verified, not a fixed capability) and
   simpLangG itself (bundles concrete gnames, not just inG evidence, so it
   needs own_alloc/wp_adequacy work a caller does separately -- heapGΣ and
   invΣ below only cover the "pre" half of what building one requires).
   subG's own transitivity through gFunctors append (#[...]) lets
   subG_heapGpreS/subG_invTokenGpreS/subG_ghostHeapInG (this file) and
   Iris's own subG_invΣ each fire straight off "subG ravenΣ Σ'" via
   solve_inG, without restating any of them here -- checked directly below,
   not just assumed, since invGpreS (unlike the other three) needed an
   explicit "apply subG_invΣ" first: solve_inG alone doesn't chase through
   invΣ's own name to find it. *)
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

Context `{!invTokenG Σ}.

Definition pvar_typs : Type := var -> typ.
Definition lvar_typs : Type := lvar -> typ.

Inductive stmt :=
| Seq (s1 s2 : stmt)
(* | Return (e : lang.expr) *)
| IfS (e : lang.expr) (s1 s2 : stmt)
| Assign (v : lang.var) (e : lang.expr)
(* | Free (e : lang.expr) *)
| SkipS
| StuckS (* stuck statement *)
(* | ExprS (e : lang.expr) *)
| Call (v : lang.var) (proc : proc_name) (args : list lang.expr)
| FldWr (v : lang.var) (fld : fld_name) (e2 : lang.expr)
| FldRd (v : lang.var) (e : lang.expr) (fld : fld_name)
| CAS (v : lang.var) (e1 : lang.expr) (fld : fld_name) (e2 : lang.expr) (e3 : lang.expr)
| Alloc (v : lang.var) (fs: list (lang.fld_name * lang.val))
| Spawn (proc : proc_name) (args : list lang.expr)
| UnfoldPred (pred : pred_name) (args : list lang.expr)
| FoldPred (pred : pred_name) (args : list lang.expr)
| InvAccessBlock (inv: inv_name) (args : list lang.expr) (body : stmt)
(* Establishing an invariant.  Deliberately one-directional: once shared, an
   invariant stays shared (as with Iris's own inv_alloc), so there is no
   matching unfold/deallocate form. *)
| FoldInv (inv: inv_name) (args : list lang.expr)
(* A proof-only check: asserts e holds against the current assertion state
   and otherwise has no effect (no physical step, no ghost update) --
   ghost-only, like FoldPred/FoldInv/Fpu. GhostSkip -- a "do nothing" branch
   filler, needed e.g. when only one arm of an IfS inside an atomic block is
   a real step -- is Assert (Val (LitBool true)): the assert condition is
   trivially provable, so it behaves exactly like SkipS but, unlike SkipS,
   costs no physical step (see counter_monotonic.v's incr_body). Also the
   Coq-level counterpart of the real tool's own generated assert statements
   (atomicityAnalysis.ml's open_inv/call_reentrancy_asserts), should a
   later pass want to formalize those. *)
| Assert (e : lang.expr)
(* old_val/new_val are lang.expr (not concrete RA_carrier values), mirroring
   CAS's e2/e3 -- a real program expression, e.g. Var g or
   BinOp RACompOp (Var g1) (Var g2), evaluated against the real stack frame
   like any other value. See FPURule, which mirrors CASSuccRule exactly. *)
| Fpu (e : lang.expr) (fld : fld_name) (r : ra_name) (old_val new_val : lang.expr)
.

Inductive assertion :=
| LProc (proc_name : proc_name) (proc_entry : ProcRecord)
| LStack (σ : gmap lang.var lvar)
| LExprA (p: LExpr)
| LPure (p : Prop)
| LOwn (e: LExpr) (fld: fld_name) (chunk: LExpr)
| LGhostOwn (e: LExpr) (fld: fld_name) (r : ra_name) (chunk: LExpr)
| LForall (v : var) (t : typ) (body : assertion)
| LExists (v : var) (t : typ) (body : assertion)
| LIte (cond : LExpr) (then_ else_ : assertion)
| LInv (inv_name : inv_name) (args : list LExpr)
| LPred (pred_name : pred_name) (args : list LExpr)
| LAnd (assert1 : assertion) (assert2 : assertion)

with ProcRecord := | Proc 
  (proc_args: list (var * typ))
  (proc_local_vars: list (var * typ))
  (proc_precond : assertion)
  (proc_postcond : assertion)
  (body : stmt).

Definition proc_args_of (p : ProcRecord) :=
  match p with Proc args _ _ _ _ => args end.

Definition proc_locals_of (p : ProcRecord) :=
  match p with Proc _ locs _ _ _ => locs end.

Definition proc_precond_of (p : ProcRecord) :=
  match p with Proc _ _ pre _ _ => pre end.

Definition proc_postcond_of (p : ProcRecord) :=
  match p with Proc _ _ _ post _ => post end.

Definition proc_body_of (p : ProcRecord) :=
  match p with Proc _ _ _ _ body => body end.

(* Syntactic sugar: an implication is an if-then-else with a trivially-true
   else branch. *)
Definition LImpl (cond : LExpr) (body : assertion) : assertion :=
  LIte cond body (LPure True).

Fixpoint subst (ra: assertion) (mp: gmap var LExpr) : assertion := match ra with
| LProc p p_e => LProc p p_e
| LStack σ => LStack σ
| LExprA e => LExprA (lexpr_subst e mp)
| LPure p => LPure p
| LOwn e fld chunk => LOwn (lexpr_subst e mp) fld (lexpr_subst chunk mp)
| LGhostOwn e fld RAPack chunk => LGhostOwn (lexpr_subst e mp) fld RAPack (lexpr_subst chunk mp)
| LForall vars t body => LForall vars t (subst body mp)
| LExists vars t body => LExists vars t (subst body mp)
| LIte cond then_ else_ => LIte (lexpr_subst cond mp) (subst then_ mp) (subst else_ mp)
| LInv inv_name args => 
    LInv inv_name (map (fun expr => lexpr_subst expr mp) args)
| LPred pred_name args =>
    LPred pred_name (map (fun expr => lexpr_subst expr mp) args)
| LAnd a1 a2 => LAnd (subst a1 mp) (subst a2 mp)
end.

(* Renaming lvar occurrences throughout an assertion via a fixed injective
   ren : lvar -> lvar that is required to be the identity on reserved names
   (see RavenHoareTriple_rename below). Applied unconditionally to LExists's
   own binder: despite being typed var (= lvar as strings), that binder is
   sometimes a genuine reserved witness (untouched, since ren is identity
   there, per pwf_*_binders_reserved) and sometimes a fresh lvar minted
   during a derivation (renamed, same as any other occurrence) -- the two
   cases need no separate treatment because ren's own required
   identity-on-reserved property already tells them apart. LForall's own
   binder is left untouched (unlike LExists): assertion_exists_binders
   deliberately does not track it, so there is no invariant forcing it to
   be reserved, and no RavenHoareTriple rule ever mints a fresh lvar via
   LForall (only via LExists) -- it is also unused by every contract in
   this development, so this choice is never exercised in practice. *)
Fixpoint rename_assertion (ren : lvar -> lvar) (ra : assertion) : assertion := match ra with
| LProc p p_e => LProc p p_e
| LStack σ => LStack (ren <$> σ)
| LExprA e => LExprA (rename_lexpr ren e)
| LPure p => LPure p
| LOwn e fld chunk => LOwn (rename_lexpr ren e) fld (rename_lexpr ren chunk)
| LGhostOwn e fld RAPack chunk => LGhostOwn (rename_lexpr ren e) fld RAPack (rename_lexpr ren chunk)
| LForall v t body => LForall v t (rename_assertion ren body)
| LExists v t body => LExists (ren v) t (rename_assertion ren body)
| LIte cond then_ else_ => LIte (rename_lexpr ren cond) (rename_assertion ren then_) (rename_assertion ren else_)
| LInv inv_name args =>
    LInv inv_name (map (fun expr => rename_lexpr ren expr) args)
| LPred pred_name args =>
    LPred pred_name (map (fun expr => rename_lexpr ren expr) args)
| LAnd a1 a2 => LAnd (rename_assertion ren a1) (rename_assertion ren a2)
end.

(* Assertion-level counterpart of lexpr_subst_singleton_rename: subst never
   touches an assertion's own LForall/LExists binder regardless of whether
   it coincides with the key being substituted (see lvar_fresh_in_assertion's
   own comment on this "naive substitution" design), so both sides of the
   equation recurse into the binder's body identically -- no reserved-namespace
   or dom-M side condition is needed at all, unlike rename_assertion_subst_commute. *)
Lemma rename_assertion_subst_singleton (ren : lvar -> lvar) (Hinj : Inj (=) (=) ren)
    (a : assertion) (lv : lvar) (e0 : LExpr) :
  rename_assertion ren (subst a (<[lv := e0]> ∅)) =
  subst (rename_assertion ren a) (<[ren lv := rename_lexpr ren e0]> ∅).
Proof.
  induction a; simpl.
  - (* LProc *) reflexivity.
  - (* LStack *) reflexivity.
  - (* LExprA *) f_equal. apply lexpr_subst_singleton_rename. exact Hinj.
  - (* LPure *) reflexivity.
  - (* LOwn *)
    f_equal; apply lexpr_subst_singleton_rename; exact Hinj.
  - (* LGhostOwn *)
    f_equal; apply lexpr_subst_singleton_rename; exact Hinj.
  - (* LForall *) f_equal. exact IHa.
  - (* LExists *) f_equal. exact IHa.
  - (* LIte *)
    f_equal; [apply lexpr_subst_singleton_rename; exact Hinj | exact IHa1 | exact IHa2].
  - (* LInv *) f_equal. apply map_lexpr_subst_singleton_rename. exact Hinj.
  - (* LPred *) f_equal. apply map_lexpr_subst_singleton_rename. exact Hinj.
  - (* LAnd *) f_equal; [exact IHa1 | exact IHa2].
Qed.

(* LExists binder variables of an assertion (does NOT descend into LInv/LPred bodies).
   Sits ahead of InvRecord/PredRecord/ProcRecord's own well-formedness
   definitions (InvBodyWF etc. below) so they can state their own "## dom M"
   premise in terms of it. *)
Fixpoint assertion_exists_binders (a : assertion) : gset lvar :=
  match a with
  | LExists v _ body => {[v]} ∪ assertion_exists_binders body
  | LForall _ _ body => assertion_exists_binders body
  | LIte _ then_ else_ => assertion_exists_binders then_ ∪ assertion_exists_binders else_
  | LAnd a1 a2 => assertion_exists_binders a1 ∪ assertion_exists_binders a2
  | _ => ∅
  end.

(* Builds an association gmap out of a key list zipped positionally against
   a value list -- the one low-level pattern every symbolic stack (var ->
   lvar), stack frame (var -> val / lvar -> val), and substitution map
   below ultimately reduces to. *)
Definition assoc_map `{Countable K} {V : Type} (ks : list K) (vs : list V) : gmap K V :=
  list_to_map (zip ks vs).

(* The two recurring shapes of substitution map built out of a name list
   paired positionally with either lvars (symbolic, used in preconditions
   naming the entry lvars of a fresh call frame) or concrete values
   (ghost/logical, used when the map is meant to evaluate away): factors
   out the zip/list_to_map/map boilerplate at every subst call site that
   builds one from a procedure's, invariant's, or predicate's argument
   names. *)
Definition lvar_subst_map (names : list var) (lvs : list lvar) : gmap var LExpr :=
  assoc_map names (map LVar lvs).
Definition val_subst_map (names : list var) (vals : list lang.val) : gmap var LExpr :=
  assoc_map names (map (fun v => LVal (trnsl_val v)) vals).

(* Mapping f over a zip-built assoc map's values is the same as mapping it
   over the value list before zipping -- needed to show a proc/inv/pred's
   own subst_map, rebuilt from a renamed lexprs list, is exactly the
   renamed original subst_map (rename_lexpr ren <$> list_to_map (zip ks lexprs)). *)
Lemma fmap_list_to_map_zip {K} `{Countable K} {V : Type} (f : V -> V) (ks : list K) (vs : list V) :
  f <$> (list_to_map (zip ks vs) : gmap K V) = list_to_map (zip ks (map f vs)).
Proof.
  revert vs. induction ks as [| k ks IH]; intros vs; simpl.
  - rewrite fmap_empty. reflexivity.
  - destruct vs as [| v vs]; simpl.
    + rewrite fmap_empty. reflexivity.
    + rewrite fmap_insert. rewrite IH. reflexivity.
Qed.

(* dom of a zip-built assoc map from equal-length key/value lists is
   exactly the key set -- lets a pwf_*_fvars_bounded fact (stated in terms
   of the formal argument names) be rephrased in terms of dom subst_map. *)
Lemma dom_list_to_map_zip_eq_len {K} `{Countable K} {V : Type} (ks : list K) (vs : list V) :
  length ks = length vs → dom (list_to_map (zip ks vs) : gmap K V) = list_to_set ks.
Proof.
  revert vs. induction ks as [| k ks IH]; intros vs Hlen; destruct vs; simpl in *;
    try discriminate.
  - reflexivity.
  - rewrite dom_insert_L. rewrite IH; [reflexivity | congruence].
Qed.

Record InvRecord := Inv {
  inv_args: list var;
  inv_body: assertion;
}.

(* Well-formedness: the body only references its formal argument variables
   (mod its own internal binders, see assertion_exists_binders r.(inv_body)
   ## dom M below), so substitution commutes with argument substitution.
   The "## dom M" premise is what a naively-unconditional version of this
   fact would need to hold for *any* M, which is unsatisfiable whenever
   inv_body has a genuine internal existential (e.g. an Auth-style ghost
   witness). Discharged via the record's own
   binders being drawn from the reserved namespace (ProgramWF's
   pwf_inv_binders_reserved) together with M avoiding it, not by M being
   unconstrained. *)
Definition InvBodyWF (r : InvRecord) : Prop :=
  forall (args : list LExpr) (M : gmap var LExpr),
    length args = length r.(inv_args) →
    assertion_exists_binders r.(inv_body) ## dom M →
    subst (r.(inv_body))
      (list_to_map (zip (r.(inv_args)) (map (fun e => lexpr_subst e M) args))) =
    subst (subst (r.(inv_body))
      (list_to_map (zip (r.(inv_args)) args))) M.

Record PredRecord := Pred {
  pred_args: list var;
  pred_body: assertion;
}.

(* Well-formedness: analogous condition for predicate bodies, with the
   same "## dom M" premise as InvBodyWF and for the same reason. *)
Definition PredBodyWF (r : PredRecord) : Prop :=
  forall (args : list LExpr) (M : gmap var LExpr),
    length args = length r.(pred_args) →
    assertion_exists_binders r.(pred_body) ## dom M →
    subst (r.(pred_body))
      (list_to_map (zip (r.(pred_args)) (map (fun e => lexpr_subst e M) args))) =
    subst (subst (r.(pred_body))
      (list_to_map (zip (r.(pred_args)) args))) M.

(* The elaborated module, bundled. Positioned here (not right after
   proc_set/etc. above): ProcRecord/InvRecord/PredRecord all need to
   already exist, and StackFree below needs inv_map/pred_map ambient, so
   this is the earliest point everything lines up. Not ra_map/ra_set --
   those stay Global Parameter in lang.v. *)
Record Program := {
  prog_proc_set : gset proc_name;
  prog_pred_set : gset pred_name;
  prog_inv_set : gset inv_name;
  prog_fld_set : gset lang.fld_name;
  prog_proc_map : gmap proc_name ProcRecord;
  prog_inv_map : gmap inv_name InvRecord;
  prog_pred_map : gmap pred_name PredRecord;
}.

Context {P : Program}.

Let proc_set := P.(prog_proc_set).
Let pred_set := P.(prog_pred_set).
Let inv_set := P.(prog_inv_set).
Let fld_set := P.(prog_fld_set).
Let proc_map := P.(prog_proc_map).
Let inv_map := P.(prog_inv_map).
Let pred_map := P.(prog_pred_map).

Inductive StackFree : assertion → Prop :=
| SF_Proc proc_name proc_entry :
    StackFree (LProc proc_name proc_entry)
| SF_Expr p :
    StackFree (LExprA p)
| SF_Pure p :
    StackFree (LPure p)
| SF_Own e fld chunk :
    StackFree (LOwn e fld chunk)
| SF_GhostOwn e fld RAPAck chunk :
    StackFree (LGhostOwn e fld RAPAck chunk)
| SF_Forall v t body :
    StackFree body →
    StackFree (LForall v t body)
| SF_Exists v t body :
    StackFree body →
    StackFree (LExists v t body)
| SF_Ite cond then_ else_ :
    StackFree then_ →
    StackFree else_ →
    StackFree (LIte cond then_ else_)
| SF_And a1 a2 :
    StackFree a1 →
    StackFree a2 →
    StackFree (LAnd a1 a2)
| SF_Inv inv_name args inv_record :
    inv_map !! inv_name = Some inv_record →
    length args = length inv_record.(inv_args) →
    StackFree (subst (inv_record.(inv_body)) (list_to_map (zip inv_record.(inv_args) args))) →
    StackFree (LInv inv_name args)
| SF_Pred pred_name args pred_record :
    pred_map !! pred_name = Some pred_record →
    length args = length pred_record.(pred_args) →
    StackFree (subst (pred_record.(pred_body)) (list_to_map (zip pred_record.(pred_args) args))) →
    StackFree (LPred pred_name args).

(* Per-(typ,val) compatibility check -- factored out of env_typ_well_defined
   so it can be used standalone by LExists/LForall's own translation
   (restricting the witness/domain to values matching the binder's declared
   type) as well as by env_typ_well_defined itself. Moved ahead of Section
   Translation (from its earlier home right after env_typ_well_defined) so
   trnsl_assertion_str's LExists/LForall cases can use it. *)
Definition typ_val_match (t : typ) (v : val) : Prop :=
  match t, v with
  | TpBool, LitBool _ => True
  | TpInt, LitInt _ => True
  | TpLoc, LitLoc _ => True
  | TpUnit, LitUnit => True
  | TpRA r, LitRAElem (existT r' _) => r = r'
  | _, _ => False
  end.

(* Whether lvar v can influence a's translation under any mp -- i.e. whether
   overriding mp at v is guaranteed to be a no-op for a's meaning. Unlike
   elim_safe's subst-based predecessor this covers LStack too: symb_stk_to_stk_frm
   reads its whole gmap, so freshness there means v never appears as one of
   the stack's *values* (fresh_lvar's own condition), not that v is merely
   absent from some LExpr leaf. LInv only needs v absent from its own arg
   vector -- it's a leaf (never interprets its stored inv_body). LPred is
   excluded outright: it's semantically the same "v absent from its args"
   condition, but its recursion goes through the *global* pred_map table
   rather than a structural subterm of a, so trnsl_assertion_mp_irrelevant's
   plain induction on a can't produce an induction hypothesis for it. LExists's
   own binder can shadow v (a self-shadowed occurrence, e.g. an invariant body
   quantifying over the same lvar name as the ExistsElimRule instance being
   applied to it, never reads the outer mp update at all -- see the ev =? v
   branch of trnsl_assertion_mp_irrelevant's LExists case), so that case is a
   disjunction rather than an unconditional recursion into body. *)
Fixpoint lvar_fresh_in_assertion (v : lvar) (a : assertion) : Prop :=
  match a with
  | LProc _ _ => True
  | LStack σ => forall v0, σ !! v0 ≠ Some v
  | LExprA e => v ∉ lexpr_fvars e
  | LPure _ => True
  | LOwn e _ chunk => v ∉ lexpr_fvars e /\ v ∉ lexpr_fvars chunk
  | LGhostOwn e _ _ chunk => v ∉ lexpr_fvars e /\ v ∉ lexpr_fvars chunk
  | LForall _ _ body => lvar_fresh_in_assertion v body
  | LExists ev _ body => ev = v \/ lvar_fresh_in_assertion v body
  | LIte cond then_ else_ => v ∉ lexpr_fvars cond /\ lvar_fresh_in_assertion v then_ /\ lvar_fresh_in_assertion v else_
  | LInv _ args => Forall (fun e => v ∉ lexpr_fvars e) args
  | LPred _ _ => False
  | LAnd a1 a2 => lvar_fresh_in_assertion v a1 /\ lvar_fresh_in_assertion v a2
  end.

(* Freshness of a renamed lvar in a renamed assertion, given freshness of
   the original -- needed for the assertion_entails rules whose side
   condition is exactly this (AE_Exists_Elim/AE_Exists_And_Swap_R/
   AE_And_Exists_Swap_L). The LExists case works uniformly whether or not
   the assertion's own binder ev happens to equal v: rename_assertion always
   applies ren to it, and injectivity turns "ev = v" into "ren ev = ren v"
   and vice versa. LPred is immediate since lvar_fresh_in_assertion is
   simply False there on both sides. *)
Lemma lvar_fresh_in_assertion_rename (ren : lvar -> lvar) (Hinj : Inj (=) (=) ren)
    (v : lvar) (a : assertion) :
  lvar_fresh_in_assertion v a → lvar_fresh_in_assertion (ren v) (rename_assertion ren a).
Proof.
  induction a; simpl; intro Hfresh.
  - (* LProc *) exact Logic.I.
  - (* LStack *) intros v0 Heq.
    apply lookup_fmap_Some in Heq as [lv0 [Heq0 Hlv0]].
    apply Hinj in Heq0. subst lv0. exact (Hfresh v0 Hlv0).
  - (* LExprA *) rewrite lexpr_fvars_rename. intro Hc.
    apply elem_of_map in Hc as [y [Heqy Hy]]. apply Hinj in Heqy. subst y. exact (Hfresh Hy).
  - (* LPure *) exact Logic.I.
  - (* LOwn *) destruct Hfresh as [Hfe Hfc]. split.
    + rewrite lexpr_fvars_rename. intro Hc.
      apply elem_of_map in Hc as [y [Heqy Hy]]. apply Hinj in Heqy. subst y. exact (Hfe Hy).
    + rewrite lexpr_fvars_rename. intro Hc.
      apply elem_of_map in Hc as [y [Heqy Hy]]. apply Hinj in Heqy. subst y. exact (Hfc Hy).
  - (* LGhostOwn *) destruct Hfresh as [Hfe Hfc]. split.
    + rewrite lexpr_fvars_rename. intro Hc.
      apply elem_of_map in Hc as [y [Heqy Hy]]. apply Hinj in Heqy. subst y. exact (Hfe Hy).
    + rewrite lexpr_fvars_rename. intro Hc.
      apply elem_of_map in Hc as [y [Heqy Hy]]. apply Hinj in Heqy. subst y. exact (Hfc Hy).
  - (* LForall *) exact (IHa Hfresh).
  - (* LExists ev _ body *) destruct Hfresh as [-> | Hfresh].
    + left. reflexivity.
    + right. exact (IHa Hfresh).
  - (* LIte *) destruct Hfresh as [Hfc [Hft Hfe]]. split; [| split].
    + rewrite lexpr_fvars_rename. intro Hc.
      apply elem_of_map in Hc as [y [Heqy Hy]]. apply Hinj in Heqy. subst y. exact (Hfc Hy).
    + exact (IHa1 Hft).
    + exact (IHa2 Hfe).
  - (* LInv *) apply Forall_forall. intros x Hx.
    apply elem_of_list_fmap in Hx as [y [-> Hy]].
    rewrite lexpr_fvars_rename. intro Hc.
    apply elem_of_map in Hc as [z [Heqz Hz]]. apply Hinj in Heqz. subst z.
    exact (proj1 (Forall_forall _ _) Hfresh y Hy Hz).
  - (* LPred *) exact Hfresh.
  - (* LAnd *) destruct Hfresh as [Hf1 Hf2]. split; [exact (IHa1 Hf1) | exact (IHa2 Hf2)].
Qed.

(* Free variables appearing in LExpr nodes of an assertion (does NOT descend into LInv/LPred bodies) *)
Fixpoint assertion_lexpr_fvars (a : assertion) : gset lvar :=
  match a with
  | LExprA e => lexpr_fvars e
  | LOwn e _ chunk => lexpr_fvars e ∪ lexpr_fvars chunk
  | LGhostOwn e _ _ chunk => lexpr_fvars e ∪ lexpr_fvars chunk
  | LForall _ _ body => assertion_lexpr_fvars body
  | LExists _ _ body => assertion_lexpr_fvars body
  | LIte cond then_ else_ => lexpr_fvars cond ∪ assertion_lexpr_fvars then_ ∪ assertion_lexpr_fvars else_
  | LInv _ args => ⋃ (lexpr_fvars <$> args)
  | LPred _ args => ⋃ (lexpr_fvars <$> args)
  | LAnd a1 a2 => assertion_lexpr_fvars a1 ∪ assertion_lexpr_fvars a2
  | _ => ∅
  end.

(* The invariant names a bare, syntactic LInv fact in an assertion
   mentions -- does NOT unfold into an invariant's own body (mirrors
   assertion_lexpr_fvars's own "does not descend into LInv/LPred bodies"
   convention), since a procedure can only ever open an invariant it
   already holds a bare LInv fact for, never one buried inside some other
   invariant/predicate's unfolded contents. Used by proc_required_mask
   below to compute the minimum mask a procedure's own call sites must
   supply -- see its own comment. *)
Fixpoint assertion_inv_names (a : assertion) : gset inv_name :=
  match a with
  | LInv inv_nm _ => {[inv_nm]}
  | LForall _ _ body => assertion_inv_names body
  | LExists _ _ body => assertion_inv_names body
  | LIte _ then_ else_ => assertion_inv_names then_ ∪ assertion_inv_names else_
  | LAnd a1 a2 => assertion_inv_names a1 ∪ assertion_inv_names a2
  | _ => ∅
  end.

(* A procedure's own required mask: the invariants it must already hold
   (as a bare LInv fact) in its own
   precondition, and hence the invariants any RavenHoareTriple derivation
   for its body might need to open via InvAccessBlockRule. Mirrors the
   standard Iris pattern for a spec that internally opens an invariant N
   (∀ E, ↑N ⊆ E → {{{P}}} e @ E {{{Q}}}, rather than claiming the triple
   for every E unconditionally) -- all_proc_specs_valid_raven/_iris and
   ProcCallRuleRet use this as the side condition on their own mask
   quantifier/premise, replacing an unconditional ∀ msk that was actually
   unsatisfiable for any procedure that opens an invariant at all (no rule
   changes mask, so a derivation that needs "counterInv" ∈ mask can never
   be transported down to a mask lacking it). Restricted to the
   precondition alone (not the whole body): the body could only ever
   reach an invariant it already named up front, since InvAccessBlockRule
   never manufactures a fresh LInv fact out of nothing. *)
Definition proc_required_mask (proc_record : ProcRecord) : gset inv_name :=
  assertion_inv_names (proc_precond_of proc_record).

(* Scope-correct free variables: unlike assertion_lexpr_fvars, this
   subtracts LExists's own bound variable from its body's fvars, so it
   never over-approximates through a genuine existential.
   assertion_lexpr_fvars deliberately over-approximates instead, since the
   reserved-namespace design tolerates it; this function is the accurate
   version needed where that tolerance isn't good enough, namely
   trnsl_assertion_mp_irrelevant_reserved below).
   LForall's bound variable is *not* subtracted, matching
   assertion_exists_binders and trnsl_assertion_forall: LForall's binder is
   inert in the translation (trnsl_assertion_forall never updates mp), so a
   leaf mention of it inside body is genuinely read from the ambient mp,
   not shadowed. *)
Fixpoint assertion_true_fvars (a : assertion) : gset lvar :=
  match a with
  | LExprA e => lexpr_fvars e
  | LOwn e _ chunk => lexpr_fvars e ∪ lexpr_fvars chunk
  | LGhostOwn e _ _ chunk => lexpr_fvars e ∪ lexpr_fvars chunk
  | LForall _ _ body => assertion_true_fvars body
  | LExists v _ body => assertion_true_fvars body ∖ {[v]}
  | LIte cond then_ else_ => lexpr_fvars cond ∪ assertion_true_fvars then_ ∪ assertion_true_fvars else_
  | LInv _ args => ⋃ (lexpr_fvars <$> args)
  | LPred _ args => ⋃ (lexpr_fvars <$> args)
  | LAnd a1 a2 => assertion_true_fvars a1 ∪ assertion_true_fvars a2
  | _ => ∅
  end.

(* assertion_true_fvars only ever removes names assertion_lexpr_fvars
   would keep (the LExists case), never adds any -- so it's always a
   subset. *)
Lemma assertion_true_fvars_subseteq_lexpr_fvars (a : assertion) :
  assertion_true_fvars a ⊆ assertion_lexpr_fvars a.
Proof.
  induction a; simpl; try set_solver.
Qed.

(* Every fvar surviving a substitution either traces back to an
   unsubstituted original fvar or came in through some substituted
   expression's own fvars -- an unconditional inclusion, independent of any
   binder-disjointness (capture, if it happened, would only route a
   would-be-bound occurrence through M's image, still counted on the
   right). The workhorse for assertion_true_fvars_subst_bound below. *)
Lemma lexpr_fvars_subst_bound (e : LExpr) (M : gmap lvar LExpr) :
  lexpr_fvars (lexpr_subst e M) ⊆ (lexpr_fvars e ∖ dom M) ∪ lexpr_map_fvars M.
Proof.
  induction e; simpl.
  - destruct (M !! x) as [ex | ] eqn:Hx; simpl; rewrite Hx /=.
    + have Hsub : lexpr_fvars ex ⊆ lexpr_map_fvars M.
      { intros y Hy. destruct (decide (y ∈ lexpr_map_fvars M)) as [Hin | Hn]; [exact Hin |].
        exfalso. exact (proj1 (lexpr_map_fvars_spec M y) Hn x ex Hx Hy). }
      intros y Hy. apply elem_of_union_r. exact (Hsub y Hy).
    + apply not_elem_of_dom in Hx.
      intros y Hy. apply elem_of_singleton in Hy as ->.
      apply elem_of_union_l. apply elem_of_difference. split; [apply elem_of_singleton; reflexivity | exact Hx].
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
Qed.

(* List-of-arguments version, for LInv/LPred's leaf case. *)
Lemma lexpr_fvars_subst_bound_list (args : list LExpr) (M : gmap lvar LExpr) :
  ⋃ (lexpr_fvars <$> map (fun e => lexpr_subst e M) args)
  ⊆ (⋃ (lexpr_fvars <$> args) ∖ dom M) ∪ lexpr_map_fvars M.
Proof.
  induction args as [| e args' IH]; simpl; [set_solver |].
  have He := lexpr_fvars_subst_bound e M. set_solver.
Qed.

(* Assertion-level analogue of lexpr_fvars_subst_bound, unconditional in
   the same way. LExists's own case needs no side hypothesis either: the
   set-algebra alone (distributing ∖{[v]} over the IH's union) gives the
   bound, regardless of whether v happens to lie in dom M. *)
Lemma assertion_true_fvars_subst_mem_bound (a : assertion) (M : gmap lvar LExpr) :
  assertion_true_fvars (subst a M) ⊆ (assertion_true_fvars a ∖ dom M) ∪ lexpr_map_fvars M.
Proof.
  induction a as
    [ pn pe
    | sg
    | pexp
    | pp
    | oe ofld ochunk
    | ge gfld gr gchunk
    | fv ft fbody IHf
    | ev et ebody IHe
    | icond ithen IHi1 ielse IHi2
    | ivn iargs
    | pdn pargs
    | a1 IH1 a2 IH2 ];
    simpl; try set_solver.
  - (* LExprA *) have := lexpr_fvars_subst_bound pexp M. set_solver.
  - (* LOwn *)
    have := lexpr_fvars_subst_bound oe M. have := lexpr_fvars_subst_bound ochunk M. set_solver.
  - (* LGhostOwn *)
    have := lexpr_fvars_subst_bound ge M. have := lexpr_fvars_subst_bound gchunk M. set_solver.
  - (* LIte *) have := lexpr_fvars_subst_bound icond M. set_solver.
  - (* LInv *) have := lexpr_fvars_subst_bound_list iargs M. set_solver.
  - (* LPred *) have := lexpr_fvars_subst_bound_list pargs M. set_solver.
Qed.

(* Tight corollary: when a's true fvars are already fully covered by dom M,
   substituting leaves nothing behind -- no reserved (or any other) name
   escapes. This is what makes the reserved-namespace design's "or
   reserved" escape hatch unnecessary once assertion_true_fvars (rather
   than assertion_lexpr_fvars) is used: see pwf_inv_fvars_closed /
   pwf_pred_fvars_closed and trnsl_assertion_mp_irrelevant_reserved. *)
Lemma assertion_true_fvars_subst_bound (a : assertion) (M : gmap lvar LExpr) :
  assertion_true_fvars a ⊆ dom M →
  assertion_true_fvars (subst a M) ⊆ lexpr_map_fvars M.
Proof.
  intro H. have := assertion_true_fvars_subst_mem_bound a M. set_solver.
Qed.

(* Naming convention distinguishing lvars an *authored* invariant/
   predicate/procedure-contract body binds internally (its own
   existential/universal witnesses, e.g. counterInv_body's own ghost
   value) from every other lvar in the system: entry lvars, derivation-
   fresh witnesses (VarAssignmentRule etc.), and formal-argument names.
   Reserved names are never chosen by anything except the author of an
   invariant/predicate/proc contract's own binder, and never appear as a
   formal-argument name or as a key/value some substitution map could
   mention -- see subst_map_avoids_reserved below. This is what lets
   ProgramWF's own binder-freshness obligations become purely syntactic, local checks
   instead of an unsatisfiable "forall M" disjointness. *)
Definition is_reserved (v : lvar) : Prop := String.prefix "$" v = true.

Global Instance is_reserved_dec (v : lvar) : Decision (is_reserved v).
Proof. unfold is_reserved. apply _. Defined.

(* An injective ren that is the identity on reserved names never maps a
   non-reserved name into the reserved namespace: if it did, that image
   would be its own fixed point (Hren_res), forcing (by injectivity) the
   non-reserved source to equal it -- contradiction. Needed throughout the
   rename theorem wherever a ¬is_reserved side condition must survive
   renaming. *)
Lemma ren_not_reserved (ren : lvar -> lvar) (Hinj : Inj (=) (=) ren)
    (Hren_res : ∀ lv, is_reserved lv → ren lv = lv) (lv : lvar) :
  ¬ is_reserved lv → ¬ is_reserved (ren lv).
Proof.
  intros Hnres Hres.
  have Hfix : ren (ren lv) = ren lv := Hren_res (ren lv) Hres.
  have Heq : lv = ren lv := Hinj lv (ren lv) (eq_sym Hfix).
  apply Hnres. rewrite Heq. exact Hres.
Qed.

(* A list of LExprs whose free lvars all avoid the reserved namespace keeps
   that property after renaming every LExpr in the list -- the
   ProcCallRuleRet/InvAccessBlockRule/InvAllocRule side condition on their
   own args' lexprs. *)
Lemma Forall_lexpr_not_reserved_rename (ren : lvar -> lvar) (Hinj : Inj (=) (=) ren)
    (Hren_res : ∀ lv, is_reserved lv → ren lv = lv) (lexprs : list LExpr) :
  Forall (fun le => ∀ v, v ∈ lexpr_fvars le → ¬ is_reserved v) lexprs →
  Forall (fun le => ∀ v, v ∈ lexpr_fvars le → ¬ is_reserved v) (map (rename_lexpr ren) lexprs).
Proof.
  intros Hall. apply Forall_forall. intros le' Hle'.
  apply elem_of_list_fmap in Hle' as [le [-> Hle]].
  intros v Hv. rewrite lexpr_fvars_rename in Hv.
  apply elem_of_map in Hv as [v0 [-> Hv0]].
  apply ren_not_reserved; [exact Hinj | exact Hren_res |].
  exact (proj1 (Forall_forall _ _) Hall le Hle v0 Hv0).
Qed.

(* Renaming an LExpr after substituting M commutes with substituting the
   renamed M, provided every free lvar of e is either a key of M (handled by
   the Some branch regardless of ren) or reserved (where ren is required to
   be the identity, matching what's left over in the None branch). Mirrors
   the existing dom-M-or-reserved bounding pattern used throughout this file
   (see subst_congr_step/fvars_bound_mono below) but purely syntactically,
   with no separation-logic content. *)
Lemma lexpr_subst_rename (ren : lvar -> lvar) (Hren_res : ∀ lv, is_reserved lv → ren lv = lv)
    (e : LExpr) (M : gmap var LExpr)
    (HfvM : ∀ v, v ∈ lexpr_fvars e → v ∈ dom M ∨ is_reserved v) :
  rename_lexpr ren (lexpr_subst e M) = lexpr_subst e (rename_lexpr ren <$> M).
Proof.
  induction e; simpl in *.
  - (* LVar x *)
    destruct (M !! x) as [e'|] eqn:HMx.
    + rewrite lookup_fmap HMx. reflexivity.
    + rewrite lookup_fmap HMx. simpl.
      destruct (HfvM x ltac:(set_solver)) as [Hxdom | Hxres].
      * exfalso. apply not_elem_of_dom in HMx. exact (HMx Hxdom).
      * f_equal. exact (Hren_res x Hxres).
  - (* LVal *) reflexivity.
  - (* LUnOp *) f_equal. apply IHe. exact HfvM.
  - (* LBinOp *) f_equal.
    + apply IHe1. intros v Hv. apply HfvM. set_solver.
    + apply IHe2. intros v Hv. apply HfvM. set_solver.
  - (* LIfE *) f_equal.
    + apply IHe1. intros v Hv. apply HfvM. set_solver.
    + apply IHe2. intros v Hv. apply HfvM. set_solver.
    + apply IHe3. intros v Hv. apply HfvM. set_solver.
  - (* LStuck *) reflexivity.
Qed.

(* List-of-args specialization of lexpr_subst_rename, for LInv/LPred's own
   argument lists. *)
Lemma map_lexpr_subst_rename (ren : lvar -> lvar) (Hren_res : ∀ lv, is_reserved lv → ren lv = lv)
    (args : list LExpr) (M : gmap var LExpr)
    (HfvM : ∀ v, v ∈ ⋃ (lexpr_fvars <$> args) → v ∈ dom M ∨ is_reserved v) :
  map (rename_lexpr ren) (map (fun e => lexpr_subst e M) args) =
  map (fun e => lexpr_subst e (rename_lexpr ren <$> M)) args.
Proof.
  induction args as [| a args IH]; simpl; [reflexivity |].
  f_equal.
  - apply lexpr_subst_rename; [exact Hren_res |].
    intros v Hv. apply HfvM. simpl. apply elem_of_union_l. exact Hv.
  - apply IH. intros v Hv. apply HfvM. simpl. apply elem_of_union_r. exact Hv.
Qed.

(* Bundles what rename_assertion_subst_commute needs at every subterm during
   its induction, parametrically in the current subterm a (not the
   top-level assertion) -- mirrors subst_congr_cond's own style below, but
   purely syntactic. StackFree rules out LStack (subst never touches it, so
   it can't be made to agree with rename_assertion's own fmap over it);
   set_Forall is_reserved (assertion_exists_binders a) is exactly
   pwf_*_binders_reserved's own conclusion, needed for the LExists case; the
   dom-M-or-reserved bound is what lexpr_subst_rename/map_lexpr_subst_rename
   need at the LExpr leaves. *)
Definition rename_subst_cond (a : assertion) (M : gmap var LExpr) : Prop :=
  StackFree a ∧
  set_Forall is_reserved (assertion_exists_binders a) ∧
  (∀ v, v ∈ assertion_lexpr_fvars a → v ∈ dom M ∨ is_reserved v).

(* The key syntactic fact the renaming theorem needs for ProcCallRuleRet/
   InvAccessBlockRule/InvAllocRule/PredUnfoldRule/PredFoldRule: renaming
   after substituting a proc/inv/pred body agrees with substituting the
   renamed substitution map, since a's own internal binders are reserved
   (untouched by ren) and every other free lvar of a is a substituted
   formal name (untouched by ren's identity-on-M-keys-via-Some-branch,
   handled inside lexpr_subst_rename). *)
Lemma rename_assertion_subst_commute (ren : lvar -> lvar)
    (Hren_res : ∀ lv, is_reserved lv → ren lv = lv) :
  ∀ (a : assertion) (M : gmap var LExpr),
    rename_subst_cond a M →
    rename_assertion ren (subst a M) = subst a (rename_lexpr ren <$> M).
Proof.
  induction a; intros M (Hsf & HbA & HfvA); simpl in HbA, HfvA |- *.
  - (* LProc *) reflexivity.
  - (* LStack *) inversion Hsf.
  - (* LExprA *) f_equal. apply lexpr_subst_rename; [exact Hren_res | exact HfvA].
  - (* LPure *) reflexivity.
  - (* LOwn *)
    f_equal.
    + apply lexpr_subst_rename; [exact Hren_res |]. intros v Hv. apply HfvA. set_solver.
    + apply lexpr_subst_rename; [exact Hren_res |]. intros v Hv. apply HfvA. set_solver.
  - (* LGhostOwn *)
    f_equal.
    + apply lexpr_subst_rename; [exact Hren_res |]. intros v Hv. apply HfvA. set_solver.
    + apply lexpr_subst_rename; [exact Hren_res |]. intros v Hv. apply HfvA. set_solver.
  - (* LForall *)
    inversion Hsf; subst.
    f_equal. apply IHa. split_and!; [assumption | exact HbA | exact HfvA].
  - (* LExists *)
    inversion Hsf; subst.
    f_equal.
    + apply Hren_res, HbA. set_solver.
    + apply IHa. split_and!.
      * assumption.
      * intros x Hx. apply HbA. set_solver.
      * exact HfvA.
  - (* LIte *)
    inversion Hsf; subst.
    f_equal.
    + apply lexpr_subst_rename; [exact Hren_res |]. intros v Hv. apply HfvA. set_solver.
    + apply IHa1. split_and!; [assumption | intros x Hx; apply HbA; set_solver | intros v Hv; apply HfvA; set_solver].
    + apply IHa2. split_and!; [assumption | intros x Hx; apply HbA; set_solver | intros v Hv; apply HfvA; set_solver].
  - (* LInv *) f_equal. apply map_lexpr_subst_rename; [exact Hren_res | exact HfvA].
  - (* LPred *) f_equal. apply map_lexpr_subst_rename; [exact Hren_res | exact HfvA].
  - (* LAnd *)
    inversion Hsf; subst.
    f_equal.
    + apply IHa1. split_and!; [assumption | intros x Hx; apply HbA; set_solver | intros v Hv; apply HfvA; set_solver].
    + apply IHa2. split_and!; [assumption | intros x Hx; apply HbA; set_solver | intros v Hv; apply HfvA; set_solver].
Qed.

(* A genuinely rich lvar_typs (Hσ_rich's shape): a naive, finite lvar_typs
   (e.g. one built by hand out of a
   handful of named lvars) only ever has finitely many lvars per type --
   sometimes zero -- failing "forall t excl, exists lv not in excl of
   type t" outright. rich_lvar_typs below has infinitely many lvars of
   *every* type by construction, and rich_lvar_typs_rich proves it;
   lvar_typs_update then lets a caller layer their own finitely many
   fixed names on top (e.g. counter_monotonic.v's "x"/"$v"/...) while
   inheriting richness for free (lvar_typs_update_rich), rather than
   reproving this whole construction per program. *)
Section RichLvarTyps.

  (* One infinite, by-construction-disjoint family of names per type: a
     fixed prefix per type-tag ("fresh_i_"/"fresh_l_"/"fresh_b_"/
     "fresh_u_"/"fresh_r_", none a prefix of another since they agree
     everywhere but position 7), numbered so no two members of one family
     ever coincide. None of the prefixes start with "$" (is_reserved).

     TpInt/TpLoc/TpBool/TpUnit only need rich_lvar_typs to recognize the
     prefix (not recover the number), so pretty (injective on nat,
     stdpp's pretty_nat_inj) is enough. TpRA r needs rich_lvar_typs to
     recover r itself from the middle of the string, which pretty can't
     support directly (nothing pins down where its digits end and r
     begins) -- solved by numbering those in unary (a run of "z"
     characters) so the run's end is exactly the first non-"z" character,
     unambiguously, regardless of what r itself contains. *)

  Fixpoint unary (n : nat) : string :=
    match n with O => EmptyString | S n' => String "z"%char (unary n') end.

  Lemma unary_inj : Inj (=) (=) unary.
  Proof.
    intros n1. induction n1 as [| n1 IH]; intros [| n2]; simpl; try done.
    intros [= H]. f_equal. exact (IH _ H).
  Qed.

  Lemma append_cancel_l (s1 s2 s3 : string) : s1 +:+ s2 = s1 +:+ s3 -> s2 = s3.
  Proof.
    induction s1 as [| a s1 IH]; simpl; [done |].
    intros [= H]. exact (IH H).
  Qed.

  Fixpoint split_at_underscore (s : string) : string * string :=
    match s with
    | EmptyString => (EmptyString, EmptyString)
    | String a s' =>
      if ascii_dec a "_"%char then (EmptyString, s')
      else let '(pre, post) := split_at_underscore s' in (String a pre, post)
    end.

  Lemma split_at_underscore_unary_app (n : nat) (r : string) :
    split_at_underscore (unary n +:+ "_" +:+ r) = (unary n, r).
  Proof.
    induction n as [| n IH]; simpl; [done |].
    destruct (ascii_dec "z"%char "_"%char) as [Hz | _]; [discriminate Hz |].
    rewrite IH. reflexivity.
  Qed.

  (* String.prefix/String.append are Fixpoints structurally recursive on
     their *second* argument, so simpl/reflexivity get stuck on goals
     like "String.prefix s1 (s1 +:+ s2) = true" whenever s2 is open, even
     though the fact holds regardless of what s2 is -- Coq's
     fixpoint-unfolding guard is tied to the structural argument being a
     literal constructor, independent of whether the body's own first
     pattern match even inspects it. Hence this lemma, proved by
     induction rather than left to computation. *)
  Lemma prefix_app_l (s1 s2 : string) : String.prefix s1 (s1 +:+ s2) = true.
  Proof.
    induction s1 as [| a s1 IH].
    - simpl. destruct s2; reflexivity.
    - simpl. destruct (ascii_dec a a) as [_ | Hne]; [exact IH | exfalso; exact (Hne eq_refl)].
  Qed.

  Lemma substring_0_length_id (s : string) : String.substring 0 (String.length s) s = s.
  Proof. induction s as [| a s IH]; simpl; [done |]. f_equal. exact IH. Qed.

  Lemma substring_length_app (s1 s2 : string) :
    String.substring (String.length s1) (String.length s2) (s1 +:+ s2) = s2.
  Proof.
    induction s1 as [| a s1 IH]; simpl; [apply substring_0_length_id | exact IH].
  Qed.

  Lemma string_length_app (s1 s2 : string) :
    String.length (s1 +:+ s2) = String.length s1 + String.length s2.
  Proof. induction s1 as [| a s1 IH]; simpl; [done | f_equal; exact IH]. Qed.

  Definition fresh_int_name (n : nat) : lvar := "fresh_i_" +:+ pretty n.
  Definition fresh_loc_name (n : nat) : lvar := "fresh_l_" +:+ pretty n.
  Definition fresh_bool_name (n : nat) : lvar := "fresh_b_" +:+ pretty n.
  Definition fresh_unit_name (n : nat) : lvar := "fresh_u_" +:+ pretty n.
  Definition fresh_ra_name (r : ra_name) (n : nat) : lvar := "fresh_r_" +:+ unary n +:+ "_" +:+ r.

  Lemma fresh_int_name_inj : Inj (=) (=) fresh_int_name.
  Proof. intros n1 n2 H. apply pretty_nat_inj, (append_cancel_l "fresh_i_"), H. Qed.
  Lemma fresh_loc_name_inj : Inj (=) (=) fresh_loc_name.
  Proof. intros n1 n2 H. apply pretty_nat_inj, (append_cancel_l "fresh_l_"), H. Qed.
  Lemma fresh_bool_name_inj : Inj (=) (=) fresh_bool_name.
  Proof. intros n1 n2 H. apply pretty_nat_inj, (append_cancel_l "fresh_b_"), H. Qed.
  Lemma fresh_unit_name_inj : Inj (=) (=) fresh_unit_name.
  Proof. intros n1 n2 H. apply pretty_nat_inj, (append_cancel_l "fresh_u_"), H. Qed.
  Lemma fresh_ra_name_inj (r : ra_name) : Inj (=) (=) (fresh_ra_name r).
  Proof.
    intros n1 n2 H. apply (append_cancel_l "fresh_r_") in H.
    have Hsplit : split_at_underscore (unary n1 +:+ "_" +:+ r) = split_at_underscore (unary n2 +:+ "_" +:+ r).
    { rewrite H. reflexivity. }
    rewrite !split_at_underscore_unary_app in Hsplit.
    injection Hsplit as Hsplit.
    exact (unary_inj _ _ Hsplit).
  Qed.

  (* Recovers r from a name produced by fresh_ra_name: strip the
     "fresh_r_" prefix (8 characters), then split at the first
     underscore -- unary n never contains one, so this always lands
     exactly at the delimiter fresh_ra_name itself inserted, regardless
     of r's own content. *)
  Definition ra_name_of_fresh (lv : lvar) : ra_name :=
    snd (split_at_underscore (String.substring 8 (String.length lv - 8) lv)).

  Lemma ra_name_of_fresh_correct (r : ra_name) (n : nat) :
    ra_name_of_fresh (fresh_ra_name r n) = r.
  Proof.
    unfold ra_name_of_fresh, fresh_ra_name.
    rewrite string_length_app.
    replace (String.length "fresh_r_" + String.length (unary n +:+ "_" +:+ r) - 8)
      with (String.length (unary n +:+ "_" +:+ r)) by (simpl; lia).
    rewrite (substring_length_app "fresh_r_").
    rewrite split_at_underscore_unary_app. reflexivity.
  Qed.

  Definition rich_lvar_typs : lvar_typs := fun lv =>
    if String.prefix "fresh_i_" lv then TpInt
    else if String.prefix "fresh_l_" lv then TpLoc
    else if String.prefix "fresh_b_" lv then TpBool
    else if String.prefix "fresh_u_" lv then TpUnit
    else if String.prefix "fresh_r_" lv then TpRA (ra_name_of_fresh lv)
    else TpUnit.

  Lemma rich_lvar_typs_fresh_int (n : nat) : rich_lvar_typs (fresh_int_name n) = TpInt.
  Proof. unfold rich_lvar_typs, fresh_int_name. rewrite (prefix_app_l "fresh_i_"). reflexivity. Qed.
  Lemma rich_lvar_typs_fresh_loc (n : nat) : rich_lvar_typs (fresh_loc_name n) = TpLoc.
  Proof. unfold rich_lvar_typs, fresh_loc_name. rewrite (prefix_app_l "fresh_l_"). reflexivity. Qed.
  Lemma rich_lvar_typs_fresh_bool (n : nat) : rich_lvar_typs (fresh_bool_name n) = TpBool.
  Proof. unfold rich_lvar_typs, fresh_bool_name. rewrite (prefix_app_l "fresh_b_"). reflexivity. Qed.
  Lemma rich_lvar_typs_fresh_unit (n : nat) : rich_lvar_typs (fresh_unit_name n) = TpUnit.
  Proof. unfold rich_lvar_typs, fresh_unit_name. rewrite (prefix_app_l "fresh_u_"). reflexivity. Qed.
  Lemma rich_lvar_typs_fresh_ra (r : ra_name) (n : nat) : rich_lvar_typs (fresh_ra_name r n) = TpRA r.
  Proof.
    unfold rich_lvar_typs, fresh_ra_name. rewrite (prefix_app_l "fresh_r_").
    fold (fresh_ra_name r n). rewrite ra_name_of_fresh_correct. reflexivity.
  Qed.

  Lemma fresh_int_name_not_reserved (n : nat) : ¬ is_reserved (fresh_int_name n).
  Proof. unfold is_reserved. discriminate. Qed.
  Lemma fresh_loc_name_not_reserved (n : nat) : ¬ is_reserved (fresh_loc_name n).
  Proof. unfold is_reserved. discriminate. Qed.
  Lemma fresh_bool_name_not_reserved (n : nat) : ¬ is_reserved (fresh_bool_name n).
  Proof. unfold is_reserved. discriminate. Qed.
  Lemma fresh_unit_name_not_reserved (n : nat) : ¬ is_reserved (fresh_unit_name n).
  Proof. unfold is_reserved. discriminate. Qed.
  Lemma fresh_ra_name_not_reserved (r : ra_name) (n : nat) : ¬ is_reserved (fresh_ra_name r n).
  Proof. unfold is_reserved. discriminate. Qed.

  Lemma NoDup_map_of_inj {A B} (f : A -> B) (Hinj : ∀ x y, f x = f y -> x = y) (l : list A) :
    NoDup l -> NoDup (map f l).
  Proof.
    induction 1 as [| x l Hnotin Hnodup IH]; simpl; constructor; auto.
    intros Hin. apply Hnotin. apply elem_of_list_In, in_map_iff in Hin as [y [Heq Hy]].
    apply Hinj in Heq. subst. apply elem_of_list_In. exact Hy.
  Qed.

  (* Pigeonhole: an injective f : nat -> lvar can't map k+1 distinct
     naturals (k := length (elements excl)) all into excl (which only
     has k elements), so at least one index must escape. Self-contained
     (not stdpp's Infinite class): avoids having to separately show that
     class's own opaque "fresh" witness lands in f's image, which stdpp
     doesn't expose. *)
  Lemma exists_fresh_index (f : nat -> lvar) (Hinj : Inj (=) (=) f) (excl : gset lvar) :
    ∃ n, f n ∉ excl.
  Proof.
    set (k := length (elements excl)).
    destruct (Forall_Exists_dec (fun n => f n ∈ excl) (fun n => f n ∉ excl)
                (fun n => decide (f n ∈ excl)) (seq 0 (S k)))
      as [Hall | Hex].
    - exfalso.
      have Hnodup : NoDup (map f (seq 0 (S k))).
      { apply NoDup_map_of_inj; [intros x y; apply Hinj | apply NoDup_seq]. }
      have Hincl : incl (map f (seq 0 (S k))) (elements excl).
      { intros y Hy. apply in_map_iff in Hy as [n [<- Hn]].
        apply (elem_of_list_In (elements excl) (f n)), elem_of_elements.
        apply (proj1 (Forall_forall _ (seq 0 (S k))) Hall n).
        apply elem_of_list_In. exact Hn. }
      pose proof (NoDup_incl_length (proj1 (NoDup_ListNoDup _) Hnodup) Hincl) as Hle.
      rewrite map_length seq_length in Hle.
      unfold k in Hle. lia.
    - apply Exists_exists in Hex as [n [_ Hn]]. exists n. exact Hn.
  Qed.

  Lemma rich_lvar_typs_rich :
    ∀ (t : typ) (excl : gset lvar), ∃ lv, lv ∉ excl ∧ ¬ is_reserved lv ∧ rich_lvar_typs lv = t.
  Proof.
    intros t excl.
    destruct t as [ | | | | r].
    - destruct (exists_fresh_index fresh_int_name fresh_int_name_inj excl) as [n Hn].
      exists (fresh_int_name n). eauto using fresh_int_name_not_reserved, rich_lvar_typs_fresh_int.
    - destruct (exists_fresh_index fresh_loc_name fresh_loc_name_inj excl) as [n Hn].
      exists (fresh_loc_name n). eauto using fresh_loc_name_not_reserved, rich_lvar_typs_fresh_loc.
    - destruct (exists_fresh_index fresh_bool_name fresh_bool_name_inj excl) as [n Hn].
      exists (fresh_bool_name n). eauto using fresh_bool_name_not_reserved, rich_lvar_typs_fresh_bool.
    - destruct (exists_fresh_index fresh_unit_name fresh_unit_name_inj excl) as [n Hn].
      exists (fresh_unit_name n). eauto using fresh_unit_name_not_reserved, rich_lvar_typs_fresh_unit.
    - destruct (exists_fresh_index (fresh_ra_name r) (fresh_ra_name_inj r) excl) as [n Hn].
      exists (fresh_ra_name r n). eauto using fresh_ra_name_not_reserved, rich_lvar_typs_fresh_ra.
  Qed.

  (* Layers finitely many fixed names on top of any already-rich
     lvar_typs (not just rich_lvar_typs above -- this holds for any base
     satisfying the same richness shape), inheriting richness for free:
     given (t, excl), search the base's own richness fact with the
     overrides' keys folded into the exclusion set too, so the witness it
     returns can never be one of the finitely many overridden names. *)
  Definition lvar_typs_update (overrides : gmap lvar typ) (base : lvar_typs) : lvar_typs :=
    fun lv => match overrides !! lv with Some t => t | None => base lv end.

  Lemma lvar_typs_update_rich (overrides : gmap lvar typ) (base : lvar_typs)
      (Hbase_rich : ∀ (t : typ) (excl : gset lvar), ∃ lv, lv ∉ excl ∧ ¬ is_reserved lv ∧ base lv = t) :
    ∀ (t : typ) (excl : gset lvar), ∃ lv, lv ∉ excl ∧ ¬ is_reserved lv ∧ lvar_typs_update overrides base lv = t.
  Proof.
    intros t excl.
    destruct (Hbase_rich t (excl ∪ (dom overrides : gset lvar))) as [lv [Hnotin [Hnotres Heq]]].
    exists lv. split; [set_solver |]. split; [exact Hnotres |].
    unfold lvar_typs_update.
    destruct (overrides !! lv) eqn:Hov; [| exact Heq].
    exfalso. apply Hnotin. apply elem_of_union_r, elem_of_dom. eexists. exact Hov.
  Qed.

End RichLvarTyps.

(* Bundles both projections of "M was built by the ordinary framework
   machinery, not by hand-picking a reserved name": neither its keys
   (formal-argument/entry-lvar names) nor the fvars of its values (lvars
   some caller's stack happens to use) ever land in the reserved
   namespace. Whoever supplies this for a concrete M is asserting it was
   actually built that way -- e.g. via trnsl_expr_lExpr against an
   ordinary symbolic stack, or via fresh_proc_entry_lvars/Hσ_rich, itself
   expected to be strengthened to avoid the reserved prefix wherever it
   is finally discharged for a concrete program (not yet needed to
   typecheck this file). *)
Definition subst_map_avoids_reserved (M : gmap lvar LExpr) : Prop :=
  (∀ v, v ∈ dom M → ¬ is_reserved v) ∧ (∀ v, v ∈ lexpr_map_fvars M → ¬ is_reserved v).

(* The bridge from the record-local pwf_*_binders_reserved fields (an
   assertion's own binders are all reserved) plus subst_map_avoids_reserved
   (a substitution map touches none of them) to the disjointness fact the
   translation machinery actually needs. *)
Lemma reserved_disjoint_dom (R X : gset lvar) :
  set_Forall is_reserved R → (∀ v, v ∈ X → ¬ is_reserved v) → R ## X.
Proof. intros HR HX v HvR HvX. exact (HX v HvX (HR v HvR)). Qed.

Lemma assertion_exists_binders_subst (a : assertion) (M : gmap lvar LExpr) :
  assertion_exists_binders (subst a M) = assertion_exists_binders a.
Proof.
  induction a; simpl; try reflexivity; try congruence.
Qed.

(* Substitution composes: if all fvars of e are in dom σ, then substituting
   via (fmap (fun e => lexpr_subst e M) σ) equals substituting σ then M.
   Generalized over an extra "safe to leave unsubstituted" set R, disjoint
   from dom M: covers names an over-approximating fvars computation might
   pull in that aren't genuinely free (see assertion_lexpr_fvars's own
   generalization below). Instantiating R := ∅
   recovers the original statement exactly. *)
Lemma lexpr_subst_compose (e : LExpr) (σ M : gmap var LExpr) (R : gset lvar) :
  R ## dom M →
  lexpr_fvars e ⊆ dom σ ∪ R →
  lexpr_subst e (fmap (fun e' => lexpr_subst e' M) σ) = lexpr_subst (lexpr_subst e σ) M.
Proof.
  intro HR. induction e; simpl; intro Hfv.
  - (* LVar x *)
    destruct (decide (x ∈ dom σ)) as [Hxin | Hxout].
    + apply elem_of_dom in Hxin as [ex Hex].
      rewrite lookup_fmap Hex /=. done.
    + have HxR : x ∈ R. { set_solver. }
      have HxM : x ∉ dom M. { set_solver. }
      apply not_elem_of_dom in Hxout.
      apply not_elem_of_dom in HxM.
      rewrite Hxout /=.
      rewrite lookup_fmap Hxout /=.
      rewrite HxM.
      reflexivity.
  - done.
  - have := IHe Hfv. congruence.
  - have H1 := IHe1 ltac:(set_solver). have H2 := IHe2 ltac:(set_solver). congruence.
  - have H1 := IHe1 ltac:(set_solver). have H2 := IHe2 ltac:(set_solver).
    have H3 := IHe3 ltac:(set_solver). congruence.
  - done.
Qed.

(* Zipping keys with a mapped list equals fmapping the list_to_map. *)
Lemma list_to_map_zip_fmap (ks : list var) (vs : list LExpr) (M : gmap var LExpr) :
  (list_to_map (zip ks (map (fun e => lexpr_subst e M) vs)) : gmap var LExpr) =
  fmap (fun e => lexpr_subst e M) (list_to_map (zip ks vs) : gmap var LExpr).
Proof.
  revert vs. induction ks as [| k ks' IH]; intro vs.
  - done.
  - destruct vs as [| v vs']; [done |].
    simpl. rewrite IH fmap_insert. done.
Qed.

(* When lengths match, dom of list_to_map(zip) equals list_to_set of keys. *)
Lemma dom_list_to_map_zip (args : list var) (vals : list LExpr) :
  length args = length vals →
  dom (list_to_map (zip args vals) : gmap var LExpr) = list_to_set args.
Proof.
  revert vals. induction args as [| a args' IH]; intros vals Hlen.
  - done.
  - destruct vals as [| v vals']; [simpl in Hlen; lia |].
    simpl. rewrite dom_insert_L IH; [done | simpl in Hlen; lia].
Qed.

(* Generalized the same way as lexpr_subst_compose, and by the same
   argument: R is threaded through the induction *unchanged* rather than
   recomputed at each LExists/LForall (assertion_lexpr_fvars doesn't
   shrink through those cases -- it's literally unchanged, by
   definition -- so the set of names needing coverage doesn't either).
   Typical instantiation: R := assertion_exists_binders a, which is what
   lets a's own over-approximated fvars at every LExists/LForall leak in
   its own binder names for free, and R := ∅ recovers the original
   unconditional statement. *)
Lemma assertion_subst_compose (a : assertion) (σ M : gmap var LExpr) (R : gset lvar) :
  R ## dom M →
  assertion_lexpr_fvars a ⊆ dom σ ∪ R →
  subst a (fmap (fun e => lexpr_subst e M) σ) = subst (subst a σ) M.
Proof.
  intro HR. induction a; simpl; intro Hfv; try done.
  - f_equal. apply (lexpr_subst_compose _ _ _ R HR). exact Hfv.
  - f_equal; apply (lexpr_subst_compose _ _ _ R HR); set_solver.
  - f_equal; apply (lexpr_subst_compose _ _ _ R HR); set_solver.
  - f_equal. apply IHa. exact Hfv.
  - f_equal. apply IHa. exact Hfv.
  - f_equal; [apply (lexpr_subst_compose _ _ _ R HR) | apply IHa1 | apply IHa2]; set_solver.
  - (* LInv *) f_equal. rewrite map_map. apply Forall_fmap_ext_1.
    apply Forall_forall. intros e He.
    apply (lexpr_subst_compose _ _ _ R HR).
    have Hsub : lexpr_fvars e ⊆ ⋃ (lexpr_fvars <$> args). {
      intros x Hx. apply elem_of_union_list. exists (lexpr_fvars e).
      split; [apply elem_of_list_fmap; exists e; split; [done | exact He] | exact Hx].
    }
    set_solver.
  - (* LPred *) f_equal. rewrite map_map. apply Forall_fmap_ext_1.
    apply Forall_forall. intros e He.
    apply (lexpr_subst_compose _ _ _ R HR).
    have Hsub : lexpr_fvars e ⊆ ⋃ (lexpr_fvars <$> args). {
      intros x Hx. apply elem_of_union_list. exists (lexpr_fvars e).
      split; [apply elem_of_list_fmap; exists e; split; [done | exact He] | exact Hx].
    }
    set_solver.
  - f_equal; [apply IHa1 | apply IHa2]; set_solver.
Qed.

(* InvBodyWF follows from the widened well-scopedness condition: every
   lexpr fvar of inv_body is either a genuine formal argument or one of
   inv_body's own binders (the latter only ever shows up because
   assertion_lexpr_fvars doesn't subtract LExists/LForall's bound
   variable). *)
Lemma inv_body_wf_from_scoped (r : InvRecord) :
  (∀ v, v ∈ assertion_lexpr_fvars r.(inv_body) →
     v ∈ (list_to_set r.(inv_args) : gset lvar) ∨ v ∈ assertion_exists_binders r.(inv_body)) →
  InvBodyWF r.
Proof.
  intros Hscoped args M Hlen HR.
  have Hdom : dom (list_to_map (zip r.(inv_args) args) : gmap var LExpr) = list_to_set r.(inv_args).
  { apply dom_list_to_map_zip. lia. }
  have Hfv : assertion_lexpr_fvars r.(inv_body) ⊆
    dom (list_to_map (zip r.(inv_args) args) : gmap var LExpr) ∪ assertion_exists_binders r.(inv_body).
  { intros v Hv. rewrite elem_of_union Hdom. exact (Hscoped v Hv). }
  rewrite list_to_map_zip_fmap.
  exact (assertion_subst_compose r.(inv_body) _ M (assertion_exists_binders r.(inv_body)) HR Hfv).
Qed.

(* PredBodyWF follows from the widened well-scopedness condition,
   analogously. *)
Lemma pred_body_wf_from_scoped (r : PredRecord) :
  (∀ v, v ∈ assertion_lexpr_fvars r.(pred_body) →
     v ∈ (list_to_set r.(pred_args) : gset lvar) ∨ v ∈ assertion_exists_binders r.(pred_body)) →
  PredBodyWF r.
Proof.
  intros Hscoped args M Hlen HR.
  have Hdom : dom (list_to_map (zip r.(pred_args) args) : gmap var LExpr) = list_to_set r.(pred_args).
  { apply dom_list_to_map_zip. lia. }
  have Hfv : assertion_lexpr_fvars r.(pred_body) ⊆
    dom (list_to_map (zip r.(pred_args) args) : gmap var LExpr) ∪ assertion_exists_binders r.(pred_body).
  { intros v Hv. rewrite elem_of_union Hdom. exact (Hscoped v Hv). }
  rewrite list_to_map_zip_fmap.
  exact (assertion_subst_compose r.(pred_body) _ M (assertion_exists_binders r.(pred_body)) HR Hfv).
Qed.

(* Ghost-embedding config: namespace/gname bookkeeping needed to embed a
   program into Iris, distinct from Program (what a .rav author writes).
   Not Gamma: Gamma_type sits inside the (already-closed, by this point)
   nested Section Translation below, so it can't be bundled here; stays
   its own Variable. *)
Record GhostConfig := {
  gc_ghost_heap_name : gname;
  gc_ghost_heap_namespace : namespace;
  gc_inv_namespace_map : inv_name -> namespace;
}.

Context {G : GhostConfig}.

Let ghost_heap_name := G.(gc_ghost_heap_name).
Let ghost_heap_namespace := G.(gc_ghost_heap_namespace).
Let inv_namespace_map := G.(gc_inv_namespace_map).

(* Well-formedness predicate for a program (proc_map, inv_map, pred_map).
   Bundles all structural side-conditions required by the translation theorem.
   A user of rrl_validity must supply one ProgramWF witness for their concrete program. *)
Record ProgramWF : Prop := {
  (* ── Procedure map ───────────────────────────────────────────────────── *)
  (* Argument names of every procedure are distinct. *)
  pwf_proc_args_unique :
    map_Forall (λ _ r, NoDup (proc_args_of r).*1) proc_map;

  (* "#ret_val" is a reserved name, never a formal argument: keeps the
     operationally-appended "#ret_val" slot (see lang.v's RTCallStep) from
     ever colliding with a real argument. *)
  pwf_proc_ret_val_fresh :
    map_Forall (λ _ r, "#ret_val" ∉ (proc_args_of r).*1) proc_map;

  (* Local-variable names of every procedure are distinct. *)
  pwf_proc_locals_unique :
    map_Forall (λ _ r, NoDup (proc_locals_of r).*1) proc_map;

  (* Formal-argument and local-variable names never collide -- both get their
     own pre-allocated slot in a fresh stack frame (see lang.v's
     RTCallStep/SpawnStep). *)
  pwf_proc_args_locals_disjoint :
    map_Forall (λ _ r, (proc_args_of r).*1 ## (proc_locals_of r).*1) proc_map;

  (* "#ret_val" is declared as one of the procedure's own local variables,
     with whatever type its associated proc_record gives it -- it is
     initialized (like every other local) to a non-deterministically chosen
     value of that type, then read out again at the return point. *)
  pwf_proc_ret_val_declared :
    map_Forall (λ _ r, "#ret_val" ∈ (proc_locals_of r).*1) proc_map;

  (* Pre- and postconditions of every procedure are stack-free. *)
  pwf_proc_stack_free :
    map_Forall (λ _ r,
      StackFree (proc_precond_of r) ∧ StackFree (proc_postcond_of r)) proc_map;

  (* LExpr free variables in pre/post are bounded by the formal argument
     names, up to pre/post's own binder names (leaked in by
     assertion_lexpr_fvars's own over-approximation through LExists/
     LForall -- it doesn't subtract the bound variable).
     pwf_proc_binders_reserved below is what makes those binder names
     harmless despite not being formal arguments. *)
  pwf_proc_fvars_bounded :
    map_Forall (λ _ r,
      (∀ v, v ∈ assertion_lexpr_fvars (proc_precond_of r) →
         v ∈ (list_to_set (proc_args_of r).*1 : gset lvar) ∨
         v ∈ assertion_exists_binders (proc_precond_of r)) ∧
      (∀ v, v ∈ assertion_lexpr_fvars (proc_postcond_of r) →
         v ∈ ({["#ret_val"]} ∪ list_to_set (proc_args_of r).*1 : gset lvar) ∨
         v ∈ assertion_exists_binders (proc_postcond_of r))) proc_map;

  (* Every procedure's own pre/postcond binders (its own internal
     existential/universal witnesses, as opposed to lvars threaded through
     the symbolic stack) are drawn from the reserved namespace (is_reserved),
     so they can never collide with any substitution map's own fvars -- an
     unconditional "forall M" disjointness would be unsatisfiable whenever
     pre/postcond has a genuine existential. *)
  pwf_proc_binders_reserved :
    map_Forall (λ _ r,
      set_Forall is_reserved (assertion_exists_binders (proc_precond_of r)) ∧
      set_Forall is_reserved (assertion_exists_binders (proc_postcond_of r))) proc_map;

  (* Analogous to pwf_inv_args_not_reserved: a procedure's own formal
     argument names are never drawn from the reserved namespace. *)
  pwf_proc_args_not_reserved :
    map_Forall (λ _ r, Forall (λ a, ¬ is_reserved a) (proc_args_of r).*1) proc_map;

  (* ── Invariant map ───────────────────────────────────────────────────── *)
  (* LExpr fvars of an invariant body are bounded by its formal argument
     names, up to its own binder names (same over-approximation as
     pwf_proc_fvars_bounded above). *)
  pwf_inv_fvars_scoped :
    map_Forall (λ _ r,
      ∀ v, v ∈ assertion_lexpr_fvars r.(inv_body) →
        v ∈ (list_to_set r.(inv_args) : gset lvar) ∨ v ∈ assertion_exists_binders r.(inv_body)) inv_map;

  (* Stronger than pwf_inv_fvars_scoped: an invariant body's *scope-correct*
     free variables (assertion_true_fvars, which -- unlike
     assertion_lexpr_fvars -- actually subtracts a genuine existential's own
     bound name) are fully covered by its formal arguments, with no reserved
     leftover at all. This rules out a body that mentions a reserved name
     "freely" outside the scope of its own matching binder -- something
     pwf_inv_fvars_scoped's "∨ reserved" escape hatch can't distinguish from
     the over-approximation's false positives. Needed by
     trnsl_assertion_mp_irrelevant_reserved. *)
  pwf_inv_fvars_closed :
    map_Forall (λ _ r, assertion_true_fvars r.(inv_body) ⊆ (list_to_set r.(inv_args) : gset lvar)) inv_map;

  (* LExpr fvars of a substituted invariant body are bounded by the argument
     fvars, up to the (subst-invariant, see assertion_exists_binders_subst)
     binder names. Needs length args = length r.(inv_args): without it,
     zip truncates and some of inv_body's own formal-argument-only free
     vars (e.g. a genuine "x" reference, not one of inv_body's own
     binders) can survive the substitution unaccounted for by either
     disjunct -- concretely false for any invariant whose body actually
     mentions a formal argument, caught while constructing a concrete
     ProgramWF witness. This field is currently
     unused elsewhere in the codebase; pwf_pred_fvars_bounded (its
     predicate analogue, used by subst_congr_step's LPred case) already
     always has this length fact on hand from StackFree's own SF_Pred/
     SF_Inv premise, so this is purely a matter of exposing it here too. *)
  pwf_inv_fvars_bounded :
    ∀ inv_nm r args, inv_map !! inv_nm = Some r → length args = length r.(inv_args) →
      ∀ v, v ∈ assertion_lexpr_fvars (subst r.(inv_body) (list_to_map (zip r.(inv_args) args))) →
        v ∈ (⋃ (lexpr_fvars <$> args) : gset lvar) ∨ v ∈ assertion_exists_binders r.(inv_body);

  (* Analogous to pwf_proc_binders_reserved: an invariant body's own
     binders are drawn from the reserved namespace. *)
  pwf_inv_binders_reserved :
    map_Forall (λ _ r, set_Forall is_reserved (assertion_exists_binders r.(inv_body))) inv_map;

  (* Ordinary formal-argument names, unlike an invariant's own internal
     witnesses, are never drawn from the reserved namespace -- needed so
     that a subst_map keyed by an invariant's own inv_args (e.g. the
     inv_arg_map built from a concrete argument-value list, used to open
     the invariant) can be shown, syntactically, to avoid reserved names,
     independent of subst_map_avoids_reserved (which is about lvars,
     not the pvar-keyed formal-argument names substitution ranges over). *)
  pwf_inv_args_not_reserved :
    map_Forall (λ _ r, Forall (λ a, ¬ is_reserved a) r.(inv_args)) inv_map;

  (* ── Predicate map ───────────────────────────────────────────────────── *)
  (* LExpr fvars of a predicate body are bounded by its formal argument
     names, up to its own binder names (same over-approximation as above). *)
  pwf_pred_fvars_scoped :
    map_Forall (λ _ r,
      ∀ v, v ∈ assertion_lexpr_fvars r.(pred_body) →
        v ∈ (list_to_set r.(pred_args) : gset lvar) ∨ v ∈ assertion_exists_binders r.(pred_body)) pred_map;

  (* Analogous to pwf_inv_fvars_closed. *)
  pwf_pred_fvars_closed :
    map_Forall (λ _ r, assertion_true_fvars r.(pred_body) ⊆ (list_to_set r.(pred_args) : gset lvar)) pred_map;

  (* LExpr fvars of a substituted predicate body are bounded by the
     argument fvars, up to the binder names. Needs length args =
     length r.(pred_args) -- see pwf_inv_fvars_bounded's own comment,
     same reason; subst_congr_step's LPred case (this field's one
     consumer) already always has the length fact on hand. *)
  pwf_pred_fvars_bounded :
    ∀ pred_nm r args, pred_map !! pred_nm = Some r → length args = length r.(pred_args) →
      ∀ v, v ∈ assertion_lexpr_fvars (subst r.(pred_body) (list_to_map (zip r.(pred_args) args))) →
        v ∈ (⋃ (lexpr_fvars <$> args) : gset lvar) ∨ v ∈ assertion_exists_binders r.(pred_body);

  (* Analogous to pwf_proc_binders_reserved: a predicate body's own binders
     are drawn from the reserved namespace. *)
  pwf_pred_binders_reserved :
    map_Forall (λ _ r, set_Forall is_reserved (assertion_exists_binders r.(pred_body))) pred_map;

  (* Analogous to pwf_inv_args_not_reserved: a predicate's own formal
     argument names are never drawn from the reserved namespace. *)
  pwf_pred_args_not_reserved :
    map_Forall (λ _ r, Forall (λ a, ¬ is_reserved a) r.(pred_args)) pred_map;

  (* An invariant body, once its formal arguments are instantiated, is
     stack-free: it never mentions the stack of whoever opens it.  This is the
     same discipline procedure pre/postconditions are already held to
     (pwf_proc_stack_free), and it is what lets the single shared world
     [Winv] below store the body without fixing a stack. *)
  pwf_inv_body_stack_free :
    map_Forall (λ _ r, StackFree r.(inv_body)) inv_map;

  (* ── Invariant ghost names ────────────────────────────────────────────── *)
  (* Distinct invariants get distinct ghost names, so an [LInv] fragment for
     one invariant can never be mistaken for another's. *)
  pwf_inv_gname_injective :
    ∀ inv1 inv2 : inv_name,
      inv1 ∈ inv_set → inv2 ∈ inv_set →
        invtoken_names inv1 = invtoken_names inv2 → inv1 = inv2;

  (* ── Invariant namespaces ─────────────────────────────────────────────── *)
  (* Namespaces assigned to *distinct* invariants are disjoint.  The [inv1 ≠ inv2]
     guard is essential: without it the reflexive instance would force every
     namespace to be empty, which no real namespace is. *)
  pwf_inv_namespace_disjoint :
    ∀ inv1 inv2 : inv_name,
      inv1 ∈ inv_set → inv2 ∈ inv_set → inv1 ≠ inv2 →
        (inv_namespace_map inv1) ## (inv_namespace_map inv2);

  (* ── Ghost heap namespace ─────────────────────────────────────────────── *)
  (* Wghost's own namespace is disjoint from every user invariant's, so
     Wghost and any Winv inv' can always be opened together without
     namespace collisions. *)
  pwf_ghost_heap_namespace_disjoint_inv :
    ∀ inv' : inv_name,
      inv' ∈ inv_set →
        ghost_heap_namespace ## (inv_namespace_map inv');
}.

(* The rename_subst_cond bundle (StackFree/binders-reserved/fvars-bounded)
   for a procedure's precondition against its own formal-argument subst_map
   -- exactly what rename_assertion_subst_commute needs to push a rename
   through ProcCallRuleRet's own subst call. pwf_proc_fvars_bounded's own
   "∨ v ∈ assertion_exists_binders" disjunct is folded into "∨ is_reserved v"
   via pwf_proc_binders_reserved. *)
Lemma rename_subst_cond_proc_precond (Hwf : ProgramWF) (proc_name : proc_name) (proc_record : ProcRecord)
    (Hpm : proc_map !! proc_name = Some proc_record) (lexprs : list LExpr)
    (Hlen : length lexprs = length (proc_args_of proc_record)) :
  rename_subst_cond (proc_precond_of proc_record) (list_to_map (zip (proc_args_of proc_record).*1 lexprs)).
Proof.
  destruct (Hwf.(pwf_proc_stack_free) proc_name proc_record Hpm) as [Hsf _].
  destruct (Hwf.(pwf_proc_binders_reserved) proc_name proc_record Hpm) as [Hbr _].
  destruct (Hwf.(pwf_proc_fvars_bounded) proc_name proc_record Hpm) as [Hfv _].
  split; [exact Hsf |]. split; [exact Hbr |].
  intros v Hv. destruct (Hfv v Hv) as [Hin | Hin].
  - left. rewrite (dom_list_to_map_zip_eq_len (proc_args_of proc_record).*1 lexprs);
      [exact Hin | rewrite map_length; symmetry; exact Hlen].
  - right. exact (Hbr v Hin).
Qed.

(* Same, for the postcondition against its own subst_map extended with the
   "#ret_val" binding -- matches pwf_proc_fvars_bounded's postcond bound,
   which already has {["#ret_val"]} unioned in. *)
Lemma rename_subst_cond_proc_postcond (Hwf : ProgramWF) (proc_name : proc_name) (proc_record : ProcRecord)
    (Hpm : proc_map !! proc_name = Some proc_record) (lexprs : list LExpr) (lvar_x : lvar)
    (Hlen : length lexprs = length (proc_args_of proc_record)) :
  rename_subst_cond (proc_postcond_of proc_record)
    (<["#ret_val" := LVar lvar_x]> (list_to_map (zip (proc_args_of proc_record).*1 lexprs))).
Proof.
  destruct (Hwf.(pwf_proc_stack_free) proc_name proc_record Hpm) as [_ Hsf].
  destruct (Hwf.(pwf_proc_binders_reserved) proc_name proc_record Hpm) as [_ Hbr].
  destruct (Hwf.(pwf_proc_fvars_bounded) proc_name proc_record Hpm) as [_ Hfv].
  split; [exact Hsf |]. split; [exact Hbr |].
  intros v Hv. destruct (Hfv v Hv) as [Hin | Hin].
  - left. rewrite dom_insert_L.
    rewrite (dom_list_to_map_zip_eq_len (proc_args_of proc_record).*1 lexprs);
      [exact Hin | rewrite map_length; symmetry; exact Hlen].
  - right. exact (Hbr v Hin).
Qed.

(* Invariant-body analogue, combining pwf_inv_body_stack_free/
   pwf_inv_binders_reserved/pwf_inv_fvars_scoped the same way. *)
Lemma rename_subst_cond_inv_body (Hwf : ProgramWF) (inv : inv_name) (inv_record : InvRecord)
    (Hinvm : inv_map !! inv = Some inv_record) (lexprs : list LExpr)
    (Hlen : length lexprs = length inv_record.(inv_args)) :
  rename_subst_cond inv_record.(inv_body) (list_to_map (zip inv_record.(inv_args) lexprs)).
Proof.
  have Hsf := Hwf.(pwf_inv_body_stack_free) inv inv_record Hinvm.
  have Hbr := Hwf.(pwf_inv_binders_reserved) inv inv_record Hinvm.
  have Hfv := Hwf.(pwf_inv_fvars_scoped) inv inv_record Hinvm.
  split; [exact Hsf |]. split; [exact Hbr |].
  intros v Hv. destruct (Hfv v Hv) as [Hin | Hin].
  - left. rewrite (dom_list_to_map_zip_eq_len inv_record.(inv_args) lexprs); [exact Hin | symmetry; exact Hlen].
  - right. exact (Hbr v Hin).
Qed.

(* Predicate-body analogue of rename_subst_cond_inv_body. ProgramWF has no
   pwf_pred_body_stack_free field (StackFree of a predicate body is only
   ever established indirectly, per-call, via StackFree's own SF_Pred
   constructor on the *substituted* body -- see its comment) so the
   unconditional StackFree pred_body fact this needs is taken as an
   explicit extra hypothesis, discharged trivially at any call site whose
   pred_map is empty (e.g. counter_monotonic.v's Program). *)
Lemma rename_subst_cond_pred_body (Hwf : ProgramWF) (pred : pred_name) (pred_record : PredRecord)
    (Hsf : StackFree pred_record.(pred_body))
    (Hpredm : pred_map !! pred = Some pred_record) (lexprs : list LExpr)
    (Hlen : length lexprs = length pred_record.(pred_args)) :
  rename_subst_cond pred_record.(pred_body) (list_to_map (zip pred_record.(pred_args) lexprs)).
Proof.
  have Hbr := Hwf.(pwf_pred_binders_reserved) pred pred_record Hpredm.
  have Hfv := Hwf.(pwf_pred_fvars_scoped) pred pred_record Hpredm.
  split; [exact Hsf |]. split; [exact Hbr |].
  intros v Hv. destruct (Hfv v Hv) as [Hin | Hin].
  - left. rewrite (dom_list_to_map_zip_eq_len pred_record.(pred_args) lexprs); [exact Hin | symmetry; exact Hlen].
  - right. exact (Hbr v Hin).
Qed.

(* Type inference for expressions---placed here so expr_well_defined can use it. *)
Definition typeOf (v: lang.val) : typ :=
match v with
| lang.LitBool _ => TpBool
| lang.LitInt _ => TpInt
| lang.LitUnit => TpUnit
| lang.LitLoc _ => TpLoc
| lang.LitRAElem (existT r _) => TpRA r
end.

(* Bridges typeOf (on lang.val, the real runtime value) to typ_val_match (on
   val, the symbolic one trnsl_val embeds into) -- needed wherever a runtime
   type fact (typeOf v = t) must justify a symbolic witness's own type
   obligation (e.g. ProcCallRuleRet's soundness case, matching a call's
   returned value against its LExists translation). *)
Lemma typeOf_trnsl_val_match (v : lang.val) (t : typ) :
  typeOf v = t -> typ_val_match t (trnsl_val v).
Proof.
  destruct v as [ | | | | [r x]]; intros <-; simpl; done.
Qed.

Lemma typeOf_val_has_typ v t : typeOf v = t <-> lang.val_has_typ v t.
Proof using G inv_namespace_map. destruct v as [ | | | | [r x] ], t; simpl; naive_solver. Qed.

Fixpoint inf_expr (ρ: pvar_typs) (e: lang.expr) : option typ :=
match e with
| Var x => Some (ρ x)
| Val v => Some (typeOf v)
| UnOp NotBoolOp e =>
  match inf_expr ρ e with
  | Some TpBool => Some TpBool
  | _ => None
  end
| UnOp NegOp e =>
  match inf_expr ρ e with
  | Some TpInt => Some TpInt
  | _ => None
  end
| UnOp (RAOfIntOp r) e =>
  match inf_expr ρ e with
  | Some TpInt => Some (TpRA r)
  | _ => None
  end
| BinOp (AddOp | SubOp | MulOp | DivOp | ModOp) e1 e2 =>
  match inf_expr ρ e1, inf_expr ρ e2 with
  | Some TpInt, Some TpInt => Some TpInt
  | _, _ => None
  end
| BinOp (LtOp | GtOp | LeOp | GeOp) e1 e2 =>
  match inf_expr ρ e1, inf_expr ρ e2 with
  | Some TpInt, Some TpInt => Some TpBool
  | _, _ => None
  end
| BinOp (AndOp | OrOp) e1 e2 =>
  match inf_expr ρ e1, inf_expr ρ e2 with
  | Some TpBool, Some TpBool => Some TpBool
  | _, _ => None
  end
| BinOp (EqOp | NeOp) e1 e2 =>
  match inf_expr ρ e1, inf_expr ρ e2 with
  | Some tp1, Some tp2 => if typ_beq tp1 tp2 then Some TpBool else None
  | _, _ => None
  end
| IfE e1 e2 e3 =>
  match inf_expr ρ e1, inf_expr ρ e2, inf_expr ρ e3 with
  | Some TpBool, Some tp2, Some tp3 => if typ_beq tp2 tp3 then Some tp2 else None
  | _, _, _ => None
  end
| _ => None
end.

(* An expression is well-defined under type context ρ iff type inference succeeds. *)
Definition expr_well_defined (ρ : pvar_typs) (e : lang.expr) : Prop :=
  ∃ tp, inf_expr ρ e = Some tp.

(* Separate type-checking judgment for procedure-call arguments: each argument
   expression's inferred type must match the corresponding formal parameter's
   declared type. Kept independent of RavenHoareTriple/stmt_well_defined's other
   rules so type-checking and verification stay cleanly separated. *)
Definition proc_call_args_well_typed (ρ : pvar_typs) (args : list lang.expr) (proc_entry : ProcRecord) : Prop :=
  Forall2 (fun arg arg_decl => inf_expr ρ arg = Some (snd arg_decl)) args (proc_args_of proc_entry).

(* The callee's own declared type for its "#ret_val" local
   (pwf_proc_ret_val_declared guarantees it's present as a key) -- shared by
   proc_call_ret_well_typed below (the static half: the caller's LHS
   variable must match it) and by all_proc_specs_valid_raven/
   all_proc_specs_valid_iris in trnsl.v (the dynamic half: the value
   actually placed in "#ret_val" at return must match it too). *)
Definition proc_ret_typ_opt (proc_entry : ProcRecord) : option typ :=
  (list_to_map (proc_locals_of proc_entry) : gmap var typ) !! "#ret_val".

(* A procedure's own pvar-typing context, built from its own declared args
   and locals -- the callee-side analogue of proc_ret_typ_opt/
   proc_call_ret_well_typed's own "type via the record, not a global slot"
   design (see that pair's comment), generalized from just "#ret_val" to
   every one of a procedure's own variable names. Used by
   all_proc_specs_valid_raven (in place of a single, externally-supplied
   pvar_typs shared by the whole program) so that two procedures reusing
   the same argument/local name -- most unavoidably "#ret_val" itself,
   which every procedure must declare -- never need to agree on its type.
   The fallback (TpUnit) is never actually consulted: a procedure's own
   RavenHoareTriple derivation only ever references its own declared
   names, per stmt_well_defined/RavenHoareTriple's own well-formedness
   discipline. *)
Definition proc_pvar_typs (proc_record : ProcRecord) : pvar_typs :=
  fun v => match (list_to_map (proc_args_of proc_record ++ proc_locals_of proc_record) : gmap var typ) !! v with
           | Some t => t
           | None => TpUnit
           end.

(* Symmetric to proc_call_args_well_typed, for the call's own LHS variable:
   treated like an out-argument, typed via the callee's own declared
   "#ret_val" local -- not via a global pvar-typing slot (rho "#ret_val"
   would force every procedure in the whole program to share one return
   type). *)
Definition proc_call_ret_well_typed (ρ : pvar_typs) (v : var) (proc_entry : ProcRecord) : Prop :=
  match proc_ret_typ_opt proc_entry with
  | Some ret_typ => ρ v = ret_typ
  | None => False
  end.

Inductive stmt_well_defined : pvar_typs -> stmt -> Prop :=
| SeqTp ρ s1 s2 :
  stmt_well_defined ρ s1 ->
  stmt_well_defined ρ s2 ->
  stmt_well_defined ρ (Seq s1 s2)
(* | ReturnTp e :
    expr_well_defined ρ e ->
    stmt_well_defined (Return e) *)
| IfSTp ρ e s1 s2 :
    expr_well_defined ρ e ->
    stmt_well_defined ρ s1 ->
    stmt_well_defined ρ s2 ->
    stmt_well_defined ρ (IfS e s1 s2)
| AssignTp ρ v e:
    expr_well_defined ρ e ->
    stmt_well_defined ρ (Assign v e)
(* | FreeTp e:
    expr_well_defined ρ e ->
    stmt_well_defined (Free e) *)
| SkipSTp ρ : stmt_well_defined ρ (SkipS)
| StuckSTp ρ : stmt_well_defined ρ (StuckS)
(* | ExprSTp e:
    expr_well_defined ρ e ->
    stmt_well_defined (ExprS e) *)
| CallTp ρ v proc proc_entry args:
    proc ∈ proc_set ->
    proc_map !! proc = Some proc_entry ->
    length args = length (proc_args_of proc_entry) ->
    (Forall (fun arg => expr_well_defined ρ arg) args) ->
    proc_call_args_well_typed ρ args proc_entry ->
    proc_call_ret_well_typed ρ v proc_entry ->
    stmt_well_defined ρ (Call v proc args)
| FldWrTp ρ v fld e2:
    (fld ∈ fld_set) ->
    expr_well_defined ρ e2 ->
    stmt_well_defined ρ (FldWr v fld e2)
| FldRdTp ρ v e fld:
    fld ∈ fld_set ->
    expr_well_defined ρ e ->
    stmt_well_defined ρ (FldRd v e fld)
| CASTp ρ v e1 fld e2 e3:
    fld ∈ fld_set ->
    expr_well_defined ρ e1 ->
    expr_well_defined ρ e2 ->
    expr_well_defined ρ e3 ->
    stmt_well_defined ρ (CAS v e1 fld e2 e3)
| AllocTp ρ v fs:
    Forall (fun fld_v => (fst fld_v) ∈ fld_set) fs ->
    stmt_well_defined ρ (Alloc v fs)
| SpawnTp ρ proc args:
    proc ∈ proc_set ->
    Forall (fun arg => expr_well_defined ρ arg) args ->
    stmt_well_defined ρ (Spawn proc args)
| UnfoldPredTp ρ pred args :
    pred ∈ pred_set ->
    Forall (fun arg => expr_well_defined ρ arg) args ->
    stmt_well_defined ρ (UnfoldPred pred args)
| FoldPredTp ρ pred args :
    pred ∈ pred_set ->
    Forall (fun arg => expr_well_defined ρ arg) args ->
    stmt_well_defined ρ (FoldPred pred args)
| InvAccessBlockTp ρ inv args stmt:
    inv ∈ inv_set ->
    Forall (fun arg => expr_well_defined ρ arg) args ->
    stmt_well_defined ρ stmt ->
    stmt_well_defined ρ (InvAccessBlock inv args stmt)

| FoldInvTp ρ inv args :
    inv ∈ inv_set ->
    Forall (fun arg => expr_well_defined ρ arg) args ->
    stmt_well_defined ρ (FoldInv inv args)
| AssertTp ρ e :
    expr_well_defined ρ e ->
    stmt_well_defined ρ (Assert e)
| FpuTp ρ e fld RAPack old_val new_val :
    fld ∈ fld_set ->
    expr_well_defined ρ e ->
    stmt_well_defined ρ (Fpu e fld RAPack  old_val new_val)
.

Lemma alloc_stmt_well_defined ρ x fld val fld_vals :
  stmt_well_defined ρ (Alloc x ((fld, val) :: fld_vals)) -> stmt_well_defined ρ (Alloc x fld_vals).
Proof.
  intros H.
  inversion H.
  apply (AllocTp ρ x fld_vals).
  inversion H2. exact H7.
Qed.

(* Isolated, single-use extraction of CallTp's proc_call_ret_well_typed
   premise, keyed to an already-known proc_entry (via Some-injectivity on
   proc_map's lookup) rather than CallTp's own existentially-bound one --
   lets call sites avoid threading this through the large, already-fragile
   auto-numbered "inversion Hwelldef; subst ..." used elsewhere for Call's
   soundness case. *)
Lemma stmt_well_defined_call_ret_typed ρ v proc args proc_entry :
  stmt_well_defined ρ (Call v proc args) ->
  proc_map !! proc = Some proc_entry ->
  proc_call_ret_well_typed ρ v proc_entry.
Proof.
  intros Hwd Hpm.
  inversion Hwd; subst.
  match goal with
  | Hpm' : proc_map !! proc = Some ?proc_entry', Hret : proc_call_ret_well_typed ρ v ?proc_entry' |- _ =>
    rewrite Hpm in Hpm'; injection Hpm' as <-; exact Hret
  end.
Qed.

Section AtomicAnnotations.
  Inductive AtomicStep : Type :=
  | Closed
  | Opened (S : list (inv_name * list LExpr))
  | Stepped (S : list (inv_name * list LExpr))
  .

  Definition AtomicAnnotation : Type := (gset inv_name * AtomicStep).

  Definition maskAnnot : Type := gset inv_name.

End AtomicAnnotations.

    Definition trnsl_lval (v: val) : lang.val :=
    match v with
    | LitBool b => (lang.LitBool b)
    | LitInt i => (lang.LitInt i)
    | LitUnit => (lang.LitUnit)
    | LitLoc l => (lang.LitLoc (lang.Loc l.(loc_car)))
    | LitRAElem p => lang.LitRAElem p
    end.

    Lemma trnsl_lval_injective v1 v2 : trnsl_lval v1 = trnsl_lval v2 -> v1 = v2.
    Proof.
      destruct v1 eqn:Hv1, v2 eqn:Hv2; try discriminate.
      - simpl; intros; inversion H. done.
      - simpl; intros; inversion H. done.
      - simpl; intros; inversion H. done.
      - simpl; intros. inversion H. destruct l, l0. simpl in H1; subst loc_car0. done.
      - simpl; intros; inversion H. done.
    Qed.

    Lemma trnsl_lval_trnsl_val_inverse y: trnsl_lval (trnsl_val y) = y.
    Proof.
      destruct y eqn:Hy; try simpl; try done.
      destruct l. simpl. done.
    Qed.

    (* Every rrl val v satisfies: trnsl_val (trnsl_lval v) = v *)
    Lemma trnsl_val_trnsl_lval_inverse (v : val) : trnsl_val (trnsl_lval v) = v.
    Proof.
      destruct v; simpl; try done.
      destruct l. simpl. done.
    Qed.

    (* val_beq and bool_decide agree modulo trnsl_lval *)
    Lemma val_beq_bool_decide (v1 v2 : val) :
      val_beq v1 v2 = bool_decide (trnsl_lval v1 = trnsl_lval v2).
    Proof.
      destruct (val_beq v1 v2) eqn:Hbeq.
      - symmetry. apply bool_decide_true.
        apply internal_val_dec_bl in Hbeq. rewrite Hbeq. done.
      - symmetry. apply bool_decide_false.
        intro Heq. apply trnsl_lval_injective in Heq.
        apply internal_val_dec_lb in Heq. rewrite Heq in Hbeq. discriminate.
    Qed.

    Definition stack: Type := gmap lang.var lvar.

    Definition symb_stk_to_stk_frm (stk : stack) (mp : symb_map) : stack_frame :=
      StackFrame (fmap (λ v, trnsl_lval (mp v)) stk).

    (* Given a richness guarantee on σ (enough distinct lvars of any type,
       avoiding any finite exclusion set), pick a list of distinct lvars
       matching a list of declared types -- used to synthesize a procedure's
       own entry stack out of fresh (not globally shared) lvar names, one per
       formal arg / local variable, so that different procedures' same-named
       parameters never need to agree on a single global type via σ. *)
    Lemma fresh_lvars_list (σ : lvar_typs)
        (Hrich : ∀ (t : typ) (excl : gset lvar), ∃ lv, lv ∉ excl ∧ ¬ is_reserved lv ∧ σ lv = t)
        (decls : list (var * typ)) (excl0 : gset lvar) :
      ∃ lvs : list lvar,
        length lvs = length decls ∧
        Forall2 (fun decl lv => σ lv = snd decl) decls lvs ∧
        NoDup lvs ∧
        Forall (fun lv => lv ∉ excl0) lvs ∧
        Forall (fun lv => ¬ is_reserved lv) lvs.
    Proof using G.
      revert excl0. induction decls as [| [v tp] decls IH]; intros excl0.
      - exists []. repeat split; try constructor.
      - destruct (Hrich tp excl0) as [lv [Hlv_notin [Hlv_res Hlv_typ]]].
        destruct (IH ({[lv]} ∪ excl0)) as [lvs [Hlen [HF2 [Hnodup [Hexcl Hres]]]]].
        exists (lv :: lvs). repeat split.
        + simpl. lia.
        + constructor; [exact Hlv_typ | exact HF2].
        + constructor.
          * intro Hin. eapply (proj1 (Forall_forall _ _)) in Hexcl; [| exact Hin]. set_solver.
          * exact Hnodup.
        + constructor.
          * exact Hlv_notin.
          * eapply Forall_impl; [exact Hexcl |]. intros lv' Hlv'. set_solver.
        + constructor.
          * exact Hlv_res.
          * exact Hres.
    Qed.

    (* A pair of lvar lists that is a legal fresh entry-stack for calling
       proc_record under σ: right length and σ-typed against proc_record's
       args/locals declarations, each list duplicate-free, and the two
       mutually disjoint. Parametric in σ and proc_record so that every
       well-formedness condition a synthesized "args ⊎ locals" entry stack
       must satisfy for that specific call lives in the type itself, rather
       than as separate side-conditions threaded wherever such a pair is
       used. *)
    Record proc_entry_lvars (σ : lvar_typs) (proc_record : ProcRecord) := ProcEntryLvars {
      dll_args : list lvar;
      dll_locals : list lvar;
      dll_args_len : length dll_args = length (proc_args_of proc_record);
      dll_locals_len : length dll_locals = length (proc_locals_of proc_record);
      dll_args_typed : Forall2 (fun decl lv => σ lv = snd decl) (proc_args_of proc_record) dll_args;
      dll_locals_typed : Forall2 (fun decl lv => σ lv = snd decl) (proc_locals_of proc_record) dll_locals;
      dll_args_nodup : NoDup dll_args;
      dll_locals_nodup : NoDup dll_locals;
      dll_disjoint : ∀ lv, lv ∈ dll_args → lv ∉ dll_locals;
      (* Entry lvars are never reserved -- lets raven_soundness's own
         precond/postcond bridging build subst_map_avoids_reserved facts
         for the symbolic (LVar-valued) substitution map it builds out of
         dll_args. *)
      dll_args_not_reserved : Forall (fun lv => ¬ is_reserved lv) dll_args;
      dll_locals_not_reserved : Forall (fun lv => ¬ is_reserved lv) dll_locals;
    }.
    Global Arguments dll_args {_ _}.
    Global Arguments dll_locals {_ _}.
    Global Arguments dll_args_len {_ _}.
    Global Arguments dll_locals_len {_ _}.
    Global Arguments dll_args_typed {_ _}.
    Global Arguments dll_locals_typed {_ _}.
    Global Arguments dll_args_nodup {_ _}.
    Global Arguments dll_locals_nodup {_ _}.
    Global Arguments dll_disjoint {_ _}.
    Global Arguments dll_args_not_reserved {_ _}.
    Global Arguments dll_locals_not_reserved {_ _}.

    (* fresh_lvars_list, applied twice (locals avoiding the args' own
       choices) and packaged into a proc_entry_lvars for proc_record. *)
    Lemma fresh_proc_entry_lvars (σ : lvar_typs)
        (Hrich : ∀ (t : typ) (excl : gset lvar), ∃ lv, lv ∉ excl ∧ ¬ is_reserved lv ∧ σ lv = t)
        (proc_record : ProcRecord) :
      ∃ dll : proc_entry_lvars σ proc_record, Logic.True.
    Proof using G.
      destruct (fresh_lvars_list σ Hrich (proc_args_of proc_record) ∅)
        as (args_lvs & Hargs_len & Hargs_typed & Hargs_nodup & _ & Hargs_res).
      destruct (fresh_lvars_list σ Hrich (proc_locals_of proc_record) (list_to_set args_lvs))
        as (locals_lvs & Hlocals_len & Hlocals_typed & Hlocals_nodup & Hlocals_excl & Hlocals_res).
      have Hdisjoint : ∀ lv, lv ∈ args_lvs → lv ∉ locals_lvs.
      { intros lv Hin1 Hin2.
        pose proof (proj1 (Forall_forall (λ lv0, lv0 ∉ list_to_set args_lvs) locals_lvs) Hlocals_excl lv Hin2) as Hcontra.
        apply Hcontra. rewrite elem_of_list_to_set. exact Hin1. }
      exists (ProcEntryLvars σ proc_record args_lvs locals_lvs Hargs_len Hlocals_len Hargs_typed Hlocals_typed
                Hargs_nodup Hlocals_nodup Hdisjoint Hargs_res Hlocals_res).
      exact Logic.I.
    Qed.

    (* Reconstructs the exact operational stack_frame -- the frame a fresh
       call/spawn produces (see lang.v's RTCallStep/SpawnStep) -- from a
       synthesized entry stack built out of fresh, distinct lvars: given
       names/lvs/vals aligned positionally, LStack (list_to_map (zip names
       lvs)) read through the mp overridden at each lv to the corresponding
       (translated) val equals exactly StackFrame (list_to_map (zip names
       vals)). *)
    Lemma symb_stk_to_stk_frm_general
        (names : list var) (lvs : list lvar) (vals : list lang.val) (mp : symb_map)
        (Hnodup_names : NoDup names) (Hnodup_lvs : NoDup lvs)
        (Hlen1 : length names = length lvs) (Hlen2 : length names = length vals) :
      symb_stk_to_stk_frm (assoc_map names lvs)
        (fun lv => match (assoc_map lvs vals : gmap lvar lang.val) !! lv with
                   | Some v => trnsl_val v | None => mp lv end)
      = StackFrame (assoc_map names vals).
    Proof.
      unfold symb_stk_to_stk_frm. f_equal.
      apply map_eq. intro v.
      rewrite lookup_fmap.
      destruct ((list_to_map (zip names lvs) : gmap var lvar) !! v) as [lv|] eqn:Hstk0.
      - rewrite Hstk0.
        have Hstk0' := Hstk0.
        apply elem_of_list_to_map_2 in Hstk0'.
        apply elem_of_list_lookup_1 in Hstk0' as [i Hi].
        rewrite lookup_zip_with in Hi.
        destruct (names !! i) as [v'|] eqn:Hnv; [| discriminate].
        destruct (lvs !! i) as [lv'|] eqn:Hlvi; [| discriminate].
        simpl in Hi. injection Hi as Heq1 Heq2. subst v'. subst lv'.
        have Hval_i : is_Some (vals !! i).
        { apply lookup_lt_is_Some_2. rewrite <- Hlen2. eapply (lookup_lt_Some names). exact Hnv. }
        destruct Hval_i as [valv Hval_i].
        have Hlv_lookup : (list_to_map (zip lvs vals) : gmap lvar lang.val) !! lv = Some valv.
        { apply elem_of_list_to_map_1.
          - rewrite (fst_zip _ _ (Nat.eq_le_incl _ _ (eq_trans (eq_sym Hlen1) Hlen2))). exact Hnodup_lvs.
          - apply (elem_of_list_lookup_2 _ i). rewrite lookup_zip_with Hlvi Hval_i. done. }
        simpl. rewrite Hlv_lookup. simpl. rewrite trnsl_lval_trnsl_val_inverse.
        symmetry. apply elem_of_list_to_map_1.
        + rewrite (fst_zip _ _ (Nat.eq_le_incl _ _ Hlen2)). exact Hnodup_names.
        + apply (elem_of_list_lookup_2 _ i). rewrite lookup_zip_with Hnv Hval_i. done.
      - rewrite Hstk0. simpl.
        symmetry. apply not_elem_of_list_to_map_1.
        rewrite (fst_zip _ _ (Nat.eq_le_incl _ _ Hlen2)).
        apply not_elem_of_list_to_map_2 in Hstk0.
        rewrite (fst_zip _ _ (Nat.eq_le_incl _ _ Hlen1)) in Hstk0.
        exact Hstk0.
    Qed.

    (* Constructively extracts a list of witness values (with their typing)
       from a "every declared name has some value of the right shape" fact --
       no choice axiom needed since decls is a concrete, finite list. *)
    Lemma extract_present_vals (decls : list (var * typ)) (frm_locals : gmap var lang.val) :
      (∀ v tp, (v, tp) ∈ decls -> ∃ val, frm_locals !! v = Some val ∧ typeOf val = tp) ->
      ∃ vals : list lang.val,
        Forall2 (fun decl val => frm_locals !! (fst decl) = Some val) decls vals ∧
        Forall2 (fun decl val => typeOf val = snd decl) decls vals.
    Proof.
      induction decls as [| [v tp] rest IH]; intros Hpresent.
      - exists []. split; constructor.
      - destruct (Hpresent v tp (elem_of_list_here _ _)) as [val [Hval Hty]].
        have IHpremise : ∀ v' tp', (v', tp') ∈ rest -> ∃ val, frm_locals !! v' = Some val ∧ typeOf val = tp'.
        { intros v' tp' Hin. apply (Hpresent v' tp'). apply elem_of_cons. right. exact Hin. }
        destruct (IH IHpremise) as [vals [HF2 HF2ty]].
        exists (val :: vals). split; constructor; try done.
    Qed.

    (* Combines two Forall2 facts sharing the same left-hand list, pointwise,
       into a single Forall2 relating their right-hand lists. *)
    Lemma Forall2_combine {A B C : Type} (P1 : A -> B -> Prop) (P2 : A -> C -> Prop) (Q : B -> C -> Prop)
        (decls : list A) (xs : list B) (ys : list C) :
      (∀ a b c, P1 a b -> P2 a c -> Q b c) ->
      Forall2 P1 decls xs -> Forall2 P2 decls ys -> Forall2 Q xs ys.
    Proof.
      intros HQ HF1. revert ys. induction HF1 as [| a b decls' xs' Hp1 Hrest IH]; intros ys HF2.
      - apply Forall2_nil_inv_l in HF2. subst ys. constructor.
      - destruct ys as [| c ys']; [exfalso; exact (Forall2_cons_nil_inv _ _ _ HF2) |].
        apply Forall2_cons_1 in HF2 as [Hp2 Hrest2].
        constructor; [exact (HQ a b c Hp1 Hp2) | exact (IH ys' Hrest2)].
    Qed.


  Fixpoint trnsl_expr_lExpr (stk: stack) (e: lang.expr) :=
  match e with
  | Var x => match stk !! x with
             | Some v => Some (LVar v)
             | None => None
             end
  | Val v => Some (LVal (trnsl_val v))
  | UnOp op e => 
      match trnsl_expr_lExpr stk e with
      | Some le => Some (LUnOp op le)
      | None => None
      end
  | BinOp op e1 e2 => 
    match (trnsl_expr_lExpr stk e1), (trnsl_expr_lExpr stk e2) with
    | Some le1, Some le2 => Some (LBinOp op le1 le2)
    | _, _ => None
    end

  | IfE e1 e2 e3 =>
    match (trnsl_expr_lExpr stk e1), (trnsl_expr_lExpr stk e2), (trnsl_expr_lExpr stk e3) with
    | Some le1, Some le2, Some le3 => Some (LIfE le1 le2 le3)
    | _, _, _ => None
    end

  | StuckE => Some LStuck
  end.

  (* Free variables of a translated expression are contained in range(stk) *)
  Lemma trnsl_expr_lExpr_fvars_range (stk : stack) (e : lang.expr) (le : LExpr) :
    trnsl_expr_lExpr stk e = Some le →
    ∀ v, v ∈ lexpr_fvars le → ∃ k, stk !! k = Some v.
  Proof.
    revert le.
    induction e; simpl; intros le Htrnsl lv Hlv.
    - destruct (stk !! x) as [lv'|] eqn:Hstk; [| discriminate].
      injection Htrnsl as <-. simpl in Hlv. apply elem_of_singleton in Hlv. subst lv'. eauto.
    - injection Htrnsl as <-. simpl in Hlv. exfalso. exact (not_elem_of_empty _ Hlv).
    - destruct (trnsl_expr_lExpr stk e) as [le'|] eqn:Hle'; [| discriminate].
      injection Htrnsl as <-. simpl in Hlv. exact (IHe le' eq_refl lv Hlv).
    - destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [| discriminate].
      destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [| discriminate].
      injection Htrnsl as <-. simpl in Hlv.
      apply elem_of_union in Hlv as [Hlv1 | Hlv2].
      + exact (IHe1 le1 eq_refl lv Hlv1).
      + exact (IHe2 le2 eq_refl lv Hlv2).
    - destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [| discriminate].
      destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [| discriminate].
      destruct (trnsl_expr_lExpr stk e3) as [le3|] eqn:Hle3; [| discriminate].
      injection Htrnsl as <-. simpl in Hlv.
      apply elem_of_union in Hlv as [Hlv12 | Hlv3].
      + apply elem_of_union in Hlv12 as [Hlv1 | Hlv2].
        * exact (IHe1 le1 eq_refl lv Hlv1).
        * exact (IHe2 le2 eq_refl lv Hlv2).
      + exact (IHe3 le3 eq_refl lv Hlv3).
    - injection Htrnsl as <-. simpl in Hlv. exfalso. exact (not_elem_of_empty _ Hlv).
  Qed.

  (* Translating against a renamed stack yields the renamed translation --
     the key commutation fact the renaming theorem needs to transport
     trnsl_expr_lExpr premises across a derivation. *)
  Lemma trnsl_expr_lExpr_rename (ren : lvar -> lvar) (stk : stack) (e : lang.expr) (le : LExpr) :
    trnsl_expr_lExpr stk e = Some le →
    trnsl_expr_lExpr (ren <$> stk) e = Some (rename_lexpr ren le).
  Proof.
    revert le.
    induction e; simpl; intros le Htrnsl.
    - destruct (stk !! x) as [lv'|] eqn:Hstk; [| discriminate].
      injection Htrnsl as <-. rewrite lookup_fmap Hstk. reflexivity.
    - injection Htrnsl as <-. reflexivity.
    - destruct (trnsl_expr_lExpr stk e) as [le'|] eqn:Hle'; [| discriminate].
      injection Htrnsl as <-. simpl. rewrite (IHe le' eq_refl). reflexivity.
    - destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [| discriminate].
      destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [| discriminate].
      injection Htrnsl as <-. simpl.
      rewrite (IHe1 le1 eq_refl) (IHe2 le2 eq_refl). reflexivity.
    - destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [| discriminate].
      destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [| discriminate].
      destruct (trnsl_expr_lExpr stk e3) as [le3|] eqn:Hle3; [| discriminate].
      injection Htrnsl as <-. simpl.
      rewrite (IHe1 le1 eq_refl) (IHe2 le2 eq_refl) (IHe3 le3 eq_refl). reflexivity.
    - injection Htrnsl as <-. reflexivity.
  Qed.

  (* List-of-arguments specialization, for the RavenHoareTriple rules whose
     own arg-translation premise has this map-of-Some shape (ProcCallRuleRet,
     InvAccessBlockRule, InvAllocRule, PredUnfoldRule, PredFoldRule). *)
  Lemma trnsl_expr_lExpr_rename_list (ren : lvar -> lvar) (stk : stack)
      (args : list lang.expr) (lexprs : list LExpr) :
    map (fun arg => trnsl_expr_lExpr stk arg) args = map (fun le => Some le) lexprs →
    map (fun arg => trnsl_expr_lExpr (ren <$> stk) arg) args =
    map (fun le => Some le) (map (rename_lexpr ren) lexprs).
  Proof.
    revert lexprs.
    induction args as [| a args IH]; intros lexprs Heq; destruct lexprs as [| le lexprs]; simpl in *;
      try discriminate.
    - reflexivity.
    - injection Heq as Ha Hargs.
      rewrite (trnsl_expr_lExpr_rename ren stk a le Ha).
      rewrite (IH lexprs Hargs).
      reflexivity.
  Qed.

  Inductive trnsl_stmt_ret :=
  | None'
  | Error
  | Some' (s: lang.stmt).
  
  Fixpoint trnsl_atomic_block (body : stmt) (step_taken : bool) : trnsl_stmt_ret * bool := 
  match body, step_taken with
  | Seq s1 s2, _ =>
    match trnsl_atomic_block s1 step_taken with
    | (None', step_taken') => trnsl_atomic_block s2 step_taken'
    | (Some' s1, step_taken') => 
      match trnsl_atomic_block s2 step_taken' with
      | (None', step_taken'') => (Some' s1, step_taken'')
      | (Some' s2, step_taken'') => (Some' (lang.Seq s1 s2), step_taken'')
      | (Error, _) => (Error, step_taken')
      end
    | (Error, _) => (Error, step_taken)
    end

  | IfS e s1 s2, _ =>
    match trnsl_atomic_block s1 step_taken, trnsl_atomic_block s2 step_taken with
    | (None', step_taken'), (None', step_taken'') => (None', step_taken' || step_taken'')
    | (None', step_taken'), (Some' s2, step_taken'') => (Some' (lang.IfS e lang.SkipS s2), step_taken' || step_taken'')
    | (Some' s1, step_taken'), (None', step_taken'') => (Some' (lang.IfS e s1 lang.SkipS), step_taken' || step_taken'')
    | (Some' s1, step_taken'), (Some' s2, step_taken'') => (Some' (lang.IfS e s1 s2), step_taken' || step_taken'')
    | (Error, _), _ | _, (Error, _) => (Error, step_taken)
    end

  | Assign v e, false => (Some' (lang.Assign v e), true)
  | Assign v e, true => (Error, true)

  | SkipS, false => (Some' lang.SkipS, true)
  | SkipS, true => (Error, true)

  | StuckS, false => (Some' lang.StuckS, true)
  | StuckS, true => (Error, true)

  | Call v proc args, _ => (Error, true)

  | FldWr v fld e2, false => (Some' (lang.FldWr v fld e2), true)
  | FldWr v fld e2, true => (Error, true)

  | FldRd v e fld, false => (Some' (lang.FldRd v e fld), true)
  | FldRd v e fld, true => (Error, true)

  | CAS v e1 fld e2 e3, false => (Some' (lang.CAS v e1 fld e2 e3), true)
  | CAS v e1 fld e2 e3, true => (Error, true)

  | Alloc v fs, false => (Some' (lang.Alloc v fs), true)
  | Alloc v fs, true => (Error, true)

  | Spawn proc args, false => (Some' (lang.Spawn proc args), true)
  | Spawn proc args, true => (Error, true)
  | InvAccessBlock inv args body, _ => trnsl_atomic_block body step_taken
  | _, _ => (None', step_taken)
  end.

  Fixpoint trnsl_stmt (s : stmt) : trnsl_stmt_ret := match s with
  | Seq s1 s2 => 
    match trnsl_stmt s1, trnsl_stmt s2 with
    | None', None' => None'
    | Some' s1, None' => Some' s1
    | None', Some' s2 => Some' s2
    | Some' s1', Some' s2' => Some' (stmt_append s1' s2' )
    | Error, _
    | _, Error => Error
    end

  | IfS e s1 s2 => 
      match (trnsl_stmt s1), (trnsl_stmt s2) with
      | None', None' => None'
      | Some' s1, None' => Some' (lang.IfS e s1 lang.SkipS)
      | None', Some' s2 => Some' (lang.IfS e lang.SkipS s2 )
      | Some' s1, Some' s2 => Some' (lang.IfS e s1 s2) 
      | Error, _ | _, Error => Error
      end

  | Assign v e => Some' (lang.Assign v e)
  | SkipS => Some' (lang.SkipS)
  | StuckS => Some' lang.StuckS
  | Call v proc args => Some' (lang.Call v proc args)
  | FldWr v fld e2 => Some' (lang.FldWr v fld e2)
  
  | FldRd v e1 fld => Some' (lang.FldRd v e1 fld)
  | CAS v e1 fld e2 e3 => Some' (lang.CAS v e1 fld e2 e3)
  | Alloc v fs => Some' (lang.Alloc v fs)
  | Spawn proc args => Some' (lang.Spawn proc args)
  
  | UnfoldPred pred args => None'
  | FoldPred pred args => None'
  | InvAccessBlock inv args body => (trnsl_atomic_block body false).1

  | FoldInv inv args => None'
  | Assert e => None'
  | Fpu e fld RAPack old_val new_val => None'
  end.

(* Every registered procedure's own body actually translates -- ruling out
   trnsl_stmt (proc_body_of r) = Error, which ProcCallRuleRet's soundness
   case needs (a well-formed callee's body is, definitionally, one that
   compiles; malformed statements should never have made it into proc_map in
   the first place). Stated standalone (not a ProgramWF field) because
   trnsl_stmt isn't defined yet at ProgramWF's own point in the file. An
   explicit premise of raven_soundness, same status as ProgramWF itself. *)
Definition proc_bodies_translate : Prop :=
  map_Forall (λ _ r, trnsl_stmt (proc_body_of r) ≠ Error) proc_map.

  Ltac proj_fst H := (apply f_equal with (f := fst) in H).
  Ltac proj_snd H := (apply f_equal with (f := snd) in H).

  (* Monotonicity for Some' *)
  Lemma trnsl_atomic_step_monotone (s : stmt)  :
    (forall stmt1 stmt2 stp1 stp2, 
        trnsl_atomic_block s true = (stmt1, stp1) ->
        trnsl_atomic_block s false = (stmt2, stp2) ->
        not (stmt1 = Error) ->
        stmt1 = stmt2 /\ (stp2 -> stp1)).
  Proof.
    induction s.
    all: intros.

    1: { (* Seq *)
      simpl in H, H0.

      destruct (trnsl_atomic_block s1 true) eqn:E1;
      destruct (trnsl_atomic_block s1 false) eqn:E2.
      specialize (IHs1 t t0 b b0 eq_refl eq_refl).

      destruct t eqn:Ht, t0 eqn:Ht0.
        all:
          try (specialize (IHs1 ltac:(intros Htemp'; discriminate)) as [IHs1stmt IHs1stp]; try done).
        all:
          try (inversion H; subst; contradiction).

      - destruct b, b0.
        ** rewrite H  in H0. inversion H0; subst. done.
        ** specialize (IHs2 stmt1 stmt2 stp1 stp2 H H0 H1) as IHs2Sp. done.
        ** exfalso. apply IHs1stp. done.
        ** rewrite H in H0. inversion H0; subst. done.

      - destruct b, b0; inversion IHs1stmt; subst.
        ** rewrite H in H0. inversion H0. done.
        ** destruct (trnsl_atomic_block s2 true) eqn:Htrnsl_s2;
          destruct (trnsl_atomic_block s2 false) eqn:Htrnsl_s2'.

          specialize (IHs2 t t0 b b0 eq_refl eq_refl).
          
          destruct t eqn:Ht, t0 eqn:Ht0. 
          all: 
            inversion H; inversion H0; subst; 
            try (specialize (IHs2 ltac:(intros Htemp; discriminate)) as [IHs2Stmt IHs2stp]; split; try done); 
            try done.
          
          inversion IHs2Stmt; subst. done.

        ** exfalso. apply IHs1stp; done.
        ** destruct (trnsl_atomic_block s2 false) eqn:Htrnsl_s2.
          destruct (trnsl_atomic_block s2 true) eqn:Htrnsl_s2'.

          specialize (IHs2 t0 t b0 b eq_refl eq_refl).

          destruct t0 eqn:Ht0, t eqn:Ht. 
          all: 
            inversion H; inversion H0; subst; 
            try (specialize (IHs2 ltac:(intros [Htemp Htemp']; discriminate)) as [IHs2Stmt IHs2stp]; split; try done); 
            try done.
    }

    1: { (* IfS *)
      simpl in H, H0.

        destruct (trnsl_atomic_block s1 true) eqn: E1.
        destruct (trnsl_atomic_block s1 false) eqn:E2.

        specialize (IHs1 t t0 b b0 eq_refl eq_refl).

        destruct t eqn:Ht, t0 eqn:Ht0.
        all:
          try (specialize (IHs1 ltac:(intros Htemp'; discriminate)) as [IHs1stmt IHs1stp]; try done).
        
        all:
          (destruct (trnsl_atomic_block s2 true) eqn:F1;
          destruct (trnsl_atomic_block s2 false) eqn:F2;
          specialize (IHs2 t1 t2 b1 b2 eq_refl eq_refl);  
          destruct t1 eqn:Ht1, t2 eqn:Ht2;
          try (specialize (IHs2 ltac:(intros Htemp; discriminate)) as [IHs2stmt IHs2stp]; try done)
          ).

        all:
            (inversion H; inversion H0; subst; split; try done).
        + destruct b0, b; intuition.
        + inversion IHs2stmt; subst; done.
        + destruct b0, b2; intuition.
        + inversion IHs1stmt; subst; done.
        + destruct b0, b2; auto.
        + inversion IHs1stmt; inversion IHs2stmt; subst; done.
        + destruct b0, b2; auto.
    }

    all: simpl in *; inversion H; inversion H0; subst; try done.
    
    apply IHs; done.
  Qed.

  Definition P_some (c : stmt) :=
    forall stmt' step_taken,
      (trnsl_atomic_block c step_taken).1 = Some' stmt' ->
      trnsl_stmt c = Some' stmt'.

  Definition P_none (c : stmt) :=
    forall step_taken,
      (trnsl_atomic_block c step_taken).1 = None' ->
      trnsl_stmt c = None'.

  Lemma trnsl_stmt_trnsl_atomic_block_some_none_mutual :
    forall c, (P_some c /\ P_none c).
  Proof.
    apply (stmt_ind (fun c => P_some c /\ P_none c)).
    all: intros; simpl in *.

    Ltac solve_split_case :=
      split;
      [ (* P_some *)
        intros stmt' step_taken H;
        simpl in H;
        destruct step_taken; try discriminate H; rewrite <- H; try done
      | (* P_none *)
        intros step_taken H;
        simpl in H;
        destruct step_taken; try discriminate H; try done
      ].

    (* All atomic steps *)
    all: try (solve_split_case).
        
    1: { (* Seq*)
      destruct H as [IHsome1 IHnone1].
      destruct H0 as [IHsome2 IHnone2].
      split.
      + (* --- P_some --- *)
        intros stmt' step_taken H.
        simpl in H.
        destruct (trnsl_atomic_block s1 step_taken) as [[| | ] step1] eqn:H1;
        simpl in H.
        ++ (* case (None', step1) *)
          unfold P_none in IHnone1. 
          proj_fst H1.
          specialize (IHnone1 step_taken H1) as Hs1.
          simpl. 
          rewrite Hs1.
          unfold P_some in IHsome2. apply IHsome2 in H. rewrite H. done.

        ++ discriminate H.
        
        ++ (* case (Some' s1', step1) *)
          unfold P_some in IHsome1.
          proj_fst H1.
          specialize (IHsome1 s step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_some in IHsome2. 
          destruct (trnsl_atomic_block s2 step1) as [[| | ] step2] eqn:H2.
          ** proj_fst H2. 
            specialize (IHnone2 step1 H2) as Hs2. rewrite Hs2. done.

          ** discriminate H.

          **  proj_fst H2. specialize (IHsome2 s0 step1 H2) as Hs2. rewrite Hs2.
          simpl in H. rewrite H. done.

      + (* --- P_none --- *)
        intros step_taken H.
        simpl in H.
        destruct (trnsl_atomic_block s1 step_taken) as [[| | ] step1] eqn:H1;
        simpl in H.
        ++ (* case (None', step1) *)
          unfold P_none in IHnone1.
          proj_fst H1.
          specialize (IHnone1 step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_none in IHnone2.
          apply IHnone2 in H. rewrite H. done.

        ++ (* case (Error, step1) *)
          discriminate H.

        ++ (* case (Some' s1', step1) *)
          unfold P_some in IHsome1.
          proj_fst H1.
          specialize (IHsome1 s step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          destruct (trnsl_atomic_block s2 step1) as [[| | ] step2] eqn:H2;
          simpl in H.
          ** (* (None', step2) *)
              unfold P_none in IHnone2.
              proj_fst H2.
              specialize (IHnone2 step1 H2) as Hs2.
              rewrite Hs2. done.
          ** discriminate H.
          ** discriminate H.
    }
      
    1: { (* IfS *)
      destruct H as [IHsome1 IHnone1].
      destruct H0 as [IHsome2 IHnone2].
      split.

      + (* --- P_some --- *)
        intros stmt' step_taken H.
        simpl in H.
        destruct (trnsl_atomic_block s1 step_taken) as [[| | ] step1] eqn:H1;
        destruct (trnsl_atomic_block s2 step_taken) as [[| | ] step2] eqn:H2;
        simpl in H.

        ++ (* case: s1 = None', s2 = None' *)
          unfold P_none in IHnone1. proj_fst H1. specialize (IHnone1 step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_none in IHnone2. proj_fst H2. specialize (IHnone2 step_taken H2) as Hs2.
          rewrite Hs2. simpl.
          rewrite H. reflexivity.

        ++ (* case: s1 = None', s2 = Error *) 
          discriminate H.
        
        ++ (* case: s1 = None', s2 = Some' s2' *)
          unfold P_none in IHnone1. proj_fst H1. specialize (IHnone1 step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_some in IHsome2. proj_fst H2. specialize (IHsome2 s step_taken H2) as Hs2.
          rewrite Hs2. simpl. rewrite H. reflexivity.

        ++ (* case: s1 = Error, s2 = None' *)
          discriminate H.

        ++ (* case: s1 = Error, s2 = Error *)
          discriminate H.
        
        ++ (* case: s1 = Error, s2 = Some' s *)
          discriminate H.

        ++ (* case: s1 = Some' s1', s2 = None' *)
          unfold P_some in IHsome1. proj_fst H1. specialize (IHsome1 s step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_none in IHnone2. proj_fst H2. specialize (IHnone2 step_taken H2) as Hs2.
          rewrite Hs2. simpl. rewrite H. reflexivity.

        ++ (* case: s1 = Some' s1', s2 = Error *)
          discriminate H.

        ++ (* case: s1 = Some' s, s2 = Some' s0 *)
          unfold P_some in IHsome1. proj_fst H1. specialize (IHsome1 s step_taken H1) as Hs1.
          simpl. rewrite Hs1.
          unfold P_some in IHsome2. proj_fst H2. specialize (IHsome2 s0 step_taken H2) as Hs2.
          rewrite Hs2. simpl. rewrite H. reflexivity.

      + (* --- P_none --- *)
        intros step_taken H.
        simpl in H.
        destruct (trnsl_atomic_block s1 step_taken) as [[| | ] step1] eqn:H1;
        destruct (trnsl_atomic_block s2 step_taken) as [[| | ] step2] eqn:H2;
        simpl in H; try discriminate H. simpl.
        unfold P_none in IHnone1. unfold P_none in IHnone2.
        proj_fst H1. proj_fst H2.

        specialize (IHnone1 step_taken H1).
        specialize (IHnone2 step_taken H2).
        rewrite IHnone1. rewrite IHnone2. done.
    }

    1: { (* InvAccessBlock *)
      split.
      + (* P_some *)
        intros stmt' step_taken H1.
        simpl.
        simpl in H1.
        destruct step_taken; try discriminate H.
        * rewrite <- H1. simpl.
          destruct (trnsl_atomic_block body true) eqn:Hb1.
          destruct (trnsl_atomic_block body false) eqn:Hb2.
          simpl in H1.

          pose proof (trnsl_atomic_step_monotone body t t0 b b0 Hb1 Hb2) as HMono.
          specialize (HMono ltac:(intros Htemp; rewrite H1 in Htemp; discriminate)) as [Hbody _]. simpl. done.
        * rewrite <- H1. simpl. done.

      + (* P_none *) 
        intros step_taken H1.
        simpl in H1.
        simpl.
        destruct H as [HIndSome HIndNone].
        unfold P_none in HIndNone.
        destruct step_taken; rewrite <- H1; simpl; try done.
        * 
          destruct (trnsl_atomic_block body true) eqn:Hb1.
          destruct (trnsl_atomic_block body false) eqn:Hb2.
          simpl in H1.

          pose proof (trnsl_atomic_step_monotone body t t0 b b0 Hb1 Hb2) as HMono.
          specialize (HMono ltac:(intros Htemp; rewrite H1 in Htemp; discriminate)) as [Hbody _]. simpl. done.
    }
  Qed.

  Lemma trnsl_stmt_trnsl_atomic_block_some c stmt :
    (trnsl_atomic_block c false).1 = Some' stmt -> trnsl_stmt c = Some' stmt.
  Proof.
    pose proof (trnsl_stmt_trnsl_atomic_block_some_none_mutual c) as [Hsome _].
    unfold P_some in Hsome.
    specialize (Hsome stmt false). done.
  Qed.

  Lemma trnsl_stmt_trnsl_atomic_block_none c :
    (trnsl_atomic_block c false).1 = None' -> trnsl_stmt c = None'.
  Proof.
    pose proof (trnsl_stmt_trnsl_atomic_block_some_none_mutual c) as [_ Hnone].
    unfold P_none in Hnone.
    specialize (Hnone false). done.
  Qed.

  Lemma trnsl_atomic_block_true_conserved stmt:
    (trnsl_atomic_block stmt true).2 = true.
  Proof.
    induction stmt. 

    all: simpl in *; try done.
    - simpl. destruct (trnsl_atomic_block stmt1 true) eqn:Hstmt1.
      destruct t; try done.
      + simpl in *. subst. done.
      + simpl in *; subst.
        destruct (trnsl_atomic_block stmt2 true) eqn:Hstmt2.
        simpl in *; subst.
        destruct t; simpl; done.
    
    - simpl in *. destruct (trnsl_atomic_block stmt1 true) eqn:Hstmt1.
      destruct t; try done.
      + simpl in *; subst.
        destruct (trnsl_atomic_block stmt2 true) eqn:Hstmt2.
        simpl in *; subst. destruct t; done.
      
      + simpl in *; subst.
        destruct (trnsl_atomic_block stmt2 true) eqn:Hstmt2.
        simpl in *; subst. destruct t; done.

  Qed.

  Lemma trnsl_atomic_block_true_conserved' stmt t b:
    trnsl_atomic_block stmt true = (t, b) -> b = true.
  Proof.
    intros.
    proj_snd H.
    pose proof (trnsl_atomic_block_true_conserved stmt). rewrite H in H0. simpl in *. done.
  Qed.

  Lemma trnsl_atomic_block_non_constant_step b stmt output:
    trnsl_atomic_block stmt b = (output, b) -> (output = None' \/ output = Error).
  Proof.
    revert b output.
    induction stmt; intros.

    all: 
      try (simpl in *;
      destruct b; inversion H; [subst; right; done]).
    - simpl in *.
      destruct (trnsl_atomic_block stmt1 b) eqn:Hstmt1.
      destruct (trnsl_atomic_block stmt2 b) eqn:Hstmt2.
      destruct b0.
      + destruct t.
        ++ pose proof (trnsl_atomic_block_true_conserved stmt2).
          destruct b.
          * specialize (IHstmt2 true output H). done.
          * proj_snd H. rewrite H in H0. discriminate.

        ++ right. proj_fst H. simpl in *. subst. done.

        ++ destruct (trnsl_atomic_block stmt2 true) eqn:Hstmt2'.
          pose proof (trnsl_atomic_block_true_conserved stmt2).
          destruct b0; destruct b.
          * specialize (IHstmt1 true (Some' s) Hstmt1). destruct IHstmt1; discriminate.
          * destruct t; discriminate.
          * proj_snd Hstmt2'. rewrite Hstmt2' in H0. discriminate.
          * proj_snd Hstmt2'. rewrite Hstmt2' in H0. discriminate.
      + destruct t.
        ++ destruct b.
          * pose proof (trnsl_atomic_block_true_conserved' stmt1 None' false Hstmt1); discriminate.
          * specialize (IHstmt2 false output H). done.

        ++ inversion H; subst. right; done.

        ++ destruct b.
          * pose proof (trnsl_atomic_block_true_conserved' stmt1 (Some' s) false Hstmt1); discriminate.
          * specialize (IHstmt1 false (Some' s) Hstmt1). destruct IHstmt1; discriminate.

    - destruct (trnsl_atomic_block stmt1 b) eqn:Hstmt1.
      destruct (trnsl_atomic_block stmt2 b) eqn:Hstmt2.
      destruct b.
      + simpl in H. rewrite Hstmt1 Hstmt2 in H.
        pose proof (trnsl_atomic_block_true_conserved' stmt1 t b0 Hstmt1); subst.
        pose proof (trnsl_atomic_block_true_conserved' stmt2 t0 b1 Hstmt2); subst.
        specialize (IHstmt1 true t Hstmt1). specialize (IHstmt2 true t0 Hstmt2).
        destruct IHstmt1, IHstmt2; subst; inversion H; subst; try (left; done); try (right; done).
      
      + destruct b0, b1.
        ++ simpl in H; rewrite Hstmt1 Hstmt2 in H.
          destruct t, t0; try discriminate; inversion H; subst.
          all: try (left; done); try (right; done).

        ++ simpl in H; rewrite Hstmt1 Hstmt2 in H.
          destruct t, t0; try discriminate; inversion H; subst.
          all: try (left; done); try (right; done).

        ++ simpl in H; rewrite Hstmt1 Hstmt2 in H.
          destruct t, t0; try discriminate; inversion H; subst.
          all: try (left; done); try (right; done).
        
        ++ simpl in H; rewrite Hstmt1 Hstmt2 in H.
          destruct t, t0; try discriminate; inversion H; subst.
          all: try (left; done); try (right; done).
          * specialize (IHstmt2 false (Some' s) Hstmt2). destruct IHstmt2; discriminate.
          * specialize (IHstmt1 false (Some' s) Hstmt1). destruct IHstmt1; discriminate.
          * specialize (IHstmt1 false (Some' s) Hstmt1). destruct IHstmt1; discriminate.

    - simpl in *.
      destruct b; inversion H; left; done.

    -  simpl in *.
      destruct b; inversion H; left; done.

    - simpl in *. apply (IHstmt b). apply H.

    - simpl in *.
      destruct b; inversion H; left; done.

    - simpl in *.
      destruct b; inversion H; left; done.

    - simpl in *.
      destruct b; inversion H; left; done.
  Qed.

  Lemma trnsl_atomic_block_atomicity stmt s stk_id:
    (trnsl_atomic_block stmt false).1 = Some' s -> Atomic WeaklyAtomic (to_rtstmt stk_id s).
  Proof.
    revert s.
    induction stmt.
    1: {
      intros. simpl in *.
      destruct (trnsl_atomic_block stmt1 false) eqn:Hstmt1.
      destruct (trnsl_atomic_block stmt2 b) eqn:Hstmt2.
      destruct b.
      - pose proof (trnsl_atomic_block_true_conserved' stmt2 t0 b0 Hstmt2); subst.
        pose proof (trnsl_atomic_block_non_constant_step true stmt2 t0 Hstmt2).
        destruct H0; subst.
        + destruct t; try discriminate. simpl in *. apply IHstmt1. apply H.
        + destruct t; discriminate.

      - pose proof (trnsl_atomic_block_non_constant_step false stmt1 t Hstmt1).
        destruct H0; subst.
        + simpl in *; subst. proj_fst Hstmt2. apply IHstmt2. apply Hstmt2.
        + simpl in *; discriminate.
     }

    1: {
      intros. simpl in *. 
      destruct (trnsl_atomic_block stmt1 false) eqn:Hstmt1;
      destruct (trnsl_atomic_block stmt2 false) eqn:Hstmt2.

      destruct t eqn:Ht, t0 eqn:Ht0; simpl in *; try discriminate.
      - inversion H; subst. simpl in *.
        specialize (IHstmt2 s0 eq_refl).
        unfold Atomic. intros.
        inversion H0; simpl in *.
        pose proof (fill_if_empty K e1' _ _ _ _ H1) as HK; subst. simpl in *. symmetry in H1. subst.
        inversion H3; subst.
        + destruct H13 as [e1' [e2'0 [K [Hs1 [Hs2 Hrtm]]]]].
          pose proof (fill_atomic_empty K e1' (RTSkipS stk_id) ltac:(simpl; done) Hs1); subst. simpl in *. symmetry in Hs1; subst.
          inversion Hrtm; subst. apply val_irreducible. done.

        + unfold Atomic in IHstmt2.
          specialize (IHstmt2 σ e2' [] σ' efs).
          destruct H13 as [e1' [e2'0 [K [Hs1 [Hs2 Hrtm]]]]].
          assert (prim_step (to_rtstmt stk_id s0) σ [] e2' σ' efs).
          { apply (Ectx_step K e1' e2'0); try done.  }
          specialize (IHstmt2 H1). done.

        + destruct b1 eqn:Hb1, (to_rtstmt stk_id s0) eqn:Hs0; try (exfalso; done).
          apply val_irreducible; done.

      - inversion H; subst. simpl in *.
        specialize (IHstmt1 s0 eq_refl).
        unfold Atomic. intros.
        inversion H0; simpl in *.
        pose proof (fill_if_empty K e1' _ _ _ _ H1) as HK; subst. simpl in *. symmetry in H1; subst.
        inversion H3; subst.
        + unfold Atomic in IHstmt1.
          specialize (IHstmt1 σ e2' [] σ' efs).
          destruct H13 as [e1' [e2'0 [K [Hs1 [Hs2 Hrtm]]]]].
          assert (prim_step (to_rtstmt stk_id s0) σ [] e2' σ' efs).
          { apply (Ectx_step K e1' e2'0); try done.  }
          specialize (IHstmt1 H1). done.

        + destruct H13 as [e1' [e2'0 [K [Hs1 [Hs2 Hrtm]]]]].
          pose proof (fill_atomic_empty K e1' (RTSkipS stk_id) ltac:(simpl; done) Hs1); subst. simpl in *. symmetry in Hs1; subst.
          inversion Hrtm; subst. apply val_irreducible. done.

        + destruct b1 eqn:Hb1, (to_rtstmt stk_id s0) eqn:Hs0; try (exfalso; done).
          apply val_irreducible; done.

      - inversion H; subst. simpl in *.
        specialize (IHstmt1 s0 eq_refl).
        specialize (IHstmt2 s1 eq_refl).
        unfold Atomic. intros.
        inversion H0; simpl in *.
        pose proof (fill_if_empty K e1' _ _ _ _ H1) as HK; subst. simpl in *. symmetry in H1; subst.
        inversion H3; subst.
        + unfold Atomic in IHstmt1.
          specialize (IHstmt1 σ e2' [] σ' efs).
          destruct H13 as [e1' [e2'0 [K [Hs1 [Hs2 Hrtm]]]]].
          assert (prim_step (to_rtstmt stk_id s0) σ [] e2' σ' efs).
          { apply (Ectx_step K e1' e2'0); try done.  }
          specialize (IHstmt1 H1). done.
          
        + unfold Atomic in IHstmt2.
          specialize (IHstmt2 σ e2' [] σ' efs).
          destruct H13 as [e1' [e2'0 [K [Hs1 [Hs2 Hrtm]]]]].
          assert (prim_step (to_rtstmt stk_id s1) σ [] e2' σ' efs).
          { apply (Ectx_step K e1' e2'0); try done.  }
          specialize (IHstmt2 H1). done.

        + destruct b1 eqn:Hb1.
          * destruct (to_rtstmt stk_id s0) eqn:Hs0; try (exfalso; done).
            apply val_irreducible; done.
            
          * destruct (to_rtstmt stk_id s1) eqn:Hs1; try (exfalso; done).
            apply val_irreducible; done.

    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_assign.
    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_skip.
    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_stuck.
    }

    1: { 
      intros. simpl in *. inversion H; subst.
    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_fld_wr.
    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_fld_rd.
    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_cas.
    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_alloc.
    }

    1: { 
      intros. simpl in *. inversion H; subst. simpl in *.
      apply atomic_spawn.
    }

    1: { 
      intros. simpl in *. inversion H; subst.
    }

    1: { 
      intros. simpl in *. inversion H; subst.
    }

    1: {
      intros. simpl in *. apply IHstmt. apply H.
    }

    1: {
      intros. simpl in *. inversion H; subst.
    }

    1: {
      intros. simpl in *. inversion H; subst.
    }

    1: {
      intros. simpl in *. inversion H; subst.
    }
  Qed.

Definition fresh_lvar (stk: stack) v := forall v', not (stk !! v' = Some v).

(* Freshness survives renaming both the stack and the witness by the same
   injective ren: any occurrence of ren lv in the renamed stack would come
   (via lookup_fmap) from some lv0 with ren lv0 = ren lv, which injectivity
   forces to be lv itself, contradicting the original freshness. *)
Lemma fresh_lvar_rename (ren : lvar -> lvar) (Hinj : Inj (=) (=) ren)
    (stk : stack) (lv : lvar) :
  fresh_lvar stk lv → fresh_lvar (ren <$> stk) (ren lv).
Proof.
  intros Hfresh v' Heq.
  apply lookup_fmap_Some in Heq as [lv0 [Heq0 Hlv0]].
  apply Hinj in Heq0. subst lv0.
  exact (Hfresh v' Hlv0).
Qed.

(* A fresh lvar is not in lexpr_fvars of any translated expression *)
Lemma trnsl_expr_lExpr_fresh_lvar (stk : stack) (e : lang.expr) (le : LExpr) (lv : lvar) :
  trnsl_expr_lExpr stk e = Some le →
  fresh_lvar stk lv →
  lv ∉ lexpr_fvars le.
Proof.
  intros Htrnsl Hfresh Hv.
  destruct (trnsl_expr_lExpr_fvars_range stk e le Htrnsl lv Hv) as [k Hk].
  exact (Hfresh k Hk).
Qed.

Section TypeInf.
    Definition stk_type_compat (ρ : pvar_typs) (σ : lvar_typs) (stk : stack) := forall v lv, (stk !! v = Some lv) -> ρ v = σ lv.

  (* typeOf and inf_expr are now defined globally above, before expr_well_defined. *)

  Fixpoint inf_lexpr (σ: lvar_typs) (le: LExpr) : option typ := 
  match le with
  | LVar x => Some (σ x)
  | LVal v => Some (typeOf (trnsl_lval v))
  | LUnOp NotBoolOp e =>
    match inf_lexpr σ e with
    | Some TpBool => Some TpBool
    | _ => None
    end
  | LUnOp NegOp e =>
    match inf_lexpr σ e with
    | Some TpInt => Some TpInt
    | _ => None
    end
  | LUnOp (RAOfIntOp r) e =>
    match inf_lexpr σ e with
    | Some TpInt => Some (TpRA r)
    | _ => None
    end

  | LBinOp (AddOp | SubOp | MulOp | DivOp | ModOp) e1 e2 =>
    match inf_lexpr σ e1, inf_lexpr σ e2 with
    | Some TpInt, Some TpInt => Some TpInt
    | _, _ => None
    end

  | LBinOp (LtOp | GtOp | LeOp | GeOp) e1 e2 =>
    match inf_lexpr σ e1, inf_lexpr σ e2 with
    | Some TpInt, Some TpInt => Some TpBool
    | _, _ => None
    end

  | LBinOp (AndOp | OrOp) e1 e2 =>
    match inf_lexpr σ e1, inf_lexpr σ e2 with
    | Some TpBool, Some TpBool => Some TpBool
    | _, _ => None
    end

  | LBinOp (EqOp | NeOp) e1 e2 =>
    match inf_lexpr σ e1, inf_lexpr σ e2 with
    | Some tp1, Some tp2 => if typ_beq tp1 tp2 then Some TpBool else None
    | _, _ => None
    end

  | LIfE e1 e2 e3 =>
    match inf_lexpr σ e1, inf_lexpr σ e2, inf_lexpr σ e3 with
    | Some TpBool, Some tp2, Some tp3 => if typ_beq tp2 tp3 then Some tp2 else None
    | _, _, _ => None
    end

  | _ => None
  end.

  (* inf_lexpr only ever inspects an lvar leaf via σ, and Hren_typ makes ren
     invisible to σ there -- every other case is a function purely of its
     recursive inf_lexpr sub-results (and, for LUnOp/LBinOp, the untouched
     operator), so rewriting those via IH closes it regardless of the op. *)
  Lemma inf_lexpr_rename (ren : lvar -> lvar) (σ : lvar_typs)
      (Hren_typ : ∀ lv, σ (ren lv) = σ lv) (le : LExpr) :
    inf_lexpr σ (rename_lexpr ren le) = inf_lexpr σ le.
  Proof.
    induction le; simpl;
      try rewrite IHle; try rewrite IHle1; try rewrite IHle2; try rewrite IHle3;
      try reflexivity.
    f_equal. apply Hren_typ.
  Qed.

  (* stk_type_compat survives renaming the stack (both keeping σ fixed):
     any binding v -> ren lv0 in the renamed stack came from v -> lv0 in the
     original (lookup_fmap), whose ρ v = σ lv0 fact transports to
     ρ v = σ (ren lv0) via Hren_typ. *)
  Lemma stk_type_compat_rename (ren : lvar -> lvar) (ρ : pvar_typs) (σ : lvar_typs)
      (Hren_typ : ∀ lv, σ (ren lv) = σ lv) (stk : stack) :
    stk_type_compat ρ σ stk → stk_type_compat ρ σ (ren <$> stk).
  Proof.
    intros Hcompat v lv' Heq.
    apply lookup_fmap_Some in Heq as [lv0 [<- Hlv0]].
    rewrite Hren_typ. exact (Hcompat v lv0 Hlv0).
  Qed.

  Definition env_typ_well_defined (σ : lvar_typs) (mp : symb_map) :=
      forall lv,
      match (σ lv), (mp lv) with
      | TpBool, LitBool b => True
      | TpInt, LitInt i => True
      | TpLoc, LitLoc l => True
      | TpUnit, LitUnit => True
      | TpRA r, LitRAElem (existT r' _) => r = r'
      | _, _ => False
      end.


  (* env_typ_well_defined survives an mp-update at v, provided the new value
     has v's own declared type -- the only new obligation ExistsElimRule's
     soundness case needs when it re-interprets its premise at mp[v:=v']
     for the witness v' an incoming existential actually produced. *)
  Lemma env_typ_well_defined_update (σ : lvar_typs) (mp : symb_map) (v : lvar) (v' : val) :
    env_typ_well_defined σ mp ->
    typ_val_match (σ v) v' ->
    env_typ_well_defined σ (fun y => if (y =? v)%string then v' else mp y).
  Proof.
    intros Henv Htyp lv. destruct (String.eqb_spec lv v) as [-> | Hne].
    - simpl.
      unfold typ_val_match in Htyp.
      destruct (σ v); destruct v' as [b|i| |l|[r2 x]]; try done.
    - simpl. exact (Henv lv).
  Qed.


  Lemma lexpr_expr_typ_compat ρ σ stk e le tp :
    stk_type_compat ρ σ stk ->
    trnsl_expr_lExpr stk e = Some le ->
    inf_expr ρ e = Some tp ->
    inf_lexpr σ le = Some tp.
  Proof.
    intros Hstk H2 H3. revert le tp H2 H3.
    induction e; intros le tp H2 H3; simpl in *.
    - (* Var x *)
      destruct (stk !! x) as [lv|] eqn:Hstk_x; [|discriminate H2].
      injection H2 as <-. injection H3 as <-.
      simpl. apply Hstk in Hstk_x. rewrite <- Hstk_x. reflexivity.
    - (* Val v *)
      injection H2 as <-. injection H3 as <-.
      simpl. rewrite trnsl_lval_trnsl_val_inverse. reflexivity.
    - (* UnOp op e *)
      destruct (trnsl_expr_lExpr stk e) as [le'|] eqn:Hle'; [|discriminate H2].
      injection H2 as <-. simpl.
      destruct op; simpl in H3;
        [ destruct (inf_expr ρ e) as [[]|] eqn:Htp_e; try discriminate H3;
          injection H3 as <-; rewrite (IHe le' TpBool eq_refl eq_refl); reflexivity
        | destruct (inf_expr ρ e) as [[]|] eqn:Htp_e; try discriminate H3;
          injection H3 as <-; rewrite (IHe le' TpInt eq_refl eq_refl); reflexivity
        | discriminate H3
        | destruct (inf_expr ρ e) as [[]|] eqn:Htp_e; try discriminate H3;
          injection H3 as <-; rewrite (IHe le' TpInt eq_refl eq_refl); reflexivity ].
    - (* BinOp op e1 e2 *)
      destruct (trnsl_expr_lExpr stk e1) as [le1'|] eqn:Hle1'; [|discriminate H2].
      destruct (trnsl_expr_lExpr stk e2) as [le2'|] eqn:Hle2'; [|discriminate H2].
      injection H2 as <-. simpl.
      destruct op; simpl in H3;
        try (destruct (inf_expr ρ e1) as [[]|] eqn:Htp1; try discriminate H3;
             destruct (inf_expr ρ e2) as [[]|] eqn:Htp2; try discriminate H3;
             injection H3 as <-;
             rewrite (IHe1 le1' TpInt eq_refl eq_refl);
             rewrite (IHe2 le2' TpInt eq_refl eq_refl); reflexivity);
        try (destruct (inf_expr ρ e1) as [[]|] eqn:Htp1; try discriminate H3;
             destruct (inf_expr ρ e2) as [[]|] eqn:Htp2; try discriminate H3;
             injection H3 as <-;
             rewrite (IHe1 le1' TpBool eq_refl eq_refl);
             rewrite (IHe2 le2' TpBool eq_refl eq_refl); reflexivity);
        try (destruct (inf_expr ρ e1) as [tp1|] eqn:Htp1; try discriminate H3;
             destruct (inf_expr ρ e2) as [tp2|] eqn:Htp2; try discriminate H3;
             destruct (typ_beq tp1 tp2) eqn:Htyp; try discriminate H3;
             injection H3 as <-;
             rewrite (IHe1 le1' tp1 eq_refl eq_refl);
             rewrite (IHe2 le2' tp2 eq_refl eq_refl);
             rewrite Htyp; reflexivity);
        try discriminate H3.
    - (* IfE e1 e2 e3 *)
      destruct (trnsl_expr_lExpr stk e1) as [le1'|] eqn:Hle1'; [|discriminate H2].
      destruct (trnsl_expr_lExpr stk e2) as [le2'|] eqn:Hle2'; [|discriminate H2].
      destruct (trnsl_expr_lExpr stk e3) as [le3'|] eqn:Hle3'; [|discriminate H2].
      injection H2 as <-. simpl.
      destruct (inf_expr ρ e1) as [[]|] eqn:Htp1; try discriminate H3.
      destruct (inf_expr ρ e2) as [tp2|] eqn:Htp2; try discriminate H3.
      destruct (inf_expr ρ e3) as [tp3|] eqn:Htp3; try discriminate H3.
      destruct (typ_beq tp2 tp3) eqn:Htyp; try discriminate H3.
      injection H3 as <-.
      rewrite (IHe1 le1' TpBool eq_refl eq_refl).
      rewrite (IHe2 le2' tp2 eq_refl eq_refl).
      rewrite (IHe3 le3' tp3 eq_refl eq_refl).
      rewrite Htyp. reflexivity.
    - (* StuckE *)
      discriminate H3.
  Qed.

  (* Combined lemma: a well-typed expression always evaluates and the result has
     the inferred type. Proved by structural induction; both corollaries follow. *)
  Local Lemma interp_lexpr_well_typed σ le mp tp :
    env_typ_well_defined σ mp →
    inf_lexpr σ le = Some tp →
    ∃ val, interp_lexpr le mp = Some val ∧ typeOf (trnsl_lval val) = tp.
  Proof.
    intros Hwf. revert tp.
    induction le; intros tp Hinf; simpl in *.
    - (* LVar x *)
      injection Hinf as <-. exists (mp x). split; [done|].
      specialize (Hwf x).
      destruct (σ x) as [ | | | | r], (mp x) as [ | | | | [r' x0]];
        simpl in *; try contradiction; try done; congruence.
    - (* LVal v *)
      injection Hinf as <-. eauto.
    - (* LUnOp *)
      destruct op.
      + (* NotBoolOp *)
        destruct (inf_lexpr σ le) as [[]|]; try discriminate Hinf.
        injection Hinf as <-.
        destruct (IHle TpBool eq_refl) as (v & Hv & Htyp).
        destruct v as [ | | | |[]]; simpl in Htyp; try discriminate Htyp.
        eexists. rewrite Hv. split; done.
      + (* NegOp *)
        destruct (inf_lexpr σ le) as [[]|]; try discriminate Hinf.
        injection Hinf as <-.
        destruct (IHle TpInt eq_refl) as (v & Hv & Htyp).
        destruct v as [ | | | |[]]; simpl in Htyp; try discriminate Htyp.
        eexists. rewrite Hv. split; done.
      + (* RAValidOp *)
        discriminate Hinf.
      + (* RAOfIntOp *)
        destruct (inf_lexpr σ le) as [[]|]; try discriminate Hinf.
        injection Hinf as <-.
        destruct (IHle TpInt eq_refl) as (v & Hv & Htyp).
        destruct v as [ |i| | |[]]; simpl in Htyp; try discriminate Htyp.
        eexists. rewrite Hv. split; done.
    - (* LBinOp: arithmetic/comparison (TpInt × TpInt) and boolean (TpBool × TpBool) share structure *)
      destruct op; simpl in Hinf;
      (* AddOp | SubOp | MulOp | DivOp | ModOp | LtOp | GtOp | LeOp | GeOp:
         both subexprs must be TpInt; note after simpl the IH sees the reduced value *)
      try (
        destruct (inf_lexpr σ le1) as [[]|]; try discriminate Hinf;
        destruct (inf_lexpr σ le2) as [[]|]; try discriminate Hinf;
        injection Hinf as <-;
        destruct (IHle1 TpInt eq_refl) as (v1 & Hv1 & Htyp1);
        destruct (IHle2 TpInt eq_refl) as (v2 & Hv2 & Htyp2);
        destruct v1 as [ | | | |[]]; simpl in Htyp1; try discriminate Htyp1;
        destruct v2 as [ | | | |[]]; simpl in Htyp2; try discriminate Htyp2;
        eexists; rewrite Hv1 Hv2; split; done);
      (* EqOp | NeOp: subexprs must have the same (any) type *)
      try (
        destruct (inf_lexpr σ le1) as [tp1|]; try discriminate Hinf;
        destruct (inf_lexpr σ le2) as [tp2|]; try discriminate Hinf;
        destruct (typ_beq tp1 tp2); try discriminate Hinf;
        injection Hinf as <-;
        destruct (IHle1 tp1 eq_refl) as (v1 & Hv1 & _);
        destruct (IHle2 tp2 eq_refl) as (v2 & Hv2 & _);
        eexists; rewrite Hv1 Hv2; split; done);
      (* AndOp | OrOp: both subexprs must be TpBool *)
      try (
        destruct (inf_lexpr σ le1) as [[]|]; try discriminate Hinf;
        destruct (inf_lexpr σ le2) as [[]|]; try discriminate Hinf;
        injection Hinf as <-;
        destruct (IHle1 TpBool eq_refl) as (v1 & Hv1 & Htyp1);
        destruct (IHle2 TpBool eq_refl) as (v2 & Hv2 & Htyp2);
        destruct v1 as [ | | | |[]]; simpl in Htyp1; try discriminate Htyp1;
        destruct v2 as [ | | | |[]]; simpl in Htyp2; try discriminate Htyp2;
        eexists; rewrite Hv1 Hv2; split; done);
      try discriminate Hinf.
    - (* LIfE *)
      destruct (inf_lexpr σ le1) as [[]|]; try discriminate Hinf.
      destruct (inf_lexpr σ le2) as [tp2|] eqn:He2; try discriminate Hinf.
      destruct (inf_lexpr σ le3) as [tp3|] eqn:He3; try discriminate Hinf.
      destruct (typ_beq tp2 tp3) eqn:Hbeq; try discriminate Hinf.
      injection Hinf as <-.
      apply internal_typ_dec_bl in Hbeq. subst tp3.
      destruct (IHle1 TpBool eq_refl) as (v1 & Hv1 & Htyp1).
      destruct v1 as [ | | | |[]]; simpl in Htyp1; try discriminate Htyp1.
      rewrite Hv1. destruct b.
      + exact (IHle2 tp2 eq_refl).
      + exact (IHle3 tp2 eq_refl).
    - (* LStuck *)
      discriminate Hinf.
  Qed.

  Lemma interp_lexpr_typ_compat σ le tp val mp :
    env_typ_well_defined σ mp ->
    inf_lexpr σ le = Some tp ->
    (interp_lexpr le mp) = Some val ->
    typeOf (trnsl_lval val) = tp.
  Proof.
    intros Hwf Hinf Heval.
    destruct (interp_lexpr_well_typed σ le mp tp Hwf Hinf) as (val' & Hval' & Htyp).
    rewrite Hval' in Heval. injection Heval as <-. exact Htyp.
  Qed.

  (* Restates interp_lexpr_typ_compat's raw typeOf fact as typ_val_match --
     what lets LExists's own type-restricted translation (see its
     trnsl_assertion_str case) get a fresh-lvar rule's witness well-typed for
     free, as long as the rule ties its lvar to an LExpr whose inf_lexpr type
     it already knows (e.g. HeapReadRule's chunk parameter), rather than
     needing a bespoke witness_well_typed-style proof per rule. *)
  Lemma interp_lexpr_well_typed_match (σ : lvar_typs) (le : LExpr) (tp : typ) (val : val) (mp : symb_map) :
    env_typ_well_defined σ mp ->
    inf_lexpr σ le = Some tp ->
    interp_lexpr le mp = Some val ->
    typ_val_match tp val.
  Proof.
    intros Hwf Hinf Heval.
    pose proof (interp_lexpr_typ_compat σ le tp val mp Hwf Hinf Heval) as Htyp.
    destruct val as [b|i| |l|[r x]]; simpl in Htyp; subst; done.
  Qed.

  Lemma lexpr_typcheck_well_defined σ mp le tp :
    env_typ_well_defined σ mp ->
    inf_lexpr σ le = Some tp ->
    ∃ val, interp_lexpr le mp = Some val.
  Proof.
    intros Hwf Hinf.
    destruct (interp_lexpr_well_typed σ le mp tp Hwf Hinf) as (val & Hval & _).
    eauto.
  Qed.

  (* Substituting a variable-named lvar map that just maps each name back to itself
     is a no-op: this is used to view an assertion's "unsubstituted" translation
     (evaluated directly via mp) as a degenerate case of the substitution lemmas. *)
  Lemma lexpr_subst_id_map (args : list var) e :
    lexpr_subst e (list_to_map (zip args (map LVar args)) : gmap var LExpr) = e.
  Proof.
    induction e; simpl; try (f_equal; done).
    destruct (list_to_map (zip args (map LVar args)) !! x) as [e'|] eqn:Hx; [ | done].
    apply elem_of_list_to_map_2 in Hx.
    apply elem_of_list_lookup_1 in Hx as [i Hi].
    apply lookup_zip_with_Some in Hi as (a & le & Heq & Ha & Hle).
    injection Heq as <- <-.
    rewrite list_lookup_fmap in Hle. rewrite Ha in Hle. simpl in Hle.
    injection Hle as <-. done.
  Qed.

  Lemma subst_id_map (args : list var) a :
    subst a (list_to_map (zip args (map LVar args)) : gmap var LExpr) = a.
  Proof.
    induction a; simpl;
      repeat match goal with
      | |- context [lexpr_subst ?e (list_to_map (zip args (map LVar args)))] =>
          rewrite (lexpr_subst_id_map args e)
      | H : subst ?a _ = ?a |- context [subst ?a (list_to_map (zip args (map LVar args)))] =>
          rewrite H
      end;
      try done.
    - f_equal. induction args0; simpl; [done|]. f_equal; [apply lexpr_subst_id_map | done].
    - f_equal. induction args0; simpl; [done|]. f_equal; [apply lexpr_subst_id_map | done].
  Qed.

  (* If mp' agrees with the zipped (args,arg_vals) pairs, then the "identity lexprs"
     (mapping each formal-arg name back to LVar itself) evaluate under mp' to exactly
     those values — the fact needed to instantiate trnsl_assertion's substitution
     lemmas at an mp that already "bakes in" the substitution directly. *)
  Lemma eval_lvar_identity_map_agrees (args : list var) (arg_vals : list lang.val) (mp' : symb_map) :
    length args = length arg_vals →
    (∀ v val, (v, val) ∈ zip args arg_vals → mp' v = trnsl_val val) →
    Forall2 (λ expr val0, interp_lexpr expr mp' = Some (trnsl_val val0)) (map LVar args) arg_vals.
  Proof using G.
    revert arg_vals. induction args as [| a args IH]; intros [| v vals] Hlen Hagree;
      simpl in Hlen; try discriminate Hlen; simpl; [constructor |].
    constructor.
    - simpl. rewrite (Hagree a v (elem_of_list_here _ _)). done.
    - apply IH; [lia |]. intros v' val' Hin. apply Hagree. right. exact Hin.
  Qed.

  Lemma zip_id_map_lookup_arg (xs : list var) (lv : var) :
    NoDup xs → lv ∈ xs →
    (list_to_map (zip xs (map LVar xs)) : gmap var LExpr) !! lv = Some (LVar lv).
  Proof.
    induction xs as [| x xs IH]; intros Hnodup Hin.
    - inversion Hin.
    - simpl. apply elem_of_cons in Hin as [-> | Hin'].
      + rewrite lookup_insert. done.
      + rewrite lookup_insert_ne.
        * apply IH; [by inversion Hnodup | exact Hin'].
        * intro Heq. subst lv. inversion Hnodup; subst. contradiction.
  Qed.

  Lemma zip_val_map_lookup_arg (xs : list var) (vals : list lang.val) (lv : var) (v : lang.val) :
    NoDup xs → (lv, v) ∈ zip xs vals →
    (list_to_map (zip xs (map (λ val, LVal (trnsl_val val)) vals)) : gmap var LExpr) !! lv = Some (LVal (trnsl_val v)).
  Proof.
    revert vals. induction xs as [| x xs IH]; intros vals Hnodup Hin.
    - inversion Hin.
    - destruct vals as [| val vals]; [inversion Hin |].
      simpl in Hin. apply elem_of_cons in Hin as [Heq | Hin'].
      + injection Heq as <- <-. simpl. rewrite lookup_insert. done.
      + simpl. rewrite lookup_insert_ne.
        * apply IH; [by inversion Hnodup | exact Hin'].
        * intro Heq. subst lv. apply elem_of_zip_l in Hin'. inversion Hnodup; subst. contradiction.
  Qed.

  (* Generalizes zip_id_map_lookup_arg / zip_val_map_lookup_arg: whatever the
     wrapping function f, a zipped (name, y) pair looks up correctly in the
     map obtained after wrapping every y with f. Used both for a genuine
     lvar-renaming (f := LVar) and for value-substitution (f := LVal ∘
     trnsl_val), matching xs against fresh, non-identity lvars rather than
     reusing the program variable names themselves. *)
  Lemma zip_wrap_map_lookup_arg {A : Type} (xs : list var) (ys : list A) (f : A -> LExpr) (x : var) (y : A) :
    NoDup xs → (x, y) ∈ zip xs ys →
    (list_to_map (zip xs (map f ys)) : gmap var LExpr) !! x = Some (f y).
  Proof.
    revert ys. induction xs as [| x0 xs IH]; intros ys Hnodup Hin.
    - inversion Hin.
    - destruct ys as [| y0 ys]; [inversion Hin |].
      simpl in Hin. apply elem_of_cons in Hin as [Heq | Hin'].
      + injection Heq as <- <-. simpl. rewrite lookup_insert. done.
      + simpl. rewrite lookup_insert_ne.
        * apply IH; [by inversion Hnodup | exact Hin'].
        * intro Heq. subst x0. apply elem_of_zip_l in Hin'. inversion Hnodup; subst. contradiction.
  Qed.

  (* Overriding mp at a list of lvar names with well-typed values (per σ) preserves
     env_typ_well_defined, as long as it held for the original mp. *)
  Lemma env_typ_well_defined_override σ mp (args : list var) (arg_vals : list lang.val) :
    Forall2 (λ v val, typeOf val = σ v) args arg_vals ->
    env_typ_well_defined σ mp ->
    env_typ_well_defined σ
      (fun lv => match (list_to_map (zip args arg_vals) : gmap var lang.val) !! lv with
                 | Some v => trnsl_val v
                 | None => mp lv
                 end).
  Proof.
    intros HF2 Henv lv.
    destruct ((list_to_map (zip args arg_vals) : gmap var lang.val) !! lv) as [v|] eqn:Hlv;
      [ | exact (Henv lv) ].
    apply elem_of_list_to_map_2 in Hlv.
    apply elem_of_list_lookup_1 in Hlv as [i Hi].
    apply lookup_zip_with_Some in Hi as (x & y & Heq & Hargs & Hvals).
    injection Heq as <- <-.
    pose proof (Forall2_lookup_lr _ _ _ _ _ _ HF2 Hargs Hvals) as Htyp.
    rewrite <- Htyp. simpl.
    destruct v as [ | | | |[]]; simpl; done.
  Qed.

  (* Connects the static proc_call_args_well_typed check on the caller's argument
     expressions to the runtime types of the resulting argument values, threading
     through the existing lexpr translation/interpretation type-soundness lemmas. *)
  Lemma proc_call_args_typed_result ρ σ stk mp args lexprs arg_vals proc_entry :
    stk_type_compat ρ σ stk ->
    env_typ_well_defined σ mp ->
    proc_call_args_well_typed ρ args proc_entry ->
    map (fun arg => trnsl_expr_lExpr stk arg) args = map (fun le => Some le) lexprs ->
    Forall2 (fun le val0 => interp_lexpr le mp = Some (trnsl_val val0)) lexprs arg_vals ->
    Forall2 (fun arg_decl val => typeOf val = snd arg_decl) (proc_args_of proc_entry) arg_vals.
  Proof.
    unfold proc_call_args_well_typed.
    intros Hstk Henv Htyped.
    revert lexprs arg_vals.
    induction Htyped as [| a arg_decl args params Htp Htyped IH];
      intros lexprs arg_vals Hmap HF2.
    - simpl in Hmap. destruct lexprs; [ | discriminate]. inversion HF2. constructor.
    - simpl in Hmap. destruct lexprs as [| le lexprs']; [discriminate |].
      injection Hmap as Hhd Htl.
      inversion HF2 as [| l0 v0 ls vs Hinterp HF2']; subst.
      constructor.
      + pose proof (lexpr_expr_typ_compat ρ σ stk a le (snd arg_decl) Hstk Hhd Htp) as Hinf_le.
        pose proof (interp_lexpr_typ_compat σ le (snd arg_decl) (trnsl_val v0) mp Henv Hinf_le Hinterp) as Htyp.
        rewrite trnsl_lval_trnsl_val_inverse in Htyp. exact Htyp.
      + exact (IH lexprs' vs Htl HF2').
  Qed.


(* entails is parameterized by sigma and only has to hold at mp's that are
   well-typed w.r.t. it -- moved here (past TypeInf) so it can state that
   requirement via env_typ_well_defined. This is what lets WeakeningRule's
   own entails premises use Henv (already in scope wherever a
   RavenHoareTriple derivation is checked for soundness) to justify things
   like introducing an existential over an already-known, well-typed value
   -- something an unconditional-over-all-mp entails could never prove,
   since nothing stops an ill-typed mp from violating the witness's own
   typ_val_match side condition. *)
(* Fragment closed under LAnd, restricted to the leaf shapes whose own
   translation reads its LExpr arguments only through interp_lexpr at the
   ambient mp (LOwn/LGhostOwn/LExprA/LPure/LInv -- LInv's own args list is
   read the same way, via a pointwise Forall2 over interp_lexpr, no
   recursion into inv_map's body) -- deliberately excludes LForall/LExists
   (binder shadowing) and LPred (recursion through a global table, the
   *body* of which does need it, unlike LInv's own nominal fact). *)
Fixpoint qf_assertion (a : assertion) : Prop :=
  match a with
  | LOwn _ _ _ => True
  | LGhostOwn _ _ _ _ => True
  | LExprA _ => True
  | LPure _ => True
  | LInv _ _ => True
  | LAnd a1 a2 => qf_assertion a1 /\ qf_assertion a2
  | _ => False
  end.

(* rename_assertion never changes an assertion's top-level constructor, so
   qf_assertion (which is purely a case split on that constructor, modulo
   LAnd's recursion) transports along it unchanged. *)
Lemma qf_assertion_rename (ren : lvar -> lvar) (a : assertion) :
  qf_assertion a → qf_assertion (rename_assertion ren a).
Proof using G inv_namespace_map.
  induction a; simpl; try tauto.
Qed.

End TypeInf.


Section RavenLogic.

  (* Purely syntactic entailment on assertions -- deliberately independent
     of trnsl_assertion/Iris (no Sigma/Gamma/GhostConfig/invTokenG needed
     anywhere in this relation's own definition), so that WeakeningRule --
     the only RavenHoareTriple rule that consumes it -- can be stated
     without them. Soundness w.r.t. the real (Iris-level) [entails] is
     proved once, by induction on this relation's derivation -- see
     assertion_entails_sound, alongside trnsl_assertion (this relation is
     "the calculus's own opinion of entailment"; that lemma is "the
     calculus's opinion agrees with the semantics"). Reasoning about pure
     facts bottoms out in plain Coq implication (AE_Pure); everything else
     is structural manipulation of the assertion AST. *)
  Inductive assertion_entails (σ : lvar_typs) : assertion -> assertion -> Prop :=
  | AE_Refl P : assertion_entails σ P P
  | AE_Trans P Q R :
      assertion_entails σ P Q -> assertion_entails σ Q R -> assertion_entails σ P R
  | AE_And_Mono P P' Q Q' :
      assertion_entails σ P P' -> assertion_entails σ Q Q' ->
      assertion_entails σ (LAnd P Q) (LAnd P' Q')
  | AE_And_Comm P Q : assertion_entails σ (LAnd P Q) (LAnd Q P)
  | AE_And_Assoc_R P Q R :
      assertion_entails σ (LAnd (LAnd P Q) R) (LAnd P (LAnd Q R))
  | AE_And_Assoc_L P Q R :
      assertion_entails σ (LAnd P (LAnd Q R)) (LAnd (LAnd P Q) R)
  | AE_And_Elim_L P Q : assertion_entails σ (LAnd P Q) P
  | AE_And_Elim_R P Q : assertion_entails σ (LAnd P Q) Q
  | AE_And_True_Intro P : assertion_entails σ P (LAnd P (LPure True))
  | AE_And_True_Elim P : assertion_entails σ (LAnd P (LPure True)) P
  | AE_True_Intro P : assertion_entails σ P (LPure True)
  | AE_Pure (p q : Prop) : (p -> q) -> assertion_entails σ (LPure p) (LPure q)
  | AE_Exists_Mono lv t A B :
      σ lv = t -> assertion_entails σ A B ->
      assertion_entails σ (LExists lv t A) (LExists lv t B)
  | AE_Exists_Intro lv t X :
      σ lv = t -> assertion_entails σ X (LExists lv t X)
  | AE_Exists_ValIntro lv t w A :
      (* Witness-intro for a value w that is not necessarily lv's own
         ambient mp-value (AE_Exists_Intro's case) but a fresh constant:
         plugs w in for lv throughout A first (via subst), restricted to
         the qf_assertion fragment where trnsl_assertion_subst_lv holds. *)
      σ lv = t -> typ_val_match t w -> qf_assertion A ->
      assertion_entails σ (subst A (<[lv := LVal w]> ∅)) (LExists lv t A)
  | AE_Exists_Elim lv t P Q :
      σ lv = t -> lvar_fresh_in_assertion lv Q ->
      assertion_entails σ P Q -> assertion_entails σ (LExists lv t P) Q
  | AE_Exists_And_Swap_R lv t body p :
      lvar_fresh_in_assertion lv p ->
      assertion_entails σ (LAnd (LExists lv t body) p) (LExists lv t (LAnd body p))
  | AE_And_Exists_Swap_L lv t c body :
      lvar_fresh_in_assertion lv c ->
      assertion_entails σ (LAnd c (LExists lv t body)) (LExists lv t (LAnd c body))
  | AE_Ite_True cond A B :
      assertion_entails σ (LAnd (LIte cond A B) (LExprA cond)) A
  | AE_Ite_False cond A B :
      (* No typing premise needed: LExprA (LUnOp NotBoolOp cond) holding at
         all already forces cond to evaluate to Some (LitBool false) --
         NotBoolOp's own interp_lexpr case gives None (so LExpr_holds is
         False, vacuously) for every other outcome. *)
      assertion_entails σ (LAnd (LIte cond A B) (LExprA (LUnOp NotBoolOp cond))) B
  | AE_Ite_Bool_True cond A B lv :
      (* Recovers cond itself (not just A) from an indirect boolean
         witness lv, tagged onto each LIte branch's own tail -- unlike
         AE_Ite_True, the fact in hand isn't cond directly but lv = true,
         so which branch actually holds has to be inferred: the else_
         branch's own tag (lv = false) would contradict it. *)
      assertion_entails σ
        (LAnd (LIte cond (LAnd A (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
                          (LAnd B (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false))))))
              (LExprA (LVar lv)))
        (LAnd A (LExprA cond))
  | AE_Ite_Bool_False cond A B lv :
      assertion_entails σ
        (LAnd (LIte cond (LAnd A (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
                          (LAnd B (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false))))))
              (LExprA (LUnOp NotBoolOp (LVar lv))))
        B
  | AE_LExpr_Subst_Eq_Congr lv lv2 A :
      (* "Swap one already-bound lvar for another, given they're
         co-asserted equal": substituting lv2 for lv throughout a
         qf_assertion A, plus the LExprA fact that lv and lv2 currently
         agree, is enough to recover A itself (unlike
         AE_Exists_ValIntro, lv/lv2 are both already ambient here -- no
         fresh binder is introduced or eliminated). *)
      qf_assertion A ->
      assertion_entails σ
        (LAnd (LExprA (LBinOp EqOp (LVar lv) (LVar lv2))) (subst A (<[lv := LVar lv2]> ∅)))
        A
  | AE_Exists_Rename_Intro lv lv2 t A :
      (* Like AE_Exists_Intro (wraps in a fresh existential using an
         ambient value as witness), but the witness comes from a
         *different* already-ambient lvar lv2 -- A is stated in terms of
         lv2 throughout (via subst), and gets rebound under a fresh lv
         using lv2's own current value. Subsumes AE_Exists_Intro
         (lv2 = lv, subst is then a no-op) as a special case, not stated
         as one to keep AE_Exists_Intro's own simpler soundness proof. *)
      σ lv = t -> σ lv2 = t -> qf_assertion A ->
      assertion_entails σ (subst A (<[lv := LVar lv2]> ∅)) (LExists lv t A)
  | AE_LExprA_Impl e1 e2 :
      (* interp_lexpr/LExpr_holds are plain, total functions of LExpr and
         symb_map -- no Sigma/Gamma/GhostConfig/invTokenG involved at all
         -- so any Coq-level implication between two LExpr_holds facts
         (e.g. RA-specific arithmetic, as in counter_monotonic.v's own
         fpuValid bridging) lifts directly, uniformly in mp. *)
      (forall mp, LExpr_holds e1 mp -> LExpr_holds e2 mp) ->
      assertion_entails σ (LExprA e1) (LExprA e2)
  | AE_LExprA_True e :
      (* Special case of AE_LExprA_Impl with no source LExprA to hang the
         implication off of: an LExpr that's unconditionally true (e.g.
         LVal (LitBool true)) can be introduced from nothing, needed for
         AssertRule's own use as GhostSkip (Assert (Val (LitBool true))). *)
      (forall mp, LExpr_holds e mp) ->
      assertion_entails σ (LPure True) (LExprA e)
  | AE_GhostOwn_Chunk_Eq e fld r chunk1 chunk2 :
      (* Unconditional (no co-asserted equality needed, unlike
         AE_LExpr_Subst_Eq_Congr): chunk1/chunk2 interp-agree at *every*
         mp, e.g. two different closed LExprs computing the same ground
         RA element -- LGhostOwn's own translation only ever consults its
         chunk argument through interp_lexpr, so this is a direct
         congruence. *)
      (forall mp, interp_lexpr chunk1 mp = interp_lexpr chunk2 mp) ->
      assertion_entails σ (LGhostOwn e fld r chunk1) (LGhostOwn e fld r chunk2).

  (* assertion_entails is closed under renaming every lvar occurrence in
     both sides by a fixed ren, needed for WeakeningRule's own two
     assertion_entails premises in the RavenHoareTriple renaming theorem
     below. Most cases are purely structural (rename_assertion is a
     homomorphism, so it commutes with the rule's own conclusion pattern
     automatically after simpl); the binder-introducing/eliminating rules
     (AE_Exists_Mono/Intro/Elim/And_Swap) need Hren_typ/ren_not_reserved-
     style side-condition transport, and AE_Exists_ValIntro/
     AE_LExpr_Subst_Eq_Congr/AE_Exists_Rename_Intro need
     rename_assertion_subst_singleton to push rename through their own
     subst. AE_LExprA_Impl/AE_GhostOwn_Chunk_Eq are semantic (universally
     quantified over mp), transported via interp_lexpr_rename/
     LExpr_holds_rename by precomposing the witness mp with ren. *)
  Lemma assertion_entails_rename (ren : lvar -> lvar) (Hinj : Inj (=) (=) ren)
      (Hren_res : ∀ lv, is_reserved lv → ren lv = lv)
      (σ : lvar_typs) (Hren_typ : ∀ lv, σ (ren lv) = σ lv) (A B : assertion) :
    assertion_entails σ A B →
    assertion_entails σ (rename_assertion ren A) (rename_assertion ren B).
  Proof using G ghost_heap_name ghost_heap_namespace inv_namespace_map.
    induction 1; simpl.
    - (* AE_Refl *) apply AE_Refl.
    - (* AE_Trans *) eapply AE_Trans; eassumption.
    - (* AE_And_Mono *) apply AE_And_Mono; assumption.
    - (* AE_And_Comm *) apply AE_And_Comm.
    - (* AE_And_Assoc_R *) apply AE_And_Assoc_R.
    - (* AE_And_Assoc_L *) apply AE_And_Assoc_L.
    - (* AE_And_Elim_L *) apply AE_And_Elim_L.
    - (* AE_And_Elim_R *) apply AE_And_Elim_R.
    - (* AE_And_True_Intro *) apply AE_And_True_Intro.
    - (* AE_And_True_Elim *) apply AE_And_True_Elim.
    - (* AE_True_Intro *) apply AE_True_Intro.
    - (* AE_Pure *) apply AE_Pure. assumption.
    - (* AE_Exists_Mono *) apply AE_Exists_Mono; [rewrite Hren_typ; assumption | assumption].
    - (* AE_Exists_Intro *) apply AE_Exists_Intro. rewrite Hren_typ. assumption.
    - (* AE_Exists_ValIntro *)
      rename H into Hty, H0 into Htv, H1 into Hqf.
      rewrite (rename_assertion_subst_singleton ren Hinj A lv (LVal w)). simpl.
      apply AE_Exists_ValIntro.
      + rewrite Hren_typ. exact Hty.
      + exact Htv.
      + exact (qf_assertion_rename ren A Hqf).
    - (* AE_Exists_Elim *)
      rename H into Hty, H0 into Hfresh.
      apply AE_Exists_Elim.
      + rewrite Hren_typ. exact Hty.
      + exact (lvar_fresh_in_assertion_rename ren Hinj lv Q Hfresh).
      + assumption.
    - (* AE_Exists_And_Swap_R *)
      apply AE_Exists_And_Swap_R. exact (lvar_fresh_in_assertion_rename ren Hinj lv p H).
    - (* AE_And_Exists_Swap_L *)
      apply AE_And_Exists_Swap_L. exact (lvar_fresh_in_assertion_rename ren Hinj lv c H).
    - (* AE_Ite_True *) apply AE_Ite_True.
    - (* AE_Ite_False *) apply AE_Ite_False.
    - (* AE_Ite_Bool_True *) apply AE_Ite_Bool_True.
    - (* AE_Ite_Bool_False *) apply AE_Ite_Bool_False.
    - (* AE_LExpr_Subst_Eq_Congr *)
      rename H into Hqf.
      rewrite (rename_assertion_subst_singleton ren Hinj A lv (LVar lv2)). simpl.
      apply AE_LExpr_Subst_Eq_Congr. exact (qf_assertion_rename ren A Hqf).
    - (* AE_Exists_Rename_Intro *)
      rename H into Hty1, H0 into Hty2, H1 into Hqf.
      rewrite (rename_assertion_subst_singleton ren Hinj A lv (LVar lv2)). simpl.
      apply AE_Exists_Rename_Intro.
      + rewrite Hren_typ. exact Hty1.
      + rewrite Hren_typ. exact Hty2.
      + exact (qf_assertion_rename ren A Hqf).
    - (* AE_LExprA_Impl *)
      rename H into Himpl.
      apply AE_LExprA_Impl. intros mp Hh.
      apply (LExpr_holds_rename ren e2 mp).
      apply (LExpr_holds_rename ren e1 mp) in Hh.
      exact (Himpl _ Hh).
    - (* AE_LExprA_True *)
      rename H into Htrue.
      apply AE_LExprA_True. intros mp.
      apply (LExpr_holds_rename ren e mp). exact (Htrue _).
    - (* AE_GhostOwn_Chunk_Eq *)
      rename H into Heq.
      apply AE_GhostOwn_Chunk_Eq. intros mp.
      rewrite !interp_lexpr_rename. exact (Heq (fun x => mp (ren x))).
  Qed.

  Lemma assertion_entails_and_stack_exists_swap (σ : lvar_typs) (stk : stack) (v : lvar) (t : typ) (body p : assertion) :
    fresh_lvar stk v ->
    lvar_fresh_in_assertion v p ->
    assertion_entails σ (LAnd (LStack stk) (LAnd (LExists v t body) p))
                       (LExists v t (LAnd (LStack stk) (LAnd body p))).
  Proof.
    intros Hfresh_stk Hfresh_p.
    eapply AE_Trans.
    - eapply AE_And_Mono; [exact (AE_Refl σ (LStack stk)) | exact (AE_Exists_And_Swap_R σ v t body p Hfresh_p)].
    - exact (AE_And_Exists_Swap_L σ v t (LStack stk) (LAnd body p) Hfresh_stk).
  Qed.

  Fixpoint field_list_to_assertion lexpr fld_vals  := match fld_vals with
  | [] => LPure true
  | (fld,val) :: fld_vals => LAnd (LOwn lexpr fld (LVal (trnsl_val val))) (field_list_to_assertion lexpr fld_vals)
  end.

  (* Ghost-field counterpart of field_list_to_assertion, for
     HeapAllocRule's second, ghost-field initialization list: each triple
     (fld, r, x) contributes an LGhostOwn fact for a freshly-minted ghost
     cell holding x : RA_carrier (ra_map r). *)
  Fixpoint field_list_to_ghost_assertion lexpr (ghost_fld_vals : list (fld_name * ra_elem)) :=
    match ghost_fld_vals with
    | [] => LPure true
    | (fld, existT r x) :: ghost_fld_vals =>
        LAnd (LGhostOwn lexpr fld r (LVal (LitRAElem (existT r x))))
             (field_list_to_ghost_assertion lexpr ghost_fld_vals)
    end.

  (* Both field-list-to-assertion builders only ever thread lexpr through
     unchanged at each step (the field/value pairs are literals, inert
     under rename_lexpr), so renaming commutes with them by a trivial
     induction on the list -- needed for HeapAllocRule's own conclusion. *)
  Lemma field_list_to_assertion_rename (ren : lvar -> lvar) (lexpr : LExpr) (fld_vals : list (fld_name * lang.val)) :
    rename_assertion ren (field_list_to_assertion lexpr fld_vals) =
    field_list_to_assertion (rename_lexpr ren lexpr) fld_vals.
  Proof.
    induction fld_vals as [| [fld val] fld_vals IH]; simpl; [reflexivity |].
    rewrite IH. reflexivity.
  Qed.

  Lemma field_list_to_ghost_assertion_rename (ren : lvar -> lvar) (lexpr : LExpr)
      (ghost_fld_vals : list (fld_name * ra_elem)) :
    rename_assertion ren (field_list_to_ghost_assertion lexpr ghost_fld_vals) =
    field_list_to_ghost_assertion (rename_lexpr ren lexpr) ghost_fld_vals.
  Proof.
    induction ghost_fld_vals as [| [fld [r x]] ghost_fld_vals IH]; simpl; [reflexivity |].
    rewrite IH. reflexivity.
  Qed.

  Inductive RavenHoareTriple :
  pvar_typs -> lvar_typs ->
  assertion ->
      stmt -> maskAnnot ->
  assertion -> Prop :=

  | VarAssignmentRule ρ σ stk mask v lv e lexpr t :
    trnsl_expr_lExpr stk e = Some lexpr ->
    inf_expr ρ e = Some t ->
    fresh_lvar stk lv ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LStack stk)
        (Assign v e) mask
      (LExists lv t
        (LAnd
          (LStack (<[v := lv]> stk))
          (LExprA (LBinOp EqOp (LVar lv) lexpr))
        )
      )

  (* chunk is an LExpr (not a concrete val), mirroring HeapWriteRule/
     CASSuccRule/FPURule: the field's currently-owned chunk need not be a
     literal (e.g. it may be an invariant's own existentially-bound
     witness). Reused unchanged in the postcondition, so -- as with
     CASFailRule's old_chunk -- needs lvar_x ∉ its fvars to justify that its
     evaluated value is stable under the postcondition's stack update. *)
  | HeapReadRule ρ σ stk mask x e chunk fld lexpr_e lvar_x t :
    trnsl_expr_lExpr stk e = Some lexpr_e ->
    inf_lexpr σ chunk = Some t ->
    fresh_lvar stk lvar_x ->
    lvar_x ∉ lexpr_fvars chunk ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LOwn lexpr_e fld chunk))
        (FldRd x e fld) mask
      (LExists lvar_x t (LAnd
        (LStack (<[x := lvar_x]> stk))
        (LAnd
          (LOwn lexpr_e fld chunk)
          (LExprA (LBinOp EqOp (LVar lvar_x) chunk))
        )
      ))

  (* e need not translate to a literal LVal: lexpr (e.g. a variable holding a
     previously-read value) becomes the new chunk directly, since chunk is
     itself an LExpr -- no separate equality-fact conjunct needed. The old
     chunk's evaluability comes for free from the precondition (unpacking
     LOwn's own existential); the new chunk (going into the postcondition)
     doesn't have a givens to unpack, so expr_well_defined is required
     explicitly, mirroring CASSuccRule's inf_expr premise for its location. *)
  | HeapWriteRule ρ σ stk mask v fld e old_chunk lv lexpr :
    stk !! v = Some lv ->
    trnsl_expr_lExpr stk e = Some lexpr ->
    expr_well_defined ρ e ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LOwn (LVar lv) fld old_chunk))
        (FldWr v fld e) mask
      (LAnd (LStack stk) (LOwn (LVar lv) fld lexpr))


  (* ghost_fld_vals is a second, ghost-field initialization list, alongside
     the real fld_vals -- not itself part of Alloc's own AST (Alloc's
     fs list stays real-fields-only, matching AllocStep's operational
     semantics, which never touches ghost state at all). Each ghost field
     mints a genuinely fresh ghost cell (see Wghost_alloc), so this list
     need not correspond to anything already present anywhere; freshness
     of the newly-allocated location is what makes it sound, exactly as
     for fld_vals's own real fields. The reservation that backs this
     freshness (ghost_dom, see simp_raven_lang/ghost_state.v) is grown by
     wp_alloc in lockstep with the real heap, at the very same fresh_loc,
     which needs the real heap to actually grow too whenever ghost fields
     are being allocated -- hence fld_vals must be nonempty whenever
     ghost_fld_vals is. *)
  | HeapAllocRule ρ σ stk mask x fld_vals ghost_fld_vals lvar_x :
    fresh_lvar stk lvar_x ->
    NoDup fld_vals.*1 ->
    NoDup ghost_fld_vals.*1 ->
    (ghost_fld_vals ≠ [] -> fld_vals ≠ []) ->
    Forall (λ fgv, (RA_inst (ra_map (projT1 fgv.2))).(valid) (projT2 fgv.2)) ghost_fld_vals ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
       (LStack stk)
        (Alloc x fld_vals) mask
      (LExists lvar_x TpLoc (LAnd (LStack (<[x := lvar_x]> stk))
        (LAnd (field_list_to_assertion (LVar lvar_x) fld_vals)
              (field_list_to_ghost_assertion (LVar lvar_x) ghost_fld_vals))))

  | ProcCallRuleRet ρ σ stk mask x proc_name args lexprs lvar_x proc_record :
    fresh_lvar stk lvar_x ->
    proc_map !! proc_name = Some proc_record ->
    length args = length (proc_args_of proc_record) ->
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    stk_type_compat ρ σ stk ->
    (* Local, per-application side conditions, appended last (rather than
       next to fresh_lvar/the Hargs premise they logically belong with) so
       this case's existing default-named hypotheses in trnsl.v's
       iInduction keep their names: the fresh result lvar and the call's
       own argument lexprs stay out of the reserved ("$") namespace
       reserved for an authored contract's own internal existentials (see
       ProgramWF's pwf_*_binders_reserved). Checkable
       by whoever builds a concrete derivation (just don't pick
       "$"-prefixed names) -- unlike a blanket "no stack/lexpr anywhere
       ever uses a reserved name" assumption, which is simply false
       (nothing stops an adversarial stk from doing so). *)
    ¬ is_reserved lvar_x ->
    (* Bundled via /\, not a separate premise: trnsl.v's rrl_validity
       pattern-matches this constructor's premises via auto-generated,
       positional Hn names (iInduction's blank "| | |" branch), so adding a
       genuinely new positional premise here would silently renumber every
       later Hn reference throughout that large, delicate proof. Folding
       the new fact into the existing last premise via /\ keeps the
       positional count (and every existing Hn name) unchanged; the few
       call sites that consume this premise directly there project out the
       half they need. *)
    Forall (fun le => ∀ v, v ∈ lexpr_fvars le → ¬ is_reserved v) lexprs ∧
    (* The caller's own current mask must already include whatever the
       callee itself needs to open (proc_required_mask) -- mirrors the
       standard Iris pattern for a spec that internally opens an invariant N (∀ E, ↑N ⊆ E → ...)
       rather than an unconditional ∀ mask, which is what
       all_proc_specs_valid_raven/_iris need on the *other* end to even be
       satisfiable for a callee that opens an invariant at all. *)
    proc_required_mask proc_record ⊆ mask ->
    let subst_map := list_to_map (zip (proc_args_of proc_record).*1 lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (subst (proc_precond_of proc_record) subst_map))
        (Call x proc_name args) mask
      (LExists lvar_x (ρ x) (LAnd (LStack (<[x := lvar_x]> stk)) (subst (proc_postcond_of proc_record) (<[ "#ret_val" := LVar lvar_x]> subst_map))))

  | SequenceRule ρ σ mask a1 c1 a2 c2 a3 :
    RavenHoareTriple ρ σ
      a1
        c1 mask
      a2
    ->
    RavenHoareTriple ρ σ
      a2
        c2 mask
      a3
    ->
    RavenHoareTriple ρ σ
      a1
        (Seq c1 c2) mask
      a3

  (* Q is a fully generic shared postcondition (not decomposed into a fixed
     LStack stk2 plus a rest q): the two branches need not leave the stack
     in the same shape (e.g. one calls a procedure, binding a fresh result
     variable into the stack, while the other is a no-op Skip that doesn't)
     -- each branch is free to reach that same Q via its own route (e.g. an
     unused LExists wrapping introduced via entails_exists_intro on one
     side, and entails_exists_mono weakening away a real stack extension on
     the other), rather than being forced to agree on one concrete stk2.
     This matches wp_if_t/wp_if_f's own operational shape already: their
     own postcondition parameter is a fully generic iProp, with no
     stack/rest split required. *)
  | CondRule ρ σ stk1 mask e s1 s2 p Q lexpr :
    trnsl_expr_lExpr stk1 e = Some lexpr ->
    inf_expr ρ e = Some TpBool ->
    stk_type_compat ρ σ stk1 ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk1) (LAnd p (LExprA (lexpr))) )
        s1 mask
      Q
    ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk1) (LAnd p (LExprA (LUnOp NotBoolOp lexpr))))
        s2 mask
      Q
    ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk1) p)
        (IfS e s1 s2) mask
      Q

  (* stk' (rather than stk again) in the inner triple's postcondition: the
     wrapped stmt is free to change the stack (e.g. a FldRd/CAS/Call binding
     a fresh result var), and that stack delta threads out to the outer
     conclusion's own postcondition. Sound because the invariant's own
     truth (subst inv_body subst_map) depends only on lexprs/mp, never on
     the stack, so it doesn't care what the stack becomes across the
     block.

     The whole postcondition is further wrapped in LExists lv on both
     sides (lv free to occur inside stk', the "reuse the fresh lvar as its
     own existential binder" pattern already used by HeapReadRule/
     CASSuccRule/VarAssignmentRule): a wrapped FldRd/CAS/Call's own natural
     postcondition puts its fresh result lvar's binding *inside* the very
     LStack that names it (stk[x:=lvar_x]), so LStack itself becomes
     lv-dependent -- entails alone can't pull it out from under the
     existential (that would need evaluating LStack at a different mp than
     the rest), so the block rule has to carry the existential through
     instead of requiring a fixed stk'.

     The earlier, non-existential shape (stk' fixed, no LExists) is not
     lost: whenever stk'/q don't mention lv, entails (LAnd (LStack stk')
     (LAnd body q)) (LExists lv (LAnd (LStack stk') (LAnd body q))) holds
     (introducing an unused existential is free), so that shape is
     recoverable via WeakeningRule for any lv fresh enough for both this
     rule's own premise and that side condition. *)
  | InvAccessBlockRule ρ σ stk stk' mask inv args stmt inv_record p q lv t lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    inv ∈ mask ->
    inv_map !! inv = Some inv_record ->
    length lexprs = length inv_record.(inv_args) ->
    (* Local, per-application reserved-namespace side condition -- see
       ProcCallRuleRet's own copy of this comment. *)
    Forall (fun le => ∀ v, v ∈ lexpr_fvars le → ¬ is_reserved v) lexprs ->
    stk_type_compat ρ σ stk ->
    let subst_map := list_to_map (zip inv_record.(inv_args) lexprs) in
    (* lv is chosen fresh w.r.t. stk, matching HeapReadRule/CASSuccRule's
       own fresh_lvar premise for the very same lvar -- needed so the
       invariant's own substituted truth, and the lexprs naming it, stay
       stable across the mp-update the existential introduces. t (lv's own
       type) is simply carried through unchanged from the wrapped
       statement's own conclusion -- this rule doesn't introduce lv itself,
       just re-closes the invariant around whatever produced it. *)
    fresh_lvar stk lv ->
    ¬ is_reserved lv ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LAnd (subst inv_record.(inv_body) subst_map) p))
        stmt (mask ∖ {[inv]})
      (LExists lv t (LAnd (LStack stk') (LAnd (subst inv_record.(inv_body) subst_map) q))) ->

    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LAnd (LInv inv lexprs) p))
        (InvAccessBlock inv args stmt ) mask
      (LExists lv t (LAnd (LStack stk') (LAnd (LInv inv lexprs) q)))

  (* Establishing an invariant: trade its (instantiated) body for the nominal
     [LInv] fact.  There is deliberately no converse rule -- once shared, an
     invariant stays shared, exactly as with Iris's [inv_alloc]. *)
  | InvAllocRule ρ σ stk mask inv args inv_record p lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs) ->
    inv ∈ mask ->
    inv_map !! inv = Some inv_record ->
    length lexprs = length inv_record.(inv_args) ->
    (* Local, per-application reserved-namespace side condition -- see
       ProcCallRuleRet's own copy of this comment. *)
    Forall (fun le => ∀ v, v ∈ lexpr_fvars le → ¬ is_reserved v) lexprs ->
    stk_type_compat ρ σ stk ->
    let subst_map := list_to_map (zip inv_record.(inv_args) lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LAnd (subst inv_record.(inv_body) subst_map) p))
        (FoldInv inv args) mask
      (LAnd (LStack stk) (LAnd (LInv inv lexprs) p))

  | PredUnfoldRule ρ σ stk mask pred args pred_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs)
    ->
    pred_map !! pred = Some pred_record ->
    stk_type_compat ρ σ stk ->
    let subst_map := list_to_map (zip pred_record.(pred_args) lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LPred pred lexprs))
        (UnfoldPred pred args) mask
      (LAnd (LStack stk) (subst pred_record.(pred_body) subst_map))

  | PredFoldRule ρ σ stk mask pred args pred_record lexprs :
    (map (fun arg => trnsl_expr_lExpr stk arg) args) = (map (fun lexpr => Some lexpr) lexprs)
    ->
    stk_type_compat ρ σ stk ->
    pred_map !! pred = Some pred_record ->
    let subst_map := list_to_map (zip pred_record.(pred_args) lexprs) in
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (subst pred_record.(pred_body) subst_map))
        (FoldPred pred args) mask
      (LAnd (LStack stk) (LPred pred lexprs))

  (* e_old/e_new need not translate to literal constants: lexpr_old/lexpr_new
     (e.g. a variable holding a previously-read RA value, or an expression
     built from comp/frame over one) become the ghost chunks directly, since
     chunk is itself an LExpr. fpuValid is checked at the assertion level via
     RAFpuValidOp instead of a separate Coq-level Prop premise, so no
     old_val/new_val metavariables are needed at all. lexpr_old's evaluability
     comes for free from the precondition; lexpr_new (going into the
     postcondition) needs its own typing premise, as in CASSuccRule/
     HeapWriteRule. *)
  | FPURule ρ σ stk mask e l_expr fld r e_old e_new lexpr_old lexpr_new :
    trnsl_expr_lExpr stk e = Some l_expr ->
    trnsl_expr_lExpr stk e_old = Some lexpr_old ->
    trnsl_expr_lExpr stk e_new = Some lexpr_new ->
    inf_expr ρ e_new = Some (TpRA r) ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LAnd (LGhostOwn l_expr fld r lexpr_old)
                                (LExprA (LBinOp RAFpuValidOp lexpr_old lexpr_new))))
        (Fpu e fld r e_old e_new) mask
        (LAnd (LStack stk) (LGhostOwn l_expr fld r lexpr_new))

  | FrameRule ρ σ mask s p q r :
    RavenHoareTriple ρ σ
      p
        s mask
      q
    ->
    RavenHoareTriple ρ σ
      (LAnd p r)
        s mask
      (LAnd q r)

  | WeakeningRule ρ σ mask p p' q q' c :
    RavenHoareTriple ρ σ
      p
        c mask
      q
    ->
    assertion_entails σ p' p ->
    assertion_entails σ q q' ->

    RavenHoareTriple ρ σ
      p'
        c mask
      q'

  | SkipRule ρ σ stk mask p :
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) p)
        SkipS mask
      (LAnd (LStack stk) p)

  (* The precondition doesn't force the owned chunk to already equal e2
     (which would require knowing, before the atomic step, which outcome
     would occur -- unknowable in general when old_chunk is an invariant's
     own existential witness, e.g. counterInv's "v", genuinely independent
     of whatever value a prior read compared against). old_chunk is a
     fully generic LExpr; the postcondition's own LIte branches on the
     *same* equality the CAS itself decides operationally (old_chunk =
     lexpr2), covering both outcomes in a single rule so the caller
     decides which branch applies only *after* seeing lvar_v's own value.
     e2/e3 need not translate to literal constants (see HeapWriteRule/
     FPURule's identical generalization): lexpr2/lexpr3 become the
     compared value / new chunk directly, since chunk is itself an LExpr.
     lvar_v ∉ old_chunk's fvars justifies that its evaluated value is
     stable under the postcondition's stack update (needed for the
     failure branch, which reuses old_chunk unchanged; the success branch
     introduces a fresh chunk expression, so doesn't need this). e2's
     evaluatedness needs its own expr_well_defined premise (not free from
     the precondition), just like e3's. *)
  | CASRule ρ σ stk mask v e1 fld e2 e3 lvar_v lexpr1 lexpr2 lexpr3 old_chunk :
    fresh_lvar stk lvar_v ->
    inf_expr ρ e1 = Some (TpLoc) ->
    expr_well_defined ρ e2 ->
    expr_well_defined ρ e3 ->
    lvar_v ∉ lexpr_fvars old_chunk ->
    trnsl_expr_lExpr stk e1 = Some lexpr1 ->
    trnsl_expr_lExpr stk e2 = Some lexpr2 ->
    trnsl_expr_lExpr stk e3 = Some lexpr3 ->
    stk_type_compat ρ σ stk ->
      RavenHoareTriple ρ σ
        (LAnd (LStack stk) (LOwn lexpr1 fld old_chunk))
          (CAS v e1 fld e2 e3) mask
        (LExists lvar_v TpBool (LAnd (LStack (<[v := lvar_v]> stk))
          (LIte (LBinOp EqOp old_chunk lexpr2)
            (LAnd (LOwn lexpr1 fld lexpr3) (LExprA (LBinOp EqOp (LVar lvar_v) (LVal (LitBool true)))))
            (LAnd (LOwn lexpr1 fld old_chunk) (LExprA (LBinOp EqOp (LVar lvar_v) (LVal (LitBool false))))))))

  (* Standard Hoare-logic exists-elimination, at the top of the precondition:
     unfolding an invariant/predicate whose body ties two ownership facts
     together via a shared witness (e.g. counterInv's
     `exists v: Int, own(h, v) && own(c, v)`), or an earlier statement's own
     witness-carrying postcondition (e.g. CASSuccRule's own conclusion, which
     an immediately following statement needs to consume via SequenceRule),
     produces an LExists that no other rule can consume directly.
     Deliberately subst-free: body keeps v as an ordinary free lvar in
     both premise and conclusion, so the soundness proof re-interprets
     the *same* derivation at mp[v:=v'] rather than needing an AST-level
     substitution -- which is what lets this rule handle LStack-containing
     bodies too (subst is a no-op on LStack's own stored map, see
     lvar_fresh_in_assertion's comment). Re-entering the premise's own
     soundness obligation at mp[v:=v'] needs v' to have v's declared type
     t; since LExists's own translation restricts its witness to
     typ_val_match t (see trnsl_assertion_str's LExists case), that comes
     for free from destructuring the incoming existential -- no separate
     witness-well-typedness side condition needed. Callers needing the
     LAnd (LStack stk) (LAnd (LExists v body) p) shape get there via a
     separate, purely structural commuting entailment (v fresh for stk/p),
     rather than baking it into the core rule. *)
  | ExistsElimRule ρ σ mask v t body c q :
    σ v = t ->
    lvar_fresh_in_assertion v q ->
    RavenHoareTriple ρ σ body c mask q ->
    RavenHoareTriple ρ σ
      (LExists v t body)
        c mask
      q

  (* A ghost-only, proof-only check: e must already be provable from the
     ambient assertion state (p, folded in as a co-asserted LExprA lexpr,
     mirroring CondRule's own precondition shape rather than a separate
     assertion_entails premise), and leaves the state unchanged -- like
     SkipRule, but translates to None' (no physical step), unlike SkipS.
     GhostSkip := Assert (Val (LitBool true)) is the "do nothing, costs no
     step" filler this enables (see the Assert constructor's own comment in
     stmt, and counter_monotonic.v's incr_body). Placed last among
     RavenHoareTriple's constructors (rather than next to SkipRule, its
     closest sibling): any induction over RavenHoareTriple sees it as the
     final case, so appending a future constructor here never renumbers
     rrl_validity's own numbered-bullet case references in trnsl.v, the
     way inserting one in the middle would. *)
  | AssertRule ρ σ stk mask e p lexpr :
    trnsl_expr_lExpr stk e = Some lexpr ->
    inf_expr ρ e = Some TpBool ->
    stk_type_compat ρ σ stk ->
    RavenHoareTriple ρ σ
      (LAnd (LStack stk) (LAnd p (LExprA lexpr)))
        (Assert e) mask
      (LAnd (LStack stk) (LAnd p (LExprA lexpr)))
  .

  (* The main renaming theorem: transports a RavenHoareTriple derivation
     built against one choice of fresh lvars to any other, via a fixed
     injective ren that must be the identity on the reserved namespace
     (so it never disturbs an authored contract's own internal witnesses,
     see rename_assertion's own comment) and type-preserving under σ.
     Needed because raven_soundness_core's own proof obtains its
     proc_entry_lvars via an opaque existential-elimination
     (fresh_proc_entry_lvars), so all_proc_specs_valid_raven must hold for
     *every* dll, not just the one a concrete derivation happens to be
     written against.

     Hwf is needed wherever a rule substitutes an authored proc/inv/pred
     body: rename_assertion_subst_commute needs that body's own binders to
     be reserved and its fvars bounded by the substitution's domain, both
     ProgramWF facts.

     Hpred_empty (pred_map is empty) is an extra restriction beyond
     ProgramWF, needed only for PredUnfoldRule/PredFoldRule: unlike
     InvAccessBlockRule/InvAllocRule, those two rules carry no
     length lexprs = length pred_record.(pred_args) premise, so
     rename_subst_cond_pred_body's dom-subst_map bound (which needs that
     length fact) isn't derivable from the rule's own premises for an
     arbitrary predicate call. Every Program with an empty pred_map (e.g.
     counter_monotonic.v's) can never actually reach these two cases at
     all (pred_map !! pred = Some _ is unsatisfiable), so the restriction
     costs nothing there; lifting it in general would need that missing
     length premise added to the rules themselves. *)
  Lemma RavenHoareTriple_rename (ren : lvar -> lvar) (Hinj : Inj (=) (=) ren)
      (Hren_res : ∀ lv, is_reserved lv → ren lv = lv)
      (Hwf : ProgramWF) (Hpred_empty : pred_map = ∅)
      (ρ : pvar_typs) (σ : lvar_typs) (Hren_typ : ∀ lv, σ (ren lv) = σ lv)
      (p q : assertion) (c : stmt) (mask : maskAnnot) :
    RavenHoareTriple ρ σ p c mask q →
    RavenHoareTriple ρ σ (rename_assertion ren p) c mask (rename_assertion ren q).
  Proof.
    induction 1 as
      [ ρ σ stk mask v lv e lexpr t Htr Hinf Hfresh Hcompat
      | ρ σ stk mask x e chunk fld lexpr_e lvar_x t Htr Hinf Hfresh Hnotfv Hcompat
      | ρ σ stk mask v fld e old_chunk lv lexpr Hstk Htr Hwd Hcompat
      | ρ σ stk mask x fld_vals ghost_fld_vals lvar_x Hfresh HND1 HND2 Hne Hvalid Hcompat
      | ρ σ stk mask x pn args lexprs lvar_x proc_record Hfresh Hpm Hlen Hargs Hcompat Hnotres Hlexprs_notres_and_mask
      | ρ σ mask a1 c1 a2 c2 a3 H1 IH1 H2 IH2
      | ρ σ stk1 mask e s1 s2 p Q lexpr Htr Hinf Hcompat H1 IH1 H2 IH2
      | ρ σ stk stk' mask inv args stmt inv_record p q lv t lexprs
          Hargs Hmem Hinvm Hlen Hnotres_lexprs Hcompat subm Hfresh Hnotres_lv Hbody IHbody
      | ρ σ stk mask inv args inv_record p lexprs Hargs Hmem Hinvm Hlen Hnotres_lexprs Hcompat
      | ρ σ stk mask pred args pred_record lexprs Hargs Hpredm Hcompat
      | ρ σ stk mask pred args pred_record lexprs Hargs Hcompat Hpredm
      | ρ σ stk mask e l_expr fld r e_old e_new lexpr_old lexpr_new Htr1 Htr2 Htr3 Hinf Hcompat
      | ρ σ mask s p q r H IH
      | ρ σ mask p p' q q' c H IH Hent1 Hent2
      | ρ σ stk mask p Hcompat
      | ρ σ stk mask v e1 fld e2 e3 lvar_v lexpr1 lexpr2 lexpr3 old_chunk
          Hfresh Hinf Hwd2 Hwd3 Hnotfv Htr1 Htr2 Htr3 Hcompat
      | ρ σ mask v t body c q Hty Hfresh H IH
      | ρ σ stk mask e p lexpr Htr Hinf Hcompat ]; simpl.
    - (* VarAssignmentRule *)
      rewrite fmap_insert.
      apply VarAssignmentRule.
      + exact (trnsl_expr_lExpr_rename ren stk e lexpr Htr).
      + exact Hinf.
      + exact (fresh_lvar_rename ren Hinj stk lv Hfresh).
      + exact (stk_type_compat_rename ren ρ σ Hren_typ stk Hcompat).
    - (* HeapReadRule *)
      rewrite fmap_insert.
      apply HeapReadRule.
      + exact (trnsl_expr_lExpr_rename ren stk e lexpr_e Htr).
      + rewrite (inf_lexpr_rename ren σ Hren_typ chunk). exact Hinf.
      + exact (fresh_lvar_rename ren Hinj stk lvar_x Hfresh).
      + rewrite lexpr_fvars_rename. intro Hc.
        apply elem_of_map in Hc as [y [Heqy Hy]]. apply Hinj in Heqy. subst y. exact (Hnotfv Hy).
      + exact (stk_type_compat_rename ren ρ σ Hren_typ stk Hcompat).
    - (* HeapWriteRule *)
      apply HeapWriteRule.
      + rewrite lookup_fmap Hstk. reflexivity.
      + exact (trnsl_expr_lExpr_rename ren stk e lexpr Htr).
      + exact Hwd.
      + exact (stk_type_compat_rename ren ρ σ Hren_typ stk Hcompat).
    - (* HeapAllocRule *)
      rewrite fmap_insert.
      rewrite (field_list_to_assertion_rename ren (LVar lvar_x) fld_vals).
      rewrite (field_list_to_ghost_assertion_rename ren (LVar lvar_x) ghost_fld_vals).
      simpl.
      apply HeapAllocRule.
      + exact (fresh_lvar_rename ren Hinj stk lvar_x Hfresh).
      + exact HND1.
      + exact HND2.
      + exact Hne.
      + exact Hvalid.
      + exact (stk_type_compat_rename ren ρ σ Hren_typ stk Hcompat).
    - (* ProcCallRuleRet *)
      have Hlen' : length lexprs = length (proc_args_of proc_record).
      { assert (Hll : length args = length lexprs).
        { assert (Hh := f_equal (@length _) Hargs). rewrite !map_length in Hh. exact Hh. }
        rewrite <- Hll. exact Hlen. }
      rewrite fmap_insert.
      rewrite (rename_assertion_subst_commute ren Hren_res (proc_precond_of proc_record) _
        (rename_subst_cond_proc_precond Hwf pn proc_record Hpm lexprs Hlen')).
      rewrite (rename_assertion_subst_commute ren Hren_res (proc_postcond_of proc_record) _
        (rename_subst_cond_proc_postcond Hwf pn proc_record Hpm lexprs lvar_x Hlen')).
      rewrite fmap_insert. rewrite (fmap_list_to_map_zip (rename_lexpr ren) (proc_args_of proc_record).*1 lexprs).
      simpl.
      apply ProcCallRuleRet.
      + exact (fresh_lvar_rename ren Hinj stk lvar_x Hfresh).
      + exact Hpm.
      + exact Hlen.
      + exact (trnsl_expr_lExpr_rename_list ren stk args lexprs Hargs).
      + exact (stk_type_compat_rename ren ρ σ Hren_typ stk Hcompat).
      + exact (ren_not_reserved ren Hinj Hren_res lvar_x Hnotres).
      + exact (conj (Forall_lexpr_not_reserved_rename ren Hinj Hren_res lexprs (proj1 Hlexprs_notres_and_mask))
                 (proj2 Hlexprs_notres_and_mask)).
    - (* SequenceRule *)
      exact (SequenceRule ρ σ mask (rename_assertion ren a1) c1 (rename_assertion ren a2) c2
        (rename_assertion ren a3) (IH1 Hren_typ) (IH2 Hren_typ)).
    - (* CondRule *)
      apply (CondRule ρ σ (ren <$> stk1) mask e s1 s2
        (rename_assertion ren p) (rename_assertion ren Q) (rename_lexpr ren lexpr)).
      + exact (trnsl_expr_lExpr_rename ren stk1 e lexpr Htr).
      + exact Hinf.
      + exact (stk_type_compat_rename ren ρ σ Hren_typ stk1 Hcompat).
      + exact (IH1 Hren_typ).
      + exact (IH2 Hren_typ).
    - (* InvAccessBlockRule *)
      have IHbody' := IHbody Hren_typ.
      simpl in IHbody'.
      rewrite (rename_assertion_subst_commute ren Hren_res inv_record.(inv_body) _
        (rename_subst_cond_inv_body Hwf inv inv_record Hinvm lexprs Hlen)) in IHbody'.
      rewrite (fmap_list_to_map_zip (rename_lexpr ren) inv_record.(inv_args) lexprs) in IHbody'.
      apply (InvAccessBlockRule ρ σ (ren <$> stk) (ren <$> stk') mask inv args stmt inv_record
        (rename_assertion ren p) (rename_assertion ren q) (ren lv) t (map (rename_lexpr ren) lexprs)).
      + exact (trnsl_expr_lExpr_rename_list ren stk args lexprs Hargs).
      + exact Hmem.
      + exact Hinvm.
      + rewrite map_length. exact Hlen.
      + exact (Forall_lexpr_not_reserved_rename ren Hinj Hren_res lexprs Hnotres_lexprs).
      + exact (stk_type_compat_rename ren ρ σ Hren_typ stk Hcompat).
      + exact (fresh_lvar_rename ren Hinj stk lv Hfresh).
      + exact (ren_not_reserved ren Hinj Hren_res lv Hnotres_lv).
      + exact IHbody'.
    - (* InvAllocRule *)
      rewrite (rename_assertion_subst_commute ren Hren_res inv_record.(inv_body) _
        (rename_subst_cond_inv_body Hwf inv inv_record Hinvm lexprs Hlen)).
      rewrite (fmap_list_to_map_zip (rename_lexpr ren) inv_record.(inv_args) lexprs).
      apply InvAllocRule.
      + exact (trnsl_expr_lExpr_rename_list ren stk args lexprs Hargs).
      + exact Hmem.
      + exact Hinvm.
      + rewrite map_length. exact Hlen.
      + exact (Forall_lexpr_not_reserved_rename ren Hinj Hren_res lexprs Hnotres_lexprs).
      + exact (stk_type_compat_rename ren ρ σ Hren_typ stk Hcompat).
    - (* PredUnfoldRule: unreachable when pred_map is empty. *)
      exfalso. rewrite Hpred_empty in Hpredm. rewrite lookup_empty in Hpredm. discriminate.
    - (* PredFoldRule: unreachable when pred_map is empty. *)
      exfalso. rewrite Hpred_empty in Hpredm. rewrite lookup_empty in Hpredm. discriminate.
    - (* FPURule *)
      apply FPURule.
      + exact (trnsl_expr_lExpr_rename ren stk e l_expr Htr1).
      + exact (trnsl_expr_lExpr_rename ren stk e_old lexpr_old Htr2).
      + exact (trnsl_expr_lExpr_rename ren stk e_new lexpr_new Htr3).
      + exact Hinf.
      + exact (stk_type_compat_rename ren ρ σ Hren_typ stk Hcompat).
    - (* FrameRule *)
      apply FrameRule. exact (IH Hren_typ).
    - (* WeakeningRule *)
      eapply WeakeningRule.
      + exact (IH Hren_typ).
      + exact (assertion_entails_rename ren Hinj Hren_res σ Hren_typ p' p Hent1).
      + exact (assertion_entails_rename ren Hinj Hren_res σ Hren_typ q q' Hent2).
    - (* SkipRule *)
      apply SkipRule. exact (stk_type_compat_rename ren ρ σ Hren_typ stk Hcompat).
    - (* CASRule *)
      rewrite fmap_insert.
      apply CASRule.
      + exact (fresh_lvar_rename ren Hinj stk lvar_v Hfresh).
      + exact Hinf.
      + exact Hwd2.
      + exact Hwd3.
      + rewrite lexpr_fvars_rename. intro Hc.
        apply elem_of_map in Hc as [y [Heqy Hy]]. apply Hinj in Heqy. subst y. exact (Hnotfv Hy).
      + exact (trnsl_expr_lExpr_rename ren stk e1 lexpr1 Htr1).
      + exact (trnsl_expr_lExpr_rename ren stk e2 lexpr2 Htr2).
      + exact (trnsl_expr_lExpr_rename ren stk e3 lexpr3 Htr3).
      + exact (stk_type_compat_rename ren ρ σ Hren_typ stk Hcompat).
    - (* ExistsElimRule *)
      apply ExistsElimRule.
      + rewrite Hren_typ. exact Hty.
      + exact (lvar_fresh_in_assertion_rename ren Hinj v q Hfresh).
      + exact (IH Hren_typ).
    - (* AssertRule *)
      apply (AssertRule ρ σ (ren <$> stk) mask e (rename_assertion ren p) (rename_lexpr ren lexpr)).
      + exact (trnsl_expr_lExpr_rename ren stk e lexpr Htr).
      + exact Hinf.
      + exact (stk_type_compat_rename ren ρ σ Hren_typ stk Hcompat).
  Qed.

End RavenLogic.

Section LExpr_embed.
  (* TODO: Figure out the right way to do this deep embedding *)
  Definition EqOp_refl : forall a b mp, LExpr_holds (LBinOp EqOp a b) mp -> LExpr_holds (LBinOp EqOp b a) mp.
  Proof.
    intros a b mp H.
    unfold LExpr_holds.
    destruct (interp_lexpr b mp) as [vb|] eqn:Hb;
    destruct (interp_lexpr a mp) as [va|] eqn:Ha.
    - (* Both Some: need val_beq vb va = true from val_beq va vb = true *)
      assert (Hba : interp_lexpr (LBinOp EqOp b a) mp =
                    Some (LitBool (val_beq vb va))).
      { simpl. rewrite Hb. rewrite Ha. done. }
      assert (Hab : interp_lexpr (LBinOp EqOp a b) mp =
                    Some (LitBool (val_beq va vb))).
      { simpl. rewrite Ha. rewrite Hb. done. }
      rewrite Hba. simpl.
      unfold LExpr_holds in H. rewrite Hab in H. simpl in H.
      destruct (val_beq va vb) eqn:Hvavb.
      + apply internal_val_dec_bl in Hvavb. subst.
        rewrite (internal_val_dec_lb vb vb eq_refl). done.
      + discriminate H.
    - (* vb = Some, va = None: EqOp a b evaluates to None, H is False *)
      assert (Hab_none : interp_lexpr (LBinOp EqOp a b) mp = None).
      { simpl. rewrite Ha. done. }
      unfold LExpr_holds in H. rewrite Hab_none in H. contradiction.
    - (* vb = None, va = Some: EqOp a b evaluates to None, H is False *)
      assert (Hab_none : interp_lexpr (LBinOp EqOp a b) mp = None).
      { simpl. rewrite Ha. rewrite Hb. done. }
      unfold LExpr_holds in H. rewrite Hab_none in H. contradiction.
    - (* Both None: EqOp a b evaluates to None, H is False *)
      assert (Hab_none : interp_lexpr (LBinOp EqOp a b) mp = None).
      { simpl. rewrite Ha. done. }
      unfold LExpr_holds in H. rewrite Hab_none in H. contradiction.
  Qed.

  Definition EqOp_trans : forall a b c mp, LExpr_holds (LBinOp EqOp a b) mp -> LExpr_holds (LBinOp EqOp b c) mp -> LExpr_holds (LBinOp EqOp a c) mp.
  Proof.
    intros a b c mp Hab Hbc.
    unfold LExpr_holds in *.
    destruct (interp_lexpr b mp) as [vb|] eqn:Hb.
    2: { (* b = None: Hab is False *)
      assert (Hab_none : interp_lexpr (LBinOp EqOp a b) mp = None).
      { simpl. rewrite Hb. destruct (interp_lexpr a mp); done. }
      rewrite Hab_none in Hab. contradiction. }
    destruct (interp_lexpr a mp) as [va|] eqn:Ha.
    2: { assert (Hab_none : interp_lexpr (LBinOp EqOp a b) mp = None).
      { simpl. rewrite Ha. done. }
      rewrite Hab_none in Hab. contradiction. }
    destruct (interp_lexpr c mp) as [vc|] eqn:Hc.
    2: { assert (Hbc_none : interp_lexpr (LBinOp EqOp b c) mp = None).
      { simpl. rewrite Hb. rewrite Hc. done. }
      rewrite Hbc_none in Hbc. contradiction. }
    (* All Some case *)
    assert (Hab_eq : interp_lexpr (LBinOp EqOp a b) mp = Some (LitBool (val_beq va vb))).
    { simpl. rewrite Ha. rewrite Hb. done. }
    assert (Hbc_eq : interp_lexpr (LBinOp EqOp b c) mp = Some (LitBool (val_beq vb vc))).
    { simpl. rewrite Hb. rewrite Hc. done. }
    assert (Hac_eq : interp_lexpr (LBinOp EqOp a c) mp = Some (LitBool (val_beq va vc))).
    { simpl. rewrite Ha. rewrite Hc. done. }
    rewrite Hab_eq in Hab. simpl in Hab.
    rewrite Hbc_eq in Hbc. simpl in Hbc.
    rewrite Hac_eq. simpl.
    injection Hab as Hab'. injection Hbc as Hbc'.
    apply internal_val_dec_bl in Hab'. subst vb.
    apply internal_val_dec_bl in Hbc'. subst vc.
    rewrite (internal_val_dec_lb va va eq_refl). done.
  Qed.

  (* Helper: substituting an evaluating expression preserves interp_lexpr up to map update. *)
  Lemma interp_lexpr_subst_some : forall var (le : LExpr) mp (v_le : val),
    interp_lexpr le mp = Some v_le ->
    forall e, interp_lexpr (lexpr_subst e (<[var := le]> ∅)) mp =
              interp_lexpr e (fun x => if (x =? var)%string then v_le else mp x).
  Proof.
    intros var le mp v_le Hle e. induction e; simpl;
      [| reflexivity | rewrite IHe; reflexivity | rewrite IHe1; rewrite IHe2; reflexivity
       | rewrite IHe1; rewrite IHe2; rewrite IHe3; reflexivity | reflexivity].
    destruct (decide (x = var)) as [-> | Hne].
    - rewrite lookup_insert. simpl. rewrite Hle. rewrite String.eqb_refl. reflexivity.
    - rewrite lookup_insert_ne; [|intro H; apply Hne; exact (eq_sym H)].
      rewrite lookup_empty. simpl.
      rewrite <- String.eqb_neq in Hne. rewrite Hne. reflexivity.
  Qed.

  (* Helper: substituting a None-evaluating expression gives None or same result. *)
  Lemma interp_lexpr_subst_none_eval : forall var (le : LExpr) mp,
    interp_lexpr le mp = None ->
    forall e, interp_lexpr (lexpr_subst e (<[var := le]> ∅)) mp = None \/
              interp_lexpr (lexpr_subst e (<[var := le]> ∅)) mp = interp_lexpr e mp.
  Proof.
    intros var le mp Hle e. induction e; simpl;
      [ (* LVar *)
      | (* LVal *) right; reflexivity
      | (* LUnOp *) destruct IHe as [H|H]; rewrite H; [left; destruct op; reflexivity | right; reflexivity]
      | (* LBinOp *)
        destruct IHe1 as [H1|H1]; destruct IHe2 as [H2|H2];
        [ left; rewrite H1; destruct op; reflexivity
        | left; rewrite H1; destruct op; reflexivity
        | left; rewrite H1; rewrite H2; destruct op; destruct (interp_lexpr e1 mp) as [v1|]; try reflexivity; destruct v1 as [ | | | |[]]; reflexivity
        | right; rewrite H1; rewrite H2; reflexivity ]
      | (* LIfE *)
        destruct IHe1 as [H1|H1];
        [ left; rewrite H1; reflexivity
        | rewrite H1; destruct (interp_lexpr e1 mp) as [v|];
          [ destruct v as [b|i| |l|[]];
            [ destruct b;
              [ destruct IHe2 as [H2|H2]; [left; exact H2 | right; exact H2]
              | destruct IHe3 as [H3|H3]; [left; exact H3 | right; exact H3] ]
            | left; reflexivity | left; reflexivity | left; reflexivity | left; reflexivity ]
          | left; reflexivity ] ]
      | (* LStuck *) left; reflexivity ].
    destruct (decide (x = var)) as [-> | Hne].
    - rewrite lookup_insert. simpl. left. exact Hle.
    - rewrite lookup_insert_ne; [|intro H; apply Hne; exact (eq_sym H)].
      rewrite lookup_empty. simpl. right. reflexivity.
  Qed.

  Definition EqOp_subst : forall var le e mp, LExpr_holds (LBinOp EqOp (LVar var) le) mp -> LExpr_holds e mp -> LExpr_holds (lexpr_subst e (<[ var := le]> ∅)) mp.
  Proof.
    intros var le e mp H1 H2.
    unfold LExpr_holds in *.
    destruct (interp_lexpr le mp) as [v_le|] eqn:Hle.
    - (* Some case: extract mp var = v_le from H1 *)
      simpl in H1; rewrite Hle in H1; simpl in H1.
      destruct (val_beq (mp var) v_le) eqn:Hbeq; [|discriminate H1].
      apply internal_val_dec_bl in Hbeq; subst v_le.
      assert (Hmap : (fun x => if (x =? var)%string then mp var else mp x) = mp)
        by (apply FunctionalExtensionality.functional_extensionality; intro x;
            destruct (String.eqb_spec x var) as [->|_]; reflexivity).
      rewrite (interp_lexpr_subst_some var le mp (mp var) Hle e); rewrite Hmap; exact H2.
    - (* None case: H1 is False since LBinOp EqOp (LVar var) le evaluates to None *)
      assert (H1_none : interp_lexpr (LBinOp EqOp (LVar var) le) mp = None).
      { simpl. rewrite Hle. done. }
      rewrite H1_none in H1. contradiction.
  Qed.

  Definition EqpOp_LVal : forall v1 v2 mp, LExpr_holds (LBinOp EqOp (LVal v1) (LVal v2)) mp -> v1 = v2.
  Proof.
    intros v1 v2 mp H.
    unfold LExpr_holds in H. simpl in H.
    destruct (val_beq v1 v2) eqn:Heq.
    - apply internal_val_dec_bl. exact Heq.
    - discriminate H.
  Qed.

End LExpr_embed.



(* ── The shared world backing invariant assertions ────────────────────────
   [LInv inv args] owns a fragment of [invtoken_names inv]'s authoritative set
   of established argument vectors.  [Winv inv] is the matching authority,
   holding the invariant's body for each established vector.  It is Timeless,
   so it can live under a native Iris [inv] and be opened with
   [inv_acc_timeless] -- no later, no later credit.  It is defined *after*
   [trnsl_assertion] is total, so there is no circularity. *)

End WithProgram.
