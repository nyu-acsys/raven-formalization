From stdpp Require Export binders strings.
From stdpp Require Import countable.
Require Import Eqdep_dec.
From stdpp Require Import gmap list sets coPset.
From stdpp Require Import namespaces.

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
   infrastructure), so it's placed here rather than where the original file
   had it (further down, after interp_lexpr/lexpr_subst). *)
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

(* Layer 0 (see local/parameters-redesign.md): the camera capability
   invTokenG needs, without the concrete invtoken_names assignment --
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

(* LExists binder variables of an assertion (does NOT descend into LInv/LPred bodies).
   Moved ahead of InvRecord/PredRecord/ProcRecord's own well-formedness
   definitions (InvBodyWF etc. below) so they can state their own "## dom M"
   premise in terms of it -- see local/binders.md. *)
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
   witness) -- see local/binders.md. Discharged via the record's own
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

(* The elaborated module, bundled -- see local/parameters-redesign.md's
   "Architecture" section. Positioned here (not right after proc_set/etc.
   above): ProcRecord/InvRecord/PredRecord all need to already exist, and
   StackFree below needs inv_map/pred_map ambient, so this is the earliest
   point everything lines up. Not ra_map/ra_set (see that decision in the
   same doc) -- those stay Global Parameter in lang.v. *)
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

(* Scope-correct free variables: unlike assertion_lexpr_fvars, this
   subtracts LExists's own bound variable from its body's fvars, so it
   never over-approximates through a genuine existential (see Finding 2 in
   local/binders.md -- assertion_lexpr_fvars deliberately keeps the bug,
   since the reserved-namespace design tolerates it; this function is the
   accurate version needed where that tolerance isn't good enough, namely
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
   mention -- see subst_map_avoids_reserved below and local/binders.md
   for the full argument. This is what lets ProgramWF's own
   binder-freshness obligations become purely syntactic, local checks
   instead of an unsatisfiable "forall M" disjointness. *)
Definition is_reserved (v : lvar) : Prop := String.prefix "$" v = true.

Global Instance is_reserved_dec (v : lvar) : Decision (is_reserved v).
Proof. unfold is_reserved. apply _. Defined.

(* Bundles both projections of "M was built by the ordinary framework
   machinery, not by hand-picking a reserved name": neither its keys
   (formal-argument/entry-lvar names) nor the fvars of its values (lvars
   some caller's stack happens to use) ever land in the reserved
   namespace. Whoever supplies this for a concrete M is asserting it was
   actually built that way -- e.g. via trnsl_expr_lExpr against an
   ordinary symbolic stack, or via fresh_proc_entry_lvars/Hσ_rich, itself
   expected to be strengthened to avoid the reserved prefix wherever it
   is finally discharged for a concrete program (see local/binders.md's
   deferred item; not yet needed to typecheck this file). *)
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
   generalization below, and local/binders.md). Instantiating R := ∅
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
   variable -- see local/binders.md). *)
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
   program into Iris, distinct from Program (what a .rav author writes) --
   see local/parameters-redesign.md's "Architecture" section. Not Gamma:
   Gamma_type sits inside the (already-closed, by this point) nested
   Section Translation below, so it can't be bundled here without redoing
   that relocation; stays its own Variable for now. *)
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
     LForall -- it doesn't subtract the bound variable, see
     local/binders.md). pwf_proc_binders_reserved below is what makes
     those binder names harmless despite not being formal arguments. *)
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
     so they can never collide with any substitution map's own fvars --
     replaces the old pwf_proc_binders_fresh, which quantified over *every*
     M unconditionally and so was unsatisfiable whenever pre/postcond had a
     genuine existential. See local/binders.md. *)
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
     ProgramWF witness (see local/binders.md). This field is currently
     unused elsewhere in the codebase; pwf_pred_fvars_bounded (its
     predicate analogue, used by subst_congr_step's LPred case) already
     always has this length fact on hand from StackFree's own SF_Pred/
     SF_Inv premise, so this is purely a matter of exposing it here too. *)
  pwf_inv_fvars_bounded :
    ∀ inv_nm r args, inv_map !! inv_nm = Some r → length args = length r.(inv_args) →
      ∀ v, v ∈ assertion_lexpr_fvars (subst r.(inv_body) (list_to_map (zip r.(inv_args) args))) →
        v ∈ (⋃ (lexpr_fvars <$> args) : gset lvar) ∨ v ∈ assertion_exists_binders r.(inv_body);

  (* Analogous to pwf_proc_binders_reserved: an invariant body's own
     binders are drawn from the reserved namespace. Replaces the old,
     unconditional-over-M pwf_inv_binders_fresh. *)
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
     are drawn from the reserved namespace. Replaces the old,
     unconditional-over-M pwf_pred_binders_fresh. *)
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

(* Isolated, single-use extraction of CallTp's new proc_call_ret_well_typed
   premise, keyed to an already-known proc_entry (via Some-injectivity on
   proc_map's lookup) rather than CallTp's own existentially-bound one --
   lets call sites avoid threading this through the large, already-fragile
   auto-numbered "inversion Hwelldef; subst ..." used elsewhere for Call's
   soundness case (see local/parameters-redesign.md). *)
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

  Definition transport {A B : Type} (H : A = B) (x : A) : B :=
    eq_rect A id x _ H.

  Lemma transport_sym : forall (A B : Type) (H : A = B) (x : B),
     (transport H (transport (eq_sym H) x)) = x.
  Proof.
    intros. unfold transport. destruct H. simpl. reflexivity.
  Qed.

  Lemma transport_cancel : forall (A B : Type) (H : A = B) (x : A),
    transport (eq_sym H) (transport H x) = x.
  Proof.
    intros. unfold transport. destruct H. simpl. reflexivity.
  Qed.

  Lemma eq_rect_transport_comp : forall (R: RA_Pack) (U : Type) (Heq_car : (RA_carrier R) = U) (x : (RA_carrier R)) (c : U),
  eq_rect (RA_carrier R) (λ T : Type, T → T → T) (RA_inst R).(comp) U Heq_car (transport Heq_car x) c = 
  transport Heq_car ((RA_inst R).(comp) x (transport (eq_sym Heq_car) c)).
Proof.
  intros. unfold transport. destruct Heq_car. simpl. reflexivity.
Qed.


  Lemma eq_rect_transport_valid : forall (R: RA_Pack) (U: Type) (Heq_car : (RA_carrier R) = U) (x : (RA_carrier R)),
    eq_rect (RA_carrier R) (λ T : Type, T -> Prop) (RA_inst R).(valid) U Heq_car (transport Heq_car x) ->
    (RA_inst R).(valid) x.
  Proof.
    intros. unfold transport in *. destruct Heq_car. simpl in *. done.
  Qed.

  Lemma eq_rect_transport_valid_inv : forall (R: RA_Pack) (U: Type) (Heq_car : (RA_carrier R) = U) (x : (RA_carrier R)),
    (RA_inst R).(valid) x ->
    eq_rect (RA_carrier R) (λ T : Type, T -> Prop) (RA_inst R).(valid) U Heq_car (transport Heq_car x).
    
  Proof.
    intros. unfold transport in *. destruct Heq_car. simpl in *. done.
  Qed.

  Lemma eq_rect_transport_inv_comp_valid : forall (R: RA_Pack) (U: Type) (Heq_car : (RA_carrier R) = U) (y : (RA_carrier R)) (c: U),
    (RA_inst R).(valid) ((RA_inst R).(comp) y (transport (eq_sym Heq_car) c)) ->
    eq_rect (RA_carrier R) (λ T : Type, T → Prop) (RA_inst R).(valid) U Heq_car (transport Heq_car ((RA_inst R).(comp) y (transport (eq_sym Heq_car) c))).
  Proof.
    intros. unfold transport in *. destruct Heq_car. simpl in *. done.
  Qed.

  (* Narrowed to ra_set (Open item 1, local/parameters-redesign.md): Γ
     used to be universally quantified over *every* RA_Pack, but every
     actual call site only ever applies it as Γ (ra_map r) for some
     r : ra_name -- and a concrete Γ witness genuinely cannot be total
     over arbitrary RA_Pack (infinitely many possible carrier types, so
     no finite Sigma could provide a matching camera slot for every one).
     option-valued (not a r ∈ ra_set proof obligation threaded through
     every call site): a concrete Γ only needs to answer for the
     program's own, finite ra_set; every other r maps to None, mirroring
     inv_map/pred_map's own partial-lookup shape (trnsl_assertion_str's
     LGhostOwn case below matches on this the same way LInv/LPred already
     match on inv_map/pred_map !! _). *)
  Definition Γ_witness (r : ra_name) := { i : I & { U : ucmra |
      CmraDiscrete U /\
      { Heq_car : RA_carrier (ra_map r) = ucmra_car U |
          ucmra_cmraR U = Gs i /\
          ucmra_op U = eq_rect (RA_carrier (ra_map r)) (fun T => T -> T -> T) ((RA_inst (ra_map r)).(comp)) (ucmra_car U) Heq_car /\
          ucmra_valid U = eq_rect (RA_carrier (ra_map r)) (fun T => T -> Prop) ((RA_inst (ra_map r)).(valid)) (ucmra_car U) Heq_car
      }
  } } .

  (* A bespoke option, not stdlib's: Γ_witness r's own large (ucmra-valued)
     type doesn't fit stdlib option's fixed universe, triggering a
     universe inconsistency -- irrelevant to what this needs (just "found
     or not"), so a fresh, unconstrained Inductive sidesteps it. *)
  Inductive Γ_answer (r : ra_name) :=
  | Γ_found (w : Γ_witness r)
  | Γ_absent.
  Arguments Γ_found {r} w.
  Arguments Γ_absent {r}.

  Definition Γ_type := forall r : ra_name, Γ_answer r.

  Lemma RAPack_fpuValid (Γ: Γ_type) (r : ra_name) (w : Γ_witness r) :
    Γ r = Γ_found w ->
    forall x y : RA_carrier (ra_map r),
      let '(existT i (exist _ U (conj Hdis (exist _ Heq_car (conj Hcmra (conj Hop Hvalid)))))) := w in
      (RA_inst (ra_map r)).(fpuValid) x y -> (transport Heq_car x) ~~> (transport Heq_car y).
  Proof.
    intros Heq x y.
    destruct w as [i [U [Hdisc [Heq_car [Hindx [Hcomp Hval]]]]]].
    intros Hfpu.

    intros n c Hvalid.
    destruct c as [c|].

    - simpl in *.

    (* make the dot-notation explicit so we can rewrite the op *)
    change (transport Heq_car x ⋅ c) with (ucmra_op U (transport Heq_car x) c) in Hvalid.
    rewrite Hcomp in Hvalid.
    (* bring the context back to the (ra_map r)-side by destructing the equality *)
    apply cmra_discrete_valid_iff.
    apply cmra_discrete_valid_iff in Hvalid.
    change (✓ (transport Heq_car y ⋅ c)) with (ucmra_valid U (transport Heq_car y ⋅ c)).
    rewrite Hval.
    unfold transport.

    set (cR := transport (eq_sym Heq_car) c).
    assert ((RA_inst (ra_map r)).(valid) ((RA_inst (ra_map r)).(comp) y cR)). {
      apply (fpuAxiom x y); [done | ].

      rewrite eq_rect_transport_comp in Hvalid.
      unfold cR.
      change (✓ transport Heq_car (comp x (transport (eq_sym Heq_car) c))) with ((ucmra_valid U) (transport Heq_car ((RA_inst (ra_map r)).(comp) x (transport (eq_sym Heq_car) c)))) in Hvalid.

      rewrite Hval in Hvalid.
      apply (eq_rect_transport_valid (ra_map r) (ucmra_car U) Heq_car). done.
    }

    subst cR.

    change (eq_rect (RA_carrier (ra_map r)) (λ T : Type, T → Prop) (RA_inst (ra_map r)).(valid) U Heq_car ((ucmra_op U) (eq_rect (RA_carrier (ra_map r)) id y U Heq_car) c)).

    rewrite Hcomp.
    rewrite eq_rect_transport_comp.

    apply eq_rect_transport_inv_comp_valid.
    done.

    - simpl in *. apply cmra_discrete_valid_iff. apply cmra_discrete_valid_iff in Hvalid.

    apply (fpuAxiom x y) in Hfpu.
    destruct Hfpu as [_ [HvVal _]].
    change (@cmra.valid (cmra_car (ucmra_cmraR U)) (cmra_valid (ucmra_cmraR U))) with (ucmra_valid U).
    rewrite Hval.
    apply eq_rect_transport_valid_inv. done.
  Qed.


  Context {Γ : Γ_type}.

Section Translation.

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
       parameters no longer need to agree on a single global type via σ. *)
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
         dll_args. See local/binders.md. *)
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
  Qed.


  Fixpoint trnsl_assertion_str (F : assertion -d> stack_id -d> symb_map -d> (iPropO Σ)) 
    (a: assertion) (stk_id: stack_id) (mp: symb_map) : 
     (iPropO Σ) :=      
      match a with
    | LProc p p_e => 
      match p_e with
        Proc args locals pre post body => 
          match trnsl_stmt body with
          | None' =>
            (proc_tbl_chunk p (
              lang.Proc p args locals lang.SkipS
            ))
          | Some' stmt =>
            (proc_tbl_chunk p (
              lang.Proc p args locals stmt
            ))
          | Error => 
            (False)%I
          end
      end
    | LStack σ => (stack_frame_own stk_id (symb_stk_to_stk_frm σ mp))
    | LExprA l_expr => 
      (⌜LExpr_holds l_expr mp⌝%I)
    
    | LPure p => (⌜ p ⌝%I)
    (* chunk is an LExpr, not a concrete val: existentially quantify over the
       concrete value it evaluates to, guarded by a purity fact. If chunk
       doesn't evaluate (or isn't RA-typed with the right ra_name, for
       LGhostOwn), no witness exists and the assertion is (correctly) False. *)
    | LOwn l_expr fld chunk_expr =>
      (∃ l: lang.loc, ∃ chunk : val, (
        ⌜LExpr_holds (LBinOp EqOp l_expr (LVal (LitLoc l))) mp⌝ ∗
        ⌜interp_lexpr chunk_expr mp = Some chunk⌝ ∗
        (l#fld ↦{ 1 } (trnsl_lval chunk))
        )%I)%I

    (* Fragment of Wghost's authoritative map (see Section GhostHeapWorld,
       below), keyed by (l, fld) via heap_addr -- not a bare per-key own, so
       that HeapAllocRule can *mint* fresh ghost ownership by growing one
       standing authoritative resource, the same way LOwn's own fragments
       come from growing heap_interp. *)
    (* γ names a freshly own_alloc'd ghost cell for this (l, fld) key,
       recorded once and for all in Wghost's own standing map (see Section
       GhostHeapWorld below) -- the map only ever holds this naming
       binding, agreement-typed and never updated post-insertion; the
       actual RA ownership lives directly at γ via a bare own, exactly as
       in the original ghost_map design, so FPURule's frame-preserving
       update never has to touch the map at all. *)
    | LGhostOwn l_expr fld RAPack chunk_expr =>
      (* RAPack not in ra_set (Γ RAPack = Γ_absent) is vacuously True,
         mirroring LInv/LPred's own "name not declared" case below --
         never actually reached for a well-formed program's own LGhostOwn
         nodes, only needed for trnsl_assertion_str's own totality. *)
      match Γ RAPack with
      | Γ_absent => True%I
      | Γ_found (existT i (exist _ U (conj Hdis (exist _ Heq_car (conj Heq_cmra (conj Hop Hvalid)))))) =>
        let HinG := inGs_inG i in
        (∃ l : lang.loc, ∃ chunk : RA_carrier (ra_map RAPack), ∃ γ : gname, (
          ⌜LExpr_holds (LBinOp EqOp l_expr (LVal (LitLoc l))) mp⌝ ∗
          ⌜interp_lexpr chunk_expr mp = Some (LitRAElem (existT RAPack chunk))⌝ ∗
          own ghost_heap_name
             (◯ {[ heap_addr_constr l fld := to_agree γ ]} : authR (gmapUR heap_addr (agreeR gnameO))) ∗
          (own γ (transport (f_equal cmra_car Heq_cmra) (transport Heq_car chunk)) (inG0 := HinG))))%I
      end
    | LForall v _t body =>
       (∀ v':lang.val, (trnsl_assertion_str F body stk_id mp))%I

    (* Restricted to witnesses matching t (the binder's declared type, per
       the LExists/LForall AST's own type annotation) -- this is what lets
       ExistsElimRule's soundness case get its witness's well-typedness for
       free from destructuring the existential, rather than needing a
       separate witness_well_typed side-condition proved per rule use. *)
    | LExists v t body =>
      (∃ v': val, ⌜typ_val_match t v'⌝ ∗
           (trnsl_assertion_str F body stk_id (λ x, if String.eqb x v then v' else mp x))
    )%I
    
    (* Generalizes LImpl's own translation (an implication is the special
       case whose else_ branch, LPure True, makes the second conjunct
       trivially provable regardless of cnd). *)
    | LIte cnd then_ else_ =>
      ((⌜LExpr_holds cnd mp⌝ -∗ (trnsl_assertion_str F then_ stk_id mp)) ∧
       (⌜¬ LExpr_holds cnd mp⌝ -∗ (trnsl_assertion_str F else_ stk_id mp)))%I

    (* Nominal, and therefore a *base case*: an invariant assertion owns a
       discrete fragment naming the invariant and its argument vector.  It
       never looks at the body, so it needs no guard and -- crucially -- is
       Timeless.  The body lives in the shared world [Winv] below. *)
    | LInv inv' args =>
        match inv_map !! inv' with
        | Some _ =>
          (∃ vs : list val,
            ⌜Forall2 (λ le v, interp_lexpr le mp = Some v) args vs⌝ ∗
            own (invtoken_names inv') (◯ ({[ vs ]} : inv_argsUR)))%I
        | None => True%I
        end

    | LPred pred args =>
        match pred_map !! pred with
        | Some pred_record =>
          let subst_map := list_to_map (zip pred_record.(pred_args) args) in

          (F (subst pred_record.(pred_body) subst_map) stk_id mp)%I
        | None => True%I
        end

    | LAnd a1 a2 => 
      ( ((trnsl_assertion_str F a1 stk_id mp) ∗ (trnsl_assertion_str F a2 stk_id mp)))%I
    end.

  Definition trnsl_assertion_pre (F : assertion -d> stack_id -d> symb_map -d> (iPropO Σ)) :
     assertion -d> stack_id -d> symb_map -d> (iPropO Σ) := λ a stk_id mp, trnsl_assertion_str F a stk_id mp.

(* --- The translation is a Knaster--Tarski least fixpoint --------------------
   Neither [LInv] (a discrete ownership fragment) nor [LPred] (a plain
   recursive call) is guarded any more, so [trnsl_assertion_pre] is no longer
   Contractive and the step-indexed [fixpoint] is unavailable.  What survives
   -- and is all that is needed -- is monotonicity in the [⊢] order, which is
   exactly [BiMonoPred].  Raven's typing rules (resource assertions never
   appear under negation or to the left of an implication) are what guarantee
   it.  -------------------------------------------------------------------- *)

Definition trnsl_dom : Type := (assertion * stack_id * symb_map)%type.

Definition trnsl_assertion_curry (Φ : leibnizO trnsl_dom → iProp Σ) :
    assertion -d> stack_id -d> symb_map -d> (iPropO Σ) :=
  λ a stk_id mp, Φ (a, stk_id, mp).

Definition trnsl_assertion_F (Φ : leibnizO trnsl_dom → iProp Σ) :
    leibnizO trnsl_dom → iProp Σ :=
  λ x, trnsl_assertion_str (trnsl_assertion_curry Φ) x.1.1 x.1.2 x.2.

(* Every function out of a leibnizO domain is non-expansive. *)
Local Lemma leibniz_dom_ne (Φ : leibnizO trnsl_dom → iProp Σ) : NonExpansive Φ.
Proof. intros n x y Heq. change (x = y) in Heq. by subst. Qed.

(* Monotonicity of the assertion-translation functional, by structural
   induction on the assertion.  [LPred] is the only clause that consults its
   argument. *)
Local Lemma trnsl_assertion_str_mono
    (Φ Ψ : assertion -d> stack_id -d> symb_map -d> (iPropO Σ)) (a : assertion) :
  ∀ (stk : stack_id) (mp : symb_map),
  □ (∀ a' stk' mp', Φ a' stk' mp' -∗ Ψ a' stk' mp') ⊢
  trnsl_assertion_str Φ a stk mp -∗ trnsl_assertion_str Ψ a stk mp.
Proof.
  induction a; intros stk mp; simpl.
  - (* LProc *) iIntros "_ H". iExact "H".
  - (* LStack *) iIntros "_ H". iExact "H".
  - (* LExprA *) iIntros "_ H". iExact "H".
  - (* LPure *) iIntros "_ H". iExact "H".
  - (* LOwn *) iIntros "_ H". iExact "H".
  - (* LGhostOwn *)
    destruct (Γ r) as [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ];
      iIntros "_ H"; iExact "H".
  - (* LForall *)
    iIntros "#Hmon H" (v').
    iDestruct (IHa stk mp with "Hmon") as "IH".
    iDestruct ("H" $! v') as "H'". by iApply "IH".
  - (* LExists *)
    iIntros "#Hmon H". iDestruct "H" as (v') "[%Htyp H]". iExists v'. iSplitR; [done|].
    iDestruct (IHa stk (λ x, if String.eqb x v then v' else mp x) with "Hmon") as "IH".
    by iApply "IH".
  - (* LIte *)
    iIntros "#Hmon H". iSplit.
    + iIntros "%Hc". iDestruct (IHa1 stk mp with "Hmon") as "IH1". iApply "IH1". iDestruct "H" as "[H _]". by iApply "H".
    + iIntros "%Hc". iDestruct (IHa2 stk mp with "Hmon") as "IH2". iApply "IH2". iDestruct "H" as "[_ H]". by iApply "H".
  - (* LInv: base case, no recursive occurrence *)
    destruct (inv_map !! inv_name0); iIntros "_ H"; iExact "H".
  - (* LPred: the one genuinely recursive clause *)
    destruct (pred_map !! pred_name0) as [pred_record|];
      [| iIntros "_ H"; iExact "H"].
    iIntros "#Hmon H". by iApply "Hmon".
  - (* LAnd *)
    iIntros "#Hmon [H1 H2]".
    iDestruct (IHa1 stk mp with "Hmon") as "IH1".
    iDestruct (IHa2 stk mp with "Hmon") as "IH2".
    iSplitL "H1"; [by iApply "IH1" | by iApply "IH2"].
Qed.

Global Instance trnsl_assertion_F_mono : BiMonoPred trnsl_assertion_F.
Proof.
  split; last first.
  { intros Φ _ n x y Heq. change (x = y) in Heq. by subst. }
  intros Φ Ψ HΦ HΨ. iIntros "#Hmon" ([[a stk] mp]).
  rewrite /trnsl_assertion_F /=.
  iApply (trnsl_assertion_str_mono (trnsl_assertion_curry Φ) (trnsl_assertion_curry Ψ) a stk mp).
  rewrite /trnsl_assertion_curry.
  iIntros "!>" (a' stk' mp') "H". by iApply "Hmon".
Qed.

Definition trnsl_assertion : assertion -d> stack_id -d> symb_map -d> (iPropO Σ) :=
  λ a stk mp, bi_least_fixpoint trnsl_assertion_F (a, stk, mp).

Global Arguments trnsl_assertion : simpl never.

Lemma trnsl_assertion_unfold a stk mp :
  trnsl_assertion a stk mp ≡ trnsl_assertion_pre trnsl_assertion a stk mp.
Proof. exact (least_fixpoint_unfold trnsl_assertion_F (a, stk, mp)). Qed.

(* Per-constructor unfolding lemmas: [trnsl_assertion_unfold] leaves the direct
   subterms in [trnsl_assertion_str]-applied form, which these fold back. *)
Lemma trnsl_assertion_and a1 a2 stk mp :
  trnsl_assertion (LAnd a1 a2) stk mp ⊣⊢
  trnsl_assertion a1 stk mp ∗ trnsl_assertion a2 stk mp.
Proof.
  rewrite (trnsl_assertion_unfold (LAnd a1 a2)) /trnsl_assertion_pre /=.
  apply bi.sep_proper; symmetry; apply trnsl_assertion_unfold.
Qed.

Lemma trnsl_assertion_forall v t body stk mp :
  trnsl_assertion (LForall v t body) stk mp ⊣⊢
  (∀ _ : lang.val, trnsl_assertion body stk mp).
Proof.
  rewrite (trnsl_assertion_unfold (LForall v t body)) /trnsl_assertion_pre /=.
  apply bi.forall_proper. intros _. symmetry. apply trnsl_assertion_unfold.
Qed.

Lemma trnsl_assertion_exists v t body stk mp :
  trnsl_assertion (LExists v t body) stk mp ⊣⊢
  (∃ v' : val, ⌜typ_val_match t v'⌝ ∗ trnsl_assertion body stk (λ x, if String.eqb x v then v' else mp x)).
Proof.
  rewrite (trnsl_assertion_unfold (LExists v t body)) /trnsl_assertion_pre /=.
  apply bi.exist_proper. intros v'. apply bi.sep_proper; [done|]. symmetry. apply trnsl_assertion_unfold.
Qed.

Lemma trnsl_assertion_ite cnd then_ else_ stk mp :
  trnsl_assertion (LIte cnd then_ else_) stk mp ⊣⊢
  (⌜LExpr_holds cnd mp⌝ -∗ trnsl_assertion then_ stk mp) ∧
  (⌜¬ LExpr_holds cnd mp⌝ -∗ trnsl_assertion else_ stk mp).
Proof.
  rewrite (trnsl_assertion_unfold (LIte cnd then_ else_)) /trnsl_assertion_pre /=.
  apply bi.and_proper; apply bi.wand_proper; try done; symmetry; apply trnsl_assertion_unfold.
Qed.

Lemma trnsl_assertion_impl cnd body stk mp :
  trnsl_assertion (LImpl cnd body) stk mp ⊣⊢
  (⌜LExpr_holds cnd mp⌝ -∗ trnsl_assertion body stk mp).
Proof.
  unfold LImpl. rewrite trnsl_assertion_ite.
  rewrite (trnsl_assertion_unfold (LPure True)) /trnsl_assertion_pre /=.
  iSplit.
  - iIntros "[H _] %Hc". by iApply "H".
  - iIntros "H". iSplit.
    + iIntros "%Hc". by iApply "H".
    + iIntros "%Hc". done.
Qed.

(* [LInv] now denotes a discrete ownership fragment, not an Iris [inv]. The
   correspondence with the invariant's body is no longer definitional; it is
   mediated by [Winv] and derived in [Winv_open]/[Winv_alloc] below. *)
Lemma trnsl_inv_validity' inv' args stk mp :
  match inv_map !! inv' with
  | Some _ =>
      trnsl_assertion (LInv inv' args) stk mp ⊣⊢
      (∃ vs : list val,
         ⌜Forall2 (λ le v, interp_lexpr le mp = Some v) args vs⌝ ∗
         own (invtoken_names inv') (◯ ({[ vs ]} : inv_argsUR)))
  | None => True
  end.
Proof.
  destruct (inv_map !! inv') eqn:HInv; try done.
  rewrite (trnsl_assertion_unfold (LInv inv' args)) /trnsl_assertion_pre /=.
  rewrite HInv. done.
Qed.

Lemma trnsl_assertion_LInv_some inv' r args stk mp :
  inv_map !! inv' = Some r →
  trnsl_assertion (LInv inv' args) stk mp ⊣⊢
  (∃ vs : list val, ⌜Forall2 (λ le v, interp_lexpr le mp = Some v) args vs⌝ ∗
                    own (invtoken_names inv') (◯ ({[ vs ]} : inv_argsUR))).
Proof.
  intros Hr. have Hv := trnsl_inv_validity' inv' args stk mp.
  rewrite Hr in Hv. exact Hv.
Qed.

(* [LInv] is a fragment of a core-id (gset) camera, hence duplicable -- which
   is what makes an invariant fact freely shareable, as it must be. *)
Global Instance trnsl_assertion_LInv_persistent inv' args stk mp :
  Persistent (trnsl_assertion (LInv inv' args) stk mp).
Proof.
  destruct (inv_map !! inv') as [r|] eqn:Hr.
  - rewrite (trnsl_assertion_LInv_some inv' r args stk mp Hr). apply _.
  - have Hv := trnsl_inv_validity' inv' args stk mp. rewrite Hr in Hv.
    rewrite (trnsl_assertion_unfold (LInv inv' args)) /trnsl_assertion_pre /=.
    rewrite Hr. apply _.
Qed.

(* [LProc]'s own proc_tbl_chunk fragment is persistent (see its definition),
   so the procedure-registration fact is freely shareable too -- needed so a
   recursive call can keep re-supplying it, the same way an invariant fact
   is freely shareable across an unbounded number of accesses. *)
Global Instance trnsl_assertion_LProc_persistent p pe stk mp :
  Persistent (trnsl_assertion (LProc p pe) stk mp).
Proof.
  rewrite (trnsl_assertion_unfold (LProc p pe)) /trnsl_assertion_pre /=.
  destruct pe. destruct (trnsl_stmt body); apply _.
Qed.

(* Overriding mp at a lvar the assertion doesn't depend on (lvar_fresh_in_assertion)
   leaves its translation unchanged. Unlike its subst-based predecessor this
   covers LStack and LForall -- it never manipulates the AST via subst (a
   no-op on LStack's own stored map, which is exactly why the old lemma had
   to exclude it), just mp directly. LPred still needs excluding: its
   recursion goes through the *global* pred_map table, not a structural
   subterm of a, so a plain induction on a can't produce an induction
   hypothesis for it (the existing subst_congr_cond/least_fixpoint_ind
   machinery handles that shape of problem, but only for StackFree
   assertions -- LStack is exactly what it excludes). Neither of this
   lemma's two target use sites (an invariant body's own existential, or an
   InvAccessBlockRule-style postcondition witness) needs LPred. *)
Lemma trnsl_assertion_mp_irrelevant (v : lvar) (a : assertion) (v' : val) (stk : stack_id) (mp : symb_map) :
  lvar_fresh_in_assertion v a ->
  trnsl_assertion a stk (fun y => if (y =? v)%string then v' else mp y)
  ≡ trnsl_assertion a stk mp.
Proof.
  revert mp.
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
    intros mp Hfresh; simpl in Hfresh.
  - (* LProc *)
    rewrite (trnsl_assertion_unfold (LProc pn pe))
            (trnsl_assertion_unfold (LProc pn pe)) /trnsl_assertion_pre /=.
    destruct pe. destruct (trnsl_stmt body); done.
  - (* LStack *) simpl.
    rewrite (trnsl_assertion_unfold (LStack sg)) (trnsl_assertion_unfold (LStack sg))
            /trnsl_assertion_pre /=.
    assert (symb_stk_to_stk_frm sg (fun y => if (y =? v)%string then v' else mp y)
            = symb_stk_to_stk_frm sg mp) as Heq.
    { unfold symb_stk_to_stk_frm. f_equal.
      apply map_eq. intros v0.
      rewrite !lookup_fmap.
      destruct (sg !! v0) as [lv|] eqn:Hsg; simpl; [ | reflexivity].
      f_equal. f_equal.
      destruct (String.eqb_spec lv v) as [-> | _]; [ | reflexivity].
      exfalso. exact (Hfresh v0 Hsg). }
    rewrite Heq. done.
  - (* LExprA *) simpl.
    rewrite (trnsl_assertion_unfold (LExprA pexp))
            (trnsl_assertion_unfold (LExprA pexp)) /trnsl_assertion_pre /=.
    unfold LExpr_holds. rewrite (interp_lexpr_stable pexp mp v v' Hfresh). done.
  - (* LPure *) simpl.
    rewrite (trnsl_assertion_unfold (LPure pp)) (trnsl_assertion_unfold (LPure pp))
            /trnsl_assertion_pre /=. done.
  - (* LOwn *) simpl. destruct Hfresh as [Hfe Hfc].
    rewrite (trnsl_assertion_unfold (LOwn oe ofld ochunk))
            (trnsl_assertion_unfold (LOwn oe ofld ochunk)) /trnsl_assertion_pre /=.
    apply bi.exist_proper; intros l. apply bi.exist_proper; intros chunk0.
    unfold LExpr_holds. simpl.
    rewrite (interp_lexpr_stable oe mp v v' Hfe) (interp_lexpr_stable ochunk mp v v' Hfc).
    done.
  - (* LGhostOwn *) simpl. destruct Hfresh as [Hfe Hfc].
    rewrite (trnsl_assertion_unfold (LGhostOwn ge gfld gr gchunk))
            (trnsl_assertion_unfold (LGhostOwn ge gfld gr gchunk)) /trnsl_assertion_pre /=.
    destruct (Γ gr) as [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ].
    + apply bi.exist_proper; intros l. apply bi.exist_proper; intros chunk0.
      unfold LExpr_holds. simpl.
      rewrite (interp_lexpr_stable ge mp v v' Hfe) (interp_lexpr_stable gchunk mp v v' Hfc).
      done.
    + done.
  - (* LForall: its own binder is already a no-op in trnsl_assertion_str
       (trnsl_assertion_forall), so this is a direct recursion regardless of
       whether fv = v. *)
    rewrite (trnsl_assertion_forall fv ft fbody stk (fun y => if (y =? v)%string then v' else mp y))
            (trnsl_assertion_forall fv ft fbody stk mp).
    apply bi.forall_proper; intros _. exact (IHf mp Hfresh).
  - (* LExists *)
    rewrite (trnsl_assertion_exists ev et ebody stk (fun y => if (y =? v)%string then v' else mp y))
            (trnsl_assertion_exists ev et ebody stk mp).
    apply bi.exist_proper; intros v''. apply bi.sep_proper; [done|].
    destruct (String.eqb_spec ev v) as [-> | Hne].
    + (* shadowed: the outer update at v is immediately overwritten *)
      assert ((fun y => if (y =? v)%string then v''
                         else (fun z => if (z =? v)%string then v' else mp z) y)
              = (fun y => if (y =? v)%string then v'' else mp y)) as Heq.
      { apply functional_extensionality. intros y.
        destruct (String.eqb_spec y v); reflexivity. }
      rewrite Heq. done.
    + (* distinct binders commute *)
      destruct Hfresh as [Heqev | Hfresh]; [exfalso; exact (Hne Heqev) |].
      assert ((fun y => if (y =? ev)%string then v''
                         else (fun z => if (z =? v)%string then v' else mp z) y)
              = (fun y => if (y =? v)%string then v'
                          else (fun z => if (z =? ev)%string then v'' else mp z) y)) as Hswap.
      { apply functional_extensionality. intros y.
        destruct (String.eqb_spec y ev) as [-> | Hyev].
        - rewrite (proj2 (String.eqb_neq ev v) Hne). reflexivity.
        - reflexivity. }
      rewrite Hswap. exact (IHe (fun y => if (y =? ev)%string then v'' else mp y) Hfresh).
  - (* LIte *) destruct Hfresh as [Hfc [Hft Hfe]].
    rewrite (trnsl_assertion_ite icond ithen ielse stk (fun y => if (y =? v)%string then v' else mp y))
            (trnsl_assertion_ite icond ithen ielse stk mp).
    unfold LExpr_holds. rewrite (interp_lexpr_stable icond mp v v' Hfc).
    apply bi.and_proper; apply bi.wand_proper; try done.
    + exact (IHi1 mp Hft).
    + exact (IHi2 mp Hfe).
  - (* LInv *) simpl.
    rewrite (trnsl_assertion_unfold (LInv ivn iargs))
            (trnsl_assertion_unfold (LInv ivn iargs)) /trnsl_assertion_pre /=.
    destruct (inv_map !! ivn); [ | done].
    apply bi.exist_proper; intros vs.
    apply bi.sep_proper; [ | done].
    apply bi.pure_proper.
    revert vs Hfresh. induction iargs as [ | le0 iargs' IHl]; intros vs Hfresh.
    + split; intros H; inversion H; subst; constructor.
    + apply Forall_cons_1 in Hfresh as [Hfresh0 Hfresh'].
      destruct vs as [ | v0 vs']; simpl.
      * split; intros H; inversion H.
      * split; intros H; inversion H as [|? ? ? ? Hh Ht]; subst.
        -- constructor.
           ++ rewrite (interp_lexpr_stable le0 mp v v' Hfresh0) in Hh. exact Hh.
           ++ apply (IHl vs' Hfresh'); exact Ht.
        -- constructor.
           ++ rewrite (interp_lexpr_stable le0 mp v v' Hfresh0). exact Hh.
           ++ apply (IHl vs' Hfresh'); exact Ht.
  - (* LPred *) exfalso. exact Hfresh.
  - (* LAnd *) destruct Hfresh as [Hf1 Hf2].
    rewrite (trnsl_assertion_and a1 a2 stk (fun y => if (y =? v)%string then v' else mp y))
            (trnsl_assertion_and a1 a2 stk mp).
    apply bi.sep_proper; [exact (IH1 mp Hf1) | exact (IH2 mp Hf2)].
Qed.

Lemma trnsl_pred_validity' pred args stk_id mp :
  match pred_map !! pred with
  | Some pred_rec =>
    let subst_map := list_to_map (zip pred_rec.(pred_args) args) in

    (trnsl_assertion (subst pred_rec.(pred_body) subst_map) stk_id mp)%I ≡ trnsl_assertion (LPred pred args) stk_id mp
  | None => true
  end
.
Proof.
  destruct (pred_map !! pred) eqn:HPred; try done.
  simpl.
  rewrite (trnsl_assertion_unfold (LPred pred args)) /trnsl_assertion_pre /=.
  rewrite HPred. done.
Qed.



End Translation.

Definition fresh_lvar (stk: stack) v := forall v', not (stk !! v' = Some v).

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
Definition entails (σ : lvar_typs) (P Q : assertion) :=
  forall stk_id mp, env_typ_well_defined σ mp ->
  ∃ P' Q', trnsl_assertion P stk_id mp = P' /\ trnsl_assertion Q stk_id mp = Q' /\ (P' ⊢  Q')%I.

Lemma entails_intro σ A B :
  (forall stk mp, env_typ_well_defined σ mp -> trnsl_assertion A stk mp ⊢ trnsl_assertion B stk mp) ->
  entails σ A B.
Proof.
  intros H stk mp Henv. exists (trnsl_assertion A stk mp), (trnsl_assertion B stk mp).
  split; [done | split; [done | apply H, Henv]].
Qed.

Lemma entails_refl σ A : entails σ A A.
Proof. apply entails_intro. intros stk mp Henv. done. Qed.

Lemma entails_trans σ A B C : entails σ A B -> entails σ B C -> entails σ A C.
Proof.
  intros H1 H2. apply entails_intro. intros stk mp Henv.
  destruct (H1 stk mp Henv) as [A' [B' [<- [<- H1']]]].
  destruct (H2 stk mp Henv) as [B'' [C' [Heq [<- H2']]]].
  rewrite Heq in H1'. rewrite H1'. exact H2'.
Qed.

(* Commutes a fixed-stack LAnd past a nested LExists into a single top-level
   LExists -- lets the new, subst-free ExistsElimRule (which only eliminates
   a top-level LExists) still reach an existential nested under
   LAnd (LStack stk) (LAnd _ p), the shape an invariant/predicate body
   naturally appears in via InvAccessBlockRule/etc. Needs v fresh for both
   stk and p, so overriding mp at v (LExists's own translation) leaves them
   untouched -- trnsl_assertion_mp_irrelevant does the rest. *)
Lemma entails_and_stack_exists_swap (σ : lvar_typs) (stk : stack) (v : lvar) (t : typ) (body p : assertion) :
  fresh_lvar stk v ->
  lvar_fresh_in_assertion v p ->
  entails σ (LAnd (LStack stk) (LAnd (LExists v t body) p))
          (LExists v t (LAnd (LStack stk) (LAnd body p))).
Proof.
  intros Hfresh_stk Hfresh_p stk_id mp Henv.
  eexists _, _. split; [reflexivity|]. split; [reflexivity|].
  rewrite trnsl_assertion_and trnsl_assertion_and trnsl_assertion_exists trnsl_assertion_exists.
  iIntros "[Hstk [[%v' [%Htyp Hbody]] Hp]]".
  iExists v'. iSplitR; [done|].
  rewrite trnsl_assertion_and trnsl_assertion_and.
  rewrite (trnsl_assertion_mp_irrelevant v (LStack stk) v' stk_id mp Hfresh_stk).
  rewrite (trnsl_assertion_mp_irrelevant v p v' stk_id mp Hfresh_p).
  iFrame.
Qed.

(* Simpler 2-way version of the above, without a fixed LStack conjunct in
   front -- lets a fresh-lvar rule's own LExists postcondition (e.g.
   VarAssignmentRule's) absorb a sibling frame fact directly. *)
Lemma entails_exists_and_swap (σ : lvar_typs) (v : lvar) (t : typ) (body p : assertion) :
  lvar_fresh_in_assertion v p ->
  entails σ (LAnd (LExists v t body) p) (LExists v t (LAnd body p)).
Proof.
  intros Hfresh_p stk_id mp Henv.
  eexists _, _. split; [reflexivity|]. split; [reflexivity|].
  rewrite trnsl_assertion_and trnsl_assertion_exists trnsl_assertion_exists.
  iIntros "[[%v' [%Htyp Hbody]] Hp]".
  iExists v'. iSplitR; [done|].
  rewrite trnsl_assertion_and.
  rewrite (trnsl_assertion_mp_irrelevant v p v' stk_id mp Hfresh_p).
  iFrame.
Qed.

(* Introduces a fresh existential over an already-known value: v' := mp v,
   justified by env_typ_well_defined + sigma v = t (Henv gives exactly the
   typ_val_match side condition LExists's own translation needs). The
   entails-unconditional-over-mp form of this is NOT provable (nothing
   constrains mp v to be well-typed without Henv) -- this is exactly why
   entails is parameterized by sigma/Henv in the first place. *)
Lemma entails_exists_intro (σ : lvar_typs) (v : lvar) (t : typ) (X : assertion) :
  σ v = t ->
  entails σ X (LExists v t X).
Proof.
  intros Hty stk_id mp Henv.
  eexists _, _. split; [reflexivity|]. split; [reflexivity|].
  rewrite trnsl_assertion_exists.
  assert ((fun y => if (y =? v)%string then mp v else mp y) = mp) as Hself.
  { apply functional_extensionality. intros y.
    destruct (String.eqb_spec y v) as [->|]; reflexivity. }
  iIntros "H".
  iExists (mp v). iSplitR.
  - iPureIntro. specialize (Henv v). rewrite Hty in Henv.
    destruct (σ v), (mp v); simpl in *; try done.
  - rewrite Hself. iExact "H".
Qed.

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

(* Substituting a concrete value w for lv throughout a qf_assertion, then
   translating at mp, is the same as translating unsubstituted at mp
   updated at lv -- the assertion-level generalization of
   interp_lexpr_subst_var, restricted to the fragment where it holds by
   plain structural induction (no least_fixpoint machinery needed, since
   LPred/LInv -- the only cases that would require it -- are excluded).
   Mirrors trnsl_assertion_mp_irrelevant's proof shape exactly, swapping
   "override mp at a fresh lvar" for "substitute a value for lv". *)
Lemma trnsl_assertion_subst_lv (a : assertion) (lv : lvar) (w : val) (stk : stack_id) (mp : symb_map) :
  qf_assertion a ->
  trnsl_assertion (subst a (<[lv := LVal w]> ∅)) stk mp ≡
  trnsl_assertion a stk (fun y => if (y =? lv)%string then w else mp y).
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
    | a1 IH1 a2 IH2 ]; intros Hqf; simpl in Hqf.
  - (* LProc *) exfalso. exact Hqf.
  - (* LStack *) exfalso. exact Hqf.
  - (* LExprA *) simpl.
    rewrite (trnsl_assertion_unfold (LExprA (lexpr_subst pexp (<[lv := LVal w]> ∅))))
            (trnsl_assertion_unfold (LExprA pexp)) /trnsl_assertion_pre /=.
    unfold LExpr_holds. rewrite (interp_lexpr_subst_var pexp lv w mp). done.
  - (* LPure *) simpl.
    rewrite (trnsl_assertion_unfold (LPure pp)) (trnsl_assertion_unfold (LPure pp))
            /trnsl_assertion_pre /=. done.
  - (* LOwn *) simpl.
    rewrite (trnsl_assertion_unfold
              (LOwn (lexpr_subst oe (<[lv := LVal w]> ∅)) ofld (lexpr_subst ochunk (<[lv := LVal w]> ∅))))
            (trnsl_assertion_unfold (LOwn oe ofld ochunk)) /trnsl_assertion_pre /=.
    apply bi.exist_proper; intros l. apply bi.exist_proper; intros chunk0.
    unfold LExpr_holds. simpl.
    rewrite (interp_lexpr_subst_var oe lv w mp) (interp_lexpr_subst_var ochunk lv w mp).
    done.
  - (* LGhostOwn *) simpl.
    rewrite (trnsl_assertion_unfold
              (LGhostOwn (lexpr_subst ge (<[lv := LVal w]> ∅)) gfld gr (lexpr_subst gchunk (<[lv := LVal w]> ∅))))
            (trnsl_assertion_unfold (LGhostOwn ge gfld gr gchunk)) /trnsl_assertion_pre /=.
    destruct (Γ gr) as [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ].
    + apply bi.exist_proper; intros l. apply bi.exist_proper; intros chunk0.
      unfold LExpr_holds. simpl.
      rewrite (interp_lexpr_subst_var ge lv w mp) (interp_lexpr_subst_var gchunk lv w mp).
      done.
    + done.
  - (* LForall *) exfalso. exact Hqf.
  - (* LExists *) exfalso. exact Hqf.
  - (* LIte *) exfalso. exact Hqf.
  - (* LInv *) simpl.
    rewrite (trnsl_assertion_unfold (LInv ivn (map (fun e => lexpr_subst e (<[lv := LVal w]> ∅)) iargs)))
            (trnsl_assertion_unfold (LInv ivn iargs)) /trnsl_assertion_pre /=.
    destruct (inv_map !! ivn); [ | done].
    apply bi.exist_proper; intros vs.
    apply bi.sep_proper; [ | done].
    apply bi.pure_proper.
    revert vs. induction iargs as [ | le0 iargs' IHl]; intros vs; simpl.
    + split; intros H; inversion H; subst; constructor.
    + destruct vs as [ | v0 vs']; simpl.
      * split; intros H; inversion H.
      * split; intros H; inversion H as [|? ? ? ? Hh Ht]; subst.
        -- constructor.
           ++ rewrite (interp_lexpr_subst_var le0 lv w mp) in Hh. exact Hh.
           ++ apply IHl; exact Ht.
        -- constructor.
           ++ rewrite (interp_lexpr_subst_var le0 lv w mp). exact Hh.
           ++ apply IHl; exact Ht.
  - (* LPred *) exfalso. exact Hqf.
  - (* LAnd *) destruct Hqf as [Hq1 Hq2]. simpl.
    rewrite (trnsl_assertion_and (subst a1 (<[lv := LVal w]> ∅)) (subst a2 (<[lv := LVal w]> ∅)) stk mp)
            (trnsl_assertion_and a1 a2 stk (fun y => if (y =? lv)%string then w else mp y)).
    apply bi.sep_proper; [exact (IH1 Hq1) | exact (IH2 Hq2)].
Qed.

(* LVar-substitution counterpart of trnsl_assertion_subst_lv (mirrors it
   case-for-case, swapping interp_lexpr_subst_var for
   interp_lexpr_subst_lvar) -- the assertion-level fact backing "swap one
   already-bound lvar for another, given they're co-asserted equal"
   (AE_LExpr_Subst_Eq_Congr). *)
Lemma trnsl_assertion_subst_lvar (a : assertion) (lv lv2 : lvar) (stk : stack_id) (mp : symb_map) :
  qf_assertion a ->
  trnsl_assertion (subst a (<[lv := LVar lv2]> ∅)) stk mp ≡
  trnsl_assertion a stk (fun y => if (y =? lv)%string then mp lv2 else mp y).
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
    | a1 IH1 a2 IH2 ]; intros Hqf; simpl in Hqf.
  - (* LProc *) exfalso. exact Hqf.
  - (* LStack *) exfalso. exact Hqf.
  - (* LExprA *) simpl.
    rewrite (trnsl_assertion_unfold (LExprA (lexpr_subst pexp (<[lv := LVar lv2]> ∅))))
            (trnsl_assertion_unfold (LExprA pexp)) /trnsl_assertion_pre /=.
    unfold LExpr_holds. rewrite (interp_lexpr_subst_lvar pexp lv lv2 mp). done.
  - (* LPure *) simpl.
    rewrite (trnsl_assertion_unfold (LPure pp)) (trnsl_assertion_unfold (LPure pp))
            /trnsl_assertion_pre /=. done.
  - (* LOwn *) simpl.
    rewrite (trnsl_assertion_unfold
              (LOwn (lexpr_subst oe (<[lv := LVar lv2]> ∅)) ofld (lexpr_subst ochunk (<[lv := LVar lv2]> ∅))))
            (trnsl_assertion_unfold (LOwn oe ofld ochunk)) /trnsl_assertion_pre /=.
    apply bi.exist_proper; intros l. apply bi.exist_proper; intros chunk0.
    unfold LExpr_holds. simpl.
    rewrite (interp_lexpr_subst_lvar oe lv lv2 mp) (interp_lexpr_subst_lvar ochunk lv lv2 mp).
    done.
  - (* LGhostOwn *) simpl.
    rewrite (trnsl_assertion_unfold
              (LGhostOwn (lexpr_subst ge (<[lv := LVar lv2]> ∅)) gfld gr (lexpr_subst gchunk (<[lv := LVar lv2]> ∅))))
            (trnsl_assertion_unfold (LGhostOwn ge gfld gr gchunk)) /trnsl_assertion_pre /=.
    destruct (Γ gr) as [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ].
    + apply bi.exist_proper; intros l. apply bi.exist_proper; intros chunk0.
      unfold LExpr_holds. simpl.
      rewrite (interp_lexpr_subst_lvar ge lv lv2 mp) (interp_lexpr_subst_lvar gchunk lv lv2 mp).
      done.
    + done.
  - (* LForall *) exfalso. exact Hqf.
  - (* LExists *) exfalso. exact Hqf.
  - (* LIte *) exfalso. exact Hqf.
  - (* LInv *) simpl.
    rewrite (trnsl_assertion_unfold (LInv ivn (map (fun e => lexpr_subst e (<[lv := LVar lv2]> ∅)) iargs)))
            (trnsl_assertion_unfold (LInv ivn iargs)) /trnsl_assertion_pre /=.
    destruct (inv_map !! ivn); [ | done].
    apply bi.exist_proper; intros vs.
    apply bi.sep_proper; [ | done].
    apply bi.pure_proper.
    revert vs. induction iargs as [ | le0 iargs' IHl]; intros vs; simpl.
    + split; intros H; inversion H; subst; constructor.
    + destruct vs as [ | v0 vs']; simpl.
      * split; intros H; inversion H.
      * split; intros H; inversion H as [|? ? ? ? Hh Ht]; subst.
        -- constructor.
           ++ rewrite (interp_lexpr_subst_lvar le0 lv lv2 mp) in Hh. exact Hh.
           ++ apply IHl; exact Ht.
        -- constructor.
           ++ rewrite (interp_lexpr_subst_lvar le0 lv lv2 mp). exact Hh.
           ++ apply IHl; exact Ht.
  - (* LPred *) exfalso. exact Hqf.
  - (* LAnd *) destruct Hqf as [Hq1 Hq2]. simpl.
    rewrite (trnsl_assertion_and (subst a1 (<[lv := LVar lv2]> ∅)) (subst a2 (<[lv := LVar lv2]> ∅)) stk mp)
            (trnsl_assertion_and a1 a2 stk (fun y => if (y =? lv)%string then mp lv2 else mp y)).
    apply bi.sep_proper; [exact (IH1 Hq1) | exact (IH2 Hq2)].
Qed.

End TypeInf.


Section RavenLogic.

  (* Purely syntactic entailment on assertions -- deliberately independent
     of trnsl_assertion/Iris (no Sigma/Gamma/GhostConfig/invTokenG needed
     anywhere in this relation's own definition), so that WeakeningRule
     (the sole reason RavenHoareTriple used to need those) can be stated
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
  | AE_GhostOwn_Chunk_Eq e fld r chunk1 chunk2 :
      (* Unconditional (no co-asserted equality needed, unlike
         AE_LExpr_Subst_Eq_Congr): chunk1/chunk2 interp-agree at *every*
         mp, e.g. two different closed LExprs computing the same ground
         RA element -- LGhostOwn's own translation only ever consults its
         chunk argument through interp_lexpr, so this is a direct
         congruence. *)
      (forall mp, interp_lexpr chunk1 mp = interp_lexpr chunk2 mp) ->
      assertion_entails σ (LGhostOwn e fld r chunk1) (LGhostOwn e fld r chunk2).

  Lemma assertion_entails_sound σ A B : assertion_entails σ A B -> entails σ A B.
  Proof.
    induction 1.
    - (* AE_Refl *) apply entails_refl.
    - (* AE_Trans *) eapply entails_trans; eassumption.
    - (* AE_And_Mono *)
      apply entails_intro. intros stk mp Henv.
      destruct (IHassertion_entails1 stk mp Henv) as [Pp [Pp' [<- [<- H1']]]].
      destruct (IHassertion_entails2 stk mp Henv) as [Qp [Qp' [<- [<- H2']]]].
      rewrite !trnsl_assertion_and. iIntros "[HP HQ]". iSplitL "HP".
      + iApply (H1' with "HP").
      + iApply (H2' with "HQ").
    - (* AE_And_Comm *)
      apply entails_intro. intros stk mp Henv. rewrite !trnsl_assertion_and. iIntros "[$ $]".
    - (* AE_And_Assoc_R *)
      apply entails_intro. intros stk mp Henv. rewrite !trnsl_assertion_and. iIntros "[[$ $] $]".
    - (* AE_And_Assoc_L *)
      apply entails_intro. intros stk mp Henv. rewrite !trnsl_assertion_and. iIntros "[$ [$ $]]".
    - (* AE_And_Elim_L *)
      apply entails_intro. intros stk mp Henv. rewrite trnsl_assertion_and. iIntros "[$ _]".
    - (* AE_And_Elim_R *)
      apply entails_intro. intros stk mp Henv. rewrite trnsl_assertion_and. iIntros "[_ $]".
    - (* AE_And_True_Intro *)
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and (trnsl_assertion_unfold (LPure True)) /trnsl_assertion_pre /=.
      iIntros "H". iFrame.
    - (* AE_And_True_Elim *)
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and (trnsl_assertion_unfold (LPure True)) /trnsl_assertion_pre /=.
      iIntros "[$ _]".
    - (* AE_True_Intro *)
      apply entails_intro. intros stk mp Henv.
      rewrite (trnsl_assertion_unfold (LPure True)) /trnsl_assertion_pre /=.
      iIntros "_". done.
    - (* AE_Pure *)
      apply entails_intro. intros stk mp Henv.
      rewrite (trnsl_assertion_unfold (LPure p)) (trnsl_assertion_unfold (LPure q))
        /trnsl_assertion_pre /=.
      iIntros "%Hp". iPureIntro. auto.
    - (* AE_Exists_Mono *)
      rename H into Hty.
      apply entails_intro. intros stk mp Henv.
      rewrite !trnsl_assertion_exists.
      iIntros "[%v' [%Htyp HA]]". iExists v'. iSplitR; [done|].
      have Henv' : env_typ_well_defined σ (fun y => if (y =? lv)%string then v' else mp y).
      { apply env_typ_well_defined_update; [exact Henv | rewrite Hty; exact Htyp]. }
      destruct (IHassertion_entails stk (fun y => if (y =? lv)%string then v' else mp y) Henv')
        as [Ap [Bp [<- [<- Hent]]]].
      iApply (Hent with "HA").
    - (* AE_Exists_Intro *) exact (entails_exists_intro σ lv t X H).
    - (* AE_Exists_ValIntro *)
      rename H into Hty, H0 into Htv, H1 into Hqf.
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_exists.
      rewrite (trnsl_assertion_subst_lv A lv w stk mp Hqf).
      iIntros "H". iExists w. iSplitR; [done|]. iExact "H".
    - (* AE_Exists_Elim *)
      rename H into Hty, H0 into Hfresh.
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_exists.
      iIntros "[%v' [%Htyp HP]]".
      have Henv' : env_typ_well_defined σ (fun y => if (y =? lv)%string then v' else mp y).
      { apply env_typ_well_defined_update; [exact Henv | rewrite Hty; exact Htyp]. }
      destruct (IHassertion_entails stk (fun y => if (y =? lv)%string then v' else mp y) Henv')
        as [Pp [Qp [<- [<- Hent]]]].
      iDestruct (Hent with "HP") as "HQ".
      iEval (rewrite (trnsl_assertion_mp_irrelevant lv Q v' stk mp Hfresh)) in "HQ".
      iExact "HQ".
    - (* AE_Exists_And_Swap_R *) exact (entails_exists_and_swap σ lv t body p H).
    - (* AE_And_Exists_Swap_L *)
      rename H into Hfresh.
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and trnsl_assertion_exists trnsl_assertion_exists.
      iIntros "[Hc [%v' [%Htyp Hbody]]]".
      iExists v'. iSplitR; [done|].
      rewrite trnsl_assertion_and.
      rewrite (trnsl_assertion_mp_irrelevant lv c v' stk mp Hfresh).
      iFrame.
    - (* AE_Ite_True *)
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and (trnsl_assertion_ite cond A B stk mp)
        (trnsl_assertion_unfold (LExprA cond)) /trnsl_assertion_pre /=.
      iIntros "[Hite %Hc]".
      iDestruct "Hite" as "[Hthen _]". iApply "Hthen". iPureIntro. exact Hc.
    - (* AE_Ite_False *)
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and (trnsl_assertion_ite cond A B stk mp)
        (trnsl_assertion_unfold (LExprA (LUnOp NotBoolOp cond))) /trnsl_assertion_pre /=.
      iIntros "[Hite %Hnc]".
      have Hcond_false : interp_lexpr cond mp = Some (LitBool false).
      { unfold LExpr_holds in Hnc. simpl in Hnc.
        destruct (interp_lexpr cond mp) as [[bv|zv| |lv0|[rv xv]]|] eqn:Hcond;
          simpl in Hnc; try (exfalso; exact Hnc).
        destruct bv; [discriminate Hnc | reflexivity]. }
      iDestruct "Hite" as "[_ Helse]". iApply "Helse". iPureIntro.
      unfold LExpr_holds. rewrite Hcond_false. intros [=].
    - (* AE_Ite_Bool_True *)
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and.
      rewrite (trnsl_assertion_ite cond (LAnd A (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
        (LAnd B (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false))))) stk mp).
      rewrite (trnsl_assertion_unfold (LExprA (LVar lv))) /trnsl_assertion_pre /=.
      iIntros "[Hite %Hlv]".
      unfold LExpr_holds in Hlv. simpl in Hlv.
      destruct (interp_lexpr cond mp) as [vc|] eqn:Hcond.
      + destruct (val_beq vc (LitBool true)) eqn:Hvc.
        * unfold val_beq in Hvc. apply bool_decide_eq_true_1 in Hvc. subst vc.
          iDestruct "Hite" as "[Hthen _]".
          iDestruct ("Hthen" with "[]") as "HA".
          { iPureIntro. unfold LExpr_holds. rewrite Hcond. done. }
          iEval (rewrite trnsl_assertion_and) in "HA". iDestruct "HA" as "[HA _]".
          rewrite trnsl_assertion_and (trnsl_assertion_unfold (LExprA cond)) /trnsl_assertion_pre /=.
          iFrame "HA". iPureIntro. unfold LExpr_holds. rewrite Hcond. done.
        * iDestruct "Hite" as "[_ Helse]".
          iDestruct ("Helse" with "[]") as "HB".
          { iPureIntro. unfold LExpr_holds. rewrite Hcond. intros ->.
            unfold val_beq in Hvc. apply bool_decide_eq_false_1 in Hvc. apply Hvc. reflexivity. }
          iEval (rewrite trnsl_assertion_and
            (trnsl_assertion_unfold (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false)))))
            /trnsl_assertion_pre /=) in "HB".
          iDestruct "HB" as "[_ %Hf]".
          unfold LExpr_holds in Hf. cbn [interp_lexpr] in Hf.
          assert (Hcomp : val_beq (LitBool true) (LitBool false) = false).
          { destruct (val_beq (LitBool true) (LitBool false)) eqn:Heq0; [|reflexivity].
            exfalso. apply internal_val_dec_bl in Heq0. discriminate. }
          congruence.
      + iDestruct "Hite" as "[_ Helse]".
        iDestruct ("Helse" with "[]") as "HB".
        { iPureIntro. unfold LExpr_holds. rewrite Hcond. intros []. }
        iEval (rewrite trnsl_assertion_and
          (trnsl_assertion_unfold (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false)))))
          /trnsl_assertion_pre /=) in "HB".
        iDestruct "HB" as "[_ %Hf]".
        unfold LExpr_holds in Hf. cbn [interp_lexpr] in Hf.
        assert (Hcomp : val_beq (LitBool true) (LitBool false) = false).
        { destruct (val_beq (LitBool true) (LitBool false)) eqn:Heq0; [|reflexivity].
          exfalso. apply internal_val_dec_bl in Heq0. discriminate. }
        congruence.
    - (* AE_Ite_Bool_False *)
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and.
      rewrite (trnsl_assertion_ite cond (LAnd A (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
        (LAnd B (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false))))) stk mp).
      rewrite (trnsl_assertion_unfold (LExprA (LUnOp NotBoolOp (LVar lv)))) /trnsl_assertion_pre /=.
      iIntros "[Hite %Hlv]".
      unfold LExpr_holds in Hlv. simpl in Hlv.
      destruct (mp lv) as [b| |i|l|ra] eqn:Hmplv; simpl in Hlv; try contradiction.
      injection Hlv as Hlv. apply negb_true_iff in Hlv. subst b.
      destruct (interp_lexpr cond mp) as [vc|] eqn:Hcond.
      + destruct (val_beq vc (LitBool true)) eqn:Hvc.
        * unfold val_beq in Hvc. apply bool_decide_eq_true_1 in Hvc. subst vc.
          iDestruct "Hite" as "[Hthen _]".
          iDestruct ("Hthen" with "[]") as "HA".
          { iPureIntro. unfold LExpr_holds. rewrite Hcond. done. }
          iEval (rewrite trnsl_assertion_and
            (trnsl_assertion_unfold (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
            /trnsl_assertion_pre /=) in "HA".
          iDestruct "HA" as "[_ %Ht]".
          unfold LExpr_holds in Ht. cbn [interp_lexpr] in Ht.
          assert (Hcomp : val_beq (LitBool false) (LitBool true) = false).
          { destruct (val_beq (LitBool false) (LitBool true)) eqn:Heq0; [|reflexivity].
            exfalso. apply internal_val_dec_bl in Heq0. discriminate. }
          congruence.
        * iDestruct "Hite" as "[_ Helse]".
          iDestruct ("Helse" with "[]") as "HB".
          { iPureIntro. unfold LExpr_holds. rewrite Hcond. intros ->.
            unfold val_beq in Hvc. apply bool_decide_eq_false_1 in Hvc. apply Hvc. reflexivity. }
          iEval (rewrite trnsl_assertion_and) in "HB". iDestruct "HB" as "[$ _]".
      + iDestruct "Hite" as "[_ Helse]".
        iDestruct ("Helse" with "[]") as "HB".
        { iPureIntro. unfold LExpr_holds. rewrite Hcond. intros []. }
        iEval (rewrite trnsl_assertion_and) in "HB". iDestruct "HB" as "[$ _]".
    - (* AE_LExpr_Subst_Eq_Congr *)
      rename H into Hqf.
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_and (trnsl_assertion_unfold (LExprA (LBinOp EqOp (LVar lv) (LVar lv2))))
        /trnsl_assertion_pre /=.
      iIntros "[%Heq H]".
      unfold LExpr_holds in Heq. simpl in Heq. injection Heq as Heq.
      apply bool_decide_eq_true in Heq.
      rewrite (trnsl_assertion_subst_lvar A lv lv2 stk mp Hqf).
      have Hself : (fun y => if (y =? lv)%string then mp lv2 else mp y) = mp.
      { apply functional_extensionality. intros y.
        destruct (String.eqb_spec y lv) as [-> | _]; [exact (eq_sym Heq) | reflexivity]. }
      rewrite Hself. iExact "H".
    - (* AE_Exists_Rename_Intro *)
      rename H into Hty, H0 into Hty2, H1 into Hqf.
      apply entails_intro. intros stk mp Henv.
      rewrite trnsl_assertion_exists.
      rewrite (trnsl_assertion_subst_lvar A lv lv2 stk mp Hqf).
      iIntros "H". iExists (mp lv2). iSplitR.
      + iPureIntro. specialize (Henv lv2). rewrite Hty2 in Henv.
        destruct (σ lv2), (mp lv2); simpl in *; try done.
      + iExact "H".
    - (* AE_LExprA_Impl *)
      rename H into Himpl.
      apply entails_intro. intros stk mp Henv.
      rewrite (trnsl_assertion_unfold (LExprA e1)) (trnsl_assertion_unfold (LExprA e2)) /trnsl_assertion_pre /=.
      iIntros "%He1". iPureIntro. exact (Himpl mp He1).
    - (* AE_GhostOwn_Chunk_Eq *)
      rename H into Heq.
      apply entails_intro. intros stk mp Henv.
      rewrite (trnsl_assertion_unfold (LGhostOwn e fld0 r chunk1)) (trnsl_assertion_unfold (LGhostOwn e fld0 r chunk2))
        /trnsl_assertion_pre /=.
      destruct (Γ r) as [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ].
      + unfold LExpr_holds. rewrite (Heq mp). done.
      + done.
  Qed.

  (* assertion_entails-typed counterpart of TypeInf's entails_and_stack_exists_swap
     (now otherwise unused -- WeakeningRule no longer takes entails), derived
     purely compositionally from the two swap primitives above: pull the
     LExists past p (AE_Exists_And_Swap_R) under the fixed LStack via
     AE_And_Mono, then past the LStack itself (AE_And_Exists_Swap_L). *)
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
       ProgramWF's pwf_*_binders_reserved and local/binders.md). Checkable
       by whoever builds a concrete derivation (just don't pick
       "$"-prefixed names) -- unlike a blanket "no stack/lexpr anywhere
       ever uses a reserved name" assumption, which is simply false
       (nothing stops an adversarial stk from doing so) and was tried,
       and abandoned, earlier. *)
    ¬ is_reserved lvar_x ->
    Forall (fun le => ∀ v, v ∈ lexpr_fvars le → ¬ is_reserved v) lexprs ->
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

  (* Consolidates the old CASSuccRule/CASFailRule (see git history) into one:
     the precondition no longer forces the owned chunk to already equal e2
     (which required knowing, before the atomic step, which outcome would
     occur -- unknowable in general when old_chunk is an invariant's own
     existential witness, e.g. counterInv's "v", genuinely independent of
     whatever value a prior read compared against). old_chunk is a fully
     generic LExpr; the postcondition's own LIte branches on the *same*
     equality the CAS itself decides operationally (old_chunk = lexpr2),
     covering both outcomes in a single rule so the caller decides which
     branch applies only *after* seeing lvar_v's own value. e2/e3 need not
     translate to literal constants (see HeapWriteRule/FPURule's identical
     generalization): lexpr2/lexpr3 become the compared value / new chunk
     directly, since chunk is itself an LExpr. lvar_v ∉ old_chunk's fvars
     justifies that its evaluated value is stable under the postcondition's
     stack update (needed for the failure branch, which reuses old_chunk
     unchanged; the success branch introduces a fresh chunk expression, so
     doesn't need this). Unlike the old CASSuccRule, e2's evaluatedness is no
     longer free from the precondition (which used to force old_chunk =
     lexpr2 literally), so it now needs its own expr_well_defined premise,
     just like e3's. *)
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
     Deliberately subst-free (contrast the old, retired rule of this name):
     body keeps v as an ordinary free lvar in both premise and conclusion,
     so the soundness proof re-interprets the *same* derivation at mp[v:=v']
     rather than needing an AST-level substitution -- which is what lets this
     one rule handle LStack-containing bodies too (subst is a no-op on
     LStack's own stored map, see lvar_fresh_in_assertion's comment), unlike
     its predecessor which had to shut those out via elim_safe. Re-entering
     the premise's own soundness obligation at mp[v:=v'] needs v' to have
     v's declared type t; since LExists's own translation now restricts its
     witness to typ_val_match t (see trnsl_assertion_str's LExists case),
     that comes for free from destructuring the incoming existential -- no
     separate witness_well_typed side-condition needed any more (contrast
     this rule's own previous version). Callers needing the old
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
  .

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


Section AssertionsProperties.

  (* Effective value of a logical variable under substitution map M and symbolic map mp:
     either interprets the substituted expression, or returns the raw symbolic value. *)
  Definition eval_lvar (M : gmap lvar LExpr) (mp : symb_map) (x : lvar) : option val :=
    match M !! x with
    | Some e => interp_lexpr e mp
    | None => Some (mp x)
    end.

  (* Helper: push interp_lexpr inside a lookup-driven match. Needed because the kernel
     won't reduce `interp_lexpr (match M!!x with …) mp` propositionally without a case split. *)
  Lemma interp_lexpr_lookup_match (M : gmap lvar LExpr) (x : lvar) (mp : symb_map) :
    interp_lexpr (match M !! x with Some e => e | None => LVar x end) mp =
    match M !! x with Some e => interp_lexpr e mp | None => Some (mp x) end.
  Proof. destruct (M !! x); reflexivity. Qed.

  (* If two (M, mp) pairs agree on eval_lvar, lexpr_subst produces the same interp_lexpr result. *)
  Lemma interp_lexpr_lexpr_subst_eval_lvar_congr (e : LExpr) (M1 M2 : gmap lvar LExpr)
      (mp1 mp2 : symb_map) :
    (∀ x, eval_lvar M1 mp1 x = eval_lvar M2 mp2 x) →
    interp_lexpr (lexpr_subst e M1) mp1 = interp_lexpr (lexpr_subst e M2) mp2.
  Proof.
    intro Hbase. induction e; simpl.
    - (* LVar x: rewrite the interp_lexpr-over-match to the distributed form, then use Hbase. *)
      rewrite !interp_lexpr_lookup_match.
      exact (Hbase x).
    - (* LVal *) reflexivity.
    - (* LUnOp *) rewrite IHe. reflexivity.
    - (* LBinOp *) rewrite IHe1; rewrite IHe2. reflexivity.
    - (* LIfE *)
      rewrite IHe1.
      destruct (interp_lexpr (lexpr_subst e1 M2) mp2) as [[b| | | |]|]; try reflexivity.
      destruct b; [exact IHe2 | exact IHe3].
    - (* LStuck *) reflexivity.
  Qed.

  (* Updating q at v leaves eval_lvar M q x unchanged when x ∈ dom M or x ≠ v *)
  Lemma eval_lvar_update_stable (M : gmap lvar LExpr) (q : symb_map) (v : lvar) (v' : val) (x : lvar) :
    v ∉ lexpr_map_fvars M →
    (x ∈ dom M ∨ x ≠ v) →
    eval_lvar M (fun y => if (y =? v)%string then v' else q y) x = eval_lvar M q x.
  Proof.
    intros Hfresh Hcases.
    unfold eval_lvar.
    destruct (M !! x) as [le|] eqn:HMx.
    - (* x ∈ dom M: use interp_lexpr_stable *)
      apply interp_lexpr_stable.
      exact (proj1 (lexpr_map_fvars_spec M v) Hfresh x le HMx).
    - (* x ∉ dom M: x ≠ v by hypothesis *)
      destruct Hcases as [Hdom | Hne].
      + (* x ∈ dom M contradicts M !! x = None *)
        exfalso. rewrite <- not_elem_of_dom in HMx. exact (HMx Hdom).
      + destruct (String.eqb_spec x v) as [Heq | _].
        * exfalso. exact (Hne Heq).
        * reflexivity.
  Qed.

  (* Restricted version: lexpr_fvars e ⊆ dom M1 → Hbase restricted to dom M1 suffices *)
  (* Generalized via is_reserved directly, rather than a fixed gset R:
     reserved names potentially escaping dom M1's coverage (through
     assertion_lexpr_fvars's over-approximation, see local/binders.md)
     aren't confined to a single top-level assertion's own binders --
     subst_congr_step below recurses into predicate bodies fetched fresh
     from pred_map (for recursive predicates), which are not syntactic
     subterms of whatever top-level assertion this all started from, so
     a fixed, pre-computed "safe" gset could never be threaded through
     that unfolding. is_reserved, being a uniform predicate rather than
     one assertion's own finite binder set, covers this uniformly.
     Instantiating with "fun _ _ => False" (never reserved) recovers the
     original, unconditional statement. *)
  Lemma interp_lexpr_lexpr_subst_eval_lvar_congr_dom (e : LExpr) (M1 M2 : gmap lvar LExpr)
      (mp1 mp2 : symb_map) :
    (∀ v, v ∈ lexpr_fvars e → v ∈ dom M1 ∨ is_reserved v) →
    (∀ x, x ∈ dom M1 ∨ is_reserved x → eval_lvar M1 mp1 x = eval_lvar M2 mp2 x) →
    interp_lexpr (lexpr_subst e M1) mp1 = interp_lexpr (lexpr_subst e M2) mp2.
  Proof using G.
    intros Hdom Hbase. induction e; simpl.
    - rewrite !interp_lexpr_lookup_match.
      apply Hbase. apply Hdom. set_solver.
    - reflexivity.
    - simpl in Hdom. rewrite (IHe Hdom). reflexivity.
    - simpl in Hdom.
      have Hd1 : ∀ v, v ∈ lexpr_fvars e1 → v ∈ dom M1 ∨ is_reserved v.
      { intros v Hv. apply Hdom. set_solver. }
      have Hd2 : ∀ v, v ∈ lexpr_fvars e2 → v ∈ dom M1 ∨ is_reserved v.
      { intros v Hv. apply Hdom. set_solver. }
      rewrite (IHe1 Hd1). rewrite (IHe2 Hd2). reflexivity.
    - simpl in Hdom.
      have Hd1 : ∀ v, v ∈ lexpr_fvars e1 → v ∈ dom M1 ∨ is_reserved v.
      { intros v Hv. apply Hdom. set_solver. }
      have Hd2 : ∀ v, v ∈ lexpr_fvars e2 → v ∈ dom M1 ∨ is_reserved v.
      { intros v Hv. apply Hdom. set_solver. }
      have Hd3 : ∀ v, v ∈ lexpr_fvars e3 → v ∈ dom M1 ∨ is_reserved v.
      { intros v Hv. apply Hdom. set_solver. }
      rewrite (IHe1 Hd1).
      destruct (interp_lexpr (lexpr_subst e1 M2) mp2) as [[b| | | |]|]; try reflexivity.
      destruct b.
      + rewrite (IHe2 Hd2). reflexivity.
      + rewrite (IHe3 Hd3). reflexivity.
    - reflexivity.
  Qed.

  (* Restricts an "every fvar is in Z or reserved" bound from a superset Y
     of fvars down to a subset X -- the workhorse for every subterm case
     below, where X is some subterm's own fvars and Y is the whole node's. *)
  Lemma fvars_bound_mono (X Y Z : gset lvar) :
    X ⊆ Y → (∀ v, v ∈ Y → v ∈ Z ∨ is_reserved v) → (∀ v, v ∈ X → v ∈ Z ∨ is_reserved v).
  Proof. intros HXY HY v Hv. exact (HY v (HXY v Hv)). Qed.

  (* Single-map specialization of interp_lexpr_lexpr_subst_eval_lvar_congr_dom:
     agreement only needs to cover e's own fvars directly (no dom/reserved
     framing at all) -- the version used by trnsl_assertion_mp_irrelevant_reserved,
     where the whole point is to avoid needing agreement at reserved names. *)
  Lemma interp_lexpr_subst_eval_lvar_congr_true (e : LExpr) (M : gmap lvar LExpr)
      (mp1 mp2 : symb_map) :
    (∀ x, x ∈ lexpr_fvars e → eval_lvar M mp1 x = eval_lvar M mp2 x) →
    interp_lexpr (lexpr_subst e M) mp1 = interp_lexpr (lexpr_subst e M) mp2.
  Proof using G.
    induction e; simpl; intro Hbase.
    - rewrite !interp_lexpr_lookup_match. apply Hbase. set_solver.
    - reflexivity.
    - rewrite (IHe ltac:(intros v Hv; apply Hbase; set_solver)). reflexivity.
    - rewrite (IHe1 ltac:(intros v Hv; apply Hbase; set_solver)).
      rewrite (IHe2 ltac:(intros v Hv; apply Hbase; set_solver)). reflexivity.
    - rewrite (IHe1 ltac:(intros v Hv; apply Hbase; set_solver)).
      destruct (interp_lexpr (lexpr_subst e1 M) mp2) as [[b| | | |]|]; try reflexivity.
      destruct b.
      + exact (IHe2 ltac:(intros v Hv; apply Hbase; set_solver)).
      + exact (IHe3 ltac:(intros v Hv; apply Hbase; set_solver)).
    - reflexivity.
  Qed.

  (* Side conditions under which (M1,mp1) and (M2,mp2) assign the same meaning
     to a StackFree assertion:
     - dom M1 = dom M2
     - the assertion's LExpr fvars are covered by dom M1, up to reserved
       names (assertion_lexpr_fvars's own over-approximation through
       LExists/LForall can leak an assertion's own binder names in --
       see local/binders.md)
     - its own binders avoid dom/fvars of either map
     - M1/M2 were built by the ordinary framework machinery, so touch no
       reserved name themselves (subst_map_avoids_reserved) -- needed so
       a reserved name can be resolved directly, without depending on
       dom M1 membership, in the leaf/LPred cases below
     - (Hstab) restricted eval_lvar agreement survives an mp update at a binder
     - (Hbase) restricted eval_lvar agreement for mp1 and mp2 themselves,
       covering reserved names too, not just dom M1 -- necessary because
       subst_congr_step recurses into predicate bodies fetched fresh from
       pred_map, which aren't syntactic subterms of whatever top-level
       assertion this all started from, so no fixed, finite "safe" set
       could be threaded through that unfolding; is_reserved, being a
       uniform predicate, covers it regardless of which body a reserved
       name came from. *)
  Definition subst_congr_cond (a : assertion) (M1 M2 : gmap lvar LExpr)
      (mp1 mp2 : symb_map) : Prop :=
    StackFree a ∧
    assertion_exists_binders a ## (dom M1 ∪ lexpr_map_fvars M1) ∧
    assertion_exists_binders a ## (dom M2 ∪ lexpr_map_fvars M2) ∧
    (∀ v, v ∈ assertion_lexpr_fvars a → v ∈ dom M1 ∨ is_reserved v) ∧
    dom M1 = dom M2 ∧
    subst_map_avoids_reserved M1 ∧
    subst_map_avoids_reserved M2 ∧
    (∀ (q1 q2 : symb_map),
      (∀ x, x ∈ dom M1 → eval_lvar M1 q1 x = eval_lvar M2 q2 x) →
      ∀ (v : lvar), v ∉ lexpr_map_fvars M1 → v ∉ lexpr_map_fvars M2 →
      ∀ (v' : val) (x : lvar), x ∈ dom M1 →
      eval_lvar M1 (fun y => if (y =? v)%string then v' else q1 y) x =
      eval_lvar M2 (fun y => if (y =? v)%string then v' else q2 y) x) ∧
    (∀ x, x ∈ dom M1 ∨ is_reserved x → eval_lvar M1 mp1 x = eval_lvar M2 mp2 x).

  (* The side conditions are symmetric, so one entailment direction suffices to
     get the equivalence. *)
  Lemma subst_congr_cond_sym a M1 M2 mp1 mp2 :
    subst_congr_cond a M1 M2 mp1 mp2 → subst_congr_cond a M2 M1 mp2 mp1.
  Proof using G P.
    intros (Hsf & HbA1 & HbA2 & HfvA & HdomEq & Hmr1 & Hmr2 & Hstab & Hbase).
    split_and!; try assumption.
    - intros v Hv. rewrite <- HdomEq. exact (HfvA v Hv).
    - exact (eq_sym HdomEq).
    - intros q1 q2 Hag v Hv2 Hv1 v' x Hx.
      symmetry. apply Hstab; try assumption.
      + intros y Hy. symmetry. apply Hag. rewrite <- HdomEq. exact Hy.
      + rewrite HdomEq. exact Hx.
    - intros x Hx. symmetry. apply Hbase. set_solver.
  Qed.

  (* Transfer of the LInv clause's argument-evaluation side condition. *)
  Local Lemma Forall2_interp_subst_congr (args : list LExpr) (vs : list val)
      (M1 M2 : gmap lvar LExpr) (mp1 mp2 : symb_map) :
    (∀ le, le ∈ args →
       interp_lexpr (lexpr_subst le M1) mp1 = interp_lexpr (lexpr_subst le M2) mp2) →
    Forall2 (λ le v, interp_lexpr le mp1 = Some v)
            (map (λ e, lexpr_subst e M1) args) vs →
    Forall2 (λ le v, interp_lexpr le mp2 = Some v)
            (map (λ e, lexpr_subst e M2) args) vs.
  Proof.
    revert vs. induction args as [| le args IH]; intros vs Heq HF2; simpl in *.
    - inversion HF2. constructor.
    - inversion HF2 as [| le' v args' vs' Hhd Htl Heq1 Heq2]; subst.
      constructor.
      + rewrite <- (Heq le (elem_of_list_here _ _)). exact Hhd.
      + apply IH; [| exact Htl].
        intros le'' Hle''. exact (Heq le'' (elem_of_list_further _ _ _ Hle'')).
  Qed.

  (* Free variables of one argument are bounded by those of the whole list. *)
  Local Lemma lexpr_fvars_elem_subseteq (le : LExpr) (args : list LExpr) :
    le ∈ args → lexpr_fvars le ⊆ ⋃ (lexpr_fvars <$> args).
  Proof.
    intros Hle y Hy. apply elem_of_union_list.
    exists (lexpr_fvars le). split; [| exact Hy].
    apply elem_of_list_fmap. exists le. split; [reflexivity | exact Hle].
  Qed.

  (* The induction hypothesis carried through the least fixpoint: at every
     index, the translation under (M1, mp1) implies the one under (M2, mp2). *)
  Definition subst_congr_Phi (x : leibnizO trnsl_dom) : iProp Σ :=
    (∀ a0 M1 M2 mp2,
       ⌜x.1.1 = subst a0 M1⌝ -∗
       ⌜subst_congr_cond a0 M1 M2 x.2 mp2⌝ -∗
       trnsl_assertion (subst a0 M2) x.1.2 mp2)%I.

  Global Arguments subst_congr_Phi : simpl never.

  Local Instance subst_congr_Phi_ne : NonExpansive subst_congr_Phi.
  Proof. intros n x y Heq. change (x = y) in Heq. by subst. Qed.

  (* One unfolding step of the congruence, by structural induction on the
     assertion; the LInv clause is a leaf and the LPred clause appeals to
     [subst_congr_Phi], i.e. to the fixpoint induction hypothesis. *)
  Local Lemma subst_congr_step (Hwf : ProgramWF) (a0 : assertion) :
    ∀ (M1 M2 : gmap lvar LExpr) (stk : stack_id) (mp1 mp2 : symb_map),
      subst_congr_cond a0 M1 M2 mp1 mp2 →
      trnsl_assertion_str (trnsl_assertion_curry subst_congr_Phi) (subst a0 M1) stk mp1
      ⊢ trnsl_assertion (subst a0 M2) stk mp2.
  Proof.
    induction a0; intros M1 M2 stk mp1 mp2 Hcond;
      destruct Hcond as (Hsf & HbA1 & HbA2 & HfvA & HdomEq & Hmr1 & Hmr2 & Hstab & Hbase);
      simpl in HbA1, HbA2, HfvA;
      (etrans; [| apply bi.equiv_entails_1_2,
                  (trnsl_assertion_unfold (subst _ M2) stk mp2)]).
    - (* LProc: independent of M and mp *) iIntros "H". iExact "H".
    - (* LStack: not StackFree *) inversion Hsf.
    - (* LExprA *)
      apply bi.pure_mono. unfold LExpr_holds.
      rewrite (interp_lexpr_lexpr_subst_eval_lvar_congr_dom p M1 M2 mp1 mp2 HfvA Hbase).
      tauto.
    - (* LPure *) iIntros "H". iExact "H".
    - (* LOwn *)
      apply bi.exist_mono. intro l.
      apply bi.exist_mono. intro chunk0.
      apply bi.sep_mono.
      { apply bi.pure_mono. unfold LExpr_holds.
        have Hfv_dom : ∀ v, v ∈ lexpr_fvars (LBinOp EqOp e (LVal (LitLoc l))) → v ∈ dom M1 ∨ is_reserved v.
        { apply (fvars_bound_mono _ (assertion_lexpr_fvars (LOwn e fld0 chunk))); [simpl; set_solver | exact HfvA]. }
        have Hcongr := interp_lexpr_lexpr_subst_eval_lvar_congr_dom
          (LBinOp EqOp e (LVal (LitLoc l))) M1 M2 mp1 mp2 Hfv_dom Hbase.
        simpl in Hcongr |- *. rewrite Hcongr. tauto. }
      apply bi.sep_mono; [| done].
      apply bi.pure_mono. intro Hchunk.
      have Hfv_dom2 : ∀ v, v ∈ lexpr_fvars chunk → v ∈ dom M1 ∨ is_reserved v.
      { apply (fvars_bound_mono _ (assertion_lexpr_fvars (LOwn e fld0 chunk))); [simpl; set_solver | exact HfvA]. }
      have Hcongr2 := interp_lexpr_lexpr_subst_eval_lvar_congr_dom
        chunk M1 M2 mp1 mp2 Hfv_dom2 Hbase.
      rewrite <- Hcongr2. exact Hchunk.
    - (* LGhostOwn *)
      simpl. generalize (Γ r).
      intros [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ]; [ | done].
      apply bi.exist_mono. intro l.
      apply bi.exist_mono. intro chunk0.
      apply bi.exist_mono. intro γ.
      apply bi.sep_mono.
      { apply bi.pure_mono. unfold LExpr_holds.
        have Hfv_dom : ∀ v, v ∈ lexpr_fvars (LBinOp EqOp e (LVal (LitLoc l))) → v ∈ dom M1 ∨ is_reserved v.
        { apply (fvars_bound_mono _ (assertion_lexpr_fvars (LGhostOwn e fld0 r chunk))); [simpl; set_solver | exact HfvA]. }
        have Hcongr := interp_lexpr_lexpr_subst_eval_lvar_congr_dom
          (LBinOp EqOp e (LVal (LitLoc l))) M1 M2 mp1 mp2 Hfv_dom Hbase.
        simpl in Hcongr |- *. rewrite Hcongr. tauto. }
      apply bi.sep_mono; [| done].
      apply bi.pure_mono. intro Hchunk.
      have Hfv_dom2 : ∀ v, v ∈ lexpr_fvars chunk → v ∈ dom M1 ∨ is_reserved v.
      { apply (fvars_bound_mono _ (assertion_lexpr_fvars (LGhostOwn e fld0 r chunk))); [simpl; set_solver | exact HfvA]. }
      have Hcongr2 := interp_lexpr_lexpr_subst_eval_lvar_congr_dom
        chunk M1 M2 mp1 mp2 Hfv_dom2 Hbase.
      rewrite <- Hcongr2. exact Hchunk.
    - (* LForall: does not update mp, so nothing about a0's own binders
         changes either -- every field carries over unchanged. *)
      inversion Hsf.
      apply bi.forall_mono. intro v'.
      etrans; [| apply bi.equiv_entails_1_1,
                 (trnsl_assertion_unfold (subst a0 M2) stk mp2)].
      apply (IHa0 M1 M2 stk mp1 mp2). by split_and!.
    - (* LExists: updates mp at the binder v. Hbase' must cover
         dom M1 ∨ is_reserved: for x ∈ dom M1, Hstab unchanged; for x = v
         (reserved, since v ∈ assertion_exists_binders (LExists v t body)
         is covered by HbA1/HbA2's own bundled dom-disjointness), both
         sides reduce to v' directly, since v ∉ dom M1 ∪ dom M2; for
         x ≠ v with x reserved, the update at v doesn't touch x, so the
         outer Hbase carries over via eval_lvar_update_stable. *)
      inversion Hsf. subst.
      apply bi.exist_mono. intro v'.
      apply bi.sep_mono; [done|].
      have Hv1dom : v ∉ dom M1. { set_solver. }
      have Hv2dom : v ∉ dom M2. { set_solver. }
      have Hv1 : v ∉ lexpr_map_fvars M1. { set_solver. }
      have Hv2 : v ∉ lexpr_map_fvars M2. { set_solver. }
      have Hbase_narrow : ∀ x, x ∈ dom M1 → eval_lvar M1 mp1 x = eval_lvar M2 mp2 x.
      { intros x Hx. apply Hbase. left. exact Hx. }
      have Hbase' : ∀ x, x ∈ dom M1 ∨ is_reserved x →
        eval_lvar M1 (fun y => if (y =? v)%string then v' else mp1 y) x =
        eval_lvar M2 (fun y => if (y =? v)%string then v' else mp2 y) x.
      { intros x Hx. destruct (decide (x ∈ dom M1)) as [HxM | HxM].
        - exact (Hstab mp1 mp2 Hbase_narrow v Hv1 Hv2 v' x HxM).
        - destruct (decide (x = v)) as [-> | Hne].
          + unfold eval_lvar.
            apply not_elem_of_dom in Hv1dom. apply not_elem_of_dom in Hv2dom.
            rewrite Hv1dom Hv2dom /=. rewrite String.eqb_refl. reflexivity.
          + rewrite (eval_lvar_update_stable M1 mp1 v v' x Hv1 (or_intror Hne)).
            rewrite (eval_lvar_update_stable M2 mp2 v v' x Hv2 (or_intror Hne)).
            apply Hbase. destruct Hx as [Hx | Hx]; [contradiction (HxM Hx) | right; exact Hx]. }
      etrans; [| apply bi.equiv_entails_1_1,
                 (trnsl_assertion_unfold (subst a0 M2) stk
                    (fun y => if (y =? v)%string then v' else mp2 y))].
      apply (IHa0 M1 M2 stk
        (fun y => if (y =? v)%string then v' else mp1 y)
        (fun y => if (y =? v)%string then v' else mp2 y)).
      split_and!.
      + assumption.
      + set_solver.
      + set_solver.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + exact Hbase'.
    - (* LIte *)
      inversion Hsf. subst.
      have Hfv_cond : ∀ v, v ∈ lexpr_fvars cond → v ∈ dom M1 ∨ is_reserved v.
      { apply (fvars_bound_mono _ (assertion_lexpr_fvars (LIte cond a0_1 a0_2))); [simpl; set_solver | exact HfvA]. }
      apply bi.and_mono.
      + apply bi.wand_mono.
        * apply bi.pure_mono. unfold LExpr_holds.
          rewrite (interp_lexpr_lexpr_subst_eval_lvar_congr_dom cond M1 M2 mp1 mp2 Hfv_cond Hbase). tauto.
        * etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold (subst a0_1 M2) stk mp2)].
          apply (IHa0_1 M1 M2 stk mp1 mp2). split_and!; try assumption.
          -- set_solver.
          -- set_solver.
          -- apply (fvars_bound_mono _ (assertion_lexpr_fvars (LIte cond a0_1 a0_2))); [simpl; set_solver | exact HfvA].
      + apply bi.wand_mono.
        * apply bi.pure_mono. unfold LExpr_holds.
          rewrite (interp_lexpr_lexpr_subst_eval_lvar_congr_dom cond M1 M2 mp1 mp2 Hfv_cond Hbase). tauto.
        * etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold (subst a0_2 M2) stk mp2)].
          apply (IHa0_2 M1 M2 stk mp1 mp2). split_and!; try assumption.
          -- set_solver.
          -- set_solver.
          -- apply (fvars_bound_mono _ (assertion_lexpr_fvars (LIte cond a0_1 a0_2))); [simpl; set_solver | exact HfvA].
    - (* LInv: a leaf -- only the argument evaluations must be transferred *)
      simpl. destruct (inv_map !! inv_name0) as [r|] eqn:Hr; [| done].
      apply bi.exist_mono. intro vs. apply bi.sep_mono; [| done].
      apply bi.pure_mono. apply Forall2_interp_subst_congr.
      intros le Hle.
      apply (interp_lexpr_lexpr_subst_eval_lvar_congr_dom le M1 M2 mp1 mp2);
        [| exact Hbase].
      intros v Hv. apply HfvA. exact (lexpr_fvars_elem_subseteq le args Hle v Hv).
    - (* LPred: the fixpoint induction hypothesis fires here. Unlike every
         other case, the recursive body (pred_body) is fetched fresh from
         pred_map, not a syntactic subterm of a0 -- its own binders need
         pwf_pred_binders_reserved (not HbA1/HbA2, which are about a0's
         own, unrelated, empty binder set) combined with Hmr1/Hmr2 to
         re-derive HbA1/HbA2- and HfvA-shaped facts for it. *)
      simpl. destruct (pred_map !! pred_name0) as [r|] eqn:Hr; [| done].
      have Hbr1 : assertion_exists_binders r.(pred_body) ## (dom M1 ∪ lexpr_map_fvars M1).
      { apply reserved_disjoint_dom.
        - exact (Hwf.(pwf_pred_binders_reserved) pred_name0 r Hr).
        - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
            [exact (proj1 Hmr1 v Hv) | exact (proj2 Hmr1 v Hv)]. }
      have Hbr2 : assertion_exists_binders r.(pred_body) ## (dom M2 ∪ lexpr_map_fvars M2).
      { apply reserved_disjoint_dom.
        - exact (Hwf.(pwf_pred_binders_reserved) pred_name0 r Hr).
        - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
            [exact (proj1 Hmr2 v Hv) | exact (proj2 Hmr2 v Hv)]. }
      have HPredBodyWF := pred_body_wf_from_scoped r
        (Hwf.(pwf_pred_fvars_scoped) pred_name0 r Hr).
      inversion Hsf. rewrite Hr in H1. inversion H1. subst pred_record.
      rewrite (HPredBodyWF args M1 H2 ltac:(set_solver));
        rewrite (HPredBodyWF args M2 H2 ltac:(set_solver)).
      rewrite /trnsl_assertion_curry.
      iIntros "H".
      iApply ("H" $! (subst r.(pred_body) (list_to_map (zip r.(pred_args) args)))
                 M1 M2 mp2); iPureIntro; [reflexivity |].
      split_and!; try assumption.
      + rewrite assertion_exists_binders_subst. exact Hbr1.
      + rewrite assertion_exists_binders_subst. exact Hbr2.
      + intros v Hv.
        destruct (Hwf.(pwf_pred_fvars_bounded) pred_name0 r args Hr H2 v Hv) as [Hin | Hin].
        * exact (HfvA v Hin).
        * right. exact (Hwf.(pwf_pred_binders_reserved) pred_name0 r Hr v Hin).
    - (* LAnd *)
      inversion Hsf. subst.
      apply bi.sep_mono.
      + etrans; [| apply bi.equiv_entails_1_1,
                   (trnsl_assertion_unfold (subst a0_1 M2) stk mp2)].
        apply (IHa0_1 M1 M2 stk mp1 mp2). split_and!; try assumption.
        * set_solver.
        * set_solver.
        * apply (fvars_bound_mono _ (assertion_lexpr_fvars (LAnd a0_1 a0_2))); [simpl; set_solver | exact HfvA].
      + etrans; [| apply bi.equiv_entails_1_1,
                   (trnsl_assertion_unfold (subst a0_2 M2) stk mp2)].
        apply (IHa0_2 M1 M2 stk mp1 mp2). split_and!; try assumption.
        * set_solver.
        * set_solver.
        * apply (fvars_bound_mono _ (assertion_lexpr_fvars (LAnd a0_1 a0_2))); [simpl; set_solver | exact HfvA].
  Qed.

  (* One direction of the congruence. *)
  Lemma trnsl_assertion_subst_mono (Hwf : ProgramWF)
      (a : assertion) (M1 M2 : gmap lvar LExpr) stk_id (mp1 mp2 : symb_map) :
    subst_congr_cond a M1 M2 mp1 mp2 →
    trnsl_assertion (subst a M1) stk_id mp1 ⊢ trnsl_assertion (subst a M2) stk_id mp2.
  Proof.
    intros Hcond.
    iIntros "H".
    iDestruct (least_fixpoint_iter trnsl_assertion_F subst_congr_Phi with "[] H") as "H'".
    { iIntros "!>" ([[b stk'] mp']) "HF".
      rewrite /subst_congr_Phi /=.
      iIntros (a0 M1' M2' mp2') "-> %Hc".
      by iApply (subst_congr_step Hwf a0 M1' M2' stk' mp' mp2' Hc). }
    rewrite /subst_congr_Phi /=.
    iApply ("H'" $! a M1 M2 mp2); iPureIntro; [reflexivity | exact Hcond].
  Qed.

  (* Common generalization:
     If (M1, mp1) and (M2, mp2) agree on eval_lvar for x ∈ dom M1 (Hbase),
     and eval_lvar agreement is preserved under mp updates at v ∉ lexpr_map_fvars M,
     then translating the same StackFree assertion under both maps yields equivalent props. *)
  Lemma trnsl_assertion_subst_congr
    (Hwf : ProgramWF)
    (a : assertion) (M1 M2 : gmap lvar LExpr) stk_id (mp1 mp2 : symb_map) :
    StackFree a →
    assertion_exists_binders a ## (dom M1 ∪ lexpr_map_fvars M1) →
    assertion_exists_binders a ## (dom M2 ∪ lexpr_map_fvars M2) →
    (∀ v, v ∈ assertion_lexpr_fvars a → v ∈ dom M1 ∨ is_reserved v) →
    dom M1 = dom M2 →
    subst_map_avoids_reserved M1 →
    subst_map_avoids_reserved M2 →
    (∀ (q1 q2 : symb_map),
      (∀ x, x ∈ dom M1 → eval_lvar M1 q1 x = eval_lvar M2 q2 x) →
      ∀ (v : lvar), v ∉ lexpr_map_fvars M1 → v ∉ lexpr_map_fvars M2 →
      ∀ (v' : val) (x : lvar), x ∈ dom M1 →
      eval_lvar M1 (fun y => if (y =? v)%string then v' else q1 y) x =
      eval_lvar M2 (fun y => if (y =? v)%string then v' else q2 y) x) →
    (∀ x, x ∈ dom M1 ∨ is_reserved x → eval_lvar M1 mp1 x = eval_lvar M2 mp2 x) →
    trnsl_assertion (subst a M1) stk_id mp1 ≡ trnsl_assertion (subst a M2) stk_id mp2.
  Proof.
    intros HSF HbA_M1 HbA_M2 HfvA HdomEq Hmr1 Hmr2 Hstab Hbase.
    have Hcond : subst_congr_cond a M1 M2 mp1 mp2 by split_and!.
    apply bi.equiv_entails; split.
    - exact (trnsl_assertion_subst_mono Hwf a M1 M2 stk_id mp1 mp2 Hcond).
    - exact (trnsl_assertion_subst_mono Hwf a M2 M1 stk_id mp2 mp1
               (subst_congr_cond_sym _ _ _ _ _ Hcond)).
  Qed.

  (* Side conditions under which two symbolic maps mp1/mp2 assign the same
     meaning to a StackFree, once-substituted assertion, *without* needing
     any agreement at reserved names -- unlike subst_congr_cond's Hbase,
     which needs exactly that (impossible at inv_body_bridge's step 3,
     see local/binders.md). The trick: assertion_true_fvars is scope-
     correct (unlike assertion_lexpr_fvars), so every name it reports is
     genuinely read from the ambient mp -- nothing here is a spurious
     over-approximation through a binder, and covering it directly is both
     necessary and sufficient. *)
  Definition mp_irr_cond (a : assertion) (M : gmap lvar LExpr) (mp1 mp2 : symb_map) : Prop :=
    StackFree a ∧
    assertion_exists_binders a ## (dom M ∪ lexpr_map_fvars M) ∧
    subst_map_avoids_reserved M ∧
    (∀ x, x ∈ assertion_true_fvars a → eval_lvar M mp1 x = eval_lvar M mp2 x).

  Lemma mp_irr_cond_sym a M mp1 mp2 :
    mp_irr_cond a M mp1 mp2 → mp_irr_cond a M mp2 mp1.
  Proof.
    intros (Hsf & HbA & Hmr & Hbase). split_and!; try assumption.
    intros x Hx. symmetry. exact (Hbase x Hx).
  Qed.

  Definition mp_irr_Phi (x : leibnizO trnsl_dom) : iProp Σ :=
    (∀ a0 M mp2,
       ⌜x.1.1 = subst a0 M⌝ -∗
       ⌜mp_irr_cond a0 M x.2 mp2⌝ -∗
       trnsl_assertion (subst a0 M) x.1.2 mp2)%I.

  Global Arguments mp_irr_Phi : simpl never.

  Local Instance mp_irr_Phi_ne : NonExpansive mp_irr_Phi.
  Proof. intros n x y Heq. change (x = y) in Heq. by subst. Qed.

  (* One unfolding step, structural induction on the assertion, exactly
     paralleling subst_congr_step but with a single map M throughout
     (mp1/mp2 only, no M1/M2), and using assertion_true_fvars (no reserved
     escape) instead of assertion_lexpr_fvars/is_reserved. *)
  Local Lemma mp_irr_step (Hwf : ProgramWF) (a0 : assertion) :
    ∀ (M : gmap lvar LExpr) (stk : stack_id) (mp1 mp2 : symb_map),
      mp_irr_cond a0 M mp1 mp2 →
      trnsl_assertion_str (trnsl_assertion_curry mp_irr_Phi) (subst a0 M) stk mp1
      ⊢ trnsl_assertion (subst a0 M) stk mp2.
  Proof.
    induction a0; intros M stk mp1 mp2 Hcond;
      destruct Hcond as (Hsf & HbA & Hmr & Hbase);
      simpl in HbA;
      (etrans; [| apply bi.equiv_entails_1_2,
                  (trnsl_assertion_unfold (subst _ M) stk mp2)]).
    - (* LProc *) iIntros "H". iExact "H".
    - (* LStack *) inversion Hsf.
    - (* LExprA *)
      apply bi.pure_mono. unfold LExpr_holds.
      rewrite (interp_lexpr_subst_eval_lvar_congr_true p M mp1 mp2
                 ltac:(intros x Hx; apply Hbase; simpl; exact Hx)).
      tauto.
    - (* LPure *) iIntros "H". iExact "H".
    - (* LOwn *)
      apply bi.exist_mono. intro l.
      apply bi.exist_mono. intro chunk0.
      apply bi.sep_mono.
      { apply bi.pure_mono. unfold LExpr_holds.
        have Hb1 : ∀ x, x ∈ lexpr_fvars (LBinOp EqOp e (LVal (LitLoc l))) →
          eval_lvar M mp1 x = eval_lvar M mp2 x.
        { intros x Hx. apply Hbase. simpl in Hx |- *. set_solver. }
        have Hcongr := interp_lexpr_subst_eval_lvar_congr_true
          (LBinOp EqOp e (LVal (LitLoc l))) M mp1 mp2 Hb1.
        simpl in Hcongr |- *. rewrite Hcongr. tauto. }
      apply bi.sep_mono; [| done].
      apply bi.pure_mono. intro Hchunk.
      have Hb2 : ∀ x, x ∈ lexpr_fvars chunk → eval_lvar M mp1 x = eval_lvar M mp2 x.
      { intros x Hx. apply Hbase. simpl. set_solver. }
      have Hcongr2 := interp_lexpr_subst_eval_lvar_congr_true chunk M mp1 mp2 Hb2.
      rewrite <- Hcongr2. exact Hchunk.
    - (* LGhostOwn *)
      simpl. generalize (Γ r).
      intros [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ]; [ | done].
      apply bi.exist_mono. intro l.
      apply bi.exist_mono. intro chunk0.
      apply bi.exist_mono. intro γ.
      apply bi.sep_mono.
      { apply bi.pure_mono. unfold LExpr_holds.
        have Hb1 : ∀ x, x ∈ lexpr_fvars (LBinOp EqOp e (LVal (LitLoc l))) →
          eval_lvar M mp1 x = eval_lvar M mp2 x.
        { intros x Hx. apply Hbase. simpl in Hx |- *. set_solver. }
        have Hcongr := interp_lexpr_subst_eval_lvar_congr_true
          (LBinOp EqOp e (LVal (LitLoc l))) M mp1 mp2 Hb1.
        simpl in Hcongr |- *. rewrite Hcongr. tauto. }
      apply bi.sep_mono; [| done].
      apply bi.pure_mono. intro Hchunk.
      have Hb2 : ∀ x, x ∈ lexpr_fvars chunk → eval_lvar M mp1 x = eval_lvar M mp2 x.
      { intros x Hx. apply Hbase. simpl. set_solver. }
      have Hcongr2 := interp_lexpr_subst_eval_lvar_congr_true chunk M mp1 mp2 Hb2.
      rewrite <- Hcongr2. exact Hchunk.
    - (* LForall: inert binder, so a direct recursion at the same mp1/mp2 --
         matches trnsl_assertion_forall never updating mp, and
         assertion_true_fvars not subtracting v either. *)
      inversion Hsf.
      apply bi.forall_mono. intro v'.
      etrans; [| apply bi.equiv_entails_1_1,
                 (trnsl_assertion_unfold (subst a0 M) stk mp2)].
      apply (IHa0 M stk mp1 mp2). by split_and!.
    - (* LExists: updates mp1/mp2 at the same fresh witness v'; assertion_true_fvars
         (LExists v t body) = assertion_true_fvars body ∖ {[v]}, so at x = v both
         sides trivially reduce to v' (v ∉ dom M, from HbA), and at x ≠ v the
         update is a no-op (eval_lvar_update_stable) and the outer Hbase carries
         over directly -- no is_reserved detour needed anywhere. *)
      inversion Hsf. subst.
      apply bi.exist_mono. intro v'.
      apply bi.sep_mono; [done|].
      have HvdomM : v ∉ dom M. { set_solver. }
      have HvlexM : v ∉ lexpr_map_fvars M. { set_solver. }
      have Hbase' : ∀ x, x ∈ assertion_true_fvars a0 →
        eval_lvar M (fun y => if (y =? v)%string then v' else mp1 y) x =
        eval_lvar M (fun y => if (y =? v)%string then v' else mp2 y) x.
      { intros x Hx. destruct (decide (x = v)) as [-> | Hne].
        - unfold eval_lvar. apply not_elem_of_dom in HvdomM. rewrite HvdomM /=.
          rewrite String.eqb_refl. reflexivity.
        - rewrite (eval_lvar_update_stable M mp1 v v' x HvlexM (or_intror Hne)).
          rewrite (eval_lvar_update_stable M mp2 v v' x HvlexM (or_intror Hne)).
          apply Hbase. simpl. set_solver. }
      etrans; [| apply bi.equiv_entails_1_1,
                 (trnsl_assertion_unfold (subst a0 M) stk
                    (fun y => if (y =? v)%string then v' else mp2 y))].
      apply (IHa0 M stk
        (fun y => if (y =? v)%string then v' else mp1 y)
        (fun y => if (y =? v)%string then v' else mp2 y)).
      split_and!.
      + assumption.
      + set_solver.
      + assumption.
      + exact Hbase'.
    - (* LIte *)
      inversion Hsf. subst.
      have Hfv_cond : ∀ x, x ∈ lexpr_fvars cond → eval_lvar M mp1 x = eval_lvar M mp2 x.
      { intros x Hx. apply Hbase. simpl. set_solver. }
      apply bi.and_mono.
      + apply bi.wand_mono.
        * apply bi.pure_mono. unfold LExpr_holds.
          rewrite (interp_lexpr_subst_eval_lvar_congr_true cond M mp1 mp2 Hfv_cond). tauto.
        * etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold (subst a0_1 M) stk mp2)].
          apply (IHa0_1 M stk mp1 mp2). split_and!; try assumption.
          -- set_solver.
          -- intros x Hx. apply Hbase. simpl. set_solver.
      + apply bi.wand_mono.
        * apply bi.pure_mono. unfold LExpr_holds.
          rewrite (interp_lexpr_subst_eval_lvar_congr_true cond M mp1 mp2 Hfv_cond). tauto.
        * etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold (subst a0_2 M) stk mp2)].
          apply (IHa0_2 M stk mp1 mp2). split_and!; try assumption.
          -- set_solver.
          -- intros x Hx. apply Hbase. simpl. set_solver.
    - (* LInv: a leaf -- only the argument evaluations must be transferred *)
      simpl. destruct (inv_map !! inv_name0) as [r|] eqn:Hr; [| done].
      apply bi.exist_mono. intro vs. apply bi.sep_mono; [| done].
      apply bi.pure_mono. apply (Forall2_interp_subst_congr args vs M M mp1 mp2).
      intros le Hle.
      apply (interp_lexpr_subst_eval_lvar_congr_true le M mp1 mp2).
      intros x Hx. apply Hbase. simpl. exact (lexpr_fvars_elem_subseteq le args Hle x Hx).
    - (* LPred: the fixpoint induction hypothesis fires here, exactly as in
         subst_congr_step's LPred case, but re-deriving the mp_irr_cond-shaped
         (rather than subst_congr_cond-shaped) facts for the unfolded body:
         its own binders are reserved (pwf_pred_binders_reserved) and disjoint
         from M (Hmr), and its true fvars are fully closed by its formal args
         (pwf_pred_fvars_closed), so once substituted by the call's own args
         they land inside assertion_true_fvars (LPred pred_name0 args) --
         exactly Hbase's domain, no reserved leftover. *)
      simpl. destruct (pred_map !! pred_name0) as [r|] eqn:Hr; [| done].
      have Hbr : assertion_exists_binders r.(pred_body) ## (dom M ∪ lexpr_map_fvars M).
      { apply reserved_disjoint_dom.
        - exact (Hwf.(pwf_pred_binders_reserved) pred_name0 r Hr).
        - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
            [exact (proj1 Hmr v Hv) | exact (proj2 Hmr v Hv)]. }
      have HPredBodyWF := pred_body_wf_from_scoped r
        (Hwf.(pwf_pred_fvars_scoped) pred_name0 r Hr).
      inversion Hsf. rewrite Hr in H1. inversion H1. subst pred_record.
      rewrite (HPredBodyWF args M H2 ltac:(set_solver)).
      rewrite /trnsl_assertion_curry.
      iIntros "H".
      iApply ("H" $! (subst r.(pred_body) (list_to_map (zip r.(pred_args) args))) M mp2);
        iPureIntro; [reflexivity |].
      split_and!.
      + assumption.
      + rewrite assertion_exists_binders_subst. exact Hbr.
      + exact Hmr.
      + have Hclosed := Hwf.(pwf_pred_fvars_closed) pred_name0 r Hr.
        have Hdom : assertion_true_fvars r.(pred_body) ⊆
          dom (list_to_map (zip r.(pred_args) args) : gmap lvar LExpr).
        { rewrite (dom_list_to_map_zip r.(pred_args) args (eq_sym H2)). exact Hclosed. }
        have Hb1 := assertion_true_fvars_subst_bound r.(pred_body)
          (list_to_map (zip r.(pred_args) args)) Hdom.
        have Hb2 := lexpr_map_fvars_zip_subseteq r.(pred_args) args.
        intros x Hx. apply Hbase. simpl.
        exact (Hb2 x (Hb1 x Hx)).
    - (* LAnd *)
      inversion Hsf. subst.
      apply bi.sep_mono.
      + etrans; [| apply bi.equiv_entails_1_1,
                   (trnsl_assertion_unfold (subst a0_1 M) stk mp2)].
        apply (IHa0_1 M stk mp1 mp2). split_and!; try assumption.
        * set_solver.
        * intros x Hx. apply Hbase. simpl. set_solver.
      + etrans; [| apply bi.equiv_entails_1_1,
                   (trnsl_assertion_unfold (subst a0_2 M) stk mp2)].
        apply (IHa0_2 M stk mp1 mp2). split_and!; try assumption.
        * set_solver.
        * intros x Hx. apply Hbase. simpl. set_solver.
  Qed.

  (* One direction of the equivalence. *)
  Lemma trnsl_assertion_mp_irrelevant_reserved_mono (Hwf : ProgramWF)
      (a : assertion) (M : gmap lvar LExpr) stk_id (mp1 mp2 : symb_map) :
    mp_irr_cond a M mp1 mp2 →
    trnsl_assertion (subst a M) stk_id mp1 ⊢ trnsl_assertion (subst a M) stk_id mp2.
  Proof.
    intros Hcond.
    iIntros "H".
    iDestruct (least_fixpoint_iter trnsl_assertion_F mp_irr_Phi with "[] H") as "H'".
    { iIntros "!>" ([[b stk'] mp']) "HF".
      rewrite /mp_irr_Phi /=.
      iIntros (a0 M' mp2') "-> %Hc".
      by iApply (mp_irr_step Hwf a0 M' stk' mp' mp2' Hc). }
    rewrite /mp_irr_Phi /=.
    iApply ("H'" $! a M mp2); iPureIntro; [reflexivity | exact Hcond].
  Qed.

  (* The lemma local/binders.md's "Blocked" section calls for: translating a
     once-substituted, StackFree assertion doesn't depend on the ambient
     mp's value anywhere -- not even at reserved names, unlike
     trnsl_assertion_subst_congr's Hbase, which needs exactly that
     agreement and is therefore unusable when mp1/mp2 (e.g. a caller's own
     mp vs the canonical WINV_MP) are genuinely unrelated. Only requires
     agreement where the assertion actually, truly (not merely
     over-approximately) reads mp -- assertion_true_fvars a, once M is
     applied, is empty of anything mp could still influence beyond that. *)
  Lemma trnsl_assertion_mp_irrelevant_reserved (Hwf : ProgramWF)
    (a : assertion) (M : gmap lvar LExpr) stk_id (mp1 mp2 : symb_map) :
    StackFree a →
    assertion_exists_binders a ## (dom M ∪ lexpr_map_fvars M) →
    subst_map_avoids_reserved M →
    (∀ x, x ∈ assertion_true_fvars a → eval_lvar M mp1 x = eval_lvar M mp2 x) →
    trnsl_assertion (subst a M) stk_id mp1 ≡ trnsl_assertion (subst a M) stk_id mp2.
  Proof.
    intros HSF HbA Hmr Hbase.
    have Hcond : mp_irr_cond a M mp1 mp2 by split_and!.
    apply bi.equiv_entails; split.
    - exact (trnsl_assertion_mp_irrelevant_reserved_mono Hwf a M stk_id mp1 mp2 Hcond).
    - exact (trnsl_assertion_mp_irrelevant_reserved_mono Hwf a M stk_id mp2 mp1
               (mp_irr_cond_sym _ _ _ _ Hcond)).
  Qed.

  (* Helper: eval_lvar agreement holds for list_to_map (zip args lexprs) vs
     list_to_map (zip args (map LVal arg_vals)) when lexprs and arg_vals are Forall2-related. *)
  Lemma eval_lvar_list_to_map_zip_forall2 (args : list lvar) (lexprs : list LExpr)
      (arg_vals : list lang.val) (mp : symb_map) :
    Forall2 (fun le v => interp_lexpr le mp = Some (trnsl_val v)) lexprs arg_vals →
    ∀ x,
    eval_lvar (list_to_map (zip args lexprs)) mp x =
    eval_lvar (list_to_map (zip args (map (fun v : lang.val => LVal (trnsl_val v)) arg_vals))) mp x.
  Proof.
    intro HF2. unfold eval_lvar.
    revert args.
    induction HF2 as [| le v lexprs' arg_vals' Hle HF2' IH]; intro args.
    - simpl. destruct args; simpl; reflexivity.
    - destruct args as [| a args']; simpl.
      + intro x. reflexivity.
      + intro x.
        destruct (decide (x = a)) as [-> | Hne].
        * rewrite !lookup_insert. simpl. exact Hle.
        * rewrite !lookup_insert_ne; [| by intro H; apply Hne; exact (eq_sym H) | by intro H; apply Hne; exact (eq_sym H)].
          exact (IH args' x).
  Qed.

  (* Helper: every value in list_to_map (zip ks vs) is in vs. *)
  Lemma lookup_list_to_map_zip_in_snd {B : Type} (ks : list lvar) (vs : list B) (k : lvar) v :
    (list_to_map (zip ks vs) : gmap lvar B) !! k = Some v → v ∈ vs.
  Proof.
    revert vs. induction ks as [| k' ks' IH]; intros vs Hk.
    - rewrite lookup_empty in Hk. discriminate.
    - destruct vs as [| v' vs'].
      + rewrite lookup_empty in Hk. discriminate.
      + simpl in Hk.
        destruct (decide (k = k')) as [-> | Hne].
        * rewrite lookup_insert in Hk. injection Hk as <-.
          apply elem_of_cons. left. reflexivity.
        * rewrite lookup_insert_ne in Hk; [| congruence].
          apply elem_of_cons. right. exact (IH vs' Hk).
  Qed.

  (* Helper: if lv is fresh w.r.t. stk, and lexprs are translations of args via trnsl_expr_lExpr,
     then lv ∉ lexpr_map_fvars of any zip map over lexprs. *)
  Lemma fresh_lvar_not_in_lexpr_map_fvars_zip (stk : stack) (args : list lang.expr)
      (lexprs : list LExpr) (arg_names : list lvar) (lv : lvar) :
    map (fun arg => trnsl_expr_lExpr stk arg) args = map Some lexprs →
    fresh_lvar stk lv →
    lv ∉ lexpr_map_fvars (list_to_map (zip arg_names lexprs)).
  Proof.
    intros H2 Hfresh.
    apply (proj2 (lexpr_map_fvars_spec _ _)).
    intros k e Hke.
    apply lookup_list_to_map_zip_in_snd in Hke.
    apply elem_of_list_lookup_1 in Hke as [i Hi].
    have H2i : map (fun arg => trnsl_expr_lExpr stk arg) args !! i = Some (Some e).
    { rewrite H2. rewrite list_lookup_fmap. rewrite Hi. reflexivity. }
    rewrite list_lookup_fmap in H2i.
    destruct (args !! i) as [arg|] eqn:Harg.
    - simpl in H2i. injection H2i as He.
      exact (trnsl_expr_lExpr_fresh_lvar stk arg e lv He Hfresh).
    - discriminate.
  Qed.

  Lemma hstab_lexpr_subst_fwd (args : list lvar) (lexprs : list LExpr)
      (arg_vals : list lang.val)
      (HdomEq : dom (list_to_map (zip args lexprs) : gmap lvar LExpr) =
                dom (list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals)) : gmap lvar LExpr)) :
    ∀ (q1 q2 : symb_map),
    (∀ x, x ∈ dom (list_to_map (zip args lexprs) : gmap lvar LExpr) →
           eval_lvar (list_to_map (zip args lexprs)) q1 x =
           eval_lvar (list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))) q2 x) →
    ∀ (v : lvar),
    v ∉ lexpr_map_fvars (list_to_map (zip args lexprs)) →
    v ∉ lexpr_map_fvars (list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))) →
    ∀ (v' : val) (x : lvar), x ∈ dom (list_to_map (zip args lexprs) : gmap lvar LExpr) →
    eval_lvar (list_to_map (zip args lexprs)) (fun y => if (y =? v)%string then v' else q1 y) x =
    eval_lvar (list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))) (fun y => if (y =? v)%string then v' else q2 y) x.
  Proof.
    intros q1 q2 Hbase v Hv1 Hv2 v' x Hx.
    rewrite (eval_lvar_update_stable _ q1 v v' x Hv1 (or_introl Hx)).
    rewrite (Hbase x Hx).
    have Hx2 : x ∈ dom (list_to_map (zip args (map (λ w, LVal (trnsl_val w)) arg_vals)) : gmap lvar LExpr).
    { rewrite <- HdomEq. exact Hx. }
    exact (eq_sym (eval_lvar_update_stable _ q2 v v' x Hv2 (or_introl Hx2))).
  Qed.

  Lemma hstab_lexpr_subst_r (args : list lvar) (lexprs : list LExpr)
      (arg_vals : list lang.val) (lvar_x : lvar) (ret_val : lang.val)
      (HdomEq : dom (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) =
                dom (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))) : gmap lvar LExpr)) :
    ∀ (q1 q2 : symb_map),
    (∀ x, x ∈ dom (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) →
           eval_lvar (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs))) q1 x =
           eval_lvar (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals)))) q2 x) →
    ∀ (v : lvar),
    v ∉ lexpr_map_fvars (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs))) →
    v ∉ lexpr_map_fvars (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals)))) →
    ∀ (v' : val) (x : lvar), x ∈ dom (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) →
    eval_lvar (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs))) (fun y => if (y =? v)%string then v' else q1 y) x =
    eval_lvar (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals)))) (fun y => if (y =? v)%string then v' else q2 y) x.
  Proof.
    intros q1 q2 Hbase v Hv1 Hv2 v' x Hx.
    rewrite (eval_lvar_update_stable _ q1 v v' x Hv1 (or_introl Hx)).
    rewrite (Hbase x Hx).
    have Hx2 : x ∈ dom (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))) : gmap lvar LExpr).
    { rewrite <- HdomEq. exact Hx. }
    exact (eq_sym (eval_lvar_update_stable _ q2 v v' x Hv2 (or_introl Hx2))).
  Qed.

  (* Extra "no key here is reserved" hypotheses (Hargs_ok, Hlvar_x_ok)
     needed for the new is_reserved x disjunct: when x is reserved, none
     of "#ret_val" (never reserved, a different, "#"-prefixed convention),
     args's own formal-argument names (never reserved by the framework's
     own naming discipline, see local/binders.md), or lvar_x (ditto for
     derivation-fresh witnesses) can equal x, so both sides fall back
     directly to mp/the ret_val update, which trivially agree. *)
  Lemma hbase_lexpr_subst_r (args : list lvar) (lexprs : list LExpr)
      (arg_vals : list lang.val) (lvar_x : lvar) (ret_val : lang.val) (mp : symb_map) :
    lvar_x ∉ lexpr_map_fvars (list_to_map (zip args lexprs)) →
    ¬ is_reserved lvar_x →
    Forall (λ a, ¬ is_reserved a) args →
    Forall2 (λ expr val0, interp_lexpr expr mp = Some (trnsl_val val0)) lexprs arg_vals →
    ∀ x, x ∈ dom (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) ∨ is_reserved x →
    eval_lvar (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)))
      (λ x0, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0) x =
    eval_lvar (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))))
      mp x.
  Proof using G.
    intros Hfresh Hlvar_x_ok Hargs_ok HF2 x [Hdom | Hres].
    - destruct (decide (x = "#ret_val")) as [-> | Hne].
      + unfold eval_lvar. rewrite !lookup_insert. simpl. rewrite String.eqb_refl. reflexivity.
      + have Hne' : "#ret_val" ≠ x := fun H => Hne (eq_sym H).
        have Hdomx : x ∈ dom (list_to_map (zip args lexprs) : gmap lvar LExpr).
        { rewrite dom_insert in Hdom. set_solver. }
        unfold eval_lvar.
        rewrite (lookup_insert_ne _ _ _ _ Hne').
        rewrite (lookup_insert_ne _ _ _ _ Hne').
        have Hcongr : eval_lvar (list_to_map (zip args lexprs)) mp x =
                      eval_lvar (list_to_map (zip args (map (λ w, LVal (trnsl_val w)) arg_vals))) mp x :=
          eval_lvar_list_to_map_zip_forall2 args lexprs arg_vals mp HF2 x.
        unfold eval_lvar in Hcongr.
        destruct (list_to_map (zip args lexprs) !! x) as [le|] eqn:Hle.
        * have Hle_fresh : lvar_x ∉ lexpr_fvars le :=
            proj1 (lexpr_map_fvars_spec _ _) Hfresh x le Hle.
          rewrite Hle. simpl. simpl in Hcongr.
          etransitivity.
          { exact (interp_lexpr_stable le mp lvar_x (trnsl_val ret_val) Hle_fresh). }
          exact Hcongr.
        * exfalso. rewrite elem_of_dom in Hdomx. destruct Hdomx as [le' Hle']. congruence.
    - have Hne_ret : x ≠ "#ret_val".
      { intros ->. unfold is_reserved in Hres. discriminate. }
      have Hne_lvar_x : x ≠ lvar_x.
      { intros ->. exact (Hlvar_x_ok Hres). }
      have Hnotin_args : x ∉ args.
      { intros Hin. rewrite Forall_forall in Hargs_ok. exact (Hargs_ok x Hin Hres). }
      have Hnotin1 : (list_to_map (zip args lexprs) : gmap lvar LExpr) !! x = None.
      { destruct ((list_to_map (zip args lexprs) : gmap lvar LExpr) !! x) as [e|] eqn:Heq; [| reflexivity].
        exfalso. apply elem_of_list_to_map_2 in Heq. apply elem_of_zip_l in Heq.
        exact (Hnotin_args Heq). }
      have Hnotin2 : (list_to_map (zip args (map (λ w, LVal (trnsl_val w)) arg_vals)) : gmap lvar LExpr) !! x = None.
      { destruct ((list_to_map (zip args (map (λ w, LVal (trnsl_val w)) arg_vals)) : gmap lvar LExpr) !! x)
          as [e|] eqn:Heq; [| reflexivity].
        exfalso. apply elem_of_list_to_map_2 in Heq. apply elem_of_zip_l in Heq.
        exact (Hnotin_args Heq). }
      unfold eval_lvar.
      rewrite (lookup_insert_ne _ _ _ _ (fun H => Hne_ret (eq_sym H))).
      rewrite (lookup_insert_ne _ _ _ _ (fun H => Hne_ret (eq_sym H))).
      rewrite Hnotin1 Hnotin2. simpl.
      rewrite (proj2 (String.eqb_neq x lvar_x) Hne_lvar_x).
      reflexivity.
  Qed.

  Lemma trnsl_assertion_w_lexpr_subst assertion lexprs args arg_vals stk_id mp p1 p2
      (Hwf : ProgramWF)
      (HSF : StackFree assertion)
      (HbA_M1 : assertion_exists_binders assertion ##
        (dom (list_to_map (zip args lexprs) : gmap lvar LExpr) ∪ lexpr_map_fvars (list_to_map (zip args lexprs))))
      (HbA_M2 : assertion_exists_binders assertion ##
        (dom (list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr) ∪
         lexpr_map_fvars (list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)))))
      (HfvA : ∀ v, v ∈ assertion_lexpr_fvars assertion →
        v ∈ (dom (list_to_map (zip args lexprs) : gmap lvar LExpr)) ∨ is_reserved v)
      (HdomEq : dom (list_to_map (zip args lexprs) : gmap lvar LExpr) = dom (list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr))
      (Hmr1 : subst_map_avoids_reserved (list_to_map (zip args lexprs)))
      (Hmr2 : subst_map_avoids_reserved (list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)))) :
    Forall2 (λ expr val0, interp_lexpr expr mp = Some (trnsl_val val0)) lexprs arg_vals →
    trnsl_assertion (subst assertion (list_to_map (zip args lexprs))) stk_id mp ≡ p1 →
    trnsl_assertion (subst assertion (list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)))) stk_id mp ≡ p2 →
    p1 -∗ p2.
  Proof.
    intros HF2 Hp1 Hp2.
    have Hbase : ∀ x, x ∈ dom (list_to_map (zip args lexprs) : gmap lvar LExpr) ∨ is_reserved x →
                       eval_lvar (list_to_map (zip args lexprs)) mp x =
                       eval_lvar (list_to_map (zip args (map (λ val, LVal (trnsl_val val)) arg_vals))) mp x.
    { intros x _. exact (eval_lvar_list_to_map_zip_forall2 args lexprs arg_vals mp HF2 x). }
    have Hstab := hstab_lexpr_subst_fwd args lexprs arg_vals HdomEq.
    have Heq := trnsl_assertion_subst_congr Hwf assertion _ _ stk_id mp mp
      HSF HbA_M1 HbA_M2 HfvA HdomEq Hmr1 Hmr2 Hstab Hbase.
    rewrite <- Hp1. rewrite Heq. rewrite Hp2.
    iIntros "H". iExact "H".
  Qed.

  Lemma trnsl_assertion_w_lexpr_subst_r assertion lexprs args arg_vals lvar_x ret_val stk stk_id mp p1 p2
      (Hwf : ProgramWF)
      (HSF : StackFree assertion)
      (HbA_M1 : assertion_exists_binders assertion ##
        (dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) ∪
         lexpr_map_fvars (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)))))
      (HbA_M2 : assertion_exists_binders assertion ##
        (dom (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))) : gmap lvar LExpr) ∪
         lexpr_map_fvars (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))))))
      (HfvA : ∀ v, v ∈ assertion_lexpr_fvars assertion →
        v ∈ (dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr)) ∨ is_reserved v)
      (HdomEq : dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) = dom (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))) : gmap lvar LExpr))
      (Hmr1 : subst_map_avoids_reserved (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs))))
      (Hmr2 : subst_map_avoids_reserved (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)))))
      (Hfresh_base : lvar_x ∉ lexpr_map_fvars (list_to_map (zip args lexprs)))
      (Hlvar_x_ok : ¬ is_reserved lvar_x)
      (Hargs_ok : Forall (λ a, ¬ is_reserved a) args) :
    fresh_lvar stk lvar_x →
    Forall2 (λ expr val0, interp_lexpr expr mp = Some (trnsl_val val0)) lexprs arg_vals →
    trnsl_assertion (subst assertion (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)))) stk_id
      (λ x0, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0) ≡ p1 →
    trnsl_assertion (subst assertion (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))))) stk_id mp ≡ p2 →
    p2 -∗ p1.
  Proof.
    intros _Hfresh HF2 Hp1 Hp2.
    have Hstab_r := hstab_lexpr_subst_r args lexprs arg_vals lvar_x ret_val HdomEq.
    have Hbase_r : ∀ x, x ∈ dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) ∨ is_reserved x →
      eval_lvar (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)))
        (λ x0, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0) x =
      eval_lvar (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val, LVal (trnsl_val val)) arg_vals))))
        mp x.
    { intros x Hx. exact (hbase_lexpr_subst_r args lexprs arg_vals lvar_x ret_val mp Hfresh_base Hlvar_x_ok Hargs_ok HF2 x Hx). }
    have Heq := trnsl_assertion_subst_congr Hwf assertion _ _ stk_id
      (λ x0, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0) mp
      HSF HbA_M1 HbA_M2 HfvA HdomEq Hmr1 Hmr2 Hstab_r Hbase_r.
    rewrite <- Hp2. rewrite <- Heq. rewrite Hp1.
    iIntros "H". iExact "H".
  Qed.



  (* Fixpoint induction hypothesis for stack-independence. *)
  Definition stack_free_Phi (x : leibnizO trnsl_dom) : iProp Σ :=
    (∀ stk', ⌜StackFree x.1.1⌝ -∗ trnsl_assertion x.1.1 stk' x.2)%I.

  Global Arguments stack_free_Phi : simpl never.

  Local Instance stack_free_Phi_ne : NonExpansive stack_free_Phi.
  Proof. intros n x y Heq. change (x = y) in Heq. by subst. Qed.

  Local Lemma stack_free_step (a : assertion) :
    ∀ (stk stk' : stack_id) (mp : symb_map),
      StackFree a →
      trnsl_assertion_str (trnsl_assertion_curry stack_free_Phi) a stk mp
      ⊢ trnsl_assertion a stk' mp.
  Proof.
    induction a; intros stk stk' mp Hsf;
      (etrans; [| apply bi.equiv_entails_1_2, (trnsl_assertion_unfold _ stk' mp)]).
    - (* LProc *) iIntros "H". iExact "H".
    - (* LStack: not StackFree *) inversion Hsf.
    - (* LExprA *) iIntros "H". iExact "H".
    - (* LPure *) iIntros "H". iExact "H".
    - (* LOwn *) iIntros "H". iExact "H".
    - (* LGhostOwn *) simpl. generalize (Γ r).
      intros [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ];
        iIntros "H"; iExact "H".
    - (* LForall *)
      inversion Hsf. apply bi.forall_mono. intro v'.
      etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold a stk' mp)].
      by apply (IHa stk stk' mp).
    - (* LExists *)
      inversion Hsf. apply bi.exist_mono. intro v'.
      apply bi.sep_mono; [done|].
      etrans; [| apply bi.equiv_entails_1_1,
                 (trnsl_assertion_unfold a stk' (λ x, if (x =? v)%string then v' else mp x))].
      by apply (IHa stk stk' (λ x, if (x =? v)%string then v' else mp x)).
    - (* LIte *)
      inversion Hsf. subst. apply bi.and_mono.
      + apply bi.wand_mono; [done |].
        etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold a1 stk' mp)].
        by apply (IHa1 stk stk' mp).
      + apply bi.wand_mono; [done |].
        etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold a2 stk' mp)].
        by apply (IHa2 stk stk' mp).
    - (* LInv: a leaf, independent of the stack *)
      simpl. destruct (inv_map !! inv_name0) as [r|] eqn:Hr; [| done].
      iIntros "H". iExact "H".
    - (* LPred: the fixpoint induction hypothesis fires here *)
      simpl. destruct (pred_map !! pred_name0) as [r|] eqn:Hr; [| done].
      inversion Hsf. rewrite Hr in H1. inversion H1. subst pred_record.
      rewrite /trnsl_assertion_curry.
      iIntros "H". by iApply ("H" $! stk').
    - (* LAnd *)
      inversion Hsf. subst. apply bi.sep_mono.
      + etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold a1 stk' mp)].
        by apply (IHa1 stk stk' mp).
      + etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold a2 stk' mp)].
        by apply (IHa2 stk stk' mp).
  Qed.

  Lemma stack_free_assertion_trnsl_mono assertion stk_id stk_id' mp :
    StackFree assertion ->
    trnsl_assertion assertion stk_id mp ⊢ trnsl_assertion assertion stk_id' mp.
  Proof.
    intros HSF.
    iIntros "H".
    iDestruct (least_fixpoint_iter trnsl_assertion_F stack_free_Phi with "[] H") as "H'".
    { iIntros "!>" ([[b stk] mp']) "HF".
      rewrite /stack_free_Phi /=. iIntros (stk'') "%Hb".
      by iApply (stack_free_step b stk stk'' mp' Hb). }
    rewrite /stack_free_Phi /=. by iApply ("H'" $! stk_id').
  Qed.

  Lemma stack_free_assertion_trnsl assertion stk_id stk_id' mp :
    StackFree assertion ->
    trnsl_assertion assertion stk_id mp ≡ trnsl_assertion assertion stk_id' mp.
  Proof.
    intros HSF. apply bi.equiv_entails; split;
      by apply stack_free_assertion_trnsl_mono.
  Qed.

  (* Hmr: subst_map touches no reserved name -- needed to re-derive the
     "## dom subst_map" premise InvBodyWF/PredBodyWF now require (in place
     of the old, unconditional-over-M pwf_*_binders_fresh) for whichever
     inv/pred body SF_Inv/SF_Pred happens to unfold. Whoever discharges
     this for a concrete subst_map is asserting it was built by the
     ordinary framework machinery -- see subst_map_avoids_reserved and
     local/binders.md. *)
  Lemma stack_free_assertion_subst
    (Hwf : ProgramWF)
    assertion subst_map
    (Hmr : (∀ v, v ∈ dom subst_map → ¬ is_reserved v)) :
    StackFree assertion -> StackFree (subst assertion subst_map).
  Proof.
    intros HSF. induction HSF; simpl; try constructor; try assumption.
    - (* SF_Inv *)
      have Hbwf := inv_body_wf_from_scoped inv_record (Hwf.(pwf_inv_fvars_scoped) _ _ H).
      have Hbr : assertion_exists_binders inv_record.(inv_body) ## dom subst_map.
      { apply reserved_disjoint_dom.
        - exact (Hwf.(pwf_inv_binders_reserved) _ _ H).
        - exact Hmr. }
      eapply SF_Inv. { exact H. } { rewrite map_length. exact H0. }
      rewrite (Hbwf args subst_map H0 Hbr). exact IHHSF.
    - (* SF_Pred *)
      have Hbwf := pred_body_wf_from_scoped pred_record (Hwf.(pwf_pred_fvars_scoped) _ _ H).
      have Hbr : assertion_exists_binders pred_record.(pred_body) ## dom subst_map.
      { apply reserved_disjoint_dom.
        - exact (Hwf.(pwf_pred_binders_reserved) _ _ H).
        - exact Hmr. }
      eapply SF_Pred. { exact H. } { rewrite map_length. exact H0. }
      rewrite (Hbwf args subst_map H0 Hbr). exact IHHSF.
  Qed.
  

  (* ── Timelessness ────────────────────────────────────────────────────────
     Nothing in the translation is step-indexed any more: [LInv] is a discrete
     ownership fragment, [LPred] is a plain recursive call, and every leaf is a
     discrete resource.  Along a StackFree derivation -- which is exactly the
     discipline invariant bodies are held to -- the translation is therefore
     Timeless, and an invariant holding one can be opened for free. *)

  Local Lemma transport_cmra_discrete {A B : cmra} (p : A = B) (x : cmra_car A) :
    Discrete x → Discrete (transport (f_equal cmra_car p) x).
  Proof. intros Hx. destruct p. simpl. exact Hx. Qed.

  Lemma trnsl_assertion_timeless (a : assertion) (Hsf : StackFree a) :
    ∀ stk mp, Timeless (trnsl_assertion a stk mp).
  Proof.
    induction Hsf; intros stk mp.
    - (* LProc *)
      rewrite trnsl_assertion_unfold /trnsl_assertion_pre /=.
      destruct proc_entry. destruct (trnsl_stmt body); apply _.
    - (* LExprA *)
      rewrite trnsl_assertion_unfold. apply _.
    - (* LPure *)
      rewrite trnsl_assertion_unfold. apply _.
    - (* LOwn *)
      rewrite trnsl_assertion_unfold. apply _.
    - (* LGhostOwn *)
      rewrite trnsl_assertion_unfold /trnsl_assertion_pre /=.
      generalize (Γ RAPAck).
      intros [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ]; [ | apply _].
      apply bi.exist_timeless. intro l.
      apply bi.exist_timeless. intro chunk0.
      apply bi.exist_timeless. intro γ.
      apply bi.sep_timeless; [apply _ |].
      apply bi.sep_timeless; [apply _ |].
      apply bi.sep_timeless; [apply _ |].
      apply own_timeless.
      have HdisGi : CmraDiscrete (Gs i). { rewrite -Heq_cmra. exact Hdis. }
      apply _.
    - (* LForall *)
      rewrite trnsl_assertion_forall. apply bi.forall_timeless. intros _. apply IHHsf.
    - (* LExists *)
      rewrite trnsl_assertion_exists. apply bi.exist_timeless. intros v'.
      apply bi.sep_timeless; [apply _ | apply IHHsf].
    - (* LIte *)
      rewrite trnsl_assertion_ite. apply bi.and_timeless.
      + apply bi.wand_timeless. apply IHHsf1.
      + apply bi.wand_timeless. apply IHHsf2.
    - (* LAnd *)
      rewrite trnsl_assertion_and. apply bi.sep_timeless; [apply IHHsf1 | apply IHHsf2].
    - (* LInv: a discrete ownership fragment *)
      have Hv := trnsl_inv_validity' inv_name0 args stk mp.
      rewrite H in Hv. rewrite Hv. apply _.
    - (* LPred *)
      have Hv := trnsl_pred_validity' pred_name0 args stk mp.
      rewrite H in Hv. simpl in Hv. rewrite <- Hv. apply IHHsf.
  Qed.

End AssertionsProperties.

(* ── The shared world backing invariant assertions ────────────────────────
   [LInv inv args] owns a fragment of [invtoken_names inv]'s authoritative set
   of established argument vectors.  [Winv inv] is the matching authority,
   holding the invariant's body for each established vector.  It is Timeless,
   so it can live under a native Iris [inv] and be opened with
   [inv_acc_timeless] -- no later, no later credit.  It is defined *after*
   [trnsl_assertion] is total, so there is no circularity. *)
Section InvariantWorld.

  (* Invariant bodies are stack-free and, once instantiated at concrete values,
     closed, so these choices are immaterial (see [Winv_body_congr]). *)
  Definition WINV_STK : stack_id := 0%Z.
  Definition WINV_MP : symb_map := λ _, LitUnit.

  Definition inv_arg_map (r : InvRecord) (vs : list val) : gmap var LExpr :=
    list_to_map (zip r.(inv_args) (map LVal vs)).

  Definition inv_body_at (inv' : inv_name) (vs : list val) : iProp Σ :=
    match inv_map !! inv' with
    | Some r =>
        if decide (length vs = length r.(inv_args))
        then trnsl_assertion (subst r.(inv_body) (inv_arg_map r vs)) WINV_STK WINV_MP
        else True%I
    | None => True%I
    end.

  Definition Winv (inv' : inv_name) : iProp Σ :=
    (∃ I : gset (list val),
       own (invtoken_names inv') (● (I : inv_argsUR)) ∗
       [∗ set] vs ∈ I, inv_body_at inv' vs)%I.

  Lemma inv_body_at_timeless (Hwf : ProgramWF) inv' vs : Timeless (inv_body_at inv' vs).
  Proof.
    rewrite /inv_body_at. destruct (inv_map !! inv') as [r|] eqn:Hr; [| apply _].
    destruct (decide (length vs = length r.(inv_args))) as [Hlen |]; [| apply _].
    apply trnsl_assertion_timeless.
    apply (stack_free_assertion_subst Hwf).
    - intros v Hv. apply elem_of_dom in Hv as [e He].
      apply elem_of_list_to_map_2 in He. apply elem_of_zip_l in He.
      exact (proj1 (Forall_forall _ _) (Hwf.(pwf_inv_args_not_reserved) inv' r Hr) v He).
    - exact (Hwf.(pwf_inv_body_stack_free) inv' r Hr).
  Qed.

  Lemma Winv_timeless (Hwf : ProgramWF) inv' : Timeless (Winv inv').
  Proof.
    rewrite /Winv. apply bi.exist_timeless. intro Iopen.
    apply bi.sep_timeless; [apply _ |].
    apply big_sepS_timeless. intros vs _. by apply inv_body_at_timeless.
  Qed.

  (* [Winv] stores an invariant's body instantiated at *concrete values* and
     translated at a canonical stack/symbolic map.  A verification site sees it
     instantiated at *symbolic* LExprs under its own stack and symbolic map.
     The two agree whenever the LExprs evaluate to those values: the body is
     StackFree (so the stack is immaterial) and, once instantiated at values,
     closed (so the symbolic map is immaterial). *)
  (* Hlexprs_ok: the caller's own argument expressions -- built by
     trnsl_expr_lExpr against some ordinary symbolic stack -- touch no
     reserved lvar. Same status as subst_map_avoids_reserved elsewhere:
     an explicit premise recording that lexprs was actually built by the
     framework's own machinery, not a proof obligation dischargeable here
     (see local/binders.md's deferred item). *)
  Lemma inv_body_bridge (Hwf : ProgramWF) (inv' : inv_name) (r : InvRecord)
      (lexprs : list LExpr) (vs : list val) (stk : stack_id) (mp : symb_map)
      (Hlexprs_ok : ∀ v, v ∈ lexpr_map_fvars (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) → ¬ is_reserved v) :
    inv_map !! inv' = Some r →
    length lexprs = length r.(inv_args) →
    Forall2 (λ le v, interp_lexpr le mp = Some v) lexprs vs →
    trnsl_assertion (subst r.(inv_body) (list_to_map (zip r.(inv_args) lexprs))) stk mp
    ≡ trnsl_assertion (subst r.(inv_body) (inv_arg_map r vs)) WINV_STK WINV_MP.
  Proof.
    intros Hr Hlen HF2.
    have Hsf : StackFree r.(inv_body) := Hwf.(pwf_inv_body_stack_free) inv' r Hr.
    have Hlenvs : length vs = length r.(inv_args).
    { rewrite <- Hlen. symmetry. exact (Forall2_length _ _ _ HF2). }
    (* The value-instantiated map has no free variables at all. *)
    have Hvals : ∀ (l : list val) e, e ∈ map LVal l → ∃ w, e = LVal w.
    { intros l. induction l as [| w l' IH]; intros e He; simpl in He.
      - inversion He.
      - apply elem_of_cons in He as [-> | He]; [by exists w | exact (IH e He)]. }
    have Hnofv : lexpr_map_fvars (inv_arg_map r vs) = ∅.
    { apply elem_of_equiv_empty_L. intros y Hy.
      have Hno : y ∉ lexpr_map_fvars (inv_arg_map r vs).
      { apply (proj2 (lexpr_map_fvars_spec _ _)). intros k e Hke.
        rewrite /inv_arg_map in Hke.
        apply lookup_list_to_map_zip_in_snd in Hke.
        destruct (Hvals vs e Hke) as [w ->]. set_solver. }
      exact (Hno Hy). }
    have Hdom1 : dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr)
                 = list_to_set r.(inv_args).
    { apply dom_list_to_map_zip. by rewrite Hlen. }
    have Hdom2 : dom (inv_arg_map r vs : gmap lvar LExpr) = list_to_set r.(inv_args).
    { rewrite /inv_arg_map. apply dom_list_to_map_zip. rewrite map_length. by rewrite Hlenvs. }
    have HdomEq : dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr)
                = dom (inv_arg_map r vs : gmap lvar LExpr).
    { by rewrite Hdom1 Hdom2. }
    have Hfv : ∀ v, v ∈ assertion_lexpr_fvars r.(inv_body) →
      v ∈ dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) ∨ is_reserved v.
    { intros v Hv. destruct (Hwf.(pwf_inv_fvars_scoped) inv' r Hr v Hv) as [Hin | Hin].
      - left. rewrite Hdom1. exact Hin.
      - right. exact (Hwf.(pwf_inv_binders_reserved) inv' r Hr v Hin). }
    have Hfv2 : ∀ v, v ∈ assertion_lexpr_fvars r.(inv_body) →
      v ∈ dom (inv_arg_map r vs : gmap lvar LExpr) ∨ is_reserved v.
    { intros v Hv. destruct (Hwf.(pwf_inv_fvars_scoped) inv' r Hr v Hv) as [Hin | Hin].
      - left. rewrite Hdom2. exact Hin.
      - right. exact (Hwf.(pwf_inv_binders_reserved) inv' r Hr v Hin). }
    have Hmr1 : subst_map_avoids_reserved (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr).
    { split.
      - intros v Hv. apply elem_of_dom in Hv as [e He].
        apply elem_of_list_to_map_2 in He. apply elem_of_zip_l in He.
        exact (proj1 (Forall_forall _ _) (Hwf.(pwf_inv_args_not_reserved) inv' r Hr) v He).
      - exact Hlexprs_ok. }
    (* eval_lvar on the value-instantiated map ignores the symbolic map. *)
    have Hval_eval : ∀ (q : symb_map) x,
        x ∈ dom (inv_arg_map r vs : gmap lvar LExpr) →
        eval_lvar (inv_arg_map r vs) q x = eval_lvar (inv_arg_map r vs) WINV_MP x.
    { intros q x Hx. rewrite /eval_lvar.
      apply elem_of_dom in Hx as [e He].
      rewrite He.
      have He2 : e ∈ map LVal vs.
      { rewrite /inv_arg_map in He.
        exact (lookup_list_to_map_zip_in_snd _ _ _ _ He). }
      destruct (Hvals vs e He2) as [w ->]. done. }
    have Hmr2 : subst_map_avoids_reserved (inv_arg_map r vs : gmap lvar LExpr).
    { split.
      - intros v Hv. apply elem_of_dom in Hv as [e He]. rewrite /inv_arg_map in He.
        apply elem_of_list_to_map_2 in He. apply elem_of_zip_l in He.
        exact (proj1 (Forall_forall _ _) (Hwf.(pwf_inv_args_not_reserved) inv' r Hr) v He).
      - rewrite Hnofv. set_solver. }
    have HbA_M1 : assertion_exists_binders r.(inv_body) ##
      (dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) ∪ lexpr_map_fvars (list_to_map (zip r.(inv_args) lexprs))).
    { apply reserved_disjoint_dom.
      - exact (Hwf.(pwf_inv_binders_reserved) inv' r Hr).
      - intros v Hv. apply elem_of_union in Hv as [Hv|Hv]; [exact (proj1 Hmr1 v Hv) | exact (proj2 Hmr1 v Hv)]. }
    have HbA_M2 : assertion_exists_binders r.(inv_body) ##
      (dom (inv_arg_map r vs : gmap lvar LExpr) ∪ lexpr_map_fvars (inv_arg_map r vs)).
    { apply reserved_disjoint_dom.
      - exact (Hwf.(pwf_inv_binders_reserved) inv' r Hr).
      - intros v Hv. apply elem_of_union in Hv as [Hv|Hv]; [exact (proj1 Hmr2 v Hv) | exact (proj2 Hmr2 v Hv)]. }
    (* Step 1: replace the symbolic arguments by the values they denote. *)
    have Hbase1 : ∀ x, x ∈ dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) →
        eval_lvar (list_to_map (zip r.(inv_args) lexprs)) mp x =
        eval_lvar (inv_arg_map r vs) mp x.
    { intros x _. rewrite /inv_arg_map /eval_lvar.
      clear Hdom1 Hdom2 HdomEq Hfv Hfv2 Hval_eval Hnofv Hlen Hlenvs
        Hlexprs_ok Hmr1 Hmr2 HbA_M1 HbA_M2.
      revert lexprs vs HF2. generalize r.(inv_args) as ks. intros ks.
      induction ks as [| k ks IH]; intros lexprs vs HF2; [done |].
      inversion HF2 as [| le v lexprs' vs' Hle HF2' Heq1 Heq2]; subst; simpl; [done |].
      destruct (decide (x = k)) as [-> | Hne].
      - rewrite !lookup_insert. by rewrite Hle.
      - rewrite !lookup_insert_ne; [| congruence | congruence]. by apply IH. }
    have Hbase1' : ∀ x, x ∈ dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) ∨ is_reserved x →
        eval_lvar (list_to_map (zip r.(inv_args) lexprs)) mp x =
        eval_lvar (inv_arg_map r vs) mp x.
    { intros x [Hx | Hx]; [exact (Hbase1 x Hx) |].
      unfold eval_lvar.
      have Hn1 : (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) !! x = None.
      { apply not_elem_of_dom. intros Hin. exact (proj1 Hmr1 x Hin Hx). }
      have Hn2 : (inv_arg_map r vs : gmap lvar LExpr) !! x = None.
      { apply not_elem_of_dom. intros Hin. exact (proj1 Hmr2 x Hin Hx). }
      rewrite Hn1 Hn2. reflexivity. }
    have Hstab1 : ∀ (q1 q2 : symb_map),
        (∀ x, x ∈ dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) →
              eval_lvar (list_to_map (zip r.(inv_args) lexprs)) q1 x =
              eval_lvar (inv_arg_map r vs) q2 x) →
        ∀ v, v ∉ lexpr_map_fvars (list_to_map (zip r.(inv_args) lexprs)) →
             v ∉ lexpr_map_fvars (inv_arg_map r vs) →
        ∀ v' x, x ∈ dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) →
        eval_lvar (list_to_map (zip r.(inv_args) lexprs))
          (fun y => if (y =? v)%string then v' else q1 y) x =
        eval_lvar (inv_arg_map r vs)
          (fun y => if (y =? v)%string then v' else q2 y) x.
    { intros q1 q2 Hag v Hv1 Hv2 v' x Hx.
      rewrite (eval_lvar_update_stable _ q1 v v' x Hv1 (or_introl Hx)).
      rewrite (Hag x Hx).
      have Hx2 : x ∈ dom (inv_arg_map r vs : gmap lvar LExpr) by rewrite <- HdomEq.
      exact (eq_sym (eval_lvar_update_stable _ q2 v v' x Hv2 (or_introl Hx2))). }
    etrans.
    { apply (trnsl_assertion_subst_congr Hwf r.(inv_body)
               (list_to_map (zip r.(inv_args) lexprs)) (inv_arg_map r vs) stk mp mp Hsf
               HbA_M1 HbA_M2 Hfv HdomEq Hmr1 Hmr2 Hstab1 Hbase1'). }
    (* Step 2: the body is StackFree, so the stack is immaterial. *)
    etrans.
    { apply stack_free_assertion_trnsl with (stk_id' := WINV_STK).
      exact (stack_free_assertion_subst Hwf _ _ (proj1 Hmr2) Hsf). }
    (* Step 3: the instantiated body is closed, so the symbolic map is too.
       trnsl_assertion_subst_congr's Hbase (agreement at reserved names too)
       is unsatisfiable here -- mp is an arbitrary caller-supplied map and
       WINV_MP a fixed global constant, genuinely unrelated at any name
       neither map's domain covers. trnsl_assertion_mp_irrelevant_reserved
       is the right tool instead: it only needs agreement where inv_body's
       *scope-correct* fvars (assertion_true_fvars, via pwf_inv_fvars_closed)
       actually land, which is exactly dom (inv_arg_map r vs) -- Hval_eval's
       own domain. See local/binders.md's "Blocked" section. *)
    have Htrue_dom : assertion_true_fvars r.(inv_body) ⊆ dom (inv_arg_map r vs : gmap lvar LExpr).
    { rewrite Hdom2. exact (Hwf.(pwf_inv_fvars_closed) inv' r Hr). }
    apply (trnsl_assertion_mp_irrelevant_reserved Hwf r.(inv_body)
             (inv_arg_map r vs) WINV_STK mp WINV_MP Hsf HbA_M2 Hmr2).
    intros x Hx. exact (Hval_eval mp x (Htrue_dom x Hx)).
  Qed.

  Lemma inv_body_at_eq (inv' : inv_name) (r : InvRecord) (vs : list val) :
    inv_map !! inv' = Some r →
    length vs = length r.(inv_args) →
    inv_body_at inv' vs =
    trnsl_assertion (subst r.(inv_body) (inv_arg_map r vs)) WINV_STK WINV_MP.
  Proof. intros Hr Hlen. rewrite /inv_body_at Hr decide_True //. Qed.

  (* Owning a fragment means the argument vector really was established. *)
  Lemma Winv_frag_mem (inv' : inv_name) (Iset : gset (list val)) (vs : list val) :
    own (invtoken_names inv') (● (Iset : inv_argsUR)) -∗
    own (invtoken_names inv') (◯ ({[vs]} : inv_argsUR)) -∗
    ⌜vs ∈ Iset⌝.
  Proof using G invTokenG0.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hval.
    apply auth_both_valid_discrete in Hval as [Hincl _].
    apply gset_included in Hincl. iPureIntro. set_solver.
  Qed.

  (* Opening an invariant: no later, no later credit.  The whole point of the
     nominal encoding is that this is available in plain Iris. *)
  Lemma Winv_open (Hwf : ProgramWF) (E : coPset) (inv' : inv_name)
      (r : InvRecord) (vs : list val) :
    inv_map !! inv' = Some r →
    length vs = length r.(inv_args) →
    ↑(inv_namespace_map inv') ⊆ E →
    inv (inv_namespace_map inv') (Winv inv') -∗
    own (invtoken_names inv') (◯ ({[vs]} : inv_argsUR)) ={E, E ∖ ↑(inv_namespace_map inv')}=∗
      trnsl_assertion (subst r.(inv_body) (inv_arg_map r vs)) WINV_STK WINV_MP ∗
      (trnsl_assertion (subst r.(inv_body) (inv_arg_map r vs)) WINV_STK WINV_MP
         ={E ∖ ↑(inv_namespace_map inv'), E}=∗ True).
  Proof.
    intros Hr Hlen HE.
    have Htl : Timeless (Winv inv') := Winv_timeless Hwf inv'.
    iIntros "#Hinv Hfrag".
    iMod (inv_acc_timeless with "Hinv") as "[HW Hclose]"; [exact HE |].
    iDestruct "HW" as (Iset) "[Hauth Hbig]".
    iDestruct (Winv_frag_mem with "Hauth Hfrag") as %Hmem.
    rewrite (big_sepS_delete _ Iset vs Hmem).
    iDestruct "Hbig" as "[Hbody Hrest]".
    rewrite (inv_body_at_eq inv' r vs Hr Hlen).
    iModIntro. iFrame "Hbody".
    iIntros "Hbody". iApply "Hclose".
    iExists Iset. iFrame "Hauth".
    rewrite (big_sepS_delete _ Iset vs Hmem) (inv_body_at_eq inv' r vs Hr Hlen).
    iFrame.
  Qed.

  (* Establishing an invariant: give up the body, get the nominal fragment.
     There is no inverse -- invariants are permanent, as in Iris. *)
  Lemma Winv_alloc (Hwf : ProgramWF) (E : coPset) (inv' : inv_name)
      (r : InvRecord) (vs : list val) :
    inv_map !! inv' = Some r →
    length vs = length r.(inv_args) →
    ↑(inv_namespace_map inv') ⊆ E →
    inv (inv_namespace_map inv') (Winv inv') -∗
    trnsl_assertion (subst r.(inv_body) (inv_arg_map r vs)) WINV_STK WINV_MP
    ={E}=∗ own (invtoken_names inv') (◯ ({[vs]} : inv_argsUR)).
  Proof.
    intros Hr Hlen HE.
    have Htl : Timeless (Winv inv') := Winv_timeless Hwf inv'.
    iIntros "#Hinv Hbody".
    iMod (inv_acc_timeless with "Hinv") as "[HW Hclose]"; [exact HE |].
    iDestruct "HW" as (Iset) "[Hauth Hbig]".
    iMod (own_update _ _ (● ((Iset ∪ {[vs]}) : inv_argsUR) ⋅ ◯ ({[vs]} : inv_argsUR))
      with "Hauth") as "[Hauth Hfrag]".
    { etrans.
      - apply (auth_update_auth (Iset : inv_argsUR) (Iset ∪ {[vs]}) (Iset ∪ {[vs]})).
        apply gset_local_update. set_solver.
      - apply auth_update_dfrac_alloc; [apply _ |].
        apply gset_included. set_solver. }
    iAssert (Winv inv') with "[Hauth Hbig Hbody]" as "HW".
    { iExists (Iset ∪ {[vs]}). iFrame "Hauth".
      destruct (decide (vs ∈ Iset)) as [Hin | Hnin].
      - have Heq : Iset ∪ {[vs]} = Iset by set_solver.
        rewrite Heq. iFrame "Hbig".
      - rewrite big_sepS_union; [| set_solver].
        iFrame "Hbig". rewrite big_sepS_singleton (inv_body_at_eq inv' r vs Hr Hlen).
        iExact "Hbody". }
    iMod ("Hclose" with "HW") as "_". iModIntro. iExact "Hfrag".
  Qed.

End InvariantWorld.

(* The ghost heap: one standing authoritative (loc,fld) -> gname naming
   map. HeapAllocRule mints a genuinely fresh gname (own_alloc, no chosen
   name needed) for each ghost field it allocates and grows this map to
   record the binding; FPURule never touches this map at all, since RA
   ownership lives directly at that gname via a bare own, exactly as in
   the pre-existing ghost_map design (see the comment on LGhostOwn's own
   translation above for why: updating a map fragment in place would need
   a genuine local update accounting for whatever else is framed at that
   key, which a bare RA-level ~~> doesn't in general provide -- the map's
   only job is solving the freshness/naming problem). Mirrors Winv's own
   invariant-wrapped, growable-via-iInv pattern above. *)
Section GhostHeapWorld.

  Definition Wghost : iProp Σ :=
    (∃ M : gmap heap_addr gname,
       own ghost_heap_name (● (to_agree <$> M) : authR (gmapUR heap_addr (agreeR gnameO))) ∗
       [∗ set] a ∈ dom M, ghost_dom_frag {[a]})%I.

  Global Instance Wghost_timeless : Timeless Wghost.
  Proof. rewrite /Wghost. apply _. Qed.

  (* Two reservations of the same (loc, fld) key can't coexist: ghost_dom's
     value type is exclR unitO, so the map fragment is exclusive at each
     key, exactly like heap_cellR's full fraction is for the real heap. *)
  Lemma ghost_dom_frag_excl (a : heap_addr) :
    ghost_dom_frag {[a]} -∗ ghost_dom_frag {[a]} -∗ False.
  Proof.
    rewrite /ghost_dom_frag.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hval.
    apply auth_frag_valid_1 in Hval.
    rewrite gset_to_gmap_singleton singleton_op singleton_valid in Hval.
    done.
  Qed.

  Lemma transport_cmra_valid {A B : cmra} (p : A = B) (x : cmra_car A) :
    ✓ x → ✓ (transport (f_equal cmra_car p) x).
  Proof. destruct p. simpl. done. Qed.

  (* Establishing a fresh ghost cell: own_alloc a genuinely fresh gname γ
     holding the initial RA chunk directly (exactly as the original
     ghost_map design would have owned it), then, given the ghost_dom_frag
     reservation wp_alloc just produced for (l, fld) (grown in lockstep
     with the real heap, at the same fresh_loc, so it's guaranteed fresh
     -- see ghost_dom_alloc_valid_sets), open Wghost, rule out (l, fld)
     already being in its domain via ghost_dom_frag_excl, and record the
     (l,fld) -> γ binding, handing the caller back both pieces in exactly
     the shape LGhostOwn's own translation expects. *)
  Lemma Wghost_alloc (E : coPset) (r : ra_name) (l : loc) (fld : fld_name)
      (chunk : RA_carrier (ra_map r)) (Hchunk_valid : (RA_inst (ra_map r)).(valid) chunk)
      (w : Γ_witness r) (HΓeq : Γ r = Γ_found w) :
    let '(existT i (exist _ U (conj Hdis (exist _ Heq_car (conj Heq_cmra (conj Hop Hvalid)))))) := w in
    ↑ghost_heap_namespace ⊆ E →
    inv ghost_heap_namespace Wghost -∗
    ghost_dom_frag {[heap_addr_constr l fld]}
    ={E}=∗
    ∃ γ : gname,
      own ghost_heap_name (◯ {[ heap_addr_constr l fld := to_agree γ ]} : authR (gmapUR heap_addr (agreeR gnameO))) ∗
      own γ (transport (f_equal cmra_car Heq_cmra) (transport Heq_car chunk)) (inG0 := inGs_inG i).
  Proof.
    destruct w as [i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]].
    intros HE.
    iIntros "#Hinv Hwit".
    iMod (own_alloc (transport (f_equal cmra_car Heq_cmra) (transport Heq_car chunk))) as (γ) "Hγ".
    { apply transport_cmra_valid.
      change (@cmra.valid (cmra_car (ucmra_cmraR U)) (cmra_valid (ucmra_cmraR U))) with (ucmra_valid U).
      rewrite Hvalid.
      apply eq_rect_transport_valid_inv. exact Hchunk_valid. }
    iMod (inv_acc_timeless with "Hinv") as "[HW Hclose]"; [exact HE |].
    iEval (rewrite /Wghost) in "HW".
    iDestruct "HW" as (M) "[Hauth Hbig]".
    destruct (decide (heap_addr_constr l fld ∈ dom M)) as [Hin | Hnin].
    - iDestruct (big_sepS_elem_of _ _ (heap_addr_constr l fld) Hin with "Hbig") as "Hwit'".
      iDestruct (ghost_dom_frag_excl with "Hwit Hwit'") as "[]".
    - have Hfresh : M !! (heap_addr_constr l fld) = None := not_elem_of_dom_1 _ _ Hnin.
      iMod (own_update _ _
        ((● (to_agree <$> (<[ heap_addr_constr l fld := γ ]> M))
          ⋅ ◯ {[ heap_addr_constr l fld := to_agree γ ]})
         : authR (gmapUR heap_addr (agreeR gnameO)))
        with "Hauth") as "[Hauth Hfrag]".
      { rewrite fmap_insert. apply auth_update_alloc.
        apply alloc_singleton_local_update; [| done].
        rewrite lookup_fmap Hfresh. done. }
      iAssert Wghost with "[Hauth Hbig Hwit]" as "HW".
      { iEval (rewrite /Wghost).
        iExists (<[heap_addr_constr l fld := γ]> M).
        iFrame "Hauth".
        rewrite dom_insert_L.
        rewrite big_sepS_union; [| apply disjoint_singleton_l; exact Hnin].
        iFrame "Hbig". rewrite big_sepS_singleton. iExact "Hwit". }
      iMod ("Hclose" with "HW") as "_". iModIntro. iExists γ. iFrame.
  Qed.

End GhostHeapWorld.

Lemma transport_cmra_update {A B} (p : A = B) (x y : (cmra_car A)) :
  x ~~> y → transport (f_equal cmra_car p) x ~~> transport (f_equal cmra_car p) y.
Proof.
  intros Hxy. subst. done.
Qed.

End WithProgram.
