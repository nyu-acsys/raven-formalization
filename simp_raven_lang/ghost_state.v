From stdpp Require Import coPset gmap.
From Coq Require Import QArith Qcanon.
From iris.algebra Require Import ofe cmra.
From iris.algebra Require Import big_op gmap frac agree.
From iris.algebra Require Import csum excl auth cmra_big_op numbers.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Export tactics.
From raven_iris.simp_raven_lang Require Export lang.

From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.

Set Default Proof Using "Type".
Import uPred.

Inductive stackvar_addr :=
| mk_stkvar_addr (stk_id : stack_id) (v : var).

Global Instance stackvar_addr_eq : EqDecision stackvar_addr.
Proof. solve_decision. Qed.

Global Instance stackvar_addr_countable : Countable stackvar_addr.
Proof.
  refine (inj_countable'
    (λ a, match a with mk_stkvar_addr s v => (s, v) end)
    (λ '(s, v), mk_stkvar_addr s v) _).
  intros [s v]. done.
Qed.


Definition heap_cellR : cmra :=
  prodR fracR (agreeR valO).

Definition heapUR : ucmra :=
  gmapUR heap_addr heap_cellR.

Definition stackUR :=
  gmapUR stack_id (exclR stack_frame).

(* Purely a freshness-tracking resource for rich_raven_lang's ghost heap
   (see Wghost in rrl_lang.v): grown by wp_alloc in lockstep with the real
   heap, at the very same fresh_loc, so that rrl_lang.v's own standing
   ghost-naming invariant can prove a freshly-allocated location's ghost
   keys were never claimed before -- via plain exclusivity here -- without
   needing to know anything about RAs, Γ, or ghost values at all (those
   stay entirely at the rich_raven_lang layer). *)
Definition ghost_domUR : ucmra :=
  gmapUR heap_addr (exclR unitO).

(* Layer 0 (see local/parameters-redesign.md): the camera capabilities
   [heapG] needs, without the concrete gnames -- mirrors iris_heap_lang's
   own heapGpreS/heapGS split. [heapG] itself bundles gnames together with
   the inG evidence (unlike the standard pre/GS split), so a [heapG]
   instance can't be derived from [subG] alone; only this "pre" half can.
   Producing concrete gnames from [heapGpreS] is [own_alloc] work that
   belongs to the adequacy wrapper (Step 5), not here. *)
Class heapGpreS Σ := HeapGpreS {
  heapGpreS_heap_inG :: inG Σ (authR heapUR);
  heapGpreS_stack_inG :: inG Σ (authR stackUR);
  heapGpreS_proctbl_inG :: ghost_mapG Σ proc_name proc;
  heapGpreS_ghostdom_inG :: inG Σ (authR ghost_domUR);
}.

Definition heapGΣ : gFunctors :=
  #[ GFunctor (authR heapUR); GFunctor (authR stackUR);
     ghost_mapΣ proc_name proc; GFunctor (authR ghost_domUR) ].

Global Instance subG_heapGpreS Σ : subG heapGΣ Σ → heapGpreS Σ.
Proof. solve_inG. Qed.

Class heapG Σ := HeapG {
  heap_heap_inG :: inG Σ (authR heapUR);
  heap_heap_name : gname;
  heap_stack_inG :: inG Σ (authR stackUR);
  heap_stack_name : gname;
  heap_proctbl_inG :: ghost_mapG Σ proc_name proc;
  heap_proctbl_name : gname;
  heap_ghostdom_inG :: inG Σ (authR ghost_domUR);
  heap_ghostdom_name : gname;
}.

Definition state_wf (σ : state) : Prop :=
  (0 ≤ σ.(max_stack_id))%Z ∧
  (∀ k v, σ.(stack) !! k = Some v → (k ≤ σ.(max_stack_id))%Z) ∧
  (∀ l f v, σ.(global_heap) !! heap_addr_constr l f = Some v →
            (l.(loc_car) < Z.of_nat (size σ.(global_heap)))%Z) ∧
  (* "#ret_val" is present, with some value, in every stack frame: every call/spawn
     step pre-populates it (see RTCallStep/SpawnStep in lang.v), and no step ever
     removes a key from a frame's locals map, so this is preserved throughout. *)
  (∀ k frm, σ.(stack) !! k = Some frm → is_Some (frm.(locals) !! "#ret_val")).

Definition swf_max_stk_non_neg {σ} (Hwf : state_wf σ) : (0 ≤ σ.(max_stack_id))%Z :=
  proj1 Hwf.
Definition swf_stk_bounded {σ} (Hwf : state_wf σ)
    : ∀ k v, σ.(stack) !! k = Some v → (k ≤ σ.(max_stack_id))%Z :=
  proj1 (proj2 Hwf).
Definition swf_heap_bounded {σ} (Hwf : state_wf σ)
    : ∀ l f v, σ.(global_heap) !! heap_addr_constr l f = Some v →
               (l.(loc_car) < Z.of_nat (size σ.(global_heap)))%Z :=
  proj1 (proj2 (proj2 Hwf)).
Definition swf_ret_val_bound {σ} (Hwf : state_wf σ)
    : ∀ k frm, σ.(stack) !! k = Some frm → is_Some (frm.(locals) !! "#ret_val") :=
  proj2 (proj2 (proj2 Hwf)).

Definition mk_state_wf σ
    (Hnn : (0 ≤ σ.(max_stack_id))%Z)
    (Hbnd : ∀ k v, σ.(stack) !! k = Some v → (k ≤ σ.(max_stack_id))%Z)
    (Hhb : ∀ l f v, σ.(global_heap) !! heap_addr_constr l f = Some v →
                    (l.(loc_car) < Z.of_nat (size σ.(global_heap)))%Z)
    (Hrv : ∀ k frm, σ.(stack) !! k = Some frm → is_Some (frm.(locals) !! "#ret_val")) :
    state_wf σ := conj Hnn (conj Hbnd (conj Hhb Hrv)).

Lemma fresh_loc_is_fresh (h : heap) (fld : fld_name)
    (Hwf : ∀ l f v, h !! heap_addr_constr l f = Some v → (l.(loc_car) < Z.of_nat (size h))%Z) :
    h !! heap_addr_constr (fresh_loc h) fld = None.
Proof.
  destruct (h !! heap_addr_constr (fresh_loc h) fld) eqn:Habs; [| done].
  exfalso. have := Hwf (fresh_loc h) fld v Habs. unfold fresh_loc. simpl. lia.
Qed.

Lemma max_stk_id_fresh (σ : state) (Hwf : state_wf σ) :
    σ.(stack) !! Z.of_nat (Z.to_nat σ.(max_stack_id) + 1) = None.
Proof.
  destruct (σ.(stack) !! Z.of_nat (Z.to_nat σ.(max_stack_id) + 1)) eqn:Habs; [| done].
  exfalso.
  have Hbnd := swf_stk_bounded Hwf _ _ Habs.
  have Hnn := swf_max_stk_non_neg Hwf.
  lia.
Qed.

Section definitions.
  Context `{!heapG Σ}.

  Definition to_heap_cellR (v: val) : heap_cellR := (1%Qp, to_agree v).
  
  Global Instance heap_addr_finmap : FinMap heap_addr (gmap heap_addr).
  Proof. apply gmap_finmap. Qed.


  Definition to_heapUR (h : heap) : heapUR :=
  fmap (λ v, (to_heap_cellR v)) h.

  Definition heap_interp (h : heap) : iProp Σ :=
  own heap_heap_name (● (to_heapUR h)).

  Definition proc_tbl_interp (proc_tbl : gmap proc_name proc) : iProp Σ :=
    ghost_map_auth heap_proctbl_name 1 proc_tbl. 

  Definition to_stackR (s : gmap stack_id stack_frame) : stackUR :=
    fmap (λ frm, Excl frm) s.

  Definition stack_interp (stack : gmap stack_id stack_frame) : iProp Σ :=
    own heap_stack_name (● (to_stackR stack)).

  Definition ghost_dom_interp (D : gset heap_addr) : iProp Σ :=
    own heap_ghostdom_name (● (gset_to_gmap (Excl ()) D : ghost_domUR)).

  Definition ghost_dom_frag (D : gset heap_addr) : iProp Σ :=
    own heap_ghostdom_name (◯ (gset_to_gmap (Excl ()) D : ghost_domUR)).

  (* Splits a reservation fragment for a freshly-grown key off the rest,
     mirroring how a batch-allocated heap fragment splits into per-field
     pieces (see wp_alloc's own induction over fs). *)
  Lemma ghost_dom_frag_insert (a : heap_addr) (D : gset heap_addr) (Hnotin : a ∉ D) :
    ghost_dom_frag ({[a]} ∪ D) ⊣⊢ ghost_dom_frag {[a]} ∗ ghost_dom_frag D.
  Proof.
    rewrite /ghost_dom_frag.
    rewrite gset_to_gmap_union_singleton.
    rewrite -own_op -auth_frag_op.
    have Hnone : gset_to_gmap (Excl ()) D !! a = None.
    { rewrite lookup_gset_to_gmap_None. exact Hnotin. }
    rewrite (insert_singleton_op (gset_to_gmap (Excl ()) D) a (Excl ()) Hnone).
    rewrite gset_to_gmap_singleton.
    reflexivity.
  Qed.

  Definition state_interp (σ : state) : iProp Σ :=
  heap_interp σ.(global_heap) ∗ proc_tbl_interp σ.(procs) ∗ stack_interp σ.(stack) ∗
  (∃ D : gset heap_addr, ghost_dom_interp D ∗
     ⌜∀ a, a ∈ D → ((heap_addr_loc a).(loc_car) < Z.of_nat (size σ.(global_heap)))%Z⌝) ∗
  ⌜state_wf σ⌝.


  Definition heap_maps_to (l : loc) (fld : fld_name) (q : Qp) (v : val) :=
    own heap_heap_name (◯ {[(heap_addr_constr l fld) := (q, to_agree v)]}).

  Definition stack_frame_own (stk_id : stack_id) (stk_frm : stack_frame)  := 
    own heap_stack_name (◯ (to_stackR ({[stk_id := stk_frm]} ))).

  (* Persistent (discarded-fraction) read-only fragment, not the default
     full-ownership points-to: the proc table is a static, never-changing
     part of the program (no rule ever allocates/updates a proc_tbl_chunk),
     and a recursive call needs to keep re-supplying wp_call's own
     proc_tbl_chunk precondition arbitrarily many times, which only a
     duplicable fact can do. *)
  Definition proc_tbl_chunk (p : proc_name) (proc : proc) : iProp Σ :=
    p ↪[heap_proctbl_name]□ proc.

  Global Instance proc_tbl_chunk_persistent p proc : Persistent (proc_tbl_chunk p proc).
  Proof. apply _. Qed.

  Lemma heap_update σ l f x v0:
    (● ((λ v1 : lang.val, to_heap_cellR v1) <$> global_heap σ)
    ⋅ ◯ {[heap_addr_constr l f := (1%Qp, to_agree x)]}) ~~>

    (● ((λ v1 : lang.val, to_heap_cellR v1) <$> <[heap_addr_constr l f:=v0]> (global_heap σ))
    ⋅ ◯ {[heap_addr_constr l f := (1%Qp, to_agree v0)]}).
  Proof.
    apply auth_update.
    rewrite fmap_insert.
    apply singleton_local_update_any.
    intros x_auth _.
    apply exclusive_local_update.
    done.
  Qed.


  
  Lemma stack_interp_agreement σ stk_id stk_frm : (stack_interp (stack σ)) -∗ stack_frame_own stk_id stk_frm -∗ ⌜stack σ !! stk_id = Some stk_frm⌝.
  Proof. 
    iIntros "Hstack Hstk".
    unfold stack_interp.
    unfold stack_frame_own.
    iCombine "Hstack" "Hstk" as "HstackV".
    iPoseProof (own_valid with "HstackV") as "%Hi".
    apply auth_both_valid_discrete in Hi.
    destruct Hi as [Hi1 Hi2].
    rewrite -> (gmap.lookup_included (to_stackR {[stk_id := stk_frm]}) (to_stackR (stack σ))) in Hi1.
    specialize (Hi1 stk_id).
    iPureIntro.

    rewrite !lookup_fmap in Hi1. cbn in Hi1. rewrite lookup_insert in Hi1. cbn in Hi1.
    destruct (stack σ !! stk_id); try done.
    -  cbn in Hi1. rewrite Excl_included in Hi1. 
    apply leibniz_equiv in Hi1. by subst s.

    - cbn in Hi1. exfalso. rewrite option_included in Hi1.
    destruct Hi1; try done.
    destruct H as [a [b [H1 [H2 H3]]]]. try done.
  Qed.

  Lemma heap_interp_agreement σ l f q v:
  (heap_interp (global_heap σ)) -∗ (heap_maps_to l f q v) -∗ ⌜lookup_heap σ l f = Some v⌝.
  Proof.
    iIntros "Hheap Hhp".
    unfold heap_interp.
    unfold heap_maps_to.
    iCombine "Hheap" "Hhp" as "HhpV".
    iPoseProof (own_valid with "HhpV") as "%Hi".
    apply auth_both_valid_discrete in Hi.
    destruct Hi as [Hi1 Hi2].

    rewrite (gmap.lookup_included ({[heap_addr_constr l f := (q, to_agree v)]})) in Hi1.
    specialize (Hi1 (heap_addr_constr l f)).
    iPureIntro.
    unfold to_heapUR in Hi1.

    rewrite lookup_insert in Hi1.
    rewrite lookup_fmap in Hi1.
    unfold lookup_heap.

    apply Some_included_is_Some in Hi1 as H3.
    (* Had to destruct a verbose version to mitigate strange Coq errors. *)
    destruct ((@lookup heap_addr val
      (@gmap heap_addr heap_addr_eq heap_addr_countable val)
      (@gmap_lookup heap_addr heap_addr_eq heap_addr_countable val)
      (heap_addr_constr l f) (global_heap σ))) eqn:Hlp; try done.

    2 : { simpl in *. destruct H3 as [x Hx]. simpl in Hx. discriminate. }
    
    rewrite Hlp.  
    simpl in *.
    apply Some_pair_included in Hi1 as [_ Heq].

    rewrite Some_included_total in Heq.
    rewrite to_agree_included in Heq.
    apply f_equal.
    simpl in *.
    setoid_subst. done.
  Qed.

  Lemma proc_tbl_interp_agreement σ proc proc_entry:
  (proc_tbl_interp (procs σ)) -∗ (proc_tbl_chunk proc proc_entry) -∗
    ⌜σ.(procs) !! proc = Some proc_entry⌝.
  Proof.
    iIntros "Hauth Hchunk".
    iApply (ghost_map_lookup with "Hauth Hchunk").
  Qed.

End definitions.

Notation " l # f  ↦{ q } v" := (heap_maps_to l f q v)
(at level 20) : bi_scope.

Notation "'stack_own[' stk_id , frm ']' " := (stack_frame_own stk_id frm)
(at level 20) : bi_scope.

Section updates.
    Context `{!heapG Σ}.
  Lemma stack_upd_valid σ stk_id stk_frm v val
      (Hlookup : stack σ !! stk_id = Some stk_frm) :
    ● to_stackR (stack σ) ⋅ ◯ to_stackR {[stk_id := stk_frm]} ~~>
    ● to_stackR (stack (update_lvar σ v stk_id val))
    ⋅ ◯ to_stackR {[stk_id := {| locals := <[v:=val]> (locals stk_frm) |}]}.
  Proof.
    unfold update_lvar. rewrite Hlookup. simpl.
    apply auth_update.
    unfold to_stackR. rewrite fmap_insert. rewrite !map_fmap_singleton.
    apply (singleton_local_update _ stk_id (Excl stk_frm)).
    - rewrite lookup_fmap. rewrite Hlookup. done.
    - apply exclusive_local_update. done.
  Qed.

  Lemma stack_lvar_upd σ stk_id stk_frm x v :
    stack_own[ stk_id, stk_frm ] ∗ stack_interp (stack σ) ==∗
    stack_own[stk_id, StackFrame (<[x := v]> stk_frm.(locals)) ] ∗ stack_interp (stack (update_lvar σ x stk_id v)).
  Proof.
    iIntros "[Hstk Hstack]".
    iDestruct (stack_interp_agreement with "Hstack Hstk") as %Hlookup.
    iCombine "Hstack" "Hstk" as "Hcomb".
    iPoseProof (own_update heap_stack_name
        (● to_stackR (stack σ) ⋅ ◯ to_stackR {[stk_id := stk_frm]})
        (● to_stackR (stack (update_lvar σ x stk_id v)) ⋅ ◯ to_stackR {[stk_id := {| locals := <[x:=v]> (locals stk_frm) |}]})
        with "Hcomb"
    ) as "Hcomb2".
    { apply (stack_upd_valid _ _ _ _ _ Hlookup). }
    iDestruct "Hcomb2" as ">[Hstack Hstk]".
    iModIntro. iFrame.
  Qed.

  (* Helper: raw CMRA update for stack allocation.
     Factored out into a standalone lemma so that `stk_map` is a plain
     gmap variable, avoiding the `σ.(stack)` vs `stack σ` syntactic
     mismatch that arises when `update_stack` is unfolded inside a ~l~> goal.
     The main Iris lemma below applies this via `exact`, which uses
     definitional equality to handle `stack (update_stack σ …) ≡ <[…]> (stack σ)`. *)
  Lemma stack_alloc_cmra_upd (stk_map : gmap stack_id stack_frame) stk_id stk_frm
      (Hfresh : stk_map !! stk_id = None) :
    ● to_stackR stk_map ~~>
    ● to_stackR (<[stk_id := stk_frm]> stk_map) ⋅ ◯ to_stackR {[stk_id := stk_frm]}.
  Proof.
    apply auth_update_alloc.
    unfold to_stackR.
    rewrite fmap_insert.         (* Excl <$> <[k:=v]> m = <[k:=Excl v]> (Excl <$> m) *)
    rewrite map_fmap_singleton.  (* Excl <$> {[k:=v]} = {[k:=Excl v]} *)
    apply alloc_singleton_local_update.
    - rewrite lookup_fmap. rewrite Hfresh. done.
    - done.
  Qed.

  (* Hfresh is the "inductive property" the caller must maintain: the id
     chosen by fresh_stk_id (= Z.of_nat (Z.to_nat σ.(max_stack_id) + 1))
     must not be already allocated.  We express it with Z.of_nat so the
     key type is stack_id = Z (no Lookup-nat issues). *)
  Lemma stack_new_stk_frm_upd σ stk_frm'
      (Hfresh : stack σ !! (Z.of_nat (Z.to_nat σ.(max_stack_id) + 1)) = None) :
    stack_interp (stack σ) ==∗
    stack_interp (update_stack σ (Z.to_nat σ.(max_stack_id) + 1) stk_frm').(stack) ∗
    stack_own[Z.to_nat σ.(max_stack_id) + 1, stk_frm'].
  Proof.
    iIntros "Hstack".
    unfold stack_interp, stack_frame_own.
    iMod (own_update with "Hstack") as "[Hnew Hown]".
    { exact (stack_alloc_cmra_upd (stack σ)
               (Z.of_nat (Z.to_nat σ.(max_stack_id) + 1)) stk_frm' Hfresh). }
    iModIntro. iFrame.
  Qed.

  Lemma heap_upd_valid σ l fld v v':
    ● to_heapUR (global_heap σ) ⋅ ◯ {[heap_addr_constr l fld := (1%Qp, to_agree v)]} ~~>
    ● to_heapUR (global_heap (update_heap σ l fld v')) ⋅ ◯ {[heap_addr_constr l fld := (1%Qp, to_agree v')]}.
  Proof.
    unfold to_heapUR, update_heap. simpl.
    apply heap_update.
  Qed.


  Lemma heap_l_upd σ l fld v v' : 
    l#fld ↦{1%Qp } v ∗ heap_interp (global_heap σ) ==∗
    l#fld ↦{1%Qp } v' ∗ heap_interp (global_heap (update_heap σ l fld v')).
  Proof.
    iIntros "[Hl Hhp]".
    iCombine "Hhp" "Hl" as "Hcomb".
    iPoseProof (own_update heap_heap_name
      (● to_heapUR (global_heap σ) ⋅ ◯ {[(heap_addr_constr l fld) := (1%Qp, to_agree v)]})
      (● to_heapUR (global_heap (update_heap σ l fld v')) ⋅ ◯ {[(heap_addr_constr l fld) := (1%Qp, to_agree v')]})
      with "Hcomb"
    ) as "Hcomb2".
    { apply heap_upd_valid. }
    iDestruct "Hcomb2" as ">[Hhp Hl]".
    iModIntro. iFrame.
  Qed.

  Lemma foldr_update_heap_not_mem (l : loc) (fld : fld_name) (fss : list (fld_name * val)) (σ : state) :
    fld ∉ fss.*1 →
    global_heap σ !! heap_addr_constr l fld = None →
    global_heap (foldr (λ f_v acc, update_heap acc l f_v.1 f_v.2) σ fss) !! heap_addr_constr l fld = None.
  Proof.
    intros H_NotIn H_Fresh.
    induction fss as [| f_v fss' IH].
    - simpl. exact H_Fresh.
    - simpl. unfold update_heap. simpl.
      destruct (decide (heap_addr_constr l f_v.1 = heap_addr_constr l fld)) as [Heq|Hne].
      { exfalso.
        have Hfld : f_v.1 = fld. { injection Heq as Hfld. exact Hfld. }
        apply H_NotIn. apply elem_of_cons. left. exact (eq_sym Hfld). }
      rewrite lookup_insert_ne; [| exact Hne].
      apply IH.
      intro Hin. apply H_NotIn. simpl. right. exact Hin.
  Qed.

  Lemma foldr_build_heap_not_mem (l : loc) (fld : fld_name) (fss : list (fld_name * val)) :
    fld ∉ fss.*1 →
    (foldr (λ f_v acc, <[heap_addr_constr l f_v.1 := f_v.2]> acc) (∅ : heap) fss) !! heap_addr_constr l fld = None.
  Proof.
    intros H_NotIn.
    induction fss as [| f_v fss' IH].
    - simpl. apply lookup_empty.
    - simpl. rewrite lookup_insert_ne.
      + apply IH. intro Hin. apply H_NotIn. simpl. right. exact Hin.
      + intro Heq.
        have Hfld : f_v.1 = fld. { injection Heq as Hfld. exact Hfld. }
        apply H_NotIn. apply elem_of_cons. left. exact (eq_sym Hfld).
  Qed.

  (* Grows the ghost-domain reservation set by one fresh key per name in
     gfs, all at the just-picked l -- mirrors heap_alloc_valid's own
     structure exactly, but keyed by field name alone (no value payload:
     this resource exists purely to let rrl_lang.v's Wghost invariant
     prove freshness, see the comment on ghost_domUR above). *)
  Lemma ghost_dom_alloc_valid :
    ∀ (gfs : list fld_name) (D : gset heap_addr) (l : loc) (h : heap),
    NoDup gfs →
    l = fresh_loc h →
    (∀ a, a ∈ D → ((heap_addr_loc a).(loc_car) < Z.of_nat (size h))%Z) →
    let D_map := gset_to_gmap (Excl ()) D in
    let D_map' := fold_right
        (λ fld acc, <[heap_addr_constr l fld := Excl ()]> acc)
      D_map gfs in
    let new_keys_map := fold_right
        (λ fld acc, <[heap_addr_constr l fld := Excl ()]> acc)
      (∅ : gmap heap_addr (exclR unitO)) gfs in
    ● (D_map : ghost_domUR) ~~> ● (D_map' : ghost_domUR) ⋅ ◯ (new_keys_map : ghost_domUR).
  Proof.
    induction gfs as [ | fld gfs' IH].

    - intros D l h HNoDup Hl HD D_map D_map' new_keys_map.
      simpl in D_map', new_keys_map. subst D_map' new_keys_map.
      apply auth_update_alloc.
      have Heq : ucmra_unit ghost_domUR = (∅ : gmap heap_addr (exclR unitO)). { done. }
      rewrite Heq. done.

    - intros D l h HNoDup Hl HD D_map D_map' new_keys_map. simpl in D_map', new_keys_map.
      inversion HNoDup as [| ? ? H_NotIn H_NoDup'].
      specialize (IH D l h H_NoDup' Hl HD).
      unfold D_map in IH.
      rewrite IH.
      unfold D_map', new_keys_map. unfold D_map.
      apply auth_update.
      apply alloc_local_update.
      { have Hfresh1 : gset_to_gmap (Excl ()) D !! heap_addr_constr l fld = None.
        { apply lookup_gset_to_gmap_None. intro Hin.
          have Hlt := HD _ Hin. simpl in Hlt. rewrite Hl in Hlt. unfold fresh_loc in Hlt.
          simpl in Hlt. lia. }
        have Hfresh2 : ∀ gfs0, fld ∉ gfs0 → (fold_right
            (λ fld' acc, <[heap_addr_constr l fld' := Excl ()]> acc)
          (gset_to_gmap (Excl ()) D) gfs0) !! heap_addr_constr l fld = None.
        { intro gfs0. induction gfs0 as [| fld' gfs'' IH2].
          - intros _. exact Hfresh1.
          - intros H_NotIn'. simpl. rewrite lookup_insert_ne.
            + apply IH2. intro Hin. apply H_NotIn'. apply elem_of_cons. right. exact Hin.
            + intro Heq. apply H_NotIn'. apply elem_of_cons. left. congruence. }
        apply Hfresh2. exact H_NotIn. }
      { done. }
  Qed.

  Lemma fold_insert_excl_gset_to_gmap (l : loc) (gfs : list fld_name) (D : gset heap_addr) :
    fold_right (λ fld acc, <[heap_addr_constr l fld := Excl ()]> acc) (gset_to_gmap (Excl ()) D) gfs
    = gset_to_gmap (Excl ()) (D ∪ list_to_set (map (heap_addr_constr l) gfs)).
  Proof.
    induction gfs as [| fld gfs' IH].
    - simpl. rewrite right_id_L. done.
    - simpl. rewrite IH.
      have Hseteq : D ∪ ({[heap_addr_constr l fld]} ∪ list_to_set (map (heap_addr_constr l) gfs'))
                  = {[heap_addr_constr l fld]} ∪ (D ∪ list_to_set (map (heap_addr_constr l) gfs')).
      { set_solver. }
      rewrite Hseteq.
      rewrite gset_to_gmap_union_singleton. done.
  Qed.

  (* Set-indexed restatement of ghost_dom_alloc_valid, for callers (wp_alloc)
     that want to talk about "the set of freshly-reserved ghost keys"
     directly rather than the fold_right-accumulated map. *)
  Lemma ghost_dom_alloc_valid_sets (gfs : list fld_name) (D : gset heap_addr) (l : loc) (h : heap) :
    NoDup gfs →
    l = fresh_loc h →
    (∀ a, a ∈ D → ((heap_addr_loc a).(loc_car) < Z.of_nat (size h))%Z) →
    let new_keys := list_to_set (map (heap_addr_constr l) gfs) : gset heap_addr in
    ● (gset_to_gmap (Excl ()) D : ghost_domUR) ~~>
    ● (gset_to_gmap (Excl ()) (D ∪ new_keys) : ghost_domUR) ⋅ ◯ (gset_to_gmap (Excl ()) new_keys : ghost_domUR).
  Proof.
    intros HNoDup Hl HD new_keys.
    have H := ghost_dom_alloc_valid gfs D l h HNoDup Hl HD.
    simpl in H.
    rewrite (fold_insert_excl_gset_to_gmap l gfs D) in H.
    rewrite <- (gset_to_gmap_empty (Excl ())) in H.
    rewrite (fold_insert_excl_gset_to_gmap l gfs ∅) in H.
    rewrite left_id_L in H.
    exact H.
  Qed.

  Lemma heap_alloc_valid :
    ∀ fs σ,
    NoDup fs.*1 →
    state_wf σ →
    let l := fresh_loc (global_heap σ) in
    let σ' := fold_right
        (λ f_v acc ,
          update_heap acc l f_v.1 f_v.2)
      σ fs  in
    let fs_heap_map := fold_right
        (λ f_v acc, <[heap_addr_constr l f_v.1:=f_v.2]> acc)
      ∅ fs in
    ● to_heapUR (global_heap σ) ~~> ● to_heapUR (global_heap σ') ⋅ ◯ to_heapUR fs_heap_map.
  Proof.
    induction fs as [ | fs fss IH].

    - intros σ HNoDup Hwf l σ' fs_heap_map. simpl in fs_heap_map. subst fs_heap_map.
      simpl in σ'. subst σ'. unfold to_heapUR. rewrite fmap_empty. apply auth_update_alloc.
      have Heq : ucmra_unit heapUR = (∅ : gmapUR heap_addr heap_cellR). { done. }
      rewrite Heq. done.

    - intros σ HNoDup Hwf l σ' fs_heap_map. simpl in fs_heap_map.
      simpl in σ'.
      inversion HNoDup as [| ? ? H_NotIn H_NoDup'].
      specialize (IH σ H_NoDup' Hwf).
      unfold l in IH.
      rewrite IH.
      unfold σ', fs_heap_map. unfold update_heap. simpl.
      apply auth_update.
      unfold to_heapUR at 3 4.
      rewrite fmap_insert. rewrite fmap_insert.
      apply alloc_local_update.
      { rewrite lookup_fmap.
        rewrite (foldr_update_heap_not_mem l fs.1 fss σ H_NotIn
                   (fresh_loc_is_fresh _ _ (swf_heap_bounded Hwf))).
        done. }
      { unfold to_heap_cellR. apply pair_valid. done. }
  Qed.

  Lemma heap_size_insert_le (m : heap) k v :
      size m ≤ size (<[k:=v]> m).
  Proof.
    destruct (m !! k) eqn:Hk.
    - have Heq : size (<[k:=v]> m) = size m.
      { apply map_size_insert_Some. exists v0. exact Hk. }
      lia.
    - have Heq : size (<[k:=v]> m) = S (size m).
      { apply map_size_insert_None. exact Hk. }
      lia.
  Qed.

  Lemma state_wf_update_heap_overwrite (σ : state) (l : loc) (fld : fld_name) (v old_v : val)
      (Hpresent : lookup_heap σ l fld = Some old_v)
      (Hwf : state_wf σ) :
      state_wf (update_heap σ l fld v).
  Proof.
    unfold lookup_heap in Hpresent.
    apply mk_state_wf.
    - exact (swf_max_stk_non_neg Hwf).
    - exact (swf_stk_bounded Hwf).
    - intros l' f' v' Hlookup. simpl in Hlookup.
      have Hsize : size (<[heap_addr_constr l fld := v]> σ.(global_heap)) = size σ.(global_heap).
      { apply map_size_insert_Some. exists old_v. exact Hpresent. }
      rewrite Hsize.
      destruct (decide (heap_addr_constr l' f' = heap_addr_constr l fld)) as [Heq | Hne].
      + injection Heq as HL HF. subst l'. subst f'.
        exact (swf_heap_bounded Hwf l fld old_v Hpresent).
      + rewrite lookup_insert_ne in Hlookup; [| by intro Heq'; apply Hne; symmetry].
        exact (swf_heap_bounded Hwf l' f' v' Hlookup).
    - exact (swf_ret_val_bound Hwf).
  Qed.

  (* Companion to state_wf_update_heap_overwrite: ghost_dom's own bound is
     stated purely in terms of size (global_heap σ), so it survives any
     step that doesn't change the real heap's size unchanged -- reproved
     explicitly at each such step, mirroring how state_wf itself is
     reproved rather than framed automatically (its bound is likewise
     σ-dependent). *)
  Lemma ghost_dom_bound_size_eq (σ σ' : state) (D : gset heap_addr)
      (Hsize : size (global_heap σ') = size (global_heap σ))
      (HD : ∀ a, a ∈ D → ((heap_addr_loc a).(loc_car) < Z.of_nat (size (global_heap σ)))%Z) :
      ∀ a, a ∈ D → ((heap_addr_loc a).(loc_car) < Z.of_nat (size (global_heap σ')))%Z.
  Proof. intros a Ha. rewrite Hsize. exact (HD a Ha). Qed.

  Lemma ghost_dom_bound_update_heap_overwrite (σ : state) (l : loc) (fld : fld_name) (v old_v : val)
      (D : gset heap_addr)
      (Hpresent : lookup_heap σ l fld = Some old_v)
      (HD : ∀ a, a ∈ D → ((heap_addr_loc a).(loc_car) < Z.of_nat (size (global_heap σ)))%Z) :
      ∀ a, a ∈ D → ((heap_addr_loc a).(loc_car) < Z.of_nat (size (global_heap (update_heap σ l fld v))))%Z.
  Proof.
    apply (ghost_dom_bound_size_eq σ (update_heap σ l fld v) D); [| exact HD].
    unfold lookup_heap in Hpresent. unfold update_heap. simpl.
    apply map_size_insert_Some. exists old_v. exact Hpresent.
  Qed.

  Lemma state_wf_update_lvar (σ : state) (x : var) (stk_id : stack_id) (v : val)
      (Hwf : state_wf σ) :
      state_wf (update_lvar σ x stk_id v).
  Proof.
    unfold update_lvar.
    destruct (σ.(stack) !! stk_id) eqn:Hlookup.
    - apply mk_state_wf.
      + exact (swf_max_stk_non_neg Hwf).
      + simpl. intros k vk Hk.
        destruct (decide (k = stk_id)) as [-> | Hne].
        * exact (swf_stk_bounded Hwf stk_id s Hlookup).
        * rewrite lookup_insert_ne in Hk; [| by intro H; exact (Hne (eq_sym H))].
          exact (swf_stk_bounded Hwf k vk Hk).
      + exact (swf_heap_bounded Hwf).
      + simpl. intros k frm Hk.
        destruct (decide (k = stk_id)) as [-> | Hne].
        * rewrite lookup_insert in Hk. injection Hk as <-. simpl.
          destruct (decide (x = "#ret_val")) as [-> | Hxne].
          -- rewrite lookup_insert. by eexists.
          -- rewrite lookup_insert_ne; [| exact Hxne].
             exact (swf_ret_val_bound Hwf stk_id s Hlookup).
        * rewrite lookup_insert_ne in Hk; [| by intro H; exact (Hne (eq_sym H))].
          exact (swf_ret_val_bound Hwf k frm Hk).
    - exact Hwf.
  Qed.

  Lemma foldr_heap_size_le (σ : state) (l : loc) (fs : list (fld_name * val)) :
      size σ.(global_heap) ≤
      size (global_heap (foldr (fun f_v acc => update_heap acc l f_v.1 f_v.2) σ fs)).
  Proof.
    induction fs as [| [f v] fs' IH].
    - simpl. lia.
    - simpl. etransitivity; [exact IH | apply heap_size_insert_le].
  Qed.

  (* When fs is nonempty, allocating it strictly grows the heap's size
     past l's own loc_car -- used to justify that the fresh ghost keys
     wp_alloc reserves (all at l too) are bounded by the post-alloc heap
     size, exactly like every real field just inserted at l already is. *)
  Lemma fresh_loc_lt_size_alloc_nonempty (σ : state) (l : loc)
      (fld0 : fld_name) (val0 : val) (fs' : list (fld_name * val))
      (Hl : l = fresh_loc (global_heap σ))
      (HNotIn : fld0 ∉ fs'.*1)
      (Hwf : state_wf σ) :
      (l.(loc_car) < Z.of_nat (size
        (global_heap (update_heap (foldr (λ f_v acc, update_heap acc l f_v.1 f_v.2) σ fs') l fld0 val0))))%Z.
  Proof.
    set (σ0 := foldr (λ f_v acc, update_heap acc l f_v.1 f_v.2) σ fs').
    have Hnotmem : global_heap σ0 !! heap_addr_constr l fld0 = None.
    { apply (foldr_update_heap_not_mem l fld0 fs' σ HNotIn).
      rewrite Hl. apply (fresh_loc_is_fresh _ _ (swf_heap_bounded Hwf)). }
    unfold update_heap. simpl.
    have Hsize : size (<[heap_addr_constr l fld0 := val0]> (global_heap σ0)) = S (size (global_heap σ0)).
    { apply map_size_insert_None. exact Hnotmem. }
    rewrite Hsize.
    have Hle := foldr_heap_size_le σ l fs'.
    fold σ0 in Hle.
    have Hlcar : l.(loc_car) = Z.of_nat (size (global_heap σ)).
    { rewrite Hl. unfold fresh_loc. reflexivity. }
    rewrite Hlcar. lia.
  Qed.

  Lemma fresh_loc_lt_size_alloc_nonempty' (σ : state) (l : loc) (fs : list (fld_name * val))
      (Hl : l = fresh_loc (global_heap σ))
      (HNoDup : NoDup fs.*1)
      (Hne : fs ≠ [])
      (Hwf : state_wf σ) :
      (l.(loc_car) < Z.of_nat (size
        (global_heap (foldr (λ f_v acc, update_heap acc l f_v.1 f_v.2) σ fs))))%Z.
  Proof.
    destruct fs as [| [fld0 val0] fs']; [done |].
    simpl in HNoDup. have HNotIn := NoDup_cons_1_1 _ _ HNoDup.
    exact (fresh_loc_lt_size_alloc_nonempty σ l fld0 val0 fs' Hl HNotIn Hwf).
  Qed.

  Lemma state_wf_alloc_step (σ : state) (l : loc) (fs : list (fld_name * val))
      (Hl : l = fresh_loc σ.(global_heap))
      (HNoDup : NoDup fs.*1)
      (Hwf : state_wf σ) :
      state_wf (foldr (fun f_v acc => update_heap acc l f_v.1 f_v.2) σ fs).
  Proof.
    induction fs as [| [f v] fs' IH].
    - simpl. exact Hwf.
    - simpl.
      simpl in HNoDup.
      have H_NotIn : f ∉ fs'.*1 := NoDup_cons_1_1 _ _ HNoDup.
      have H_NoDup' : NoDup fs'.*1 := NoDup_cons_1_2 _ _ HNoDup.
      specialize (IH H_NoDup').
      have Hge := foldr_heap_size_le σ l fs'.
      set σ0 := foldr (fun f_v acc => update_heap acc l f_v.1 f_v.2) σ fs'.
      fold σ0 in IH, Hge.
      have H_not_mem : σ0.(global_heap) !! heap_addr_constr l f = None.
      { apply (foldr_update_heap_not_mem l f fs' σ H_NotIn).
        rewrite Hl. apply (fresh_loc_is_fresh _ _ (swf_heap_bounded Hwf)). }
      apply mk_state_wf.
      + exact (swf_max_stk_non_neg IH).
      + exact (swf_stk_bounded IH).
      + intros l' f' v' Hlookup. simpl in Hlookup.
        have Hsize : size (<[heap_addr_constr l f := v]> σ0.(global_heap)) =
                     S (size σ0.(global_heap)).
        { apply map_size_insert_None. exact H_not_mem. }
        rewrite Hsize.
        destruct (decide (heap_addr_constr l' f' = heap_addr_constr l f)) as [Heq | Hne].
        * injection Heq as HL HF. subst l'. subst f'.
          have Hlcar : l.(loc_car) = Z.of_nat (size σ.(global_heap)).
          { rewrite Hl. unfold fresh_loc. reflexivity. }
          rewrite Hlcar. lia.
        * rewrite lookup_insert_ne in Hlookup; [| by intro H; exact (Hne (eq_sym H))].
          have := swf_heap_bounded IH l' f' v' Hlookup. lia.
      + exact (swf_ret_val_bound IH).
  Qed.

  Lemma state_wf_fresh_stk_id (σ : state) (Hwf : state_wf σ) :
      state_wf (fresh_stk_id σ).2.
  Proof.
    unfold fresh_stk_id. simpl.
    apply mk_state_wf.
    - simpl. have := swf_max_stk_non_neg Hwf. lia.
    - simpl. intros k v Hlookup.
      have := swf_stk_bounded Hwf k v Hlookup.
      have := swf_max_stk_non_neg Hwf. lia.
    - simpl. exact (swf_heap_bounded Hwf).
    - simpl. exact (swf_ret_val_bound Hwf).
  Qed.

  Lemma state_wf_update_stack (σ : state) (stk_id : stack_id) (frame : stack_frame)
      (Hid : (stk_id ≤ σ.(max_stack_id))%Z)
      (Hrv : is_Some (frame.(locals) !! "#ret_val"))
      (Hwf : state_wf σ) :
      state_wf (update_stack σ stk_id frame).
  Proof.
    unfold update_stack. apply mk_state_wf.
    - exact (swf_max_stk_non_neg Hwf).
    - simpl. intros k vk Hk.
      destruct (decide (k = stk_id)) as [-> | Hne].
      + exact Hid.
      + rewrite lookup_insert_ne in Hk; [| by intro H; exact (Hne (eq_sym H))].
        exact (swf_stk_bounded Hwf k vk Hk).
    - exact (swf_heap_bounded Hwf).
    - simpl. intros k frm Hk.
      destruct (decide (k = stk_id)) as [-> | Hne].
      + rewrite lookup_insert in Hk. injection Hk as <-. exact Hrv.
      + rewrite lookup_insert_ne in Hk; [| by intro H; exact (Hne (eq_sym H))].
        exact (swf_ret_val_bound Hwf k frm Hk).
  Qed.

End updates.

(* ----------------------------------------------------------------------- *)
(* Layer 0 (see local/parameters-redesign.md): every [ResourceAlgebra]
   embeds into a discrete CMRA, generically -- reusable by any program's
   [Γ] witness so it doesn't need to hand-align its own RAs with some
   pre-existing Iris camera. [pcore := fun _ => None]: Raven's RA has no
   notion of a duplicable/persistent part, so "no core" is the honest
   reading, not a hack -- every [pcore]-related CMRA law below is then
   vacuous, since its hypothesis never fires. *)
Section ra_cmra.
  Context (A : Type) `{ResourceAlgebra A} `{EqDecision A}.

  Canonical Structure ra_ofe : ofe := leibnizO A.

  Local Instance ra_pcore : PCore A := fun _ => None.
  Local Instance ra_op : Op A := comp.
  (* [valid] as a bare identifier is ambiguous with iris.algebra.cmra's own
     [Valid] class field of the same name; the [lang.valid] qualified path
     disambiguates to ResourceAlgebra's own field. *)
  Local Instance ra_valid_inst : Valid A := lang.valid.

  Lemma ra_cmra_mixin : RAMixin A.
  Proof.
    split.
    - intros x y1 y2 ->. done.
    - intros x y cx _ Hcx. discriminate.
    - intros x y ->. done.
    - intros x y z. symmetry. apply comp_assoc.
    - intros x y. apply comp_comm.
    - intros x cx Hcx. discriminate.
    - intros x cx Hcx. discriminate.
    - intros x y cx _ Hcx. discriminate.
    - intros x y Hv. destruct (comp_valid x y Hv) as [Hx _]. exact Hx.
  Qed.

  Definition ra_cmra : cmra := discreteR A ra_cmra_mixin.
End ra_cmra.

