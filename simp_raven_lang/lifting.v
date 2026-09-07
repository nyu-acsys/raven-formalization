From iris.algebra Require Import cmra gmap excl auth.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
From iris Require Import options.
From raven_iris.simp_raven_lang Require Import lang ghost_state.
From stdpp Require Import gmap list fin_maps.
Import uPred.
Import weakestpre.

From stdpp Require Import countable.

Module Make (RAs : RA_CONFIG).
Module ghost_state := raven_iris.simp_raven_lang.ghost_state.Make RAs.
Module lang := ghost_state.lang.
Import lang ghost_state.

Class simpLangG Σ := SimpLangG {
  simpLangG_invG : invGS Σ;
  simpLangG_gen_heapG :: heapG Σ
}.

Global Instance simpLang_irisG `{!simpLangG Σ} : irisGS simp_lang Σ := {
  iris_invGS := simpLangG_invG;
  state_interp σ κs _ _ := ghost_state.state_interp σ;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
  state_interp_mono _ _ _ _ := fupd_intro _ _;
}.

Section lifting.
  Context `{!simpLangG Σ}.

  (** Convenience bundle for clients that carry the complete operational
      procedure-frame layout. *)
  Record proc_call_layout (proc_entry : lang.proc) : Prop := {
    proc_call_args_nodup : NoDup (proc_args proc_entry).*1;
    proc_call_locals_nodup : NoDup (proc_local_vars proc_entry).*1;
    proc_call_args_locals_disjoint :
      (proc_args proc_entry).*1 ## (proc_local_vars proc_entry).*1;
    proc_call_return_local :
      "#ret_val" ∈ (proc_local_vars proc_entry).*1
  }.

  Lemma wp_heap_wr_expr stk_id stk_frm base e val l f x msk :
    {{{ stack_own[ stk_id, stk_frm] ∗ l#f ↦{1%Qp} x ∗
        ⌜expr_step base stk_frm (Val (LitLoc l))⌝ ∗
        ⌜expr_step e stk_frm (Val val)⌝}}}
      (RTFldWr base f e stk_id) @ msk
    {{{RET LitUnit; stack_own[ stk_id, stk_frm] ∗ l#f ↦{1%Qp} val ∗ £1 }}}.
  Proof.
    iIntros (Φ) "[Hstk [Hl [%He %He2]]] HΦ" .
    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate". 
    iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk ") as "%HstkPure".
    iModIntro. iSplit. 
    - unfold base_reducible. 
      iExists [], (RTVal LitUnit), (update_heap σ l f val), [].
      iPureIntro.
      apply (FldWrStep σ stk_id stk_frm _ f e l val); try done.
      

    - iNext. iIntros (e2 σ2 efs) "%H Hcred".
      inversion H as [  |  |  |  |  |
        | σ0 stk_id0 stk_frm0 e1 fld e' l0 v0 Hstk_frm0  Hl0 Hv0 
      |  |  |  |  |  |  |  |  |  ]; subst κ efs σ2 σ0 fld stk_id0 e' e1 e2; simpl; iFrame.
      
      assert (stk_frm0 = stk_frm) as Hstkfrm_subst. { 
          rewrite HstkPure in Hstk_frm0.  
          injection Hstk_frm0 as Hstk_frm0; try done.
      } subst stk_frm0. 
      assert (l = l0) as Hlsubst.
        { have Hlocation : LitLoc l = LitLoc l0 :=
            expr_step_val_unique _ _ _ _ He Hl0.
          injection Hlocation. trivial. }
      subst l0.
      assert (val = v0) as Hvsubst. 
        { apply (expr_step_val_unique _ _ _ _ He2 Hv0). } subst v0.
      
      iPoseProof (heap_interp_agreement with "Hhp Hl") as "%HHeapPure".
      iCombine "Hhp Hl" as "Hcomb".
      iSplitR; first done.
      iPoseProof (own_update heap_heap_name _ _ (heap_update _ _ _ _ val) with "Hcomb") as "Hcomb".
      iMod "Hcomb" as "Hcomb".
      iDestruct "Hcomb" as "[Hauth Hfrag]".
      iModIntro.
      iSplitL "Hauth".
      + iFrame. iPureIntro. split.
        { exact (ghost_dom_bound_update_heap_overwrite _ _ _ _ _ _ HHeapPure HgdomB). }
        { exact (state_wf_update_heap_overwrite _ _ _ _ _ HHeapPure Hwf). }
      + iApply "HΦ". iFrame.
  Qed.

  Lemma wp_heap_wr stk_id stk_frm v e val l f x msk :
    {{{ stack_own[ stk_id, stk_frm] ∗ l#f ↦{1%Qp} x ∗
        ⌜stk_frm.(locals) !! v = Some (LitLoc l)⌝ ∗
        ⌜expr_step e stk_frm (Val val)⌝}}}
      (RTFldWr (Var v) f e stk_id) @ msk
    {{{RET LitUnit; stack_own[ stk_id, stk_frm] ∗ l#f ↦{1%Qp} val ∗ £1 }}}.
  Proof.
    iIntros (Φ) "[Hstk [Hfield [%Hbase %Hvalue]]] HΦ".
    iApply (wp_heap_wr_expr stk_id stk_frm (Var v) e val l f x msk
      with "[Hstk Hfield]").
    { iFrame. iPureIntro. split; [apply VarStep; exact Hbase|exact Hvalue]. }
    iApply "HΦ".
  Qed.


  Lemma wp_assign stk_id stk_frm v v' e msk:
    {{{ stack_own[ stk_id, stk_frm] ∗ ⌜expr_step e stk_frm (Val v')⌝}}}
      (RTAssign v e stk_id) @ msk
    {{{ RET LitUnit; stack_own[ stk_id, StackFrame (<[v:=v']>stk_frm.(locals)) ] ∗ £1 }}}.
  Proof.
    iIntros (Φ) "[Hstk %He] HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate".
    iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iModIntro. iSplitR.
    - unfold base_reducible.
      iExists [], (RTVal LitUnit), (update_lvar σ v stk_id v'), [].
      iPureIntro.
      apply (RTAssignStep σ stk_id stk_frm v e v'); try done.

    - iNext. iIntros (e2 σ2 efs) "%H Hcred".
      inversion H as [  |  |  |
        σ0 stk_id0 stk_frm0 e1 v0 e0 Hstk_frm0 Hv0 
      |  |  |  |  |  |  |  |  |  |  |  |  ]; subst κ efs σ2 σ0 v0 e1 e2; simpl.

      assert (stk_frm0 = stk_frm) as Hstkfrm_subst. { 
          rewrite HstkPure in Hstk_frm0.  
          injection Hstk_frm0 as Hstk_frm0; try done.
      } subst stk_frm0. 
      assert (v' = e0) as Hvsubst. 
        { apply (expr_step_val_unique _ _ _ _ He Hv0). } subst v'.
      
      iCombine "Hstack" "Hstk" as "Hcomb".
      iSplitR; first done.
      iPoseProof (own_update heap_stack_name
          (● to_stackR (stack σ) ⋅ ◯ to_stackR {[stk_id := stk_frm]})
          (● to_stackR (stack σ') ⋅ ◯ to_stackR {[stk_id := {| locals := <[v:=e0]> (locals stk_frm) |}]})

           with "Hcomb"
      )
          as "Hcomb2".
      { apply (stack_upd_valid _ _ _ _ _ Hstk_frm0). }
      iMod "Hcomb2" as "Hcomb".
      iDestruct "Hcomb" as "[Hauth Hfrag]".
      iModIntro. iFrame.
      replace (global_heap σ') with (global_heap σ) by (unfold σ', update_lvar; rewrite HstkPure; done).
      replace (procs σ') with (procs σ) by (unfold σ', update_lvar; rewrite HstkPure; done).
      have Hwf' : state_wf σ' := state_wf_update_lvar σ v stk_id e0 Hwf.
      iFrame. iFrame (HgdomB Hwf').

      + iApply "HΦ". by iFrame.
  Qed.


  Lemma wp_heap_rd stk_id stk_frm fld e val l x msk q:
  {{{ stack_own[ stk_id, stk_frm ] ∗ ⌜expr_step e stk_frm (Val (LitLoc l))⌝ ∗ l#fld ↦{q%Qp} val }}}
      (RTFldRd x e fld stk_id) @ msk
    {{{RET LitUnit; stack_own[ stk_id, StackFrame (<[x:=val]>stk_frm.(locals))] ∗ l#fld ↦{q%Qp} val ∗ £1}}}.
  Proof.
    iIntros (Φ) "[Hstk [%HexprStep HHeap]] HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate".
    iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iPoseProof (heap_interp_agreement with "Hhp HHeap") as "%HHeapPure".
    iSplitR.
    - unfold base_reducible.
      iExists [], (RTVal LitUnit), (update_lvar σ x stk_id val), [].
      iPureIntro.
      apply (FldRdStep σ stk_id stk_frm x e fld l val); try done.

    - iModIntro. iNext. iIntros (e2 σ2 efs) "%H Hcred".
      inversion H as [ | | | | | | |
          σ0 stk_id0 stk_frm0 v0 e0 fld0 l0 v2 Hstk_frm0 HexSt HlookUp
        |  |  |  |  |  |  |  |  ]; subst v0 e0 fld0 stk_id0 σ0 κ e2 σ2 efs. simpl.
      iSplitR; try done.

      assert (stk_frm0 = stk_frm) as Hstkfrm_subst. {
          rewrite HstkPure in Hstk_frm0.
          injection Hstk_frm0 as Hstk_frm0; try done.
      } subst stk_frm0.

      assert (LitLoc l = LitLoc l0) as Hlsubst.
        { apply (expr_step_val_unique _ _ _ _ HexprStep HexSt). } injection  Hlsubst as Hl. subst l0.

      assert (val = v2) as Hvalsubst. {
        rewrite HHeapPure in HlookUp.
        injection HlookUp as HlookUp; try done.
      } subst v2.

      iCombine "Hstack" "Hstk" as "Hcomb".

      iPoseProof (own_update heap_stack_name
          (● to_stackR (stack σ) ⋅ ◯ to_stackR {[stk_id := stk_frm]})
          (● to_stackR (stack σ') ⋅ ◯ to_stackR {[stk_id := {| locals := <[x:=val]> (locals stk_frm) |}]})

           with "Hcomb"
      )
          as "Hcomb2".
      { apply (stack_upd_valid _ _ _ _ _ HstkPure). }
      iMod "Hcomb2" as "Hcomb".
      iDestruct "Hcomb" as "[Hauth Hfrag]".
      iModIntro. iFrame.
      replace (global_heap σ') with (global_heap σ) by (unfold σ', update_lvar; rewrite HstkPure; done).
      replace (procs σ') with (procs σ) by (unfold σ', update_lvar; rewrite HstkPure; done).
      have Hwf_rd : state_wf σ' := state_wf_update_lvar σ x stk_id val Hwf.
      iFrame. iFrame (HgdomB Hwf_rd).
      iApply "HΦ". iFrame.
  Qed.

  Fixpoint field_list_to_iprop lexpr fld_vals : iProp Σ := match fld_vals with
  | [] => ⌜True⌝
  | (fld,val) :: fld_vals => ( lexpr#fld ↦{1%Qp}(val)) ∗(field_list_to_iprop lexpr fld_vals)
  end.

  Lemma field_initializer_steps_unique stk
      (initializers : list (fld_name * expr))
      (values1 values2 : list (fld_name * lang.val)) :
    Forall2 (fun initializer field_value =>
      fst initializer = fst field_value /\
      expr_step (snd initializer) stk (Val (snd field_value)))
      initializers values1 ->
    Forall2 (fun initializer field_value =>
      fst initializer = fst field_value /\
      expr_step (snd initializer) stk (Val (snd field_value)))
      initializers values2 ->
    values1 = values2.
  Proof.
    intros Hsteps1. revert values2.
    induction Hsteps1; intros values2 Hsteps2; inversion Hsteps2; subst.
    - reflexivity.
    - destruct x as [field initializer], y as [field1 value1], y0 as [field2 value2].
      simpl in *. destruct H as [Hfield1 Hvalue1].
      destruct H2 as [Hfield2 Hvalue2]. subst field1 field2.
      have Hvalue : value1 = value2 :=
        expr_step_val_unique _ _ _ _ Hvalue1 Hvalue2.
      subst value2. f_equal. eapply IHHsteps1. exact H4.
  Qed.

  Lemma field_value_initializers_steps stk
      (values : list (fld_name * lang.val)) :
    Forall2 (fun initializer field_value =>
      fst initializer = fst field_value /\
      expr_step (snd initializer) stk (Val (snd field_value)))
      (map (fun '(field, value) => (field, Val value)) values) values.
  Proof.
    induction values as [|[field value] values IH].
    - constructor.
    - constructor; [split; [reflexivity|constructor]|exact IH].
  Qed.

  (* gfs is a list of *ghost* field names -- purely a naming/freshness
     bookkeeping list for rich_raven_lang's ghost heap (see Wghost in
     rrl_lang.v), carrying no values and never touching fs/the real heap
     at all. Growing ghost_dom_interp in lockstep with the real heap here,
     at the same fresh_loc, is what lets rrl_lang.v's HeapAllocRule prove
     a freshly-allocated location's ghost cells were never claimed before
     -- via plain exclusivity in ghost_dom_frag -- without needing to
     relate ghost ownership to the real heap in any other way. *)
  Lemma wp_alloc_expr stk_id stk_frm
      (initializers : list (fld_name * expr))
      (fs : list (fld_name * lang.val)) gfs x msk:
    Forall2 (fun initializer field_value =>
      fst initializer = fst field_value /\
      expr_step (snd initializer) stk_frm (Val (snd field_value)))
      initializers fs ->
    NoDup (fs.*1) ->
    NoDup gfs ->
    (gfs ≠ [] -> fs ≠ []) ->
    {{{ stack_own[ stk_id, stk_frm ] }}}
      (RTAlloc x initializers stk_id) @ msk
    {{{RET LitUnit; ∃ l: loc, stack_own[ stk_id, StackFrame (<[x:=LitLoc l]>stk_frm.(locals))] ∗
        field_list_to_iprop l fs ∗
        ghost_dom_frag (list_to_set (map (heap_addr_constr l) gfs)) ∗ £1}}}.
  Proof.
    intros Hinitializers HNoDup HNoDupGfs HgfsFs.
    iIntros (Φ) "Hstk HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate".
    iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iSplitR.
    - unfold base_reducible.
        set (l := fresh_loc σ.(global_heap)).
        set (σ' := (foldr (fun f_v  acc => update_heap acc l (fst f_v) (snd f_v)) σ fs)).
        set (σ'' := update_lvar σ' x stk_id (LitLoc l)). 
      iExists [], (RTVal LitUnit), σ'', [].
      iPureIntro.
      apply (AllocStep σ stk_id stk_frm x initializers fs); done.

    - iModIntro. iNext. iIntros (e2 σ2 efs) "%H Hcred".
    inversion H as [  |  |  |  |  |  |  |  |  |
        | σ0 stk_id0 stk_frm0 x0 initializers0 fs0 Hstack0 Hinitializers0
        |  |  |  |  |  ]; subst x0 initializers0 stk_id0 σ0 κ e2 σ2 efs; simpl;
        iRevert "Hgdom"; iFrame; iIntros "Hgdom".
        iSplitR; try done.

      assert (stk_frm0 = stk_frm) as ->.
      { rewrite HstkPure in Hstack0. by injection Hstack0. }
      assert (fs0 = fs) as ->.
      { eapply field_initializer_steps_unique; eassumption. }

      iCombine "Hstack" "Hstk" as "Hcomb".

      unfold heap_interp.

      set (fs_map := list_to_map fs : gmap fld_name lang.val).
      set (fs_heap_map := foldr (λ f_v acc, 
        <[(heap_addr_constr l f_v.1) := f_v.2]> acc) ∅ fs : gmap heap_addr lang.val).

      iPoseProof (own_update heap_heap_name
        (● to_heapUR (global_heap σ))
        (● to_heapUR (global_heap σ') ⋅ (◯  (to_heapUR fs_heap_map ) ))
        with "Hhp"
      ) as "HHeapUpd".

      {
        apply (heap_alloc_valid fs σ HNoDup Hwf).
      }

      assert ((stack σ) = (stack σ')) as H0. {
        clear H HgfsFs Hinitializers Hinitializers0 Hstack0.

        induction fs.
        - simpl in σ'. subst σ'. done.
        - simpl in σ'. 
        remember (foldr (λ f_v acc, update_heap acc l f_v.1 f_v.2) σ fs) as σ0 eqn:Hσ.
        unfold σ' in IHfs. rewrite IHfs. 2:{ inversion HNoDup. done. } subst σ'. unfold update_heap. simpl. done.
      }
      rewrite H0.

      iPoseProof (own_update heap_stack_name 
          (● to_stackR (stack σ') ⋅ ◯ to_stackR {[stk_id := stk_frm]})
          (● to_stackR (stack σ'') ⋅ ◯ to_stackR {[stk_id := {| locals := <[x:=LitLoc l]> (locals stk_frm) |}]})

           with "Hcomb"
      )
          as "Hcomb2".
      { rewrite H0 in HstkPure. apply (stack_upd_valid _ _ _ _ _ HstkPure). }
      iMod "Hcomb2" as "Hcomb".
      iDestruct "Hcomb" as "[Hauth Hfrag]".
      iDestruct "HHeapUpd" as ">[HHeapUpd HHp2]".
      iPoseProof (own_update heap_ghostdom_name
          (● gset_to_gmap (Excl ()) D)
          (● gset_to_gmap (Excl ()) (D ∪ list_to_set (map (heap_addr_constr l) gfs))
            ⋅ ◯ gset_to_gmap (Excl ()) (list_to_set (map (heap_addr_constr l) gfs)))
          with "Hgdom"
      ) as "HGdomUpd".
      { apply (ghost_dom_alloc_valid_sets gfs D l (global_heap σ) HNoDupGfs eq_refl HgdomB). }
      iMod "HGdomUpd" as "[Hgdom' Hgfrag]".
      iModIntro. iFrame.
      replace (global_heap σ'') with (global_heap σ') by (unfold σ'', update_lvar; rewrite <- H0; rewrite HstkPure; done).
      replace (procs σ'') with (procs σ') by (unfold σ'', update_lvar; rewrite <- H0; rewrite HstkPure; done).
      assert (procs σ' = procs σ) as Hprocs.
      { clear H H0 HgfsFs Hinitializers Hinitializers0 Hstack0. subst σ'. induction fs.
      - simpl. done.
      - simpl. unfold update_heap. simpl. apply IHfs. inversion HNoDup. done. }
      rewrite Hprocs. iFrame.
      have Hwf_σ' : state_wf σ' := state_wf_alloc_step σ l fs eq_refl HNoDup Hwf.
      have Hwf_alloc : state_wf σ'' := state_wf_update_lvar σ' x stk_id (LitLoc l) Hwf_σ'.
      have Hgh_eq : global_heap σ'' = global_heap σ' by (unfold σ'', update_lvar; rewrite <- H0; rewrite HstkPure; done).
      have HgdomB' : ∀ a, a ∈ (D ∪ list_to_set (map (heap_addr_constr l) gfs)) →
          ((heap_addr_loc a).(loc_car) < Z.of_nat (size (global_heap σ'')))%Z.
      { intros a Ha. apply elem_of_union in Ha. rewrite Hgh_eq. destruct Ha as [Ha | Ha].
        - have Hle : size (global_heap σ) ≤ size (global_heap σ').
          { subst σ'. apply foldr_heap_size_le. }
          have Hlt := HgdomB a Ha. lia.
        - apply elem_of_list_to_set in Ha. apply elem_of_list_fmap in Ha.
          destruct Ha as [fld [-> Hin]].
          have Hgfs_ne : gfs ≠ [].
          { intro Hcontra. rewrite Hcontra in Hin. by apply elem_of_nil in Hin. }
          have Hfs_ne : fs ≠ [] := HgfsFs Hgfs_ne.
          simpl.
          exact (fresh_loc_lt_size_alloc_nonempty' σ l fs eq_refl HNoDup Hfs_ne Hwf). }
      rewrite Hgh_eq in HgdomB'.
      iSplitR; [iPureIntro; split; [exact HgdomB' | exact Hwf_alloc] |].
      iApply "HΦ".
      iExists l. iFrame.

      clear H H0 Hprocs Hwf_σ' Hwf_alloc HgfsFs HgdomB HgdomB' Hgh_eq
        Hinitializers Hinitializers0 Hstack0.
      iInduction fs as [| a fss'] "IHfs" forall (HNoDup).
      + simpl. iDestruct "HHp2" as "_". iPureIntro. done.
      + simpl in fs_heap_map.
        subst fs_heap_map. simpl.
        unfold to_heapUR.
        rewrite fmap_insert.
        inversion HNoDup as [| ? ? H_NotIn H_NoDup'].
        rewrite insert_singleton_op.
        2 : {
          rewrite lookup_fmap.
          have foldr_fresh : ∀ fss0 : list (fld_name * lang.val),
            a.1 ∉ fss0.*1 →
            (foldr (λ f_v acc, (<[heap_addr_constr l f_v.1:=f_v.2]> acc : heap)) ∅ fss0) !! heap_addr_constr l a.1 = None.
          { intros fss0. induction fss0 as [| fv fss'' IH'].
            - intros _. apply lookup_empty.
            - intros H_ni. simpl. rewrite lookup_insert_ne.
              + apply IH'. set_solver.
              + intro Heq. apply H_ni. apply elem_of_cons. left. congruence. }
          rewrite (foldr_fresh fss' H_NotIn). done.
        }
        rewrite auth_frag_op.
        iDestruct "HHp2" as "[HHp2 HHp3]".
        destruct a as [fld val]. simpl. iFrame.
        iApply ("IHfs" with "[%]"). { exact H_NoDup'. } iApply "HHp3".

  Qed.

  Lemma wp_alloc stk_id stk_frm fs gfs x msk:
    NoDup (fs.*1) ->
    NoDup gfs ->
    (gfs ≠ [] -> fs ≠ []) ->
    {{{ stack_own[ stk_id, stk_frm ] }}}
      (RTAlloc x (map (fun '(field, value) => (field, Val value)) fs) stk_id) @ msk
    {{{RET LitUnit; ∃ l: loc,
        stack_own[ stk_id, StackFrame (<[x:=LitLoc l]>stk_frm.(locals))] ∗
        field_list_to_iprop l fs ∗
        ghost_dom_frag (list_to_set (map (heap_addr_constr l) gfs)) ∗ £1}}}.
  Proof.
    intros Hfields Hghost Hnonempty.
    apply (wp_alloc_expr stk_id stk_frm _ fs gfs x msk).
    - apply field_value_initializers_steps.
    - exact Hfields.
    - exact Hghost.
    - exact Hnonempty.
  Qed.

  Lemma wp_seq p q r s1 s2 mask:
  {{{ p }}} s1 @ mask {{{ RET lang.LitUnit; q }}} -∗
  {{{ q }}} s2 @ mask {{{ RET lang.LitUnit; r }}} -∗

  {{{ p }}} RTSeq s1 s2 @ mask {{{ RET lang.LitUnit; r }}}.
  Proof.
    iIntros "#Hs1 #Hs2".
    iIntros (Φ). iModIntro. iIntros "Hp HΦ".
    iApply (wp_bind (fill_item (SeqCtx s2)) _ _ _ _).
    iApply ("Hs1" with "Hp").
    iNext. iIntros "Hq".
    simpl.

    iApply wp_lift_base_step; first done.
    iIntros (σ ns κ κs nt) "Hstate".

    iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iApply fupd_mask_intro. { set_unfold. try done. }
    iIntros "Hemp".
  
    iSplitR.
    - iPureIntro. unfold base_reducible. 
    exists [], s2, σ, [].
    apply SeqStep.

    - iModIntro. iIntros (e2 σ2 efs).
    
    iIntros "%H Hcred".
    inversion H; subst s0 σ0 κ s2 σ2 efs. iFrame.
    simpl. 
    iMod "Hemp". iModIntro.
    iFrame. iFrame (HgdomB Hwf).
    iApply ("Hs2" with "Hq"). iNext; iFrame.
  Qed.

  (** A result-indexed sequence rule.  This is the direct counterpart of
      [wp_seq]: the second command may return an arbitrary value, and its WP
      is carried as the continuation of the unit result of the first one. *)
  Lemma wp_seq_wp s1 s2 (Φ : val -> iProp Σ) mask :
    WP s1 @ mask {{ v, ⌜v = LitUnit⌝ ∗ WP s2 @ mask {{ Φ }} }} -∗
    WP RTSeq s1 s2 @ mask {{ Φ }}.
  Proof.
    iIntros "Hs1".
    iApply (wp_bind (fill_item (SeqCtx s2)) _ _ _ _).
    iApply (wp_wand with "Hs1").
    iIntros (v) "Hunit".
    iDestruct "Hunit" as "[%Hunit Hs2]".
    destruct v; try discriminate.
    simpl.

    iApply wp_lift_base_step; first done.
    iIntros (σ ns κ κs nt) "Hstate".
    iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iApply fupd_mask_intro. { set_unfold. try done. }
    iIntros "Hemp".

    iSplitR.
    - iPureIntro. unfold base_reducible.
      exists [], s2, σ, [].
      apply SeqStep.

    - iModIntro. iIntros (e2 σ2 efs).
      iIntros "%H Hcred".
      inversion H; subst s0 σ0 κ s2 σ2 efs. iFrame.
      simpl.
      iMod "Hemp". iModIntro.
      iFrame. iFrame (HgdomB Hwf).
  Qed.

  (** The inverse of [wp_seq_wp], keeping the residual context intact rather
      than collapsing it to an immediate [WP s2].  [SeqStep] accepts an
      arbitrary result value for the first component ([RTSeq (RTVal v) s2]
      steps to [s2] for any [v], not only [LitUnit]); the unit fact
      [wp_seq_wp] relies on is an external strengthening from Raven's own
      statement-translation convention, not something the operational
      semantics forces, so it cannot be recovered here.  This is exactly
      [wp_bind_inv] specialized to [SeqCtx]. *)
  Lemma wp_seq_wp_context_inv s1 s2 (Φ : val -> iProp Σ) mask :
    WP RTSeq s1 s2 @ mask {{ Φ }} -∗
    WP s1 @ mask {{ v, WP RTSeq (RTVal v) s2 @ mask {{ Φ }} }}.
  Proof.
    iIntros "Hwp".
    iPoseProof (wp_bind_inv (fill_item (SeqCtx s2)) _ _ _ _ with "Hwp")
      as "Hwp".
    iApply (wp_wand with "Hwp"). iIntros (v) "Hwp". iExact "Hwp".
  Qed.

  (** The forward companion: rewrap a residual sequence around an arbitrary
      expression [s1], not only one already known to return [LitUnit].  This
      is exactly [wp_bind] specialized to [SeqCtx]; it is what lets a
      conditional-context lifting reassemble [RTSeq (RTIfS ...) s2] from a
      per-arm [WP e {{v, WP RTSeq (RTVal v) s2}}] fact obtained via
      [wp_seq_wp_context_inv] and [runtime_wp_if_true]/[runtime_wp_if_false],
      without ever needing [wp_seq_wp]'s unit-specific collapse. *)
  Lemma wp_seq_wp_context s1 s2 (Φ : val -> iProp Σ) mask :
    WP s1 @ mask {{ v, WP RTSeq (RTVal v) s2 @ mask {{ Φ }} }} -∗
    WP RTSeq s1 s2 @ mask {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply (wp_bind (fill_item (SeqCtx s2)) _ _ _ _).
    iApply (wp_wand with "Hwp"). iIntros (v) "Hwp". iExact "Hwp".
  Qed.

  Lemma wp_skip p mask stk_id :
  {{{ p }}} RTSkipS stk_id @ mask {{{ RET lang.LitUnit; p ∗ £1 }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate".
    iSplitR.
    - unfold base_reducible. iExists [], (RTVal LitUnit), σ, [].
    iPureIntro. apply RTSkipStep.

    - iModIntro. iNext. iIntros (e2 σ2 efs) "%H Hcred". iModIntro.
    inversion H; subst σ0 κ e2 σ2 efs. iSplitR; try done. iFrame. simpl. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_cas_succ x e1 fld e2 e3 stk_id stk_frm l v v' mask:
  expr_step e1 stk_frm (Val (LitLoc l)) ->
  expr_step e2 stk_frm (Val v) ->
  expr_step e3 stk_frm (Val v') ->
  {{{ stack_own[ stk_id, stk_frm ] ∗ l#fld ↦{1} v }}}
    RTCAS x e1 fld e2 e3 stk_id @ mask
  {{{ RET lang.LitUnit; stack_own[ stk_id, StackFrame (<[x:=LitBool true]> stk_frm.(locals)) ] ∗ l#fld ↦{1} v' ∗ £1 }}}.
  Proof.
    intros He1 He2 He3.
    iIntros (Φ) "[Hstk Hl] HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate".
    iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iPoseProof (heap_interp_agreement with "Hhp Hl") as "%HHeapPure".

    iModIntro. iSplitR.
    - iPureIntro. unfold base_reducible. exists [], (RTVal LitUnit), (update_lvar (update_heap σ l fld v') x stk_id (LitBool true)), [].
    apply (CASSuccStep σ stk_id stk_frm x e1 fld e2 e3 l v v'); try done.

    - iNext. iIntros (e0 σ2 efs) "%H Hcred".
    inversion H; subst v0 e4 fld0 e5 e6 stk_id0 σ0 κ e0 efs.

      +
        rewrite HstkPure in H11. inversion H11; subst stk_frm0.
        assert (v' = v3) as Hv. { apply (expr_step_val_unique e3 stk_frm); try done. } subst v3.
        assert (l0 = l) as Hl. { assert (LitLoc l0 = LitLoc l). {apply (expr_step_val_unique e1 stk_frm (LitLoc l0) (LitLoc l)); try done. } inversion H0; done. } subst l0.
        clear H11 H12.
        subst σ''.
        iPoseProof (heap_l_upd σ l fld v v' with "[Hl Hhp]") as "Hhp_upd"; first iFrame.
        iPoseProof (stack_lvar_upd _ _ _ x (LitBool true) with "[Hstk Hstack]") as "Hstk_upd"; try iFrame.

        iDestruct "Hhp_upd" as ">[Hl Hhp]".
        iDestruct "Hstk_upd" as ">[Hstk Hstack]".
        iModIntro.
        iSplitR; try auto.
         
        have Hstk' : stack σ' !! stk_id = Some stk_frm.
        { unfold σ'. simpl. exact HstkPure. }
        change (weakestpre.state_interp (update_lvar σ' x stk_id (LitBool true)) (S ns) κs nt) with
          (ghost_state.state_interp (update_lvar σ' x stk_id (LitBool true))).
        unfold ghost_state.state_interp.
        replace (global_heap (update_lvar σ' x stk_id (LitBool true))) with (global_heap σ') by
          (unfold update_lvar, σ'; simpl; rewrite HstkPure; done).
        replace (procs (update_lvar σ' x stk_id (LitBool true))) with (procs σ) by
          (unfold update_lvar, σ'; simpl; rewrite HstkPure; done).
        replace (stack (update_lvar σ' x stk_id (LitBool true))) with (stack (update_lvar σ x stk_id (LitBool true))) by
          (unfold update_lvar, σ'; simpl; rewrite HstkPure; done).
        iFrame "Hhp Hstack Hproc".
        have Hwf_σ' : state_wf σ' := state_wf_update_heap_overwrite σ l fld v' v HHeapPure Hwf.
        have Hwf_cas : state_wf (update_lvar σ' x stk_id (LitBool true)) :=
          state_wf_update_lvar σ' x stk_id (LitBool true) Hwf_σ'.
        have HgdomB_σ' : ∀ a, a ∈ D → ((heap_addr_loc a).(loc_car) < Z.of_nat (size (global_heap σ')))%Z :=
          ghost_dom_bound_update_heap_overwrite σ l fld v' v D HHeapPure HgdomB.
        iFrame (HgdomB_σ' Hwf_cas).
        simpl. iApply "HΦ". iFrame.

      + rewrite HstkPure in H11. inversion H11; subst stk_frm0.
        assert (l0 = l) as Hl. { assert (LitLoc l0 = LitLoc l). { apply (expr_step_val_unique e1 stk_frm (LitLoc l0) (LitLoc l)); try done. } inversion H0; done. } subst l0.
        rewrite HHeapPure in H14. inversion H14; subst v1.
        assert (v = v2). { apply (expr_step_val_unique e2 stk_frm); try done. }
        contradiction. 
  Qed.

  Lemma wp_cas_fail x e1 fld e2 e3 stk_id stk_frm l v v0 mask:
    expr_step e1 stk_frm (Val (LitLoc l)) ->
    expr_step e2 stk_frm (Val v) ->
    not (v = v0) -> 
    {{{ stack_own[ stk_id, stk_frm ] ∗ l#fld ↦{1} v0 }}}
      RTCAS x e1 fld e2 e3 stk_id @ mask
    {{{ RET lang.LitUnit; stack_own[ stk_id, StackFrame (<[x:=LitBool false]> stk_frm.(locals)) ] ∗ l#fld ↦{1} v0 ∗ £1 }}}.
  Proof.
    intros He1 He2 Hneq.
    iIntros (Φ) "[Hstk Hl] HΦ".

    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate".
    iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iPoseProof (heap_interp_agreement with "Hhp Hl") as "%HHeapPure".

    iModIntro. iSplitR.
    - iPureIntro. unfold base_reducible. exists [], (RTVal LitUnit), (update_lvar σ x stk_id (LitBool false)), [].
    apply (CASFailStep σ stk_id stk_frm x e1 fld e2 e3 l v0 v); try done.

    - iNext. iIntros (e0 σ2 efs) "%H Hcred".
    inversion H; subst v1 e4 fld0 e5 e6 stk_id0 σ0 κ e0 efs.

      + assert (stk_frm = stk_frm0) as Hstk_frm.
        { rewrite HstkPure in H11. injection H11 as H11. done. }
        subst stk_frm0.
        assert (LitLoc l = LitLoc l0) as Hl_l0. { apply (expr_step_val_unique e1 stk_frm); try done. } injection Hl_l0 as Hl_l0. subst l0. rewrite HHeapPure in H15. injection H15 as H15. subst v2.
        assert (v = v0) as Hv_v0. { apply (expr_step_val_unique e2 stk_frm); try done. } contradiction.

      + subst σ2.
        assert (stk_frm = stk_frm0) as Hstk_frm.
          { rewrite HstkPure in H11. injection H11 as H11. done. }
        subst stk_frm0. 
        assert (LitLoc l = LitLoc l0) as Hl_l0. { apply (expr_step_val_unique e1 stk_frm); try done. } injection Hl_l0 as Hl_l0. subst l0. rewrite HHeapPure in H14. injection H14 as H14. subst v2.
        clear H15 H13 H12 v3.
        
        iPoseProof (stack_lvar_upd _ _ _ x (LitBool false) with "[Hstk Hstack]") as "Hstk_upd"; try iFrame.

        iDestruct "Hstk_upd" as ">[Hstk Hstack]".
        iModIntro. iSplitR; try done.
        change (weakestpre.state_interp σ' (S ns) κs nt) with
          (ghost_state.state_interp σ').
        unfold ghost_state.state_interp.
        replace (global_heap σ') with (global_heap σ) by
          (unfold σ', update_lvar; rewrite HstkPure; done).
        replace (procs σ') with (procs σ) by
          (unfold σ', update_lvar; rewrite HstkPure; done).
        iFrame "Hhp Hstack Hproc".
        have Hwf_fail : state_wf σ' := state_wf_update_lvar σ x stk_id (LitBool false) Hwf.
        iFrame (HgdomB Hwf_fail).
        simpl. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_if_t e s1 s2 stk_id stk_frm p q v mask :
    expr_step e stk_frm (Val (LitBool true)) ->
    {{{ stack_own[ stk_id, stk_frm ] ∗ p }}} s1 @ mask {{{ RET v; q }}} -∗
    {{{ stack_own[ stk_id, stk_frm ] ∗ p }}} RTIfS e s1 s2 stk_id @ mask {{{ RET v; q }}}.
  Proof.
    intros Hstp.
    iIntros "#Hhoare".
    iIntros (Φ). iModIntro. iIntros "[Hstk Hp] HΦ".

    destruct (to_val s1) eqn:Hs1_val.
    2: {
          iApply wp_unfold.
    iIntros (σ ns κ κs nt) "Hstate".

    iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    
    iSpecialize ("Hhoare" $! Φ with "[Hstk Hp] HΦ"); iFrame.
      iPoseProof (wp_unfold with "Hhoare") as "Hhoare".
      iEval (unfold wp_pre) in "Hhoare".
      change (language.to_val s1 = None) in Hs1_val.
      iEval (rewrite Hs1_val) in "Hhoare".
      iAssert (∃ D0, ghost_dom_interp D0 ∗
                ⌜∀ a, a ∈ D0 → ((heap_addr_loc a).(loc_car) < Z.of_nat (size (global_heap σ)))%Z⌝)%I
        with "[Hgdom]" as "Hgdom_bundle".
      { iExists D. iFrame. iPureIntro. exact HgdomB. }
      iMod ("Hhoare" $! σ ns κ κs nt with "[Hhp Hproc Hstack Hgdom_bundle]") as "[%Hred Hrest]".
      { iFrame. iFrame (Hwf). }
      iModIntro.
      destruct Hred.
      destruct H as [e' [σ' [efs Hprim]]].
      simpl in x.

      iSplitR.
      + iPureIntro. unfold base_reducible. exists [], e', σ', efs.
        apply (Ectx_step [] (RTIfS e s1 s2 stk_id) e'); try done.
      apply  (RTIfTStep σ stk_id stk_frm e s1 s2 e' σ' efs); try done.
      pose proof  (obs_list_empty _ _ _ _ _ _ Hprim) as Hx_empt; subst.
      destruct Hprim.
      exists e1', e2', K.
      split; try done.
      
      + 
        iIntros (e2 σ2 efs0).
        iSpecialize ("Hrest" $! e2 σ2 efs0).
        iIntros "%Hbase".
        simpl in *.
        inversion Hbase; subst. simpl in *.

        pose proof  (obs_list_empty _ _ _ _ _ _ Hbase) as Hx_empt; subst.

        assert (K = []).
        { destruct K; try done. simpl in *.
          pose proof (fill_not_if K e0 e1' e s1 s2 stk_id). symmetry in H. contradiction. }
        subst. simpl in *. subst.

        inversion H1; subst.

        2: { rewrite HstkPure in H5. inversion H5; subst. pose proof (expr_step_val_unique _ _ _ _ Hstp H9). discriminate. }

        2: { rewrite HstkPure in H5. inversion H5; subst. pose proof (expr_step_val_unique _ _ _ _ Hstp H9). inversion H; subst. destruct s1; simpl; try (exfalso; done). }

        ++ simpl in *. assert (prim_step s1 σ [] e2' σ2 efs0).
          { destruct H10 as [e1'' [e2'' [K [Hfill1 [Hfill2 Hrtm]]]]]. apply (Ectx_step K e1'' e2''); try done. }
          iSpecialize ("Hrest" $! H).
          iExact "Hrest".
    }

    1: {
      iApply wp_lift_base_step; first done.
      iIntros (σ ns κ κs nt) "Hstate".
          iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iApply fupd_mask_intro. { set_unfold. try done. }

    iSpecialize ("Hhoare" $! Φ with "[Hstk Hp] HΦ"); iFrame.

    iIntros "Hfupd".
    iSplitR.
    - iPureIntro. unfold base_reducible. exists [], s1, σ, [].
    destruct s1 eqn:Hs1; simpl in Hs1_val; try discriminate.
    rewrite <- Hs1.
    apply (RTIfValStep σ stk_id stk_frm e s1 s2 true); try done.
    rewrite Hs1. done.


    -
      iIntros (e2 σ2 efs).
      iNext. iIntros "%Hbase Hcr".
      iMod "Hfupd". iModIntro.
      inversion Hbase; subst.
      1: {  
        destruct s1 eqn:Hs1; simpl in Hs1_val; try discriminate.
        destruct H10 as [e1' [e2' [K [Hs1' [Hs2' Hrtm]]]]].

      assert (K = []).
      { destruct K; try done. simpl in *.
          pose proof (lang.fill_not_val K e0 e1' v1). symmetry in Hs1'. contradiction. }
      subst. simpl in *. symmetry in Hs1'. subst.
      inversion Hrtm.
      
      }

      2: { rewrite HstkPure in H8. inversion H8; subst. pose proof (expr_step_val_unique e stk_frm0 _ _ Hstp H9). inversion H; subst. iFrame. simpl in *. iFrame. iFrame (HgdomB Hwf). }

      1: { rewrite HstkPure in H8. inversion H8; subst. pose proof (expr_step_val_unique e stk_frm0 _ _ Hstp H9). inversion H. }


     }
  Qed.

  Lemma wp_if_f e s1 s2 stk_id stk_frm p q v mask :
    expr_step e stk_frm (Val (LitBool false)) ->
    {{{ stack_own[ stk_id, stk_frm ] ∗ p }}} s2 @ mask {{{ RET v; q }}} -∗
    {{{ stack_own[ stk_id, stk_frm ] ∗ p }}} RTIfS e s1 s2 stk_id @ mask {{{ RET v; q }}}.
  Proof.
    intros Hstp.
    iIntros "#Hhoare".
    iIntros (Φ). iModIntro. iIntros "[Hstk Hp] HΦ".


    destruct (to_val s2) eqn:Hs2_val.
    2: {
          iApply wp_unfold.
    iIntros (σ ns κ κs nt) "Hstate".

    iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    
    iSpecialize ("Hhoare" $! Φ with "[Hstk Hp] HΦ"); iFrame.
      iPoseProof (wp_unfold with "Hhoare") as "Hhoare".
      iEval (unfold wp_pre) in "Hhoare".
      change (language.to_val s2 = None) in Hs2_val.
      iEval (rewrite Hs2_val) in "Hhoare".
      iAssert (∃ D0, ghost_dom_interp D0 ∗
                ⌜∀ a, a ∈ D0 → ((heap_addr_loc a).(loc_car) < Z.of_nat (size (global_heap σ)))%Z⌝)%I
        with "[Hgdom]" as "Hgdom_bundle".
      { iExists D. iFrame. iPureIntro. exact HgdomB. }
      iMod ("Hhoare" $! σ ns κ κs nt with "[Hhp Hproc Hstack Hgdom_bundle]") as "[%Hred Hrest]".
      { iFrame. iFrame (Hwf). }
      iModIntro.
      destruct Hred.
      destruct H as [e' [σ' [efs Hprim]]].
      simpl in x.

      iSplitR.
      + iPureIntro. unfold base_reducible. exists [], e', σ', efs.
        apply (Ectx_step [] (RTIfS e s1 s2 stk_id) e'); try done.
      apply  (RTIfFStep σ stk_id stk_frm e s1 s2 e' σ' efs); try done.
      pose proof  (obs_list_empty _ _ _ _ _ _ Hprim) as Hx_empt; subst.
      destruct Hprim.
      exists e1', e2', K.
      split; try done.
      
      + 
        iIntros (e2 σ2 efs0).
        iSpecialize ("Hrest" $! e2 σ2 efs0).
        iIntros "%Hbase".
        simpl in *.
        inversion Hbase; subst. simpl in *.

        pose proof  (obs_list_empty _ _ _ _ _ _ Hbase) as Hx_empt; subst.

        assert (K = []).
        { destruct K; try done. simpl in *.
          pose proof (fill_not_if K e0 e1' e s1 s2 stk_id). symmetry in H. contradiction. }
        subst. simpl in *. subst.

        inversion H1; subst.

        1: { rewrite HstkPure in H5. inversion H5; subst. pose proof (expr_step_val_unique _ _ _ _ Hstp H9). discriminate. }

        2: { rewrite HstkPure in H5. inversion H5; subst. pose proof (expr_step_val_unique _ _ _ _ Hstp H9). inversion H; subst. destruct s2; simpl; try (exfalso; done). }

        ++ simpl in *. assert (prim_step s2 σ [] e2' σ2 efs0).
          { destruct H10 as [e1'' [e2'' [K [Hfill1 [Hfill2 Hrtm]]]]]. apply (Ectx_step K e1'' e2''); try done. }
          iSpecialize ("Hrest" $! H).
          iExact "Hrest".
    }

    1: {
      iApply wp_lift_base_step; first done.
      iIntros (σ ns κ κs nt) "Hstate".
          iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iApply fupd_mask_intro. { set_unfold. try done. }

    iSpecialize ("Hhoare" $! Φ with "[Hstk Hp] HΦ"); iFrame.

    iIntros "Hfupd".
    iSplitR.
    - iPureIntro. unfold base_reducible. exists [], s2, σ, [].
    destruct s2 eqn:Hs2; simpl in Hs2_val; try discriminate.
    rewrite <- Hs2.
    apply (RTIfValStep σ stk_id stk_frm e s1 s2 false); try done.
    rewrite Hs2. done.


    -
      iIntros (e2 σ2 efs).
      iNext. iIntros "%Hbase Hcr".
      iMod "Hfupd". iModIntro.
      inversion Hbase; subst.
      2: { 
        destruct s2 eqn:Hs2; simpl in Hs2_val; try discriminate.
        destruct H10 as [e1' [e2' [K [Hs1' [Hs2' Hrtm]]]]].

      assert (K = []).
      { destruct K; try done. simpl in *.
          pose proof (lang.fill_not_val K e0 e1' v1). symmetry in Hs1'. contradiction. }
      subst. simpl in *. symmetry in Hs1'. subst.
      inversion Hrtm.
      
      }

      2: { rewrite HstkPure in H8. inversion H8; subst. pose proof (expr_step_val_unique e stk_frm0 _ _ Hstp H9). inversion H; subst. iFrame. simpl in *. iFrame. iFrame (HgdomB Hwf). }

      1: { rewrite HstkPure in H8. inversion H8; subst. pose proof (expr_step_val_unique e stk_frm0 _ _ Hstp H9). inversion H. }


     }
  Qed.

  (** Result-indexed versions of the conditional lifting rules.  Unlike the
      Texan-triple rules above, these preserve an arbitrary continuation
      directly, which is the form needed at the typed runtime boundary. *)
  Lemma wp_if_t_wp e s1 s2 stk_id stk_frm p (Φ : val -> iProp Σ) mask :
    expr_step e stk_frm (Val (LitBool true)) ->
    (stack_own[ stk_id, stk_frm ] ∗ p -∗ WP s1 @ mask {{ Φ }}) -∗
    stack_own[ stk_id, stk_frm ] ∗ p -∗
      WP RTIfS e s1 s2 stk_id @ mask {{ Φ }}.
  Proof.
    intros Hstp.
    iIntros "Hwp [Hstk Hp]".

    destruct (to_val s1) eqn:Hs1_val.
    2: {
      iApply wp_unfold.
      iIntros (σ ns κ κs nt) "Hstate".

      iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
      iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".

      iSpecialize ("Hwp" with "[Hstk Hp]"); iFrame.
      iPoseProof (wp_unfold with "Hwp") as "Hwp".
      iEval (unfold wp_pre) in "Hwp".
      change (language.to_val s1 = None) in Hs1_val.
      iEval (rewrite Hs1_val) in "Hwp".
      iAssert (∃ D0, ghost_dom_interp D0 ∗
                ⌜∀ a, a ∈ D0 → ((heap_addr_loc a).(loc_car) < Z.of_nat (size (global_heap σ)))%Z⌝)%I
        with "[Hgdom]" as "Hgdom_bundle".
      { iExists D. iFrame. iPureIntro. exact HgdomB. }
      iMod ("Hwp" $! σ ns κ κs nt with "[Hhp Hproc Hstack Hgdom_bundle]") as "[%Hred Hrest]".
      { iFrame. iFrame (Hwf). }
      iModIntro.
      destruct Hred.
      destruct H as [e' [σ' [efs Hprim]]].
      simpl in x.

      iSplitR.
      + iPureIntro. unfold base_reducible. exists [], e', σ', efs.
        apply (Ectx_step [] (RTIfS e s1 s2 stk_id) e'); try done.
        apply (RTIfTStep σ stk_id stk_frm e s1 s2 e' σ' efs); try done.
        pose proof (obs_list_empty _ _ _ _ _ _ Hprim) as Hx_empt; subst.
        destruct Hprim.
        exists e1', e2', K.
        split; try done.

      + iIntros (e2 σ2 efs0).
        iSpecialize ("Hrest" $! e2 σ2 efs0).
        iIntros "%Hbase".
        simpl in *.
        inversion Hbase; subst. simpl in *.

        pose proof (obs_list_empty _ _ _ _ _ _ Hbase) as Hx_empt; subst.

        assert (K = []).
        { destruct K; try done. simpl in *.
          pose proof (fill_not_if K e0 e1' e s1 s2 stk_id). symmetry in H. contradiction. }
        subst. simpl in *. subst.

        inversion H1; subst.

        2: { rewrite HstkPure in H5. inversion H5; subst.
             pose proof (expr_step_val_unique _ _ _ _ Hstp H9). discriminate. }

        2: { rewrite HstkPure in H5. inversion H5; subst.
             pose proof (expr_step_val_unique _ _ _ _ Hstp H9).
             inversion H; subst. destruct s1; simpl; try (exfalso; done). }

        ++ simpl in *. assert (prim_step s1 σ [] e2' σ2 efs0).
           { destruct H10 as [e1'' [e2'' [K [Hfill1 [Hfill2 Hrtm]]]]].
             apply (Ectx_step K e1'' e2''); try done. }
           iSpecialize ("Hrest" $! H).
           iExact "Hrest".
    }

    1: {
      iApply wp_lift_base_step; first done.
      iIntros (σ ns κ κs nt) "Hstate".
      iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
      iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
      iApply fupd_mask_intro. { set_unfold. try done. }

      iSpecialize ("Hwp" with "[Hstk Hp]"); iFrame.

      iIntros "Hfupd".
      iSplitR.
      - iPureIntro. unfold base_reducible. exists [], s1, σ, [].
        destruct s1 eqn:Hs1; simpl in Hs1_val; try discriminate.
        rewrite <- Hs1.
        apply (RTIfValStep σ stk_id stk_frm e s1 s2 true); try done.
        rewrite Hs1. done.

      - iIntros (e2 σ2 efs).
        iNext. iIntros "%Hbase Hcr".
        iMod "Hfupd". iModIntro.
        inversion Hbase; subst.
        1: {
          destruct s1 eqn:Hs1; simpl in Hs1_val; try discriminate.
          destruct H10 as [e1' [e2' [K [Hs1' [Hs2' Hrtm]]]]].

          assert (K = []).
          { destruct K; try done. simpl in *.
            pose proof (lang.fill_not_val K e0 e1' v0). symmetry in Hs1'. contradiction. }
          subst. simpl in *. symmetry in Hs1'. subst.
          inversion Hrtm.
        }

        2: { rewrite HstkPure in H8. inversion H8; subst.
             pose proof (expr_step_val_unique e stk_frm0 _ _ Hstp H9).
             inversion H; subst. iFrame. simpl in *. iFrame. iFrame (HgdomB Hwf). }

        1: { rewrite HstkPure in H8. inversion H8; subst.
             pose proof (expr_step_val_unique e stk_frm0 _ _ Hstp H9). inversion H. }
    }
  Qed.

  Lemma wp_if_f_wp e s1 s2 stk_id stk_frm p (Φ : val -> iProp Σ) mask :
    expr_step e stk_frm (Val (LitBool false)) ->
    (stack_own[ stk_id, stk_frm ] ∗ p -∗ WP s2 @ mask {{ Φ }}) -∗
    stack_own[ stk_id, stk_frm ] ∗ p -∗
      WP RTIfS e s1 s2 stk_id @ mask {{ Φ }}.
  Proof.
    intros Hstp.
    iIntros "Hwp [Hstk Hp]".

    destruct (to_val s2) eqn:Hs2_val.
    2: {
      iApply wp_unfold.
      iIntros (σ ns κ κs nt) "Hstate".

      iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
      iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".

      iSpecialize ("Hwp" with "[Hstk Hp]"); iFrame.
      iPoseProof (wp_unfold with "Hwp") as "Hwp".
      iEval (unfold wp_pre) in "Hwp".
      change (language.to_val s2 = None) in Hs2_val.
      iEval (rewrite Hs2_val) in "Hwp".
      iAssert (∃ D0, ghost_dom_interp D0 ∗
                ⌜∀ a, a ∈ D0 → ((heap_addr_loc a).(loc_car) < Z.of_nat (size (global_heap σ)))%Z⌝)%I
        with "[Hgdom]" as "Hgdom_bundle".
      { iExists D. iFrame. iPureIntro. exact HgdomB. }
      iMod ("Hwp" $! σ ns κ κs nt with "[Hhp Hproc Hstack Hgdom_bundle]") as "[%Hred Hrest]".
      { iFrame. iFrame (Hwf). }
      iModIntro.
      destruct Hred.
      destruct H as [e' [σ' [efs Hprim]]].
      simpl in x.

      iSplitR.
      + iPureIntro. unfold base_reducible. exists [], e', σ', efs.
        apply (Ectx_step [] (RTIfS e s1 s2 stk_id) e'); try done.
        apply (RTIfFStep σ stk_id stk_frm e s1 s2 e' σ' efs); try done.
        pose proof (obs_list_empty _ _ _ _ _ _ Hprim) as Hx_empt; subst.
        destruct Hprim.
        exists e1', e2', K.
        split; try done.

      + iIntros (e2 σ2 efs0).
        iSpecialize ("Hrest" $! e2 σ2 efs0).
        iIntros "%Hbase".
        simpl in *.
        inversion Hbase; subst. simpl in *.

        pose proof (obs_list_empty _ _ _ _ _ _ Hbase) as Hx_empt; subst.

        assert (K = []).
        { destruct K; try done. simpl in *.
          pose proof (fill_not_if K e0 e1' e s1 s2 stk_id). symmetry in H. contradiction. }
        subst. simpl in *. subst.

        inversion H1; subst.

        1: { rewrite HstkPure in H5. inversion H5; subst.
             pose proof (expr_step_val_unique _ _ _ _ Hstp H9). discriminate. }

        2: { rewrite HstkPure in H5. inversion H5; subst.
             pose proof (expr_step_val_unique _ _ _ _ Hstp H9).
             inversion H; subst. destruct s2; simpl; try (exfalso; done). }

        ++ simpl in *. assert (prim_step s2 σ [] e2' σ2 efs0).
           { destruct H10 as [e1'' [e2'' [K [Hfill1 [Hfill2 Hrtm]]]]].
             apply (Ectx_step K e1'' e2''); try done. }
           iSpecialize ("Hrest" $! H).
           iExact "Hrest".
    }

    1: {
      iApply wp_lift_base_step; first done.
      iIntros (σ ns κ κs nt) "Hstate".
      iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
      iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
      iApply fupd_mask_intro. { set_unfold. try done. }

      iSpecialize ("Hwp" with "[Hstk Hp]"); iFrame.

      iIntros "Hfupd".
      iSplitR.
      - iPureIntro. unfold base_reducible. exists [], s2, σ, [].
        destruct s2 eqn:Hs2; simpl in Hs2_val; try discriminate.
        rewrite <- Hs2.
        apply (RTIfValStep σ stk_id stk_frm e s1 s2 false); try done.
        rewrite Hs2. done.

      - iIntros (e2 σ2 efs).
        iNext. iIntros "%Hbase Hcr".
        iMod "Hfupd". iModIntro.
        inversion Hbase; subst.
        2: {
          destruct s2 eqn:Hs2; simpl in Hs2_val; try discriminate.
          destruct H10 as [e1' [e2' [K [Hs1' [Hs2' Hrtm]]]]].

          assert (K = []).
          { destruct K; try done. simpl in *.
            pose proof (lang.fill_not_val K e0 e1' v0). symmetry in Hs1'. contradiction. }
          subst. simpl in *. symmetry in Hs1'. subst.
          inversion Hrtm.
        }

        2: { rewrite HstkPure in H8. inversion H8; subst.
             pose proof (expr_step_val_unique e stk_frm0 _ _ Hstp H9).
             inversion H; subst. iFrame. simpl in *. iFrame. iFrame (HgdomB Hwf). }

        1: { rewrite HstkPure in H8. inversion H8; subst.
             pose proof (expr_step_val_unique e stk_frm0 _ _ Hstp H9). inversion H. }
    }
  Qed.

  Lemma Forall2_list_to_map_zip args arg_vals :
    NoDup args ->
    length args = length arg_vals →
    Forall2
      (λ var (val : lang.val),
        @list_to_map lang.var lang.val (gmap lang.var lang.val) _ _ (zip args arg_vals) !! var = Some val)
      args arg_vals.
  Proof.
    revert arg_vals.
    induction args as [|x args IH]; intros [|v vs] HNoDup Hlen; simpl in *; try discriminate.
    - constructor.
    - constructor.
      + simpl. rewrite lookup_insert; try done.

      + pose proof HNoDup as HNoDup'. apply NoDup_cons_1_2 in HNoDup'. inversion Hlen. specialize (IH vs HNoDup' H0 ).
      apply NoDup_cons_1_1 in HNoDup.
      eapply Forall2_impl; [|exact IH].
      intros y val Hlookup.
      rewrite lookup_insert_ne; [done|]. simpl. simpl in Hlookup.
      intros ->. apply HNoDup.
      apply elem_of_list_to_map_2 in Hlookup.
      apply elem_of_zip_l in Hlookup.
      exact Hlookup.
  Qed.

  (* Like Forall2_list_to_map_zip, but for a declaration list (name * typ)
     zipped against non-deterministically chosen, well-typed values: keeps
     both the resulting lookup fact and the typing fact for each entry. *)
  Lemma Forall2_list_to_map_zip_typed (locals : list (lang.var * lang.typ)) (local_vals : list lang.val) :
    NoDup locals.*1 ->
    Forall2 (fun decl val => val_has_typ val (snd decl)) locals local_vals ->
    Forall2 (fun decl val =>
      (list_to_map (zip locals.*1 local_vals) : gmap lang.var lang.val) !! (fst decl) = Some val
      ∧ val_has_typ val (snd decl))
      locals local_vals.
  Proof.
    intros Hnodup Htyped.
    induction Htyped as [| [v tp] val locs vals Hty Hrest IH].
    - constructor.
    - simpl in Hnodup |- *. constructor.
      + split; [simpl; rewrite lookup_insert; done | exact Hty].
      + apply NoDup_cons_1_2 in Hnodup as Hnodup'.
        pose proof (IH Hnodup') as IH'.
        eapply Forall2_impl; [| exact IH'].
        intros [v' tp'] val' [Hlookup Hty'].
        simpl in *. split; [| exact Hty'].
        rewrite lookup_insert_ne; [exact Hlookup |].
        intro Heq. subst v'.
        apply NoDup_cons_1_1 in Hnodup.
        apply elem_of_list_to_map_2 in Hlookup.
        apply elem_of_zip_l in Hlookup.
        contradiction.
  Qed.

  (* The per-entry fact needed to reconstruct a fresh frame's locals exactly:
     every declared local is present, with a value of its declared type. *)
  Lemma proc_locals_present_typed (locals : list (lang.var * lang.typ)) (local_vals : list lang.val) :
    NoDup locals.*1 ->
    Forall2 (fun decl val => val_has_typ val (snd decl)) locals local_vals ->
    ∀ v tp, (v, tp) ∈ locals ->
      ∃ val, (list_to_map (zip locals.*1 local_vals) : gmap lang.var lang.val) !! v = Some val ∧ val_has_typ val tp.
  Proof.
    intros Hnodup Htyped v tp Hin.
    have Hlem := Forall2_list_to_map_zip_typed locals local_vals Hnodup Htyped.
    apply elem_of_list_lookup_1 in Hin as [i Hi].
    pose proof (Forall2_lookup_l _ locals local_vals i (v, tp) Hlem Hi) as [val [Hval HP]].
    exists val. exact HP.
  Qed.

  Lemma Forall2_canonical_val_has_typ (decls : list (lang.var * lang.typ)) :
    Forall2 (fun decl val => val_has_typ val (snd decl)) decls (map (fun decl => canonical_val (snd decl)) decls).
  Proof.
    induction decls as [| [v tp] rest IH]; simpl; constructor; [apply canonical_val_has_typ | exact IH].
  Qed.

  Lemma wp_active_call_nostore callee_stk_id callee_frame value mask p :
    {{{ stack_own[ callee_stk_id, callee_frame ] ∗ p }}}
      RTActiveCallNoStore (RTVal value) callee_stk_id @ mask
    {{{ RET LitUnit; p ∗ £1 }}}.
  Proof.
    iIntros (Φ) "[Hcallee Hp] HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ ns κ κs nt) "Hstate".
    iDestruct "Hstate" as
      "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iPoseProof (stack_interp_agreement with "Hstack Hcallee") as "%Hcallee".
    iModIntro. iSplitR.
    - iPureIntro. unfold base_reducible.
      exists [], (RTVal LitUnit), σ, [].
      apply (ActiveCallNoStoreStep σ callee_stk_id value callee_frame).
      exact Hcallee.
    - iNext. iIntros (e2 σ2 efs) "%Hstep Hcred".
      inversion Hstep; subst σ0 κ e2 σ2 efs.
      iModIntro. iSplitR; first done.
      iFrame "Hhp Hproc Hstack Hgdom". iFrame (HgdomB Hwf).
      simpl. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_call stk_id stk_frm args arg_vals proc x proc_entry mask p (q : lang.val -> iProp Σ):
    NoDup (proc_args proc_entry).*1 ->
    NoDup (proc_local_vars proc_entry).*1 ->
    (proc_args proc_entry).*1 ## (proc_local_vars proc_entry).*1 ->
    "#ret_val" ∈ (proc_local_vars proc_entry).*1 ->
    length args = length (proc_entry.(proc_args)) ->
    Forall2 (fun expr val => expr_step expr stk_frm (Val val)) args arg_vals ->
    ▷ (∀ stk_id' stk_frm',
      ⌜Forall2 (fun var val => stk_frm'.(locals) !! var = Some val) proc_entry.(proc_args).*1 arg_vals
       ∧ (∀ v tp, (v, tp) ∈ proc_entry.(proc_local_vars) ->
            ∃ val, stk_frm'.(locals) !! v = Some val ∧ val_has_typ val tp)
       ∧ dom stk_frm'.(locals) = list_to_set proc_entry.(proc_args).*1 ∪ list_to_set (proc_entry.(proc_local_vars)).*1⌝ -∗
        {{{ stack_own[ stk_id', stk_frm' ] ∗ p }}}
            to_rtstmt stk_id' proc_entry.(proc_stmt) @ mask
        {{{ RET (LitUnit); ∃ ret_val stk_frm'', stack_own[ stk_id', stk_frm'' ] ∗ ⌜ (stk_frm''.(locals) !! "#ret_val" = Some ret_val) ⌝ ∗ q ret_val }}} ) -∗

    {{{ stack_own[ stk_id, stk_frm ] ∗ (proc_tbl_chunk proc proc_entry) ∗ p }}}
        RTCall x proc args stk_id @ mask
    {{{ RET LitUnit; ∃ ret_val, stack_own[ stk_id, StackFrame (<[x:=ret_val]>stk_frm.(locals)) ] ∗ q ret_val ∗ £1}}}.
  Proof.
    intros HNoDup HNoDupLocals Hdisjoint Hrv_in Hlen Harg_evals.

    iIntros "#Hproc_body".
    iIntros (Φ). iModIntro. iIntros "[Hstk [Hproc_tbl Hp]] HΦ".

    iApply wp_lift_base_step; first done.
    iIntros (σ1 ns κ κs nt) "Hstate".
    iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iPoseProof (proc_tbl_interp_agreement with "Hproc Hproc_tbl") as "%HprocPure".
    iApply fupd_mask_intro. { set_solver. }

    iIntros "Hfupd". iSplitR.

    - iPureIntro. unfold base_reducible.

    set new_stk_id := (fresh_stk_id σ1).1.
    set σ' :=  (fresh_stk_id σ1).2.
    set local_vals0 := map (fun decl => canonical_val (snd decl)) proc_entry.(proc_local_vars).
    set new_stk_frame := StackFrame
      (list_to_map (decls_zip_vals proc_entry.(proc_args) arg_vals
                    ++ decls_zip_vals proc_entry.(proc_local_vars) local_vals0)).
    set σ'' := update_stack σ' new_stk_id new_stk_frame.

    set new_stmt := to_rtstmt new_stk_id proc_entry.(proc_stmt).

    exists [], (RTActiveCall x new_stmt new_stk_id stk_id), σ'', [].

    apply (RTCallStep σ1 stk_id stk_frm x proc args arg_vals proc_entry local_vals0); try done.
    apply Forall2_canonical_val_has_typ.

  - iNext. iIntros (e2 σ2 efs) "%H Hcred".
    inversion H; subst proc0 args0 stk_id0 σ1 κ σ2 e2 efs.
    have Hprocedure : procedure = proc_entry.
    { match goal with
      | Hlookup : procs σ !! proc = Some procedure |- _ =>
          rewrite HprocPure in Hlookup; by injection Hlookup
      end. }
    have Hcaller : stk_frm0 = stk_frm.
    { match goal with
      | Hlookup : stack σ !! stk_id = Some stk_frm0 |- _ =>
          rewrite HstkPure in Hlookup; by injection Hlookup
      end. }
    subst procedure stk_frm0.
    have Hlocal_vals : Forall2
        (fun decl val => val_has_typ val (snd decl))
        (proc_local_vars proc_entry) local_vals.
    { match goal with
      | Htyped : Forall2 _ (proc_local_vars proc_entry) local_vals |- _ =>
          exact Htyped
      end. }
    have Harg_steps : Forall2
        (fun expression value => expr_step expression stk_frm (Val value))
        args arg_vals0.
    { match goal with
      | Hsteps : Forall2 _ args arg_vals0 |- _ => exact Hsteps
      end. }
    iMod "Hfupd".
    (* Freshness: the new stack id (Z.of_nat (Z.to_nat σ.(max_stack_id) + 1))
       must not yet be in the stack map. Follows from state_wf's own
       invariant that every allocated stack id is ≤ max_stack_id. *)
    assert (Hfresh_new : stack σ !! Z.of_nat (Z.to_nat σ.(max_stack_id) + 1) = None) by (apply (max_stk_id_fresh _ Hwf)).
    iPoseProof ((stack_new_stk_frm_upd σ new_stk_frame Hfresh_new) with "Hstack") as ">[Hstack' Hstk']".

    simpl; iFrame.
    have Hwf_σ' : state_wf (fresh_stk_id σ).2 := state_wf_fresh_stk_id σ Hwf.
    have Hle_call : (Z.of_nat (Z.to_nat σ.(max_stack_id) + 1) ≤ (fresh_stk_id σ).2.(max_stack_id))%Z.
    { have := swf_max_stk_non_neg Hwf. unfold fresh_stk_id. simpl. lia. }
    have Hrv_new : is_Some (new_stk_frame.(locals) !! "#ret_val").
    { simpl.
      have HNoDupLocalsC : NoDup proc_entry.(proc_local_vars).*1 := HNoDupLocals.
      have Hrv_pair : ∃ tp, ("#ret_val", tp) ∈ proc_entry.(proc_local_vars).
      { apply elem_of_list_fmap_2 in Hrv_in as [[v0 tp0] [Heq Hin]].
        simpl in Heq. subst v0. exists tp0. exact Hin. }
      destruct Hrv_pair as [tp Hrv_pair].
      have Hpresent := proc_locals_present_typed proc_entry.(proc_local_vars)
        local_vals HNoDupLocalsC Hlocal_vals "#ret_val" tp Hrv_pair.
      destruct Hpresent as [val [Hlk _]].
      rewrite list_to_map_app.
      destruct (@list_to_map lang.var lang.val (gmap lang.var lang.val) _ _
                  (zip (map fst (proc_args proc_entry)) arg_vals0) !! "#ret_val") as [rv|] eqn:Hm1.
      - rewrite (lookup_union_Some_l _ _ _ _ Hm1). by eexists.
      - rewrite lookup_union_r; [| exact Hm1]. rewrite Hlk. by eexists.
    }
    have Hwf_call : state_wf (update_stack (fresh_stk_id σ).2 (Z.to_nat σ.(max_stack_id) + 1) new_stk_frame) :=
      state_wf_update_stack (fresh_stk_id σ).2 (Z.to_nat σ.(max_stack_id) + 1) new_stk_frame Hle_call Hrv_new Hwf_σ'.
    iFrame (HgdomB Hwf_call). iModIntro.

    iApply (wp_bind (fill_item (ActiveCallCtx x (Z.to_nat (max_stack_id σ) + 1) stk_id)) _ _ _ _).
    set stk_id' := (Z.to_nat (max_stack_id σ) + 1).
    iSpecialize ("Hproc_body" $! stk_id' new_stk_frame).
    iPoseProof ("Hproc_body" with "[%]") as "Hproc_body'".
    { simpl.
      assert (arg_vals0 = arg_vals).
      { apply (Forall2_expr_step_val_unique args stk_frm); try done. }
      subst arg_vals0.
      have Hargs_len : length (proc_args proc_entry).*1 = length arg_vals.
      { apply Forall2_length in Harg_evals. rewrite map_length. rewrite <- Hlen. exact Harg_evals. }
      have Hargs_len_le : length (proc_args proc_entry).*1 ≤ length arg_vals. { lia. }
      have Hlocals_len_le : length (proc_local_vars proc_entry).*1 ≤ length local_vals.
      { apply Forall2_length in Hlocal_vals. rewrite map_length. lia. }
      have Hzip := Forall2_list_to_map_zip (proc_args proc_entry).*1 arg_vals HNoDup Hargs_len.
      have Hm1_none : (@list_to_map lang.var lang.val (gmap lang.var lang.val) _ _
                  (zip (proc_args proc_entry).*1 arg_vals)) !! "#ret_val" = None.
      { apply not_elem_of_list_to_map_1. rewrite (fst_zip _ _ Hargs_len_le).
        intro Hc. apply (Hdisjoint "#ret_val" Hc). exact Hrv_in. }
      rewrite list_to_map_app.
      split; [| split].
      - eapply Forall2_impl; [| exact Hzip].
        intros var val Hlookup. by apply lookup_union_Some_l.
      - intros vname tp Hin.
        have Hpresent := proc_locals_present_typed (proc_local_vars proc_entry)
          local_vals HNoDupLocals Hlocal_vals vname tp Hin.
        destruct Hpresent as [val [Hlk Hty]].
        have Hv_not_arg : vname ∉ (proc_args proc_entry).*1.
        { intro Hc. apply (Hdisjoint vname Hc). apply elem_of_list_fmap. exists (vname, tp). done. }
        have Hm2_none : (@list_to_map lang.var lang.val (gmap lang.var lang.val) _ _
                  (zip (proc_args proc_entry).*1 arg_vals)) !! vname = None.
        { apply not_elem_of_list_to_map_1. rewrite (fst_zip _ _ Hargs_len_le). exact Hv_not_arg. }
        exists val. split; [| exact Hty].
        rewrite lookup_union_r; [| exact Hm2_none]. exact Hlk.
      - rewrite dom_union_L !dom_list_to_map_L (fst_zip _ _ Hargs_len_le) (fst_zip _ _ Hlocals_len_le).
        reflexivity.
    }
    iClear "Hproc_body".
    iApply ("Hproc_body'" with "[Hstk' Hp]") .

    + iFrame.

    + iNext. simpl. iIntros "[%ret_val [%stk_frm'' [Hstk'' [%Hret Hq]]]]".
      iApply wp_lift_atomic_base_step_no_fork; first done.
      iIntros (σ1 ns0 κ κs0 nt0) "Hstate".
      iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D1 [Hgdom1 %HgdomB1]] %Hwf1]]]]".
      iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure2".
      iPoseProof (stack_interp_agreement with "Hstack Hstk''") as "%HstkPure3".
      iPoseProof (stack_lvar_upd σ1 stk_id stk_frm x ret_val with "[Hstk Hstack ]" ) as "Hstk0"; [iFrame | ].

      iDestruct "Hstk0" as ">[Hstk0 Hstack]".

      iModIntro. iSplitR.
      
      * iPureIntro. unfold base_reducible.
        
      exists [], (RTVal LitUnit), (update_lvar σ1 x stk_id ret_val), [].
      apply (ActiveCallStep σ1 stk_id' stk_id x LitUnit stk_frm'' ret_val); try done.

      * iNext. iIntros (e2 σ2 efs H') "Hcred'".
       inversion H'; subst callee_stk_id caller_stk_id σ0 κ e2 σ2 efs.
       assert (callee_stack = stk_frm'') as Hcallee.
       { match goal with
         | Hlookup : stack ?state !! ?callee_id = Some callee_stack |- _ =>
             rewrite HstkPure3 in Hlookup; by injection Hlookup
         end. }
       subst callee_stack.
       assert (ret_val0 = ret_val) as Hretval.
       { match goal with
         | Hlookup : locals ?frame !! "#ret_val" = Some ret_val0 |- _ =>
             rewrite Hret in Hlookup; by injection Hlookup
         end. }
       subst ret_val0.
       iModIntro. iSplitR; try done.
       change (weakestpre.state_interp σ' (S ns0) κs0 nt0) with (ghost_state.state_interp σ').
       unfold ghost_state.state_interp.
       replace (global_heap σ') with (global_heap σ1) by
         (unfold σ', update_lvar; rewrite HstkPure2; done).
       replace (procs σ') with (procs σ1) by
         (unfold σ', update_lvar; rewrite HstkPure2; done).
       iFrame "Hhp Hstack Hproc Hgdom1".
       have Hwf_ret : state_wf σ' := state_wf_update_lvar σ1 x stk_id ret_val Hwf1.
       iFrame (HgdomB1 Hwf_ret).
       simpl. iApply "HΦ". iExists ret_val. iFrame.
  Qed.

  Lemma wp_call_nostore stk_id stk_frm args arg_vals proc proc_entry mask p (q : lang.val -> iProp Σ):
    NoDup (proc_args proc_entry).*1 ->
    NoDup (proc_local_vars proc_entry).*1 ->
    (proc_args proc_entry).*1 ## (proc_local_vars proc_entry).*1 ->
    "#ret_val" ∈ (proc_local_vars proc_entry).*1 ->
    length args = length (proc_entry.(proc_args)) ->
    Forall2 (fun expr val => expr_step expr stk_frm (Val val)) args arg_vals ->
    ▷ (∀ stk_id' stk_frm',
      ⌜Forall2 (fun var val => stk_frm'.(locals) !! var = Some val) proc_entry.(proc_args).*1 arg_vals
       ∧ (∀ v tp, (v, tp) ∈ proc_entry.(proc_local_vars) ->
            ∃ val, stk_frm'.(locals) !! v = Some val ∧ val_has_typ val tp)
       ∧ dom stk_frm'.(locals) = list_to_set proc_entry.(proc_args).*1 ∪ list_to_set (proc_entry.(proc_local_vars)).*1⌝ -∗
        {{{ stack_own[ stk_id', stk_frm' ] ∗ p }}}
            to_rtstmt stk_id' proc_entry.(proc_stmt) @ mask
        {{{ RET (LitUnit); ∃ ret_val stk_frm'', stack_own[ stk_id', stk_frm'' ] ∗ ⌜ (stk_frm''.(locals) !! "#ret_val" = Some ret_val) ⌝ ∗ q ret_val }}} ) -∗

    {{{ stack_own[ stk_id, stk_frm ] ∗ (proc_tbl_chunk proc proc_entry) ∗ p }}}
        RTCallNoStore proc args stk_id @ mask
    {{{ RET LitUnit; ∃ ret_val, stack_own[ stk_id, stk_frm ] ∗ q ret_val ∗ £1}}}.
  Proof.
    intros HNoDup HNoDupLocals Hdisjoint Hrv_in Hlen Harg_evals.

    iIntros "#Hproc_body".
    iIntros (Φ). iModIntro. iIntros "[Hstk [Hproc_tbl Hp]] HΦ".

    iApply wp_lift_base_step; first done.
    iIntros (σ1 ns κ κs nt) "Hstate".
    iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iPoseProof (proc_tbl_interp_agreement with "Hproc Hproc_tbl") as "%HprocPure".
    iApply fupd_mask_intro. { set_solver. }

    iIntros "Hfupd". iSplitR.

    - iPureIntro. unfold base_reducible.

    set new_stk_id := (fresh_stk_id σ1).1.
    set σ' :=  (fresh_stk_id σ1).2.
    set local_vals0 := map (fun decl => canonical_val (snd decl)) proc_entry.(proc_local_vars).
    set new_stk_frame := StackFrame
      (list_to_map (decls_zip_vals proc_entry.(proc_args) arg_vals
                    ++ decls_zip_vals proc_entry.(proc_local_vars) local_vals0)).
    set σ'' := update_stack σ' new_stk_id new_stk_frame.

    set new_stmt := to_rtstmt new_stk_id proc_entry.(proc_stmt).

    exists [], (RTActiveCallNoStore new_stmt new_stk_id), σ'', [].

    apply (RTCallNoStoreStep σ1 stk_id stk_frm proc args arg_vals proc_entry local_vals0); try done.
    apply Forall2_canonical_val_has_typ.

  - iNext. iIntros (e2 σ2 efs) "%H Hcred".
    inversion H; subst proc0 args0 stk_id0 σ1 κ σ2 e2 efs.
    have Hprocedure : procedure = proc_entry.
    { match goal with
      | Hlookup : procs σ !! proc = Some procedure |- _ =>
          rewrite HprocPure in Hlookup; by injection Hlookup
      end. }
    have Hcaller : stk_frm0 = stk_frm.
    { match goal with
      | Hlookup : stack σ !! stk_id = Some stk_frm0 |- _ =>
          rewrite HstkPure in Hlookup; by injection Hlookup
      end. }
    subst procedure stk_frm0.
    have Hlocal_vals : Forall2
        (fun decl val => val_has_typ val (snd decl))
        (proc_local_vars proc_entry) local_vals.
    { match goal with
      | Htyped : Forall2 _ (proc_local_vars proc_entry) local_vals |- _ =>
          exact Htyped
      end. }
    have Harg_steps : Forall2
        (fun expression value => expr_step expression stk_frm (Val value))
        args arg_vals0.
    { match goal with
      | Hsteps : Forall2 _ args arg_vals0 |- _ => exact Hsteps
      end. }
    iMod "Hfupd".
    (* Freshness: the new stack id (Z.of_nat (Z.to_nat σ.(max_stack_id) + 1))
       must not yet be in the stack map. Follows from state_wf's own
       invariant that every allocated stack id is ≤ max_stack_id. *)
    assert (Hfresh_new : stack σ !! Z.of_nat (Z.to_nat σ.(max_stack_id) + 1) = None) by (apply (max_stk_id_fresh _ Hwf)).
    iPoseProof ((stack_new_stk_frm_upd σ new_stk_frame Hfresh_new) with "Hstack") as ">[Hstack' Hstk']".

    simpl; iFrame.
    have Hwf_σ' : state_wf (fresh_stk_id σ).2 := state_wf_fresh_stk_id σ Hwf.
    have Hle_call : (Z.of_nat (Z.to_nat σ.(max_stack_id) + 1) ≤ (fresh_stk_id σ).2.(max_stack_id))%Z.
    { have := swf_max_stk_non_neg Hwf. unfold fresh_stk_id. simpl. lia. }
    have Hrv_new : is_Some (new_stk_frame.(locals) !! "#ret_val").
    { simpl.
      have HNoDupLocalsC : NoDup proc_entry.(proc_local_vars).*1 := HNoDupLocals.
      have Hrv_pair : ∃ tp, ("#ret_val", tp) ∈ proc_entry.(proc_local_vars).
      { apply elem_of_list_fmap_2 in Hrv_in as [[v0 tp0] [Heq Hin]].
        simpl in Heq. subst v0. exists tp0. exact Hin. }
      destruct Hrv_pair as [tp Hrv_pair].
      have Hpresent := proc_locals_present_typed proc_entry.(proc_local_vars)
        local_vals HNoDupLocalsC Hlocal_vals "#ret_val" tp Hrv_pair.
      destruct Hpresent as [val [Hlk _]].
      rewrite list_to_map_app.
      destruct (@list_to_map lang.var lang.val (gmap lang.var lang.val) _ _
                  (zip (map fst (proc_args proc_entry)) arg_vals0) !! "#ret_val") as [rv|] eqn:Hm1.
      - rewrite (lookup_union_Some_l _ _ _ _ Hm1). by eexists.
      - rewrite lookup_union_r; [| exact Hm1]. rewrite Hlk. by eexists.
    }
    have Hwf_call : state_wf (update_stack (fresh_stk_id σ).2 (Z.to_nat σ.(max_stack_id) + 1) new_stk_frame) :=
      state_wf_update_stack (fresh_stk_id σ).2 (Z.to_nat σ.(max_stack_id) + 1) new_stk_frame Hle_call Hrv_new Hwf_σ'.
    iFrame (HgdomB Hwf_call). iModIntro.

    iApply (wp_bind (fill_item (ActiveCallNoStoreCtx (Z.to_nat (max_stack_id σ) + 1))) _ _ _ _).
    set stk_id' := (Z.to_nat (max_stack_id σ) + 1).
    iSpecialize ("Hproc_body" $! stk_id' new_stk_frame).
    iPoseProof ("Hproc_body" with "[%]") as "Hproc_body'".
    { simpl.
      assert (arg_vals0 = arg_vals).
      { apply (Forall2_expr_step_val_unique args stk_frm); try done. }
      subst arg_vals0.
      have Hargs_len : length (proc_args proc_entry).*1 = length arg_vals.
      { apply Forall2_length in Harg_evals. rewrite map_length. rewrite <- Hlen. exact Harg_evals. }
      have Hargs_len_le : length (proc_args proc_entry).*1 ≤ length arg_vals. { lia. }
      have Hlocals_len_le : length (proc_local_vars proc_entry).*1 ≤ length local_vals.
      { apply Forall2_length in Hlocal_vals. rewrite map_length. lia. }
      have Hzip := Forall2_list_to_map_zip (proc_args proc_entry).*1 arg_vals HNoDup Hargs_len.
      have Hm1_none : (@list_to_map lang.var lang.val (gmap lang.var lang.val) _ _
                  (zip (proc_args proc_entry).*1 arg_vals)) !! "#ret_val" = None.
      { apply not_elem_of_list_to_map_1. rewrite (fst_zip _ _ Hargs_len_le).
        intro Hc. apply (Hdisjoint "#ret_val" Hc). exact Hrv_in. }
      rewrite list_to_map_app.
      split; [| split].
      - eapply Forall2_impl; [| exact Hzip].
        intros var val Hlookup. by apply lookup_union_Some_l.
      - intros vname tp Hin.
        have Hpresent := proc_locals_present_typed (proc_local_vars proc_entry)
          local_vals HNoDupLocals Hlocal_vals vname tp Hin.
        destruct Hpresent as [val [Hlk Hty]].
        have Hv_not_arg : vname ∉ (proc_args proc_entry).*1.
        { intro Hc. apply (Hdisjoint vname Hc). apply elem_of_list_fmap. exists (vname, tp). done. }
        have Hm2_none : (@list_to_map lang.var lang.val (gmap lang.var lang.val) _ _
                  (zip (proc_args proc_entry).*1 arg_vals)) !! vname = None.
        { apply not_elem_of_list_to_map_1. rewrite (fst_zip _ _ Hargs_len_le). exact Hv_not_arg. }
        exists val. split; [| exact Hty].
        rewrite lookup_union_r; [| exact Hm2_none]. exact Hlk.
      - rewrite dom_union_L !dom_list_to_map_L (fst_zip _ _ Hargs_len_le) (fst_zip _ _ Hlocals_len_le).
        reflexivity.
    }
    iClear "Hproc_body".
    iApply ("Hproc_body'" with "[Hstk' Hp]") .

    + iFrame.

    + iNext. simpl. iIntros "[%ret_val [%stk_frm'' [Hstk'' [%Hret Hq]]]]".
      iApply (wp_active_call_nostore stk_id' stk_frm'' LitUnit mask
        (stack_own[ stk_id, stk_frm ] ∗ q ret_val) with
        "[$Hstk'' $Hstk $Hq]").
      iNext. iIntros "[[Hstk Hq] Hreturn_credit]".
      iApply "HΦ". iExists ret_val. iFrame.
  Qed.

  Lemma wp_spawn stk_id stk_frm args arg_vals proc proc_entry mask p :
    NoDup (proc_args proc_entry).*1 ->
    NoDup (proc_local_vars proc_entry).*1 ->
    (proc_args proc_entry).*1 ## (proc_local_vars proc_entry).*1 ->
    "#ret_val" ∈ (proc_local_vars proc_entry).*1 ->
    length args = length (proc_entry.(proc_args)) ->
    Forall2 (fun expr val => expr_step expr stk_frm (Val val)) args arg_vals ->
    ▷ (∀ stk_id' stk_frm',
      ⌜Forall2 (fun var val => stk_frm'.(locals) !! var = Some val) proc_entry.(proc_args).*1 arg_vals
       ∧ (∀ v tp, (v, tp) ∈ proc_entry.(proc_local_vars) ->
            ∃ val, stk_frm'.(locals) !! v = Some val ∧ val_has_typ val tp)
       ∧ dom stk_frm'.(locals) = list_to_set proc_entry.(proc_args).*1 ∪ list_to_set (proc_entry.(proc_local_vars)).*1⌝ -∗
        {{{ stack_own[ stk_id', stk_frm' ] ∗ p }}}
            to_rtstmt stk_id' proc_entry.(proc_stmt) @ ⊤
        {{{ RET LitUnit; True }}}) -∗
    {{{ stack_own[ stk_id, stk_frm ] ∗ proc_tbl_chunk proc proc_entry ∗ p }}}
        RTSpawn proc args stk_id @ mask
    {{{ RET LitUnit; stack_own[ stk_id, stk_frm ] ∗ £1 }}}.
  Proof.
    intros HNoDup HNoDupLocals Hdisjoint Hrv_in Hlen Harg_evals.
    iIntros "#Hproc_body" (Phi). iModIntro.
    iIntros "[Hstk [Hproc_tbl Hp]] HΦ".

    iApply wp_lift_base_step; first done.
    iIntros (σ1 ns κ κs nt) "Hstate".
    iDestruct "Hstate" as "[Hhp [Hproc [Hstack [[%D [Hgdom %HgdomB]] %Hwf]]]]".
    iPoseProof (stack_interp_agreement with "Hstack Hstk") as "%HstkPure".
    iPoseProof (proc_tbl_interp_agreement with "Hproc Hproc_tbl") as "%HprocPure".
    iApply fupd_mask_intro. { set_solver. }
    iIntros "Hfupd". iSplitR.
    - iPureIntro. unfold base_reducible.
      set local_vals0 := map (fun decl => canonical_val (snd decl)) proc_entry.(proc_local_vars).
      set new_stk_frame := StackFrame
        (list_to_map (decls_zip_vals proc_entry.(proc_args) arg_vals
                      ++ decls_zip_vals proc_entry.(proc_local_vars) local_vals0)).
      set new_stk_id := (fresh_stk_id σ1).1.
      set σ' := update_stack (fresh_stk_id σ1).2 new_stk_id new_stk_frame.
      exists [], (RTVal LitUnit), σ', [to_rtstmt new_stk_id proc_entry.(proc_stmt)].
      apply (SpawnStep σ1 stk_id stk_frm proc args arg_vals proc_entry local_vals0); try done.
      apply Forall2_canonical_val_has_typ.
    - iNext. iIntros (e2 σ2 efs) "%Hstep Hcred".
      inversion Hstep; subst proc0 args0 stk_id0 σ1 κ σ2 e2 efs.
      have Hprocedure : procedure = proc_entry.
      { match goal with
        | Hlookup : procs σ !! proc = Some procedure |- _ =>
            rewrite HprocPure in Hlookup; by injection Hlookup
        end. }
      have Hcaller : stk_frm0 = stk_frm.
      { match goal with
        | Hlookup : stack σ !! stk_id = Some stk_frm0 |- _ =>
            rewrite HstkPure in Hlookup; by injection Hlookup
        end. }
      subst procedure stk_frm0.
      have Hlocal_vals : Forall2
          (fun decl val => val_has_typ val (snd decl))
          (proc_local_vars proc_entry) local_vals.
      { match goal with
        | Htyped : Forall2 _ (proc_local_vars proc_entry) local_vals |- _ => exact Htyped
        end. }
      iMod "Hfupd".
      assert (Hfresh_new : stack σ !! Z.of_nat (Z.to_nat σ.(max_stack_id) + 1) = None)
        by (apply (max_stk_id_fresh _ Hwf)).
      iPoseProof ((stack_new_stk_frm_upd σ new_stk_frame Hfresh_new) with "Hstack")
        as ">[Hstack' Hstk']".

      simpl; iFrame.
      have Hwf_fresh : state_wf (fresh_stk_id σ).2 := state_wf_fresh_stk_id σ Hwf.
      have Hle_spawn :
          (Z.of_nat (Z.to_nat σ.(max_stack_id) + 1) ≤ (fresh_stk_id σ).2.(max_stack_id))%Z.
      { have := swf_max_stk_non_neg Hwf. unfold fresh_stk_id. simpl. lia. }
      have Hrv_new : is_Some (new_stk_frame.(locals) !! "#ret_val").
      { simpl.
        have Hrv_pair : ∃ tp, ("#ret_val", tp) ∈ proc_entry.(proc_local_vars).
        { apply elem_of_list_fmap_2 in Hrv_in as [[v0 tp0] [Heq Hin]].
          simpl in Heq. subst v0. exists tp0. exact Hin. }
        destruct Hrv_pair as [tp Hrv_pair].
        have Hpresent := proc_locals_present_typed proc_entry.(proc_local_vars)
          local_vals HNoDupLocals Hlocal_vals "#ret_val" tp Hrv_pair.
        destruct Hpresent as [val [Hlk _]].
        rewrite list_to_map_app.
        destruct (@list_to_map lang.var lang.val (gmap lang.var lang.val) _ _
                    (zip (map fst (proc_args proc_entry)) arg_vals0) !! "#ret_val")
          as [rv|] eqn:Hm1.
        - rewrite (lookup_union_Some_l _ _ _ _ Hm1). by eexists.
        - rewrite lookup_union_r; [| exact Hm1]. rewrite Hlk. by eexists. }
      have Hwf_spawn :
          state_wf (update_stack (fresh_stk_id σ).2
            (Z.to_nat σ.(max_stack_id) + 1) new_stk_frame) :=
        state_wf_update_stack (fresh_stk_id σ).2
          (Z.to_nat σ.(max_stack_id) + 1) new_stk_frame Hle_spawn Hrv_new Hwf_fresh.
      iFrame (HgdomB Hwf_spawn). iModIntro.
      iSplitL "Hstk Hcred HΦ".
      + iApply wp_value.
        * done.
        * iApply "HΦ". iFrame.
      + iSpecialize ("Hproc_body" $! (Z.to_nat σ.(max_stack_id) + 1) new_stk_frame).
        iPoseProof ("Hproc_body" with "[%]") as "Hbody".
        { simpl.
          assert (arg_vals0 = arg_vals).
          { apply (Forall2_expr_step_val_unique args stk_frm); try done. }
          subst arg_vals0.
          have Hargs_len : length (proc_args proc_entry).*1 = length arg_vals.
          { apply Forall2_length in Harg_evals. rewrite map_length.
            rewrite <- Hlen. exact Harg_evals. }
          have Hargs_len_le : length (proc_args proc_entry).*1 ≤ length arg_vals by lia.
          have Hlocals_len_le : length (proc_local_vars proc_entry).*1 ≤ length local_vals.
          { apply Forall2_length in Hlocal_vals. rewrite map_length. lia. }
          have Hzip := Forall2_list_to_map_zip
            (proc_args proc_entry).*1 arg_vals HNoDup Hargs_len.
          rewrite list_to_map_app.
          split; [| split].
          - eapply Forall2_impl; [| exact Hzip].
            intros var val Hlookup. by apply lookup_union_Some_l.
          - intros vname tp Hin.
            have Hpresent := proc_locals_present_typed (proc_local_vars proc_entry)
              local_vals HNoDupLocals Hlocal_vals vname tp Hin.
            destruct Hpresent as [val [Hlk Hty]].
            have Hv_not_arg : vname ∉ (proc_args proc_entry).*1.
            { intro Harg. apply (Hdisjoint vname Harg).
              apply elem_of_list_fmap. exists (vname, tp). done. }
            have Hm_none : (@list_to_map lang.var lang.val (gmap lang.var lang.val) _ _
                (zip (proc_args proc_entry).*1 arg_vals)) !! vname = None.
            { apply not_elem_of_list_to_map_1.
              rewrite (fst_zip _ _ Hargs_len_le). exact Hv_not_arg. }
            exists val. split; [| exact Hty].
            rewrite lookup_union_r; [exact Hlk | exact Hm_none].
          - rewrite dom_union_L !dom_list_to_map_L
              (fst_zip _ _ Hargs_len_le) (fst_zip _ _ Hlocals_len_le).
            reflexivity. }
        iSpecialize ("Hbody" $! (fun _ => True%I)).
        iPoseProof ("Hbody" with "[$Hstk' $Hp]") as "Hbodywp".
        iSpecialize ("Hbodywp" with "[]").
        { iNext. iIntros "_". done. }
        iExact "Hbodywp".
  Qed.

  Lemma wp_call_nostore_no_ret stk_id stk_frm args arg_vals proc proc_entry
      mask p (q : lang.val -> iProp Σ) :
    proc_call_layout proc_entry ->
    length args = length (proc_entry.(proc_args)) ->
    Forall2 (fun expr val => expr_step expr stk_frm (Val val)) args arg_vals ->
    ▷ (∀ stk_id' stk_frm',
      ⌜Forall2 (fun var val => stk_frm'.(locals) !! var = Some val)
          proc_entry.(proc_args).*1 arg_vals
       ∧ (∀ v tp, (v, tp) ∈ proc_entry.(proc_local_vars) ->
            ∃ val, stk_frm'.(locals) !! v = Some val ∧ val_has_typ val tp)
       ∧ dom stk_frm'.(locals) = list_to_set proc_entry.(proc_args).*1 ∪
           list_to_set (proc_entry.(proc_local_vars)).*1⌝ -∗
        {{{ stack_own[ stk_id', stk_frm' ] ∗ p }}}
            to_rtstmt stk_id' proc_entry.(proc_stmt) @ mask
        {{{ RET (LitUnit); ∃ ret_val stk_frm'', stack_own[ stk_id', stk_frm'' ] ∗
            ⌜ (stk_frm''.(locals) !! "#ret_val" = Some ret_val) ⌝ ∗
            q ret_val }}} ) -∗
    {{{ stack_own[ stk_id, stk_frm ] ∗ (proc_tbl_chunk proc proc_entry) ∗ p }}}
        RTCallNoStore proc args stk_id @ mask
    {{{ RET LitUnit; ∃ ret_val, stack_own[ stk_id, stk_frm ] ∗ q ret_val ∗ £1}}}.
  Proof.
    intros Hlayout Hlen Harg_evals.
    destruct Hlayout as [HNoDup HNoDupLocals Hdisjoint Hrv_in].
    eapply wp_call_nostore; eauto.
  Qed.

  Lemma wp_spawn_no_ret stk_id stk_frm args arg_vals proc proc_entry mask p :
    proc_call_layout proc_entry ->
    length args = length (proc_entry.(proc_args)) ->
    Forall2 (fun expr val => expr_step expr stk_frm (Val val)) args arg_vals ->
    ▷ (∀ stk_id' stk_frm',
      ⌜Forall2 (fun var val => stk_frm'.(locals) !! var = Some val)
          proc_entry.(proc_args).*1 arg_vals
       ∧ (∀ v tp, (v, tp) ∈ proc_entry.(proc_local_vars) ->
            ∃ val, stk_frm'.(locals) !! v = Some val ∧ val_has_typ val tp)
       ∧ dom stk_frm'.(locals) = list_to_set proc_entry.(proc_args).*1 ∪
           list_to_set (proc_entry.(proc_local_vars)).*1⌝ -∗
        {{{ stack_own[ stk_id', stk_frm' ] ∗ p }}}
            to_rtstmt stk_id' proc_entry.(proc_stmt) @ ⊤
        {{{ RET LitUnit; True }}}) -∗
    {{{ stack_own[ stk_id, stk_frm ] ∗ proc_tbl_chunk proc proc_entry ∗ p }}}
        RTSpawn proc args stk_id @ mask
    {{{ RET LitUnit; stack_own[ stk_id, stk_frm ] ∗ £1 }}}.
  Proof.
    intros Hlayout Hlen Harg_evals.
    destruct Hlayout as [HNoDup HNoDupLocals Hdisjoint Hrv_in].
    eapply wp_spawn; eauto.
  Qed.

End lifting.

End Make.
