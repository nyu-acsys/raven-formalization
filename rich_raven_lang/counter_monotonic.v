(* Example: encoding of test/concurrent/counter/counter_monotonic.rav
   (a monotone counter backed by a simplified Auth[MaxNat]-style resource
   algebra) against rrl_lang.v/lang.v, together with a RavenHoareTriple
   derivation for incr/read. make() is out of scope: counterInv(x) is taken
   as a given precondition, as authorized by the user. *)
From stdpp Require Import gmap.
From raven_iris.simp_raven_lang Require Import lang.
From raven_iris.rich_raven_lang Require Import rrl_lang.

(* ----------------------------------------------------------------------- *)
(* The resource algebra: a plain monotone nat -- comp/frame is max, every
   element is valid, and a frame-preserving update is exactly "go up".
   This is the fragment of Auth[MaxNat] this proof actually needs: nothing
   here ever holds a separate authoritative/fragment split, so there is no
   need to formalize Auth on top of it. *)
Definition MonoNat := nat.

Definition mn_comp (x y : MonoNat) : MonoNat := Nat.max x y.
Definition mn_frame (x y : MonoNat) : MonoNat := x.
Definition mn_valid (x : MonoNat) : Prop := True.
Definition mn_fpuValid (x y : MonoNat) : Prop := x <= y.
(* Total: negative ints (which MonoNat has no natural reading of) fall back
   to ra_id (0), rather than getting stuck. *)
Definition mn_of_int (z : Z) : MonoNat :=
  match z with
  | Z0 => 0%nat
  | Zpos p => Pos.to_nat p
  | Zneg _ => 0%nat
  end.

(* Needed to discharge incr's own Fpu step: incr always moves the counter up
   by exactly 1, so mn_of_int of the new value is always >= mn_of_int of the
   old one -- true across the fallback-to-0 case too (z and z+1 both
   negative, or z negative and z+1 = 0, both give mn_of_int z = 0). *)
Lemma mn_of_int_mono (z : Z) : mn_of_int z <= mn_of_int (z + 1).
Proof.
  unfold mn_of_int.
  destruct z as [ | p | p]; simpl.
  - lia.
  - rewrite Pos.add_1_r. rewrite Pos2Nat.inj_succ. lia.
  - destruct p as [p' | p' | ]; simpl; lia.
Qed.

Lemma mn_fpuAxiom : forall x y : MonoNat, mn_fpuValid x y ->
  mn_valid x /\ mn_valid y /\ forall c, mn_valid (mn_comp x c) -> mn_valid (mn_comp y c).
Proof. intros x y _. repeat split; done. Qed.

Lemma mn_ra_id_comp : forall x, mn_comp 0%nat x = x.
Proof. intros x. unfold mn_comp. lia. Qed.

Global Instance MonoNatRA : ResourceAlgebra MonoNat := {|
  comp := mn_comp;
  frame := mn_frame;
  valid := mn_valid;
  valid_dec := fun x => left I;
  fpuValid := mn_fpuValid;
  fpuValid_dec := fun x y => le_dec x y;
  fpuAxiom := mn_fpuAxiom;
  ra_id := 0%nat;
  ra_id_comp := mn_ra_id_comp;
  ra_of_int := mn_of_int;
|}.

Definition MonoNatPack : RA_Pack := {|
  RA_carrier := MonoNat;
  RA_carrier_eqdec := _;
  RA_carrier_countable := _;
  RA_inst := MonoNatRA;
|}.

Definition h_ra : ra_name := "h_ra".

Axiom ra_map_h_ra : ra_map h_ra = MonoNatPack.

(* Isolates the ra_map h_ra = MonoNatPack rewrite (needed to fall back from
   the RA-generic ra_of_int/fpuValid to their concrete MonoNat definitions)
   into one small lemma, so incr's own Fpu-step proof doesn't have to fight
   the dependent types directly. *)
Lemma h_ra_fpuValid_mono (z1 z2 : Z) :
  z2 = (z1 + 1)%Z ->
  @fpuValid (RA_carrier (ra_map h_ra)) (ra_inst_instance (ra_map h_ra)) (ra_of_int z1) (ra_of_int z2).
Proof.
  intros ->. rewrite ra_map_h_ra. simpl. apply mn_of_int_mono.
Qed.

(* ----------------------------------------------------------------------- *)
(* counterInv(x): exists v: Int, own(x.h, <v as MonoNat>) && own(x.c, v). *)

Definition counterInv_body : assertion :=
  LExists "v" TpInt (LAnd
    (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
    (LOwn (LVar "x") "c" (LVar "v"))).

Definition counterInv_record : InvRecord := Inv ["x"] counterInv_body.

Axiom inv_map_counterInv : inv_map !! "counterInv" = Some counterInv_record.

(* ----------------------------------------------------------------------- *)
(* Program-level setup shared by incr/read's derivations. Moved ahead of the
   entails helpers below: entails is parameterized by sigma (see
   rrl_lang.v), so sigma has to exist before the "entails" local notation
   that partially applies it does. *)

Definition rho : pvar_typs := fun v =>
  match v with
  | "x" => TpLoc
  | "v1" => TpInt
  | "new_v1" => TpInt
  | "res" => TpBool
  | "#ret_val" => TpInt
  | _ => TpUnit
  end.

Definition sigma : lvar_typs := fun lv =>
  match lv with
  | "x" => TpLoc
  | "v" => TpInt (* counterInv_body's own existential witness *)
  | "l_v1" => TpInt
  | "l_new_v1" => TpInt
  | "l_res" => TpBool
  | "l_ret" => TpInt
  | "l_call" => TpUnit
  | _ => TpUnit
  end.

Definition stk0 : stack := {[ "x" := "x" ]}.
Definition cmask : maskAnnot := {[ "counterInv" ]}.

Lemma stk_type_compat_stk0 : stk_type_compat rho sigma stk0.
Proof.
  intros v lv Hv. unfold stk0 in Hv.
  apply lookup_singleton_Some in Hv as [<- <-]. reflexivity.
Qed.

Lemma fresh_lvar_stk0 (lv : lvar) : lv ≠ "x" -> fresh_lvar stk0 lv.
Proof.
  intros Hne v0 Heq. unfold stk0 in Heq.
  apply lookup_singleton_Some in Heq as [<- <-]. exact (Hne eq_refl).
Qed.

(* Extending a well-typed/fresh stack at a new (var, lvar) pair stays
   well-typed/fresh -- reused at every FldRd/Assign/CAS/Call step of
   incr/read's own derivations. *)
Lemma stk_type_compat_extend (stk : stack) (v lv : var) (tp : typ) :
  stk_type_compat rho sigma stk -> rho v = tp -> sigma lv = tp ->
  stk_type_compat rho sigma (<[v:=lv]> stk).
Proof.
  intros Hcompat Hv Hlv v0 lv0 Hv0.
  destruct (decide (v0 = v)) as [->|Hne].
  - rewrite lookup_insert in Hv0. injection Hv0 as <-. rewrite Hv Hlv. reflexivity.
  - rewrite lookup_insert_ne in Hv0; [|congruence]. exact (Hcompat v0 lv0 Hv0).
Qed.

Lemma fresh_lvar_extend (stk : stack) (v lv lv' : var) :
  fresh_lvar stk lv' -> lv ≠ lv' -> fresh_lvar (<[v:=lv]> stk) lv'.
Proof.
  intros Hfresh Hne v0 Heq.
  destruct (decide (v0 = v)) as [->|Hne'].
  - rewrite lookup_insert in Heq. injection Heq as Heq. exact (Hne Heq).
  - rewrite lookup_insert_ne in Heq; [|congruence]. exact (Hfresh v0 Heq).
Qed.

(* ----------------------------------------------------------------------- *)
(* Small reusable helpers for bridging InvAccessBlockRule's fixed
   LAnd (LInv ...) p shape against a bare LInv ... contract.

   entails is parameterized by sigma (rrl_lang.v) so WeakeningRule's own
   entails premises can use env_typ_well_defined; this local notation keeps
   every call site below exactly as it read before that change, always
   instantiated at this file's own sigma. *)
Local Notation entails P Q := (rrl_lang.entails sigma P Q).

Lemma entails_intro P Q :
  (forall stk mp, env_typ_well_defined sigma mp -> trnsl_assertion P stk mp ⊢ trnsl_assertion Q stk mp) -> entails P Q.
Proof.
  intros H stk mp Henv. exists (trnsl_assertion P stk mp), (trnsl_assertion Q stk mp).
  split; [done | split; [done | apply H, Henv]].
Qed.

Lemma entails_and_true_intro P : entails P (LAnd P (LPure True)).
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite trnsl_assertion_and (trnsl_assertion_unfold (LPure True)) /trnsl_assertion_pre /=.
  iIntros "H". iFrame.
Qed.

Lemma entails_and_true_elim P : entails (LAnd P (LPure True)) P.
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite trnsl_assertion_and (trnsl_assertion_unfold (LPure True)) /trnsl_assertion_pre /=.
  iIntros "[H _]". iFrame.
Qed.

(* A small reusable entails algebra, so LAnd-trees can be reshuffled freely
   via WeakeningRule instead of ad hoc per-site proofs. *)
Lemma entails_refl P : entails P P.
Proof. apply entails_intro. intros stk mp Henv. done. Qed.

Lemma entails_trans P Q R : entails P Q -> entails Q R -> entails P R.
Proof.
  intros H1 H2. apply entails_intro. intros stk mp Henv.
  destruct (H1 stk mp Henv) as [P' [Q' [<- [<- H1']]]].
  destruct (H2 stk mp Henv) as [Q'' [R' [Heq [<- H2']]]].
  rewrite Heq in H1'. rewrite H1'. exact H2'.
Qed.

Lemma entails_and_mono P P' Q Q' :
  entails P P' -> entails Q Q' -> entails (LAnd P Q) (LAnd P' Q').
Proof.
  intros H1 H2. apply entails_intro. intros stk mp Henv.
  destruct (H1 stk mp Henv) as [Pp [Pp' [<- [<- H1']]]].
  destruct (H2 stk mp Henv) as [Qp [Qp' [<- [<- H2']]]].
  rewrite !trnsl_assertion_and. iIntros "[HP HQ]". iSplitL "HP".
  - iApply (H1' with "HP").
  - iApply (H2' with "HQ").
Qed.

Lemma entails_and_comm P Q : entails (LAnd P Q) (LAnd Q P).
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite !trnsl_assertion_and. iIntros "[$ $]".
Qed.

Lemma entails_and_assoc_r P Q R : entails (LAnd (LAnd P Q) R) (LAnd P (LAnd Q R)).
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite !trnsl_assertion_and. iIntros "[[$ $] $]".
Qed.

Lemma entails_and_assoc_l P Q R : entails (LAnd P (LAnd Q R)) (LAnd (LAnd P Q) R).
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite !trnsl_assertion_and. iIntros "[$ [$ $]]".
Qed.

Lemma entails_exists_mono (lv : lvar) (t : typ) (A B : assertion) :
  sigma lv = t ->
  entails A B -> entails (LExists lv t A) (LExists lv t B).
Proof.
  intros Hty H. apply entails_intro. intros stk mp Henv.
  rewrite !trnsl_assertion_exists.
  iIntros "[%v' [%Htyp HA]]". iExists v'. iSplitR; [done|].
  have Henv' : env_typ_well_defined sigma (fun y => if (y =? lv)%string then v' else mp y).
  { apply env_typ_well_defined_update; [exact Henv | rewrite Hty; exact Htyp]. }
  destruct (H stk (fun y => if (y =? lv)%string then v' else mp y) Henv') as [P' [Q' [<- [<- Hent]]]].
  iApply (Hent with "HA").
Qed.

(* Re-folds counterInv's own existential witness ("v") from a concretely
   known value v': the ordinary reassembly step every read/CAS/fpu inside
   an open counterInv block needs to restore InvAccessBlockRule's required
   postcondition shape. *)
Lemma trnsl_repack_counterInv (v' : val) (stk : stack_id) (mp : symb_map) :
  trnsl_assertion (LOwn (LVar "x") "c" (LVal v')) stk mp -∗
  trnsl_assertion (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVal v'))) stk mp -∗
  trnsl_assertion counterInv_body stk mp.
Proof.
  unfold counterInv_body.
  rewrite (trnsl_assertion_exists "v" TpInt
    (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
          (LOwn (LVar "x") "c" (LVar "v"))) stk mp).
  rewrite (trnsl_assertion_unfold (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVal v'))))
          /trnsl_assertion_pre /=.
  destruct (Γ (ra_map h_ra)) as [i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] eqn:HΓ.
  iIntros "Hown Hghost".
  iDestruct "Hghost" as (l chunk) "[%Heql [%Heval Hghost]]".
  assert (typ_val_match TpInt v') as Htyp.
  { destruct v' as [b|z| |lc|[r x0]]; simpl in Heval; try discriminate; done. }
  iExists v'. iSplitR; [done|].
  rewrite trnsl_assertion_and.
  rewrite (trnsl_assertion_unfold (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v"))))
          /trnsl_assertion_pre /= HΓ.
  rewrite (trnsl_assertion_unfold (LOwn (LVar "x") "c" (LVar "v"))) /trnsl_assertion_pre /=.
  iEval (rewrite (trnsl_assertion_unfold (LOwn (LVar "x") "c" (LVal v'))) /trnsl_assertion_pre /=) in "Hown".
  simpl.
  iSplitL "Hghost".
  - iExists l, chunk. iFrame "Hghost". iPureIntro. split; [exact Heql | ].
    unfold LExpr_holds in Heql |- *. simpl. exact Heval.
  - iExact "Hown".
Qed.

Lemma entails_repack_counterInv (v' : val) :
  entails
    (LAnd (LOwn (LVar "x") "c" (LVal v'))
          (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVal v'))))
    counterInv_body.
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite trnsl_assertion_and.
  iIntros "[Hown Hghost]".
  iApply (trnsl_repack_counterInv v' stk mp with "Hown Hghost").
Qed.

(* ----------------------------------------------------------------------- *)
(* read(x): requires/ensures counterInv(x). *)

Definition read_body : stmt :=
  Seq
    (InvAccessBlock "counterInv" [Var "x"] (FldRd "v1" (Var "x") "c"))
    (Assign "#ret_val" (Var "v1")).

Definition read_precond : assertion := LInv "counterInv" [LVar "x"].
(* No need to restate the invariant here: LInv's own translation is
   Persistent (see trnsl_assertion_LInv_persistent), so the caller keeps
   their copy from read_precond for free, without it being handed back. *)
Definition read_postcond : assertion := LPure True.

Definition read_record : ProcRecord :=
  Proc [("x", TpLoc)] [("v1", TpInt); ("#ret_val", TpInt)]
    read_precond read_postcond read_body.

Axiom proc_map_read : proc_map !! "read" = Some read_record.

Lemma entails_regroup_pre_sym :
  entails
    (LAnd (LStack stk0) (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
                                     (LOwn (LVar "x") "c" (LVar "v")))
                               (LPure True)))
    (LAnd (LAnd (LStack stk0) (LOwn (LVar "x") "c" (LVar "v")))
          (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v"))) (LPure True))).
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite !trnsl_assertion_and.
  iIntros "[$ [[$ $] $]]".
Qed.

(* LOwn/LGhostOwn's translation only ever consults its chunk expr through
   interp_lexpr, so any two chunks agreeing there translate identically --
   lets a symbolic chunk (e.g. LVar "v") be swapped for the concrete literal
   trnsl_repack_counterInv expects, once its interp is known. *)
Lemma trnsl_assertion_lown_interp_congr (e : LExpr) (fld : fld_name) (chunk1 chunk2 : LExpr) stk mp :
  interp_lexpr chunk1 mp = interp_lexpr chunk2 mp ->
  trnsl_assertion (LOwn e fld chunk1) stk mp ⊢ trnsl_assertion (LOwn e fld chunk2) stk mp.
Proof.
  intros Heq.
  rewrite (trnsl_assertion_unfold (LOwn e fld chunk1)) (trnsl_assertion_unfold (LOwn e fld chunk2))
    /trnsl_assertion_pre /=.
  unfold LExpr_holds. rewrite Heq. done.
Qed.

Lemma trnsl_assertion_lghostown_interp_congr (e : LExpr) (fld : fld_name) (r : ra_name) (chunk1 chunk2 : LExpr) stk mp :
  interp_lexpr chunk1 mp = interp_lexpr chunk2 mp ->
  trnsl_assertion (LGhostOwn e fld r chunk1) stk mp ⊢ trnsl_assertion (LGhostOwn e fld r chunk2) stk mp.
Proof.
  intros Heq.
  rewrite (trnsl_assertion_unfold (LGhostOwn e fld r chunk1)) (trnsl_assertion_unfold (LGhostOwn e fld r chunk2))
    /trnsl_assertion_pre /=.
  destruct (Γ (ra_map r)) as [i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]].
  unfold LExpr_holds. rewrite Heq. done.
Qed.

(* Symbolic counterpart of the old entails_regroup_post: the witness "l_v1"
   equals not a known literal but mp "v" -- trnsl_assertion_mp_irrelevant
   (rather than the old, retired trnsl_assertion_subst_var) is what lets the
   LGhostOwn/LOwn facts, read off at the l_v1-extended map, be carried back
   down to plain mp, matching what trnsl_repack_counterInv expects. *)
Lemma entails_regroup_post_sym (stk1 : stack) :
  entails
    (LAnd (LExists "l_v1" TpInt (LAnd (LStack stk1) (LAnd (LOwn (LVar "x") "c" (LVar "v")) (LExprA (LBinOp EqOp (LVar "l_v1") (LVar "v"))))))
          (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v"))) (LPure True)))
    (LExists "l_v1" TpInt (LAnd (LStack stk1) (LAnd counterInv_body (LPure True)))).
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite trnsl_assertion_and
    (trnsl_assertion_exists "l_v1" TpInt (LAnd (LStack stk1) (LAnd (LOwn (LVar "x") "c" (LVar "v")) (LExprA (LBinOp EqOp (LVar "l_v1") (LVar "v"))))) stk mp)
    (trnsl_assertion_exists "l_v1" TpInt (LAnd (LStack stk1) (LAnd counterInv_body (LPure True))) stk mp).
  iIntros "[[%v'' [%Htyp Hleft]] Hframe]".
  rewrite trnsl_assertion_and.
  iDestruct "Hleft" as "[Hstk1 Hrest]".
  rewrite trnsl_assertion_and.
  iDestruct "Hrest" as "[Hown Heq]".
  iEval (rewrite (trnsl_assertion_unfold (LExprA (LBinOp EqOp (LVar "l_v1") (LVar "v")))) /trnsl_assertion_pre /=) in "Heq".
  iDestruct "Heq" as "%Heq".
  unfold LExpr_holds in Heq. simpl in Heq.
  injection Heq as Heq. apply bool_decide_eq_true in Heq. simpl in Heq. subst v''.
  iEval (rewrite trnsl_assertion_and) in "Hframe".
  iDestruct "Hframe" as "[Hghost _]".
  have HghostFresh : lvar_fresh_in_assertion "l_v1"
    (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v"))).
  { simpl. split; set_solver. }
  iEval (rewrite <- (trnsl_assertion_mp_irrelevant "l_v1"
    (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v"))) (mp "v") stk mp HghostFresh)) in "Hghost".
  iExists (mp "v"). iSplitR; [iPureIntro; exact Htyp|].
  rewrite trnsl_assertion_and.
  iFrame "Hstk1".
  rewrite trnsl_assertion_and.
  set (mp' := (fun y => if (y =? "l_v1")%string then mp "v" else mp y)).
  iDestruct (trnsl_assertion_lown_interp_congr (LVar "x") "c" (LVar "v") (LVal (mp' "v")) stk mp'
    eq_refl with "Hown") as "Hown'".
  iDestruct (trnsl_assertion_lghostown_interp_congr (LVar "x") "h" h_ra
    (LUnOp (RAOfIntOp h_ra) (LVar "v")) (LUnOp (RAOfIntOp h_ra) (LVal (mp' "v"))) stk mp'
    ltac:(simpl; f_equal) with "Hghost") as "Hghost'".
  iSplitL "Hown' Hghost'".
  - iApply (trnsl_repack_counterInv (mp' "v") stk mp' with "Hown' Hghost'").
  - rewrite (trnsl_assertion_unfold (LPure True)) /trnsl_assertion_pre /=. done.
Qed.

(* The single, symbolic derivation the new ExistsElimRule needs for read's
   FldRd, run with counterInv's own existential witness kept as the free
   lvar "v" rather than substituted -- matching the new rule's shape. *)
Lemma read_inner_step_sym :
  RavenHoareTriple rho sigma
    (LAnd (LStack stk0)
          (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
                      (LOwn (LVar "x") "c" (LVar "v")))
                (LPure True)))
      (FldRd "v1" (Var "x") "c") (cmask ∖ {["counterInv"]})
    (LExists "l_v1" TpInt (LAnd (LStack (<["v1":="l_v1"]> stk0)) (LAnd counterInv_body (LPure True)))).
Proof.
  eapply WeakeningRule.
  - eapply FrameRule with
      (r := LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v"))) (LPure True)).
    apply (HeapReadRule rho sigma stk0 (cmask ∖ {["counterInv"]}) "v1" (Var "x") (LVar "v") "c" (LVar "x") "l_v1").
    + reflexivity.
    + reflexivity.
    + apply fresh_lvar_stk0. discriminate.
    + set_solver.
    + exact stk_type_compat_stk0.
  - exact entails_regroup_pre_sym.
  - exact (entails_regroup_post_sym (<["v1":="l_v1"]> stk0)).
Qed.

(* Eliminates counterInv's own existential to reach read_inner_step_sym. Uses
   the new, subst-free ExistsElimRule at the top-level LExists shape, so the
   LStack-fixed precondition is first commuted into that shape via
   WeakeningRule + entails_and_stack_exists_swap. The witness's well-typedness
   ("v" : Int) now comes directly from sigma's own declaration (sigma "v" =
   TpInt), via the rule's new sigma-consistency premise -- no separate
   witness_well_typed proof needed any more. *)
Lemma read_fldrd_block_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack stk0) (LAnd counterInv_body (LPure True)))
      (FldRd "v1" (Var "x") "c") (cmask ∖ {["counterInv"]})
    (LExists "l_v1" TpInt (LAnd (LStack (<["v1":="l_v1"]> stk0)) (LAnd counterInv_body (LPure True)))).
Proof.
  eapply WeakeningRule.
  - apply (ExistsElimRule rho sigma (cmask ∖ {["counterInv"]}) "v" TpInt
      (LAnd (LStack stk0)
            (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
                        (LOwn (LVar "x") "c" (LVar "v")))
                  (LPure True)))
      (FldRd "v1" (Var "x") "c")
      (LExists "l_v1" TpInt (LAnd (LStack (<["v1":="l_v1"]> stk0)) (LAnd counterInv_body (LPure True))))).
    + reflexivity.
    + simpl. right. split.
      { apply fresh_lvar_extend; [apply fresh_lvar_stk0; discriminate | discriminate]. }
      split; [left; reflexivity | exact I].
    + exact read_inner_step_sym.
  - eapply entails_and_stack_exists_swap.
    + apply fresh_lvar_stk0. discriminate.
    + simpl. auto.
  - exact (entails_refl _).
Qed.

(* Wraps the FldRd in the InvAccessBlock; recovers counterInv(x) as a bare
   LInv fact on both sides. *)
Lemma read_invblock_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack stk0) (LInv "counterInv" [LVar "x"]))
      (InvAccessBlock "counterInv" [Var "x"] (FldRd "v1" (Var "x") "c")) cmask
    (LExists "l_v1" TpInt (LAnd (LStack (<["v1":="l_v1"]> stk0)) (LInv "counterInv" [LVar "x"]))).
Proof.
  eapply WeakeningRule.
  - eapply (InvAccessBlockRule rho sigma stk0 (<["v1":="l_v1"]> stk0) cmask "counterInv" [Var "x"]
      (FldRd "v1" (Var "x") "c") counterInv_record (LPure True) (LPure True) "l_v1" TpInt [LVar "x"]).
    + reflexivity.
    + set_solver.
    + exact inv_map_counterInv.
    + reflexivity.
    + exact stk_type_compat_stk0.
    + apply fresh_lvar_stk0. discriminate.
    + simpl. exact read_fldrd_block_step.
  - exact (entails_and_mono _ _ _ _ (entails_refl (LStack stk0)) (entails_and_true_intro (LInv "counterInv" [LVar "x"]))).
  - exact (entails_exists_mono "l_v1" TpInt _ _ eq_refl
      (entails_and_mono _ _ _ _ (entails_refl (LStack (<["v1":="l_v1"]> stk0)))
                         (entails_and_true_elim (LInv "counterInv" [LVar "x"])))).
Qed.

(* Drops a fresh-witness LExists together with the LStack fact riding along
   with it -- the target assertion X doesn't depend on lv, so its own
   translation is unaffected by which witness/stack the existential carries.
   Used to weaken read/incr's own per-step conclusions down to their bare
   procedure-level postcondition, since neither cares about the specific
   fresh lvars intermediate statements happened to introduce. *)
Lemma entails_exists_stack_drop (lv : lvar) (t : typ) (stk : stack) (X : assertion) :
  lvar_fresh_in_assertion lv X ->
  entails (LExists lv t (LAnd (LStack stk) X)) X.
Proof.
  intros Hfresh. apply entails_intro. intros stk' mp Henv.
  rewrite trnsl_assertion_exists.
  iIntros "[%v' [%Htyp H]]".
  rewrite trnsl_assertion_and.
  iDestruct "H" as "[_ H]".
  iEval (rewrite (trnsl_assertion_mp_irrelevant lv X v' stk' mp Hfresh)) in "H".
  iExact "H".
Qed.

(* The single, symbolic derivation for read's Assign "#ret_val" (Var "v1")
   step: VarAssignmentRule + FrameRule (carrying the re-closed counterInv
   fact through), weakened all the way down to the bare procedure
   postcondition -- neither "l_ret" (the assigned value's own fresh lvar)
   nor the intermediate stack state matter beyond this point. *)
Lemma read_assign_inner_step :
  RavenHoareTriple rho sigma
    (LStack (<["v1":="l_v1"]> stk0))
      (Assign "#ret_val" (Var "v1")) cmask
    (LExists "l_ret" TpInt (LAnd (LStack (<["#ret_val":="l_ret"]> (<["v1":="l_v1"]> stk0)))
                            (LExprA (LBinOp EqOp (LVar "l_ret") (LVar "l_v1"))))).
Proof.
  apply (VarAssignmentRule rho sigma (<["v1":="l_v1"]> stk0) cmask "#ret_val" "l_ret" (Var "v1") (LVar "l_v1") TpInt).
  - reflexivity.
  - reflexivity.
  - apply fresh_lvar_extend; [apply fresh_lvar_stk0; discriminate | discriminate].
  - eapply stk_type_compat_extend; [exact stk_type_compat_stk0 | reflexivity | reflexivity].
Qed.

Lemma entails_and_elim_l P Q : entails (LAnd P Q) P.
Proof. apply entails_intro. intros stk mp Henv. rewrite trnsl_assertion_and. iIntros "[$ _]". Qed.

Lemma entails_true_intro X : entails X (LPure True).
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite (trnsl_assertion_unfold (LPure True)) /trnsl_assertion_pre /=.
  iIntros "_". done.
Qed.

(* No need to carry counterInv's own LInv fact (or the intermediate stack
   state / "l_ret" witness) through to the end: read_postcond doesn't
   restate it (LInv is Persistent -- the caller already keeps their own
   copy from read_precond), so the whole thing weakens straight down to
   LPure True. *)
Lemma read_assign_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack (<["v1":="l_v1"]> stk0)) (LInv "counterInv" [LVar "x"]))
      (Assign "#ret_val" (Var "v1")) cmask
    read_postcond.
Proof.
  eapply WeakeningRule.
  - exact read_assign_inner_step.
  - exact (entails_and_elim_l _ _).
  - unfold read_postcond. apply entails_true_intro.
Qed.

(* Combines the InvAccessBlock (read_invblock_step) with the Assign
   (read_assign_step) via SequenceRule: read_assign_step's own precondition
   is exactly what read_invblock_step's postcondition existentially
   provides, once "l_v1" is unwrapped via the new, subst-free
   ExistsElimRule -- straightforward now that read_assign_step's own
   conclusion (read_postcond) doesn't mention "l_v1" at all. *)
Lemma read_body_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack stk0) read_precond)
      read_body cmask
    read_postcond.
Proof.
  unfold read_body, read_precond.
  eapply SequenceRule.
  - exact read_invblock_step.
  - apply (ExistsElimRule rho sigma cmask "l_v1" TpInt
      (LAnd (LStack (<["v1":="l_v1"]> stk0)) (LInv "counterInv" [LVar "x"]))
      (Assign "#ret_val" (Var "v1"))
      read_postcond).
    + reflexivity.
    + unfold read_postcond. exact I.
    + exact read_assign_step.
Qed.

(* ----------------------------------------------------------------------- *)
(* incr(x): requires/ensures counterInv(x). Two separate unfold/fold
   regions, matching the source: the first just reads x.c (identical shape
   to read_body's own InvAccessBlock); the second wraps the CAS together
   with a *conditional* Fpu (only on success) inside one InvAccessBlock --
   both branches fold at the same point right after, since
   InvAccessBlockRule's own conclusion re-closes the invariant
   unconditionally -- and the retry-on-failure recursive call happens
   *after* that fold, outside the invariant's scope, exactly where the
   source calls incr(x) only once already folded back. counterInv's own
   witness ("v", tied to x.c's value while the invariant is open) is
   consumed directly via CASSuccRule/CASFailRule/FPURule's own LOwn/LGhostOwn
   premises -- no separate "v2 :| ..." pick or "assert" needed, matching how
   read never introduced a named witness for its own FldRd either. *)

Definition incr_body : stmt :=
  Seq
    (InvAccessBlock "counterInv" [Var "x"] (FldRd "v1" (Var "x") "c"))
    (Seq
      (Assign "new_v1" (BinOp AddOp (Var "v1") (Val (lang.LitInt 1))))
      (Seq
        (InvAccessBlock "counterInv" [Var "x"]
          (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
               (IfS (Var "res")
                 (Fpu (Var "x") "h" h_ra
                   (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
                 SkipS)))
        (IfS (UnOp NotBoolOp (Var "res")) (Call "call_res" "incr" [Var "x"]) SkipS))).

Definition incr_precond : assertion := LInv "counterInv" [LVar "x"].
(* Same simplification as read_postcond: LInv is Persistent, so the caller
   (including incr's own recursive self-call) keeps their copy for free. *)
Definition incr_postcond : assertion := LPure True.

Definition incr_record : ProcRecord :=
  Proc [("x", TpLoc)] [("v1", TpInt); ("new_v1", TpInt); ("res", TpBool)]
    incr_precond incr_postcond incr_body.

Axiom proc_map_incr : proc_map !! "incr" = Some incr_record.

(* The first InvAccessBlock (FldRd "v1") is byte-for-byte read's own first
   step -- reuse read_invblock_step directly. *)

Lemma incr_assign_inner_step :
  RavenHoareTriple rho sigma
    (LStack (<["v1":="l_v1"]> stk0))
      (Assign "new_v1" (BinOp AddOp (Var "v1") (Val (lang.LitInt 1)))) cmask
    (LExists "l_new_v1" TpInt (LAnd (LStack (<["new_v1":="l_new_v1"]> (<["v1":="l_v1"]> stk0)))
      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))).
Proof.
  apply (VarAssignmentRule rho sigma (<["v1":="l_v1"]> stk0) cmask "new_v1" "l_new_v1"
    (BinOp AddOp (Var "v1") (Val (lang.LitInt 1)))
    (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))) TpInt).
  - reflexivity.
  - reflexivity.
  - apply fresh_lvar_extend; [apply fresh_lvar_stk0; discriminate | discriminate].
  - eapply stk_type_compat_extend; [exact stk_type_compat_stk0 | reflexivity | reflexivity].
Qed.

(* Carries counterInv's LInv fact through the Assign via FrameRule (unlike
   read's own Assign, this one is a *middle* step -- the invariant is still
   needed afterwards for the CAS/FPU block), then regroups the resulting
   LAnd (LExists ...) (LInv ...) back into the LExists-outermost shape via
   entails_exists_and_swap. *)
Lemma incr_assign_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack (<["v1":="l_v1"]> stk0)) (LInv "counterInv" [LVar "x"]))
      (Assign "new_v1" (BinOp AddOp (Var "v1") (Val (lang.LitInt 1)))) cmask
    (LExists "l_new_v1" TpInt (LAnd (LAnd (LStack (<["new_v1":="l_new_v1"]> (<["v1":="l_v1"]> stk0)))
      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))) (LInv "counterInv" [LVar "x"]))).
Proof.
  eapply WeakeningRule.
  - apply (FrameRule rho sigma cmask (Assign "new_v1" (BinOp AddOp (Var "v1") (Val (lang.LitInt 1))))
      (LStack (<["v1":="l_v1"]> stk0))
      (LExists "l_new_v1" TpInt (LAnd (LStack (<["new_v1":="l_new_v1"]> (<["v1":="l_v1"]> stk0)))
        (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
      (LInv "counterInv" [LVar "x"])
      incr_assign_inner_step).
  - exact (entails_refl _).
  - apply entails_exists_and_swap.
    simpl. apply Forall_singleton. set_solver.
Qed.

(* CASRule's postcondition ties its own fresh boolean result lvar to which
   branch of the LIte holds (then_'s tail is "lv = true", else_'s is
   "lv = false"); CondRule, on the IfS reading that same result var, only
   hands back a separately-known "lv = true"/"lv = false" fact, not cond
   itself. These two lemmas bridge the gap: from the LIte plus the known
   boolean tag, recover the corresponding branch by casing on cond directly
   (constructively decidable, since LExpr_holds cond mp reduces to comparing
   two `option val`s) and refuting the other branch's tag via the known one. *)
(* Also hands back cond itself (established internally when deciding which
   branch of the LIte holds), not just A -- needed by callers that must
   relate a fact tied to the LIte's own witness (e.g. a ghost chunk keyed on
   "v") to one tied to whatever the program actually compared against. *)
Lemma entails_ite_bool_true (cond : LExpr) (A B : assertion) (lv : lvar) :
  entails
    (LAnd (LIte cond (LAnd A (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
                      (LAnd B (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false))))))
          (LExprA (LVar lv)))
    (LAnd A (LExprA cond)).
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite trnsl_assertion_and.
  rewrite (trnsl_assertion_ite cond (LAnd A (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
    (LAnd B (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false))))) stk mp).
  rewrite (trnsl_assertion_unfold (LExprA (LVar lv))) /trnsl_assertion_pre /=.
  iIntros "[Hite %Hlv]".
  unfold LExpr_holds in Hlv. simpl in Hlv.
  destruct (interp_lexpr cond mp) as [vc|] eqn:Hcond.
  - destruct (val_beq vc (LitBool true)) eqn:Hvc.
    + unfold val_beq in Hvc. apply bool_decide_eq_true_1 in Hvc. subst vc.
      iDestruct "Hite" as "[Hthen _]".
      iDestruct ("Hthen" with "[]") as "HA".
      { iPureIntro. unfold LExpr_holds. rewrite Hcond. done. }
      iEval (rewrite trnsl_assertion_and) in "HA". iDestruct "HA" as "[HA _]".
      rewrite trnsl_assertion_and (trnsl_assertion_unfold (LExprA cond)) /trnsl_assertion_pre /=.
      iFrame "HA". iPureIntro. unfold LExpr_holds. rewrite Hcond. done.
    + iDestruct "Hite" as "[_ Helse]".
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
  - iDestruct "Hite" as "[_ Helse]".
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
Qed.

Lemma entails_ite_bool_false (cond : LExpr) (A B : assertion) (lv : lvar) :
  entails
    (LAnd (LIte cond (LAnd A (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
                      (LAnd B (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false))))))
          (LExprA (LUnOp NotBoolOp (LVar lv))))
    B.
Proof.
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
  - destruct (val_beq vc (LitBool true)) eqn:Hvc.
    + unfold val_beq in Hvc. apply bool_decide_eq_true_1 in Hvc. subst vc.
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
    + iDestruct "Hite" as "[_ Helse]".
      iDestruct ("Helse" with "[]") as "HB".
      { iPureIntro. unfold LExpr_holds. rewrite Hcond. intros ->.
        unfold val_beq in Hvc. apply bool_decide_eq_false_1 in Hvc. apply Hvc. reflexivity. }
      iEval (rewrite trnsl_assertion_and) in "HB". iDestruct "HB" as "[$ _]".
  - iDestruct "Hite" as "[_ Helse]".
    iDestruct ("Helse" with "[]") as "HB".
    { iPureIntro. unfold LExpr_holds. rewrite Hcond. intros []. }
    iEval (rewrite trnsl_assertion_and) in "HB". iDestruct "HB" as "[$ _]".
Qed.

(* entails_ite_bool_true, with an extra frame fact riding alongside the
   LIte untouched -- lets a caller carry other resources/facts (e.g.
   counterInv's ghost chunk) through the same branch-extraction step. *)
Lemma entails_ite_bool_true_framed (cond : LExpr) (A B FRAME : assertion) (lv : lvar) :
  entails
    (LAnd (LAnd (LIte cond (LAnd A (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
                          (LAnd B (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false))))))
                FRAME)
          (LExprA (LVar lv)))
    (LAnd (LAnd A (LExprA cond)) FRAME).
Proof.
  eapply entails_trans; [exact (entails_and_assoc_r _ _ _) |].
  eapply entails_trans; [apply entails_and_mono; [exact (entails_refl _) | exact (entails_and_comm _ _)] |].
  eapply entails_trans; [exact (entails_and_assoc_l _ _ _) |].
  exact (entails_and_mono _ _ _ _ (entails_ite_bool_true cond A B lv) (entails_refl FRAME)).
Qed.

(* ----------------------------------------------------------------------- *)
(* incr's second InvAccessBlock: CAS(x.c, v1, new_v1) followed by a
   conditional Fpu(x.h, ...) on success, both wrapped in one InvAccessBlock
   -- matching read_inner_step_sym's approach, counterInv's own existential
   witness "v" is kept as a free lvar throughout rather than substituted. *)

Definition incr_stk1 : stack := <["new_v1":="l_new_v1"]> (<["v1":="l_v1"]> stk0).

Lemma stk_type_compat_incr_stk1 : stk_type_compat rho sigma incr_stk1.
Proof.
  unfold incr_stk1.
  eapply stk_type_compat_extend;
    [eapply stk_type_compat_extend; [exact stk_type_compat_stk0 | reflexivity | reflexivity]
    | reflexivity | reflexivity].
Qed.

Lemma fresh_lvar_incr_stk1 (lv : lvar) : lv ≠ "x" -> "l_v1" ≠ lv -> "l_new_v1" ≠ lv -> fresh_lvar incr_stk1 lv.
Proof.
  intros Hx Hv1 Hnv1. unfold incr_stk1.
  apply fresh_lvar_extend; [apply fresh_lvar_extend; [apply fresh_lvar_stk0; exact Hx | exact Hv1] | exact Hnv1].
Qed.

(* The CAS itself, framing counterInv's GhostOwn fact -- together with the
   "l_new_v1 = l_v1 + 1" arithmetic fact established by incr_assign_step,
   needed later to discharge Fpu's own fpuValid premise -- through unchanged
   (the Fpu that actually updates the ghost chunk comes later, only on
   success). *)
Lemma incr_cas_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack incr_stk1)
          (LAnd (LOwn (LVar "x") "c" (LVar "v"))
                (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
                      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))))
      (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1")) (cmask ∖ {["counterInv"]})
    (LExists "l_res" TpBool (LAnd
      (LAnd (LStack (<["res":="l_res"]> incr_stk1))
        (LIte (LBinOp EqOp (LVar "v") (LVar "l_v1"))
          (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
          (LAnd (LOwn (LVar "x") "c" (LVar "v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false)))))))
      (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
            (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))).
Proof.
  eapply WeakeningRule.
  - eapply FrameRule with (r := LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
                                      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))).
    apply (CASRule rho sigma incr_stk1 (cmask ∖ {["counterInv"]}) "res" (Var "x") "c" (Var "v1") (Var "new_v1")
      "l_res" (LVar "x") (LVar "l_v1") (LVar "l_new_v1") (LVar "v")).
    + apply fresh_lvar_incr_stk1; discriminate.
    + reflexivity.
    + exists TpInt. reflexivity.
    + exists TpInt. reflexivity.
    + set_solver.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact stk_type_compat_incr_stk1.
  - exact (entails_and_assoc_l _ _ _).
  - apply entails_exists_and_swap.
    simpl. split; [split; set_solver | set_solver].
Qed.

Definition incr_stk2 : stack := <["res":="l_res"]> incr_stk1.

Lemma stk_type_compat_incr_stk2 : stk_type_compat rho sigma incr_stk2.
Proof.
  unfold incr_stk2. eapply stk_type_compat_extend; [exact stk_type_compat_incr_stk1 | reflexivity | reflexivity].
Qed.

Lemma fresh_lvar_incr_stk2 (lv : lvar) :
  lv ≠ "x" -> "l_v1" ≠ lv -> "l_new_v1" ≠ lv -> "l_res" ≠ lv -> fresh_lvar incr_stk2 lv.
Proof.
  intros Hx Hv1 Hnv1 Hres. unfold incr_stk2.
  apply fresh_lvar_extend; [apply fresh_lvar_incr_stk1; done | exact Hres].
Qed.

(* Bridges the "l_new_v1 = l_v1 + 1" arithmetic fact (established by
   incr_assign_step) into the RAFpuValidOp fact Fpu's own precondition
   needs. *)
Lemma incr_fpu_pre_entails :
  entails
    (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")))
          (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))
    (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")))
          (LExprA (LBinOp RAFpuValidOp (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")) (LUnOp (RAOfIntOp h_ra) (LVar "l_new_v1"))))).
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite trnsl_assertion_and.
  rewrite (trnsl_assertion_unfold (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))
    /trnsl_assertion_pre /=.
  rewrite trnsl_assertion_and.
  rewrite (trnsl_assertion_unfold (LExprA (LBinOp RAFpuValidOp (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")) (LUnOp (RAOfIntOp h_ra) (LVar "l_new_v1")))))
    /trnsl_assertion_pre /=.
  iIntros "[$ %Harith]".
  unfold LExpr_holds in Harith. simpl in Harith.
  destruct (mp "l_v1") as [b|z1| |l|p] eqn:Hv1val; try (exfalso; exact Harith).
  injection Harith as Harith.
  unfold val_beq in Harith. apply bool_decide_eq_true_1 in Harith.
  iPureIntro. unfold LExpr_holds.
  rewrite (interp_lexpr_ra_fpuvalid h_ra (ra_of_int z1) (ra_of_int (z1 + 1)%Z)
    (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")) (LUnOp (RAOfIntOp h_ra) (LVar "l_new_v1")) mp).
  - simpl. f_equal. apply bool_decide_eq_true_2. apply h_ra_fpuValid_mono. reflexivity.
  - simpl. rewrite Hv1val. reflexivity.
  - simpl. rewrite Harith. reflexivity.
Qed.

(* incr's Fpu step: bumps the ghost chunk from "l_v1" to "l_new_v1". *)
Lemma incr_fpu_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack incr_stk2)
          (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")))
                (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
      (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
      (cmask ∖ {["counterInv"]})
    (LAnd (LStack incr_stk2) (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_new_v1")))).
Proof.
  eapply WeakeningRule.
  - apply (FPURule rho sigma incr_stk2 (cmask ∖ {["counterInv"]})
      (Var "x") (LVar "x") "h" h_ra
      (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1"))
      (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")) (LUnOp (RAOfIntOp h_ra) (LVar "l_new_v1"))).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact stk_type_compat_incr_stk2.
  - exact (entails_and_mono _ _ _ _ (entails_refl _) incr_fpu_pre_entails).
  - exact (entails_refl _).
Qed.

(* Frames the CAS's own LOwn(x.c, l_new_v1) fact through the Fpu unchanged --
   needed afterward to repack counterInv with witness "l_new_v1" once the
   ghost chunk has also been bumped. *)
Lemma incr_fpu_step_framed :
  RavenHoareTriple rho sigma
    (LAnd (LStack incr_stk2)
          (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")))
                      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))
                (LOwn (LVar "x") "c" (LVar "l_new_v1"))))
      (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
      (cmask ∖ {["counterInv"]})
    (LAnd (LStack incr_stk2)
          (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_new_v1")))
                (LOwn (LVar "x") "c" (LVar "l_new_v1")))).
Proof.
  eapply WeakeningRule.
  - eapply FrameRule with (r := LOwn (LVar "x") "c" (LVar "l_new_v1")). exact incr_fpu_step.
  - exact (entails_and_assoc_l _ _ _).
  - exact (entails_and_assoc_r _ _ _).
Qed.

(* Repacks counterInv_body from the post-Fpu state, with "l_new_v1" as the
   witness -- ghost chunk and heap chunk now agree again. Mirrors
   entails_regroup_post_sym's own use of trnsl_repack_counterInv, minus the
   LExists/map-update machinery (no fresh witness is being introduced here,
   "l_new_v1" is already the natural map). *)
Lemma incr_repack_post_l_new_v1 :
  entails
    (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_new_v1")))
          (LOwn (LVar "x") "c" (LVar "l_new_v1")))
    (LAnd counterInv_body (LPure True)).
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite trnsl_assertion_and.
  iIntros "[Hghost Hown]".
  rewrite trnsl_assertion_and (trnsl_assertion_unfold (LPure True)) /trnsl_assertion_pre /=.
  set (v' := mp "l_new_v1").
  iDestruct (trnsl_assertion_lown_interp_congr (LVar "x") "c" (LVar "l_new_v1") (LVal v') stk mp eq_refl with "Hown") as "Hown'".
  iDestruct (trnsl_assertion_lghostown_interp_congr (LVar "x") "h" h_ra
    (LUnOp (RAOfIntOp h_ra) (LVar "l_new_v1")) (LUnOp (RAOfIntOp h_ra) (LVal v')) stk mp
    ltac:(simpl; f_equal) with "Hghost") as "Hghost'".
  iSplitL.
  - iApply (trnsl_repack_counterInv v' stk mp with "Hown' Hghost'").
  - done.
Qed.

(* Rewrites counterInv's ghost chunk from "v" to "l_v1" using the CAS-success
   equality extracted from CASRule's own LIte (via entails_ite_bool_true). *)
Lemma incr_ghostown_v_to_l_v1 :
  entails
    (LAnd (LExprA (LBinOp EqOp (LVar "v") (LVar "l_v1")))
          (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v"))))
    (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_v1"))).
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite trnsl_assertion_and (trnsl_assertion_unfold (LExprA (LBinOp EqOp (LVar "v") (LVar "l_v1")))) /trnsl_assertion_pre /=.
  iIntros "[%Heq Hghost]".
  unfold LExpr_holds in Heq. simpl in Heq.
  injection Heq as Heq. unfold val_beq in Heq. apply bool_decide_eq_true_1 in Heq.
  iApply (trnsl_assertion_lghostown_interp_congr (LVar "x") "h" h_ra
    (LUnOp (RAOfIntOp h_ra) (LVar "v")) (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")) stk mp
    ltac:(simpl; rewrite Heq; reflexivity) with "Hghost").
Qed.

(* Regroups the pieces entails_ite_bool_true_framed hands back -- A (=LOwn
   x.c l_new_v1), the CAS-success equality, GhostOwn(v), and the arithmetic
   fact -- into incr_fpu_step_framed's own expected precondition shape,
   rewriting GhostOwn(v) to GhostOwn(l_v1) along the way. *)
Lemma incr_true_branch_regroup :
  entails
    (LAnd (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "v") (LVar "l_v1"))))
          (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
                (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
    (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")))
                (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))
          (LOwn (LVar "x") "c" (LVar "l_new_v1"))).
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite !trnsl_assertion_and.
  iIntros "[[HA Hcond] [Hghost Harith]]".
  destruct (incr_ghostown_v_to_l_v1 stk mp Henv) as [P' [Q' [<- [<- Hent]]]].
  rewrite trnsl_assertion_and in Hent.
  iDestruct (Hent with "[Hcond Hghost]") as "Hghost'"; [iFrame|].
  iFrame.
Qed.

(* The IfS's "res = true" branch (the Fpu), fully composed: extract, rewrite,
   apply Fpu, repack counterInv. *)
Lemma incr_true_branch_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack incr_stk2)
      (LAnd (LAnd (LIte (LBinOp EqOp (LVar "v") (LVar "l_v1"))
                     (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                     (LAnd (LOwn (LVar "x") "c" (LVar "v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false))))))
                   (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
                         (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
            (LExprA (LVar "l_res"))))
      (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
      (cmask ∖ {["counterInv"]})
    (LAnd (LStack incr_stk2) (LAnd counterInv_body (LPure True))).
Proof.
  eapply WeakeningRule.
  - exact incr_fpu_step_framed.
  - apply entails_and_mono; [exact (entails_refl _) |].
    eapply entails_trans; [exact (entails_ite_bool_true_framed _ _ _ _ _) | exact incr_true_branch_regroup].
  - apply entails_and_mono; [exact (entails_refl _) | exact incr_repack_post_l_new_v1].
Qed.

(* entails_ite_bool_false, with an extra frame fact riding alongside --
   mirrors entails_ite_bool_true_framed. *)
Lemma entails_ite_bool_false_framed (cond : LExpr) (A B FRAME : assertion) (lv : lvar) :
  entails
    (LAnd (LAnd (LIte cond (LAnd A (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
                          (LAnd B (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false))))))
                FRAME)
          (LExprA (LUnOp NotBoolOp (LVar lv))))
    (LAnd B FRAME).
Proof.
  eapply entails_trans; [exact (entails_and_assoc_r _ _ _) |].
  eapply entails_trans; [apply entails_and_mono; [exact (entails_refl _) | exact (entails_and_comm _ _)] |].
  eapply entails_trans; [exact (entails_and_assoc_l _ _ _) |].
  exact (entails_and_mono _ _ _ _ (entails_ite_bool_false cond A B lv) (entails_refl FRAME)).
Qed.

(* Repacks counterInv_body with "v" (unchanged -- CAS failed, nothing was
   written) as the witness. *)
Lemma incr_repack_post_v :
  entails
    (LAnd (LOwn (LVar "x") "c" (LVar "v"))
          (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v"))))
    (LAnd counterInv_body (LPure True)).
Proof.
  apply entails_intro. intros stk mp Henv.
  rewrite trnsl_assertion_and.
  iIntros "[Hown Hghost]".
  rewrite trnsl_assertion_and (trnsl_assertion_unfold (LPure True)) /trnsl_assertion_pre /=.
  set (v' := mp "v").
  iDestruct (trnsl_assertion_lown_interp_congr (LVar "x") "c" (LVar "v") (LVal v') stk mp eq_refl with "Hown") as "Hown'".
  iDestruct (trnsl_assertion_lghostown_interp_congr (LVar "x") "h" h_ra
    (LUnOp (RAOfIntOp h_ra) (LVar "v")) (LUnOp (RAOfIntOp h_ra) (LVal v')) stk mp
    ltac:(simpl; f_equal) with "Hghost") as "Hghost'".
  iSplitL.
  - iApply (trnsl_repack_counterInv v' stk mp with "Hown' Hghost'").
  - done.
Qed.

(* The IfS's "res = false" branch (SkipS): extract, drop the now-unused
   arithmetic fact, repack counterInv unchanged. *)
Lemma incr_false_branch_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack incr_stk2)
      (LAnd (LAnd (LIte (LBinOp EqOp (LVar "v") (LVar "l_v1"))
                     (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                     (LAnd (LOwn (LVar "x") "c" (LVar "v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false))))))
                   (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
                         (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
            (LExprA (LUnOp NotBoolOp (LVar "l_res")))))
      SkipS
      (cmask ∖ {["counterInv"]})
    (LAnd (LStack incr_stk2) (LAnd counterInv_body (LPure True))).
Proof.
  eapply WeakeningRule.
  - apply (SkipRule rho sigma incr_stk2 (cmask ∖ {["counterInv"]})
      (LAnd (LOwn (LVar "x") "c" (LVar "v")) (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v"))))).
    exact stk_type_compat_incr_stk2.
  - apply entails_and_mono; [exact (entails_refl _) |].
    eapply entails_trans; [exact (entails_ite_bool_false_framed _ _ _ _ _) |].
    apply entails_and_mono; [exact (entails_refl _) | exact (entails_and_elim_l _ _)].
  - apply entails_and_mono; [exact (entails_refl _) | exact incr_repack_post_v].
Qed.

(* The IfS(res, Fpu, Skip) as a whole. *)
Lemma incr_ifs_res_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack incr_stk2)
          (LAnd (LIte (LBinOp EqOp (LVar "v") (LVar "l_v1"))
                   (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                   (LAnd (LOwn (LVar "x") "c" (LVar "v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false))))))
                (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
                      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))))
      (IfS (Var "res")
        (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
        SkipS)
      (cmask ∖ {["counterInv"]})
    (LAnd (LStack incr_stk2) (LAnd counterInv_body (LPure True))).
Proof.
  apply (CondRule rho sigma incr_stk2 (cmask ∖ {["counterInv"]})
    (Var "res")
    (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
    SkipS
    (LAnd (LIte (LBinOp EqOp (LVar "v") (LVar "l_v1"))
             (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
             (LAnd (LOwn (LVar "x") "c" (LVar "v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false))))))
          (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
                (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
    (LAnd (LStack incr_stk2) (LAnd counterInv_body (LPure True)))
    (LVar "l_res")).
  - reflexivity.
  - reflexivity.
  - exact stk_type_compat_incr_stk2.
  - exact incr_true_branch_step.
  - exact incr_false_branch_step.
Qed.

(* Wraps incr_ifs_res_step's conclusion in a fresh existential over "l_res"
   itself: sound because entails is now parameterized by sigma, giving
   entails_exists_intro access to Henv (via env_typ_well_defined) to justify
   the witness v' := mp "l_res" against sigma "l_res" = TpBool -- an
   unconditional-over-mp entails could never do this (see entails_exists_intro
   in rrl_lang.v). This existential re-uses "l_res" itself as the bound
   name, which is what makes it possible to eliminate "l_res" again just
   below via ExistsElimRule: LExists's own freshness check is trivially true
   when the queried lvar equals the binder (shadowing), regardless of
   whether the body underneath genuinely mentions it (incr_stk2 does). *)
Lemma incr_ifs_res_step_wrapped :
  RavenHoareTriple rho sigma
    (LAnd (LStack incr_stk2)
          (LAnd (LIte (LBinOp EqOp (LVar "v") (LVar "l_v1"))
                   (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                   (LAnd (LOwn (LVar "x") "c" (LVar "v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false))))))
                (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
                      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))))
      (IfS (Var "res")
        (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
        SkipS)
      (cmask ∖ {["counterInv"]})
    (LExists "l_res" TpBool (LAnd (LStack incr_stk2) (LAnd counterInv_body (LPure True)))).
Proof.
  eapply WeakeningRule.
  - exact incr_ifs_res_step.
  - exact (entails_refl _).
  - exact (entails_exists_intro sigma "l_res" TpBool _ eq_refl).
Qed.

(* Combines incr_cas_step with incr_ifs_res_step_wrapped via SequenceRule:
   incr_cas_step's own postcond (LExists "l_res" TpBool ...) IS the
   precondition ExistsElimRule needs to unwrap "l_res" as a free lvar for
   the IfS's own derivation, reaching incr_ifs_res_step_wrapped's
   "l_res"-wrapped conclusion directly (no separate unwrap-then-rewrap step
   needed: the wrapping already happened inside incr_ifs_res_step_wrapped
   itself, via entails_exists_intro). *)
Lemma incr_invblock2_inner_sym :
  RavenHoareTriple rho sigma
    (LAnd (LStack incr_stk1)
          (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
                      (LOwn (LVar "x") "c" (LVar "v")))
                (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
      (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
           (IfS (Var "res")
             (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
             SkipS))
      (cmask ∖ {["counterInv"]})
    (LExists "l_res" TpBool (LAnd (LStack incr_stk2) (LAnd counterInv_body (LPure True)))).
Proof.
  eapply SequenceRule.
  - eapply WeakeningRule.
    + exact incr_cas_step.
    + apply entails_and_mono; [exact (entails_refl _) |].
      eapply entails_trans.
      * apply entails_and_mono; [exact (entails_and_comm _ _) | exact (entails_refl _)].
      * exact (entails_and_assoc_r _ _ _).
    + exact (entails_refl _).
  - apply (ExistsElimRule rho sigma (cmask ∖ {["counterInv"]}) "l_res" TpBool
      (LAnd (LAnd (LStack incr_stk2)
               (LIte (LBinOp EqOp (LVar "v") (LVar "l_v1"))
                  (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                  (LAnd (LOwn (LVar "x") "c" (LVar "v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false)))))))
            (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
                  (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
      (IfS (Var "res")
        (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
        SkipS)
      (LExists "l_res" TpBool (LAnd (LStack incr_stk2) (LAnd counterInv_body (LPure True))))).
    + reflexivity.
    + simpl. left. reflexivity.
    + eapply WeakeningRule.
      * exact incr_ifs_res_step_wrapped.
      * exact (entails_and_assoc_r _ _ _).
      * exact (entails_refl _).
Qed.

(* Wraps incr_invblock2_inner_sym in InvAccessBlockRule -- mirrors
   read_invblock_step, except the frame p carried in is the arithmetic fact
   (not LPure True), matching what incr_invblock2_inner_sym's own
   precondition already needs, and q is LPure True (nothing survives
   outward, matching how the frame was already dropped inside
   incr_true_branch_step/incr_false_branch_step's own repack steps). *)

(* Eliminates counterInv's own "v" existential to reach
   incr_invblock2_inner_sym -- mirrors read_fldrd_block_step exactly. *)
Lemma incr_invblock2_v_elim_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack incr_stk1)
          (LAnd counterInv_body
                (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
      (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
           (IfS (Var "res")
             (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
             SkipS))
      (cmask ∖ {["counterInv"]})
    (LExists "l_res" TpBool (LAnd (LStack incr_stk2) (LAnd counterInv_body (LPure True)))).
Proof.
  eapply WeakeningRule.
  - apply (ExistsElimRule rho sigma (cmask ∖ {["counterInv"]}) "v" TpInt
      (LAnd (LStack incr_stk1)
            (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "v")))
                        (LOwn (LVar "x") "c" (LVar "v")))
                  (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
      (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
           (IfS (Var "res")
             (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
             SkipS))
      (LExists "l_res" TpBool (LAnd (LStack incr_stk2) (LAnd counterInv_body (LPure True))))).
    + reflexivity.
    + simpl. right. split.
      { apply fresh_lvar_incr_stk2; discriminate. }
      split; [left; reflexivity | exact I].
    + exact incr_invblock2_inner_sym.
  - eapply entails_and_stack_exists_swap.
    + apply fresh_lvar_incr_stk1; discriminate.
    + simpl. set_solver.
  - exact (entails_refl _).
Qed.

Lemma incr_invblock2_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack incr_stk1)
          (LAnd (LInv "counterInv" [LVar "x"])
                (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
      (InvAccessBlock "counterInv" [Var "x"]
        (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
             (IfS (Var "res")
               (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
               SkipS)))
      cmask
    (LExists "l_res" TpBool (LAnd (LStack incr_stk2) (LAnd (LInv "counterInv" [LVar "x"]) (LPure True)))).
Proof.
  eapply (InvAccessBlockRule rho sigma incr_stk1 incr_stk2 cmask "counterInv" [Var "x"]
    (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
         (IfS (Var "res")
           (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
           SkipS))
    counterInv_record
    (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))
    (LPure True) "l_res" TpBool [LVar "x"]).
  - reflexivity.
  - set_solver.
  - exact inv_map_counterInv.
  - reflexivity.
  - exact stk_type_compat_incr_stk1.
  - apply fresh_lvar_incr_stk1; discriminate.
  - rewrite (subst_id_map ["x"] counterInv_body). exact incr_invblock2_v_elim_step.
Qed.

(* ----------------------------------------------------------------------- *)
(* incr's retry: IfS(!res, Call incr, Skip), outside the invariant scope. *)

(* The retry branch: ProcCallRuleRet's own precondition doesn't want the
   guard fact (LExprA (!l_res)) at all, and its conclusion -- whatever
   fresh stack/result it produces -- is trivially weakened to LPure True
   via entails_true_intro, since incr_postcond doesn't care what "call_res"
   came back as. *)
Lemma incr_retry_true_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack incr_stk2) (LAnd (LInv "counterInv" [LVar "x"]) (LExprA (LUnOp NotBoolOp (LVar "l_res")))))
      (Call "call_res" "incr" [Var "x"]) cmask
    (LPure True).
Proof.
  eapply WeakeningRule.
  - apply (ProcCallRuleRet rho sigma incr_stk2 cmask "call_res" "incr" [Var "x"] [LVar "x"] "l_call" incr_record).
    + apply fresh_lvar_incr_stk2; discriminate.
    + exact proc_map_incr.
    + reflexivity.
    + reflexivity.
    + exact stk_type_compat_incr_stk2.
  - apply entails_and_mono; [exact (entails_refl _) |].
    eapply entails_trans; [exact (entails_and_elim_l _ _) |].
    unfold incr_precond. simpl. exact (entails_refl _).
  - exact (entails_true_intro _).
Qed.

Lemma incr_retry_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack incr_stk2) (LInv "counterInv" [LVar "x"]))
      (IfS (UnOp NotBoolOp (Var "res")) (Call "call_res" "incr" [Var "x"]) SkipS)
      cmask
    incr_postcond.
Proof.
  unfold incr_postcond.
  apply (CondRule rho sigma incr_stk2 cmask
    (UnOp NotBoolOp (Var "res"))
    (Call "call_res" "incr" [Var "x"])
    SkipS
    (LInv "counterInv" [LVar "x"])
    (LPure True)
    (LUnOp NotBoolOp (LVar "l_res"))).
  - reflexivity.
  - reflexivity.
  - exact stk_type_compat_incr_stk2.
  - exact incr_retry_true_step.
  - eapply WeakeningRule.
    + apply (SkipRule rho sigma incr_stk2 cmask (LInv "counterInv" [LVar "x"])).
      exact stk_type_compat_incr_stk2.
    + apply entails_and_mono; [exact (entails_refl _) | exact (entails_and_elim_l _ _)].
    + exact (entails_true_intro _).
Qed.

(* ----------------------------------------------------------------------- *)
(* incr's full body: nested SequenceRule/ExistsElimRule chaining the four
   pieces, mirroring read_body_step exactly, just three stages deeper. *)
Lemma incr_body_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack stk0) incr_precond)
      incr_body cmask
    incr_postcond.
Proof.
  unfold incr_body, incr_precond.
  eapply SequenceRule.
  - exact read_invblock_step.
  - apply (ExistsElimRule rho sigma cmask "l_v1" TpInt
      (LAnd (LStack (<["v1":="l_v1"]> stk0)) (LInv "counterInv" [LVar "x"]))
      (Seq (Assign "new_v1" (BinOp AddOp (Var "v1") (Val (lang.LitInt 1))))
           (Seq (InvAccessBlock "counterInv" [Var "x"]
                  (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
                       (IfS (Var "res")
                         (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
                         SkipS)))
                (IfS (UnOp NotBoolOp (Var "res")) (Call "call_res" "incr" [Var "x"]) SkipS)))
      incr_postcond).
    + reflexivity.
    + unfold incr_postcond. exact I.
    + eapply SequenceRule.
      * exact incr_assign_step.
      * apply (ExistsElimRule rho sigma cmask "l_new_v1" TpInt
          (LAnd (LAnd (LStack incr_stk1) (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))
                (LInv "counterInv" [LVar "x"]))
          (Seq (InvAccessBlock "counterInv" [Var "x"]
                 (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
                      (IfS (Var "res")
                        (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
                        SkipS)))
               (IfS (UnOp NotBoolOp (Var "res")) (Call "call_res" "incr" [Var "x"]) SkipS))
          incr_postcond).
        -- reflexivity.
        -- unfold incr_postcond. exact I.
        -- eapply SequenceRule.
           ++ eapply WeakeningRule.
              ** exact incr_invblock2_step.
              ** eapply entails_trans.
                 --- exact (entails_and_assoc_r _ _ _).
                 --- apply entails_and_mono; [exact (entails_refl _) | exact (entails_and_comm _ _)].
              ** exact (entails_refl _).
           ++ apply (ExistsElimRule rho sigma cmask "l_res" TpBool
                 (LAnd (LStack incr_stk2) (LAnd (LInv "counterInv" [LVar "x"]) (LPure True)))
                 (IfS (UnOp NotBoolOp (Var "res")) (Call "call_res" "incr" [Var "x"]) SkipS)
                 incr_postcond).
                --- reflexivity.
                --- unfold incr_postcond. exact I.
                --- eapply WeakeningRule.
                    +++ exact incr_retry_step.
                    +++ apply entails_and_mono; [exact (entails_refl _) | exact (entails_and_true_elim _)].
                    +++ exact (entails_refl _).
Qed.
