(* Example: encoding of test/concurrent/counter/counter_monotonic.rav
   (a monotone counter backed by a simplified Auth[MaxNat]-style resource
   algebra) against rrl_lang.v/lang.v, together with a RavenHoareTriple
   derivation for incr/read/make. *)
From stdpp Require Import gmap namespaces.
From raven_iris.simp_raven_lang Require Import lang.
From raven_iris.rich_raven_lang Require Import rrl_lang.
Require Import Coq.Logic.FunctionalExtensionality.

(* Sigma/Gs/I (hence invTokenG's own inG obligation) are still abstract
   Context declarations throughout rrl_lang.v -- picking a concrete Sigma
   is Step 5's job (the adequacy wrapper), not this file's. Everything
   else this file needs (Program, GhostConfig) is concrete, defined below
   once read/incr/make/counterInv's own records exist (see RProg/G,
   after make_record). *)
Context `{!invTokenG rrl_lang.Σ}.

(* ----------------------------------------------------------------------- *)
(* The resource algebra: a plain monotone nat -- comp/frame is max, and a
   frame-preserving update is exactly "go up". This is the fragment of
   Auth[MaxNat] this proof actually needs: nothing here ever holds a
   separate authoritative/fragment split, so there is no need to formalize
   Auth on top of it.
   Carrier is [option nat], not [nat]: the restored ResourceAlgebra axioms
   (see local/parameters-redesign.md, Step 0) require [frame] to actually
   reject the [x < y] case via [valid], and plain [nat] has no element to
   reject with. [None] is that invalid sentinel -- mirrors
   lib/library/resource_algebra.rav's own [MaxNat] module, which uses
   [Int]'s [-1] as its sentinel, filtered out by [valid(n) := n >= 0]. *)
Definition MonoNat := option nat.

Definition mn_comp (x y : MonoNat) : MonoNat :=
  match x, y with
  | Some a, Some b => Some (Nat.max a b)
  | _, _ => None
  end.

(* [y = id]: pass [x] through unchanged, valid or not (mirrors [comp]'s own
   id-absorption, and gives [frame_id] for free). Otherwise [x]/[y] must
   both be valid and [x >= y], else the result is invalid ([None]). *)
Definition mn_frame (x y : MonoNat) : MonoNat :=
  match y with
  | Some 0%nat => x
  | Some n =>
      match x with
      | Some m => if le_dec n m then Some m else None
      | None => None
      end
  | None => None
  end.

Definition mn_valid (x : MonoNat) : Prop := is_Some x.

Definition mn_fpuValid (x y : MonoNat) : Prop :=
  match x, y with
  | Some a, Some b => a <= b
  | _, _ => False
  end.

(* Total: negative ints (which MonoNat has no natural reading of) fall back
   to ra_id (Some 0), rather than getting stuck. *)
Definition mn_of_int (z : Z) : MonoNat :=
  Some match z with
  | Z0 => 0%nat
  | Zpos p => Pos.to_nat p
  | Zneg _ => 0%nat
  end.

Definition mn_valid_dec (x : MonoNat) : Decision (mn_valid x).
Proof.
  destruct x as [a|].
  - left. by exists a.
  - right. intros [a Ha]. discriminate.
Defined.

Definition mn_fpuValid_dec (x y : MonoNat) : Decision (mn_fpuValid x y).
Proof.
  destruct x as [a|].
  - destruct y as [b|].
    + simpl. apply le_dec.
    + simpl. right. intros [].
  - simpl. right. intros [].
Defined.

(* Needed to discharge incr's own Fpu step: incr always moves the counter up
   by exactly 1, so mn_of_int of the new value is always >= mn_of_int of the
   old one -- true across the fallback-to-0 case too (z and z+1 both
   negative, or z negative and z+1 = 0, both give mn_of_int z = 0). *)
Lemma mn_of_int_mono (z : Z) : mn_fpuValid (mn_of_int z) (mn_of_int (z + 1)).
Proof.
  unfold mn_of_int, mn_fpuValid.
  destruct z as [ | p | p]; simpl.
  - lia.
  - rewrite Pos.add_1_r. rewrite Pos2Nat.inj_succ. lia.
  - destruct p as [p' | p' | ]; simpl; lia.
Qed.

Lemma mn_fpuAxiom : forall x y : MonoNat, mn_fpuValid x y ->
  mn_valid x /\ mn_valid y /\ forall c, mn_valid (mn_comp x c) -> mn_valid (mn_comp y c).
Proof.
  intros x y Hfpu. unfold mn_fpuValid in Hfpu.
  destruct x as [a|]; destruct y as [b|]; try done.
  unfold mn_valid, mn_comp in *.
  repeat split; [by exists a | by exists b |].
  intros c [r Hr]. destruct c as [cc|]; [| discriminate].
  by exists (Nat.max b cc).
Qed.

Lemma mn_ra_id_comp : forall x, mn_comp (Some 0%nat) x = x.
Proof. intros [a|]; unfold mn_comp; [f_equal; lia | reflexivity]. Qed.

Lemma mn_ra_id_valid : mn_valid (Some 0%nat).
Proof. by exists 0%nat. Qed.

Lemma mn_comp_comm : forall x y, mn_comp x y = mn_comp y x.
Proof. intros [a|] [b|]; unfold mn_comp; [f_equal; lia | ..]; reflexivity. Qed.

Lemma mn_comp_assoc : forall x y z, mn_comp (mn_comp x y) z = mn_comp x (mn_comp y z).
Proof.
  intros [a|] [b|] [c|]; unfold mn_comp; simpl; try reflexivity.
  f_equal. lia.
Qed.

Lemma mn_comp_valid : forall x y, mn_valid (mn_comp x y) -> mn_valid x /\ mn_valid y.
Proof.
  intros [a|] [b|] Hv; unfold mn_valid, mn_comp in *;
    [split; [by exists a | by exists b] | ..];
    destruct Hv as [? Hv]; discriminate.
Qed.

Lemma mn_frame_id : forall x, mn_valid x -> mn_frame x (Some 0%nat) = x.
Proof. intros x _. unfold mn_frame. reflexivity. Qed.

Lemma mn_comp_frame_inv : forall x y, mn_valid (mn_frame x y) -> mn_comp (mn_frame x y) y = x.
Proof.
  intros x y Hv.
  destruct y as [[|n]|].
  - destruct x as [a|]; unfold mn_frame, mn_comp in *; simpl; [f_equal; lia | reflexivity].
  - destruct x as [a|]; unfold mn_frame, mn_valid, mn_comp in *; simpl in *.
    + destruct (le_dec (S n) a) as [Hle|Hnle]; simpl in *.
      * f_equal. lia.
      * exfalso. destruct Hv as [? Hv]; discriminate.
    + exfalso. destruct Hv as [? Hv]; discriminate.
  - exfalso. unfold mn_frame, mn_valid in Hv. destruct Hv as [? Hv]; discriminate.
Qed.

Lemma mn_weak_frame_comp_inv : forall x y, mn_valid (mn_comp x y) -> mn_valid (mn_frame (mn_comp x y) y).
Proof.
  intros x y Hv.
  destruct x as [a|]; destruct y as [[|n]|]; unfold mn_valid, mn_comp, mn_frame in *; simpl in *.
  - by exists (Nat.max a 0).
  - destruct (le_dec (S n) (Nat.max a (S n))) as [Hle|Hnle].
    + by exists (Nat.max a (S n)).
    + exfalso. apply Hnle. lia.
  - destruct Hv as [? Hv]; discriminate.
  - destruct Hv as [? Hv]; discriminate.
  - destruct Hv as [? Hv]; discriminate.
  - destruct Hv as [? Hv]; discriminate.
Qed.

Global Instance MonoNatRA : ResourceAlgebra MonoNat := {|
  comp := mn_comp;
  frame := mn_frame;
  valid := mn_valid;
  valid_dec := mn_valid_dec;
  fpuValid := mn_fpuValid;
  fpuValid_dec := mn_fpuValid_dec;
  fpuAxiom := mn_fpuAxiom;
  ra_id := Some 0%nat;
  ra_id_comp := mn_ra_id_comp;
  ra_id_valid := mn_ra_id_valid;
  comp_comm := mn_comp_comm;
  comp_assoc := mn_comp_assoc;
  comp_valid := mn_comp_valid;
  frame_id := mn_frame_id;
  comp_frame_inv := mn_comp_frame_inv;
  weak_frame_comp_inv := mn_weak_frame_comp_inv;
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
  LExists "$v" TpInt (LAnd
    (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
    (LOwn (LVar "x") "c" (LVar "$v"))).

Definition counterInv_record : InvRecord := Inv ["x"] counterInv_body.

(* ----------------------------------------------------------------------- *)
(* read/incr/make's own ProcRecords, and the concrete Program/GhostConfig
   built from them -- moved ahead of read/incr/make's own proof
   development (which used to sit right after each record) so RProg/G
   exist before RavenHoareTriple/ProgramWF's own Local Notations
   (needed by every RavenHoareTriple-typed lemma in this file) do. *)

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

(* "#ret_val" must be declared (pwf_proc_ret_val_declared) even though incr
   never assigns it: incr's own contract (incr_postcond = LPure True) says
   nothing about it, so its non-deterministically-chosen entry value is
   simply never touched or observed -- same status as a void return. *)
Definition incr_record : ProcRecord :=
  Proc [("x", TpLoc)] [("v1", TpInt); ("new_v1", TpInt); ("res", TpBool); ("#ret_val", TpUnit)]
    incr_precond incr_postcond incr_body.

Definition make_body : stmt :=
  Seq
    (Alloc "x" [("c", lang.LitInt 0)])
    (Seq (FoldInv "counterInv" [Var "x"])
         (Assign "#ret_val" (Var "x"))).

Definition make_precond : assertion := LPure True.
(* No existential: "#ret_val" is a placeholder for the call's own fresh
   result lvar, substituted in by whoever consumes make_record's contract
   (see all_proc_specs_valid_raven's own <["#ret_val":=LVar lv_final]>
   substitution). Unlike the old "x"-existential shape, this has no
   top-level LExists binder -- required by ProgramWF's own
   pwf_proc_binders_fresh field, an unconditional forall over substitution
   maps that a top-level binder could never satisfy (pick a map sending some
   key to LVar "x" to violate disjointness). *)
Definition make_postcond : assertion := LInv "counterInv" [LVar "#ret_val"].

Definition make_record : ProcRecord :=
  Proc [] [("x", TpLoc); ("#ret_val", TpLoc)] make_precond make_postcond make_body.

(* The concrete Program/GhostConfig this file's whole development is
   about -- replaces the old per-fact axioms (proc_map_read, proc_map_incr,
   proc_map_make, inv_map_counterInv, proc_map_only, inv_map_only,
   pred_map_empty, inv_set_eq, ghost_heap_namespace_disjoint_counterInv),
   all provable lemmas below now. gname/namespace are concrete, inhabited
   Coq types (gname := positive) -- no allocation is needed to pick *a*
   name/namespace, only to later prove ownership *at* one (a separate,
   Step-5 concern, unrelated to picking the value itself). *)
Definition RProg : Program := {|
  prog_proc_set := {["read"; "incr"; "make"]};
  prog_pred_set := ∅;
  prog_inv_set := {["counterInv"]};
  prog_fld_set := {["c"; "h"]};
  prog_proc_map := list_to_map [("read", read_record); ("incr", incr_record); ("make", make_record)];
  prog_inv_map := list_to_map [("counterInv", counterInv_record)];
  prog_pred_map := ∅;
|}.

Definition G : GhostConfig := {|
  gc_ghost_heap_name := 1%positive;
  gc_ghost_heap_namespace := nroot .@ "ghost_heap";
  gc_inv_namespace_map := fun iv => nroot .@ iv;
|}.

Local Notation proc_map := (RProg.(prog_proc_map)).
Local Notation inv_map := (RProg.(prog_inv_map)).
Local Notation pred_map := (RProg.(prog_pred_map)).
Local Notation inv_set := (RProg.(prog_inv_set)).
Local Notation ghost_heap_namespace := (G.(gc_ghost_heap_namespace)).
Local Notation inv_namespace_map := (G.(gc_inv_namespace_map)).
Local Notation ProgramWF := (@ProgramWF invTokenG0 RProg G).
Local Notation RavenHoareTriple := (@RavenHoareTriple RProg).

Lemma proc_map_read : proc_map !! "read" = Some read_record.
Proof. reflexivity. Qed.

Lemma proc_map_incr : proc_map !! "incr" = Some incr_record.
Proof. reflexivity. Qed.

Lemma proc_map_make : proc_map !! "make" = Some make_record.
Proof. reflexivity. Qed.

Lemma inv_map_counterInv : inv_map !! "counterInv" = Some counterInv_record.
Proof. reflexivity. Qed.

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
  | "$v" => TpInt (* counterInv_body's own existential witness *)
  | "l_v1" => TpInt
  | "l_new_v1" => TpInt
  | "l_res" => TpBool
  | "l_ret" => TpInt
  | "l_call" => TpUnit
  | "l_x_ret" => TpLoc
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

   WeakeningRule takes assertion_entails, not entails (see rrl_lang.v's
   assertion_entails: a purely syntactic entailment on assertions,
   independent of Gamma/GhostConfig/invTokenG, restated there so
   RavenHoareTriple itself doesn't depend on them). assertion_entails is
   parameterized by sigma so its own AE_Exists_Mono/AE_Exists_ValIntro
   cases can use it; this local notation keeps every call site below
   instantiated at this file's own sigma. *)
Local Notation assertion_entails P Q := (rrl_lang.assertion_entails sigma P Q).

Lemma entails_and_true_intro P : assertion_entails P (LAnd P (LPure True)).
Proof. exact (AE_And_True_Intro sigma P). Qed.

Lemma entails_and_true_elim P : assertion_entails (LAnd P (LPure True)) P.
Proof. exact (AE_And_True_Elim sigma P). Qed.

(* A small reusable entails algebra, so LAnd-trees can be reshuffled freely
   via WeakeningRule instead of ad hoc per-site proofs. *)
Lemma entails_refl P : assertion_entails P P.
Proof. exact (AE_Refl sigma P). Qed.

Lemma entails_trans P Q R : assertion_entails P Q -> assertion_entails Q R -> assertion_entails P R.
Proof. exact (AE_Trans sigma P Q R). Qed.

Lemma entails_and_mono P P' Q Q' :
  assertion_entails P P' -> assertion_entails Q Q' -> assertion_entails (LAnd P Q) (LAnd P' Q').
Proof. exact (AE_And_Mono sigma P P' Q Q'). Qed.

Lemma entails_and_comm P Q : assertion_entails (LAnd P Q) (LAnd Q P).
Proof. exact (AE_And_Comm sigma P Q). Qed.

Lemma entails_and_assoc_r P Q R : assertion_entails (LAnd (LAnd P Q) R) (LAnd P (LAnd Q R)).
Proof. exact (AE_And_Assoc_R sigma P Q R). Qed.

Lemma entails_and_assoc_l P Q R : assertion_entails (LAnd P (LAnd Q R)) (LAnd (LAnd P Q) R).
Proof. exact (AE_And_Assoc_L sigma P Q R). Qed.

Lemma entails_exists_mono (lv : lvar) (t : typ) (A B : assertion) :
  sigma lv = t ->
  assertion_entails A B -> assertion_entails (LExists lv t A) (LExists lv t B).
Proof. exact (AE_Exists_Mono sigma lv t A B). Qed.

(* ----------------------------------------------------------------------- *)
(* read(x): requires/ensures counterInv(x). *)

(* Purely a 4-leaf LAnd reshuffling (LStack/GhostOwn/Own/True, grouped by
   (LStack,Own) and (GhostOwn,True) instead of the source's grouping) --
   the "medial" law (A∧B)∧(C∧D) ⊢ (A∧C)∧(B∧D), built from
   assoc/comm/mono since assertion_entails has no single primitive for
   arbitrary LAnd-tree permutations. *)
Lemma entails_regroup_pre_sym :
  assertion_entails
    (LAnd (LStack stk0) (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                                     (LOwn (LVar "x") "c" (LVar "$v")))
                               (LPure True)))
    (LAnd (LAnd (LStack stk0) (LOwn (LVar "x") "c" (LVar "$v")))
          (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v"))) (LPure True))).
Proof.
  eapply AE_Trans; [eapply AE_And_Assoc_L | ].
  eapply AE_Trans; [eapply AE_And_Mono; [eapply AE_And_Assoc_L | eapply AE_Refl] | ].
  eapply AE_Trans; [eapply AE_And_Assoc_R | ].
  eapply AE_Trans; [eapply AE_And_Assoc_R | ].
  eapply AE_Trans; [eapply AE_And_Mono; [eapply AE_Refl | eapply AE_And_Assoc_L] | ].
  eapply AE_Trans; [eapply AE_And_Mono; [eapply AE_Refl | eapply AE_And_Mono; [eapply AE_And_Comm | eapply AE_Refl]] | ].
  eapply AE_Trans; [eapply AE_And_Mono; [eapply AE_Refl | eapply AE_And_Assoc_R] | ].
  eapply AE_And_Assoc_L.
Qed.

(* Everything here is already phrased in terms of "$v" (not "l_v1") --
   HeapReadRule's own "l_v1 = $v" equality fact never actually has to be
   consumed: the l_v1 binder is just carried through vacuously (its scoped
   body doesn't depend on it at all once we're done), and counterInv_body
   is reassembled from GhostOwn($v)/Own($v) via AE_Exists_Intro "$v" using
   "$v"'s own ambient value as witness, exactly as counterInv's contract
   already reads. No value-substitution witness-intro needed here (unlike
   entails_alloc_fields_to_counterInv below, which does start from a
   concrete literal). *)
Lemma entails_regroup_post_sym (stk1 : stack) :
  assertion_entails
    (LAnd (LExists "l_v1" TpInt (LAnd (LStack stk1) (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LExprA (LBinOp EqOp (LVar "l_v1") (LVar "$v"))))))
          (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v"))) (LPure True)))
    (LExists "l_v1" TpInt (LAnd (LStack stk1) (LAnd counterInv_body (LPure True)))).
Proof.
  eapply AE_Trans.
  { eapply AE_Exists_And_Swap_R. simpl. set_solver. }
  eapply AE_Exists_Mono; [reflexivity | ].
  (* AE_Exists_And_Swap_R's own body is the *whole* LAnd (LStack stk1)
     (LAnd Own Eq) bundled as one LAnd-pair with p -- re-associate first so
     LStack stk1 is a top-level sibling again, matching the target shape. *)
  eapply AE_Trans; [eapply AE_And_Assoc_R | ].
  eapply AE_And_Mono; [eapply AE_Refl | ].
  (* Middle terms named explicitly throughout below: AE_Exists_Intro's own
     conclusion (X ⊢ LExists lv t X) doesn't pin lv/t from its LHS alone,
     so leaving them as AE_Trans metavariables (resolved only by the
     *other* branch) is unsafe under eapply's left-to-right subgoal order. *)
  eapply (AE_Trans sigma _
    (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))) _).
  - eapply AE_And_Mono; eapply AE_And_Elim_L.
  - eapply (AE_Trans sigma _
      (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v"))) (LOwn (LVar "x") "c" (LVar "$v"))) _).
    + eapply AE_And_Comm.
    + eapply (AE_Trans sigma _ counterInv_body _).
      * eapply AE_Exists_Intro. reflexivity.
      * eapply AE_And_True_Intro.
Qed.

(* The single, symbolic derivation the new ExistsElimRule needs for read's
   FldRd, run with counterInv's own existential witness kept as the free
   lvar "$v" rather than substituted -- matching the new rule's shape. *)
Lemma read_inner_step_sym :
  RavenHoareTriple rho sigma
    (LAnd (LStack stk0)
          (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                      (LOwn (LVar "x") "c" (LVar "$v")))
                (LPure True)))
      (FldRd "v1" (Var "x") "c") (cmask ∖ {["counterInv"]})
    (LExists "l_v1" TpInt (LAnd (LStack (<["v1":="l_v1"]> stk0)) (LAnd counterInv_body (LPure True)))).
Proof.
  eapply WeakeningRule.
  - eapply FrameRule with
      (r := LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v"))) (LPure True)).
    apply (HeapReadRule rho sigma stk0 (cmask ∖ {["counterInv"]}) "v1" (Var "x") (LVar "$v") "c" (LVar "x") "l_v1").
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
   ("$v" : Int) now comes directly from sigma's own declaration (sigma "$v" =
   TpInt), via the rule's new sigma-consistency premise -- no separate
   witness_well_typed proof needed any more. *)
Lemma read_fldrd_block_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack stk0) (LAnd counterInv_body (LPure True)))
      (FldRd "v1" (Var "x") "c") (cmask ∖ {["counterInv"]})
    (LExists "l_v1" TpInt (LAnd (LStack (<["v1":="l_v1"]> stk0)) (LAnd counterInv_body (LPure True)))).
Proof.
  eapply WeakeningRule.
  - apply (ExistsElimRule rho sigma (cmask ∖ {["counterInv"]}) "$v" TpInt
      (LAnd (LStack stk0)
            (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                        (LOwn (LVar "x") "c" (LVar "$v")))
                  (LPure True)))
      (FldRd "v1" (Var "x") "c")
      (LExists "l_v1" TpInt (LAnd (LStack (<["v1":="l_v1"]> stk0)) (LAnd counterInv_body (LPure True))))).
    + reflexivity.
    + simpl. right. split.
      { apply fresh_lvar_extend; [apply fresh_lvar_stk0; discriminate | discriminate]. }
      split; [left; reflexivity | exact I].
    + exact read_inner_step_sym.
  - eapply assertion_entails_and_stack_exists_swap.
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
    + constructor; [| constructor]. intros v Hv. simpl in Hv.
      apply elem_of_singleton in Hv as ->. unfold is_reserved. discriminate.
    + exact stk_type_compat_stk0.
    + apply fresh_lvar_stk0. discriminate.
    + unfold is_reserved. discriminate.
    + simpl. exact read_fldrd_block_step.
  - exact (entails_and_mono _ _ _ _ (entails_refl (LStack stk0)) (entails_and_true_intro (LInv "counterInv" [LVar "x"]))).
  - exact (entails_exists_mono "l_v1" TpInt _ _ eq_refl
      (entails_and_mono _ _ _ _ (entails_refl (LStack (<["v1":="l_v1"]> stk0)))
                         (entails_and_true_elim (LInv "counterInv" [LVar "x"])))).
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

Lemma entails_and_elim_l P Q : assertion_entails (LAnd P Q) P.
Proof. exact (AE_And_Elim_L sigma P Q). Qed.

Lemma entails_true_intro X : assertion_entails X (LPure True).
Proof. exact (AE_True_Intro sigma X). Qed.

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
   witness ("$v", tied to x.c's value while the invariant is open) is
   consumed directly via CASSuccRule/CASFailRule/FPURule's own LOwn/LGhostOwn
   premises -- no separate "v2 :| ..." pick or "assert" needed, matching how
   read never introduced a named witness for its own FldRd either. *)

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
  - apply AE_Exists_And_Swap_R.
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
   "$v") to one tied to whatever the program actually compared against. *)
(* Both promoted to rrl_lang.v as AE_Ite_Bool_True/AE_Ite_Bool_False --
   general, reusable facts about LIte's relationship to an indirect
   boolean witness lv, not specific to this file. *)
Lemma entails_ite_bool_true (cond : LExpr) (A B : assertion) (lv : lvar) :
  assertion_entails
    (LAnd (LIte cond (LAnd A (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
                      (LAnd B (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false))))))
          (LExprA (LVar lv)))
    (LAnd A (LExprA cond)).
Proof. exact (AE_Ite_Bool_True sigma cond A B lv). Qed.

Lemma entails_ite_bool_false (cond : LExpr) (A B : assertion) (lv : lvar) :
  assertion_entails
    (LAnd (LIte cond (LAnd A (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool true)))))
                      (LAnd B (LExprA (LBinOp EqOp (LVar lv) (LVal (LitBool false))))))
          (LExprA (LUnOp NotBoolOp (LVar lv))))
    B.
Proof. exact (AE_Ite_Bool_False sigma cond A B lv). Qed.

(* entails_ite_bool_true, with an extra frame fact riding alongside the
   LIte untouched -- lets a caller carry other resources/facts (e.g.
   counterInv's ghost chunk) through the same branch-extraction step. *)
Lemma entails_ite_bool_true_framed (cond : LExpr) (A B FRAME : assertion) (lv : lvar) :
  assertion_entails
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
   witness "$v" is kept as a free lvar throughout rather than substituted. *)

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
          (LAnd (LOwn (LVar "x") "c" (LVar "$v"))
                (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))))
      (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1")) (cmask ∖ {["counterInv"]})
    (LExists "l_res" TpBool (LAnd
      (LAnd (LStack (<["res":="l_res"]> incr_stk1))
        (LIte (LBinOp EqOp (LVar "$v") (LVar "l_v1"))
          (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
          (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false)))))))
      (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
            (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))).
Proof.
  eapply WeakeningRule.
  - eapply FrameRule with (r := LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                                      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))).
    apply (CASRule rho sigma incr_stk1 (cmask ∖ {["counterInv"]}) "res" (Var "x") "c" (Var "v1") (Var "new_v1")
      "l_res" (LVar "x") (LVar "l_v1") (LVar "l_new_v1") (LVar "$v")).
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
  - apply AE_Exists_And_Swap_R.
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
  assertion_entails
    (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")))
          (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))
    (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")))
          (LExprA (LBinOp RAFpuValidOp (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")) (LUnOp (RAOfIntOp h_ra) (LVar "l_new_v1"))))).
Proof.
  eapply AE_And_Mono; [eapply AE_Refl | ].
  eapply AE_LExprA_Impl. intros mp Harith.
  unfold LExpr_holds in Harith. simpl in Harith.
  destruct (mp "l_v1") as [b|z1| |l|p] eqn:Hv1val; try (exfalso; exact Harith).
  injection Harith as Harith.
  unfold val_beq in Harith. apply bool_decide_eq_true_1 in Harith.
  unfold LExpr_holds.
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
  assertion_entails
    (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_new_v1")))
          (LOwn (LVar "x") "c" (LVar "l_new_v1")))
    (LAnd counterInv_body (LPure True)).
Proof.
  eapply (AE_Trans sigma _ counterInv_body _).
  - exact (AE_Exists_Rename_Intro sigma "$v" "l_new_v1" TpInt
      (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
            (LOwn (LVar "x") "c" (LVar "$v")))
      eq_refl eq_refl (conj I I)).
  - eapply AE_And_True_Intro.
Qed.

(* Rewrites counterInv's ghost chunk from "$v" to "l_v1" using the CAS-success
   equality extracted from CASRule's own LIte (via entails_ite_bool_true). *)
Lemma incr_ghostown_v_to_l_v1 :
  assertion_entails
    (LAnd (LExprA (LBinOp EqOp (LVar "$v") (LVar "l_v1")))
          (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v"))))
    (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_v1"))).
Proof.
  eapply (AE_Trans sigma _
    (LAnd (LExprA (LBinOp EqOp (LVar "l_v1") (LVar "$v")))
          (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))) _).
  - eapply AE_And_Mono; [ | eapply AE_Refl].
    eapply AE_LExprA_Impl. intros mp Heq.
    unfold LExpr_holds in Heq |- *. simpl in Heq |- *.
    injection Heq as Heq. unfold val_beq in Heq |- *.
    apply bool_decide_eq_true_1 in Heq. f_equal. apply bool_decide_eq_true_2. exact (eq_sym Heq).
  - exact (AE_LExpr_Subst_Eq_Congr sigma "l_v1" "$v"
      (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_v1"))) I).
Qed.

(* Regroups the pieces entails_ite_bool_true_framed hands back -- A (=LOwn
   x.c l_new_v1), the CAS-success equality, GhostOwn(v), and the arithmetic
   fact -- into incr_fpu_step_framed's own expected precondition shape,
   rewriting GhostOwn(v) to GhostOwn(l_v1) along the way. *)
Lemma incr_true_branch_regroup :
  assertion_entails
    (LAnd (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "$v") (LVar "l_v1"))))
          (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
    (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")))
                (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))
          (LOwn (LVar "x") "c" (LVar "l_new_v1"))).
Proof.
  (* (A∧B)∧(C∧D) ⊢ (B∧C)∧(A∧D), regrouping the Eq/GhostOwn(v) pair (B∧C)
     together so incr_ghostown_v_to_l_v1 applies, then reshuffling the
     GhostOwn(l_v1)-for-(B∧C) result back with D/A into the target shape. *)
  eapply AE_Trans; [eapply AE_And_Assoc_R | ].
  eapply AE_Trans; [eapply AE_And_Mono; [eapply AE_Refl | eapply AE_And_Assoc_L] | ].
  eapply AE_Trans; [eapply AE_And_Assoc_L | ].
  eapply AE_Trans; [eapply AE_And_Mono; [eapply AE_And_Comm | eapply AE_Refl] | ].
  eapply AE_Trans; [eapply AE_And_Assoc_R | ].
  eapply AE_Trans; [eapply AE_And_Mono; [exact incr_ghostown_v_to_l_v1 | eapply AE_Refl] | ].
  eapply AE_Trans; [eapply AE_And_Assoc_L | ].
  eapply AE_Trans; [eapply AE_And_Mono; [eapply AE_And_Comm | eapply AE_Refl] | ].
  eapply AE_Trans; [eapply AE_And_Assoc_R | ].
  eapply AE_And_Comm.
Qed.

(* The IfS's "res = true" branch (the Fpu), fully composed: extract, rewrite,
   apply Fpu, repack counterInv. *)
Lemma incr_true_branch_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack incr_stk2)
      (LAnd (LAnd (LIte (LBinOp EqOp (LVar "$v") (LVar "l_v1"))
                     (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                     (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false))))))
                   (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
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
  assertion_entails
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

(* Repacks counterInv_body with "$v" (unchanged -- CAS failed, nothing was
   written) as the witness. *)
Lemma incr_repack_post_v :
  assertion_entails
    (LAnd (LOwn (LVar "x") "c" (LVar "$v"))
          (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v"))))
    (LAnd counterInv_body (LPure True)).
Proof.
  eapply (AE_Trans sigma _ counterInv_body _).
  - eapply AE_Trans; [eapply AE_And_Comm | ].
    exact (AE_Exists_Intro sigma "$v" TpInt
      (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
            (LOwn (LVar "x") "c" (LVar "$v")))
      eq_refl).
  - eapply AE_And_True_Intro.
Qed.

(* The IfS's "res = false" branch (SkipS): extract, drop the now-unused
   arithmetic fact, repack counterInv unchanged. *)
Lemma incr_false_branch_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack incr_stk2)
      (LAnd (LAnd (LIte (LBinOp EqOp (LVar "$v") (LVar "l_v1"))
                     (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                     (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false))))))
                   (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                         (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
            (LExprA (LUnOp NotBoolOp (LVar "l_res")))))
      SkipS
      (cmask ∖ {["counterInv"]})
    (LAnd (LStack incr_stk2) (LAnd counterInv_body (LPure True))).
Proof.
  eapply WeakeningRule.
  - apply (SkipRule rho sigma incr_stk2 (cmask ∖ {["counterInv"]})
      (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v"))))).
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
          (LAnd (LIte (LBinOp EqOp (LVar "$v") (LVar "l_v1"))
                   (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                   (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false))))))
                (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
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
    (LAnd (LIte (LBinOp EqOp (LVar "$v") (LVar "l_v1"))
             (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
             (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false))))))
          (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
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
          (LAnd (LIte (LBinOp EqOp (LVar "$v") (LVar "l_v1"))
                   (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                   (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false))))))
                (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
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
  - exact (AE_Exists_Intro sigma "l_res" TpBool _ eq_refl).
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
          (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                      (LOwn (LVar "x") "c" (LVar "$v")))
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
               (LIte (LBinOp EqOp (LVar "$v") (LVar "l_v1"))
                  (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                  (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false)))))))
            (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
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

(* Eliminates counterInv's own "$v" existential to reach
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
  - apply (ExistsElimRule rho sigma (cmask ∖ {["counterInv"]}) "$v" TpInt
      (LAnd (LStack incr_stk1)
            (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                        (LOwn (LVar "x") "c" (LVar "$v")))
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
  - eapply assertion_entails_and_stack_exists_swap.
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
  - constructor; [| constructor]. intros v Hv. simpl in Hv.
    apply elem_of_singleton in Hv as ->. unfold is_reserved. discriminate.
  - exact stk_type_compat_incr_stk1.
  - apply fresh_lvar_incr_stk1; discriminate.
  - unfold is_reserved. discriminate.
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
    + unfold is_reserved. discriminate.
    + constructor; [| constructor]. intros v Hv. simpl in Hv.
      apply elem_of_singleton in Hv as ->. unfold is_reserved. discriminate.
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

(* ----------------------------------------------------------------------- *)
(* make(): returns (x: Ref), ensures counterInv(x). No requires-clause and
   no args -- "x" here is both the freshly allocated location's own pvar
   (introduced by the Alloc statement itself, exactly as the source's own
   "returns (x: Ref)" clause introduces it, with no separate "#ret_val"
   ever needed since nothing in the body runs after the fold) and, reusing
   stk0's own pvar-"x"-to-lvar-"x" naming convention, its lvar too, so
   counterInv_body's own repack lemmas (trnsl_repack_counterInv, hardcoded
   to "x") apply directly with no generalization needed. The proc's own
   postcondition existentially quantifies over that same location, so
   nothing beyond this file's existing rho/sigma/entails machinery (both
   already keyed at "x" : TpLoc) is needed either -- only a fresh, empty
   entry stack (make has no args, unlike read/incr). *)

Definition stk_make0 : stack := ∅.

Lemma stk_type_compat_stk_make0 : stk_type_compat rho sigma stk_make0.
Proof. intros v lv Hv. unfold stk_make0 in Hv. rewrite lookup_empty in Hv. discriminate. Qed.

Lemma fresh_lvar_stk_make0 (lv : lvar) : fresh_lvar stk_make0 lv.
Proof. intros v0 Heq. unfold stk_make0 in Heq. rewrite lookup_empty in Heq. discriminate. Qed.

(* The ghost cell's initial value, at the generic ra_of_int operation for
   h_ra's own RA instance -- matches RAOfIntOp's own interp_lexpr semantics
   exactly (both resolve the very same ResourceAlgebra instance for
   RA_carrier (ra_map h_ra)), so no dependent-type transport is ever needed
   to relate the two. *)
Definition h0 : RA_carrier (ra_map h_ra) := ra_of_int 0.

Lemma h0_valid : (RA_inst (ra_map h_ra)).(valid) h0.
Proof. unfold h0. rewrite ra_map_h_ra. simpl. by exists 0%nat. Qed.

(* Folds the two field-initialization lists HeapAllocRule's own conclusion
   produces (one real, one ghost) down into counterInv_body. *)
Lemma entails_alloc_fields_to_counterInv :
  assertion_entails
    (LAnd (field_list_to_assertion (LVar "x") [("c", lang.LitInt 0)])
          (field_list_to_ghost_assertion (LVar "x") [("h", existT h_ra h0)]))
    (LAnd counterInv_body (LPure True)).
Proof.
  simpl.
  eapply AE_Trans.
  { eapply AE_And_Mono; eapply AE_And_Elim_L. }
  eapply (AE_Trans sigma _
    (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVal (LitInt 0)))) (LOwn (LVar "x") "c" (LVal (LitInt 0)))) _).
  - eapply AE_Trans; [eapply AE_And_Comm | ].
    eapply AE_And_Mono; [ | eapply AE_Refl].
    eapply AE_GhostOwn_Chunk_Eq. intros mp. simpl. reflexivity.
  - eapply (AE_Trans sigma _ counterInv_body _).
    + exact (AE_Exists_ValIntro sigma "$v" TpInt (LitInt 0)
        (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
              (LOwn (LVar "x") "c" (LVar "$v")))
        eq_refl I (conj I I)).
    + eapply AE_And_True_Intro.
Qed.

Lemma make_alloc_step :
  RavenHoareTriple rho sigma
    (LStack stk_make0)
      (Alloc "x" [("c", lang.LitInt 0)]) cmask
    (LExists "x" TpLoc (LAnd (LStack (<["x":="x"]> stk_make0)) (LAnd counterInv_body (LPure True)))).
Proof.
  eapply WeakeningRule.
  - apply (HeapAllocRule rho sigma stk_make0 cmask "x"
      [("c", lang.LitInt 0)] [("h", existT h_ra h0)] "x").
    + apply fresh_lvar_stk_make0.
    + constructor; [set_solver | constructor].
    + constructor; [set_solver | constructor].
    + discriminate.
    + constructor; [exact h0_valid | constructor].
    + exact stk_type_compat_stk_make0.
  - exact (entails_refl _).
  - apply (entails_exists_mono "x" TpLoc _ _ eq_refl
      (entails_and_mono _ _ _ _ (entails_refl (LStack (<["x":="x"]> stk_make0)))
        entails_alloc_fields_to_counterInv)).
Qed.

(* fold counterInv(x): InvAllocRule at the freshly allocated location, with
   counterInv_body's own "x" substituted to itself (subst_map is the
   identity map {"x" := LVar "x"} here, exactly as at every other
   InvAccessBlockRule/InvAllocRule call site in this file that reuses
   stk0's pvar-"x"-to-lvar-"x" naming), so subst counterInv_body {"x" :=
   LVar "x"} reduces to counterInv_body itself via simpl. *)
Lemma make_foldinv_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack (<["x":="x"]> stk_make0)) (LAnd counterInv_body (LPure True)))
      (FoldInv "counterInv" [Var "x"]) cmask
    (LAnd (LStack (<["x":="x"]> stk_make0)) (LAnd (LInv "counterInv" [LVar "x"]) (LPure True))).
Proof.
  apply (InvAllocRule rho sigma (<["x":="x"]> stk_make0) cmask "counterInv" [Var "x"]
    counterInv_record (LPure True) [LVar "x"]).
  - reflexivity.
  - set_solver.
  - exact inv_map_counterInv.
  - reflexivity.
  - constructor; [| constructor]. intros v Hv. simpl in Hv.
    apply elem_of_singleton in Hv as ->. unfold is_reserved. discriminate.
  - eapply stk_type_compat_extend; [exact stk_type_compat_stk_make0 | reflexivity | reflexivity].
Qed.

(* make's own Assign "#ret_val" (Var "x") step: bare VarAssignmentRule,
   picking "l_x_ret" (typed TpLoc in sigma) as the assignment's own fresh
   witness. Mirrors read_assign_inner_step/incr_assign_inner_step exactly. *)
Lemma make_assign_inner_step :
  RavenHoareTriple rho sigma
    (LStack (<["x":="x"]> stk_make0))
      (Assign "#ret_val" (Var "x")) cmask
    (LExists "l_x_ret" TpLoc (LAnd (LStack (<["#ret_val":="l_x_ret"]> (<["x":="x"]> stk_make0)))
                             (LExprA (LBinOp EqOp (LVar "l_x_ret") (LVar "x"))))).
Proof.
  apply (VarAssignmentRule rho sigma (<["x":="x"]> stk_make0) cmask "#ret_val" "l_x_ret"
    (Var "x") (LVar "x") TpLoc).
  - reflexivity.
  - reflexivity.
  - apply fresh_lvar_extend; [apply fresh_lvar_stk_make0 | discriminate].
  - eapply stk_type_compat_extend; [exact stk_type_compat_stk_make0 | reflexivity | reflexivity].
Qed.

(* Frames counterInv's own LInv fact (established by make_foldinv_step)
   through the Assign, then rewrites the LInv's own argument from "x" (the
   local pvar holding the allocation) to "l_x_ret" (the assignment's own
   fresh witness, standing for the eventual "#ret_val") using the equality
   fact VarAssignmentRule's own conclusion provides -- mirrors
   incr_ghostown_v_to_l_v1's rewrite, just for LInv instead of LGhostOwn.
   The rewrite happens *inside* the "l_x_ret" existential throughout (via
   entails_exists_mono), rather than trying to eliminate that existential:
   unlike every other fresh witness this file discards once consumed,
   "l_x_ret" is exactly the value the whole point of this step is to
   expose, so it must survive in the conclusion, not vanish from it --
   ExistsElimRule could never reach a target that itself mentions "l_x_ret"
   freely, since that name would then denote the ambient mp, not the
   witness just bound (this is why make_postcond, unlike read/incr's own
   LPure True, cannot be reached directly here: bridging "l_x_ret" to the
   "#ret_val" placeholder is exactly the job of the later step that
   connects make_body_step to all_proc_specs_valid_raven's own
   ∃ stk0' lv_final, via its <["#ret_val":=LVar lv_final]> substitution). *)
Lemma make_assign_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack (<["x":="x"]> stk_make0)) (LAnd (LInv "counterInv" [LVar "x"]) (LPure True)))
      (Assign "#ret_val" (Var "x")) cmask
    (LExists "l_x_ret" TpLoc (LInv "counterInv" [LVar "l_x_ret"])).
Proof.
  eapply WeakeningRule.
  - apply (FrameRule rho sigma cmask (Assign "#ret_val" (Var "x"))
      (LStack (<["x":="x"]> stk_make0))
      (LExists "l_x_ret" TpLoc (LAnd (LStack (<["#ret_val":="l_x_ret"]> (<["x":="x"]> stk_make0)))
                               (LExprA (LBinOp EqOp (LVar "l_x_ret") (LVar "x")))))
      (LAnd (LInv "counterInv" [LVar "x"]) (LPure True))
      make_assign_inner_step).
  - exact (entails_refl _).
  - eapply AE_Trans.
    { eapply AE_Exists_And_Swap_R. simpl. split; [apply Forall_singleton; set_solver | exact I]. }
    eapply AE_Exists_Mono; [reflexivity | ].
    eapply (AE_Trans sigma _
      (LAnd (LExprA (LBinOp EqOp (LVar "l_x_ret") (LVar "x"))) (LInv "counterInv" [LVar "x"])) _).
    + eapply AE_And_Mono; [eapply AE_And_Elim_R | eapply AE_And_Elim_L].
    + exact (AE_LExpr_Subst_Eq_Congr sigma "l_x_ret" "x" (LInv "counterInv" [LVar "l_x_ret"]) I).
Qed.

(* make's full body: HeapAllocRule, then InvAllocRule, then the Assign that
   exposes the allocated/folded location as "#ret_val"'s own fresh witness
   -- mirrors read_body_step's own SequenceRule/ExistsElimRule shape for
   the alloc, with one more SequenceRule stage folded in for the trailing
   Assign. Concludes at an "l_x_ret"-existential, not raw make_postcond
   itself -- see make_assign_step's own comment for why the latter is
   unreachable directly from a derivation. *)
Lemma make_body_step :
  RavenHoareTriple rho sigma
    (LAnd (LStack stk_make0) make_precond)
      make_body cmask
    (LExists "l_x_ret" TpLoc (LInv "counterInv" [LVar "l_x_ret"])).
Proof.
  unfold make_body, make_precond.
  eapply SequenceRule.
  - eapply WeakeningRule.
    + exact make_alloc_step.
    + exact (entails_and_true_elim (LStack stk_make0)).
    + exact (entails_refl _).
  - apply (ExistsElimRule rho sigma cmask "x" TpLoc
      (LAnd (LStack (<["x":="x"]> stk_make0)) (LAnd counterInv_body (LPure True)))
      (Seq (FoldInv "counterInv" [Var "x"]) (Assign "#ret_val" (Var "x")))
      (LExists "l_x_ret" TpLoc (LInv "counterInv" [LVar "l_x_ret"]))).
    + reflexivity.
    + simpl. right. apply Forall_singleton. set_solver.
    + eapply SequenceRule.
      * exact make_foldinv_step.
      * exact make_assign_step.
Qed.

(* ----------------------------------------------------------------------- *)
(* ProgramWF: pin proc_map/inv_map/pred_map/inv_set to this program's own
   concrete records and discharge every field.

   proc_map/inv_map are concrete now (RProg above), so "pinning" them is
   just computation. The individual "contains at least this entry" facts
   above (proc_map_read, proc_map_incr, proc_map_make, inv_map_counterInv)
   already do half of that; *_only below adds the other half ("nothing
   else is in the map"), stated as a standalone complement rather than
   restating the map's contents, so there is no risk of the two
   accidentally disagreeing -- any actual mismatch would simply fail to
   typecheck in proc_map_forall/inv_map_forall below. *)

Lemma proc_map_only : forall k : proc_name,
  k ≠ "make" -> k ≠ "read" -> k ≠ "incr" -> proc_map !! k = None.
Proof.
  intros k Hm Hr Hi. simpl.
  rewrite lookup_insert_ne; [| congruence].
  rewrite lookup_insert_ne; [| congruence].
  rewrite lookup_insert_ne; [| congruence].
  apply lookup_empty.
Qed.

Lemma inv_map_only : forall k : inv_name,
  k ≠ "counterInv" -> inv_map !! k = None.
Proof. intros k Hne. simpl. rewrite lookup_insert_ne; [| congruence]. apply lookup_empty. Qed.

Lemma pred_map_empty : pred_map = (∅ : gmap pred_name PredRecord).
Proof. reflexivity. Qed.

Lemma inv_set_eq : inv_set = {["counterInv"]}.
Proof. reflexivity. Qed.

(* With only one invariant in scope, pwf_inv_namespace_disjoint/
   pwf_inv_gname_injective turn out vacuous (no two *distinct* elements
   of a singleton set), but this one -- ghost_heap_namespace vs.
   counterInv's own namespace -- is a genuine fact about how the two
   namespaces were picked (both under nroot, distinct suffixes). *)
Lemma ghost_heap_namespace_disjoint_counterInv :
  ghost_heap_namespace ## inv_namespace_map "counterInv".
Proof. apply ndot_ne_disjoint. congruence. Qed.

Lemma proc_map_forall (P : proc_name -> ProcRecord -> Prop) :
  P "make" make_record -> P "read" read_record -> P "incr" incr_record ->
  map_Forall P proc_map.
Proof.
  intros Hm Hr Hi k v Hkv.
  destruct (decide (k = "make")) as [-> | Hne1].
  { rewrite proc_map_make in Hkv. injection Hkv as <-. exact Hm. }
  destruct (decide (k = "read")) as [-> | Hne2].
  { rewrite proc_map_read in Hkv. injection Hkv as <-. exact Hr. }
  destruct (decide (k = "incr")) as [-> | Hne3].
  { rewrite proc_map_incr in Hkv. injection Hkv as <-. exact Hi. }
  rewrite (proc_map_only k Hne1 Hne2 Hne3) in Hkv. discriminate.
Qed.

Lemma inv_map_forall (P : inv_name -> InvRecord -> Prop) :
  P "counterInv" counterInv_record -> map_Forall P inv_map.
Proof.
  intros Hc k v Hkv.
  destruct (decide (k = "counterInv")) as [-> | Hne].
  { rewrite inv_map_counterInv in Hkv. injection Hkv as <-. exact Hc. }
  rewrite (inv_map_only k Hne) in Hkv. discriminate.
Qed.

(* "x" is the only lvar every record/body here ever uses that could
   collide with the reserved namespace; "$v" is the only reserved one.
   Both are settled by unfolding is_reserved and letting discriminate
   compute String.prefix. *)
Ltac not_reserved := unfold is_reserved; simpl; discriminate.

Lemma counter_monotonic_ProgramWF : ProgramWF.
Proof.
  constructor.
  - (* pwf_proc_args_unique *)
    apply proc_map_forall; simpl.
    + constructor.
    + repeat constructor; set_solver.
    + repeat constructor; set_solver.
  - (* pwf_proc_ret_val_fresh *)
    apply proc_map_forall; simpl; set_solver.
  - (* pwf_proc_locals_unique *)
    apply proc_map_forall; simpl.
    + repeat constructor; set_solver.
    + repeat constructor; set_solver.
    + repeat constructor; set_solver.
  - (* pwf_proc_args_locals_disjoint *)
    apply proc_map_forall; simpl; set_solver.
  - (* pwf_proc_ret_val_declared *)
    apply proc_map_forall; simpl; set_solver.
  - (* pwf_proc_stack_free *)
    apply proc_map_forall; simpl.
    + split; [constructor |].
      unfold make_postcond. eapply SF_Inv; [exact inv_map_counterInv | reflexivity |].
      simpl. repeat constructor.
    + split.
      * unfold read_precond. eapply SF_Inv; [exact inv_map_counterInv | reflexivity |].
        simpl. repeat constructor.
      * constructor.
    + split.
      * unfold incr_precond. eapply SF_Inv; [exact inv_map_counterInv | reflexivity |].
        simpl. repeat constructor.
      * constructor.
  - (* pwf_proc_fvars_bounded *)
    apply proc_map_forall; simpl.
    + split; set_solver.
    + split; set_solver.
    + split; set_solver.
  - (* pwf_proc_binders_reserved *)
    apply proc_map_forall; simpl; split; set_solver.
  - (* pwf_proc_args_not_reserved *)
    apply proc_map_forall; simpl.
    + constructor.
    + repeat constructor. not_reserved.
    + repeat constructor. not_reserved.
  - (* pwf_inv_fvars_scoped *)
    apply inv_map_forall; simpl. set_solver.
  - (* pwf_inv_fvars_closed *)
    apply inv_map_forall; simpl. set_solver.
  - (* pwf_inv_fvars_bounded *)
    intros inv_nm r args Hr Hlen v Hv.
    destruct (decide (inv_nm = "counterInv")) as [-> | Hne].
    2: { rewrite (inv_map_only inv_nm Hne) in Hr. discriminate. }
    rewrite inv_map_counterInv in Hr. injection Hr as <-.
    unfold counterInv_record in *. simpl in Hlen.
    destruct args as [| a args']; [discriminate Hlen |].
    destruct args' as [| b args'']; [| discriminate Hlen].
    have Hsubst : subst counterInv_body (list_to_map (zip ["x"] [a]))
                = LExists "$v" TpInt (LAnd
                    (LGhostOwn a "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                    (LOwn a "c" (LVar "$v"))).
    { unfold counterInv_body. simpl. rewrite lookup_insert. reflexivity. }
    rewrite Hsubst in Hv. simpl in Hv. set_solver.
  - (* pwf_inv_binders_reserved *)
    apply inv_map_forall; simpl. intros v Hv.
    assert (Hv' : v ∈ ({["$v"]} : gset lvar)) by set_solver.
    apply elem_of_singleton in Hv'. subst v. unfold is_reserved. reflexivity.
  - (* pwf_inv_args_not_reserved *)
    apply inv_map_forall; simpl. repeat constructor. not_reserved.
  - (* pwf_pred_fvars_scoped *)
    rewrite pred_map_empty. intros k v Hkv. rewrite lookup_empty in Hkv. discriminate.
  - (* pwf_pred_fvars_closed *)
    rewrite pred_map_empty. intros k v Hkv. rewrite lookup_empty in Hkv. discriminate.
  - (* pwf_pred_fvars_bounded *)
    rewrite pred_map_empty. intros pred_nm r args Hr. rewrite lookup_empty in Hr. discriminate.
  - (* pwf_pred_binders_reserved *)
    rewrite pred_map_empty. intros k v Hkv. rewrite lookup_empty in Hkv. discriminate.
  - (* pwf_pred_args_not_reserved *)
    rewrite pred_map_empty. intros k v Hkv. rewrite lookup_empty in Hkv. discriminate.
  - (* pwf_inv_body_stack_free *)
    apply inv_map_forall; simpl. repeat constructor.
  - (* pwf_inv_gname_injective *)
    rewrite inv_set_eq. intros inv1 inv2 Hin1 Hin2 Heq.
    apply elem_of_singleton in Hin1 as ->. apply elem_of_singleton in Hin2 as ->. reflexivity.
  - (* pwf_inv_namespace_disjoint *)
    rewrite inv_set_eq. intros inv1 inv2 Hin1 Hin2 Hne.
    apply elem_of_singleton in Hin1 as ->. apply elem_of_singleton in Hin2 as ->.
    exfalso. exact (Hne eq_refl).
  - (* pwf_ghost_heap_namespace_disjoint_inv *)
    rewrite inv_set_eq. intros inv' Hin. apply elem_of_singleton in Hin as ->.
    exact ghost_heap_namespace_disjoint_counterInv.
Qed.
