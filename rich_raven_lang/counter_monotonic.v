(* Example: encoding of test/concurrent/counter/counter_monotonic.rav
   (a monotone counter backed by a simplified Auth[MaxNat]-style resource
   algebra) against rrl_lang.v/lang.v, together with a RavenHoareTriple
   derivation for incr/read/make. *)
From stdpp Require Import gmap namespaces.
From raven_iris.simp_raven_lang Require Import ra_base.
Require Import Coq.Logic.FunctionalExtensionality.

(* ----------------------------------------------------------------------- *)
(* The resource algebra: a plain monotone nat -- comp/frame is max, and a
   frame-preserving update is exactly "go up". This is the fragment of
   Auth[MaxNat] this proof actually needs: nothing here ever holds a
   separate authoritative/fragment split, so there is no need to formalize
   Auth on top of it.
   Carrier is [option nat], not [nat]: ResourceAlgebra's own axioms
   require [frame] to actually reject the [x < y] case via [valid], and
   plain [nat] has no element to
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

From iris.proofmode Require Import tactics.
From raven_iris.simp_raven_lang Require Import lang.
From raven_iris.rich_raven_lang Require Import soundness.

Module CounterRAConfig.
  Definition ra_map (_ : ra_name) : RA_Pack := MonoNatPack.
End CounterRAConfig.

Module soundness := raven_iris.rich_raven_lang.soundness.Make CounterRAConfig.
Module trnsl := soundness.trnsl.
Module rrl_lang := soundness.rrl_lang.
Module lifting := soundness.lifting.
Module ghost_state := soundness.ghost_state.
Module lang := soundness.lang.
Import lang ghost_state lifting rrl_lang trnsl soundness.

Section CounterMonotonic.

Context {Σ : gFunctors}.
Context `{!invTokenG Σ}.

Lemma ra_map_h_ra : ra_map h_ra = MonoNatPack.
Proof. reflexivity. Qed.

(* Isolates the ra_map h_ra = MonoNatPack rewrite (needed to fall back from
   the RA-generic ra_of_int/fpuValid to their concrete MonoNat definitions)
   into one small lemma, so incr's own Fpu-step proof doesn't have to fight
   the dependent types directly. *)
Lemma h_ra_fpuValid_mono (z1 z2 : Z) :
  z2 = (z1 + 1)%Z ->
  @fpuValid (RA_carrier (ra_map h_ra)) (ra_inst_instance (ra_map h_ra)) (ra_of_int z1) (ra_of_int z2).
Proof.
  intros ->. change (mn_fpuValid (mn_of_int z1) (mn_of_int (z1 + 1))).
  apply mn_of_int_mono.
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
   built from them, come before each proc's own proof development below:
   RProg/G must exist before RavenHoareTriple/ProgramWF's own Local
   Notations (needed by every RavenHoareTriple-typed lemma in this file)
   do. *)

(* A "do nothing" filler for a branch that must cost no physical step --
   e.g. incr_body's CAS-failure branch below, which sits inside an
   InvAccessBlock that already spent its one atomic step on the CAS, so
   SkipS (a real step) there makes the block need two steps depending on
   which branch runs, and trnsl_atomic_block rejects it. Assert (Val
   (LitBool true)) costs no step at all (see the Assert constructor's own
   comment in rrl_lang.v) and, since "true" is trivially provable, behaves
   exactly like SkipS at the Hoare-logic level (see ghostskip_step below,
   defined once entails_* wrappers are available). *)
Definition GhostSkip : stmt := Assert (Val (lang.LitBool true)).

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
                 GhostSkip)))
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
  Proc [("x", TpLoc)] [("v1", TpInt); ("new_v1", TpInt); ("res", TpBool); ("call_res", TpUnit); ("#ret_val", TpUnit)]
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
   substitution). No top-level LExists binder here: ProgramWF's own
   pwf_proc_binders_reserved field requires every one of a postcondition's
   own binders to be a reserved name (is_reserved, i.e. "$"-prefixed), and
   "x" isn't one. *)
Definition make_postcond : assertion := LInv "counterInv" [LVar "#ret_val"].

Definition make_record : ProcRecord :=
  Proc [] [("x", TpLoc); ("#ret_val", TpLoc)] make_precond make_postcond make_body.

(* The concrete Program/GhostConfig this file's whole development is
   about. proc_map_read/proc_map_incr/proc_map_make/inv_map_counterInv/
   proc_map_only/inv_map_only/pred_map_empty/inv_set_eq/
   ghost_heap_namespace_disjoint_counterInv below are all provable lemmas
   about it, not axioms. gname/namespace are concrete, inhabited Coq types
   (gname := positive) -- no allocation is needed to pick *a* name/
   namespace, only to later prove ownership *at* one (the adequacy
   wrapper's own concern, unrelated to picking the value itself). *)
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
Local Notation ProgramWF := (@ProgramWF Σ invTokenG0 RProg G).
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
(* Program-level setup shared by incr/read's derivations, ahead of the
   entails helpers below: entails is parameterized by sigma (see
   rrl_lang.v), so sigma has to exist before the "entails" local notation
   that partially applies it does. *)

(* Per-procedure pvar-typing contexts: read/incr/make each declare
   "#ret_val" with a genuinely different type
   (Int/Unit/Loc respectively -- make's return really is a location, not an
   arbitrary choice), which a single global rho could never satisfy for all
   three at once (all_proc_specs_valid_raven's own entry stack needs
   rho "#ret_val" = sigma lv for whichever lv the proc's own dll picks,
   and dll_locals_typed ties that lv's type to the *callee's* own
   declaration). rrl_lang.v's proc_pvar_typs (all_proc_specs_valid_raven's
   own replacement for a shared pvar_typs parameter) builds exactly the
   right context from each proc_record's own args/locals -- see its
   comment, and proc_call_ret_well_typed's, for the caller-side half of
   this same fix. *)
Definition rho_read : pvar_typs := proc_pvar_typs read_record.
Definition rho_incr : pvar_typs := proc_pvar_typs incr_record.
Definition rho_make : pvar_typs := proc_pvar_typs make_record.

(* Genuinely rich sigma (Hσ_rich): the fixed names above give sigma only
   finitely many lvars per type -- e.g. only "l_res" ever had TpBool, so excluding
   it leaves nothing. rrl_lang.v's rich_lvar_typs fixes this generically
   (infinitely many lvars of every type, by construction); layering these
   few fixed names on top via lvar_typs_update inherits richness for free
   from rich_lvar_typs_rich, with no proof to redo here. *)
Definition sigma : lvar_typs := lvar_typs_update
  (list_to_map [
     ("x", TpLoc);
     ("$v", TpInt); (* counterInv_body's own existential witness *)
     ("l_v1", TpInt);
     ("l_new_v1", TpInt);
     ("l_res", TpBool);
     ("l_ret", TpInt);
     ("l_call", TpUnit);
     ("l_x_ret", TpLoc);
     (* Placeholder entry values for a procedure's own not-yet-touched
        locals (e.g. read's "v1"/"#ret_val" before FldRd/Assign overwrite
        them) -- needed so read/incr/make's own entry stack can bind every
        declared local from the start, matching all_proc_specs_valid_raven's
        own entry-stack shape (every RTCallStep-allocated local is bound at
        once, not just the ones a given derivation happens to touch first).
        Never read, only overwritten -- but *distinct* per simultaneous slot
        of the same type within one procedure's own entry stack (read/incr
        each need two live Int placeholders at once, make two Loc ones),
        since a real dll's own dll_locals are NoDup: reusing one name for
        two slots would make read_body_step's own entry stack correspond to
        no valid dll at all, blocking RavenHoareTriple_rename's later
        instantiation at an arbitrary one (renaming is a function, so it
        cannot split one placeholder into two distinct targets). *)
     ("l_ph_int1", TpInt);
     ("l_ph_int2", TpInt);
     ("l_ph_bool", TpBool);
     ("l_ph_unit", TpUnit);
     ("l_ph_unit2", TpUnit);
     ("l_ph_loc1", TpLoc);
     ("l_ph_loc2", TpLoc)
  ] : gmap lvar typ)
  rich_lvar_typs.

Lemma Hsigma_rich : ∀ (t : typ) (excl : gset lvar), ∃ lv, lv ∉ excl ∧ ¬ is_reserved lv ∧ sigma lv = t.
Proof. exact (lvar_typs_update_rich _ rich_lvar_typs rich_lvar_typs_rich). Qed.

(* Type-preserving transpositions are the building blocks used below to
   transport the three canonical body derivations to the arbitrary fresh
   entry lvars chosen by raven_soundness. *)
Definition lvar_swap (a b x : lvar) : lvar :=
  if decide (x = a) then b else if decide (x = b) then a else x.

Lemma lvar_swap_involutive a b : a ≠ b → ∀ x, lvar_swap a b (lvar_swap a b x) = x.
Proof.
  intros Hab x. unfold lvar_swap. repeat case_decide; congruence.
Qed.

Lemma lvar_swap_inj a b : a ≠ b → Inj (=) (=) (lvar_swap a b).
Proof.
  intros Hab x y Hxy.
  rewrite <-(lvar_swap_involutive a b Hab x), <-(lvar_swap_involutive a b Hab y), Hxy.
  reflexivity.
Qed.

Lemma lvar_swap_typ a b : sigma a = sigma b → ∀ x, sigma (lvar_swap a b x) = sigma x.
Proof.
  intros Hab x. unfold lvar_swap.
  destruct (decide (x = a)) as [-> | Hxa]; [exact (eq_sym Hab) |].
  destruct (decide (x = b)) as [-> | Hxb]; [exact Hab | reflexivity].
Qed.

Lemma lvar_swap_reserved a b :
  ¬ is_reserved a → ¬ is_reserved b → ∀ x, is_reserved x → lvar_swap a b x = x.
Proof.
  intros Hna Hnb x Hx. unfold lvar_swap.
  destruct (decide (x = a)) as [-> | Hxa]; [contradiction |].
  destruct (decide (x = b)) as [-> | Hxb]; [contradiction | reflexivity].
Qed.

Lemma lvar_swap_not_reserved a b :
  ¬ is_reserved a → ¬ is_reserved b → ∀ x, ¬ is_reserved x → ¬ is_reserved (lvar_swap a b x).
Proof.
  intros Hna Hnb x Hx. unfold lvar_swap.
  destruct (decide (x = a)) as [-> | Hxa]; [simpl; exact Hnb |].
  destruct (decide (x = b)) as [-> | Hxb]; [simpl; exact Hna | exact Hx].
Qed.

Lemma lvar_swap_eq_iff a b x y : a ≠ b →
  lvar_swap a b x = y ↔ x = lvar_swap a b y.
Proof.
  intros Hab. split; intro H.
  - apply (f_equal (lvar_swap a b)) in H.
    rewrite !(lvar_swap_involutive a b Hab) in H. exact H.
  - apply (f_equal (lvar_swap a b)) in H.
    rewrite !(lvar_swap_involutive a b Hab) in H. exact H.
Qed.

(* A finite, type-preserving change of names.  The [protected] list is
   useful when this lemma is used inductively: it records names that the
   remaining swaps must leave alone.  Taking it to be [[]] gives the usual
   form needed to transport a canonical body proof to its fresh entry
   lvars. *)
Lemma finite_lvar_renaming (xs ys protected : list lvar) :
  NoDup xs →
  NoDup ys →
  Forall (fun x => ¬ is_reserved x) xs →
  Forall (fun y => ¬ is_reserved y) ys →
  Forall2 (fun x y => sigma x = sigma y) xs ys →
  (∀ z, z ∈ protected → z ∉ xs ∧ z ∉ ys) →
  ∃ ren : lvar → lvar,
    Inj (=) (=) ren ∧
    (∀ z, sigma (ren z) = sigma z) ∧
    (∀ z, is_reserved z → ren z = z) ∧
    (∀ z, z ∈ protected → ren z = z) ∧
    map ren xs = ys.
Proof.
  remember (length xs) as n eqn:Hlen.
  revert xs ys protected Hlen.
  induction n as [|n IH]; intros xs ys protected Hlen Hndx Hndy Hnr_x Hnr_y Htys Hprotected.
  - destruct xs as [|a xs]; [|discriminate Hlen].
    destruct ys as [|b ys]; [|inversion Htys].
    exists (fun z => z).
    split.
    { intros x y Hxy. exact Hxy. }
    split.
    { intros z. reflexivity. }
    split.
    { intros z _. reflexivity. }
    split.
    { intros z _. reflexivity. }
    { reflexivity. }
  - destruct xs as [|a xs]; [discriminate Hlen|].
    simpl in Hlen. apply Nat.succ_inj in Hlen.
    destruct ys as [|b ys]; [inversion Htys|].
    inversion Hndx as [|? ? Hnotin_a Hndx']; subst.
    inversion Hndy as [|? ? Hnotin_b Hndy']; subst.
    inversion Hnr_x as [|? ? Hnres_a Hnr_x']; subst.
    inversion Hnr_y as [|? ? Hnres_b Hnr_y']; subst.
    inversion Htys as [|? ? ? ? Hty_ab Htys']; subst.
    destruct (decide (a = b)) as [Hab|Hab].
    + subst b.
      have Hprotected' : ∀ z, z ∈ a :: protected → z ∉ xs ∧ z ∉ ys.
      { intros z Hz. apply elem_of_cons in Hz as [Hza|Hz].
        - subst z. exact (conj Hnotin_a Hnotin_b).
        - specialize (Hprotected z Hz). simpl in Hprotected.
          split; intro Hzin; [apply (proj1 Hprotected) | apply (proj2 Hprotected)];
            apply elem_of_cons; right; exact Hzin. }
      destruct (IH xs ys (a :: protected) eq_refl Hndx' Hndy' Hnr_x' Hnr_y' Htys' Hprotected')
        as [ren [Hinj [Htyp [Hres [Hfix Hmap]]]]].
      exists ren.
      refine (conj Hinj (conj Htyp (conj Hres (conj _ _)))).
      * intros z Hz. apply Hfix. apply elem_of_cons; right; exact Hz.
      * have Ha_protected : a ∈ a :: protected by (apply elem_of_cons; left; reflexivity).
        simpl. rewrite (Hfix a Ha_protected). f_equal. exact Hmap.
    + have Hswap_inj : Inj (=) (=) (lvar_swap a b) := lvar_swap_inj a b Hab.
      have Hnd_swap : NoDup (map (lvar_swap a b) xs).
      { apply NoDup_map_of_inj; [intros x y; apply Hswap_inj | exact Hndx']. }
      have Hnr_swap : Forall (fun x => ¬ is_reserved x) (map (lvar_swap a b) xs).
      { apply Forall_forall. intros z Hz.
        apply elem_of_list_fmap in Hz as [x [Hx Hxz]].
        rewrite Hx.
        apply lvar_swap_not_reserved; try assumption.
        apply (proj1 (Forall_forall _ _) Hnr_x' x Hxz). }
      have Htys_swap : Forall2 (fun x y => sigma x = sigma y) (map (lvar_swap a b) xs) ys.
      { assert (Haux : ∀ xs0 ys0,
            Forall2 (fun x y => sigma x = sigma y) xs0 ys0 →
            Forall2 (fun x y => sigma x = sigma y) (map (lvar_swap a b) xs0) ys0).
        { intros xs0 ys0 Hxy. induction Hxy; simpl; constructor; auto.
          rewrite lvar_swap_typ; assumption. }
        exact (Haux xs ys Htys'). }
      have Hprotected' : ∀ z, z ∈ b :: protected →
        z ∉ map (lvar_swap a b) xs ∧ z ∉ ys.
      { intros z Hz. apply elem_of_cons in Hz as [Hzb|Hz].
        subst z.
        - split.
          + intro Hb. apply elem_of_list_fmap in Hb as [x [Hxb Hx]].
            apply Hnotin_a. symmetry in Hxb.
            apply (lvar_swap_eq_iff a b x b Hab) in Hxb.
            unfold lvar_swap in Hxb.
            rewrite decide_False in Hxb; [|congruence].
            rewrite decide_True in Hxb; [|reflexivity].
            subst x. exact Hx.
          + exact Hnotin_b.
        - specialize (Hprotected z Hz) as [Hzx Hzy]. split.
          2: { intro Hzin. apply Hzy. right. exact Hzin. }
          intro Hzswap. apply elem_of_list_fmap in Hzswap as [x [Hxswap Hx]].
          have Hza : z ≠ a.
          { set_solver. }
          have Hzb : z ≠ b.
          { set_solver. }
          symmetry in Hxswap.
          apply (lvar_swap_eq_iff a b x z Hab) in Hxswap.
          unfold lvar_swap in Hxswap.
          rewrite decide_False in Hxswap; [|exact Hza].
          rewrite decide_False in Hxswap; [|exact Hzb].
          subst x. apply Hzx. right. exact Hx.
      }
      destruct (IH (map (lvar_swap a b) xs) ys (b :: protected)
        ltac:(rewrite map_length; reflexivity) Hnd_swap Hndy' Hnr_swap Hnr_y' Htys_swap Hprotected')
        as [ren [Hinj [Htyp [Hres [Hfix Hmap]]]]].
      exists (fun z => ren (lvar_swap a b z)).
      repeat split.
      * intros x y Hxy. apply Hswap_inj. apply Hinj. exact Hxy.
      * intro z. rewrite Htyp. apply lvar_swap_typ. exact Hty_ab.
      * intros z Hz. rewrite (lvar_swap_reserved a b Hnres_a Hnres_b z Hz). exact (Hres z Hz).
      * intros z Hz. specialize (Hprotected z Hz) as [Hzx Hzy].
        assert (Hza : z ≠ a).
        { set_solver. }
        assert (Hzb : z ≠ b).
        { set_solver. }
        unfold lvar_swap. rewrite decide_False; [|exact Hza]. rewrite decide_False; [|exact Hzb].
        apply Hfix. right. exact Hz.
      * have Hb_protected : b ∈ b :: protected by (apply elem_of_cons; left; reflexivity).
        simpl. unfold lvar_swap at 1. rewrite decide_True; [|reflexivity].
        rewrite (Hfix b Hb_protected).
        rewrite <- Hmap. rewrite map_map. reflexivity.
Qed.

Definition stk0 : stack := {[ "x" := "x" ]}.
Definition cmask : maskAnnot := {[ "counterInv" ]}.

(* Generic over rho: stk0 only ever binds "x", and read/incr agree that
   "x" is TpLoc (both declare it as their own first argument), so this one
   fact is reusable by both via an explicit rho "x" = TpLoc side
   hypothesis, rather than being pinned to rho_read specifically -- needed
   since read_invblock_step_ext's whole chain (reused byte-for-byte by
   incr) is built on top of it. *)
Lemma stk_type_compat_stk0 (rho : pvar_typs) (Hx : rho "x" = TpLoc) : stk_type_compat rho sigma stk0.
Proof.
  intros v lv Hv. unfold stk0 in Hv.
  apply lookup_singleton_Some in Hv as [<- <-]. exact Hx.
Qed.

Lemma fresh_lvar_stk0 (lv : lvar) : lv ≠ "x" -> fresh_lvar stk0 lv.
Proof.
  intros Hne v0 Heq. unfold stk0 in Heq.
  apply lookup_singleton_Some in Heq as [<- <-]. exact (Hne eq_refl).
Qed.

(* Extending a well-typed/fresh stack at a new (var, lvar) pair stays
   well-typed/fresh -- reused at every FldRd/Assign/CAS/Call step of
   incr/read's own derivations. *)
Lemma stk_type_compat_extend (rho : pvar_typs) (stk : stack) (v lv : var) (tp : typ) :
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

(* Union counterparts of stk_type_compat_extend/fresh_lvar_extend, needed to
   merge stk0 with an extra, disjoint stack fragment recording placeholder
   entries for a procedure's own not-yet-touched locals -- see
   read_invblock_step_ext's own comment for why this is needed instead of
   widening stk0 itself. *)
Lemma stk_type_compat_union (rho : pvar_typs) (stk1 stk2 : stack) :
  stk_type_compat rho sigma stk1 -> stk_type_compat rho sigma stk2 ->
  stk_type_compat rho sigma (stk1 ∪ stk2).
Proof.
  intros H1 H2 v lv Hv.
  apply lookup_union_Some_raw in Hv as [Hv | [Hnone Hv]].
  - exact (H1 v lv Hv).
  - exact (H2 v lv Hv).
Qed.

Lemma fresh_lvar_union (stk1 stk2 : stack) (lv : lvar) :
  fresh_lvar stk1 lv -> fresh_lvar stk2 lv -> fresh_lvar (stk1 ∪ stk2) lv.
Proof.
  intros H1 H2 v0 Hv0.
  apply lookup_union_Some_raw in Hv0 as [Hv0 | [Hnone Hv0]].
  - exact (H1 v0 Hv0).
  - exact (H2 v0 Hv0).
Qed.

(* stk0's own binding survives being unioned with any extra fragment on its
   left -- needed since reflexivity alone doesn't compute through ∪, unlike
   the singleton-literal lookups that worked against stk0 directly. *)
Lemma stk0_union_lookup_x (extra : stack) : (stk0 ∪ extra) !! "x" = Some "x".
Proof. apply lookup_union_Some_l. reflexivity. Qed.

(* An "extra" stack fragment merged into stk0 to widen a procedure's entry
   stack (see read_invblock_step_ext's own comment) never holds anything
   but one of the seven placeholder lvars -- the one invariant every
   concrete extra fragment below satisfies by construction, letting a
   single hypothesis stand in for "extra can't possibly clash with any of
   this file's own internal fresh names", rather than restating that
   freshness fact once per internal name (l_v1/l_new_v1/l_res/l_ret/$v). *)
Definition extra_placeholder (extra : stack) : Prop :=
  ∀ v0 lv0, extra !! v0 = Some lv0 →
    lv0 = "l_ph_int1" ∨ lv0 = "l_ph_int2" ∨ lv0 = "l_ph_bool" ∨ lv0 = "l_ph_unit" ∨
    lv0 = "l_ph_unit2" ∨ lv0 = "l_ph_loc1" ∨ lv0 = "l_ph_loc2".

Lemma fresh_lvar_extra_ph (extra : stack) (Hextra_ph : extra_placeholder extra) (lv : lvar) :
  lv ≠ "l_ph_int1" → lv ≠ "l_ph_int2" → lv ≠ "l_ph_bool" → lv ≠ "l_ph_unit" →
  lv ≠ "l_ph_unit2" →
  lv ≠ "l_ph_loc1" → lv ≠ "l_ph_loc2" →
  fresh_lvar extra lv.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 v0 Heq.
  destruct (Hextra_ph v0 lv Heq) as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    [exact (H1 eq_refl) | exact (H2 eq_refl) | exact (H3 eq_refl) | exact (H4 eq_refl) |
     exact (H5 eq_refl) | exact (H6 eq_refl) | exact (H7 eq_refl)].
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

Lemma entails_lexpra_true (le : LExpr) :
  (forall mp, LExpr_holds le mp) -> assertion_entails (LPure True) (LExprA le).
Proof. exact (AE_LExprA_True sigma le). Qed.

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
Lemma entails_regroup_pre_sym (stk : stack) :
  assertion_entails
    (LAnd (LStack stk) (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                                     (LOwn (LVar "x") "c" (LVar "$v")))
                               (LPure True)))
    (LAnd (LAnd (LStack stk) (LOwn (LVar "x") "c" (LVar "$v")))
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

(* The single, symbolic derivation ExistsElimRule needs for read's
   FldRd, run with counterInv's own existential witness kept as the free
   lvar "$v" rather than substituted -- matching ExistsElimRule's own shape.

   Generalized over an extra, disjointly-merged stack fragment recording
   placeholder entries for a
   procedure's own not-yet-touched locals: all_proc_specs_valid_raven's own
   entry stack must bind every declared local from the start (matching
   RTCallStep's allocate-everything-at-once semantics), not just "x", but
   read's and incr's own extra locals need *different* types at "#ret_val"
   (Int vs Unit) -- incompatible with a single shared stk0. Since every rule
   here only ever inserts into or reads specific keys of the stack (never
   iterates its whole domain), an arbitrary extra fragment merged in via
   stk0 ∪ extra survives untouched through every step, as long as its own
   values avoid "l_v1" (the one fresh name this chain itself introduces). *)
(* Generic over rho (see stk_type_compat_stk0's own comment): reused
   byte-for-byte by incr's own first InvAccessBlock, which needs
   rho_incr, not rho_read, here. *)
Lemma read_inner_step_sym_ext (rho : pvar_typs) (Hx : rho "x" = TpLoc) (extra : stack)
    (Hextra_compat : stk_type_compat rho sigma extra)
    (Hextra_ph : extra_placeholder extra) :
  RavenHoareTriple rho sigma
    (LAnd (LStack (stk0 ∪ extra))
          (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                      (LOwn (LVar "x") "c" (LVar "$v")))
                (LPure True)))
      (FldRd "v1" (Var "x") "c") (cmask ∖ {["counterInv"]}) (cmask ∖ {["counterInv"]})
    (LExists "l_v1" TpInt (LAnd (LStack (<["v1":="l_v1"]> (stk0 ∪ extra))) (LAnd counterInv_body (LPure True)))).
Proof.
  have Hfresh_l_v1 : fresh_lvar extra "l_v1" := fresh_lvar_extra_ph extra Hextra_ph "l_v1"
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate).
  eapply WeakeningRule.
  - eapply FrameRule with
      (r := LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v"))) (LPure True)).
    apply (HeapReadRule rho sigma (stk0 ∪ extra) (cmask ∖ {["counterInv"]}) "v1" (Var "x") (LVar "$v") "c" (LVar "x") "l_v1").
    + simpl. rewrite stk0_union_lookup_x. reflexivity.
    + reflexivity.
    + apply fresh_lvar_union; [apply fresh_lvar_stk0; discriminate | exact Hfresh_l_v1].
    + set_solver.
    + exact (stk_type_compat_union _ _ _ (stk_type_compat_stk0 rho Hx) Hextra_compat).
  - exact (entails_regroup_pre_sym (stk0 ∪ extra)).
  - exact (entails_regroup_post_sym (<["v1":="l_v1"]> (stk0 ∪ extra))).
Qed.

(* Eliminates counterInv's own existential to reach read_inner_step_sym_ext.
   Uses ExistsElimRule (subst-free) at the top-level LExists shape, so the
   LStack-fixed precondition is first commuted into that shape via
   WeakeningRule + entails_and_stack_exists_swap. The witness's well-typedness
   ("$v" : Int) comes directly from sigma's own declaration (sigma "$v" =
   TpInt), via ExistsElimRule's own sigma-consistency premise. *)
Lemma read_fldrd_block_step_ext (rho : pvar_typs) (Hx : rho "x" = TpLoc) (extra : stack)
    (Hextra_compat : stk_type_compat rho sigma extra)
    (Hextra_ph : extra_placeholder extra) :
  RavenHoareTriple rho sigma
    (LAnd (LStack (stk0 ∪ extra)) (LAnd counterInv_body (LPure True)))
      (FldRd "v1" (Var "x") "c") (cmask ∖ {["counterInv"]}) (cmask ∖ {["counterInv"]})
    (LExists "l_v1" TpInt (LAnd (LStack (<["v1":="l_v1"]> (stk0 ∪ extra))) (LAnd counterInv_body (LPure True)))).
Proof.
  have Hfresh_l_v1 : fresh_lvar extra "l_v1" := fresh_lvar_extra_ph extra Hextra_ph "l_v1"
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate).
  have Hfresh_dollarv : fresh_lvar extra "$v" := fresh_lvar_extra_ph extra Hextra_ph "$v"
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate).
  eapply WeakeningRule.
  - apply (ExistsElimRule rho sigma (cmask ∖ {["counterInv"]}) (cmask ∖ {["counterInv"]}) "$v" TpInt
      (LAnd (LStack (stk0 ∪ extra))
            (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                        (LOwn (LVar "x") "c" (LVar "$v")))
                  (LPure True)))
      (FldRd "v1" (Var "x") "c")
      (LExists "l_v1" TpInt (LAnd (LStack (<["v1":="l_v1"]> (stk0 ∪ extra))) (LAnd counterInv_body (LPure True))))).
    + reflexivity.
    + simpl. right. split.
      { apply fresh_lvar_extend;
          [apply fresh_lvar_union; [apply fresh_lvar_stk0; discriminate | exact Hfresh_dollarv] | discriminate]. }
      split; [left; reflexivity | exact I].
    + exact (read_inner_step_sym_ext rho Hx extra Hextra_compat Hextra_ph).
  - eapply assertion_entails_and_stack_exists_swap.
    + apply fresh_lvar_union; [apply fresh_lvar_stk0; discriminate | exact Hfresh_dollarv].
    + simpl. auto.
  - exact (entails_refl _).
Qed.

(* Wraps the FldRd in the InvAccessBlock; recovers counterInv(x) as a bare
   LInv fact on both sides. *)
Lemma read_invblock_step_ext (rho : pvar_typs) (Hx : rho "x" = TpLoc) (extra : stack)
    (Hextra_compat : stk_type_compat rho sigma extra)
    (Hextra_ph : extra_placeholder extra) :
  RavenHoareTriple rho sigma
    (LAnd (LStack (stk0 ∪ extra)) (LInv "counterInv" [LVar "x"]))
      (InvAccessBlock "counterInv" [Var "x"] (FldRd "v1" (Var "x") "c")) cmask cmask
    (LExists "l_v1" TpInt (LAnd (LStack (<["v1":="l_v1"]> (stk0 ∪ extra))) (LInv "counterInv" [LVar "x"]))).
Proof.
  have Hfresh_l_v1 : fresh_lvar extra "l_v1" := fresh_lvar_extra_ph extra Hextra_ph "l_v1"
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate).
  eapply WeakeningRule.
  - eapply (InvAccessBlockRule rho sigma (stk0 ∪ extra) (<["v1":="l_v1"]> (stk0 ∪ extra)) cmask "counterInv" [Var "x"]
      (FldRd "v1" (Var "x") "c") counterInv_record (LPure True) (LPure True) "l_v1" TpInt [LVar "x"]).
    + simpl. rewrite stk0_union_lookup_x. reflexivity.
    + set_solver.
    + exact inv_map_counterInv.
    + reflexivity.
    + constructor; [| constructor]. intros v Hv. simpl in Hv.
      apply elem_of_singleton in Hv as ->. unfold is_reserved. discriminate.
    + exact (stk_type_compat_union _ _ _ (stk_type_compat_stk0 rho Hx) Hextra_compat).
    + apply fresh_lvar_union; [apply fresh_lvar_stk0; discriminate | exact Hfresh_l_v1].
    + unfold is_reserved. discriminate.
    + simpl. exact (read_fldrd_block_step_ext rho Hx extra Hextra_compat Hextra_ph).
  - exact (entails_and_mono _ _ _ _ (entails_refl (LStack (stk0 ∪ extra))) (entails_and_true_intro (LInv "counterInv" [LVar "x"]))).
  - exact (entails_exists_mono "l_v1" TpInt _ _ eq_refl
      (entails_and_mono _ _ _ _ (entails_refl (LStack (<["v1":="l_v1"]> (stk0 ∪ extra))))
                         (entails_and_true_elim (LInv "counterInv" [LVar "x"])))).
Qed.

(* read's own extra fragment: placeholder entries for its two declared
   locals ("v1"/"#ret_val", both TpInt), needed so read_body_step's own
   entry stack binds every declared local from the start (see
   read_invblock_step_ext's comment). Both keys get overwritten before
   ever being read (FldRd rebinds "v1", the final Assign rebinds
   "#ret_val"), so any placeholder value of the right type is safe. *)
Definition extra_read : stack := <["v1" := "l_ph_int1"]> ({[ "#ret_val" := "l_ph_int2" ]}).

Lemma stk_type_compat_extra_read : stk_type_compat rho_read sigma extra_read.
Proof.
  intros v lv Hv. unfold extra_read in Hv.
  apply lookup_insert_Some in Hv as [[<- <-] | [Hne Hv]].
  - reflexivity.
  - apply lookup_singleton_Some in Hv as [<- <-]. reflexivity.
Qed.

Lemma extra_placeholder_read : extra_placeholder extra_read.
Proof.
  intros v0 lv0 Hv0. unfold extra_read in Hv0.
  apply lookup_insert_Some in Hv0 as [[<- <-] | [Hne Hv0]].
  - left. reflexivity.
  - apply lookup_singleton_Some in Hv0 as [<- <-]. right; left. reflexivity.
Qed.

(* The single, symbolic derivation for read's Assign "#ret_val" (Var "v1")
   step: VarAssignmentRule + FrameRule (carrying the re-closed counterInv
   fact through), weakened all the way down to the bare procedure
   postcondition -- neither "l_ret" (the assigned value's own fresh lvar)
   nor the intermediate stack state matter beyond this point. *)
Lemma read_assign_inner_step :
  RavenHoareTriple rho_read sigma
    (LStack (<["v1":="l_v1"]> (stk0 ∪ extra_read)))
      (Assign "#ret_val" (Var "v1")) cmask cmask
    (LExists "l_ret" TpInt (LAnd (LStack (<["#ret_val":="l_ret"]> (<["v1":="l_v1"]> (stk0 ∪ extra_read))))
                            (LExprA (LBinOp EqOp (LVar "l_ret") (LVar "l_v1"))))).
Proof.
  apply (VarAssignmentRule rho_read sigma (<["v1":="l_v1"]> (stk0 ∪ extra_read)) cmask "#ret_val" "l_ret" (Var "v1") (LVar "l_v1") TpInt).
  - reflexivity.
  - reflexivity.
  - apply fresh_lvar_extend;
      [apply fresh_lvar_union; [apply fresh_lvar_stk0; discriminate
        | apply (fresh_lvar_extra_ph extra_read extra_placeholder_read);
          [discriminate | discriminate | discriminate | discriminate | discriminate | discriminate | discriminate]]
      | discriminate].
  - eapply stk_type_compat_extend;
      [eapply stk_type_compat_union; [exact (stk_type_compat_stk0 rho_read eq_refl) | exact stk_type_compat_extra_read]
      | reflexivity | reflexivity].
Qed.

Lemma entails_and_elim_l P Q : assertion_entails (LAnd P Q) P.
Proof. exact (AE_And_Elim_L sigma P Q). Qed.

Lemma entails_true_intro X : assertion_entails X (LPure True).
Proof. exact (AE_True_Intro sigma X). Qed.

(* GhostSkip's own Hoare rule: derived from AssertRule (assert (Val (LitBool
   true)), trivially provable) via WeakeningRule, rather than a bespoke
   RavenHoareTriple constructor -- mirrors SkipRule's own shape exactly
   (arbitrary p, unchanged), but GhostSkip costs no physical step, unlike
   SkipS (see GhostSkip's own comment above incr_body). *)
Lemma ghostskip_step (ρ : pvar_typs) (mask : maskAnnot) (stk : stack) (p : assertion) :
  stk_type_compat ρ sigma stk ->
  RavenHoareTriple ρ sigma (LAnd (LStack stk) p) GhostSkip mask mask (LAnd (LStack stk) p).
Proof.
  intros Hcompat.
  eapply WeakeningRule.
  - apply (AssertRule ρ sigma stk mask (Val (lang.LitBool true)) p (LVal (LitBool true))).
    + reflexivity.
    + reflexivity.
    + exact Hcompat.
  - apply entails_and_mono; [exact (entails_refl _) |].
    eapply entails_trans; [exact (entails_and_true_intro p) |].
    apply entails_and_mono; [exact (entails_refl _) |].
    apply entails_lexpra_true. intros mp. reflexivity.
  - apply entails_and_mono; [exact (entails_refl _) | exact (entails_and_elim_l _ _)].
Qed.

(* No need to carry counterInv's own LInv fact (or the intermediate stack
   state / "l_ret" witness) through to the end: read_postcond doesn't
   restate it (LInv is Persistent -- the caller already keeps their own
   copy from read_precond), so the whole thing weakens straight down to
   LPure True. *)
Lemma read_assign_step :
  RavenHoareTriple rho_read sigma
    (LAnd (LStack (<["v1":="l_v1"]> (stk0 ∪ extra_read))) (LInv "counterInv" [LVar "x"]))
      (Assign "#ret_val" (Var "v1")) cmask cmask
    (LExists "l_v1" TpInt
      (LExists "l_ret" TpInt
        (LAnd (LStack (<["#ret_val":="l_ret"]> (<["v1":="l_v1"]> (stk0 ∪ extra_read))))
              read_postcond))).
Proof.
  eapply WeakeningRule.
  - exact read_assign_inner_step.
  - exact (entails_and_elim_l _ _).
  - eapply AE_Trans.
    + eapply AE_Exists_Mono; [reflexivity |].
      eapply AE_And_Mono; [eapply AE_Refl |].
      unfold read_postcond. eapply AE_True_Intro.
    + eapply AE_Exists_Intro. reflexivity.
Qed.

(* Combines the InvAccessBlock (read_invblock_step_ext) with the Assign
   (read_assign_step) via SequenceRule: read_assign_step's own precondition
   is exactly what read_invblock_step_ext's postcondition existentially
   provides, once "l_v1" is unwrapped via ExistsElimRule (subst-free) --
   straightforward since read_assign_step's own conclusion (read_postcond)
   doesn't mention "l_v1" at all. *)
Lemma read_body_step :
  RavenHoareTriple rho_read sigma
    (LAnd (LStack (stk0 ∪ extra_read)) read_precond)
      read_body cmask cmask
    (LExists "l_v1" TpInt
      (LExists "l_ret" TpInt
        (LAnd (LStack (<["#ret_val":="l_ret"]> (<["v1":="l_v1"]> (stk0 ∪ extra_read))))
              read_postcond))).
Proof.
  unfold read_body, read_precond.
  eapply SequenceRule.
  - exact (read_invblock_step_ext rho_read eq_refl extra_read stk_type_compat_extra_read extra_placeholder_read).
  - apply (ExistsElimRule rho_read sigma cmask cmask "l_v1" TpInt
      (LAnd (LStack (<["v1":="l_v1"]> (stk0 ∪ extra_read))) (LInv "counterInv" [LVar "x"]))
      (Assign "#ret_val" (Var "v1"))
      (LExists "l_v1" TpInt
        (LExists "l_ret" TpInt
          (LAnd (LStack (<["#ret_val":="l_ret"]> (<["v1":="l_v1"]> (stk0 ∪ extra_read))))
                read_postcond)))).
    + reflexivity.
    + simpl. left. reflexivity.
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
   step -- reuse read_invblock_step_ext directly, instantiated at incr's own
   extra fragment. *)

(* incr's own extra fragment: placeholder entries for all four of its
   declared locals ("v1"/"new_v1"/"res"/"#ret_val"), needed for the same
   reason as extra_read -- see read_invblock_step_ext's comment. Can't
   reuse extra_read: incr's own "#ret_val" is TpUnit, read's is TpInt, and
   sigma is one global function, so the same lvar can't have both types. *)
Definition extra_incr : stack :=
  <["v1" := "l_ph_int1"]> (<["new_v1" := "l_ph_int2"]>
    (<["res" := "l_ph_bool"]> (<["call_res" := "l_ph_unit2"]>
      ({[ "#ret_val" := "l_ph_unit" ]})))).

Lemma stk_type_compat_extra_incr : stk_type_compat rho_incr sigma extra_incr.
Proof.
  intros v lv Hv. unfold extra_incr in Hv.
  apply lookup_insert_Some in Hv as [[<- <-] | [Hne1 Hv]]; [reflexivity |].
  apply lookup_insert_Some in Hv as [[<- <-] | [Hne2 Hv]]; [reflexivity |].
  apply lookup_insert_Some in Hv as [[<- <-] | [Hne3 Hv]]; [reflexivity |].
  apply lookup_insert_Some in Hv as [[<- <-] | [Hne4 Hv]]; [reflexivity |].
  apply lookup_singleton_Some in Hv as [<- <-]. reflexivity.
Qed.

Lemma extra_placeholder_incr : extra_placeholder extra_incr.
Proof.
  intros v0 lv0 Hv0. unfold extra_incr in Hv0.
  apply lookup_insert_Some in Hv0 as [[<- <-] | [Hne1 Hv0]]; [left; reflexivity |].
  apply lookup_insert_Some in Hv0 as [[<- <-] | [Hne2 Hv0]]; [right; left; reflexivity |].
  apply lookup_insert_Some in Hv0 as [[<- <-] | [Hne3 Hv0]]; [right; right; left; reflexivity |].
  apply lookup_insert_Some in Hv0 as [[<- <-] | [Hne4 Hv0]];
    [right; right; right; right; left; reflexivity |].
  apply lookup_singleton_Some in Hv0 as [<- <-]. right; right; right; left; reflexivity.
Qed.

Lemma incr_assign_inner_step :
  RavenHoareTriple rho_incr sigma
    (LStack (<["v1":="l_v1"]> (stk0 ∪ extra_incr)))
      (Assign "new_v1" (BinOp AddOp (Var "v1") (Val (lang.LitInt 1)))) cmask cmask
    (LExists "l_new_v1" TpInt (LAnd (LStack (<["new_v1":="l_new_v1"]> (<["v1":="l_v1"]> (stk0 ∪ extra_incr))))
      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))).
Proof.
  apply (VarAssignmentRule rho_incr sigma (<["v1":="l_v1"]> (stk0 ∪ extra_incr)) cmask "new_v1" "l_new_v1"
    (BinOp AddOp (Var "v1") (Val (lang.LitInt 1)))
    (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))) TpInt).
  - reflexivity.
  - reflexivity.
  - apply fresh_lvar_extend;
      [apply fresh_lvar_union; [apply fresh_lvar_stk0; discriminate
        | apply (fresh_lvar_extra_ph extra_incr extra_placeholder_incr);
          [discriminate | discriminate | discriminate | discriminate | discriminate | discriminate | discriminate]]
      | discriminate].
  - eapply stk_type_compat_extend;
      [eapply stk_type_compat_union; [exact (stk_type_compat_stk0 rho_incr eq_refl) | exact stk_type_compat_extra_incr]
      | reflexivity | reflexivity].
Qed.

(* Carries counterInv's LInv fact through the Assign via FrameRule (unlike
   read's own Assign, this one is a *middle* step -- the invariant is still
   needed afterwards for the CAS/FPU block), then regroups the resulting
   LAnd (LExists ...) (LInv ...) back into the LExists-outermost shape via
   entails_exists_and_swap. *)
Lemma incr_assign_step :
  RavenHoareTriple rho_incr sigma
    (LAnd (LStack (<["v1":="l_v1"]> (stk0 ∪ extra_incr))) (LInv "counterInv" [LVar "x"]))
      (Assign "new_v1" (BinOp AddOp (Var "v1") (Val (lang.LitInt 1)))) cmask cmask
    (LExists "l_new_v1" TpInt (LAnd (LAnd (LStack (<["new_v1":="l_new_v1"]> (<["v1":="l_v1"]> (stk0 ∪ extra_incr))))
      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))) (LInv "counterInv" [LVar "x"]))).
Proof.
  eapply WeakeningRule.
  - apply (FrameRule rho_incr sigma cmask cmask (Assign "new_v1" (BinOp AddOp (Var "v1") (Val (lang.LitInt 1))))
      (LStack (<["v1":="l_v1"]> (stk0 ∪ extra_incr)))
      (LExists "l_new_v1" TpInt (LAnd (LStack (<["new_v1":="l_new_v1"]> (<["v1":="l_v1"]> (stk0 ∪ extra_incr))))
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

Definition incr_stk1 : stack := <["new_v1":="l_new_v1"]> (<["v1":="l_v1"]> (stk0 ∪ extra_incr)).

Lemma stk_type_compat_incr_stk1 : stk_type_compat rho_incr sigma incr_stk1.
Proof.
  unfold incr_stk1.
  eapply stk_type_compat_extend;
    [eapply stk_type_compat_extend;
      [eapply stk_type_compat_union; [exact (stk_type_compat_stk0 rho_incr eq_refl) | exact stk_type_compat_extra_incr]
      | reflexivity | reflexivity]
    | reflexivity | reflexivity].
Qed.

Lemma fresh_lvar_incr_stk1 (lv : lvar) :
  lv ≠ "x" -> lv ≠ "l_ph_int1" -> lv ≠ "l_ph_int2" -> lv ≠ "l_ph_bool" -> lv ≠ "l_ph_unit" ->
  lv ≠ "l_ph_unit2" ->
  lv ≠ "l_ph_loc1" -> lv ≠ "l_ph_loc2" -> "l_v1" ≠ lv -> "l_new_v1" ≠ lv -> fresh_lvar incr_stk1 lv.
Proof.
  intros Hx Hphi1 Hphi2 Hphb Hphu Hphu2 Hphl1 Hphl2 Hv1 Hnv1. unfold incr_stk1.
  apply fresh_lvar_extend;
    [apply fresh_lvar_extend;
      [apply fresh_lvar_union; [apply fresh_lvar_stk0; exact Hx
        | apply (fresh_lvar_extra_ph extra_incr extra_placeholder_incr); assumption]
      | exact Hv1]
    | exact Hnv1].
Qed.

(* The CAS itself, framing counterInv's GhostOwn fact -- together with the
   "l_new_v1 = l_v1 + 1" arithmetic fact established by incr_assign_step,
   needed later to discharge Fpu's own fpuValid premise -- through unchanged
   (the Fpu that actually updates the ghost chunk comes later, only on
   success). *)
Lemma incr_cas_step :
  RavenHoareTriple rho_incr sigma
    (LAnd (LStack incr_stk1)
          (LAnd (LOwn (LVar "x") "c" (LVar "$v"))
                (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))))
      (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1")) (cmask ∖ {["counterInv"]}) (cmask ∖ {["counterInv"]})
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
    apply (CASRule rho_incr sigma incr_stk1 (cmask ∖ {["counterInv"]}) "res" (Var "x") "c" (Var "v1") (Var "new_v1")
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

Lemma stk_type_compat_incr_stk2 : stk_type_compat rho_incr sigma incr_stk2.
Proof.
  unfold incr_stk2. eapply stk_type_compat_extend; [exact stk_type_compat_incr_stk1 | reflexivity | reflexivity].
Qed.

Lemma fresh_lvar_incr_stk2 (lv : lvar) :
  lv ≠ "x" -> lv ≠ "l_ph_int1" -> lv ≠ "l_ph_int2" -> lv ≠ "l_ph_bool" -> lv ≠ "l_ph_unit" ->
  lv ≠ "l_ph_unit2" ->
  lv ≠ "l_ph_loc1" -> lv ≠ "l_ph_loc2" ->
  "l_v1" ≠ lv -> "l_new_v1" ≠ lv -> "l_res" ≠ lv -> fresh_lvar incr_stk2 lv.
Proof.
  intros Hx Hphi1 Hphi2 Hphb Hphu Hphu2 Hphl1 Hphl2 Hv1 Hnv1 Hres. unfold incr_stk2.
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
  RavenHoareTriple rho_incr sigma
    (LAnd (LStack incr_stk2)
          (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")))
                (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
      (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
      (cmask ∖ {["counterInv"]}) (cmask ∖ {["counterInv"]})
    (LAnd (LStack incr_stk2) (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_new_v1")))).
Proof.
  eapply WeakeningRule.
  - apply (FPURule rho_incr sigma incr_stk2 (cmask ∖ {["counterInv"]})
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
  RavenHoareTriple rho_incr sigma
    (LAnd (LStack incr_stk2)
          (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "l_v1")))
                      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))
                (LOwn (LVar "x") "c" (LVar "l_new_v1"))))
      (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
      (cmask ∖ {["counterInv"]}) (cmask ∖ {["counterInv"]})
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
  RavenHoareTriple rho_incr sigma
    (LAnd (LStack incr_stk2)
      (LAnd (LAnd (LIte (LBinOp EqOp (LVar "$v") (LVar "l_v1"))
                     (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                     (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false))))))
                   (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                         (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
            (LExprA (LVar "l_res"))))
      (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
      (cmask ∖ {["counterInv"]}) (cmask ∖ {["counterInv"]})
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

(* The IfS's "res = false" branch (GhostSkip): extract, drop the now-unused
   arithmetic fact, repack counterInv unchanged. *)
Lemma incr_false_branch_step :
  RavenHoareTriple rho_incr sigma
    (LAnd (LStack incr_stk2)
      (LAnd (LAnd (LIte (LBinOp EqOp (LVar "$v") (LVar "l_v1"))
                     (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                     (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false))))))
                   (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                         (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
            (LExprA (LUnOp NotBoolOp (LVar "l_res")))))
      GhostSkip
      (cmask ∖ {["counterInv"]}) (cmask ∖ {["counterInv"]})
    (LAnd (LStack incr_stk2) (LAnd counterInv_body (LPure True))).
Proof.
  eapply WeakeningRule.
  - apply (ghostskip_step rho_incr (cmask ∖ {["counterInv"]}) incr_stk2
      (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v"))))).
    exact stk_type_compat_incr_stk2.
  - apply entails_and_mono; [exact (entails_refl _) |].
    eapply entails_trans; [exact (entails_ite_bool_false_framed _ _ _ _ _) |].
    apply entails_and_mono; [exact (entails_refl _) | exact (entails_and_elim_l _ _)].
  - apply entails_and_mono; [exact (entails_refl _) | exact incr_repack_post_v].
Qed.

(* The IfS(res, Fpu, Skip) as a whole. *)
Lemma incr_ifs_res_step :
  RavenHoareTriple rho_incr sigma
    (LAnd (LStack incr_stk2)
          (LAnd (LIte (LBinOp EqOp (LVar "$v") (LVar "l_v1"))
                   (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                   (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false))))))
                (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))))
      (IfS (Var "res")
        (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
        GhostSkip)
      (cmask ∖ {["counterInv"]}) (cmask ∖ {["counterInv"]})
    (LAnd (LStack incr_stk2) (LAnd counterInv_body (LPure True))).
Proof.
  apply (CondRule rho_incr sigma incr_stk2 (cmask ∖ {["counterInv"]})
    (Var "res")
    (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
    GhostSkip
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
   itself: sound because entails is parameterized by sigma, giving
   entails_exists_intro access to Henv (via env_typ_well_defined) to justify
   the witness v' := mp "l_res" against sigma "l_res" = TpBool -- an
   unconditional-over-mp entails could never do this (see entails_exists_intro
   in rrl_lang.v). This existential re-uses "l_res" itself as the bound
   name, which is what makes it possible to eliminate "l_res" again just
   below via ExistsElimRule: LExists's own freshness check is trivially true
   when the queried lvar equals the binder (shadowing), regardless of
   whether the body underneath genuinely mentions it (incr_stk2 does). *)
Lemma incr_ifs_res_step_wrapped :
  RavenHoareTriple rho_incr sigma
    (LAnd (LStack incr_stk2)
          (LAnd (LIte (LBinOp EqOp (LVar "$v") (LVar "l_v1"))
                   (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                   (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false))))))
                (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                      (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))))
      (IfS (Var "res")
        (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
        GhostSkip)
      (cmask ∖ {["counterInv"]}) (cmask ∖ {["counterInv"]})
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
  RavenHoareTriple rho_incr sigma
    (LAnd (LStack incr_stk1)
          (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                      (LOwn (LVar "x") "c" (LVar "$v")))
                (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
      (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
           (IfS (Var "res")
             (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
             GhostSkip))
      (cmask ∖ {["counterInv"]}) (cmask ∖ {["counterInv"]})
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
  - apply (ExistsElimRule rho_incr sigma (cmask ∖ {["counterInv"]}) (cmask ∖ {["counterInv"]}) "l_res" TpBool
      (LAnd (LAnd (LStack incr_stk2)
               (LIte (LBinOp EqOp (LVar "$v") (LVar "l_v1"))
                  (LAnd (LOwn (LVar "x") "c" (LVar "l_new_v1")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool true)))))
                  (LAnd (LOwn (LVar "x") "c" (LVar "$v")) (LExprA (LBinOp EqOp (LVar "l_res") (LVal (LitBool false)))))))
            (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                  (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
      (IfS (Var "res")
        (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
        GhostSkip)
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
  RavenHoareTriple rho_incr sigma
    (LAnd (LStack incr_stk1)
          (LAnd counterInv_body
                (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
      (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
           (IfS (Var "res")
             (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
             GhostSkip))
      (cmask ∖ {["counterInv"]}) (cmask ∖ {["counterInv"]})
    (LExists "l_res" TpBool (LAnd (LStack incr_stk2) (LAnd counterInv_body (LPure True)))).
Proof.
  eapply WeakeningRule.
  - apply (ExistsElimRule rho_incr sigma (cmask ∖ {["counterInv"]}) (cmask ∖ {["counterInv"]}) "$v" TpInt
      (LAnd (LStack incr_stk1)
            (LAnd (LAnd (LGhostOwn (LVar "x") "h" h_ra (LUnOp (RAOfIntOp h_ra) (LVar "$v")))
                        (LOwn (LVar "x") "c" (LVar "$v")))
                  (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
      (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
           (IfS (Var "res")
             (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
             GhostSkip))
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
  RavenHoareTriple rho_incr sigma
    (LAnd (LStack incr_stk1)
          (LAnd (LInv "counterInv" [LVar "x"])
                (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))))
      (InvAccessBlock "counterInv" [Var "x"]
        (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
             (IfS (Var "res")
               (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
               GhostSkip)))
      cmask cmask
    (LExists "l_res" TpBool (LAnd (LStack incr_stk2) (LAnd (LInv "counterInv" [LVar "x"]) (LPure True)))).
Proof.
  eapply (InvAccessBlockRule rho_incr sigma incr_stk1 incr_stk2 cmask "counterInv" [Var "x"]
    (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
         (IfS (Var "res")
           (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
           GhostSkip))
    counterInv_record
    (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1)))))
    (LPure True) "l_res" TpBool [LVar "x"]).
  - reflexivity.
  - set_solver.
  - reflexivity.
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
  RavenHoareTriple rho_incr sigma
    (LAnd (LStack incr_stk2) (LAnd (LInv "counterInv" [LVar "x"]) (LExprA (LUnOp NotBoolOp (LVar "l_res")))))
      (Call "call_res" "incr" [Var "x"]) cmask cmask
    (LExists "l_call" TpUnit
      (LAnd (LStack (<["call_res" := "l_call"]> incr_stk2)) (LPure True))).
Proof.
  eapply WeakeningRule.
  - apply (ProcCallRuleRet rho_incr sigma incr_stk2 cmask "call_res" "incr" [Var "x"] [LVar "x"] "l_call" incr_record).
    + apply fresh_lvar_incr_stk2; discriminate.
    + exact proc_map_incr.
    + reflexivity.
    + reflexivity.
    + exact stk_type_compat_incr_stk2.
    + unfold is_reserved. discriminate.
    + split.
      { constructor; [| constructor]. intros v Hv. simpl in Hv.
        apply elem_of_singleton in Hv as ->. unfold is_reserved. discriminate. }
      { unfold proc_required_mask, incr_record, incr_precond. simpl. set_solver. }
  - apply entails_and_mono; [exact (entails_refl _) |].
    eapply entails_trans; [exact (entails_and_elim_l _ _) |].
    unfold incr_precond. simpl. exact (entails_refl _).
  - simpl. exact (entails_refl _).
Qed.

Lemma incr_retry_step :
  RavenHoareTriple rho_incr sigma
    (LAnd (LStack incr_stk2) (LInv "counterInv" [LVar "x"]))
      (IfS (UnOp NotBoolOp (Var "res")) (Call "call_res" "incr" [Var "x"]) SkipS)
      cmask cmask
    (LExists "l_call" TpUnit
      (LAnd (LStack (<["call_res" := "l_call"]> incr_stk2)) (LPure True))).
Proof.
  apply (CondRule rho_incr sigma incr_stk2 cmask
    (UnOp NotBoolOp (Var "res"))
    (Call "call_res" "incr" [Var "x"])
    SkipS
    (LInv "counterInv" [LVar "x"])
    (LExists "l_call" TpUnit
      (LAnd (LStack (<["call_res" := "l_call"]> incr_stk2)) (LPure True)))
    (LUnOp NotBoolOp (LVar "l_res"))).
  - reflexivity.
  - reflexivity.
  - exact stk_type_compat_incr_stk2.
  - exact incr_retry_true_step.
  - eapply WeakeningRule.
    + apply (SkipRule rho_incr sigma incr_stk2 cmask (LInv "counterInv" [LVar "x"])).
      exact stk_type_compat_incr_stk2.
    + apply entails_and_mono; [exact (entails_refl _) | exact (entails_and_elim_l _ _)].
    + eapply AE_Trans.
      * exact (entails_and_elim_l _ _).
      * eapply AE_Trans.
        -- eapply (AE_Stack_Exists_Rename sigma incr_stk2 "call_res"
              "l_ph_unit2" "l_call" TpUnit).
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply fresh_lvar_incr_stk2; discriminate.
        -- eapply AE_Exists_Mono; [reflexivity |].
           exact (entails_and_true_intro _).
Qed.

Definition incr_final_assertion : assertion :=
  LExists "l_v1" TpInt
    (LExists "l_new_v1" TpInt
      (LExists "l_res" TpBool
        (LExists "l_ph_unit" TpUnit
          (LExists "l_call" TpUnit
            (LAnd (LStack (<["call_res" := "l_call"]> incr_stk2))
                  incr_postcond))))).

(* ----------------------------------------------------------------------- *)
(* incr's full body: nested SequenceRule/ExistsElimRule chaining the four
   pieces, mirroring read_body_step exactly, just three stages deeper. *)
Lemma incr_body_step :
  RavenHoareTriple rho_incr sigma
    (LAnd (LStack (stk0 ∪ extra_incr)) incr_precond)
      incr_body cmask cmask
    incr_final_assertion.
Proof.
  unfold incr_body, incr_precond.
  eapply SequenceRule.
  - exact (read_invblock_step_ext rho_incr eq_refl extra_incr stk_type_compat_extra_incr extra_placeholder_incr).
  - apply (ExistsElimRule rho_incr sigma cmask cmask "l_v1" TpInt
      (LAnd (LStack (<["v1":="l_v1"]> (stk0 ∪ extra_incr))) (LInv "counterInv" [LVar "x"]))
      (Seq (Assign "new_v1" (BinOp AddOp (Var "v1") (Val (lang.LitInt 1))))
           (Seq (InvAccessBlock "counterInv" [Var "x"]
                  (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
                       (IfS (Var "res")
                         (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
                         GhostSkip)))
                (IfS (UnOp NotBoolOp (Var "res")) (Call "call_res" "incr" [Var "x"]) SkipS)))
      incr_final_assertion).
    + reflexivity.
    + unfold incr_final_assertion. simpl. left. reflexivity.
    + eapply SequenceRule.
      * exact incr_assign_step.
      * apply (ExistsElimRule rho_incr sigma cmask cmask "l_new_v1" TpInt
          (LAnd (LAnd (LStack incr_stk1) (LExprA (LBinOp EqOp (LVar "l_new_v1") (LBinOp AddOp (LVar "l_v1") (LVal (LitInt 1))))))
                (LInv "counterInv" [LVar "x"]))
          (Seq (InvAccessBlock "counterInv" [Var "x"]
                 (Seq (CAS "res" (Var "x") "c" (Var "v1") (Var "new_v1"))
                      (IfS (Var "res")
                        (Fpu (Var "x") "h" h_ra (UnOp (RAOfIntOp h_ra) (Var "v1")) (UnOp (RAOfIntOp h_ra) (Var "new_v1")))
                        GhostSkip)))
               (IfS (UnOp NotBoolOp (Var "res")) (Call "call_res" "incr" [Var "x"]) SkipS))
          incr_final_assertion).
        -- reflexivity.
        -- unfold incr_final_assertion. simpl. right. left. reflexivity.
        -- eapply SequenceRule.
           ++ eapply WeakeningRule.
              ** exact incr_invblock2_step.
              ** eapply entails_trans.
                 --- exact (entails_and_assoc_r _ _ _).
                 --- apply entails_and_mono; [exact (entails_refl _) | exact (entails_and_comm _ _)].
              ** exact (entails_refl _).
           ++ apply (ExistsElimRule rho_incr sigma cmask cmask "l_res" TpBool
                 (LAnd (LStack incr_stk2) (LAnd (LInv "counterInv" [LVar "x"]) (LPure True)))
                 (IfS (UnOp NotBoolOp (Var "res")) (Call "call_res" "incr" [Var "x"]) SkipS)
                 incr_final_assertion).
                --- reflexivity.
                --- unfold incr_final_assertion. simpl. right. right. left. reflexivity.
                --- eapply WeakeningRule.
                    +++ exact incr_retry_step.
                    +++ apply entails_and_mono; [exact (entails_refl _) | exact (entails_and_true_elim _)].
                    +++ unfold incr_final_assertion.
                        eapply AE_Trans with (Q :=
                          LExists "l_ph_unit" TpUnit
                            (LExists "l_call" TpUnit
                              (LAnd (LStack (<["call_res" := "l_call"]> incr_stk2)) (LPure True)))).
                        *** eapply AE_Exists_Intro. reflexivity.
                        *** eapply AE_Trans with (Q :=
                              LExists "l_res" TpBool
                                (LExists "l_ph_unit" TpUnit
                                  (LExists "l_call" TpUnit
                                    (LAnd (LStack (<["call_res" := "l_call"]> incr_stk2)) (LPure True))))).
                            { eapply AE_Exists_Intro. reflexivity. }
                            eapply AE_Trans with (Q :=
                              LExists "l_new_v1" TpInt
                                (LExists "l_res" TpBool
                                  (LExists "l_ph_unit" TpUnit
                                    (LExists "l_call" TpUnit
                                      (LAnd (LStack (<["call_res" := "l_call"]> incr_stk2)) (LPure True)))))).
                            { eapply AE_Exists_Intro. reflexivity. }
                            eapply AE_Exists_Intro. reflexivity.
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
   nothing beyond this file's existing rho_make/sigma/entails machinery (both
   already keyed at "x" : TpLoc) is needed either -- only a fresh, empty
   entry stack (make has no args, unlike read/incr). *)

(* Binds both of make's own declared locals ("x"/"#ret_val", both TpLoc --
   make has no args at all) from the start, matching
   all_proc_specs_valid_raven's own entry stack shape -- see
   read_invblock_step_ext's comment for why this is needed in general.
   Unlike read/incr, make's own chain isn't shared with any other
   procedure, so no rho/extra-fragment generalization is needed here:
   stk_make0 is just this shape directly. *)
Definition stk_make0 : stack := <["x" := "l_ph_loc1"]> ({[ "#ret_val" := "l_ph_loc2" ]}).

Lemma stk_type_compat_stk_make0 : stk_type_compat rho_make sigma stk_make0.
Proof.
  intros v lv Hv. unfold stk_make0 in Hv.
  apply lookup_insert_Some in Hv as [[<- <-] | [Hne Hv]].
  - reflexivity.
  - apply lookup_singleton_Some in Hv as [<- <-]. reflexivity.
Qed.

Lemma fresh_lvar_stk_make0 (lv : lvar) : lv ≠ "l_ph_loc1" -> lv ≠ "l_ph_loc2" -> fresh_lvar stk_make0 lv.
Proof.
  intros Hne1 Hne2 v0 Heq. unfold stk_make0 in Heq.
  apply lookup_insert_Some in Heq as [[<- <-] | [Hne' Heq]].
  - exact (Hne1 eq_refl).
  - apply lookup_singleton_Some in Heq as [<- <-]. exact (Hne2 eq_refl).
Qed.

(* The ghost cell's initial value, at the generic ra_of_int operation for
   h_ra's own RA instance -- matches RAOfIntOp's own interp_lexpr semantics
   exactly (both resolve the very same ResourceAlgebra instance for
   RA_carrier (ra_map h_ra)), so no dependent-type transport is ever needed
   to relate the two. *)
Definition h0 : RA_carrier (ra_map h_ra) := ra_of_int 0.

Lemma h0_valid : @ra_base.valid _ (RA_inst (ra_map h_ra)) h0.
Proof. unfold h0. change (mn_valid (mn_of_int 0)). by exists 0%nat. Qed.

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

Lemma make_alloc_step_ext (msk : maskAnnot) :
  RavenHoareTriple rho_make sigma
    (LStack stk_make0)
      (Alloc "x" [("c", lang.LitInt 0)]) msk msk
    (LExists "x" TpLoc (LAnd (LStack (<["x":="x"]> stk_make0)) (LAnd counterInv_body (LPure True)))).
Proof.
  eapply WeakeningRule.
  - apply (HeapAllocRule rho_make sigma stk_make0 msk "x"
      [("c", lang.LitInt 0)] [("h", existT h_ra h0)] "x").
    + apply fresh_lvar_stk_make0; discriminate.
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

Lemma make_alloc_step :
  RavenHoareTriple rho_make sigma
    (LStack stk_make0)
      (Alloc "x" [("c", lang.LitInt 0)]) cmask cmask
    (LExists "x" TpLoc (LAnd (LStack (<["x":="x"]> stk_make0)) (LAnd counterInv_body (LPure True)))).
Proof. exact (make_alloc_step_ext cmask). Qed.

(* fold counterInv(x): InvAllocRule at the freshly allocated location, with
   counterInv_body's own "x" substituted to itself (subst_map is the
   identity map {"x" := LVar "x"} here, exactly as at every other
   InvAccessBlockRule/InvAllocRule call site in this file that reuses
   stk0's pvar-"x"-to-lvar-"x" naming), so subst counterInv_body {"x" :=
   LVar "x"} reduces to counterInv_body itself via simpl. *)
Lemma make_foldinv_step_ext (msk : maskAnnot) :
  RavenHoareTriple rho_make sigma
    (LAnd (LStack (<["x":="x"]> stk_make0)) (LAnd counterInv_body (LPure True)))
      (FoldInv "counterInv" [Var "x"]) msk (msk ∪ {["counterInv"]})
    (LAnd (LStack (<["x":="x"]> stk_make0)) (LAnd (LInv "counterInv" [LVar "x"]) (LPure True))).
Proof.
  apply (InvAllocRule rho_make sigma (<["x":="x"]> stk_make0) msk "counterInv" [Var "x"]
    counterInv_record (LPure True) [LVar "x"]).
  - reflexivity.
  - exact inv_map_counterInv.
  - reflexivity.
  - constructor; [| constructor]. intros v Hv. simpl in Hv.
    apply elem_of_singleton in Hv as ->. unfold is_reserved. discriminate.
  - eapply stk_type_compat_extend; [exact stk_type_compat_stk_make0 | reflexivity | reflexivity].
Qed.

Lemma make_foldinv_step :
  RavenHoareTriple rho_make sigma
    (LAnd (LStack (<["x":="x"]> stk_make0)) (LAnd counterInv_body (LPure True)))
      (FoldInv "counterInv" [Var "x"]) cmask cmask
    (LAnd (LStack (<["x":="x"]> stk_make0)) (LAnd (LInv "counterInv" [LVar "x"]) (LPure True))).
Proof.
  have Hmask : cmask ∪ {["counterInv"]} = cmask by set_solver.
  rewrite <- Hmask.
  exact (make_foldinv_step_ext cmask).
Qed.

(* make's own Assign "#ret_val" (Var "x") step: bare VarAssignmentRule,
   picking "l_x_ret" (typed TpLoc in sigma) as the assignment's own fresh
   witness. Mirrors read_assign_inner_step/incr_assign_inner_step exactly. *)
Lemma make_assign_inner_step_ext (msk : maskAnnot) :
  RavenHoareTriple rho_make sigma
    (LStack (<["x":="x"]> stk_make0))
      (Assign "#ret_val" (Var "x")) msk msk
    (LExists "l_x_ret" TpLoc (LAnd (LStack (<["#ret_val":="l_x_ret"]> (<["x":="x"]> stk_make0)))
                             (LExprA (LBinOp EqOp (LVar "l_x_ret") (LVar "x"))))).
Proof.
  apply (VarAssignmentRule rho_make sigma (<["x":="x"]> stk_make0) msk "#ret_val" "l_x_ret"
    (Var "x") (LVar "x") TpLoc).
  - reflexivity.
  - reflexivity.
  - apply fresh_lvar_extend; [apply fresh_lvar_stk_make0; discriminate | discriminate].
  - eapply stk_type_compat_extend; [exact stk_type_compat_stk_make0 | reflexivity | reflexivity].
Qed.

Lemma make_assign_inner_step :
  RavenHoareTriple rho_make sigma
    (LStack (<["x":="x"]> stk_make0))
      (Assign "#ret_val" (Var "x")) cmask cmask
    (LExists "l_x_ret" TpLoc (LAnd (LStack (<["#ret_val":="l_x_ret"]> (<["x":="x"]> stk_make0)))
                             (LExprA (LBinOp EqOp (LVar "l_x_ret") (LVar "x"))))).
Proof. exact (make_assign_inner_step_ext cmask). Qed.

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
Lemma make_assign_step_ext (msk : maskAnnot) :
  RavenHoareTriple rho_make sigma
    (LAnd (LStack (<["x":="x"]> stk_make0)) (LAnd (LInv "counterInv" [LVar "x"]) (LPure True)))
      (Assign "#ret_val" (Var "x")) msk msk
    (LExists "x" TpLoc
      (LExists "l_x_ret" TpLoc
        (LAnd (LStack (<["#ret_val":="l_x_ret"]> (<["x":="x"]> stk_make0)))
          (LAnd (LInv "counterInv" [LVar "l_x_ret"]) (LPure True))))).
Proof.
  eapply WeakeningRule.
  - apply (FrameRule rho_make sigma msk msk (Assign "#ret_val" (Var "x"))
      (LStack (<["x":="x"]> stk_make0))
      (LExists "l_x_ret" TpLoc (LAnd (LStack (<["#ret_val":="l_x_ret"]> (<["x":="x"]> stk_make0)))
                               (LExprA (LBinOp EqOp (LVar "l_x_ret") (LVar "x")))))
      (LAnd (LInv "counterInv" [LVar "x"]) (LPure True))
      (make_assign_inner_step_ext msk)).
  - exact (entails_refl _).
  - eapply AE_Trans.
    2: { eapply AE_Exists_Intro. reflexivity. }
    eapply AE_Trans.
    { eapply AE_Exists_And_Swap_R. simpl. split; [apply Forall_singleton; set_solver | exact I]. }
    eapply AE_Exists_Mono; [reflexivity | ].
    eapply AE_Trans; [eapply AE_And_Assoc_R |].
    eapply AE_And_Mono; [eapply AE_Refl |].
    exact (AE_LExpr_Subst_Eq_Congr sigma "l_x_ret" "x"
      (LAnd (LInv "counterInv" [LVar "l_x_ret"]) (LPure True)) (conj I I)).
Qed.

Lemma make_assign_step :
  RavenHoareTriple rho_make sigma
    (LAnd (LStack (<["x":="x"]> stk_make0)) (LAnd (LInv "counterInv" [LVar "x"]) (LPure True)))
      (Assign "#ret_val" (Var "x")) cmask cmask
    (LExists "x" TpLoc
      (LExists "l_x_ret" TpLoc
        (LAnd (LStack (<["#ret_val":="l_x_ret"]> (<["x":="x"]> stk_make0)))
          (LAnd (LInv "counterInv" [LVar "l_x_ret"]) (LPure True))))).
Proof. exact (make_assign_step_ext cmask). Qed.

(* make's full body: HeapAllocRule, then InvAllocRule, then the Assign that
   exposes the allocated/folded location as "#ret_val"'s own fresh witness
   -- mirrors read_body_step's own SequenceRule/ExistsElimRule shape for
   the alloc, with one more SequenceRule stage folded in for the trailing
   Assign. Concludes at an "l_x_ret"-existential, not raw make_postcond
   itself -- see make_assign_step's own comment for why the latter is
   unreachable directly from a derivation. *)
Lemma make_body_step_ext (msk : maskAnnot) :
  RavenHoareTriple rho_make sigma
    (LAnd (LStack stk_make0) make_precond)
      make_body msk (msk ∪ {["counterInv"]})
    (LExists "x" TpLoc
      (LExists "l_x_ret" TpLoc
        (LAnd (LStack (<["#ret_val":="l_x_ret"]> (<["x":="x"]> stk_make0)))
          (LAnd (LInv "counterInv" [LVar "l_x_ret"]) (LPure True))))).
Proof.
  unfold make_body, make_precond.
  eapply SequenceRule.
  - eapply WeakeningRule.
    + exact (make_alloc_step_ext msk).
    + exact (entails_and_true_elim (LStack stk_make0)).
    + exact (entails_refl _).
  - apply (ExistsElimRule rho_make sigma msk (msk ∪ {["counterInv"]}) "x" TpLoc
      (LAnd (LStack (<["x":="x"]> stk_make0)) (LAnd counterInv_body (LPure True)))
      (Seq (FoldInv "counterInv" [Var "x"]) (Assign "#ret_val" (Var "x")))
      (LExists "x" TpLoc
        (LExists "l_x_ret" TpLoc
          (LAnd (LStack (<["#ret_val":="l_x_ret"]> (<["x":="x"]> stk_make0)))
            (LAnd (LInv "counterInv" [LVar "l_x_ret"]) (LPure True)))))).
    + reflexivity.
    + simpl. left. reflexivity.
    + eapply SequenceRule.
      * exact (make_foldinv_step_ext msk).
      * exact (make_assign_step_ext (msk ∪ {["counterInv"]})).
Qed.

Lemma make_body_step :
  RavenHoareTriple rho_make sigma
    (LAnd (LStack stk_make0) make_precond)
      make_body cmask cmask
    (LExists "x" TpLoc
      (LExists "l_x_ret" TpLoc
        (LAnd (LStack (<["#ret_val":="l_x_ret"]> (<["x":="x"]> stk_make0)))
          (LAnd (LInv "counterInv" [LVar "l_x_ret"]) (LPure True))))).
Proof.
  have Hmask : cmask ∪ {["counterInv"]} = cmask by set_solver.
  rewrite <- Hmask.
  exact (make_body_step_ext cmask).
Qed.

Lemma make_body_spec_ext (msk : maskAnnot) :
  RavenHoareTriple rho_make sigma
    (LAnd (LStack stk_make0) make_precond)
      make_body msk (msk ∪ {["counterInv"]})
    (LExists "x" TpLoc
      (LExists "l_x_ret" TpLoc
        (LAnd (LStack (<["#ret_val":="l_x_ret"]> (<["x":="x"]> stk_make0)))
          (LInv "counterInv" [LVar "l_x_ret"])))).
Proof.
  eapply WeakeningRule.
  - exact (make_body_step_ext msk).
  - exact (entails_refl _).
  - eapply AE_Exists_Mono; [reflexivity |].
    eapply AE_Exists_Mono; [reflexivity |].
    eapply AE_And_Mono; [eapply AE_Refl |].
    exact (entails_and_true_elim _).
Qed.

(* ----------------------------------------------------------------------- *)
(* ProgramWF: pin proc_map/inv_map/pred_map/inv_set to this program's own
   concrete records and discharge every field.

   proc_map/inv_map are concrete (RProg above), so "pinning" them is
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

(* proc_bodies_translate: every registered procedure's own body actually
   compiles (trnsl_stmt _ <> Error) -- purely syntactic, decided entirely
   by trnsl_stmt's own structural recursion over each concrete body,
   computed once per procedure via vm_compute/discriminate. Not vacuous:
   incr_body's CAS-failure branch has to be GhostSkip rather than SkipS
   for this to hold, since its InvAccessBlock's one allowed physical step
   is already spent on the CAS (see GhostSkip's own comment above
   incr_body). *)
Lemma Hpbt : proc_bodies_translate (P:=RProg).
Proof.
  apply proc_map_forall.
  - (* make *) vm_compute. discriminate.
  - (* read *) vm_compute. discriminate.
  - (* incr *) vm_compute. discriminate.
Qed.

(* The body-validity package below also asks for the ordinary syntactic
   well-definedness judgment.  Keep the two non-recursive bodies in named
   lemmas: they are exactly the constructor trees used by the package, and
   spelling them out here avoids coupling that bookkeeping to the much
   larger semantic derivations above. *)
Lemma make_body_well_defined : @stmt_well_defined RProg rho_make make_body.
Proof.
  unfold make_body. repeat constructor; vm_compute; eauto.
Qed.

Lemma read_body_well_defined : @stmt_well_defined RProg rho_read read_body.
Proof.
  unfold read_body. repeat constructor; vm_compute; eauto.
Qed.

Lemma incr_body_well_defined : @stmt_well_defined RProg rho_incr incr_body.
Proof.
  unfold incr_body, GhostSkip.
  repeat constructor; try (vm_compute; eauto).
  eapply (CallTp rho_incr "call_res" "incr" incr_record [Var "x"]).
  - vm_compute. set_solver.
  - exact proc_map_incr.
  - reflexivity.
  - vm_compute. eauto.
  - constructor; [reflexivity | constructor].
  - vm_compute. reflexivity.
Qed.

(* The body-validity proofs use assertion renaming from the translation layer.
   Keep this import after the concrete resource-algebra instance above to avoid
   shadowing its [valid] field during construction. *)

Lemma ren_not_reserved (ren : lvar → lvar) :
  Inj (=) (=) ren →
  (∀ z, is_reserved z → ren z = z) →
  ∀ z, ¬ is_reserved z → ¬ is_reserved (ren z).
Proof.
  intros Hinj Hres z Hnz Hz.
  have Heq : ren (ren z) = ren z := Hres _ Hz.
  apply Hinj in Heq. apply Hnz. rewrite <- Heq. exact Hz.
Qed.

Lemma proc_entry_all_nodup {pr : ProcRecord} (dll : proc_entry_lvars sigma pr) :
  NoDup (dll_args dll ++ dll_locals dll).
Proof.
  apply NoDup_app. repeat split.
  - exact (dll_args_nodup dll).
  - intros lv Ha Hl. exact (dll_disjoint dll lv Ha Hl).
  - exact (dll_locals_nodup dll).
Qed.

Lemma proc_entry_all_not_reserved {pr : ProcRecord} (dll : proc_entry_lvars sigma pr) :
  Forall (fun lv => ¬ is_reserved lv) (dll_args dll ++ dll_locals dll).
Proof. apply Forall_app. split; [exact (dll_args_not_reserved dll) | exact (dll_locals_not_reserved dll)]. Qed.

Lemma ren_ne_target (ren : lvar → lvar) (Hinj : Inj (=) (=) ren)
    (x y target : lvar) :
  ren x = target → y ≠ x → ren y ≠ target.
Proof.
  intros Htarget Hne Heq.
  rewrite <- Htarget in Heq. apply Hinj in Heq. exact (Hne Heq).
Qed.

Lemma incr_entry_names_nodup :
  NoDup ["x"; "l_ph_int1"; "l_ph_int2"; "l_ph_bool"; "l_ph_unit2"; "l_ph_unit"].
Proof.
  constructor; [set_solver |].
  constructor; [set_solver |].
  constructor; [set_solver |].
  constructor; [set_solver |].
  constructor; [set_solver |].
  constructor; [set_solver | constructor].
Qed.

Lemma incr_live_names_nodup :
  NoDup ["l_v1"; "l_new_v1"; "l_res"; "l_ph_unit"; "l_call"].
Proof.
  constructor; [set_solver |].
  constructor; [set_solver |].
  constructor; [set_solver |].
  constructor; [set_solver |].
  constructor; [set_solver | constructor].
Qed.

Lemma make_entry_names_nodup : NoDup ["l_ph_loc1"; "l_ph_loc2"].
Proof.
  constructor; [set_solver |].
  constructor; [set_solver | constructor].
Qed.

Lemma read_entry_names_nodup : NoDup ["x"; "l_ph_int1"; "l_ph_int2"].
Proof.
  constructor; [set_solver |].
  constructor; [set_solver |].
  constructor; [set_solver | constructor].
Qed.
Lemma make_body_valid :
  @stmt_well_defined RProg (proc_pvar_typs make_record) (proc_body_of make_record) ∧
  ∀ msk, proc_required_mask make_record ⊆ msk → msk ⊆ inv_set →
  ∀ dll : proc_entry_lvars sigma make_record,
    ∃ stk_final lv_ret xs msk_post,
      stk_final !! "#ret_val" = Some lv_ret ∧
      ¬ is_reserved lv_ret ∧ lv_ret ∈ xs.*1 ∧
      proc_ret_typ_opt make_record = Some (sigma lv_ret) ∧
      msk_post ⊆ inv_set ∧ msk_post ⊆ msk ∪ proc_grants_mask make_record ∧
      NoDup xs.*1 ∧
      Forall (λ xt, sigma xt.1 = xt.2 ∧ ¬ is_reserved xt.1) xs ∧
      Forall (λ xt, xt.1 ∉ dll_args dll) xs ∧
      (∀ x lv, stk_final !! x = Some lv → lv ∈ dll_args dll ∨ lv ∈ xs.*1) ∧
      RavenHoareTriple (proc_pvar_typs make_record) sigma
        (LAnd (LStack (assoc_map (proc_args_of make_record ++ proc_locals_of make_record).*1
                                  (dll_args dll ++ dll_locals dll)))
          (subst (proc_precond_of make_record)
             (lvar_subst_map (proc_args_of make_record).*1 (dll_args dll))))
        (proc_body_of make_record) msk msk_post
        (lvar_exists_list xs
          (LAnd (LStack stk_final)
            (subst (proc_postcond_of make_record)
              (<["#ret_val" := LVar lv_ret]>
                (lvar_subst_map (proc_args_of make_record).*1 (dll_args dll)))))).
Proof.
  split; [exact make_body_well_defined |].
  intros msk Hreq Hmsk dll.
  have Halen := dll_args_len dll. have Hllen := dll_locals_len dll.
  simpl in Halen, Hllen.
  destruct (dll_args dll) as [|arg args] eqn:Ha; [|discriminate Halen].
  destruct (dll_locals dll) as [|lx locals] eqn:Hl; [discriminate Hllen|].
  destruct locals as [|lr locals]; [discriminate Hllen|].
  destruct locals as [|extra locals]; [|discriminate Hllen].
  have Htarget_nd : NoDup [lx; lr].
  { have H := proc_entry_all_nodup dll. rewrite Ha Hl in H. simpl in H. exact H. }
  have Htarget_nr : Forall (fun z => ¬ is_reserved z) [lx; lr].
  { have H := proc_entry_all_not_reserved dll. rewrite Ha Hl in H. simpl in H. exact H. }
  have Htyped := dll_locals_typed dll. rewrite Hl in Htyped. simpl in Htyped.
  inversion Htyped as [|? ? ? ? Hlx Htyped']; subst.
  inversion Htyped' as [|? ? ? ? Hlr Hnil]; subst.
  destruct (finite_lvar_renaming ["l_ph_loc1"; "l_ph_loc2"] [lx; lr] [])
    as [ren [Hinj [Htyp [Hres [Hfix Hmap]]]]].
  - exact make_entry_names_nodup.
  - exact Htarget_nd.
  - repeat constructor; not_reserved.
  - exact Htarget_nr.
  - constructor; [simpl; symmetry; exact Hlx |].
    constructor; [simpl; symmetry; exact Hlr | constructor].
  - intros z Hz. inversion Hz.
  - simpl in Hmap. injection Hmap as Hph1 Hph2.
  have Hx_nr : ¬ is_reserved (ren "x") := ren_not_reserved ren Hinj Hres "x" ltac:(not_reserved).
  have Hr_nr : ¬ is_reserved (ren "l_x_ret") := ren_not_reserved ren Hinj Hres "l_x_ret" ltac:(not_reserved).
  exists (<["#ret_val" := ren "l_x_ret"]>
            (<["x" := ren "x"]>
              (<["x" := lx]> ({[ "#ret_val" := lr ]})))).
  exists (ren "l_x_ret").
  exists [(ren "x", TpLoc); (ren "l_x_ret", TpLoc)].
  exists (msk ∪ {["counterInv"]}).
  repeat match goal with |- _ /\ _ => split end.
  + reflexivity.
  + exact Hr_nr.
  + simpl. right. left.
  + simpl. rewrite Htyp. reflexivity.
  + rewrite inv_set_eq. rewrite inv_set_eq in Hmsk.
    intros i Hi. apply elem_of_union in Hi as [Hi | Hi].
    * exact (Hmsk _ Hi).
    * exact Hi.
  + unfold proc_grants_mask, make_record, make_postcond. simpl. reflexivity.
  + have Hneq : ren "x" ≠ ren "l_x_ret".
    { intro Heq. apply Hinj in Heq. discriminate. }
    change (NoDup [ren "x"; ren "l_x_ret"]).
    constructor.
    * rewrite elem_of_list_singleton. exact Hneq.
    * exact (NoDup_singleton _).
  + constructor.
    * split; [rewrite Htyp; reflexivity | exact Hx_nr].
    * constructor.
      -- split; [rewrite Htyp; reflexivity | exact Hr_nr].
      -- constructor.
  + constructor.
    * rewrite elem_of_nil. tauto.
    * constructor; [rewrite elem_of_nil; tauto | constructor].
  + intros v lv Hv. simpl in Hv.
    apply lookup_insert_Some in Hv as [[<- <-] | [Hret Hv]].
    { right. simpl. right. left. }
    apply lookup_insert_Some in Hv as [[<- <-] | [Hxv Hv]].
    { right. simpl. left. }
    apply lookup_insert_Some in Hv as [[<- <-] | [_ Hv]]; [congruence |].
    apply lookup_singleton_Some in Hv as [<- <-]. congruence.
  + pose proof (RavenHoareTriple_rename ren Hinj Hres counter_monotonic_ProgramWF
      pred_map_empty rho_make sigma Htyp _ _ _ _ _ (make_body_spec_ext msk)) as Htr.
    have Hentry : ren <$> stk_make0 = <["x" := lx]> ({[ "#ret_val" := lr ]}).
    { unfold stk_make0. apply map_eq. intros k. rewrite lookup_fmap.
      destruct (decide (k = "x")) as [-> | Hkx].
      - rewrite !lookup_insert. simpl. rewrite Hph1. reflexivity.
      - rewrite lookup_insert_ne; [|exact (not_eq_sym Hkx)].
        destruct (decide (k = "#ret_val")) as [-> | Hkr].
        + rewrite !lookup_singleton. simpl. rewrite Hph2. reflexivity.
        + rewrite lookup_singleton_ne; [|exact (not_eq_sym Hkr)].
          rewrite lookup_insert_ne; [|exact (not_eq_sym Hkx)].
          rewrite lookup_singleton_ne; [|exact (not_eq_sym Hkr)]. reflexivity. }
    have Hfinal :
      ren <$> (<["#ret_val":="l_x_ret"]> (<["x":="x"]> stk_make0)) =
      <["#ret_val" := ren "l_x_ret"]>
        (<["x" := ren "x"]> (<["x" := lx]> ({[ "#ret_val" := lr ]}))).
    { rewrite fmap_insert. rewrite fmap_insert. rewrite Hentry. reflexivity. }
    simpl in Htr. rewrite Hentry Hfinal in Htr. exact Htr.
Qed.
Lemma incr_body_valid :
  @stmt_well_defined RProg (proc_pvar_typs incr_record) (proc_body_of incr_record) ∧
  ∀ msk, proc_required_mask incr_record ⊆ msk → msk ⊆ inv_set →
  ∀ dll : proc_entry_lvars sigma incr_record,
    ∃ stk_final lv_ret xs msk_post,
      stk_final !! "#ret_val" = Some lv_ret ∧
      ¬ is_reserved lv_ret ∧ lv_ret ∈ xs.*1 ∧
      proc_ret_typ_opt incr_record = Some (sigma lv_ret) ∧
      msk_post ⊆ inv_set ∧ msk_post ⊆ msk ∪ proc_grants_mask incr_record ∧
      NoDup xs.*1 ∧
      Forall (λ xt, sigma xt.1 = xt.2 ∧ ¬ is_reserved xt.1) xs ∧
      Forall (λ xt, xt.1 ∉ dll_args dll) xs ∧
      (∀ x lv, stk_final !! x = Some lv → lv ∈ dll_args dll ∨ lv ∈ xs.*1) ∧
      RavenHoareTriple (proc_pvar_typs incr_record) sigma
        (LAnd (LStack (assoc_map (proc_args_of incr_record ++ proc_locals_of incr_record).*1
                                  (dll_args dll ++ dll_locals dll)))
          (subst (proc_precond_of incr_record)
             (lvar_subst_map (proc_args_of incr_record).*1 (dll_args dll))))
        (proc_body_of incr_record) msk msk_post
        (lvar_exists_list xs
          (LAnd (LStack stk_final)
            (subst (proc_postcond_of incr_record)
              (<["#ret_val" := LVar lv_ret]>
                (lvar_subst_map (proc_args_of incr_record).*1 (dll_args dll)))))).
Proof.
  split; [exact incr_body_well_defined |].
  intros msk Hreq Hmsk dll.
  have Hmask : msk = cmask.
  { have Hreq' := Hreq.
    unfold proc_required_mask, incr_record, incr_precond in Hreq'. simpl in Hreq'.
    have Hmsk' := Hmsk. rewrite inv_set_eq in Hmsk'.
    apply set_eq. intros i. split; [exact (Hmsk' i) | exact (Hreq' i)]. }
  subst msk.
  have Halen := dll_args_len dll. have Hllen := dll_locals_len dll.
  simpl in Halen, Hllen.
  destruct (dll_args dll) as [|dx dxs] eqn:Ha; [discriminate Halen |].
  destruct dxs as [|extra_args dxs]; [|discriminate Halen].
  destruct (dll_locals dll) as [|dv1 dlocals] eqn:Hl; [discriminate Hllen |].
  destruct dlocals as [|dnew dlocals]; [discriminate Hllen |].
  destruct dlocals as [|dres dlocals]; [discriminate Hllen |].
  destruct dlocals as [|dcall dlocals]; [discriminate Hllen |].
  destruct dlocals as [|dret dlocals]; [discriminate Hllen |].
  destruct dlocals as [|extra_locals dlocals]; [|discriminate Hllen].
  have Htarget_nd : NoDup [dx; dv1; dnew; dres; dcall; dret].
  { have H := proc_entry_all_nodup dll. rewrite Ha Hl in H. simpl in H. exact H. }
  have Htarget_nr : Forall (fun z => ¬ is_reserved z) [dx; dv1; dnew; dres; dcall; dret].
  { have H := proc_entry_all_not_reserved dll. rewrite Ha Hl in H. simpl in H. exact H. }
  have Hargs_typed := dll_args_typed dll. rewrite Ha in Hargs_typed. simpl in Hargs_typed.
  inversion Hargs_typed as [|? ? ? ? Hdx Hargs_nil]; subst.
  have Htyped := dll_locals_typed dll. rewrite Hl in Htyped. simpl in Htyped.
  inversion Htyped as [|? ? ? ? Hdv1 Htyped1]; subst.
  inversion Htyped1 as [|? ? ? ? Hdnew Htyped2]; subst.
  inversion Htyped2 as [|? ? ? ? Hdres Htyped3]; subst.
  inversion Htyped3 as [|? ? ? ? Hdcall Htyped4]; subst.
  inversion Htyped4 as [|? ? ? ? Hdret Hnil]; subst.
  destruct (finite_lvar_renaming
      ["x"; "l_ph_int1"; "l_ph_int2"; "l_ph_bool"; "l_ph_unit2"; "l_ph_unit"]
      [dx; dv1; dnew; dres; dcall; dret] [])
    as [ren [Hinj [Htyp [Hres [Hfix Hmap]]]]].
  - exact incr_entry_names_nodup.
  - exact Htarget_nd.
  - repeat constructor; not_reserved.
  - exact Htarget_nr.
  - constructor; [simpl; symmetry; exact Hdx |].
    constructor; [simpl; symmetry; exact Hdv1 |].
    constructor; [simpl; symmetry; exact Hdnew |].
    constructor; [simpl; symmetry; exact Hdres |].
    constructor; [simpl; symmetry; exact Hdcall |].
    constructor; [simpl; symmetry; exact Hdret | constructor].
  - intros z Hz. inversion Hz.
  - simpl in Hmap. injection Hmap as Hx Hpint1 Hpint2 Hpbool Hpunit2 Hpunit.
  have Hv1_nr : ¬ is_reserved (ren "l_v1") := ren_not_reserved ren Hinj Hres "l_v1" ltac:(not_reserved).
  have Hnew_nr : ¬ is_reserved (ren "l_new_v1") := ren_not_reserved ren Hinj Hres "l_new_v1" ltac:(not_reserved).
  have Hres_nr : ¬ is_reserved (ren "l_res") := ren_not_reserved ren Hinj Hres "l_res" ltac:(not_reserved).
  have Hret_nr : ¬ is_reserved (ren "l_ph_unit") := ren_not_reserved ren Hinj Hres "l_ph_unit" ltac:(not_reserved).
  have Hcall_nr : ¬ is_reserved (ren "l_call") := ren_not_reserved ren Hinj Hres "l_call" ltac:(not_reserved).
  exists (ren <$> (<["call_res" := "l_call"]> incr_stk2)).
  exists (ren "l_ph_unit").
  exists [(ren "l_v1", TpInt); (ren "l_new_v1", TpInt); (ren "l_res", TpBool);
          (ren "l_ph_unit", TpUnit); (ren "l_call", TpUnit)].
  exists cmask.
  repeat match goal with |- _ /\ _ => split end.
  + have Hlookup : (<["call_res" := "l_call"]> incr_stk2) !! "#ret_val" =
        Some "l_ph_unit".
    { unfold incr_stk2, incr_stk1, stk0, extra_incr.
      repeat (rewrite lookup_insert_ne; [|discriminate]).
      rewrite lookup_union.
      rewrite lookup_singleton_ne; [|discriminate].
      reflexivity. }
    apply lookup_fmap_Some.
    exists "l_ph_unit". split; [reflexivity | exact Hlookup].
  + exact Hret_nr.
  + simpl. right. right. right. left.
  + simpl. rewrite Htyp. reflexivity.
  + rewrite inv_set_eq. reflexivity.
  + unfold proc_required_mask, incr_record, incr_precond in Hreq. simpl in Hreq.
    unfold proc_grants_mask, incr_record, incr_postcond. simpl.
    unfold cmask. intros i Hi. apply elem_of_union_l. exact (Hreq _ Hi).
  + change (NoDup [ren "l_v1"; ren "l_new_v1"; ren "l_res"; ren "l_ph_unit"; ren "l_call"]).
    change (NoDup (ren <$> ["l_v1"; "l_new_v1"; "l_res"; "l_ph_unit"; "l_call"])).
    apply (NoDup_fmap_2_strong ren).
    { intros x y _ _ Heq. exact (Hinj _ _ Heq). }
    { exact incr_live_names_nodup. }
  + constructor.
    * split; [rewrite Htyp; reflexivity | exact Hv1_nr].
    * constructor.
      -- split; [rewrite Htyp; reflexivity | exact Hnew_nr].
      -- constructor.
         ++ split; [rewrite Htyp; reflexivity | exact Hres_nr].
         ++ constructor.
            ** split; [rewrite Htyp; reflexivity | exact Hret_nr].
            ** constructor.
               --- split; [rewrite Htyp; reflexivity | exact Hcall_nr].
               --- constructor.
  + have Hv1_arg : ren "l_v1" ≠ dx :=
      ren_ne_target ren Hinj "x" "l_v1" dx Hx ltac:(discriminate).
    have Hnew_arg : ren "l_new_v1" ≠ dx :=
      ren_ne_target ren Hinj "x" "l_new_v1" dx Hx ltac:(discriminate).
    have Hres_arg : ren "l_res" ≠ dx :=
      ren_ne_target ren Hinj "x" "l_res" dx Hx ltac:(discriminate).
    have Hret_arg : ren "l_ph_unit" ≠ dx :=
      ren_ne_target ren Hinj "x" "l_ph_unit" dx Hx ltac:(discriminate).
    have Hcall_arg : ren "l_call" ≠ dx :=
      ren_ne_target ren Hinj "x" "l_call" dx Hx ltac:(discriminate).
    constructor; [rewrite elem_of_list_singleton; exact Hv1_arg |].
    constructor; [rewrite elem_of_list_singleton; exact Hnew_arg |].
    constructor; [rewrite elem_of_list_singleton; exact Hres_arg |].
    constructor; [rewrite elem_of_list_singleton; exact Hret_arg |].
    constructor; [rewrite elem_of_list_singleton; exact Hcall_arg | constructor].
  + intros v lv Hv.
    apply lookup_fmap_Some in Hv as [lv0 [<- Hv]].
    unfold incr_stk2, incr_stk1, stk0, extra_incr in Hv.
    apply lookup_insert_Some in Hv as [[<- <-] | [Hcall Hv]].
    { right. simpl. right. right. right. right. left. }
    apply lookup_insert_Some in Hv as [[<- <-] | [Hresv Hv]].
    { right. simpl. right. right. left. }
    apply lookup_insert_Some in Hv as [[<- <-] | [Hnew Hv]].
    { right. simpl. right. left. }
    apply lookup_insert_Some in Hv as [[<- <-] | [Hv1 Hv]].
    { right. simpl. left. }
    apply lookup_union_Some_raw in Hv as [Hv | [_ Hv]].
    { apply lookup_singleton_Some in Hv as [<- <-].
      left. simpl. rewrite Hx. left. }
    apply lookup_insert_Some in Hv as [[<- <-] | [_ Hv]]; [congruence |].
    apply lookup_insert_Some in Hv as [[<- <-] | [_ Hv]]; [congruence |].
    apply lookup_insert_Some in Hv as [[<- <-] | [_ Hv]]; [congruence |].
    apply lookup_insert_Some in Hv as [[<- <-] | [_ Hv]]; [congruence |].
    apply lookup_singleton_Some in Hv as [<- <-].
    right. simpl. right. right. right. left.
  + pose proof (RavenHoareTriple_rename ren Hinj Hres counter_monotonic_ProgramWF
      pred_map_empty rho_incr sigma Htyp _ _ _ _ _ incr_body_step) as Htr.
    have Hentry : ren <$> (stk0 ∪ extra_incr) =
      assoc_map (proc_args_of incr_record ++ proc_locals_of incr_record).*1
        [dx; dv1; dnew; dres; dcall; dret].
    { unfold stk0, extra_incr, assoc_map.
      rewrite map_fmap_union. rewrite map_fmap_singleton.
      repeat rewrite fmap_insert.
      rewrite Hx Hpint1 Hpint2 Hpbool Hpunit2 Hpunit.
      reflexivity. }
    simpl in Htr. rewrite Hentry in Htr. rewrite Hx in Htr. exact Htr.
Qed.
Lemma read_body_valid :
  @stmt_well_defined RProg (proc_pvar_typs read_record) (proc_body_of read_record) ∧
  ∀ msk, proc_required_mask read_record ⊆ msk → msk ⊆ inv_set →
  ∀ dll : proc_entry_lvars sigma read_record,
    ∃ stk_final lv_ret xs msk_post,
      stk_final !! "#ret_val" = Some lv_ret ∧
      ¬ is_reserved lv_ret ∧ lv_ret ∈ xs.*1 ∧
      proc_ret_typ_opt read_record = Some (sigma lv_ret) ∧
      msk_post ⊆ inv_set ∧ msk_post ⊆ msk ∪ proc_grants_mask read_record ∧
      NoDup xs.*1 ∧
      Forall (λ xt, sigma xt.1 = xt.2 ∧ ¬ is_reserved xt.1) xs ∧
      Forall (λ xt, xt.1 ∉ dll_args dll) xs ∧
      (∀ x lv, stk_final !! x = Some lv → lv ∈ dll_args dll ∨ lv ∈ xs.*1) ∧
      RavenHoareTriple (proc_pvar_typs read_record) sigma
        (LAnd (LStack (assoc_map (proc_args_of read_record ++ proc_locals_of read_record).*1
                                  (dll_args dll ++ dll_locals dll)))
          (subst (proc_precond_of read_record)
             (lvar_subst_map (proc_args_of read_record).*1 (dll_args dll))))
        (proc_body_of read_record) msk msk_post
        (lvar_exists_list xs
          (LAnd (LStack stk_final)
            (subst (proc_postcond_of read_record)
              (<["#ret_val" := LVar lv_ret]>
                (lvar_subst_map (proc_args_of read_record).*1 (dll_args dll)))))).
Proof.
  split; [exact read_body_well_defined |].
  intros msk Hreq Hmsk dll.
  have Hmask : msk = cmask.
  { have Hreq' := Hreq.
    unfold proc_required_mask, read_record, read_precond in Hreq'. simpl in Hreq'.
    have Hmsk' := Hmsk. rewrite inv_set_eq in Hmsk'.
    apply set_eq. intros i. split; [exact (Hmsk' i) | exact (Hreq' i)]. }
  subst msk.
  have Halen := dll_args_len dll. have Hllen := dll_locals_len dll.
  simpl in Halen, Hllen.
  destruct (dll_args dll) as [|arg args] eqn:Ha; [discriminate Halen |].
  destruct args as [|extra_arg args]; [|discriminate Halen].
  destruct (dll_locals dll) as [|lx locals] eqn:Hl; [discriminate Hllen|].
  destruct locals as [|lr locals]; [discriminate Hllen |].
  destruct locals as [|extra locals]; [|discriminate Hllen].
  have Htarget_nd : NoDup [arg; lx; lr].
  { have H := proc_entry_all_nodup dll. rewrite Ha Hl in H. simpl in H. exact H. }
  have Htarget_nr : Forall (fun z => ¬ is_reserved z) [arg; lx; lr].
  { have H := proc_entry_all_not_reserved dll. rewrite Ha Hl in H. simpl in H. exact H. }
  have Harg_typed := dll_args_typed dll. rewrite Ha in Harg_typed. simpl in Harg_typed.
  inversion Harg_typed as [|? ? ? ? Harg Hargs_nil]; subst.
  have Htyped := dll_locals_typed dll. rewrite Hl in Htyped. simpl in Htyped.
  inversion Htyped as [|? ? ? ? Hlx Htyped']; subst.
  inversion Htyped' as [|? ? ? ? Hlr Hlocals_nil]; subst.
  destruct (finite_lvar_renaming ["x"; "l_ph_int1"; "l_ph_int2"] [arg; lx; lr] [])
    as [ren [Hinj [Htyp [Hres [Hfix Hmap]]]]].
  - exact read_entry_names_nodup.
  - exact Htarget_nd.
  - repeat constructor; not_reserved.
  - exact Htarget_nr.
  - constructor; [simpl; symmetry; exact Harg |].
    constructor; [simpl; symmetry; exact Hlx |].
    constructor; [simpl; symmetry; exact Hlr | constructor].
  - intros z Hz. inversion Hz.
  - simpl in Hmap. injection Hmap as Hxmap Hph1 Hph2.
  have Hx_nr : ¬ is_reserved (ren "x") := ren_not_reserved ren Hinj Hres "x" ltac:(not_reserved).
  have Hv1_nr : ¬ is_reserved (ren "l_v1") := ren_not_reserved ren Hinj Hres "l_v1" ltac:(not_reserved).
  have Hret_nr : ¬ is_reserved (ren "l_ret") := ren_not_reserved ren Hinj Hres "l_ret" ltac:(not_reserved).
  exists (ren <$> (<["#ret_val" := "l_ret"]>
            (<["v1" := "l_v1"]> (stk0 ∪ extra_read)))).
  exists (ren "l_ret").
  exists [(ren "l_v1", TpInt); (ren "l_ret", TpInt)].
  exists cmask.
  repeat match goal with |- _ /\ _ => split end.
  + rewrite fmap_insert. rewrite fmap_insert. simpl. reflexivity.
  + exact Hret_nr.
  + simpl. right. left.
  + simpl. rewrite Htyp. reflexivity.
  + rewrite inv_set_eq. reflexivity.
  + unfold proc_grants_mask, read_record, read_postcond. simpl.
    intros i Hi. apply elem_of_union_l. exact Hi.
  + have Hneq : ren "l_v1" ≠ ren "l_ret".
    { intro Heq. apply Hinj in Heq. discriminate. }
    change (NoDup [ren "l_v1"; ren "l_ret"]).
    constructor.
    * rewrite elem_of_list_singleton. exact Hneq.
    * exact (NoDup_singleton _).
  + constructor.
    * split; [simpl; rewrite Htyp; reflexivity | exact Hv1_nr].
    * constructor.
      -- split; [simpl; rewrite Htyp; reflexivity | exact Hret_nr].
      -- constructor.
  + have Hv1_arg : ren "l_v1" ≠ arg :=
      ren_ne_target ren Hinj "x" "l_v1" arg Hxmap ltac:(discriminate).
    have Hret_arg : ren "l_ret" ≠ arg :=
      ren_ne_target ren Hinj "x" "l_ret" arg Hxmap ltac:(discriminate).
    constructor; [rewrite elem_of_list_singleton; exact Hv1_arg |].
    constructor; [rewrite elem_of_list_singleton; exact Hret_arg | constructor].
  + intros v lv Hv.
    apply lookup_fmap_Some in Hv as [lv0 [<- Hv]].
    unfold stk0, extra_read in Hv.
    apply lookup_insert_Some in Hv as [[<- <-] | [Hretv Hv]].
    { right. simpl. right. left. }
    apply lookup_insert_Some in Hv as [[<- <-] | [Hv1v Hv]].
    { right. simpl. left. }
    apply lookup_union_Some_raw in Hv as [Hv | [_ Hv]].
    * apply lookup_singleton_Some in Hv as [<- <-].
      left. rewrite elem_of_list_singleton. exact Hxmap.
    * apply lookup_insert_Some in Hv as [[<- <-] | [_ Hv]]; [congruence |].
      apply lookup_singleton_Some in Hv as [<- <-]. congruence.
  + pose proof (RavenHoareTriple_rename ren Hinj Hres counter_monotonic_ProgramWF
      pred_map_empty rho_read sigma Htyp _ _ _ _ _ read_body_step) as Htr.
    have Hentry : ren <$> (stk0 ∪ extra_read) =
        <["x" := arg]> (<["v1" := lx]> ({[ "#ret_val" := lr ]})).
    { unfold stk0, extra_read.
      rewrite map_fmap_union. rewrite map_fmap_singleton.
      repeat rewrite fmap_insert.
      rewrite Hxmap Hph1 Hph2. reflexivity. }
    have Hfinal :
      ren <$> (<["#ret_val":="l_ret"]> (<["v1":="l_v1"]> (stk0 ∪ extra_read))) =
      <["#ret_val" := ren "l_ret"]>
        (<["v1" := ren "l_v1"]> (ren <$> (stk0 ∪ extra_read))).
    { rewrite fmap_insert. rewrite fmap_insert. reflexivity. }
    simpl in Htr. rewrite Hxmap Hentry Hfinal in Htr. exact Htr.
Qed.
Lemma counter_monotonic_all_proc_specs_valid_raven :
  @all_proc_specs_valid_raven RProg sigma.
Proof.
  unfold all_proc_specs_valid_raven.
  apply proc_map_forall.
  - exact make_body_valid.
  - exact read_body_valid.
  - exact incr_body_valid.
Qed.

(* The semantic soundness theorem allocates the ghost heap and invariant
   token names itself.  Consequently its ProgramWF premise is uniform in
   those freshly chosen names.  All structural fields are inherited from
   the concrete witness above; the three name/namespace fields are
   immediate because this program has exactly one invariant. *)

Local Instance counter_invTokenGpreS : invTokenGpreS Σ :=
  {| invtoken_pre_inG := invtoken_inG |}.

Lemma counter_monotonic_ProgramWF_allocated
    (gamma_g gamma_i : gname) :
  @rrl_lang.ProgramWF Σ (mkInvTokenG gamma_i)
    RProg
    (mkGhostConfig (nroot .@ "ghost_heap") (nroot .@ "counterInv") gamma_g).
Proof.
  destruct counter_monotonic_ProgramWF.
  constructor; try assumption.
  - rewrite inv_set_eq. intros inv1 inv2 Hin1 Hin2 _.
    apply elem_of_singleton in Hin1 as ->.
    apply elem_of_singleton in Hin2 as ->. reflexivity.
  - rewrite inv_set_eq. intros inv1 inv2 Hin1 Hin2 Hne.
    apply elem_of_singleton in Hin1 as ->.
    apply elem_of_singleton in Hin2 as ->. contradiction.
  - rewrite inv_set_eq. intros inv' Hin.
    apply elem_of_singleton in Hin as ->.
    apply ndot_ne_disjoint. congruence.
Qed.

End CounterMonotonic.

Section CounterMonotonicSoundnessSetup.
  Context {Σ : gFunctors} `{!invTokenGpreS Σ}.

  Local Instance counter_proof_invTokenG : invTokenG Σ :=
    mkInvTokenG 1%positive.

Section CounterMonotonicSoundness.
  Context {I : Type} (Gs : I -> cmra) `{!inGs Σ Gs}.
  Context `{!inG Σ (authR (gmap.gmapUR heap_addr (agreeR gnameO)))}.
  Context `{!simpLangG Σ}.
  Context (wh : Γ_witness Gs h_ra).

  Theorem counter_monotonic_soundness :
    all_proc_tbl_chunks (RProg:=RProg) -∗
    |={⊤}=> ∃ gamma_g gamma_i,
      all_proc_specs_valid_iris Gs sigma (RProg:=RProg)
        (G:=mkGhostConfig (nroot .@ "ghost_heap")
              (nroot .@ "counterInv") gamma_g)
        (Γ:=Γ0 Gs h_ra wh)
        (invTokenG0:=mkInvTokenG gamma_i).
  Proof.
    iApply (raven_soundness Gs RProg h_ra wh "counterInv" inv_set_eq
      (nroot .@ "ghost_heap") (nroot .@ "counterInv")
      ghost_heap_namespace_disjoint_counterInv sigma
      counter_monotonic_ProgramWF_allocated Hsigma_rich Hpbt
      counter_monotonic_all_proc_specs_valid_raven).
  Qed.
End CounterMonotonicSoundness.

Definition counter_monotonic_initial_state : lang.state :=
  lang.State ∅ (trnsl.translated_proc_map (RProg:=RProg)) ∅ 0.

Lemma counter_monotonic_initial_state_wf :
  ghost_state.state_wf counter_monotonic_initial_state.
Proof.
  unfold counter_monotonic_initial_state.
  apply ghost_state.mk_state_wf.
  - exact (Z.le_refl 0).
  - intros k v Hlookup. rewrite lookup_empty in Hlookup. discriminate.
  - intros l f v Hlookup. rewrite lookup_empty in Hlookup. discriminate.
  - intros k frame Hlookup. rewrite lookup_empty in Hlookup. discriminate.
Qed.

Section CounterMonotonicInitializedSoundness.
  Context {I : Type} (Gs : I -> cmra) `{!inGs Σ Gs}.
  Context `{!inG Σ (authR (gmap.gmapUR heap_addr (agreeR gnameO)))}.
  Context `{!invGS Σ} `{!heapGpreS Σ}.
  Context (wh : Γ_witness Gs h_ra).

  Theorem counter_monotonic_soundness_initialized :
    ⊢ |={⊤}=> ∃ gamma_h gamma_s gamma_p gamma_d gamma_g gamma_i,
      let hG := initialized_heapG gamma_h gamma_s gamma_p gamma_d in
      let sG := initialized_simpLangG gamma_h gamma_s gamma_p gamma_d in
      @ghost_state.state_interp Σ hG counter_monotonic_initial_state ∗
      @all_proc_specs_valid_iris I Gs Σ inGs0 inG0 sG RProg
        (mkGhostConfig (nroot .@ "ghost_heap")
          (nroot .@ "counterInv") gamma_g)
        (Γ0 Gs h_ra wh) (mkInvTokenG gamma_i) sigma.
  Proof.
    iApply (raven_soundness_initialized Gs RProg h_ra wh "counterInv"
      inv_set_eq (nroot .@ "ghost_heap") (nroot .@ "counterInv")
      ghost_heap_namespace_disjoint_counterInv sigma
      counter_monotonic_ProgramWF_allocated Hsigma_rich Hpbt
      counter_monotonic_all_proc_specs_valid_raven
      counter_monotonic_initial_state eq_refl
      counter_monotonic_initial_state_wf).
  Qed.
End CounterMonotonicInitializedSoundness.

End CounterMonotonicSoundnessSetup.
