(* The monotonic-natural resource algebra: a plain monotone nat -- comp/frame
   is max, and a frame-preserving update is exactly "go up". This is the
   fragment of Auth[MaxNat] the counter_monotonic examples actually need:
   nothing here ever holds a separate authoritative/fragment split, so there
   is no need to formalize Auth on top of it.
   Extracted out of counter_monotonic.v (a pre-redesign example scheduled to
   leave the default build) so that the redesigned counter examples do not
   have to import it just to get this resource algebra. *)
From stdpp Require Import gmap namespaces.
From raven Require Import runtime.ra_base.

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

Module CounterRAConfig.
  Definition ra_map (_ : ra_name) : RA_Pack := MonoNatPack.
End CounterRAConfig.

(* Isolates the ra_map h_ra = MonoNatPack rewrite (needed to fall back from
   the RA-generic ra_of_int/fpuValid to their concrete MonoNat definitions)
   into one small lemma, so incr's own Fpu-step proof doesn't have to fight
   the dependent types directly. *)
Lemma h_ra_fpuValid_mono (z1 z2 : Z) :
  z2 = (z1 + 1)%Z ->
  @fpuValid (RA_carrier (CounterRAConfig.ra_map h_ra)) (ra_inst_instance (CounterRAConfig.ra_map h_ra)) (ra_of_int z1) (ra_of_int z2).
Proof.
  intros ->. change (mn_fpuValid (mn_of_int z1) (mn_of_int (z1 + 1))).
  apply mn_of_int_mono.
Qed.
