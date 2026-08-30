From stdpp Require Export strings.
From stdpp Require Import countable.

(* Names identify the resource algebras that program values may carry. *)
Definition ra_name := string.

(* Resource algebras usable as RA-typed program values.  This lives below
   the language syntax because RA elements are ordinary runtime values. *)
Class ResourceAlgebra (A : Type) := {
  comp : A -> A -> A;
  frame : A -> A -> A;
  valid : A -> Prop;
  valid_dec :: forall x : A, Decision (valid x);
  fpuValid : A -> A -> Prop;
  fpuValid_dec :: forall x y : A, Decision (fpuValid x y);
  fpuAxiom : forall x y, fpuValid x y -> valid x /\ valid y /\ forall c, (valid (comp x c) -> valid (comp y c));
  ra_id : A;
  ra_id_comp : forall x, comp ra_id x = x;
  ra_id_valid : valid ra_id;
  comp_comm : forall x y, comp x y = comp y x;
  comp_assoc : forall x y z, comp (comp x y) z = comp x (comp y z);
  comp_valid : forall x y, valid (comp x y) -> valid x /\ valid y;
  frame_id : forall x, valid x -> frame x ra_id = x;
  comp_frame_inv : forall x y, valid (frame x y) -> comp (frame x y) y = x;
  weak_frame_comp_inv : forall x y, valid (comp x y) -> valid (frame (comp x y) y);
  ra_of_int : Z -> A;
}.

Record RA_Pack := {
  RA_carrier :> Type;
  RA_carrier_eqdec :> EqDecision RA_carrier;
  RA_carrier_countable :> Countable RA_carrier;
  RA_inst :> ResourceAlgebra RA_carrier;
}.

(* RA_Pack's coercion fields are not class instance fields, so expose them
   explicitly to typeclass search. *)
Global Instance ra_carrier_eqdec_instance (r : RA_Pack) : EqDecision (RA_carrier r) :=
  RA_carrier_eqdec r.
Global Instance ra_carrier_countable_instance (r : RA_Pack) : Countable (RA_carrier r) :=
  RA_carrier_countable r.
Global Instance ra_inst_instance (r : RA_Pack) : ResourceAlgebra (RA_carrier r) :=
  RA_inst r.

Module Type RA_CONFIG.
  Parameter ra_map : ra_name -> RA_Pack.
End RA_CONFIG.
