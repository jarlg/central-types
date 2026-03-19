From HoTT Require Import HoTT.
(* TODO: refine the imports later as needed. *)

From CentralTypes Require Import BAut1 Bands Central ProjectiveLemmas Reflections
  Torsor TorsorTangent Spheres.

(** * In this file, we study projective spaces and their tangent bundles *)

Open Scope pointed_scope.

(** For any type [B] and type family [E : B -> Type] giving the "elements" of term of type [B], we can define associated spheres, projective spaces and their tangent bundles. *)

(** We will think of a map [f : X -> B] as describing a bundle of "B's" over [X], namely the bundle classified by [E o f].  But we will describe the classifying map [f] via *its* classifying map, [B -> Type]. *)

(** The motivating example is the universal bundle over [BH]. *)
Definition universal (BH : pType)
  : BH -> Type
  := fun t => (pt = t).

(** A map [E : BH -> Type] can also be thought of as a type [E pt] with an action of [H].  The universal bundle represents the right-action of [H] on itself. *)

(** We say that a type family is "torsorial" if it is equivalent to the universal family. *)
Definition torsorial {B : pType} (E : B -> Type)
  := forall t : B, E t <~> (pt = t).

(** The total space of a bundle.  When [B] is [BH], this gives the quotient of [E pt] by the action of [H]. *)
Definition tot {B : Type} (E : B -> Type) : Type
  := { t : B & E t}.

(** This is the same as [pr1], except that [E] is an explicit argument. *)
Definition pr1' {B : Type} (E : B -> Type)
  : tot E -> B
  := pr1.

(** A characterizing property of torsorial families. *)
Definition contr_tot_universal (BH : pType)
  : Contr (tot (universal BH))
  := _.

(** The trivial bundle.  When [B] is [BH], this represents the trivial action of [H] on [X]. *)
Definition trivial_bundle (B : Type) (X : Type)
  : B -> Type
  := fun t => X.

(** The total space of the bundle with contractible fibers is the base.  When [B] is [BH], this says that the quotient of the action of [H] on the unit type is [BH]. *)
Definition tot_trivial_bundle_unit {B : Type}
  : tot (trivial_bundle B Unit) <~> B
  := Build_Equiv _ _ pr1 _.

(** Given two B-bundles, we can form the fibrewise join. *)
Definition fibrewise_join {B : Type} (E E' : B -> Type)
  : B -> Type
  := fun t => Join (E t) (E' t).

(** The n-fold fibrewise join power. *)
Definition fibrewise_join_power {B : Type} (E : B -> Type) (n : nat)
  : B -> Type
  := fun t => join_power (E t) n.

(** The maps classifying the projective spaces of [B] relative to [E]. *)
Definition projective_bundle {B : Type} (E : B -> Type) (n : nat)
  : B -> Type
  := fibrewise_join_power E n.

(** The projective space is the total space. *)
Definition projective_space {B : Type} (E : B -> Type) (n : nat)
  := tot (projective_bundle E n).

(** And this map classifies its tautological bundle. *)
Definition projective_taut {B : Type} (E : B -> Type) (n : nat)
  : projective_space E n -> Type
  := E o pr1.

(** To recover the "classical" projective spaces, we apply this to the universal bundle. *)
Definition projective_space_BH (BH : pType) (n : nat)
  := projective_space (universal BH) n.

(** We can specialize these to produce the real and complex projective spaces. However, it is more convenient to describe these special cases using a bundle that is equivalent to the universal bundle. *)
Definition RP_oo := pBAut Bool.
Definition RP_oo_taut : RP_oo -> Type := fun b => b.1.
Definition RP (n : nat) := projective_space RP_oo_taut n.
Definition RP_taut (n : nat) := projective_taut RP_oo_taut n.
(* Note that the indexing is off by one.  [RP 0] is empty, [RP 1] is contractible, etc.  This shift in indexing makes some base cases easier. Also observe that [projective_bundle RP_oo_taut n] sends [Bool] to [join_power Bool n], which is equivalent to the (n-1)-sphere, and [RP n] is the quotient of this sphere by the antipodal action. *)

(** We will work with [Join Bool Bool] as our model of the circle and [pBAut1 S1] as our model of K(Z, 2). *)
Definition S1 := Join Bool Bool.
Definition CP_oo := pBAut1 S1.
Definition CP_oo_taut : CP_oo -> Type := fun s : BAut1 S1 => s.1.
Definition CP (n : nat) := projective_space CP_oo_taut n.
Definition CP_taut (n : nat) := projective_taut CP_oo_taut n.
(* Again, the indexing is one off from usual. *)

Definition RP_torsor `{Univalence} (t : RP_oo) : torsor Bool t.1
  := equiv_inhab_baut_bool_bool true t.

(* [BCM:defn:tau-RPn] *)
Definition RP_tau `{Univalence} (n : nat) : RP n -> Type
  := fun x => match x with (t; s) => tau (RP_torsor t) reflection_bool n s end.

(** To show that oriented circles are torsors, we'll use that [S1] is central. *)

Definition pS1 := Build_pType S1 (joinl true).

(** [psphere 1] is central.  We already know that K(Z, 1) is central, but we haven't formalized an equivalence to the circle, so it's easiest to just do this directly. *)
Global Instance central_psphere1 `{Univalence} : Central (psphere 1).
Proof.
  rapply central_connected_hspace_pequiv_set.
  (* That [psphere 1] is an H-space is found by typeclass search. *)
  (* It remains to show that [psphere 1 <~>* psphere 1] is an h-prop. *)
  rapply pequiv_hset_pequiv_pmap.
  (* For this, it's enough to show [psphere 1 ->* psphere 1] is an h-prop.  We know the latter is equivalent to the loop space, which typeclass search then handles. *)
  exact (istrunc_equiv_istrunc _ (pmap_from_psphere_iterated_loops 1 (psphere 1))^-1* ).
Defined.

(** [pS1] is central. *)
Global Instance central_pS1 `{Univalence} : Central pS1.
Proof.
  (* We prove this by giving a pointed equivalence to [psphere 1]. *)
  rapply (central_pequiv_central (A:=psphere 1)).
  snapply Build_pEquiv'.
  - change (Susp (Sphere 0) <~> Join Bool Bool).
    refine (_ oE emap Susp equiv_S0_Bool).
    symmetry; apply equiv_join_susp.
  - reflexivity.
Defined.

Definition CP_torsor `{Univalence} (t : CP_oo): torsor S1 t.1.
Proof.
  unfold CP_oo, pBAut1, pointed_type in *.
  intro x.
  (* Since [pS1] is central, [ev1'] is an equivalence.  The inverse of this equivalence takes a point [x] to an equivalence in [S1 <~> t.1] along with a proof that it is in the component of the identity map.  The ".1" extracts the equivalence. *)
  exact ((@equiv_ev_band _ pS1 isequiv_ev1' t)^-1 x).1.
Defined.

(* Part of [BCM:cor:reflection-circle] *)
Definition reflection_S1 : reflection (@equiv_idmap S1)
  := reflection_idmap_join _ reflection_bool.

(* [BCM:defn:tau-CPn] *)
Definition CP_tau `{Univalence} (n : nat) : CP n -> Type
  := fun x => match x with (t; s) => tau (CP_torsor t) reflection_S1 n s end.
