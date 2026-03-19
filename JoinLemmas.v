Require Import Basics Types.Equiv Types.Universe Homotopy.Join.Core Homotopy.Join.JoinAssoc WildCat.

Definition Join_fam `{Univalence} {A B : Type} (P_A : A -> Type@{u}) (P_B : B -> Type@{u})
  (P_g : forall a b, P_A a <~> P_B b) : Join A B -> Type@{u}.
Proof.
  apply (Join_rec P_A P_B).
  intros a b.
  exact (path_universe_uncurried (P_g a b)).
Defined.

(* This isn't really needed, since it's just [Join_rec_beta_jglue]. *)
Definition Join_fam_beta_jglue'' `{Univalence} {A B : Type} (P_A : A -> Type)
  (P_B : B -> Type) (P_g : forall a b, P_A a <~> P_B b) a b
  : ap (Join_fam P_A P_B P_g) (jglue a b) = path_universe_uncurried (P_g a b)
  := Join_rec_beta_jglue _ _ _ a b.

(* Put in PathGroupoids.v, and make some args of [transport_idmap_ap] implicit. *)
Definition transport_idmap_ap' `{Funext} {A : Type} (P : A -> Type) {x y : A} (p : x = y)
  : transport P p = transport idmap (ap P p).
Proof.
  apply path_forall.
  rapply transport_idmap_ap.  (* Why doesn't [apply] work here? *)
Defined.

Definition Join_fam_beta_jglue' `{Univalence} {A B : Type} (P_A : A -> Type)
  (P_B : B -> Type) (P_g : forall a b, P_A a <~> P_B b) a b
  : transport (Join_fam P_A P_B P_g) (jglue a b) = P_g a b.
Proof.
  refine (transport_idmap_ap' _ _ @ _).
  refine (ap (transport idmap) _ @ _); only 1: rapply Join_rec_beta_jglue.
  apply transport_idmap_path_universe_uncurried.
Defined.

Definition Join_fam_beta_jglue `{Univalence} {A B : Type} (P_A : A -> Type)
  (P_B : B -> Type) (P_g : forall a b, P_A a <~> P_B b) a b
  : equiv_transport (Join_fam P_A P_B P_g) (jglue a b) = P_g a b.
Proof.
  apply path_equiv; cbn.
  apply Join_fam_beta_jglue'.
Defined.

(* A version with just a homotopy, which is all we really need. *)
Definition Join_fam_beta_jglue_homotopy `{Univalence} {A B : Type} (P_A : A -> Type)
  (P_B : B -> Type) (P_g : forall a b, P_A a <~> P_B b) a b
  : transport (Join_fam P_A P_B P_g) (jglue a b) == P_g a b.
Proof.
  intro y.
  lhs napply transport_idmap_ap.
  lhs napply (transport2 idmap); only 1: rapply Join_rec_beta_jglue.
  apply transport_path_universe_uncurried.
Defined.

(** The following results could go at the end of JoinAssoc.v *)

(** A variant of the hexagon.  This shows that you can pass [B] through [Join A C] by passing it through [C] and then through [A], with appropriate associativities inserted as needed. *)
Definition hexagon_join_assoc_sym' A B C
  : join_sym (Join A C) B
    ==  (join_assoc B A C)^-1 o functor_join (join_sym A B) idmap
          o join_assoc A B C o trijoin_id_sym A C B o (join_assoc A C B)^-1.
Proof.
  intro x.
  symmetry.
  apply moveR_equiv_V.
  lhs napply hexagon_join_assoc_sym.
  apply (ap (_ o _)).
  apply eisretr.
Defined.

(** This should replace equiv_inverse_homotopy.  That can then be renamed with a prime and defined as a one-liner using this.  (Or just be removed.) *)
Definition equiv_inverse_homotopy' {A B} (f g : A -> B) `{!IsEquiv f} `{!IsEquiv g}
  (p : f == g)
  : g^-1 == f^-1.
Proof.
  intros x; refine (_ @ _ @ _).
  1:symmetry; apply (eissect f).
  1:apply ap, p.
  apply ap, eisretr.
Defined.

(** Inverting everything gives this version. *)
Definition hexagon_join_assoc_sym'' A B C
  : join_sym B (Join A C)
    == join_assoc A C B o functor_join idmap (join_sym B C)
         o (join_assoc A B C)^-1 o functor_join (join_sym B A) idmap
         o join_assoc B A C.
Proof.
  change ((join_sym (Join A C) B)^-1
    ==  ((join_assoc B A C)^-1 o functor_join (join_sym A B) idmap
          o join_assoc A B C o trijoin_id_sym A C B o (join_assoc A C B)^-1)^-1).
  apply equiv_inverse_homotopy'.
  symmetry; apply hexagon_join_assoc_sym'.
Defined.

Definition pentagon_join_assoc : PentagonIdentity Join.
Admitted.
