(** * Integral Eilenberg-Mac Lane spaces K(Z, n) *)

From HoTT Require Import Basics Types.Universe WildCat.Equiv Pointed
  Algebra.AbGroups Truncations.Core Truncations.Connectedness
  Spaces.Int Spaces.Spheres
  Homotopy.EMSpace Homotopy.HSpace Homotopy.HomotopyGroup Homotopy.PinSn.

From CentralTypes Require Import BAut1 Central EMSpace Bands.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.

(** Maybe this should be done in AbGroups.Z, without the Local annotation? *)
Local Notation ZZ := abgroup_Z.

(** Universes: could make [S^n] and [KZ n] land in the lowest universe [Set].  But we want to consider [BAut1{u v} S^n], with [u] not [Set], and this generates some goals that typeclass inference has trouble with.  So we'll let [S^n] and [KZ n] float. *)

(** todo: Put this in HoTT library? *)
Notation "'S^' n" := (psphere n) (at level 5).

(** This is an alternate definition of [K(ZZ, n)]. *)
Definition KZ@{u} (n : nat) : pType@{u}.
Proof.
  (** We put this truncation on the outside, even though it is redundant for [n = 0], as it means that typeclass resolutions knows that this is [n]-truncated.  And we'll mainly use this for [n > 0]. *)
  refine (pTr@{u} n _).
  destruct n.
  - exact (Build_pType@{u} Int 0%int).
  - exact (psphere@{u} n.+1).
Defined.

Definition istrunc_KZ (n : nat) : IsTrunc n (KZ n) := _.

Global Instance isconnected_KZ (n : nat) : IsConnected n.-1 (KZ n)
  := ltac:(destruct n; exact _).

(** TODO: fill in *)
Definition equiv_KZ_EM `{Univalence} (n : nat) : KZ n <~>* K(ZZ, n).
Admitted.

Global Instance ishspace_KZ `{Univalence} (n : nat)
  : IsHSpace (KZ n).
Proof.
  napply (ishspace_equiv_hspace (equiv_KZ_EM n)).
  apply iscohhspace_em.
Defined.

Definition iscohspace_KZ `{Univalence} (n : nat)
  : IsCohHSpace (KZ n).
Proof.
  napply (iscohhspace_equiv_cohhspace (equiv_KZ_EM n)).
  apply iscohhspace_em.
Defined.

Global Instance central_KZ `{Univalence} (n : nat)
  : Central (KZ@{u} n.+1).
Proof.
  nrefine (central_pequiv_central (equiv_KZ_EM n.+1)^-1* ).
  apply central_em.
Defined.

Definition pi_KZ `{Univalence} (n : nat) : Pi n (KZ n) <~>* ZZ.
Proof.
  refine (_ o*E (pequiv_pi_Tr n _)^-1* ).
  destruct n.
  - symmetry; apply pequiv_ptr.
  - exact (pin_sn n).
Defined.

Definition grp_iso_pi_KZ `{Univalence} (n : nat) : Pi n.+1 (KZ n.+1) $<~> ZZ.
Proof.
  refine (_ $oE _).
  2: symmetry; rapply grp_iso_pi_Tr.
  exact (pin_sn n).
Defined.

(** TODO: verify that [ptr] "is" the generator. *)
