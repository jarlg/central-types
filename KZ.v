(** * Integral Eilenberg-Mac Lane spaces K(Z, n) *)

From HoTT Require Import Basics Types.Universe WildCat.Core WildCat.Equiv Pointed
  Algebra.AbGroups Truncations.Core Truncations.Connectedness
  Spaces.Int Spaces.Spheres
  Homotopy.EMSpace Homotopy.HSpace Homotopy.HomotopyGroup Homotopy.PiSpheres.

From CentralTypes Require Import Central CoHSpace EMSpace Bands.

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

Definition equiv_KZ_EM `{Univalence} (n : nat) : KZ n <~>* K(ZZ, n).
Proof.
  destruct n.
  1: symmetry; rapply pequiv_ptr.
  refine (_ o*E (pequiv_em_connected_truncated _ n)^-1* ).
  tapply (emap (K' n.+1)).
  refine (pin_sn _ $oE _).
  unfold KZ.
  symmetry; apply grp_iso_pi_Tr.
Defined.

(** [KZ n.+1] gets its coherent H-space structure from [central_KZ] below, via [ishspace_central] and [iscoherent_central].  We deliberately do not transport one across [equiv_KZ_EM] as well: two [IsHSpace (KZ n)] instances that are not definitionally equal make [IsCoherent (KZ n)] resolve against a different structure than [IsHSpace (KZ n)] does.  The cost is that [KZ 0] gets no H-space structure, since [central_KZ] needs connectedness. *)

Global Instance central_KZ `{Univalence} (n : nat)
  : Central (KZ@{u} n.+1).
Proof.
  nrefine (central_pequiv_central (equiv_KZ_EM n.+1)^-1* ).
  napply central_em.
Defined.

(** The negation map on [KZ n.+1] is the [n.+1]-truncation of the negation on [S^n.+1].  We record it as a pointed equivalence, so that coercions supply either a pointed map (as in [ishspaceinverse_KZ_neg]) or an equivalence (as in [twist_baut1_KZ_neg]). *)
Definition KZ_neg (n : nat) : KZ n.+1 <~>* KZ n.+1
  := emap (pTr n.+1) (pequiv_susp_neg S^n).

(** [KZ_neg] is an inverse map for the H-space [KZ n.+1].  Indeed, [S^n.+1] is a co-H-space with inverse map [psusp_neg], and truncation carries a co-H-space inverse on [A] to an H-space inverse on [pTr n A]. *)
Definition ishspaceinverse_KZ_neg `{Univalence} (n : nat)
  : IsHSpaceInverse (KZ_neg n).
Proof.
  unfold KZ_neg.
  apply (ptr_functor_ishspaceinverse (iscohspaceinverse_psusp_neg S^n)).
Defined.

Definition neg_homotopic_KZ_neg `{Univalence} (n : nat)
  : neg (A:=KZ n.+1) == KZ_neg n.
Proof.
  srapply homotopic_ishspaceinverse.
  - apply ishspaceinverse_neg.
  - apply ishspaceinverse_KZ_neg.
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
