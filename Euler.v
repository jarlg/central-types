From HoTT Require Import Basics Types.Sigma Types.Universe Types.Equiv Tactics.EvalIn
  Pointed HFiber Algebra.AbGroups.Z Truncations.Core Truncations.Connectedness
  Spaces.Spheres Homotopy.Suspension Homotopy.HSpace.Core Homotopy.HSpace.Pointwise.

From CentralTypes Require Import BAut1 KZ CoHSpace Bands Central.

(** * The Euler class *)

Open Scope pointed_scope.
Open Scope trunc_scope.

(** This should be done in AbGroups.Z. *)
Notation ZZ := abgroup_Z.

(** The general situation involved in defining the Euler class:

                   F
        Type ----------> Type
         |                |
    tr m |                | tr m
         v                v
      ||Type||_m ----> ||Type||_m

    where the bottom row is [Trunc_functor m F].

    In our case, [m] is [1] and [F] is itself a truncation operation [Tr n.+1].  The proof below works because the square commutes definitionally. *)
Definition tr_path (m : nat) {F : Type -> Type} {X Y : Type} (p : @tr m _ X = @tr m _ Y)
  : @tr m _ (F X) = @tr m _ (F Y)
  := ap (Trunc_functor m F) p.

(** The Euler class.  This definition works because [KZ n.+1] is definitionally the [n.+1]-truncation of [S^n.+1]. *)
(** [BCM:defn:euler.class] *)
Definition euler {n : nat} (X : BAut1 S^n.+1) : BAut1 (KZ n.+1)
  := (Tr n.+1 X.1; tr_path 1 X.2).

(** The positive spheres are co-H-spaces. *)
Instance iscohspace_sphere (n : nat) : IsCoHSpace S^n.+1
  := iscohspace_susp S^n.

(** The negation on [BAut1 S^n.+1] adjusts the orientation by post-composition with the negation on [S^n.+1]. This is [BCM:rmk:euler.flip]. *)
Definition twist_baut1_susp_neg `{Univalence} (n : nat)
  : BAut1 S^n.+1 -> BAut1 S^n.+1
  := twist_baut1 (pequiv_susp_neg S^n).

(** The negation on [BAut1 (KZ n.+1)] adjusts the orientation by post-composition with the negation on [KZ n.+1]. *)
Definition twist_baut1_KZ_neg `{Univalence} (n : nat)
  : pBAut1 (KZ n.+1) ->* pBAut1 (KZ n.+1)
  := pmap_twist_baut1 (KZ_neg n) (KZ_neg_involutive n).

(** Since [KZ_neg n] is homotopic to the negation defined in [Bands], the twist map we use here is homotopic to the twist map defined there. *)
Definition twist_baut1_neg_homotopic_twist_baut1_KZ_neg `{Univalence} (n : nat)
  : twist_baut1_neg (A:=KZ n.+1) == twist_baut1_KZ_neg n
  := twist_baut1_homotopic neg (KZ_neg n) (neg_homotopic_KZ_neg n).

(** Since [twist_baut1_neg] was already shown to be a negation, so is [twist_baut1_KZ_neg]. *)
Definition ishspaceinverse_twist_baut1_KZ_neg `{Univalence} (n : nat)
  : IsHSpaceInverse (twist_baut1_KZ_neg n).
Proof.
  unfold IsHSpaceInverse.
  rhs_V' exact (ishspaceinverse_twist_baut1_neg (A:=KZ n.+1)).
  rapply sgop_pmap_phomotopy.
  - reflexivity.
  - apply hspace_phomotopy_from_homotopy.
    symmetry; apply twist_baut1_neg_homotopic_twist_baut1_KZ_neg.
Defined.

