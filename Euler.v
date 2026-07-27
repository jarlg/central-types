From HoTT Require Import Basics Types.Sigma Types.Universe Tactics.EvalIn Pointed
  Algebra.AbGroups.Z Truncations.Core Truncations.Connectedness
  Spaces.Spheres Homotopy.Suspension.

From CentralTypes Require Import BAut1 KZ CoHSpace.

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

