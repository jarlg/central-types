From HoTT Require Import Basics Homotopy.Join.

From CentralTypes Require Import JoinLemmas ProjectiveLemmas.

(** * Torsors for a type [A] *)

(** [E] is a torsor for a type [A] when for any point [e : E] we are given an equivalence [A <~> E].  This can also be thought of as an action [A -> E -> E] of [A] on [E] that is right-invertible. *)
Definition torsor (A E : Type)
  := E -> (A <~> E).

(** We sometimes swap the order of the variables and think of the torsor structure as giving an action of [A] on [E]. *)
Definition torsor_action {A E : Type} (T : torsor A E)
  : A -> (E -> E)
  := fun x y => T y x.

(** We can extend the torsor action to the join powers as a sort of scalar multiplication. *)
(* [BCM:defn:scalar.multiplication] *)
Definition torsor_scalar_multiplication {A E : Type} (T : torsor A E)
  (n : nat) (x : A)
  : join_power E n -> join_power E n
  := functor_join_power (torsor_action T x) n.

Definition torsor_scalar_multiplication_beta_jglue {A E : Type} (T : torsor A E)
  (n : nat) (x : A) (e : E) (e' : join_power E n)
  : ap (fun x0 : join_power E n.+1 => torsor_scalar_multiplication T n.+1 x x0)
    (jglue e e') = jglue (T e x) (torsor_scalar_multiplication T n x e').
Proof.
  rapply Join_rec_beta_jglue.
Defined.

(** Swapping the variables back gives a "scalar multiplication" map as shown, whose image is morally the "span" of [y]. *)
Definition torsor_inclusion {A E : Type} (T : torsor A E)
  (n : nat) (y : join_power E n)
  : A -> join_power E n.
Proof.
  intro x.
  exact (torsor_scalar_multiplication T n x y).
Defined.

