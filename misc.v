(* Miscellaneous results that will be added to appropriate places in the HoTT library. *)

Require Import HoTT.

(* The universe variables here do not follow our general convention.  We name them nicely here because later we need to provide universe annotations when using this result. *)
Definition equiv_postcompose_equiv@{i j k u v | i <= u, j <= v, k <= u, k <= v} `{Funext}
           {X : Type@{i}} {Y : Type@{j}} (Z : Type@{k}) (e : X <~> Y)
  : Equiv@{u v} (Z <~> X) (Z <~> Y).
(* This follows from equiv_induction, but we need to control universe variables. This method also avoids Univalence. *)
Proof.
  snapply equiv_adjointify.
  - exact (fun f => e oE f).
  - exact (fun g => e^-1 oE g).
  - intro g.
    apply path_equiv@{k j v}; cbn.
    funext z.
    apply eisretr.
  - intro f.
    apply path_equiv@{k i u}; cbn.
    funext z.
    apply eissect.
Defined.

Definition equiv_precompose_equiv@{i j k u v | i <= u, j <= v, k <= u, k <= v} `{Funext}
           {X : Type@{i}} {Y : Type@{j}} (Z : Type@{k}) (e : X <~> Y)
  : Equiv@{v u} (Y <~> Z) (X <~> Z).
(* This follows from equiv_induction, but we need to control universe variables. This method also avoids Univalence. *)
Proof.
  snapply equiv_adjointify.
  - exact (fun g => g oE e).
  - exact (fun f => f oE e^-1).
  - intro f.
    apply path_equiv@{i k u}; cbn.
    funext x.
    apply (ap f).
    apply eissect.
  - intro g.
    apply path_equiv@{j k v}; cbn.
    funext y.
    apply (ap g).
    apply eisretr.
Defined.

Definition iff_contr_equiv {P Q : Type} (e : P <~> Q) : Contr P <-> Contr Q
  := (@contr_equiv' _ _ e, @contr_equiv' _ _ e^-1).

Definition nullhomotopy_factor_through_unit {A B : Type} (f : A -> B)
           (E : ExtensionAlong (fun _ => tt) (fun _ => B) f)
  : NullHomotopy f.
Proof.
  exists (E.1 tt).
  intro x.
  symmetry.
  apply E.2.
Defined.

Definition factor_through_unit_nullhomotopy {A B : Type} (f : A -> B)
           (N : NullHomotopy f)
  : ExtensionAlong (fun _ => tt) (fun _ => B) f.
Proof.
  destruct N as [b H].
  unfold ExtensionAlong.
  exists (fun _ => b).
  intro x.
  symmetry.
  apply H.
Defined.

(* If maps are n-extendable along the constant map [X -> Unit] for definitionally constant type families over [Unit], then they are n-extendable along all type families. *)
Definition extendable_along_unit (n : nat) (X : Type) (P : Unit -> Type)
           (ea : ExtendableAlong n (fun _ : X => tt) (fun _ : Unit => P tt))
  : ExtendableAlong n (fun _ : X => tt) P.
Proof.
  revert P ea.
  (* Using [simple_induction] avoids an extra universe variable. *)
  simple_induction n n IHn; intros P ea.
  - exact tt.
  - split.
    + intro g.
      pose (feag := (fst ea) g).
      srefine (_; _).
      * intro y; destruct y.
        exact (feag.1 tt).
      * cbn.  exact feag.2.
    + intros h k.
      apply IHn.
      apply (snd ea (fun _ => h tt) (fun _ => k tt)).
Defined.

(* ** This next part is essentially showing that [Tr n.+1] is accessible. *)
Definition istrunc_iff_sphere_null (n : trunc_index) (X : Type)
  : IsTrunc n.+1 X <-> forall f : Sphere n.+2 -> X, ExtensionAlong (fun _ : Sphere n.+2 => tt) (unit_name X) f.
Proof.
  split.
  - intros isTrX f.
    apply factor_through_unit_nullhomotopy.
    apply allnullhomot_trunc.
  - intros ea.
    apply istrunc_allnullhomot@{k k k k}; intro f.
    srapply nullhomotopy_factor_through_unit.
    apply ea.
Defined.

(* This has four universe variables, but can accept them being equal.  Can get it down to a single universe variable with some annotations. *)
Definition istrunc_iff_sphere_oo_null (n : trunc_index) (X : Type)
  : IsTrunc n.+1 X <-> ooExtendableAlong (fun _ : Sphere n.+2 => tt) (unit_name X).
Proof.
  split.
  - intros isTrX n0; revert X isTrX.
    simple_induction n0 n0 IHn0; intros X isTrX.
    + exact tt.
    + split; intros.
      * apply istrunc_iff_sphere_null; assumption.
      * apply extendable_along_unit.
        rapply IHn0.
  - intros ea.
    apply istrunc_allnullhomot; intro f.
    srapply nullhomotopy_factor_through_unit.
    apply (ea 1%nat).
Defined.
