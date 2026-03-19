Require Import HoTT.

Open Scope pointed_scope.

(* This follows the style near the end of Universe.v, giving an equality of equivalences. *)
Definition ap_join_square_path_universe_uncurried `{Univalence} {Y Z : Type} (f : Y <~> Z)
  : equiv_path _ _ (ap (fun X => Join X X) (path_universe_uncurried f)) = equiv_functor_join f f.
Proof.
  revert Z f; apply equiv_induction.
  refine (ap (fun x => equiv_path _ _ (ap (fun X => Join X X) x)) path_universe_1 @ _).
  symmetry; cbn.
  apply path_equiv, path_arrow, functor_join_idmap.
Defined.

(* Add to BAut/Bool.v *)
(** An induction principle for [BAut Bool]. *)
Lemma baut_bool_ind_hset `{Univalence}
      (P : Type -> Type) {HS : forall (Z : BAut Bool), IsHSet (P Z)}
  : { e : P (point (BAut Bool)) & transport P (path_universe_uncurried equiv_negb) e = e }
  <~> (forall (Z:BAut Bool), P Z).
Proof.
  refine (baut_ind_hset _ _ oE _).
  rapply equiv_functor_sigma_id; intro a.
  (* This ensures that Coq realizes that the path types are hprops: *)
  pose (HSpt := HS pt); rapply equiv_iff_hprop; clear HSpt HS.
  - intros p g.
    pose (c := aut_baut_bool_idmap_or_negb pt g).
    destruct c as [q | q]; rewrite q; clear g q.
    + exact (ap (fun x => transport P x a) path_universe_1).
    + cbn.
      rewrite eta_path_universe.
      unfold "..1".
      rewrite ap_pr1_path_sigma_hprop.
      exact p.
  - intro f.  exact (f equiv_negb).
Defined.

(* A computation rule for the inverse of [join_assoc]. *)
Lemma join_assoc_inv_joinl {A B C}
  : (join_assoc A B C)^-1 o joinl == functor_join idmap joinl.
Proof.
  (* These [change]s are just for the reader to see what is happening. *)
  (* We use that [join_assoc] is its own inverse, and unfold the definition: *)
  change (join_assoc A B C)^-1 with
    (functor_join idmap (join_sym C B) o trijoin_twist C A B o join_sym (Join A B) C).
  (* We use how [join_sym] computes on [joinl]: *)
  change (functor_join idmap (join_sym C B) o trijoin_twist C A B o joinr == functor_join idmap joinl).
  (* Then we use that [trijoin_twist _ _ _ o joinr] is [functor_join idmap joinr]: *)
  change (functor_join idmap (join_sym C B) o functor_join (Id A) joinr == functor_join idmap joinl).
  symmetry; exact (functor_join_compose _ joinr _ _).
Defined.

Definition join_power_squared (X : Type) (n : nat)
  : join_power X (n * 2) <~> join_power (Join X X) n.
Proof.
  induction n.
  - exact equiv_idmap.
  - cbn.
    refine (_ oE join_assoc _ _ _).
    exact (equiv_functor_join equiv_idmap IHn).
Defined.

Definition functor_join_power {A B : Type} (f : A -> B) (n : nat)
  : join_power A n -> join_power B n.
Proof.
  induction n.
  - exact idmap.
  - exact (functor_join f IHn).
Defined.

Definition equiv_functor_join_power {A B : Type} (f : A <~> B) (n : nat)
  : join_power A n <~> join_power B n.
Proof.
  induction n.
  - exact equiv_idmap.
  - exact (equiv_functor_join f IHn).
Defined.

Definition functor_join_power_idmap {A : Type} (n : nat)
  : functor_join_power (A:=A) idmap n == idmap.
Proof.
  induction n.
  - intros [].
  - simpl.
    intro x.
    refine (functor2_join (reflexive_pointwise_paths _ _ _) IHn x @ functor_join_idmap x).
Defined.

Definition functor2_join_power {A B : Type} (f g : A -> B) (h : f == g) (n : nat)
  : functor_join_power f n == functor_join_power g n.
Proof.
  induction n.
  - intros [].
  - simpl.
    exact (functor2_join h IHn).
Defined.

(* This is a variant of the ap_join lemmas above. *)
Definition transport_join_r {A : Type} (B : A -> Type) (C : Type) {a0 a1 : A} (p : a0 = a1)
  (x : Join C (B a0))
  : transport (fun a => Join C (B a)) p x = functor_join idmap (transport B p) x.
Proof.
  induction p.
  refine ((functor_join_idmap x)^ @ _).
  rapply functor2_join; reflexivity.
Defined.

Definition transport_join_l {A : Type} (B : A -> Type) (C : Type) {a0 a1 : A} (p : a0 = a1)
  (x : Join (B a0) C)
  : transport (fun a => Join (B a) C) p x = functor_join (transport B p) idmap x.
Proof.
  induction p.
  refine ((functor_join_idmap x)^ @ _).
  rapply functor2_join; reflexivity.
Defined.
