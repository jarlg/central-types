(* Various results about connectivity that will be put into the appropriate place in the HoTT library. *)

Require Import HoTT.
Require Import Truncations.  (* To get the correct [isconnected_paths] in scope. *)

Require Import misc.

Open Scope pointed_scope.

(** The next five results should be generalized to any ReflectiveSubuniverse [O], either using [Sep O] or the approach of Descent.v. *)

(** This is a converse to [isconnected_paths] in the merely inhabited case.  In fact, the conditions are necessary and sufficient. *)
(* ** It can replace [is0connected_merely_allpath], or at least be used to prove that result. *)
Definition isconnected_isconnected_paths_merely `{Univalence} {n : trunc_index}
           (A : Type) (ma : merely A)
           (p : forall x y : A, IsConnected n (x = y))
  : IsConnected n.+1 A.
Proof.
  unfold IsConnected.
  strip_truncations.
  apply (Build_Contr _ (tr ma)).
  intro y.
  strip_truncations.
  apply (equiv_path_Tr _ _).
  apply center, p.
Defined.

(** This is a converse to [isconnected_paths] in the pointed case. *)
Definition isconnected_isconnected_paths_pointed `{Univalence} {n : trunc_index}
           {A : pType}
           (p : forall y, IsConnected n ((point A) = y))
  : IsConnected n.+1 A.
Proof.
  (** This follows from the previous result, but it's easier to just adjust the proof. *)
  apply (Build_Contr _ (tr (point A))).
  intro y.
  strip_truncations.
  apply (equiv_path_Tr _ _).
  apply center, p.
Defined.

(** This is a converse to [isconnected_loops] in the pointed, 0-connected case. *)
Definition isconnected_isconnected_loops `{Univalence} {n : trunc_index}
           (A : pType) `{IsConnected (Tr 0) A} `{IsConnected n (loops A)}
  : IsConnected n.+1 A.
Proof.
  snrapply isconnected_isconnected_paths_pointed.
  srapply (conn_point_elim (-1) (A:=A)); assumption.
Defined.

(** This is a converse to [isconnected_fmap_loops] when [f] is surjective. In fact, these conditions are necessary and sufficient. *)
Definition isconn_map_isconn_map_ap `{Univalence} {n : trunc_index}
           {A B : Type} (f : A -> B) `{S : IsSurjection f}
           (CM : forall x y : A, IsConnMap n (@ap _ _ f x y))
  : IsConnMap n.+1 f.
Proof.
  unfold IsConnMap.
  intro b.
  snrapply (isconnected_isconnected_paths_merely (hfiber f b)).
  1: apply center, S.
  intros [x p] [y q].
  induction q.
  nrapply isconnected_equiv'.
  1: apply hfiber_ap.
  apply CM.
Defined.

(** This is a converse to [isconnected_fmap_loops] in the pointed, 0-connected case. *)
Definition isconn_map_isconn_map_fmap_loops `{Univalence} {n : trunc_index}
           {A B : pType} `{IsConnected (Tr 0) A} `{IsConnected (Tr 0) B}
           (f : A ->* B) `{IsConnMap n _ _ (fmap loops f)}
  : IsConnMap n.+1 f.
Proof.
  apply isconn_map_isconn_map_ap.
  - snrapply (conn_point_elim (-1)). 1,2: exact _. cbn beta.
    rapply contr_inhabited_hprop.
    exact (tr (point A; point_eq f)).
  - snrapply (conn_point_elim (-1)). 1,2: exact _. cbn beta.
    snrapply (conn_point_elim (-1)). 1,2: exact _. cbn beta.
    pointed_reduce_pmap f.
    refine (conn_map_homotopic _ _ _ _ H2).
    exact (fun p => (concat_1p _) @ concat_p1 _).
Defined.

(** A surjective map of groups induces a 0-connected map on classifying spaces.  This is true, with the same proof, when [0] is replaced with [n], but this is the only interesting case. *)
Definition isconn_map_functor_pclassifyingspace `{U : Univalence}
           {G H : Group} (f : GroupHomomorphism G H) (S : IsSurjection f)
  : IsConnMap (Tr 0) (fmap pClassifyingSpace f).
Proof.
  snrapply isconn_map_isconn_map_fmap_loops.
  1, 2: exact _.
  nrapply (cancelR_conn_map _ bloop).
  - exact _.
  - nrapply conn_map_homotopic.
    1: symmetry; apply bloop_natural.
    rapply conn_map_compose.
Defined.

(* ** Replace merely_isconnected in Connectedness.v with the following two: *)
(** By induction, an [n.+1]-connected type is also [-1]-connected. *)
Definition minus_one_connected_isconnected n A `{IsConnected n.+1 A}
  : IsConnected (Tr (-1)) A.
Proof.
  induction n as [|n IHn].
  - assumption.
  - apply IHn, isconnected_pred; assumption.
Defined.

Definition merely_isconnected n A `{IsConnected n.+1 A}
  : merely A.
Proof.
  apply center.
  srapply minus_one_connected_isconnected.
Defined.

Definition minus_one_connmap_isconnmap n {A B : Type} (f : A -> B) (C: IsConnMap n.+1 f)
  : IsConnMap (Tr (-1)) f.
Proof.
  intro b.
  rapply minus_one_connected_isconnected.
Defined.

(* It's possible to arrange this so that it involves [A : Type@{i}], [B : Type@{j}] and [IsConnmap@{k}], with [i <= k] and [j <= k], but that doesn't really add any useful generality, and is slightly messier to prove. *)
Definition isconnmap_ap@{k u | k < u} `{Univalence} (n : trunc_index)
           {A B : Type@{k}} (f : A -> B) `{IsConnMap n.+1 _ _ f} {x1 x2 : A}
           : IsConnMap n (@ap _ _ f x1 x2).
Proof.
  intro p.
  apply (isconnected_equiv _ _ (hfiber_ap p)^-1%equiv).
  apply isconnected_paths.
Defined.

(** We are going to show that we can move [IsConnMap (Tr n) f] across universes. First we adjust an existing result. *)

(* Here is what is in the HoTT library:
Print Trunc_functor_equiv.
     : forall (n : trunc_index) (X : Type@{u}) (Y : Type@{u0}),
       X <~> Y -> Tr@{u1} n X <~> Tr@{u1} n Y
   u u0 u1 |= u <= u1
              u0 <= u1
That's not unreasonable, but here's a variation:  *)

Definition Trunc_functor_equiv@{i j k | i <= k, j <= k} (n : trunc_index)
           {X : Type@{i}} {Y : Type@{j}} (f : X <~> Y)
  : Tr@{i} n X <~> Tr@{j} n Y
  := equiv_O_functor@{k i j} (Tr n) f.

(** We can move [IsConnMap (Tr n) f] across universes, since [Tr] is cumulative. *)
(* Could generalize to  i j k, with i <= j and i <= k. *)
(* This is essentially the same as [conn_map_O_leq' (Tr@{j} n) (Tr@{i} n)], except that that needs [IsAccRSU (Tr n)], which I couldn't find in the library.  It follows from the results at the end of Spheres.v, but hasn't been filled in.  So we prove this directly.  (The other hypothesis of [conn_map_O_leq'] is found automatically.)  **  Results recently added to misc.v do show that (Tr n) is accessible, so this could be revamped. *)
Definition lift_isconnmap_trunc@{i j | i <= j} (n : trunc_index)
           {X Y : Type@{i}} (f : X -> Y)
  : IsConnMap@{i} (Tr@{i} n) f <-> IsConnMap@{j} (Tr@{j} n) f.
Proof.
  unfold IsConnMap, IsConnected, Tr, hfiber; cbn.
  apply iff_functor_forall; intro y.
  apply iff_contr_equiv.
  nrapply Trunc_functor_equiv@{i j j}.
  make_equiv.
Defined.

(* Should this be a Global Instance? [mapinO_pr1] is, but isn't found automatically for this goal. *)
Definition istruncmap_pr1 {n : trunc_index} {A : Type} (B : A -> Type) (T : forall a, IsTrunc n (B a))
  : IsTruncMap n (pr1 : {a : A & B a} -> A).
Proof.
  apply (mapinO_pr1 (Tr n)).
Defined.
