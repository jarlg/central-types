From HoTT Require Import Basics Types Truncations Pointed
  Homotopy.HSpace Homotopy.Cover HFiber Modalities.ReflectiveSubuniverse.

Require Import Lemmas.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.

(** * Path components *)

Definition O_cover_change_center `{O : ReflectiveSubuniverse} {X : Type} {x0 x1 : O X} (p : x0 = x1)
  : O_cover X x0 <~> O_cover X x1.
Proof.
  srapply equiv_functor_sigma_id; intro x; cbn.
  exact (equiv_concat_r p _).
Defined.

Definition pfunctor_O_cover_from_point `{O : ReflectiveSubuniverse@{u}} {X Y : Type@{u}}
  (f : X -> Y) (x : X) : O_pcover@{u} O _ x ->* O_pcover@{u} O _ (f x).
Proof.
  srapply pfunctor_pfiber_from_point.
  1: exact (O_pfunctor_from_point O f x).
  apply to_O_natural.
Defined.

Definition equiv_functor_O_cover_from_point@{u} {O : ReflectiveSubuniverse@{u}}
  {X Y : Type@{u}} (f : X <~> Y) (x : O X)
  : O_cover@{u} X x <~> O_cover@{u} Y (O_functor O f x).
Proof.
  nrapply (equiv_functor_hfiber (h:=f) (k:=equiv_O_functor O f)).
  apply to_O_natural.
Defined.

(** If a pointed type is connected then it is equivalent to its base point component. *)
Global Instance equiv_connected_pcomp {A : pType} `{IsConnected 0%nat A}
  : IsEquiv (pr1 : pcomp A pt -> A).
Proof.
  apply isequiv_pr1.
  intro x.
  rapply istrunc_paths.
Defined.

Definition pequiv_connected_pcomp {A : pType} `{IsConnected 0%nat A}
  : pcomp A pt <~>* A.
Proof.
  srapply Build_pEquiv'.
  - snrapply (Build_Equiv _ _ pr1).
    apply equiv_connected_pcomp.
  - reflexivity.
Defined.

(** All components of a left-invertible H-space are pointed equivalent to the base point component. *)
Definition pequiv_comp_hspace_pt `{Univalence} (A : pType) `{mu : IsHSpace A}
  `{E : forall a:A, IsEquiv (a *.)}
  : forall a, pcomp A pt <~>* pcomp A a.
Proof.
  intro a.
  exact (pequiv_pfunctor_O_pcover (pequiv_hspace_left_op a)).
Defined.

(** It follows that all components are pointed equivalent. *)
Definition pequiv_comp_hspace `{Univalence} (A : pType) `{mu : IsHSpace A}
  `{E : forall a:A, IsEquiv (a *.)}
  : forall a b, pcomp A a <~>* pcomp A b
  := fun a b => pequiv_comp_hspace_pt A b o*E (pequiv_comp_hspace_pt A a)^-1*.

(** If a property holds at a given point, then it holds for the whole component. This yields equivalences like the following: *)
(** TODO replaces [equiv_comp_property] in Homotopy.Cover. *)
Definition pequiv_comp_property `{Univalence} {X : Type}
  (x : X) (P : X -> Type) `{forall x, IsHProp (P x)} (Px : P x)
  : pcomp (sig P) (x; Px) <~>* pcomp X x.
Proof.
  snrapply Build_pEquiv'.
  { unfold pcomp, O_pcover, pfiber, hfiber; simpl.
    refine (_ oE (equiv_sigma_assoc _ _)^-1).
    apply equiv_functor_sigma_id; intro y.
    apply equiv_iff_hprop.
    - intros [py q].
      change pt with (tr (n:=0) (x; Px)) in q.
      change pt with (tr (n:=0) x).
      exact (ap (Trunc_functor _ pr1) q).
    - refine (equiv_ind (equiv_path_Tr _ _) _ _).
      apply Trunc_rec; intro p; induction p^.
      exact (Px; idpath). }
  reflexivity.
Defined.

(** [pfunctor_pcomp] in Homotopy.Cover. has the wrong modality... This is the correct version: *)
Definition pfunctor_pcomp {X Y : pType@{u}} (f : X ->* Y)
  : pcomp X pt ->* pcomp Y pt
  := @pfunctor_pTr_pcover 0 X Y f.

Definition pequiv_pfunctor_pcomp {X Y : pType@{u}} (f : X <~>* Y)
  : pcomp X pt <~>* pcomp Y pt
  := @pequiv_pfunctor_pTr_pcover 0 X Y f _.

Definition pcomp_equiv_to_map {A B : Type@{u}} (e : A <~> B)
  : pcomp (A <~> B) e ->* pcomp (A -> B) (equiv_fun e)
  := (pfunctor_pcomp (pmap_from_point equiv_fun e)).

(** For example, we may take components of equivalences among underlying maps. *)
(** Note: [pcomp_equiv_to_map] is not definitionally the underlying map of this. *)
(** Can we fix that?  It would be great if they were equal... *)
Definition pequiv_pcomp_equiv_to_map `{Univalence}
  {A B : Type@{u}} (e : A <~> B)
  : pcomp (A <~> B) e <~>* pcomp (A -> B) e.
Proof.
  snrapply Build_pEquiv'.
  { refine (_ oE equiv_functor_O_cover@{u u u u} (issig_equiv _ _)^-1 _); cbn.
    rapply pequiv_comp_property. }
  reflexivity.
Defined.

(** We can make analogous statements for pointed maps. *)
(** TODO The proofs are almost exactly as above... Is there a general tactic we should make? Probably not worth spending much time on, as we only really use [pequiv_pcomp_to_pmap] below. (We use it to show that a connected H-space is central iff the pointed self-equivalences form a set.) *)

Definition pcomp_pequiv_to_pmap {A B : pType@{u}} (e : A <~>* B)
  : pcomp (A <~>* B) e ->* pcomp (A ->* B) e
  := (pfunctor_pcomp (pmap_from_point (pointed_equiv_fun _ _) e)).

Definition pequiv_pcomp_pequiv_to_pmap `{Univalence}
  {A B : pType@{u}} (e : A <~>* B)
  : pcomp (A <~>* B) e <~>* pcomp (A ->* B) e.
Proof.
  snrapply Build_pEquiv'.
  { refine (_ oE equiv_functor_O_cover@{u u u u} (issig_pequiv _ _)^-1 _); cbn.
    rapply pequiv_comp_property. }
  reflexivity.
Defined.

(** Note: Coq knows that components of sets are contractible. We should add a comment about this in Homotopy.Cover. *)

(** A type is a set if every component is contractible. *)
Definition ishset_contr_comp `{Univalence}
  {A : Type} `{forall a, Contr (comp A (tr a))}
  : IsHSet A.
Proof.
  (* It suffices to check that every loop space of [A] is contractible. *)
  apply equiv_istrunc_istrunc_loops; intro a; cbn.
  (* [pcomp A a] is a sigma-type of HProp's, so [ap pr1] is an equivalence. *)
  rapply (istrunc_equiv_istrunc (pt = pt :> pcomp A a)).
  refine (equiv_path_sigma_hprop _ _)^-1%equiv.
Defined.
