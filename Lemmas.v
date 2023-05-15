From HoTT Require Import Basics Types Truncations HFiber Pointed 
  Modalities.ReflectiveSubuniverse WildCat PathAny Homotopy.HSpace.

Open Scope pointed_scope.

(** * General lemmas *)

(** We can twist H-space structures by swapping the arguments. *)
Definition ishspace_twist {X : pType} : IsHSpace X -> IsHSpace X.
Proof.
  intros [mu mu_lid mu_rid].
  exact (Build_IsHSpace X (fun x y => mu y x) mu_rid mu_lid).
Defined.

(* Place in EquivGroupoids.v?  Or Basics/Equivalences.v, near cancelR_isequiv? *)
(* jarl: The proof uses [equiv_iff_hprop] from Basics/Trunc.v, which
   depends on Basics/Equivalences.v. So we can't place it in the latter
   due to cyclic dependencies. *)
Definition equiv_isequiv_cancelR `{Funext} {A B C}
  (f : A -> B) (g : B -> C) `{E : IsEquiv _ _ f}
  : IsEquiv g <~> IsEquiv (g o f).
Proof.
  apply equiv_iff_hprop.
  1: intro e; apply isequiv_compose.
  intro e.
  apply (isequiv_homotopic ((g o f) o f^-1)).
  intro x.
  apply (ap g).
  apply eisretr.
Defined.

(* Place in EquivGroupoids.v? *)
Definition equiv_isequiv_cancelL `{Funext} {A B C}
  (f : A -> B) (g : B -> C) `{E : IsEquiv _ _ g}
  : IsEquiv f <~> IsEquiv (g o f).
Proof.
  apply equiv_iff_hprop.
  1: intro e; apply isequiv_compose.
  intro e.
  apply (isequiv_homotopic (g^-1 o (g o f))).
  intro x.
  apply eissect.
Defined.

Ltac equiv_conjugate f :=
  refine (ltac:(rapply f) oE _ oE ltac:(rapply f)^-1%equiv).

Definition equiv_precompose_equiv' `{Funext} {A B C : Type} (phi : A <~> B)
  : (B <~> C) <~> (A <~> C).
Proof.
  equiv_conjugate issig_equiv.
  srapply equiv_functor_sigma'.
  1: exact (equiv_precompose phi).
  intro a; cbn.
  rapply equiv_isequiv_cancelR.
Defined.
  
Definition equiv_postcompose_equiv' `{Funext} {A B C : Type} (phi : B <~> C)
  : (A <~> B) <~> (A <~> C).
Proof.
  equiv_conjugate issig_equiv.
  srapply equiv_functor_sigma'.
  1: exact (equiv_postcompose' phi).
  intro a; cbn.
  rapply equiv_isequiv_cancelL.
Defined.

Definition transport_tr (n : trunc_index) {X Y : Type} (p : X = Y) {P : Type -> Type}
  : transport (fun Z => Trunc n (P Z)) p == Trunc_functor n (equiv_path _ _ (ap P p)).
Proof.
  intro x.
  induction p; symmetry.
  exact (Trunc_functor_idmap n _ _).
Defined.

Definition ap_equiv_fromconst_path_universe `{Univalence} {X Y Z : Type} (f : Y <~> Z)
  : equiv_path _ _ (ap (Equiv X) (path_universe f)) == (fun g => f oE g).
Proof.
  revert Z f; rapply equiv_induction.
  intro g.
  refine (ap (fun y => transport idmap y g) _ @ _).
  1: refine (ap (ap _) (y:=idpath) path_universe_1).
  apply path_equiv.
  reflexivity.
Defined.

(** The next few results could probably be done for any univalent 1-category, reducing the duplication. But the WildCat univalence map isn't the same as the univalence map that we study in specific cases, because the identity equivalence is wrong. *)
Lemma transport_equiv_fromconst_path_universe `{Univalence} {X Y Z : Type} (f : Y <~> Z)
  : transport (Equiv X) (path_universe_uncurried f)
    == (fun g => f oE g).
Proof.
  revert Z f; rapply equiv_induction.
  intro k.
  refine (ap (fun p => transport _ p _) _ @ _).
  1: apply path_universe_1.
  apply path_equiv.
  reflexivity.
Defined.

(** Add to Pointed/Core.v, right after isequiv_pequiv_path. *)
Definition equiv_pequiv_path `{Univalence} (A B : pType)
  : (A = B) <~> (A <~>* B)
  := (equiv_path_ptype A B)^-1.

(** Maybe this and things above read better with [g] explicitly listed as an argument? *)
(** We don't actually need this one. *)
Lemma transport_pequiv_fromconst_path_ptype `{Univalence} {X Y Z : pType} (f : Y <~>* Z)
  : transport (pEquiv X) (path_ptype f) == (fun g => f o*E g).
Proof.
  revert Z f; rapply (equiv_path_ind (equiv_pequiv_path Y)).
  intro g.
  refine (ap (fun q => transport _ q _) _ @ _).
  1: apply eisretr.
  unfold transport.
  apply path_pequiv; cbn.
  symmetry; apply pmap_postcompose_idmap.
Defined.

Lemma transport_pequiv_toconst_path_ptype `{Univalence} {X Y Z : pType} (f : X <~>* Y)
  : transport (fun Y => pEquiv Y Z) (path_ptype f) == (fun g => g o*E f^-1*).
Proof.
  revert Y f; rapply (equiv_path_ind (equiv_pequiv_path X)).
  intro g.
  refine (ap (fun q => transport _ q _) _ @ _).
  1: apply eisretr.
  unfold transport.
  apply path_pequiv; cbn.
  symmetry; apply pmap_precompose_idmap.
Defined.

Definition ap_functor_path_ptype `{Univalence}
  (F : pType@{u} -> pType@{v}) `{!Is0Functor F, !Is1Functor F}
  {X Y : pType@{u}} (e : X $<~> Y)
  : ap F (path_ptype e) = path_ptype (emap F e).
Proof.
  revert Y e; rapply (equiv_path_ind (equiv_pequiv_path X)).
  refine (ap _ (eisretr _ _) @ _).
  unfold ap.
  apply moveL_equiv_M'.
  apply path_pequiv; cbn.
  exact (fmap_id F _)^$.
Defined.

Definition ap_apD10_inv `{Funext} {X Y : Type} (x : X) (f g : X -> Y) (h : f == g)
  : ap (fun f => f x) (path_forall _ _ h) = h x.
Proof.
  revert g h; rapply (equiv_path_ind (equiv_apD10 _ f)).
  cbn.
  exact (ap _ (eissect _ _)).
Defined.

Definition equiv_fiber_precompose {X' X Y : Type} (f : X -> Y) (e : X' <~> X) (y : Y)
  : hfiber (f o e) y <~> hfiber f y.
Proof.
  rapply (equiv_functor_hfiber (g:=f) (k := equiv_idmap) (fun _ => idpath)).
Defined.

Global Instance istruncmap_snd {X Y : Type} (n : trunc_index)
  `{IsTrunc n X} : IsTruncMap n (snd (A:=X) (B:=Y)).
Proof.
  intro y.
  nrapply (@inO_equiv_inO' (Tr n)).
  2: { snrefine (equiv_fiber_precompose _ _ _ oE _).
       2: exact (equiv_prod_symm _ _ oE equiv_sigma_prod0 _ _).
       rapply hfiber_fibration. }
  exact H.
Defined.


Definition equiv_path_path_sigma_hprop {A : Type} {P : A -> Type} `{forall a, IsTrunc 0 (P a)}
  {X Y : sig P} (p q : X = Y)
  : pr1_path p = pr1_path q <~> (p = q).
Proof.
  refine ((equiv_ap' (equiv_path_sigma _ _ _)^-1%equiv _ _)^-1%equiv oE _); cbn.
  exact (equiv_path_sigma_hprop (p ..1; p ..2) (q ..1; q ..2)).
Defined.

Lemma ap_path_universe_compose `{Univalence} {X Y Z B : Type}
  (F : Type -> B) (f : X <~> Z) (g : X <~> Y) (h : Y <~> Z)
  (K : f == h o g)
  : ap F (path_universe_uncurried f) = ap F (path_universe_uncurried g) @ ap F (path_universe_uncurried h).
Proof.
  refine (_ @ ap_pp _ _ _).
  apply (ap (ap F)).
  refine (_ @ path_universe_compose _ _).
  refine (ap path_universe_uncurried _).
  apply path_equiv, path_arrow.
  apply K.
Defined.

Lemma ap_path_universe_invol `{Univalence} {X B : Type}
  (F : Type -> B) (f : X <~> X) (invol : equiv_idmap == f o f)
  : idpath = ap F (path_universe_uncurried f) @ ap F (path_universe_uncurried f).
Proof.
  refine (_ @ ap_path_universe_compose _ _ _ _ invol).
  exact (ap (ap F) path_universe_1^).
Defined.

Definition nat_eisretr {X Y : Type} (f : X -> Y) `{IsEquiv _ _ f}
  {y0 y1 : Y} (p : y0 = y1)
  : ap (f o f^-1) p @ eisretr f y1 = eisretr f y0 @ p.
Proof.
  snrapply concat_A1p.
Defined.

Definition nat_eissect {X Y : Type} (f : X -> Y) `{IsEquiv _ _ f}
  {x0 x1 : X} (p : x0 = x1)
  : ap (f^-1 o f) p @ eissect f x1 = eissect f x0 @ p.
Proof.
  snrapply concat_A1p.
Defined.

(* Rename? *)
Definition nat_ap_f {X Y : Type} (f : X -> Y) `{IsEquiv _ _ f}
  {x : X} {y : Y} (p : f x = y)
  : ap f (eissect f x) @ p = ap (f o f^-1) p @ (eisretr f y).
Proof.
  refine (nat_eisretr f p @ (eisadj f x @@ 1))^.
Defined.

Definition ap011_rl {X Y Z : Type} (m : X -> Y -> Z)
  {x0 x1 : X} {y0 y1 : Y} (p : x0 = x1) (q : y0 = y1)
  : ap011 m p q = ap (m x0) q @ ap (fun x => m x y1) p
  := ltac:(by path_induction).

Definition ap011_lr {X Y Z : Type} (m : X -> Y -> Z)
  {x0 x1 : X} {y0 y1 : Y} (p : x0 = x1) (q : y0 = y1)
  : ap011 m p q = ap (fun x => m x y0) p @ ap (m x1) q
  := ltac:(by path_induction).

Definition ap011_rl_lr {X Y Z : Type} (m : X -> Y -> Z)
  {x0 x1 : X} {y0 y1 : Y} (p : x0 = x1) (q : y0 = y1)
  : ap (m x0) q @ ap (fun x => m x y1) p = ap (fun x => m x y0) p @ ap (m x1) q
  := (ap011_rl _ _ _)^ @ ap011_lr _ _ _.

Definition ap011_pp {X Y Z : Type} (m : X -> Y -> Z)
  {x0 x1 x2 : X} {y0 y1 y2 : Y} (p01 : x0 = x1) (p12 : x1 = x2) (q01 : y0 = y1) (q12 : y1 = y2)
  : ap011 m (p01 @ p12) (q01 @ q12) = ap011 m p01 q01 @ ap011 m p12 q12
  := ltac:(by path_induction).

Definition ap011_1r {X Y Z : Type} (m : X -> Y -> Z) 
  {x0 : X} {y0 y1 : Y} (q : y0 = y1)
  : ap011 m idpath q = ap (m x0) q := ltac:(by path_induction).

Definition ap011_l1 {X Y Z : Type} (m : X -> Y -> Z)
  {x0 x1 : X} {y0 : Y} (p : x0 = x1)
  : ap011 m p idpath = ap (fun x => m x y0) p := ltac:(by path_induction).

Definition ap011_swap {X Y Z : Type} (m : X -> Y -> Z)
  {x0 x1 : X} {y0 y1 : Y} (p : x0 = x1) (q : y0 = y1)
  : ap011 m p q = ap011 (fun y x => m x y) q p
  := ltac:(by path_induction).


(** ** Things related to pointedness *)

Local Open Scope pointed_scope.
Local Open Scope type_scope.

Lemma ap_pcompose {X Y Z : pType} (f : X ->* Y) (g : Y ->* Z)
  {x0 x1 : X} (p : x0 = x1)
  : ap (g o* f) p = ap g (ap f p).
Proof.
  exact (ap_compose f g p).
Defined.

Definition pequiv_from_pointed_domain {A : pType} {B : Type} (f : A <~> B)
  : A <~>* [B, f (point A)]
  := @Build_pEquiv' A [B, f (point A)] f 1%path.

Definition pequiv_from_pointed_codomain {A : Type} {B : pType} (f : A <~> B)
  : [A, f^-1 pt] <~>* B
  := @Build_pEquiv' [A, f^-1 pt] B f (eisretr _ _).

(** Transport of left and right identities of binary operations along paths between the underlying functions. *)
Definition transport_binop_lr_id `{Funext} {X : pType} {mu nu : X -> X -> X}
  `{mu_lid : forall x, mu pt x = x} `{mu_rid : forall x, mu x pt = x} (p : mu = nu)
  : transport (fun m : X -> X -> X => (forall x, m pt x = x) * (forall x, m x pt = x))
      p (mu_lid, mu_rid) = (fun x => (ap100 p _ _)^ @ mu_lid x, fun x => (ap100 p _ _)^ @ mu_rid x).
Proof.
  induction p; cbn.
  apply path_prod'; funext x.
  all: exact (concat_1p _)^.
Defined.

(* Place in Pointed.pModality. *)
Definition O_pfunctor_from_point (O : ReflectiveSubuniverse) {X Y : Type}
  (f : X -> Y) (x : X) : [O X, to O _ x] ->* [O Y, to O _ (f x)].
Proof.
  srapply Build_pMap.
  1: exact (O_functor O f).
  apply to_O_natural.
Defined.

(* place in Pointed/pFiber.v *)
Definition pfunctor_pfiber_from_point {A B C D : Type} (f : A -> B) (a : A)
  {g : C -> D} {h : A -> C} {k : B -> D} (p : k o f == g o h)
  : pfiber (pmap_from_point f a) ->* pfiber (pmap_from_point g (h a)).
Proof.
  srapply functor_pfiber.
  - exact (pmap_from_point h a).
  - srapply Build_pMap.
    1: exact k.
    apply p.
  - srapply Build_pHomotopy.
    1: apply p.
    symmetry; cbn.
    exact (concat_p1 _ @ concat_1p _).
Defined.

Definition conn_point_elim_beta `{Univalence} (n : trunc_index) {A : pType@{u}} `{IsConnected n.+1 A}
           (P : A -> Type@{u}) `{forall a, IsTrunc n (P a)} (p0 : P (point A))
  : conn_point_elim n P p0 (point A) = p0.
Proof.
  unfold conn_point_elim.
  unfold isconnected_paths.  (* Invisible to the user; see with Set Printing Implicit. *)
  simpl.
  unfold contr.
  rewrite concat_Vp.
  reflexivity.
Defined.

(** A converse to [isconnected_loops] when [A] is 0-connected. *)
Definition isconnected_isconnected_loops `{Univalence} {n : trunc_index} (A : pType)
  `{IsConnected 0%nat A} `{IsConnected n (loops A)}
  : IsConnected n.+1 A.
Proof.
  nrapply (conn_pointed_type (ispointed_type A)); hnf.
  rapply conn_point_elim; unfold hfiber.
  rapply isconnected_equiv'.
  exact (equiv_contr_sigma _)^-1%equiv.
Defined.

(** A variant in which [loops A] is only assumed to be equivalent to an n-connected type. *)
Global Instance isconnected_isconnected_loops' `{Univalence} {n : trunc_index} {A B : pType}
  `{IsConnected n A, IsConnected 0%nat B} (e : loops B <~> A)
  : IsConnected n.+1 B.
Proof.
  rapply isconnected_isconnected_loops.
  rapply isconnected_equiv'.
  exact e^-1%equiv.
Defined.

Global Instance hasmorext_core_ptype `{Funext} : HasMorExt (core pType).
Proof.
  snrapply Build_HasMorExt.
  intros a b f g.
  unfold GpdHom_path.
  cbn in f, g.
  (* [GpdHom_path] and the inverse of [equiv_path_pequiv] are not definitionally equal, but they compute to definitionally equal things on [idpath]. *)
  apply (isequiv_homotopic (equiv_path_pequiv f g)^-1%equiv).
  intro p; induction p; cbn.
  reflexivity.
Defined.

(* Put in PathAny.v, right after [equiv_path_from_contr].  (Also, the last line of the proof of equiv_path_from_contr can be replaced with "rapply isequiv_contr_contr." and the comment can be deleted.) *)
Definition equiv_path_from_contr_center {A : Type} (P : A -> Type)
           (cp : Contr {y:A & P y} )
           (b : A)
  : P b <~> (@center _ cp).1 = b
  := equiv_path_from_contr _ _ (@center _ cp).2 cp b.
