From HoTT Require Import Basics Types Pointed
  Homotopy.Wedge Homotopy.HSpace Homotopy.Suspension
  Truncations Pointed.pTrunc WildCat.

From CentralTypes Require Import Wedge.

Open Scope pointed_scope.
Open Scope mc_mult_scope.

(** * Co-H-spaces *)

(** [BCM:defn:cohspace] *)
Class IsCoHSpace (X : pType) := {
  cohspace_op : X ->* X \/ X;
  cohspace_left_identity : wedge_pr1 o* cohspace_op ==* pmap_idmap;
  cohspace_right_identity : wedge_pr2 o* cohspace_op ==* pmap_idmap;
}.

(* TODO:
- Not sure about left/right identity naming.
- Is it correct to have the cohspace_op map be pointed?
- Do we want pointed homotopies?
- Do we need any additional coherence?  Probably not, and a proof that
  [X ->* Y] is a *coherent* H-space for any [Y : pType] would confirm this.
*)

Arguments wedge_inl & {X Y}.
Arguments wedge_inr & {X Y}.

(** [BCM:defn:cohspace-sum] *)
Definition sgop_pmap_cohspace {X Y : pType} `{IsCoHSpace X}
  (f g : X ->* Y) : X ->* Y
  := wedge_rec f g o* cohspace_op.

(** Postcomposition with a pointed map distributes over [sgop_pmap_cohspace]; equivalently, it is an H-space map for the [sgop_pmap_cohspace] structures. *)
Definition sgop_pmap_cohspace_postcompose {A X Y : pType} `{IsCoHSpace A}
  (h : X ->* Y) (f g : A ->* X)
  : h o* sgop_pmap_cohspace f g ==* sgop_pmap_cohspace (h o* f) (h o* g).
Proof.
  unfold sgop_pmap_cohspace.
  symmetry.
  rhs_V' napply pmap_compose_assoc.
  napply pmap_prewhisker.
  napply wedge_rec_postcompose.
Defined.

(** [sgop_pmap_cohspace] respects pointed homotopy in each argument. *)
Definition sgop_pmap_cohspace_phomotopy {A Y : pType} `{IsCoHSpace A}
  {f f' g g' : A ->* Y} (p : f ==* f') (q : g ==* g')
  : sgop_pmap_cohspace f g ==* sgop_pmap_cohspace f' g'.
Proof.
  unfold sgop_pmap_cohspace.
  napply pmap_prewhisker.
  snapply wedge_up'.
  - exact (p @* (wedge_rec_beta_inl f' g')^*).
  - exact (q @* (wedge_rec_beta_inr f' g')^*).
Defined.

(** The constant map is a left unit for [sgop_pmap_cohspace]. *)
Definition leftidentity_pmap_cohspace {A Y : pType} `{IsCoHSpace A} (g : A ->* Y)
  : sgop_pmap_cohspace pconst g ==* g.
Proof.
  unfold sgop_pmap_cohspace.
  lhs' napply (pmap_prewhisker _ (wedge_rec_pconst_l g)).
  lhs' napply pmap_compose_assoc.
  lhs' napply (pmap_postwhisker _ cohspace_right_identity).
  napply pmap_precompose_idmap.
Defined.

(** The constant map is a right unit for [sgop_pmap_cohspace]. *)
Definition rightidentity_pmap_cohspace {A Y : pType} `{IsCoHSpace A} (f : A ->* Y)
  : sgop_pmap_cohspace f pconst ==* f.
Proof.
  unfold sgop_pmap_cohspace.
  lhs' napply (pmap_prewhisker _ (wedge_rec_pconst_r f)).
  lhs' napply pmap_compose_assoc.
  lhs' napply (pmap_postwhisker _ cohspace_left_identity).
  napply pmap_precompose_idmap.
Defined.

(** The type of pointed maps from a co-H-space is an H-space under [sgop_pmap_cohspace]. *)
Instance ishspace_pmap_cohspace `{Funext} (X Y : pType) `{IsCoHSpace X}
  : IsHSpace (X ->** Y).
Proof.
  snapply Build_IsHSpace.
  - exact sgop_pmap_cohspace.
  - intro g; exact (path_pforall (leftidentity_pmap_cohspace g)).
  - intro f; exact (path_pforall (rightidentity_pmap_cohspace f)).
Defined.

Class IsHSpaceMap {X Y : pType} `{IsHSpace X} `{IsHSpace Y} (f : X ->* Y) := {
  (* I'm not sure why Rocq gets confused if I use [*] in the next line for the operation on [Y]. *)
  preserves_hspace_op : forall x y : X, f (x * y) = hspace_op (f x) (f y);
  preserves_left_identity : forall x : X, ap f (hspace_left_identity x)
                                     = preserves_hspace_op pt x @ ap (.* f x) (point_eq f) @ hspace_left_identity (f x);
  preserves_right_identity : forall x : X, ap f (hspace_right_identity x)
                                      = preserves_hspace_op x pt @ ap (f x *.) (point_eq f) @ hspace_right_identity (f x);
}.

(** ** Inverse maps *)

(** [r] is an inverse map for the H-space [X] if it is a right inverse of [pmap_idmap] in [X ->* X] under the pointwise sum [sgop_pmap]. Unfolding [==*], this is the pointwise condition [x * r x = pt] together with a coherence at the base point identifying its value there with [left_identity (r pt) @ point_eq r]. This makes the definition dual to [IsCoHSpaceInverse] and, unlike a bare pointwise condition, uses the pointedness of [r]. The underlying relation [x * y = pt] is preserved by H-space maps (see [hspace_map_preserves_inverse]). *)
Definition IsHSpaceInverse {X : pType} `{IsHSpace X} (r : X ->* X) : Type
  := sgop_pmap pmap_idmap r ==* pconst.

(** Dually, [r] is an inverse map for the co-H-space [X] if it is a right inverse of [pmap_idmap] in [X ->* X] under [sgop_pmap_cohspace]. *)
Definition IsCoHSpaceInverse {X : pType} `{IsCoHSpace X} (r : X ->* X) : Type
  := sgop_pmap_cohspace pmap_idmap r ==* pconst.

(** Inverse maps for a left-invertible H-space are unique, since [r x] is the unique right inverse of [x]. This lets us prove two maps equal by showing both are inverse maps. *)
Definition homotopic_ishspaceinverse `{Funext} {X : pType} `{IsHSpace X}
  `{forall x : X, IsEquiv (x *.)}
  {r s : X ->* X} (hr : IsHSpaceInverse r) (hs : IsHSpaceInverse s)
  : r ==* s.
Proof.
  apply hspace_phomotopy_from_homotopy.
  intro x.
  exact (equiv_inj (x *.) (hr x @ (hs x)^)).
Defined.

(** Every left-invertible H-space has an inversion map (which is unique by [homotopic_ishspaceinverse]).  In [BCFR], this is denoted [id^*]. *)
Definition hspace_right_inverse {X : pType} `{IsHSpace X}
  `{forall x : X, IsEquiv (x *.)}
  : X ->* X.
Proof.
  refine (Build_pMap (fun x => (x *.)^-1 pt) _).
  apply moveR_equiv_V.
  symmetry; apply hspace_left_identity.
Defined.

Definition ishspaceinverse_hspace_right_inverse {X : pType} `{IsHSpace X}
  `{forall x : X, IsEquiv (x *.)}
  : IsHSpaceInverse (hspace_right_inverse (X:=X)).
Proof.
  (* The second bullet can be removed if we use [hspace_phomotopy_from_homotopy], but that currently requires [Funext], so we'll avoid it. *)
  snapply Build_pHomotopy.
  - intros x; cbn.
    apply eisretr.
  - cbn.
    rhs napply concat_p1.
    unfold moveR_equiv_V.
    rhs napply (ap_pp _ _ _ @@ concat_1p _).
    rhs_V napply concat_p_pp.
    rhs_V napply (ap_compose _ _ _ @@ 1).
    rhs napply (ap_V (fun x => pt * (sg_op pt)^-1 x) _ @@ 1).
    apply moveL_Vp.
    lhs napply (concat_A1p (eisretr (sg_op pt))).
    nrefine (_ @@ 1).
    apply eisadj.
Defined.

(** When [X] is both left- and right-invertible, [hspace_right_inverse] is an equivalence. This applies when [X] is connected, or when [X] is left-invertible and commutative. *)
Instance isequiv_hspace_right_inverse {X : pType} `{IsHSpace X}
  `{forall x : X, IsEquiv (x *.)} `{forall x : X, IsEquiv (.* x)}
  : IsEquiv (hspace_right_inverse (X:=X)).
Proof.
  cbn.
  snapply isequiv_adjointify.
  - exact (fun x => (.* x)^-1 pt).
  - intro z.
    apply equiv_moveR_equiv_V.
    symmetry; apply (eisretr (.* z)).
  - intro z.
    apply equiv_moveR_equiv_V.
    symmetry; apply (eisretr (z *.)).
Defined.

(** When [X] is left-invertible and commutative, [hspace_right_inverse] is an involution. *)
Definition hspace_right_inverse_involutive  {X : pType} `{IsHSpace X}
  `{forall x : X, IsEquiv (x *.)} `{comm : Commutative X X hspace_op}
  : hspace_right_inverse (X:=X) o hspace_right_inverse == idmap.
Proof.
  cbn.
  intro z.
  apply equiv_moveR_equiv_V.
  symmetry.
  lhs rapply comm.
  apply eisretr.
Defined.

(** An H-space map sends inverse pairs to inverse pairs: if [x * y = pt] then [f x * f y = pt]. This uses only that [f] preserves the operation and the base point. *)
Definition hspace_map_preserves_inverse {X Y : pType} `{IsHSpace X} `{IsHSpace Y}
  (f : X ->* Y) `{!IsHSpaceMap f} {x y : X} (p : x * y = pt)
  : f x * f y = pt.
Proof.
  lhs_V rapply preserves_hspace_op.
  lhs napply (ap f p).
  exact (point_eq f).
Defined.

(** Consequently, an H-space map into a left-invertible H-space commutes with inverse maps: [f (r x)] is the inverse of [f x]. Writing [-] for the inverse, this is [f (- x) = - (f x)]. *)
Definition hspacemap_ishspaceinverse {X Y : pType} `{IsHSpace X} `{IsHSpace Y}
  `{forall y : Y, IsEquiv (y *.)}
  (f : X ->* Y) `{!IsHSpaceMap f}
  {r : X ->* X} (hr : IsHSpaceInverse r)
  {s : Y ->* Y} (hs : IsHSpaceInverse s)
  : forall x : X, f (r x) = s (f x).
Proof.
  intro x.
  rapply (equiv_inj (f x *.)).
  lhs rapply (hspace_map_preserves_inverse f (hr x)).
  symmetry; napply hs.
Defined.

(** ** Induced inverse maps on pointed mapping spaces *)

(** If [A] is a co-H-space with an inverse map [r], then precomposition with [r] gives an inverse map on the [sgop_pmap_cohspace] H-space [A ->* B]: for each [f], the map [f o* r] is a right inverse of [f]. *)
Definition iscohspaceinverse_pmap {A B : pType} `{IsCoHSpace A}
  {r : A ->* A} (hr : IsCoHSpaceInverse r) (f : A ->* B)
  : sgop_pmap_cohspace f (f o* r) ==* pconst.
Proof.
  lhs' napply (sgop_pmap_cohspace_phomotopy
    (pmap_precompose_idmap f)^* (phomotopy_reflexive (f o* r))).
  lhs_V' napply sgop_pmap_cohspace_postcompose.
  lhs' napply (pmap_postwhisker f hr).
  exact (precompose_pconst f).
Defined.

(** Dually, if [X] is an H-space with an inverse map [s], then postcomposition with [s] gives an inverse map on the pointwise H-space [A ->* X]: for each [f], the map [s o* f] is a right inverse of [f] under [sgop_pmap]. This needs no coherence on [X]. We build the pointed homotopy by hand so that its underlying homotopy is exactly [fun a => hs (f a)]; the base-point coherence is borrowed from [pmap_prewhisker f hs], whose underlying homotopy agrees, so what remains is a base-point identity that [pelim] discharges. *)
Definition ishspaceinverse_pmap {A X : pType} `{IsHSpace X}
  {s : X ->* X} (hs : IsHSpaceInverse s) (f : A ->* X)
  : sgop_pmap f (s o* f) ==* pconst.
Proof.
  snapply Build_pHomotopy.
  - exact (hs o f).
  - lhs napply (dpoint_eq (pmap_prewhisker f hs)).
    clear hs; pelim f s; cbn.
    exact (concat_1p _ @@ 1).
Defined.

(** ** Coincidence of the pointwise and co-H-space sums *)

(** The interchange law relating the two sums on [A ->* Y]. No unit laws are used, so this needs no coherence. *)
Definition sgop_pmap_interchange {A Y : pType} `{IsCoHSpace A} `{IsHSpace Y}
  (a b c d : A ->* Y)
  : sgop_pmap (sgop_pmap_cohspace a b) (sgop_pmap_cohspace c d)
    ==* sgop_pmap_cohspace (sgop_pmap a c) (sgop_pmap b d).
Proof.
  unfold sgop_pmap_cohspace.
  lhs_V' napply sgop_pmap_precompose.
  napply pmap_prewhisker.
  symmetry.
  snapply wedge_up'.
  - symmetry.
    lhs' napply sgop_pmap_precompose.
    exact (sgop_pmap_phomotopy
      (wedge_rec_beta_inl a b) (wedge_rec_beta_inl c d)).
  - symmetry.
    lhs' napply sgop_pmap_precompose.
    exact (sgop_pmap_phomotopy
      (wedge_rec_beta_inr a b) (wedge_rec_beta_inr c d)).
Defined.

(** On pointed maps from a co-H-space [A] into a coherent H-space [Y], the co-H-space sum [sgop_pmap_cohspace] agrees with the pointwise sum [sgop_pmap] by the Eckmann-Hilton argument (adapted to homotopies): [f + g = (f * pt) + (pt * g) = (f + pt) * (pt + g) = f * g]. *)
Definition sgop_pmap_agree {A Y : pType} `{IsCoHSpace A}
  `{IsCoherent Y} (f g : A ->* Y)
  : sgop_pmap_cohspace f g ==* sgop_pmap f g.
Proof.
  lhs' rapply (sgop_pmap_cohspace_phomotopy
    (rightidentity_pmap f)^* (leftidentity_pmap g)^*).
  lhs_V' rapply sgop_pmap_interchange.
  exact (sgop_pmap_phomotopy
    (rightidentity_pmap_cohspace f) (leftidentity_pmap_cohspace g)).
Defined.

(** The other half of Eckmann-Hilton: the common operation is commutative: [f * g = (pt + f) * (g + pt) = (pt * g) + (f * pt) = g + f = g * f]. *)
Definition commutative_sgop_pmap {A Y : pType} `{IsCoHSpace A}
  `{IsCoherent Y} (f g : A ->* Y)
  : sgop_pmap f g ==* sgop_pmap g f.
Proof.
  lhs_V' rapply (sgop_pmap_phomotopy
    (leftidentity_pmap_cohspace f) (rightidentity_pmap_cohspace g)).
  lhs' rapply sgop_pmap_interchange.
  lhs' rapply (sgop_pmap_cohspace_phomotopy
    (leftidentity_pmap g) (rightidentity_pmap f)).
  rapply sgop_pmap_agree.
Defined.

(** ** The [n]-truncation functor preserves the H-space structure *)

(** When [A] is a co-H-space and the n-truncation of [B] is a coherent H-space, the n-truncation functor sends the [sgop_pmap_cohspace] operation on [A ->* B] to the pointwise sum [sgop_pmap] on [pTr n A ->* pTr n B]. Both sides are determined by their precomposite with [ptr : A ->* pTr n A] (as [pTr n B] is [n]-truncated), so by [pTr_ind_homotopy] the claim reduces to [sgop_pmap_agree] via naturality of [ptr]. Put another way, we are using the triangle
<<
          (A ->* B)  ----> (pTr n A ->* pTr n B)
               \             /
                \           /
                 v         v
                (A ->* pTr n B)
>>
The diagonal maps are post- and pre-composition with a [ptr] map and so respect the operations [sgop_pmap_cohspace] and [sgop_pmap], respectively.  Those operations agree on the bottom type, and the right-hand diagonal map is an equivalence, so the top map respects the operations as well. *)
Definition ptr_functor_sgop_pmap {n : trunc_index} {A B : pType}
  `{IsCoHSpace A} `{IsCoherent (pTr n B)} (f g : A ->* B)
  : fmap (pTr n) (sgop_pmap_cohspace f g)
    ==* sgop_pmap (fmap (pTr n) f) (fmap (pTr n) g).
Proof.
  rapply pTr_indpaths.
  lhs' napply (ptr_natural n (sgop_pmap_cohspace f g)).
  lhs' napply sgop_pmap_cohspace_postcompose.
  lhs' rapply sgop_pmap_agree.
  rhs' napply sgop_pmap_precompose.
  exact (sgop_pmap_phomotopy (ptr_natural n f)^* (ptr_natural n g)^*).
Defined.

(** If in addition [A] has a co-H-space inverse [r], then [n]-truncation carries the induced inverse of a map [f : A ->* B] (precomposition with [r]) to a right inverse of [fmap (pTr n) f] under [sgop_pmap]. *)
Definition ptr_functor_iscohspaceinverse_pmap {n : trunc_index}
  {A B : pType} `{IsCoHSpace A} `{IsCoherent (pTr n B)}
  {r : A ->* A} (hr : IsCoHSpaceInverse r) (f : A ->* B)
  : sgop_pmap (fmap (pTr n) f) (fmap (pTr n) (f o* r)) ==* pconst.
Proof.
  lhs_V' rapply ptr_functor_sgop_pmap.
  lhs' tapply (fmap2 (pTr n) (iscohspaceinverse_pmap hr f)).
  napply ptr_functor_pconst.
Defined.

(** Taking [B] to be [A] and [f] to be [pmap_idmap], the [n]-truncation of a co-H-space inverse map on [A] is an H-space inverse map on [pTr n A]. *)
Definition ptr_functor_ishspaceinverse {n : trunc_index} {A : pType}
  `{IsCoHSpace A} `{IsCoherent (pTr n A)}
  {r : A ->* A} (hr : IsCoHSpaceInverse r)
  : IsHSpaceInverse (fmap (pTr n) r).
Proof.
  unfold IsHSpaceInverse.
  rhs_V' rapply (ptr_functor_iscohspaceinverse_pmap hr pmap_idmap).
  symmetry; apply sgop_pmap_phomotopy.
  - tapply (fmap_id (pTr n)).
  - tapply (fmap2 (pTr n)).
    apply pmap_postcompose_idmap.
Defined.

(** Going back to independent [A] and [B], as in [ptr_functor_iscohspaceinverse_pmap], if moreover [pTr n B] is left-invertible and has an inverse [s], then the right inverse above is the induced inverse on [pTr n A ->* pTr n B] (postcomposition with [s]).  Both are right inverses of [fmap (pTr n) f] under [sgop_pmap], and these are unique because [pTr n A ->* pTr n B] is left-invertible. *)
Definition ptr_functor_ishspaceinverse_unique `{Funext} {n : trunc_index}
  {A B : pType} `{IsCoHSpace A} `{IsCoherent (pTr n B)}
  `{forall y : pTr n B, IsEquiv (y *.)}
  {r : A ->* A} (hr : IsCoHSpaceInverse r)
  {s : pTr n B ->* pTr n B} (hs : IsHSpaceInverse s)
  (f : A ->* B)
  : fmap (pTr n) (f o* r) ==* s o* fmap (pTr n) f.
Proof.
  apply phomotopy_path.
  tapply (equiv_inj (sgop_pmap (fmap (pTr n) f))).
  1: rapply isleftinvertible_hspace_pmap.
  apply path_pforall.
  lhs' rapply (ptr_functor_iscohspaceinverse_pmap hr f).
  symmetry; apply (ishspaceinverse_pmap hs).
Defined.

(** ** Suspensions as co-H-spaces *)

(** [BCM:prop:iscohspace-susp] *)
Instance iscohspace_susp (X : pType) : IsCoHSpace (psusp X).
Proof.
  snapply Build_IsCoHSpace.
  - snapply Build_pMap.
    + snapply Susp_rec.
      * exact (wedge_inl North).
      * exact (wedge_inr South).
      * intro x; cbn zeta.
        (* The underscores are [wedge_inl] and [wedge_inr], respectively, but if you write them in, Rocq has trouble figuring out their implicit arguments. *)
        exact (ap _ (merid x @ (merid pt)^) @ wglue @ ap _ (merid x)).
    + reflexivity.
  - snapply Build_pHomotopy.
    + snapply Susp_ind_FFlr.
      1, 2: simpl.
      * reflexivity.
      * exact (merid pt).
      * intro x.
        rewrite Susp_rec_beta_merid.
        rewrite 2 ap_pp.
        rewrite <- 2 ap_compose.
        rewrite (wedge_rec_beta_wglue (@pmap_idmap (psusp X)) pconst).
        simpl.
        rewrite ap_idmap.
        rewrite ap_const.
        rewrite 2 concat_p1.
        rhs napply concat_1p.
        apply concat_pV_p.
    + reflexivity.
  - snapply Build_pHomotopy.
    + snapply Susp_ind_FFlr.
      1, 2: simpl.
      * reflexivity.
      * reflexivity.
      * intro x.
        rewrite Susp_rec_beta_merid.
        apply equiv_p1_1q.
        rewrite 2 ap_pp.
        rewrite <- 2 ap_compose.
        rewrite (wedge_rec_beta_wglue pconst (@pmap_idmap (psusp X))).
        simpl.
        rewrite ap_idmap.
        rewrite ap_const.
        apply concat_1p.
    + reflexivity.
Defined.

Definition sgop_pmap_susp {X Y : pType}
  (f g : psusp X ->* Y) : psusp X ->* Y.
Proof.
  snapply Build_pMap.
  - snapply Susp_rec.
    + exact (f North).
    + exact (g South).
    + intro x.
      exact (ap f (merid x @ (merid pt)^) @ point_eq f @ (point_eq g)^ @ ap g (merid x)).
  - exact (point_eq f).
Defined.

(** [BCM:cor:sum-susp] *)
Definition sgop_pmap_cohspace_susp {X Y : pType}
  (f g : psusp X ->* Y)
  : sgop_pmap_cohspace f g ==* sgop_pmap_susp f g.
Proof.
  snapply Build_pHomotopy.
  - snapply Susp_ind_FlFr.
    + reflexivity.
    + reflexivity.
    + intro x.
      apply equiv_p1_1q.
      unfold sgop_pmap_cohspace, sgop_pmap_susp, "o*", iscohspace_susp, cohspace_op,
        Build_pMap, pointed_fun.
      rewrite ap_compose.
      rewrite 2 Susp_rec_beta_merid.
      rewrite 2 ap_pp.
      rewrite wedge_rec_beta_wglue.
      rewrite <- 2 ap_compose.
      simpl.
      exact (concat_p_pp _ _ _ @@ 1).
  - simpl.
    symmetry; apply concat_pp_V.
Defined.

(** The negation map [susp_neg] of a suspension is pointed, via the meridian at the base point. *)
Definition psusp_neg (X : pType) : psusp X ->* psusp X
  := Build_pMap (susp_neg X) (merid pt)^.

(** [psusp_neg] is a pointed equivalence, since [susp_neg] is an equivalence. *)
Definition pequiv_susp_neg (X : pType) : psusp X <~>* psusp X
  := Build_pEquiv (psusp_neg X) (isequiv_susp_neg X).

(** Suspensions have inverses: [psusp_neg] is an inverse map for the co-H-space [psusp X]. *)
Definition iscohspaceinverse_psusp_neg (X : pType)
  : IsCoHSpaceInverse (psusp_neg X).
Proof.
  unfold IsCoHSpaceInverse.
  lhs' napply sgop_pmap_cohspace_susp.
  snapply Build_pHomotopy.
  - snapply Susp_ind_FlFr.
    1, 2: reflexivity.
    intro x.
    apply equiv_p1_1q.
    rhs napply ap_const.
    cbn.
    lhs napply Susp_rec_beta_merid.
    lhs napply (((ap_idmap _ @@ 1) @@ inv_V _) @@ Susp_rec_beta_merid (H_N:=South) x).
    lhs napply ((concat_p1 _ @@ 1) @@ 1).
    lhs napply (concat_pV_p _ _ @@ 1).
    napply concat_pV.
  - reflexivity.
Defined.
