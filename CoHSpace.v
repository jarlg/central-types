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

(* Next:
? conclude that positive spheres are cohspaces
- If f is the antipodal map, it will require a non-trivial [point_eq f], which
  will exactly cancel the [ap f (merid pt)^]!
*)
