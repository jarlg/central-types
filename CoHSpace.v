Require Import HoTT.

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

(** [BCM:defn:cohspace-sum] *)
Definition cohspace_sum {X Y : pType} `{IsCoHSpace X}
  (f g : X ->* Y) : X ->* Y
  := wedge_rec f g o* cohspace_op.

Definition sum_susp {X Y : pType}
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
Definition cohspace_sum_susp {X Y : pType}
  (f g : psusp X ->* Y)
  : cohspace_sum f g ==* sum_susp f g.
Proof.
  snapply Build_pHomotopy.
  - snapply Susp_ind_FlFr.
    + reflexivity.
    + reflexivity.
    + intro x.
      apply equiv_p1_1q.
      unfold cohspace_sum, sum_susp, "o*", iscohspace_susp, cohspace_op,
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

(** The type of pointed maps from a co-H-space is an H-space under [cohspace_sum]. *)
Instance ishspace_pmap_from_cohspace `{Funext} (X Y : pType) `{IsCoHSpace X}
  : IsHSpace (X ->** Y).
Proof.
  snapply Build_IsHSpace.
  - exact cohspace_sum.
  - intro g.
    apply path_pforall.
    unfold cohspace_sum.
    refine (pmap_prewhisker cohspace_op (wedge_rec_pconst_l g) @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    exact (pmap_postwhisker _ cohspace_right_identity @* pmap_precompose_idmap _).
  - intro f.
    apply path_pforall.
    unfold cohspace_sum.
    refine (pmap_prewhisker cohspace_op (wedge_rec_pconst_r f) @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    exact (pmap_postwhisker _ cohspace_left_identity @* pmap_precompose_idmap _).
Defined.

(* Next:
? conclude that positive spheres are cohspaces
- If f is the antipodal map, it will require a non-trivial [point_eq f], which
  will exactly cancel the [ap f (merid pt)^]!
*)
