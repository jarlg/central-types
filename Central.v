From HoTT Require Import Basics Types Pointed Truncations
  Homotopy.HSpace Homotopy.Cover Homotopy.EvaluationFibration
  WhiteheadsPrinciple WildCat PathAny
  Modalities.ReflectiveSubuniverse Modalities.Separated.

Require Import Lemmas HSpace Cover SelfMaps Bands BAut1 Smallness misc.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope trunc_scope.

(** * Central types *)

(** A pointed type is central if the evaluation fibration of the identity is an equivalence. *)
Class Central (A : pType) := central : IsEquiv (ev1 A).
Global Existing Instance central.

Global Instance isequiv_ev1' `{Univalence} {A : pType@{u}} `{Central@{u} A}
  : IsEquiv (ev1' A).
Proof.
  change (pointed_fun (ev1' A))
    with (ev1 A o pequiv_pcomp_equiv_to_map pequiv_pmap_idmap).
  rapply isequiv_compose.
Defined.

Definition pequiv_ev1' `{Univalence} {A : pType} `{Central A}
  : pcomp (A <~> A) equiv_idmap <~>* A
  := Build_pEquiv _ _ (ev1' A) _.

(** Central types are connected. *)
Global Instance isconnected_central {A : pType} `{Central A}
  : IsConnected 0 A := isconnected_equiv _ _ (ev1 A) _.

(** Central types are automatically H-spaces. *)
(** TODO: Show that [IsCohHSpace A] is contractible. *)
Definition cohhspace_central `{Funext} {A : pType} `{Central A}
  : IsCohHSpace A := induced_cohhspace_equiv_ev1 A.

Global Instance ishspace_central `{Funext} {A : pType} `{Central A}
  : IsHSpace A := ishspace_cohhspace A cohhspace_central.

(** Thus [pBAut1 A] is an H-space whenever [A] is central. *)
Global Instance ishspace_baut1_central `{Univalence} {A : pType} `{Central A}
  : IsHSpace (pBAut1 A)
  := hspace_twisted_baut1.

Global Instance iscoherent_baut1_central `{Univalence} {A : pType} `{Central A}
  : IsCoherent (pBAut1 A)
  := iscoherent_hspace_twisted_baut1.

(** Coq knows that the H-space structure is left and right invertible. *)

(** TODO: Finish characterization of central types. *)

(** Lemma 3.5 is [equiv_hfiber_ev1] in SelfMaps. We use this to prove (most of) Lemma 3.6, which gives several characterizations of central types.  We begin by showing that a connected H-space is central if the pointed self-equivalences form a set, which is (3) => (1) in Lemma 3.6. *)
Proposition central_connected_hspace_pequiv_set `{Univalence} {A : pType}
  `{IsConnected 0 A, IsHSpace A, IsHSet (A <~>* A)}
  : Central A.
Proof.
  apply isequiv_contr_map; hnf.
  rapply (conn_point_elim (-1)).
  rapply (contr_equiv' _ equiv_hfiber_ev1^-1).
  (** Coq knows that components of sets are contractible, so it suffices to change the goal to a component of [A <~>* A]. *)
  apply (contr_equiv _ (pequiv_pcomp_pequiv_to_pmap pequiv_pmap_idmap)).
Defined.

(** This is (1) => (2) in Lemma 3.6. *)
Proposition pmap_set_central `{Univalence} {A : pType} `{Central A}
  : IsHSet (A ->* A).
Proof.
  rapply ishset_contr_comp.
  intro phi.
  rapply (contr_equiv' (comp (A ->* A) (tr pmap_idmap))).
  { unshelve rapply (pequiv_comp_hspace (A ->** A)).
    apply cohhspace_central. }
  rapply (contr_equiv' _ equiv_hfiber_ev1).
Defined.

(* todo: Put in Pointed/Core.v *)
Global Instance isembedding_pointed_equiv_fun `{Funext} (X Y : pType)
  : IsEmbedding (pointed_equiv_fun X Y).
Proof.
  (* After precomposing with [issig_pequiv X Y], we need to show that [pr1] is a (-1)-truncated map, which is handled by [mapinO_pr1]. *)
  srefine (cancelR_equiv_mapinO (Tr (-1)) (issig_pequiv X Y) _).
Defined.

(** This is (2) => (3) in Lemma 3.6. *)
Proposition pequiv_hset_pequiv_pmap `{Funext} {A : pType} `{IsHSet (A ->* A)}
  : IsHSet (A <~>* A).
Proof.
  rapply (istrunc_embedding_trunc (pointed_equiv_fun A A)).
Defined.

(** This is (1) => (3) in Lemma 3.6. *)
Proposition pequiv_set_central `{Univalence} {A : pType} `{Central A}
  : IsHSet (A <~>* A).
Proof.
  nrapply pequiv_hset_pequiv_pmap.
  rapply pmap_set_central.
Defined.

(** This is (4) => (2) in Lemma 3.6, except that we do not assume that [A] is coherent.  We use [iscohhspace_hspace] to upgrade the H-space structure. Note that saying that a pointed mapping space is an h-prop is equivalent to saying that it is contractible. *)
Proposition pmap_set_connected_hspace_hprop_pmap_loops `{Univalence} {A : pType}
  `{IsConnected 0 A, IsHSpace A} {HP : IsHProp (A ->* loops A)}
  : IsHSet (A ->* A).
Proof.
  (* It's enough to show that the loop spaces are h-props: *)
  apply (equiv_istrunc_istrunc_loops (-2) _)^-1.
  intro phi.
  (* Since [A ->* A] is homogeneous, it's enough to check this for [phi] the constant map.  Here we use that [A ->* A] is again a left-invertible H-space, which requires coherence.  We could alternatively refactor this through [A ->* A] being homogeneous, which shouldn't need coherence.  In any case, we simply upgrade the H-space structure to a coherent one. *)
  rapply (istrunc_equiv_istrunc (loops [A ->* A, pconst])).
  { rapply (emap loops).
    rapply ishomogeneous.
    unshelve rapply ishomogeneous_hspace.
    rapply iscohhspace_hspace. }
  (* We show that this loop space is equivalent to the type we know is an h-prop: *)
  refine (@istrunc_equiv_istrunc _ _ _ _ HP).
  symmetry.
  exact (equiv_loops_ppforall (fun a : A => A)).
Defined.

(** Therefore, (4) => (1). *)
Proposition central_connected_hspace_hprop_pmap_loops `{Univalence} {A : pType}
  `{IsConnected 0 A, IsHSpace A} {C : IsHProp (A ->* loops A)}
  : Central A.
Proof.
  rapply central_connected_hspace_pequiv_set.
  nrapply pequiv_hset_pequiv_pmap.
  apply pmap_set_connected_hspace_hprop_pmap_loops.
Defined.

(** (Prop. 3.12) All evaluation fibrations of self-maps of a central type are equivalences. *)
Global Instance isequiv_evfib_selfmap_central `{Univalence}
  {A : pType} `{Central A} (f : A ->* A)
  : IsEquiv (evfib f).
Proof.
  nrapply (isequiv_homotopic (ev1 A o pequiv_comp_hspace [A -> A, const pt] _ _)).
  - apply isequiv_compose.
  - snrapply (equiv_ind (pequiv_comp_hspace_pt [A -> A, const pt] f) _).
    + rapply ishspace_map.
    + rapply isleftinvertible_hspace_map.
    + exact _.
    + intros [phi p]; cbn in phi, p.
      unfold pequiv_comp_hspace.
      refine (ap (ev1 A o pequiv_comp_hspace_pt [A -> A, const pt] pmap_idmap)
                (eissect _ _) @ _); simpl.
      unfold "*".
      by rewrite (point_eq f).
Defined.

(** The inversion operation on a central type. *)
Definition inv `{Univalence} {A : pType} `{Central A} : A ->* A.
Proof.
  refine (Build_pMap _ _ (fun a => (a *.)^-1 pt) _).
  apply moveR_equiv_V.
  exact (hspace_left_identity _)^.
Defined.

Definition equiv_inv `{Univalence} {A : pType} `{Central A}
  : A <~>* A.
Proof.
  apply (Build_pEquiv _ _ inv).
  (* Since [A] is connected, it suffices to show that [hfiber inv pt] is contractible. *)
  apply isequiv_contr_map; hnf.
  rapply (conn_point_elim (-1)).
  (* This fibre is equivalent to the following, which is clearly contractible. *)
  rapply (contr_equiv' {a : A & pt = a}).
  apply equiv_functor_sigma_id; intro a.
  unfold inv, Build_pMap, pointed_fun.
  refine (Build_Equiv _ _ (moveR_equiv_V _ _) _ oE _).
  apply equiv_concat_r.
  exact (hspace_right_identity _)^.
Defined.

(** In order to show that [inv] is an involution (or equivalently, equal to it's own inverse), we need associativity. This is needed for various later things. For this reason I reverted to the old approach in Bands.v. *)

(** ** [BAut1 A] is a delooping of a central type *)

(** When [A] is central, [BAut1] is a delooping of [A]. (Prop. 4.4) *)
Definition pequiv_loops_baut1@{u v w | u < v, v < w} `{Univalence}
  {A : pType@{u}} `{Central@{u} A}
  : loops (pBAut1 A) <~>* A
  := pequiv_ev1'@{u v} o*E (pequiv_pretensor_path_baut1@{u v w w v} pt)^-1*.

(** We will frequently work with pointed, connected types. This could be a Record, but then we'd have to use issig in several places. *)
Definition pcType@{u +} := { B : pType@{u} & IsConnected 0 B }.

Definition pctype_pr1 : pcType -> pType := pr1.

Coercion pctype_pr1 : pcType >-> pType.

(* Why doesn't this work?  Compare the top of Spaces/BAut.v.
Coercion pctype_pr1 : pcType -> pType := pr1.
*)

Global Instance isconnected_pctype (BC : pcType)
  : IsConnected 0 BC.1
  := BC.2.

Definition equiv_path_pctype `{Univalence} (A B : pcType) : A <~>* B <~> A = B.
Proof.
  nrefine (_ oE equiv_path_ptype _ _).
  apply equiv_path_sigma_hprop.
Defined.

(** ** Uniqueness of deloopings *)

(** The delooping [BAut1 A] of a central type is unique. (Theorem 4.6) *)

Section UniqueDelooping.

  (** Given a delooping [B] of [A], i.e., a pointed, connected type equipped with a pointed equivalence [e : loops B <~>* A], we construct a pointed equivalence [B <~>* pBAut1 A] which respects [e] and [pequiv_loops_baut1] on loops. In other words, [pBAut1 A] is the unique delooping of [A]. *)

  Universes u v.

  Context `{Univalence} {A : pType@{u}} {B : pcType@{u v}}
    `{Central A} (e : loops B <~>* A).

  (** We can band [pt = b] for any [b : B]. *)
  Definition delooping_central_banding
    : forall b:B, tr (n:=1) (point B = b) = tr@{v} (pointed_type A).
  Proof.
    nrapply (conn_point_elim 0).
    - rapply (isconnected_isconnected_loops'@{u v} e).
    - exact _.
      (* todo: experimenting *)
      (* This would work: 
    - apply (ap tr), path_universe_uncurried.
       but this is more convenient below: *)
    - apply path_Tr, tr, path_universe_uncurried.
      exact e.
  Defined.

  (** This lets us produce a map [B -> BAut1 A]. *)
  Definition delooping_to_baut1 : B -> pBAut1 A
    := fun b => (pt = b; delooping_central_banding b).

  (* There are (a priori) two ways of making this map pointed: using [pointed_tensor_trivial], and using [e]. In fact, these identifications are equal, as we now show. *)

  (** First we construct the identification which uses [e]. *)
  Definition delooping_central_band_pt
    : delooping_to_baut1 (point B) = pt.
  Proof.
    apply equiv_pretensor_path_baut1.
    exists e.
    rewrite concat_p1.
    refine (_ @ ap _ _^).
    2: { unfold delooping_to_baut1, delooping_central_banding.
         refine (ap _ (conn_point_elim_beta _ _ _) @ _).
         apply eissect. }
    cbn. apply (ap tr).
    exact (eisretr _ _)^.
  Defined.

  (* TODO: Is it hard to instead show
    : delooping_central_band_pt
      = (pointed_tensor_trivial (delooping_to_baut1 pt) idpath)^.
    ?  This would match the comment above better. *)
  Definition delooping_central_band_pt_comp
    : delooping_central_band_pt^
      = pointed_tensor_trivial (delooping_to_baut1 pt) idpath.
  Proof.
    apply moveL_equiv_M.
    refine (ap (ev_band _) _ @ _).
    1: { refine (baut1_symm_comp _ @ ap (baut1_symm _ _) _ ).
         apply eissect. }
    lazy beta.
    exact (point_eq e^-1*).
  Defined.

  (** Now we define the pointed map using [pointed_tensor_trivial]. *)
  Definition delooping_pto_baut1 : B ->* pBAut1 A.
  Proof.
    srapply Build_pMap.
    1: exact (fun b => (pt = b; delooping_central_banding b)).
    lazy beta.
    symmetry; apply pointed_tensor_trivial; unfold pr1.
    reflexivity.
  Defined.

  (** The action of [delooping_pto_baut1] on paths [p : pt = b] is by right-concatenation. *)
  Definition ap_delooping_pto_baut1 {b : B}
    : forall p : pt = b, ((equiv_pretensor_path_baut1 _ _ _)^-1
                       (ap delooping_pto_baut1 p)).1
                    == equiv_concat_r p _.
  Proof.
    intros [] q; cbn.
    exact (concat_p1 _)^.
  Defined.

  (** It remains to show that [delooping_pto_baut1] is an equivalence, and that after looping it respects [e] and [pequiv_loops_baut1]. In fact, we deduce the former from the latter. *)

  Definition delooping_pto_baut1_htpy
    : e == pequiv_loops_baut1 o fmap loops delooping_pto_baut1.
  Proof.
    intro q; symmetry.
    simpl.
    rewrite inv_V, 2 pr1_path_pp, 2 transport_pp.
    refine (ap _ _ @ _).
    { refine (ap _ (pointed_tensor_trivial_comp _) @ _).
      apply ap_delooping_pto_baut1. }
    simpl. rewrite concat_1p.
    rewrite <- delooping_central_band_pt_comp, inv_V.
    exact (transport_idmap_pretensor_path_baut1
             (delooping_to_baut1 pt) pt _ _).
  Defined.

  (** Since [A] is an H-space, we can promote this to a pointed homotopy. *)
  Definition delooping_pto_baut1_phtpy
    : e ==* pequiv_loops_baut1 o* fmap loops delooping_pto_baut1.
  Proof.
    apply hspace_phomotopy_from_homotopy, delooping_pto_baut1_htpy.
  Defined.

  (** From the commuting triangle above, we deduce that [delooping_pto_baut1] is an equivalence. *)
  Theorem isequiv_delooping_pto_baut1
    : IsEquiv delooping_pto_baut1.
  Proof.
    rapply isequiv_is0connected_isequiv_loops.
    1: apply isconnected_pctype. (* Why doesn't Coq find this? *)
    apply (isequiv_homotopic (pequiv_loops_baut1^-1 oE e)).
    intro x.
    apply moveR_equiv_V, delooping_pto_baut1_htpy.
  Defined.

  Definition delooping_pequiv_baut1 : B <~>* pBAut1 A
    := Build_pEquiv _ _ delooping_pto_baut1 isequiv_delooping_pto_baut1.

End UniqueDelooping.

Global Instance issmall_baut1@{u v w | u < v, v < w} `{Univalence} (A : pType@{u}) `{Central@{u} A}
  : IsSmall@{u v} (pBAut1@{u v} A)
  := issmall_issmall_loops (Build_IsSmall _ _ pequiv_loops_baut1^-1).

(** A pointed version of smallness. *)
Definition issmall_pbaut1@{u v w | u < v, v < w} `{Univalence} (A : pType@{u}) `{Central@{u} A}
  : { BA : pType@{u} & BA <~>* pBAut1@{u v} A }
  := (_; pequiv_from_pointed_codomain (equiv_smalltype (pBAut1 A))).

(** We break it up to make it easier to use. *)
Definition spBAut1@{u v w | u < v, v < w} `{Univalence} (A : pType@{u}) `{Central@{u} A}
  : pType@{u}
  := (issmall_pbaut1 A).1.

Definition pequiv_spbaut1_pbaut1@{u v w | u < v, v < w} `{Univalence} (A : pType@{u}) `{Central@{u} A}
  : spBAut1@{u v w} A <~>* pBAut1@{u v} A
  := (issmall_pbaut1 A).2.

(** We also record that [spBAut1 A] is again a delooping, and is connected. *)
Definition pequiv_loops_spbaut1@{u v w | u < v, v < w} `{Univalence} (A : pType@{u}) `{Central@{u} A}
  : loops@{v} (spBAut1@{u v w} A) <~>* A
  := pequiv_loops_baut1 o*E (emap loops@{v} (pequiv_spbaut1_pbaut1 A)).

Global Instance isconnected_spbaut1@{u v w | u < v, v < w} `{Univalence} (A : pType@{u}) `{Central@{u} A}
  : IsConnected@{u} 0 (spBAut1 A)
  := isconnected_equiv' 0 _ (pequiv_spbaut1_pbaut1 A)^-1%equiv _.

(* TODO: get rid of rewrites? *)

(** Abstracting the main idea of the argument makes it go much more smoothly.  It's faster and requires many fewer universe annotations. This has two universes, [u < v].  [v] is used to form the sigma type and for WildCat instances. *)
Lemma unique_delooping_helper@{u +} `{Univalence} (A : pType@{u})
  (BA : pcType@{u v}) (e : loops BA <~>* A)
  (f : forall B : pcType@{u v}, loops B <~>* A -> B <~>* BA)
  (h : forall (B : pcType@{u v}) (g : loops B <~>* A), g ==* e o* emap loops (f B g))
  : Contr { B : pcType@{u v} & loops B <~>* A }.
Proof.
  snrapply Build_Contr.
  - refine (BA; e).
  - intros [B g]; cbn in g.
    snrapply path_sigma.
    + unfold ".1".
      rapply equiv_path_pctype.
      exact (f B g)^-1*.
    + cbn beta; unfold ".2".
      refine (transport_compose (fun Y : pType => loops Y <~>* A) pctype_pr1 _ _ @ _).
      refine (transport_compose (fun Y : pType => Y <~>* A) (fun Y : _ => loops Y) _ _ @ _).
      rewrite ap_pr1_path_sigma_hprop.
      rewrite (ap_functor_path_ptype loops).
      refine (transport_pequiv_toconst_path_ptype _ _ @ _).
      apply path_pequiv.
      refine (_ @* (h B g)^* ).
      rapply pmap_postwhisker.
      refine (cate_inv2 (emap_inv loops _)^* $@ _).
      rapply cate_inv_V.
Defined.

(** This version handles the situation where the center of contraction is large (in universe [v]), but is equivalent to a type in universe [u]. That this goes through uses cumulativity in various ways. *)
Lemma unique_delooping_helper2@{u v w | u < v, v < w} `{Univalence} (A : pType@{u})
  (BA : pcType@{v w}) (e : loops BA <~>* A)
  (sBA : pType@{u}) (es : sBA <~>* BA)
  (f : forall B : pcType@{u v}, loops B <~>* A -> B <~>* BA)
  (h : forall (B : pcType@{u v}) (g : loops@{u} B <~>* A), g ==* e o* emap loops (f B g))
  : Contr { B : pcType@{u v} & loops B <~>* A }.
Proof.
  snrapply unique_delooping_helper.
  - exact (sBA; isconnected_equiv' 0 _ (es)^-1%equiv _).
  - exact (e o*E emap loops es).
  - intros B g.
    exact (es^-1* o*E f B g).
  - intros B g; cbn beta.
    nrefine (h B g @* _^*).
    nrefine (pmap_compose_assoc _ _ _ @* _).
    nrapply pmap_postwhisker.
    nrefine (pmap_postwhisker _ _ @* _).
    1: { refine (emap_compose loops@{v} _ _ @* _).  (* Cumulativity is used here. *)
         exact (pmap_prewhisker _ (emap_inv loops es)^*). }
    exact (compose_h_Vh _ _).
Defined.

(** A central type in universe [u] has a unique connected delooping in universe [u].  One can also show that it has a unique delooping in a larger universe [v], since any such delooping is automatically [u]-small.  This would make the next few results cleaner, since we could take [pBAut1 A] as the center of contraction. But this statement is the more natural one. *)
Global Instance unique_delooping_central@{u v w | u < v, v < w} `{Univalence}
  (A : pType@{u}) `{Central@{u} A}
  : Contr { B : pcType@{u v} & loops B <~>* A }.
Proof.
  snrapply unique_delooping_helper2@{u v w}.
  - exists (pBAut1 A); exact _.
  - rapply pequiv_loops_baut1.
  - exact (spBAut1 A).
  - exact (pequiv_spbaut1_pbaut1 A).
  - intros B g; cbn.
    exact (delooping_pequiv_baut1@{u v w v} g).
  - intros B g; cbn beta.
    nrapply delooping_pto_baut1_phtpy.
Defined.

(** We will show that the loops functor defined here is an equivalence. This shows that equivalences have unique deloopings. *)
Definition loops_functor_pbaut1@{u v w | u < v, v < w} `{Univalence}
  (A B : pType@{u}) `{Central@{u} A}
  : (B <~>* pBAut1@{u v} A) -> (loops B <~>* A).
Proof.
  refine (_ o emap loops).
  exact (equiv_postcompose_core_cat_equiv@{w v v v w u v} pequiv_loops_baut1).
Defined.

(** To do this, we show that on total spaces, it is a map between contractible types.  The codomain is done in [unique_delooping_central], so we handle the domain now. *)
Global Instance contr_sigma_pequiv@{u v w | u < v, v < w} `{Univalence}
   {A : pType@{u}} `{Central A}
  : Contr { B : pcType & B <~>* pBAut1 A }.
Proof.
  rapply (contr_equiv' {B : pcType & B = (spBAut1 A; isconnected_spbaut1 A)}).
  refine (equiv_functor_sigma_id _); intros B.
  refine (_ oE (equiv_path_sigma_hprop _ _)^-1); unfold ".1".
  refine (_ oE equiv_pequiv_path _ _).
  exact (equiv_postcompose_core_cat_equiv@{w v v v w u v} (pequiv_spbaut1_pbaut1 A)).
Defined.

Global Instance isequiv_loops_functor_pbaut1@{u v w | u < v, v < w} `{Univalence}
  (A : pType@{u}) `{Central@{u} A} (B : pcType)
  : IsEquiv (loops_functor_pbaut1 A B).
Proof.
  revert B; apply isequiv_from_functor_sigma.
  rapply isequiv_contr_contr.
Defined.

Definition equiv_loops_functor_pbaut1 `{Univalence}
  (A : pType) `{Central A} (B : pcType)
  := Build_Equiv _ _ (loops_functor_pbaut1 A B) _.

(* Making this [Opaque] speeds up the [Defined] in the following proof. *)
Opaque spBAut1.

(** The special case of self-equivalences. The equivalence that is produced is roundabout, involving both [phi] and [phi^-1], as we need to pass through small types. *)
Definition unique_delooping_self_equivalences_central@{u v w +} `{Univalence}
  {A : pType@{u}} `{Central@{u} A}
  : (pBAut1 A <~>* pBAut1 A) <~> (A <~>* A).
Proof.
  refine (_ oE (equiv_precompose_core_cat_equiv@{w v v v w v v} (pequiv_spbaut1_pbaut1 A))).
  srefine (_ oE equiv_loops_functor_pbaut1@{u v w} _ (spBAut1 A;_)).
  2: exact (isconnected_equiv' 0 _ (pequiv_spbaut1_pbaut1 A)^-1 _).
  refine (equiv_precompose_core_cat_equiv@{w v v v w v v} _).
  symmetry; apply pequiv_loops_spbaut1.
Defined.

Transparent spBAut1.

Definition central_pbaut1@{u v w | u < v, v < w} `{Univalence}
  {A : pType@{u}} `{Central@{u} A}
  : Central (pBAut1 A).
Proof.
  (* Coq can find this, but this allows us to remove one universe variable. *)
  pose (@ishspace_baut1_central@{u v w v} _ A _).
  rapply central_connected_hspace_pequiv_set.
  nrapply (istrunc_equiv_istrunc (A <~>* A)).
  - symmetry; apply unique_delooping_self_equivalences_central.
  - nrapply pequiv_set_central@{u v}; assumption.
Defined.
