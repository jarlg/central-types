From HoTT Require Import Basics Types EquivGroupoids Pointed HFiber Truncations
  Homotopy.HSpace Homotopy.Cover Homotopy.EvaluationFibration WildCat.Yoneda
  Universes.Smallness.

From CentralTypes Require Import Lemmas SelfMaps Cover Conn Smallness.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.

(** * The type [BAut1 A]. *)

(** For a type [A], [BAut1 A] consists of types with a band to [A]. That is, it consists of pairs [(X, p)], where [X] is a type and [p : tr X = tr A], where [tr] denotes the map to the 1-truncation of [Type]. *)
Definition BAut1@{u v | u < v} (A : Type@{u}) : Type@{v}
  := hfiber@{v v} (tr@{v} (n:=1)) (tr A).
(** This is definitionally equal to [O_cover@{v} (O:=Tr 1) Type@{u} (tr A)], but using the above leads to goals involving [tr X] instead of the awkward [to (Tr 1) Type X]. *)

(** It sometimes helps reduce universes to use this in place of [pr1]. *)
Definition baut1_pr1@{u v} {A : Type@{u}} : BAut1@{u v} A -> Type@{u} := pr1.

Coercion baut1_pr1 : BAut1 >-> Sortclass.

Global Instance ispointed_baut1 {A : Type} : IsPointed (BAut1 A)
  := (A; idpath).

Definition pBAut1@{u v | u < v} (A : Type@{u}) : pType@{v}
  := [BAut1@{u v} A, _].

Definition pbaut1_pr1 {A : Type} : pBAut1 A ->* [Type, A]
  := Build_pMap pr1 idpath.

(** Coq knows that [BAut1 A] is 1-connected, but can't deduce that it is 0-connected, so we provide this. *)
Global Instance isconnected_BAut1 (A : Type) : IsConnected 0 (BAut1 A)
  := ltac:(rapply isconnected_pred).

(** We can "tensor" bands as follows. The 'pretensor' gives the underlying type: *)
Definition pretensor_baut1@{u v w | u < v, v < w} `{Univalence}
  {A : Type@{u}} (X Y : BAut1@{u v} A) : Type@{u}.
Proof.
  destruct X as [X p], Y as [Y q].
  refine (comp@{u} (X <~> Y) _).
  rapply (Trunc_functor@{v u v} 0 (equiv_path@{u v} _ _)).
  rapply (equiv_path_Tr _ _)^-1. (* Uses Univalence. *)
  exact (p @ q^).
Defined.

Global Instance ispointed_pretensor_baut1 `{Univalence} {A : Type} (X : BAut1 A)
  : IsPointed (pretensor_baut1 X X).
Proof.
  exists equiv_idmap.
  by rewrite concat_pV.
Defined.

(** A variant of the pretensor using equalities instead of equivalences. It lives in a higher universe. *)
Definition pretensor_baut1'@{u v w | u < v, v < w} `{Univalence} {A : Type@{u}}
  (X Y : BAut1@{u v} A) : Type@{v}
  := comp@{v} (paths@{v} X.1 Y.1)
       ((equiv_path_Tr _ _)^-1 (X.2 @ Y.2^)).

Global Instance ispointed_pretensor_baut1' `{Univalence} {A : Type} (X : BAut1 A)
  : IsPointed (pretensor_baut1' X X).
Proof.
  exists idpath.
  by rewrite concat_pV.
Defined.

Definition equiv_pretensor_pretensor' `{Univalence} {A : Type} (X Y : BAut1 A)
  : pretensor_baut1 X Y <~> pretensor_baut1' X Y.
Proof.
  destruct X as [X p], Y as [Y q].
  unfold pretensor_baut1, pretensor_baut1', comp, O_cover, hfiber, ".1", ".2".
  refine (equiv_inverse _).
  snapply equiv_functor_sigma'.
  1: apply equiv_equiv_path.
  intro e; destruct e.
  refine (equiv_moveL_equiv_M _ _ oE _).
  refine (equiv_concat_l _ _).
  cbn.
  exact (ap tr (eissect _ _)).
Defined.

Definition pequiv_pretensor_pretensor' `{Univalence} {A : Type} (X : BAut1 A)
  : [pretensor_baut1 X X, pt] <~>* [pretensor_baut1' X X, pt].
Proof.
  srapply Build_pEquiv'.
  1: exact (equiv_pretensor_pretensor' X X).
  apply path_sigma_hprop; cbn.
  apply path_universe_1.
Defined.

Definition equiv_pretensor_path_baut1' `{Univalence} {A : Type} (X Y : BAut1 A)
  : pretensor_baut1' X Y <~> (X = Y).
Proof.
  destruct X as [X p], Y as [Y q].
  refine (equiv_path_sigma _ _ _ oE _); unfold ".1", ".2".
  unfold pretensor_baut1', comp, O_cover, hfiber, ".1", ".2".
  snapply equiv_functor_sigma_id.
  intro e; destruct e.
  unfold transport.
  snrefine (_ oE equiv_moveR_equiv_M _ _); cbn.
  refine (equiv_path_inverse _ _ oE _).
  apply equiv_moveR_1M.
Defined.

Definition pequiv_pretensor_path_baut1' `{Univalence} {A : Type} (X : BAut1 A)
  : [pretensor_baut1' X X, pt] <~>* [X = X, idpath].
Proof.
  symmetry.
  srapply Build_pEquiv'.
  1: exact (equiv_pretensor_path_baut1' X X)^-1%equiv.
  apply path_sigma_hprop; cbn.
  reflexivity.
Defined.

Definition equiv_pretensor_path_baut1 `{Univalence} (A : Type) (X Y : BAut1 A)
  : pretensor_baut1 X Y <~> (X = Y)
  := equiv_pretensor_path_baut1' _ _ oE equiv_pretensor_pretensor' _ _.

Definition pequiv_pretensor_path_baut1 `{Univalence} {A : Type} (X : BAut1 A)
  : [pretensor_baut1 X X, _] <~>* [X = X, idpath]
  := pequiv_pretensor_path_baut1' X o*E pequiv_pretensor_pretensor' X.

(** The analog of [SelfMaps.ev1'] for a general band. *)
Definition ev_band `{Univalence} `{A : pType@{u}} (X : BAut1@{u v} A)
  : pretensor_baut1@{u v w} pt X -> X.1
  := fun p => p.1 pt.

(** This goal often comes up, so we record it as a lemma. *)
Definition transport_idmap_pretensor_path_baut1 `{Univalence} {A : pType}
  (X Y : BAut1 A) (p : pretensor_baut1 X Y)
  : transport idmap (equiv_pretensor_path_baut1 A X Y p)..1 == p.1
  := ap10_equiv (ap pr1 (eissect (equiv_pretensor_path_baut1 A X Y) p)).


(** We often need to do path induction on the equality [tr X = tr A].  The next few lemmas record this idiom and a computation rule. *)

(** We start with a result for any truncation level, as we make use of this with [n := -1] for [pcomp] and with [n := 0] for [BAut1].  We don't generalize all the way to any reflective subuniverse, since for [Tr n] we can eliminate into any universe. *)
Definition pcover_trunc_induction@{u u0 v | u < v} `{Univalence} {n : trunc_index}
  {T : Type@{u}} {t : T}
  (P : O_pcover@{u} (Tr n.+1) T t -> Type@{u0}) `{forall X, IsTrunc n (P X)}
  (Ppt : P pt)
  : forall (X : O_pcover _ T t), P X.
Proof.
  intros [X p]; revert p.
  refine (equiv_ind (equiv_path_Tr _ _) _ _).
  rapply Trunc_ind.
  revert X; rapply paths_ind_r.
  exact Ppt.
Defined.

(** This version uses induction a second time to reduce the [IsTrunc] hypothesis to the base point. We need to increase [n] by [1] for this. *)
Definition pcover_trunc_induction'@{u u0 v | u < v} `{Univalence} {n : trunc_index}
  {T : Type@{u}} {t : T}
  (P : O_pcover@{u} (Tr n.+2) T t -> Type@{u0}) `{IsTrunc n.+1 (P pt)}
  (Ppt : P pt)
  : forall (X : O_pcover _ T t), P X.
Proof.
  refine (pcover_trunc_induction P Ppt).
  rapply pcover_trunc_induction.
  2: assumption.
  intro X.
  refine (@istrunc_leq (-1) n.+1 tt _ _).
Defined.

Definition pcover_trunc_induction_comp@{u u0 v | u < v} `{Univalence} {n : trunc_index}
  {T : Type@{u}} {t : T}
  (P : O_pcover@{u} (Tr n.+1) T t -> Type@{u0}) `{forall X, IsTrunc n (P X)}
  (Ppt : P pt)
  : pcover_trunc_induction@{u u0 v} P Ppt pt = Ppt.
Proof.
  unfold pcover_trunc_induction.
  exact (equiv_ind_comp _ _ (tr idpath)).
Defined.

(** A version with the sigma type unpacked. *)
Definition pcover_trunc_induction_curried `{Univalence} {n : trunc_index} {T : Type} {t : T}
  (P : forall (X : T) (p : tr (n:=n.+1) X = tr t), Type) `{forall X p, IsTrunc n (P X p)}
  (Ppt : P t idpath)
  : forall (X : T) (p : tr X = tr t), P X p.
Proof.
  intros X p; exact (pcover_trunc_induction (fun X => P X.1 X.2) Ppt (X;p)).
Defined.

(** While the above lemmas apply to bands as well, they leave goals that look awkward, so we specialize to the case of banded types.  Since [n:=-1] for this case, we only give the version that does induction twice. *)
Definition band_induction `{Univalence} {A : Type}
  (P : BAut1 A -> Type) `{IsTrunc 0 (P pt)}
  (Ppt : P pt)
  : forall (X : BAut1 A), P X
  := pcover_trunc_induction' P Ppt.

(** A version with the sigma type unpacked. *)
Definition band_induction_curried `{Univalence} {A : Type}
  (P : forall X (p : tr (n:=1) X = tr A), Type) `{IsTrunc 0 (P A idpath)}
  (Ppt : P A idpath)
  : forall X (p : tr X = tr A), P X p.
Proof.
  intros X p; exact (band_induction (fun X => P X.1 X.2) Ppt (X;p)).
Defined.

(** Various results related to [BCM:lem:pmap.conn.BAut1] in tangent2.tex. *)

(** If two pointed maps [f] and [g] from a connected type [B] to [BAut1 A] are pointed homotopic after forgetting the orientations (i.e. as maps into the universe pointed at [A]), then they are pointed homotopic as maps into [BAut1 A].  I'm fairly sure that the assumption that [B] is connected is needed, as is the assumption that the given homotopy is pointed.  Note that this is stronger than the universal property of the 1-connected cover, since [B] is only 0-connected.  If all you need is an unpointed homotopy, see [map_conn_BAut1] below. *)
(* [BCM:lem:pmap.conn.BAut1] *)
Definition pmap_conn_BAut1 `{Univalence} {B : pType} `{IsConnected 0 B} {A : Type}
  (f g : B ->* pBAut1 A) (h : pbaut1_pr1 o* f ==* pbaut1_pr1 o* g)
  : f ==* g.
Proof.
  snapply Build_pHomotopy.
  - intro b.
    srapply path_sigma.
    + exact (h b).
    + revert b; rapply (conn_point_elim (-1)).
      by pelim h f g.
  - cbn.
    rewrite conn_point_elim_beta.
    by pelim h f g.
Defined.

(** Put this right after [psigma]. *)
Definition ppr1 {X : pType} {P : pFam X} : psigma P ->* X
  := Build_pMap pr1 idpath.

(** Here we generalize to any family and any truncation level.  This should also follow from [istrunc_extension_along_conn], but you have to juggle things to put it into that form, using [equiv_extension_along_pforall] and taking [P] to be the family of lifts-up-to-homotopy of [pbaut1_pr1 o* f]. *)
Definition pmap_conn_trunc_family `{Univalence} (n : trunc_index) {A X : pType} `{IsConnected n.+1 A}
  (P : pFam X) `{forall X, IsTrunc n.+1 (P X)}
  (f g : A ->* psigma P) (h : ppr1 o* f ==* ppr1 o* g)
  : f ==* g.
Proof.
  snapply Build_pHomotopy.
  - intro b.
    srapply path_sigma.
    + exact (h b).
    + revert b; rapply (conn_point_elim n).
      by pelim h f g.
  - cbn.
    rewrite conn_point_elim_beta.
    by pelim h f g.
Defined.

(** Our original statement follows from the generalized version. We need to tell Coq the pointed family whose [psigma] is [pBAut1]. *)
Definition pfam_baut1 (A : Type@{u}) : pFam [Type@{u}, A].
Proof.
  snapply Build_pFam.
  - exact (fun X => @tr 1 _ X = @tr 1 _ A).
  - cbn. exact idpath.
Defined.

Definition pmap_conn_BAut1' `{Univalence} {B : pType} `{IsConnected 0 B} {A : Type}
  (f g : B ->* pBAut1 A) (h : pbaut1_pr1 o* f ==* pbaut1_pr1 o* g)
  : f ==* g
  := pmap_conn_trunc_family (-1) (pfam_baut1 A) f g h.

(** A version for any (n+1)-truncated map. It has one extra step in each case because [pr] isn't strictly pointed; this can also be dealt with by starting the proof with [pointed_reduce_pmap pr]. *)
Definition pmap_conn_truncmap `{Univalence} (n : trunc_index) {A X Y : pType} `{IsConnected n.+1 A}
  (pr : X ->* Y) `{!IsTruncMap n.+1 pr}
  (f g : A ->* X) (h : pr o* f ==* pr o* g)
  : f ==* g.
Proof.
  snapply Build_pHomotopy.
  - intro b.
    (* We prove [f b = g b] by proving an equality in a fiber. *)
    refine (ap pr1 (_ : (f b; h b) = (g b; idpath) :> hfiber pr (pr (g b)))).
    (* This helps because the fibers are truncated, allowing us to reduce to the base point. *)
    revert b; rapply (conn_point_elim n).
    pelim h f g.
    by destruct (point_eq pr).
  - cbn.
    rewrite conn_point_elim_beta.
    pelim h f g.
    by destruct (point_eq pr).
Defined.

(** Our original statement also follows from the second generalization. *)
Definition pmap_conn_BAut1'' `{Univalence} {B : pType} `{IsConnected 0 B} {A : Type}
  (f g : B ->* pBAut1 A) (h : pbaut1_pr1 o* f ==* pbaut1_pr1 o* g)
  : f ==* g
  := pmap_conn_truncmap (-1) pbaut1_pr1 f g h.

(** If all you need is an unpointed homotopy, then you can actually do slightly better than requiring that [h] be a pointed homotopy.  It's enough to assume that [h pt] respects the banding.  This extra condition, [hpt], lies in a proposition that is equivalent to the propositional truncation of the pointedness of [h] (when [f] and [g] are pointed). *)
(** Note: since [BAut1 A] is a connected H-space when [A] is *central*, in this case we in fact get [f ==* g] from this weaker hypothesis! *)
Definition map_conn_BAut1 `{Univalence} {B : pType} `{IsConnected 0 B} {A : Type}
  (f g : B -> pBAut1 A) (h : baut1_pr1 o f == baut1_pr1 o g)
  (hpt : (f pt).2 = ap tr (h pt) @ (g pt).2)
  : f == g.
Proof.
  intro b.
  srapply path_sigma.
  - exact (h b).
  - revert b; rapply (conn_point_elim (-1)).
    lhs napply transport_paths_Fl.
    apply moveR_Vp.
    exact hpt.
Defined.

Definition BAut1_ptd (A : pType) := { X : pType & Tr 0 (X <~>* A) }.

Definition path_BAut1_ptd `{Univalence} (A : pType) (X : BAut1_ptd A)
  : ((A; tr pequiv_pmap_idmap) = X) <~> { e : A <~>* X.1 & tr e^-1* = X.2 }.
Proof.
  refine (_ oE (equiv_path_sigma _ _ _)^-1%equiv).
  unfold ".1", ".2".
  snapply equiv_functor_sigma'.
  1: symmetry; apply equiv_path_ptype.
  destruct X as [X omega].
  intro p.
  apply equiv_concat_l; clear omega.
  revert A p; napply paths_ind_r.
  simpl.
  apply ap.
  (* This is almost definitionally true, except that the LHS uses adjointification. *)
  apply equiv_path_pequiv'; cbn.
  reflexivity.
Defined.

(* TODO: This needs cleaning up.  It's not clear how much the previous lemma helps. *)
(* Really, it should be clear.  Under the IsHSet hypothesis, the 1-truncation map induces an equivalence on the components, so its fiber is contractible.  Abstract this to BAut1 of a general type, not just Type or pType. This special case is used in the proof of [BCM:lem:thom.iso.lemma]. *)
Definition contr_BAut1_ptd `{Univalence}
  {A : pType} `{IsHSet (A <~>* A)}
  : Contr (BAut1_ptd A).
Proof.
  snapply Build_Contr.
  1: exact (A; tr pequiv_pmap_idmap).
  intro X.
  apply (path_BAut1_ptd A X)^-1.
  destruct X as [X omega]; cbn.
  revert omega; napply Trunc_ind; intro omega.
  - rapply istrunc_sigma.
    strip_truncations.
    rapply (istrunc_equiv_istrunc (A <~>* A)).
    exact (equiv_postcompose_core_cat_equiv omega^-1* ).
  - exists omega^-1*.
    apply ap.
    revert omega.
    rapply (equiv_ind (equiv_path_ptype _ _)^-1%equiv).
    revert X; napply paths_ind_r.
    simpl.
    (* This is almost definitionally true, except that the LHS uses adjointification. *)
    apply equiv_path_pequiv'; cbn.
    reflexivity.
Defined.

Local Instance islocally_small_baut1@{u v w | u < v, v < w} `{Univalence} (A : pType@{u})
  : IsLocallySmall@{u v v} 1 (pBAut1@{u v} A).
Proof.
  intros X Y; cbn.
  exists (pretensor_baut1 X Y).
  exact (equiv_pretensor_path_baut1@{u v w} A X Y).
Defined.

Instance issmall_baut1@{u v w | u < v, v < w} `{Univalence} (A : pType@{u})
  : IsSmall@{u v} (pBAut1@{u v} A)
  := issmall_pointed_connected_islocallysmall _ _.

(** A pointed version of smallness. *)
Definition issmall_pbaut1@{u v w | u < v, v < w} `{Univalence} (A : pType@{u})
  : { BA : pType@{u} & BA <~>* pBAut1@{u v} A }
  := (_; pequiv_from_pointed_codomain (equiv_smalltype (pBAut1@{u v} A))).

(** We break it up to make it easier to use. *)
Definition spBAut1@{u v w | u < v, v < w} `{Univalence} (A : pType@{u})
  : pType@{u}
  := (issmall_pbaut1 A).1.

Definition pequiv_spbaut1_pbaut1@{u v w | u < v, v < w} `{Univalence} (A : pType@{u})
  : spBAut1@{u v w} A <~>* pBAut1@{u v} A
  := (issmall_pbaut1 A).2.

