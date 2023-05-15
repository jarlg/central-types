From HoTT Require Import Basics Types EquivGroupoids Pointed HFiber Truncations
  Homotopy.HSpace Homotopy.Cover Homotopy.EvaluationFibration.
Require Import Lemmas HSpace SelfMaps Cover.

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

Global Instance ispointed_baut1 {A : Type} : IsPointed (BAut1 A)
    := (A; idpath).

Definition pBAut1@{u v | u < v} (A : Type@{u}) : pType@{v}
    := [BAut1@{u v} A, _].

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
  snrapply equiv_functor_sigma'.
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
  snrapply equiv_functor_sigma_id.
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


(** We often need to do path induction on the equality [tr X = tr A].  The next three lemmas record this idiom and a computation rule. *)
Definition band_induction@{u u0 v | u < v} `{Univalence} {n : trunc_index}
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

Definition band_induction_comp@{u u0 v | u < v} `{Univalence} {n : trunc_index}
  {T : Type@{u}} {t : T}
  (P : O_pcover@{u} (Tr n.+1) T t -> Type@{u0}) `{forall X, IsTrunc n (P X)}
  (Ppt : P pt)
  : band_induction@{u u0 v} P Ppt pt = Ppt.
Proof.
  unfold band_induction.
  exact (equiv_ind_comp _ _ (tr idpath)).
Defined.

Definition band_induction' `{Univalence} {n : trunc_index} {T : Type} {t : T}
  (P : forall (X : T) (p : tr (n:=n.+1) X = tr t), Type) `{forall X p, IsTrunc n (P X p)}
  (Ppt : P t idpath)
  : forall (X : T) (p : tr X = tr t), P X p.
Proof.
  intros X p; exact (band_induction (fun X => P X.1 X.2) Ppt (X;p)).
Defined.


Section Central.

  (** We now assume that [A] is a central type and define an H-space structure on [BAut1 A], as in Theorem 4.19. *)

  (* TODO: use `{Central A} here, which will mean reordering some things. *)
  Universes u v.
  Context `{Univalence} {A : pType@{u}} `{IsEquiv _ _ (ev1'@{u} A)}.

  Local Definition pequiv_ev1'
    : pcomp (A <~> A) equiv_idmap <~>* A
    := Build_pEquiv _ _ (ev1' A) _.

  (** Under the hypotheses of this section, [ev_band] is an equivalence. *)
  Local Instance isequiv_ev_band@{w}
    : forall X : BAut1@{u v} A, IsEquiv (ev_band@{u v w} X).
  Proof.
    by rapply band_induction@{v v w}.
  Defined.

  Local Definition equiv_ev_band@{w}
    : forall X, pretensor_baut1@{u v w} pt X <~> X.1
    := fun X => Build_Equiv _ _ (ev_band@{u v w} X) (isequiv_ev_band@{w} X).

  Definition equiv_ev_band'@{w} (Xp : BAut1 A)
    : (pt = Xp) <~> Xp.1
    := equiv_ev_band Xp oE (equiv_pretensor_path_baut1@{u v w} _ _ _)^-1.

  Definition equal_ev_band
    : forall X, pretensor_baut1 pt X = X.1
    := fun X => path_universe_uncurried@{u u v} (equiv_ev_band X).

  (** Consequently, any pointed tensor is trivial. *)
  Definition pointed_tensor_trivial@{w} (Xp : BAut1@{u v} A)
    : Xp.1 -> (pt = Xp) := (equiv_ev_band'@{w} Xp)^-1.

  Definition pointed_tensor_trivial_comp@{w} {Xp : BAut1@{u v} A}
    : forall x, equiv_ev_band@{w} Xp
             ((equiv_pretensor_path_baut1 _ _ _)^-1
                (pointed_tensor_trivial Xp x)) = x.
  Proof.
    intro x.
    refine (ap (equiv_ev_band Xp) _ @ _).
    1: exact (eissect (equiv_pretensor_path_baut1 _ _ _) _).
    apply eisretr.
  Defined.

  (** The ("untwisted") tensor operation on bands. *)
  Proposition tensor_baut1
    : BAut1@{u v} A -> BAut1@{u v} A -> BAut1@{u v} A.
  Proof.
    intros X Y.
    exists (pretensor_baut1 X Y).
    revert Y X.
    do 2 rapply band_induction.
    exact (ap tr@{v} (equal_ev_band pt)).
  Defined.

  Definition ap_tensor_baut1_pt_right {X Y : BAut1 A} (p : X = Y)
    : (tensor_baut1 X pt).1 = (tensor_baut1 Y pt).1 :> Type@{u}.
  Proof.
    (** It works to do [destruct p; reflexivity.], but later we need the proof to compute like below. *)
    rapply path_universe_uncurried@{u u v}.
    snrapply equiv_functor_sigma'.
    1: exact (equiv_precompose_equiv' ((equiv_path@{u v} _ _) (ap baut1_pr1 p^))).
    intro e; lazy beta.
    induction p.
    rapply equiv_concat_l.
    apply (ap tr).
    apply path_equiv.
    by apply path_arrow.
  Defined.

  Definition ap_pr1_ap_tensor_baut1_pt_right {X Y : BAut1 A} (p : X = Y)
    : ap pr1 (ap (fun x : BAut1 A => tensor_baut1 x pt) p)
      = ap_tensor_baut1_pt_right p.
  Proof.
    destruct p; cbn.
    refine (path_universe_1^ @ _).
    refine (ap path_universe_uncurried _).
    apply path_equiv.
    funext b.
    rapply path_sigma_hprop.
    by apply path_equiv.
  Defined.

  Definition pr2_tensor_baut1
    : forall X, (tensor_baut1 pt X).2 =
             ap tr@{v} (equal_ev_band X) @ X.2.
  Proof.
    rapply band_induction.
    refine (_ @ (concat_p1 _)^).
    unfold tensor_baut1, ".2".
    refine (apD10 _ pt @ _); rapply band_induction_comp.
  Defined.

  (** The point is a left unit for tensoring. *)
  Theorem tensor_unit_l
    : forall X, tensor_baut1 pt X = X.
  Proof.
    intros [X p].
    srapply path_sigma.
    1: rapply equal_ev_band.
    refine (transport_paths_Fl _ _ @ _).
    apply moveR_Vp.
    apply pr2_tensor_baut1.
  Defined.

  (** It turns out that [pt] is not a right unit for [tensor_baut1]. To understand this we need the notion of twisting. *)

  (** ** Twisting bands *)

  (** There's an equivalence between the underlying types when flipping the order of tensoring. (This will not in general be an equivalence of the tensors, however.) *)
  Definition baut1_symm (X Y : BAut1@{u v} A)
    : pretensor_baut1 X Y <~> pretensor_baut1 Y X.
  Proof.
    destruct X as [X p], Y as [Y q].
    refine (_ oE equiv_functor_O_cover_from_point (equiv_equiv_inverse _ _) _).
    apply O_cover_change_center.
    revert X p; rapply band_induction'.
    revert Y q; rapply band_induction'.
    reflexivity.
  Defined.

  Definition baut1_symm1
    : [pretensor_baut1 (A:=A) pt pt, _] <~>* [pretensor_baut1 (A:=A) pt pt, _].
  Proof.
    srapply Build_pEquiv'.
    1: apply baut1_symm.
    srapply path_sigma_hprop.
    reflexivity.
  Defined.

  (** Symmetry corresponds to path inversion. *)
  Definition baut1_symm_comp {X Y : BAut1 A} (p : X = Y)
    : (equiv_pretensor_path_baut1 _ _ _)^-1 p^
      = baut1_symm _ _ ((equiv_pretensor_path_baut1 _ _ _)^-1 p).
  Proof.
    induction p.
    by apply path_sigma_hprop.
  Defined.

  Lemma baut1_symm_involutive (X Y : BAut1 A)
    : baut1_symm Y X o baut1_symm X Y == idmap.
  Proof.
    intros [p r].
    srapply path_sigma_hprop; cbn.
    apply path_equiv; cbn.
    reflexivity.
  Defined.

  (** *** The negation operation *)

  (** [baut1_symm1] is a self-equivalence of [A] tensored with itself, and thus we get a self-equivalence [neg] of [A] (short for negation). We define it in two steps to get rid of one universe variable. *)
  Local Definition neg' : A <~>* A
    := pequiv_ev1' o*E baut1_symm1 o*E pequiv_ev1'^-1*.
  Definition neg@{w} := Eval unfold neg' in neg'@{v w}.

  (** This causes [cbn] to be faster in some situations. *)
  Arguments neg : simpl never.

  Definition neg_involutive : neg o neg == idmap.
  Proof.
    intro a.
    pose (b := (pequiv_ev1')^-1 (neg a)).
    nrefine (ap (ev1' A o baut1_symm1) (x:=b) _ @ _).
    1: nrapply (eissect (pequiv_ev1')).
    nrefine (ap pequiv_ev1' _ @ _).
    1: rapply (baut1_symm_involutive pt pt).
    nrapply eisretr.
  Defined.

  (** The negation map lets us move between path components of [(A <~> A)]. *)
  Definition neg_precompose
    : pcomp (A <~> A) 1%equiv <~>* pcomp (A <~> A) neg.
  Proof.
    srapply (pequiv_pfunctor_pcomp@{u v}
               (X:=[A<~>A, equiv_idmap]) (Y:=[A<~>A, neg])).
    srapply Build_pEquiv'.
    1: exact (equiv_precompose_equiv' neg).
    by apply path_equiv.
  Defined.

  (** Thus we get an equivalence [pcomp (A<~>A) negation <~> A]. *)
  Definition equiv_ev_neg : pcomp (A<~>A) neg <~>* A
    := pequiv_ev1' o*E neg_precompose^-1*.

  (** [equiv_ev_neg] is homotopic to evaluation at the point. *)
  Lemma equiv_ev_neg_homotopic : equiv_ev_neg == (fun f => f.1 pt).
  Proof.
    intro f.
    apply (ap f.1).
    apply point_eq.
  Defined.

  (** Inversion of auto-equivalences in the component of [equiv_idmap]. *)
  Definition comp_idmap_inv : pcomp (A <~> A) equiv_idmap -> pcomp (A <~> A) equiv_idmap.
  Proof.
    srapply functor_sigma.
    1: apply equiv_inverse.
    simpl.
    rapply band_induction'.
    apply (ap tr).
    by apply path_equiv.
  Defined.

  (** Inversion of auto-equivalences in the component of [neg]. *)
  Definition comp_neg_inv : pcomp (A <~> A) neg -> pcomp (A <~> A) neg.
  Proof.
    srapply functor_sigma.
    1: apply equiv_inverse.
    simpl.
    rapply band_induction'@{u u v}.
    apply (ap tr).
    by apply path_equiv.
    (* [neg^-1] and [neg] are definitionally equal as functions! *)
  Defined.

  (** Perhaps surprisingly, inversion of paths in the component of [neg] is homotopic to the identity. *)
  Definition comp_neg_inv_idmap : comp_neg_inv == idmap.
  Proof.
    rapply (equiv_ind equiv_ev_neg^-1%equiv);
      intro a.
    apply (equiv_ap' equiv_ev_neg _ _)^-1.
    refine (_ @ (eisretr _ _)^).
    refine (equiv_ev_neg_homotopic _ @ _).
    apply moveR_equiv_V; symmetry.
    rapply eisretr. (* the LHS is [neg(a) * a] *)
  Defined.

  (** It follows that [f.1 pt = f.1^-1 pt] for [f : pcomp (A <~> A) neg]. *)
  Lemma comp_neg_inv_ev_pt
    : forall f : pcomp (A <~> A) neg, f.1^-1 pt = f.1 pt.
  Proof.
    intros f; cbn.
    pose (q := ap equiv_ev_neg@{_ v} (comp_neg_inv_idmap f)).
    refine (_ @ q @ equiv_ev_neg_homotopic f).
    refine (ap (f.1)^-1 _).
    apply moveL_equiv_V.
    apply point_eq.
  Defined.

  Lemma comp_idmap_neg_inv_ev_pt (f : pcomp (A<~>A) equiv_idmap)
    : neg (f.1^-1 pt) = f.1 pt.
  Proof.
    unfold neg; cbn.
    change (f.1^-1 pt) with (ev1' A (comp_idmap_inv@{v} f)).
    rewrite eissect.
    reflexivity.
  Defined.

  (** *** The twisting operation *)

  (** Negation induces a 'twisting' operation on bands. *)
  Definition twist_baut1 : BAut1@{u v} A -> BAut1@{u v} A
    := fun X => (X.1; X.2 @ ap tr (path_universe_uncurried@{u u v} neg)).

  Local Notation "X ^T" := (twist_baut1 X) (at level 5).

  (** This goal comes up twice below, so we make a lemma for it. *)
  Lemma ap_tr_path_universe_neg_neg {n : trunc_index}
    : idpath = ap@{v v} (tr (n:=n)) (path_universe_uncurried neg)
                 @ ap tr (path_universe_uncurried neg).
  Proof.
    apply ap_path_universe_invol.
    symmetry; exact neg_involutive.
  Defined.

  (** The point twists to itself (but a general band does not). *)
  Definition twist_baut1_1 : pt = pt^T.
  Proof.
    snrapply path_hfiber.
    1: exact (path_universe_uncurried neg).
    nrefine (_ @ ap _ (concat_1p _)^).
    exact ap_tr_path_universe_neg_neg.
  Defined.

  Definition twist_involutive : forall X, (X^T)^T = X.
  Proof.
    intros [X p].
    snrapply path_hfiber.
    1: exact idpath.
    revert X p; rapply band_induction'.
    refine (_ @ (concat_1p _)^).
    unfold twist_baut1, pr2.
    refine (whiskerR (concat_1p _) _ @ _).
    exact ap_tr_path_universe_neg_neg^.
  Defined.

  (** Tensoring with the point on the right twists the left factor. *)
  Theorem tensor_twist_r
    : forall X, tensor_baut1 X pt = X^T.
  Proof.
    intros [X p].
    snrapply path_hfiber.
    1: exact (path_universe_uncurried (equiv_ev_band (X;p) oE baut1_symm _ _)).
    revert X p; rapply band_induction'.
    refine (_ @ ap _ (concat_1p _)^).
    refine (pr2_tensor_baut1 _ @ _).
    refine (concat_p1 _ @ _).
    apply ap_path_universe_compose.
    intro b.
    cbn; unfold ev_band; symmetry.
    apply comp_idmap_neg_inv_ev_pt.
  Defined.

  (** TODO: maybe we should remove "twisted" everywhere?  The tensor *is* the twisted version of the operation defined earlier, so it could be called something different. *)
  Definition twisted_tensor_baut1
    := fun X Y => tensor_baut1 X^T Y.

  (** It follows that we get an H-space structure by first twisting the left factor. *)
  Local Instance hspace_twisted_baut1 : IsHSpace (pBAut1 A).
  Proof.
    snrapply Build_IsHSpace.
    - exact twisted_tensor_baut1.
    - intro X.
      refine (ap (fun x => tensor_baut1 x X) twist_baut1_1^ @ _).
      apply tensor_unit_l.
    - intro X.
      refine (tensor_twist_r _ @ _).
      apply twist_involutive.
  Defined.

  (** *** Coherence *)

  (** We show that [hspace_twisted_baut1] is a coherent H-space structure. *)

  (** The underlying type of [twisted_tensor_baut1 pt pt] is [pcomp (A<~>A) neg]. *)
  Definition twisted_hspace_op_pt_pt
    : (hspace_op (X:=pBAut1 A) pt pt).1 <~> pcomp (A<~>A) neg.
  Proof.
    apply O_cover_change_center.
    refine (ap _ _ (y:=tr (path_universe_uncurried neg)) @ _).
    { rapply moveR_equiv_V.
      exact (concat_p1 _ @ concat_1p _). }
    apply (ap tr).
    rapply eisretr.
  Defined.

  (** This speeds up uses of [ap_pr1_path_sigma] below. *)
  Definition ap_pr1_path_hfiber {X Y : Type} {f : X -> Y} {y : Y}
    {x0 x1 : hfiber f y} (p : x0.1 = x1.1) (q : x0.2 = ap f p @ x1.2)
    : ap pr1 (path_hfiber p q) = p
    := ap_pr1_path_sigma _ _.

  Definition iscoherent_hspace_twisted_baut1
    : @IsCoherent (pBAut1 A) hspace_twisted_baut1.
  Proof.
    unfold IsCoherent.
    srapply equiv_path_path_sigma_hprop.
    unfold "..1".
    (* Each of the identity laws is defined as a composite of two paths. *)
    refine (ap_pp _ _ _ @ _ @ (ap_pp _ _ _)^).
    (* The two on the RHS can be simplified with [ap_pr1_path_hfiber]. *)
    refine (_ @ (_ @@ _)).
    2,3: exact (ap_pr1_path_hfiber _ _)^.
    refine (_ @ (concat_p1 _)^).
    (* One on the LHS can be simplified in the same way, while the other uses [ap_pr1_ap_tensor_baut1_pt_right]. *)
    refine ((_ @@ (ap_pr1_path_hfiber _ _)) @ _).
    1: apply ap_pr1_ap_tensor_baut1_pt_right.
    (* The next three lines reduce the goal to a question about two maps being homotopic. *)
    refine ((path_universe_compose_uncurried _ _)^ @ _).
    apply (ap path_universe_uncurried).
    apply path_equiv, path_arrow.
    rapply (equiv_ind twisted_hspace_op_pt_pt^-1%equiv); intro p.
    (* The RHS is definitionally [p.1^-1 pt], which we change to [p.1 pt]: *)
    refine (_ @ (comp_neg_inv_ev_pt _)^).
    (* The LHS is definitionally of the form [p.1 (something)], allowing us to do: *)
    refine (ap p.1 _).
    (* We can further replace the RHS with [neg pt]: *)
    refine (_ @ point_eq neg).
    apply ap10.
    rewrite inv_V.
    unfold equiv_path, equiv_fun.
    refine (ap _ (ap_pr1_path_sigma _ _) @ _); unfold ".1".
    apply transport_idmap_path_universe_uncurried.
  Defined.

End Central.
