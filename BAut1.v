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

