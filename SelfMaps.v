From HoTT Require Import Basics Types Truncations Pointed
  Homotopy.HSpace Homotopy.Cover Homotopy.EvaluationFibration
  Tactics.EvalIn Modalities.ReflectiveSubuniverse.

Require Import Lemmas Cover.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.


(* TODO: I wonder about defining this to be [ev1 A o* pmap_comp_equiv_map pequiv_pmap_idmap], where the latter is the underlying pointed map of [pequiv_comp_equiv_map pequiv_pmap_idmap].  This is what comes up in isequiv_ev1'. *)
Definition ev1' (A : pType)
  : pcomp (A <~> A) equiv_idmap ->* A.
Proof.
  refine (ev _ o* _ o* pfib _); cbn.
  srapply Build_pMap.
  1: exact equiv_fun.
  reflexivity.
Defined.

(** If [ev1] is an equivalence we get an induced coherent H-space structure. Note that it follows from this assumption that [A] is connected. *)
Definition induced_cohhspace_equiv_ev1 `{Funext} (A : pType)
  `{E : IsEquiv _ _ (ev1 A)} : IsCohHSpace A.
Proof.
  apply (equiv_iscohhspace_psect A)^-1.
  pose (pev := Build_pEquiv _ _ (ev1 A) E).
  exists (pfib _ o* pev^-1*).
  refine ((pmap_compose_assoc _ _ _)^* @* _).
  exact (peisretr pev).
Defined.

(** We can restrict to the component of [idmap]. *)
Definition pequiv_pcomp_endo_pendo_hspace `{Funext} {A : pType}
  `{IsCoherent A} `{forall a:A, IsEquiv (hspace_op a)}
  : pcomp (selfmaps A) idmap <~>*
      pcomp ((A ->* A) * A) (pmap_idmap, pt)
  := pequiv_pfunctor_O_pcover pequiv_map_pmap_hspace^-1*.

Definition pequiv_pcomp_endo_pendo_hspace' `{Funext} {A : pType}
  `{IsCoherent A} `{forall a:A, IsEquiv (hspace_op a)}
  : pcomp (selfmaps A) idmap <~>*
      [pcomp (A ->* A) pmap_idmap * pcomp A pt, _]
  := O_pcover_prod (X:=[A ->* A, pmap_idmap])
       o*E pequiv_pfunctor_O_pcover pequiv_map_pmap_hspace^-1*.

Definition psnd' {A B : pType} : pcomp (A * B) (pt, pt) ->* pcomp B pt.
Proof.
  snrapply functor_pfiber.
  - exact psnd.
  - snrapply Build_pMap.
    + exact (Trunc_functor _ snd).
    + reflexivity.
  - snrapply Build_pHomotopy; easy.
Defined.

(** Lemma 3.5 *)
Definition equiv_hfiber_ev1 `{Univalence} {A : pType} `{IsHSpace A}
  : hfiber (ev1 A) pt <~> pcomp (A ->* A) pmap_idmap.
Proof.
  transitivity { fp : { f : A -> A & f pt = pt } & tr (n:=0) fp.1 = tr idmap }.
  1: make_equiv.
  unfold pcomp, O_pcover, pfiber, hfiber; cbn.
  srapply (equiv_functor_sigma' (issig_pmap _ _)); cbn.
  intro f.
  refine (equiv_path_Tr _ _ oE _ oE (equiv_path_Tr _ _)^-1).
  apply equiv_iff_hprop.
  - apply Trunc_functor.
    intro K.
    by apply hspace_path_pforall_from_path_arrow.
  - apply Trunc_functor.
    exact (ap pointed_fun).
Defined.

(** We can restrict the equivalences above to automorphisms. *)

Definition equiv_pauto_hspace `{Funext} {A : pType} (a : A)
  `{IsHSpace A} `{!IsEquiv (hspace_op a)}
  : (A <~>* [A,a]) <~> (A <~>* A).
Proof.
  equiv_conjugate issig_pequiv.
  srapply (equiv_functor_sigma' (equiv_pmap_hspace a)^-1).
  intro f; cbn.
  rapply equiv_isequiv_cancelL.
Defined.

Theorem equiv_auto_pauto_hspace `{Funext} {A : pType}
  `{IsHSpace A} `{forall a:A, IsEquiv (hspace_op a)}
  : (A <~> A) <~> (A <~>* A) * A.
Proof.
  etransitivity {fa : (A ->* A) * A & IsEquiv (fst fa)}.
  2: make_equiv.
  refine (_ oE (issig_equiv _ _)^-1%equiv).
  srapply (equiv_functor_sigma' equiv_map_pmap_hspace^-1).
  intro f; cbn.
  rapply equiv_isequiv_cancelL.
Defined.

(** As before, if the H-space is coherent then we get a pointed equivalence. *)
Theorem pequiv_auto_pauto_hspace `{Funext} {A : pType}
  `{IsHSpace A} `{forall a:A, IsEquiv (hspace_op a)}
  : [A <~> A, equiv_idmap] <~>* [(A <~>* A) * A, (pequiv_pmap_idmap, pt)].
Proof.
  srapply Build_pEquiv'.
  1: apply equiv_auto_pauto_hspace.
  cbn.
  apply path_prod'.
  2: reflexivity.
  apply path_pequiv.
  exact (phomotopy_path (ap fst (point_eq pequiv_map_pmap_hspace^-1*))).
Defined.

Definition pcomp_auto_pauto_hspace `{Funext} {A : pType}
  `{IsHSpace A} `{forall a:A, IsEquiv (hspace_op a)}
  : pcomp (A <~> A) (equiv_idmap) <~>*
      pcomp ((A <~>* A) * A) (pequiv_pmap_idmap, pt)
  := pequiv_pfunctor_O_pcover pequiv_auto_pauto_hspace.

Definition pcomp_auto_pauto_hspace' `{Funext} {A : pType}
  `{IsHSpace A} `{forall a:A, IsEquiv (hspace_op a)}
  : pcomp (A <~> A) equiv_idmap <~>*
      [pcomp (A <~>* A) pequiv_pmap_idmap * pcomp A pt, _]
    := O_pcover_prod (X:=[A <~>* A, pequiv_pmap_idmap])
          o*E pcomp_auto_pauto_hspace.
