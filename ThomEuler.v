From HoTT Require Import Basics Types.Sigma Types.Universe Tactics.EvalIn Pointed
  Algebra.AbGroups.Z Truncations.Core Truncations.Connectedness
  Spaces.Spheres Homotopy.Suspension.

From CentralTypes Require Import BAut1 Central EMSpace Bands KZ.

(** * The Thom class and the Euler class *)

(** TODO: separate out Euler class material? *)

Open Scope pointed_scope.
Open Scope trunc_scope.

(** Maybe this should be done in AbGroups.Z, without the Local annotation? *)
Local Notation ZZ := abgroup_Z.

Local Instance isconnected_Sn_band `{Univalence} (n : nat) (X : BAut1 S^n)
  : IsConnected n.-1 X.
Proof.
  revert X; rapply band_induction; exact _.
Defined.

Local Instance ishset_pmap_Sn_KZn `{Univalence} (n : nat) (X : BAut1 S^n)
  : IsHSet (psusp X ->* KZ n.+1)
  := istrunc_pmap (m:=n.-1) _ _.

Definition thom_class `{Univalence} (n : nat) (X : BAut1 S^n.+1)
  : psusp X ->* KZ n.+2.
Proof.
  revert X; rapply band_induction.
  change (S^n.+2 ->* KZ n.+2).
  exact ptr.
Defined.

(** We give a different proof of [loop_susp_adjoint].  Here's one based on the non-exported one in pSusp.v, but factored into two, and made shorter using [make_equiv_contr_basedpaths]. *)

(** First we go partway. *)
Definition equiv_psusp_rec `{Funext} (A : Type) (B : pType)
  : (psusp A ->* B) <~> { b : B & A -> pt = b }.
Proof.
  refine (_ oE (issig_pmap (psusp A) B)^-1).
  refine (_ oE (equiv_functor_sigma_pb
                  (Q := fun NSm => fst NSm.1 = point B)
                  (equiv_Susp_rec A B))).
  (* make_equiv_contr_basedpaths: succeeds here, but with a proof that computes poorly. *)
  equiv_via { S : B & { Np : { N : B & N = pt } & A -> Np.1 = S }}.
  1: make_equiv.
  napply equiv_functor_sigma_id; intro S.
  (* make_equiv_contr_basedpaths.  Fails on this form of the goal!  Bug?  Maybe it's because it intros [A]?  *)
  exact (equiv_contr_sigma (fun Np : { N : B & N = pt } => A -> Np.1 = S)).
Defined.

(** This is the behaviour we were careful to achieve: *)
Definition equiv_psusp_rec_beta `{Funext} (A : Type) (B : pType) (f : psusp A ->* B)
  : (equiv_psusp_rec A B f).1 = f South
  := 1.
(** One might hope that [(equiv_psusp_rec A B f).2 = fun a => (point_eq f)^ @ ap f (merid a)], but that does not hold definitionally.  TODO: is there an easy proof that also achieves this? *)

(** And now the second half, which we factor out to help us keep the goal small later. *)
Definition issig_pmap_loops (A B : pType)
  : { b : B & A -> pt = b } <~> (A ->* loops B).
Proof.
  transitivity {bp : {b:B & point B = b} & {f : A -> point B = bp.1 & f (point A) = bp.2} }.
  1: make_equiv_contr_basedpaths.
  make_equiv_contr_basedpaths.
Defined.

Definition issig_pmap_loops_inv_beta (A B : pType) (f : A ->* loops B)
  : (issig_pmap_loops A B)^-1 f = (pt; pointed_fun f)
  := 1.

(** Here's the custom version of [loop_susp_adjoint], with free universe variables. *)
Definition loop_susp_adjoint' `{Funext} (A B : pType)
  : (psusp A ->* B) <~> (A ->* loops B)
  := issig_pmap_loops A B oE equiv_psusp_rec A B.

Local Instance istrunc_BAut1_KZ `{Univalence} (n : nat)
  : IsTrunc n.+2 (BAut1 (KZ n.+1))
  := istrunc_baut1 _ n.+1.

Local Instance ishset_pmap_Sn_pBAut1_KZn `{Univalence} (n : nat) (X : BAut1@{u v} S^n.+1)
  : IsHSet (psusp@{u} X ->* (pBAut1@{u' v'} (KZ@{u'} n.+1))).
Proof.
  rapply (istrunc_pmap (m:=n)).
  napply isconnected_susp.
  apply (isconnected_Sn_band (n.+1)).
Defined.

Definition generator_loops_BAut1_KZ `{Univalence} (n : nat)
  : S^n.+1 ->* loops (pBAut1 (KZ n.+1)).
Proof.
  nrefine (_ o* (ptr : S^n.+1 ->* KZ n.+1)).
  exact pequiv_loops_baut1^-1*.
Defined.
(* Note that as an unpointed equivalence, [pequiv_loops_baut1] is equal to [equiv_ev_band' pt] which is used below. We can't use one in both places, since we need a pointed equivalence here and one that works for all bands later. *)

(** TODO: verify that this corresponds to [ptr] after composing with the centrality equivalence. *)
Definition generator_BAut1_KZ `{Univalence} (n : nat)
  : S^n.+2 ->* pBAut1 (KZ n.+1).
Proof.
  rapply (loop_susp_adjoint' S^n.+1 _)^-1.
  apply generator_loops_BAut1_KZ.
Defined.

(** A variant, where we model [KZ n.+2] using [BAut1]. I think this corresponds to one of the variants in the current draft. *)
(** TODO: show that after composing with the centrality equivalence, these agree. *)
Definition thom_class_BAut1 `{Univalence} (n : nat) (X : BAut1 S^n.+1)
  : psusp X ->* pBAut1 (KZ n.+1).
Proof.
  revert X; rapply band_induction.
  exact (generator_BAut1_KZ n).
Defined.

Definition thom_class_BAut1_beta `{Univalence} (n : nat)
  : thom_class_BAut1 n pt = generator_BAut1_KZ n
  := pcover_trunc_induction_comp _ _.

(** The general situation involved in defining the Euler class:

                   F
        Type ----------> Type
         |                |
    tr m |                | tr m
         v                v
      ||Type||_m ----> ||Type||_m

    In our case, [m] is [1] and [F] is itself a truncation operation [Tr n.+1].  The proof below works because the square commutes definitionally. *)
Definition tr_path (m : nat) {F : Type -> Type} {X Y : Type} (p : @tr m _ X = @tr m _ Y)
  : @tr m _ (F X) = @tr m _ (F Y)
  := ap (Trunc_functor m F) p.

(** The Euler class *)
(* [BCM:defn:euler.class] *)
Definition euler {n : nat} (X : BAut1 S^n.+1) : BAut1 (KZ n.+1)
  := (Tr n.+1 X.1; tr_path 1 X.2).

(* In all of these "ishset" results, instead of assuming that X is in BAut1 S^n.+1, we could assume that X is n-connected. We could add the ishset version of istrunc_pmap as a local instance. *)
Local Instance ishset_pmap_sigma `{Univalence} (n : nat) (X : BAut1 S^n.+1)
  : IsHSet { K : BAut1 (KZ n.+1) & X -> (pt = K :> pBAut1 (KZ n.+1)) }
  := istrunc_equiv_istrunc _ (equiv_psusp_rec X (pBAut1 (KZ n.+1))).

(** This is another version, landing in a Sigma-type which is equivalent (by [equiv_psusp_rec]) to the type of pointed functions.  We'll show that it agrees with [thom_class_BAut1]. *)
Definition thom_class_sigma `{Univalence} (n : nat) (X : BAut1 S^n.+1)
  : { K : BAut1 (KZ n.+1) & X -> (pt = K :> pBAut1 (KZ n.+1)) }.
Proof.
  (* We define this so that its first component computes to [euler X] without needing to do induction. *)
  exists (euler X).
  (* Our goal is now [X -> pt = euler X]. *)
  refine (_ o tr (n:=n.+1)).
  (* Goal: [Trunc n.+1 X -> pt = euler X], which is definitionally [euler X -> (pt = euler X)]. And this is given by the inverse of the bandedness equivalence, since [euler X] is banded. *)
  exact (equiv_ev_band' (euler X))^-1.
Defined.

Definition thom_class_sigma_beta `{Univalence} (n : nat)
  : thom_class_sigma n pt = (pt; pointed_fun (generator_loops_BAut1_KZ n)).
Proof.
  unfold thom_class_sigma.
  (* The first components are definitionally equal, so we can do: *)
  apply (ap _).
  (* Make the goal easier to read: *)
  set (KZ := point (pBAut1 (KZ n.+1))).
  change ((equiv_ev_band' KZ)^-1 o tr = pequiv_loops_baut1^-1 o tr).
  (* So it's enough to show that the two equivalences being inverted are equal. *)
  tapply (ap (y:=pequiv_loops_baut1) (fun e : KZ = KZ <~> KZ.1 => e^-1 o tr)).
  symmetry; apply pequiv_loops_baut1_equiv_ev_band'.
Defined.

Definition thom_classes_agree `{Univalence} (n : nat) (X : BAut1 S^n.+1)
  : equiv_psusp_rec _ _ (thom_class_BAut1 n X) = thom_class_sigma n X.
Proof.
  revert X; rapply band_induction.
  rhs napply thom_class_sigma_beta.
  rewrite thom_class_BAut1_beta.
  (* The next three lines are all definitional equalities. *)
  unfold generator_BAut1_KZ, loop_susp_adjoint'.
  (* The inverse of the composite is the composite of the inverses. *)
  change (_ = ?R) with (equiv_psusp_rec S^n.+1 (pBAut1 (KZ n.+1))
                         ((equiv_psusp_rec S^n.+1 (pBAut1 (KZ n.+1)))^-1
                           ((issig_pmap_loops S^n.+1 (pBAut1 (KZ n.+1)))^-1
                             (generator_loops_BAut1_KZ n))) = R).
  (* This changes the LHS further to [equiv_psusp_rec S^ n.+1 (pBAut1 (KZ n.+1)) ((equiv_psusp_rec S^ n.+1 (pBAut1 (KZ n.+1)))^-1 (pt; generator_loops_BAut1_KZ n))]. The RHS is *)
  rewrite_refl issig_pmap_loops_inv_beta.
  (* Goal: [equiv_psusp_rec S^ n.+1 (pBAut1 (KZ n.+1))
             ((equiv_psusp_rec S^ n.+1 (pBAut1 (KZ n.+1)))^-1
               (pt; generator_loops_BAut1_KZ n))
             = (pt; generator_loops_BAut1_KZ n)] *)
  (* We cancel the equivalence and its inverse. *)
  apply eisretr.
Defined.

(** It follows that our [BAut1] definition produces the Euler class when evaluated on [South]. *)
(* [BCM:cor:thom.euler], up to comparing how the Thom classes are defined *)
Definition thom_euler `{Univalence} (n : nat) (X : BAut1 S^n.+1)
  : thom_class_BAut1 n X South = euler X.
Proof.
  (* Both sides are the first projection of the previous result! *)
  exact (ap pr1 (thom_classes_agree n X)).
  Opaque thom_class_BAut1. (* To make the Defined line fast. *)
Defined.
Transparent thom_class_BAut1.
