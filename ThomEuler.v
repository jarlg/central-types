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

(** This instance is useful because Rocq can't guess the [n.-1] argument to [istrunc_pmap], but even so it has no principled way to guess the argument [n] here. *)
Local Instance ishset_pmap `{Univalence} (n : nat) (X Y : pType)
  `{IsConnected n X} `{IsTrunc n.+1 Y}
  : IsHSet (X ->* Y)
  := istrunc_pmap (m:=n.-1) _ _.

(** TODO: This is currently unused, but should be compared to the other definitions given below. *)
(** By [BCM:rmk:thom-class], this agrees with \tilde{th}^*(Σ, N), as mentioned after diagram [BCM:eqn:thom.triangle], using the notation from [BCM:defn:thom.class]. *)
(** Note that this could be generalized to anything in BAut_1 of the universe of pointed types, but we haven't defined BAut_1 in that generality in the formalization. *)
Definition thom_class `{Univalence} (n : nat) (X : BAut1 S^n.+1)
  : psusp X ->* KZ n.+2.
Proof.
  revert X; rapply band_induction.
  change (S^n.+2 ->* KZ n.+2).
  exact ptr.
Defined.

(** We give a different proof of [loop_susp_adjoint].  Here's one based on the non-exported one in pSusp.v, but factored into two, and made shorter using [make_equiv]. *)

(** First we go partway. [BCM:lem:transpose] *)
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
  all: make_equiv_contr_basedpaths.
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

Definition generator_loops_BAut1_KZ `{Univalence} (n : nat)
  : S^n.+1 ->* loops (pBAut1 (KZ n.+1)).
Proof.
  nrefine (_ o* (ptr : S^n.+1 ->* KZ n.+1)).
  exact pequiv_loops_baut1^-1*.
Defined.
(* Note that as an unpointed equivalence, [pequiv_loops_baut1] is equal to [equiv_ev_band' pt] which is used below. We can't use one in both places, since we need a pointed equivalence here and one that works for all bands later. *)

(** This is the canonical generator, since the way [pBAut1 (KZ n.+1)] has the structure of a K(Z, n.+2) is via the equivalence [pequiv_loops_baut1] used in the previous result. *)
(** TODO: verify that this corresponds to [ptr] after composing with the centrality equivalence. *)
Definition generator_BAut1_KZ `{Univalence} (n : nat)
  : S^n.+2 ->* pBAut1 (KZ n.+1).
Proof.
  rapply (loop_susp_adjoint' S^n.+1 _)^-1.
  apply generator_loops_BAut1_KZ.
Defined.

(** Another definition of the Thom class, using the [BAut1] model of K(Z, n+2).  By [BCM:rmk:thom-class], this agrees with \tilde{th}^*(Σ, N), as mentioned after diagram [BCM:eqn:thom.triangle], using the notation from [BCM:defn:thom.class]. *)
(** Note that [X] could be generalized to anything in BAut_1 of the universe of pointed types, but we haven't defined BAut_1 in that generality in the formalization. *)
(** TODO: show that after composing with the centrality equivalence, this agrees with [thom_class]. *)
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

    where the bottom row is [Trunc_functor m F].

    In our case, [m] is [1] and [F] is itself a truncation operation [Tr n.+1].  The proof below works because the square commutes definitionally. *)
Definition tr_path (m : nat) {F : Type -> Type} {X Y : Type} (p : @tr m _ X = @tr m _ Y)
  : @tr m _ (F X) = @tr m _ (F Y)
  := ap (Trunc_functor m F) p.

(** The Euler class *)
(** [BCM:defn:euler.class] *)
Definition euler {n : nat} (X : BAut1 S^n.+1) : BAut1 (KZ n.+1)
  := (Tr n.+1 X.1; tr_path 1 X.2).

(** No longer used. *)
Local Instance ishset_pmap_sigma `{Univalence} (n : nat) (X : Type) (Y : pType)
  `{IsConnected n X} `{IsTrunc n.+2 Y}
  : IsHSet { p : Y & X -> (pt = p) }.
Proof.
  nrefine (istrunc_equiv_istrunc _ (equiv_psusp_rec X Y)).
  rapply (ishset_pmap n.+1).
Defined.

(** This is another version of the Thom class, landing in a Sigma-type which is equivalent (by [equiv_psusp_rec]) to the type of pointed functions.  We'll show that it agrees with [thom_class_BAut1]. [BCM:defn:second.thom.class] (denoted th'_{n+2} in the paper). *)
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

(** We show how this computes when [X] is the standard (n+1)-sphere.  In the following, we could write [pt] in both places, but we are more explicit to help the reader. *)
Definition thom_class_sigma_beta `{Univalence} (n : nat)
  : thom_class_sigma n (point (BAut1 S^n.+1))
    = (point (BAut1 (KZ n.+1)); pointed_fun (generator_loops_BAut1_KZ n)).
Proof.
  unfold thom_class_sigma.
  (* The first components are definitionally equal, so we can do: *)
  apply (ap _).
  (* Make the goal easier to read: *)
  set (KZ := point (pBAut1 (KZ n.+1))).
  change ((equiv_ev_band' KZ)^-1 o tr = pequiv_loops_baut1^-1 o tr).
  (* So it's enough to show that the two equivalences being inverted are equal. *)
  tapply (ap (y:=pequiv_loops_baut1) (fun e : (KZ = KZ) <~> KZ.1 => e^-1 o tr)).
  symmetry; apply pequiv_loops_baut1_equiv_ev_band'.
Defined.

(** [BCM:thm:thom.classes.agree] *)
Definition thom_classes_agree `{Univalence} (n : nat) (X : BAut1 S^n.+1)
  : equiv_psusp_rec _ _ (thom_class_BAut1 n X) = thom_class_sigma n X.
Proof.
  apply moveR_equiv_M.
  revert X; rapply band_induction.
  rewrite thom_class_sigma_beta.
  napply thom_class_BAut1_beta.
  (* For more details, undo the last line, and see how things unfold:
  Undo.
  lhs napply thom_class_BAut1_beta.
  unfold generator_BAut1_KZ, loop_susp_adjoint'.
  (* The inverse of the composite is the composite of the inverses. *)
  change (_ = ?R) with ((equiv_psusp_rec S^n.+1 (pBAut1 (KZ n.+1)))^-1
                          ((issig_pmap_loops S^n.+1 (pBAut1 (KZ n.+1)))^-1
                             (generator_loops_BAut1_KZ n)) = R).
  (* The [equiv_psusp_rec]s exactly map, and the inverse of [issig_pmap_loops] takes a pointed map to [(pt; f)], as shown by this definitional equality: *)
  rewrite_refl issig_pmap_loops_inv_beta.
  reflexivity. *)
Defined.

(** It follows that our [BAut1] definition produces the Euler class when evaluated on [South]. By [BCM:eqn:thom.triangle], this corresponds to pulling back along the zero-section. This is [BCM:cor:thom.euler]. *)
Definition thom_euler `{Univalence} (n : nat) (X : BAut1 S^n.+1)
  : thom_class_BAut1 n X South = euler X.
Proof.
  (* Both sides are the first projection of the previous result! *)
  exact (ap pr1 (thom_classes_agree n X)).
  Opaque thom_class_BAut1. (* To make the Defined line fast. *)
Defined.
Transparent thom_class_BAut1.
