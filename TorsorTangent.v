From HoTT Require Import Basics Types Homotopy.Join Truncations.Core.

From CentralTypes Require Import Torsor Lemmas ProjectiveLemmas JoinLemmas Reflections.

(** * "Tangent spaces" of join powers *)

(** ** The tangent bundle and its trivialization *)

(** First we show in [tau_step] and [theta_step] that given a torsor [E] and an orthotorsor [En], we get an orthotorsor structure on [Join E En].  When these results are used below, [En] will be [join_power E n]. *)

Definition tau_step `{Univalence} {A E En : Type}
  (T : torsor A E) {r : A <~> A} (h : reflection r)
  (IHtau : En -> Type@{u})
  (IHtheta : forall x : En,  Join@{_ u u} A (IHtau x) <~> En)
  : Join E En -> Type@{u}.
Proof.
  snapply Join_fam.
  - intro e.
    exact En.
  - intro e'.
    exact (Join E (IHtau e')).
  - intros e e'; cbn.
    (* It's best to put an inverse on the outside, since we'll later compose with the inverse of this equivalence. *)
    exact ((IHtheta e') oE equiv_functor_join (r oE (T e)^-1) equiv_idmap)^-1%equiv.
Defined.

Definition transport_tau_step `{Univalence} {A E En : Type}
  (T : torsor A E) {r : A <~> A} (h : reflection r)
  (IHtau : En -> Type@{u})
  (IHtheta : forall x : En,  Join@{_ u u} A (IHtau x) <~> En)
  (e : E) (e' : En)
  : transport (tau_step T h IHtau IHtheta) (jglue e e')
    = (IHtheta e' oE equiv_functor_join (r oE (T e)^-1) equiv_idmap)^-1
  := Join_fam_beta_jglue' _ _ _ _ _.

(** A version with equivalences. *)
Definition transport_tau_step' `{Univalence} {A E En : Type}
  (T : torsor A E) {r : A <~> A} (h : reflection r)
  (IHtau : En -> Type@{u})
  (IHtheta : forall x : En,  Join@{_ u u} A (IHtau x) <~> En)
  (e : E) (e' : En)
  : equiv_transport (tau_step T h IHtau IHtheta) (jglue e e')
    = (IHtheta e' oE equiv_functor_join (r oE (T e)^-1) equiv_idmap)^-1%equiv
  := Join_fam_beta_jglue _ _ _ _ _.

(** Transporting in the reverse direction. *)
Definition transport_tau_step_inv `{Univalence} {A E En : Type}
  (T : torsor A E) {r : A <~> A} (h : reflection r)
  (IHtau : En -> Type@{u})
  (IHtheta : forall x : En,  Join@{_ u u} A (IHtau x) <~> En)
  (e : E) (e' : En)
  : transport (tau_step T h IHtau IHtheta) (jglue e e')^
    = (IHtheta e' oE equiv_functor_join (r oE (T e)^-1) equiv_idmap).
Proof.
  change (_ = ?RHS) with
    (equiv_fun (equiv_transport (tau_step T h IHtau IHtheta) (jglue e e'))^-1%equiv = RHS).
  rewrite transport_tau_step'. (* todo: avoid rewrite *)
  reflexivity.
Defined.

(** Transporting in the reverse direction, as a homotopy. *)
Definition transport_tau_step_inv_htpy `{Univalence} {A E En : Type}
  (T : torsor A E) {r : A <~> A} (h : reflection r)
  {IHtau : En -> Type@{u}}
  (IHtheta : forall x : En,  Join@{_ u u} A (IHtau x) <~> En)
  (e : E) (e' : En)
  : transport (tau_step T h IHtau IHtheta) (jglue e e')^
    == (IHtheta e' oE equiv_functor_join (r oE (T e)^-1) equiv_idmap).
Proof.
  change (_ == ?RHS) with
    (equiv_fun (equiv_transport (tau_step T h IHtau IHtheta) (jglue e e'))^-1%equiv == RHS).
  (* Here we use that [(f^-1)^-1] is [f], as functions: *)
  match goal with |- equiv_fun (?e1^-1) == equiv_fun ?e2 =>
                    refine (equiv_inverse_homotopy e2^-1 e1 _) end.
  symmetry.
  unfold tau_step; cbn.
  exact (Join_fam_beta_jglue_homotopy _ (fun e' => Join E (IHtau e')) _ _ _).
  (* The last four lines can also be replaced with:
  rewrite transport_tau_step'.
  reflexivity.
  *)
Defined.

(** A lemma that handles the main part of [theta_step] by generalizing. [Te] here is [T e] below, etc. *)
Lemma theta_step_helper `{Univalence} {A E En Tau}
  (Te : A <~> E) {r : A <~> A} (h : reflection r) (th : Join A Tau <~> En)
  (x : Join A (Join E Tau))
  : functor_join Te idmap (functor_join idmap (th o functor_join (r o Te^-1) idmap) x)
    = functor_join idmap th (trijoin_twist A E Tau x).
Proof.
  (* By univalence and path induction, we can assume that [Te] and [th] are identity equivalences. *)
  revert E Te x; snapply equiv_induction; cbn beta.
  revert En th; snapply equiv_induction; intro x; cbn.
  apply ap.
  apply fix_the_twist; assumption.
  (* The second [equiv_induction] can also be replaced by some elementary path algebra (see git). *)
Defined.

(** Later, we will need to know how [theta_step_helper] computes, using that [r] is coherent. *)
Lemma theta_step_helper_joinl `{Univalence} {A E En Tau}
  (Te : A <~> E) {r : A <~> A} (hc : coherent_reflection r) (th : Join A Tau <~> En)
  (a : A)
  : theta_step_helper Te hc.1 th (joinl a) = jglue (Te a) (th (joinl a)).
Proof.
  set (h := hc.1).
  (* By univalence and path induction, we can assume that [Te] and [th] are identity equivalences. *)
  revert E Te a; snapply equiv_induction; cbn beta.
  revert En th; snapply equiv_induction; intro x; cbn.
  unfold theta_step_helper.
  rewrite 2 equiv_induction_comp.
  (* The RHS is equal to [ap (functor_join idmap idmap)] applied to [jglue x (joinl x)], so we can reduce to the following goal: *)
  rhs_V napply functor_join_beta_jglue.
  apply ap.
  apply fix_the_twist_beta_joinl. (* This uses that [r] is coherent, specifically [hl]. *)
Defined.

(** A computation rule for [theta_step_helper] on the middle factor [E]. This is used in Spheres.v, but nowhere else. *)
Lemma theta_step_helper_joinr_joinl `{Univalence} {A E En Tau}
  (Te : A <~> E) {r : A <~> A} (hc : coherent_reflection r) (th : Join A Tau <~> En)
  (e' : E)
  : theta_step_helper Te hc.1 th (joinr (joinl e')) = (jglue e' (th (joinl (r (Te^-1 e')))))^.
Proof.
  set (h := hc.1).
  (* By univalence and path induction, we can assume that [Te] and [th] are identity equivalences. *)
  revert E Te e'; snapply equiv_induction; cbn beta.
  revert En th; snapply equiv_induction; intro x; cbn.
  unfold theta_step_helper.
  rewrite 2 equiv_induction_comp.
  lhs nrefine (ap _ _).
  1: napply fix_the_twist_beta_joinr_joinl. (* This uses that [r] is coherent, specifically [hr]. *)
  lhs napply ap_V.
  apply (ap inverse).
  napply functor_join_beta_jglue.
Defined.

Definition theta_step `{Univalence} {A E En : Type}
  (T : torsor A E) {r : A <~> A} (h : reflection r)
  (IHtau : En -> Type)
  (IHtheta : forall x : En,  Join A (IHtau x) <~> En)
  :  forall x : Join E En, Join A (tau_step T h IHtau IHtheta x) <~> Join E En.
Proof.
  (* We'll first define theta as a map, using join induction, and then do a separate join induction to show that it is an equivalence.  This will make it simpler to reason about the underlying map. *)
  intro x; snapply Build_Equiv.
  - revert x; snapply Join_ind.
    + intro e; cbn beta.
      exact (equiv_functor_join (T e) equiv_idmap).
    + intro e'; cbn beta.
      exact (equiv_functor_join equiv_idmap (IHtheta e') oE equiv_trijoin_twist A E (IHtau e')).
    + intros e e'; cbn beta.
      funext x; simpl in x.
      lhs napply transport_arrow_toconst.
      unfold equiv_functor_join, "oE", equiv_compose, equiv_idmap, equiv_fun.
      (* Next we work out the inner transport. *)
      lhs napply ap.
      { lhs napply transport_join_r.
        napply functor2_join; only 1: reflexivity.
        napply transport_tau_step_inv_htpy. }
      ev_equiv. (* This just makes it look nice. *)
      napply theta_step_helper; assumption.
  - revert x; snapply Join_ind.
    + intro e; apply equiv_isequiv.
    + intro e'; apply equiv_isequiv.
    + intros e e'; apply path_ishprop.
Defined.

Definition theta_step_beta_joinl `{Univalence} {A E En : Type}
  (T : torsor A E) {r : A <~> A} (h : reflection r)
  (IHtau : En -> Type)
  (IHtheta : forall x : En,  Join A (IHtau x) <~> En)
  (e : E)
  : theta_step T h IHtau IHtheta (joinl e) = equiv_functor_join (T e) equiv_idmap
  := 1.

(* Ah, here's the trick I need to get Coq to generate the RHS, but keep it small.  Takes 0.04s. *)
Definition theta_step_beta_jglue `{Univalence} {A E En : Type}
  (T : torsor A E) {r : A <~> A} (h : reflection r)
  (IHtau : En -> Type)
  (IHtheta : forall x : En,  Join A (IHtau x) <~> En)
  (e : E) (e' : En)
  : apD (fun x => equiv_fun (theta_step T h IHtau IHtheta x)) (jglue e e') = _
  := ltac:(nrefine (Join_ind_beta_jglue _ _ _ _ e e')).
(*
Check theta_step_beta_jglue. (* Around 25 lines long, exactly as expected. *)
Print theta_step_beta_jglue. (* Around 115 lines. *)
*)

Definition ap_transport_toconst_theta_step_jglue `{Univalence} {A E En : Type}
  (T : torsor A E) {r : A <~> A} (hc : coherent_reflection r)
  (IHtau : En -> Type)
  (IHtheta : forall x : En,  Join A (IHtau x) <~> En)
  (a : A) (e : E) (e' : En)
  : ap_transport_toconst (theta_step T hc.1 IHtau IHtheta) (jglue e e') (joinl a)
  = ap (functor_join (T e) idmap) (apD (fun x : Join E En => joinl (tau_step T hc.1 IHtau IHtheta x) a) (jglue e e')^)
  @ jglue (T e a) (IHtheta e' (joinl a)).
(* todo: can I improve the first term on the RHS? *)
(** todo: can this be merged with alpha_jglue_helper1 in Spheres.v, which evaluates on [joinr o joinl] instead of [joinl]? Can I phrase it for any [a] that is a section?  The problem is that the [functor2_join] part doesn't disappear in that generality.  But maybe at least parts can be unified, and put beside each other? *)
Proof.
  unfold ap_transport_toconst.
  rewrite (theta_step_beta_jglue T hc.1 IHtau IHtheta e e').
  rewrite (eisretr ap10). (* Cancels [ap10] and [path_forall]. *)
  rewrite concat_V_pp. (* Cancels [transport_arrow_toconst] and its inverse. *)
  (* The [functor2_join ... (joinl a)] term is equal to reflexivity. *)
  unfold functor2_join; simpl. rewrite concat_p1.
  (* The [transport_join_r] term is definitionally the same as the earlier [apD] term, allowing: *)
  refine (1 @@ _).
  napply theta_step_helper_joinl.
Defined.

(** The tangent space and trivialization of a join power of a torsor over a type with reflection. **)
(* [BCM:thm:tangent-spaces] *)
Definition tangent_triv `{Univalence} {A E : Type}
  (T : torsor A E) {r : A <~> A} (h : reflection r)
  (n : nat)
  : { tau : forall (x : join_power E n), Type &
          forall (x : join_power E n), Join A (tau x) <~> join_power E n }.
Proof.
  induction n.
  - cbn.
    (* The [x] takes values in [Empty], so there is nothing to do. *)
    srefine (_; _); intros [].
  - destruct IHn as [IHtau IHtheta].
    exact (tau_step T h IHtau IHtheta ; theta_step T h IHtau IHtheta).
Defined.

Definition tau `{Univalence} {A E : Type} (T : torsor A E) {r} (h : reflection r) n
  := (tangent_triv T h n).1.

Definition theta `{Univalence} {A E : Type} T {r} (h : reflection r) n
  : forall x, Join A (tau T h n x) <~> join_power E n
  := (tangent_triv T h n).2.

(* I tried to avoid having these unfold when [n] is not a successor, but none of these helped:
Arguments tangent_triv _ _ _ _ _ _ !n / : simpl nomatch.
Arguments theta_step  _ _ _ _ _ _ !n / : simpl nomatch.
Arguments tau  _ _ _ _ _ _ !n / : simpl nomatch.
Arguments theta  _ _ _ _ _ _ !n / : simpl nomatch.
*)

(** To describe the fibres of [tau], we shift the indexing on the join power so that we can go one lower, making the base case of the induction trivial (but adding a [destruct n] step to the inductive step. *)
Definition join_power_shift (E : Type) (n : nat) : Type
  := match n with
    | O => Empty
    | S m => join_power E m
    end.

(** The fibers of the tangent bundle are merely join powers of [A]. *)
(* [BCM:prop:tau-mere-fibers] *)
Definition tau_merely_join_power `{Univalence}
  {A E : Type} (T : torsor A E) {r} (h : reflection r) n
  : forall x, merely (tau T h n x <~> join_power_shift E n).
Proof.
  induction n.
  - intros [].
  - snapply (Join_ind (B:=join_power E n)).
    + intro e; exact (tr equiv_idmap).
    + intro e'; cbn beta.
      specialize (IHn e'); strip_truncations.
      apply tr.
      simpl; change (_ <~> ?R) with (Join E (tau T h n e') <~> R).
      destruct n.
      * destruct e'.
      * exact (equiv_functor_join equiv_idmap IHn).
    + intros a b; apply path_ishprop.
Defined.

(** Here's the version only stated for [n] at least [1].  The base case is very slightly harder, but the inductive step is a bit simpler. *)
Definition tau_merely_join_power' `{Univalence}
  {A E : Type} (T : torsor A E) {r} (h : reflection r) n
  : forall x, merely (tau T h n.+1 x <~> join_power E n).
Proof.
  induction n.
  - snapply Join_ind.
    + intro e; exact (tr equiv_idmap).
    + intros [].
    + intros e [].
  - snapply (Join_ind (B:=join_power E n.+1)).
    + intro e; exact (tr equiv_idmap).
    + intro e'; cbn beta.
      specialize (IHn e'); strip_truncations.
      apply tr.
      simpl; change (_ <~> ?R) with (Join E (tau T h n.+1 e') <~> R).
      exact (equiv_functor_join equiv_idmap IHn).
    + intros a b; apply path_ishprop.
Defined.

(** In the special case where [E] is [A], the proof simplifies, with no induction over [n].  Can the previous proof be made simpler in some way, maybe using [theta] and/or a separate lemma that involves an induction over [n]? *)
Definition tau_merely_join_power'' `{Univalence}
  {A : Type} (T : torsor A A) {r} (h : reflection r) n
  : forall x, merely (tau T h n.+1 x <~> join_power A n).
Proof.
  snapply (Join_ind (B:=join_power A n)); cbn beta.
  - intro e.
    unfold tau; simpl.
    exact (tr (equiv_functor_join_power (T e)^-1%equiv n)).
  - intro e'.
    apply tr.
    change (_ <~> ?R) with (Join A (tau T h n e') <~> R).
    apply theta.
  - intros a b; apply path_ishprop.
Defined.

Definition tau_beta_joinl `{Univalence} {A E : Type} (T : torsor A E) {r} (h : reflection r) n
  (e : E)
  : tau T h n.+1 (joinl e) = join_power E n
  := idpath.

Definition transport_tau `{Univalence} {A E : Type} (T : torsor A E) {r} (h : reflection r) n
  (e : E) (e' : join_power E n)
  : transport (tau T h n.+1) (jglue e e')
    = (theta T h n e' oE equiv_functor_join (r oE (T e)^-1) equiv_idmap)^-1
  := transport_tau_step T h _ _ e e'.

(* A version with equivalences instead of functions. *)
Definition transport_tau' `{Univalence} {A E : Type} (T : torsor A E) {r} (h : reflection r) n
  (e : E) (e' : join_power E n)
  : equiv_transport (tau T h n.+1) (jglue e e')
    = ((theta T h n e') oE equiv_functor_join (r oE (T e)^-1) equiv_idmap)^-1%equiv
  := transport_tau_step' T h _ _ e e'.

Definition theta_beta_joinl `{Univalence} {A E : Type} (T : torsor A E) {r} (h : reflection r) n
  (e : E)
  : theta T h n.+1 (joinl e) = equiv_functor_join (T e) equiv_idmap
  := idpath.

Definition theta_beta_joinr `{Univalence} {A E : Type} (T : torsor A E) {r} (h : reflection r) n
  (e' : join_power E n)
  : theta T h n.+1 (joinr e') = equiv_functor_join equiv_idmap (theta T h n e') oE equiv_trijoin_twist _ _ _
  := idpath.

(* Takes 0s and is tiny.  Worth having, as I can't seem to get Coq to do this simplification otherwise. Moreover, at this point you can unfold [theta_step], and it's only about 40 lines long. *)
Definition theta_beta_nat' `{Univalence} {A E : Type} (T : torsor A E) {r} (h : reflection r) n
  : theta T h n.+1 = theta_step T h (tau T h n) (theta T h n)
  := idpath.

Definition theta_beta_jglue `{Univalence} {A E : Type} (T : torsor A E) {r} (h : reflection r) n
  (e : E) (e' : join_power E n)
  : apD (fun x => equiv_fun (theta T h n.+1 x)) (jglue e e') = _
  := theta_step_beta_jglue T h (tau T h n) (theta T h n) e e'.
(*
Check theta_beta_jglue. (* Around 28 lines long, exactly as expected. *)

If I want a version with [tau T h n.+1] instead of [tau_step ...], I can do:
  := ltac:(change (theta T h n.+1) with (theta_step T h n (tau T h n) (theta T h n));
          nrefine (Join_ind_beta_jglue _ _ _ _ e e' @ _);
          change (tau_step T h n (tau T h n) (theta T h n)) with (tau T h n.+1);
          reflexivity).
But it takes a few seconds. *)

(** To check that [theta] really gives an orthogonal decomposition of the join power of [E] (in David's sense), we need to check that on the left factor it does the right thing. *)
(* [BCM:thm:theta-inl] *)
Definition theta_joinl `{Univalence} {A E : Type}
  (T : torsor A E) {r : A <~> A} (hc : coherent_reflection r)
  (n : nat) (y : join_power E n)
  : (theta T hc.1 n y) o joinl == torsor_inclusion T n y.
Proof.
  set (h := hc.1).
  intro a.
  revert y.
  induction n.
  - intros [].
  - snapply (Join_ind_FlFr (B:=join_power E n)).
    + intro e; simpl.
      reflexivity.
    + intro e'; simpl.
      apply (ap joinr).
      apply IHn.
    + intros e e'; cbn beta.
      rhs napply concat_1p.
      unfold torsor_inclusion.
      rhs napply torsor_scalar_multiplication_beta_jglue.
      nrefine (_ @@ 1 @ triangle_v (T e a) (IHn e')).
      (* Reexpress the LHS in terms of [apD theta], which has a beta rule by definition. *)
      lhs napply (ap_compose_dependent _ (fun x0 => joinl a) (fun x0 => theta T h n.+1 x0) (jglue e e')).
      (* Note that [fun x0 => joinl a] above is not a constant function. *)
      lhs refine (1 @@ ap_transport_toconst_theta_step_jglue T hc (tau T h n) (theta T h n) a e e').
      apply concat_V_pp. (* Cancels first two terms. *)
Defined. (* todo: 0.14s *)

(** ** Sections of tangent bundles and antipodal maps *)

(** If a tangent bundle has a section, then the antipodal map should be homotopic to the identity. We need to assume that the identity map is induced by the torsor action, a condition that holds for [Bool]. For the "antipodal" maps, we can take the torsor action by *any* element of [A]. The usual antipodal maps of spheres are of this form. *)

(** We begin with something more general.  If we are given a tangent vector at the point [x], then for any [a b : A], the torsor scalar multiplication of [a] and [b] on [x] agree. *)
(* [BCM:lem:section-scalar-mult] *)
Definition torsor_scalar_multiplications_agree_section `{Univalence} {A E : Type}
  (T : torsor A E) {r : A <~> A} (hc : coherent_reflection r)
  (n : nat)
  {x : join_power E n} (s : tau T hc.1 n x)
  (a b : A)
  : torsor_scalar_multiplication T n a x = torsor_scalar_multiplication T n b x.
Proof.
  (* By [theta_joinl], we can replace the torsor actions with [theta x (joinl a/b)]. *)
  refine ((theta_joinl T hc n x a)^ @ _ @ theta_joinl T hc n x b).
  (* But since we have [s] in the other join factor, there is a zig-zag path between [joinl a] and [joinl b]. *)
  exact (ap (theta T hc.1 n x) ((jglue a s) @ (jglue b s)^)).
Defined.

(** Therefore, if there is a point [idpt] such that the torsor action of [idpt] is the identity map and we have a section [s] at [x], then the torsor scalar multiplication of any point sends [x] to [x]. *)
Definition antipodal_idmap_section_tangent_pointwise `{Univalence} {A E : Type}
  (T : torsor A E) {r : A <~> A} (hc : coherent_reflection r)
  (n : nat)
  (idpt a : A) (ptd : torsor_action T idpt = idmap)
  {x : join_power E n} (s : tau T hc.1 n x)
  : torsor_scalar_multiplication T n a x = x.
Proof.
  refine (torsor_scalar_multiplications_agree_section T hc n s a idpt @ _).
  unfold torsor_scalar_multiplication.
  rewrite ptd.
  apply functor_join_power_idmap.
Defined.
(** Todo: replace [ptd] with a homotopy. We'll need something like "functor2_join_power". *)

(** Now the more standard version. *)
(* [BCM:prop:section-antipodal] *)
Definition antipodal_idmap_section_tangent `{Univalence} {A E : Type}
  (T : torsor A E) {r : A <~> A} (hc : coherent_reflection r)
  (n : nat)
  (idpt a : A)
  (ptd : torsor_action T idpt = idmap)
  (s : forall (x : join_power E n), tau T hc.1 n x)
  : torsor_scalar_multiplication T n a == idmap.
Proof.
  intro x.
  exact (antipodal_idmap_section_tangent_pointwise T hc n idpt a ptd (s x)).
Defined.
