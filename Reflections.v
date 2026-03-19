From HoTT Require Import Basics Homotopy.Join.

From CentralTypes Require Import Torsor Lemmas ProjectiveLemmas JoinLemmas.

(** * "Tangent spaces" of join powers *)

(** ** Reflections *)

(** In order to construct our tangent spaces, we'll need to assume that we have two types [A] and [E], with [E] a torsor for [A].  We'll also need to know that [A] "has a reflection", and for some results, some added coherence. *)

(* Next two are in [BCM:defn:reflection] *)
Definition reflection {A : Type} (r : A <~> A)
  := functor_join idmap r == join_sym A A.

Definition coherent_reflection {A : Type} (r : A <~> A)
  := { h : reflection r & prod (forall a, h (joinl a) = jglue a a) (forall a', h (joinr a') = (jglue a' (r a'))^) }.

(** A coherent reflection [r] has three pieces of additional data [h [hl hr]].
    In the paper, we didn't include the [hr] part of this assumption, but I'm
    pretty sure we use [hr] to prove Prop 6.10 [alpha_merid_bool_pow].
    Search for Spheres.v below and in TorsorTangent.v for where [hr] is used.

    The three pieces of data [h], [hl] and [hr] are equivalent to just providing:
      [forall a a', jglue a a @ (jglue a' a)^ = jglue a (r a') @ (jglue a' (r a'))^]
    With this, one can construct [h] such that [hl] and [hr] hold definitionally.
    (The new condition follows from knowing that [forall a a', (a = a') + (a = r a')].
    But this last condition is too strong, since it is not true for [A = S^1] and [r = idmap].)
*)

(** When [r] is a reflection, [functor_join idmap r] is involutive (its own inverse).  I'm not sure whether it follows that [r] is involutive. *)
Definition involutive_idmap_reflection {A : Type} (r : A <~> A) (h : reflection r)
  : functor_join (A:=A) idmap r o functor_join idmap r == idmap.
Proof.
  intro x.
  lhs napply h.
  lhs napply (ap _ (h x)).
  exact (eissect (join_sym A A) x).
Defined.

(** This is part of [BCM:lem:permute-reflection] in the paper. *)
Definition reflection_flip {A : Type} (r : A <~> A) (h : reflection r)
  : functor_join r idmap == join_sym A A.
Proof.
  intro x.
  apply moveL_equiv_M.
  cbn. (* [join_sym] is its own inverse. *)
  lhs napply join_sym_nat.
  lhs napply h.
  exact (eissect (join_sym A A) x).
Defined.

(** This is also part of [BCM:lem:permute-reflection] in the paper. *)
Definition move_reflection {A : Type} (r : A <~> A) (h : reflection r)
  : functor_join r idmap == functor_join idmap r
  := fun x => reflection_flip r h x @ (h x)^.

(** It follows that [functor_join r r] is the identity map. This is also part of [BCM:lem:permute-reflection] in the paper. *)
Definition reflection_join_itself {A : Type} (r : A <~> A) (h : reflection r)
  : functor_join r r == idmap.
Proof.
  intro x.
  lhs napply (functor_join_compose idmap r r idmap).
  lhs napply (move_reflection r h).
  by apply involutive_idmap_reflection.
Defined.

Local Notation "1pp" := (reflexive_pointwise_paths _ _ _).

Definition reflection_homotopic {A : Type} (r s : A <~> A)
  (p : r == s) (h : reflection r)
  : reflection s
  := fun x => (functor2_join 1pp p x)^ @ h x.

Definition coherent_reflection_homotopic {A : Type} (r s : A <~> A)
  (p : r == s) (hc : coherent_reflection r)
  : coherent_reflection s.
Proof.
  destruct hc as [h [hl hr]].
  exists (reflection_homotopic r s p h).
  unfold reflection_homotopic; simpl.
  split.
  - intro a.
    exact (concat_1p _ @ hl a).
  - intro a'.
    lhs napply (1 @@ hr a').
    (* What's left is a triangle law for joins, but it's easier to just handle it by path induction: *)
    destruct (p a').
    exact (concat_1p _).
Defined.

(** If [A] and [B] have reflections, then the functorial action of join on these reflections gives a reflection on [join A B].  The proof goes through with [A] and [B] in different universes, but applying the pentagon law is very slow in that case, so we assume WLOG that they are in the same universe.  Note that the pentagon law has *not* been proved yet. *)
(* [BCM:prop:reflection-join-reflections] *)
Definition reflection_join_reflections {A B : Type@{u}}
  (r : A <~> A) (h : reflection r)
  (s : B <~> B) (k : reflection s)
  : reflection (equiv_functor_join r s).
Proof.
  unfold reflection.
  symmetry.
  intro x.
  (* This form of the hexagon law replaces one [join_sym] with two: *)
  lhs napply hexagon_join_assoc_sym'.
  unfold trijoin_id_sym; cbn.
  (* Move outer [join_assoc] to RHS, and pass it through RHS: *)
  apply moveR_equiv_V.
  rhs napply join_assoc_nat.
  (* Move inner [join_assoc] to RHS: *)
  revert x; equiv_intro (join_assoc A B (Join A B)) y.
  rewrite eissect.
  (* Use the hexagon law on the two [join_sym]s: *)
  rewrite (functor2_join (hexagon_join_assoc_sym'' _ _ _) 1pp).
  rewrite (functor2_join 1pp (hexagon_join_assoc_sym'' _ _ _)).
  (* Now there are four [join_sym]s, all involving atomic factors. *)
  (* Two of these can be replaced with the reflections [r] and [s]. *)
  (* Unfortunately, both are wrapped *twice* in [functor_join]s, so it's tricky to replace them: *)
  lhs napply (functor2_join _ 1pp).
  1: { intro x'.
       rewrite (functor2_join (symmetric_pointwise_paths _ _ _ _ h) 1pp _).
       (* While we're in here, we'll simplify the expression. First, get rid of two [join_assoc]s. *)
       rewrite <- join_assoc_nat.
       rewrite eissect.
       (* Now we'll reorder some terms. *)
       rewrite <- functor_join_compose.
       rewrite (functor2_join 1pp (fun x0 => join_sym_nat _ _ _)).
       (* And move the [join_assoc] deeper in: *)
       rewrite (functor_join_compose idmap (join_sym A B) idmap _ x').
       lhs rapply join_assoc_nat.
       (* Change [functor_join idmap idmap] to [idmap]. *)
       napply (functor2_join functor_join_idmap 1pp). }
  (* Handle the deeper [join_sym]: *)
  unshelve erewrite (functor2_join (f:=idmap) 1pp _).
  2: { intro x'.
       rewrite (functor2_join 1pp (symmetric_pointwise_paths _ _ _ _ k) _).
       rewrite join_assoc_nat.
       rewrite (eisretr (join_assoc A B B)).
       (* Change [functor_join idmap idmap] to [idmap]. *)
       lhs napply (functor2_join functor_join_idmap 1pp).
       (* Temporarily put [join_sym] and [s] side-by-side. *)
       symmetry; napply functor_join_compose. }
  change (s o idmap) with (equiv_fun s).
  change (idmap o join_sym B A) with (join_sym B A).
  (* Try to get the [join_assoc]s close together. *)
  rewrite (functor_join_compose idmap (join_assoc B A B) idmap _).
  rewrite join_assoc_nat.
  (* Now we cancel the remaining two [join_sym]s. *)
  lhs napply (functor_join_compose (functor_join idmap (join_sym A B)) idmap (functor_join idmap r o join_assoc A B A) idmap).
  lhs napply (functor_join_compose _ idmap _ idmap).
  rewrite <- (functor_join_compose _ s _ idmap).
  unshelve erewrite (functor2_join (g:=s) _ 1pp).
  2: exact (eisretr (equiv_functor_join equiv_idmap (equiv_join_sym A B))).
  (* Now bring the [r] and the [s] together. *)
  rewrite <- (functor_join_compose _ s).
  rewrite (functor_join_compose _ _ idmap s).
  lhs_V napply functor_join_compose.
  (* Make all the [r]s and [s]s disappear: *)
  apply ap.
  (* What's left is the pentagon identity.  I don't think this has been formalized, but I have Admitted it elsewhere. *)
  symmetry; napply pentagon_join_assoc.
  (* The previous line takes around 60s if [A] and [B] are in different universes.  It can be sped up slightly by using [Opaque join_assoc functor_join Join.], but is still very slow. *)
Defined.

(** I don't know if this is true.  The previous proof is complicated and appears here.  Moreover, the pentagon law will arise and won't compute. *)
Definition coherent_reflection_join_coherent_reflections {A B : Type@{u}}
  (r : A <~> A) (hc : coherent_reflection r)
  (s : B <~> B) (kc : coherent_reflection s)
  : coherent_reflection (equiv_functor_join r s).
Proof.
  destruct hc as [h [hl hr]].
  destruct kc as [k [kl kr]].
  exists (reflection_join_reflections r h s k).
  split.
  - intro x.
    unfold reflection_join_reflections.
Abort.

(** It follows from the above that if [A] has a reflection [r], then [Join A A] has the identity map as a reflection. *)
(* Part of [BCM:cor:reflection-circle] *)
Definition reflection_idmap_join {A : Type} (r : A <~> A) (h : reflection r)
  : reflection (@equiv_idmap (Join A A)).
Proof.
  rapply (reflection_homotopic _ _ _ (reflection_join_reflections _ h _ h)).
  apply reflection_join_itself, h.
Defined.

(** The compatibility with [join_sym] implies a compatibility with [trijoin_twist] as well. This is [BCM:lem:fix-the-twist] in the paper. *)
Lemma fix_the_twist `{Funext} {A B : Type}
      {r : A <~> A} (h : reflection r)
  : functor_join idmap (functor_join r idmap) == trijoin_twist A A B.
Proof.
  transitivity ((join_assoc A A B)^-1 o functor_join (functor_join idmap r) idmap o join_assoc A A B).
  - intro x.
    apply moveL_equiv_V.
    apply join_assoc_nat.
  - intro x.
    apply moveR_equiv_V.
    rhs_V napply square_join_sym_assoc_twist.
    apply functor2_join.
    + apply h.
    + reflexivity.
Defined.

(** When [r] is coherent, we get computation rules. *)

Definition fix_the_twist_beta_joinl `{Funext} {A B : Type}
  {r : A <~> A} (hc : coherent_reflection r) (x : A)
  : fix_the_twist (B:=B) hc.1 (joinl x) = join12 x x :> (join1 x = join2 x).
Proof.
  destruct hc as [h [hl hr]]. (* [hr] is not used here. *)
  (* [unfold fix_the_twist; simpl.] doesn't finish, but this simplifies to: *)
  change (1 @ (ap (join_assoc A A B)^-1 (ap joinl (h (joinl x)) @ 1) @ 1) = jglue x (joinl x)).
  rewrite concat_1p, 2 concat_p1.
  lhs_V napply ap_compose.
  lhs nrefine (ap_homotopic join_assoc_inv_joinl (h (joinl x))).
  (* Luckily the conjugation terms are both reflexivity. *)
  refine (concat_p1 _ @ concat_1p _ @ _).
  (* LHS is [ap (functor_join idmap joinl) (h (joinl x))]. *)
  lhs nrefine (ap _ (hl x)). (* This is the only place we use the condition on [h]. *)
  exact (functor_join_beta_jglue _ _ x x).
Defined.
(* todo: investigate why [simpl] doesn't work above.  I already tried making many things opaque. *)

(** This is used in [theta_step_helper_joinr_joinl], which is only used in one place in Spheres.v. *)
Definition fix_the_twist_beta_joinr_joinl `{Funext} {A B : Type}
  {r : A <~> A} (hc : coherent_reflection r) (x : A)
  : fix_the_twist (B:=B) hc.1 (joinr (joinl x)) = (join12 x (r x))^ :> (join2 (r x) = join1 x).
Proof.
  destruct hc as [h [hl hr]]. (* [hl] is not used here. *)
  (* [unfold fix_the_twist; simpl.] doesn't finish, but this simplifies to: *)
  change (1 @ (ap (join_assoc A A B)^-1 (ap joinl (h (joinr x)) @ 1) @ 1) = (jglue x (joinl (r x)))^).
  lhs napply concat_1p.
  lhs napply concat_p1.
  rewrite concat_p1.
  lhs_V napply ap_compose.
  lhs nrefine (ap_homotopic join_assoc_inv_joinl (h (joinr x))).
  (* Luckily the conjugation terms are both reflexivity. *)
  refine (concat_p1 _ @ concat_1p _ @ _).
  lhs nrefine (ap _ (hr x)). (* This is the only place we use the condition on [h]. *)
  lhs napply (ap_V _ (jglue x (r x))).
  apply (ap inverse).
  apply functor_join_beta_jglue.
Defined.

