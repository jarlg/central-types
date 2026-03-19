From HoTT Require Import Basics Types Truncations Homotopy.Join Spaces.Spheres Tactics.EvalIn Spaces.Nat.

From CentralTypes Require Import Lemmas ProjectiveLemmas Reflections Torsor TorsorTangent.

Open Scope nat_scope.
Open Scope path_scope.

(** * Examples of pre-manifolds *)

(** ** [Bool] has a [coherent_reflection] symmetry *)

Definition reflection_bool : reflection equiv_negb.
Proof.
  unfold reflection.
  snapply Join_ind_FlFr.
  - intro a; simpl.
    apply jglue.
  - intro b; simpl.
    symmetry; apply jglue.
  - intros a b; cbn beta.
    lhs refine (_ @@ 1). 1: napply functor_join_beta_jglue.
    rhs refine (1 @@ _). 2: napply join_sym_beta_jglue.
    (* There are really two cases: [a = b] and [a = negb b]. *)
    destruct a, b; cbn.
    1, 4: exact (concat_pV _ @ (concat_pV _)^).  (* [a = b] *)
    all: reflexivity.                            (* [a = negb b] *)
Defined.

(* [BCM:lem:reflection.on.0.sphere] *)
Definition coherent_reflection_bool : coherent_reflection equiv_negb.
Proof.
  unfold coherent_reflection.
  exists reflection_bool.
  split; intros; reflexivity.
Defined.

Definition ap_join_negb `{Univalence}
  : ap (fun X : Type => Join X X) (path_universe_uncurried equiv_negb) = idpath.
Proof.
  apply (equiv_inj (equiv_path _ _)).
  refine (ap_join_square_path_universe_uncurried _ @ _).
  (* RHS is now [equiv_idmap]. *)
  apply path_equiv, path_forall.
  apply (reflection_join_itself _ reflection_bool).
Defined.

(** ** [Bool] is a torsor over itself *)

(** Here we're regarding [bool] as a left-invertible H-space, with [true] the identity element.  So [bool_torsor b c] is [b times c].  In logical notation, it's [not (b xor c)].  We write it as below because we need to know that it is an equivalence as a function of [c]. *)
Definition bool_torsor : torsor Bool Bool.
Proof.
  intro b.
  exact (if b then equiv_idmap else equiv_negb).
Defined.

(** The action is symmetric. *)
Definition bool_torsor_symm (b c : Bool)
  : bool_torsor b c = bool_torsor c b.
Proof.
  destruct b, c; reflexivity.
Defined.

Definition bool_torsor_symm' `{Funext} (c : Bool)
  : (fun b => bool_torsor b c) = bool_torsor c.
Proof.
  funext b; apply bool_torsor_symm.
Defined.

(** In particular, we have: *)
Definition bool_torsor_true `{Funext}
  : (fun b => bool_torsor b true) = idmap
  := bool_torsor_symm' true.

Definition bool_torsor_true' (b : Bool)
  : bool_torsor b true = b.
Proof.
  by destruct b.
Defined.

Definition bool_torsor_false `{Funext}
  : (fun b => bool_torsor b false) = equiv_negb
  := bool_torsor_symm' false.

Definition bool_torsor_false' (b : Bool)
  : bool_torsor b false = negb b.
Proof.
  by destruct b.
Defined.

(** It also follows that the action is an equivalence as a function of [b]. *)
Definition equiv_bool_torsor `{Funext} (c : Bool)
  : IsEquiv (fun b => bool_torsor b c).
Proof.
  rewrite bool_torsor_symm'.
  exact _.
Defined.

(** This also comes up: *)
Definition bool_torsor_inv (b : Bool)
  : (bool_torsor b)^-1 = bool_torsor b.
Proof.
  destruct b; reflexivity.
Defined.

(** The tangent space to [S^{n-1}], regarded as the [n]-fold join power of [Bool]. *)
(* [BCM:defn:tau-sphere] *)
Definition bool_pow_tau `{Univalence} (n : nat) := tau bool_torsor reflection_bool n.

Definition bool_pow_theta `{Univalence} (n : nat) := theta bool_torsor reflection_bool n.

Definition is_bool_pow_bool_pow_tau `{Univalence} (n : nat)
  : forall x : bool_pow n.+1, merely (bool_pow_tau n.+1 x = bool_pow n).
Proof.
  snapply (Join_ind (B:=bool_pow n)).
  - intro a; cbn beta.
    unfold bool_pow_tau, tau; simpl.
    apply tr; reflexivity.
  - intro b; cbn beta.
    apply tr.
    napply path_universe_uncurried.
    (* The LHS is definitionally [Join Bool (sphere_tau n b)], so the goal is exactly [theta]. *)
    napply theta.
  - intros a b; apply path_ishprop.
Defined.

Definition is_sphere_bool_pow_tau `{Univalence} (n : nat)
  : forall x : bool_pow n.+1, merely (bool_pow_tau n.+1 x = Sphere n.-1).
Proof.
  intro x.
  napply tr_concat.
  1: apply is_bool_pow_bool_pow_tau.
  apply tr.
  apply path_universe_uncurried.
  apply equiv_bool_pow_sphere.
Defined.

Definition sphere_tau `{Univalence} (n : nat) :=
  bool_pow_tau n o (equiv_bool_pow_sphere n)^-1.

(** ** Sections and antipodal maps *)

(** When we have a section of the tangent bundle, the action by *any* boolean is the identity. *)
Definition action_idmap_section_tangent_bool_pow `{Univalence}
  (n : nat)
  (s : forall (x : bool_pow n), bool_pow_tau n x)
  (b : Bool)
  : torsor_scalar_multiplication bool_torsor n b == idmap
  := antipodal_idmap_section_tangent _ coherent_reflection_bool n true b bool_torsor_true s.

(** We define the antipodal map on [bool_pow n] to be the torsor scalar multiplication of [false : Bool].  This is also [functor_join_power] applied to the reflection, but that won't generalize as well to projective spaces. Luckily, the general theory applies to scalar multiplication maps. *)
Definition antipodal_bool_pow (n : nat) : bool_pow n -> bool_pow n
  := torsor_scalar_multiplication bool_torsor n false.

(** When we have a section, the antipodal map is homotopic to the identity map. *)
Definition antipodal_idmap_section_tangent_bool_pow `{Univalence}
  (n : nat)
  (s : forall (x : bool_pow n), bool_pow_tau n x)
  : antipodal_bool_pow n == idmap
  := action_idmap_section_tangent_bool_pow n s false.

(** In passing, we note that acting by [true] is the identity map. *)
Definition torsor_scalar_multiplication_bool_pow_idmap (n : nat) (x : bool_pow n)
  : torsor_scalar_multiplication bool_torsor n true x = x.
Proof.
  unfold torsor_scalar_multiplication.
  rhs_V napply functor_join_power_idmap.
  napply functor2_join_power.
  unfold torsor_action.
  napply bool_torsor_true'.
Defined.

(** A section of the tangent space of S^1. Note that this is a special case of [section_tau_bool_pow_2n] and is not used to prove that result. *)
Definition section_tau_bool_pow_2 `{Univalence} : forall x, bool_pow_tau 2 x.
Proof.
  (* This proof looks more complicated than it is because we have to handle the [Empty] join factor in two places. *)
  snapply Join_ind.
  - intro e; unfold bool_pow_tau, tau; simpl.
    exact (joinl e).
  - change (forall b : Join Bool Empty, Join Bool (bool_pow_tau 1 b)).
    snapply Join_ind.
    + intro e'; cbn beta. (* Goal is [Join Bool Empty]. *)
      exact (joinl (negb e')).
    + intros [].
    + intros e' [].
  - intros e; simpl.
    snapply Join_ind.
    + intro e'; simpl.
      lhs nrefine (ap10 (transport_tau _ _ _ _ _) _).
      (* For the reader's benefit, unfold [theta ... (joinl e')]: *)
      rewrite_refl (theta_beta_joinl bool_torsor reflection_bool 0 e').
      simpl.
      napply (ap joinl).
      by destruct e, e'.
    + intros [].
    + intros e' [].
Defined.

(** todo: Put this in Types/Bool.v, and use it twice in [equiv_negb]. *)
Definition negb_inv (b : Bool) : negb (negb b) = b.
Proof.
  by destruct b.
Defined.

(** ** Sections and obstructions to sections of [bool_pow_tau n] *)

(** The following material is roughly based on Sphere2.v.  That file uses suspensions;  see the comments at the top of that file. *)

(** We regard [Join Bool X] as a suspension of [X], with north pole [joinl true] and south pole [joinl false]. *)

Definition Northb {X : Type} := joinl true : Join Bool X.
Definition Southb {X : Type} := joinl false : Join Bool X.

(**  Here are the meridians and their inverses. *)

Definition meridb {X : Type} (x : X)
  := zigzag true false x : Northb = Southb.

Definition meridb_inv {X : Type} (x : X)
  := zigzag false true x : Southb = Northb.

(** It seems like we need both [A] and [E] to be [Bool] for this result. *)
(* [BCM:lem:transport-tau-merid] *)
Definition transport_tau_step_bool_meridb `{Univalence} {En : Type}
  (IHtau : En -> Type@{u})
  (IHtheta : forall x : En,  Join@{_ u u} Bool (IHtau x) <~> En)
  (x : En)
  : transport (tau_step bool_torsor reflection_bool IHtau IHtheta) (meridb x)
  == IHtheta x oE equiv_functor_join equiv_negb equiv_idmap oE (IHtheta x)^-1%equiv.
Proof.
  intro s.
  lhs napply transport_pp.
  rewrite transport_tau_step.
  change (transport ?tau (jglue false x)^ ?t) with ((equiv_transport tau (jglue false x))^-1%equiv t).
  rewrite transport_tau_step'.
  ev_equiv.
  simpl.
  apply ap.
  lhs napply functor2_join.
  1: reflexivity.
  1: exact negb_inv.
  apply functor_join_idmap.
Defined.

(** This is the map that appears on the RHS of [transport_tau_step_bool_meridb], evaluated at [joinl true]. Note that [IHtheta] has been replaced with [theta_step], so that there is one extra join factor. *)
Definition alpha `{Univalence} {En : Type}
  {IHtau : En -> Type@{u}}
  (IHtheta : forall x : En,  Join@{_ u u} Bool (IHtau x) <~> En)
  (theta := theta_step bool_torsor reflection_bool IHtau IHtheta)
  : Join Bool En -> Join Bool En
  := fun x => (theta x o functor_join negb idmap o (theta x)^-1) (joinl true).

(** [alpha] sends both poles to the south pole, definitionally on [joinl true] and [joinl false]. *)
Definition alpha_joinl `{Univalence} {En : Type}
  {IHtau : En -> Type@{u}}
  (IHtheta : forall x : En,  Join@{_ u u} Bool (IHtau x) <~> En)
  (b : Bool)
  : alpha IHtheta (joinl b) = Southb.
Proof.
  unfold alpha; simpl. (* Just for the reader. *)
  by destruct b.
Defined.

(** [alpha] sends the equator to the north pole, definitionally. *)
Definition alpha_joinr `{Univalence} {En : Type}
  {IHtau : En -> Type@{u}}
  (IHtheta : forall x : En,  Join@{_ u u} Bool (IHtau x) <~> En)
  (x : En)
  : alpha IHtheta (joinr x) = Northb
  := idpath.

(** We next work towards [alpha] on the half-meridians.  We begin with some helper lemmas. *)

(** A lemma for our specific situation involving a triple-composite of dependent functions. Since it is so specific, we keep it here. There are many variants of the RHS, but this one works for us. *)
Lemma alpha_jglue_helper0 {A B} {P : A -> Type}
  (g : forall a, P a <~> B) (h : forall a, P a -> P a)
  {a0 a1 : A} (p : a0 = a1)
  (b : B)
  (b' := (g a1)^-1 b)
  : ap (fun a => ((g a) o (h a) o (g a)^-1) b) p
    = ap (g a0) (ap (h a0 o (g a0)^-1) ((eisretr (g a1) b)^ @ (ap_transport_toconst g p b')^)
                   @ ap (h a0) (eissect (g a0) (p^ # b'))
                   @ ap_transport p^ h b')
      @ ap_transport_toconst g p (h a1 b').
Proof.
  destruct p; unfold ap_transport_toconst; simpl.
  rhs napply concat_p1.
  refine (ap (ap (g a0)) (x:=1) _).
  rhs napply concat_p1.
  rewrite concat_p1.
  rhs napply (ap_V _ _ @@ 1).
  apply moveL_Vp.
  lhs napply concat_p1.
  lhs napply (ap_compose _ (h a0)).
  apply ap.
  exact (eisadj (g a0)^-1%equiv b)^.
Defined.

(** This [ap_transport_toconst] term comes up twice, so we factor it out. *)
(** todo: can this be merged with ap_transport_to_const_theta_step_jglue in TorsorTangent.v, which evaluates on [joinl] instead of [joinr o joinl]? *)
Lemma alpha_jglue_helper1 `{Univalence} {En : Type}
  {IHtau : En -> Type@{u}}
  (IHtheta : forall x : En,  Join@{_ u u} Bool (IHtau x) <~> En)
  (b : Bool) (x : En)
  (theta := theta_step bool_torsor reflection_bool IHtau IHtheta)
  (tau := tau_step bool_torsor reflection_bool IHtau IHtheta)
  : ap_transport_toconst (fun a0 : Join Bool En => theta a0)
      (jglue b x) (joinr (joinl true))
  =  ap (functor_join (bool_torsor b) idmap)
       (transport_join_r tau Bool (jglue b x)^ (joinr (joinl true)))
     @ (jglue true (transport tau (jglue b x)^ (joinl true)))^.
Proof.
  Open Scope long_path_scope.
  unfold ap_transport_toconst.
  rewrite (theta_step_beta_jglue _ _ _ _ b x).
  fold tau.
  rewrite (eisretr ap10). (* Cancels [ap10] and [path_forall]. *)
  lhs napply concat_V_pp. (* Cancels [transport_arrow_toconst] and its inverse. *)
  lhs refine (1 @@ theta_step_helper_joinr_joinl (bool_torsor b) coherent_reflection_bool (IHtheta x) true).
  match goal with |- context [ functor2_join ?f ?g (joinr ?z) ] =>
    change (functor2_join f g (joinr z)) with (ap (joinr (A:=Bool)) (g z))
  end.
  rewrite ap_pp.
  rewrite <- (ap_compose joinr _).
  simpl.
  (** I can replace the [ap joinr] term with a zig-zag to any point in Bool. By choosing [true], the 2nd half of the zig-zag cancels with the last term on the LHS. There are other things one could put there as well. *)
  lhs refine (1 @@ (triangle_v' (B:=En) true _)^ @@ 1).
  lhs napply concat_pp_p.
  exact (1 @@ concat_pp_V _ _).
  Close Scope long_path_scope.
Defined.

Lemma alpha_jglue_helper2 {A B} (e : A <~> B) {a0 a1 : A} (p : a0 = a1)
  {b1 b2 b3 : B} (q : e a1 = b3) (r : e a0 = b1) (s : b1 = b2) (t : b2 = b3)
  (h : eissect e a0 @ p @ (eissect e a1)^ @ ap e^-1 q = ap e^-1 r @ (ap e^-1 s @ ap e^-1 t))
  : ap e p @ q = r @ (s @ t).
Proof.
  refine (equiv_inj (ap e^-1) _).
  lhs napply ap_pp.
  rhs napply ap_pp.
  rhs napply (1 @@ ap_pp _ _ _).
  lhs_V napply (ap_compose e e^-1 p @@ 1).
  lhs napply (ap_homotopic_id (eissect e) p @@ 1).
  exact h.
Defined.

Lemma alpha_jglue_helper3 {En} (tau : Join Bool En -> Type) {x : Join Bool En} (jlt : tau x) {y : Join Bool En} (p : x = y)
  : ap (functor_join negb idmap) (transport_join_r tau Bool p (joinr jlt))^
    @ (ap_transport p (fun x0 : Join Bool En => functor_join negb idmap) (joinr jlt)
       @ transport_join_r tau Bool p (joinr jlt)) = 1.
Proof.
  by destruct p.
Defined.

(** [alpha] sends both northern and southern half-meridians to inverted full meridians.  [alpha_joinl] is needed to make it type check, but is reflexivity when [b] is [true] or [false]. The map [a] is the identity map when [b] is [false] and the antipodal map when [b] is [true]. *)
(** todo: use torsor action instead of a?  Or make that a separate result? *)
(* [BCM:prop:alpha-glue] *)
Definition alpha_jglue `{Univalence} {En : Type}
  {IHtau : En -> Type@{u}}
  (IHtheta : forall x : En,  Join@{_ u u} Bool (IHtau x) <~> En)
  (b : Bool) (x : En)
  (a := (fun x => IHtheta x (joinl (negb b))) : En -> En)
  : ap (alpha IHtheta) (jglue b x) = alpha_joinl IHtheta b @ meridb_inv (a x).
Proof.
  Open Scope long_path_scope.
  unfold alpha.
  set (theta := theta_step bool_torsor reflection_bool IHtau IHtheta).
  set (tau := tau_step bool_torsor reflection_bool IHtau IHtheta) in *.
  (* We begin by breaking up the triple composite: *)
  lhs napply (alpha_jglue_helper0 theta (fun x0 => functor_join negb idmap) (jglue b x) (joinl true)).
  (* Cleanup: *)
  rewrite concat_1p. (* Gets rid of eisretr. *)
  change (equiv_fun (theta (joinl b))) with (functor_join (D:=En) (bool_torsor b) idmap).
  change (theta (joinl b))^-1 with (functor_join (D:=En) (bool_torsor b)^-1 idmap).
  change (theta (joinl b)) with (equiv_functor_join (D:=En) (bool_torsor b) equiv_idmap).
  change ((theta (joinr x))^-1 (joinl true)) with (joinr (A:=Bool) (joinl (B:=IHtau x) true)).
  change (tau_step bool_torsor reflection_bool IHtau IHtheta (joinl b)) with En.
  change (functor_join negb idmap (joinr ?z)) with (joinr Bool z).
  set (c := transport (fun x0 : Join Bool En => Join Bool (tau x0)) (jglue b x)^ (joinr (joinl true))).
  (* We next change the two [ap_transport_toconst] terms using [alpha_jglue_helper1].
     The next four lines accomplish the same thing as:
       [rewrite (alpha_jglue_helper1 IHtheta b x).]
     (which does two rewrites, for some reason).  But this way is faster: *)
  lhs napply (1 @@ alpha_jglue_helper1 IHtheta b x).
  lhs refine (ap _ _ @@ 1).
  { refine (ap _ _ @@ 1 @@ 1).
    apply (ap inverse (alpha_jglue_helper1 IHtheta b x)). }
  (* Combine the two [ap (functor_join (bool_torsor b) idmap)]s: *)
  lhs napply concat_p_pp.
  rewrite <- ap_pp.
  (* [helper2] moves the [ap (functor_join (bool_torsor b) idmap)] to the other terms by inverting it, at the cost of two [eissect] terms: *)
  match goal with |- ap _ ?p @ ?q = ?r @ _ =>
                    refine (alpha_jglue_helper2 (equiv_functor_join (bool_torsor b) equiv_idmap) p q r _ _ _) end.
  (* [helper2] created two new [eissect] terms on the LHS; the last one is reflexivity: *)
  lhs napply (concat_p1 _ @@ 1).
  (* Cleanup: *)
  fold tau.
  change (equiv_functor_join (bool_torsor b) 1)^-1 with (functor_join (D:=En) (bool_torsor b)^-1 idmap).
  (* [The [ap]s created by [helper2] all compute: *)
  rewrite (functor_join_beta_jglue (bool_torsor b)^-1 idmap false (a x)).
  rhs napply (1 @@ (1 @@ ap_V _ _)).
  rewrite (functor_join_beta_jglue (bool_torsor b)^-1 idmap true (a x)).
  lhs napply (1 @@ 1 @@ ap_V _ _).
  rewrite (functor_join_beta_jglue (bool_torsor b)^-1 idmap true (transport tau (jglue b x)^ (joinl true))).
  (* We replace the zigzag on the RHS with a different zigzag, matching the last term on the LHS: *)
  rhs napply (1 @@ diamond_v (b':=transport tau (jglue b x)^ (joinl true)) _ _ _).
  2: { symmetry; unfold a.
       lhs napply transport_tau_step_inv_htpy; simpl.
       destruct b; reflexivity. }
  (* Now the last terms on each side cancel. *)
  rhs napply concat_p_pp.
  refine (_ @@ 1).
  (* Next we reorganize the first [ap], splitting it into two: *)
  rewrite inv_pp.
  rewrite inv_V.
  rewrite ap_pp.
  (* The first [ap] computes: *)
  rewrite ap_compose.
  rewrite (functor_join_beta_jglue _ idmap true (transport tau (jglue b x)^ (joinl true))).
  rewrite (functor_join_beta_jglue negb idmap _ (transport tau (jglue b x)^ (joinl true))).
  change (equiv_idmap _ true) with true.
  (* The resulting [jglue] will later cancel the [jglue] on the RHS, after we destruct [b]. *)
  (* Now we work on the next two terms, involving [transport_join_r] and [eissect]. *)
  rewrite ap_compose.
  rewrite ap_V.
  rewrite <- (ap_compose (functor_join (bool_torsor b) idmap) (functor_join (bool_torsor b)^-1 idmap)).
  (* Group the two terms together: *)
  rewrite (concat_pp_p (jglue _ _) _ _).
  match goal with |- context [ ap ?f ?p @ ap ?f ?q ] => rewrite <- (ap_pp f p q) end.
  match goal with |- context [ (ap ?f ?p)^ ] => rewrite <- (ap_V f p) end.
  (* Now the inner [ap] simplifies:  (a direct rewrite fails for some reason) *)
  lhs refine (1 @@ (1 @@ ap _ _ @@ 1 @@ 1)).
  1: exact (concat_A1p (eissect (equiv_functor_join (A:=Bool) (B:=En) (bool_torsor b) 1))
              (transport_join_r tau Bool (jglue b x)^ (joinr (joinl true)))^).
  (* The new [eissect] term is reflexivity: *)
  rewrite concat_1p.
  (* The last three terms on the LHS combine to reflexivity. *)
  lhs refine (1 @@ _).
  { do 2 lhs napply concat_pp_p.
    lhs napply (1 @@ alpha_jglue_helper3 tau (x:=joinr x) (joinl true) (jglue b x)^).
    apply concat_p1. }
  (* And the rest cancels once we destruct [b]. *)
  destruct b; reflexivity.
Defined. (* todo: a bit slow, ~0.44s *)

(** A version with the torsor action instead of [theta]. For this, we need to express it with [En] replaced with [bool_pow n]. *)
Definition alpha_jglue_bool_pow `{Univalence} (n : nat)
  (b : Bool) (x : bool_pow n)
  (a := torsor_scalar_multiplication bool_torsor n (negb b))
  : ap (alpha (bool_pow_theta n)) (jglue b x) = alpha_joinl (bool_pow_theta n) b @ meridb_inv (a x).
Proof.
  lhs napply alpha_jglue.
  refine (1 @@ _).
  apply ap.
  exact (theta_joinl bool_torsor coherent_reflection_bool n x (negb b)).
Defined.

(** We can use [alpha_jglue] twice to get the action on meridians.  Below, [act] is the action of [Bool] on [En] via [theta], which by [theta_joinl] we know is equal to the usual action.  So [act true] is the identity map and [act false] is the antipodal map. *)
Definition alpha_merid `{Univalence} {En : Type}
  {IHtau : En -> Type@{u}}
  (IHtheta : forall x : En,  Join@{_ u u} Bool (IHtau x) <~> En)
  (x : En)
  (act := (fun b x => IHtheta x (joinl b)) : Bool -> En -> En)
  : ap (alpha IHtheta) (meridb x)
    = meridb_inv (act false x) @ meridb (act true x).
Proof.
  lhs napply ap_pp.
  refine (_ @@ _).
  - lhs napply (alpha_jglue IHtheta true x); apply concat_1p.
  - lhs napply ap_V.
    lhs napply (inverse2 (alpha_jglue IHtheta false x @ concat_1p _)).
    napply zigzag_inv.
Defined.

(** Similarly, when specialized to the tangent bundle of a sphere, we can use how [theta] computes to unfold [act].  This is the last part of Prop 6.10 in the draft. *)
Definition alpha_merid_bool_pow `{Univalence} (n : nat)
  (x : bool_pow n)
  : ap (alpha (bool_pow_theta n)) (meridb x)
    = meridb_inv (antipodal_bool_pow n x) @ meridb x.
Proof.
  lhs napply ap_pp.
  refine (_ @@ _).
  - lhs napply (alpha_jglue_bool_pow n true x); apply concat_1p.
  - lhs napply ap_V.
    lhs napply (inverse2 (alpha_jglue_bool_pow n false x @ concat_1p _)).
    simpl.
    unfold meridb_inv.
    rewrite torsor_scalar_multiplication_bool_pow_idmap.
    napply zigzag_inv.
Defined.

(** This shows that [Join Bool E] has the same induction principle as [Susp E]. *)
Definition Join_bool_ind (E : Type) (P : Join Bool E -> Type)
  (P_bool : forall b, P (joinl b))
  (P_merid : forall e, transport P (meridb e) (P_bool true) = P_bool false)
  : forall x, P x.
Proof.
  snapply (Join_ind P P_bool).
  - intro e.
    (* Send [e] to what it has to be to make the northern half-meridians go to reflexivity. *)
    exact ((jglue true e) # (P_bool true)).
  - intros b e; cbn beta.
    destruct b.
    + reflexivity. (* Northern half-meridians. *)
    + (* On the southern half-meridians, we rearrange things a bit to get transport along the full meridians. *)
      napply (moveR_equiv_M' (equiv_transport P (jglue false e))).
      simpl.
      rhs_V napply transport_pp.
      exact (P_merid e)^.
Defined.

(** The tangent bundle of S^{2n-1} has a section. Roughly following [section_tau_odd_sphere] in Spheres2.v. *)
(* [BCM:thm:tau-sphere-section] *)
Definition section_tau_bool_pow_2n `{Univalence} (n : nat)
  : forall x, bool_pow_tau (n*2) x.
Proof.
  induction n.
  - intros [].
  - snapply (Join_bool_ind (join_power Bool (n * 2).+1)).
    + (* Send the north pole to the north pole and the south pole to the south pole. *)
      change (Bool -> join_power Bool (n * 2).+1).
      exact joinl.
    + (* This case should closely match what was done for suspensions in [section_tau_odd_sphere]. *)
      intros e; simpl.
      set (N:=(n*2)) in *.
      (* The LHS can be expressed in terms of obstruction map [alpha] describing the extension from the north pole to the south pole: *)
      lhs napply (transport_tau_step_bool_meridb (bool_pow_tau N.+1) (bool_pow_theta N.+1)).
      change (alpha (bool_pow_theta N) e = joinl false).
      (* The goal is precisely to show that [alpha] is constant.  We need to use the section we have inductively to prove this. *)
      revert e; snapply (Join_bool_ind (join_power Bool N)); cbn beta.
      * apply alpha_joinl.
      * intros e; unfold alpha_joinl. (* Both [alpha_joinl] terms are reflexivity. *)
        lhs napply transport_paths_Fl.
        lhs napply concat_p1.
        apply (ap inverse (y:=1)).
        lhs napply alpha_merid.
        (* Here is the key step.  The section we have gives us a zigzag from [joinl true] to [joinl false]: *)
        rewrite (meridb (IHn e) : joinl true = joinl false).
        napply zigzag_zigzag.
Defined.
