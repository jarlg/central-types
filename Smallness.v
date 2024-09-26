(** * Facts about "small" types *)

(** This closely follows Section 2 of the paper "Non-accessible localizations", by Dan Christensen, https://arxiv.org/abs/2109.06670 *)

From HoTT Require Import Basics Types.Unit Types.Sigma Types.Universe.
From HoTT Require Import Universes.Smallness. (* Part has been merged into Coq-HoTT here. *)
From HoTT Require Import HFiber Truncations Pointed.Core Pointed.Loops PropResizing.

Require Import Conn.
Require Import misc.

Open Scope trunc_scope.

(** Universe variables:  we most often use a subset of [i j k u].  We think of [Type@{i}] as containing the "small" types and [Type@{j}] the "large" types.  In some early results, there are no constraints between [i] and [j], and in others we require that [i <= j], as expected.  While the case [i = j] isn't particularly interesting, we put some effort into ensuring that it is permitted as well, as there is no semantic reason to exclude it.  The universe variable [k] should be thought of as max(i+1,j), and it is generally required to satisfy [i < k] and [j <= k].  If we assume that [i < j], then we can take [k = j], but we include [k] so that we also allow the case [i = j].  The universe variable [u] is only present because we occasionally use Univalence in [Type@{k}], so the equality types need a larger universe to live in.  Because of this, most results require [k < u].

Summary of the most common situation:  [i < k < u, j <= k], where [i] is for the small types, [j] is for the large types, [k = max(i+1,j)] and [u] is an ambient universe for Univalence.

We include universe annotations when they clarify the meaning (e.g. in [IsSmall] and when using [PropResizing]), and also when it is required in order to keep control of the universe variables. *)

Local Notation "n ..+2" := (trunc_index_to_nat n) (at level 2) : trunc_scope.

(** Rijke's join construction, taken as an axiom. Egbert assumes [Funext] globally, so we assume it here. Not 100% sure that is needed. This has been formalized by Valery Isaev in the Arend Standard Library available at https://github.com/JetBrains/arend-lib.  See the file Homotopy/Image.ard. *)
(** TODO: delete the version in Modalities.Truncated when I merge this.  My version uses my set-up, to avoid assuming that [i < j]. *)
(** TODO: Actually prove this, and put it somewhere more appropriate. *)
Section JoinConstruction.
  Universes i j k.
  Context `{Funext} {X : Type@{i}} {Y : Type@{j}} (f : X -> Y)
          (ls : IsLocallySmall@{i j k} 1 Y).
  Definition jc_image@{} : Type@{i}. Admitted.
  Definition jc_factor1@{} : X -> jc_image. Admitted.
  Definition jc_factor2@{} : jc_image -> Y. Admitted.
  Definition jc_factors@{} : jc_factor2 o jc_factor1 == f. Admitted.
  Global Instance jc_factor1_issurj@{} : IsSurjection jc_factor1. Admitted.
  Global Instance jc_factor2_isemb : IsEmbedding jc_factor2. Admitted.
End JoinConstruction.

(** If [X] is locally small and has a surjection from a small type, then it is small. *)
Definition jc_surjection@{i j k | i < k, j <= k} `{Funext} {A : Type@{i}} {X : Type@{j}}
  (ls : IsLocallySmall@{i j k} 1 X)
  (f : A -> X) (s : IsSurjection@{k} f)
  : IsSmall@{i j} X.
Proof.
  exists (jc_image f ls).
  snrapply Build_Equiv.
  1: apply jc_factor2.
  apply isequiv_surj_emb.
  - nrapply (cancelR_issurjection (jc_factor1 f ls)).
    exact (conn_map_homotopic _ _ _ (fun x => (jc_factors f ls x)^) s).
  - apply jc_factor2_isemb.
Defined.

(** It follows that if [X] is pointed, connected and 1-locally small, then it is small. *)
Definition issmall_pointed_connected_islocallysmall@{i j k u | i < k, j <= k, k < u} `{Univalence}
  (X : pType@{j}) `{IsConnected 0 X} (ls : IsLocallySmall@{i j k} 1 X)
  : IsSmall@{i j} X.
Proof.
  apply (jc_surjection ls (unit_name pt)).
  apply conn_point_incl@{k u}; assumption.
Defined.

(** If a pointed, connected type has a small loop space, then it is small. *)
Definition issmall_issmall_loops@{i j k u| i < k, j <= k, k < u} `{Univalence}
  {B : pType@{j}} `{IsConnected 0 B} (islB : IsSmall@{i j} (loops B))
  : IsSmall@{i j} B.
Proof.
  nrapply issmall_pointed_connected_islocallysmall@{i j k u}.
  1: assumption.
  intros b0.
  nrapply (conn_point_elim@{k u} (-1)); [assumption | exact _ |].
  revert b0; nrapply (conn_point_elim@{k u} (-1)); [assumption | exact _ |].
  exact islB.
Defined.

(** If [f : A -> X] is n-connected, [A] is in [Type@{i}] and [X] is (n+2)-locally small, then [X] is small.  This is Proposition 2.2 from the paper. This could of course be generalized to only requiring that [A] be small. *)
Definition issmall_n_image@{i j k u | i < k, j <= k, k < u} `{Univalence}
  (n : trunc_index) {A : Type@{i}} {X : Type@{j}}
  (f : A -> X) (C : IsConnMap@{k} n f) (ls : IsLocallySmall@{i j k} n..+2 X)
  : IsSmall@{i j} X.
Proof.
  revert A X f C ls; simple_induction n n IHn; intros A X f C ls.
  - exact ls.
  - assert (IsConnMap (Tr (-1)) f) as C' by rapply minus_one_connmap_isconnmap.
    snrefine (jc_surjection _ f C').
    (* [f] is surjective and [IsSmall] is an [HProp], so we can assume that [x] and [y] are in the image of [f]. *)
    (* We speed up typeclass inference by providing this: *)
    pose proof (fun x y : X => ishprop_issmall (x = y)) as HP.
    intro x.
    apply (@conn_map_elim@{k i j k} (Tr (-1)) _ _ f C' _ (HP x)).
    intro b.
    revert x.
    apply (@conn_map_elim@{k i j k} (Tr (-1)) _ _ f C' _ (fun x => HP x (f b))).
    intro a.
    snrapply (IHn (a = b) _ (ap@{i j} f)).
    + srapply isconnmap_ap.
    + apply ls.
Defined.

(** If [f : X -> Y] is (n+1)-truncated and [Y] is (n+2)-locally small, then [X] is (n+2)-locally small.  This is Lemma 2.4 from the paper. When [n] is -2, it says that a subtype of a small type is small. *)
Definition islocallysmall_truncmap@{i j k | i < k, j <= k} `{PropResizing}
  (n : trunc_index) {X : Type@{j}} {Y : Type@{j}} (f : X -> Y)
  (T : IsTruncMap n.+1 f) (ls : IsLocallySmall@{i j k} n..+2 Y)
  : IsLocallySmall@{i j k} n..+2 X.
Proof.
  apply (islocallysmall_islocallysmall_codomain_fibers _ f).
  - exact ls.
  - intro y.
    apply islocallysmall_trunc.
    apply T.
Defined.

(** If [f : X -> Y] is (n+1)-truncated, [X] is (n+1)-connected and [Y] is (n+2)-locally small, then [X] is small. This is Lemma 2.5 from the paper. *)
Definition issmall_truncmap_connected@{i j k u | i < k, j <= k, k < u} `{PropResizing} `{Univalence}
  (n : trunc_index) {X Y : Type@{j}} (f : X -> Y) (T : IsTruncMap n.+1 f)
  (ls : IsLocallySmall@{i j k} n..+2 Y)
  (C : IsConnected n.+1 X)
  : IsSmall@{i j} X.
Proof.
  pose proof (x := merely_isconnected n X).
  strip_truncations.
  apply (issmall_n_image@{i j k u} n (unit_name x)).
  - apply lift_isconnmap_trunc@{j k}.
    rapply conn_point_incl@{j u}.
  - by rapply islocallysmall_truncmap.
Defined.

(** [X] is small iff it is (n+2)-locally small and its (n+1)-truncation is small. This is Theorem 2.6 from the paper. *)
Definition issmall_iff_islocallysmall_truncated@{i j k u | i < k, j <= k, k < u} `{PropResizing} `{Univalence}
  (n : trunc_index) (X : Type@{j})
  : IsSmall@{i j} X <-> (IsLocallySmall@{i j k} n..+2 X * IsSmall@{i j} (Trunc n.+1 X)).
Proof.
  split.
  - intro sX.
    split.
    + by apply islocallysmall_issmall.
    + rapply (issmall_equiv_issmall (Trunc_functor_equiv@{i j k} _ (equiv_smalltype X))).
  - intros [lsX sTrX].
    apply (issmall_issmall_codomain_fibers (@tr n.+1 X)).
    + exact sTrX.
    + intro y.
      rapply (issmall_truncmap_connected@{i j k u} n pr1).
      rapply istruncmap_pr1.
Defined.

(** If [f : X -> Y] is (n+1)-truncated, the (n+1)-truncation of [X] is small and [Y] is (n+2)-locally small, then [X] is small. This is Corollary 2.7 from the paper. *)
Definition issmall_truncmap_issmall_truncation@{i j k u | i < k, j <= k, k < u} `{PropResizing} `{Univalence}
  (n : trunc_index) {X Y : Type@{j}} (f : X -> Y) (T : IsTruncMap n.+1 f)
  (ls : IsLocallySmall@{i j k} n..+2 Y)
  (sTrX : IsSmall@{i j} (Trunc n.+1 X))
  : IsSmall@{i j} X.
Proof.
  apply (snd (issmall_iff_islocallysmall_truncated@{i j k u} n X)).
  nrefine (_, sTrX).
  rapply islocallysmall_truncmap; assumption.
Defined.

(** TODO: Add Prop 2.8, with simplified statement. *)

(** Another approach to Theorem 2.6, that avoids propositional resizing. First we need this result. *)

(** If [X] is n-locally small, then so is [Trunc k X] for any [k]. *)
Definition islocallysmall_trunc_islocallysmall@{i j k u | i < k, j <= k, k < u} `{Univalence}
  (n : nat) (k : trunc_index) (X : Type@{j})
  (ls : IsLocallySmall@{i j k} n X)
  : IsLocallySmall@{i j k} n (Trunc k X).
Proof.
  revert k X ls; simple_induction n n IHn; intros k X ls.
  - cbn in *.
    exists (Trunc@{i} k (smalltype X)).
    apply Trunc_functor_equiv@{i j k}, equiv_smalltype.
  - destruct k.
    + apply islocallysmall_issmall.
      rapply issmall_contr.
    + intros a b.
      assert (ist : forall W, IsTrunc k.+1 (IsLocallySmall n W)).
      1: intro W; apply (@istrunc_leq (-1) k.+1 tt _ _).
      strip_truncations.
      apply (islocallysmall_equiv_islocallysmall _ (equiv_path_Tr@{_ u} a b)).
      apply IHn, ls.
Defined.

(** A proof of Theorem 2.6, without propositional resizing. *)
Definition issmall_iff_locallysmall_truncated'@{i j k u | i < k, j <= k, k < u} `{Univalence}
  (n : trunc_index) (X : Type@{j})
  : IsSmall@{i j} X <-> (IsLocallySmall@{i j k} n..+2 X * IsSmall@{i j} (Trunc n.+1 X)).
Proof.
  split.
  - intro sX.
    split.
    + by apply islocallysmall_issmall.
    + apply (issmall_equiv_issmall (Trunc_functor_equiv@{i j k} _ (equiv_smalltype X))).
      apply issmall_in.
  - intros [lsX sTrX].
    apply (issmall_issmall_codomain_fibers (@tr n.+1 X)).
    + exact sTrX.
    (* The only changes are here. *)
    + nrapply Trunc_ind; intro y.
      1: apply (@istrunc_leq (-1) n.+1 tt _ _).
      nrefine (issmall_n_image@{i j k u} n (unit_name (y; idpath)) _ _).
      1: rapply conn_point_incl@{k u}. (* The fibres of (n+1)-truncation are (n+1)-connected. *)
      apply (sigma_closed_islocallysmall _ _ lsX).
      intro x.
      apply (islocallysmall_equiv_islocallysmall _ (equiv_path_Tr@{_ u} x y)).
      apply islocallysmall_trunc_islocallysmall@{i j k u}.
      apply islocallysmall_succ.
      apply lsX.
Defined.
