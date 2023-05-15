Require Import Basics Types WildCat.

Definition cate_monic_equiv {A} `{HasEquivs A} {a b : A} (e : a $<~> b)
  : Monic e.
Proof.
  intros c f g p.
  refine ((compose_V_hh e _)^$ $@ _ $@ compose_V_hh e _).
  exact (_ $@L p).
Defined.

Definition cate_moveL_V1 {A} `{HasEquivs A} {a b : A} {e : a $<~> b} (f : b $-> a)
  (p : e $o f $== Id _)
  : cate_fun e^-1$ $== f.
Proof.
  apply (cate_monic_equiv e).
  exact (cate_isretr e $@ p^$).
Defined.

Definition cate_inv2 {A} `{HasEquivs A} {a b : A} {e f : a $<~> b} (p : cate_fun e $== cate_fun f)
  : cate_fun e^-1$ $== cate_fun f^-1$.
Proof.
  apply cate_moveL_V1.
  exact ((p $@R _) $@ cate_isretr _).
Defined.

Definition cate_inv_compose {A} `{HasEquivs A} {a b c : A} (e : a $<~> b) (f : b $<~> c)
  : cate_fun (f $oE e)^-1$ $== cate_fun (e^-1$ $oE f^-1$).
Proof.
  refine (_ $@ (compose_cate_fun _ _)^$).
  apply cate_moveL_V1.
  refine ((compose_cate_fun _ _ $@R _) $@ _).
  refine (cat_assoc_opp _ _ _ $@ _).
  refine ((compose_hh_V _ _ $@R _) $@ _).
  apply cate_isretr.
Defined.

Definition cate_inv_V {A} `{HasEquivs A} {a b : A} (e : a $<~> b)
  : cate_fun (e^-1$)^-1$ $== cate_fun e.
Proof.
  apply cate_moveL_V1.
  apply cate_issect.
Defined.

(** Add this or see if I can make some of the arguments implicit right in the definition (a, b, fe). *)
Arguments cate_buildequiv_fun' {A}%type_scope
  {IsGraph0 Is2Graph0 Is01Cat0 H HasEquivs} {a b}
  f {fe}.

Definition cat_comp2 {A} `{Is1Cat A} {a b c : A}
  {f g : a $-> b} {h k : b $-> c}
  (p : f $== g) (q : h $== k )
  : h $o f $== k $o g
  := (q $@R _) $@ (_ $@L p).
Reserved Infix "$@@" (at level 30).  (* Put in Notations.v *)
Notation "q $@@ p" := (cat_comp2 q p).

Definition emap_inv {A B : Type} `{HasEquivs A} `{HasEquivs B}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F}
  {a b : A} (e : a $<~> b)
  : cate_fun (emap F e)^-1$ $== cate_fun (emap F e^-1$).
Proof.
  apply cate_moveL_V1.
  refine ((cate_buildequiv_fun' _ $@@ cate_buildequiv_fun' _ ) $@ _).
  refine ((fmap_comp _ _ _)^$ $@ _).
  refine (fmap2 _ (cate_isretr _) $@ _).
  rapply fmap_id.
Defined.

Definition emap_compose {A B : Type} `{HasEquivs A} `{HasEquivs B}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F}
  {a b c : A} (f : a $<~> b) (g : b $<~> c)
  : cate_fun (emap F (g $oE f)) $== cate_fun ((emap F g) $oE (emap F f)).
Proof.
  refine (cate_buildequiv_fun' _ $@ _ $@ (compose_cate_fun _ _)^$).
  refine (fmap2 F (compose_cate_fun _ _) $@ _).
  refine (fmap_comp _ _ _ $@ _).
  symmetry.
  exact (cate_buildequiv_fun' _ $@@ cate_buildequiv_fun' _).
Defined.

(* We don't end up using this one. *)
Definition emap_id {A B : Type} `{HasEquivs A} `{HasEquivs B}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F} {a : A}
  : cate_fun (emap F (id_cate a)) $== cate_fun (id_cate (F a)).
Proof.
  refine (cate_buildequiv_fun' _ $@ _).
  refine (fmap2 F (id_cate_fun a) $@ _ $@ (id_cate_fun (F a))^$).
  rapply fmap_id.
Defined.

Global Instance hasequivs_core {A : Type} `{HasEquivs A}
  : HasEquivs (core A).
Proof.
  srapply Build_HasEquivs.
  1: exact (fun a b => a $-> b).  (* In [core A], i.e. [CatEquiv' (uncore a) (uncore b)]. *)
  all: intros a b f; cbn; intros.
  - exact Unit.  (* Or [CatIsEquiv' (uncore a) (uncore b) (cate_fun f)]? *)
  - exact f.
  - exact tt.    (* Or [cate_isequiv' _ _ _]? *)
  - exact f.
  - reflexivity.
  - exact f^-1$.
  - refine (compose_cate_fun _ _ $@ _).
    refine (cate_issect _ $@ _).
    symmetry; apply id_cate_fun.
  - refine (compose_cate_fun _ _ $@ _).
    refine (cate_isretr _ $@ _).
    symmetry; apply id_cate_fun.
  - exact tt.
Defined.

Definition to_core {A : Type} `{HasEquivs A} (a : A)
  : core A
  := Build_core A a.

(* When [A] has morphism extensionality, I don't think it follows that [core A] does.  We'd need to know that being an equivalence is a property, and I don't think we assume that (since even for [Type] it requires [Funext]). So we need to assume this in the following results. *)

(** Postcomposition with a cat_equiv is an equivalence between the types of equivalences. *)
Definition equiv_postcompose_core_cat_equiv {A : Type} `{HasEquivs A} `{!HasMorExt A} `{!HasMorExt (core A)}
  {x y z : A} (f : y $<~> z)
  : (x $<~> y) <~> (x $<~> z).
Proof.
  change ((to_core x $-> to_core y) <~> (to_core x $-> to_core z)).
  refine (equiv_postcompose_cat_equiv (A := core A) _).
  exact f.  (* It doesn't work to insert [f] on the previous line. *)
Defined.

Definition equiv_precompose_core_cat_equiv {A : Type} `{HasEquivs A} `{!HasMorExt A} `{!HasMorExt (core A)}
  {x y z : A} (f : x $<~> y)
  : (y $<~> z) <~> (x $<~> z).
Proof.
  change ((to_core y $-> to_core z) <~> (to_core x $-> to_core z)).
  refine (equiv_precompose_cat_equiv (A := core A) _).
  exact f.  (* It doesn't work to insert [f] on the previous line. *)
Defined.
