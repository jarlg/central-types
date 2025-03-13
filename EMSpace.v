(** This material could go at the end of Homotopy.EMSpace.v. *)

From HoTT Require Import HoTT.

Require Import BAut1 Central.

Open Scope pointed_scope.

Definition central_em `{Univalence} (A : AbGroup) (n : nat)
  : Central K(A, n.+1).
Proof.
  rapply central_connected_hspace_hprop_pmap_loops.
  1: apply iscohhspace_em.
  napply istrunc_succ.
  rapply (contr_pmap_isconnected_inO n).
Defined.

Definition pbaut1_deloop_em `{Univalence} (A : AbGroup) (n : nat)
  : loops (pBAut1 K(A,n.+1)) <~>* K(A,n.+1).
Proof.
  napply (pequiv_loops_baut1 (A:=K(A, n.+1))).
  apply central_em.
Defined.
