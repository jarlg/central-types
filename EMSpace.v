(** This material could go at the end of Homotopy.EMSpace.v. *)

From HoTT Require Import HoTT.

Require Import BAut1 Central.

Open Scope pointed_scope.

(** Lemma 2.27 [Buchholtz-van Doorn-Rijke, Corollary 4.3] *)
(** We take this as an axiom. Todo: prove it. *)
Global Instance istrunc_pmap {m n : trunc_index} (X Y : pType)
  `{!IsConnected m.+1 X} `{!IsTrunc (n +2+ m).+1 Y}
  : IsTrunc n.+1 (X ->* Y).
Admitted.

(** Prove special case of istrunc_pmap when n = -2 (or -1)? *)

Definition central_em `{Univalence} (A : AbGroup) (n : nat)
  : Central K(A, n.+1).
Proof.
  rapply central_connected_hspace_contr_pmap_loops.
  1: apply iscohhspace_em.
  apply contr_inhabited_hprop.
  2: exact pconst.
  rapply (istrunc_pmap (m:=n.-1) (n:=-2)).
  change (IsTrunc (n.-1).+1 (loops K( A, n.+1))).
  rewrite trunc_index_succ_pred.
  apply istrunc_loops.
  apply (@istrunc_em A n.+1).
Defined.

Definition pbaut1_deloop_em `{Univalence} (A : AbGroup) (n : nat)
  : loops (pBAut1 K(A,n.+1)) <~>* K(A,n.+1).
Proof.
  nrapply (pequiv_loops_baut1 (A:=K(A, n.+1))).
  apply central_em.
Defined.
