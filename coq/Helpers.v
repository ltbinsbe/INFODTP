
Open Scope nat_scope.
Require Import Coq.Arith.Compare_dec.


(* trivial helpers *)

Theorem eq_ge : forall (a b : nat),
  Eq = nat_compare a b -> a >= b.
Proof.
Admitted.

Theorem gt_ge : forall (a b : nat),
  Gt = nat_compare a b -> a >= b.
Proof.
Admitted.

Theorem not_eq_r : forall (n m : nat),
  n >= m -> ~ n < m.
Proof.
Admitted.

Theorem not_ge_r : forall (n m : nat),
  n < m -> ~ n >= m.
Proof.
Admitted.
