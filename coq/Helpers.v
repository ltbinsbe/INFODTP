Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Lt.

Open Scope nat_scope.


(* trivial helpers *)

Theorem eq_ge: forall (a b : nat), Eq = nat_compare a b -> a >= b.
Proof.
    intros a b Eq.
Admitted.

Theorem gt_ge: forall (a b : nat), Gt = nat_compare a b -> a >= b.
Proof.
Admitted.

Theorem not_eq_r: forall (n m : nat), n >= m -> ~ n < m.
Proof.
Admitted.

Theorem not_ge_r: forall (n m : nat), n < m -> ~ n >= m.
Proof.
Admitted.

Theorem eq_nmo_mo: forall (n m o : nat),
    Eq = nat_compare n m -> Eq = nat_compare n o -> Eq = nat_compare m o.
Proof.
    intros n m o H1 H2.
        assert (A1 : n = m). apply nat_compare_eq. symmetry. assumption.
        assert (A2 : n = o). apply nat_compare_eq. symmetry. assumption.
        rewrite A1 in H2.
        assumption.
Qed.

Theorem gt_nmo_mo : forall (n m o : nat),
    Eq = nat_compare n m -> Gt = nat_compare n o -> Gt = nat_compare m o.
Proof.
    intros n m o H1 H2.
        assert (A1 : n = m). apply nat_compare_eq. symmetry. assumption.
        assert (A2 : n > o). apply nat_compare_gt. symmetry. assumption.
        rewrite A1 in H2.
        assumption.
Qed.
