
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Gt.
Require Import Arith.Wf_nat.
Require Import Helpers.
Require Import Recdef.
Require Import Tree.

Open Scope nat_scope.

Import ListNotations.

Fixpoint step (t : tree) (xs : list tree) (n : nat) {struct n} : list tree :=
  match n with
  | 0 => [t]
  | S n2 =>
    match xs with
    | nil      => [t]
    | u :: nil =>
        match nat_compare (ht t) (ht u) with
        | Lt => t :: u :: nil
        | _  => (join t u) :: nil
        end
    | u :: v :: ts =>
        match nat_compare (ht t) (ht u) with
        | Lt => t :: u :: v :: ts
        | _  =>
            match nat_compare (ht t) (ht v) with
            | Lt => step (join t u) (v :: ts) (n2)
            | _  => step t (step (join u v) ts n2) (n2)
            end
        end
    end
  end.

Theorem step_not_nil : forall (ts : list tree) (t : tree),
  step t ts (length ts) <> [].
Proof.
  intros ts.
  (* match n *)  induction (length ts) as [|n2]. 
  (* | 0 => [t] *) simpl. intuition. inversion H.
  (* | S n2 => *) 
    (* match xs *) induction ts as [|u].
    (* | nil      => [t] *)  simpl. intuition. inversion H. 
    (* | u :: nil => *) induction ts as [|v].
        (* match nat_compare (ht t) (ht u) with *) intros t. remember (nat_compare (ht t) (ht u)) as R1. induction R1. 
        (* | Eq => (join t u) :: nil *) simpl. rewrite <- HeqR1. intuition. inversion H.
        (* | Lt => t :: u :: nil *) simpl. rewrite <- HeqR1. intuition. inversion H.
        (* | Gt => (join t u) :: nil *) simpl. rewrite <- HeqR1. intuition. inversion H.
        (* end *)
   (* | u :: v :: ts => *)
        (* match nat_compare (ht t) (ht u) with *) intros t. remember (nat_compare (ht t) (ht u)) as R2. induction R2.
        (* | Eq => *)
            (* match nat_compare (ht t) (ht v) with *) remember (nat_compare (ht t) (ht v)) as R3. induction R3.
            (* | Eq => step t (step (join u v) ts n2) (n2) *) simpl. rewrite <- HeqR2. rewrite <- HeqR3.
            (* | Lt => step (join t u) (v :: ts) (n2) *)
            (* | Gt => step t (step (join u v) ts n2) (n2) *)
            (* end *)
        (* | Lt => t :: u :: v :: ts *)
        (* | Gt => *)
            (* match nat_compare (ht t) (ht v) with *)
            (* | Lt => step (join t u) (v :: ts) (n2) *)
            (* | _  => step t (step (join u v) ts n2) (n2) *)
            (* end *)
        (* end *)
    (* end *)
  (* end. *)
Admitted.

Theorem step_join_le : forall (l : list tree) (t u : tree) (n : nat) (P : n >= length l),
  length (step (join t u) l n) <= length (u :: l).
Proof.
  induction n. intros Len. simpl. intuition.

  induction l. simpl. intuition.
    simpl. remember (nat_compare (max (ht t) 
