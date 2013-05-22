
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.

Open Scope nat_scope.


Definition max (a b : nat) :=
    match nat_compare a b with
    | Lt => b
    | _  => a
    end.


Inductive tree :=
    | Tip : tree
    | Bin : nat -> tree -> tree -> tree.

Definition ht (t : tree) :=
    match t with
    | Tip       => 0
    | Bin n _ _ => n
    end.


(* TODO: should increment height *)
Definition join (x y : tree) := Bin (max (ht x) (ht y)) x y.

Fixpoint step (t : tree) (xs : list tree) :=
    match xs with
    | nil      => t :: nil
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
            | Lt => step (join t u) (v :: ts)  (* non-structural recursion? *)
            | _  => step t (step (join u v) ts)  (* non-structural recursion *)
            end
        end
    end.


(* TODO: problem: there is no fold1 is Coq (partial) *)
Definition build (xs : list tree) := fold_left join (fold_right step nil xs).

