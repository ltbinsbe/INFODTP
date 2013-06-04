
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Arith.Wf_nat.
Require Import Recdef.

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


Definition join (x y : tree) : tree := Bin (max (ht x) (ht y) + 1) x y.

Fixpoint fold_step (input : list tree) (acc : list tree) : list tree :=
  match input with
  | nil => acc
  | i :: is => 
    match acc with
    | nil => fold_step is (i :: nil)
    | u :: nil => 
      match nat_compare (ht i) (ht u) with
      | Lt => fold_step is (i :: u :: nil)
      | _  => fold_step is (join u i :: nil)
      end
    | u :: v :: us => 
      match nat_compare (ht i) (ht u) with
      | Lt => fold_step is (i :: u :: v :: us)
      | _  => 
        match nat_compare (ht u) (ht v) with
        | Lt => fold_step is (fold_step (join i u :: nil) (v :: us))
        | _  => fold_step is (fold_step (i :: nil) (fold_step (join u v :: nil) us))
        end
      end
    end
  end.

(* TODO: problem: there is no fold1 is Coq (partial) *)
Definition build (xs : list tree) := fold_left join (fold_right step nil xs).

