Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Gt.
Require Import Arith.Wf_nat.
Require Import Recdef.

Open Scope nat_scope.

Import ListNotations.


(* Auxiliary definitions and lemmas *)
Definition max (a b : nat) :=
    match nat_compare a b with
    | Lt => b
    | _  => a
    end.

Inductive tree :=
    | Tip :
        nat (* height of the tree it represents *)
        -> tree
    | Bin :
        nat (* height *)
        -> tree (* left child *)
        -> tree (* right child *)
        -> tree.


(* functions on trees *)
Definition ht (t : tree) :=
    match t with
    | Tip n     => n
    | Bin n _ _ => n
    end.

Definition join (x y : tree) : tree :=
    Bin (max (ht x) (ht y) + 1) x y.

Fixpoint flatten (t : tree) : list tree :=
    match t with
    | Tip n       => Tip n :: nil
    | Bin n t1 t2 => flatten t1 ++ flatten t2
    end.

Fixpoint siblings (t : tree) (a b : tree) : Prop :=
    match t with 
    | Tip _     => False
    | Bin _ x y => a = x /\ b = y \/ siblings x a b \/ siblings y a b
    end.

(* local minimum pair *)
Inductive lmp : tree -> tree -> list tree -> Set :=
    | lmp_pair :
        forall (a b : tree), lmp a b (a :: b :: nil)

    | lmp_threel :
        forall (a b x : tree),
            (ht a < ht b /\ ht x >= ht b) \/ ht b <= ht a  ->  lmp a b (x :: a :: b :: nil)

    | lmp_threer :
        forall (a b y : tree) (l : list tree),
            (ht a < ht b /\ ht b < ht y) \/ ht b <= ht a /\ ht a < ht y
            -> lmp a b (a :: b :: y :: l)

    | lmp_left :
        forall (a b x y : tree) (l l1 l2 : list tree),
            (l = l1 ++ (x :: a :: b :: y :: l2))
            -> ht b <= ht a
            -> ht b < ht y
            -> lmp a b l

    | lmp_right :
        forall (a b x y : tree) (l l1 l2 : list tree),
            (l = l1 ++ (x :: a :: b :: y :: l2))
            -> ht a < ht b
            -> ht b < ht y
            -> ht x >= ht b
            -> lmp a b l.

