
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

Inductive Step_acc : list tree -> Prop :=
  | step_nil  : Step_acc nil
  | step_sin  : forall (u : tree),  Step_acc (u :: nil)
  | step_mul  : forall (u v : tree) (ts : list tree) (pts : Step_acc ts),
                       Step_acc (v :: ts) ->
                       Step_acc (step pts (join u v) ts) ->
                       Step_acc (u :: v :: ts).

Fixpoint step (acc : Step_acc) (t : tree) (xs : list tree) : list tree := 
  match acc, xs with
  | step_nil, nil      => t :: nil
  | step_sin, u :: nil => 
     match nat_compare (ht t) (ht u) with
     | Lt => t :: u :: nil
     | _  => (join t u) :: nil
     end
  | (step_mul pts pvts pstep), u :: v :: ts => 
        match nat_compare (ht t) (ht u) with
        | Lt => t :: u :: v :: ts
        | _  =>
            match nat_compare (ht t) (ht v) with
            | Lt => step pvts (join t u) (v :: ts)
            | _  => step pstep t (step pts (join u v) ts)
            end
        end
    end.

(* TODO: problem: there is no fold1 is Coq (partial) *)
Definition build (xs : list tree) := fold_left join (fold_right step nil xs).

