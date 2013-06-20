
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
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
    | Tip : tree
    | Bin : nat -> tree -> tree -> tree.

Definition ht (t : tree) :=
    match t with
    | Tip       => 0
    | Bin n _ _ => n
    end.

Inductive s_inc : (list tree) -> Prop :=
  | s_inc_nil  : s_inc nil
  | s_inc_sin  : forall (x : tree), s_inc (x :: nil)
  | s_inc_two  : forall (x y : tree), ht x < ht y -> s_inc (x :: y :: nil)
  | s_inc_cons : forall (x y : tree) (ys : list tree), ht x < ht y /\ s_inc (y :: ys) -> s_inc (x :: y :: ys).

Example first : s_inc ((Bin 1 Tip Tip)::(Bin 2 Tip Tip)::nil).
Proof.
  apply s_inc_two with (x := Bin 1 Tip Tip) (y := Bin 2 Tip Tip). intuition.
Qed.

Example sec : s_inc ((Bin 1 Tip Tip)::(Bin 2 Tip Tip)::(Bin 3 Tip Tip)::(Bin 4 Tip Tip)::nil).
Proof.
  apply s_inc_cons. simpl. split; [|apply s_inc_cons; simpl; intuition; apply s_inc_two]; intuition.
Qed.

Inductive lmp : tree -> tree -> list tree -> Set :=
  | lmp_pair : forall (a b : tree), lmp a b (a :: b :: nil)
  | lmp_threel : forall (a b x : tree), 
                   (ht a < ht b /\ ht x >= ht b) \/ ht b <= ht a 
                   -> lmp a b (x :: a :: b :: nil)
  | lmp_threer : forall (a b y : tree), 
                   (ht a < ht b /\ ht b < ht y) \/ ht b <= ht a /\ ht a < ht y
                   -> lmp a b (a :: b :: y :: nil)
  | lmp_left : forall (a b x y : tree) (l l1 l2 : list tree),
              (l = l1 ++ (x :: a :: b :: y :: l2)) ->
              ht b <= ht a -> 
              ht b < ht y ->
              lmp a b l
  | lmp_right : forall (a b x y : tree) (l l1 l2 : list tree),
              (l = l1 ++ (x :: a :: b :: y :: l2)) ->
              ht a < ht b -> 
              ht b < ht y ->
              ht x >= ht b -> 
              lmp a b l.

Example lmp_first : lmp (Bin 2 Tip Tip) (Bin 3 Tip Tip) (Bin 4 Tip Tip :: Bin 2 Tip Tip :: Bin 3 Tip Tip :: Bin 5 Tip Tip :: nil).
Proof.
  apply lmp_right with (x := Bin 4 Tip Tip) (y := Bin 5 Tip Tip) (l1 := nil) (l2 := nil).
    reflexivity. 
    intuition.
    intuition.
    intuition.
Qed.

Theorem s_inc_two_lmp : forall (a b : tree) (l1 l2 : list tree), 
  l1 = (a :: b :: l2) -> s_inc l1 -> lmp a b l1.
Proof.
  intros a b l1 l2 H1 Inc.
Admitted.

(* Implementation of the algorithm itself *)
Definition join (x y : tree) : tree := Bin (max (ht x) (ht y) + 1) x y.

Inductive Step_acc : list tree -> Set :=
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


