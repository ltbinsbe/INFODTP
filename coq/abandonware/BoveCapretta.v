
Require Import Coq.Strings.String.
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
    | Tip : nat (* height of the tree it represents *)
            -> tree
    | Bin : nat -> (* height *)
            tree -> (* left child *)
            tree ->  (* right child *)
            tree.

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

Inductive s_inc : (list tree) -> Prop :=
  | s_inc_nil  : s_inc nil
  | s_inc_sin  : forall (x : tree), s_inc (x :: nil)
  | s_inc_two  : forall (x y : tree), ht x < ht y -> s_inc (x :: y :: nil)
  | s_inc_cons : forall (x y : tree) (ys : list tree), ht x < ht y /\ s_inc (y :: ys) -> s_inc (x :: y :: ys).
(*
Example first : s_inc ((Bin 1)::(Bin 2)::nil).
Proof.
  apply s_inc_two with (x := Bin 1) (y := Bin 2). intuition.
Qed.

Example sec : s_inc ((Bin 1)::(Bin 2)::(Bin 3)::(Bin 4)::nil).
Proof.
  apply s_inc_cons. simpl. split; [|apply s_inc_cons; simpl; intuition; apply s_inc_two]; intuition.
Qed.
*)
Inductive lmp : tree -> tree -> list tree -> Set :=
  | lmp_pair : forall (a b : tree), lmp a b (a :: b :: nil)
  | lmp_threel : forall (a b x : tree), 
                   (ht a < ht b /\ ht x >= ht b) \/ ht b <= ht a 
                   -> lmp a b (x :: a :: b :: nil)
  | lmp_threer : forall (a b y : tree) (l : list tree), 
                   (ht a < ht b /\ ht b < ht y) \/ ht b <= ht a /\ ht a < ht y
                   -> lmp a b (a :: b :: y :: l)
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
(*
Example lmp_first : lmp (Bin 2) (Bin 3) (Bin 4 :: Bin 2 :: Bin 3 :: Bin 5 :: nil).
Proof.
  apply lmp_right with (x := Bin 4) (y := Bin 5) (l1 := nil) (l2 := nil).
    reflexivity. 
    intuition.
    intuition.
    intuition.
Qed.
*)
Theorem s_inc_two_lmp : forall (a b : tree) (l1 l2 : list tree), 
  l1 = (a :: b :: l2) -> s_inc l1 -> lmp a b l1.
Proof.
  intros a b l1 l2 Cons Inc. rewrite Cons. 
  destruct l2 as [|y]. apply lmp_pair. 
    (* step *) apply lmp_threer. left. 
    (* using the fact that the list is strictly increasing on both cases *)
      split; rewrite Cons in Inc; inversion Inc; inversion H0.
        assumption.
        inversion H4. assumption. inversion H6. assumption.
Qed.

Definition minimum (l : list tree) (t : tree) : Prop :=
  forall (t' : tree), flatten t' = l -> ht t <= ht t'.

(* Implementation of the algorithm itself *)
(*
Inductive Step_acc : list tree -> Set :=
  | step_nil  : Step_acc nil
  | step_sin  : forall (u : tree),  Step_acc (u :: nil)
  | step_mul  : forall (u v : tree) (ts : list tree) (pts : Step_acc ts),
                       Step_acc (v :: ts) ->
                       Step_acc (step pts (join u v) ts) ->
                       Step_acc (u :: v :: ts).
*)

Definition admit {T: Type} : T. Admitted.

Fixpoint step (t : tree) (xs : list tree) (n : nat) {struct n} : list tree :=
    match xs,n with
    | nil,_       => [t]
    | _, 0        => [t]
    | u :: nil, _ =>
        match nat_compare (ht t) (ht u) with
        | Lt => t :: u :: nil
        | _  => (join t u) :: nil
        end
    | u :: v :: ts, S n2 =>
        match nat_compare (ht t) (ht u) with
        | Lt => t :: u :: v :: ts
        | _  =>
            match nat_compare (ht t) (ht v) with
            | Lt => step (join t u) (v :: ts) (n2)
            | _  => step t (step (join u v) ts n2) (n2)
            end
        end
(*    | u :: v :: ts, _ => t :: nil *)
    end.


(*  match acc, xs with
Fixpoint step (t : tree) (xs : list tree) : list tree := 
  admit.
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
    end.*)

Theorem step_inc : forall (l : list tree) (t : tree),
  s_inc l -> s_inc (step t l (length l)).
Proof.
  induction l. simpl. intros t Sinc. apply s_inc_sin.
  (* step *) induction l. simpl. intros t sIncA. remember (nat_compare (ht t) (ht a)) as H. destruct H; [apply s_inc_sin | apply s_inc_two; apply nat_compare_lt; symmetry; assumption | apply s_inc_sin].
    (* step *) intros t sInc. unfold step. 
Admitted.

Theorem fold_right_step : forall (l : list tree),
  s_inc (fold_right (fun (a : tree) (xs : list tree) => step a xs (length xs)) nil l).
Proof.
  induction l as [|l']. simpl. apply s_inc_nil. simpl. apply step_inc. assumption.
Qed.

Theorem step_not_nil : forall (l : list tree) (t : tree),
  step t l (length l) <> [].
Proof.
  induction l. simpl. intros t contra. inversion contra. 
 (* step *) induction l. simpl. intros t. case (nat_compare (ht t) (ht a)). intros contra. inversion contra. intros contra. inversion contra. intros contra. inversion contra. 
   (* step *) intros t. unfold step. case (nat_compare (ht t) (ht a)).
   (* 1/3 : induction h, 2/3 trivial, 3/3 : induction h *)
Admitted.

Theorem fold_right_not_nil : forall (l : list tree),
  l <> [] -> fold_right (fun (a : tree) (xs : list tree) => step a xs (length xs)) [] l <> [].
Proof.
  induction l. intros LNNil. simpl. assumption.
  (* step *) intros alNNil. simpl. apply step_not_nil.
Qed.

Theorem fold_step_not_nil : forall (l : list tree),
  l <> nil -> (fold_right (fun (a : tree) (xs : list tree) => step a xs (length xs)) nil l) <> nil.
Proof.
  intros l NNil. apply fold_right_not_nil. assumption.
Qed.

Definition foldl1 (f : tree -> tree -> tree) (l : list tree) (P : l <> nil) : tree. 
  case l as [| x xs].
  contradiction P. reflexivity.
  apply fold_left with (B := tree). 
  exact f. exact xs. exact x.
Defined.
(*
Theorem foldl1test : [Tip 2; Tip 3] <> [].
Proof.
  intuition. inversion H.
Qed.


Eval program in (foldl1 join [Tip 2;Tip 3] (foldl1test)).
*)

Theorem foldl1_fold_left : forall (t : tree) (l1 : list tree) (P : l1 <> []),
  foldl1 join l1 P = fold_left join l1 t.
Proof.
  intros t l1 NNil. 
Admitted.

Theorem join_preserves : forall (t1 t2 t3 : tree) (l s: list tree) (sub : l = [t1;t2] ++ s),
  lmp t1 t2 l -> minimum l t3 -> minimum (join t1 t2 :: s) t3.
Proof.
Admitted.

Theorem Lemma1 : forall (l s : list tree) (a b : tree) (sub : l = [a;b] ++ s),
  lmp a b l -> exists (t : tree), siblings t a b -> minimum l t.
Proof.
Admitted.

Theorem foldl1_join : forall (t1 t2 : tree) (l1 l2 : list tree) (P: l1 <> []) (sub : l1 = [t1;t2] ++ l2),
  siblings t1 t2 (foldl1 join l1 P).
Proof.
Admitted.

Theorem join_pairs : forall (t1 t2 : tree) (l1 l2 : list tree) (P : l1 <> []) (sub : l1 = [t1;t2] ++ l2), 
  lmp t1 t2 l1 -> minimum l1 (foldl1 join l1 P).
Proof.
  intros t1 t2 l1 l2 P sub lmp.
Admitted.

Theorem flatten_pres_ht : forall (t hd : tree),
  flatten t = hd :: nil -> ht hd <= ht t.
Proof.
  intros t hd flthd. induction t. simpl in *. 
    (* trivial *)
    (* trivial from contradiction, flatten Bin cannot lead to a list of size 1 *)
Admitted.

Theorem foldl1_is_min : forall (l1 : list tree) (P : l1 <> []),
  s_inc l1 -> minimum l1 (foldl1 join l1 P).
Proof.
  intros l1 NNil Sinc. destruct l1. contradiction NNil. reflexivity.
  (* <> nil *) destruct l1. simpl. unfold minimum. intros t' flt'. apply flatten_pres_ht. assumption. 
    (* <> nil *) apply join_pairs with (t1 := t) (t2 := t0) (l2 := l1). reflexivity. apply s_inc_two_lmp with (l2 := l1). reflexivity. assumption.
Qed.

Definition build (xs : list tree) (P : xs <> []) : tree := 
  foldl1 join (fold_right (fun (a : tree) (xs : list tree) => step a xs (length xs)) nil xs) (fold_step_not_nil xs P).

Theorem build_is_min : forall (l : list tree) (t : tree) (P : l <> nil), 
  t = build l P -> minimum l t.
Proof.
  intros l t NNil BRes. unfold build in BRes. rewrite BRes. apply foldl1_is_min. 
    reflexivity.
    apply fold_right_step.
Qed.
