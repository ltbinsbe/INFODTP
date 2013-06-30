
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
    end.

Inductive s_inc : (list tree) -> Prop :=
  | s_inc_nil  : s_inc nil
  | s_inc_sin  : forall (x : tree), s_inc (x :: nil)
  | s_inc_two  : forall (x y : tree), ht x < ht y -> s_inc (x :: y :: nil)
  | s_inc_cons : forall (x y : tree) (ys : list tree), ht x < ht y /\ s_inc (y :: ys) -> s_inc (x :: y :: ys).



Theorem step_jointuv : forall (t u v : tree) (ts : list tree) (H3 : nat),
  ht t >= ht u -> ht t < ht v -> H3 = (length (v :: ts)) -> step (join t u) (v :: ts) H3 = join t u :: v :: ts.
Proof.
Admitted.

Theorem s_trans : forall (n m : nat),
  S n = S m -> n = m.
Proof.
Admitted.

Theorem step_bigger : forall (t u : tree) (ts : list tree),
  s_inc (u :: ts) -> ht t >= ht u -> s_inc (step t (u :: ts) (length (u :: ts))). 
Proof.
 intros t u ts Sinc t_ge_u.

Theorem tuvts_step : forall (t u v : tree) (ts : list tree),
  ht t < ht u -> step t (u :: v :: ts) (length (u :: v :: ts)) = t :: u :: v :: ts.
Proof.
  intros t u v ts t_lt_u.
  simpl. remember (nat_compare (ht t) (ht u)) as H. destruct H. 
    Focus 2. reflexivity. 
    contradict t_lt_u. apply not_eq_r. apply eq_ge. assumption.
    contradict t_lt_u. apply not_eq_r. apply gt_ge. assumption.
Qed.

Theorem tuvts_inc : forall (t u v : tree) (ts : list tree),
  s_inc (u :: v :: ts) -> ht t < ht u -> s_inc (t :: u :: v :: ts).
Proof.
intros t u v ts Sinc ht1. apply s_inc_cons. split.
  assumption.
  apply s_inc_cons. split.
    inversion Sinc. assumption. inversion H0. assumption.
    inversion Sinc. apply s_inc_sin. inversion H0. assumption.
Qed.

Theorem jtuvts_step : forall (t u v : tree) (ts : list tree),
  ht t >= ht u -> ht t < ht v -> step t (u :: v :: ts) (length (u :: v :: ts)) = join t u :: v :: ts.
Proof.
  intros t u v ts t_ge_u t_lt_v.
  remember (length (u :: v :: ts)) as H3. destruct H3. simpl in HeqH3. inversion HeqH3. simpl.
    remember (nat_compare (ht t) (ht u)) as H. destruct H. simpl.
      remember (nat_compare (ht t) (ht v)) as H2. destruct H2.
        contradict t_lt_v. apply not_eq_r. apply eq_ge. assumption. 
        Focus 2. contradict t_lt_v. apply not_eq_r. apply gt_ge. assumption.
        Focus 2. contradict t_ge_u. apply not_ge_r. apply nat_compare_lt. symmetry. assumption.
        Focus 2. remember (nat_compare (ht t) (ht v)) as H2. destruct H2.
          contradict t_lt_v. apply not_eq_r. apply eq_ge. assumption.
          Focus 2. contradict t_lt_v. apply not_eq_r. apply gt_ge. assumption.
          apply step_jointuv. assumption. assumption. simpl in *. apply s_trans. assumption.
        apply step_jointuv. assumption. assumption. simpl in *. apply s_trans. assumption.
Qed.

Theorem jtjuvts_step : forall (t u v : tree) (ts : list tree),
  ht t >= ht u -> ht t >= ht v -> step t (u :: v :: ts) (length (u :: v :: ts)) = join t (join u v) :: ts.
Proof.
Admitted.

Theorem jtuvts_inc2 : forall (t u v : tree) (ts : list tree),
  s_inc (u :: v :: ts) -> ht t >= ht u -> ht t < ht v -> ht (join t u) >= ht v -> s_inc (join (join t u) v :: ts).
Proof.
Admitted.

Theorem jtuvts_inc3 : forall (t u v : tree) (ts : list tree),
  s_inc (u :: v :: ts) -> ht t >= ht u -> ht t < ht v -> ht (join t u) < ht v -> s_inc (join t u :: v :: ts).
Proof.
  intros t u v ts Sinc t_ge_u t_lt_v jtu_lt_v. remember (nat_compare (ht (join t u)) (ht v)) as H. destruct H.
    Focus 2. apply s_inc_cons. split.
      assumption. 
      inversion Sinc. apply s_inc_sin. destruct H0. assumption.
    contradict jtu_lt_v. apply not_eq_r. apply eq_ge. assumption.
    contradict jtu_lt_v. apply not_eq_r. apply gt_ge. assumption.
Qed.

Theorem jtuvts_inc1 : forall (t u v : tree) (ts : list tree),
  s_inc (u :: v :: ts) -> ht t >= ht u -> ht t < ht v -> s_inc (step (join t u) (v :: ts) (length (v :: ts))).
Proof.
  intros t u v ts Sinc t_ge_u t_lt_v. remember (nat_compare (ht (join t u)) (ht v)) as H. destruct H.
    induction ts. simpl. remember (nat_compare (max (ht t) (ht u) + 1) (ht v)) as H. destruct H.
      apply s_inc_sin. apply s_inc_two. apply nat_compare_lt. symmetry. assumption. apply s_inc_sin.
      (* step *) rewrite jtjuvts_step.
        apply s_inc_cons.
      
Admitted.

Theorem jtjuvts_inc : forall (t u v : tree) (ts : list tree),
  s_inc (u :: v :: ts) -> ht t >= ht u -> ht t >= ht v -> s_inc (join t (join u v) :: ts).
Proof.
Admitted.

Theorem step_inc : forall (l : list tree) (t : tree),
  s_inc l -> s_inc (step t l (length l)).
Proof.
  induction l. simpl. intros t Sinc. apply s_inc_sin.
  (* step *) induction l. simpl. intros t sIncA. remember (nat_compare (ht t) (ht a)) as H. destruct H; [apply s_inc_sin | apply s_inc_two; apply nat_compare_lt; symmetry; assumption | apply s_inc_sin].
    (* step *) intros t sInc. remember (nat_compare (ht t) (ht a)) as H. destruct H.
        remember (nat_compare (ht t) (ht a0)) as H2. destruct H2.
          rewrite jtjuvts_step. apply jtjuvts_inc. assumption. apply eq_ge. assumption. 
                                                 apply eq_ge. assumption.
                                                 apply eq_ge. assumption.
                                                 apply eq_ge. assumption.
          rewrite jtuvts_step. apply jtuvts_inc. assumption. apply eq_ge. assumption.
                                                 apply nat_compare_lt. symmetry. assumption.
                                                 apply eq_ge. assumption.
                                                 apply nat_compare_lt. symmetry. assumption.
          rewrite jtjuvts_step. apply jtjuvts_inc. assumption. apply eq_ge. assumption.
                                                 apply gt_ge. assumption.
                                                 apply eq_ge. assumption.
                                                 apply gt_ge. assumption.
        remember (nat_compare (ht t) (ht a0)) as H2. destruct H2.
          rewrite tuvts_step. apply tuvts_inc. assumption. apply nat_compare_lt. symmetry. assumption.
                                                 apply nat_compare_lt. symmetry. assumption. 
          rewrite tuvts_step. apply tuvts_inc. assumption. apply nat_compare_lt. symmetry. assumption.  
                                                 apply nat_compare_lt. symmetry. assumption. 
          rewrite tuvts_step. apply tuvts_inc. assumption. apply nat_compare_lt. symmetry. assumption.  
                                                 apply nat_compare_lt. symmetry. assumption. 
        remember (nat_compare (ht t) (ht a0)) as H2. destruct H2.
          rewrite jtjuvts_step. apply jtjuvts_inc. assumption. apply gt_ge. assumption. 
                                                 apply eq_ge. assumption.
                                                 apply gt_ge. assumption.
                                                 apply eq_ge. assumption.
          rewrite jtuvts_step. apply jtuvts_inc. assumption. apply gt_ge. assumption.
                                                 apply nat_compare_lt. symmetry. assumption.
                                                 apply gt_ge. assumption.
                                                 apply nat_compare_lt. symmetry. assumption.
          rewrite jtjuvts_step. apply jtjuvts_inc. assumption. apply gt_ge. assumption.
                                                 apply gt_ge. assumption.
                                                 apply gt_ge. assumption.
                                                 apply gt_ge. assumption.
Qed.


Theorem step_not_nil : forall (l : list tree) (t : tree),
  step t l (length l) <> [].
Proof.
  induction l. simpl. intros t contra. inversion contra. 
 (* step *) induction l. simpl. intros t. case (nat_compare (ht t) (ht a)). intros contra. inversion contra. intros contra. inversion contra. intros contra. inversion contra. 
   (* step *) intros t. remember (nat_compare (ht t) (ht a)) as H. destruct H.
        remember (nat_compare (ht t) (ht a0)) as H2. destruct H2.
          rewrite jtjuvts_step. intuition. inversion H. apply eq_ge. assumption. 
                                                 apply eq_ge. assumption.
          rewrite jtuvts_step. intuition. inversion H. apply eq_ge. assumption.
                                                 apply nat_compare_lt. symmetry. assumption.
          rewrite jtjuvts_step. intuition. inversion H. apply eq_ge. assumption.
                                                 apply gt_ge. assumption.
        remember (nat_compare (ht t) (ht a0)) as H2. destruct H2.
          rewrite tuvts_step. intuition. inversion H. apply nat_compare_lt. symmetry. assumption.
          rewrite tuvts_step. intuition. inversion H. apply nat_compare_lt. symmetry. assumption. 
          rewrite tuvts_step. intuition. inversion H. apply nat_compare_lt. symmetry. assumption. 
        remember (nat_compare (ht t) (ht a0)) as H2. destruct H2.
          rewrite jtjuvts_step. intuition. inversion H. apply gt_ge. assumption. 
                                                 apply eq_ge. assumption.
          rewrite jtuvts_step. intuition. inversion H. apply gt_ge. assumption.
                                                 apply nat_compare_lt. symmetry. assumption.
          rewrite jtjuvts_step. intuition. inversion H. apply gt_ge. assumption.
                                                 apply gt_ge. assumption.
Qed.

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

Theorem fold_right_step : forall (l : list tree),
  s_inc (fold_right (fun (a : tree) (xs : list tree) => step a xs (length xs)) nil l).
Proof.
  induction l as [|l']. simpl. apply s_inc_nil. simpl. apply step_inc. assumption.
Qed.
