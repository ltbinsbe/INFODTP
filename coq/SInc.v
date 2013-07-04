
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

Inductive s_inc : (list tree) -> Prop :=
  | s_inc_nil  : s_inc nil
  | s_inc_sin  : forall (x : tree), s_inc (x :: nil)
  | s_inc_two  : forall (x y : tree), ht x < ht y -> s_inc (x :: y :: nil)
  | s_inc_cons : forall (x y : tree) (ys : list tree), ht x < ht y /\ s_inc (y :: ys) -> s_inc (x :: y :: ys).

Fixpoint join_until_smaller (t : tree) (ts : list tree) :=
  match ts with
  | nil => [t]
  | x :: xs => 
    match nat_compare (ht t) (ht x) with
    | Eq => join_until_smaller (join t x) xs
    | Lt => t :: x :: xs
    | Gt => join_until_smaller (join t x) xs
    end
  end.

Theorem join_until_smaller_produces : forall (ts : list tree) (t : tree),
  join_until_smaller t ts <> [].
Proof.
  induction ts. simpl. intros t contra. inversion contra.
  intros t. remember (nat_compare (ht t) (ht a)) as R. destruct R.
    simpl. rewrite <- HeqR. apply IHts.
    simpl. rewrite <- HeqR. intros contra. inversion contra. 
    simpl. rewrite <- HeqR. apply IHts.
Qed.

Theorem join_until_smaller_inc : forall (ts : list tree) (t : tree),
  s_inc ts -> s_inc (join_until_smaller t ts).
Proof.
  induction ts. intros t s_inc_nil. simpl. apply s_inc_sin.
  intros t s_inc_ats. remember (nat_compare (ht t) (ht a)) as R. destruct R.
    simpl. rewrite <- HeqR. apply IHts. inversion s_inc_ats. apply s_inc_nil. apply s_inc_sin. destruct H0. assumption. 
    simpl. rewrite <- HeqR. apply s_inc_cons. split. apply nat_compare_lt. symmetry. assumption. assumption.
    simpl. rewrite <- HeqR. apply IHts. inversion s_inc_ats. apply s_inc_nil. apply s_inc_sin. destruct H0. assumption. 
Qed.

Fixpoint step (t : tree) (xs : list tree) : list tree :=
    match xs with
    | nil  => [t]
    | u :: vs =>
      match vs with 
        | nil => 
          match nat_compare (ht t) (ht u) with
          | Lt => t :: u :: nil
          | _  => (join t u) :: nil
          end
        | v :: ts =>
          match nat_compare (ht t) (ht u) with
          | Lt => t :: u :: v :: ts
          | _  =>
              match nat_compare (ht t) (ht v) with
              | Lt => step (join t u) vs
              | _  => join_until_smaller t (join_until_smaller (join u v) ts)
              end
          end
      end
    end.


Theorem step_not_nil : forall (xs : list tree) (t : tree),
  step t xs <> [].
Proof. 
    (* match xs with*) induction xs as [|u].
    (* | nil  => [t]*) simpl. intuition. inversion H.
    (* | u :: vs =>*)
      (* match vs with *) remember xs as vs. induction vs as [|v]; intros t. 
        (* | nil => *)
          (* match nat_compare (ht t) (ht u) with*) remember (nat_compare (ht t) (ht u)) as R1. destruct R1.
          (* | Eq => (join t u) :: nil*) simpl. rewrite <- HeqR1. intros contra. inversion contra.
          (* | Lt => t :: u :: nil*) simpl. rewrite <- HeqR1. intros contra. inversion contra.
          (* | Gt => (join t u) :: nil*) simpl. rewrite <- HeqR1. intros contra. inversion contra.
          (* end*)
        (* | v :: ts =>*)
         (* match nat_compare (ht t) (ht u) with *) remember (nat_compare (ht t) (ht u)) as R1. destruct R1.
         (* | Eq => *) 
              (* match nat_compare (ht t) (ht v) with *) remember (nat_compare (ht t) (ht v)) as R2. destruct R2.
              (* | Eq =>  join_until_smaller t (join u v :: ts) *) unfold step. rewrite <- HeqR1. rewrite <- HeqR2. apply join_until_smaller_produces.
              (* | Lt => step (join t u) vs *) rewrite Heqvs. simpl. rewrite <- Heqvs. rewrite <- HeqR1. rewrite <- HeqR2. apply IHxs.
              (* | Gt =>  join_until_smaller t (join u v :: ts) *) unfold step. rewrite <- HeqR1. rewrite <- HeqR2. apply join_until_smaller_produces.
              (* end *)
         (* | Lt => t :: u :: v :: ts *) simpl.  rewrite <- HeqR1. intros contra. inversion contra.
         (* | Gt => *) 
              (* match nat_compare (ht t) (ht v) with *) remember (nat_compare (ht t) (ht v)) as R2. destruct R2.
              (* | Eq =>  join_until_smaller t (join u v :: ts) *) unfold step. rewrite <- HeqR1. rewrite <- HeqR2. apply join_until_smaller_produces.
              (* | Lt => step (join t u) vs *)  rewrite Heqvs. simpl. rewrite <- Heqvs. rewrite <- HeqR1. rewrite <- HeqR2. apply IHxs.
              (* | Gt =>  join_until_smaller t (join u v :: ts) *) unfold step. rewrite <- HeqR1. rewrite <- HeqR2. apply join_until_smaller_produces.
              (* end *)
      (* end*)
    (* end.*)
Qed.

Theorem step_inc : forall (xs : list tree) (t : tree),
  s_inc xs -> s_inc (step t xs).
Proof. 
    (* match xs with*) induction xs as [|u].
    (* | nil  => [t]*) simpl. intuition. apply s_inc_sin.
    (* | u :: vs =>*)
      (* match vs with *) remember xs as vs. induction vs as [|v]; intros t H. 
        (* | nil => *)
          (* match nat_compare (ht t) (ht u) with*) remember (nat_compare (ht t) (ht u)) as R1. destruct R1.
          (* | Eq => (join t u) :: nil*) simpl. rewrite <- HeqR1. apply s_inc_sin.
          (* | Lt => t :: u :: nil*) simpl. rewrite <- HeqR1. apply s_inc_two. apply nat_compare_lt. symmetry. assumption.
          (* | Gt => (join t u) :: nil*) simpl. rewrite <- HeqR1. apply s_inc_sin.
          (* end*)
        (* | v :: ts =>*)
         (* match nat_compare (ht t) (ht u) with *) remember (nat_compare (ht t) (ht u)) as R1. destruct R1.
         (* | Eq => *) 
              (* match nat_compare (ht t) (ht v) with *) remember (nat_compare (ht t) (ht v)) as R2. destruct R2.
              (* | Eq =>  join_until_smaller t (join u v :: ts) *) inversion H. contradict H1. apply not_eq_r. apply eq_ge. apply eq_nmo_mo with (n := ht t); assumption. 
                                                                   inversion H1. contradict H4. apply not_eq_r. apply eq_ge. apply eq_nmo_mo with (n := ht t); assumption.
              (* | Lt => step (join t u) vs *) rewrite Heqvs. simpl. rewrite <- Heqvs. rewrite <- HeqR1. rewrite <- HeqR2. apply IHxs. inversion H. apply s_inc_sin. inversion H1. assumption.
              (* | Gt =>  join_until_smaller t (join u v :: ts) *) inversion H. contradict H1. apply not_eq_r. apply gt_ge. apply gt_nmo_mo with (n := ht t); assumption. 
                                                                   inversion H1. contradict H4. apply not_eq_r. apply gt_ge. apply gt_nmo_mo with (n := ht t); assumption. 
              (* end *)
         (* | Lt => t :: u :: v :: ts *) simpl.  rewrite <- HeqR1. apply s_inc_cons. split. apply nat_compare_lt. symmetry. assumption. assumption.
         (* | Gt => *) 
              (* match nat_compare (ht t) (ht v) with *) remember (nat_compare (ht t) (ht v)) as R2. destruct R2.
              (* | Eq =>  join_until_smaller t (join u v :: ts) *) simpl. rewrite <- HeqR1. rewrite <- HeqR2. remember (nat_compare (ht t) (max (ht u) (ht v) + 1)) as R3. destruct R3.
                                                                     apply join_until_smaller_inc. apply join_until_smaller_inc. inversion H. apply s_inc_nil. inversion H1. inversion H5. apply s_inc_nil. apply s_inc_sin. inversion H7. assumption.
                                                                     apply join_until_smaller_inc. apply join_until_smaller_inc. inversion H. apply s_inc_nil. inversion H1. inversion H5. apply s_inc_nil. apply s_inc_sin. inversion H7. assumption.
                                                                     apply join_until_smaller_inc. apply join_until_smaller_inc. inversion H. apply s_inc_nil. inversion H1. inversion H5. apply s_inc_nil. apply s_inc_sin. inversion H7. assumption.
              (* | Lt => step (join t u) vs *)  rewrite Heqvs. simpl. rewrite <- Heqvs. rewrite <- HeqR1. rewrite <- HeqR2. apply IHxs. inversion H. apply s_inc_sin. inversion H1. assumption. 
              (* | Gt =>  join_until_smaller t (join u v :: ts) *)  simpl. rewrite <- HeqR1. rewrite <- HeqR2. remember (nat_compare (ht t) (max (ht u) (ht v) + 1)) as R3. destruct R3.
                                                                     apply join_until_smaller_inc. apply join_until_smaller_inc. inversion H. apply s_inc_nil. inversion H1. inversion H5. apply s_inc_nil. apply s_inc_sin. inversion H7. assumption.
                                                                     apply join_until_smaller_inc. apply join_until_smaller_inc. inversion H. apply s_inc_nil. inversion H1. inversion H5. apply s_inc_nil. apply s_inc_sin. inversion H7. assumption.
                                                                     apply join_until_smaller_inc. apply join_until_smaller_inc. inversion H. apply s_inc_nil. inversion H1. inversion H5. apply s_inc_nil. apply s_inc_sin. inversion H7. assumption.
              (* end *)
      (* end*)
    (* end.*)
Qed.

Theorem fold_right_not_nil : forall (l : list tree),
  l <> [] -> fold_right (fun (a : tree) (xs : list tree) => step a xs) [] l <> [].
Proof.
  induction l. intros LNNil. simpl. assumption.
  (* step *) intros alNNil. simpl. apply step_not_nil.
Qed.

Theorem fold_step_not_nil : forall (l : list tree),
  l <> nil -> (fold_right (fun (a : tree) (xs : list tree) => step a xs) nil l) <> nil.
Proof.
  intros l NNil. apply fold_right_not_nil. assumption.
Qed.

Theorem fold_right_step : forall (l : list tree),
  s_inc (fold_right (fun (a : tree) (xs : list tree) => step a xs) nil l).
Proof.
  induction l as [|l']. simpl. apply s_inc_nil. simpl. apply step_inc. assumption.
Qed.
  
