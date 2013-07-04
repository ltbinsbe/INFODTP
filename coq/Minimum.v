
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Gt.
Require Import Arith.Wf_nat.
Require Import Recdef.
Require Import Helpers.
Require Import Tree.
Require Import SInc.

Open Scope nat_scope.

Import ListNotations.

(**************************************************)
(* Key definitions *)

Definition minimum (l : list tree) (t : tree) : Prop :=
  forall (t' : tree), flatten t' = l -> ht t <= ht t'.

Theorem Lemma1 : forall (l s : list tree) (a b : tree) (sub : l = [a;b] ++ s),
  lmp a b l -> exists (t : tree), siblings t a b -> minimum l t.
Proof.
Admitted.


(**************************************************)
(* Proving 'foldl1 join' gives minimum implicitly *)

(* proving that the invariant holds when 'foldl1 join' is called,
   assuming that 'fold_right step []' produces a strictly increasing list
*)

Theorem s_inc_leftmost_lmp : forall (a b : tree) (l1 l2 : list tree), 
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

(* proving the the invariant that adding the join of a left-most pair in a strictly increasing list
   preserves the fact that the left-most pair is still a local minimum pair.
   assuming that foldl_left acts as it should 
*)

Theorem join_preservse_leftmost_lmp : forall (t u v : tree) (ts : list tree),
  s_inc (t :: u :: v :: ts) -> lmp (join t u) v (join t u :: v :: ts).
Proof.
 intros t u v ts Sinc. assert (H : ht (join t u) <= ht v). 
   (* ass 1 *) simpl. replace (max (ht t) (ht u) + 1) with (S (max (ht t) (ht u))). apply lt_le_S. unfold max. remember (nat_compare (ht t) (ht u)) as R. destruct R.
     inversion Sinc. inversion H0.  inversion H4. apply lt_trans with (m := ht u).  assumption. assumption.  apply lt_trans with (m := ht u). assumption. inversion H6. assumption. 
     inversion Sinc. inversion H0. inversion H4.  assumption.  inversion H6. assumption. 
     inversion Sinc. inversion H0.  inversion H4. apply lt_trans with (m := ht u).  assumption. assumption.  apply lt_trans with (m := ht u). assumption. inversion H6. assumption.
   (* replace *) symmetry. apply NPeano.Nat.add_1_r.
   induction ts. apply lmp_pair. 
     (* step *) remember (nat_compare (ht (join t u)) (ht v)) as R1. destruct R1.
       (* R1 = Eq *)apply lmp_threer. right. split. apply eq_ge. assumption. 
                                       inversion Sinc. inversion H1. inversion H5. inversion H7. inversion H11. replace (ht (join t u)) with (ht v). assumption. symmetry. apply nat_compare_eq. symmetry. assumption. 
                                                                                                                replace (ht (join t u)) with (ht v). inversion H13. assumption. symmetry. apply nat_compare_eq. symmetry. assumption.
       (* R1 = LT *)apply lmp_threer. left. split. apply nat_compare_lt. symmetry. assumption. inversion Sinc. inversion H1.  inversion H5. inversion H7. inversion H11. assumption. inversion H13. assumption.
       (* R1 = GT *)apply lmp_threer. contradict H. apply lt_not_le. apply nat_compare_gt. symmetry. assumption.
Qed.

(* Now given that Lemma1 proves that joining a lmp in a list of trees preserves the fact that we are on the way
   of building a tree of minimum height, foldl1 creates a tree of minimum height *)


(**************************************************)
(* Proving 'foldl1 join' gives minimum explicitly *)

Definition foldl1 (f : tree -> tree -> tree) (l : list tree) (P : l <> nil) : tree. 
  case l as [| x xs].
  contradiction P. reflexivity.
  apply fold_left with (B := tree). 
  exact f. exact xs. exact x.
Defined.

Theorem foldl1_fold_left : forall (t : tree) (l1 : list tree) (P : l1 <> []),
  foldl1 join l1 P = fold_left join l1 t.
Proof.
  intros t l1 NNil. 
Admitted.

Theorem join_preserves : forall (t1 t2 t3 : tree) (l s: list tree) (sub : l = [t1;t2] ++ s),
  lmp t1 t2 l -> minimum l t3 -> minimum (join t1 t2 :: s) t3.
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

Theorem foldl1_is_min : forall (l1 l2 : list tree) (P : l1 <> []) (H : l1 = (fold_right (fun  (a : tree) (xs : list tree) => step a xs) [] l2)),
  minimum l2 (foldl1 join l1 P).
Proof.
  intros l1 l2 P l1Is. destruct l1. contradiction P. reflexivity.
  (* <> nil *) destruct l1. simpl. unfold minimum. intros t' flt'. apply flatten_pres_ht.
Admitted.
(*
  intros l1 NNil Sinc. destruct l1. contradiction NNil. reflexivity.
  (* <> nil *) destruct l1. simpl. unfold minimum. intros t' flt'. apply flatten_pres_ht. assumption. 
    (* <> nil *) apply join_pairs with (t1 := t) (t2 := t0) (l2 := l1). reflexivity. apply s_inc_two_lmp with (l2 := l1). reflexivity. assumption.
Qed.
*)

