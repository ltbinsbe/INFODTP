
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Gt.
Require Import Arith.Wf_nat.
Require Import Recdef.
Require Import Tree.
Require Import SInc.

Open Scope nat_scope.

Import ListNotations.

Definition minimum (l : list tree) (t : tree) : Prop :=
  forall (t' : tree), flatten t' = l -> ht t <= ht t'.

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

Theorem foldl1_is_min : forall (l1 l2 : list tree) (P : l1 <> []) (H : l1 = (fold_right (fun  (a : tree) (xs : list tree) => step a xs (length xs)) [] l2)),
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