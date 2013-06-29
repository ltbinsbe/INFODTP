
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Gt.
Require Import Arith.Wf_nat.
Require Import Recdef.
Require Import Tree.
Require Import SInc.
Require Import Minimum.

Open Scope nat_scope.

Import ListNotations.

(* Auxiliary definitions and lemmas *)
Definition max (a b : nat) :=
    match nat_compare a b with
    | Lt => b
    | _  => a
    end.

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

Definition build (xs : list tree) (P : xs <> []) : tree := 
  foldl1 join (fold_right (fun (a : tree) (xs : list tree) => step a xs (length xs)) nil xs) (fold_step_not_nil xs P).

Theorem build_is_min : forall (l : list tree) (t : tree) (P : l <> nil), 
  t = build l P -> minimum l t.
Proof.
  intros l t NNil BRes. unfold build in BRes. rewrite BRes. apply foldl1_is_min. 
    reflexivity.
Qed.
