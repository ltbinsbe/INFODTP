
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

Definition build (xs : list tree) (P : xs <> []) : tree := 
  foldl1 join (fold_right (fun (a : tree) (xs : list tree) => step a xs) nil xs) (fold_step_not_nil xs P).

Theorem build_is_min : forall (l : list tree) (t : tree) (P : l <> nil), 
  t = build l P -> minimum l t.
Proof.
  intros l t NNil BRes. unfold build in BRes. rewrite BRes. apply foldl1_is_min. 
    reflexivity.
Qed.

(* The example from the paper, which outputs the same result *)
Eval compute in build [Tip 4; Tip 2; Tip 3; Tip 5; Tip 1; Tip 4; Tip 6].
