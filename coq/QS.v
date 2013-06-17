Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Bool.Bool.

Open Scope list_scope.

Import ListNotations.

Inductive QSAcc : list nat -> Type :=
    | qsAcc_nil  : QSAcc nil
    | qsAcc_cons : forall (x : nat) (xs : list nat),
                    QSAcc (filter (fun y => ltb y x) xs) ->
                    QSAcc (filter (fun y => negb (ltb y x)) xs) ->
                    QSAcc (x :: xs).

Fixpoint quicksort (l : list nat)  (qs_acc : QSAcc l) : list nat :=
    match qs_acc with
    | qsAcc_nil  => nil
    | (qsAcc_cons p ps lesser greater) =>
            quicksort (filter (fun y => ltb y p) ps) lesser
            ++ p :: nil
            ++ quicksort (filter (fun y => negb (ltb y p)) ps) greater
    end.

Definition list := 5::3::1::4::nil.

Theorem exTerm : QSAcc list.
Proof.
  apply qsAcc_cons. apply qsAcc_cons. apply qsAcc_cons. simpl. apply qsAcc_nil. simpl. apply qsAcc_nil. apply qsAcc_cons; simpl; apply qsAcc_nil.
  simpl. apply qsAcc_nil.
Qed.

Eval simpl in filter (fun y => ltb y 5) list.

Definition res := quicksort list exTerm.
Eval simpl in res.

