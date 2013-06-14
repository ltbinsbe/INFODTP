Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Bool.Bool.

Open Scope list_scope.

Import ListNotations.

Inductive QSAcc : list nat -> Prop :=
    | qsAcc_nil  : QSAcc nil
    | qsAcc_cons : forall (x : nat) (xs : list nat),
                    QSAcc (filter (fun y => ltb y x) xs) ->
                    QSAcc (filter (fun y => negb (ltb y x)) xs) ->
                    QSAcc (x :: xs).


Fixpoint quicksort (l : list nat) (qsAcc : QSAcc l) : list nat :=
    match qsAcc, l with
    | qsAcc_nil,      _           => []
    | qsAcc_cons _ _ _ _, []      => []
    | qsAcc_cons _ _ l g, x :: xs =>
            quicksort (filter (fun y => ltb y x) xs) l ++ [x]
            ++ quicksort (filter (fun y => negb (ltb y x)) xs) g
    end.

