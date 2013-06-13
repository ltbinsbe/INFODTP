Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Bool.Bool.

Open Scope list_scope.


Inductive QS : list nat -> Prop :=
    | qs_nil  : QS nil
    | qs_cons : forall (x : nat) (xs : list nat),
                    QS (filter (fun y => ltb y x) xs) ->
                    QS (filter (fun y => negb (ltb y x)) xs) ->
                    QS (x :: xs).


Fixpoint quicksort (qs_acc : QS) (l : list nat) : list nat :=
    match qs_acc, l with
    | qs_nil, _ => []
    | (qs_cons lesser greater), x :: xs =>
            quicksort lesser (filter (fun y => ltb y x) xs)
            ++ [x]
            ++ quicksort greater (filter (fun y => negb (ltb y x)) xs)
    end.
