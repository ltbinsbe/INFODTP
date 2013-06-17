Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Bool.Bool.

Open Scope list_scope.


Inductive QS : list nat -> Type :=
    | qs_nil  : QS nil
    | qs_cons : forall {x : nat} {xs : list nat},
                    QS (filter (fun y => ltb y x) xs) ->
                    QS (filter (fun y => negb (ltb y x)) xs) ->
                    QS (x :: xs).


Fixpoint quicksort (l : list nat)  (qs_acc : QS l) : list nat :=
    match qs_acc with
    | qs_nil  => nil
    | (qs_cons p ps lesser greater) =>
            quicksort (filter (fun y => ltb y p) ps) lesser
            ++ p :: nil
            ++ quicksort (filter (fun y => negb (ltb y p)) ps) greater
    end.

Definition list := 5::3::1::4::nil.

Theorem exTerm : QS list.
Proof.
  apply qs_cons. apply qs_cons. apply qs_cons. simpl. apply qs_nil. simpl. apply qs_nil. apply qs_cons; simpl; apply qs_nil.
  simpl. apply qs_nil.
Qed.

Eval simpl in filter (fun y => ltb y 5) list.
Eval simpl in quicksort list exTerm.