Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Inductive Qs (x : nat) (l : list nat) : Prop :=
  | qs_nil  : Qs x nil
  | qs_cons : Qs x (filter (fun y => ltb y x) l) -> Qs x (filter (fun y => not (leb y x)) l) -> Qs x l.