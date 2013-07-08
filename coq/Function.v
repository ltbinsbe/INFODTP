Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Arith.Wf_nat.
Require Import Recdef.

Open Scope nat_scope.


Definition max (a b : nat) :=
    match nat_compare a b with
    | Lt => b
    | _  => a
    end.


Inductive tree :=
    | Tip : tree
    | Bin : nat -> tree -> tree -> tree.

Definition ht (t : tree) :=
    match t with
    | Tip       => 0
    | Bin n _ _ => n
    end.


Definition join (x y : tree) : tree := Bin (max (ht x) (ht y) + 1) x y.

Function step (t : tree) (xs : list tree) {measure length xs} : list tree :=
    match xs with
    | nil      => t :: nil
    | u :: nil =>
        match nat_compare (ht t) (ht u) with
        | Lt => t :: u :: nil
        | _  => (join t u) :: nil
        end
    | u :: v :: ts =>
        match nat_compare (ht t) (ht u) with
        | Lt => t :: u :: v :: ts
        | _  =>
            match nat_compare (ht t) (ht v) with
            | Lt => step (join t u) (v :: ts)
            | _  => (* step t *) (step (join u v) ts) 
                    (* step t (step (join u v) ts) is required, but not allowed *)
            end
        end
    end.
Proof.
    intros t xs u l v ts L X C1 C2. simpl. apply le_lt_SS. apply le_n.
    intros t xs u l v ts L X C1 C2. simpl. apply Lt.lt_n_Sn. 
    intros t xs u l v ts L X C1 C2. simpl. apply le_lt_SS. apply le_n.
    intros t xs u l v ts L X C1 C2. simpl. apply le_lt_SS. apply le_n. 
    intros t xs u l v ts L X C1 C2. simpl. apply Lt.lt_n_Sn.
    intros t xs u l v ts L X C1 C2. simpl. apply le_lt_SS. apply le_n. 
Qed.

