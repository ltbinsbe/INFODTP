INFODTP
=======

Verification of the algorithm described in "On building trees of minimum height" by Richard S. Bird, using Coq

## TODO
* Proof that by joining a lmp into a subtree we do not ruin our chances of building a tree of mimimum height (lemma 1)

_____________
* Proof that in an strictly increasing list, the rightmost pair is always an lmp (local minimum pair).
* Proof that in a non-strictly decreasing list, the leftmost pair is always an lmp
* Proof that in a list that is not non-strictly decreasing list there is always a pair (a, b) for which holds that a < b. This is a strictly increasing sequence.

________________
From this we can conclude that every sequence has an lmp (I'm not sure whether we actually need this proof)

* Proof that forall a, [a] is a strictly increasing list (trivial)
* Proof that forall a b, a < b => [a, b] is strictly increasing (trivial)
* Proof from induction on the above 2 base cases, that the result of the function step is an strictly increasing list. For this we need to prove that using join in the definition of step is safe:

_________________
For this we at least need:
* Proof that in any sequence xs ++ [a,b]: a >= b => (a,b) is an lmp (easy)
* Proof that in any sequence xs ++ [t, u, v] ++ ts: v > t >= u => (t, u) is an lmp (easy)
* Proof that in any sequence xs ++ [t, u, v] ++ ts: v <= t >= u => (u, v) is an lmp (easy)

________________
  From the above follows that foldl1 join creates a tree of minimum height

_________
## Possible problems
* step is not a fixpoint decreasing on one of its arguments, in combination with foldr it is however terminating. how to convince coq?
* there is no fold1, since it is an partial function. is this a problem for us?
* how to deal with 'end of list' (NIL), which can be interpreted as an item of the maximum height
* the main problem: how to prove that using join on lmps as arguments to a recursive call on step maintains the invariant (that step creates a strictly increasing list)
