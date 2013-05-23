INFODTP
=======

Verification of the algorithm described in "On building trees of minimum height" by Richard S. Bird, using Coq

TODO
----

### Prove Lemma 1:

* **Given that** ![pair](http://latex.codecogs.com/svg.latex?%28t_%7Bi%7D%2C%20t_%7Bi&plus;1%7D%29)
  is a lmp (local minimum pair) in a sequence of trees
  ![bounds](http://latex.codecogs.com/svg.latex?h_%7Bi%7D%20%3A%20%281%20%5Cleq%20i%20%5Cleq%20N%29)
* **Then** there is a tree T of **minimum height** in which
  ![pair](http://latex.codecogs.com/svg.latex?%28t_%7Bi%7D%2C%20t_%7Bi&plus;1%7D%29) are siblings
    a. Given list [..,x, a, b, y, ..] a => b ^ y > a  -> (a, b) lmp
    b. Given list [..,x, a, b, y, ..] a < b  ^ b < y ^ x >= a -> (a, b) lmp
### Prove auxiliary facts about lmp (local minimum pair):

1. Proof that in an strictly increasing list, the leftmost pair is always an lmp.
2. Proof that in a non-strictly decreasing list, the rightmost pair is always an lmp.
3. Proof that in a list that is not non-strictly decreasing there is always a pair (a, b)
   for which it holds that ![alessb](http://latex.codecogs.com/svg.latex?a%3Cb).
   This is a strictly increasing sequence.

From these facts we should be able to conclude that every sequence has an lmp
(Thomas: I'm not sure whether we actually need this proof)

### Invariants about order on lists:

1. Proof that ![FAa](http://latex.codecogs.com/svg.latex?%5Cforall%7Ba%7D) [a] is a
   strictly increasing list (trivial)
2. Proof that ![FAaaltb](http://latex.codecogs.com/svg.latex?%5Cforall%7Ba%7D%20%3A%20a%20%3C%20b)
   implies that [a, b] is strictly increasing (trivial)
3. From induction on the above 2 base cases, prove that the result of the function step is
   an strictly increasing list.
     * For this we need to prove that using join in the definition of step is safe. Needs:
       - Proof that in any sequence xs ++ [a,b]:
         ![ageb](http://latex.codecogs.com/svg.latex?a%20%5Cgeq%20b) implies that (a,b) is an lmp.
         (follows from 1.a)
       - Proof that in any sequence xs ++ [t, u, v] ++ ts:
         ![vgttgequ](http://latex.codecogs.com/svg.latex?v%20%3E%20t%20%5Cgeq%20u)
         implies that (t, u) is an lmp.
         (follows from 1.a)
       - Proof that in any sequence 
            xs ++ [t, u, v] ++ ts: [u,v] ++ ts is increasing & t >= v ^ t >= u => (u, v) is an lmp 
         (follows from 1.b)

From the above follows that foldl1 join creates a tree of minimum height.


Possible problems
-----------------

* Step is not a fixpoint decreasing on one of its arguments, in combination with foldr it is
  however terminating. How to convince coq?
* There is no fold1, since it is an partial function. is this a problem for us?
* How to deal with 'end of list' (NIL), which can be interpreted as an item of the maximum height.
* The main problem: how to prove that using join on lmps as arguments to a recursive call on step
  maintains the invariant (that step creates a strictly increasing list).
