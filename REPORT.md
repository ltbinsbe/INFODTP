% Verification Challenge, On Building Trees of Minimum Height
% Liewe Thomas van Binsbergen; João Paulo Pizani Flor;
% July 5th, 2013

# Accompanied files:
* Main.v (containing the main function and proof)
* SInc.v (containing the proves needed for 'fold_right step []')
* Minimum.v (containing the proves about 'foldl1 join')
* Tree.v (defining (functions on) trees)
* Helpers.v (defining some helper lemmas that come in handy in the other files)
* FoldStep.v (trying to define 'fold_right step []' as a single function)
* Function.v (trying to define 'step' using the 'Function' keyword)

# Introduction
The functional Pearl "On Building Trees of Minimum Height" by Richard S. Bird
solves the problem of building a tree out of a list of sub-trees, in such a 
way that the resulting tree has the input list as its frontier while being
minimum in the sense that any tree that we can build with this property has at
least the same height. Where the height of a tree is defined as the maximum
depth of any node node in the tree.

## Local minimum pairs
In order to do this the author uses the concept of 'local minimum pairs' (LMP).
It should be clear that when we are joining pairs together repeatedly, we 
always end up with a tree that has the input list as its frontier.

## Lemma 1 
The author proves a lemma (which we will call 'Lemma 1') that says that we can
safely join a local minimum pair in the process of building a tree. Where
safely means that we do not lose the opportunity of constructing a tree that
has a minimum height.
In other words, to find a tree of minimum height we can always select the
first lmp that we encounter in our input list and join them.
Since any list has always at least one lmp this process will halt in a single
tree that is of minimum height.

# The main definition
Now in order to do this in a very efficient (linear) way, the author provides
an algorithm that consists of two steps. One 'preprocessing' step that will
produce a list of trees in such a way that this list is strictly increasing
(using the height of the trees as cost function), and a producing step that
will transform this preprocessed list (which might already contain but a 
single element) into a single tree. Since we show that for any strictly
increasing list, the left-most pair is always an lmp, using 'foldl join' on
this list will create a tree of minimal height.

> build = foldl1 join . fold_right step []

In order to prove the correctness of this algorithm we will split up the work
in two phases (each on one end of the function composition operator): 
* First that 'fold_right step []' produces a strictly increasing list
* Second that 'foldl1 join', given a strictly increasing list, produces a 
tree of minimum height.

# Proving the minimum height
Proving that 'foldl1 join' produces a tree of minimum height, relies strongly
on so called 'Lemma 1'. We can take two approaches:
* Proving 'Lemma 1' is correct and that 'foldl1 join' always selects
an lmp, when given a strictly increasing list
* Proving that 'foldl1 join' produces a tree of minimal height, when given
a strictly increasing list 

Both approaches will be equally correct, however in the first approach the
link between 'Lemma 1' and 'foldl1 join' is not explicit (only implied).
This, however, makes it easier to prove, due to separation of concerns.

We assume that the definition of fold_left that we have imported is indeed 
correct.
The loop 'foldl1 join' will always use join, unless the input list contains
but a single element. From the definition of fold_left we know that 'fold join'
will always join the first pair of a list. All we have to show is that
every join operation performed by fold_left is 'safe' (invariant). 
Where a safe join means that the joined pair is a local minimum pair in the
given input list. Which comes down to showing that the left-most pair
in a strictly increasing list is always an lmp and that appending
the join of the left-most pair of a strictly increasing list preserves the
fact that the left-most pair of this list is an lmp even though a list
produced this way does not necessarily have to be strictly increasing anymore.

The proofs can be found in the file Minimum.v.v and are named s_inc_leftmost_lmp 
and join_preserves_leftmost_lmp.
'Lemma 1' can also be found at this location(TODO).

## Definitions
We have defined foldl1 (which is usually not total) using a predicate that
the input list is not empty, which allows us to ignore the usual base case
of foldl.

TODO:
* Prove 'foldl1 join => minimum' using 'Lemma 1' and a definition of 'minimum'
explicitly, in such a way that it can be used in the proof for function
'build'.

# Proving strictly increasingness
In order to prove that 'fold_right step []' produces strictly increasing list we
will have to do case analysis on the function step.

Function step acts very much like the list constructor 'cons', accept that
it analyzes the first elements of the list that it will add to by pattern 
matching.
When the newly element is smaller then the element currently on top of the list
we can just add it, otherwise we will join the new element and the head of the
list together and add this joined tree to the list instead (again using step).
If we try to use 'step' as a compositional operator for creating a decreasing
list (by giving it values in decreasing order), the result will simply be a 
single tree since join will be applied to all elements.

Using 'join' is only safe (looking at the properties that the entire
algorithm should have) when the joined pair is an lmp. And we can not 
guarantee this when only looking at the first element of the list.
We can, however, ensure this when we analyze the first two elements of the 
list.
 
In order to define the function step, which uses nested recursion and is 
therefor not clearly structural decreasing, we have tried several methods for
defining 'general recursion'. Including
* Using the keyword 'Function'
* Define 'fold_right step []' as a single function, since fold_right has a an
obvious decreasing argument.
* Using the Bove-Capretta method.
* Using Well-foundedness (TODO)
* Using a decreasing natural number and ensuring that it is always at least
as big as the length of the input list of which we know that is decreases.
We pattern match on this natural number and give a bogus result when it is 
zero. Meaning that if we want to prove that the function step as certain 
properties it can not return this bogus result.
This corresponds very much to an amortizing argument, giving the function
step a limit on the number of recursive calls it can use.

Using the keyword 'Function' seemed like a very good approach since we 
expected to be able to 'measure length input', where 'input' is the input list.
However, 'Function' can not be used to define functions with nested recursion
(a recursive call of which the result is an argument to a recursive call).
(The attempt can be found in Function.v)

The same problem we encountered when using the Bove-Capretta method. 
Similar to their example about QuickSort in their paper on 'General Recursion',
they provided an example of a function that has a nested recursive call.
Bove and Capretta described in their paper a problem about nested recursive
calls, namely that the predicate and function we want to define depend on each 
other mutually. This is exactly the problem we encountered while defining the 
function 'step'. The provided solution in the paper is based on work of 
Dybjer (2000), who introduced a method of defining a predicate and the 
definition it supports at the same time, even though they depend on each other.
This method does, however, not help us to define the function / predicate pair
in Coq.

Another unsuccessful approach was trying to define 'fold_right step []'  as a
single function (see FoldStep.v). The function is defined as to have two
list of trees as arguments. One being the 'worklist', while the other is the
'accumulated result'. When the worklist is empty we simply return the 
accumulated result, otherwise we add the first element to the worklist
to the accumulated result in such a way that it should match to definition of
step in the paper by Bird. This new accumulated result is then given as an 
argument to a recursive call of the function 'fold_step' together with the
decreased worklist.
When we reach the cases of the function step where we need a nested recursive
call, due to the nature of the definition of 'fold_step', we have to invent
a new worklist which contains only a single element.
This seems to be the problem of this definition, since we have no assurance
that the worklist of the current function call is actually larger then a 
single element. Which means that we can not be sure that the input list
is always structurally decreasing, since the old and the new worklist
can both be of length one.

A method that we did use successfully, was to use something very similar to an
amortizing argument. Namely we give the function step a natural number as
additional argument and make sure that this number is always decreased when
being passed on with every recursive call. In order to assure that this can
happen we need to pattern match on it and provide a function result when
the natural number reaches zero. The result we give in this case is arbitrary
and to prevent this result from ever being returned we must give the initial
call a value high enough natural number to begin with.
This number has to be related to the length of the input list and can not be
arbitrary since we always increase the size of the input list to such an 
extent that any arbitrary number is not enough. However, we can see, by 
analyzing the algorithm (the paper suggests an amortizing approach), that the
input list decreases at least by one in every recursive call. And since our
natural number will exactly decrease by one every recursive call, we can 
use the length of the input list as the initial value of this extra argument.

Well-founded recursion (TODO)

TODO: 
* Prove the fact that 'fold step []' produces (anything non-empty)
* Prove the fact that 'fold step []' produces a strictly increasing list
