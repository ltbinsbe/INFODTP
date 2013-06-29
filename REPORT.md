% Verification Challenge, On Building Trees of Minimum Height
% Liewe Thomas van Binsbergen; João Paulo Pizani Flor;
% July 5th, 2013

# Introduction
The functional Pearl "On Building Trees of Minimum Height" by Richard S. Bird
solves the problem of building a tree out of a list of subtrees, in such a 
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

> build = foldl1 join . foldr step []

In order to prove the correctness of this algorithm we will split up the work
in two phases (each on one end of the function composition operator): 
* First that 'foldr step []' produces a strictly increasing list
* Second that 'foldl1 join', given a strictly increasing list, produces a 
tree of minimum height.

# Proving the minimum height
Proving that 'foldl1 join' produces a tree of minimum height, relies strongly
on so called 'Lemma 1'. We can take two approaches:
* Proving 'Lemma 1' is correct and that 'foldl1 join' always selects
an lmp, when given a strictly increasing list
* Proving that 'foldl1 join' produces a tree of minimal height, when given
a strictly increasing list 

Both approaces will be equally correct, however in the first approach the
link between 'Lemma 1' and 'foldl1 join' is not explicit (only implied).
This, however, makes it easier to prove, due to separation of concerns.

## Definitions
We have defined foldl1 (which is usually not total) using a predicate that
the input list is not empty, which allows us to ignore the usual base case
of foldl.

# Proving strictly increasingness
In order to prove that 'foldr step []' produces strictly increasing list we
will have to do case analysis on the function step.

Function step acts very much like the list constructor 'cons', accept that
it analyses the first elements of the list that it will add to.
In order to do this the function must pattern match on the list.
When the newly element is smaller then the element currently on top of the list
we can just add it, otherwise we will join the new element and the head of the
list together and add this joined tree to the list instead (again using step).
If we try to use 'step' as a compositional operator for creating a decreasing
list (by giving it values in decreasing order), the result will simply be a 
single tree since join will be applied to all elements.

Using 'join' is only safe (looking at the properties that the entire
algorithm should have) when the joined pair is an lmp. And we can not 
guarantee this when only looking at the first element of the list.
We can, however, ensure this when we analyse the first two elements of the 
list.

