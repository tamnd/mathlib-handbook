# Intervals

An interval is the set of the elements between two bounds. Intervals make sense in each preorder, not only in the real numbers, and Mathlib has one name for each of the nine kinds: `Set.Icc a b` for the closed interval $[a, b]$, `Set.Ico a b` for $[a, b)$, `Set.Ioi a` for the ray $(a, \infty)$, and so on.

The first section defines the intervals and proves the rules that a computation with intervals uses: when an interval is empty, when one interval is a subset of another, and how intervals meet and join. The second section studies the sets that contain each interval between two of their points, the order-connected sets, and proves that in the real numbers these are exactly the intervals. It also defines the unordered interval and the finite intervals `Finset.Icc` of a locally finite order, with the formulas for their numbers of elements.

The chapter needs the preorders, partial orders and linear orders of Chapter 1, and the sets of Volume 1. Chapter 8 uses the intervals to describe the bounds on an absolute value, and the volumes on topology and analysis use them for the connected subsets of the real line.
