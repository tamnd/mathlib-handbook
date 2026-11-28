# Nonempty, Unique and junk values

Some theorems need a type with an element, with exactly one element or with two different elements. This chapter gives the classes for these conditions and their relations. It then explains why every function in Mathlib is total, and lists the values at points such as $x / 0$ and $\log 0$.

A third section treats the types that record the absence of a value in place of a junk value: options, the partial values `Part α`, the partial functions `α →. β` and the erased values `Erased α`. A fourth section treats the small types `Bool`, `Ordering` and `SignType`, and the two-pointings, which are the data behind `Nontrivial`.
