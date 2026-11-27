# Lists and multisets

A finite collection in Mathlib starts as a list. A multiset is a list up to the order of its elements, and a finset is a multiset with no repeated element. This chapter builds the multisets and their operations, because the finsets of Chapter 3 and the sums of Chapter 6 rest on them.

The first section defines `Multiset α` as the quotient of `List α` by the permutation relation. It proves that the relation is an equivalence relation, that a function on lists that does not see the order passes to multisets, and that a multiset is determined by the multiplicities of its elements. So the quotient of lists and the finitely supported functions $\alpha \to \mathbb{N}$ give the same objects.

The second section gives the operations map, filter, sum, product and dedup, and the predicate Nodup. It proves the formula for the count in a map, shows why the sum of a multiset needs a commutative monoid, and ends with the bridge to finsets: a finset is a pair of a multiset and a proof that it is Nodup.

The chapter needs the quotient types and the equivalence relations of Volume 1 and of Chapter 1. Chapter 3 uses the dedup and the Nodup predicate to make finsets, Chapter 6 defines the sum over a finset as the sum of a multiset, and Chapter 7 turns a multiset into a finitely supported function.
