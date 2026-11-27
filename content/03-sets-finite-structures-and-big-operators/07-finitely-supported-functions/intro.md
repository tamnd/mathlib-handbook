# Finitely supported functions

A function that is zero at all points except finitely many is a finitely supported function. Mathlib writes the type as `α →₀ M`. The polynomials, the factorization of a number, the multisets and the linear combinations of linear algebra are all made from it. The finite support is what makes these objects useful: a sum over all points of an infinite type has a meaning when all terms except finitely many are zero, and it is then a finite sum over the support.

Section 1 gives the type, the functions with one point `Finsupp.single`, the operations on the values, the rule of extensionality, the decomposition of each function into a finite sum of singles and the principle of induction. Section 2 gives the sum and the product over the support with their two main rules, the push forward `Finsupp.mapDomain` along a map of the points, and the identification of the multisets with the functions to $\mathbb{N}$.

The chapter needs the finsets of Chapter 3, the multisets of Chapter 2 and the finite sums of Chapter 6. It prepares the free modules and the coordinates in a basis of the volume on linear algebra, and the polynomials and monoid algebras of the volumes on rings.
