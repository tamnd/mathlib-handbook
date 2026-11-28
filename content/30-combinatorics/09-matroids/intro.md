# Matroids

A matroid is a set with a family of independent subsets that satisfies the exchange property of linearly independent sets of vectors. The same axioms describe the forests of a graph, the transversals of a set system and the algebraically independent sets of a field extension. This chapter treats the matroid library of Mathlib. It starts from the axioms and then studies the dual matroid, circuits, closure, minors and rank.

Section 1 defines a matroid by its bases and by its independent sets, and it gives the constructions of the library that build a matroid from independence axioms. It defines the dual matroid, the free matroid, the loopy matroid and the matroid with one base, and it constructs direct sums of matroids.

Section 2 defines circuits, the minimal dependent sets, and proves the elimination axioms for them. It defines the closure of a set, flats and spanning sets, and it ends with loops, coloops and loopless matroids.

Section 3 studies maps of matroids along functions and the three operations of restriction, deletion and contraction. It defines minors and the order on matroids that these operations give.

Section 4 defines the rank function of a matroid, with values in the cardinals, in $\mathbb{N}_\infty$ and in $\mathbb{N}$ for matroids of finite rank. It proves the submodularity of the rank and relates the rank to bases and closure.

All sections need Volume 3, Chapters 1 and 5, and the maximal elements of Volume 4, Chapter 1. Section 2 also needs the closure operators of Volume 4, Chapter 6. The level is a first graduate course in combinatorics, and the standard references are Oxley, *Matroid Theory*, and Welsh, *Matroid Theory*.

In Mathlib, a matroid on a type `α` has a ground set `M.E : Set α`, and matroids can be infinite. Sizes of sets are values of `Set.encard` in $\mathbb{N}_\infty$. Many statements need a hypothesis `X ⊆ M.E`, and the tactic `aesop_mat` proves most of these hypotheses. The sections give each fact of finite matroid theory together with the form that the library proves for all matroids.
