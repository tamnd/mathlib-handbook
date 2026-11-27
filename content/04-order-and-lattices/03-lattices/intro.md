# Lattices

A lattice is a partial order in which any two elements have a least upper bound $a \sqcup b$ and a greatest lower bound $a \sqcap b$. The subsets of a set, the subspaces of a vector space, the subgroups of a group, the propositions and each linear order are lattices. This chapter has three sections.

Section 1 defines semilattices, lattices and bounded lattices, and it proves that a lattice is the same thing as a set with two operations that are commutative, associative and absorptive. It gives the standard examples, among them divisibility on $\mathbb{N}$ and the two small lattices $N_5$ and $M_3$. Section 2 studies distributive lattices, complements and Boolean algebras. It proves that complements are unique in a distributive lattice, derives the laws of De Morgan, and introduces Heyting algebras. Section 3 treats ideals and filters of an order, prime and maximal filters, and the ultrafilter lemma. It then explains the type `Filter α` of Mathlib as a lattice of families of sets with the reversed order.

The chapter needs the partial orders of Chapter 1, and Section 3 uses Zorn's lemma from Section 4 of Chapter 1. Chapter 4 extends the lattices of this chapter to complete lattices, in which each set has a supremum. Chapter 6 uses the lattice operations for Galois connections, and Volume 13 builds limits and topology on the filters of Section 3.
