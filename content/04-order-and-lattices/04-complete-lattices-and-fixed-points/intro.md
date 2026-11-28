# Complete lattices and fixed points

In a complete lattice, each set has a supremum and an infimum, also the empty set and the set of all elements. The power set of a set, the closed interval $[0, 1]$, the extended natural numbers and the lattice of subgroups of a group are examples.

Section 1 defines complete lattices, indexed suprema and complete linear orders, and proves the basic properties of `sSup` and `sInf`: the universal property, monotonicity in the set, the supremum of a union, and the construction of the infimum from the supremum. It shows also two ordered types that are not complete, $\mathbb{N}$ and $\mathbb{Q} \cap [0, 1]$.

Section 2 proves the theorem of Knaster and Tarski: a monotone map on a complete lattice has a least and a greatest fixed point, and its fixed points form a complete lattice. The section gives the induction principle for the least fixed point, the Cantor-Schröder-Bernstein theorem as an application, and Kleene's theorem, which builds the least fixed point as the supremum of an iteration.

Section 3 describes the Mathlib interface for upper sets and lower sets: the predicates, the closure maps `upperClosure` and `lowerClosure`, the complete lattice of upper sets with the reverse inclusion, the principal upper sets, the products and the relative upper sets.

Section 4 describes the $\omega$-complete partial orders, the continuous maps between them with Kleene's fixed point theorem, the order on `Part α`, and the Scott continuous and order continuous maps.

Section 5 describes frames, coframes and complete Boolean algebras with their infinite distributive laws, the complete sublattices of a complete lattice, and the maps that preserve all suprema, all infima or both.

Section 6 describes the concepts of a relation between objects and attributes, which form a complete lattice, and the Dedekind-MacNeille completion of a partial order with its universal property.

Section 7 describes compact elements and compactly generated lattices, the characterisations of the ascending chain condition, the theorem that a modular compactly generated lattice is complemented exactly when it is atomistic, the complete partial orders, and the sets closed under directed or countable suprema.

The chapter needs partial orders, monotone maps and lattices from Chapters 1 to 3. Chapter 5 removes the hypothesis that every set has a supremum, for the real numbers. The Galois connections of Chapter 6 use complete lattices as their main examples, and the filters of a type, in a later volume, form a complete lattice.
