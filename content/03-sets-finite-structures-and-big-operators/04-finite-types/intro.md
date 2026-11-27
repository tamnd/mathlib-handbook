# Finite types

A finite type is a type with a finset of all its elements. The class `Fintype` gives this finset as data, and `Fintype.card` counts it. Chapter 3 counted the finsets inside a type. This chapter counts whole types, and the types that are built from them.

Section 1 gives the class `Fintype`, proves that the card does not depend on the instance, and computes the card of the standard constructions: $|\alpha \times \beta| = |\alpha| |\beta|$, $|\alpha \oplus \beta| = |\alpha| + |\beta|$, $|\mathrm{Option}\ \alpha| = |\alpha| + 1$, $|\alpha \to \beta| = |\beta|^{|\alpha|}$ and $|\mathrm{Set}\ \alpha| = 2^{|\alpha|}$. It ends with the pigeonhole principle. Section 2 counts the maps with a property: the injections, with the falling factorial, and the permutations, with $n!$. It proves that a self-map of a finite type is injective exactly when it is surjective, and it gives the strong pigeonhole principle by a sum over the fibers of a map.

The chapter needs the finsets and their card from Chapter 3, and the equivalences of types from Volume 1. Chapter 5 replaces the data of `Fintype` by the proposition `Finite`, and Chapter 6 uses `Finset.univ` of a finite type for the sums $\sum_{i} f(i)$ over a whole type.
