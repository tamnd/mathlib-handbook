# Conditionally complete lattices

The real numbers are not a complete lattice, because the empty set and a set with no upper bound have no supremum in $\mathbb{R}$. A conditionally complete lattice asks for a supremum only of the sets that are nonempty and bounded above. The reals, the integers and the natural numbers are examples. The rationals are not. This chapter has two sections.

Section 1 defines conditionally complete lattices and linear orders, proves the properties of the supremum of a bounded set, and proves that $\mathbb{Q}$ is not conditionally complete. It shows how Mathlib gives a junk value to `sSup s` for each set `s`, and which hypotheses each lemma needs to make the value meaningful.

Section 2 treats the supremum of a family, `⨆ i, f i`, and the classes with a bottom element, such as $\mathbb{N}$ and $[0, \infty)$. It proves in order form three consequences of the completeness of $\mathbb{R}$: the behavior of a monotone bounded sequence, the nested interval theorem, and the supremum of a sum of two sets. It also compares $\sup g(S)$ with $g(\sup S)$ for a monotone map $g$.

The chapter needs the complete lattices of Chapter 4, since most proofs repeat a proof of Chapter 4 with the additional hypotheses. The limits and the continuity that use these results are in the volumes on topology and analysis.
