# Topological algebra and infinite sums

This volume studies algebraic structures that carry a compatible topology, and the infinite sums and products that such a structure makes possible. A topological group is a group with a topology in which multiplication and inversion are continuous. Topological rings, fields and modules follow the same pattern. The real line, the circle $\mathbb{R}/\mathbb{Z}$, the $p$-adic numbers and the spaces of functions are examples. Each main theorem has a proof on paper and its Mathlib name.

Chapters 1 to 3 are topological algebra, Chapters 4 to 7 the theory of infinite sums and products, and Chapter 8 the topologies of absolute values and valuations.

- Chapter 1 defines topological monoids and groups. It proves that an open subgroup is closed, that a topological group which is $T_0$ is Hausdorff and regular, and that a quotient $G/H$ is Hausdorff exactly when $H$ is closed.
- Chapter 2 defines topological rings, division rings and modules, and the continuous linear maps `E →L[R] F` of Mathlib. It proves that a Hausdorff topological vector space of finite dimension over a complete field has only one such topology.
- Chapter 3 gives a commutative topological group its uniform structure, so that the Cauchy filters and the completion of Volume 13 apply. The completion of a topological group is a group, the completion of a ring is a ring, and $\mathbb{R}$ and $\mathbb{Q}_p$ are both completions of $\mathbb{Q}$.
- Chapter 4 defines the sum of a family $(f_i)_{i \in I}$ in a commutative topological group as Mathlib does: `HasSum f a` says that the finite partial sums tend to $a$ along the directed set of finite subsets of $I$. This sum does not depend on an order of $I$.
- Chapter 5 gives the criteria of summability: comparison of nonnegative terms, absolute convergence, the Cauchy criterion, the rearrangement theorem of Riemann, the Cauchy product, the criterion "the terms tend to $0$" in a nonarchimedean group, and sums of functions that converge uniformly.
- Chapter 6 studies the extended nonnegative reals $[0, \infty]$, written `ℝ≥0∞`, in which every family has a sum and the order of two summations can always be exchanged. This is the setting of measure theory.
- Chapter 7 studies infinite products `tprod`, the multiplicative form of `tsum`, and the relation between products and sums of logarithms.
- Chapter 8 studies absolute values on a field, the theorem that two absolute values define the same topology exactly when one is a power of the other, nonarchimedean groups and valued fields.

Two examples from the plan of the handbook mark the main point of the second half. The series $\sum_{n \ge 1} 1/n^2$ is summable in the sense of Mathlib, with sum $\pi^2/6$. The series $\sum_{n \ge 1} (-1)^{n+1}/n$ converges in the sense of a first course, to $\log 2$, but it is not summable in the sense of Mathlib, because its sum depends on the order of the terms. In $\mathbb{R}$ the summable families are exactly the absolutely summable ones. In $\mathbb{Q}_p$ a sequence is summable exactly when its terms tend to $0$.

The volume needs Volume 5 for groups, subgroups and quotients, Volume 6 for rings, ideals and fields, Volume 7 for modules and linear maps, and Volume 13 for topological spaces, filters, compactness, uniform spaces and the completion. Chapters 4 and 5 build on the real series of Volume 15, Chapter 1, and do not prove again the tests that it proves. The volume has no Lean companion yet, so the sections give no Lean exercises.
