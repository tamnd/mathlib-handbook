# Uniform structure and completion

A topological group carries more than a topology. Two points $x, y$ are close when $yx^{-1}$ is close to $1$, and this notion of closeness is the same at each point of the group. So a topological group has a uniform structure in the sense of Volume 13, Chapter 7, with Cauchy filters and a completion. This chapter builds this structure and uses it to complete groups, rings and fields.

Section 1 defines the right and left uniformities of a topological group and the class `IsUniformGroup` of Mathlib. It proves that a commutative topological group is a uniform group, that a continuous homomorphism is uniformly continuous, and that a discrete subgroup of a Hausdorff group is closed. The group of affine maps $x \mapsto ax + b$ shows that the two uniformities can differ. Section 2 completes a commutative group and a ring, and gives a criterion for the completion of a field to be a field. The real numbers and the $p$-adic numbers arise as completions of $\mathbb{Q}$ for two different field topologies, and a counterexample shows that the completion of a topological field can have zero divisors.

The chapter needs uniform spaces and their completion from Volume 13, Chapter 7, and Chapters 1 and 2 of this volume. The theory of sums in Chapters 4 to 7 uses the uniform structure for the Cauchy criterion, and Chapter 8 completes valued fields.
