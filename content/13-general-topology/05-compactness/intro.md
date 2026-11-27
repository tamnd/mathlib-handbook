# Compactness

A compact set is a set on which "local" facts become "global" facts: a continuous function is bounded and attains its bounds, a locally finite cover is finite, a pointwise bound is uniform. The classical definition says that each open cover has a finite subcover. Mathlib defines compactness with filters: each proper filter on the set has a cluster point in the set. The two definitions agree, and the filter definition gives the shortest proofs of the main theorems.

Section 1 proves that the two definitions agree and gives the first properties: closed subsets, continuous images, the closedness of compact sets in a Hausdorff space, the extreme value theorem, the normality of compact Hausdorff spaces and the homeomorphism criterion. Section 2 gives the filter proof that $[a, b]$ is compact and proves the Tychonoff theorem with ultrafilters. Section 3 studies compact metric spaces. It proves that compact, sequentially compact, and complete and totally bounded are equivalent, and the Heine-Borel theorem in $\mathbb{R}^n$.

The chapter needs Chapters 1 to 4. Section 3 uses the Cauchy sequences of Chapter 3.
