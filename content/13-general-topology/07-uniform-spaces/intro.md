# Uniform spaces and completion

A topology says when a point is close to a fixed point. It does not say when two points $x$ and $y$ are close to each other, independently of where they are. Uniform continuity and Cauchy sequences need this second kind of closeness. A metric gives it, but many spaces of analysis have it without a natural metric. A uniform space is a set with a filter of "closeness relations", and Mathlib defines Cauchy sequences, completeness and uniform continuity at this level.

Section 1 defines uniform spaces, uniform continuity, Cauchy filters and complete spaces. It proves the theorem of Heine on compact sets, the closedness of complete sets, and that $\mathbb{Q}$ is not complete. Section 2 constructs the completion of a uniform space and proves its universal property: a uniformly continuous map to a complete Hausdorff space extends uniquely from a dense subspace.

The chapter needs Chapters 1 to 5. The proofs use filters (Chapter 2) throughout, and the metric spaces of Chapter 3 are the main examples.
