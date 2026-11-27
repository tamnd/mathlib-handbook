# Vector fields and Lie groups

A vector field on a manifold $M$ chooses a tangent vector at each point. It is a section of the tangent bundle of Chapter 5, and a smooth vector field is a smooth section. Vector fields act on functions as derivations, and two of them have a bracket $[V, W]$, a new vector field that measures how far the two derivations fail to commute. The bracket is antisymmetric and satisfies the Jacobi identity, so the smooth vector fields form a Lie algebra.

Section 1 defines the bracket first on a normed space, where it is $DW \cdot V - DV \cdot W$, proves its identities from the symmetry of second derivatives, proves that it commutes with pullbacks by diffeomorphisms, and uses this to define it on a manifold through charts. The same method gives the exterior derivative of differential forms and the identity $d \circ d = 0$. The section ends with the other operations on sections that Mathlib has: point derivations, local frames, tensorial maps and covariant derivatives, up to the Levi-Civita connection.

Section 2 integrates a vector field. An integral curve is a curve whose velocity is the field. Existence and uniqueness come from the theorem of Picard and Lindelöf and from the estimate of Grönwall (Volume 17, Chapter 8), read in charts. The section then proves that curves defined for a uniform time extend to all of $\mathbb{R}$, and that a maximal integral curve is either injective or periodic.

Section 3 treats Lie groups: groups that are manifolds with smooth operations. It defines the left invariant vector fields, the Lie algebra of a Lie group as the tangent space at the identity with the bracket of left invariant fields, and the Lie algebra of left invariant derivations.

The chapter needs smooth maps and `mfderiv` (Chapters 3 and 4), vector bundles and their sections (Chapter 5), the theory of ordinary differential equations (Volume 17, Chapter 8) and alternating maps (Volume 8, Chapter 1). It closes the volume.
