# Fiber bundles and vector bundles

A bundle over a space $B$ is a family of spaces $E_b$, one for each point $b \in B$, glued into one space, the total space. The tangent spaces of a manifold form the basic example. A fiber bundle is a bundle that looks like a product $U \times F$ over small open sets $U$ of the base. A vector bundle is a fiber bundle whose fibers are vector spaces and whose local product structures are linear on the fibers. This chapter builds the theory in three layers, in the order of Mathlib.

Section 1 is topology. It defines the total space of a family of fibers, trivializations, fiber bundles, and the construction of a fiber bundle from an open cover of the base and transition functions that satisfy the cocycle condition. It gives the trivial bundle, products, pullbacks and the Möbius band.

Section 2 adds linear structure. It defines topological vector bundles, the linear maps between fibers that the trivializations give, and the construction of a vector bundle from linear transition functions. It treats the trivial bundle, products, pullbacks, the bundle of continuous linear maps between two bundles, bundles of alternating maps, and continuous Riemannian metrics.

Section 3 adds smoothness. A vector bundle over a manifold is smooth if its transition functions are smooth. Its total space is then a manifold. The tangent bundle of a manifold is the main example: its transition functions are the derivatives of the changes of charts. The section proves that the tangent map of a $C^{n}$ map is $C^{n-1}$ and closes with a short account of Riemannian manifolds.

The chapter needs Chapters 2 and 3 and the derivative of Chapter 4, the topology of Volume 13, and the normed spaces of continuous linear maps of Volume 16. Chapter 6 uses smooth vector bundles to glue sections with partitions of unity. Chapter 8 studies smooth sections of the tangent bundle, which are the vector fields.
