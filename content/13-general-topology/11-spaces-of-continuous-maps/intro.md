# Spaces of continuous maps

Chapter 1 studies one continuous map at a time. This chapter studies the set of all continuous maps from a space $X$ to a space $Y$ as a new object. Mathlib bundles a continuous map as a structure `C(X, Y)`: a function together with a proof of its continuity. The type `C(X, Y)` carries a topology, the compact-open topology, and it inherits the algebra and the order of $Y$. When $Y$ is a normed space, the bounded continuous maps form a normed space with the supremum norm, and the theorems of Weierstrass and Stone describe its dense subalgebras.

Section 1 defines the bundled maps `C(X, Y)`, their basic constructions, the compact-open topology, and the supremum metric on `C(X, Y)` for a compact space $X$. Section 2 gives the algebraic, order and star structures on `C(X, Y)`, proves the approximation theorems of Weierstrass and Stone-Weierstrass, and studies the ideals of `C(X, ℝ)`. Section 3 studies the bounded continuous functions `X →ᵇ Y`. Section 4 studies the functions that vanish at infinity, the functions with compact support, and the continuous maps that send $0$ to $0$.

The chapter needs Chapters 1 to 5, the equicontinuity of Chapter 7, and the groups, rings and modules of Volumes 5 to 7. Sections 3 and 4 use the norm of a normed group, and they recall each fact about norms that they use.
