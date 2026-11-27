# The tangent space and mfderiv

A smooth map between manifolds has a derivative at each point. The derivative is a linear map from the tangent space at the point to the tangent space at the image. This chapter defines the tangent space, the derivative `mfderiv` and the tangent map, and it shows how to compute them.

Section 1 sets up the definitions. Mathlib takes the tangent space at a point $x$ of a manifold modelled on a vector space $E$ to be $E$ itself. The derivative of $f$ at $x$ is the derivative of $f$ written in the preferred extended charts at $x$ and at $f(x)$, within the range of the model with corners. The section proves that differentiability implies continuity, that the derivative is unique where the domain has unique differentials, the chain rule, and that a $C^n$ map with $n \ge 1$ is differentiable. It also proves that differentiability does not depend on the choice of charts when the manifolds are of class $C^1$.

Section 2 computes. For maps between normed spaces `mfderiv` is `fderiv`. The derivatives of the identity, of constants, of projections, of pairs, of sums, of scalar multiples and of products follow. The section computes the derivative of a chart, which is invertible, and of a change of charts. A worked example finds the tangent space of the sphere inside the ambient space and the critical points of the height function on the circle.

The chapter needs Chapter 2 for models with corners, extended charts and the class `IsManifold`, and Chapter 3 for smooth maps. From Volume 17 it uses the Fréchet derivative, the derivative within a set, sets with unique differentials, and the chain rule.

Chapter 5 makes the tangent spaces into a vector bundle, the tangent bundle, and proves that the tangent map of a smooth map is smooth. Chapter 7 uses the derivative to define immersions and submersions. Chapter 8 uses it for vector fields, their brackets and integral curves.
