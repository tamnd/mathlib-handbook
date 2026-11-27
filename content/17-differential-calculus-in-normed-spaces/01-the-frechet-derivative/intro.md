# The Fréchet derivative

This chapter defines the derivative of a map $f : E \to F$ between normed spaces. The derivative at $x$ is a continuous linear map $Df(x) : E \to F$ with $f(x + h) = f(x) + Df(x)h + o(\|h\|)$. For $E = F = \mathbb{R}$ it is multiplication by the number $f'(x)$ of Volume 15.

Section 1 gives the definition, proves that the derivative is unique at an interior point and that a differentiable map is continuous, and explains the predicate `HasFDerivAt f f' x` and the function `fderiv 𝕜 f x` of Mathlib. The examples treat linear maps, quadratic forms, the square of a matrix and the square of the norm, and show that the norm is not differentiable at $0$.

Section 2 defines directional derivatives, partial derivatives, the Jacobian matrix and the gradient. A counterexample shows that all directional derivatives can exist at a point of discontinuity, and a theorem shows that continuous partial derivatives imply differentiability. The section then defines the derivative within a set and the tangent cone, and proves that the derivative within a convex set with nonempty interior is unique.

The chapter needs Volume 7, the normed spaces and filters of Volume 13, and Volume 15, Chapter 3. Chapter 2 proves the rules of calculus and Chapter 3 the mean value inequality, and the later chapters use both in the inverse function theorem, Taylor's formula and differential equations.
