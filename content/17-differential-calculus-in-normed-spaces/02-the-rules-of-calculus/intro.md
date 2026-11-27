# The rules of calculus

This chapter proves the rules that compute Fréchet derivatives without a return to the definition. They have the form of the rules of Volume 15, but the derivative is now a continuous linear map, so products of derivatives become composites, and the order of factors matters.

Section 1 proves the rule for sums and the chain rule $D(g \circ f)(x) = Dg(f(x)) \circ Df(x)$, with the $o$ notation of Chapter 1. It shows that a map into a finite product is differentiable if and only if each component is, defines the partial derivatives $D_1 f$ and $D_2 f$ on a product $E_1 \times E_2$, and shows that a continuous linear equivalence does not change differentiability, which allows a change of norm or of coordinates.

Section 2 proves that a continuous bilinear map $B$ has the derivative $(h, k) \mapsto B(h, y) + B(x, k)$. This gives the product rule in a normed algebra, the derivative of $x^n$ in a noncommutative algebra, and the rules for maps into a space of operators. The section proves that the inverse in a Banach algebra has the derivative $h \mapsto -x^{-1}hx^{-1}$, with the Neumann series of Volume 16, and proves Jacobi's formula $D\det(A)H = \operatorname{tr}(\operatorname{adj}(A)H)$, which Mathlib lacks.

The chapter needs Chapter 1, Volume 7 for the determinant, and Volume 15, Chapter 3. Chapter 3 applies the chain rule on segments, Chapter 4 differentiates maps into $L(E, F)$, and Chapter 6 uses the derivative of the inverse.
