# Product measures and Fubini

This chapter builds the product of two measures and proves that a double integral is an iterated integral. Section 1 constructs the product measure $\mu \otimes \nu$ on $X \times Y$. It shows that the measure of a set is the integral of the measures of its sections, that a rectangle $A \times B$ has measure $\mu(A)\nu(B)$, and that this property fixes the product when both measures are σ-finite. It ends with the product of finitely many measures, which is the measure `volume` on $\mathbb{R}^n$ in Mathlib.

Section 2 proves the theorem of Tonelli for functions with values in $[0, \infty]$ and the theorem of Fubini for integrable functions. Two counterexamples show that each hypothesis is necessary. A worked example computes the Gaussian integral with only Fubini and a substitution. Section 3 passes to infinite products: it describes the cylinder sets that generate the product σ-algebra, the projective families of finite-dimensional measures, and the theorem of Kolmogorov that builds a measure from such a family on a product of Polish spaces.

The chapter needs the product σ-algebra and the π-λ theorem of Chapter 1, the measures and the classes `SFinite` and `SigmaFinite` of Chapter 2, Lebesgue measure on the line of Chapter 3, the monotone convergence theorem of Chapter 4, and the Bochner integral and dominated convergence of Chapter 5.

In Mathlib the product measure is defined for every pair of measures, and the main results need s-finiteness, a weaker hypothesis than σ-finiteness. The text explains where each of the two hypotheses is used.

The results of this chapter return in Chapter 7, where an exercise bounds the $L^1$ norm of a convolution with Tonelli, and in Chapter 8, where the change of variables formula in $\mathbb{R}^n$ and polar coordinates rest on the product structure of `volume`.
