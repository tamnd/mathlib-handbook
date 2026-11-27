# $L^p$ spaces

This chapter studies the functions whose $p$-th power is integrable. These spaces are the first examples of Banach spaces of functions, and most of analysis works in one of them.

Section 1 defines the quantity $\|f\|_p$ for $0 < p \le \infty$, with the essential supremum for $p = \infty$. It proves the inequality of Hölder from the inequality of Young, and the inequality of Minkowski from Hölder. It compares the exponents: on a finite measure space, $L^q \subseteq L^p$ for $p \le q$, and an example shows that this fails on the line. Mathlib calls the quantity `eLpNorm`, with values in $[0, \infty]$, and it defines `MemLp` from it.

Section 2 passes to classes of functions equal almost everywhere. On these classes $\|\cdot\|_p$ is a norm for $1 \le p \le \infty$. The main theorem is that $L^p$ is complete, the theorem of Riesz and Fischer, with a full proof. The section then proves that simple functions are dense, states the density of continuous functions with compact support, and gives $L^2$ its inner product.

The chapter needs the inequality of Young and the convexity of powers from Volume 15, the Lebesgue integral of Chapter 4 with monotone convergence and Fatou, and the integrable functions and dominated convergence of Chapter 5. Some examples use Lebesgue measure on the line from Chapter 3 and the computed integrals of Chapter 8, Section 1.

The spaces of this chapter return in Chapter 8 for the Lebesgue differentiation theorem, which uses the density of continuous functions in $L^1$.
