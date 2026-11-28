# The interval integral and the fundamental theorem of calculus

This chapter applies the integral of Chapter 5 to the real line and to $\mathbb{R}^n$. It connects the integral with the derivatives of Volume 15.

Section 1 defines the integral $\int_a^b f$ for all $a$ and $b$, with a sign when $b < a$. It proves the two forms of the fundamental theorem of calculus. Integration by parts and the substitution rule follow from them. The section then computes improper integrals on half lines, for example the powers $x^s$ on $(1, \infty)$ and $e^{-x}$ on $(0, \infty)$.

Section 2 states the change of variables formula in $\mathbb{R}^n$ with the absolute value of the Jacobian determinant, and gives a plan of its proof. It then proves the covering lemma of Vitali and the Lebesgue differentiation theorem: the averages of an integrable function on small balls converge to the function almost everywhere. Mathlib proves this theorem for Vitali families, with the covering theorem of Besicovitch.

Section 3 extends the fundamental theorem to absolutely continuous functions, to functions of class $C^1$ on a closed interval and to monotone functions. It also gives the mean value theorems for integrals, the integrals of periodic functions, the trapezoidal rule with its error bound, and the integrals of the form $\int_0^\infty x^q e^{-x^p} \, dx$ that give the Gamma function.

Section 4 defines the circle integral in $\mathbb{C}$, the circle average, the torus integral and the integral of a 1-form along a path. It proves the Cauchy power series formula, the lemma of Poincaré on a convex set and the divergence theorem on a box.

The chapter needs the mean value theorem of Volume 15, Lebesgue measure and its scaling from Chapter 3, and dominated convergence from Chapter 5. Section 2 also uses the density of continuous functions in $L^1$ from Chapter 7, Section 2.
