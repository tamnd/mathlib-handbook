---
title: Classical families of polynomials
kind: api
modules:
  - Mathlib.RingTheory.Polynomial.Chebyshev
  - Mathlib.RingTheory.Polynomial.Dickson
  - Mathlib.RingTheory.Polynomial.Bernstein
  - Mathlib.RingTheory.Polynomial.Hermite.Basic
  - Mathlib.RingTheory.Polynomial.Hermite.Gaussian
  - Mathlib.RingTheory.Polynomial.Pochhammer
  - Mathlib.RingTheory.Polynomial.ShiftedLegendre
explains:
  E2: [Polynomial.Chebyshev.T, Polynomial.Chebyshev.T_mul, Polynomial.Chebyshev.T_derivative_eq_U, Polynomial.dickson_one_one_eval_add_inv, bernsteinPolynomial.sum, Polynomial.hermite_succ, ascPochhammer_succ_right, Polynomial.factorial_mul_shiftedLegendre_eq]
  E1: auto
families: []
requires: [V06.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Classical families of polynomials

### Overview

Several sequences of polynomials appear in many parts of mathematics. The Chebyshev polynomials satisfy $T_n(\cos \theta) = \cos(n \theta)$. The Dickson polynomials are their analogues in characteristic $p$. The Bernstein polynomials give a proof of the theorem of Weierstrass on uniform approximation. The Hermite polynomials come from the derivatives of the Gaussian function. The Pochhammer polynomials $X(X+1)\cdots(X+n-1)$ give the rising and falling factorials, and the shifted Legendre polynomials are orthogonal on the interval $[0, 1]$.

In the library each family is defined by a recurrence or by an explicit formula, over a general commutative ring when possible, and then mapped to other rings. This section is a guide to the seven modules that hold these families. The applications in analysis are in later volumes. Here the focus is on the algebraic identities: recurrences, degrees, leading coefficients, composition and derivatives.

A proof about one of these families usually goes by induction on the index with the recurrence, and then by the simp tactic with the lemmas for the small cases. For this reason each module gives the first values as separate lemmas, such as `Polynomial.Chebyshev.T_two`, `Polynomial.Chebyshev.U_two`, `Polynomial.hermite_one` and `ascPochhammer_one`. A second common step is to move between rings with the lemmas on `Polynomial.map`, because several families are defined over $\mathbb{Z}$ only. Each family has a lemma for the change of rings, so a computation over $\mathbb{Z}$ gives the result over every commutative ring. The exercises of this section follow the same pattern: first values, then an induction on the index.

### The library around it

**Chebyshev polynomials.** The module `Mathlib.RingTheory.Polynomial.Chebyshev` defines four families, indexed by integers so that the recurrence holds in both directions. The polynomials of the first kind, `Polynomial.Chebyshev.T R n`, start with $T_0 = 1$ and $T_1 = X$, and satisfy
$$T_{n+2} = 2 X T_{n+1} - T_n,$$
which is `Polynomial.Chebyshev.T_add_two`. The polynomials of the second kind, `Polynomial.Chebyshev.U R n`, start with $U_0 = 1$ and $U_1 = 2X$ and satisfy the same recurrence, `Polynomial.Chebyshev.U_add_two`. The two kinds are related by `Polynomial.Chebyshev.T_eq_X_mul_U_sub_U`, $T_{n+2} = X U_{n+1} - U_n$, and by the derivative:
$$T_n' = n U_{n-1},$$
which is `Polynomial.Chebyshev.T_derivative_eq_U`. The rescaled families `Polynomial.Chebyshev.C` and `Polynomial.Chebyshev.S` satisfy the recurrence with $X$ in place of $2X$, and `Polynomial.Chebyshev.S_comp_two_mul_X` says that $S_n(2X) = U_n$. The central identity is composition:
$$T_{mn} = T_m \circ T_n,$$
which is `Polynomial.Chebyshev.T_mul`. It corresponds to $\cos(mn\theta) = \cos(m \cdot n\theta)$. Over a domain in which $2 \neq 0$, the degree of $T_n$ is $|n|$, `Polynomial.Chebyshev.degree_T`, and its leading coefficient is $2^{|n| - 1}$, `Polynomial.Chebyshev.leadingCoeff_T`. The values at $0$ and $\pm 1$ are `Polynomial.Chebyshev.T_eval_zero`, `Polynomial.Chebyshev.T_eval_one` and `Polynomial.Chebyshev.U_eval_neg_one`. The differential equations take the form of `Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_T_eq_poly_in_T`. The families commute with ring homomorphisms, `Polynomial.Chebyshev.map_T` and `Polynomial.Chebyshev.map_U`, and with evaluation in an algebra, `Polynomial.Chebyshev.aeval_T`.

**Dickson polynomials.** The module `Mathlib.RingTheory.Polynomial.Dickson` defines `Polynomial.dickson k a n` over a commutative ring $R$, for $a \in R$ and $k \in \{1, 2\}$ in the cases of interest. It starts with $D_0 = 3 - k$ and $D_1 = X$, and satisfies
$$D_{n+2} = X D_{n+1} - a D_n,$$
which is `Polynomial.dickson_add_two`. The family with $k = 1$ and $a = 1$ is characterized by
$$D_n(x + y) = x^n + y^n \quad \text{when } x y = 1,$$
which is `Polynomial.dickson_one_one_eval_add_inv`. It also satisfies $D_{mn} = D_m \circ D_n$, `Polynomial.dickson_one_one_mul`. When $2$ is invertible, the Dickson and Chebyshev polynomials determine each other, `Polynomial.dickson_one_one_eq_chebyshev_T` and `Polynomial.chebyshev_T_eq_dickson_one_one`, and the second family gives $U_n$, `Polynomial.dickson_two_one_eq_chebyshev_U`. The Dickson form is useful in characteristic $2$, where the Chebyshev form loses information. Over $\mathbb{Z}/p$ one has $D_p = X^p$, `Polynomial.dickson_one_one_zmod_p`, and the general version in characteristic $p$ is `Polynomial.dickson_one_one_charP`.

**Bernstein polynomials.** The module `Mathlib.RingTheory.Polynomial.Bernstein` defines
$$b_{n, \nu} = \binom{n}{\nu} X^{\nu} (1 - X)^{n - \nu},$$
which is `bernsteinPolynomial R n ν`. They form a partition of unity:
$$\sum_{\nu = 0}^{n} b_{n, \nu} = 1,$$
which is `bernsteinPolynomial.sum`. The first and second moments are `bernsteinPolynomial.sum_smul` and `bernsteinPolynomial.variance`, with $\sum_\nu (nX - \nu)^2 b_{n,\nu} = n X (1 - X)$. These are the identities used in the proof of the theorem of Weierstrass. The substitution $X \mapsto 1 - X$ exchanges $b_{n, \nu}$ and $b_{n, n-\nu}$, `bernsteinPolynomial.flip`. Over $\mathbb{Q}$ the $n + 1$ polynomials $b_{n, \nu}$ are linearly independent, `bernsteinPolynomial.linearIndependent`, and the proof uses the values of their derivatives at $0$, such as `bernsteinPolynomial.iterate_derivative_at_0`.

**Hermite polynomials.** The module `Mathlib.RingTheory.Polynomial.Hermite.Basic` defines the probabilists' Hermite polynomials `Polynomial.hermite n` over $\mathbb{Z}$, by
$$H_0 = 1, \qquad H_{n+1} = X H_n - H_n',$$
which is `Polynomial.hermite_succ`. The polynomial $H_n$ is monic, `Polynomial.hermite_monic`, of degree $n$, `Polynomial.natDegree_hermite`, and its coefficients have the explicit formula `Polynomial.coeff_hermite`. Coefficients with $n + k$ odd vanish, `Polynomial.coeff_hermite_of_odd_add`. The module `Mathlib.RingTheory.Polynomial.Hermite.Gaussian` connects the definition with analysis: the $n$-th derivative of $e^{-x^2/2}$ is $(-1)^n H_n(x) e^{-x^2/2}$, `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`, with the inverse form `Polynomial.hermite_eq_deriv_gaussian`.

**Pochhammer polynomials.** The module `Mathlib.RingTheory.Polynomial.Pochhammer` defines the rising and the falling factorial polynomials over a semiring and a ring:
$$\operatorname{ascPochhammer}_n = X (X + 1) \cdots (X + n - 1), \qquad \operatorname{descPochhammer}_n = X (X - 1) \cdots (X - n + 1).$$
These are `ascPochhammer S n` and `descPochhammer R n`. The recurrences are `ascPochhammer_succ_right` and `descPochhammer_succ_right`, and the product formula for a sum of indices is `ascPochhammer_mul`. On natural numbers they give the factorials of the library: `ascPochhammer_nat_eq_ascFactorial` and `descPochhammer_eval_eq_descFactorial`. They also give the binomial coefficients, `Nat.cast_choose_eq_ascPochhammer_div` and `Nat.cast_choose_eq_descPochhammer_div`. The two families are related by a shift, `descPochhammer_eval_eq_ascPochhammer`. Both are monic, `monic_ascPochhammer` and `monic_descPochhammer`, of degree $n$, and the rising one is positive at positive points of an ordered semiring, `ascPochhammer_pos`.

**Shifted Legendre polynomials.** The module `Mathlib.RingTheory.Polynomial.ShiftedLegendre` defines `Polynomial.shiftedLegendre n` over $\mathbb{Z}$ by its coefficients, `Polynomial.coeff_shiftedLegendre`. The formula of Rodrigues is
$$n! \, \tilde P_n = \frac{d^n}{dX^n} \bigl( X^n (1 - X)^n \bigr),$$
which is `Polynomial.factorial_mul_shiftedLegendre_eq`. The degree is $n$, `Polynomial.natDegree_shiftedLegendre`, and the substitution $X \mapsto 1 - X$ multiplies $\tilde P_n$ by $(-1)^n$, `Polynomial.neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq`.

#### Common errors

1. The Chebyshev polynomials take an integer index, so `Polynomial.Chebyshev.T R 2` has the index $(2 : \mathbb{Z})$. A natural number index must be cast, and lemmas such as `Polynomial.Chebyshev.degree_U_natCast` exist for the cast case.
2. The statements on degree and leading coefficient of $T_n$ need `[IsDomain R]` and `[NeZero (2 : R)]`. In characteristic $2$ the leading coefficient $2^{n-1}$ is zero, and $T_n$ has smaller degree.
3. `Polynomial.hermite` is the probabilists' version, with leading coefficient $1$. The physicists' Hermite polynomials differ by a scaling of $X$ and a power of $2$.

### Exercises

1. (A) Compute $T_3$ and $T_4$ from `Polynomial.Chebyshev.T_add_two`, and check that $T_2 \circ T_2 = T_4$, as `Polynomial.Chebyshev.T_mul` predicts.
2. (A) Use `bernsteinPolynomial.sum` with $n = 2$ to write $1$ as a sum of three Bernstein polynomials, and expand each of them.
3. (B) Prove that $T_n(1) = 1$ and $T_n(-1) = (-1)^n$ for all $n \in \mathbb{N}$ by induction with the recurrence.
4. (B) Use `Polynomial.dickson_one_one_eval_add_inv` to show that $D_n(X + X^{-1}) = X^n + X^{-n}$ in the ring of Laurent polynomials, and deduce $D_p \equiv X^p$ modulo $p$.
5. (B) Prove that $\operatorname{ascPochhammer}_n$ evaluated at $1$ is $n!$, and that $\operatorname{descPochhammer}_n$ evaluated at $k$ is $0$ for natural numbers $k < n$.
6. (C) Prove from `Polynomial.factorial_mul_shiftedLegendre_eq` and integration by parts that $\int_0^1 \tilde P_n(x) q(x)\, dx = 0$ for every polynomial $q$ of degree less than $n$.

### Reference

<?reference?>
