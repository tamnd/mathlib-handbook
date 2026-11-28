---
title: Derivatives, truncation and expansion of power series
kind: api
modules:
  - Mathlib.RingTheory.PowerSeries.Derivative
  - Mathlib.RingTheory.MvPowerSeries.Derivative
  - Mathlib.RingTheory.PowerSeries.Trunc
  - Mathlib.RingTheory.MvPowerSeries.Trunc
  - Mathlib.RingTheory.PowerSeries.Expand
  - Mathlib.RingTheory.MvPowerSeries.Expand
  - Mathlib.RingTheory.PowerSeries.CoeffMulMem
explains:
  E2: [PowerSeries.derivative, PowerSeries.coeff_derivative, PowerSeries.derivative_subst, MvPowerSeries.pderiv, PowerSeries.trunc, PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc, MvPowerSeries.truncTotal, PowerSeries.expand, PowerSeries.map_frobenius_expand, PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal]
  E1: auto
families: []
requires: [V06.C05, V09.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Derivatives, truncation and expansion of power series

### Overview

Three operations on power series act one coefficient at a time. The formal derivative of $f = \sum_n a_n X^n$ is $f' = \sum_n (n + 1) a_{n+1} X^n$. It needs no limit, and it satisfies the rules of calculus: the product rule, the power rule, the derivative of an inverse and the chain rule for substitution. The truncation of $f$ at $n$ is the polynomial $a_0 + a_1 X + \cdots + a_{n-1} X^{n-1}$. It is the tool to reduce a statement about one coefficient of a product to a statement about polynomials, since the coefficient of $X^d$ in $f g$ depends only on the coefficients of index at most $d$. The expansion by $p$ replaces $X$ with $X^p$, and in characteristic $p$ it is related to the Frobenius map by $f(X^p) = f^p$ up to a twist of the coefficients.

Each operation exists in one variable and in several variables, in separate modules. The multivariate versions use partial derivatives, truncations at a multi-index or at a total degree, and expansion of every variable. A last module proves that the coefficients of a product stay in an ideal when the coefficients of a factor do, up to a given index. These operations are the daily tools of computations with generating functions. The derivative turns the equation $f' = f$ into a recursion on the coefficients, truncation turns a statement about the first $n$ coefficients into a statement about polynomials that a computer can check, and expansion appears in the theory of formal groups and in characteristic $p$. This section is a guide to these seven modules.

### The library around it

**The derivative in one variable.** The module `Mathlib.RingTheory.PowerSeries.Derivative` defines `PowerSeries.derivative`, an $R$-linear derivation of $R[[X]]$, with the notation `d⁄dX R`. Its coefficients are
$$\operatorname{coeff}_n(f') = (n + 1) \operatorname{coeff}_{n+1}(f),$$
which is `PowerSeries.coeff_derivative`. As a derivation it satisfies the product rule by `Derivation.leibniz`, and the module states the power rule `PowerSeries.derivative_pow` and the values `PowerSeries.derivative_X`, `PowerSeries.derivative_C` and `PowerSeries.derivative_X_pow`. On a polynomial it agrees with the derivative of polynomials, `PowerSeries.derivative_coe`. For a unit $f$ the derivative of the inverse is $-f^{-2} f'$, `PowerSeries.derivative_inv`, with versions for `Invertible` instances and for fields, `PowerSeries.derivative_invOf` and `PowerSeries.derivative_inv'`. The chain rule for a series $g$ that can be substituted is
$$(f(g))' = f'(g) \cdot g',$$
which is `PowerSeries.derivative_subst`. The iterated derivative has the coefficients `PowerSeries.coeff_iterate_derivative`, and its constant coefficient is $n! \, a_n$, `PowerSeries.constantCoeff_iterate_derivative`, the formula of Taylor for power series. Over a ring in which $n a = n b$ implies $a = b$ for $n \neq 0$, the class `HasUniqueDiv`, a series is determined by its constant coefficient and its derivative, `PowerSeries.derivative.ext`. Truncation commutes with the derivative up to a shift of the index, `PowerSeries.trunc_derivative`.

**Partial derivatives.** The module `Mathlib.RingTheory.MvPowerSeries.Derivative` defines `MvPowerSeries.pderiv i`, the derivation of $R[[\sigma]]$ for the variable $X_i$. Its coefficients are given by `MvPowerSeries.coeff_pderiv`, its value on a variable is `MvPowerSeries.pderiv_X`, and on a polynomial it agrees with `MvPolynomial.pderiv`, `MvPowerSeries.pderiv_coe`. The rules for inverses are `MvPowerSeries.pderiv_inv` and `MvPowerSeries.pderiv_invOf`, and `MvPowerSeries.pderiv.ext` is the analogue of the uniqueness statement in one variable.

**Truncation in one variable.** The module `Mathlib.RingTheory.PowerSeries.Trunc` defines `PowerSeries.trunc n`, the $R$-linear map to $R[X]$ that keeps the coefficients of index less than $n$, `PowerSeries.coeff_trunc`. Its degree is less than $n$, `PowerSeries.degree_trunc_lt`, and it does not change a polynomial of degree less than $n$, `PowerSeries.trunc_coe_eq_self`. The main property is that a product only needs truncated factors:
$$\operatorname{coeff}_d(f g) = \operatorname{coeff}_d\bigl(\operatorname{trunc}_n f \cdot \operatorname{trunc}_n g\bigr) \quad (d < n),$$
which is `PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc`. In the form of truncations this is `PowerSeries.trunc_trunc_mul_trunc`, and the version for powers is `PowerSeries.trunc_trunc_pow`. Truncation commutes with maps of coefficients, `PowerSeries.trunc_map`, and the evaluation of a truncation is a finite sum, `PowerSeries.eval₂_trunc_eq_sum_range`.

**Truncation in several variables.** The module `Mathlib.RingTheory.MvPowerSeries.Trunc` has four truncations to `MvPolynomial`. The map `MvPowerSeries.truncFinset R s` keeps the coefficients of a finite set $s$ of exponents. The map `MvPowerSeries.trunc R n` keeps the exponents strictly below the multi-index $n$, and `MvPowerSeries.trunc' R n` keeps the exponents at most $n$. For finitely many variables, `MvPowerSeries.truncTotal n` keeps the monomials of total degree less than $n$, `MvPowerSeries.coeff_truncTotal`, and the result has total degree less than $n$, `MvPowerSeries.totalDegree_truncTotal_lt`. Each version has the property of products: `MvPowerSeries.coeff_trunc_mul_trunc_eq_coeff_mul`, `MvPowerSeries.coeff_trunc'_mul_trunc'_eq_coeff_mul`, `MvPowerSeries.coeff_truncFinset_mul_truncFinset_eq_coeff_mul` and `MvPowerSeries.coeff_truncTotal_mul_truncTotal_eq_coeff_mul`. Two series are equal when all their truncations agree, `MvPowerSeries.ext_trunc'`.

**Expansion.** The module `Mathlib.RingTheory.PowerSeries.Expand` defines `PowerSeries.expand p hp` for $p \neq 0$, the algebra map that sends $X$ to $X^p$, `PowerSeries.expand_X`. Its coefficients are
$$\operatorname{coeff}_n(f(X^p)) = \begin{cases} \operatorname{coeff}_{n/p}(f) & p \mid n, \\ 0 & \text{otherwise}, \end{cases}$$
which is `PowerSeries.coeff_expand`, and it multiplies the order by $p$, `PowerSeries.order_expand`. Expansions compose, `PowerSeries.expand_mul`, and expansion commutes with substitution, `PowerSeries.expand_subst`. When $R$ has exponential characteristic $p$, the Frobenius map on the coefficients turns expansion into a power:
$$\operatorname{map}(\operatorname{Frob})(f(X^p)) = f^p,$$
which is `PowerSeries.map_frobenius_expand`, with the iterated form `PowerSeries.map_iterateFrobenius_expand`. Over a finite field $K$ with $q$ elements every $a \in K$ satisfies $a^q = a$, so $f(X^q) = f^q$, `FiniteField.PowerSeries.expand_card`. The module `Mathlib.RingTheory.MvPowerSeries.Expand` gives `MvPowerSeries.expand`, which expands every variable, with the same results: `MvPowerSeries.support_expand`, `MvPowerSeries.order_expand`, `MvPowerSeries.map_frobenius_expand`, `FiniteField.MvPowerSeries.expand_card` and `MvPowerSeries.expand_subst`.

**Coefficients in an ideal.** The module `Mathlib.RingTheory.PowerSeries.CoeffMulMem` proves statements on coefficients up to an index $n$. If the coefficients of $f$ of index at most $n$ lie in an ideal $I$ and those of $g$ lie in $J$, then the coefficients of $f g$ of index at most $n$ lie in $I J$, `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal`. The one-sided versions for a two-sided ideal are `PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal` and `PowerSeries.coeff_mul_mem_ideal_of_coeff_right_mem_ideal`, and the primed versions treat all coefficients at once. These statements are used in the proof of the Weierstrass preparation theorem, later in this chapter, where the coefficients are controlled modulo powers of the maximal ideal.

#### Common errors

1. `PowerSeries.trunc n f` keeps the coefficients of index less than $n$, not at most $n$. So `PowerSeries.trunc (n + 1)` is the truncation that contains $X^n$, and `PowerSeries.trunc_derivative` has $n + 1$ on the right side.
2. `PowerSeries.expand p hp` takes a proof that $p \neq 0$, and `PowerSeries.map_frobenius_expand` needs an `ExpChar R p` instance. A `CharP R p` instance with $p$ prime gives it, but the elaborator must find a proof that $p$ is prime. Over a field of characteristic $0$ the exponential characteristic is $1$, and the statement is trivial.
3. `PowerSeries.derivative.ext` fails in characteristic $p$: the series $X^p$ and $0$ have the same constant coefficient and the same derivative. The hypothesis `HasUniqueDiv R` excludes this case.

### Exercises

1. (A) Compute the derivative of $\sum_n X^n = (1 - X)^{-1}$ in two ways: with `PowerSeries.coeff_derivative` and with `PowerSeries.derivative_inv`.
2. (A) Use `PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc` to compute the coefficient of $X^3$ in $(\sum_n X^n)^2$ from two polynomials of degree $3$.
3. (B) Prove the chain rule for $f(X^2)$ from `PowerSeries.derivative_subst`, and compare with `PowerSeries.expand`.
4. (B) Over $\mathbb{F}_3$, check `PowerSeries.map_frobenius_expand` for $f = 1 + X + X^2$ by direct computation of $f^3$.
5. (B) Let $f \in \mathbb{Q}[[X]]$ satisfy $f' = f$ and $f(0) = 1$. Use `PowerSeries.derivative.ext` to prove that $f$ is the exponential series.
6. (C) Let $I$ be an ideal of $A$ and let $f \in A[[X]]$ have all coefficients of index at most $n$ in $I$. Prove that the coefficients of $f^k$ of index at most $n$ lie in $I^k$, using `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal` and induction on $k$.

### Reference

<?reference?>
