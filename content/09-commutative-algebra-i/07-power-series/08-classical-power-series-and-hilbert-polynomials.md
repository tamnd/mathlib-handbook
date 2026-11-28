---
title: Classical power series and Hilbert polynomials
kind: api
modules:
  - Mathlib.RingTheory.PowerSeries.WellKnown
  - Mathlib.RingTheory.PowerSeries.Exp
  - Mathlib.RingTheory.PowerSeries.Log
  - Mathlib.RingTheory.PowerSeries.Binomial
  - Mathlib.RingTheory.PowerSeries.Catalan
  - Mathlib.RingTheory.PowerSeries.Schroder
  - Mathlib.RingTheory.PowerSeries.ExponentialModule
  - Mathlib.RingTheory.Polynomial.HilbertPoly
explains:
  E2: [PowerSeries.invOneSubPow, PowerSeries.exp, PowerSeries.exp_mul_exp_eq_exp_add, PowerSeries.log, PowerSeries.subst_exp_log, PowerSeries.binomialSeries, PowerSeries.catalanSeries, PowerSeries.IsExponential, Polynomial.hilbertPoly, Polynomial.existsUnique_hilbertPoly]
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

## Classical power series and Hilbert polynomials

### Overview

Some power series have names in every textbook: the geometric series $1/(1 - X)$ and its powers, the exponential $e^X = \sum X^n / n!$, the logarithm $\log(1 + X) = \sum (-1)^{n+1} X^n / n$, the sine, the cosine and the binomial series $(1 + X)^r$. In combinatorics the generating functions of the Catalan and the Schröder numbers are power series with integer coefficients that satisfy a quadratic equation. In the library these series are formal: they are elements of $A[[X]]$, defined by their coefficients, and the identities between them are identities of formal series. No convergence is involved.

The series with factorials in the denominators need $\mathbb{Q} \subseteq A$, which the library writes as `[Algebra ℚ A]`. The geometric series and the binomial series do not. This section is a guide to these modules, to the module on exponential series in the sense of the functional equation $f(X + Y) = f(X) f(Y)$, and to the module on Hilbert polynomials. A Hilbert polynomial comes from a rational function $p / (1 - X)^d$: its coefficients agree, for large $n$, with the values of a polynomial in $n$. This is the algebraic core of the theory of Hilbert functions of graded modules in Volume 10.

### The library around it

**The geometric series and its powers.** The module `Mathlib.RingTheory.PowerSeries.WellKnown` starts with `PowerSeries.invUnitsSub u`, the series $\sum_n u^{-(n+1)} X^n$, which is the inverse of $u - X$ for a unit $u$. Its coefficients are `PowerSeries.coeff_invUnitsSub` and the relation with $X$ is `PowerSeries.invUnitsSub_mul_X`. For the unit $1$ the series is $\sum X^n$, which is `PowerSeries.mk 1`, and `PowerSeries.mk_one_mul_one_sub_eq_one` says $(\sum X^n)(1 - X) = 1$. The unit `PowerSeries.invOneSubPow S d` is $(1 - X)^{-d}$ in the group of units of $S[[X]]$. Its value has binomial coefficients:
$$\frac{1}{(1 - X)^{d+1}} = \sum_{n \ge 0} \binom{d + n}{d} X^n,$$
which is `PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose`, with the variant `PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos` for $d > 0$. The same formula for the power of $\sum X^n$ is `PowerSeries.mk_one_pow_eq_mk_choose_add`. The unit is the inverse of $(1 - X)^d$, `PowerSeries.invOneSubPow_inv_eq_one_sub_pow`, and it is additive in $d$, `PowerSeries.invOneSubPow_add`. The module also defines `PowerSeries.sin A` and `PowerSeries.cos A` by their coefficients, with `PowerSeries.map_sin` and `PowerSeries.map_cos` for a change of rings.

**The exponential.** The module `Mathlib.RingTheory.PowerSeries.Exp` defines `PowerSeries.exp A`, with coefficients $1/n!$, `PowerSeries.coeff_exp`. The functional equation takes the form of a rescaling. With $\operatorname{rescale}_a f = f(aX)$,
$$e^{aX} e^{bX} = e^{(a + b) X},$$
which is `PowerSeries.exp_mul_exp_eq_exp_add`. The special cases are `PowerSeries.exp_mul_exp_neg_eq_one`, which says $e^X e^{-X} = 1$, and `PowerSeries.exp_pow_eq_rescale_exp`, which says $(e^X)^k = e^{kX}$. The exponential is a unit, `PowerSeries.isUnit_exp`, with order $0$, `PowerSeries.order_exp`. It is the unique series with $f' = f$ and constant coefficient $1$, `PowerSeries.exp_unique_of_derivative_eq_self`, with the derivative of Section 7. The sum $\sum_{k < n} e^{kX}$ has the coefficients $\sum_{k < n} k^p / p!$, `PowerSeries.exp_pow_sum`, which gives the sums of powers that lead to the Bernoulli numbers.

**The logarithm.** The module `Mathlib.RingTheory.PowerSeries.Log` defines `PowerSeries.log A`, the series of $\log(1 + X)$. Its coefficients are $0$ for $n = 0$ and $(-1)^{n+1}/n$ otherwise, `PowerSeries.coeff_log`, so its order is $1$, `PowerSeries.order_log`. Its derivative is $\sum (-1)^n X^n = 1/(1 + X)$, `PowerSeries.derivative_log`. The two series are inverse to each other under the substitution of Section 6:
$$e^{\log(1 + X)} = 1 + X, \qquad \log\bigl(1 + (e^X - 1)\bigr) = X,$$
which are `PowerSeries.subst_exp_log` and `PowerSeries.subst_log_exp_sub_one`. The substitutions are allowed because $\log(1+X)$ and $e^X - 1$ have constant coefficient $0$. For a series $f$ with constant coefficient $1$, `PowerSeries.logOf f` is $\log f$, the substitution of $f - 1$ into the logarithm. It has constant coefficient $0$, `PowerSeries.constantCoeff_logOf`, and `PowerSeries.logOf_exp` says $\log(e^X) = X$.

**The binomial series.** The module `Mathlib.RingTheory.PowerSeries.Binomial` defines `PowerSeries.binomialSeries A r` for $r$ in a binomial ring $R$. Its coefficients are the generalized binomial coefficients $\binom{r}{n}$, `PowerSeries.binomialSeries_coeff`, so it is the series of $(1 + X)^r$. A binomial ring, `BinomialRing`, is a ring in which $\binom{r}{n}$ makes sense, for example $\mathbb{Z}$ or a $\mathbb{Q}$-algebra. The law of exponents holds,
$$(1 + X)^{r + s} = (1 + X)^r (1 + X)^s,$$
which is `PowerSeries.binomialSeries_add`, and for a natural number $d$ the series is the polynomial $(1 + X)^d$, `PowerSeries.binomialSeries_nat`. Negative integers give the geometric series: `PowerSeries.rescale_neg_one_invOneSubPow` says that $(1 + X)^{-d}$ is $(1 - X)^{-d}$ with $X$ replaced by $-X$.

**Catalan and Schröder series.** The module `Mathlib.RingTheory.PowerSeries.Catalan` defines `PowerSeries.catalanSeries` in $\mathbb{N}[[X]]$, with the Catalan numbers as coefficients, `PowerSeries.catalanSeries_coeff`. Its main identity is the quadratic equation $C = 1 + X C^2$, `PowerSeries.catalanSeries_sq_mul_X_add_one`. The module `Mathlib.RingTheory.PowerSeries.Schroder` defines `PowerSeries.largeSchroderSeries`, with the large Schröder numbers as coefficients, `PowerSeries.coeff_largeSchroderSeries`, and the equation $S = 1 + X S + X S^2$, `PowerSeries.largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq`. Both equations encode the recurrences of the numbers.

**Exponential series.** The module `Mathlib.RingTheory.PowerSeries.ExponentialModule` studies the power series $f$ that satisfy the functional equation of the exponential without the need for $\mathbb{Q} \subseteq R$. The predicate `PowerSeries.IsExponential f` asks for $f(0) = 1$ and for the binomial identity on coefficients:
$$\binom{p + q}{p} f_{p+q} = f_p f_q,$$
which is `PowerSeries.isExponential_iff`. Equivalently, $f(X + Y) = f(X) f(Y)$ in the power series in two variables, `PowerSeries.IsExponential.subst_add_eq_mul`, with the converse in `PowerSeries.subst_add_eq_mul_iff`. Products of exponential series are exponential, `PowerSeries.IsExponential.mul`, every exponential series is a unit, `PowerSeries.IsExponential.isUnit`, and its inverse is $f(-X)$, `PowerSeries.IsExponential.invOfUnit_eq_rescale_neg_one`. So the exponential series form a group under multiplication. The library writes this group additively as `PowerSeries.ExponentialModule R`, a submonoid of `Additive (PowerSeries R)` with `PowerSeries.mem_exponentialModule_iff`. For an $A$-algebra $R$ it is an $A$-module, where $a$ acts by the rescaling $f(X) \mapsto f(aX)$, `PowerSeries.ofMul_smul_coe'`. An algebra map $R \to S$ gives the linear map `PowerSeries.ExponentialModule.linearMap`. This module appears in the theory of divided powers, where an exponential series is a family $(x^{[n]})$ of divided powers of one element.

**Hilbert polynomials.** The module `Mathlib.RingTheory.Polynomial.HilbertPoly` works over a field $F$ of characteristic $0$. For a polynomial $p$ and $d \in \mathbb{N}$, the coefficients of $p / (1 - X)^d$ are, for large $n$, the values of a single polynomial. That polynomial is `Polynomial.hilbertPoly p d`, and the precise statement is
$$[X^n] \, \frac{p}{(1 - X)^d} = h(n) \quad \text{for } n > \deg p,$$
which is `Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval`. The polynomial is unique with this property, `Polynomial.existsUnique_hilbertPoly`. The building blocks are `Polynomial.preHilbertPoly F d k`, which treats $p = X^k$, `Polynomial.hilbertPoly_X_pow_succ`. It has degree $d$ and leading coefficient $1/d!$, `Polynomial.natDegree_preHilbertPoly` and `Polynomial.leadingCoeff_preHilbertPoly`. A factor $1 - X$ in $p$ cancels one factor of $(1 - X)^d$, `Polynomial.hilbertPoly_mul_one_sub_succ`, and the degree of a nonzero Hilbert polynomial is $d - m - 1$, where $m$ is the multiplicity of $1$ as a root of $p$, `Polynomial.natDegree_hilbertPoly_of_ne_zero`.

#### Common errors

1. `PowerSeries.exp A`, `PowerSeries.log A`, `PowerSeries.sin A` and `PowerSeries.cos A` take the ring $A$ as an explicit argument and need `[Algebra ℚ A]`. Over a ring of positive characteristic they do not exist. The exponential series of `PowerSeries.IsExponential` are the replacement there.
2. The functional equation of `PowerSeries.exp_mul_exp_eq_exp_add` is about rescalings $e^{aX}$ for $a \in A$, not about a substitution $X \mapsto X + Y$. For two variables use `PowerSeries.IsExponential.subst_add_eq_mul`, which lives in the power series in variables indexed by `Fin 2`.
3. `PowerSeries.invOneSubPow S d` is a unit, not a series. Use its coercion to `PowerSeries S` in coefficient computations, and use `PowerSeries.invOneSubPow_inv_eq_one_sub_pow` to get $(1 - X)^d$ back.

### Exercises

1. (A) Use `PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose` to write the first four coefficients of $1/(1 - X)^3$, and check the result by multiplication with $(1 - X)^3$.
2. (A) Prove from `PowerSeries.exp_mul_exp_eq_exp_add` that $e^{2X} = (e^X)^2$, and compare with `PowerSeries.exp_pow_eq_rescale_exp`.
3. (B) Compute the coefficients of $X^2$ and $X^3$ in $e^{\log(1 + X)}$ by hand, and check that they agree with `PowerSeries.subst_exp_log`.
4. (B) Use `PowerSeries.catalanSeries_sq_mul_X_add_one` to derive the recurrence $C_{n+1} = \sum_{i=0}^{n} C_i C_{n-i}$ for the Catalan numbers.
5. (B) Prove that $f = \sum_n X^n$ is not exponential over $\mathbb{Q}$, with the criterion `PowerSeries.isExponential_iff` for $p = q = 1$.
6. (C) Let $p = 1 + X$ and $d = 2$. Compute `Polynomial.hilbertPoly p 2` from the coefficients of $(1 + X)/(1 - X)^2$, and check its degree with `Polynomial.natDegree_hilbertPoly_of_ne_zero`.

### Reference

<?reference?>
