---
title: Operations on L-series
kind: api
modules:
  - Mathlib.NumberTheory.LSeries.Linearity
  - Mathlib.NumberTheory.LSeries.Deriv
  - Mathlib.NumberTheory.LSeries.Convolution
  - Mathlib.NumberTheory.LSeries.Injectivity
  - Mathlib.NumberTheory.LSeries.Positivity
  - Mathlib.NumberTheory.LSeries.SumCoeff
  - Mathlib.NumberTheory.AbelSummation
  - Mathlib.NumberTheory.EulerProduct.ExpLog
  - Mathlib.NumberTheory.ArithmeticFunction.LFunction
explains:
  E2: [LSeries_add, LSeries_deriv, LSeries_analyticOnNhd, LSeries_eq_iff_of_abscissaOfAbsConv_lt_top, LSeries.positive, LSeries_eq_mul_integral, sum_mul_eq_sub_integral_mul, EulerProduct.exp_tsum_primes_log_eq_tsum, ArithmeticFunction.ofPowerSeries, ArithmeticFunction.eulerProduct]
  E1: auto
families: []
requires: [V12.C02, V15, V19]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Operations on L-series

### Overview

Section 2 defines the L-series $L(f, s) = \sum_{n \geq 1} f(n) n^{-s}$ of a function $f : \mathbb{N} \to \mathbb{C}$ and its abscissa of absolute convergence. This section collects the operations on L-series that the library proves in separate small modules. The L-series is linear in $f$. It is holomorphic on the half-plane of absolute convergence, and its derivative is the L-series of $-f(n)\log n$. It turns Dirichlet convolution into a product. It determines $f$ on the positive integers. When $f \geq 0$ it is positive on the real axis. It can be written as an integral of the partial sums of $f$, by Abel summation. The section ends with two forms of the Euler product: an exponential of a sum of logarithms, and a formal product of power series.

The modules are `Mathlib.NumberTheory.LSeries.Linearity`, `Mathlib.NumberTheory.LSeries.Deriv`, `Mathlib.NumberTheory.LSeries.Convolution`, `Mathlib.NumberTheory.LSeries.Injectivity`, `Mathlib.NumberTheory.LSeries.Positivity`, `Mathlib.NumberTheory.LSeries.SumCoeff`, `Mathlib.NumberTheory.AbelSummation`, `Mathlib.NumberTheory.EulerProduct.ExpLog` and `Mathlib.NumberTheory.ArithmeticFunction.LFunction`. The analysis comes from Volume 15 and the holomorphic functions from Volume 19.

### The library around it

#### Linearity

The terms of the series are `LSeries.term f s n`, which is $f(n)/n^s$ for $n \neq 0$ and $0$ for $n = 0$. The value $f(0)$ never enters. The terms are linear in $f$: `LSeries.term_add`, `LSeries.term_sub`, `LSeries.term_neg`, `LSeries.term_smul` and `LSeries.term_sum`. The summability and the sum then follow the usual pattern of `HasSum`.

| Lean name | Statement |
|---|---|
| `LSeriesSummable.add`, `LSeriesSummable.sub`, `LSeriesSummable.neg` | sums, differences and negatives of summable series are summable |
| `LSeriesSummable.smul_iff` | for $c \neq 0$, $cf$ is summable at $s$ if and only if $f$ is |
| `LSeries_add` | $L(f + g, s) = L(f, s) + L(g, s)$ if both series converge at $s$ |
| `LSeries_smul` | $L(cf, s) = c\,L(f, s)$, with no hypothesis |
| `LSeries_neg` | $L(-f, s) = -L(f, s)$ |
| `LSeries_sum` | the L-series of a finite sum of summable functions |

`LSeries_add` needs the two summability hypotheses because `LSeries` is defined with `tsum`, which is $0$ for a divergent series. `LSeries_smul` and `LSeries_neg` need none. The abscissa of the sum satisfies `LSeries.abscissaOfAbsConv_add_le`, $\sigma_a(f + g) \leq \max(\sigma_a(f), \sigma_a(g))$, and `LSeries.abscissaOfAbsConv_sub_le` is the version for the difference.

#### Derivatives and analyticity

Write `LSeries.logMul f` for the function $n \mapsto \log(n) f(n)$. Each term $f(n)n^{-s}$ has derivative $-\log(n) f(n) n^{-s}$, by `LSeries.hasDerivAt_term`. The factor $\log n$ grows slower than each power of $n$, so it does not change the abscissa: `LSeries.abscissaOfAbsConv_logMul`. A uniform convergence argument on compact sets then gives the derivative of the whole series.

**Theorem.** Let $\operatorname{Re} s > \sigma_a(f)$. Then $L(f, \cdot)$ is complex differentiable at $s$, with
$$L'(f, s) = -L(\log \cdot f, s).$$

The statements are `LSeries_hasDerivAt` and `LSeries_deriv`, and `LSeries_deriv_eqOn` gives the equality on the whole half-plane. By induction, `LSeries_iteratedDeriv` gives the $m$-th derivative as $(-1)^m L(\log^m \cdot f, s)$, with the iterate `LSeries.logMul^[m] f`. The function is holomorphic on the open half-plane $\{s \mid \sigma_a(f) < \operatorname{Re} s\}$, by `LSeries_differentiableOn`, and analytic there, by `LSeries_analyticOnNhd` and `LSeries_analyticOn`.

#### Convolution

The convolution of two functions on `ℕ` is `LSeries.convolution f g`, with the scoped notation `f ⍟ g`. It is the Dirichlet product of Chapter 2, applied to `toArithmeticFunction f` and `toArithmeticFunction g`, which set the value at $0$ to $0$. So
$$(f \star g)(n) = \sum_{ab = n} f(a)g(b), \qquad n \geq 1.$$
The terms satisfy `LSeries.term_convolution`. The product formula is `LSeries_convolution'` of Section 2: if both series converge absolutely at $s$, then $L(f \star g, s) = L(f, s)L(g, s)$. The version `LSeries_convolution` uses the abscissas, and `LSeries.abscissaOfAbsConv_convolution_le` bounds the abscissa of the product. For arithmetic functions, which already vanish at $0$, the same results are `ArithmeticFunction.LSeries_mul`, `ArithmeticFunction.LSeries_mul'` and `ArithmeticFunction.LSeriesSummable_mul`.

#### Uniqueness

An L-series that converges somewhere determines its coefficients. The key limit is `LSeries.tendsto_atTop`: when $\sigma_a(f) < \infty$, $L(f, x) \to f(1)$ as the real number $x$ tends to $+\infty$. The reason is that each term with $n \geq 2$ tends to $0$, and the tail is bounded uniformly for large $x$. If $f(m) = 0$ for $m \leq n$, the same argument gives $(n + 1)^x L(f, x) \to f(n + 1)$, which is `LSeries.tendsto_cpow_mul_atTop`. Induction on $n$ then gives the uniqueness.

**Theorem.** Let $\sigma_a(f) < \infty$. Then $L(f, \cdot) = L(g, \cdot)$ if and only if $f(n) = g(n)$ for all $n \neq 0$.

This is `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`. Two other forms are `LSeries_injOn`, injectivity on the functions with $f(0) = 0$ and a finite abscissa, and `LSeries_eq_zero_iff`: for $f(0) = 0$, $L(f, \cdot) = 0$ if and only if $f = 0$ or the series converges nowhere. In the second case the value is $0$ everywhere by convention, `LSeries_eq_zero_of_abscissaOfAbsConv_eq_top`. The version `LSeries_eventually_eq_zero_iff'` only asks that the L-series vanish for large real $s$.

#### Positivity

Let $a : \mathbb{N} \to \mathbb{C}$ take nonnegative real values, written `0 ≤ a` with the partial order on `ℂ` of the scope ComplexOrder. The library proves the following.

1. `LSeries.positive`: if also $a(1) > 0$, then $L(a, x) > 0$ for real $x > \sigma_a(a)$.
2. `LSeries.iteratedDeriv_alternating`: $(-1)^n L^{(n)}(a, x) \geq 0$ for real $x > \sigma_a(a)$.
3. `LSeries.positive_of_differentiable_of_eqOn`: if an entire function $F$ agrees with $L(a, \cdot)$ on a half-plane $\operatorname{Re} s > x$ with $x \geq \sigma_a(a)$, then $F(y) > 0$ for all real $y$.

The proof of the third item expands $F$ in a Taylor series at a real point in the half-plane. The coefficients have alternating signs by item 2, so the series is positive at each smaller real point. The versions for arithmetic functions are `ArithmeticFunction.LSeries_positive`, `ArithmeticFunction.iteratedDeriv_LSeries_alternating` and `ArithmeticFunction.LSeries_positive_of_differentiable_of_eqOn`.

#### Abel summation

Abel summation is the discrete version of integration by parts. Let $c : \mathbb{N} \to \mathbb{K}$, with $\mathbb{K}$ equal to $\mathbb{R}$ or $\mathbb{C}$, and let $f$ be differentiable on $[0, b]$ with integrable derivative. With $C(t) = \sum_{k \leq t} c(k)$:
$$\sum_{k \leq b} f(k)c(k) = f(b)C(b) - \int_0^b f'(t)C(t)\,dt.$$
This is `sum_mul_eq_sub_integral_mul`. The version on an interval $(a, b]$ is `sum_mul_eq_sub_sub_integral_mul`. The versions `sum_mul_eq_sub_integral_mul₀` and `sum_mul_eq_sub_integral_mul₁` integrate from $1$ or $2$ when $c(0) = 0$, or $c(0) = c(1) = 0$, so that $f$ may be singular at $0$, as $\log$ is. The limit form `tendsto_sum_mul_atTop_nhds_one_sub_integral` passes to $b \to \infty$, and `summable_mul_of_bigO_atTop` gives a criterion for summability of $f(n)c(n)$ from bounds on $f$, $f'$ and $C$.

For L-series, take $f(t) = t^{-s}$. Then $f'(t) = -s t^{-s-1}$, and the boundary term disappears in the limit.

**Theorem.** Let $r \geq 0$ and $\operatorname{Re} s > r$. If the partial sums $\sum_{k=1}^n f(k)$ are $O(n^r)$ and $L(f, s)$ converges, then
$$L(f, s) = s \int_1^\infty \Big(\sum_{k \leq t} f(k)\Big) t^{-s-1}\,dt.$$

This is `LSeries_eq_mul_integral`. The version `LSeries_eq_mul_integral'` assumes the bound on $\sum \lvert f(k) \rvert$ instead, which also gives the convergence by `LSeriesSummable_of_sum_norm_bigO`. The integral form gives the behaviour at $s = 1$: if $\frac{1}{n}\sum_{k=1}^n f(k) \to l$, then $(s - 1)L(f, s) \to l$ as the real number $s$ tends to $1$ from above. This is `LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div`, with the version `LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg` for nonnegative real $f$. For $f = 1$ it gives the residue of $\zeta$ at $1$.

#### Euler products

For a completely multiplicative $f$ with $\sum \lvert f(n) \rvert < \infty$, Section 2 proves $\sum_n f(n) = \prod_p (1 - f(p))^{-1}$. The module `Mathlib.NumberTheory.EulerProduct.ExpLog` writes the product as the exponential of a sum. By `Summable.clog_one_sub`, the series $\sum_p \log(1 - f(p))$ converges, and `EulerProduct.exp_tsum_primes_log_eq_tsum` says
$$\exp\Big(\sum_p -\log(1 - f(p))\Big) = \sum_{n} f(n).$$
Here $f$ is a monoid homomorphism with zero `ℕ →*₀ ℂ`. This form avoids infinite products, and it is the form that gives bounds for $\log L(\chi, s)$.

The module `Mathlib.NumberTheory.ArithmeticFunction.LFunction` builds L-functions as formal Dirichlet series, with no convergence. For $q \in \mathbb{N}$ and a power series $F(T)$ over a commutative semiring $R$, `ArithmeticFunction.ofPowerSeries q F` is the arithmetic function of $F(q^{-s})$. Its value at $q^k$ is the coefficient of $T^k$, by `ArithmeticFunction.ofPowerSeries_apply_pow` for $q > 1$, and it is $0$ at the integers that are not powers of $q$. The map is an algebra homomorphism `PowerSeries R →ₐ[R] ArithmeticFunction R`, so products of power series become Dirichlet products. If $q$ is a prime power and $F$ has constant term $1$, the result is multiplicative, by `ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow`.

The Euler product of a family $(g_i)$ of arithmetic functions is `ArithmeticFunction.eulerProduct g`. It is defined as an infinite product for a topology of pointwise eventual equality, and the interface is `ArithmeticFunction.tendsTo_eulerProduct_of_tendsTo`: if for each $n$ almost all $g_i(n)$ equal $1(n)$, then for each $n$ the finite products $\prod_{i \in s} g_i$ have the value of the Euler product at $n$ for all large $s$. A product of multiplicative functions is multiplicative, `ArithmeticFunction.isMultiplicative_eulerProduct`. For local factors $F_i(q_i^{-s})$ with constant term $1$, `ArithmeticFunction.tendsTo_eulerProduct_ofPowerSeries` needs the class `Northcott q`, which says that only finitely many $q_i$ lie below each bound. For example, the factor $(1 - T)^{-1}$ at each prime $p$ gives the formal Dirichlet series of $\zeta$.

#### Common errors

1. `LSeries_add` fails without the summability hypotheses. Outside the domain of convergence `LSeries f s` is the junk value $0$, so $L(f + g, s)$ and $L(f, s) + L(g, s)$ can differ there.
2. The uniqueness theorems compare $f$ and $g$ only at $n \neq 0$, since the value $f(0)$ never enters an L-series. To get an equality of functions, add the hypotheses $f(0) = g(0) = 0$ as in `LSeries_injOn`.
3. `LSeries.positive` needs `0 ≤ a` in the order of `ℂ`, which says that each $a(n)$ is a nonnegative real number. It is not a statement about the norms $\lvert a(n) \rvert$.

### Exercises

1. (A) Use `LSeries_deriv` to show that $\zeta'(s) = -\sum_{n \geq 1} \log(n) n^{-s}$ for $\operatorname{Re} s > 1$.
2. (A) Let $g = f + \delta_0$, where $\delta_0$ is $1$ at $0$ and $0$ elsewhere. Show that $L(f, \cdot) = L(g, \cdot)$, and explain why this agrees with `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`.
3. (B) Prove the Abel summation formula $\sum_{k \leq b} f(k)c(k) = f(b)C(b) - \int_0^b f'(t)C(t)\,dt$ for an integer $b$ by summation by parts and $f(k + 1) - f(k) = \int_k^{k+1} f'$.
4. (B) Use `LSeries_eq_mul_integral` with $f = 1$ to show $\zeta(s) = s/(s - 1) - s\int_1^\infty \{t\} t^{-s-1}\,dt$ for $\operatorname{Re} s > 1$, where $\{t\}$ is the fractional part.
5. (B) Let $q$ be prime and $F = (1 - T)^{-1}$. Compute `ArithmeticFunction.ofPowerSeries q F` at each $n$, and show that it is multiplicative.
6. (C) Let $a \geq 0$ with $a(1) > 0$, and let $x$ be real with $x > \sigma_a(a)$. Prove that the Taylor series of $L(a, \cdot)$ at $x$ is positive at each real $y < x$ in its disc of convergence, from the alternating signs of the derivatives.

### Reference

<?reference?>
