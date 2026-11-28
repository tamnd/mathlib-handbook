---
title: Formal multilinear series and the radius of convergence
kind: theory
modules:
  - Mathlib.Analysis.Calculus.FormalMultilinearSeries
  - Mathlib.Analysis.Analytic.ConvergenceRadius
  - Mathlib.Analysis.Analytic.Basic
  - Mathlib.Analysis.Analytic.OfScalars
  - Mathlib.Analysis.Analytic.RadiusLiminf
  - Mathlib.Analysis.Analytic.Binomial
  - Mathlib.Analysis.Analytic.Within
explains:
  E3: [FormalMultilinearSeries, FormalMultilinearSeries.radius, HasFPowerSeriesOnBall, AnalyticAt]
  E2: [FormalMultilinearSeries.le_radius_of_bound, FormalMultilinearSeries.summable_norm_mul_pow, FormalMultilinearSeries.not_summable_norm_of_radius_lt_nnNorm, HasFPowerSeriesAt, AnalyticOnNhd, FormalMultilinearSeries.ofScalars, FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto, AnalyticAt.continuousAt, HasFPowerSeriesOnBall.coeff_zero, FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero]
  E1: auto
families: []
requires: [V17.C04, V15.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Formal multilinear series and the radius of convergence

### Overview

A power series in one variable is $\sum a_n z^n$. In a normed space $E$ the monomial $z^n$ has no meaning, but the expression $p_n(y, \dots, y)$ for a continuous $n$-linear map $p_n$ does. Chapter 4 showed that the terms of Taylor's formula have exactly this form: $\frac1{n!}D^n f(x)(h^n)$. So a power series on $E$ with values in $F$ is a sequence of continuous multilinear maps, and a function is analytic when it is the sum of such a series near each point.

$E$ and $F$ are normed spaces over $\mathbb{K}$, and $F$ is complete when a sum must exist. For $y \in E$ write $y^n = (y, \dots, y) \in E^n$, as in Chapter 4.

### Definitions

**Definition (Formal multilinear series).** A *formal multilinear series* from $E$ to $F$ is a sequence $p = (p_n)_{n \ge 0}$ with $p_n \in L^n(E; F)$, the space of continuous $n$-linear maps $E^n \to F$. Here $p_0$ is a constant: $L^0(E; F) = F$.

The series of $p$ at $y$ is $\sum_n p_n(y^n)$. The name *formal* means that no convergence is assumed.

::: mathlib
`FormalMultilinearSeries` · `Mathlib.Analysis.Calculus.FormalMultilinearSeries`

`FormalMultilinearSeries 𝕜 E F` is defined as `∀ n : ℕ, E [×n]→L[𝕜] F`, a dependent function from $\mathbb{N}$ to the spaces of continuous multilinear maps. The term $p_n(y^n)$ is written `p n (fun _ => y)`.

<?decl FormalMultilinearSeries?>
:::

A formal multilinear series is not determined by the function it defines. Let $E = \mathbb{K}^2$, and let $p_2(v, w) = v_1 w_2$ and $q_2(v, w) = v_2 w_1$, with all other terms zero. Then $p_2 \ne q_2$, but $p_2(y, y) = y_1 y_2 = q_2(y, y)$ for every $y$. Only the symmetric part of $p_n$ is seen on the diagonal. Mathlib works with all series, not only symmetric ones.

**Definition (Radius of convergence).** The *radius of convergence* of $p$ is
$$R(p) = \sup\big\{ r \ge 0 : \sup_n \|p_n\|\, r^n < \infty \big\} \in [0, \infty].$$

**Definition (Power series expansion).** Let $f : E \to F$, $x \in E$ and $0 < r \le \infty$. The function $f$ *has the expansion $p$ on the ball $B(x, r)$* if $r \le R(p)$ and
$$f(x + y) = \sum_{n=0}^\infty p_n(y^n) \quad \text{for all } y \text{ with } \|y\| < r.$$
The function $f$ *has an expansion at $x$* if this holds for some $r > 0$.

**Definition (Analytic function).** A function $f$ is *analytic at $x$* if it has an expansion at $x$ for some $p$. It is *analytic on a set $s$* if it is analytic at each point of $s$.

::: mathlib
`FormalMultilinearSeries.radius` · `Mathlib.Analysis.Analytic.ConvergenceRadius`

The radius is `⨆ (r : ℝ≥0) (C : ℝ) (_ : ∀ n, ‖p n‖ * r ^ n ≤ C), (r : ℝ≥0∞)`. Its type is `ℝ≥0∞`, the extended nonnegative reals, so that the radius $\infty$ needs no special case. The basic lower bound is `FormalMultilinearSeries.le_radius_of_bound`: from `∀ n, ‖p n‖ * r ^ n ≤ C` it gives `(r : ℝ≥0∞) ≤ p.radius`.

<?decl FormalMultilinearSeries.radius?>
:::

::: mathlib
`HasFPowerSeriesOnBall` · `Mathlib.Analysis.Analytic.Basic`

`HasFPowerSeriesOnBall f p x r` is a structure with three fields: `r_le : r ≤ p.radius`, `r_pos : 0 < r`, and `hasSum : ∀ {y}, y ∈ Metric.eball 0 r → HasSum (fun n => p n (fun _ => y)) (f (x + y))`. The radius `r` is in `ℝ≥0∞`, so the ball is `Metric.eball`, the ball for the extended distance. `HasFPowerSeriesAt f p x` is `∃ r, HasFPowerSeriesOnBall f p x r`.

<?decl HasFPowerSeriesOnBall?>
:::

::: mathlib
`AnalyticAt` · `Mathlib.Analysis.Analytic.Basic`

`AnalyticAt 𝕜 f x` is `∃ p, HasFPowerSeriesAt f p x`. The field `𝕜` is explicit, because a map on a complex space can be real analytic without being complex analytic. On a set there are two notions. `AnalyticOnNhd 𝕜 f s` is `∀ x ∈ s, AnalyticAt 𝕜 f x`, the definition above. `AnalyticOn 𝕜 f s` asks only for an expansion within `s` at each point, a weaker condition. On an open set the two agree.

<?decl AnalyticAt?>
:::

### Theorems and proofs

**Theorem (Convergence inside the radius).** Let $p$ be a formal multilinear series and $R = R(p)$.

1. If $0 \le r < R$, then there are $C$ and $a < 1$ with $\|p_n\| r^n \le C a^n$ for all $n$, and $\sum_n \|p_n\|\, r^n < \infty$.
2. If $r > R$, then $\|p_n\| r^n$ is unbounded, and $\sum_n \|p_n\| r^n = \infty$.

So if $F$ is complete and $\|y\| < R$, the series $\sum_n p_n(y^n)$ converges absolutely.

*Proof.* 1. Since $r < R$, the definition of the supremum gives $s$ with $r < s$ and $\|p_n\| s^n \le C$ for all $n$. For $s = 0$ the claim is trivial, so let $s > 0$ and $a = r/s < 1$. Then $\|p_n\| r^n = \|p_n\| s^n a^n \le C a^n$, and the geometric series gives the sum.

2. If $\|p_n\| r^n \le C$ for all $n$, then $r \le R$ by the definition, a contradiction. A series of nonnegative terms that are unbounded diverges.

For the last claim, $\|p_n(y^n)\| \le \|p_n\|\,\|y\|^n$, so the series of norms converges by part 1 with $r = \|y\|$. In a Banach space an absolutely convergent series converges. $\square$

::: mathlib
`FormalMultilinearSeries.summable_norm_mul_pow` · `Mathlib.Analysis.Analytic.ConvergenceRadius`

For `r : ℝ≥0` with `↑r < p.radius`, it gives `Summable fun n => ‖p n‖ * (r : ℝ) ^ n`. Part 2 is `FormalMultilinearSeries.not_summable_norm_of_radius_lt_nnNorm`: if `p.radius < ‖x‖₊`, the series `‖p n‖ * ‖x‖ ^ n` is not summable. Part 2 concerns the norms $\|p_n\|$, not the values $p_n(y^n)$, which can vanish on the diagonal.

<?decl FormalMultilinearSeries.summable_norm_mul_pow?>
:::

**Theorem (Cauchy and Hadamard).** Let $L = \limsup_n \|p_n\|^{1/n} \in [0, \infty]$. Then $R(p) = 1/L$, with $1/0 = \infty$ and $1/\infty = 0$.

*Proof.* First, $R \le 1/L$. Let $r < R$ with $r > 0$. Part 1 of the previous theorem gives $\|p_n\| \le C a^n r^{-n}$, so $\|p_n\|^{1/n} \le C^{1/n} a / r$, and $C^{1/n} \to 1$. So $L \le a/r < 1/r$. Since $r < R$ is arbitrary, $L \le 1/R$.

Second, $R \ge 1/L$. Let $r \ge 0$ with $rL < 1$, and choose $q$ with $rL < q < 1$. For $r > 0$, $q/r > L$, so $\|p_n\|^{1/n} < q/r$ for all large $n$. Then $\|p_n\| r^n < q^n \le 1$ for large $n$, the sequence $\|p_n\| r^n$ is bounded, and $r \le R$. Every $r < 1/L$ satisfies $rL < 1$, so $1/L \le R$. $\square$

::: mathlib
`FormalMultilinearSeries.radius_eq_liminf` · `Mathlib.Analysis.Analytic.RadiusLiminf`

The formula of Cauchy and Hadamard in the form `p.radius = liminf (fun n => (1 / (‖p n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop`.

<?decl FormalMultilinearSeries.radius_eq_liminf?>
:::

**Theorem (Analytic functions are continuous).** If $f$ has the expansion $p$ on $B(x, r)$, then $f(x) = p_0$ and $f$ is continuous at $x$.

*Proof.* For $y = 0$, every term with $n \ge 1$ vanishes, so $f(x) = p_0$. Choose $s$ with $0 < s < r$ and a bound $\|p_n\| s^n \le C$; it exists because $s < R(p)$. For $\|y\| \le s/2$,
$$\|f(x + y) - f(x)\| = \Big\|\sum_{n \ge 1} p_n(y^n)\Big\| \le \sum_{n \ge 1} C \Big(\frac{\|y\|}{s}\Big)^n = C\,\frac{\|y\|/s}{1 - \|y\|/s} \le \frac{2C}{s}\,\|y\|.$$
The right side tends to $0$ with $y$. $\square$

The proof gives more: $\|f(x + y) - f(x) - p_1(y)\| = O(\|y\|^2)$. Section 2 uses this to show that $Df(x) = p_1$.

::: mathlib
`AnalyticAt.continuousAt` · `Mathlib.Analysis.Analytic.Basic`

From `AnalyticAt 𝕜 f x` it gives `ContinuousAt f x`. The value at the center is `HasFPowerSeriesOnBall.coeff_zero`: `p 0 v = f x` for each `v : Fin 0 → E`.

<?decl AnalyticAt.continuousAt?>
:::

In one variable, the coefficients of an expansion are unique. If $\sum a_n z^n = 0$ for $|z| < r$ and $a_k$ is the first nonzero coefficient, then $z^{-k}\sum_n a_n z^n = a_k + z\sum_{n > k} a_n z^{n - k - 1}$. The second term tends to $0$ by the estimate of the last proof, so $a_k = 0$, a contradiction. In several variables the same argument along each line $t \mapsto ty$ shows that $p_n(y^n)$ is determined for each $y$, which is all that the diagonal example allows.

### Examples

**Example (The geometric series in a Banach algebra).** Let $\mathcal{A}$ be a Banach algebra with $\|1\| = 1$, and $p_n(y_1, \dots, y_n) = y_1 y_2 \cdots y_n$, with $p_0 = 1$. Then $\|p_n\| = 1$: the bound $\|y_1 \cdots y_n\| \le \|y_1\| \cdots \|y_n\|$ gives $\le 1$, and $y_i = 1$ gives equality. So $\|p_n\| r^n = r^n$, which is bounded if and only if $r \le 1$, and $R(p) = 1$. For $\|y\| < 1$,
$$(1 - y)\sum_{n < N} y^n = 1 - y^N \to 1,$$
and also $\big(\sum_{n<N} y^n\big)(1 - y) = 1 - y^N$. So the sum is $(1 - y)^{-1}$, and $y \mapsto (1 - y)^{-1}$ has the expansion $p$ on $B(0, 1)$. In Mathlib the series is `formalMultilinearSeries_geometric`, with the radius `formalMultilinearSeries_geometric_radius` and the expansion `hasFPowerSeriesOnBall_inverse_one_sub`.

**Example (The exponential).** In the same algebra let $p_n(y_1, \dots, y_n) = \frac{1}{n!}y_1 \cdots y_n$. Then $\|p_n\| r^n = r^n/n!$, which is bounded for every $r$, since $r^n/n! \to 0$. So $R(p) = \infty$, and $\exp y = \sum_n y^n/n!$ converges on all of $\mathcal{A}$. This is `NormedSpace.expSeries` with `NormedSpace.expSeries_radius_eq_top`.

**Example (A quadratic map).** Let $B : E \times E \to F$ be continuous bilinear and $f(x) = B(x, x)$. Then
$$f(x + y) = B(x, x) + \big(B(x, y) + B(y, x)\big) + B(y, y).$$
So $f$ has the expansion $p_0 = B(x, x)$, $p_1(y) = B(x, y) + B(y, x)$, $p_2 = B$ and $p_n = 0$ for $n \ge 3$, on the ball of radius $\infty$. The radius is $\infty$ because $\|p_n\| r^n$ is eventually $0$, which is `FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero`. Every continuous polynomial map is analytic in the same way.

**Example (The ratio test).** Let $c_n \in \mathbb{K}$ and $p_n = c_n \cdot (y_1, \dots, y_n \mapsto y_1 \cdots y_n)$ on $\mathbb{K}$, so $p_n(z^n) = c_n z^n$ and $\|p_n\| = |c_n|$. If $|c_{n+1}|/|c_n| \to \rho \ne 0$, then $|c_n|^{1/n} \to \rho$ and $R = 1/\rho$. For $c_n = 2^n$ the ratio is $2$ and $R = \frac12$.

**Counterexample (The radius is not visible on the real line).** The function $f(x) = 1/(1 + x^2)$ is analytic at every point of $\mathbb{R}$, since it is a quotient of polynomials with a nonzero denominator (Section 3). Its expansion at $0$ is $\sum_n (-1)^n x^{2n}$, and the radius is $1$, although $f$ is smooth and bounded on all of $\mathbb{R}$. The obstruction lies at the complex zeros $\pm i$ of $1 + z^2$.

::: mathlib
`FormalMultilinearSeries.ofScalars` · `Mathlib.Analysis.Analytic.OfScalars`

`ofScalars E c` is the series with `p n = c n • ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E`, for a normed algebra `E` and scalars `c : ℕ → 𝕜`. The ratio test is `FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto`: with `[NormOneClass E]`, `r ≠ 0` and `Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)`, the radius is `r⁻¹`.

<?decl FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto?>
:::

### The library around it

The type is in `Mathlib.Analysis.Calculus.FormalMultilinearSeries`, the radius and the sum `p.sum` in `Mathlib.Analysis.Analytic.ConvergenceRadius`, and the expansions in `Mathlib.Analysis.Analytic.Basic`. The predicates come in a family: `HasFPowerSeriesOnBall`, `HasFPowerSeriesAt`, `AnalyticAt`, `AnalyticOnNhd`, and their versions within a set.

The module `Mathlib.Analysis.Analytic.RadiusLiminf` holds the formula of Cauchy and Hadamard above, `FormalMultilinearSeries.radius_eq_liminf`, and its form for the inverse, `FormalMultilinearSeries.radius_inv_eq_limsup`: $1/R = \limsup_n \|p_n\|^{1/n}$.

The module `Mathlib.Analysis.Analytic.Binomial` gives the binomial series. For a field $\mathbb{K}$ of characteristic $0$ and a $\mathbb{K}$-algebra $\mathbb{A}$, `binomialSeries 𝔸 a` has the term of degree $n$ equal to $\binom{a}{n} x^n$, with the generalized binomial coefficient `Ring.choose a n` (`binomialSeries_apply`). Its radius is at least $1$ (`binomialSeries_radius_ge_one`), exactly $1$ when $a$ is not a natural number (`binomialSeries_radius_eq_one`), and $\infty$ when it is (`binomialSeries_radius_eq_top_of_nat`). Over $\mathbb{R}$ and $\mathbb{C}$ it is the series of $(1 + x)^a$ on the unit ball: `Real.one_add_rpow_hasFPowerSeriesOnBall_zero` and `Complex.one_add_cpow_hasFPowerSeriesOnBall_zero`. The module also gives the series at $0$ of $1/(r - x)$, $1/(r - x)^2$ and $1/(r - x)^{a+1}$, for example `Real.one_div_sub_hasFPowerSeriesOnBall_zero` with radius $|r|$, and it writes the binomial series as a hypergeometric series (`binomialSeries_eq_ordinaryHypergeometricSeries`).

The module `Mathlib.Analysis.Analytic.Within` explains the versions within a set by the versions at a point. A function is analytic within $s$ at $x$ if and only if it agrees near $x$ in $s \cup \{x\}$ with a function that is analytic at $x$ (`analyticWithinAt_iff_exists_analyticAt`); the same holds for power series (`hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt`). On an open set the two notions agree: `IsOpen.analyticOn_iff_analyticOnNhd`. Analyticity within $s$ is local: `analyticOn_of_locally_analyticOn`, and `AnalyticWithinAt.eventually_analyticWithinAt` says that it holds at all points of $s$ near $x$. Most of these results need $F$ complete.

Common errors of a learner:

- Expecting the coefficients of an analytic function to be unique. They are unique only after symmetrization; the diagonal example shows two different series with one sum.
- Treating the radius as a real number. It is in `ℝ≥0∞`, and comparisons with a real `r` go through the coercion `(r : ℝ≥0∞)`.
- Using `AnalyticOn` for the classical notion on an open set. It is the weaker version within a set. Use `AnalyticOnNhd`, or prove the agreement on an open set.

### Exercises

1. (A) Find the radius of $\sum_n z^n/2^n$ and of $\sum_n n!\,z^n$ on $\mathbb{C}$.
2. (A) Show that $R(p + q) \ge \min(R(p), R(q))$.
3. (A) In the quadratic example with $E = F = \mathbb{R}$ and $B(x, y) = xy$, write the expansion of $x^2$ at $x = 3$.
4. (B) Let $p_n = c_n \cdot (y_1 \cdots y_n)$ on $\mathbb{K}$ with $c_n = 1$ for even $n$ and $c_n = 2^n$ for odd $n$. Show that the ratio $|c_{n+1}|/|c_n|$ has no limit, and compute $R$ by the formula of Cauchy and Hadamard.
5. (B) Let $\mathcal{A}$ be a Banach algebra with $\|1\| = 1$ and $a \in \mathcal{A}$ with $\|a\| < 1$. Find a series for $y \mapsto (1 - a - y)^{-1}$ at $0$ and a lower bound for its radius. Hint: $1 - a - y = (1 - a)(1 - (1 - a)^{-1}y)$.
6. (C) Prove that if $f$ has the expansion $p$ on $B(x, r)$ and $p_1 = 0$, then $\|f(x + y) - f(x)\| = O(\|y\|^2)$. Deduce that $f$ is differentiable at $x$ with $Df(x) = 0$.

### Notes and history

Cauchy stated the formula for the radius in his *Cours d'analyse* (1821), and Hadamard found it again later. Mathlib takes the radius as a supremum of bounds rather than as $1/\limsup$, because the bounds are what the proofs use.

### Reference

<?reference?>
