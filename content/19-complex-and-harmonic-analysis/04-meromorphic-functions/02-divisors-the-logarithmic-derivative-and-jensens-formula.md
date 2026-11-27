---
title: Divisors, the logarithmic derivative and Jensen's formula
kind: theory
modules:
  - Mathlib.Analysis.Meromorphic.Divisor
  - Mathlib.Analysis.Meromorphic.LogDeriv
  - Mathlib.Analysis.Meromorphic.FactorizedRational
  - Mathlib.Analysis.Meromorphic.TrailingCoefficient
  - Mathlib.Analysis.Complex.JensenFormula
explains:
  E3: [MeromorphicOn.divisor, MeromorphicOn.logDeriv_mul_eventuallyEq, Function.factorizedRational, MeromorphicOn.extract_zeros_poles, AnalyticOnNhd.circleAverage_log_norm, MeromorphicOn.circleAverage_log_norm]
  E2: [MeromorphicOn.divisor_def, MeromorphicOn.divisor_mul, MeromorphicOn.divisor_inv, MeromorphicOn.AnalyticOnNhd.divisor_nonneg, MeromorphicOn.logDeriv_zpow_eventuallyEq, Function.FactorizedRational.meromorphicOrderAt_eq, meromorphicTrailingCoeffAt, MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt, AnalyticOnNhd.circleAverage_log_norm_of_ne_zero, AnalyticOnNhd.sum_divisor_le, MeromorphicOn.log_norm_meromorphicTrailingCoeffAt]
  E1: auto
families: []
requires: [V19.C02, V19.C03, V18.C08, V17.C07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Divisors, the logarithmic derivative and Jensen's formula

### Overview

This section collects the orders of Section 1 into the divisor and uses it in three ways. The logarithmic derivative $f'/f$ turns products into sums. On a disc, the zeros and poles come out as a finite product $\prod (z - u)^{d(u)}$ times a zero free analytic factor. Jensen's formula computes the average of $\log|f|$ on a circle from the value at the centre and the zeros inside.

### Definitions

**Definition (Divisor).** Let $f$ be meromorphic on $U \subseteq \mathbb{K}$. Its divisor is the function $D_f : U \to \mathbb{Z}$ with $D_f(u) = \operatorname{ord}_u f$ when this order is finite and $D_f(u) = 0$ when it is $\infty$.

By the theorem on isolated zeros and poles of Section 1, the support of $D_f$ is locally finite in $U$: each $u \in U$ has a neighbourhood $V$ with $D_f = 0$ on $U \cap V \setminus \{u\}$.

**Definition (Logarithmic derivative).** For $f : \mathbb{K} \to \mathbb{K}$, the logarithmic derivative is $f'/f$.

**Definition (Factorized rational function).** For $d : \mathbb{K} \to \mathbb{Z}$ with finite support, $R_d(z) = \prod_u (z - u)^{d(u)}$.

**Definition (Trailing coefficient).** If $f = (z - x)^n g$ off $x$ near $x$, with $g$ analytic and $g(x) \ne 0$, the trailing coefficient of $f$ at $x$ is $g(x) = \lim_{z \to x} (z - x)^{-n} f(z)$.

### Theorems and proofs

**Theorem (Divisors).** Let $f, g : \mathbb{K} \to \mathbb{K}$ be meromorphic on $U$ with no order $\infty$. Then $D_{fg} = D_f + D_g$ and $D_{1/f} = -D_f$. If $U$ is compact, $D_f$ has finite support.

*Proof.* The first two claims are the product theorem of Section 1 at each point. For the third, finitely many of the neighbourhoods $V$ of the definition cover $U$, so the support lies in the finite set of their centres. $\square$

::: mathlib
`MeromorphicOn.divisor` · `Mathlib.Analysis.Meromorphic.Divisor`

`MeromorphicOn.divisor f U` is a function `𝕜 → ℤ` with locally finite support in `U`. By `MeromorphicOn.divisor_def` its value at `z` is `(meromorphicOrderAt f z).untop₀` if `MeromorphicOn f U ∧ z ∈ U`, and `0` otherwise. The rules are `MeromorphicOn.divisor_mul` and `MeromorphicOn.divisor_inv`.

<?decl MeromorphicOn.divisor?>
:::

**Theorem (Logarithmic derivative).** Let $f, g$ be meromorphic at $x$ with finite orders. Then $(fg)'/(fg) = f'/f + g'/g$ off $x$ near $x$. If $f = (z - x)^n h$ with $h(x) \ne 0$, then
$$\frac{f'(z)}{f(z)} = \frac{n}{z - x} + \frac{h'(z)}{h(z)}$$
off $x$ near $x$, with $h'/h$ analytic at $x$.

*Proof.* Off $x$ near $x$, $f$ and $g$ are differentiable and nonzero, by the factorization theorem of Section 1. Divide the product rule $(fg)' = f'g + fg'$ by $fg$. For the second, $((z - x)^n)' / (z - x)^n = n/(z - x)$, and $h'/h$ is analytic at $x$ because $h$ is analytic with $h(x) \ne 0$. $\square$

So $f'/f$ has a simple pole with residue $n$ at a zero or pole of order $n \ne 0$.

::: mathlib
`MeromorphicOn.logDeriv_mul_eventuallyEq` · `Mathlib.Analysis.Meromorphic.LogDeriv`

`logDeriv f` is `deriv f / f`. The theorem gives `logDeriv (f * g) =ᶠ[Filter.codiscreteWithin U] logDeriv f + logDeriv g`, an equality off a discrete subset of `U`. Powers are `MeromorphicOn.logDeriv_zpow_eventuallyEq`.

<?decl MeromorphicOn.logDeriv_mul_eventuallyEq?>
:::

**Theorem (Extraction of zeros and poles).** Let $f$ be meromorphic on $U$ with no order $\infty$, and let $D_f$ have finite support. Then there is $g$ analytic on $U$ with $g(u) \ne 0$ for all $u \in U$ and $f = R_{D_f} \cdot g$ on $U$ off a discrete subset of $U$.

*Proof.* Put $d = D_f$, extended by $0$ off $U$. Step 1: $R_d$ has order $d(u)$ at each $u$, since the other factors are analytic and nonzero at $u$. Step 2: $h = f / R_d$ is meromorphic on $U$ with order $d(u) - d(u) = 0$ at each $u \in U$, by the product theorem of Section 1. Step 3: let $g$ be the normal form of $h$ on $U$. At each point it is analytic with order $0$, so $g(u) \ne 0$. Step 4: $g = h$ off a discrete set, so $f = R_d \, g$ there. $\square$

::: mathlib
`MeromorphicOn.extract_zeros_poles` · `Mathlib.Analysis.Meromorphic.FactorizedRational`

`Function.factorizedRational d` is `fun z ↦ ∏ᶠ u, (z - u) ^ d u`. The theorem gives `g` with `AnalyticOnNhd 𝕜 g U`, `∀ u : U, g u ≠ 0` and `f` equal to `factorizedRational (divisor f U) • g` off a discrete set. Step 1 is `Function.FactorizedRational.meromorphicOrderAt_eq`.

<?decl Function.factorizedRational?>
<?decl MeromorphicOn.extract_zeros_poles?>
:::

**Theorem (Argument principle).** Let $f$ be meromorphic on a neighbourhood of $\overline{B}(c, R) \subseteq \mathbb{C}$, with no order $\infty$ and no zero or pole on the circle $|z - c| = R$. Then
$$\frac{1}{2\pi i} \oint_{|z - c| = R} \frac{f'(z)}{f(z)}\, dz = \sum_{|u - c| < R} D_f(u),$$
the number of zeros minus the number of poles, counted with order.

*Proof.* The divisor on a slightly larger closed disc has finite support, so there is $R' > R$ with $f$ meromorphic on $\overline{B}(c, R')$ and no zero or pole with $R \le |u - c| < R'$. Apply the extraction theorem on $B(c, R')$: $f = R_d \, g$ with $g$ analytic and without zeros, off a discrete set. Then the derivatives agree off a discrete set too, and on the circle $f'/f = \sum_u d(u)/(z - u) + g'/g$ by the product rule. The function $g'/g$ is holomorphic on $B(c, R')$, so its circle integral is $0$ by Chapter 2, Section 2. For $|u - c| < R$, $\oint (z - u)^{-1} dz = 2\pi i$. $\square$

::: mathlib
`circleIntegral.integral_sub_inv_of_mem_ball` · `Mathlib.MeasureTheory.Integral.CircleIntegral`

This gives `∮ z in C(c, R), (z - w)⁻¹ = 2 * π * I` for `w` in the ball, and `circleIntegral.integral_sub_zpow_of_ne` gives `0` for other integer powers. The index of this edition has no declaration for residues, the residue theorem or the argument principle.

<?decl circleIntegral.integral_sub_inv_of_mem_ball?>
<?decl circleIntegral.integral_sub_zpow_of_ne?>
:::

**Theorem (Jensen's formula).** Let $f$ be holomorphic on a neighbourhood of $\overline{B}(c, R)$, $R > 0$, with $f(c) \ne 0$. Then
$$\frac{1}{2\pi} \int_0^{2\pi} \log|f(c + Re^{i\theta})|\, d\theta = \log|f(c)| + \sum_{|a - c| \le R} D_f(a) \log \frac{R}{|a - c|}.$$

*Proof.* Step 1: the zeros of $f$ in the closed disc are finitely many, by the divisor theorem. By the extraction theorem, $f(z) = \prod_a (z - a)^{n_a}\, g(z)$ with $g$ holomorphic and zero free on a neighbourhood of $\overline{B}(c, R)$. Both sides are continuous off the zeros, so they agree there. So
$$\log|f(z)| = \sum_a n_a \log|z - a| + \log|g(z)|$$
for $z$ not a zero, so for all but finitely many points of the circle.

Step 2: the average of $\log|g|$ is $\log|g(c)|$. On a disc $B(c, R'')$ with $R'' > R$, $g$ has a holomorphic logarithm $L$, a primitive of $g'/g$ (Chapter 2, Section 2) plus a constant. Then $\log|g| = \operatorname{Re} L$, and the Cauchy formula at the centre (Chapter 2, Section 3) gives the claim.

Step 3: for $|a - c| \le R$, the average of $\log|z - a|$ is $\log R$. Write $z = c + R\zeta$ with $|\zeta| = 1$ and $b = (a - c)/R$. Then $|z - a| = R|\zeta - b| = R|1 - \bar b \zeta|$, since $|\zeta| = 1$. For $|b| < 1$, $1 - \bar b \zeta$ is zero free on a disc of radius $1/|b| > 1$, so Step 2 gives the average $0$. For $|b| = 1$, the integral $\int_0^{2\pi} \log|1 - e^{i\theta}|\, d\theta = 0$ of Exercise 3 gives the same value.

Step 4: averaging Step 1 gives $\sum_a n_a \log R + \log|g(c)|$. At $z = c$, Step 1 gives $\log|f(c)| = \sum_a n_a \log|c - a| + \log|g(c)|$. Subtract. $\square$

::: mathlib
`AnalyticOnNhd.circleAverage_log_norm` · `Mathlib.Analysis.Complex.JensenFormula`

The conclusion is `circleAverage (fun x ↦ log ‖f x‖) c R = ∑ᶠ u, divisor f (closedBall c |R|) u * log (R * ‖c - u‖⁻¹) + log ‖f c‖`. `Real.circleAverage f c R` is the average on the circle, for any real `R`, so the disc has radius `|R|`. Step 2 is `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero`, and Step 3 is `circleAverage_log_norm_sub_const_of_mem_closedBall`.

<?decl AnalyticOnNhd.circleAverage_log_norm?>
:::

**Theorem (Counting zeros).** In Jensen's formula, let $|f| \le M$ on the circle $|z - c| = R$, and let $0 < r < R$. Then the number $N(r)$ of zeros in $\overline{B}(c, r)$, with order, satisfies $N(r) \log(R/r) \le \log(M/|f(c)|)$.

*Proof.* The left side of Jensen's formula is at most $\log M$. Every term of the sum is $\ge 0$, and a zero in $\overline{B}(c, r)$ contributes at least $n_a \log(R/r)$. So $\log|f(c)| + N(r)\log(R/r) \le \log M$. $\square$

For meromorphic $f$, the same proof gives
$$\frac{1}{2\pi} \int_0^{2\pi} \log|f(c + Re^{i\theta})|\, d\theta = \log|t_c| + \sum_{u \ne c} D_f(u) \log \frac{R}{|u - c|} + D_f(c) \log R,$$
with $t_c$ the trailing coefficient at $c$ and the sum over $|u - c| \le R$.

::: mathlib
`MeromorphicOn.circleAverage_log_norm` · `Mathlib.Analysis.Complex.JensenFormula`

For `R ≠ 0`, this is the formula above. The term `u = c` of the sum is `log 0 = 0` in Lean. The counting theorem is `AnalyticOnNhd.sum_divisor_le`. `MeromorphicOn.log_norm_meromorphicTrailingCoeffAt` is the Poisson-Jensen formula.

<?decl MeromorphicOn.circleAverage_log_norm?>
:::

### Examples

**Example (One zero).** Let $f(z) = z - a$ with $0 < |a| < 1$, $c = 0$, $R = 1$. The right side of Jensen's formula is $\log|a| + \log(1/|a|) = 0$, and the left side is $0$ by Step 3.

**Example (The cotangent).** The sine has simple zeros at $k\pi$, so $(\sin)'/\sin = \cot$ has simple poles with residue $1$ there. On the circle $|z| = 4$, the argument principle counts the zeros $0, \pm\pi$: $\frac{1}{2\pi i}\oint \cot z\, dz = 3$.

### The library around it

`meromorphicTrailingCoeffAt f x` is the trailing coefficient, with `MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt` for the limit. The divisor of an analytic function is nonnegative by `MeromorphicOn.AnalyticOnNhd.divisor_nonneg`.

Common errors of a learner:

- Applying `MeromorphicOn.divisor_mul` without the hypotheses that no order is `⊤`. If $f = 0$, then $D_f = 0$ and $D_{fg} = 0$, but $D_g$ need not be $0$.
- Reading `log` as a function that fails at $0$. In Mathlib `Real.log 0 = 0`.

### Exercises

1. (A) Compute the divisor of $z^3/(z - 1)^2$ on $\mathbb{C}$ and its trailing coefficients at $0$ and $1$. Check Jensen's formula for $e^z$ on $|z| = R$.
2. (B) Use the argument principle to count the zeros of $z^5 + 3z + 1$ in $|z| < 2$. Hint: on the circle, $f = z^5 (1 + w)$ with $|w| \le 7/32$.
3. (B) Prove the identity $\int_0^{2\pi} \log|1 - e^{i\theta}|\, d\theta = 0$. Hint: use $|1 - e^{i\theta}| = 2|\sin(\theta/2)|$.
4. (C) Let $f$ be entire with $|f(z)| \le e^{|z|}$ and $f(0) = 1$. Show that the number of zeros in $|z| \le r$ is at most $2r/\log 2$. Hint: take $R = 2r$.
5. (C) Show that $\log|f|$ is subharmonic for holomorphic $f$: its value at the centre of a disc is at most its average on the circle.

### Notes and history

Jensen published his formula in 1899. The residue theorem is due to Cauchy.

### Reference

<?reference?>
