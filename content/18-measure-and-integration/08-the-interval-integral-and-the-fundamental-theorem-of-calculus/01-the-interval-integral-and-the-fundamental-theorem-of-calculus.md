---
title: The interval integral and the fundamental theorem of calculus
kind: theory
modules:
  - Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
  - Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
  - Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
  - Mathlib.MeasureTheory.Integral.IntegralEqImproper
  - Mathlib.Analysis.SpecialFunctions.Integrals.Basic
  - Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
explains:
  E3: [intervalIntegral, IntervalIntegrable, intervalIntegral.integral_add_adjacent_intervals, intervalIntegral.integral_hasDerivAt_right, intervalIntegral.integral_eq_sub_of_hasDerivAt, MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto]
  E2: [intervalIntegrable_iff, intervalIntegral.integral_of_le, intervalIntegral.integral_same, intervalIntegral.integral_symm, intervalIntegral.integral_const, intervalIntegral.norm_integral_le_integral_norm, Continuous.intervalIntegrable, Continuous.deriv_integral, intervalIntegral.integral_mul_deriv_eq_deriv_mul, intervalIntegral.integral_comp_mul_deriv, integrableOn_Ioi_rpow_iff, integral_Ioi_rpow_of_lt, integral_exp_neg_Ioi_zero, integral_pow, integral_inv_one_add_sq, integral_Ioi_inv_one_add_sq, MeasureTheory.intervalIntegral_tendsto_integral_Ioi]
  E1: auto
families: []
requires: [V15, V18.C03, V18.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The interval integral and the fundamental theorem of calculus

### Overview

This section defines $\int_a^b f$ as a Bochner integral over an interval, with a sign when $b < a$, so that additivity holds in all orders. It proves the two forms of the fundamental theorem of calculus: the derivative of an integral in its upper limit, and an integral computed from a primitive. Integration by parts, substitution and improper integrals on half lines follow in short.

### Definitions

Let $\lambda$ be Lebesgue measure on $\mathbb{R}$ (Chapter 3), let $E$ be a complete normed space and let $f : \mathbb{R} \to E$.

**Definition (Interval integrable).** The function $f$ is interval integrable between $a$ and $b$ if $f$ is integrable on $(\min(a, b), \max(a, b)]$.

**Definition (Interval integral).** For real $a$ and $b$,
$$\int_a^b f = \int_{(a, b]} f \, d\lambda - \int_{(b, a]} f \, d\lambda.$$

One of the two sets is empty. Thus $\int_a^b f = \int_{(a, b]} f$ when $a \le b$, and $\int_b^a f = -\int_a^b f$ for all $a$ and $b$. A point has measure $0$, so the choice of $(a, b]$ in place of $[a, b]$ does not change the value.

### Theorems and proofs

**Proposition 1 (Rules).** For all $a$, $b$ and a constant $c \in E$:

1. $\int_a^a f = 0$ and $\int_b^a f = -\int_a^b f$;
2. $\int_a^b c = (b - a)c$;
3. $\| \int_a^b f \| \le |\int_a^b \|f\||$;
4. a continuous function is interval integrable between all $a$ and $b$.

*Proof.* Items 1 and 2 follow from the definition and $\lambda((a, b]) = b - a$. Item 3 is the norm inequality of Chapter 5. For item 4, a continuous function is bounded on a compact interval, which has finite measure. $\square$

**Theorem 2 (Additivity).** If $f$ is interval integrable between $a$ and $b$ and between $b$ and $c$, then
$$\int_a^b f + \int_b^c f = \int_a^c f.$$

*Proof.* First let $a \le b \le c$. The sets $(a, b]$ and $(b, c]$ are disjoint with union $(a, c]$, and $f$ is integrable on both. Additivity of the integral over disjoint sets (Chapter 5) gives the formula. The other orders of $a$, $b$ and $c$ reduce to this one with item 1 of Proposition 1. $\square$

**Theorem 3 (Fundamental theorem of calculus, first form).** Let $f$ be interval integrable between $a$ and $b$, and continuous at $b$. Let $F(u) = \int_a^u f$. Then $F$ has the derivative $f(b)$ at $b$.

*Proof.* Let $\varepsilon > 0$. Continuity at $b$ gives $\delta > 0$ with $\|f(x) - f(b)\| \le \varepsilon$ for $|x - b| < \delta$. Then $f$ is bounded near $b$. With measurability of $f$ near $b$, it is interval integrable between $b$ and $b + h$ for $|h| < \delta$. By Theorem 2 and item 2 of Proposition 1,
$$F(b + h) - F(b) - h f(b) = \int_b^{b + h} (f(x) - f(b)) \, dx.$$
By item 3, the norm of the right side is at most $\varepsilon |h|$. Thus $\|F(b + h) - F(b) - h f(b)\| \le \varepsilon |h|$ for $|h| < \delta$, which is the definition of the derivative from Volume 15, Chapter 3. $\square$

Mathlib states this measurability as a hypothesis. It is true for continuous $f$. When $f$ is continuous everywhere, the result is `Continuous.deriv_integral`.

**Theorem 4 (Fundamental theorem of calculus, second form).** Let $f$ be differentiable at all points of $[a, b]$, with derivative $f'$, and let $f'$ be continuous on $[a, b]$. Then
$$\int_a^b f' = f(b) - f(a).$$

*Proof.* Take $E = \mathbb{R}$; for a general $E$ apply the result to $\ell \circ f$ for each continuous linear functional $\ell$. Let $G(x) = \int_a^x f' - f(x)$ for $x \in [a, b]$. By Theorem 3, applied to $f'$ extended continuously outside $[a, b]$, the function $G$ has derivative $f'(x) - f'(x) = 0$ at each point of $(a, b)$. $G$ is continuous on $[a, b]$, because both terms are. By the mean value theorem (Volume 15, Chapter 3), $G$ is constant on $[a, b]$. Then $G(b) = G(a) = -f(a)$, which is the claim. $\square$

Mathlib asks only that $f'$ be interval integrable. Its proof bounds $f'$ above by a lower semicontinuous function with a near integral, from the theorem of Vitali and Carathéodory. The counterexample below shows that integrability of $f'$ is necessary.

**Corollary 5 (Integration by parts).** Let $u$ and $v$ have derivatives $u'$ and $v'$ at each point of $[a, b]$, with $u'$ and $v'$ interval integrable. Then
$$\int_a^b u v' = u(b)v(b) - u(a)v(a) - \int_a^b u' v.$$

*Proof.* The product $uv$ has the derivative $u'v + uv'$, which is integrable because $u$ and $v$ are continuous. Apply the second form to $uv$ and use the linearity of the integral. $\square$

**Corollary 6 (Substitution).** Let $\varphi$ have a derivative $\varphi'$ at each point of $[a, b]$, with $\varphi'$ continuous on $[a, b]$, and let $g$ be continuous. Then
$$\int_a^b g(\varphi(x)) \varphi'(x) \, dx = \int_{\varphi(a)}^{\varphi(b)} g.$$

*Proof.* Let $G(y) = \int_{\varphi(a)}^y g$. By the first form, $G' = g$. By the chain rule, $(G \circ \varphi)' = (g \circ \varphi)\varphi'$, a continuous function. The second form gives $\int_a^b (g \circ \varphi)\varphi' = G(\varphi(b)) - G(\varphi(a)) = \int_{\varphi(a)}^{\varphi(b)} g$. $\square$

**Theorem 7 (Improper integrals).** Let $f$ be continuous on $[a, \infty)$ and differentiable on $(a, \infty)$, with derivative $f'$ integrable on $(a, \infty)$. If $f(x) \to m$ as $x \to \infty$, then
$$\int_{(a, \infty)} f' \, d\lambda = m - f(a).$$

*Proof.* For $n > a$, Mathlib's form of Theorem 4 gives $\int_a^n f' = f(n) - f(a)$. The functions $f' \mathbf{1}_{(a, n]}$ converge to $f' \mathbf{1}_{(a, \infty)}$ and are dominated by $|f'|$. By dominated convergence (Chapter 5), $\int_a^n f' \to \int_{(a, \infty)} f'$. The right side tends to $m - f(a)$. $\square$

### Examples

**Example (Three integrals).** By Theorem 4 with $f(x) = x^{n+1}/(n+1)$, $\int_a^b x^n \, dx = \frac{b^{n+1} - a^{n+1}}{n + 1}$. Let $s < -1$ and $c > 0$. The function $f(x) = x^{s+1}/(s+1)$ tends to $0$ at $\infty$, and $f' = x^s$ is positive. Its integral on $(c, n]$ is $f(n) - f(c) \le -f(c)$, so $x^s$ is integrable on $(c, \infty)$ by monotone convergence, and Theorem 7 gives $\int_{(c, \infty)} x^s \, dx = -\frac{c^{s+1}}{s+1}$. With $f = -e^{-x}$ the same argument gives $\int_{(0, \infty)} e^{-x} \, dx = 1$. With $f = \arctan$, whose derivative $\frac{1}{1 + x^2}$ is given in Volume 15, Chapter 6, $\int_{(0, \infty)} \frac{dx}{1 + x^2} = \frac{\pi}{2}$.

**Counterexample (A derivative that is not integrable).** Let $f(x) = x^2 \sin(x^{-2})$ for $x \ne 0$ and $f(0) = 0$. Then $f$ is differentiable at every point of $[0, 1]$, with $f'(0) = 0$, because $|f(h)| \le h^2$. For $x \ne 0$, $f'(x) = 2x \sin(x^{-2}) - 2x^{-1}\cos(x^{-2})$. Let $b_k = (2k\pi)^{-1/2}$ and $a_k = (2k\pi + \pi/2)^{-1/2}$ for $k \ge 1$. The intervals $[a_k, b_k]$ are disjoint and do not contain $0$, so $f'$ is continuous on them. Theorem 4 gives
$$\int_{a_k}^{b_k} |f'| \ge |f(b_k) - f(a_k)| = a_k^2 = \frac{1}{2k\pi + \pi/2}.$$
The sum over $k$ diverges, so $f'$ is not integrable on $[0, 1]$. In Mathlib the integral of a function that is not integrable is $0$. Thus `∫ x in 0..1, deriv f x` is $0$, but $f(1) - f(0) = \sin 1 \ne 0$. The hypothesis of integrability in `integral_eq_sub_of_hasDerivAt` is necessary.

### The library around it

Lean writes $\int_a^b f$ as `∫ x in a..b, f x`, notation for `intervalIntegral f a b volume`; any measure on $\mathbb{R}$ can replace `volume`. The rules of Proposition 1 are `intervalIntegral.integral_same`, `intervalIntegral.integral_symm`, `intervalIntegral.integral_const` and `intervalIntegral.norm_integral_le_integral_norm`. The lemma `intervalIntegral.integral_of_le` rewrites the integral as a set integral on `Ioc a b` when `a ≤ b`, and `intervalIntegrable_iff` gives `IntervalIntegrable` as integrability on `Ι a b`, the interval $(\min, \max]$.

::: mathlib
`intervalIntegral.integral_eq_sub_of_hasDerivAt` · `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`

The second form of the fundamental theorem, with derivatives on `uIcc a b` and an interval integrable derivative.

<?decl intervalIntegral.integral_eq_sub_of_hasDerivAt?>
:::

::: mathlib
`intervalIntegral.integral_hasDerivAt_right` · `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`

The first form. The hypothesis `StronglyMeasurableAtFilter f (𝓝 b)` asks for measurability of $f$ near $b$.

<?decl intervalIntegral.integral_hasDerivAt_right?>
:::

Integration by parts is `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, for functions with values in a normed algebra. Substitution is `intervalIntegral.integral_comp_mul_deriv`, for real functions. The index of this edition has no declaration for `intervalIntegral.integral_comp_smul_deriv`.

The computed integrals live in `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`: `integral_pow`, `integral_exp`, `integral_sin`, `integral_inv_one_add_sq` (the value $\arctan b - \arctan a$) and others. Improper integrals use `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto` and `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`. The values of the first example are `integral_Ioi_rpow_of_lt`, `integral_exp_neg_Ioi_zero` and `integral_Ioi_inv_one_add_sq`, and `integrableOn_Ioi_rpow_iff` states that $x^s$ is integrable on $(t, \infty)$ with $t > 0$ if and only if $s < -1$.

::: mathlib
`MeasureTheory.ContinuousOn.hasBoxIntegral` · `Mathlib.Analysis.BoxIntegral.Integrability`

`BoxIntegral` defines integrals as limits of Riemann sums over boxes. For a continuous function the two integrals agree.

<?decl MeasureTheory.ContinuousOn.hasBoxIntegral?>
:::

Common errors of a learner:

- The order of the limits matters: `∫ x in 1..0, x` is $-\frac{1}{2}$.
- An integral of a function that is not integrable is $0$, so a computation that drops the integrability hypothesis can give a false value without an error.
- `deriv f` is $0$ at points where $f$ is not differentiable. Use `HasDerivAt` hypotheses, not `deriv`, when the derivative is not known to exist.

### Exercises

1. (A) Compute $\int_{-1}^{2} (3x^2 - 2x) \, dx$ with Theorem 4.
2. (A) Show that $\int_a^b f + \int_b^a f = 0$ for all $a$, $b$ and all $f$, also when $f$ is not interval integrable.
3. (A) Use integration by parts to compute $\int_0^1 x e^x \, dx$.
4. (B) Show that $\int_0^\pi \sin^2 x \, dx = \frac{\pi}{2}$. *Hint:* integrate $\sin \cdot \sin$ by parts and use $\sin^2 + \cos^2 = 1$.
5. (B) Let $f$ be continuous and let $\alpha$ and $\beta$ be differentiable. Compute the derivative of $x \mapsto \int_{\alpha(x)}^{\beta(x)} f$. *Hint:* write the integral as $F(\beta(x)) - F(\alpha(x))$ with $F(u) = \int_0^u f$.
6. (B) Show that $\int_{(0, 1]} x^s \, dx = \frac{1}{s + 1}$ for $s > -1$. *Hint:* use Theorem 4 on $[\varepsilon, 1]$ and monotone convergence as $\varepsilon \to 0$.
7. (C) Let $f$ be integrable on $\mathbb{R}$ and $F(u) = \int_0^u f$. Show that $F$ is uniformly continuous. *Hint:* $|F(v) - F(u)| \le \int_{(u, v]} |f|$, and $\int_A |f| \le N \lambda(A) + \int_{\{|f| > N\}} |f|$, where the last term is small for large $N$ by dominated convergence.

### Notes and history

Lebesgue showed that the second form holds with his integral for a bounded derivative. Mathlib proves the form with an integrable derivative by semicontinuous approximation, not by the differentiation theorem of Section 2.

The interval integral, the fundamental theorem and integration by parts in Mathlib are by Yury Kudryashov, Patrick Massot and Sébastien Gouëzel. The improper integrals in `Mathlib.MeasureTheory.Integral.IntegralEqImproper` are by Anatole Dedecker and Bhavik Mehta. The computed integrals in `Mathlib.Analysis.SpecialFunctions.Integrals.Basic` are by Benjamin Davidson, and those in `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals` by David Loeffler.

### Reference

<?reference?>
