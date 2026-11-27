---
title: The Cauchy integral formula and analyticity
kind: theory
modules:
  - Mathlib.Analysis.Complex.CauchyIntegral
  - Mathlib.Analysis.Complex.TaylorSeries
explains:
  E3: [Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable, DifferentiableOn.hasFPowerSeriesOnBall, Complex.analyticOnNhd_iff_differentiableOn, Complex.hasSum_taylorSeries_on_ball]
  E2: [Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable, DiffContOnCl.circleIntegral_sub_inv_smul, DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul, Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable, DiffContOnCl.hasFPowerSeriesOnBall, Differentiable.hasFPowerSeriesOnBall, DifferentiableOn.analyticAt, DifferentiableOn.analyticOnNhd, Differentiable.analyticAt, Complex.analyticAt_iff_eventually_differentiableAt, DifferentiableOn.contDiffOn, Differentiable.contDiff, DifferentiableOn.deriv, DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul, DiffContOnCl.deriv_eq_smul_circleIntegral, Complex.taylorSeries_eq_on_ball, Complex.hasSum_taylorSeries_of_entire, Complex.taylorSeries_eq_of_entire']
  E1: auto
families: []
requires: [V19.C01, V17.C07, V18.C05, V18.C08]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Cauchy integral formula and analyticity

### Overview

The Cauchy integral formula expresses the values of a holomorphic function inside a disc by its values on the boundary circle:
$$f(w) = \frac{1}{2\pi i}\oint_{C(c,R)} \frac{f(z)}{z - w}\,dz.$$
The kernel $1/(z - w)$ is a geometric series in $w - c$. Integrating it term by term turns the formula into a power series for $f$ that converges on the whole disc. So a holomorphic function is analytic. By Volume 17, Chapter 7, it is then infinitely differentiable, its derivatives are holomorphic, and the coefficients are $f^{(n)}(c)/n!$. The section ends with Taylor series: on any disc in its domain, a holomorphic function is the sum of its Taylor series, and an entire function is the sum of its Taylor series on all of $\mathbb{C}$.

The section uses Section 2, the power series of Volume 17, Chapter 7, and limits of integrals from Volume 18.

### Definitions

**Definition (Cauchy coefficients).** Let $f$ be continuous on the circle $C(c, R)$ with $R > 0$. Its *Cauchy coefficients* are
$$a_n = \frac{1}{2\pi i}\oint_{C(c,R)} \frac{f(z)}{(z - c)^{n+1}}\,dz, \qquad n \ge 0,$$
and the power series $\sum_n a_n (w - c)^n$ is the *Cauchy power series* of $f$ on $C(c,R)$.

**Definition (Analytic).** Recall from Volume 17, Chapter 7 that $f$ is *analytic at* $c$ if $f(w) = \sum_n a_n (w - c)^n$ for all $w$ near $c$, for some convergent power series. It is analytic on an open set $U$ if it is analytic at each point of $U$.

::: mathlib
`cauchyPowerSeries` · `Mathlib.MeasureTheory.Integral.CircleIntegral`

`cauchyPowerSeries f c R : FormalMultilinearSeries ℂ ℂ E` is the series of the definition. It belongs to the theory of the circle integral, which is in Volume 18, together with the bound `norm_cauchyPowerSeries_le`.

<?decl cauchyPowerSeries?>
:::

### Theorems and proofs

**Lemma (The kernel).** Let $|w - c| < R$. Then
$$\frac{1}{z - w} = \sum_{n=0}^{\infty} \frac{(w - c)^n}{(z - c)^{n+1}}$$
uniformly for $|z - c| = R$, and $\oint_{C(c,R)} \frac{dz}{z - w} = 2\pi i$.

*Proof.* Put $q = |w - c|/R < 1$. For $|z - c| = R$,
$$\frac{1}{z - w} = \frac{1}{(z - c) - (w - c)} = \frac{1}{z - c}\cdot\frac{1}{1 - \frac{w - c}{z - c}},$$
and $|(w - c)/(z - c)| = q$. The geometric series converges, and the $n$-th term has modulus $q^n/R$, so the convergence is uniform by the Weierstrass M-test. A uniformly convergent series of continuous functions on a compact interval can be integrated term by term. By the computation of Section 2, $\oint (z - c)^{-n-1}\,dz$ is $2\pi i$ for $n = 0$ and $0$ for $n \ge 1$. $\square$

**Theorem (Cauchy integral formula).** Let $f$ be continuous on the closed disc $\bar D = \bar D(c, R)$ and holomorphic on the open disc $D$. Then for every $w \in D$,
$$f(w) = \frac{1}{2\pi i}\oint_{C(c,R)} \frac{f(z)}{z - w}\,dz.$$

*Proof.* Define $g(z) = (f(z) - f(w))/(z - w)$ for $z \ne w$ and $g(w) = f'(w)$. Then $g$ is continuous on $\bar D$, by the definition of $f'(w)$, and holomorphic on $D \setminus \{w\}$.

Step 1. The boundary integral of $g$ vanishes over every closed rectangle $Q \subseteq D$. If $w \notin Q$, this is Goursat. Otherwise, cut $Q$ into $N^2$ congruent rectangles. Those that do not contain $w$ give $0$. At most four contain $w$, and each has perimeter at most $p/N$, where $p$ is the perimeter of $Q$. With $M = \sup_{\bar D}|g|$, this gives $|\eta(g; Q)| \le 4Mp/N$. Let $N \to \infty$.

Step 2. Let $0 < \rho < R$. The proof of primitives in Section 2 used only continuity and Step 1, so $g$ has a primitive $G$ on $D$. Then $\theta \mapsto G(c + \rho e^{i\theta})$ has derivative $g(c + \rho e^{i\theta})\, i\rho e^{i\theta}$, and the fundamental theorem of calculus gives $\oint_{C(c,\rho)} g = G(c + \rho) - G(c + \rho) = 0$.

Step 3. As $\rho \to R$, the integrands $g(c + \rho e^{i\theta})i\rho e^{i\theta}$ converge uniformly in $\theta$, because $g$ is uniformly continuous on the compact set $\bar D$. So $\oint_{C(c,R)} g = 0$.

Step 4. Expand: $0 = \oint \frac{f(z)}{z - w}dz - f(w)\oint \frac{dz}{z - w}$, and the lemma gives the second integral. $\square$

::: mathlib
`Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable` · `Mathlib.Analysis.Complex.CauchyIntegral`

The statement, for `f : ℂ → E` with `E` a complex Banach space, takes `s.Countable`, `w ∈ ball c R`, `ContinuousOn f (closedBall c R)` and differentiability on `ball c R \ s`, and concludes `∮ z in C(c, R), (z - w)⁻¹ • f z = (2 * π * I) • f w`. Mathlib's proof is shorter than the one above: the countable set of Section 2 absorbs the point $w$, so Steps 1 to 3 are not needed. The form with `DiffContOnCl ℂ f (ball c R)` is `DiffContOnCl.circleIntegral_sub_inv_smul`, and the form solved for `f w` is `DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul`.

<?decl Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable?>
:::

**Theorem (Holomorphic functions are analytic).** Let $f$ be continuous on $\bar D(c, R)$ and holomorphic on $D(c, R)$, and let $(a_n)$ be its Cauchy coefficients. Then the radius of convergence of $\sum a_n (w - c)^n$ is at least $R$, and
$$f(w) = \sum_{n=0}^{\infty} a_n (w - c)^n \qquad \text{for } |w - c| < R.$$

*Proof.* Let $M = \sup_{|z - c| = R}|f(z)|$. The circle has length $2\pi R$ and $|z - c|^{n+1} = R^{n+1}$ on it, so $|a_n| \le \frac{1}{2\pi} \cdot 2\pi R \cdot \frac{M}{R^{n+1}} = \frac{M}{R^n}$. Then $|a_n|^{1/n} \le M^{1/n}/R \to 1/R$, so the radius is at least $R$ by the formula of Cauchy and Hadamard (Volume 17, Chapter 7). Fix $w$ with $|w - c| < R$. Multiply the series of the lemma by the bounded continuous function $f(z)/(2\pi i)$. The product still converges uniformly on the circle, so
$$f(w) = \frac{1}{2\pi i}\oint \frac{f(z)}{z - w}dz = \sum_n \frac{(w - c)^n}{2\pi i}\oint\frac{f(z)}{(z - c)^{n+1}}dz = \sum_n a_n (w - c)^n. \qquad \square$$

**Corollary.** Let $U \subseteq \mathbb{C}$ be open. Then $f$ is holomorphic on $U$ if and only if it is analytic on $U$. In that case $f$ is infinitely complex differentiable on $U$, every derivative $f^{(n)}$ is holomorphic on $U$, and for every closed disc $\bar D(c, R) \subseteq U$,
$$f^{(n)}(c) = \frac{n!}{2\pi i}\oint_{C(c,R)} \frac{f(z)}{(z - c)^{n+1}}\,dz.$$

*Proof.* If $f$ is holomorphic on $U$ and $c \in U$, choose $R > 0$ with $\bar D(c, R) \subseteq U$. The theorem gives a power series at $c$, so $f$ is analytic at $c$. Conversely an analytic function is complex differentiable (Volume 17, Chapter 7). The same chapter shows that an analytic function is $C^\infty$, that its derivative is analytic, and that the coefficients of its series at $c$ are $f^{(n)}(c)/n!$. By uniqueness of the coefficients, $a_n = f^{(n)}(c)/n!$, which is the formula. $\square$

::: mathlib
`DifferentiableOn.hasFPowerSeriesOnBall` · `Mathlib.Analysis.Complex.CauchyIntegral`

The statement is `DifferentiableOn ℂ f (closedBall c R) → 0 < R → HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R`, with `R : NNReal`. The general form, with a countable exceptional set and continuity on the closed ball only, is `Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable`. For entire functions, `Differentiable.hasFPowerSeriesOnBall` gives the radius `⊤`. The formula for derivatives is `DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul`, with the right side `(2 * π * I / n !) • iteratedDeriv n f c`.

<?decl DifferentiableOn.hasFPowerSeriesOnBall?>
<?decl HasFPowerSeriesOnBall?>
:::

::: mathlib
`Complex.analyticOnNhd_iff_differentiableOn` · `Mathlib.Analysis.Complex.CauchyIntegral`

For an open `s`, `AnalyticOnNhd ℂ f s ↔ DifferentiableOn ℂ f s`. The pointwise form is `Complex.analyticAt_iff_eventually_differentiableAt : AnalyticAt ℂ f c ↔ ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z`. The consequences are `DifferentiableOn.analyticAt`, `Differentiable.analyticAt`, `DifferentiableOn.contDiffOn` (with `IsOpen s`) and `DifferentiableOn.deriv`.

<?decl Complex.analyticOnNhd_iff_differentiableOn?>
<?decl AnalyticAt?>
:::

**Theorem (Taylor series).** Let $f$ be holomorphic on the open disc $D(c, r)$. Then for every $z \in D(c, r)$,
$$f(z) = \sum_{n=0}^{\infty} \frac{f^{(n)}(c)}{n!}(z - c)^n.$$
If $f$ is entire, this holds for all $z \in \mathbb{C}$.

*Proof.* Let $|z - c| < r$, and choose $R$ with $|z - c| < R < r$. Then $f$ is holomorphic on a neighbourhood of $\bar D(c, R)$. By the theorem and the corollary, $f(z) = \sum_n a_n (z - c)^n$ with $a_n = f^{(n)}(c)/n!$. For entire $f$, every $z$ lies in some disc $D(c, r)$. $\square$

::: mathlib
`Complex.hasSum_taylorSeries_on_ball` · `Mathlib.Analysis.Complex.TaylorSeries`

The statement is `DifferentiableOn ℂ f (ball c r) → z ∈ ball c r → HasSum (fun n ↦ (n !)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z)`. The `tsum` form is `Complex.taylorSeries_eq_on_ball`, and the entire case is `Complex.hasSum_taylorSeries_of_entire`, with `Complex.taylorSeries_eq_of_entire'` for scalar functions.

<?decl Complex.hasSum_taylorSeries_on_ball?>
:::

### Examples

**Example.** $\oint_{C(0,1)} \frac{e^z}{z}\,dz = 2\pi i e^0 = 2\pi i$, by the formula with $w = 0$. The derivative formula with $n = 2$ gives $\oint_{C(0,1)} \frac{e^z}{z^3}\,dz = \frac{2\pi i}{2!}e^0 = \pi i$.

**Example.** Compute $\oint_{C(0,2)} \frac{dz}{z^2 + 1}$. Partial fractions give $\frac{1}{z^2 + 1} = \frac{1}{2i}\big(\frac{1}{z - i} - \frac{1}{z + i}\big)$. By the lemma, each of the two integrals is $2\pi i$, so the result is $0$.

**Example.** The function $f(x) = 1/(1 + x^2)$ is analytic on all of $\mathbb{R}$, but its Taylor series at $0$, $\sum (-1)^n x^{2n}$, has radius $1$. The complex view explains this. The extension $1/(1 + z^2)$ is holomorphic on $D(0, 1)$, so the radius is at least $1$. It is unbounded near $\pm i$, so the radius is not more than $1$.

### The library around it

Common errors of a learner:

- Stating the formula with `f z / (z - w)`. For values in a general `E`, Mathlib writes `(z - w)⁻¹ • f z`.
- Expecting `DifferentiableAt ℂ f c` alone to give `AnalyticAt ℂ f c`. Differentiability is needed on a neighbourhood.
- Using `DifferentiableOn.hasFPowerSeriesOnBall` with an open ball hypothesis. It needs the closed ball; on an open ball use `Complex.hasSum_taylorSeries_on_ball`.

### Exercises

1. (A) Compute $\oint_{C(0,2)} \frac{\cos z}{z - 1}\,dz$ and $\oint_{C(0,2)} \frac{\sin z}{z^4}\,dz$.
2. (A) Find the radius of convergence of the Taylor series of $1/\cos z$ at $0$. Hint: the nearest zeros of $\cos$ are $\pm\pi/2$.
3. (B) Let $f$ be holomorphic on a neighbourhood of $\bar D(c, R)$ with $|f| \le M$ on $C(c, R)$. Show that $|f^{(n)}(c)| \le n!\,M/R^n$. Chapter 3 calls these the Cauchy estimates.
4. (B) Show that a function with a primitive on an open set is holomorphic there. Deduce Morera's theorem: a continuous $f$ on $U$ whose rectangle integrals vanish is holomorphic. Hint: Section 2 gives a primitive on discs.
5. (B) Show that $\frac{1}{2\pi}\int_0^{2\pi} |f(c + Re^{i\theta})|^2\,d\theta = \sum_n |a_n|^2 R^{2n}$ when $f$ is holomorphic on a neighbourhood of $\bar D(c, R)$. Hint: orthogonality of $e^{in\theta}$.
6. (C) Let $U$ be open, $L$ a line, and $f$ continuous on $U$ and holomorphic on $U \setminus L$. Show that $f$ is holomorphic on $U$. Hint: Morera and Exercise 5 of Section 2.

### Notes and history

The integral formula is due to Cauchy. The consequence that holomorphic functions are analytic separates complex analysis from real analysis, where a differentiable function need not even be twice differentiable.

### Reference

<?reference?>
