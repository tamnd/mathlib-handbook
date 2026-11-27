---
title: Inversion, Plancherel and Poisson summation
kind: theory
modules:
  - Mathlib.Analysis.Fourier.Inversion
  - Mathlib.Analysis.Fourier.LpSpace
  - Mathlib.Analysis.Fourier.PoissonSummation
explains:
  E3: [MeasureTheory.Integrable.fourierInv_fourier_eq, MeasureTheory.Lp.fourierTransformₗᵢ, Real.tsum_eq_tsum_fourier_of_rpow_decay]
  E2: [Continuous.fourierInv_fourier_eq, Continuous.fourier_fourierInv_eq, Real.tendsto_integral_gaussian_smul, Real.tendsto_integral_cexp_sq_smul, MeasureTheory.Lp.norm_fourier_eq, MeasureTheory.Lp.inner_fourier_eq, MeasureTheory.Lp.instFourierTransform, SchwartzMap.toLp_fourier_eq, Real.fourierCoeff_tsum_comp_add, Real.tsum_eq_tsum_fourier, Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable, SchwartzMap.tsum_eq_tsum_fourier]
  E1: auto
families: []
requires: [V15, V16.C06, V18.C05, V18.C06, V18.C07, V19.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Inversion, Plancherel and Poisson summation

### Overview

This section proves the three central theorems on the Fourier transform. The inversion theorem recovers $f$ from $\mathcal{F}f$ by the same integral with the opposite sign. Plancherel's theorem states that $\mathcal{F}$ preserves the $L^2$ norm, and so extends to a unitary map of $L^2$. The Poisson summation formula links the transform on $\mathbb{R}$ to the Fourier series of Chapter 6: the sum of the values of $f$ at the integers equals the sum of the values of $\mathcal{F}f$ at the integers.

The convention is $\mathcal{F}f(\xi) = \int e^{-2\pi i\langle x, \xi\rangle}f(x)\,dx$ and $\mathcal{F}^{-1}g(x) = \int e^{2\pi i\langle x, \xi\rangle}g(\xi)\,d\xi$ on a real inner product space $V$ of dimension $d$, so $\mathcal{F}^{-1}g(x) = \mathcal{F}g(-x)$.

### Definitions

**Definition (Approximate identity).** For $\varepsilon > 0$ put $\varphi_\varepsilon(z) = \varepsilon^{-d}e^{-\pi\|z\|^2/\varepsilon^2}$ on $V$. Then $\varphi_\varepsilon > 0$ and $\int\varphi_\varepsilon = 1$, by the Gaussian integral $\int_{\mathbb{R}}e^{-\pi t^2}\,dt = 1$ of Volume 15, Fubini, and the change of variables $z = \varepsilon u$. As $\varepsilon \to 0$ the mass concentrates at $0$: for each $\delta > 0$, $\sup_{\|z\| \ge \delta}\varphi_\varepsilon(z) = \varepsilon^{-d}e^{-\pi\delta^2/\varepsilon^2} \to 0$ and $\int_{\|z\| \ge \delta}\varphi_\varepsilon \to 0$.

**Definition (The transform on $L^2$).** The Fourier transform on $L^2(V)$ is the unique continuous extension of $\mathcal{F}$ from the Schwartz space, which is dense in $L^2$. The theorem of Plancherel below shows that this extension exists.

::: mathlib
`MeasureTheory.Lp.fourierTransformₗᵢ` · `Mathlib.Analysis.Fourier.LpSpace`

`Lp.fourierTransformₗᵢ E F : Lp F 2 volume ≃ₗᵢ[ℂ] Lp F 2 volume`, a linear isometric equivalence, for `F` a complex Hilbert space. The instance `Lp.instFourierTransform` makes `𝓕` act on `Lp F 2 volume` through it. The link with Schwartz space is `SchwartzMap.toLp_fourier_eq`: `𝓕 (f.toLp 2) = (𝓕 f).toLp 2`.

<?decl MeasureTheory.Lp.fourierTransformₗᵢ?>
<?decl MeasureTheory.Lp.instFourierTransform?>
<?decl SchwartzMap.toLp_fourier_eq?>
:::

### Theorems and proofs

**Lemma (Approximate identity).** Let $f : V \to E$ be integrable and continuous at $x$. Then $(\varphi_\varepsilon * f)(x) \to f(x)$ as $\varepsilon \to 0$.

*Proof.* Since $\int\varphi_\varepsilon = 1$,
$$(\varphi_\varepsilon * f)(x) - f(x) = \int\varphi_\varepsilon(z)\big(f(x - z) - f(x)\big)\,dz.$$
Let $\eta > 0$ and choose $\delta$ with $\|f(x - z) - f(x)\| < \eta$ for $\|z\| < \delta$. The part of the integral over $\|z\| < \delta$ has norm at most $\eta\int\varphi_\varepsilon = \eta$. The part over $\|z\| \ge \delta$ has norm at most
$$\Big(\sup_{\|z\| \ge \delta}\varphi_\varepsilon(z)\Big)\|f\|_1 + \|f(x)\|\int_{\|z\| \ge \delta}\varphi_\varepsilon,$$
and both terms tend to $0$. So the difference is at most $2\eta$ for small $\varepsilon$. $\square$

**Theorem (Fourier inversion).** Let $f : V \to E$ be integrable with $\mathcal{F}f$ integrable. If $f$ is continuous at $x$, then $\mathcal{F}^{-1}\mathcal{F}f(x) = f(x)$. In particular, a continuous $f$ with $f, \mathcal{F}f \in L^1$ satisfies $\mathcal{F}^{-1}\mathcal{F}f = f$ and $\mathcal{F}\mathcal{F}^{-1}f = f$.

*Proof.* The plan is to insert a Gaussian factor, move the transform to the other side, and remove the factor in two ways. Put $G_\varepsilon(\xi) = e^{-\pi\varepsilon^2\|\xi\|^2}$ and
$$I_\varepsilon(x) = \int e^{2\pi i\langle x, \xi\rangle}G_\varepsilon(\xi)\,\mathcal{F}f(\xi)\,d\xi.$$

Step 1: $I_\varepsilon(x) \to \mathcal{F}^{-1}\mathcal{F}f(x)$. As $\varepsilon \to 0$, $G_\varepsilon(\xi) \to 1$ for each $\xi$, and the integrand has norm at most $\|\mathcal{F}f(\xi)\|$, which is integrable by hypothesis. Apply dominated convergence.

Step 2: the transform of the factor. The Gaussian satisfies $\mathcal{F}(e^{-\pi\|\cdot\|^2}) = e^{-\pi\|\cdot\|^2}$ (box below). By the scaling rule of Section 1, Exercise 1, $\mathcal{F}G_\varepsilon = \varphi_\varepsilon$. By Exercise 2 of Section 1, the function $h(\xi) = e^{2\pi i\langle x, \xi\rangle}G_\varepsilon(\xi)$ has $\mathcal{F}h(y) = \varphi_\varepsilon(y - x)$.

Step 3: move the transform. The multiplication formula of Section 1 gives
$$I_\varepsilon(x) = \int h(\xi)\,\mathcal{F}f(\xi)\,d\xi = \int\mathcal{F}h(y)\,f(y)\,dy = \int\varphi_\varepsilon(y - x)f(y)\,dy = (\varphi_\varepsilon * f)(x),$$
since $\varphi_\varepsilon$ is even.

Step 4: by the lemma, $I_\varepsilon(x) \to f(x)$. Limits are unique, so $\mathcal{F}^{-1}\mathcal{F}f(x) = f(x)$. For the last claim, apply the first to $g(x) = f(-x)$, which has $\mathcal{F}g(\xi) = \mathcal{F}f(-\xi)$: this gives $\mathcal{F}\mathcal{F}^{-1}f = f$. $\square$

::: mathlib
`MeasureTheory.Integrable.fourierInv_fourier_eq` · `Mathlib.Analysis.Fourier.Inversion`

The statement is `𝓕⁻ (𝓕 f) v = f v` under `Integrable f`, `Integrable (𝓕 f)` and `ContinuousAt f v`. The global forms for continuous `f` are `Continuous.fourierInv_fourier_eq` and `Continuous.fourier_fourierInv_eq`. Mathlib proves Steps 1 to 3 as `Real.tendsto_integral_gaussian_smul`. Its parameter is $c = \varepsilon^{-2}/\pi$, with the kernel $(\pi c)^{d/2}e^{-\pi^2 c\|v - w\|^2}$. Step 1 alone is `Real.tendsto_integral_cexp_sq_smul`. The relation $\mathcal{F}^{-1}g(w) = \mathcal{F}g(-w)$ is `Real.fourierInv_eq_fourier_neg`.

<?decl MeasureTheory.Integrable.fourierInv_fourier_eq?>
<?decl Continuous.fourierInv_fourier_eq?>
<?decl Continuous.fourier_fourierInv_eq?>
<?decl Real.tendsto_integral_gaussian_smul?>
<?decl Real.tendsto_integral_cexp_sq_smul?>
<?decl Real.fourierInv_eq_fourier_neg?>
:::

::: mathlib
`fourier_gaussian_innerProductSpace` · `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`

The transform of $x \mapsto e^{-b\|x\|^2}$ on an inner product space, for `0 < b.re`. The one-variable form is `fourier_gaussian_pi`. The Gaussian integral `integral_gaussian` is $\int e^{-bx^2}dx = \sqrt{\pi/b}$.

<?decl fourier_gaussian_innerProductSpace?>
<?decl fourier_gaussian_pi?>
<?decl integral_gaussian?>
:::

**Theorem (Plancherel).** For $f$ in the Schwartz space, $\int\|\mathcal{F}f\|^2 = \int\|f\|^2$. The map $\mathcal{F}$ extends uniquely to a linear isometry of $L^2(V)$ onto itself, and it preserves inner products.

*Proof.* Take scalar $f$. Put $h = \overline{\mathcal{F}f}$, a Schwartz function. Its transform is
$$\mathcal{F}h(x) = \int e^{-2\pi i\langle x, \xi\rangle}\overline{\mathcal{F}f(\xi)}\,d\xi = \overline{\int e^{2\pi i\langle x, \xi\rangle}\mathcal{F}f(\xi)\,d\xi} = \overline{\mathcal{F}^{-1}\mathcal{F}f(x)} = \overline{f(x)},$$
by the inversion theorem. The multiplication formula gives $\int|\mathcal{F}f|^2 = \int\mathcal{F}f\,h = \int f\,\mathcal{F}h = \int|f|^2$.

Extension. The Schwartz functions are dense in $L^2$ (Section 2). A linear isometry from a dense subspace into a complete space extends uniquely to an isometry of the closure (Volume 16). Call it $\mathcal{F}$. Its range is complete, hence closed, and it contains $\mathcal{F}(\mathcal{S}) = \mathcal{S}$, which is dense. So the range is all of $L^2$. The polarisation identity turns the equality of norms into the equality of inner products. $\square$

::: mathlib
`MeasureTheory.Lp.norm_fourier_eq` · `Mathlib.Analysis.Fourier.LpSpace`

`‖𝓕 f‖ = ‖f‖` for `f : Lp F 2 volume`, and `Lp.inner_fourier_eq` is `⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫`. The identity on Schwartz space is `SchwartzMap.integral_norm_sq_fourier` of `Mathlib.Analysis.Distribution.SchwartzSpace.Fourier`.

<?decl MeasureTheory.Lp.norm_fourier_eq?>
<?decl MeasureTheory.Lp.inner_fourier_eq?>
<?decl SchwartzMap.integral_norm_sq_fourier?>
:::

**Theorem (Poisson summation).** Let $f : \mathbb{R} \to \mathbb{C}$ be continuous, and let $b > 1$ and $C$ satisfy $|f(x)| \le C(1 + |x|)^{-b}$ and $|\mathcal{F}f(\xi)| \le C(1 + |\xi|)^{-b}$. Then for every $x \in \mathbb{R}$,
$$\sum_{n \in \mathbb{Z}}f(x + n) = \sum_{n \in \mathbb{Z}}\mathcal{F}f(n)\,e^{2\pi i n x}.$$
In particular $\sum_n f(n) = \sum_n\mathcal{F}f(n)$.

*Proof.* Step 1: the periodisation. For $x \in [0, 1]$ and $|n| \ge 2$, $1 + |x + n| \ge |n|$, so $|f(x + n)| \le C|n|^{-b}$. The series $\sum_n|n|^{-b}$ converges because $b > 1$. By the Weierstrass test the series $F(x) = \sum_n f(x + n)$ converges uniformly on $[0, 1]$, and in the same way on every bounded interval. So $F$ is continuous, and $F(x + 1) = F(x)$ by a shift of the index. So $F$ is a continuous function on $\mathbb{R}/\mathbb{Z}$.

Step 2: the coefficients. Uniform convergence on $[0, 1]$ lets the sum and the integral change places:
$$\hat F(m) = \int_0^1\sum_n f(x + n)e^{-2\pi i m x}\,dx = \sum_n\int_n^{n+1}f(y)e^{-2\pi i m y}\,dy = \int_{\mathbb{R}}f(y)e^{-2\pi i m y}\,dy = \mathcal{F}f(m).$$
The middle step substitutes $y = x + n$ and uses $e^{-2\pi i m(y - n)} = e^{-2\pi i m y}$. The integrals over $[n, n + 1]$ add up to the integral over $\mathbb{R}$, since $f$ is integrable.

Step 3: the series. By hypothesis $\sum_m|\hat F(m)| = \sum_m|\mathcal{F}f(m)| \le C\sum_m(1 + |m|)^{-b} < \infty$. The theorem on absolutely summable Fourier series of Chapter 6, Section 2 gives $F(x) = \sum_m\hat F(m)e^{2\pi i m x}$ for every $x$. $\square$

::: mathlib
`Real.tsum_eq_tsum_fourier_of_rpow_decay` · `Mathlib.Analysis.Fourier.PoissonSummation`

The hypotheses are `Continuous f`, `1 < b`, `f =O[cocompact ℝ] fun x ↦ |x| ^ (-b)` and the same for `𝓕 f`. The conclusion is `∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle)`. Step 2 is `Real.fourierCoeff_tsum_comp_add`. The most general form is `Real.tsum_eq_tsum_fourier`. The variant `..._of_summable` replaces the decay of `𝓕 f` by its summability, and `SchwartzMap.tsum_eq_tsum_fourier` is the case of a Schwartz function.

<?decl Real.tsum_eq_tsum_fourier_of_rpow_decay?>
<?decl Real.fourierCoeff_tsum_comp_add?>
<?decl Real.tsum_eq_tsum_fourier?>
<?decl Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable?>
<?decl SchwartzMap.tsum_eq_tsum_fourier?>
:::

### Examples

**Example (The theta function).** Let $t > 0$ and $f(x) = e^{-\pi t x^2}$. The Gaussian rule with scaling gives $\mathcal{F}f(\xi) = t^{-1/2}e^{-\pi\xi^2/t}$. Both decay faster than any power, so Poisson summation at $x = 0$ gives
$$\sum_{n \in \mathbb{Z}}e^{-\pi t n^2} = \frac{1}{\sqrt t}\sum_{n \in \mathbb{Z}}e^{-\pi n^2/t}.$$
With $\theta(t) = \sum_n e^{-\pi t n^2}$ this reads $\theta(1/t) = \sqrt t\,\theta(t)$. Riemann used this identity to prove the functional equation of the zeta function.

::: mathlib
`Real.tsum_exp_neg_mul_int_sq` · `Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation`

For `0 < a`: `∑' n : ℤ, exp (-π * a * n ^ 2) = 1 / a ^ (1 / 2) * ∑' n : ℤ, exp (-π / a * n ^ 2)`. The complex form is `Complex.tsum_exp_neg_mul_int_sq`.

<?decl Real.tsum_exp_neg_mul_int_sq?>
<?decl Complex.tsum_exp_neg_mul_int_sq?>
:::

**Example (Plancherel for an indicator).** Let $f = \mathbf{1}_{[-1/2, 1/2]}$. It is in $L^2$ but not continuous, and Section 1 found $\mathcal{F}f(\xi) = \frac{\sin\pi\xi}{\pi\xi}$, which is not integrable. The integral formula for $\mathcal{F}f$ agrees with the $L^2$ transform, since $f$ lies in $L^1 \cap L^2$ (Exercise 4). Plancherel gives
$$\int_{\mathbb{R}}\frac{\sin^2\pi\xi}{\pi^2\xi^2}\,d\xi = \int|f|^2 = 1, \qquad\text{that is}\qquad \int_{\mathbb{R}}\frac{\sin^2 u}{u^2}\,du = \pi.$$

### The library around it

The inversion theorem in Mathlib holds on any finite-dimensional real inner product space, with `volume` the Lebesgue measure of an orthonormal basis. The theorem of Plancherel lives in `Mathlib.Analysis.Fourier.LpSpace`, and its proof there goes through the dense Schwartz space, as above. The Poisson summation formula is only for $\mathbb{R}$. The index of this edition has no declaration for Poisson summation over a lattice in $\mathbb{R}^d$.

Common errors of a learner:

- Applying the inversion theorem without `Integrable (𝓕 f)`. The indicator of an interval fails it.
- Expecting `𝓕 f` on `Lp F 2` to be given by the integral. It agrees with the integral only for functions in $L^1 \cap L^2$.
- Writing the Poisson formula with $\mathcal{F}f(2\pi n)$. That is the formula for the convention $\int e^{-ix\xi}f(x)\,dx$.

### Exercises

1. (A) Show that $\mathcal{F}\mathcal{F}f(x) = f(-x)$ for $f$ in the Schwartz space.
2. (A) Compute $\mathcal{F}\big(\frac{1}{1 + 4\pi^2x^2}\big)$ with the inversion theorem.
3. (B) Show that $\int_{\mathbb{R}}\frac{dx}{(1 + x^2)^2} = \frac{\pi}{2}$ with Plancherel and the transform $\pi e^{-2\pi|\xi|}$ of $\frac{1}{1 + x^2}$.
4. (B) Let $f \in L^1 \cap L^2$. Show that the $L^2$ transform of $f$ is the integral $\mathcal{F}f$ almost everywhere. Hint: approximate $f$ by Schwartz functions in both norms at once, by convolution with $\varphi_\varepsilon$ and truncation.
5. (B) Prove the convolution theorem $\mathcal{F}(f * g) = \mathcal{F}f\,\mathcal{F}g$ for $f, g \in \mathcal{S}$, then show $\int f\bar g = \int\mathcal{F}f\,\overline{\mathcal{F}g}$ directly from it.
6. (C) Let $f \in L^1(\mathbb{R})$ with $\mathcal{F}f = 0$. Show that $f = 0$ almost everywhere. Hint: $\varphi_\varepsilon * f$ is continuous and integrable with transform $0$, so it is $0$ by inversion; then let $\varepsilon \to 0$ in $L^1$.

### Notes and history

Plancherel proved his theorem in 1910. Poisson used the summation formula in the 1820s. Riemann derived the functional equation of the zeta function from the transformation of the theta function in his memoir of 1859 on the number of primes below a given bound.

### Reference

<?reference?>
