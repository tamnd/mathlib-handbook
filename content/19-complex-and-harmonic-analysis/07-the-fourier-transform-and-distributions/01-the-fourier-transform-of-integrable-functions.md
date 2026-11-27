---
title: The Fourier transform of integrable functions
kind: theory
modules:
  - Mathlib.Analysis.Fourier.FourierTransform
  - Mathlib.Analysis.Fourier.Notation
  - Mathlib.Analysis.Fourier.RiemannLebesgueLemma
  - Mathlib.Analysis.Fourier.Convolution
  - Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar
explains:
  E3: [FourierTransform.fourier, Real.fourier_eq, VectorFourier.fourierIntegral, Real.zero_at_infty_fourier, Real.fourier_bilin_convolution_eq]
  E2: [Real.fourier_eq', Real.fourier_real_eq, Real.norm_fourier_le_integral_norm, VectorFourier.norm_fourierIntegral_le_integral_norm, VectorFourier.fourierIntegral_continuous, Real.Lp.fourierTransformCLM, Fourier.fourierIntegral, FourierTransformInv.fourierInv, Real.fourierInv_eq', FourierAdd, FourierSMul, VectorFourier.fourierIntegral_comp_add_right, Real.fourier_comp_linearIsometry, Real.fourier_congr_ae, VectorFourier.integral_fourierIntegral_smul_eq_flip, fourierIntegral_half_period_translate, tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support, Real.fourier_mul_convolution_eq, BoundedContinuousFunction.char, BoundedContinuousFunction.charPoly, BoundedContinuousFunction.ext_of_char_eq]
  E1: auto
families: []
requires: [V13, V15, V16.C06, V18.C05, V18.C06, V18.C07, V19.C01, V19.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Fourier transform of integrable functions

### Overview

Chapter 6 expanded a periodic function into the characters $e^{2\pi i n x}$ of the circle. On $\mathbb{R}^n$ there is a character $x \mapsto e^{2\pi i\langle x, \xi\rangle}$ for every $\xi \in \mathbb{R}^n$, and the sum over $n$ becomes an integral over $\xi$. This section defines the transform of an integrable function, proves that it is bounded and continuous, proves the Riemann-Lebesgue lemma that it vanishes at infinity, and proves that it turns convolution into a product.

The convention of this chapter is the one of Mathlib. Let $V$ be a finite-dimensional real inner product space with its Lebesgue measure. Then
$$\mathcal{F}f(\xi) = \int_V e^{-2\pi i\langle x, \xi\rangle} f(x)\,dx, \qquad \mathcal{F}^{-1}g(x) = \int_V e^{2\pi i\langle x, \xi\rangle} g(\xi)\,d\xi.$$

### Definitions

**Definition (Fourier transform).** Let $E$ be a complex Banach space and $f : V \to E$ integrable. The *Fourier transform* of $f$ is the function $\mathcal{F}f : V \to E$ given by the integral above. The integrand is integrable, since $|e^{-2\pi i\langle x, \xi\rangle}| = 1$.

More generally, let $e : \mathbb{R} \to \mathbb{C}$ be a continuous character with values in the unit circle, $\mu$ a measure on $V$, and $L : V \times W \to \mathbb{R}$ a continuous bilinear form. The *Fourier integral* of $f$ is
$$\mathcal{F}_{e, \mu, L}f(w) = \int_V e(-L(v, w))\, f(v)\,d\mu(v).$$
The transform above is the case $e(t) = e^{2\pi i t}$, $\mu$ the Lebesgue measure, $W = V$ and $L$ the inner product.

::: mathlib
`FourierTransform.fourier` · `Mathlib.Analysis.Fourier.Notation`

`FourierTransform.fourier` is the field of a type class `FourierTransform E F`, with notation `𝓕`. The inverse transform is `FourierTransformInv.fourierInv`, with notation `𝓕⁻`. The class lets the same symbol act on functions, on Schwartz functions (Section 2), on `Lp` (Section 3) and on tempered distributions (Section 4). `FourierAdd` and `FourierSMul` say that `𝓕` is additive and commutes with scalars.

<?decl FourierTransform.fourier?>
<?decl FourierTransformInv.fourierInv?>
<?decl FourierAdd?>
<?decl FourierSMul?>
:::

::: mathlib
`Real.fourier_eq` · `Mathlib.Analysis.Fourier.FourierTransform`

For `f : V → E`, with `V` a finite-dimensional real inner product space, `Real.fourier_eq` states `𝓕 f w = ∫ v, fourierChar (-⟪v, w⟫) • f v`. Here `Real.fourierChar : AddChar ℝ Circle` is $t \mapsto e^{2\pi i t}$. The variant `Real.fourier_eq'` writes `Complex.exp (↑(-2 * π * ⟪v, w⟫) * I)`, and `Real.fourier_real_eq` is the case `V = ℝ` with `v * w`. The inverse is `Real.fourierInv_eq'`, with the opposite sign.

<?decl Real.fourier_eq?>
<?decl Real.fourier_eq'?>
<?decl Real.fourier_real_eq?>
<?decl Real.fourierInv_eq'?>
<?decl Real.fourierChar?>
:::

::: mathlib
`VectorFourier.fourierIntegral` · `Mathlib.Analysis.Fourier.FourierTransform`

`VectorFourier.fourierIntegral e μ L f w = ∫ v, e (-L v w) • f v ∂μ`, for `e : AddChar 𝕜 Circle` and `L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜`. The one-variable form `Fourier.fourierIntegral e μ f` takes `L` to be multiplication.

<?decl VectorFourier.fourierIntegral?>
<?decl Fourier.fourierIntegral?>
:::

### Theorems and proofs

**Theorem (Bound and continuity).** Let $f : V \to E$ be integrable. Then $\|\mathcal{F}f(\xi)\| \le \|f\|_1$ for every $\xi$, and $\mathcal{F}f$ is continuous. So $f \mapsto \mathcal{F}f$ is a continuous linear map from $L^1(V, E)$ to the bounded continuous functions with the sup norm.

*Proof.* The bound: the norm of an integral is at most the integral of the norm (Volume 18, Chapter 5), and $\|e^{-2\pi i\langle x, \xi\rangle}f(x)\| = \|f(x)\|$. Continuity: let $\xi_k \to \xi$. For each $x$, $e^{-2\pi i\langle x, \xi_k\rangle}f(x) \to e^{-2\pi i\langle x, \xi\rangle}f(x)$, and the norm of every term is at most $\|f(x)\|$, an integrable function. Dominated convergence gives $\mathcal{F}f(\xi_k) \to \mathcal{F}f(\xi)$. The transform depends only on the class of $f$ almost everywhere, and it is linear. With the bound, it is a continuous linear map of norm at most $1$. $\square$

::: mathlib
`Real.norm_fourier_le_integral_norm` · `Mathlib.Analysis.Fourier.FourierTransform`

`‖𝓕 f w‖ ≤ ∫ v, ‖f v‖`. The general form is `VectorFourier.norm_fourierIntegral_le_integral_norm`. Continuity is `VectorFourier.fourierIntegral_continuous`. The bundled map is `Real.Lp.fourierTransformCLM : Lp E 1 volume →L[ℂ] (V →ᵇ E)`. Only almost everywhere values matter: `Real.fourier_congr_ae`.

<?decl Real.norm_fourier_le_integral_norm?>
<?decl VectorFourier.norm_fourierIntegral_le_integral_norm?>
<?decl VectorFourier.fourierIntegral_continuous?>
<?decl Real.Lp.fourierTransformCLM?>
<?decl Real.fourier_congr_ae?>
:::

**Proposition (Translation and the multiplication formula).** Let $f, g$ be integrable. (a) For $a \in V$, $\mathcal{F}(f(\cdot + a))(\xi) = e^{2\pi i\langle a, \xi\rangle}\mathcal{F}f(\xi)$. (b) For $f$ with values in $\mathbb{C}$, $\int \mathcal{F}f(\xi)\,g(\xi)\,d\xi = \int f(x)\,\mathcal{F}g(x)\,dx$.

*Proof.* (a) Substitute $y = x + a$, which preserves Lebesgue measure: $\int e^{-2\pi i\langle x, \xi\rangle}f(x + a)\,dx = \int e^{-2\pi i\langle y - a, \xi\rangle}f(y)\,dy = e^{2\pi i\langle a, \xi\rangle}\mathcal{F}f(\xi)$. (b) The function $(x, \xi) \mapsto e^{-2\pi i\langle x, \xi\rangle}f(x)g(\xi)$ has absolute value $|f(x)|\,\|g(\xi)\|$, which is integrable on $V \times V$ with integral $\|f\|_1\|g\|_1$ by Tonelli. By Fubini (Volume 18, Chapter 6) both iterated integrals are equal, and they are the two sides. $\square$

::: mathlib
`VectorFourier.integral_fourierIntegral_smul_eq_flip` · `Mathlib.Analysis.Fourier.FourierTransform`

The statement is `∫ ξ, fourierIntegral e μ L f ξ • g ξ ∂ν = ∫ x, f x • fourierIntegral e ν L.flip g x ∂μ`, for integrable `f` and `g`. The translation rule is `VectorFourier.fourierIntegral_comp_add_right`. Invariance under a linear isometry `A` is `Real.fourier_comp_linearIsometry`: `𝓕 (f ∘ A) w = 𝓕 f (A w)`.

<?decl VectorFourier.integral_fourierIntegral_smul_eq_flip?>
<?decl VectorFourier.fourierIntegral_comp_add_right?>
<?decl Real.fourier_comp_linearIsometry?>
:::

**Theorem (Riemann-Lebesgue lemma).** Let $f : V \to E$ be integrable. Then $\mathcal{F}f(\xi) \to 0$ as $\|\xi\| \to \infty$.

*Proof.* Step 1: a half period. Let $\xi \ne 0$ and $a = \frac{\xi}{2\|\xi\|^2}$, so that $\langle a, \xi\rangle = \frac12$ and $e^{2\pi i\langle a, \xi\rangle} = -1$. Part (a) of the proposition gives $\mathcal{F}(f(\cdot + a))(\xi) = -\mathcal{F}f(\xi)$. Hence
$$\mathcal{F}f(\xi) = \frac12\int e^{-2\pi i\langle x, \xi\rangle}\big(f(x) - f(x + a)\big)\,dx, \qquad \|\mathcal{F}f(\xi)\| \le \frac12\int\|f(x) - f(x + a)\|\,dx.$$

Step 2: continuous $f$ with compact support $K$. Then $f$ is uniformly continuous. As $\|\xi\| \to \infty$, $\|a\| = \frac{1}{2\|\xi\|} \to 0$, so $\sup_x\|f(x) - f(x + a)\| \to 0$. For $\|a\| \le 1$ the integrand vanishes outside the compact set $K_1 = \{x : d(x, K) \le 1\}$. So the integral is at most $\lambda(K_1)\sup_x\|f(x) - f(x + a)\| \to 0$.

Step 3: general $f$. Let $\varepsilon > 0$. Continuous functions with compact support are dense in $L^1$ (Volume 18, Chapter 7, Section 2). Choose such a $g$ with $\|f - g\|_1 < \varepsilon$. By the bound, $\|\mathcal{F}f(\xi) - \mathcal{F}g(\xi)\| \le \|f - g\|_1 < \varepsilon$ for all $\xi$. By Step 2, $\|\mathcal{F}g(\xi)\| < \varepsilon$ for $\|\xi\|$ large. Then $\|\mathcal{F}f(\xi)\| < 2\varepsilon$ for $\|\xi\|$ large. $\square$

::: mathlib
`Real.zero_at_infty_fourier` · `Mathlib.Analysis.Fourier.RiemannLebesgueLemma`

`Real.zero_at_infty_fourier (f : ℝ → E) : Tendsto (𝓕 f) (cocompact ℝ) (𝓝 0)`. The filter `cocompact` is the filter of complements of compact sets, so this is the limit as $|\xi| \to \infty$. The form on an inner product space is `tendsto_integral_exp_inner_smul_cocompact`. Step 1 is `fourierIntegral_half_period_translate`, and Step 2 is `tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support`.

<?decl Real.zero_at_infty_fourier?>
<?decl tendsto_integral_exp_inner_smul_cocompact?>
<?decl fourierIntegral_half_period_translate?>
<?decl tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support?>
:::

**Theorem (Convolution theorem).** Let $f, g : V \to \mathbb{C}$ be integrable, and $(f * g)(x) = \int f(y)g(x - y)\,dy$. Then $f * g$ is integrable and $\mathcal{F}(f * g) = \mathcal{F}f \cdot \mathcal{F}g$.

*Proof.* By Tonelli and the invariance of Lebesgue measure under $x \mapsto x - y$,
$$\int\!\!\int |f(y)|\,|g(x - y)|\,dx\,dy = \int |f(y)|\,\|g\|_1\,dy = \|f\|_1\|g\|_1 < \infty.$$
So $F(x, y) = f(y)g(x - y)$ is integrable on $V \times V$. Fubini shows that $f * g$ is defined almost everywhere and integrable with $\|f * g\|_1 \le \|f\|_1\|g\|_1$. The function $e^{-2\pi i\langle x, \xi\rangle}F(x, y)$ is integrable too. Fubini and the substitution $x = y + z$ give
$$\mathcal{F}(f * g)(\xi) = \int f(y)\int e^{-2\pi i\langle x, \xi\rangle}g(x - y)\,dx\,dy = \int f(y)e^{-2\pi i\langle y, \xi\rangle}\int e^{-2\pi i\langle z, \xi\rangle}g(z)\,dz\,dy,$$
which is $\mathcal{F}f(\xi)\,\mathcal{F}g(\xi)$. $\square$

::: mathlib
`Real.fourier_bilin_convolution_eq` · `Mathlib.Analysis.Fourier.Convolution`

Mathlib's convolution `MeasureTheory.convolution f₁ f₂ B μ` takes a continuous bilinear map `B` to combine the values. The theorem states `𝓕 (convolution f₁ f₂ B volume) ξ = B (𝓕 f₁ ξ) (𝓕 f₂ ξ)` for integrable `f₁` and `f₂`. The scalar case is `Real.fourier_mul_convolution_eq`, with `B = ContinuousLinearMap.mul ℂ R`.

<?decl Real.fourier_bilin_convolution_eq?>
<?decl Real.fourier_mul_convolution_eq?>
<?decl MeasureTheory.convolution?>
:::

### Examples

**Example (The two-sided exponential).** Let $f(x) = e^{-|x|}$ on $\mathbb{R}$. Put $a = 2\pi\xi$. Then $\int_0^\infty e^{-x}e^{-iax}\,dx = \frac{1}{1 + ia}$ and $\int_{-\infty}^0 e^{x}e^{-iax}\,dx = \frac{1}{1 - ia}$. So
$$\mathcal{F}f(\xi) = \frac{1}{1 + ia} + \frac{1}{1 - ia} = \frac{2}{1 + 4\pi^2\xi^2}.$$
It is continuous, bounded by $\|f\|_1 = 2$, and tends to $0$, as the theorems predict. It decays like $\xi^{-2}$ because $f$ has a corner at $0$.

**Example (An indicator).** Let $f = \mathbf{1}_{[-1/2, 1/2]}$. For $\xi \ne 0$,
$$\mathcal{F}f(\xi) = \int_{-1/2}^{1/2}e^{-2\pi i x\xi}\,dx = \frac{e^{\pi i\xi} - e^{-\pi i\xi}}{2\pi i\xi} = \frac{\sin\pi\xi}{\pi\xi},$$
and $\mathcal{F}f(0) = 1$. The convolution $f * f$ is the triangle $\max(1 - |x|, 0)$, and the convolution theorem gives its transform $\big(\frac{\sin\pi\xi}{\pi\xi}\big)^2$.

**Counterexample (The transform need not be integrable).** For the indicator above, $\int|\mathcal{F}f| = \infty$: on $[k, k + 1]$ with $k \ge 1$ the integral of $|\sin\pi\xi|/(\pi|\xi|)$ is at least $\frac{2}{\pi^2(k + 1)}$, and $\sum_k\frac{1}{k + 1}$ diverges. So $\mathcal{F}$ does not map $L^1$ into $L^1$, and the inversion formula of Section 3 needs an extra hypothesis.

### The library around it

`Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar` packages the characters $v \mapsto e(L(v, w))$ as bounded continuous functions, `BoundedContinuousFunction.char`. Their span `charPoly` is a star subalgebra. `ext_of_char_eq` shows that the characters separate points when $e \ne 1$ and $L$ is nondegenerate. The index of this edition has no declaration for the Hausdorff-Young inequality on $L^p$ with $1 < p < 2$.

Common errors of a learner:

- Using the convention $\int e^{-i x\xi}f(x)\,dx$. Mathlib puts $2\pi$ in the exponent, and the rules change by factors of $2\pi$.
- Expecting `𝓕 f` to be integrable. The indicator shows that it need not be.
- Writing `convolution f g` without the bilinear map. Mathlib needs `B`.

::: mathlib
`BoundedContinuousFunction.char` · `Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar`

`char he hL w : V →ᵇ ℂ` is `fun v ↦ e (L v w)`, with `he` the continuity of `e` and `hL` the continuity of `L`.

<?decl BoundedContinuousFunction.char?>
<?decl BoundedContinuousFunction.charPoly?>
<?decl BoundedContinuousFunction.ext_of_char_eq?>
:::

### Exercises

1. (A) Show that $\mathcal{F}(f(\lambda\,\cdot))(\xi) = |\lambda|^{-n}\mathcal{F}f(\xi/\lambda)$ on $\mathbb{R}^n$ for $\lambda \ne 0$.
2. (A) Show that $\mathcal{F}(e^{2\pi i\langle\cdot, b\rangle}f)(\xi) = \mathcal{F}f(\xi - b)$.
3. (B) Show that $\|f * g\|_1 \le \|f\|_1\|g\|_1$ and that $f * g = g * f$ almost everywhere.
4. (B) Show that no integrable $u$ satisfies $u * f = f$ for all integrable $f$. Hint: $\mathcal{F}u$ would be $1$ everywhere.
5. (C) Let $f \in L^1(\mathbb{R})$ with $f * f = f$ almost everywhere. Show that $f = 0$ almost everywhere. Hint: $\mathcal{F}f$ is continuous with values in $\{0, 1\}$ and tends to $0$. Then use the multiplication formula with $g$ a Schwartz function, and the fact of Section 2 that $\mathcal{F}$ maps the Schwartz space onto itself.

### Notes and history

Fourier wrote the transform and the inversion formula for the heat equation on the line in his work of 1822. Riemann proved the lemma for integrals over an interval in his habilitation thesis of 1854 on trigonometric series, and Lebesgue extended it to his integrable functions in 1903.

### Reference

<?reference?>
