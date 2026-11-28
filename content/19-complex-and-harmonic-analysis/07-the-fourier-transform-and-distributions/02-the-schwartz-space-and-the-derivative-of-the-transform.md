---
title: The Schwartz space and the derivative of the transform
kind: theory
modules:
  - Mathlib.Analysis.Distribution.SchwartzSpace.Basic
  - Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
  - Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
  - Mathlib.Analysis.Fourier.FourierTransformDeriv
  - Mathlib.Analysis.Distribution.TemperateGrowth
  - Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
  - Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
explains:
  E3: [SchwartzMap, SchwartzMap.seminorm, Real.fourier_deriv, Real.deriv_fourier, SchwartzMap.fourierTransformCLM, Function.HasTemperateGrowth]
  E2: [SchwartzMap.decay, schwartzSeminormFamily, schwartz_withSeminorms, SchwartzMap.integrable, SchwartzMap.denseRange_toLpCLM, SchwartzMap.derivCLM, SchwartzMap.fderivCLM, SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul, Real.hasDerivAt_fourier, Real.fourier_fderiv, Real.fderiv_fourier, VectorFourier.fourierSMulRight, SchwartzMap.fourier_coe, SchwartzMap.instFourierPair, SchwartzMap.fourier_fderivCLM_eq, SchwartzMap.integral_norm_sq_fourier, HasCompactSupport.hasTemperateGrowth, MeasureTheory.Measure.HasTemperateGrowth]
  E1: auto
families: []
requires: [V15, V16.C06, V17.C07, V18.C05, V18.C07, V18.C08, V19.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Schwartz space and the derivative of the transform

### Overview

Section 1 showed that the transform of an integrable function need not be integrable. This section finds a space on which $\mathcal{F}$ is a bijection. The key is a pair of rules that exchange smoothness and decay: the transform of a derivative is a multiplication by $2\pi i\xi$, and the derivative of a transform is the transform of a multiplication by $-2\pi i x$. A space that is closed under both differentiation and multiplication by polynomials is therefore mapped into itself. The Schwartz space of smooth functions that decay faster than every power, with all their derivatives, is the smallest natural such space.

As in Section 1, $V$ is a finite-dimensional real inner product space, of dimension $d$.

### Definitions

**Definition (Schwartz space).** A function $f : V \to E$ is a *Schwartz function* if it is $C^\infty$ and for all $k, n \in \mathbb{N}$
$$p_{k,n}(f) = \sup_{x \in V}\|x\|^k\,\|D^n f(x)\| < \infty,$$
where $D^n f(x)$ is the $n$-th derivative, a multilinear map, with its operator norm (Volume 17). The Schwartz functions form a vector space $\mathcal{S}(V, E)$, and each $p_{k,n}$ is a seminorm on it. The topology of $\mathcal{S}(V, E)$ is the one defined by the whole family $(p_{k,n})$.

::: mathlib
`SchwartzMap` · `Mathlib.Analysis.Distribution.SchwartzSpace.Basic`

`SchwartzMap E F`, with notation `𝓢(E, F)`, bundles a function with proofs of smoothness and decay. The bound is `SchwartzMap.decay`: `∀ k n, ∃ C, 0 < C ∧ ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C`.

<?decl SchwartzMap?>
<?decl SchwartzMap.decay?>
<?decl SchwartzMap.smooth?>
:::

::: mathlib
`SchwartzMap.seminorm` · `Mathlib.Analysis.Distribution.SchwartzSpace.Basic`

`SchwartzMap.seminorm 𝕜 k n : Seminorm 𝕜 𝓢(E, F)` is $p_{k,n}$. The two working lemmas are `le_seminorm`, the bound at a point, and `seminorm_le_bound`, which bounds the seminorm by a pointwise bound. The family is `schwartzSeminormFamily 𝕜 E F`, indexed by `ℕ × ℕ`, and `schwartz_withSeminorms` states that the topology of `𝓢(E, F)` is the one of this family.

<?decl SchwartzMap.seminorm?>
<?decl SchwartzMap.le_seminorm?>
<?decl SchwartzMap.seminorm_le_bound?>
<?decl schwartzSeminormFamily?>
<?decl schwartz_withSeminorms?>
:::

**Definition (Temperate growth).** A function $g : V \to F$ has *temperate growth* if it is $C^\infty$ and for each $n$ there are $C$ and $k$ with $\|D^n g(x)\| \le C(1 + \|x\|)^k$ for all $x$. Polynomials, smooth functions with compact support, $(1 + \|x\|^2)^r$ for real $r$, and $x \mapsto e^{i\langle x, a\rangle}$ have temperate growth. A product $g f$ with $g$ of temperate growth and $f$ Schwartz is a Schwartz function, by the Leibniz rule.

::: mathlib
`Function.HasTemperateGrowth` · `Mathlib.Analysis.Distribution.TemperateGrowth`

`Function.HasTemperateGrowth f` holds when `ContDiff ℝ ∞ f` and every `iteratedFDeriv ℝ n f` is bounded by `C * (1 + ‖x‖) ^ k`. Examples in the file are `HasCompactSupport.hasTemperateGrowth` and `hasTemperateGrowth_one_add_norm_sq_rpow`. The same file defines `MeasureTheory.Measure.HasTemperateGrowth μ`: some $(1 + \|x\|)^{-n}$ is `μ`-integrable.

<?decl Function.HasTemperateGrowth?>
<?decl Function.hasTemperateGrowth_iff_isBigO?>
<?decl HasCompactSupport.hasTemperateGrowth?>
<?decl Function.hasTemperateGrowth_one_add_norm_sq_rpow?>
<?decl MeasureTheory.Measure.HasTemperateGrowth?>
:::

### Theorems and proofs

**Lemma (Schwartz functions are integrable).** Let $f \in \mathcal{S}(V, E)$. Then $\|f(x)\| \le (p_{0,0}(f) + p_{d+1,0}(f))\,2^{d+1}(1 + \|x\|)^{-(d+1)}$, and $f$ is integrable. The map $f \mapsto \|f\|_1$ is bounded by a constant times $p_{0,0}(f) + p_{d+1,0}(f)$.

*Proof.* If $\|x\| \le 1$, then $\|f(x)\| \le p_{0,0}(f)$ and $(1 + \|x\|)^{d+1} \le 2^{d+1}$. If $\|x\| \ge 1$, then $(1 + \|x\|)^{d+1} \le 2^{d+1}\|x\|^{d+1}$ and $\|x\|^{d+1}\|f(x)\| \le p_{d+1,0}(f)$. This gives the bound. For integrability, cut $V$ into the ball $B_0 = \{\|x\| < 1\}$ and the shells $A_j = \{2^{j} \le \|x\| < 2^{j+1}\}$ for $j \ge 0$. The shell $A_j$ lies in the ball of radius $2^{j+1}$, of measure $c\,2^{(j+1)d}$, and on it $(1 + \|x\|)^{-(d+1)} \le 2^{-j(d+1)}$. So the integral over $A_j$ is at most $c\,2^d\,2^{-j}$, and the sum over $j$ converges. $\square$

::: mathlib
`SchwartzMap.integrable` · `Mathlib.Analysis.Distribution.SchwartzSpace.Basic`

`SchwartzMap.integrable` holds for every measure `μ` with `μ.HasTemperateGrowth`. The continuous inclusion into `Lp` is `toLpCLM 𝕜 F p μ`, and `denseRange_toLpCLM` states that its range is dense for `p ≠ ⊤`.

<?decl SchwartzMap.integrable?>
<?decl SchwartzMap.toLpCLM?>
<?decl SchwartzMap.denseRange_toLpCLM?>
:::

**Theorem (Transform of a derivative).** Let $f : \mathbb{R} \to E$ be integrable and differentiable, with $f'$ integrable. Then $\mathcal{F}(f')(\xi) = 2\pi i\xi\,\mathcal{F}f(\xi)$.

*Proof.* Step 1: $f(x) \to 0$ as $x \to \pm\infty$. By the fundamental theorem of calculus (Volume 18, Chapter 8), $f(x) = f(0) + \int_0^x f'$. Since $f'$ is integrable, the limit $\ell = \lim_{x \to \infty}f(x)$ exists. If $\ell \ne 0$, then $\|f(x)\| \ge \|\ell\|/2$ for all large $x$, and $f$ is not integrable. So $\ell = 0$, and in the same way at $-\infty$.

Step 2: integration by parts on $[-R, R]$. Put $u(x) = e^{-2\pi i x\xi}$, so $u' = -2\pi i\xi\,u$. Then
$$\int_{-R}^{R}u f'\,dx = u(R)f(R) - u(-R)f(-R) + 2\pi i\xi\int_{-R}^{R}u f\,dx.$$
Step 3: let $R \to \infty$. The boundary terms tend to $0$ by Step 1, since $|u| = 1$. The integrals over $[-R, R]$ tend to the integrals over $\mathbb{R}$ by dominated convergence, with the bounds $\|f'\|$ and $\|f\|$. $\square$

::: mathlib
`Real.fourier_deriv` · `Mathlib.Analysis.Fourier.FourierTransformDeriv`

The hypotheses are `Integrable f`, `Differentiable ℝ f` and `Integrable (deriv f)`, and the conclusion is `𝓕 (deriv f) = fun x ↦ (2 * π * I * x) • 𝓕 f x`. The iterated form is `Real.fourier_iteratedDeriv`, with the factor $(2\pi i x)^n$. On a general space, `Real.fourier_fderiv` gives the transform of `fderiv ℝ f`.

<?decl Real.fourier_deriv?>
<?decl Real.fourier_iteratedDeriv?>
<?decl Real.fourier_fderiv?>
:::

**Theorem (Derivative of the transform).** Let $f : \mathbb{R} \to E$ with $f$ and $x f(x)$ integrable. Then $\mathcal{F}f$ is differentiable and
$$(\mathcal{F}f)'(\xi) = \mathcal{F}\big(x \mapsto -2\pi i x\,f(x)\big)(\xi).$$

*Proof.* For $h \ne 0$,
$$\frac{\mathcal{F}f(\xi + h) - \mathcal{F}f(\xi)}{h} = \int e^{-2\pi i x\xi}\,\frac{e^{-2\pi i x h} - 1}{h}\,f(x)\,dx.$$
For real $t$, $|e^{it} - 1| = |\int_0^t ie^{is}\,ds| \le |t|$. So the integrand has norm at most $2\pi|x|\,\|f(x)\|$, an integrable function that does not depend on $h$. As $h \to 0$, the integrand tends to $-2\pi i x\,e^{-2\pi i x\xi}f(x)$ for every $x$. Dominated convergence along every sequence $h_j \to 0$ gives the claim. $\square$

::: mathlib
`Real.deriv_fourier` · `Mathlib.Analysis.Fourier.FourierTransformDeriv`

`Real.deriv_fourier` states `deriv (𝓕 f) = 𝓕 (fun x ↦ (-2 * π * I * x) • f x)` under `Integrable f` and `Integrable (fun x ↦ x • f x)`. The form with `HasDerivAt` is `Real.hasDerivAt_fourier`, and `Real.iteratedDeriv_fourier` gives the $n$-th derivative. On a general space, `Real.fderiv_fourier` uses `VectorFourier.fourierSMulRight`.

<?decl Real.deriv_fourier?>
<?decl Real.hasDerivAt_fourier?>
<?decl Real.iteratedDeriv_fourier?>
<?decl Real.fderiv_fourier?>
<?decl VectorFourier.fourierSMulRight?>
:::

**Theorem (The transform on Schwartz space).** $\mathcal{F}$ maps $\mathcal{S}(V, E)$ into itself, and $\mathcal{F} : \mathcal{S}(V, E) \to \mathcal{S}(V, E)$ is a continuous linear map. With the inversion theorem of Section 3, it is a continuous linear bijection with continuous inverse $\mathcal{F}^{-1}$.

*Proof.* Take $V = \mathbb{R}$. The general case is the same with multi-indices. Let $f \in \mathcal{S}$. Every function $x^m f^{(j)}$ is integrable by the lemma, so the derivative theorem applies $n$ times, and $\mathcal{F}f$ is $C^\infty$ with $(\mathcal{F}f)^{(n)} = \mathcal{F}(g_n)$, $g_n(x) = (-2\pi i x)^n f(x)$. The function $g_n$ is Schwartz. The theorem on derivatives, applied $k$ times to $g_n$, gives
$$(2\pi i\xi)^k(\mathcal{F}f)^{(n)}(\xi) = \mathcal{F}\big(g_n^{(k)}\big)(\xi).$$
By the bound of Section 1, $|\xi|^k\,\|(\mathcal{F}f)^{(n)}(\xi)\| \le (2\pi)^{-k}\|g_n^{(k)}\|_1$. The Leibniz rule writes $g_n^{(k)}$ as a finite sum of terms $c\,x^{m}f^{(j)}(x)$ with $m \le n$ and $j \le k$. The lemma bounds the $L^1$ norm of each term by $p_{m,j}(f) + p_{m+2,j}(f)$, up to a constant. So $p_{k,n}(\mathcal{F}f)$ is finite, and it is at most a constant times a finite sum of seminorms of $f$. Hence $\mathcal{F}f \in \mathcal{S}$, and the linear map $\mathcal{F}$ is continuous. The inverse $\mathcal{F}^{-1}g(x) = \mathcal{F}g(-x)$ is continuous by the same bound. Section 3 proves $\mathcal{F}^{-1}\mathcal{F} = \mathrm{id}$ and $\mathcal{F}\mathcal{F}^{-1} = \mathrm{id}$ on $\mathcal{S}$. $\square$

::: mathlib
`SchwartzMap.fourierTransformCLM` · `Mathlib.Analysis.Distribution.SchwartzSpace.Fourier`

`fourierTransformCLM 𝕜 : 𝓢(V, E) →L[𝕜] 𝓢(V, E)`, with `fourierTransformCLM_apply` and `fourier_coe`, which says that the underlying function of `𝓕 f` is `𝓕` of the function. The instances `instFourierPair` and `instFourierInvPair` record $\mathcal{F}^{-1}\mathcal{F} = \mathrm{id}$ and $\mathcal{F}\mathcal{F}^{-1} = \mathrm{id}$. With them, `FourierTransform.fourierCLE` gives the transform as `𝓢(V, E) ≃L[ℂ] 𝓢(V, E)`. The rules for derivatives are `fourier_fderivCLM_eq` and `fderivCLM_fourier_eq`, and Plancherel on Schwartz space is `integral_norm_sq_fourier`.

<?decl SchwartzMap.fourierTransformCLM?>
<?decl SchwartzMap.fourier_coe?>
<?decl SchwartzMap.instFourierPair?>
<?decl SchwartzMap.instFourierInvPair?>
<?decl FourierTransform.fourierCLE?>
<?decl SchwartzMap.fourier_fderivCLM_eq?>
<?decl SchwartzMap.integral_norm_sq_fourier?>
:::

### Examples

**Example (The Gaussian and its first moment).** The Gaussian $\gamma(x) = e^{-\pi x^2}$ is a Schwartz function: each derivative is a polynomial times $\gamma$, and $x^m\gamma(x) \to 0$ for every $m$. Its transform is $\gamma$ (box below). The derivative of the transform gives $\mathcal{F}(-2\pi i x\gamma) = \gamma' = -2\pi\xi\gamma$, so $\mathcal{F}(x\gamma)(\xi) = -i\xi\gamma(\xi)$.

::: mathlib
`fourier_gaussian_pi` · `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`

For `b : ℂ` with `0 < b.re`, `𝓕 (fun x ↦ cexp (-π * b * x ^ 2)) = fun t ↦ 1 / b ^ (1 / 2) * cexp (-π / b * t ^ 2)`. The case `b = 1` is $\mathcal{F}\gamma = \gamma$. The form on an inner product space is `fourier_gaussian_innerProductSpace`.

<?decl fourier_gaussian_pi?>
<?decl fourier_gaussian_innerProductSpace?>
:::

**Counterexample (Smooth or decaying is not enough).** The function $e^{-|x|}$ decays fast but has a corner at $0$, and Section 1 found $\mathcal{F}e^{-|x|} = \frac{2}{1 + 4\pi^2\xi^2}$. This transform is smooth but decays only like $\xi^{-2}$, so it is not Schwartz. In the other direction, $\frac{1}{1 + x^2}$ is smooth, and its transform $\pi e^{-2\pi|\xi|}$ has a corner.

### The library around it

Differentiation is a continuous linear map on Schwartz space, and integration by parts has no boundary terms (box below).

The Gaussian is the main example of a Schwartz function, and the module `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform` computes its transform. The proof moves the line of integration from $\mathbb{R}$ to $\mathbb{R} + ic$ by the Cauchy theorem on a rectangle. The function `GaussianFourier.verticalIntegral` is the integral over the two vertical sides, and `GaussianFourier.tendsto_verticalIntegral` shows that it tends to $0$. The result is `GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I`, and its consequence `integral_cexp_quadratic` gives $\int e^{bx^2 + cx + d}\,dx = (\pi/(-b))^{1/2} e^{d - c^2/(4b)}$ for $\operatorname{Re} b < 0$. The theorem `fourierIntegral_gaussian` gives the transform with the kernel $e^{itx}$, and `fourier_gaussian_pi` and `fourier_gaussian_pi'` give it with the kernel of Mathlib. In a finite dimensional inner product space $V$, `GaussianFourier.integral_cexp_neg_mul_sq_norm` gives $\int_V e^{-b\|v\|^2}\,dv = (\pi/b)^{\dim V/2}$, and `fourier_gaussian_innerProductSpace` gives the transform. The module `Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport` proves `SchwartzMap.dense_hasCompactSupport`: on a finite dimensional space, the Schwartz functions with compact support are dense in the Schwartz space. The proof multiplies $f$ by a cutoff $\varphi(\varepsilon x)$ and lets $\varepsilon \to 0$, by `SchwartzMap.tendsto_smulLeftCLM_comp_smul`.

Common errors of a learner:

- Using $(1 + \|x\|)^k$ in the seminorms. Mathlib uses $\|x\|^k$, and the two families give the same topology.
- Forgetting the hypothesis `Integrable (fun x ↦ x • f x)` in `Real.deriv_fourier`. Without it the transform need not be differentiable.

::: mathlib
`SchwartzMap.derivCLM` · `Mathlib.Analysis.Distribution.SchwartzSpace.Deriv`

`derivCLM 𝕜 F : 𝓢(ℝ, F) →L[𝕜] 𝓢(ℝ, F)` and `fderivCLM 𝕜 E F : 𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F)`. For `f g : 𝓢(ℝ, 𝕜)`, `integral_mul_deriv_eq_neg_deriv_mul` is `∫ f * g' = -∫ f' * g`.

<?decl SchwartzMap.derivCLM?>
<?decl SchwartzMap.fderivCLM?>
<?decl SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul?>
:::

### Exercises

1. (A) Show that $x^m e^{-\pi x^2}$ is a Schwartz function for every $m$.
2. (A) Show that $\frac{1}{1 + x^2}$ has temperate growth but is not a Schwartz function.
3. (B) Show that the product of a Schwartz function and a function of temperate growth is a Schwartz function. Hint: the Leibniz rule and the bound $(1 + \|x\|)^k \le 2^k\max(1, \|x\|^k)$.
4. (B) Show that $\mathcal{S}(\mathbb{R}, \mathbb{C})$ is closed under convolution, using $\mathcal{F}(f * g) = \mathcal{F}f\,\mathcal{F}g$ and the theorem on Schwartz space.
5. (C) Let $f \in \mathcal{S}(\mathbb{R}, \mathbb{C})$. Show the uncertainty inequality $\|f\|_2^2 \le 4\pi\,\|x f\|_2\,\|\xi\mathcal{F}f\|_2$. Hint: integrate $\frac{d}{dx}(x)|f|^2$ by parts, use Cauchy-Schwarz, and Plancherel for $f'$.

### Notes and history

Laurent Schwartz introduced the space of rapidly decreasing functions and the tempered distributions in his *Théorie des distributions*, published in two volumes in 1950 and 1951. The uncertainty inequality of Exercise 5 is the mathematical form of the uncertainty principle of Heisenberg of 1927.

### Reference

<?reference?>
