---
title: Distributions
kind: theory
modules:
  - Mathlib.Analysis.Distribution.TestFunction
  - Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
  - Mathlib.Analysis.Distribution.Distribution
  - Mathlib.Analysis.Distribution.TemperedDistribution
  - Mathlib.Analysis.Distribution.Support
  - Mathlib.Analysis.Distribution.DerivNotation
  - Mathlib.Analysis.Distribution.FourierMultiplier
  - Mathlib.Analysis.Distribution.Sobolev
  - Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
explains:
  E3: [TestFunction, Distribution, Distribution.ofFun, TemperedDistribution, Distribution.dsupport, ae_eq_zero_of_integral_contDiff_smul_eq_zero]
  E2: [ContDiffMapSupportedIn, TestFunction.topologicalSpace, TestFunction.continuous_iff_continuous_comp, Distribution.delta, Distribution.delta_apply, Distribution.ofFun_apply, Distribution.ofFun_injective, Distribution.ofFun_dirac_eq_delta, Distribution.lineDerivOp_apply_apply, Distribution.IsVanishingOn, Distribution.notMem_dsupport_iff, Distribution.dsupport_delta, Distribution.dsupport_lineDerivOp_subset, TemperedDistribution.delta, TemperedDistribution.fourier_apply, TemperedDistribution.fourier_delta_zero, TemperedDistribution.fourier_lineDerivOp_eq, TemperedDistribution.lineDerivOp_apply_apply, SchwartzMap.toTemperedDistributionCLM, TemperedDistribution.fourier_toTemperedDistributionCLM_eq, Function.HasTemperateGrowth.toTemperedDistribution, MeasureTheory.Lp.toTemperedDistribution, MeasureTheory.Measure.toTemperedDistribution, LineDeriv, Laplacian, TemperedDistribution.fourierMultiplierCLM, TemperedDistribution.laplacian_eq_fourierMultiplierCLM, TemperedDistribution.MemSobolev, TemperedDistribution.besselPotential, TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier, TemperedDistribution.MemSobolev.lineDerivOp]
  E1: auto
families: []
requires: [V16.C06, V17.C07, V18.C05, V18.C07, V19.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Distributions

### Overview

Many functions of analysis have no derivative and no Fourier transform in the classical sense. A distribution is a continuous linear form on a space of test functions. A locally integrable function $f$ gives the distribution $\varphi \mapsto \int\varphi f$, and the integration by parts formula turns into a definition: the derivative of a distribution $T$ is $\varphi \mapsto -T(\varphi')$. Every distribution then has derivatives of all orders.

The same idea with the Schwartz space of Section 2 in place of the test functions gives the tempered distributions. The multiplication formula of Section 1 turns into a definition: $(\mathcal{F}T)(g) = T(\mathcal{F}g)$. So every tempered distribution has a Fourier transform, and the constant $1$ and the Dirac mass $\delta_0$ are transforms of each other.

### Definitions

**Definition (Test functions).** Let $\Omega$ be an open subset of a finite-dimensional real normed space $E$. A test function on $\Omega$ is a smooth function $\varphi : E \to F$ with compact support $\operatorname{tsupport}\varphi \subseteq \Omega$. For a compact $K \subseteq \Omega$, the test functions with support in $K$ form the space $\mathcal{D}_K(\Omega, F)$ with the seminorms $\sup_x\|D^k\varphi(x)\|$, $k \in \mathbb{N}$. The space $\mathcal{D}(\Omega, F)$ of all test functions carries the finest locally convex topology for which every inclusion $\mathcal{D}_K \to \mathcal{D}$ is continuous.

::: mathlib
`TestFunction` · `Mathlib.Analysis.Distribution.TestFunction`

`TestFunction Ω F n`, with notation `𝓓^{n}(Ω, F)`, for `Ω : Opens E` and `n : ℕ∞`; `𝓓(Ω, F)` is the case `n = ⊤`. The space with fixed support is `ContDiffMapSupportedIn E F n K`, and `TestFunction.ofSupportedIn` is the inclusion. The topology is `TestFunction.topologicalSpace`. Its main property is `TestFunction.continuous_iff_continuous_comp`: a linear map into a locally convex space is continuous if and only if its composition with each inclusion is continuous.

<?decl TestFunction?>
<?decl ContDiffMapSupportedIn?>
<?decl TestFunction.topologicalSpace?>
<?decl TestFunction.continuous_iff_continuous_comp?>
:::

**Definition (Distribution).** An $F$-valued distribution on $\Omega$ is a continuous $\mathbb{R}$-linear map $T : \mathcal{D}(\Omega, \mathbb{R}) \to F$. Examples: for $f$ locally integrable on $\Omega$, $T_f(\varphi) = \int\varphi(x)f(x)\,dx$; for $a \in \Omega$, the Dirac mass $\delta_a(\varphi) = \varphi(a)$.

**Definition (Derivative).** The derivative of a distribution $T$ along $m \in E$ is $(\partial_m T)(\varphi) = T(-\partial_m\varphi)$.

**Definition (Support).** $T$ vanishes on an open set $U$ if $T(\varphi) = 0$ for every $\varphi$ with $\operatorname{tsupport}\varphi \subseteq U$. The support of $T$ is the complement of the union of all open sets on which $T$ vanishes. It is closed.

::: mathlib
`Distribution` · `Mathlib.Analysis.Distribution.Distribution`

`Distribution Ω F n`, with notation `𝓓'^{n}(Ω, F)` and `𝓓'(Ω, F)` for `n = ⊤`, is `𝓓^{n}(Ω, ℝ) →L_c[ℝ] F`. `Distribution.ofFun Ω f μ n` is $T_f$, with `Distribution.ofFun_apply`. It is the zero map if `f` is not locally integrable on `Ω`. `Distribution.delta x` is $\delta_x$, with `delta_apply` and `ofFun_dirac_eq_delta`. The derivative is the notation `∂_{m}` of the class `LineDeriv`, and `Distribution.lineDerivOp_apply_apply` is `(∂_{m} f) g = f (-∂_{m} g)`. The support is `Distribution.dsupport`, defined with `Distribution.IsVanishingOn` for any `FunLike` map.

<?decl Distribution?>
<?decl Distribution.ofFun?>
<?decl Distribution.ofFun_apply?>
<?decl Distribution.delta?>
<?decl Distribution.delta_apply?>
<?decl Distribution.ofFun_dirac_eq_delta?>
<?decl LineDeriv?>
<?decl Distribution.lineDerivOp_apply_apply?>
<?decl Distribution.dsupport?>
<?decl Distribution.IsVanishingOn?>
<?decl Distribution.notMem_dsupport_iff?>
<?decl Distribution.dsupport_lineDerivOp_subset?>
:::

**Definition (Tempered distribution).** Let $E$ be a finite-dimensional real inner product space. A tempered distribution is a continuous $\mathbb{C}$-linear map $T : \mathcal{S}(E, \mathbb{C}) \to F$. Its Fourier transform is $(\mathcal{F}T)(g) = T(\mathcal{F}g)$, its inverse transform is $(\mathcal{F}^{-1}T)(g) = T(\mathcal{F}^{-1}g)$, and its derivative is $(\partial_m T)(g) = T(-\partial_m g)$.

::: mathlib
`TemperedDistribution` · `Mathlib.Analysis.Distribution.TemperedDistribution`

`TemperedDistribution E F`, notation `𝓢'(E, F)`, is `𝓢(E, ℂ) →L[ℂ] F` with the topology of pointwise convergence. The rules are `TemperedDistribution.fourier_apply` and `TemperedDistribution.lineDerivOp_apply_apply`. A Schwartz function `f` gives `SchwartzMap.toTemperedDistributionCLM E F μ f`, a function of temperate growth gives `Function.HasTemperateGrowth.toTemperedDistribution`, an element of $L^p$ gives `MeasureTheory.Lp.toTemperedDistribution`, and a measure gives `MeasureTheory.Measure.toTemperedDistribution`. In each case the form is $g \mapsto \int g\,f$. The Dirac mass is `TemperedDistribution.delta`.

<?decl TemperedDistribution?>
<?decl TemperedDistribution.fourier_apply?>
<?decl TemperedDistribution.lineDerivOp_apply_apply?>
<?decl SchwartzMap.toTemperedDistributionCLM?>
<?decl Function.HasTemperateGrowth.toTemperedDistribution?>
<?decl MeasureTheory.Lp.toTemperedDistribution?>
<?decl MeasureTheory.Measure.toTemperedDistribution?>
<?decl TemperedDistribution.delta?>
:::

### Theorems and proofs

**Theorem (Fundamental lemma).** Let $f : E \to F$ be locally integrable, and suppose $\int g(x)f(x)\,dx = 0$ for every smooth $g : E \to \mathbb{R}$ with compact support. Then $f = 0$ almost everywhere. So the map $f \mapsto T_f$ is injective on locally integrable functions modulo null sets.

*Proof.* Fix $R > 0$ and a smooth $\chi$ with compact support and $\chi = 1$ on the ball $B(0, R + 1)$. Then $h = \chi f$ is integrable. Let $\rho \ge 0$ be smooth with support in $B(0, 1)$ and $\int\rho = 1$, and $\rho_\varepsilon(z) = \varepsilon^{-d}\rho(z/\varepsilon)$. For $\|x\| < R$ and $\varepsilon < 1$, the function $y \mapsto \rho_\varepsilon(x - y)$ is smooth with compact support in $B(0, R + 1)$, where $\chi = 1$. So
$$(\rho_\varepsilon * h)(x) = \int\rho_\varepsilon(x - y)f(y)\,dy = 0.$$
Convolution with $\rho_\varepsilon$ tends to the identity in $L^1$: this holds for continuous $h$ with compact support by uniform continuity, and for all $h \in L^1$ by density (Volume 18) and the bound $\|\rho_\varepsilon * h\|_1 \le \|h\|_1$. So $h = 0$ almost everywhere on $B(0, R)$, that is $f = 0$ there. Take $R = 1, 2, \ldots$. $\square$

::: mathlib
`ae_eq_zero_of_integral_contDiff_smul_eq_zero` · `Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff`

The hypothesis is `LocallyIntegrable f μ` and the vanishing of `∫ x, g x • f x ∂μ` for every `g : E → ℝ` with `ContDiff ℝ ⊤ g` and `HasCompactSupport g`. The local form on an open set is `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. The consequence for distributions is `Distribution.ofFun_injective`.

<?decl ae_eq_zero_of_integral_contDiff_smul_eq_zero?>
<?decl IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero?>
<?decl Distribution.ofFun_injective?>
:::

**Proposition (Classical and weak derivatives).** Let $f : \mathbb{R} \to \mathbb{C}$ be $C^1$. Then $(T_f)' = T_{f'}$.

*Proof.* Let $\varphi$ be a test function with support in $[-a, a]$. Integration by parts on $[-a, a]$ gives
$$(T_f)'(\varphi) = -\int_{-a}^{a}\varphi'(x)f(x)\,dx = -\big[\varphi f\big]_{-a}^{a} + \int_{-a}^{a}\varphi(x)f'(x)\,dx = T_{f'}(\varphi),$$
since $\varphi(\pm a) = 0$. $\square$

**Proposition (Support of a Dirac mass).** For $a \in \Omega$, the support of $\delta_a$ is $\{a\}$.

*Proof.* The set $U = \Omega \setminus \{a\}$ is open, and every $\varphi$ with support in $U$ has $\varphi(a) = 0$, so $\delta_a$ vanishes on $U$. The support therefore lies in $\{a\}$. If $V$ is an open set that contains $a$, take a smooth bump $\varphi$ with $\varphi(a) = 1$ and support in $V$. Then $\delta_a(\varphi) \ne 0$, so $\delta_a$ does not vanish on $V$, and $a$ is in the support. $\square$

::: mathlib
`Distribution.dsupport_delta` · `Mathlib.Analysis.Distribution.Support`

`∀ x ∈ Ω, dsupport (delta x) = {x}`. Also `Distribution.dsupport_lineDerivOp_subset`: a derivative does not enlarge the support.

<?decl Distribution.dsupport_delta?>
:::

**Theorem (Fourier transform of tempered distributions).** (a) For a Schwartz function $f$, $\mathcal{F}T_f = T_{\mathcal{F}f}$. (b) $\mathcal{F}\delta_0 = T_1$, the distribution $g \mapsto \int g$. (c) $\mathcal{F}(\partial_m T) = 2\pi i\langle x, m\rangle\,\mathcal{F}T$.

*Proof.* (a) For a Schwartz $g$, the multiplication formula of Section 1 gives $(\mathcal{F}T_f)(g) = \int\mathcal{F}g\,f = \int g\,\mathcal{F}f = T_{\mathcal{F}f}(g)$. (b) $(\mathcal{F}\delta_0)(g) = \mathcal{F}g(0) = \int g(x)\,dx$. (c) Section 2 proves $\mathcal{F}(x_m g) = \frac{-1}{2\pi i}\partial_m\mathcal{F}g$ with $x_m = \langle x, m\rangle$. So
$$\mathcal{F}(\partial_m T)(g) = T(-\partial_m\mathcal{F}g) = T\big(\mathcal{F}(2\pi i\,x_m g)\big) = 2\pi i\,(\mathcal{F}T)(x_m g). \qquad\square$$

::: mathlib
`TemperedDistribution.fourier_delta_zero` · `Mathlib.Analysis.Distribution.TemperedDistribution`

`𝓕 (delta 0) = volume.toTemperedDistribution`. Part (a) is `TemperedDistribution.fourier_toTemperedDistributionCLM_eq`, and part (c) is `TemperedDistribution.fourier_lineDerivOp_eq`. On $L^2$, `MeasureTheory.Lp.fourier_toTemperedDistribution_eq` states that the transform of Section 3 agrees with this one.

<?decl TemperedDistribution.fourier_delta_zero?>
<?decl TemperedDistribution.fourier_toTemperedDistributionCLM_eq?>
<?decl TemperedDistribution.fourier_lineDerivOp_eq?>
<?decl MeasureTheory.Lp.fourier_toTemperedDistribution_eq?>
:::

**Definition (Fourier multiplier and Sobolev space).** For $\sigma$ of temperate growth, the Fourier multiplier with symbol $\sigma$ is $T \mapsto \mathcal{F}^{-1}(\sigma\,\mathcal{F}T)$. The Bessel potential $J^s$ is the multiplier with $\sigma(\xi) = (1 + \|\xi\|^2)^{s/2}$. A tempered distribution $T$ lies in the Sobolev space $H^{s,p}$ if $J^sT$ is an element of $L^p$.

By part (c), $\partial_m$ is the multiplier with symbol $2\pi i\langle\xi, m\rangle$, and the Laplacian is the multiplier with symbol $-4\pi^2\|\xi\|^2$.

**Proposition (Derivatives in $H^s$).** If $T \in H^{s,2}$ then $\partial_m T \in H^{s-1,2}$.

*Proof.* By Plancherel, $T \in H^{s,2}$ means that $(1 + \|\xi\|^2)^{s/2}\mathcal{F}T$ is an element of $L^2$. The transform of $\partial_m T$ is $2\pi i\langle\xi, m\rangle\mathcal{F}T$, and
$$\big|(1 + \|\xi\|^2)^{(s-1)/2}\,2\pi i\langle\xi, m\rangle\big| \le 2\pi\|m\|(1 + \|\xi\|^2)^{s/2},$$
since $|\langle\xi, m\rangle| \le \|m\|(1 + \|\xi\|^2)^{1/2}$. So $(1 + \|\xi\|^2)^{(s-1)/2}\mathcal{F}(\partial_m T)$ is in $L^2$ too. $\square$

::: mathlib
`TemperedDistribution.MemSobolev` · `Mathlib.Analysis.Distribution.Sobolev`

`MemSobolev s p f` states that some `f' : Lp F p` has `𝓕⁻ ((1 + ‖x‖ ^ 2) ^ (s / 2) • 𝓕 f) = f'`, with the operator `besselPotential E F s`. For `p = 2` the form with the transform is `memSobolev_iff_exists_smulLeftCLM_fourier`, and the proposition is `MemSobolev.lineDerivOp`. The multiplier is `TemperedDistribution.fourierMultiplierCLM F g`, and `laplacian_eq_fourierMultiplierCLM` is `Δ f = -(2π)² • fourierMultiplierCLM F (‖x‖²) f`.

<?decl TemperedDistribution.MemSobolev?>
<?decl TemperedDistribution.besselPotential?>
<?decl TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier?>
<?decl TemperedDistribution.MemSobolev.lineDerivOp?>
<?decl TemperedDistribution.fourierMultiplierCLM?>
<?decl TemperedDistribution.laplacian_eq_fourierMultiplierCLM?>
<?decl Laplacian?>
:::

### Examples

**Example (The Heaviside function).** Let $H = \mathbf{1}_{[0, \infty)}$ on $\mathbb{R}$. It is locally integrable, and for a test function $\varphi$,
$$(T_H)'(\varphi) = -\int_0^\infty\varphi'(x)\,dx = \varphi(0) - \lim_{x \to \infty}\varphi(x) = \varphi(0).$$
So $(T_H)' = \delta_0$. The classical derivative is $0$ almost everywhere, and $T_0 = 0 \ne \delta_0$: the weak derivative sees the jump.

**Example (The transform of a constant).** By part (b), $\mathcal{F}\delta_0 = 1$. Apply the same argument to $\mathcal{F}^{-1}$: $\mathcal{F}^{-1}\delta_0 = 1$, so $\mathcal{F}1 = \delta_0$ by the inversion theorem on $\mathcal{S}$. More generally $\mathcal{F}(e^{2\pi i\langle x, a\rangle}) = \delta_a$.

### The library around it

The two kinds of distributions use different scalars: a distribution acts on real test functions, a tempered distribution acts on complex Schwartz functions. The derivative and the support are defined for both. The index of this edition has no declaration for the Schwartz kernel theorem, for the structure theorem of distributions with compact support, for the convolution of distributions, or for the Sobolev embedding theorem.

Common errors of a learner:

- Forgetting the minus sign in the derivative of a distribution.
- Using `Distribution.ofFun` with a function that is not locally integrable. The result is `0`, not an error.
- Taking the Bessel potential to be $(1 - \Delta)^{s/2}$. With the convention of Mathlib it is $(1 - (2\pi)^{-2}\Delta)^{s/2}$.

### Exercises

1. (A) Show that $\delta_a' (\varphi) = -\varphi'(a)$, and that the support of $\delta_a'$ is $\{a\}$.
2. (A) Show that $x\,\delta_0 = 0$ as a distribution, where $(x T)(\varphi) = T(x\varphi)$.
3. (A) Compute the derivative of $T_f$ for $f(x) = \max(x, 0)$.
4. (B) Compute $\mathcal{F}(\partial_m\delta_0)$ and $\mathcal{F}(x_m)$ as tempered distributions.
5. (B) Show that $T_f \in H^{0,2}$ if and only if $f \in L^2$. Hint: Plancherel and the injectivity of $L^2 \to \mathcal{S}'$.
6. (C) Show that $\mathbf{1}_{[-1/2, 1/2]}$ lies in $H^{s,2}(\mathbb{R})$ for every $s < 1/2$ and not for $s = 1/2$. Hint: use the transform $\frac{\sin\pi\xi}{\pi\xi}$ of Section 1.

### Notes and history

Sobolev introduced generalised functions and generalised derivatives in the 1930s in his work on partial differential equations. Laurent Schwartz built the general theory of distributions in the late 1940s and published *Théorie des distributions* in 1950 and 1951. He received the Fields Medal in 1950 for this work.

### Reference

<?reference?>
