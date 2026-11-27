---
title: Removable singularities and limits of holomorphic functions
kind: theory
modules:
  - Mathlib.Analysis.Complex.RemovableSingularity
  - Mathlib.Analysis.Complex.LocallyUniformLimit
  - Mathlib.Analysis.Complex.SummableUniformlyOn
explains:
  E3: [Complex.differentiableOn_update_limUnder_of_bddAbove, Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt, TendstoLocallyUniformlyOn.differentiableOn, TendstoLocallyUniformlyOn.deriv, Complex.differentiableOn_tsum_of_summable_norm]
  E2: [Complex.differentiableOn_compl_singleton_and_continuousAt_iff, Complex.differentiableOn_dslope, Complex.differentiableOn_update_limUnder_of_isLittleO, Complex.differentiableOn_update_limUnder_insert_of_isLittleO, Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO, Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under, Complex.cderiv, Complex.cderiv_eq_deriv, Complex.norm_cderiv_le, Complex.exists_cthickening_tendstoUniformlyOn, Complex.tendstoUniformlyOn_deriv_of_cthickening_subset, Complex.hasSum_deriv_of_summable_norm, SummableLocallyUniformlyOn.differentiableOn]
  E1: auto
families: []
requires: [V19.C01, V19.C02, V17.C07, V18.C08, V13]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Removable singularities and limits of holomorphic functions

### Overview

This section proves two theorems that let holomorphic functions survive a passage to a limit. The first is Riemann's theorem on removable singularities. A function that is holomorphic near $c$ except at $c$, and bounded near $c$, extends to a holomorphic function at $c$. Chapter 4 builds the theory of poles on it.

The second is the theorem of Weierstrass. A locally uniform limit of holomorphic functions is holomorphic, and the derivatives converge locally uniformly to the derivative of the limit. Nothing like this holds for real functions: by the approximation theorem of Weierstrass, $|x|$ is a uniform limit of polynomials on $[-1, 1]$.

Both proofs use the Cauchy formula of Chapter 2, Section 3, circle integrals from Volume 18, Chapter 8, and uniform convergence from Volume 13.

### Definitions

**Definition (Punctured neighbourhood).** A *punctured neighbourhood* of $c$ is a set $V \setminus \{c\}$ where $V$ is a neighbourhood of $c$. A function $f$ has an *isolated singularity* at $c$ if it is holomorphic on a punctured neighbourhood of $c$. The singularity is *removable* if some value at $c$ makes $f$ holomorphic on $V$.

**Definition (Locally uniform convergence).** A family $f_n$ *converges locally uniformly* to $f$ on an open set $U$ if every point of $U$ has a neighbourhood on which $f_n \to f$ uniformly. On an open subset of $\mathbb{C}$ this is the same as uniform convergence on every compact subset of $U$.

**Definition (Circle derivative).** For $r > 0$ and $f$ continuous on the circle $|z - w| = r$, put
$$\operatorname{cderiv}_r f(w) = \frac{1}{2\pi i}\oint_{|z - w| = r} \frac{f(z)}{(z - w)^2}\,dz.$$

::: mathlib
`TendstoLocallyUniformlyOn` · `Mathlib.Topology.UniformSpace.LocallyUniformConvergence`

`TendstoLocallyUniformlyOn F f φ U` takes a family `F : ι → ℂ → E` and a filter `φ` on `ι`. The circle derivative is `Complex.cderiv r f w`. It is defined for every `f`, and `Complex.cderiv_eq_deriv` identifies it with `deriv f w` when `f` is differentiable on an open set that contains `closedBall w r`.

<?decl TendstoLocallyUniformlyOn?>
:::

### Theorems and proofs

**Theorem (Riemann's removable singularity theorem).** Let $f$ be holomorphic on $D(c, R) \setminus \{c\}$, and bounded near $c$. Then $\lim_{z \to c} f(z)$ exists, and $f$ with this value at $c$ is holomorphic on $D(c, R)$.

*Proof.* Let $|f| \le M$ on $D(c, \rho) \setminus \{c\}$. Define $h(z) = (z - c)^2 f(z)$ for $z \ne c$ and $h(c) = 0$. At $c$,
$$\left|\frac{h(z) - h(c)}{z - c}\right| = |z - c|\,|f(z)| \le M|z - c| \to 0,$$
so $h$ is complex differentiable at $c$ with $h'(c) = 0$. So $h$ is holomorphic on $D(c, R)$. By Chapter 2, Section 3, $h(z) = \sum_{n \ge 0} a_n (z - c)^n$ on $D(c, R)$, with $a_0 = h(c) = 0$ and $a_1 = h'(c) = 0$. The series $g(z) = \sum_{n \ge 2} a_n (z - c)^{n - 2}$ has the same radius of convergence, so $g$ is holomorphic on $D(c, R)$. For $z \ne c$, $g(z) = h(z)/(z - c)^2 = f(z)$. So $f(z) \to g(c) = a_2$ as $z \to c$, and $f$ with the value $a_2$ at $c$ is $g$. $\square$

The proof used the bound only to get $(z - c) f(z) \to 0$. So the theorem holds under the weaker hypothesis $f(z) = o(1/|z - c|)$. The function $1/(z - c)$ shows that this is sharp.

**Corollary.** If $f$ is holomorphic on a punctured neighbourhood of $c$ and continuous at $c$, then $f$ is analytic at $c$.

*Proof.* A function continuous at $c$ is bounded near $c$. The theorem gives a holomorphic extension, and its value at $c$ is the limit, which is $f(c)$ by continuity. So $f$ is holomorphic near $c$, hence analytic at $c$ by Chapter 2, Section 3. $\square$

::: mathlib
`Complex.differentiableOn_update_limUnder_of_bddAbove` · `Mathlib.Analysis.Complex.RemovableSingularity`

For `s ∈ 𝓝 c`, `DifferentiableOn ℂ f (s \ {c})` and `BddAbove (norm ∘ f '' (s \ {c}))`, it gives `DifferentiableOn ℂ (update f c (limUnder (𝓝[≠] c) f)) s`. The `o` form is `Complex.differentiableOn_update_limUnder_of_isLittleO`, with the hypothesis `(fun z ↦ f z - f c) =o[𝓝[≠] c] fun z ↦ (z - c)⁻¹`. The limit itself is `Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under`.

<?decl Complex.differentiableOn_update_limUnder_of_bddAbove?>
:::

::: mathlib
`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` · `Mathlib.Analysis.Complex.RemovableSingularity`

From `∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z` and `ContinuousAt f c` it concludes `AnalyticAt ℂ f c`. The set form is `Complex.differentiableOn_compl_singleton_and_continuousAt_iff`. A typical use is `Complex.differentiableOn_dslope`.

<?decl Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt?>
:::

**Lemma (Integrals of the Cauchy kernel).** Let $f$ be continuous on the circle $|z - c| = r$. Then
$$F(w) = \frac{1}{2\pi i}\oint_{|z - c| = r}\frac{f(z)}{z - w}\,dz$$
is holomorphic on $D(c, r)$.

*Proof.* Fix $w$ with $|w - c| = s < r$. For $|z - c| = r$,
$$\frac{1}{z - w} = \sum_{n \ge 0}\frac{(w - c)^n}{(z - c)^{n + 1}},$$
and the $n$-th term is bounded by $s^n/r^{n+1}$. The series converges uniformly in $z$, so it can be integrated term by term. This gives $F(w) = \sum_n b_n (w - c)^n$ with $b_n = \frac{1}{2\pi i}\oint f(z)(z - c)^{-n-1}\,dz$ and $|b_n| \le \max|f|\,r^{-n}$. This power series converges on $D(c, r)$, so $F$ is holomorphic there (Volume 17, Chapter 7). $\square$

**Theorem (Weierstrass).** Let $U$ be open, let $f_n$ be holomorphic on $U$, and let $f_n \to f$ locally uniformly on $U$. Then $f$ is holomorphic on $U$, and $f_n' \to f'$ locally uniformly on $U$.

*Proof.* The limit $f$ is continuous. Fix $c \in U$ and $r > 0$ with $\bar D(c, r) \subseteq U$. The circle is compact, so $f_n \to f$ uniformly on it. Let $w \in D(c, r)$ and $\delta = r - |w - c| > 0$. The Cauchy formula gives
$$f_n(w) = \frac{1}{2\pi i}\oint_{|z - c| = r}\frac{f_n(z)}{z - w}\,dz.$$
The difference of the integrals for $f_n$ and $f$ is bounded by $\frac{1}{2\pi}\cdot 2\pi r\cdot\frac{\sup|f_n - f|}{\delta}$, which tends to $0$. Since $f_n(w) \to f(w)$, $f$ satisfies the same formula on $D(c, r)$. By the lemma, $f$ is holomorphic on $D(c, r)$. So $f$ is holomorphic on $U$.

For the derivatives, let $K \subseteq U$ be compact. There is $\rho > 0$ such that the closed $\rho$-thickening $K_\rho = \{z : \operatorname{dist}(z, K) \le \rho\}$ lies in $U$. Otherwise there are $z_k \notin U$ with $\operatorname{dist}(z_k, K) \to 0$, and a subsequence converges to a point of $K$ outside the open set $U$. The set $K_\rho$ is closed and bounded, hence compact, so $f_n \to f$ uniformly on $K_\rho$. For a holomorphic $g$ on $U$ and $w \in K$, the derivative formula of Chapter 2, Section 3 gives $g'(w) = \operatorname{cderiv}_\rho g(w)$. The standard estimate of the integral gives
$$|f_n'(w) - f'(w)| = |\operatorname{cderiv}_\rho (f_n - f)(w)| \le \frac{1}{\rho}\sup_{K_\rho}|f_n - f|,$$
uniformly in $w \in K$. So $f_n' \to f'$ uniformly on $K$. $\square$

::: mathlib
`TendstoLocallyUniformlyOn.differentiableOn` · `Mathlib.Analysis.Complex.LocallyUniformLimit`

The statement takes `TendstoLocallyUniformlyOn F f φ U`, `∀ᶠ n in φ, DifferentiableOn ℂ (F n) U` and `IsOpen U`, with `[φ.NeBot]`, and concludes `DifferentiableOn ℂ f U`. The filter must not be `⊥`, since every statement holds eventually along `⊥`.

<?decl TendstoLocallyUniformlyOn.differentiableOn?>
:::

::: mathlib
`TendstoLocallyUniformlyOn.deriv` · `Mathlib.Analysis.Complex.LocallyUniformLimit`

With the same hypotheses, minus `NeBot`, it concludes `TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f) φ U`. The steps of the proof are `Complex.exists_cthickening_tendstoUniformlyOn`, `Complex.norm_cderiv_le` and `Complex.tendstoUniformlyOn_deriv_of_cthickening_subset`.

<?decl TendstoLocallyUniformlyOn.deriv?>
:::

**Corollary (Series).** Let $f_i$ be holomorphic on $U$ with $|f_i(z)| \le u_i$ for $z \in U$, where $\sum_i u_i < \infty$. Then $F = \sum_i f_i$ is holomorphic on $U$, and $F' = \sum_i f_i'$ on $U$.

*Proof.* By the Weierstrass test, the partial sums converge uniformly on $U$. They are holomorphic, so the theorem applies to them. The derivatives of the partial sums are the partial sums of the derivatives, and they converge to $F'$. $\square$

::: mathlib
`Complex.differentiableOn_tsum_of_summable_norm` · `Mathlib.Analysis.Complex.LocallyUniformLimit`

The statement takes `Summable u`, `∀ i, DifferentiableOn ℂ (F i) U`, `IsOpen U` and `∀ i, ∀ w ∈ U, ‖F i w‖ ≤ u i`, and concludes `DifferentiableOn ℂ (fun w ↦ ∑' i, F i w) U`. The derivative is `Complex.hasSum_deriv_of_summable_norm`. For a bound that holds only locally, `SummableLocallyUniformlyOn.differentiableOn` asks for `SummableLocallyUniformlyOn f s`.

<?decl Complex.differentiableOn_tsum_of_summable_norm?>
:::

### Examples

**Example.** The function $\sin z/z$ is holomorphic on $\mathbb{C} \setminus \{0\}$ and tends to $1$ at $0$. The theorem makes it entire, with the series $\sum_{n \ge 0} (-1)^n z^{2n}/(2n+1)!$.

**Example.** For $\operatorname{Re} s \ge \sigma > 1$, $|n^{-s}| = n^{-\operatorname{Re} s} \le n^{-\sigma}$, and $\sum n^{-\sigma} < \infty$. The corollary on the open half plane $\operatorname{Re} s > \sigma$ shows that $\sum_{n \ge 1} n^{-s}$ is holomorphic there. Every $s$ with $\operatorname{Re} s > 1$ lies in such a half plane. This is the Riemann zeta function on $\operatorname{Re} s > 1$, with derivative $-\sum_n (\log n)\,n^{-s}$.

**Example.** On $\mathbb{D}$, $f_n(z) = z^n/n$ tends to $0$ uniformly. The derivatives $z^{n-1}$ tend to $0$ locally uniformly but not uniformly on $\mathbb{D}$, since $f_n'(x) \to 1$ as $x \to 1$ for each $n$. So the theorem cannot promise more than locally uniform convergence of the derivatives.

### The library around it

Common errors of a learner:

- Asking for uniform convergence on all of $U$. Uniform convergence on compact subsets suffices.
- Forgetting the new value at $c$. In Mathlib the function `f` keeps its old value; the holomorphic function is `update f c (limUnder (𝓝[≠] c) f)`.

The index of this edition has no declaration for Hurwitz's theorem on the zeros of a limit of holomorphic functions, nor for Montel's theorem on normal families.

### Exercises

1. (A) Show that $(1 - \cos z)/z^2$ has a removable singularity at $0$, and find its value there.
2. (A) Show that $\sum_{n \ge 1} z^n/n^2$ is holomorphic on $\mathbb{D}$, and find its derivative.
3. (B) Let $f$ be holomorphic on $D(c, R) \setminus \{c\}$ with $|f(z)| \le |z - c|^{-1/2}$ near $c$. Show that the singularity is removable. Hint: use the $o(1/|z - c|)$ form of the theorem.
4. (B) Show that $\sum_{n \ge 1} 2^{-n}\sin(nz)$ is holomorphic on the strip $|\operatorname{Im} z| < \log 2$, and that it diverges for $|\operatorname{Im} z| > \log 2$. Hint: apply the corollary on $|\operatorname{Im} z| < \sigma$ for each $\sigma < \log 2$.
5. (B) Show that $\sum_{n \ge 1} (z - n)^{-2}$ is holomorphic on $\mathbb{C} \setminus \{1, 2, 3, \dots\}$. Hint: on a disc that avoids the positive integers, bound the terms by $C/n^2$ for large $n$, and apply the corollary on that disc.
6. (C) Prove Hurwitz's theorem: if $f_n \to f$ locally uniformly on a domain, each $f_n$ has no zeros, and $f$ is not identically zero, then $f$ has no zeros. Hint: on a small circle around a zero, compare $\frac{1}{2\pi i}\oint f_n'/f_n$ with $\frac{1}{2\pi i}\oint f'/f$.

### Notes and history

The removable singularity theorem carries the name of Riemann. The theorem on limits carries the name of Weierstrass, who built his theory of analytic functions on power series and their limits rather than on the Cauchy integral.

### Reference

<?reference?>
