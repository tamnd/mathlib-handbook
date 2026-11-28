---
title: Strict differentiability and limits of derivatives
kind: theory
modules:
  - Mathlib.Analysis.Calculus.UniformLimitsDeriv
  - Mathlib.Analysis.Calculus.SmoothSeries
  - Mathlib.Analysis.Calculus.FDeriv.Extend
  - Mathlib.Analysis.Calculus.LogDerivUniformlyOn
explains:
  E3: [HasStrictFDerivAt, hasFDerivAt_of_tendstoUniformlyOn, hasFDerivAt_tsum]
  E2: [hasStrictFDerivAt_iff_isLittleO, HasStrictFDerivAt.hasFDerivAt, HasStrictFDerivAt.exists_lipschitzOnWith, hasFDerivAt_of_tendstoUniformly, hasFDerivAt_of_tendstoLocallyUniformlyOn, hasDerivAt_of_tendstoUniformly, hasDerivAt_tsum, hasFDerivAt_tsum_of_isPreconnected, differentiable_tsum, fderiv_tsum]
  E1: auto
families: []
requires: [V17.C01, V17.C02, V15.C01, V15.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Strict differentiability and limits of derivatives

### Overview

This section gives two applications of the mean value inequality of Section 1. The first is the strict derivative. The Fréchet derivative compares $f(y)$ with $f(x)$ at the fixed point $x$. The strict derivative compares $f(y)$ with $f(z)$ for two points $y, z$ that both tend to $x$. This is the hypothesis of the inverse function theorem in Mathlib, and the section proves that each $C^1$ map is strictly differentiable. The second application is the exchange of a limit and a derivative: if $f_n \to g$ pointwise and $Df_n \to G$ uniformly, then $Dg = G$. For series this gives the termwise derivative of $\sum_n f_n$ under a summable bound on $\|Df_n\|$.

### Definitions

**Definition (Strict derivative).** Let $f : E \to F$ and $x \in E$. A map $L \in L(E, F)$ is a *strict derivative* of $f$ at $x$ if
$$f(y) - f(z) - L(y - z) = o(\|y - z\|) \quad \text{as } (y, z) \to (x, x).$$
In $\varepsilon$-$\delta$ form: for each $\varepsilon > 0$ there is $\delta > 0$ with $\|f(y) - f(z) - L(y - z)\| \le \varepsilon\|y - z\|$ for all $y, z \in B(x, \delta)$.

With $z = x$ this is the definition of the Fréchet derivative, so a strict derivative is a derivative, and it is unique.

::: mathlib
`HasStrictFDerivAt` · `Mathlib.Analysis.Calculus.FDeriv.Defs`

`HasStrictFDerivAt f f' x` is `HasFDerivAtFilter f f' (𝓝 (x, x))`: the structure of Chapter 1, with the filter `𝓝 (x, x)` on pairs in place of `𝓝 x ×ˢ pure x`. The form with `isLittleO` is `hasStrictFDerivAt_iff_isLittleO`: `(fun p : E × E => f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝓝 (x, x)] fun p => p.1 - p.2`. Each rule of Chapter 2 has a strict form, such as `HasStrictFDerivAt.comp`.

<?decl HasStrictFDerivAt?>
<?decl hasStrictFDerivAt_iff_isLittleO?>
:::

**Definition (Uniform convergence).** A sequence of maps $G_n : s \to L(E, F)$ *converges uniformly* on $s$ to $G$ if $\sup_{z \in s}\|G_n(z) - G(z)\| \to 0$. It is *uniformly Cauchy* on $s$ if for each $\varepsilon > 0$ there is $N$ with $\|G_m(z) - G_n(z)\| \le \varepsilon$ for all $m, n \ge N$ and $z \in s$.

### Theorems and proofs

**Theorem (Strict implies Lipschitz).** If $f$ has the strict derivative $L$ at $x$, then $f$ is differentiable at $x$ with $Df(x) = L$, and for each $K > \|L\|$ the map $f$ is $K$-Lipschitz on a ball around $x$.

*Proof.* The first part is the case $z = x$. For the second, take $\varepsilon = K - \|L\|$ and $\delta$ as in the definition. For $y, z \in B(x, \delta)$, $\|f(y) - f(z)\| \le \|L(y - z)\| + \varepsilon\|y - z\| \le K\|y - z\|$. $\square$

A map that is only differentiable at $x$ need not be Lipschitz near $x$: the derivative of $x^2\sin(x^{-2})$ is unbounded near $0$.

::: mathlib
`HasStrictFDerivAt.exists_lipschitzOnWith` · `Mathlib.Analysis.Calculus.FDeriv.Basic`

The conclusion is `∃ K, ∃ s ∈ 𝓝 x, LipschitzOnWith K f s`. The form with a given `K > ‖f'‖₊` is `HasStrictFDerivAt.exists_lipschitzOnWith_of_nnNorm_lt`. The derivative is `HasStrictFDerivAt.hasFDerivAt`.

<?decl HasStrictFDerivAt.exists_lipschitzOnWith?>
<?decl HasStrictFDerivAt.hasFDerivAt?>
:::

**Theorem (Continuous derivative implies strict).** Let $f$ be differentiable on a neighbourhood of $x$, and let $z \mapsto Df(z)$ be continuous at $x$. Then $Df(x)$ is a strict derivative of $f$ at $x$. In particular, a $C^1$ map is strictly differentiable at each point.

*Proof.* Let $\varepsilon > 0$. By continuity there is $\delta > 0$ such that $f$ is differentiable on $B(x, \delta)$ and $\|Df(w) - Df(x)\| \le \varepsilon$ for all $w \in B(x, \delta)$. The ball is convex. The mean value inequality with the linear term $L = Df(x)$ of Section 1 gives
$$\|f(y) - f(z) - Df(x)(y - z)\| \le \varepsilon\|y - z\| \quad \text{for } y, z \in B(x, \delta).$$
This is the definition. $\square$

**Theorem (Strict implies continuous derivative).** Let $f$ be differentiable on a neighbourhood of $x$ and have a strict derivative at $x$. Then $z \mapsto Df(z)$ is continuous at $x$.

*Proof.* Let $L = Df(x)$, $\varepsilon > 0$ and $\delta$ as in the definition, with $f$ differentiable on $B(x, \delta)$. Fix $y \in B(x, \delta)$ and $v \in E$. For small $t > 0$, $y + tv \in B(x, \delta)$, so
$$\Big\|\frac{f(y + tv) - f(y)}{t} - Lv\Big\| \le \varepsilon\|v\|.$$
As $t \to 0^+$ the quotient tends to $Df(y)v$ (Chapter 1, Section 2). So $\|Df(y)v - Lv\| \le \varepsilon\|v\|$, that is, $\|Df(y) - L\| \le \varepsilon$. $\square$

So for a map that is differentiable near $x$, the strict derivative at $x$ exists if and only if $Df$ is continuous at $x$.

::: mathlib
`hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt` · `Mathlib.Analysis.Calculus.MeanValue`

`(∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) → ContinuousAt f' x → HasStrictFDerivAt f (f' x) x`, over `ℝ` or `ℂ`. The proof is the one of the text. For a map of class $C^n$ with $n \ge 1$ (Chapter 4), the form is `ContDiffAt.hasStrictFDerivAt`, with the hypothesis `n ≠ 0`.

<?decl hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt?>
<?decl ContDiffAt.hasStrictFDerivAt?>
:::

**Theorem (Limits of derivatives).** Let $U \subseteq E$ be open, and let $f_n : E \to F$ be differentiable at each point of $U$. Assume that $f_n(z) \to g(z)$ for each $z \in U$, and that $Df_n \to G$ uniformly on $U$. Then $g$ is differentiable at each $x \in U$ with $Dg(x) = G(x)$.

*Proof.* Fix $x \in U$ and a ball $B = B(x, r) \subseteq U$. Let $\varepsilon > 0$. A uniformly convergent sequence is uniformly Cauchy, so there is $N$ with $\|Df_m(w) - Df_n(w)\| \le \varepsilon$ for $m, n \ge N$ and $w \in B$, and $\|Df_N(x) - G(x)\| \le \varepsilon$.

Step 1. Let $m, n \ge N$. The map $f_m - f_n$ is differentiable on the convex set $B$ with derivative of norm at most $\varepsilon$. By the mean value inequality, for $\|h\| < r$,
$$\|(f_m - f_n)(x + h) - (f_m - f_n)(x)\| \le \varepsilon\|h\|.$$
Let $m \to \infty$. Since $f_m \to g$ at $x$ and at $x + h$, and the norm is continuous,
$$\|(g - f_n)(x + h) - (g - f_n)(x)\| \le \varepsilon\|h\| \quad \text{for } n \ge N.$$

Step 2. Since $f_N$ is differentiable at $x$, there is $\delta \in (0, r)$ with $\|f_N(x + h) - f_N(x) - Df_N(x)h\| \le \varepsilon\|h\|$ for $\|h\| < \delta$.

Step 3. For $\|h\| < \delta$, write
$$g(x + h) - g(x) - G(x)h = \big[(g - f_N)(x + h) - (g - f_N)(x)\big] + \big[f_N(x + h) - f_N(x) - Df_N(x)h\big] + \big(Df_N(x) - G(x)\big)h.$$
The three terms have norms at most $\varepsilon\|h\|$ by Steps 1 and 2 and the choice of $N$. So $\|g(x + h) - g(x) - G(x)h\| \le 3\varepsilon\|h\|$. Since $\varepsilon$ is arbitrary, $G(x)$ is the derivative. $\square$

::: mathlib
`hasFDerivAt_of_tendstoUniformlyOn` · `Mathlib.Analysis.Calculus.UniformLimitsDeriv`

`IsOpen s → TendstoUniformlyOn f' g' l s → (∀ n, ∀ x ∈ s, HasFDerivAt (f n) (f' n x) x) → (∀ x ∈ s, Tendsto (fun n => f n x) l (𝓝 (g x))) → x ∈ s → HasFDerivAt g (g' x) x`, for a filter `l` with `[NeBot l]` in place of the sequence. The local form is `hasFDerivAt_of_tendstoLocallyUniformlyOn`, the form on all of `E` is `hasFDerivAt_of_tendstoUniformly`, and the form in one variable is `hasDerivAt_of_tendstoUniformly`.

<?decl hasFDerivAt_of_tendstoUniformlyOn?>
<?decl hasFDerivAt_of_tendstoLocallyUniformlyOn?>
<?decl hasFDerivAt_of_tendstoUniformly?>
<?decl hasDerivAt_of_tendstoUniformly?>
:::

**Theorem (Termwise derivative of a series).** Let $F$ be a Banach space, $f_n : E \to F$ differentiable, and $u_n \ge 0$ with $\sum_n u_n < \infty$ and $\|Df_n(z)\| \le u_n$ for all $n$ and $z$. Assume that $\sum_n f_n(x_0)$ converges for one $x_0$. Then $\sum_n f_n(z)$ converges for each $z$, the sum $g$ is differentiable, and $Dg(z) = \sum_n Df_n(z)$.

*Proof.* By the mean value inequality, $\|f_n(z) - f_n(x_0)\| \le u_n\|z - x_0\|$. So $\sum_n \|f_n(z) - f_n(x_0)\|$ converges, and $\sum_n f_n(z)$ converges because $F$ is complete. Put $s_N = \sum_{n < N} f_n$. Then $s_N \to g$ pointwise. The derivatives $Ds_N = \sum_{n < N} Df_n$ converge uniformly on $E$ by the test of Weierstrass: $\|\sum_{n \ge N} Df_n(z)\| \le \sum_{n \ge N} u_n \to 0$, and $L(E, F)$ is complete. The theorem on limits of derivatives gives the result. $\square$

::: mathlib
`hasFDerivAt_tsum` · `Mathlib.Analysis.Calculus.SmoothSeries`

`Summable u → (∀ n x, HasFDerivAt (f n) (f' n x) x) → (∀ n x, ‖f' n x‖ ≤ u n) → Summable (fun n => f n x₀) → ∀ x, HasFDerivAt (fun y => ∑' n, f n y) (∑' n, f' n x) x`. The form on an open connected set is `hasFDerivAt_tsum_of_isPreconnected`. The one-variable form is `hasDerivAt_tsum`, and `differentiable_tsum` and `fderiv_tsum` give the other forms.

<?decl hasFDerivAt_tsum?>
<?decl hasFDerivAt_tsum_of_isPreconnected?>
<?decl hasDerivAt_tsum?>
<?decl differentiable_tsum?>
<?decl fderiv_tsum?>
:::

### Examples

**Example (A series of sines).** Let $g(x) = \sum_{n \ge 1} \frac{\sin nx}{n^3}$. The terms have the derivatives $\frac{\cos nx}{n^2}$, bounded by $u_n = \frac{1}{n^2}$, and $\sum_n u_n = \frac{\pi^2}{6}$. The series converges at $0$. So $g$ is differentiable on $\mathbb{R}$ with $g'(x) = \sum_{n \ge 1} \frac{\cos nx}{n^2}$, and $g'(0) = \frac{\pi^2}{6}$. The next step fails: the derivatives $-\frac{\sin nx}{n}$ of the terms of $g'$ have no summable bound. Indeed $g'(x) = \frac{\pi^2}{6} - \frac{\pi x}{2} + \frac{x^2}{4}$ on $[0, 2\pi]$, and $g'$ is even. So the right derivative of $g'$ at $0$ is $-\frac{\pi}{2}$ and the left derivative is $\frac{\pi}{2}$: $g'$ is not differentiable at $0$.

**Example (Differentiable but not strict).** Let $f(x) = x^2\sin(1/x)$ for $x \neq 0$ and $f(0) = 0$. Then $f'(0) = \lim_{h \to 0} h\sin(1/h) = 0$, and $f'(x) = 2x\sin(1/x) - \cos(1/x)$ for $x \neq 0$. The function is differentiable everywhere, but $f'$ is not continuous at $0$. By the theorem above, $f$ is not strictly differentiable at $0$.

**Example (Strict at a point, not differentiable near it).** Let $A = \{0\} \cup \{1/n : n \ge 1\}$ and $f(x) = |x| \cdot d(x, A)$, where $d(x, A)$ is the distance to $A$. The function $d(\cdot, A)$ is $1$-Lipschitz and $d(x, A) \le |x|$. For $|y|, |z| \le r$,
$$|f(y) - f(z)| \le |y|\,|d(y, A) - d(z, A)| + d(z, A)\,\big||y| - |z|\big| \le 2r|y - z|.$$
So $f$ has the strict derivative $0$ at $0$. Near $1/n$ the distance is $|x - 1/n|$, so $f(x) = x|x - 1/n|$ has the one-sided derivatives $\pm 1/n$ at $1/n$. So $f$ is not differentiable at the points $1/n$, which tend to $0$.

**Counterexample (Uniform convergence of the maps is not enough).** Let $f_n(x) = \sqrt{x^2 + 1/n}$ on $\mathbb{R}$. Then $0 \le f_n(x) - |x| \le 1/\sqrt n$, so $f_n \to |x|$ uniformly, and each $f_n$ is differentiable. The limit is not differentiable at $0$. The derivatives $f_n'(x) = x/\sqrt{x^2 + 1/n}$ converge pointwise to the sign of $x$, but not uniformly near $0$.

### The library around it

`HasStrictFDerivAt` appears in the inverse and implicit function theorems of Chapter 6, which need two moving points. The file `SmoothSeries` gives the differentiability of series, and also `contDiff_tsum`, a form for $C^n$ that Chapter 4 uses.

The file `FDeriv.Extend` extends a derivative to the boundary by a limit. `hasFDerivWithinAt_closure_of_tendsto_fderiv` takes a real map $f$ differentiable on an open convex set $s$, continuous within $s$ at each point of the closure, with `fderiv ℝ f y` tending to $f'$ as $y \to x$ in $s$, and gives `HasFDerivWithinAt f f' (closure s) x`. On the line, `hasDerivWithinAt_Ici_of_tendsto_deriv` gives the one-sided form at an end point. `hasDerivAt_of_hasDerivAt_of_ne` removes one point: if $f$ has derivative $g(y)$ at each $y \neq x$, and $f$ and $g$ are continuous at $x$, then $f$ has derivative $g(x)$ at $x$. The proofs use the mean value inequality, so the field is $\mathbb{R}$.

The file `LogDerivUniformlyOn` treats infinite products of complex functions. `logDeriv_tprod_eq_tsum` states that the logarithmic derivative of $\prod_i f_i$ is $\sum_i f_i'/f_i$ at a point $x$ of an open set $s$, when each $f_i$ is differentiable on $s$ and nonzero at $x$, the product converges locally uniformly on $s$ (`MultipliableLocallyUniformlyOn`), the product is nonzero at $x$, and the series of logarithmic derivatives is summable.

Common errors of a learner:

- Using `HasFDerivAt` for the inverse function theorem. The map $x + 2x^2\sin(1/x)$ has the derivative $1$ at $0$ and is not injective near $0$.
- Asking only for uniform convergence of `f n` in `hasFDerivAt_of_tendstoUniformlyOn`. The uniform convergence is on the derivatives `f' n`.
- Forgetting the pointwise summability at one point in `hasFDerivAt_tsum`. Without it the series can diverge, and `∑'` is then `0`.

### Exercises

1. (A) Show that $x \mapsto x^2$ on $\mathbb{R}$ has the strict derivative $2x$ at each $x$, directly from $y^2 - z^2 - 2x(y - z) = (y - z)(y + z - 2x)$.
2. (A) Show that $g(x) = \sum_{n \ge 1} \frac{e^{-n}}{n}\sin(nx)$ is differentiable, and give $g'$.
3. (B) Let $f$ have a strict derivative $L$ at $x$, and let $L$ be injective with $\|Lh\| \ge c\|h\|$ for some $c > 0$. Show that $f$ is injective on a ball around $x$.
4. (B) Let $A$ be a Banach algebra. Show that $\exp(a) = \sum_{n \ge 0} a^n/n!$ is differentiable on each ball $B(0, R)$, with $D\exp(0) = \mathrm{id}$. Hint: the theorem on series on an open connected set, with $u_n = nR^{n-1}/n!$.
5. (B) Let $f_n(x) = \frac{\sin(n^2 x)}{n}$. Show that $f_n \to 0$ uniformly and that $f_n'(0)$ does not tend to $0$.
6. (C) Prove the theorem on limits of derivatives with the pointwise convergence asked at one point $x_0$ only, for a connected open $U$ on which $Df_n \to G$ uniformly and a Banach space $F$. Hint: show that the set of points where $f_n(z)$ converges is open and closed in $U$, by Step 1 of the proof.

### Notes and history

Karl Weierstrass gave, in 1872, a continuous function on $\mathbb{R}$ that is nowhere differentiable, as a series of cosines; its termwise derivatives have no summable bound.

### Reference

<?reference?>
