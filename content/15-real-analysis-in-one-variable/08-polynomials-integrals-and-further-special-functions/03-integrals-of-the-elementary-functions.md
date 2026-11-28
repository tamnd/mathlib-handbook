---
title: Integrability of the elementary functions
kind: api
modules:
  - Mathlib.Analysis.SpecialFunctions.Integrability.Basic
  - Mathlib.Analysis.SpecialFunctions.Integrability.Log
  - Mathlib.Analysis.SpecialFunctions.Integrability.PosLog
  - Mathlib.Analysis.SpecialFunctions.NonIntegrable
  - Mathlib.Analysis.SpecialFunctions.Pow.Integral
  - Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
  - Mathlib.Analysis.SpecialFunctions.PolarCoord
  - Mathlib.Analysis.SpecialFunctions.MulExpNegMulSqIntegral
explains:
  E2: [intervalIntegral.integrableOn_Ioo_rpow_iff, intervalIntegrable_inv_iff, not_integrableOn_Ioi_inv, MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul, Frullani.integral_comp_mul_inv_smul, Frullani.integral_Ioi_eq, det_fderivPolarCoordSymm, integral_comp_polarCoord_symm]
  E1: auto
families: []
requires: [V13, V15.C02, V15.C03, V15.C05, V15.C06, V18]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Integrability of the elementary functions

### Overview

The theory of the integral is in Volume 18. Before a proof computes an integral of an elementary function, it must know that the function is integrable on the domain. This section collects these facts for the functions of Chapters 5 and 6: powers, the logarithm, the exponential, the trigonometric functions and $1/x$. It also treats three classical computations that need only these facts and a change of variables: the layer-cake formula for $\int f^p$, Frullani's integral $\int_0^\infty (f(ax) - f(bx))/x \, dx$, and the change to polar coordinates in the plane.

The questions of integrability have two kinds of answers. A continuous function on a compact interval is integrable, so most lemmas only check continuity. The interesting cases are the singular ones: $x^s$ near $0$, $\log x$ near $0$, $1/x$ on an interval that contains $0$, and $1/x$ on $(a, \infty)$. For these the library gives exact criteria.

In Mathlib, `IntervalIntegrable f μ a b` states that $f$ is integrable on the interval between $a$ and $b$, in either order, and `MeasureTheory.IntegrableOn f s μ` states that $f$ is integrable on the set $s$. The measure `volume` on $\mathbb{R}$ is the Lebesgue measure.

### The library around it

#### Interval integrability of the elementary functions

The module `Mathlib.Analysis.SpecialFunctions.Integrability.Basic` has one lemma for each elementary function, in the namespace `intervalIntegral`. The name of each lemma is the name of the function after `intervalIntegrable_`. The continuous functions need no hypothesis: `intervalIntegral.intervalIntegrable_exp`, `intervalIntegral.intervalIntegrable_sin`, `intervalIntegral.intervalIntegrable_cos`, `intervalIntegral.intervalIntegrable_pow` and `intervalIntegral.intervalIntegrable_inv_one_add_sq` hold for every locally finite measure $\mu$ and all $a, b$. The functions with a singularity at $0$ have a hypothesis of the form `0 ≤ r ∨ 0 ∉ Set.uIcc a b`: the exponent is harmless, or the interval avoids $0$. This is the form of `intervalIntegral.intervalIntegrable_rpow`, `intervalIntegral.intervalIntegrable_zpow`, `intervalIntegral.intervalIntegrable_cpow` and `intervalIntegral.intervalIntegrable_log`. For a composition, `intervalIntegral.intervalIntegrable_inv` and `IntervalIntegrable.log` need $f$ continuous and nonzero on the interval.

For the Lebesgue measure the singular functions are integrable in more cases, and the primed lemmas state this. `intervalIntegral.intervalIntegrable_rpow'` holds for every $r > -1$, and `intervalIntegral.intervalIntegrable_log'` holds on every interval, also an interval that contains $0$. The exact criterion for powers near $0$ is the next theorem.

**Theorem.** For $t > 0$, $x^s$ is integrable on $(0, t)$ if and only if $s > -1$.

*Proof.* For $s > -1$ the function $x^{s+1}/(s+1)$ is a primitive of $x^s$ on $(0, t)$, continuous on $[0, t]$, so the integral is $t^{s+1}/(s+1) < \infty$. For $s \le -1$ and $0 < x < t$, $x^s = x^{-1} x^{s+1} \ge t^{s+1} x^{-1}$, because $s + 1 \le 0$. The function $1/x$ is not integrable on $(0, t)$, because $\int_\varepsilon^t dx/x = \log(t/\varepsilon) \to \infty$ as $\varepsilon \to 0$. $\square$

This is `intervalIntegral.integrableOn_Ioo_rpow_iff`, and `intervalIntegral.integrableOn_Ioo_cpow_iff` is the complex version with the real part of $s$.

#### Logarithms of meromorphic functions

The modules `Mathlib.Analysis.SpecialFunctions.Integrability.Log` and `Mathlib.Analysis.SpecialFunctions.Integrability.PosLog` treat $\log |f|$ and $\log^+ |f|$ for a meromorphic function $f$. A meromorphic function has isolated zeros and poles, and near each of them $\log |f(x)|$ behaves as $k \log |x - x_0|$, which is integrable. So `MeromorphicOn.intervalIntegrable_log_norm` states that $\log \|f\|$ is interval integrable on $[a, b]$ when $f$ is meromorphic on $[a, b]$, and `MeromorphicOn.intervalIntegrable_posLog_norm` states the same for $\log^+$. Special cases are `intervalIntegrable_log_sin` and `intervalIntegrable_log_cos`. The versions on circles, `MeromorphicOn.circleIntegrable_log_norm`, `circleIntegrable_log_norm_sub_const` and `MeromorphicOn.circleIntegrable_posLog_norm`, give the integrability of $\theta \mapsto \log|f(c + Re^{i\theta})|$. Jensen's formula of Volume 19 and the Mahler measure of the first section of this chapter need exactly these facts.

#### Functions that are not integrable

The module `Mathlib.Analysis.SpecialFunctions.NonIntegrable` proves non-integrability from the growth of a primitive. The main lemma is `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured`: if $\|f(x)\| \to \infty$ as $x \to c$, $x \ne c$, and $f' = O(g)$ near $c$, then $g$ is not interval integrable on any nontrivial interval that contains $c$. The idea is the fundamental theorem of calculus: if $g$ were integrable, then $\|f(y) - f(x)\| \le C \int_x^y \|g\|$ would stay bounded near $c$. The version `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter` works for a one-sided neighborhood or another filter, and `not_intervalIntegrable_of_sub_inv_isBigO_punctured` applies the lemma with $f(x) = \log|x - c|$: a function that is at least of size $1/|x - c|$ near $c$ is not integrable.

**Theorem.** $1/x$ is interval integrable on $[a, b]$ if and only if $a = b$ or $0 \notin [a, b]$.

*Proof.* If $0 \notin [a, b]$, then $1/x$ is continuous on $[a, b]$ and so integrable. If $a = b$, the interval is a point. If $a \ne b$ and $0 \in [a, b]$, apply the previous lemma with $f = \log|x|$: $|\log|x|| \to \infty$ as $x \to 0$, and $f'(x) = 1/x$. $\square$

This is `intervalIntegrable_inv_iff`, and `intervalIntegrable_sub_inv_iff` is the version for $1/(x - c)$. At infinity, `not_integrableOn_Ioi_inv` and `not_integrableOn_Ici_inv` state that $1/x$ is not integrable on $(a, \infty)$: the primitive $\log x$ tends to infinity at $\infty$. These two facts are the continuous form of the divergence of the harmonic series of Chapter 1.

#### The layer-cake formula and power decay

The module `Mathlib.Analysis.SpecialFunctions.Pow.Integral` proves the layer-cake formula for powers. For $f \ge 0$ almost everywhere and $p > 0$,
$$\int f^p \, d\mu = p \int_0^\infty \mu\{f \ge t\}\, t^{p-1} \, dt.$$
This is `MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul`, with lower integrals in $[0, \infty]$. *Proof sketch.* Write $f(\omega)^p = \int_0^{f(\omega)} p\, t^{p-1}\, dt$, which is the integral of the power from the previous subsection. Then exchange the two integrals by Tonelli's theorem: the integral over $\omega$ of the indicator of $t \le f(\omega)$ is $\mu\{f \ge t\}$. $\square$ The variant `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul` uses the sets $\{f > t\}$. The same module proves `MeasureTheory.locallyIntegrable_of_norm_le_rpow`: in a real normed space of finite dimension $d \ge 1$ with a Haar measure, a function with $\|f(x)\| \le C\|x\|^{-\alpha}$ for $\alpha < d$ is locally integrable. This is the analogue in dimension $d$ of the criterion $s > -1$.

#### Frullani's integral

The module `Mathlib.Analysis.SpecialFunctions.FrullaniIntegral` proves Frullani's formula. Let $f$ be locally integrable on $(0, \infty)$ with $f(x) \to L$ as $x \to 0^+$ and $f(x) \to R$ as $x \to \infty$, and let $a, b > 0$. Then
$$\int_0^\infty \frac{f(ax) - f(bx)}{x}\, dx = (L - R) \log \frac{b}{a},$$
provided the integrand is integrable on $(0, \infty)$. This is `Frullani.integral_Ioi_eq`, for $f$ with values in a Banach space $E$.

*Proof.* The substitution $u = cx$ gives $\int_\varepsilon^r f(cx)/x \, dx = \int_{c\varepsilon}^{cr} f(u)/u \, du$ (`Frullani.integral_comp_mul_inv_smul`). So
$$\int_\varepsilon^r \frac{f(ax) - f(bx)}{x}\, dx = \int_{a\varepsilon}^{b\varepsilon} \frac{f(u)}{u}\, du - \int_{ar}^{br} \frac{f(u)}{u}\, du.$$
On $[a\varepsilon, b\varepsilon]$ the function $f$ is close to $L$, and $\int_{a\varepsilon}^{b\varepsilon} du/u = \log(b/a)$. So the first integral tends to $L \log(b/a)$ as $\varepsilon \to 0$, and the second tends to $R \log(b/a)$ as $r \to \infty$. $\square$

The limit form `Frullani.tendsto_intervalIntegral` states the convergence of the integrals over $[\varepsilon, r]$ without the hypothesis of integrability on $(0, \infty)$. The norm bound `Frullani.norm_integral_inv_smul_sub_le` gives the estimate of the proof. For example, $f(x) = e^{-x}$ gives $\int_0^\infty (e^{-ax} - e^{-bx})/x \, dx = \log(b/a)$.

#### Polar coordinates

The module `Mathlib.Analysis.SpecialFunctions.PolarCoord` defines `polarCoord` as an open partial homeomorphism of $\mathbb{R}^2$. Its source is the plane without the closed half-line $\{(x, 0) : x \le 0\}$ (`polarCoord_source`), and its target is $(0, \infty) \times (-\pi, \pi)$ (`polarCoord_target`). The inverse is the familiar map (`polarCoord_symm_apply`):
$$(r, \theta) \mapsto (r \cos\theta, r\sin\theta).$$
The forward map sends $q$ to $(\sqrt{q_1^2 + q_2^2}, \arg q)$ (`polarCoord_apply`), with the argument of Chapter 6 of the complex number $q_1 + iq_2$.

**Theorem.** The Jacobian determinant of $(r, \theta) \mapsto (r\cos\theta, r\sin\theta)$ is $r$.

*Proof.* The derivative is the matrix with rows $(\cos\theta, -r\sin\theta)$ and $(\sin\theta, r\cos\theta)$. Its determinant is $r\cos^2\theta + r\sin^2\theta = r$. $\square$

This is `det_fderivPolarCoordSymm`, for the derivative `fderivPolarCoordSymm` of `hasFDerivAt_polarCoord_symm`. The removed half-line has measure $0$ (`polarCoord_source_ae_eq_univ`), so the change of variables formula of Volume 18 gives `integral_comp_polarCoord_symm`:
$$\int_{\mathbb{R}^2} f(p)\, dp = \int_{(0,\infty) \times (-\pi, \pi)} r\, f(r\cos\theta, r\sin\theta)\, dr\, d\theta.$$
The version `lintegral_comp_polarCoord_symm` is for functions with values in $[0, \infty]$, and the versions for products, such as `integral_comp_pi_polarCoord_symm`, use polar coordinates in each factor of $(\mathbb{R}^2)^\iota$. The complex version `Complex.polarCoord` sends $z$ to $(|z|, \arg z)$ (`Complex.polarCoord_apply`), with source the slit plane `Complex.slitPlane`, and `Complex.integral_comp_polarCoord_symm` is its change of variables. The computation of the Gaussian integral $\int_{\mathbb{R}} e^{-x^2} dx = \sqrt{\pi}$ uses this formula for $e^{-(x^2 + y^2)}$.

#### Integrals of $x e^{-\varepsilon x^2}$

The module `Mathlib.Analysis.SpecialFunctions.MulExpNegMulSqIntegral` integrates the bounded cut-off `Real.mulExpNegMulSq ε ∘ g` of the section on auxiliary functions against a finite measure $P$. By dominated convergence, `tendsto_integral_mulExpNegMulSq_comp` states that $\int g(x) e^{-\varepsilon g(x)^2}\, dP \to \int g\, dP$ as $\varepsilon \to 0^+$, for a bounded continuous $g$. The exponential is the limit of $(1 - \varepsilon g^2/n)^n$, so `integral_mulExpNegMulSq_comp_eq` states: if two finite measures give the same integral to every element of a subalgebra $A$ of bounded continuous functions, then they give the same integral to $g e^{-\varepsilon g^2}$ for $g \in A$. With the Stone-Weierstrass theorem, `dist_integral_mulExpNegMulSq_comp_le` bounds the difference of the two integrals of $f e^{-\varepsilon f^2}$ by $6\sqrt{\varepsilon}$ for every bounded continuous $f$, when $A$ separates points. Probability theory uses this to prove that a separating algebra of functions determines a finite measure.

#### Common errors

1. `intervalIntegral.intervalIntegrable_rpow` with a general measure needs `0 ≤ r ∨ 0 ∉ Set.uIcc a b`. For $r \in (-1, 0)$ and the Lebesgue measure, use the primed lemma `intervalIntegral.intervalIntegrable_rpow'`.
2. The Lean integral of a non-integrable function is $0$, not $\infty$. So `∫ x in (0:ℝ)..1, x⁻¹` is $0$ in Mathlib. A computation of an integral must first prove integrability, and `intervalIntegrable_inv_iff` shows when this fails.
3. The target of `polarCoord` uses the angles in $(-\pi, \pi)$, not $[0, 2\pi)$. A computation that integrates $\theta$ over $[0, 2\pi]$ must shift the interval with the periodicity of $\sin$ and $\cos$.

### Exercises

1. (A) Decide for which real $s$ the function $x^s$ is integrable on $(0, 1)$ and on $(1, \infty)$. Use the substitution $x = 1/u$ for the second interval.
2. (A) Compute $\int_0^\infty (e^{-x} - e^{-2x})/x \, dx$ with Frullani's formula, and check the hypotheses $L$ and $R$.
3. (B) Prove the layer-cake formula for $p = 1$ and a simple function $f$ with two values, by a direct computation of both sides.
4. (B) Use polar coordinates to show $\int_{\mathbb{R}^2} e^{-(x^2+y^2)}\, dx\,dy = \pi$, and deduce $\int_{\mathbb{R}} e^{-x^2} dx = \sqrt{\pi}$.
5. (B) Show that $\log|\sin x|$ is integrable on $[0, \pi]$ from the bound $|\sin x| \ge 2x/\pi$ on $[0, \pi/2]$ and the integrability of $\log x$ near $0$.
6. (C) Show that $1/(x \log x)$ is not integrable on $(2, \infty)$ with the method of the module on non-integrable functions: find a primitive that tends to infinity.

### Reference

<?reference?>
