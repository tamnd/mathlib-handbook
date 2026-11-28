---
title: Circle, torus and curve integrals and the divergence theorem
kind: api
modules:
  - Mathlib.MeasureTheory.Integral.CircleIntegral
  - Mathlib.MeasureTheory.Integral.CircleAverage
  - Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
  - Mathlib.MeasureTheory.Integral.CircleTransform
  - Mathlib.MeasureTheory.Integral.TorusIntegral
  - Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
  - Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
  - Mathlib.MeasureTheory.Integral.DivergenceTheorem
explains:
  E2: [circleIntegral, circleIntegral.integral_sub_zpow_of_ne, circleIntegral.integral_sub_inv_of_mem_ball, hasFPowerSeriesOn_cauchy_integral, Real.circleAverage, torusIntegral, curveIntegral, curveIntegral_trans, Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric, MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable]
  E1: auto
families: []
requires: [V13, V15, V16, V18.C03, V18.C05, V18.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Circle, torus and curve integrals and the divergence theorem

### Overview

The interval integral of Section 1 gives several integrals of geometry by a change of parameter. A circle in $\mathbb{C}$ is the image of $[0, 2\pi]$, a torus in $\mathbb{C}^n$ is the image of $[0, 2\pi]^n$, and a path in a normed space is the image of $[0, 1]$. Each integral is defined as an interval integral, or an integral on a box, of the function composed with the parameter and multiplied by the derivative of the parameter. This section describes the circle integral $\oint_{|z - c| = R} f(z) \, dz$ and the circle average, the Cauchy integral formula for power series, the torus integral, the integral of a 1-form along a path with the lemma of Poincaré, and the divergence theorem on a box.

These integrals are the base of complex analysis in Mathlib. The theorems of Cauchy for holomorphic functions are in the volume on complex analysis; this section gives only the parts that are pure integration.

### The library around it

#### The circle integral

The function `circleMap c R` sends $\theta$ to $c + R e^{i\theta}$. It is smooth, `contDiff_circleMap`, and its derivative is $i R e^{i\theta}$, `deriv_circleMap`. The circle integral `circleIntegral f c R` is

$$\oint_{C(c, R)} f(z) \, dz = \int_0^{2\pi} (\text{circleMap } c\, R)'(\theta) \cdot f(c + R e^{i\theta}) \, d\theta.$$

The notation `∮ z in C(c, R), f z` stands for it. The radius $R$ is a real number of any sign; a negative radius gives the same circle with a different start point. The predicate `CircleIntegrable f c R` says that $\theta \mapsto f(\text{circleMap } c\, R\, \theta)$ is integrable on $[0, 2\pi]$. A function continuous on the sphere is circle integrable, `ContinuousOn.circleIntegrable`.

The basic computation is the integral of a power. For an integer $n \ne -1$, `circleIntegral.integral_sub_zpow_of_ne` gives

$$\oint_{C(c, R)} (z - w)^n \, dz = 0$$

for every $w$. The proof finds a primitive: $(z - w)^{n+1}/(n + 1)$. When $w$ is on the circle and $n < 0$, the integrand is not integrable, and the integral is $0$ by the convention of Chapter 5. For $n = -1$ and $w$ inside the open disc, `circleIntegral.integral_sub_inv_of_mem_ball` gives the value $2 \pi i$. The case $w = c$ is `circleIntegral.integral_sub_center_inv`.

The bound $\|\oint f\| \le 2 \pi R C$ for $\|f\| \le C$ on the circle is `circleIntegral.norm_integral_le_of_norm_le_const`. The integral of a derivative along the circle is $0$, `circleIntegral.integral_eq_zero_of_hasDerivWithinAt`.

#### The Cauchy power series

For a circle integrable $f$, the file defines the formal power series `cauchyPowerSeries f c R` whose $n$th coefficient is

$$\frac{1}{2 \pi i} \oint_{C(c, R)} \frac{f(z)}{(z - c)^{n+1}} \, dz.$$

The theorem `hasFPowerSeriesOn_cauchy_integral` says that this series converges on the open disc of radius $R$ to the function

$$w \mapsto \frac{1}{2 \pi i} \oint_{C(c, R)} \frac{f(z)}{z - w} \, dz.$$

The proof expands $1/(z - w)$ as a geometric series in $(w - c)/(z - c)$ and exchanges the sum and the integral. This theorem needs no holomorphy: it holds for every circle integrable $f$. The Cauchy integral formula, in the volume on complex analysis, then shows that for a holomorphic $f$ the function on the right is $f$ itself, so a holomorphic function is analytic.

#### Circle averages and the circle transform

The file `Mathlib.MeasureTheory.Integral.CircleAverage` defines `Real.circleAverage f c R`, the average of $f$ on the circle:

$$\frac{1}{2\pi} \int_0^{2\pi} f(c + R e^{i\theta}) \, d\theta.$$

The function $f$ takes values in a real normed space; this is the form that harmonic and subharmonic functions need. The link with the circle integral is `Real.circleAverage_eq_circleIntegral`: for $R \ne 0$, the average is $\frac{1}{2\pi i} \oint (z - c)^{-1} f(z) \, dz$. The average is monotone, `Real.circleAverage_mono`, it is at most a bound of $f$ on the circle, `Real.circleAverage_mono_on_of_le_circle`, and it does not depend on the sign of $R$, `Real.circleAverage_neg_radius`.

The file `Mathlib.Analysis.SpecialFunctions.Integrals.PosLog` computes one circle average that the theory of value distribution needs. For $a \in \mathbb{C}$, `circleAverage_log_norm_sub_const_eq_posLog` gives
$$\frac{1}{2\pi} \int_0^{2\pi} \log |e^{i\theta} - a| \, d\theta = \log^+ |a|,$$
where $\log^+ t = \max(\log t, 0)$. The average is $0$ for $|a| \le 1$ and $\log |a|$ for $|a| > 1$. The form for a circle of center $c$ and radius $R \ne 0$ is `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`.

The file `Mathlib.MeasureTheory.Integral.CircleTransform` names the integrand of the Cauchy formula as a function of $\theta$, `Complex.circleTransform R z w f`. Its integral over $[0, 2\pi]$ is the Cauchy integral, `Complex.integral_circleTransform`. The derivative in $w$ and the bounds that permit differentiation under the integral sign are `Complex.circleTransformDeriv` and `Complex.circleTransformDeriv_bound`.

#### The torus integral

The file `Mathlib.MeasureTheory.Integral.TorusIntegral` treats functions of $n$ complex variables. The map `torusMap c R` sends $\theta \in \mathbb{R}^n$ to the point with coordinates $c_i + R_i e^{i\theta_i}$. The torus integral `torusIntegral f c R`, with notation `∯ x in T(c, R), f x`, is the integral over the box $[0, 2\pi]^n$ of $f$ composed with this map, multiplied by $\prod_i i R_i e^{i\theta_i}$. By Fubini, it is an iterated circle integral: `torusIntegral_succAbove` takes out the coordinate $i$ and gives a circle integral of a torus integral in $n$ variables. In dimension $1$ the torus integral is the circle integral, `torusIntegral_dim1`.

#### Curve integrals and the lemma of Poincaré

The file `Mathlib.MeasureTheory.Integral.CurveIntegral.Basic` integrates a 1-form along a path. A 1-form on a normed space $E$ with values in $F$ is a function $\omega : E \to (E \to_L F)$. For a path $\gamma$ from $a$ to $b$, `curveIntegral ω γ`, with notation `∫ᶜ x in γ, ω x`, is

$$\int_\gamma \omega = \int_0^1 \omega(\gamma(t))(\gamma'(t)) \, dt,$$

which is `curveIntegral_eq_intervalIntegral_deriv`. The path is a continuous map from $[0, 1]$; its derivative is the derivative of its extension to $\mathbb{R}$, and the integral is $0$ when the integrand is not integrable. The integral along the concatenation of two paths is the sum, `curveIntegral_trans`, and the integral along the reversed path is the negative, `curveIntegral_symm`. On a segment the integral is $\int_0^1 \omega(a + t(b - a))(b - a) \, dt$, `curveIntegral_segment`. If $\omega$ is continuous, then the function $x \mapsto \int_{[a, x]} \omega$ has derivative $\omega(a)$ at $a$, `HasFDerivAt.curveIntegral_segment_source`.

The file `Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare` proves the lemma of Poincaré for 1-forms. A form is closed if its derivative is symmetric: $d\omega(x)(u)(v) = d\omega(x)(v)(u)$. On a convex open set, a differentiable closed form has a primitive, `Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`: there is $f$ with $f'(x) = \omega(x)$ on the set. The primitive is the integral of $\omega$ along the segments from a fixed point. The same file proves homotopy invariance: for a $C^2$ homotopy between two paths in a set where $\omega$ is closed, the integrals along the four sides of the square add to $0$, `ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`.

#### The divergence theorem

The file `Mathlib.MeasureTheory.Integral.DivergenceTheorem` proves the divergence theorem on a box $[a, b] \subseteq \mathbb{R}^{n+1}$. Let $f$ be continuous on the box, differentiable in the interior off a countable set, with an integrable divergence. Then `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` gives

$$\int_{[a, b]} \sum_i \frac{\partial f_i}{\partial x_i} = \sum_i \left( \int_{F_i^+} f_i - \int_{F_i^-} f_i \right),$$

where $F_i^+$ and $F_i^-$ are the two faces of the box normal to the coordinate $i$. The countable exceptional set is important in complex analysis, where it permits a function that is not differentiable at a countable set of points. The proof uses the Henstock-Kurzweil integral on boxes of Chapter 11, which has a divergence theorem with weak assumptions.

The special cases are often more convenient. In dimension $1$, `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le` is the fundamental theorem of calculus with a countable exceptional set. In dimension $2$, `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt` states the theorem for two functions $f, g$ on a rectangle with iterated interval integrals, the form of the theorem of Green.

#### Common errors

1. Reading the circle integral as a real line integral. The value $\oint f(z) \, dz$ includes the factor $(\text{circleMap } c\, R)'(\theta) = i R e^{i\theta}$. To integrate $f$ against the arc length, use `Real.circleAverage` and multiply by $2\pi |R|$.
2. Forgetting that a 1-form is a function to continuous linear maps. The argument of `curveIntegral` is $\omega : E \to (E \to_L F)$, not a vector field $E \to E$. For a vector field $v$ on an inner product space, the form is $x \mapsto \langle v(x), \cdot \rangle$.
3. Applying the Poincaré lemma on a set that is not convex. On the punctured plane, the form $dz/z$ is closed but has no primitive; its circle integral is $2\pi i$.

### Exercises

1. (A) Use `circleIntegral.integral_sub_zpow_of_ne` and `circleIntegral.integral_sub_center_inv` to compute $\oint_{C(0, 1)} (z^{-2} + 3 z^{-1} + z^2) \, dz$.
2. (A) Compute `Real.circleAverage` of $f(z) = |z|^2$ on the circle $C(0, R)$.
3. (B) Prove the bound $\|\oint_{C(c, R)} f\| \le 2 \pi R C$ of `circleIntegral.norm_integral_le_of_norm_le_const` from the definition and the bound for interval integrals.
4. (B) Compute the curve integral of the form $\omega(x, y)(u, v) = x v - y u$ along the closed path that goes once around the unit square, and compare with `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`.
5. (B) Show that the torus integral of $z_1^{-1} z_2^{-1}$ on $T(0, (1, 1))$ is $(2\pi i)^2$, with `torusIntegral_succAbove`.
6. (C) Explain why `hasFPowerSeriesOn_cauchy_integral` needs no hypothesis of holomorphy, and what the coefficients of the series are for $f(z) = \bar{z}$ on $C(0, 1)$.

### Reference

<?reference?>
