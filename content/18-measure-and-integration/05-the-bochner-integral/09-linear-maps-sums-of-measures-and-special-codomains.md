---
title: Linear maps, sums of measures and special codomains
kind: api
modules:
  - Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
  - Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
  - Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
  - Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap
  - Mathlib.MeasureTheory.SpecificCodomains.ContinuousMapZero
  - Mathlib.MeasureTheory.SpecificCodomains.Pi
  - Mathlib.MeasureTheory.SpecificCodomains.WithLp
explains:
  E2: [ContinuousLinearMap.integral_comp_comm, ContinuousLinearEquiv.integral_comp_comm, integral_withDensity_eq_integral_smul, integral_re_add_im, ContinuousMap.integral_apply, MeasureTheory.integral_sum_measure, MeasureTheory.integral_countable, MeasureTheory.integral_sum_dirac_eq_tsum, MeasureTheory.exists_lt_lowerSemicontinuous_integral_lt, MeasureTheory.eval_integral]
  E1: auto
families: []
requires: [V13, V16, V18.C02, V18.C03, V18.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Linear maps, sums of measures and special codomains

### Overview

A continuous linear map commutes with the Bochner integral: $\int L(f) \, d\mu = L\left(\int f \, d\mu\right)$. This one rule has many uses. With the coordinate maps it says that the integral of a vector valued function is computed coordinate by coordinate. With the real and imaginary parts it splits a complex integral into two real integrals. With the evaluation at a point it says that the integral of a function with values in continuous functions is computed pointwise. This section explains the rule and its special cases, and it collects the integration rules for sums of measures, for counting and Dirac measures, and for densities. It ends with the theorem of Vitali and Carathéodory, which approximates an integrable function from above by a lower semicontinuous function and from below by an upper semicontinuous function.

The integral and its basic properties are in Section 2. The files of this section are short, and their statements are often used without notice through the simplifier.

### The library around it

#### Continuous linear maps

The file `Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap` proves the main rule. For a continuous linear map $L : E \to F$ over `ℝ` or `ℂ` and an integrable $\varphi$, `ContinuousLinearMap.integral_comp_comm` gives

$$\int_X L(\varphi(x)) \, d\mu(x) = L\left(\int_X \varphi \, d\mu\right).$$

The proof is the uniqueness of continuous extensions: both sides are continuous linear functions of $\varphi$ in $L^1$, and they agree on indicators. For a continuous linear equivalence, `ContinuousLinearEquiv.integral_comp_comm` holds without the integrability hypothesis, because $L \circ \varphi$ is integrable exactly when $\varphi$ is; both sides are $0$ otherwise. Linear isometries have `LinearIsometry.integral_comp_comm`. A semilinear version is `ContinuousLinearMap.integral_comp_commSL`.

The rule has many named special cases. For a function with values in continuous linear maps, `ContinuousLinearMap.integral_apply` gives $(\int \varphi)(v) = \int \varphi(x)(v)$, and `ContinuousMultilinearMap.integral_apply` does the same for multilinear maps. For products, `fst_integral` and `snd_integral` take the components, and `integral_pair` gives $\int (f, g) = (\int f, \int g)$. For scalars, `integral_smul_const` gives $\int f(x) \cdot c = (\int f) \cdot c$, and `integral_mul_const_of_integrable` is the version for a normed ring.

#### Real and complex parts

For a function $f$ with values in a field `𝕜` with the class `RCLike`, such as `ℝ` or `ℂ`, the real and imaginary parts commute with the integral: `integral_re` and `integral_im`. The combined statement is `integral_re_add_im`:

$$\int \operatorname{Re} f + i \int \operatorname{Im} f = \int f.$$

The conjugate commutes with the integral, `integral_conj`, and the inclusion of the reals commutes too, `integral_ofReal` and `integral_complex_ofReal`. These rules reduce most statements about complex integrals to real ones.

#### Densities

The integral for a measure with a density $f \ge 0$ is the integral of $f$ times the function. For a measurable $f$ with values in `NNReal`, `integral_withDensity_eq_integral_smul` gives

$$\int g \, d(f \mu) = \int f(x) \, g(x) \, d\mu(x).$$

The versions with values in `ENNReal` are `integral_withDensity_eq_integral_toReal_smul` and its forms with almost everywhere measurability. The set versions are `setIntegral_withDensity_eq_setIntegral_smul` and its variants. The density measure itself is in Chapter 4.

#### Sums of measures

The file `Mathlib.MeasureTheory.Integral.Bochner.SumMeasure` integrates against a countable sum of measures. For $f$ integrable for $\sum_i \mu_i$, `MeasureTheory.integral_sum_measure` gives $\int f \, d\left(\sum_i \mu_i\right) = \sum_i \int f \, d\mu_i$, and `MeasureTheory.hasSum_integral_measure` states the convergence of the series. Integrability for the sum is `MeasureTheory.integrable_sum_measure_iff`.

On a countable space with measurable singletons, every measure is a sum of point masses, and `MeasureTheory.integral_countable` gives

$$\int f \, d\mu = \sum_x \mu(\{x\}) \, f(x).$$

The finite version is `MeasureTheory.integral_fintype`, and for the counting measure `MeasureTheory.integral_count` gives the finite sum $\sum_a f(a)$. For a measure $\sum_i c_i \delta_{x_i}$ with finite weights, `MeasureTheory.integral_sum_dirac_eq_tsum` gives $\sum_i c_i f(x_i)$ when the series of norms converges.

#### The theorem of Vitali and Carathéodory

The file `Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory` approximates integrable functions by semicontinuous functions. Let $\mu$ be weakly regular and σ-finite on a topological space. For a real integrable $f$ and $\varepsilon > 0$, `MeasureTheory.exists_lt_lowerSemicontinuous_integral_lt` gives a lower semicontinuous $g$ with values in `EReal`, with $f < g$ everywhere, $g < \infty$ almost everywhere, $g$ integrable and

$$\int g \, d\mu < \int f \, d\mu + \varepsilon.$$

The symmetric statement is `MeasureTheory.exists_upperSemicontinuous_lt_integral_gt`. The proof starts with simple functions. For the indicator of a set $s$, outer regularity gives an open $U \supseteq s$ of slightly larger measure, and the indicator of $U$ is lower semicontinuous. A nonnegative function is a series of such indicators with small total error. The versions for the lower Lebesgue integral are `MeasureTheory.exists_le_lowerSemicontinuous_lintegral_ge` and `MeasureTheory.exists_upperSemicontinuous_le_lintegral_le`. The theorem is a step in the proof of the fundamental theorem of calculus for integrable derivatives in Chapter 8.

#### Special codomains

The files in the folder SpecificCodomains treat four kinds of target spaces. For a finite product of spaces $E_i$, `MeasureTheory.integrable_pi_iff` says that $f$ is integrable when each coordinate is, and `MeasureTheory.eval_integral` says that the integral is computed coordinatewise. The same is true for `MeasureTheory.MemLp`, `MeasureTheory.memLp_pi_iff`, and for binary products, `MeasureTheory.memLp_prod_iff`. The type `PiLp q E` has the same elements with the $\ell^q$ norm, and its file gives the same results, `MeasureTheory.integrable_piLp_iff` and `MeasureTheory.eval_integral_piLp`, together with the versions for `WithLp q (E × F)`.

For functions with values in the continuous maps `C(Y, E)` on a compact space $Y$, `ContinuousMap.integral_apply` gives $(\int f)(y) = \int f(x)(y)$, from the evaluation at $y$. The other lemmas of these files build integrable functions with values in `C(Y, E)` from functions of two variables. A function $f : X \to Y \to E$ that is jointly continuous gives a strongly measurable function to `C(Y, E)`, `ContinuousMap.aeStronglyMeasurable_mkD_of_uncurry`. A bound by an integrable function gives finite integral, `ContinuousMap.hasFiniteIntegral_mkD_of_bound`. The construction uses `ContinuousMap.mkD`, which takes a default value for the points $x$ where $f(x)$ is not continuous. The files for `ContinuousMapZero` repeat this for continuous maps that vanish at a point.

#### Common errors

1. Applying `ContinuousLinearMap.integral_comp_comm` to a function that is not integrable. For a linear map that is not injective, $L \circ \varphi$ can be integrable while $\varphi$ is not; the left side is then a real integral and the right side is $L(0) = 0$. Use the version for equivalences when it applies.
2. Using `MeasureTheory.integral_countable` without the class `MeasurableSingletonClass`. Without measurable singletons, the values $\mu(\{x\})$ need not determine the measure.
3. Reading the result of `MeasureTheory.exists_lt_lowerSemicontinuous_integral_lt` as a real function. The function $g$ has values in `EReal` and can be $+\infty$ on a null set. Its integral is the integral of the real function `(g x).toReal`.

### Exercises

1. (A) Use `integral_re_add_im` to compute $\int_0^1 e^{ix} \, dx$ from the integrals of $\cos$ and $\sin$.
2. (A) Compute $\int f \, d\mu$ for $\mu = \delta_0 + 2\delta_1 + 3\delta_2$ on $\mathbb{R}$ and $f(x) = x^2$, with `MeasureTheory.integral_fintype` or with the rules for sums of measures.
3. (B) Show that the integral of a function $f : X \to \mathbb{R}^n$ is the vector of the integrals of its coordinates, with `MeasureTheory.eval_integral`.
4. (B) Give a continuous linear map $L$ and a function $\varphi$ that is not integrable, with $L \circ \varphi$ integrable and $\int L \circ \varphi \ne 0$.
5. (B) Let $\mu = \sum_{n \ge 1} 2^{-n} \delta_{1/n}$ on $\mathbb{R}$. Compute $\int x \, d\mu$ with `MeasureTheory.integral_sum_dirac_eq_tsum`.
6. (C) Prove `MeasureTheory.exists_lt_lowerSemicontinuous_integral_lt` for the indicator of a measurable set of finite measure in $\mathbb{R}$.

### Reference

<?reference?>
