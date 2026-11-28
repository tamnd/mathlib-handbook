---
title: Averages, the layer cake formula and peak functions
kind: api
modules:
  - Mathlib.MeasureTheory.Integral.Average
  - Mathlib.MeasureTheory.Integral.MeanValue
  - Mathlib.MeasureTheory.Integral.Layercake
  - Mathlib.MeasureTheory.Integral.PeakFunction
  - Mathlib.MeasureTheory.Integral.Asymptotics
  - Mathlib.MeasureTheory.Integral.Lebesgue.Norm
  - Mathlib.MeasureTheory.Integral.LebesgueNormedSpace
  - Mathlib.MeasureTheory.Integral.Indicator
explains:
  E2: [MeasureTheory.average, MeasureTheory.setAverage_eq, MeasureTheory.laverage_eq, MeasureTheory.exists_notMem_null_le_integral, MeasureTheory.average_union, MeasureTheory.exists_eq_setAverage, exists_eq_const_mul_setIntegral_of_nonneg, MeasureTheory.lintegral_eq_lintegral_meas_le, MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul, tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn]
  E1: auto
families: []
requires: [V13, V15, V16, V18.C02, V18.C03, V18.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Averages, the layer cake formula and peak functions

### Overview

This section collects tools that turn integrals into estimates. The average of a function over a set is its integral divided by the measure of the set. Averages behave like convex combinations, and a real function is at most its average on a set of positive measure. The mean value theorem for integrals says that a continuous function on a connected set takes its average value at some point. The layer cake formula writes the integral of a nonnegative function as an integral of the measures of its superlevel sets:

$$\int_\alpha f \, d\mu = \int_0^\infty \mu(\{f \ge t\}) \, dt.$$

Peak functions are families $\varphi_i$ that concentrate near a point $x_0$; their integrals against $g$ tend to $g(x_0)$. Finally, the section has small files on integrability from asymptotic bounds, on the Lebesgue integral of a norm, and on limits of measures of sets from limits of indicators. The integrals are the lower Lebesgue integral of Chapter 4 and the Bochner integral of Section 2.

### The library around it

#### Averages

The file `Mathlib.MeasureTheory.Integral.Average` defines `MeasureTheory.average μ f` for $f$ with values in a real normed space. The notation is the integral notation with a barred integral sign in place of `∫`, and the form with `x in s` is the average over $s$. This text writes $\operatorname{avg}_\mu f$ and $\operatorname{avg}_s f$. By `MeasureTheory.average_eq`,

$$\operatorname{avg}_\mu f = \frac{1}{\mu(\alpha)} \int f \, d\mu,$$

and `MeasureTheory.setAverage_eq` is the same with $s$ in place of $\alpha$. The definition is the integral for the normalized measure $\mu(\alpha)^{-1} \mu$, so the average of a function over a set of infinite measure is $0$, and so is the average for the zero measure, `MeasureTheory.average_zero_measure`. For a probability measure the average is the integral, `MeasureTheory.average_eq_integral`. The version for functions with values in `ENNReal` is `MeasureTheory.laverage`, with the barred integral sign and a superscript minus as notation, and `MeasureTheory.laverage_eq` gives the integral divided by $\mu(\alpha)$.

The rules are those of an integral: additivity, `MeasureTheory.average_add`, constants, `MeasureTheory.average_const`, and congruence almost everywhere, `MeasureTheory.average_congr`. The average over a union of two almost disjoint sets of finite measure is a convex combination of the two averages, `MeasureTheory.average_union`, with weights $\mu(s)/(\mu(s) + \mu(t))$ and $\mu(t)/(\mu(s) + \mu(t))$. When both sets have positive measure, the average over $\alpha$ lies in the open segment between the averages over $s$ and over $s^c$, `MeasureTheory.average_mem_openSegment_compl_self`. This is the form needed for the strict Jensen inequality. The integral of $f$ minus its average is $0$, `MeasureTheory.integral_sub_average`.

The key estimates say that a function is at most its average on a set of positive measure. For a real integrable $f$ on a set of positive finite measure, `MeasureTheory.measure_le_setAverage_pos` gives $\mu(\{x \in s : f(x) \le \operatorname{avg}_s f\}) > 0$. As a consequence, for a probability measure and a null set $N$, `MeasureTheory.exists_notMem_null_le_integral` gives a point $x \notin N$ with $f(x) \le \int f \, d\mu$. The inequality in the other direction has names with the order of the two sides exchanged, such as `MeasureTheory.exists_notMem_null_integral_le`. Such statements are the measure theoretic form of the fact that a minimum is at most a mean. They are used in probabilistic arguments, where a random choice is shown to be good on average.

#### The mean value theorem for integrals

The file `Mathlib.MeasureTheory.Integral.MeanValue` combines these estimates with the intermediate value theorem. For a real function $f$ continuous on a connected set $s$ of positive finite measure, `MeasureTheory.exists_eq_setAverage` gives $c \in s$ with $f(c) = \operatorname{avg}_s f$. The weighted form is `exists_eq_const_mul_setIntegral_of_nonneg`: for a nonnegative weight $g$ on $s$,

$$\int_s f g \, d\mu = f(c) \int_s g \, d\mu$$

for some $c \in s$. The version with $0 \le g$ only almost everywhere is `exists_eq_const_mul_setIntegral_of_ae_nonneg`.

#### The layer cake formula

The file `Mathlib.MeasureTheory.Integral.Layercake` proves the layer cake formula for a nonnegative almost everywhere measurable $f$. The plain form is `MeasureTheory.lintegral_eq_lintegral_meas_le`, with the lower Lebesgue integral on both sides. The general form `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul` adds a weight: for $G(x) = \int_0^x g$ with $g \ge 0$,

$$\int_\alpha G(f(\omega)) \, d\mu(\omega) = \int_0^\infty \mu(\{f \ge t\}) \, g(t) \, dt.$$

With $g(t) = p t^{p-1}$ this gives $\int f^p \, d\mu = \int_0^\infty p t^{p-1} \mu(\{f \ge t\}) \, dt$, the usual formula for the $L^p$ norm by the distribution function. The proof is the theorem of Tonelli of Chapter 6 for the region $\{(\omega, t) : 0 < t \le f(\omega)\}$. The statements with strict inequality, `MeasureTheory.lintegral_eq_lintegral_meas_lt`, follow because $\mu(\{f \ge t\})$ and $\mu(\{f > t\})$ differ only for countably many $t$, `MeasureTheory.countable_meas_le_ne_meas_lt`. For an integrable $f$, `MeasureTheory.Integrable.integral_eq_integral_meas_lt` gives the Bochner form. The integral $\int_0^x g$ is the interval integral of Chapter 8.

#### Peak functions

The file `Mathlib.MeasureTheory.Integral.PeakFunction` is about a family $\varphi_i \ge 0$ on a set $s$ with integral tending to $1$ near $x_0$ and tending uniformly to $0$ outside each neighbourhood of $x_0$. Then $\int_s \varphi_i g \, d\mu \to g(x_0)$ for each $g$ that is integrable and continuous at $x_0$, `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto`. The version on the whole space is `tendsto_integral_peak_smul_of_integrable_of_tendsto`.

The main example uses powers. Let $c$ be continuous and nonnegative on a compact set $s$, with a unique maximum at $x_0$ and $c(x_0) > 0$. Then the normalized powers $c^n / \int_s c^n$ are peak functions, and `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn` gives

$$\frac{\int_s c(x)^n g(x) \, d\mu(x)}{\int_s c(x)^n \, d\mu(x)} \to g(x_0).$$

The measure must be positive on open sets and $x_0$ must be in the closure of the interior of $s$. A second family comes from scaling: for $\varphi \ge 0$ on a finite dimensional space with $\int \varphi = 1$ and $\|x\|^n \varphi(x) \to 0$ at infinity, the functions $c^n \varphi(cx)$ form an approximate identity, `tendsto_integral_comp_smul_smul_of_integrable`.

#### Integrability from asymptotics and small files

The file `Mathlib.MeasureTheory.Integral.Asymptotics` deduces integrability from a bound $f = O(g)$. On the whole space, `Asymptotics.IsBigO.integrable` needs the bound everywhere. Near infinity on a linear order, `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atTop` asks for a locally integrable $f$ and $f = O(g)$ at the top with $g$ integrable there. The versions for both ends and for the cocompact filter are `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atBot_atTop` and `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_cocompact`. Local integrability is in Section 5.

The file `Mathlib.MeasureTheory.Integral.Lebesgue.Norm` relates the extended norm of a real function to its positive part: `MeasureTheory.lintegral_eNorm_of_nonneg` gives $\int \|f\|_e = \int \operatorname{ofReal}(f)$ for $f \ge 0$. The file `Mathlib.MeasureTheory.Integral.LebesgueNormedSpace` has `aemeasurable_withDensity_iff`, which moves a density into the function. The file `Mathlib.MeasureTheory.Integral.Indicator` has `MeasureTheory.tendsto_measure_of_tendsto_indicator`: if the indicators of $A_i$ converge pointwise to the indicator of $A$ and all $A_i$ lie in a set of finite measure, then $\mu(A_i) \to \mu(A)$. It is the dominated convergence theorem for indicators.

#### Common errors

1. Averaging over a set of infinite measure. The average is then $0$, by the convention for the inverse of $\infty$ in `ENNReal` and for the integral. Lemmas such as `MeasureTheory.exists_eq_setAverage` have $\mu(s) \ne \infty$ as a hypothesis.
2. Using the layer cake formula with a function that takes negative values. `MeasureTheory.lintegral_eq_lintegral_meas_le` needs $0 \le f$ almost everywhere; for a real function, apply it to the positive and the negative parts.
3. Forgetting the positivity of the measure on open sets in `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`. For a measure concentrated away from $x_0$, the powers $c^n$ do not concentrate at $x_0$.

### Exercises

1. (A) Compute the average of $x^2$ over $[0, 2]$ for Lebesgue measure and find the point $c$ of `MeasureTheory.exists_eq_setAverage`.
2. (A) Show with `MeasureTheory.average_union` that the average of $f$ over $[0, 2]$ is the mean of its averages over $[0, 1]$ and $[1, 2]$.
3. (B) Use `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul` to prove $\int f^2 \, d\mu = \int_0^\infty 2t \, \mu(\{f \ge t\}) \, dt$ for $f \ge 0$.
4. (B) Let $X_1, \dots, X_n$ be vectors of norm $1$ in an inner product space. Use `MeasureTheory.exists_notMem_null_le_integral` on random signs to find signs $\varepsilon_i$ with $\|\sum \varepsilon_i X_i\|^2 \le n$.
5. (B) Use `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn` with $c(x) = 1 - x^2$ on $[-1, 1]$ to compute the limit of $\int_{-1}^1 (1 - x^2)^n \cos x \, dx / \int_{-1}^1 (1 - x^2)^n \, dx$.
6. (C) Prove the layer cake formula `MeasureTheory.lintegral_eq_lintegral_meas_le` from the theorem of Tonelli.

### Reference

<?reference?>
