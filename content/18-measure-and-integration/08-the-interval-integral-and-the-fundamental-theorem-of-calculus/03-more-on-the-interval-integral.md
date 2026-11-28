---
title: More on the interval integral
kind: api
modules:
  - Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
  - Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
  - Mathlib.MeasureTheory.Function.AbsolutelyContinuous
  - Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
  - Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
  - Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
  - Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
  - Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
  - Mathlib.MeasureTheory.Integral.IntervalIntegral.Slope
  - Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
  - Mathlib.MeasureTheory.Integral.IntervalAverage
  - Mathlib.MeasureTheory.Integral.ExpDecay
  - Mathlib.MeasureTheory.Integral.Gamma
explains:
  E2: [AbsolutelyContinuousOnInterval.integral_deriv_eq_sub, AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero, intervalIntegral.integral_deriv_of_contDiffOn_Icc, MonotoneOn.intervalIntegral_deriv_mem_uIcc, norm_sub_le_integral_of_norm_deriv_le_of_le, exists_eq_const_mul_intervalIntegral_of_nonneg, Function.Periodic.intervalIntegral_add_eq, trapezoidal_error_le_of_c2, integrable_of_isBigO_exp_neg, integral_rpow_mul_exp_neg_rpow]
  E1: auto
families: []
requires: [V15, V16, V18.C03, V18.C04, V18.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## More on the interval integral

### Overview

Section 1 proved the fundamental theorem of calculus for the interval integral $\int_a^b f$. This section collects the results around it that a user of real analysis needs. The first group extends the fundamental theorem: to absolutely continuous functions, to functions of class $C^1$ on a closed interval, and to monotone functions, where only an inequality holds. A related group bounds $\|f(b) - f(a)\|$ by the integral of a bound on the derivative. The second group has the mean value theorems for integrals, the integrals of periodic functions, the trapezoidal rule with its error bound, and averages over an interval. The last group has two families of improper integrals: integrability of functions with exponential decay, and integrals of the form $\int_0^\infty x^q e^{-x^p} \, dx$, which give the Gamma function.

The interval integral is the Bochner integral of Chapter 5 on the interval $(a, b]$, with a sign when $b < a$. The derivatives come from Volume 15.

### The library around it

#### A general form of the first fundamental theorem

The file `Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus` states the first fundamental theorem on a general space. Let $\mu$ be locally finite on a topological space, let $f$ be continuous at $x$, and let $s_i$ be sets that shrink to $x$. Then

$$\int_{s_i} f \, d\mu = \mu(s_i) f(x) + o(\mu(s_i)),$$

which is `ContinuousAt.integral_sub_linear_isLittleO_ae`. Versions with continuity within a set and with a limit of $f$ are `ContinuousWithinAt.integral_sub_linear_isLittleO_ae` and `Filter.Tendsto.integral_sub_linear_isLittleO_ae`. On the real line with $s_i = [x, x + h_i]$, this is the statement that $\frac{d}{dh} \int_x^{x+h} f = f(x)$.

#### Extensions of the second fundamental theorem

For a function $f$ of class $C^1$ on $[a, b]$, `intervalIntegral.integral_deriv_of_contDiffOn_Icc` gives $\int_a^b f' = f(b) - f(a)$. The derivative at the end points is the derivative of $f$, which need not exist, but the integral does not see two points. The version with the derivative within the interval is `intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc`. The bound $\|f(b) - f(a)\|_e \le \int_{[a, b]} \|f'\|_e$ for the lower Lebesgue integral is `eNorm_sub_le_lintegral_deriv_of_contDiffOn_Icc`.

The predicate `AbsolutelyContinuousOnInterval f a b` says that $f$ is absolutely continuous on the interval between $a$ and $b$. For such a real $f$, `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` gives

$$\int_a^b f'(x) \, dx = f(b) - f(a),$$

where $f'$ is `deriv f`, defined almost everywhere. This is the most general form of the second fundamental theorem for real functions. If the derivative is $0$ almost everywhere, the function is constant, `AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`. The rule for integration by parts with absolutely continuous functions is `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`.

The predicate itself is in `Mathlib.MeasureTheory.Function.AbsolutelyContinuous`. The lemma `absolutelyContinuousOnInterval_iff` gives the usual form: for every $\varepsilon > 0$ there is a $\delta > 0$ such that $\sum_i \operatorname{dist}(f(b_i), f(a_i)) < \varepsilon$ for every finite family of disjoint intervals $(a_i, b_i]$ in $[a, b]$ with total length less than $\delta$. The definition uses a filter on such families, `AbsolutelyContinuousOnInterval.totalLengthFilter`. An absolutely continuous function is uniformly continuous, `AbsolutelyContinuousOnInterval.uniformContinuousOn`, and has bounded variation, `AbsolutelyContinuousOnInterval.boundedVariationOn`. A real one is therefore differentiable almost everywhere, `AbsolutelyContinuousOnInterval.ae_differentiableAt`. Lipschitz functions and $C^1$ functions are absolutely continuous, by `LipschitzOnWith.absolutelyContinuousOnInterval` and `ContDiffOn.absolutelyContinuousOnInterval`. So is an indefinite integral, by `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`. Sums, scalar multiples and products stay absolutely continuous: `AbsolutelyContinuousOnInterval.add`, `AbsolutelyContinuousOnInterval.smul` and `AbsolutelyContinuousOnInterval.mul`.

Monotone functions are differentiable almost everywhere, and their derivative is integrable, `MonotoneOn.intervalIntegrable_deriv`. The fundamental theorem fails for them: the Cantor function has derivative $0$ almost everywhere. What remains is an inequality, `MonotoneOn.intervalIntegral_deriv_mem_uIcc`: the integral of $f'$ lies between $0$ and $f(b) - f(a)$. The same integrability holds for functions of bounded variation, `BoundedVariationOn.intervalIntegrable_deriv`, since they are differences of monotone functions. The file `Mathlib.MeasureTheory.Integral.IntervalIntegral.Slope` has the tool for the proof: for monotone $f$, the integral of the slope $(f(x + c) - f(x))/c$ over $[a, b]$ is at most $f(b + c) - f(a)$, `MonotoneOn.intervalIntegral_slope_le`. Fatou's lemma, applied as $c \to 0$, then bounds the integral of $f'$.

#### Bounds by the derivative

The file `Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral` bounds an increment by an integral. If $f$ is continuous on $[a, b]$, differentiable on $(a, b)$, and $\|f'(t)\| \le B(t)$ almost everywhere for an integrable $B$, then `norm_sub_le_integral_of_norm_deriv_le_of_le` gives

$$\|f(b) - f(a)\| \le \int_a^b B(t) \, dt.$$

This is the mean value inequality with a variable bound. In a normed space, `norm_sub_le_mul_volume_of_norm_fderiv_le` gives a sharper form of the usual bound $\|f(b) - f(a)\| \le C \|b - a\|$: the factor $\|b - a\|$ is multiplied by the measure of the set of $t \in (0, 1)$ where the derivative at $a + t(b - a)$ is not $0$.

#### Mean value theorems for integrals

The file `Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue` has the first mean value theorem for integrals. For a continuous $f$ and a nonnegative weight $g$, `exists_eq_const_mul_intervalIntegral_of_nonneg` gives $c$ in the interval with $\int_a^b f g = f(c) \int_a^b g$. The second mean value theorem, in the form of Bonnet, is `exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn`: for $f \ge 0$ decreasing, $\|\int_a^b f g\| \le f(a) \|\int_a^\xi g\|$ for some $\xi \in [a, b]$. The file `Mathlib.MeasureTheory.Integral.IntervalAverage` defines the average of $f$ over the interval as $(b - a)^{-1} \int_a^b f$, `interval_average_eq`. It is symmetric in $a$ and $b$, `interval_average_symm`, and a continuous function takes its average value at an interior point, `exists_eq_interval_average`.

#### Periodic functions

The file `Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic` is about functions with $f(x + T) = f(x)$. The integral over a period does not depend on the start point, `Function.Periodic.intervalIntegral_add_eq`:

$$\int_t^{t+T} f = \int_s^{s+T} f.$$

A periodic function that is integrable on one period is integrable on every bounded interval, `Function.Periodic.intervalIntegrable`. If the integral over a period is positive, then $\int_0^t f \to \infty$ as $t \to \infty$, `Function.Periodic.tendsto_atTop_intervalIntegral_of_pos`. The file also links the real line to the circle `AddCircle T`. The interval $(t, t + T]$ is a fundamental domain for the action of $T\mathbb{Z}$, `isAddFundamentalDomain_Ioc`, the projection is measure preserving on it, `AddCircle.measurePreserving_mk`, and the integral over the circle is the integral over one period, `AddCircle.intervalIntegral_preimage`.

#### The trapezoidal rule

The file `Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule` defines the approximation `trapezoidal_integral f N a b` with $N$ equal steps of length $h = (b - a)/N$:

$$T_N(f) = h \sum_{k=0}^{N-1} \frac{f(a + kh) + f(a + (k+1)h)}{2}.$$

The error `trapezoidal_error f N a b` is $T_N(f) - \int_a^b f$. For a function of class $C^2$ with $|f''| \le \zeta$, `trapezoidal_error_le_of_c2` gives

$$|T_N(f) - \textstyle\int_a^b f| \le \frac{|b - a|^3 \zeta}{12 N^2}.$$

The version `trapezoidal_error_le` asks only for two derivatives within the interval. The proof computes the error on one step by integration by parts twice and sums the bounds, `sum_trapezoidal_error_adjacent_intervals`.

#### Exponential decay and the Gamma integrals

The file `Mathlib.MeasureTheory.Integral.ExpDecay` proves integrability on half lines. The function $e^{-bx}$ is integrable on $(a, \infty)$ for $b > 0$, `exp_neg_integrableOn_Ioi`. A continuous function that is $O(e^{-bx})$ at infinity is integrable on $(a, \infty)$, `integrable_of_isBigO_exp_neg`.

The file `Mathlib.MeasureTheory.Integral.Gamma` computes integrals with the Gamma function `Real.Gamma`. For $p > 0$ and $q > -1$, `integral_rpow_mul_exp_neg_rpow` gives

$$\int_0^\infty x^q e^{-x^p} \, dx = \frac{1}{p} \, \Gamma\!\left(\frac{q + 1}{p}\right).$$

The proof substitutes $y = x^p$. With $q = 0$ this is `integral_exp_neg_rpow`, the value $\Gamma(1/p + 1)$. The versions with a factor $b$ in the exponent and the complex versions are `integral_rpow_mul_exp_neg_mul_rpow` and `Complex.integral_rpow_mul_exp_neg_rpow`. These integrals give the volume of the unit ball of $\ell^p$.

#### Common errors

1. Applying the fundamental theorem to a monotone function. The equality $\int_a^b f' = f(b) - f(a)$ needs absolute continuity; for a monotone function, `MonotoneOn.intervalIntegral_deriv_mem_uIcc` gives only an inequality.
2. Using `deriv f` at the end points of the interval. The function `deriv f` is $0$ where $f$ is not differentiable, and on a closed interval the derivative at the end points can be different from the one sided derivative. The integral does not depend on these two values, but pointwise statements do.
3. Forgetting the factor $|b - a|^3$ in the trapezoidal bound. The bound in `trapezoidal_error_le_of_c2` is for the whole interval, not for one step; the error on one step is of order $h^3$, and the total is of order $h^2$.

### Exercises

1. (A) Compute `trapezoidal_integral` for $f(x) = x^2$ on $[0, 1]$ with $N = 2$, and check the bound of `trapezoidal_error_le_of_c2`.
2. (A) Use `Function.Periodic.intervalIntegral_add_eq` to show $\int_t^{t + 2\pi} \sin^2 x \, dx = \pi$ for every $t$.
3. (B) Use `integral_rpow_mul_exp_neg_rpow` to compute $\int_0^\infty x^2 e^{-x^2} \, dx$.
4. (B) Show that $f(x) = \sqrt{x}$ is absolutely continuous on $[0, 1]$, and verify `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` for it.
5. (B) For the Cantor function $f$, show that `MonotoneOn.intervalIntegral_deriv_mem_uIcc` holds with the value $0$, and that $f(1) - f(0) = 1$.
6. (C) Prove `norm_sub_le_integral_of_norm_deriv_le_of_le` for continuously differentiable $f$ from the fundamental theorem of Section 1.

### Reference

<?reference?>
