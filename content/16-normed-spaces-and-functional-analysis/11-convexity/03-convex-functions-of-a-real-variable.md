---
title: Convex functions of a real variable, continuity and integrals
kind: api
modules:
  - Mathlib.Analysis.Convex.Deriv
  - Mathlib.Analysis.Convex.SpecificFunctions.Basic
  - Mathlib.Analysis.Convex.SpecificFunctions.Deriv
  - Mathlib.Analysis.Convex.SpecificFunctions.Pow
  - Mathlib.Analysis.Convex.Integral
  - Mathlib.Analysis.Convex.Continuous
  - Mathlib.Analysis.Convex.FunctionTopology
  - Mathlib.Analysis.Convex.Approximation
explains:
  E2: [convexOn_of_deriv2_nonneg, MonotoneOn.convexOn_of_deriv, ConvexOn.monotoneOn_rightDeriv, strictConvexOn_exp, convexOn_rpow, Real.strictConcaveOn_rpow, ConvexOn.map_integral_le, ConvexOn.locallyLipschitzOn_interior, ConvexOn.exists_lipschitzOnWith_of_isBounded, ConvexOn.sSup_affine_eq]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C03, V16.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Convex functions of a real variable, continuity and integrals

### Overview

Section 2 gives the algebra of convex functions and the slope criterion on an ordered field. This section adds analysis. On an interval of $\mathbb{R}$, a differentiable function is convex if and only if its derivative is monotone, and a twice differentiable function is convex if its second derivative is nonnegative. Each convex function on an open interval has one sided derivatives at every point, and they are monotone. These tests prove the convexity of $e^x$, of $x^p$ for $p \ge 1$ on $[0, \infty)$, and the concavity of $\log$, $\sin$ on $[0, \pi]$ and $x^p$ for $0 < p < 1$.

The section then turns to functions on a normed space. A convex function on an open convex set in a finite dimensional space is continuous, and even locally Lipschitz. In any normed space, a convex function that is bounded on a ball is Lipschitz on each smaller ball. The integral form of the Jensen inequality says that $g(\int f \, d\mu) \le \int g \circ f \, d\mu$ for a convex continuous $g$ and a probability measure $\mu$. At the end, a lower semicontinuous convex function on a closed convex set is the supremum of the affine functions below it. That result uses the separation theorems of Chapter 5.

### The library around it

The file `Mathlib.Analysis.Convex.Deriv` works with `f : ℝ → ℝ` on a convex set `D`. The derivative tests are `MonotoneOn.convexOn_of_deriv`, which asks for continuity on `D`, differentiability on the interior, and a monotone `deriv f` on the interior, and `convexOn_of_deriv2_nonneg`, which asks for `0 ≤ deriv^[2] f x` on the interior. The strict and concave forms are `StrictMonoOn.strictConvexOn_of_deriv`, `strictConvexOn_of_deriv2_pos'`, `concaveOn_of_deriv2_nonpos` and `strictConcaveOn_univ_of_deriv2_neg`, and the primed forms state the hypotheses at each point of the interior. The proof of `MonotoneOn.convexOn_of_deriv` uses the slope criterion of Section 2. For $x < y < z$ in `D`, the mean value theorem gives points $a \in (x, y)$ and $b \in (y, z)$ where the derivative equals the two slopes, and $a < b$ with a monotone derivative gives the inequality of slopes. The second derivative test follows, because a function with a nonnegative derivative is monotone. The converse direction is `ConvexOn.monotoneOn_deriv`. The lemmas `ConvexOn.le_slope_of_hasDerivAt` and `ConvexOn.slope_le_deriv` compare the derivative with the slopes of chords, which gives the tangent line inequality.

The same file has the theory of one sided derivatives, written as `derivWithin f (Set.Ioi x) x` for the right derivative and with `Set.Iio x` for the left one. At a point in the interior, `ConvexOn.differentiableWithinAt_Ioi_of_mem_interior` and `ConvexOn.differentiableWithinAt_Iio_of_mem_interior` say that both exist, `ConvexOn.leftDeriv_le_rightDeriv_of_mem_interior` compares them, and `ConvexOn.monotoneOn_rightDeriv` and `ConvexOn.monotoneOn_leftDeriv` say that they are monotone. The proofs use the monotone slopes of Section 2: a monotone function that is bounded on one side has a one sided limit, and `ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior` states the result as a derivative within `Set.Ioi x`. The lemma `ConvexOn.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg` gives the optimality test at a point where the function is not differentiable.

The file `Mathlib.Analysis.Convex.SpecificFunctions.Basic` proves `strictConvexOn_exp`, `convexOn_exp`, `strictConcaveOn_log_Ioi`, `strictConcaveOn_log_Iio`, `convexOn_rpow` for `1 ≤ p` and `strictConvexOn_rpow` for `1 < p`. These proofs use the slope criterion, not derivatives, so they do not depend on the calculus library. Two consequences are the Bernoulli inequality `one_add_mul_self_le_rpow_one_add`, which says that $1 + p s \le (1 + s)^p$ for $s \ge -1$ and $p \ge 1$, and `Real.exp_mul_le_cosh_add_mul_sinh`. The file `Mathlib.Analysis.Convex.SpecificFunctions.Deriv` uses the second derivative test for `strictConvexOn_pow`, `Even.strictConvexOn_pow`, `strictConvexOn_zpow`, `strictConcaveOn_sin_Icc`, `strictConcaveOn_cos_Icc` and `strictConcaveOn_sqrt_mul_log_Ioi`. The file `Mathlib.Analysis.Convex.SpecificFunctions.Pow` proves `Real.strictConcaveOn_rpow` for $0 < p < 1$, `Real.strictConcaveOn_sqrt`, and the forms on `NNReal`, such as `NNReal.strictConcaveOn_rpow`.

The file `Mathlib.Analysis.Convex.Integral` has the integral forms of the convexity results. `Convex.integral_mem` says that the integral of a function with values in a closed convex set `s` lies in `s`, for a probability measure, and `Convex.average_mem` is the form with the average `⨍`. The Jensen inequality is `ConvexOn.map_integral_le`, with `ConvexOn.map_average_le` and `ConvexOn.map_set_average_le` for averages, and `ConcaveOn.le_map_integral` for concave functions. The strict form `StrictConvexOn.ae_eq_const_or_map_average_lt` says that either `f` is almost everywhere constant or the inequality is strict. For a strictly convex closed set `s`, `StrictConvex.ae_eq_const_or_average_mem_interior` says that either `f` is almost everywhere constant or its average lies in the interior of `s`. In a strictly convex space, `ae_eq_const_or_norm_integral_lt_of_norm_le_const` gives the same alternative for the norm of an integral.

The file `Mathlib.Analysis.Convex.Continuous` proves continuity. In a finite dimensional real space, `ConvexOn.continuousOn_interior` and `ConvexOn.locallyLipschitzOn_interior` hold on the interior of the domain, and `ConvexOn.continuousOn_intrinsicInterior` holds on the relative interior. In a general normed space, `ConvexOn.exists_lipschitzOnWith_of_isBounded` says that a convex function bounded on a ball `Metric.ball x₀ r` is Lipschitz on each ball `Metric.ball x₀ r'` with `r' < r`. The explicit form is `ConvexOn.lipschitzOnWith_of_abs_le`: if $|f| \le M$ on the ball of radius $r$ and $\varepsilon > 0$, then $f$ is Lipschitz with constant $2 M / \varepsilon$ on the ball of radius $r - \varepsilon$. The proof extends the segment between two points of the small ball by $\varepsilon$ beyond one end, and uses the slope criterion on this line. The lemma `ConvexOn.isBoundedUnder_abs` says that, for a convex function, a local bound above implies a local bound for the absolute value, since the function is bounded below near a point by the reflection of the upper bound. The lemma `ConvexOn.continuousOn_tfae` lists equivalent conditions on an open convex set: continuity, continuity at one point, local boundedness above at one point, and local boundedness everywhere. On intervals of `ℝ`, `ConvexOn.continuousOn_Icc` and its variants handle the end points.

The file `Mathlib.Analysis.Convex.FunctionTopology` proves that the set of convex functions is closed in the topology of pointwise convergence. The current names are `isClosed_setOfPred_convexOn` and `isClosed_setOfPred_concaveOn`.

The file `Mathlib.Analysis.Convex.Approximation` works in a locally convex space over `ℝ` or `ℂ`, a notion of Chapter 8. The lemma `ConvexOn.exists_affine_le_of_lt` says that for `a < φ x` there is a continuous affine function below `φ` on `s` with value `a` at `x`, when `s` is closed and `φ` is convex and lower semicontinuous on `s`. The proof applies the geometric Hahn Banach theorem to the closed convex epigraph, which is `LowerSemicontinuousOn.isClosed_re_epigraph` together with `ConvexOn.convex_re_epigraph`, and a point below it. Then `ConvexOn.sSup_affine_eq` writes `φ` as the supremum of these affine functions. In a hereditarily Lindelöf space, the forms `ConvexOn.sSup_of_countable_affine_eq` and `ConvexOn.real_univ_sSup_of_nat_affine_eq` use a countable family.

#### Common errors

1. The derivative tests in `Mathlib.Analysis.Convex.Deriv` ask for hypotheses on `interior D` and continuity on `D`. For `D = Set.Ici 0`, the interior is `Set.Ioi 0`, so prove the derivative facts only there.
2. `convexOn_rpow` is stated on `Set.Ici 0`, because `x ^ p` for real `p` and negative `x` is not the value that a reader expects. For integer powers on all of `ℝ`, use `Even.convexOn_pow`.
3. The Jensen inequality `ConvexOn.map_integral_le` needs the integrability of both `f` and `g ∘ f`. In Mathlib, the integral of a function that is not integrable is zero, so without these hypotheses the statement is false.

### Exercises

1. (A) Prove that $x \mapsto x \log x$ is convex on `Set.Ici 0` with `convexOn_of_deriv2_nonneg`.
2. (A) Derive the inequality of arithmetic and geometric means for two numbers from `strictConcaveOn_log_Ioi`.
3. (A) Prove that $\sin x \ge 2x/\pi$ on $[0, \pi / 2]$, with `strictConcaveOn_sin_Icc`.
4. (B) Prove the Hölder inequality for two finite sums from `Real.strictConcaveOn_rpow`.
5. (B) Prove that a convex function on `ℝ` is differentiable except at countably many points, with `ConvexOn.monotoneOn_rightDeriv`.
6. (C) Prove that a convex function on a Banach space that is lower semicontinuous is continuous on the interior of its domain.

### Reference

<?reference?>
