---
title: Measurable derivatives, integrals with a parameter and the theorem of Rademacher
kind: api
modules:
  - Mathlib.Analysis.Calculus.FDeriv.Measurable
  - Mathlib.Analysis.Calculus.LineDeriv.Measurable
  - Mathlib.Analysis.Calculus.ParametricIntegral
  - Mathlib.Analysis.Calculus.ParametricIntervalIntegral
  - Mathlib.Analysis.Calculus.ParametricCircleIntegral
  - Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
  - Mathlib.Analysis.Calculus.Rademacher
explains:
  E2: [measurableSet_of_differentiableAt, measurable_fderiv, measurable_deriv, hasFDerivAt_integral_of_dominated_of_fderiv_le, hasFDerivAt_integral_of_dominated_loc_of_lip, ContDiff.parametric_integral, intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le, integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable, LipschitzWith.ae_differentiableAt]
  E1: auto
families: []
requires: [V17.C01, V17.C02, V18]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Measurable derivatives, integrals with a parameter and the theorem of Rademacher

### Overview

This section connects the derivative with measure theory. It treats three questions.

The first question is measurability. The function `fderiv 𝕜 f` is defined for every $f$, with the value $0$ where $f$ is not differentiable. Without any hypothesis on $f$, the set of points where $f$ is differentiable is a Borel set, and `fderiv 𝕜 f` is a measurable function. So the derivative of an arbitrary function can be integrated, as soon as it satisfies a bound.

The second question is the derivative of an integral with a parameter:
$$\frac{d}{dx} \int F(x, a) \, d\mu(a) = \int \partial_x F(x, a) \, d\mu(a).$$
The exchange of the derivative and the integral holds when the partial derivatives have an integrable bound near the point. This is a consequence of the mean value inequality of Section 1 and of the dominated convergence theorem of Volume 18.

The third question is the theorem of Rademacher: a Lipschitz map between finite-dimensional real spaces is differentiable almost everywhere. The proof uses integration by parts for directional derivatives, which is also an independent result of the library.

The section uses the Fréchet derivative and the line derivative of Chapter 1, the rules of Chapter 2, the mean value inequality of Section 1, and the integral, the Haar measure and dominated convergence of Volume 18.

### The library around it

#### The derivative is measurable

The module `Mathlib.Analysis.Calculus.FDeriv.Measurable` assumes that $E$ has a measurable structure that contains the open sets (`OpensMeasurableSpace E`) and that $F$ is complete. The main results are:

| Lean name | Statement |
|---|---|
| `measurableSet_of_differentiableAt` | $\{x \mid f \text{ differentiable at } x\}$ is measurable |
| `measurableSet_of_differentiableAt_of_isComplete` | the same with the condition $Df(x) \in K$, for a complete set $K$ of operators |
| `measurable_fderiv` | `fderiv 𝕜 f` is measurable |
| `measurable_fderiv_apply_const` | $x \mapsto Df(x)\,y$ is measurable, for fixed $y$ |
| `measurable_deriv` | for $f : 𝕜 \to F$, `deriv f` is measurable |

The proof writes the set of differentiability with countable unions and intersections of open sets. Each open set is given by a condition $\|f(z) - f(y) - L(z - y)\| < \varepsilon r$ for $y, z$ in a ball at $x$ of radius about $r$, with $\varepsilon$ and $r$ in countable families. The helper sets are in the namespace `FDerivMeasurableAux`, and a user does not need them.

The library also gives the strong versions `stronglyMeasurable_deriv` and `aestronglyMeasurable_deriv`, and the almost everywhere version `aemeasurable_deriv`, for every measure. The strong versions need `SecondCountableTopologyEither 𝕜 F`. For maps $f : \mathbb{R} \to F$, the right derivatives `derivWithin f (Set.Ioi x) x` and `derivWithin f (Set.Ici x) x` are measurable too (`measurable_derivWithin_Ioi`, `measurable_derivWithin_Ici`). The versions with a parameter, such as `measurable_fderiv_with_param` and `measurable_deriv_with_param`, take $f : \alpha \to E \to F$ with `Continuous (Function.uncurry f)` and prove that $(p, x) \mapsto D(f_p)(x)$ is measurable.

The module `Mathlib.Analysis.Calculus.LineDeriv.Measurable` proves the same for the line derivative of a continuous map, over a locally compact field: `measurable_lineDeriv` for a fixed direction $v$, `measurable_lineDeriv_uncurry` for $(x, v) \mapsto \partial_v f(x)$, and `measurableSet_lineDifferentiableAt` for the set where the line derivative exists.

#### Derivatives of integrals with a parameter

The module `Mathlib.Analysis.Calculus.ParametricIntegral` takes $F : H \to \alpha \to E$, a measure $\mu$ on $\alpha$ and a point $x_0$. The field is `RCLike 𝕜`. All the theorems ask that $F(x, \cdot)$ is a.e. strongly measurable for $x$ near $x_0$ and that $F(x_0, \cdot)$ is integrable. They differ in the hypothesis on the derivative.

| Lean name | Hypothesis on $\partial_x F$ |
|---|---|
| `hasFDerivAt_integral_of_dominated_of_fderiv_le` | $\|\partial_x F(x, a)\| \le b(a)$ for $x$ in a neighbourhood $s$, a.e. in $a$, with $b$ integrable |
| `hasFDerivAt_integral_of_dominated_loc_of_lip` | $F(\cdot, a)$ is Lipschitz on $s$ with constant $b(a)$, and differentiable at $x_0$ |
| `hasFDerivAt_integral_of_dominated_loc_of_lip'` | the bound $\|F(x, a) - F(x_0, a)\| \le b(a)\|x - x_0\|$ instead of the Lipschitz condition |
| `hasDerivAt_integral_of_dominated_loc_of_deriv_le` | the version of the first line for $x$ in $𝕜$, with `HasDerivAt` |
| `hasFDerivAt_integral_of_contDiffOn` | $F$ of class $C^1$ on $u \times k$, $k$ compact, the integral over $s \subseteq k$ with $\mu(s) < \infty$ |

The conclusion is `HasFDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀`. The versions with a Lipschitz condition also give the integrability of the derivative, so their conclusion is a conjunction. The proof applies the mean value inequality of Section 1 to the difference quotients and then dominated convergence.

For the higher derivatives, `hasFTaylorSeriesUpToOn_integral_of_le_bound` integrates a family of Taylor series under integrable bounds on each term, and `ContDiff.parametric_integral` gives the common case: if $(x, a) \mapsto f(x, a)$ is of class $C^n$, then $x \mapsto \int_{s_0} f(x, a) \, d\mu(a)$ is of class $C^n$ for every set $s_0$ of finite measure inside a compact set. The local form is `ContDiffOn.parametric_integral`.

The module `Mathlib.Analysis.Calculus.ParametricIntervalIntegral` gives the same theorems for $\int_a^b F(x, t) \, dt$ in the namespace `intervalIntegral`, for example `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`. The hypotheses hold for almost every $t$ in `Set.uIoc a b`, so $a > b$ is allowed. The smooth version `ContDiff.parametric_intervalIntegral` asks only that $f : H \times \mathbb{R} \to E$ is $C^n$, because the interval is compact. The module `Mathlib.Analysis.Calculus.ParametricCircleIntegral` does the same for the circle integral $\oint_{|z - c| = R} F(x, z) \, dz$ of complex analysis, with `hasFDerivAt_circleIntegral_of_dominated_of_fderiv_le` and three related forms.

#### Integration by parts

The module `Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts` works on a finite-dimensional real space $E$ with an additive Haar measure $\mu$. For a continuous bilinear map $B$ and a direction $v$, the theorem `integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable` states
$$\int B(f(x), Dg(x)\,v) \, d\mu = -\int B(Df(x)\,v, g(x)) \, d\mu.$$
Its hypotheses are: the three functions $B(Df\,v, g)$, $B(f, Dg\,v)$ and $B(f, g)$ are integrable, $f$ has the derivative $f'$ at each point of the closed support of $g$, and $g$ has the derivative $g'$ at each point of the closed support of $f$. There is no boundary term, because the integrability of $B(f, g)$ makes the boundary terms tend to $0$. The forms `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`, `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` and `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable` use `fderiv`, multiplication and scalar multiplication. The proof reduces to $E \times \mathbb{R}$ with $v$ the last direction and uses Fubini and the one-dimensional formula.

#### The theorem of Rademacher

The module `Mathlib.Analysis.Calculus.Rademacher` assumes that $E$ is a finite-dimensional real space with an additive Haar measure $\mu$. The main theorem is

`LipschitzWith.ae_differentiableAt : LipschitzWith C f → ∀ᵐ x ∂μ, DifferentiableAt ℝ f x`

for $f : E \to F$ with $F$ finite-dimensional. The local form `LipschitzOnWith.ae_differentiableWithinAt` takes a measurable set $s$ and gives differentiability within $s$ for almost every point of $s$, and `LipschitzOnWith.ae_differentiableWithinAt_of_mem` removes the condition that $s$ is measurable. The proof has four steps, each a lemma of the module:

1. For each direction $v$, $f$ has a line derivative a.e. (`LipschitzWith.ae_lineDifferentiableAt`). This is the one-dimensional theorem for Lipschitz functions on each line, with Fubini.
2. The line derivative satisfies the integration by parts `LipschitzWith.integral_lineDeriv_mul_eq` against Lipschitz functions of compact support.
3. Hence $v \mapsto \partial_v f(x)$ is linear for almost every $x$ on finite sums (`LipschitzWith.ae_lineDeriv_sum_eq`), and on a countable set of directions it is given by one linear map (`LipschitzWith.ae_exists_fderiv_of_countable`).
4. A Lipschitz map with line derivatives $L v$ for all $v$ in a set whose closure contains the unit sphere has the Fréchet derivative $L$ (`LipschitzWith.hasFDerivAt_of_hasLineDerivAt_of_closure`).

As a corollary, every norm on $E$ is differentiable almost everywhere (`ae_differentiableAt_norm`) and on a dense set (`dense_differentiableAt_norm`).

#### Common errors

1. The theorem `measurable_fderiv` needs `CompleteSpace F`. Without it the theorem does not apply, even for a differentiable $f$. In that case, work in the completion, or prove measurability from continuity when $f$ is $C^1$.
2. The hypothesis of `hasFDerivAt_integral_of_dominated_of_fderiv_le` is a bound for all $x$ in a neighbourhood $s$ of $x_0$, not only at $x_0$. A bound $\|\partial_x F(x_0, a)\| \le b(a)$ at the single point does not give the exchange. Choose $s$ as a ball around $x_0$ and give the bound uniformly in $x \in s$.
3. The theorem of Rademacher needs both spaces finite-dimensional and the measure an additive Haar measure. It fails for Lipschitz maps into infinite-dimensional spaces such as $L^1([0, 1])$.

### Exercises

1. (A) Use `measurable_deriv` to prove that for every $f : \mathbb{R} \to \mathbb{R}$ the function $x \mapsto (f'(x))^2$ is measurable.
2. (A) Use `ContDiff.parametric_intervalIntegral` to prove that $x \mapsto \int_0^1 \sin(x t) \, dt$ is smooth on $\mathbb{R}$.
3. (B) Prove $\frac{d}{dx} \int_0^\infty e^{-t} \cos(x t) \, dt = -\int_0^\infty t \, e^{-t} \sin(x t) \, dt$ with `hasDerivAt_integral_of_dominated_loc_of_deriv_le`. Give the bound $b$ and the neighbourhood $s$.
4. (B) State the integration by parts `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` for $f, g : \mathbb{R}^n \to \mathbb{R}$ with $g$ smooth of compact support, and check each hypothesis.
5. (B) Use `LipschitzWith.ae_differentiableAt` to prove that $x \mapsto \mathrm{dist}(x, A)$ on $\mathbb{R}^n$ is differentiable almost everywhere, for every set $A$.
6. (C) Prove that a convex function $\mathbb{R}^n \to \mathbb{R}$ is differentiable almost everywhere, by showing that it is locally Lipschitz and using `LipschitzOnWith.ae_differentiableWithinAt` on open balls.

### Reference

<?reference?>
