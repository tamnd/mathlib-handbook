---
title: Bump functions, mollifiers and smooth approximation
kind: api
modules:
  - Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
  - Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
  - Mathlib.Analysis.Calculus.BumpFunction.Normed
  - Mathlib.Analysis.Calculus.BumpFunction.Convolution
  - Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
  - Mathlib.Analysis.Calculus.ContDiff.Convolution
explains:
  E2: [ContDiffBumpBase, IsOpen.exists_contDiff_support_eq, ContDiffBump.normed, ContDiffBump.integral_normed, HasCompactSupport.contDiff_convolution_left, HasCompactSupport.hasFDerivAt_convolution_right, ContDiffBump.dist_normed_convolution_le, ContDiffBump.convolution_tendsto_right_of_continuous, ContinuousMap.dense_setOfPred_contDiff]
  E1: auto
families: []
requires: [V17.C02, V16, V18]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bump functions, mollifiers and smooth approximation

### Overview

Section 3 introduced the type `ContDiffBump c` of bump functions at a point $c$ and the class `HasContDiffBump E` of the spaces that have them. This section shows where the instances of the class come from, and what bump functions are used for in analysis.

There are two sources of bump functions. In an inner product space, the function $x \mapsto \psi\bigl((R - \|x\|)/(R - 1)\bigr)$, with $\psi$ the smooth transition from $0$ to $1$, is smooth because the norm is smooth away from $0$. In a finite-dimensional real normed space, the norm need not be smooth, and the construction is different: the library convolves a smooth function of small support with the indicator of the unit ball. The second construction also gives a stronger result: every open set of a finite-dimensional real space is the support of a smooth function.

A bump function with integral $1$ is a *mollifier*. The convolution
$$(\varphi \star g)(x) = \int \varphi(t) \, g(x - t) \, d\mu(t)$$
with a smooth $\varphi$ of compact support is smooth, for every locally integrable $g$. When the support of $\varphi$ shrinks to the point $0$, $\varphi \star g$ tends to $g$: at each point of continuity, and almost everywhere for a locally integrable $g$. Together these facts prove that smooth functions are dense in the continuous functions, for the topology of uniform convergence on compact sets.

The section uses the class $C^n$ and the smoothness of compositions of Sections 2 and 3, the Haar measure and the convolution of Volume 18, and the normed spaces of Volume 16.

### The library around it

#### Where the instances come from

The structure `ContDiffBumpBase E` holds a function `toFun : ℝ → E → ℝ` with these properties, for every $R > 1$: the values are in $[0, 1]$, the function is even in $x$, it is $1$ on the closed unit ball, its support is the open ball of radius $R$, and `uncurry toFun` is smooth on $(1, \infty) \times E$. The class `HasContDiffBump E` says that such a structure exists. A term `f : ContDiffBump c` with radii $r_{\mathrm{in}} < r_{\mathrm{out}}$ then coerces to the function
$$x \mapsto \mathrm{toFun}\,(r_{\mathrm{out}} / r_{\mathrm{in}})\,\bigl(r_{\mathrm{in}}^{-1} \cdot (x - c)\bigr).$$
The joint smoothness in $R$ and $x$ is the reason that a bump function depends smoothly on its radii and its center.

The module `Mathlib.Analysis.Calculus.BumpFunction.InnerProduct` defines `ContDiffBumpBase.ofInnerProductSpace E` for a real inner product space with the formula of the overview, and registers `hasContDiffBump_of_innerProductSpace`.

The module `Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension` works in a finite-dimensional real normed space. Its first theorem is `IsOpen.exists_contDiff_support_eq`: every open set $s$ is the support of a function of class $C^n$ with values in $[0, 1]$. The proof covers $s$ by the supports of countably many smooth functions and adds them with small coefficients. The theorem `exists_contDiff_tsupport_subset` of Section 3 also lives here. The rest of the module is the construction in the namespace `ExistsContDiffBumpBase`:

| Lean name | Meaning |
|---|---|
| `ExistsContDiffBumpBase.u` | a smooth even function with support the open unit ball (`ExistsContDiffBumpBase.u_exists`) |
| `ExistsContDiffBumpBase.w` | `u` rescaled to the ball of radius $D$ and divided by its integral, so its integral is $1$ |
| `ExistsContDiffBumpBase.φ` | the indicator of the closed unit ball |
| `ExistsContDiffBumpBase.y` | the convolution `w D ⋆ φ`: it is $1$ on the ball of radius $1 - D$ and its support is the ball of radius $1 + D$ |

The instance `ExistsContDiffBumpBase.instHasContDiffBumpOfFiniteDimensionalReal` builds the structure from `y` with a change of variables. These names are steps of a proof. A user needs only the instance, which is found automatically.

#### Normed bump functions

The module `Mathlib.Analysis.Calculus.BumpFunction.Normed` divides a bump function by its integral. For a measure $\mu$ on $E$, `f.normed μ x` is $f(x) / \int f \, d\mu$ (`ContDiffBump.normed_def`). Its basic properties are:

- `ContDiffBump.integral_normed`: the integral of `f.normed μ` is $1$;
- `ContDiffBump.integral_normed_smul`: $\int f_{\mu}(x) \cdot z \, d\mu = z$ for a vector $z$;
- `ContDiffBump.contDiff_normed`, `ContDiffBump.nonneg_normed`, `ContDiffBump.hasCompactSupport_normed`;
- `ContDiffBump.support_normed_eq`: the support is the open ball of radius $r_{\mathrm{out}}$;
- `ContDiffBump.normed_le_div_measure_closedBall_rIn`: the bound $1 / \mu(\bar B(c, r_{\mathrm{in}}))$.

These lemmas need `FiniteDimensional ℝ E`, a Borel space, and a measure that is finite on compact sets and positive on open sets, for example the Lebesgue measure. The lemma `ContDiffBump.tendsto_support_normed_smallSets` says that the supports shrink to $c$ when $r_{\mathrm{out}} \to 0$.

#### Smoothness of convolutions

The module `Mathlib.Analysis.Calculus.ContDiff.Convolution` proves that a convolution is as smooth as its smoother factor. The convolution `MeasureTheory.convolution f g L μ` takes a continuous bilinear map $L$, so that it covers products, scalar products and the application of operators, and is written `f ⋆[L, μ] g`. The field is `RCLike 𝕜`, the group $G$ is a normed space over $𝕜$, and $\mu$ is invariant under translation.

| Lean name | Statement |
|---|---|
| `HasCompactSupport.hasFDerivAt_convolution_right` | $g$ of class $C^1$ with compact support, $f$ locally integrable: $D(f \star g) = f \star Dg$ |
| `HasCompactSupport.hasFDerivAt_convolution_left` | the same with the roles of $f$ and $g$ exchanged |
| `HasCompactSupport.contDiff_convolution_right` | $g$ of class $C^n$ with compact support: $f \star g$ is $C^n$ |
| `HasCompactSupport.contDiff_convolution_left` | $f$ of class $C^n$ with compact support: $f \star g$ is $C^n$ |
| `HasCompactSupport.hasDerivAt_convolution_right` | the version with `deriv` on $𝕜$ |

In the derivative $f \star Dg$, the bilinear map is not $L$ but `ContinuousLinearMap.precompR G L`, because $Dg$ takes values in operators. The versions `MeasureTheory.contDiffOn_convolution_right_with_param` and `MeasureTheory.contDiffOn_convolution_left_with_param` let $g$ depend on a parameter $p$ in an open set and prove joint smoothness in $(p, x)$. They need a fixed compact set $k$ outside of which every $g_p$ vanishes.

#### Approximation by convolution

The module `Mathlib.Analysis.Calculus.BumpFunction.Convolution` uses the normed bumps `φ.normed μ` with `φ : ContDiffBump 0` as mollifiers, with the bilinear map `ContinuousLinearMap.lsmul ℝ ℝ`.

- `ContDiffBump.convolution_eq_right` and `ContDiffBump.normed_convolution_eq_right`: if $g$ is constant on the ball of radius $r_{\mathrm{out}}$ at $x_0$, the convolution at $x_0$ is the value $g(x_0)$, times $\int \varphi$ for the unnormed version.
- `ContDiffBump.dist_normed_convolution_le`: if $\mathrm{dist}(g(x), g(x_0)) \le \varepsilon$ on that ball, then the convolution at $x_0$ is at distance at most $\varepsilon$ from $g(x_0)$.
- `ContDiffBump.convolution_tendsto_right_of_continuous`: for continuous $g$ and a family $\varphi_i$ with $r_{\mathrm{out}} \to 0$, the convolutions tend to $g(x_0)$ at every point.
- `ContDiffBump.convolution_tendsto_right`: a version where the functions $g_i$ and the points of evaluation also vary.
- `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`: for a locally integrable $g$, the convergence holds almost everywhere, under the condition $r_{\mathrm{out}} \le K r_{\mathrm{in}}$. This is a form of the differentiation theorem of Lebesgue.

#### Density of smooth functions

The module `Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox` removes the measures from these statements. Let $E$ be a finite-dimensional real normed space and $F$ a real Banach space.

- `UniformContinuous.exists_contDiff_dist_le`: for a uniformly continuous $f$ and $\varepsilon > 0$, there is a smooth $g$ with $\mathrm{dist}(g(a), f(a)) < \varepsilon$ for all $a$.
- `Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`: for a continuous $f$ and a radius $\varepsilon$, there is a smooth $g$ such that $\mathrm{dist}(g(a), f(a)) \le \delta$ at each point $a$ where $f$ varies by at most $\delta$ on the ball $B(a, \varepsilon)$.
- `MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`: the same for a locally integrable $f$.
- `ContinuousMap.dense_setOfPred_contDiff`: the set of smooth maps is dense in `C(E, F)`, with the topology of uniform convergence on compact sets.

#### Common errors

1. A lemma of `Mathlib.Analysis.Calculus.BumpFunction.Convolution` asks for `φ : ContDiffBump 0`, not `ContDiffBump c`. A mollifier is centered at $0$, and the convolution moves it to each point. A bump at $c \ne 0$ in the convolution gives the value of $g$ near $x_0 - c$, not near $x_0$.
2. The function `f.normed μ` needs the measure as an explicit argument, and its integral is $1$ only for this same measure. With `volume` on a space that has another Haar measure, or without the instances `IsLocallyFiniteMeasure` and `IsOpenPosMeasure`, `ContDiffBump.integral_normed` does not apply.
3. The density theorem is for the topology of uniform convergence on compact sets, not for the supremum norm on all of $E$. For a function that is only continuous, no smooth $g$ with $\sup |g - f| < \varepsilon$ is given. Use `UniformContinuous.exists_contDiff_dist_le` when a global uniform bound is necessary.

### Exercises

1. (A) Use `IsOpen.exists_contDiff_support_eq` to prove that the set $\{x \in \mathbb{R}^2 : x_1 x_2 \ne 1\}$ is the support of a smooth function with values in $[0, 1]$.
2. (A) Let `f : ContDiffBump (0 : ℝ)` with $r_{\mathrm{in}} = 1$ and $r_{\mathrm{out}} = 2$. Bound `f.normed volume x` from above with `ContDiffBump.normed_le_div_measure_closedBall_rIn`, and compute the bound.
3. (B) Prove that if $g : \mathbb{R}^n \to \mathbb{R}$ is locally integrable and $\varphi$ is a bump function, then $\varphi \star g$ is smooth. Name the lemma and give the bilinear map.
4. (B) Explain why the derivative in `HasCompactSupport.hasFDerivAt_convolution_right` uses `ContinuousLinearMap.precompR G L` and not $L$, by checking the types of $f$, $Dg$ and $f \star Dg$.
5. (B) Use `ContDiffBump.convolution_tendsto_right_of_continuous` with $\varphi_k$ of radii $1/(k+2)$ and $1/(k+1)$ to prove that $\varphi_k \star g \to g$ pointwise for continuous $g$.
6. (C) Prove from `ContinuousMap.dense_setOfPred_contDiff` the theorem of Weierstrass type: for a continuous $f : \mathbb{R}^n \to \mathbb{R}$, a compact $K$ and $\varepsilon > 0$, there is a smooth $g$ with $|g - f| < \varepsilon$ on $K$.

### Reference

<?reference?>
