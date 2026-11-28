---
title: Continuously polynomial functions and the analyticity of linear maps
kind: api
modules:
  - Mathlib.Analysis.Analytic.CPolynomialDef
  - Mathlib.Analysis.Analytic.CPolynomial
  - Mathlib.Analysis.Analytic.Linear
  - Mathlib.Analysis.Analytic.Polynomial
  - Mathlib.Analysis.Calculus.ContDiff.CPolynomial
explains:
  E2: [HasFiniteFPowerSeriesOnBall, CPolynomialAt, FormalMultilinearSeries.sum_of_finite, HasFiniteFPowerSeriesOnBall.changeOrigin, isOpen_cpolynomialAt, ContinuousMultilinearMap.hasFiniteFPowerSeriesOnBall, ContinuousLinearMap.hasFPowerSeriesOnBall_bilinear, CPolynomialAt.contDiffAt, AnalyticOnNhd.eval_polynomial]
  E1: auto
families: []
requires: [V17.C04, V16]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Continuously polynomial functions and the analyticity of linear maps

### Overview

A polynomial in one variable is a power series with only finitely many nonzero coefficients. The same idea works in normed spaces: a function $f : E \to F$ is *continuously polynomial* at $x$ when it is the sum of a formal multilinear series $p$ near $x$ and $p_m = 0$ for all large $m$. Then the sum $\sum_m p_m(y^m)$ is a finite sum, and no question of convergence arises. Mathlib calls this class `CPolynomialAt`, and it treats it in parallel with the class `AnalyticAt` of Section 1.

The class matters for two reasons. First, it contains the most common building blocks of calculus: constants, continuous linear maps, continuous bilinear maps and continuous multilinear maps. The library proves that these maps are analytic by proving that they are continuously polynomial. Second, the finite sums need no completeness of the target $F$. So the theorems of this section hold for every normed space $F$, while the change of origin of Section 2 needs $F$ complete.

The section first gives the definitions and the change of origin for finite series. It then lists the maps that are continuously polynomial, the operations that preserve the class, and the consequences for analyticity and smoothness. It ends with polynomials on a normed algebra. It uses the formal multilinear series and the radius of Section 1, the change of origin of Section 2 and the continuous multilinear maps of Volume 16.

### The library around it

#### Finite power series

The module `Mathlib.Analysis.Analytic.CPolynomialDef` defines four predicates. They mirror the predicates `HasFPowerSeriesOnBall`, `HasFPowerSeriesAt`, `AnalyticAt` and `AnalyticOnNhd` of Section 1.

| Lean name | Meaning |
|---|---|
| `HasFiniteFPowerSeriesOnBall f p x n r` | $f(x + y) = \sum_m p_m(y^m)$ for $\|y\| < r$, and $p_m = 0$ for $m \ge n$ |
| `HasFiniteFPowerSeriesAt f p x n` | the same on some ball of positive radius |
| `CPolynomialAt 𝕜 f x` | there are $p$ and $n$ with `HasFiniteFPowerSeriesAt f p x n` |
| `CPolynomialOn 𝕜 f s` | `CPolynomialAt 𝕜 f x` for each $x \in s$ |

The number $n$ is a strict bound: the series has its nonzero terms among $p_0, \dots, p_{n-1}$. A constant function has a finite series with $n = 1$, a continuous linear map has one with $n = 2$, and the zero function has one with $n = 0$. The structure `HasFiniteFPowerSeriesOnBall` extends `HasFPowerSeriesOnBall` with the field `finite`, and the lemma `HasFiniteFPowerSeriesOnBall.finite` reads it. The projection `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall` forgets it. To build the structure, `HasFiniteFPowerSeriesOnBall.mk'` asks only for the vanishing of $p_m$ for $m \ge n$, a positive radius and the identity $f(x + y) = \sum_{i < n} p_i(y^i)$ on the ball.

**Theorem (A finite series sums to a partial sum).** Let $p$ be a formal multilinear series with $p_m = 0$ for $m \ge n$. Then for every $y \in E$ the series $\sum_m p_m(y^m)$ converges, its sum is the partial sum $\sum_{m < n} p_m(y^m)$, and the radius of $p$ is $\infty$.

*Proof.* All terms with index $m \ge n$ are zero. A series with finitely many nonzero terms converges in every normed space to the sum of these terms. The bound $\|p_m\| r^m \le C$ holds for every $r$ with $C = \max_{m < n} \|p_m\| r^m$, so the radius is $\infty$ by Section 1. $\square$

This is `FormalMultilinearSeries.sum_of_finite`, with `FormalMultilinearSeries.hasSum_of_finite` for the convergence and `FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite` for the statement that `p.sum` has the finite series `p` on the whole space. The lemma `FormalMultilinearSeries.continuousOn_of_finite` gives the continuity of `p.sum`, again without completeness.

**Theorem (Change of origin).** Let $f$ have a finite series $p$ at $x$ with bound $n$ on the ball of radius $r$, and let $\|y\| < r$. Then $f$ has the finite series `p.changeOrigin y` at $x + y$ with the same bound $n$ on the ball of radius $r - \|y\|$.

*Proof sketch.* The $k$th coefficient of `p.changeOrigin y` is a sum over $l$ of terms built from $p_{k + l}$ with $l$ arguments equal to $y$. If $k \ge n$, then $k + l \ge n$ for every $l$, so all these terms vanish. This gives the bound $n$ for the new series (`FormalMultilinearSeries.changeOrigin_finite_of_finite`). For $k < n$ the sum over $l$ is finite, so it exists in every normed space. The identity $(p.\mathrm{changeOrigin}\ y)(z) = p(y + z)$ is a rearrangement of a finite sum (`FormalMultilinearSeries.changeOrigin_eval_of_finite`). $\square$

This is `HasFiniteFPowerSeriesOnBall.changeOrigin`. With $r = \infty$ in the main examples, it shows that a function with a finite series on a ball is continuously polynomial at every point of the ball (`HasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem` and `HasFiniteFPowerSeriesOnBall.cpolynomialOn`). The consequence is `isOpen_cpolynomialAt`: the set of points where $f$ is continuously polynomial is open. The analytic analogue, `AnalyticAt.eventually_analyticAt`, needs `[CompleteSpace F]`; this one does not.

The rest of `CPolynomialDef` is the expected API. The lemmas `HasFiniteFPowerSeriesAt.of_le` and `HasFiniteFPowerSeriesOnBall.of_le` raise the bound $n$. The lemmas `HasFiniteFPowerSeriesOnBall.mono` and `HasFiniteFPowerSeriesOnBall.comp_sub` shrink the ball and translate the function. Congruence goes through `CPolynomialAt.congr` and `CPolynomialAt_congr` for functions that agree near $x$, and `CPolynomialOn.congr` for functions that agree on an open set. A series with bound $0$ is zero near $x$ (`HasFiniteFPowerSeriesAt.eventually_zero_of_bound_zero`), and a series with bound $1$ makes $f$ constant near $x$ (`HasFiniteFPowerSeriesAt.eventually_const_of_bound_one`). The implications to the analytic world are `CPolynomialAt.analyticAt`, `CPolynomialOn.analyticOnNhd`, `CPolynomialOn.analyticOn` and `CPolynomialAt.analyticWithinAt`, and the continuity lemmas are `CPolynomialAt.continuousAt`, `CPolynomialOn.continuousOn` and `CPolynomialOn.continuous`.

#### Linear and bilinear maps

The module `Mathlib.Analysis.Analytic.Linear` treats continuous linear and bilinear maps. A continuous linear map $f : E \to F$ satisfies $f(x + y) = f(x) + f(y)$. So its series at $x$ is `f.fpowerSeries x`, with $p_0 = f(x)$, $p_1 = f$ and $p_m = 0$ for $m \ge 2$. The lemma `ContinuousLinearMap.hasFiniteFPowerSeriesOnBall` states that this series has bound $2$ on the ball of radius $\infty$, and `ContinuousLinearMap.fpowerSeries_radius` says that the radius is $\infty$.

**Theorem (Bilinear maps are analytic).** Let $B : E \times F \to G$ be continuous bilinear and $(x, y) \in E \times F$. Then $B$ has a power series at $(x, y)$ with radius $\infty$ and with $p_m = 0$ for $m \ge 3$.

*Proof.* Bilinearity gives
$$B(x + h, y + k) = B(x, y) + \bigl(B(x, k) + B(h, y)\bigr) + B(h, k).$$
The first term is the constant $p_0$. The second is the continuous linear map $p_1(h, k) = B(x, k) + B(h, y)$, which is the derivative of $B$ at $(x, y)$. The third is $p_2((h, k), (h, k))$ for the continuous bilinear map $p_2((h_1, k_1), (h_2, k_2)) = B(h_1, k_2)$. The identity holds for all $(h, k)$, so the radius is $\infty$. $\square$

In Lean, the series is `ContinuousLinearMap.fpowerSeriesBilinear`. The lemmas `ContinuousLinearMap.fpowerSeriesBilinear_apply_zero`, `ContinuousLinearMap.fpowerSeriesBilinear_apply_one`, `ContinuousLinearMap.fpowerSeriesBilinear_apply_two` and `ContinuousLinearMap.fpowerSeriesBilinear_apply_add_three` compute its four kinds of terms. The term of degree $1$ is `f.deriv₂ x`, and the term of degree $2$ is `ContinuousLinearMap.uncurryBilinear`, the map $p_2$ of the proof. The theorem is `ContinuousLinearMap.hasFPowerSeriesOnBall_bilinear`.

From these two series the module derives the full family of analyticity statements, one for each predicate of Section 1. The names follow one pattern: `ContinuousLinearMap.analyticAt`, `ContinuousLinearMap.analyticWithinAt`, `ContinuousLinearMap.analyticOn` and `ContinuousLinearMap.analyticOnNhd` for a linear map; `ContinuousLinearMap.analyticAt_bilinear` and its three variants for a bilinear map written as `fun x ↦ f x.1 x.2`; the same four for `ContinuousLinearEquiv` and `LinearIsometryEquiv`. The identity and the two projections have their own lemmas: `analyticAt_id`, `analyticOnNhd_id`, `analyticAt_fst` and `analyticAt_snd`, with the forms `Within`, `On` and `OnNhd`. A proof that some map is analytic usually starts from one of these lemmas and then uses the rules of Section 3.

#### Multilinear maps

The module `Mathlib.Analysis.Analytic.CPolynomial` extends the list to multilinear maps. Let $f : \prod_{i \in \iota} E_i \to F$ be continuous multilinear, with $\iota$ finite. At the origin, $f(h)$ is homogeneous of degree $|\iota|$ in $h$, so the series of $f$ at $0$ has the single nonzero term $p_{|\iota|}$, the map $f$ read on the diagonal. This is the series `ContinuousMultilinearMap.toFormalMultilinearSeries`, and `ContinuousMultilinearMap.hasFiniteFPowerSeriesOnBall` gives the bound $|\iota| + 1$ at the origin with radius $\infty$. At another point $x$, multilinearity gives an expansion in which each term chooses, for each $i$, either the base point $x_i$ or the increment $h_i$:
$$f(x + h) = \sum_{S \subseteq \iota} f(y^S), \qquad y^S_i = h_i \text{ for } i \in S, \quad y^S_i = x_i \text{ for } i \notin S.$$
The term for $S$ is homogeneous of degree $|S|$ in $h$, so the expansion has the degrees $0$ to $|\iota|$. The change of origin produces this expansion, so $f$ is continuously polynomial everywhere: `ContinuousMultilinearMap.cpolynomialAt` and `ContinuousMultilinearMap.cpolynomialOn`. The analytic forms `ContinuousMultilinearMap.analyticAt`, `ContinuousMultilinearMap.analyticOnNhd` and the others follow. All these lemmas need `[Fintype ι]`.

The module proves the same results for maps of two arguments that combine linear and multilinear dependence:

1. evaluation $(f, v) \mapsto f(v)$ on `ContinuousMultilinearMap 𝕜 Em F × (∀ i, Em i)`, in `ContinuousMultilinearMap.cpolynomialAt_apply` and `ContinuousMultilinearMap.analyticAt_apply`;
2. a linear map into multilinear maps, uncurried, in `ContinuousLinearMap.cpolynomialAt_uncurry_of_multilinear`, with the explicit series `ContinuousLinearMap.toFormalMultilinearSeriesOfMultilinear`;
3. a multilinear map into linear maps, uncurried, in `ContinuousMultilinearMap.cpolynomialAt_uncurry_of_linear`;
4. the composition $(g, f) \mapsto f \circ (g_i)_i$ of a multilinear map with linear maps, in `ContinuousMultilinearMap.cpolynomialAt_uncurry_compContinuousLinearMap`.

Continuous alternating maps are multilinear, so they have the same family: `ContinuousAlternatingMap.cpolynomialAt`, `ContinuousAlternatingMap.analyticAt_apply` and the analyticity of the pullback `ContinuousAlternatingMap.compContinuousLinearMapCLM` in `ContinuousAlternatingMap.analyticAt_compContinuousLinearMapCLM`.

#### Operations

The class is closed under the linear operations. For finite series, `HasFiniteFPowerSeriesOnBall.add` adds two series with bounds $n$ and $m$ and gets the bound $\max(n, m)$, and `HasFiniteFPowerSeriesOnBall.neg`, `HasFiniteFPowerSeriesOnBall.sub` and `HasFiniteFPowerSeriesOnBall.prodMk` follow the same pattern. For the predicates, the lemmas are `CPolynomialAt.add`, `CPolynomialAt.sub`, `CPolynomialAt.neg`, `CPolynomialAt.smul` and `CPolynomialAt.prodMk`, with the same names for `CPolynomialOn`. Each operation has two forms, as in the rest of the library: `CPolynomialAt.add` is about `f + g`, and `CPolynomialAt.fun_add` is about `fun x ↦ f x + g x`. The constants are `CPolynomialAt_const` and `CPolynomialOn_const`, and a continuous linear map on the left preserves the class (`ContinuousLinearMap.comp_cpolynomialAt`). Composition `CPolynomialAt.comp` lives with the composition of analytic maps in Section 3.

#### Smoothness

**Theorem.** A function that is continuously polynomial at $x$ is $C^n$ at $x$ for every $n$, including $n = \omega$.

*Proof sketch.* By `CPolynomialAt.exists_ball_cpolynomialOn`, $f$ is continuously polynomial on a ball $B$ around $x$. The derivative of a continuously polynomial function on an open set is again continuously polynomial there (`CPolynomialOn.fderiv`, from Section 2). By induction all iterated derivatives exist and are continuous on $B$. $\square$

The module `Mathlib.Analysis.Calculus.ContDiff.CPolynomial` records this as `CPolynomialAt.contDiffAt` and `CPolynomialOn.contDiffOn`. The analytic version of Section 2 needs a complete target. This one does not, which is why the module proves `ContinuousMultilinearMap.contDiff` for every normed space $F$.

#### Polynomials

The module `Mathlib.Analysis.Analytic.Polynomial` treats polynomial expressions. Let $A$ be a normed commutative algebra over $\mathbb{K}$ and $p \in A[X]$. Then $x \mapsto p(x)$ is analytic on $A$ (`AnalyticOnNhd.eval_polynomial`). The proof writes $p(x)$ as a finite sum of constants times powers of $x$ and uses the rules for sums and products of Section 3. More generally, if $f : E \to B$ is analytic at $z$ and $p$ has coefficients in an algebra $A$ over which $B$ is an algebra, then $x \mapsto p(f(x))$ is analytic at $z$ (`AnalyticAt.aeval_polynomial`, with the forms `Within`, `On` and `OnNhd`). For several variables, `AnalyticAt.aeval_mvPolynomial` asks that each coordinate $x \mapsto f(x)_i$ is analytic, and `AnalyticOnNhd.eval_mvPolynomial` states that a multivariate polynomial on $\mathbb{K}^\sigma$, for a finite $\sigma$, is analytic. The lemmas `AnalyticOnNhd.eval_continuousLinearMap` and `AnalyticOnNhd.eval_linearMap` treat $x \mapsto P(f(x))$ for a linear $f : E \to (\sigma \to B)$.

#### Common errors

1. Reading the bound $n$ of `HasFiniteFPowerSeriesOnBall f p x n r` as the degree. The terms are $p_0, \dots, p_{n-1}$, so a linear map has bound $2$ and a constant has bound $1$.
2. Proving analyticity of a linear map by hand. The lemmas `ContinuousLinearMap.analyticAt` and `ContinuousLinearMap.analyticAt_bilinear` do it, and they need no completeness.
3. Looking for `CPolynomialAt.comp` or `CPolynomialOn.fderiv` in these modules. Composition is in the module of the composition of analytic maps (Section 3), and the derivative is in the module of derivatives of analytic maps (Section 2).

### Exercises

1. (A) Let $B : E \times E \to F$ be continuous bilinear. Show that $x \mapsto B(x, x)$ is continuously polynomial on $E$ and find its finite series at $x$, with its bound.
2. (A) Show that a function with a finite series of bound $1$ at $x$ is constant near $x$. Compare with `HasFiniteFPowerSeriesAt.eventually_const_of_bound_one`.
3. (B) Let $f : E \to F$ be continuously polynomial on $E$ and $F$ an incomplete normed space. Explain why $f$ is still $C^\infty$, and which step of the analytic proof of Section 2 fails for a general analytic $f$.
4. (B) Show that the determinant $M_n(\mathbb{K}) \to \mathbb{K}$ is continuously polynomial, with a finite series of bound $n + 1$ at $0$. Hint: it is multilinear in the columns.
5. (B) Let $f : E \to \mathcal{A}$ be continuously polynomial at $x$, with $\mathcal{A}$ a normed algebra. Show that $f^2$ is continuously polynomial at $x$. Hint: compose $f$ with a bilinear map.
6. (C) Let $f : \mathbb{R} \to F$ be continuously polynomial on $\mathbb{R}$. Show that there is one formal multilinear series $p$ with finitely many nonzero terms such that $f = p.\mathrm{sum}$ on all of $\mathbb{K}$. Hint: the set where the series at $0$ represents $f$ near the point is open and closed. Explain why the statement fails over the $p$-adic numbers.

### Reference

<?reference?>
