---
title: Directional derivatives, partial derivatives and derivatives within a set
kind: theory
modules:
  - Mathlib.Analysis.Calculus.LineDeriv.Basic
  - Mathlib.Analysis.Calculus.Gradient.Basic
  - Mathlib.Analysis.Calculus.TangentCone.Defs
  - Mathlib.Analysis.Calculus.TangentCone.Basic
  - Mathlib.Analysis.Calculus.TangentCone.Real
  - Mathlib.Analysis.Calculus.FDeriv.Pi
  - Mathlib.Analysis.Calculus.FDeriv.Partial
  - Mathlib.Analysis.Calculus.FDeriv.WithLp
  - Mathlib.Analysis.Calculus.LineDeriv.QuadraticMap
  - Mathlib.Analysis.Calculus.TangentCone.DimOne
  - Mathlib.Analysis.Calculus.TangentCone.Pi
  - Mathlib.Analysis.Calculus.TangentCone.Prod
  - Mathlib.Analysis.Calculus.TangentCone.ProperSpace
  - Mathlib.Analysis.Calculus.TangentCone.Seq
explains:
  E3: [HasLineDerivAt, HasFDerivWithinAt, tangentConeAt, UniqueDiffWithinAt]
  E2: [lineDeriv, HasFDerivAt.hasLineDerivAt, DifferentiableAt.lineDeriv_eq_fderiv, gradient, hasGradientAt_iff_hasFDerivAt, fderivWithin, HasFDerivWithinAt.fderivWithin, UniqueDiffOn, uniqueDiffOn_convex, mem_tangentConeAt_of_seq, hasFDerivAt_update]
  E1: auto
families: []
requires: [V07, V13, V15.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Directional derivatives, partial derivatives and derivatives within a set

### Overview

To compute the Fréchet derivative of Section 1, restrict $f$ to lines: the derivative of $t \mapsto f(x + tv)$ at $t = 0$ is the directional derivative, and in $\mathbb{R}^n$ the directions $e_j$ give the partial derivatives and the Jacobian matrix. A differentiable map has all directional derivatives, the converse fails, and continuous partial derivatives imply differentiability. The last part treats a map on a set $s$, such as a closed interval. The derivative within $s$ is unique when the tangent cone of $s$ spans a dense subspace, and this holds for each convex set with nonempty interior.

### Definitions

**Definition (Directional derivative).** Let $f : E \to F$, $x, v \in E$. The vector $w \in F$ is the *derivative of $f$ at $x$ in the direction $v$* if the map $t \mapsto f(x + tv)$ of one variable has the derivative $w$ at $t = 0$:
$$w = \lim_{t \to 0} \frac{f(x + tv) - f(x)}{t}.$$
It is written $\partial_v f(x)$. It is also called the *Gateaux derivative*.

For $E = \mathbb{R}^n$ and the standard basis $e_1, \dots, e_n$, the *partial derivative* is $\partial_j f(x) = \partial_{e_j} f(x)$.

::: mathlib
`HasLineDerivAt` · `Mathlib.Analysis.Calculus.LineDeriv.Basic`

`HasLineDerivAt 𝕜 f f' x v` is defined as `HasDerivAt (fun t => f (x + t • v)) f' 0`, the definition of the text. The function `lineDeriv 𝕜 f x v` is the value, with the junk value `0`. Mathlib has no separate partial derivative: in $\mathbb{R}^n$ it is `lineDeriv ℝ f x (Pi.single j 1)`, or `fderiv ℝ f x (Pi.single j 1)` for a differentiable `f`. On a product of spaces, `hasFDerivAt_update` differentiates `Function.update x i`, and the partial derivative in the factor `i` is the derivative of `f ∘ Function.update x i`.

<?decl HasLineDerivAt?>
<?decl lineDeriv?>
<?decl hasFDerivAt_update?>
:::

**Definition (Gradient).** Let $E$ be a real Hilbert space and $f : E \to \mathbb{R}$ differentiable at $x$. The *gradient* $\nabla f(x)$ is the unique vector with $Df(x)h = \langle \nabla f(x), h\rangle$ for all $h \in E$.

The vector exists by the theorem of Riesz of Volume 16. In $\mathbb{R}^n$ no theorem is needed: $a_j = Df(x)e_j = \partial_j f(x)$, so $\nabla f(x) = (\partial_1 f(x), \dots, \partial_n f(x))$.

::: mathlib
`gradient` · `Mathlib.Analysis.Calculus.Gradient.Basic`

`gradient f x` is `(toDual 𝕜 F).symm (fderiv 𝕜 f x)`, where `toDual` is the Riesz isometry, so the space needs `[CompleteSpace F]`. The relation `HasGradientAt f f' x` is equivalent to `HasFDerivAt f (toDual 𝕜 F f') x` by `hasGradientAt_iff_hasFDerivAt`.

<?decl gradient?>
<?decl hasGradientAt_iff_hasFDerivAt?>
:::

**Definition (Derivative within a set).** Let $s \subseteq E$, $x \in s$ and $f : s \to F$. A map $L \in L(E, F)$ is a *derivative of $f$ at $x$ within $s$* if $f(y) = f(x) + L(y - x) + o(\|y - x\|)$ as $y \to x$ with $y \in s$.

**Definition (Tangent cone).** The *tangent cone* $T_s(x)$ is the set of the vectors $v \in E$ for which there are sequences $c_n \in \mathbb{K}$ and $d_n \in E$ with $x + d_n \in s$, $d_n \to 0$ and $c_n d_n \to v$. The set $s$ has *unique differentials at $x$* if the linear span of $T_s(x)$ is dense in $E$ and $x \in \overline{s}$.

For an open $s$ the tangent cone is all of $E$. For a line $\ell$ in $\mathbb{R}^2$ through $x$ it is $\ell - x$, and its span is not dense.

::: mathlib
`HasFDerivWithinAt` · `Mathlib.Analysis.Calculus.FDeriv.Defs`

`HasFDerivWithinAt f f' s x` is `HasFDerivAtFilter f f' (𝓝[s] x ×ˢ pure x)`: the first point tends to `x` inside `s`. The function `fderivWithin 𝕜 f s x` takes the value `0` when `f` is not differentiable within `s` at `x`, and also when `0` is one of the possible derivatives. `fderiv 𝕜 f x` is by definition `fderivWithin 𝕜 f univ x`.

<?decl HasFDerivWithinAt?>
<?decl fderivWithin?>
:::

::: mathlib
`tangentConeAt` · `Mathlib.Analysis.Calculus.TangentCone.Defs`

`tangentConeAt 𝕜 s x` is defined with cluster points of a filter, and `mem_tangentConeAt_of_seq` gives the sequence form of the text. `UniqueDiffWithinAt 𝕜 s x` is a structure with two fields, `dense_tangentConeAt` and `mem_closure`, and `UniqueDiffOn 𝕜 s` asks it at each point of `s`.

<?decl tangentConeAt?>
<?decl UniqueDiffWithinAt?>
<?decl mem_tangentConeAt_of_seq?>
:::

### Theorems and proofs

**Theorem (Differentiable implies directional derivatives).** If $f$ is differentiable at $x$, then for each $v \in E$ the directional derivative exists and $\partial_v f(x) = Df(x)v$. For $f : \mathbb{R}^n \to \mathbb{R}^m$ the matrix of $Df(x)$ is the *Jacobian matrix* $\big(\partial_j f_i(x)\big)_{i,j}$.

*Proof.* For $t \neq 0$, $f(x + tv) - f(x) = t\,Df(x)v + r(tv)$, so
$$\Big\|\frac{f(x + tv) - f(x)}{t} - Df(x)v\Big\| = \frac{\|r(tv)\|}{|t|}.$$
For $v = 0$ this is $0$. For $v \neq 0$ it equals $\|v\| \cdot \|r(tv)\|/\|tv\|$, which tends to $0$ as $t \to 0$ because $tv \to 0$. The $j$-th column of the matrix of $Df(x)$ is $Df(x)e_j = \partial_j f(x)$. $\square$

::: mathlib
`HasFDerivAt.hasLineDerivAt` · `Mathlib.Analysis.Calculus.LineDeriv.Basic`

`HasFDerivAt f L x → ∀ v, HasLineDerivAt 𝕜 f (L v) x v`. The `lineDeriv` form is `DifferentiableAt.lineDeriv_eq_fderiv : lineDeriv 𝕜 f x v = fderiv 𝕜 f x v`.

<?decl HasFDerivAt.hasLineDerivAt?>
<?decl DifferentiableAt.lineDeriv_eq_fderiv?>
:::

**Theorem (Continuous partial derivatives).** Let $U \subseteq \mathbb{R}^n$ be open, $x \in U$, and $f : U \to \mathbb{R}$. Assume that the partial derivatives $\partial_1 f, \dots, \partial_n f$ exist on a ball $B(x, r) \subseteq U$ and are continuous at $x$. Then $f$ is differentiable at $x$ with $Df(x)h = \sum_j h_j\,\partial_j f(x)$.

*Proof.* Let $\|h\| < r$, for the Euclidean norm. Put $p_0 = x$ and $p_k = x + h_1 e_1 + \dots + h_k e_k$, so $p_n = x + h$, and each $p_k$ lies in $B(x, r)$ because $\|p_k - x\| \le \|h\|$. Then
$$f(x + h) - f(x) = \sum_{k=1}^n \big(f(p_k) - f(p_{k-1})\big).$$
The points $p_{k-1}$ and $p_k$ differ only in the $k$-th coordinate. The function $g(t) = f(p_{k-1} + te_k)$ between $0$ and $h_k$ has $g'(t) = \partial_k f(p_{k-1} + te_k)$. The mean value theorem of Volume 15, Chapter 3 gives a point $q_k$ on the segment from $p_{k-1}$ to $p_k$ with $f(p_k) - f(p_{k-1}) = h_k\,\partial_k f(q_k)$. Then $\|q_k - x\| \le \|h\|$, and
$$f(x + h) - f(x) - \sum_k h_k\,\partial_k f(x) = \sum_k h_k\big(\partial_k f(q_k) - \partial_k f(x)\big).$$
Let $\varepsilon > 0$. By continuity at $x$ there is $\delta \in (0, r)$ with $|\partial_k f(y) - \partial_k f(x)| \le \varepsilon$ for all $k$ and $\|y - x\| < \delta$. For $\|h\| < \delta$ the right side has absolute value at most $\varepsilon\sum_k |h_k| \le \varepsilon\sqrt{n}\,\|h\|$, by Cauchy-Schwarz. So the remainder is $o(\|h\|)$. $\square$

For $f : U \to \mathbb{R}^m$ apply the theorem to each component (Chapter 2). The index of this edition has no declaration for this theorem in coordinates.

**Theorem (Uniqueness within a set).** Let $L_1, L_2$ be derivatives of $f$ at $x$ within $s$. Then $L_1 v = L_2 v$ for each $v$ in the closure of the span of $T_s(x)$. So if $s$ has unique differentials at $x$, then $L_1 = L_2$.

*Proof.* Let $v \in T_s(x)$, with $c_n$, $d_n$ as in the definition, and $r_i(d) = f(x + d) - f(x) - L_i d$. Then $(L_1 - L_2)(c_n d_n) = c_n\big(r_2(d_n) - r_1(d_n)\big)$. If $d_n = 0$ this is $0$. Otherwise
$$\|c_n r_i(d_n)\| = \|c_n d_n\| \cdot \frac{\|r_i(d_n)\|}{\|d_n\|} \to \|v\| \cdot 0 = 0,$$
because $x + d_n \in s$ and $d_n \to 0$. The left side tends to $(L_1 - L_2)v$ by continuity. So $(L_1 - L_2)v = 0$. The kernel of the continuous linear map $L_1 - L_2$ is a closed subspace that contains $T_s(x)$, so it contains the closure of its span. $\square$

::: mathlib
`HasFDerivWithinAt.fderivWithin` · `Mathlib.Analysis.Calculus.FDeriv.Basic`

`HasFDerivWithinAt f f' s x → UniqueDiffWithinAt 𝕜 s x → fderivWithin 𝕜 f s x = f'`. The uniqueness itself is `UniqueDiffWithinAt.eq`.

<?decl HasFDerivWithinAt.fderivWithin?>
:::

**Theorem (Convex sets).** Let $s \subseteq E$ be a real convex set with nonempty interior. Then $s$ has unique differentials at each point of $s$.

*Proof.* Let $x \in s$ and $y$ in the interior of $s$. For $n \ge 1$ put $d_n = (y - x)/n$ and $c_n = n$. Then $x + d_n = (1 - \frac1n)x + \frac1n y \in s$ by convexity, $d_n \to 0$ and $c_n d_n = y - x$. So $y - x \in T_s(x)$. The set $V = \operatorname{int}(s) - x$ is open and nonempty, so it contains a ball $B(z, \rho)$. For $w \in E$ with $w \neq 0$, both $z$ and $z + \frac{\rho}{2\|w\|}w$ lie in the ball, so $w$ is in the span of $V$. So the span of $T_s(x)$ is all of $E$. $\square$

So a closed interval $[a, b]$, a closed ball and the closed quadrant $[0, \infty)^2$ have unique differentials, and the one-sided derivatives of Volume 15 are derivatives within $[a, b]$.

::: mathlib
`uniqueDiffOn_convex` · `Mathlib.Analysis.Calculus.TangentCone.Real`

`Convex ℝ s → (interior s).Nonempty → UniqueDiffOn ℝ s`. For intervals there are `uniqueDiffOn_Icc` and `uniqueDiffOn_Ici`. Each open set has unique differentials by `IsOpen.uniqueDiffOn`.

<?decl uniqueDiffOn_convex?>
<?decl UniqueDiffOn?>
:::

### Examples

**Counterexample (Directional derivatives without differentiability).** Let $f(x, y) = \frac{x^2 y}{x^4 + y^2}$ for $(x, y) \neq 0$ and $f(0, 0) = 0$. Let $v = (a, b)$. For $t \neq 0$,
$$\frac{f(ta, tb)}{t} = \frac{a^2 b}{t^2 a^4 + b^2}.$$
For $b \neq 0$ this tends to $a^2/b$, and for $b = 0$ it is $0$. So every directional derivative at $0$ exists, with $\partial_v f(0) = a^2/b$ for $b \neq 0$. This is not linear in $v$, so $f$ is not differentiable at $0$. Also $f(x, x^2) = \frac{x^4}{2x^4} = \frac12$ for $x \neq 0$, so $f$ is not continuous at $0$.

**Example (A Jacobian matrix).** The map of polar coordinates $P(r, \theta) = (r\cos\theta, r\sin\theta)$ has continuous partial derivatives, so it is differentiable, with
$$DP(r, \theta) = \begin{pmatrix} \cos\theta & -r\sin\theta \\ \sin\theta & r\cos\theta \end{pmatrix}, \qquad \det DP(r, \theta) = r.$$
At $(r, \theta) = (2, \pi/2)$ this gives $DP(h, k) = (-2k, h)$.

**Example (A gradient and a directional derivative).** Let $f(x, y) = x^2 + 3xy$. Then $\nabla f(x, y) = (2x + 3y, 3x)$, and $\nabla f(1, 1) = (5, 3)$. For the unit vector $v = (\frac35, \frac45)$, $\partial_v f(1, 1) = 5 \cdot \frac35 + 3 \cdot \frac45 = \frac{27}{5}$. By Cauchy-Schwarz, the largest directional derivative over unit vectors is $\|\nabla f(1, 1)\| = \sqrt{34}$.

### The library around it

The files `LineDeriv.*` give the line derivative its own API, parallel to `HasDerivAt`: `HasLineDerivAt.lineDeriv`, `lineDeriv_smul` and `hasLineDerivAt_iff_tendsto_slope_zero`. For derivatives within a set the main lemmas are `HasFDerivWithinAt.mono` (shrink the set), `hasFDerivWithinAt_of_isOpen` (an open set changes nothing) and `HasFDerivWithinAt.hasFDerivAt` (a neighbourhood changes nothing).

The file `FDeriv.Partial` gives the classical test for a map of two variables: if the partial derivatives exist near $u$ and are continuous at $u$, then the map is strictly differentiable at $u$. `hasStrictFDerivAt_uncurry_coprod` states this for `↿f : E₁ × E₂ → F`, with derivative `(↿f₁ u).coprod (↿f₂ u)`. The partial derivatives are given as two functions `f₁` and `f₂`, not computed with `fderiv`. The file `FDeriv.WithLp` does the same work as `FDeriv.Pi` for `PiLp p E`, the product with the $L^p$ norm: `differentiableAt_piLp` and `hasFDerivWithinAt_piLp` reduce the question to the components `(f x).ofLp i`, and `PiLp.hasFDerivAt_apply` differentiates one coordinate. The file `LineDeriv.QuadraticMap` computes the line derivative of a quadratic map: `QuadraticMap.hasLineDerivAt` gives `QuadraticMap.polar f a b` at $a$ in direction $b$, and `QuadraticMap.lineDeriv` states `lineDeriv 𝕜 f = QuadraticMap.polar f`.

The files `TangentCone.*` give more ways to prove `UniqueDiffWithinAt`. On the scalar field, `uniqueDiffWithinAt_iff_accPt` states that the condition holds exactly when $x$ is an accumulation point of $s$, and `tangentConeAt_eq_univ` gives the whole line as tangent cone. `UniqueDiffWithinAt.prod`, `UniqueDiffOn.prod` and `UniqueDiffOn.univ_pi` pass the condition to products, so a box in $\mathbb{R}^n$ is handled one coordinate at a time. In a proper space, `tangentConeAt_nonempty_of_properSpace` gives a nonzero tangent vector at each accumulation point. The file `TangentCone.Seq` describes the cone by sequences: `mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop` asks for scalars $c_n$ with $\|c_n\| \to \infty$ and points $x + d_n \in s$ with $c_n d_n \to y$, and `mem_tangentConeAt_of_pow_smul` uses the points $x + r^n y$ for a fixed $r$ with $0 < \|r\| < 1$.

Common errors of a learner:

- Concluding differentiability from the existence of all directional derivatives. The counterexample shows that even continuity can fail.
- Using `fderivWithin 𝕜 f s x` on a set that does not have unique differentials at `x`. Its value is then an arbitrary choice.
- Forgetting `CompleteSpace` for `gradient`.

### Exercises

1. (A) Compute the Jacobian matrix of $f(x, y, z) = (xyz, x + y^2)$ at $(1, 2, 3)$, and $Df(1, 2, 3)(1, 0, -1)$.
2. (A) Let $g(x, y) = \frac{x^3 y}{x^6 + y^2}$ for $(x, y) \neq 0$ and $g(0) = 0$. Show that every directional derivative of $g$ at $0$ is $0$, so that $v \mapsto \partial_v g(0)$ is linear, and that $g$ is not continuous at $0$.
3. (B) Let $f(x, y) = \sqrt{|xy|}$. Show that $\partial_1 f(0) = \partial_2 f(0) = 0$ and that $f$ is not differentiable at $0$. Hint: the direction $(1, 1)$.
4. (B) Compute the tangent cones at $0$ of $\{(x, y) : y \ge |x|\}$ and of the parabola $\{(x, y) : y = x^2\}$. Which of the two sets has unique differentials at $0$?
5. (B) Let $A$ be a real $n \times n$ matrix. Show that the gradient of $x \mapsto \langle Ax, x\rangle$ is $(A + A^{\mathsf T})x$, and that the gradient of $x \mapsto \|x\|^2$ in a real Hilbert space is $2x$.
6. (C) Let $f : \mathbb{R}^2 \to \mathbb{R}$. Assume that $\partial_1 f$ exists near $x$ and is continuous at $x$, and that $\partial_2 f(x)$ exists. Show that $f$ is differentiable at $x$. Hint: split $f(x + h) - f(x)$ through the point $x + h_2 e_2$.

### Notes and history

René Gateaux studied derivatives in one direction for functionals on spaces of functions, before the First World War. Mathlib uses the tangent cone to give one theory of the derivative on open sets, on closed intervals and on manifolds with boundary.

### Reference

<?reference?>
