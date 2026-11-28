---
title: The mean value inequality
kind: theory
modules:
  - Mathlib.Analysis.Calculus.FDeriv.Norm
  - Mathlib.Analysis.ConstantSpeed
explains:
  E3: []
  E2: [not_differentiableAt_norm_zero, norm_fderiv_norm, DifferentiableAt.fderiv_norm_self, fderiv_norm_smul, differentiableAt_norm_smul]
  E1: [Convex.norm_image_sub_le_of_norm_fderiv_le, Convex.norm_image_sub_le_of_norm_fderiv_le', Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le, Convex.lipschitzOnWith_of_nnNorm_fderiv_le, lipschitzWith_of_nnNorm_fderiv_le, IsOpen.is_const_of_fderiv_eq_zero, is_const_of_fderiv_eq_zero, IsOpen.eqOn_of_fderiv_eq, norm_image_sub_le_of_norm_deriv_le_segment', image_le_of_deriv_right_lt_deriv_boundary, HasFDerivAt.le_of_lipschitz]
families: []
requires: [V17.C01, V17.C02, V15.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The mean value inequality

### Overview

For a real function on $[a, b]$, the mean value theorem of Volume 15, Chapter 3 gives a point $c$ with $f(b) - f(a) = f'(c)(b - a)$. For a map into $\mathbb{R}^2$ this equation fails. What survives is an inequality: if $\|f'\| \le M$ on the segment, then $\|f(b) - f(a)\| \le M(b - a)$. This mean value inequality is the main tool of the rest of the volume. It gives Lipschitz bounds and the estimate $\|f(y) - f(x) - L(y - x)\| \le \sup\|Df - L\|\,\|y - x\|$ that Section 2 and Chapter 6 use.

### Definitions

**Definition (Segment and convex set).** Let $E$ be a real vector space. The *segment* between $x, y \in E$ is $[x, y] = \{x + t(y - x) : t \in [0, 1]\}$. A set $s \subseteq E$ is *convex* if $[x, y] \subseteq s$ for all $x, y \in s$.

**Definition (Lipschitz map).** A map $f : s \to F$ is *$M$-Lipschitz* on $s$ if $\|f(y) - f(x)\| \le M\|y - x\|$ for all $x, y \in s$.

### Theorems and proofs

**Theorem (Mean value inequality for curves).** Let $F$ be a normed space, $a < b$, and $\gamma : [a, b] \to F$ continuous. Assume that $\gamma$ is differentiable at each $t \in (a, b)$ with $\|\gamma'(t)\| \le M$. Then $\|\gamma(b) - \gamma(a)\| \le M(b - a)$.

*Proof.* Fix $\varepsilon > 0$ and put $\varphi(t) = \|\gamma(t) - \gamma(a)\| - (M + \varepsilon)(t - a)$. The function $\varphi$ is continuous on $[a, b]$ and $\varphi(a) = 0$. Let
$$S = \{t \in [a, b] : \varphi(u) \le \varepsilon \text{ for all } u \in [a, t]\}, \qquad c = \sup S.$$
The set $S$ contains $a$ and is an interval. If $c > a$, then $\varphi \le \varepsilon$ on $[a, c)$, and by continuity $\varphi(c) \le \varepsilon$. So $c \in S$ in each case.

Assume $c < b$. If $c = a$: since $\varphi(a) = 0 < \varepsilon$ and $\varphi$ is continuous, $\varphi \le \varepsilon$ on $[a, a + \delta]$ for some $\delta > 0$. So $a + \delta \in S$, against $c = a$. If $a < c < b$: $\gamma$ is differentiable at $c$, so there is $\delta > 0$ with $c + \delta \le b$ and
$$\|\gamma(t) - \gamma(c) - (t - c)\gamma'(c)\| \le \varepsilon(t - c) \quad \text{for } t \in [c, c + \delta].$$
For these $t$, $\|\gamma(t) - \gamma(c)\| \le (M + \varepsilon)(t - c)$, and by the triangle inequality
$$\varphi(t) \le \|\gamma(c) - \gamma(a)\| + (M + \varepsilon)(t - c) - (M + \varepsilon)(t - a) = \varphi(c) \le \varepsilon.$$
So $c + \delta \in S$, against $c = \sup S$. Hence $c = b$, and $\varphi(b) \le \varepsilon$:
$$\|\gamma(b) - \gamma(a)\| \le (M + \varepsilon)(b - a) + \varepsilon.$$
This holds for each $\varepsilon > 0$, so $\|\gamma(b) - \gamma(a)\| \le M(b - a)$. $\square$

The proof uses only the derivative from the right at the points of $(a, b)$, and the hypothesis that the bound holds there.

::: mathlib
`norm_image_sub_le_of_norm_deriv_le_segment'` · `Mathlib.Analysis.Calculus.MeanValue`

`(∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) → (∀ x ∈ Ico a b, ‖f' x‖ ≤ C) → ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a)`. The file proves it from a comparison principle for right derivatives, `image_le_of_deriv_right_lt_deriv_boundary`.

<?decl norm_image_sub_le_of_norm_deriv_le_segment'?>
<?decl image_le_of_deriv_right_lt_deriv_boundary?>
:::

**Theorem (Mean value inequality).** Let $s \subseteq E$ be convex and $f : E \to F$ differentiable at each point of $s$, with $\|Df(z)\| \le M$ for all $z \in s$. Then for all $x, y \in s$,
$$\|f(y) - f(x)\| \le M\|y - x\|.$$
So $f$ is $M$-Lipschitz on $s$.

*Proof.* Let $\gamma(t) = f(x + t(y - x))$ for $t \in [0, 1]$. The map $t \mapsto x + t(y - x)$ has the derivative $y - x$, and its values lie in $s$ by convexity. By the chain rule of Chapter 2, $\gamma$ is differentiable at each $t \in [0, 1]$, so it is continuous, and $\gamma'(t) = Df(x + t(y - x))(y - x)$. Then $\|\gamma'(t)\| \le M\|y - x\|$. Apply the theorem for curves. $\square$

::: mathlib
`Convex.norm_image_sub_le_of_norm_fderiv_le` · `Mathlib.Analysis.Calculus.MeanValue`

`(∀ x ∈ s, DifferentiableAt 𝕜 f x) → (∀ x ∈ s, ‖fderiv 𝕜 f x‖ ≤ C) → Convex ℝ s → x ∈ s → y ∈ s → ‖f y - f x‖ ≤ C * ‖y - x‖`. Here `𝕜` is `ℝ` or `ℂ` (`RCLike`). The variant with `HasFDerivWithinAt` applies on a closed ball. The primed form `Convex.norm_image_sub_le_of_norm_fderiv_le'` is the theorem with a linear term below. The Lipschitz forms `Convex.lipschitzOnWith_of_nnNorm_fderiv_le` and `lipschitzWith_of_nnNorm_fderiv_le` take the bound in `ℝ≥0`.

<?decl Convex.norm_image_sub_le_of_norm_fderiv_le?>
<?decl Convex.norm_image_sub_le_of_norm_fderiv_le'?>
<?decl Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le?>
<?decl Convex.lipschitzOnWith_of_nnNorm_fderiv_le?>
<?decl lipschitzWith_of_nnNorm_fderiv_le?>
:::

**Theorem (Mean value inequality with a linear term).** Let $s$ and $f$ be as above and $L \in L(E, F)$. Assume $\|Df(z) - L\| \le M$ for all $z \in s$. Then $\|f(y) - f(x) - L(y - x)\| \le M\|y - x\|$ for all $x, y \in s$.

*Proof.* Apply the theorem to $g = f - L$. It is differentiable on $s$ with $Dg(z) = Df(z) - L$ by Chapter 2, and $g(y) - g(x) = f(y) - f(x) - L(y - x)$. $\square$

**Theorem (Zero derivative).** Let $U \subseteq E$ be open and connected, and $f$ differentiable on $U$ with $Df(z) = 0$ for all $z \in U$. Then $f$ is constant on $U$.

*Proof.* Fix $x_0 \in U$ and let $A = \{x \in U : f(x) = f(x_0)\}$. Then $x_0 \in A$. The set $A$ is open: for $x \in A$ there is a ball $B(x, r) \subseteq U$, the ball is convex, and the mean value inequality with $M = 0$ gives $f(y) = f(x) = f(x_0)$ for $y \in B(x, r)$. The set $U \setminus A$ is open too: for $x \in U \setminus A$, the same ball gives $f = f(x) \neq f(x_0)$ on $B(x, r)$. Since $U$ is connected, $A = U$. $\square$

The connectedness is needed: on $U = (0, 1) \cup (2, 3)$ the function equal to $0$ on the first interval and $1$ on the second has derivative $0$.

::: mathlib
`IsOpen.is_const_of_fderiv_eq_zero` · `Mathlib.Analysis.Calculus.MeanValue`

`IsOpen s → IsPreconnected s → DifferentiableOn 𝕜 f s → s.EqOn (fderiv 𝕜 f) 0 → x ∈ s → y ∈ s → f x = f y`. The version `is_const_of_fderiv_eq_zero` is for all of `E`, and `IsOpen.eqOn_of_fderiv_eq` compares two maps with the same derivative and one common value.

<?decl IsOpen.is_const_of_fderiv_eq_zero?>
<?decl is_const_of_fderiv_eq_zero?>
<?decl IsOpen.eqOn_of_fderiv_eq?>
:::

**Theorem (Lipschitz bound on the derivative).** If $f$ is $M$-Lipschitz on a neighbourhood of $x$ and differentiable at $x$, then $\|Df(x)\| \le M$.

*Proof.* For $v \in E$, $Df(x)v = \lim_{t \to 0^+} (f(x + tv) - f(x))/t$ by Section 2 of Chapter 1. For small $t > 0$ the quotient has norm at most $M\|tv\|/t = M\|v\|$. So $\|Df(x)v\| \le M\|v\|$. $\square$

::: mathlib
`HasFDerivAt.le_of_lipschitz` · `Mathlib.Analysis.Calculus.FDeriv.Basic`

`HasFDerivAt f f' x → LipschitzWith C f → ‖f'‖ ≤ C`.

<?decl HasFDerivAt.le_of_lipschitz?>
:::

**Theorem (Derivative of the norm).** Let $E$ be a real normed space with $E \neq 0$. Then:

1. the norm is not differentiable at $0$;
2. if the norm is differentiable at $x$, then $D\|\cdot\|(x)x = \|x\|$ and $\|D\|\cdot\|(x)\| = 1$;
3. for $t \neq 0$, the norm is differentiable at $tx$ if and only if it is at $x$, and then $D\|\cdot\|(tx) = \operatorname{sign}(t)\,D\|\cdot\|(x)$.

*Proof.* (1) is the counterexample of Chapter 1: along a line through $0$ the norm is $t \mapsto |t|\,\|v\|$, which has no derivative at $0$ for $v \neq 0$. For (2), $x \neq 0$ by (1). For real $t$ near $0$, $\|x + tx\| = |1 + t|\,\|x\| = (1 + t)\|x\|$, whose derivative at $t = 0$ is $\|x\|$. So $D\|\cdot\|(x)x = \|x\|$ and $\|D\|\cdot\|(x)\| \ge 1$. The norm is $1$-Lipschitz, so $\|D\|\cdot\|(x)\| \le 1$ by the previous theorem. For (3), $\|y\| = |t|\,\|y/t\|$, so the norm near $tx$ is $|t|$ times the composite of the norm with the linear equivalence $y \mapsto y/t$. By the chain rule of Chapter 2 the derivative at $tx$ is $|t| \cdot t^{-1}\,D\|\cdot\|(x) = \operatorname{sign}(t)\,D\|\cdot\|(x)$. $\square$

::: mathlib
`norm_fderiv_norm` · `Mathlib.Analysis.Calculus.FDeriv.Norm`

`[Nontrivial E] → DifferentiableAt ℝ (‖·‖) x → ‖fderiv ℝ (‖·‖) x‖ = 1`. The other parts of the theorem are `not_differentiableAt_norm_zero`, `DifferentiableAt.fderiv_norm_self : fderiv ℝ (‖·‖) x x = ‖x‖`, `differentiableAt_norm_smul` and `fderiv_norm_smul`, with the sign as `SignType.sign t`.

<?decl norm_fderiv_norm?>
<?decl not_differentiableAt_norm_zero?>
<?decl DifferentiableAt.fderiv_norm_self?>
<?decl differentiableAt_norm_smul?>
<?decl fderiv_norm_smul?>
:::

### Examples

**Counterexample (No mean value equation).** Let $\gamma(t) = (\cos t, \sin t)$ on $[0, 2\pi]$. Then $\gamma(2\pi) = \gamma(0)$, but $\|\gamma'(t)\| = 1$ for every $t$. So no $c$ satisfies $\gamma(2\pi) - \gamma(0) = 2\pi\gamma'(c)$. The inequality holds: $0 \le 1 \cdot 2\pi$.

**Example (A Lipschitz constant).** Let $f(x, y) = \sin x + \cos y$ on $\mathbb{R}^2$ with the Euclidean norm. Then $Df(x, y)(h, k) = h\cos x - k\sin y$, and $\|Df(x, y)\| = \sqrt{\cos^2 x + \sin^2 y} \le \sqrt2$ by Cauchy-Schwarz. So $|f(p) - f(q)| \le \sqrt2\,\|p - q\|$. The bound is sharp: at $p = (0, \pi/2)$ the gradient is $(1, -1)$, of norm $\sqrt2$.

**Example (The linear term).** Let $E$ be a real inner product space and $f(x) = \|x\|^2$, with $Df(z)h = 2\langle z, h\rangle$. On the ball $B(x_0, r)$, $\|Df(z) - Df(x_0)\| = 2\|z - x_0\| < 2r$. The theorem with a linear term gives $|f(y) - f(x) - 2\langle x_0, y - x\rangle| \le 2r\|y - x\|$ for $x, y \in B(x_0, r)$.

**Counterexample (A set that is not convex).** Let $U = \{z \in \mathbb{R}^2 : \|z\| > 1\}$ minus the half line $\{(x, 0) : x \le 0\}$, and let $\theta : U \to (-\pi, \pi)$ be the polar angle. Then $\nabla\theta(x, y) = (-y, x)/(x^2 + y^2)$, so $\|D\theta\| = 1/\|z\| < 1$ on $U$. But for $p = (-2, \delta)$ and $q = (-2, -\delta)$ with small $\delta > 0$, $|\theta(p) - \theta(q)|$ is close to $2\pi$, while $\|p - q\| = 2\delta$. The set $U$ is connected but not convex.

### The library around it

The file `Calculus.MeanValue` has its home in Volume 15. It contains the comparison principles for right derivatives, the inequality on segments and on convex sets in all the forms of the derivative, and the theorems on zero derivatives.

The file `Analysis.ConstantSpeed` uses the variation of a path, not its derivative, to measure speed. `HasConstantSpeedOnWith f s l` states that on each interval $[x, y]$ with $x, y \in s$, the variation of $f$ on $s \cap [x, y]$ is $l(y - x)$, and `HasUnitSpeedOn f s` is the case $l = 1$. The main result is `has_unit_speed_naturalParameterization`: a path of locally bounded variation has a unit-speed reparametrization, `naturalParameterization f s a`. `unique_unit_speed` states that this parametrization is unique up to translation among monotone changes of variable. `HasConstantSpeedOnWith.Icc_Icc` glues two adjacent intervals.

Common errors of a learner:

- Looking for a point $c$ with $f(y) - f(x) = Df(c)(y - x)$ for a map into $\mathbb{R}^n$ with $n \ge 2$. Such a point need not exist.
- Applying `Convex.norm_image_sub_le_of_norm_fderiv_le` on a set that is not convex, for example an annulus.
- Forgetting the hypothesis `IsPreconnected` in `IsOpen.is_const_of_fderiv_eq_zero`.
- Forgetting the differentiability hypothesis: the junk value $0$ of `fderiv` satisfies every bound.

### Exercises

1. (A) Show that $f(x, y) = \frac{1}{2}\sin(x + y)$ is $\frac{\sqrt2}{2}$-Lipschitz on $\mathbb{R}^2$ with the Euclidean norm.
2. (A) Let $f : \mathbb{R}^n \to \mathbb{R}^m$ be differentiable with $Df(x) = A$ for all $x$. Show that $f(x) = Ax + b$ for a constant $b$.
3. (B) Let $U \subseteq E$ be open and connected and $f : U \to F$ differentiable with $\|Df(z)\| \le M$ on $U$. Show that $f$ is locally $M$-Lipschitz, and give an example where $f$ is not $M'$-Lipschitz on $U$ for any $M'$. Hint: the last counterexample of the section.
4. (B) Let $f : E \to F$ be differentiable with $\|Df(z) - I\| \le \frac12$ for all $z$, where $E = F$ and $I$ is the identity. Show that $\|f(y) - f(x)\| \ge \frac12\|y - x\|$, so that $f$ is injective.
5. (B) Let $E$ be a real inner product space. Show that the norm is differentiable at $x \neq 0$ with $D\|\cdot\|(x)h = \langle x, h\rangle/\|x\|$, and check the three parts of the theorem on the derivative of the norm.
6. (C) Let $\gamma : [a, b] \to F$ be continuous and have a right derivative $\gamma'_+(t)$ at each $t \in [a, b)$ with $\|\gamma'_+(t)\| \le g'(t)$, where $g$ is a real differentiable function. Show that $\|\gamma(b) - \gamma(a)\| \le g(b) - g(a)$. Hint: replace $(M + \varepsilon)(t - a)$ in the proof by $g(t) - g(a) + \varepsilon(t - a)$.

### Notes and history

The mean value inequality for maps between normed spaces is the form that Jean Dieudonné put at the center of the calculus in *Foundations of Modern Analysis* (1960). He stated it for right derivatives with a real comparison function $g$, in the form of Exercise 6.

### Reference

<?reference?>
