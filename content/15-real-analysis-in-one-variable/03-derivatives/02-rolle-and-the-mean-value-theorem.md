---
title: Rolle's theorem and the mean value theorem
kind: theory
modules:
  - Mathlib.Analysis.Calculus.LocalExtr.Basic
  - Mathlib.Analysis.Calculus.LocalExtr.Rolle
  - Mathlib.Analysis.Calculus.Deriv.MeanValue
  - Mathlib.Analysis.Calculus.MeanValue
  - Mathlib.Analysis.Calculus.Darboux
explains:
  E3: [IsLocalMax.hasDerivAt_eq_zero, exists_hasDerivAt_eq_zero, exists_hasDerivAt_eq_slope, exists_ratio_hasDerivAt_eq_ratio_slope]
  E2: [exists_deriv_eq_zero, monotoneOn_of_deriv_nonneg, strictMonoOn_of_deriv_pos, is_const_of_deriv_eq_zero, Convex.norm_image_sub_le_of_norm_deriv_le, exists_hasDerivWithinAt_eq_of_gt_of_lt]
  E1: auto
families: []
requires: [V02, V13, V15.C01, V15.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Rolle's theorem and the mean value theorem

### Overview

The derivative is defined at one point, but its main use is global: the sign of $f'$ on an interval tells whether $f$ increases, and a bound on $|f'|$ tells how far $f$ can move. The bridge is the mean value theorem: the slope $\frac{f(b) - f(a)}{b - a}$ is the value of $f'$ at some interior point. The proof needs the completeness of $\mathbb{R}$, through the extreme value theorem of Chapter 2. The section proves the theorems of Fermat, Rolle, Lagrange and Cauchy, the consequences for monotonicity, and Darboux's theorem. Section 3 uses the theorem of Cauchy for l'Hôpital's rule.

### Definitions

**Definition (Local extremum).** The point $c$ is a *local maximum* of $f$ if there is $\delta > 0$ with $f(x) \le f(c)$ for all $x$ with $|x - c| < \delta$, and a *local minimum* if $f(x) \ge f(c)$ for these $x$. A *local extremum* is one of the two.

A local extremum is an interior notion. A maximum of $f$ on $[a, b]$ at the end point $a$ is not a local maximum in this sense. For example $f(x) = x$ on $[0, 1]$ has its maximum at $1$ and $f'(1) = 1 \neq 0$.

::: mathlib
`IsLocalMax` · `Mathlib.Topology.Order.LocalExtr`

`IsLocalMax f a` means `∀ᶠ x in 𝓝 a, f x ≤ f a`. It is defined in Volume 13 for any topological space and preorder. The forms `IsLocalMin` and `IsLocalExtr` are similar.

<?decl IsLocalMax?>
:::

**Definition (Monotone function).** A function $f$ on an interval $I$ is *increasing* if $x \le y$ implies $f(x) \le f(y)$, and *strictly increasing* if $x < y$ implies $f(x) < f(y)$. In Mathlib these are `MonotoneOn f I` and `StrictMonoOn f I` (Volume 4).

### Theorems and proofs

**Theorem (Fermat).** If $f$ has a local extremum at $c$ and is differentiable at $c$, then $f'(c) = 0$.

*Proof.* Let $c$ be a local maximum; for a minimum use $-f$. Choose $\delta > 0$ with $f(x) \le f(c)$ for $|x - c| < \delta$. For $c < x < c + \delta$ the slope $\frac{f(x) - f(c)}{x - c}$ has numerator $\le 0$ and denominator $> 0$, so it is $\le 0$, and its limit gives $f'(c) \le 0$. For $c - \delta < x < c$ the denominator is $< 0$, the slope is $\ge 0$, and $f'(c) \ge 0$. So $f'(c) = 0$. $\square$

The converse fails: $x^3$ has derivative $0$ at $0$ and no local extremum there.

::: mathlib
`IsLocalMax.hasDerivAt_eq_zero` · `Mathlib.Analysis.Calculus.LocalExtr.Basic`

`IsLocalMax f a → HasDerivAt f f' a → f' = 0`, with the forms `IsLocalMin.hasDerivAt_eq_zero` and `IsLocalExtr.hasDerivAt_eq_zero`. Mathlib proves the Fréchet form `IsLocalMax.hasFDerivAt_eq_zero` first and gets this one as a special case.

<?decl IsLocalMax.hasDerivAt_eq_zero?>
:::

**Theorem (Rolle).** Let $a < b$, $f$ continuous on $[a, b]$, differentiable on $(a, b)$, and $f(a) = f(b)$. Then $f'(c) = 0$ for some $c \in (a, b)$.

*Proof.* By the extreme value theorem there are $p, q \in [a, b]$ with $f(p) \le f(x) \le f(q)$ on $[a, b]$. If $p$ and $q$ are both end points, then $f(p) = f(q) = f(a)$, so $f$ is constant and $f' = 0$ on $(a, b)$. Otherwise one of them, $c$, lies in $(a, b)$. Since $(a, b)$ is a neighbourhood of $c$, $c$ is a local extremum, and Fermat's theorem gives $f'(c) = 0$. $\square$

::: mathlib
`exists_hasDerivAt_eq_zero` · `Mathlib.Analysis.Calculus.LocalExtr.Rolle`

From `a < b`, `ContinuousOn f (Icc a b)`, `f a = f b` and `∀ x ∈ Ioo a b, HasDerivAt f (f' x) x` it gives `∃ c ∈ Ioo a b, f' c = 0`. The variant `exists_hasDerivAt_eq_zero'` replaces continuity on `Icc a b` by equal limits at `a` and `b`.

<?decl exists_hasDerivAt_eq_zero?>
:::

::: mathlib
`exists_deriv_eq_zero` · `Mathlib.Analysis.Calculus.LocalExtr.Rolle`

The `deriv` form has no differentiability hypothesis. If `f` is not differentiable at an interior point `c`, then `deriv f c = 0` by the junk value, and `c` satisfies the conclusion. So the point may be a corner, not a critical point.

<?decl exists_deriv_eq_zero?>
:::

**Theorem (Mean value theorem, Lagrange).** Let $a < b$, $f$ continuous on $[a, b]$ and differentiable on $(a, b)$. Then there is $c \in (a, b)$ with $f'(c) = \frac{f(b) - f(a)}{b - a}$.

*Proof.* Let $s$ be this slope and $h(x) = f(x) - f(a) - s(x - a)$. Then $h$ satisfies the hypotheses of Rolle, with $h(a) = 0 = h(b)$ and $h' = f' - s$. Rolle gives $c$ with $h'(c) = 0$, that is $f'(c) = s$. $\square$

::: mathlib
`exists_hasDerivAt_eq_slope` · `Mathlib.Analysis.Calculus.Deriv.MeanValue`

`∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a)` under the hypotheses of the theorem. Mathlib derives it from the Cauchy form with `g = id`. The `deriv` form `exists_deriv_eq_slope` needs `DifferentiableOn ℝ f (Ioo a b)`. For vector valued functions there is no such point in general, and Mathlib has only inequalities.

<?decl exists_hasDerivAt_eq_slope?>
:::

**Theorem (Mean value theorem, Cauchy).** Let $a < b$ and $f, g$ continuous on $[a, b]$ and differentiable on $(a, b)$. Then there is $c \in (a, b)$ with
$$\big(g(b) - g(a)\big) f'(c) = \big(f(b) - f(a)\big) g'(c).$$
If also $g' \neq 0$ on $(a, b)$, then $g(b) \neq g(a)$ and $\frac{f'(c)}{g'(c)} = \frac{f(b) - f(a)}{g(b) - g(a)}$.

*Proof.* Let $h(x) = (g(b) - g(a)) f(x) - (f(b) - f(a)) g(x)$. Expanding gives $h(a) = g(b) f(a) - f(b) g(a) = h(b)$. Rolle gives $c \in (a, b)$ with $0 = h'(c) = (g(b) - g(a)) f'(c) - (f(b) - f(a)) g'(c)$. If $g' \neq 0$ on $(a, b)$ and $g(b) = g(a)$, Rolle for $g$ gives a zero of $g'$, which is excluded. So $g(b) - g(a) \neq 0$ and $g'(c) \neq 0$, and division gives the second claim. $\square$

With $g(x) = x$ this is the theorem of Lagrange. Applying Lagrange to $f$ and $g$ separately does not prove it, because the two points $c_1$ and $c_2$ differ.

::: mathlib
`exists_ratio_hasDerivAt_eq_ratio_slope` · `Mathlib.Analysis.Calculus.Deriv.MeanValue`

The cross multiplied form `(g b - g a) * f' c = (f b - f a) * g' c`, which needs no hypothesis on `g'`.

<?decl exists_ratio_hasDerivAt_eq_ratio_slope?>
:::

**Theorem (Monotonicity from the derivative).** Let $f$ be continuous on an interval $I$ and differentiable at each interior point $x$ of $I$.

1. If $f'(x) \ge 0$ for each such $x$, then $f$ is increasing on $I$.
2. If $f'(x) > 0$ for each such $x$, then $f$ is strictly increasing on $I$.
3. If $f'(x) = 0$ for each such $x$, then $f$ is constant on $I$.
4. If $|f'(x)| \le M$ for each such $x$, then $|f(y) - f(x)| \le M |y - x|$ for $x, y \in I$.

*Proof.* Let $x < y$ in $I$. Then $[x, y] \subseteq I$ because $I$ is an interval, and $(x, y)$ consists of interior points. The mean value theorem gives $c \in (x, y)$ with $f(y) - f(x) = f'(c)(y - x)$. Since $y - x > 0$, the sign of $f(y) - f(x)$ is the sign of $f'(c)$, which gives parts 1 to 3, and $|f(y) - f(x)| = |f'(c)|\,|y - x| \le M|y - x|$ gives part 4. $\square$

The interval is needed: on $\mathbb{R} \setminus \{0\}$ the function $-1$ for $x < 0$ and $1$ for $x > 0$ has derivative $0$ and is not constant.

::: mathlib
`monotoneOn_of_deriv_nonneg` · `Mathlib.Analysis.Calculus.Deriv.MeanValue`

Part 1 on a convex set `D`, with `ContinuousOn f D`, `DifferentiableOn ℝ f (interior D)` and `0 ≤ deriv f x` on `interior D`. The differentiability is needed, because the junk value `0` satisfies `0 ≤ deriv f x`. The decreasing form is `antitoneOn_of_deriv_nonpos`.

<?decl monotoneOn_of_deriv_nonneg?>
:::

::: mathlib
`strictMonoOn_of_deriv_pos` · `Mathlib.Analysis.Calculus.Deriv.MeanValue`

Part 2, with no differentiability hypothesis: `0 < deriv f x` forces `deriv f x ≠ 0`, so `f` is differentiable at `x`.

<?decl strictMonoOn_of_deriv_pos?>
:::

::: mathlib
`is_const_of_deriv_eq_zero` · `Mathlib.Analysis.Calculus.MeanValue`

Part 3 on the whole line: `Differentiable 𝕜 f → (∀ x, deriv f x = 0) → ∀ x y, f x = f y`.

<?decl is_const_of_deriv_eq_zero?>
:::

::: mathlib
`Convex.norm_image_sub_le_of_norm_deriv_le` · `Mathlib.Analysis.Calculus.MeanValue`

Part 4 on a convex set, for values in any normed space: if `‖deriv f x‖ ≤ C` on `s`, then `‖f y - f x‖ ≤ C * ‖y - x‖`. Its proof does not use the mean value equality, which fails for vector values.

<?decl Convex.norm_image_sub_le_of_norm_deriv_le?>
:::

**Theorem (Darboux).** Let $f$ be differentiable on $[a, b]$, with one-sided derivatives at the end points. If $m$ lies strictly between $f'(a)$ and $f'(b)$, then $f'(c) = m$ for some $c \in (a, b)$.

*Proof.* Let $f'(a) < m < f'(b)$; for the other order use $-f$ and $-m$. Let $g(x) = f(x) - mx$, so $g'(a) < 0 < g'(b)$. By the extreme value theorem $g$ has a minimum on $[a, b]$ at some $c$. Since the right derivative $g'(a)$ is negative, the slope $\frac{g(x) - g(a)}{x - a}$ is negative for $x$ close to $a$ on the right, so $g(x) < g(a)$ there, and $c \neq a$. In the same way $g'(b) > 0$ gives $g(x) < g(b)$ for $x$ close to $b$ on the left, and $c \neq b$. So $c \in (a, b)$ is a local minimum, and Fermat gives $g'(c) = 0$. $\square$

So a function with a jump, such as the sign function, is not a derivative on an interval, while the discontinuous derivative of $x^2 \sin(1/x)$ still has the intermediate value property.

::: mathlib
`exists_hasDerivWithinAt_eq_of_gt_of_lt` · `Mathlib.Analysis.Calculus.Darboux`

The theorem with derivatives within `Icc a b`: if `f' a < m < f' b`, then `m ∈ f' '' Ioo a b`. The set form `Convex.image_deriv` says that `deriv f '' s` is convex.

<?decl exists_hasDerivWithinAt_eq_of_gt_of_lt?>
:::

### Examples

**Example (A Lipschitz bound for the sine).** The derivative of $\sin$ is $\cos$, and $|\cos t| \le 1$ (Chapter 6). Part 4 on $\mathbb{R}$ gives $|\sin x - \sin y| \le |x - y|$, and with $y = 0$, $|\sin x| \le |x|$. In Mathlib this is `Real.abs_sin_sub_sin_le`.

**Example (An estimate of a square root).** The mean value theorem for $\sqrt{x}$ on $[100, 101]$ gives $c \in (100, 101)$ with $\sqrt{101} - 10 = \frac{1}{2\sqrt c}$. Since $10 < \sqrt c < 11$, $10.045 < \sqrt{101} < 10.05$.

**Example (Exactly one root).** Let $p(x) = x^3 + x - 1$. Since $p(0) < 0 < p(1)$, $p$ has a root in $(0, 1)$. Since $p'(x) = 3x^2 + 1 > 0$, $p$ is strictly increasing by part 2, and it has no other root.

**Counterexample (Rolle without differentiability).** The function $|x|$ on $[-1, 1]$ is continuous with equal values at $\pm 1$, but its derivative is $\pm 1$ where it exists. So no $c$ has $f'(c) = 0$. The lemma `exists_deriv_eq_zero` still gives $c = 0$, the junk value.

**Counterexample (Rolle without continuity at an end point).** Let $f(x) = x$ on $[0, 1)$ and $f(1) = 0$. Then $f(0) = f(1)$ and $f' = 1$ on $(0, 1)$. The proof fails at the extreme value theorem: $f$ has no maximum on $[0, 1]$.

### The library around it

The real mean value theorems are in `Mathlib.Analysis.Calculus.Deriv.MeanValue`, and the inequalities for vector valued functions are in `Mathlib.Analysis.Calculus.MeanValue`. The names follow the pattern `exists_<form>_eq_<conclusion>`, and the monotonicity results come in the families `monotoneOn_of_deriv_nonneg`, `antitoneOn_of_deriv_nonpos`, `strictMonoOn_of_deriv_pos` and `strictAntiOn_of_deriv_neg`, each with a global form without `On`. The file `Mathlib.Analysis.Calculus.Monotone` proves the theorem of Lebesgue that a monotone function is differentiable almost everywhere.

Common errors of a learner:

- Applying Fermat's theorem at an end point of the interval.
- Forgetting continuity on the closed interval $[a, b]$ in Rolle and in the mean value theorem.
- Concluding that $f$ is constant from $f' = 0$ on a set that is not an interval.
- Treating the point of the `deriv` form of Rolle's theorem as a critical point.

### Exercises

1. (A) Find the point $c$ of the mean value theorem for $x^3$ on $[0, 2]$.
2. (A) Show that $x^5 + 3x + 1$ has exactly one real root.
3. (A) Show that $|\sqrt{x} - \sqrt{y}| \le \frac{1}{2}|x - y|$ for $x, y \ge 1$.
4. (B) Let $f$ be twice differentiable on $[a, b]$ with $f(a) = f(b) = f(c) = 0$ for some $c \in (a, b)$. Show that $f''(\xi) = 0$ for some $\xi \in (a, b)$.
5. (B) Let $f$ be continuous on $[a, b]$, differentiable on $(a, b)$, and $f'(x) \to L$ as $x \to a^+$. Show that the right derivative of $f$ at $a$ is $L$. Hint: the mean value theorem on $[a, x]$.
6. (C) Let $\gamma(t) = (\cos t, \sin t)$ on $[0, 2\pi]$. Show that no $c$ has $2\pi\gamma'(c) = \gamma(2\pi) - \gamma(0)$. Hint: $|\gamma'(c)| = 1$.
7. (C) Let $f$ be differentiable on an interval with $f'$ increasing. Show that $f$ is convex. Hint: compare the slopes on $[x, z]$ and $[z, y]$ by the mean value theorem.

### Notes and history

Rolle stated his theorem for polynomials in 1691 with an algebraic proof. The mean value theorem is in Lagrange's *Théorie des fonctions analytiques* (1797), the form with two functions in Cauchy (1823), and Darboux's theorem in a memoir of 1875. In Mathlib, `Mathlib.Analysis.Calculus.Deriv.MeanValue` has the authors Yury Kudryashov and Sébastien Gouëzel, and `Mathlib.Analysis.Calculus.Darboux` the author Yury Kudryashov.

### Reference

<?reference?>
