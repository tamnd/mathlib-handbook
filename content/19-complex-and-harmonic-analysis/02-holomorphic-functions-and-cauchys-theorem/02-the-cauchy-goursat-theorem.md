---
title: The Cauchy-Goursat theorem
kind: theory
modules:
  - Mathlib.Analysis.Complex.CauchyIntegral
  - Mathlib.Analysis.Complex.HasPrimitives
explains:
  E3: [Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable, Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable, Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable, DifferentiableOn.isExactOn_ball]
  E2: [Complex.integral_boundary_rect_eq_zero_of_differentiableOn, Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn, Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable, Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable, DiffContOnCl.circleIntegral_eq_zero, Complex.wedgeIntegral, Complex.wedgeIntegral_add_wedgeIntegral_eq, Complex.IsConservativeOn, Complex.IsExactOn, DifferentiableOn.isConservativeOn, Complex.IsConservativeOn.hasDerivAt_wedgeIntegral, Complex.IsConservativeOn.isExactOn_ball, Differentiable.isExactOn_univ, Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn, Complex.IsExactOn.differentiableOn]
  E1: auto
families: []
requires: [V19.C01, V17.C02, V18.C08]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Cauchy-Goursat theorem

### Overview

Cauchy's theorem says that the integral of a holomorphic function around a closed curve is zero when the function is holomorphic inside the curve. This section proves the theorem for the curves that the rest of the volume needs: the boundary of a rectangle and a circle. The proof for rectangles is Goursat's: it does not need the continuity of $f'$. An exponential change of variables gives circles and annuli, and the rectangle case gives primitives on discs.

The section uses Section 1 and the interval integral of Volume 18, Chapter 8.

### Definitions

For $z, w \in \mathbb{C}$, the *rectangle* with opposite corners $z$ and $w$ is the set of $\zeta$ with $\operatorname{Re}\zeta$ between $\operatorname{Re} z$ and $\operatorname{Re} w$ and $\operatorname{Im}\zeta$ between $\operatorname{Im} z$ and $\operatorname{Im} w$.

**Definition (Boundary integral of a rectangle).** Let $z = a + ic$ and $w = b + id$, and let $f$ be continuous on the rectangle. Put
$$\eta(f; z, w) = \int_a^b f(x + ic)\,dx - \int_a^b f(x + id)\,dx + i\int_c^d f(b + iy)\,dy - i\int_c^d f(a + iy)\,dy.$$

For $a < b$ and $c < d$, this is the integral of $f$ along the four sides, in the counterclockwise order: bottom, right, top, left.

**Definition (Circle integral).** For $c \in \mathbb{C}$ and $R > 0$, the integral of $f$ over the circle $C(c, R)$ is
$$\oint_{C(c,R)} f(z)\,dz = \int_0^{2\pi} f(c + Re^{i\theta})\, iRe^{i\theta}\,d\theta.$$

**Definition (Primitive).** A *primitive* of $f$ on an open set $U$ is a function $F$, complex differentiable on $U$, with $F' = f$ on $U$.

::: mathlib
`circleIntegral` · `Mathlib.MeasureTheory.Integral.CircleIntegral`

The circle integral is `circleIntegral f c R`, written `∮ z in C(c, R), f z`. It is built from `circleMap c R θ = c + R * exp (θ * I)`. The rectangle integral has no name: Mathlib writes out the four integrals.

<?decl circleIntegral?>
:::

### Theorems and proofs

**Lemma (Integral of a derivative).** If $F$ is complex differentiable on an open set containing the rectangle with corners $z, w$, and $F'$ is continuous there, then $\eta(F'; z, w) = 0$.

*Proof.* By the chain rule, $x \mapsto F(x + ic)$ has derivative $F'(x + ic)$, and $y \mapsto F(b + iy)$ has derivative $iF'(b + iy)$. The fundamental theorem of calculus (Volume 18, Chapter 8) gives
$$\eta(F'; z, w) = [F(b + ic) - F(a + ic)] - [F(b + id) - F(a + id)] + [F(b + id) - F(b + ic)] - [F(a + id) - F(a + ic)].$$
Every term appears twice with opposite signs. $\square$

**Theorem (Goursat).** Let $f$ be complex differentiable at every point of the rectangle $Q$ with corners $z, w$, and continuous on $Q$. Then $\eta(f; z, w) = 0$.

*Proof.* Write $\eta(Q)$ for the boundary integral over a rectangle $Q$, let $p$ be the perimeter of $Q$ and $d$ its diameter. Cut $Q$ into four congruent rectangles $Q^1, \dots, Q^4$ by the two midlines. Each interior edge is traversed twice, in opposite directions, so
$$\eta(Q) = \eta(Q^1) + \eta(Q^2) + \eta(Q^3) + \eta(Q^4).$$
Choose $Q_1$ among them with $|\eta(Q_1)| \ge |\eta(Q)|/4$. Repeat with $Q_1$ in place of $Q$. This gives nested rectangles $Q \supseteq Q_1 \supseteq Q_2 \supseteq \cdots$ with
$$|\eta(Q_n)| \ge 4^{-n}|\eta(Q)|, \qquad \operatorname{perimeter}(Q_n) = 2^{-n}p, \qquad \operatorname{diam}(Q_n) = 2^{-n}d.$$
The $Q_n$ are compact and nested, so their intersection contains a point $\zeta_0 \in Q$. Let $\varepsilon > 0$. Since $f$ is complex differentiable at $\zeta_0$, there is $\delta > 0$ such that
$$|f(\zeta) - f(\zeta_0) - f'(\zeta_0)(\zeta - \zeta_0)| \le \varepsilon|\zeta - \zeta_0| \quad \text{for } \zeta \in Q,\ |\zeta - \zeta_0| < \delta.$$
Take $n$ with $2^{-n} d < \delta$. Then $Q_n$ lies in the disc of radius $\delta$ about $\zeta_0$. By the lemma, the affine function $f(\zeta_0) + f'(\zeta_0)(\zeta - \zeta_0)$, the derivative of a polynomial, has boundary integral $0$ over $Q_n$. So $\eta(Q_n)$ is the boundary integral of the remainder, which is bounded by $\varepsilon \cdot 2^{-n} d$ on $\partial Q_n$. Bounding each side integral by length times supremum,
$$4^{-n}|\eta(Q)| \le |\eta(Q_n)| \le 2^{-n}p \cdot \varepsilon\, 2^{-n} d.$$
Hence $|\eta(Q)| \le \varepsilon p d$ for every $\varepsilon > 0$, and $\eta(Q) = 0$. A degenerate $Q$ is trivial. $\square$

::: mathlib
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` · `Mathlib.Analysis.Complex.CauchyIntegral`

For `f : ℂ → E`, corners `z w` and a countable `s`, the hypotheses are `ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im)` and `DifferentiableAt ℂ f x` for every `x` in the open rectangle outside `s`. The conclusion is the four integrals of the definition, summed to `0`. Section 3 uses the countable set for $(f(z) - f(w))/(z - w)$. Mathlib does not quadrisect: it proves a Green-type formula, `Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`, and the Cauchy-Riemann equations kill the area term. The plain version is `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.

<?decl Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable?>
:::

**Theorem (Annulus).** Let $0 < r \le R$, and let $f$ be continuous on the closed annulus $r \le |z - c| \le R$ and holomorphic on the open annulus. Then
$$\oint_{C(c,R)} f(z)\,dz = \oint_{C(c,r)} f(z)\,dz.$$

*Proof.* Put $g(\zeta) = e^{\zeta} f(c + e^{\zeta})$. For $\zeta = s + it$ with $\log r \le s \le \log R$, the point $c + e^{\zeta}$ lies in the closed annulus, so $g$ is continuous on the rectangle $Q$ with corners $\log r$ and $\log R + 2\pi i$. Goursat's theorem, in the form that allows a continuous extension to the boundary (see the box), gives $\eta(g; \log r, \log R + 2\pi i) = 0$. The two horizontal integrals cancel, because $g(s + 2\pi i) = g(s)$ by the periodicity of $\exp$. The vertical integrals are
$$i\int_0^{2\pi} e^{\log R + it} f(c + Re^{it})\,dt = \int_0^{2\pi} f(c + Re^{it})\, iRe^{it}\,dt = \oint_{C(c,R)} f,$$
and the same for $r$. So $\oint_{C(c,R)} f - \oint_{C(c,r)} f = 0$. $\square$

**Theorem (Cauchy's theorem for a disc).** Let $f$ be continuous on the closed disc $|z - c| \le R$ and holomorphic on the open disc. Then $\oint_{C(c,R)} f = 0$.

*Proof.* Let $M = \sup |f|$ on the closed disc, finite by compactness. For $0 < r < R$ the annulus theorem gives $\oint_{C(c,R)} f = \oint_{C(c,r)} f$. The circle $C(c, r)$ has length $2\pi r$, so $|\oint_{C(c,r)} f| \le 2\pi r M$. Let $r \to 0$. $\square$

::: mathlib
`Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable` · `Mathlib.Analysis.Complex.CauchyIntegral`

The hypotheses are `0 ≤ R`, `s.Countable`, `ContinuousOn f (closedBall c R)` and `∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z`; the conclusion is `∮ z in C(c, R), f z = 0`. The short form is `DiffContOnCl.circleIntegral_eq_zero`. The annulus theorem is `Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`. The interior version of Goursat used there is `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`.

<?decl Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable?>
<?decl Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable?>
:::

For $z, w \in \mathbb{C}$, the *wedge integral* $W(z, w; f)$ is the integral of $f$ along the horizontal segment from $z$ to $\operatorname{Re} w + i\operatorname{Im} z$, followed by the vertical segment to $w$.

**Theorem (Primitives on a disc).** Let $f$ be holomorphic on the open disc $D = D(c, r)$. Then $F(w) = W(c, w; f)$ is a primitive of $f$ on $D$.

*Proof.* Fix $w \in D$. For $\zeta \in D$, the rectangle with corners $c$ and $\zeta$ lies in $D$: its points $\xi$ satisfy $|\operatorname{Re}(\xi - c)| \le |\operatorname{Re}(\zeta - c)|$ and $|\operatorname{Im}(\xi - c)| \le |\operatorname{Im}(\zeta - c)|$, so $|\xi - c| \le |\zeta - c|$. Let $h$ be small. Compare the paths of $F(w + h)$ and $F(w) + W(w, w + h; f)$. They share the vertical segment ending at $w + h$ and the part of the bottom edge from $c$ to $\operatorname{Re} w + i \operatorname{Im} c$. The rest forms the boundary of the rectangle with corners $\operatorname{Re} w + i\operatorname{Im} c$ and $\operatorname{Re}(w + h) + i\operatorname{Im} w$. For small $h$, this rectangle lies in $D$: its points are no farther from $c$ than the farther of the two points $w$ and $\operatorname{Re}(w + h) + i \operatorname{Im} w$, and both are in $D$. By Goursat its boundary integral is $0$, so
$$F(w + h) - F(w) = W(w, w + h; f).$$
The two segments of $W(w, w + h; f)$ have lengths $|\operatorname{Re} h|$ and $|\operatorname{Im} h|$, both at most $|h|$, and $W(w, w+h; 1) = h$. So
$$|F(w + h) - F(w) - f(w)h| = |W(w, w + h; f - f(w))| \le 2|h| \sup_{|\xi - w| \le |h|} |f(\xi) - f(w)|.$$
The supremum tends to $0$ as $h \to 0$ by the continuity of $f$ at $w$. Hence $F'(w) = f(w)$. $\square$

::: mathlib
`DifferentiableOn.isExactOn_ball` · `Mathlib.Analysis.Complex.HasPrimitives`

The statement is `DifferentiableOn ℂ f (ball c r) → IsExactOn f (ball c r)`, for `f : ℂ → E` with `E` complete. The wedge integral is `Complex.wedgeIntegral c w f`, and `Complex.wedgeIntegral_add_wedgeIntegral_eq` says that `wedgeIntegral z w f + wedgeIntegral w z f` is the boundary integral of the rectangle. `Complex.IsConservativeOn f U` asks that it vanish for rectangles in `U`. The steps are `DifferentiableOn.isConservativeOn` and `Complex.IsConservativeOn.hasDerivAt_wedgeIntegral`. For an entire function, `Differentiable.isExactOn_univ` gives a primitive on `ℂ`. The converse, `Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`, is Morera's theorem; it needs Section 3.

<?decl DifferentiableOn.isExactOn_ball?>
:::

### Examples

**Example.** For $n \in \mathbb{Z}$, compute $\oint_{C(0,R)} z^n\,dz = \int_0^{2\pi} R^n e^{in\theta} iRe^{i\theta}\,d\theta = iR^{n+1}\int_0^{2\pi} e^{i(n+1)\theta}\,d\theta$. The last integral is $2\pi$ for $n = -1$ and $0$ otherwise. So $\oint z^{-1}\,dz = 2\pi i$. So $z^{-1}$ has no primitive on $\mathbb{C} \setminus \{0\}$.

**Example.** For $f(z) = \bar z$ and $Q$ the unit square, $\eta(f; 0, 1 + i) = 2i$. Indeed the bottom gives $\int_0^1 x\,dx = 1/2$, the top $-\int_0^1 (x - i)\,dx = -1/2 + i$, the right side $i\int_0^1 (1 - iy)\,dy = i + 1/2$, and the left side $-i\int_0^1 (-iy)\,dy = -1/2$. The sum is $2i$, twice the area. So Goursat needs complex differentiability.

### The library around it

Common errors of a learner:

- Using `DifferentiableOn ℂ f (closedBall c R)` when only the open ball is known. `DiffContOnCl` and the off-countable forms are made for this.

### Exercises

1. (A) Compute $\oint_{C(1,2)} (z - 1)^{-2}\,dz$ and $\oint_{C(0,1)} \bar z\,dz$. Hint: on the unit circle $\bar z = 1/z$.
2. (B) Let $f$ be entire. Show that $\oint_{C(c,R)} f = 0$ for all $c, R$, using the primitive. Hint: differentiate $\theta \mapsto F(c + Re^{i\theta})$.
3. (B) Show that $\oint_{C(0,R)} \frac{dz}{z^2 + 1}$ is the same for all $R > 1$, and that it tends to $0$ as $R \to \infty$. Conclude that it is $0$. Hint: the annulus theorem, and $|z^2 + 1| \ge R^2 - 1$ on the circle.
4. (B) Compute $\eta(\bar z; z, w)$ for any rectangle, and show that it is $2i$ times the area.
5. (C) Let $f$ be continuous on $\mathbb{C}$ and holomorphic outside the real axis. Show that $f$ has a primitive on every disc. Hint: a rectangle that meets the axis is a limit of rectangles that do not.

### Notes and history

Cauchy proved the integral theorem under the assumption that $f'$ is continuous. Goursat removed this assumption in 1900 with the subdivision argument above. Morera proved the converse in 1886.

### Reference

<?reference?>
