---
title: Distances and angles
kind: theory
modules:
  - Mathlib.Geometry.Euclidean.Basic
  - Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
  - Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
  - Mathlib.Geometry.Euclidean.Angle.Unoriented.Conformal
  - Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
  - Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
explains:
  E3: [InnerProductGeometry.angle, EuclideanGeometry.angle, InnerProductGeometry.angle_le_angle_add_angle, EuclideanGeometry.angle_le_angle_add_angle, InnerProductGeometry.angle_eq_zero_iff, InnerProductGeometry.angle_eq_pi_iff, EuclideanGeometry.angle_eq_pi_iff_sbtw]
  E2: [InnerProductGeometry.angle_zero_left, InnerProductGeometry.IsConformalMap.preserves_angle, InnerProductGeometry.norm_ofLp_crossProduct, AffineIsometry.angle_map, EuclideanGeometry.angle_self_left, EuclideanGeometry.angle_eq_zero_iff_ne_and_wbtw]
  E1: auto
families: []
requires: [V07, V13, V15.C06, V16.C06, V22.C01, V22.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Distances and angles

### Overview

An affine space has no length and no angle. A Euclidean affine space adds both through an inner product on the vectors (Volume 16, Chapter 6). This section defines the angle, links the angles $0$ and $\pi$ to the betweenness of Chapter 2, and proves the triangle inequality for angles.

### Definitions

Let $V$ be a real inner product space and $P$ an affine space over $V$. For $p, q \in P$ write $p - q \in V$ for the vector from $q$ to $p$, as in Chapter 1.

**Definition (Euclidean affine space).** A *Euclidean affine space* is an affine space $P$ over a real inner product space $V$, with the metric $d(p, q) = \|p - q\|$.

::: mathlib
`NormedAddTorsor` · `Mathlib.Analysis.Normed.Group.AddTorsor`

Mathlib has no structure for a Euclidean affine space. A file in `Mathlib.Geometry.Euclidean` opens with the instances `[NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]`. The last one makes `P` a torsor of `V` with `dist p q = ‖p -ᵥ q‖`.

<?decl NormedAddTorsor?>
:::

**Definition (Angle between vectors).** Let $x, y \in V$. If $x \ne 0$ and $y \ne 0$, the *angle* between them is
$$\angle(x, y) = \arccos \frac{\langle x, y\rangle}{\|x\|\,\|y\|} \in [0, \pi].$$
If $x = 0$ or $y = 0$, put $\angle(x, y) = \pi/2$.

By Cauchy-Schwarz the quotient lies in $[-1, 1]$, where $\arccos$ inverts $\cos$ on $[0, \pi]$ (Volume 15, Chapter 6).

::: mathlib
`InnerProductGeometry.angle` · `Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic`

`InnerProductGeometry.angle x y` is `Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))`. Division by zero gives zero in Lean and `arccos 0 = π / 2`, so the convention for a zero vector comes out of the formula; `angle_zero_left` records it.

<?decl InnerProductGeometry.angle?>
:::

**Definition (Angle at a point).** For $a, b, c \in P$ the *angle at* $b$ is $\angle abc = \angle(a - b, c - b)$.

If $a = b$ or $c = b$, then $\angle abc = \pi/2$.

::: mathlib
`EuclideanGeometry.angle` · `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine`

`EuclideanGeometry.angle p₁ p₂ p₃` is `InnerProductGeometry.angle (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)`, with the scoped notation `∠ p₁ p₂ p₃` after `open EuclideanGeometry`. The vertex is the middle argument. `angle_self_left` gives `∠ p₀ p₀ p = π / 2`.

<?decl EuclideanGeometry.angle?>
:::

### Theorems and proofs

**Theorem (Basic properties).** For all $x, y \in V$:

1. $\angle(x, y) = \angle(y, x)$ and $0 \le \angle(x, y) \le \pi$.
2. $\langle x, y\rangle = \|x\|\,\|y\| \cos\angle(x, y)$.
3. $\angle(x, -y) = \pi - \angle(x, y)$, and $\angle(x, r y) = \angle(x, y)$ for $r > 0$.
4. $\langle x, y\rangle = 0$ if and only if $\angle(x, y) = \pi/2$.

*Proof.* Let $t$ be the quotient in the definition. (1) The real inner product is symmetric, and $\arccos$ takes values in $[0, \pi]$. (2) If $x = 0$ or $y = 0$ both sides are $0$. Otherwise $t \in [-1, 1]$ by Cauchy-Schwarz, so $\cos(\arccos t) = t$. Multiply by $\|x\|\,\|y\|$. (3) The quotient for $(x, -y)$ is $-t$, and $\arccos(-t) = \pi - \arccos t$. For a zero vector both sides are $\pi/2$. The quotient for $(x, ry)$ is $r\langle x, y\rangle / (r\|x\|\,\|y\|) = t$. (4) For a zero vector both sides hold. Otherwise $\arccos$ is injective on $[-1, 1]$, so $\angle(x, y) = \pi/2$ if and only if $t = 0$. $\square$

**Theorem (Angles $0$ and $\pi$).** $\angle(x, y) = 0$ if and only if $x \ne 0$ and $y = r x$ for some $r > 0$. Also $\angle(x, y) = \pi$ if and only if $x \ne 0$ and $y = r x$ for some $r < 0$.

*Proof.* If $y = r x$ with $x \ne 0$ and $r > 0$, then $t = r\|x\|^2 / (r\|x\|^2) = 1$ and $\arccos 1 = 0$. Conversely let $\angle(x, y) = 0$. Then $x, y \ne 0$, since otherwise the angle is $\pi/2$. By (2), $\langle x, y\rangle = \|x\|\,\|y\|$. Then
$$\bigl\| \|y\| x - \|x\| y \bigr\|^2 = 2\|x\|^2\|y\|^2 - 2\|x\|\,\|y\|\langle x, y\rangle = 0,$$
so $y = r x$ with $r = \|y\| / \|x\| > 0$. The case $\pi$ follows from the case $0$ for $x$ and $-y$, by (3). $\square$

Chapter 2 defined $\operatorname{Sbtw}(a, b, c)$: $b$ lies on the segment $[a, c]$ and differs from $a$ and $c$.

**Corollary (Straight angles).** $\angle abc = \pi$ if and only if $b$ is strictly between $a$ and $c$. Then $d(a, c) = d(a, b) + d(b, c)$.

*Proof.* By the theorem, $\angle abc = \pi$ if and only if $a \ne b$ and $c - b = -s(a - b)$ with $s > 0$. This gives $b = \frac{1}{1+s} c + \frac{s}{1+s} a$, a point of the open segment different from $a$ and $c$. Conversely, if $b = (1-t)a + tc$ with $0 < t < 1$ and $a \ne c$, then $a - b = t(a - c)$ and $c - b = -(1-t)(a - c)$, so $c - b = -\frac{1-t}{t}(a - b)$. For the distances, $a - c = (a - b) + (b - c)$ is a sum of two vectors that are positive multiples of each other, so the norms add. $\square$

The same method shows that three points are collinear if and only if two of them are equal or $\angle abc \in \{0, \pi\}$. So each angle of a non-collinear triple lies in $(0, \pi)$.

**Theorem (Invariance).** A linear isometry $f$ satisfies $\angle(f x, f y) = \angle(x, y)$, and an affine isometry $g$ satisfies $\angle\, g(a)g(b)g(c) = \angle abc$. A nonzero multiple of a linear isometry, a conformal linear map, also keeps angles.

*Proof.* A linear isometry keeps norms, and by polarization it keeps inner products (Volume 16, Chapter 6). So $t$ does not change. For an affine isometry, $g(a) - g(b) = \vec g(a - b)$ with $\vec g$ a linear isometry. For $c\,h$ with $c \ne 0$, numerator and denominator of $t$ are multiplied by $c^2$. $\square$

**Theorem (Triangle inequality for angles).** For all $x, y, z \in V$, $\angle(x, z) \le \angle(x, y) + \angle(y, z)$.

*Proof.* If $y = 0$, the right side is $\pi \ge \angle(x, z)$. If $x = 0$, then $\angle(x, z) = \pi/2 = \angle(x, y)$; the case $z = 0$ is the same. So let all three be nonzero. By (3) the angles do not change under positive scaling, so let $\|x\| = \|y\| = \|z\| = 1$. Put $\alpha = \angle(x, y)$ and $\beta = \angle(y, z)$. If $\alpha + \beta \ge \pi$ the claim is clear, so let $\alpha + \beta < \pi$.

By (2), $\langle x, y\rangle = \cos\alpha$ and $\langle z, y\rangle = \cos\beta$. Put $u = x - \cos\alpha\, y$ and $w = z - \cos\beta\, y$. Then $\langle u, y\rangle = \cos\alpha - \cos\alpha = 0$ and $\langle w, y\rangle = 0$. By Pythagoras $1 = \cos^2\alpha + \|u\|^2$, so $\|u\| = \sin\alpha$, as $\sin \ge 0$ on $[0, \pi]$. In the same way $\|w\| = \sin\beta$. The cross terms vanish, so
$$\langle x, z\rangle = \cos\alpha\cos\beta + \langle u, w\rangle \ge \cos\alpha\cos\beta - \sin\alpha\sin\beta = \cos(\alpha + \beta),$$
by Cauchy-Schwarz for $u, w$. Thus $\cos\angle(x, z) \ge \cos(\alpha + \beta)$ with both angles in $[0, \pi]$. Since $\cos$ is strictly decreasing on $[0, \pi]$, $\angle(x, z) \le \alpha + \beta$. $\square$

::: mathlib
`InnerProductGeometry.angle_le_angle_add_angle` · `Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality`

`angle_le_angle_add_angle x y z : angle x z ≤ angle x y + angle y z` has no hypothesis, since the zero cases hold by the convention. The point form `EuclideanGeometry.angle_le_angle_add_angle p p₁ p₂ p₃ : ∠ p₁ p p₃ ≤ ∠ p₁ p p₂ + ∠ p₂ p p₃` takes the vertex first.

<?decl InnerProductGeometry.angle_le_angle_add_angle?>
<?decl EuclideanGeometry.angle_le_angle_add_angle?>
:::

::: mathlib
`EuclideanGeometry.angle_eq_pi_iff_sbtw` · `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine`

`angle_eq_pi_iff_sbtw : ∠ p₁ p₂ p₃ = π ↔ Sbtw ℝ p₁ p₂ p₃` is the bridge to the betweenness of Chapter 2. Its partner for the angle `0` is `angle_eq_zero_iff_ne_and_wbtw`. The vector forms are `angle_eq_zero_iff : angle x y = 0 ↔ x ≠ 0 ∧ ∃ r, 0 < r ∧ y = r • x` and `angle_eq_pi_iff` with `r < 0`.

<?decl EuclideanGeometry.angle_eq_pi_iff_sbtw?>
<?decl InnerProductGeometry.angle_eq_zero_iff?>
:::

### Examples

**Example (An angle in $\mathbb{R}^3$).** Let $a = (1, 0, 0)$, $b = 0$ and $c = (1, 1, 0)$. Then $\langle a - b, c - b\rangle = 1$ with norms $1$ and $\sqrt 2$, so $\angle abc = \arccos(1/\sqrt 2) = \pi/4$. At $a$ the vectors $(-1, 0, 0)$ and $(0, 1, 0)$ are orthogonal, so $\angle bac = \pi/2$. At $c$ the vectors $(0, -1, 0)$ and $(-1, -1, 0)$ give $\pi/4$. The sum is $\pi$, as Section 2 proves in general. The cross product of $(1,0,0)$ and $(1,1,0)$ is $(0,0,1)$, and $\|x \times y\| = \|x\|\,\|y\|\sin\angle(x, y) = \sqrt 2 \sin(\pi/4) = 1$.

**Counterexample (Affine maps do not keep angles).** The affine map $f(s, t) = (s, 2t)$ of $\mathbb{R}^2$ fixes $(1, 0)$ and $0$ and sends $(1, 1)$ to $(1, 2)$. The angle at the origin changes from $\pi/4$ to $\arccos(1/\sqrt 5)$.

### The library around it

`AffineIsometry.angle_map` is the invariance under affine isometries, and `InnerProductGeometry.IsConformalMap.preserves_angle` the conformal case. The cross product formula is `norm_ofLp_crossProduct`.

Common errors:

- The vertex of `∠ a b c` is `b`. The point form of the triangle inequality puts the vertex first.

### Exercises

1. (A) Compute the angles of the triangle $(0, 0)$, $(3, 0)$, $(0, 4)$ as values of $\arccos$.
2. (A) Show that $\angle(-x, -y) = \angle(x, y)$ and $\angle(r x, y) = \pi - \angle(x, y)$ for $r < 0$.
3. (A) Let $a \ne b$ with midpoint $m$. Show that $\angle abm = 0$ and $\angle amb = \pi$.
4. (B) Show that $\angle(x, y) < \pi/2$ if and only if $\langle x, y\rangle > 0$.
5. (C) In the proof of the triangle inequality let equality hold with $\alpha + \beta < \pi$. Show that $w = -\lambda u$ with $\lambda \ge 0$ or $u = 0$, and deduce that $y = s x + t z$ with $s, t \ge 0$. Hint: the equality case of Cauchy-Schwarz.
6. (C) Prove that $\angle$ is a metric on the unit sphere of $V$. Which axiom needs the theorem on angles $0$?

### Notes and history

The files `Mathlib.Geometry.Euclidean.Basic`, `Angle.Unoriented.Basic` and `Angle.Unoriented.Affine` have the authors Joseph Myers and Manuel Candales in their headers.

### Reference

<?reference?>
