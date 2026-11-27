---
title: Spheres, tangents and the power of a point
kind: theory
modules:
  - Mathlib.Geometry.Euclidean.Sphere.Basic
  - Mathlib.Geometry.Euclidean.Sphere.SecondInter
  - Mathlib.Geometry.Euclidean.Sphere.OrthRadius
  - Mathlib.Geometry.Euclidean.Sphere.Tangent
  - Mathlib.Geometry.Euclidean.Sphere.Power
  - Mathlib.Geometry.Euclidean.Sphere.PolePolar
explains:
  E3: [EuclideanGeometry.Sphere, EuclideanGeometry.Cospherical, EuclideanGeometry.Sphere.secondInter, EuclideanGeometry.Sphere.orthRadius, EuclideanGeometry.Sphere.IsTangentAt, EuclideanGeometry.Sphere.power, EuclideanGeometry.Sphere.mul_dist_eq_abs_power, EuclideanGeometry.Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant]
  E2: [EuclideanGeometry.mem_sphere, EuclideanGeometry.Concyclic, EuclideanGeometry.Sphere.inner_vsub_center_midpoint_vsub, EuclideanGeometry.Cospherical.affineIndependent_of_ne, EuclideanGeometry.Sphere.secondInter_dist, EuclideanGeometry.Sphere.secondInter_mem, EuclideanGeometry.Sphere.secondInter_eq_self_iff, EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left, EuclideanGeometry.Sphere.inter_orthRadius_eq_singleton_of_dist_eq_radius, EuclideanGeometry.Sphere.IsTangentAt.dist_sq_eq_of_mem, EuclideanGeometry.Sphere.IsTangent, EuclideanGeometry.Sphere.tangentsFrom, EuclideanGeometry.Sphere.ncard_tangentsFrom_eq_two_of_radius_lt_dist, EuclideanGeometry.Sphere.tangentsFrom_eq_empty_of_dist_lt_radius, EuclideanGeometry.Sphere.isExtTangent_iff_dist_center, EuclideanGeometry.Sphere.isIntTangent_iff_dist_center, EuclideanGeometry.Sphere.power_eq_zero_iff_mem_sphere, EuclideanGeometry.Sphere.power_pos_iff_radius_lt_dist_center, EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi, EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero, EuclideanGeometry.Sphere.polar, EuclideanGeometry.Sphere.pole, EuclideanGeometry.Sphere.mem_polar_iff_inner]
  E1: auto
families: []
requires: [V07, V13, V16.C06, V16.C07, V22.C01, V22.C02, V22.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Spheres, tangents and the power of a point

### Overview

A sphere in a Euclidean affine space is the set of points at a fixed distance from a centre. This section studies how a sphere meets a line. A line through a point of a sphere meets it in exactly one more point, or touches it, when it is orthogonal to the radius. From this computation comes the main theorem of the section, the power of a point. For a point $p$ and a line through $p$ that meets the sphere in $a$ and $b$, the product $d(p, a)\, d(p, b)$ does not depend on the line. It equals $|d(p, c)^2 - r^2|$. The theorem of intersecting chords, the theorem of intersecting secants and the theorem of the tangent and the secant are three cases of this one statement.

The section works in a Euclidean affine space $P$ over a real inner product space $V$, as in Chapter 3, and $p - q \in V$ is the vector from $q$ to $p$.

### Definitions

**Definition (Sphere).** Let $c \in P$ and $r \in \mathbb{R}$. The *sphere* with centre $c$ and radius $r$ is $S(c, r) = \{p \in P : d(p, c) = r\}$. A set of points is *cospherical* if it lies in some sphere. A set is *concyclic* if it is cospherical and coplanar.

A sphere with $r < 0$ is empty, and a sphere with $r = 0$ is the single point $c$. Textbooks usually ask $r > 0$. Mathlib allows each real radius and puts the hypothesis $0 \le r$ or $0 < r$ on the theorems that need it.

::: mathlib
`EuclideanGeometry.Sphere` · `Mathlib.Geometry.Euclidean.Sphere.Basic`

`Sphere P` is a structure with two fields, `center : P` and `radius : ℝ`, for any metric space `P`. The radius is not required to be positive. A coercion turns `s : Sphere P` into the set `Metric.sphere s.center s.radius`, and `p ∈ s` unfolds by `EuclideanGeometry.mem_sphere` to `dist p s.center = s.radius`. A sphere of radius $-1$ and a sphere of radius $-2$ are different structures with the same empty set of points. `Cospherical ps` says `∃ center radius, ∀ p ∈ ps, dist p center = radius`, and `Concyclic ps` is a structure with the two fields `Cospherical` and `Coplanar`.

<?decl EuclideanGeometry.Sphere?>
:::

**Definition (Orthogonal hyperplane at a point).** Let $s = S(c, r)$ and $p \in P$. The *hyperplane orthogonal to the radius at* $p$ is the affine subspace $T_p = \{x \in P : \langle x - p, p - c\rangle = 0\}$, the affine subspace through $p$ with direction $(\mathbb{R}(p - c))^\perp$. An affine subspace $A$ is *tangent to $s$ at $p$* if $p \in s$, $p \in A$ and $A \subseteq T_p$. It is *tangent to* $s$ if it is tangent at some point.

For $p \in s$ and $p \ne c$, $T_p$ is the tangent hyperplane at $p$. A line through $p$ is tangent at $p$ if and only if it is orthogonal to the radius $p - c$. Each affine subspace through $p$ inside $T_p$ is tangent at $p$, even the point $\{p\}$.

::: mathlib
`EuclideanGeometry.Sphere.orthRadius` · `Mathlib.Geometry.Euclidean.Sphere.OrthRadius`

`s.orthRadius p` is `AffineSubspace.mk' p (ℝ ∙ (p -ᵥ s.center)).orthogonal`, the affine subspace through `p` with the orthogonal complement of the line of the radius as direction. It is defined for each `p`, on the sphere or not. The lemma `mem_orthRadius_iff_inner_left` gives `x ∈ s.orthRadius p ↔ ⟪x -ᵥ p, p -ᵥ s.center⟫ = 0`.

<?decl EuclideanGeometry.Sphere.orthRadius?>
:::

::: mathlib
`EuclideanGeometry.Sphere.IsTangentAt` · `Mathlib.Geometry.Euclidean.Sphere.Tangent`

`s.IsTangentAt p as` is a structure in `Prop` with three fields: `mem_sphere : p ∈ s`, `mem_space : p ∈ as` and `le_orthRadius : as ≤ s.orthRadius p`. `s.IsTangent as` is `∃ p, s.IsTangentAt p as`, and `s.tangentsFrom p` is the set of the spaces `s.orthRadius t`, `t ∈ s`, that contain `p`.

<?decl EuclideanGeometry.Sphere.IsTangentAt?>
:::

**Definition (Power of a point).** The *power* of $p$ with respect to $s = S(c, r)$ is $\operatorname{pow}_s(p) = d(p, c)^2 - r^2$.

For $r \ge 0$ the sign of the power says where $p$ is: $\operatorname{pow}_s(p) > 0$ outside the sphere, $= 0$ on it, $< 0$ inside.

::: mathlib
`EuclideanGeometry.Sphere.power` · `Mathlib.Geometry.Euclidean.Sphere.Power`

`s.power p` is `dist p s.center ^ 2 - s.radius ^ 2`. The lemmas `power_eq_zero_iff_mem_sphere`, `power_pos_iff_radius_lt_dist_center` and `power_neg_iff_dist_center_lt_radius` give the three cases. Each of them has the hypothesis `0 ≤ s.radius`.

<?decl EuclideanGeometry.Sphere.power?>
:::

### Theorems and proofs

**Lemma (Chord and centre).** Let $p_1, p_2 \in S(c, r)$ and let $m$ be their midpoint. Then $\langle c - m, p_2 - p_1\rangle = 0$. So the centre lies on the perpendicular bisector of each chord. In Mathlib this is `Sphere.inner_vsub_center_midpoint_vsub`.

*Proof.* Put $u = p_1 - m$, so $p_2 - m = -u$ and $p_2 - p_1 = -2u$. Let $w = m - c$. Then $r^2 = \|p_1 - c\|^2 = \|w + u\|^2 = \|w\|^2 + 2\langle w, u\rangle + \|u\|^2$ and $r^2 = \|p_2 - c\|^2 = \|w - u\|^2 = \|w\|^2 - 2\langle w, u\rangle + \|u\|^2$. Subtract: $4\langle w, u\rangle = 0$. Hence $\langle c - m, p_2 - p_1\rangle = \langle -w, -2u\rangle = 2\langle w, u\rangle = 0$. $\square$

**Theorem (Second intersection).** Let $p \in s = S(c, r)$ and $v \in V$ with $v \ne 0$. The points of $s$ on the line $\{p + tv : t \in \mathbb{R}\}$ are $p$ and $p + t_0 v$ with
$$t_0 = \frac{-2\langle v, p - c\rangle}{\langle v, v\rangle}.$$
The two points are equal if and only if $\langle v, p - c\rangle = 0$, that is, if and only if the line is tangent at $p$. In particular a line meets a sphere in at most two points, and three distinct points of a sphere are not collinear.

*Proof.* Since $d(p, c) = r$,
$$\|p + tv - c\|^2 - r^2 = \|p - c\|^2 + 2t\langle v, p - c\rangle + t^2\|v\|^2 - r^2 = t\bigl(2\langle v, p - c\rangle + t\|v\|^2\bigr).$$
The point $p + tv$ is on $s$ if and only if this is $0$, so if and only if $t = 0$ or $t = t_0$. The two roots agree if and only if $t_0 = 0$, that is, $\langle v, p - c\rangle = 0$. This is the condition $p + v \in T_p$, so the line is in $T_p$ and is tangent at $p$. $\square$

::: mathlib
`EuclideanGeometry.Sphere.secondInter` · `Mathlib.Geometry.Euclidean.Sphere.SecondInter`

`s.secondInter p v` is defined as `(-2 * ⟪v, p -ᵥ s.center⟫ / ⟪v, v⟫) • v +ᵥ p`, the formula of the theorem. It does not use the radius, so for each `p` it is a point at the same distance from the centre as `p` (`secondInter_dist`), and it is on `s` if and only if `p` is (`secondInter_mem`). The tangent case is `secondInter_eq_self_iff : s.secondInter p v = p ↔ ⟪v, p -ᵥ s.center⟫ = 0`. Three distinct points of a sphere are affinely independent by `Cospherical.affineIndependent_of_ne`.

<?decl EuclideanGeometry.Sphere.secondInter?>
:::

**Theorem (Tangent hyperplane).** Let $p \in s = S(c, r)$. For each $q \in T_p$, $d(q, c)^2 = r^2 + d(q, p)^2$. Hence $s \cap T_p = \{p\}$, and each point of $T_p$ other than $p$ is outside the sphere.

*Proof.* The vectors $q - p$ and $p - c$ are orthogonal, since $q \in T_p$. Pythagoras gives $\|q - c\|^2 = \|q - p\|^2 + \|p - c\|^2 = d(q, p)^2 + r^2$. If $q \ne p$ then $d(q, c)^2 > r^2$, and $r \ge 0$ because $p \in s$, so $d(q, c) > r$. $\square$

::: mathlib
`EuclideanGeometry.Sphere.IsTangentAt.dist_sq_eq_of_mem` · `Mathlib.Geometry.Euclidean.Sphere.Tangent`

For `h : s.IsTangentAt p as` and `q ∈ as` the lemma gives `dist q s.center ^ 2 = s.radius ^ 2 + dist q p ^ 2`. The intersection statement is `inter_orthRadius_eq_singleton_of_dist_eq_radius`.

<?decl EuclideanGeometry.Sphere.IsTangentAt.dist_sq_eq_of_mem?>
:::

**Theorem (Power of a point).** Let $s = S(c, r)$, let $a, b \in s$, and let $p$ be a point of the line through $a$ and $b$. Then
$$d(p, a)\, d(p, b) = |\operatorname{pow}_s(p)| = |d(p, c)^2 - r^2|.$$

*Proof.* If $a = b$, the line is the point $a$, so $p = a$. Both sides are $0$, because $d(a, c) = r$. Assume $a \ne b$. Let $m$ be the midpoint of $a$ and $b$, let $u = (b - a)/\|b - a\|$ and $h = \|b - a\|/2$. Then $a = m - hu$ and $b = m + hu$. Write $p = m + \sigma u$ with $\sigma \in \mathbb{R}$. So $d(p, a) = |\sigma + h|$ and $d(p, b) = |\sigma - h|$, and
$$d(p, a)\, d(p, b) = |\sigma^2 - h^2|.$$
By the lemma on chords, $c - m$ is orthogonal to $u$. Pythagoras for $p - c = \sigma u + (m - c)$ and for $a - c = -hu + (m - c)$ gives
$$d(p, c)^2 = \sigma^2 + d(m, c)^2, \qquad r^2 = h^2 + d(m, c)^2.$$
Subtract: $d(p, c)^2 - r^2 = \sigma^2 - h^2$. $\square$

**Corollary (Chords, secants, tangent).** Let $a, b, a', b'$ be points of $s$.

1. (Intersecting chords.) If $p$ is strictly between $a$ and $b$ and strictly between $a'$ and $b'$, then $d(p, a)\, d(p, b) = d(p, a')\, d(p, b')$.
2. (Intersecting secants.) If $p$ lies on the lines $ab$ and $a'b'$ outside the sphere, the same equation holds.
3. (Tangent and secant.) If the line $pt$ is tangent to $s$ at $t$ and $p$ is on the line $ab$, then $d(p, t)^2 = d(p, a)\, d(p, b)$.

*Proof.* In 1 and 2 both products equal $|\operatorname{pow}_s(p)|$. In 3, $p$ is in the tangent line at $t$, so the theorem on the tangent hyperplane gives $d(p, c)^2 = r^2 + d(p, t)^2$, that is, $\operatorname{pow}_s(p) = d(p, t)^2 \ge 0$. The theorem gives $d(p, a)\, d(p, b) = |\operatorname{pow}_s(p)| = d(p, t)^2$. $\square$

::: mathlib
`EuclideanGeometry.Sphere.mul_dist_eq_abs_power` · `Mathlib.Geometry.Euclidean.Sphere.Power`

The statement is `dist p a * dist p b = |s.power p|` for `p ∈ line[ℝ, a, b]`, `a ∈ s` and `b ∈ s`. The notation `line[ℝ, a, b]` is the affine span of `{a, b}`. The forms for a cospherical set `{a, b, c, d}` state "between" through angles: `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi` (chords, `∠ a p b = π`) and `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero` (secants, `∠ a p b = 0`). The tangent case is `Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant`, with the hypothesis `s.IsTangentAt t (line[ℝ, p, t])`.

<?decl EuclideanGeometry.Sphere.mul_dist_eq_abs_power?>
:::

### Examples

**Example (A tangent length).** Let $s$ be the circle $x^2 + y^2 = 25$ in $\mathbb{R}^2$ and $p = (7, 1)$. Then $\operatorname{pow}_s(p) = 49 + 1 - 25 = 25$. The horizontal line $y = 1$ through $p$ meets $s$ at $a = (-\sqrt{24}, 1)$ and $b = (\sqrt{24}, 1)$. So $d(p, a)\, d(p, b) = (7 + \sqrt{24})(7 - \sqrt{24}) = 49 - 24 = 25$, as the theorem says. The polar line of $p$ is $7x + y = 25$, and its points on $s$ are the points of contact of the tangents from $p$. Put $y = 25 - 7x$ into $x^2 + y^2 = 25$: $50x^2 - 350x + 600 = 0$, so $x^2 - 7x + 12 = 0$ and $x \in \{3, 4\}$. The points of contact are $(3, 4)$ and $(4, -3)$. Their squared distance to $p$ is $25$, the power of $p$, so the tangent length is $5$.

**Example (Intersecting chords).** In the same circle let $p = (1, 0)$, inside. The chord on the $x$ axis has ends $(\pm 5, 0)$, and $d(p, (5, 0))\, d(p, (-5, 0)) = 4 \cdot 6 = 24$. The vertical chord through $p$ has ends $(1, \pm\sqrt{24})$, and the product is $\sqrt{24}^2 = 24$. Both equal $|\operatorname{pow}_s(p)| = |1 - 25| = 24$.

**Counterexample (A negative radius).** The statement $\operatorname{pow}_s(p) = 0 \Leftrightarrow p \in s$ needs $r \ge 0$. Let $s$ have centre $c$ and radius $-5$, and let $d(p, c) = 5$. Then $\operatorname{pow}_s(p) = 25 - 25 = 0$, but $s$ is empty. This is why `power_eq_zero_iff_mem_sphere` has the hypothesis `0 ≤ s.radius`.

### The library around it

In the files of `Mathlib.Geometry.Euclidean.Sphere` a lemma `*_map` says that an affine isometry carries each notion to the same notion for the image sphere, and `mem_sphere` and `mem_sphere'` unfold `p ∈ s` with the two orders of `dist`.

Two spheres can touch. The lemma `isExtTangent_iff_dist_center` says that they touch from outside if and only if the distance of the centres is the sum of the radii, both radii nonnegative, and `isIntTangent_iff_dist_center` gives the difference of the radii for the inner case. The file `PolePolar` adds `s.pole as`, the inverse of the foot of the perpendicular from the centre to `as`, and `pole_polar` says that the pole of the polar of `p` is `p`.

In the plane, `ncard_tangentsFrom_eq_two_of_radius_lt_dist` says that exactly two tangent lines pass through a point outside a circle of positive radius, and `tangentsFrom_eq_empty_of_dist_lt_radius` says that none passes through a point inside. The points of contact lie on the *polar* `s.polar p`, which is `s.orthRadius (inversion s.center s.radius p)`, and `mem_polar_iff_inner` gives its equation $\langle q - c, p - c\rangle = r^2$. The radius can be negative or zero, and a lemma that ends in `_of_mem` usually gets `0 ≤ s.radius` from `radius_nonneg_of_mem`.

### Exercises

1. (A) Compute the power of $(2, 3)$ with respect to the circle with centre $(1, 1)$ and radius $2$. Is the point inside or outside?
2. (A) Show that the tangent line to $x^2 + y^2 = r^2$ at $(x_0, y_0)$ is $x_0 x + y_0 y = r^2$, from the definition of $T_p$.
3. (A) Let $p$ be the midpoint of a chord $ab$ of a circle of radius $r$ and let $d(p, c) = \delta$. Show that $d(a, b) = 2\sqrt{r^2 - \delta^2}$.
4. (B) Show that the set of points with equal powers with respect to two spheres with different centres is an affine hyperplane orthogonal to the line of the centres (the radical axis in the plane). Hint: expand $d(p, c_1)^2 - d(p, c_2)^2$.
5. (B) Prove the converse of the theorem of intersecting chords in the plane: if two segments $ab$ and $a'b'$ meet at a point $p$ strictly between the ends and $d(p, a)\, d(p, b) = d(p, a')\, d(p, b')$, and the two lines are different, then $a, b, a', b'$ are concyclic. Hint: take the circle through $a, b, a'$ and its second intersection with the line $a'p$.
6. (C) Let $s$ be a circle with centre $c$ and $p$ a point outside. Show that the polar line of $p$ passes through the two points of contact of the tangents from $p$, and that $p$ lies on the polar of a point $q$ if and only if $q$ lies on the polar of $p$.
7. (C) Show that $d(c_1, c_2) = r_1 + r_2$ with $r_1, r_2 \ge 0$ implies that the spheres $S(c_1, r_1)$ and $S(c_2, r_2)$ meet in exactly one point, and find it.

### Notes and history

The theorem of intersecting chords is Proposition 35 of Book III of Euclid's *Elements*, and the theorem of the tangent and the secant is Proposition 36 of the same book. Pole and polar are the basis of the projective theory of conics. The files `Mathlib.Geometry.Euclidean.Sphere.Basic`, `SecondInter`, `OrthRadius`, `Tangent` and `PolePolar` have the author Joseph Myers in their headers, and the file `Mathlib.Geometry.Euclidean.Sphere.Power` has the authors Manuel Candales, Benjamin Davidson and Li Jiale.

### Reference

<?reference?>
