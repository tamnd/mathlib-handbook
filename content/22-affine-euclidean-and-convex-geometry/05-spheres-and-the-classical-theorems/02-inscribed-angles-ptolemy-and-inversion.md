---
title: Inscribed angles, Ptolemy and inversion
kind: theory
modules:
  - Mathlib.Geometry.Euclidean.Angle.Sphere
  - Mathlib.Geometry.Euclidean.Sphere.Ptolemy
  - Mathlib.Geometry.Euclidean.EulerQuadrilateral
  - Mathlib.Geometry.Euclidean.Inversion.Basic
  - Mathlib.Geometry.Euclidean.Inversion.ImageHyperplane
  - Mathlib.Geometry.Euclidean.Inversion.Calculus
explains:
  E3: [EuclideanGeometry.Sphere.oangle_center_eq_two_zsmul_oangle, EuclideanGeometry.Sphere.two_zsmul_oangle_eq, EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter, EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical, EuclideanGeometry.inversion, EuclideanGeometry.dist_inversion_inversion, EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist, EuclideanGeometry.dist_sq_add_dist_sq_add_dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_add_four_mul_dist_sq]
  E2: [EuclideanGeometry.concyclic_or_collinear_of_two_zsmul_oangle_eq, EuclideanGeometry.Sphere.angle_center_eq_two_mul_angle_of_two_mul_angle_le_pi, EuclideanGeometry.Cospherical.two_zsmul_oangle_eq, EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear, EuclideanGeometry.Sphere.thales_theorem, EuclideanGeometry.Sphere.isDiameter_of_angle_eq_pi_div_two, EuclideanGeometry.Sphere.IsDiameter, EuclideanGeometry.Sphere.IsTangentAt_iff_angle_eq_pi_div_two, Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius, EuclideanGeometry.inversion_inversion, EuclideanGeometry.dist_inversion_center, EuclideanGeometry.inversion_of_mem_sphere, EuclideanGeometry.image_inversion_perpBisector, EuclideanGeometry.image_inversion_sphere_dist_center, EuclideanGeometry.hasFDerivAt_inversion, EuclideanGeometry.dist_sq_add_dist_sq_add_dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_iff_midpoint_eq]
  E1: auto
families: []
requires: [V07, V15.C06, V16.C06, V22.C02, V22.C03, V22.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Inscribed angles, Ptolemy and inversion

### Overview

This section studies the angles and the distances between points of a circle. There are three main results. The inscribed angle theorem says that the angle at the centre is twice the angle at the circumference. Ptolemy's theorem says that for a convex quadrilateral inscribed in a circle, the product of the diagonals is the sum of the products of the opposite sides. Ptolemy's inequality says that for any four points, the product of the diagonals is at most that sum. The tool for the inequality is inversion in a sphere. The section ends with Euler's theorem on quadrilaterals.

The inscribed angle theorem uses the oriented angle $\measuredangle$ of Chapter 4, with values in $\mathbb{R}/2\pi\mathbb{Z}$, and the oriented angle sum of a triangle. The unoriented angle $\angle$ of Chapter 3 takes values in $[0, \pi]$.

### Definitions

**Definition (Diameter).** Let $s = S(c, r)$ be a sphere. Two points $a, b$ are the *ends of a diameter* of $s$ if $a \in s$ and $c$ is the midpoint of $a$ and $b$. Then $b \in s$ and $d(a, b) = 2r$.

::: mathlib
`EuclideanGeometry.Sphere.IsDiameter` · `Mathlib.Geometry.Euclidean.Sphere.Basic`

`s.IsDiameter p₁ p₂` is a structure with two fields: `p₁ ∈ s` and `midpoint ℝ p₁ p₂ = s.center`.

<?decl EuclideanGeometry.Sphere.IsDiameter?>
:::

**Definition (Inversion).** Let $c \in P$ and $R \in \mathbb{R}$. The *inversion* with centre $c$ and radius $R$ is the map $\iota : P \to P$ with
$$\iota(x) = c + \frac{R^2}{d(x, c)^2}\,(x - c) \quad (x \ne c), \qquad \iota(c) = c.$$
The point $\iota(x)$ is on the ray from $c$ through $x$, and $d(\iota(x), c)\, d(x, c) = R^2$. Points near $c$ go far away, and points far away come near $c$. Each point of the sphere $S(c, |R|)$ stays where it is.

The value $\iota(c) = c$ is a convention, because an affine space has no point at infinity. The map is not continuous at $c$ when $R \ne 0$.

::: mathlib
`EuclideanGeometry.inversion` · `Mathlib.Geometry.Euclidean.Inversion.Basic`

`inversion c R x` is `(R / dist x c) ^ 2 • (x -ᵥ c) +ᵥ c`. At `x = c` the vector `x -ᵥ c` is zero, so the formula gives `c` with no case split: division by zero gives zero in Mathlib. The lemmas `inversion_self`, `inversion_of_mem_sphere`, `dist_inversion_center` (the value `R ^ 2 / dist x c`) and `inversion_inversion` (the map is an involution for `R ≠ 0`) give the basic facts.

<?decl EuclideanGeometry.inversion?>
:::

### Theorems and proofs

Let $P$ be a Euclidean affine plane with an orientation, as in Chapter 4. For points $a, b, x$ write $\measuredangle\, a\, x\, b$ for the oriented angle at $x$ from $a$ to $b$.

**Theorem (Inscribed angle theorem).** Let $s = S(o, r)$ be a circle and let $a, b, c \in s$ with $b \ne a$ and $b \ne c$. Then
$$\measuredangle\, a\, o\, c = 2\,\measuredangle\, a\, b\, c \pmod{2\pi}.$$

*Proof.* If $r = 0$, all the points are equal to $o$, which contradicts $b \ne a$. So $r > 0$ and $o$ differs from $a$, $b$ and $c$. First take the triangle $o\, a\, b$. Since $d(o, a) = d(o, b)$, the base angles are equal as oriented angles: $\measuredangle\, o\, a\, b = \measuredangle\, a\, b\, o$. The oriented angle sum of a triangle (Chapter 4) gives
$$\measuredangle\, a\, o\, b + \measuredangle\, o\, b\, a + \measuredangle\, b\, a\, o = \pi.$$
Here $\measuredangle\, b\, a\, o = -\measuredangle\, o\, a\, b = -\measuredangle\, a\, b\, o = \measuredangle\, o\, b\, a$. So $\measuredangle\, a\, o\, b = \pi - 2\measuredangle\, o\, b\, a = \pi + 2\measuredangle\, a\, b\, o$. The same argument in the triangle $o\, b\, c$, with $d(o, b) = d(o, c)$, gives $\measuredangle\, b\, o\, c = \pi + 2\measuredangle\, o\, b\, c$. Oriented angles at one vertex add, so
$$\measuredangle\, a\, o\, c = \measuredangle\, a\, o\, b + \measuredangle\, b\, o\, c = 2\pi + 2(\measuredangle\, a\, b\, o + \measuredangle\, o\, b\, c) = 2\,\measuredangle\, a\, b\, c.$$
Since $2\pi = 0$ in $\mathbb{R}/2\pi\mathbb{Z}$, this is the claim. $\square$

The textbook proof with unoriented angles has three cases for the position of $o$. The oriented proof has none.

::: mathlib
`EuclideanGeometry.Sphere.oangle_center_eq_two_zsmul_oangle` · `Mathlib.Geometry.Euclidean.Angle.Sphere`

The hypotheses are `p₁ ∈ s`, `p₂ ∈ s`, `p₃ ∈ s`, `p₂ ≠ p₁` and `p₂ ≠ p₃`, and the conclusion is `∡ p₁ s.center p₃ = (2 : ℤ) • ∡ p₁ p₂ p₃` in `Real.Angle`. The plane is given by the instances `Fact (finrank ℝ V = 2)` and `Module.Oriented ℝ V (Fin 2)`. The unoriented form `angle_center_eq_two_mul_angle_of_two_mul_angle_le_pi` needs the extra hypothesis `2 * ∠ p₁ p₂ p₃ ≤ π`. Without it the conclusion is false, because an unoriented angle is never more than $\pi$.

<?decl EuclideanGeometry.Sphere.oangle_center_eq_two_zsmul_oangle?>
:::

**Corollary (Angles in the same segment).** Let $a, b, c, d \in s$ with $b, c \notin \{a, d\}$. Then $2\,\measuredangle\, a\, b\, d = 2\,\measuredangle\, a\, c\, d$.

*Proof.* Both sides equal $\measuredangle\, a\, o\, d$ by the theorem. $\square$

The equality $2\theta = 2\varphi$ says $\theta = \varphi$ modulo $\pi$. So it holds two classical theorems: equal angles on the same arc, and opposite angles of a cyclic quadrilateral that add to $\pi$.

::: mathlib
`EuclideanGeometry.Sphere.two_zsmul_oangle_eq` · `Mathlib.Geometry.Euclidean.Angle.Sphere`

The conclusion is `(2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄`, with the four non-equality hypotheses of the corollary. The variant `Cospherical.two_zsmul_oangle_eq` takes `Cospherical {p₁, p₂, p₃, p₄}` instead of a named sphere.

<?decl EuclideanGeometry.Sphere.two_zsmul_oangle_eq?>
:::

Conversely, if $2\,\measuredangle\, a\, b\, d = 2\,\measuredangle\, a\, c\, d$, then the four points are concyclic or collinear. Four points on a line satisfy the hypothesis. In Mathlib this is `concyclic_or_collinear_of_two_zsmul_oangle_eq`, and `cospherical_of_two_zsmul_oangle_eq_of_not_collinear` gives the cospherical case when $a$, $b$, $d$ are not collinear.


**Theorem (Thales).** Let $a, c$ be the ends of a diameter of $s$. For each point $b$, $\angle\, a\, b\, c = \pi/2$ if and only if $b \in s$.

*Proof.* Let $o$ be the centre, $u = a - o$ and $w = b - o$. Then $c - o = -u$, so
$$\langle a - b, c - b\rangle = \langle u - w, -u - w\rangle = \|w\|^2 - \|u\|^2 = d(b, o)^2 - r^2.$$
The angle is $\pi/2$ exactly when this inner product is $0$, that is, when $d(b, o) = r$. $\square$

The theorem holds in each dimension, with no hypothesis $b \ne a$: in Mathlib an angle with a zero vector is $\pi/2$. The lemma `isDiameter_of_angle_eq_pi_div_two` gives a diameter from a right angle, and `IsTangentAt_iff_angle_eq_pi_div_two` is the angle form of the tangent criterion of the previous section.

::: mathlib
`EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter` · `Mathlib.Geometry.Euclidean.Angle.Sphere`

From `s.IsDiameter p₁ p₃` it gives `∠ p₁ p₂ p₃ = π / 2 ↔ p₂ ∈ s`. The alias `Sphere.thales_theorem` has the same statement. No dimension or orientation instance is needed.

<?decl EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter?>
:::

**Theorem (Ptolemy).** Let $a, b, c, d$ be cospherical and let $p$ be a point with $\angle\, a\, p\, c = \pi$ and $\angle\, b\, p\, d = \pi$, so that the diagonals $ac$ and $bd$ cross at $p$. Then
$$d(a, b)\, d(c, d) + d(b, c)\, d(d, a) = d(a, c)\, d(b, d).$$

*Proof.* Write $\alpha, \beta, \gamma, \delta$ for the distances from $p$ to $a, b, c, d$. These are positive, and $p$ is strictly between $a$ and $c$ and strictly between $b$ and $d$. The theorem of intersecting chords from the previous section gives $\alpha\gamma = \beta\delta$. The triangles $p\, b\, a$ and $p\, c\, d$ have equal angles at $p$ (vertical angles), and $\gamma/\beta = \delta/\alpha$. By the side-angle-side similarity of Chapter 3, $d(c, d) = (\gamma/\beta)\, d(a, b)$. In the same way the triangles $p\, b\, c$ and $p\, a\, d$ have equal angles at $p$ and $\alpha/\beta = \delta/\gamma$, so $d(d, a) = (\alpha/\beta)\, d(b, c)$. Then
$$d(a, b)\, d(c, d) + d(b, c)\, d(d, a) = \frac{\gamma\, d(a, b)^2 + \alpha\, d(b, c)^2}{\beta}.$$
Let $\theta = \angle\, a\, p\, b$, so $\angle\, c\, p\, b = \pi - \theta$. The law of cosines (Chapter 3) gives $d(a, b)^2 = \alpha^2 + \beta^2 - 2\alpha\beta\cos\theta$ and $d(b, c)^2 = \gamma^2 + \beta^2 + 2\gamma\beta\cos\theta$. Multiply by $\gamma$ and by $\alpha$ and add: $\gamma\, d(a, b)^2 + \alpha\, d(b, c)^2 = (\alpha + \gamma)(\beta^2 + \alpha\gamma)$. This is Stewart's theorem. Also $d(a, c) = \alpha + \gamma$ and $d(b, d) = \beta + \delta = \beta + \alpha\gamma/\beta = (\beta^2 + \alpha\gamma)/\beta$. The two sides agree. $\square$

::: mathlib
`EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical` · `Mathlib.Geometry.Euclidean.Sphere.Ptolemy`

The proof in the file follows the proof above: `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi` for the chords, `dist_mul_of_eq_angle_of_dist_mul` for the similarities and `dist_sq_mul_dist_add_dist_sq_mul_dist` for Stewart's theorem. No dimension hypothesis is needed.

<?decl EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical?>
:::

The key fact about inversion is how it changes distances.

**Lemma (Distances under inversion).** Let $x, y \ne c$ and let $\iota$ be the inversion with centre $c$ and radius $R$. Then
$$d(\iota(x), \iota(y)) = \frac{R^2}{d(x, c)\, d(y, c)}\, d(x, y).$$

*Proof.* Let $u = x - c$ and $v = y - c$. Then $\iota(x) - \iota(y) = R^2(u/\|u\|^2 - v/\|v\|^2)$, and
$$\Big\|\frac{u}{\|u\|^2} - \frac{v}{\|v\|^2}\Big\|^2 = \frac{1}{\|u\|^2} - \frac{2\langle u, v\rangle}{\|u\|^2\|v\|^2} + \frac{1}{\|v\|^2} = \frac{\|v\|^2 - 2\langle u, v\rangle + \|u\|^2}{\|u\|^2\|v\|^2} = \frac{\|u - v\|^2}{\|u\|^2\|v\|^2}.$$
Take square roots and multiply by $R^2$. $\square$

::: mathlib
`EuclideanGeometry.dist_inversion_inversion` · `Mathlib.Geometry.Euclidean.Inversion.Basic`

There is no hypothesis on `R`: for `R = 0` both sides are zero.

<?decl EuclideanGeometry.dist_inversion_inversion?>
:::

**Theorem (Ptolemy's inequality).** For all points $a, b, c, d$ of a Euclidean affine space,
$$d(a, c)\, d(b, d) \le d(a, b)\, d(c, d) + d(b, c)\, d(a, d).$$

*Proof.* If $b$, $c$ or $d$ equals $a$, the inequality is direct. Otherwise let $\iota$ be the inversion with centre $a$ and radius $1$, and write $x' = \iota(x)$. The triangle inequality gives $d(b', d') \le d(b', c') + d(c', d')$. By the lemma this is
$$\frac{d(b, d)}{d(a, b)\, d(a, d)} \le \frac{d(b, c)}{d(a, b)\, d(a, c)} + \frac{d(c, d)}{d(a, c)\, d(a, d)}.$$
Multiply by $d(a, b)\, d(a, c)\, d(a, d) > 0$. $\square$

The proof shows when equality holds: exactly when $c'$ lies on the segment from $b'$ to $d'$. In the plane, the image of a circle through $a$ is a line, so this happens for a convex cyclic quadrilateral, and Ptolemy's theorem is the equality case. The index of this edition has no declaration for the statement that equality in Ptolemy's inequality implies that the points are concyclic or collinear.

::: mathlib
`EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist` · `Mathlib.Geometry.Euclidean.Inversion.Basic`

The statement holds for all `a b c d : P`, in each dimension, and the proof in Mathlib is the proof above.

<?decl EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist?>
:::

The lemma on distances also gives the images of spheres. A sphere through $c$ goes to a hyperplane, with the point $c$ added because $\iota(c) = c$. A hyperplane that does not contain $c$ goes to a sphere through $c$, minus the point $c$.

::: mathlib
`EuclideanGeometry.image_inversion_sphere_dist_center` · `Mathlib.Geometry.Euclidean.Inversion.ImageHyperplane`

For `R ≠ 0` and `y ≠ c` the image of `Metric.sphere y (dist y c)`, the sphere with centre `y` through `c`, is `insert c (perpBisector c (inversion c R y))`. The reverse statement `image_inversion_perpBisector` gives the image of the perpendicular bisector of `c` and `y` as a sphere minus `{c}`.

<?decl EuclideanGeometry.image_inversion_sphere_dist_center?>
:::

Inversion is also conformal: its derivative at $x \ne c$ is $(R/d(x, c))^2$ times a reflection, so it keeps unoriented angles between curves. The statement is `hasFDerivAt_inversion` in `Mathlib.Geometry.Euclidean.Inversion.Calculus`.

**Theorem (Euler's quadrilateral theorem).** For any four points $a, b, c, d$,
$$d(a, b)^2 + d(b, c)^2 + d(c, d)^2 + d(d, a)^2 = d(a, c)^2 + d(b, d)^2 + 4\, d(m, n)^2,$$
where $m$ is the midpoint of $a$ and $c$, and $n$ is the midpoint of $b$ and $d$.

*Proof.* Let $x = a - b$, $y = b - c$ and $z = c - d$. Then $d - a = -(x + y + z)$, $a - c = x + y$, $b - d = y + z$ and $2(m - n) = (a - b) + (c - d) = x + z$. Expand both sides with $\|v + w\|^2 = \|v\|^2 + 2\langle v, w\rangle + \|w\|^2$. Each side is $2(\|x\|^2 + \|y\|^2 + \|z\|^2) + 2(\langle x, y\rangle + \langle y, z\rangle + \langle x, z\rangle)$. $\square$

The points need not be in a plane. The correction term is zero exactly when $m = n$, that is, when $a\, b\, c\, d$ is a parallelogram. Then the theorem is the parallelogram law $2\|u\|^2 + 2\|v\|^2 = \|u + v\|^2 + \|u - v\|^2$ of V16.

::: mathlib
`EuclideanGeometry.dist_sq_add_dist_sq_add_dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_add_four_mul_dist_sq` · `Mathlib.Geometry.Euclidean.EulerQuadrilateral`

The statement has no hypothesis. The companion `dist_sq_add_dist_sq_add_dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_iff_midpoint_eq` says that the sum of the squares of the sides equals the sum of the squares of the diagonals if and only if `midpoint ℝ a c = midpoint ℝ b d`.

<?decl EuclideanGeometry.dist_sq_add_dist_sq_add_dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_add_four_mul_dist_sq?>
:::

### Examples

**Example (An inscribed angle).** On the unit circle in $\mathbb{R}^2$ with centre $o = (0, 0)$, take $a = (1, 0)$, $c = (0, 1)$ and $b = (-1, 0)$. Then $a - b = (2, 0)$ and $c - b = (1, 1)$, so $\angle\, a\, b\, c = \pi/4$. The central angle $\angle\, a\, o\, c$ is $\pi/2$, twice as large. With $b = (0, -1)$ instead, $a - b = (1, 1)$ and $c - b = (0, 2)$, and the angle is again $\pi/4$: $b$ moved on the same arc.

**Example (Pythagoras from Ptolemy).** A rectangle with sides $3$ and $4$ is inscribed in a circle, and its diagonals have length $5$ and cross at the centre. Ptolemy's theorem gives $3 \cdot 3 + 4 \cdot 4 = 5 \cdot 5$.

**Example (A strict Ptolemy inequality).** Take $a = (0, 0)$, $b = (1, 0)$, $c = (1, 1)$, $d = (0, 2)$. Then $d(a, c)\, d(b, d) = \sqrt2 \cdot \sqrt5 \approx 3.162$, while $d(a, b)\, d(c, d) + d(b, c)\, d(a, d) = 1 \cdot \sqrt2 + 1 \cdot 2 \approx 3.414$. The four points are not concyclic: the circle through $a$, $b$, $d$ has centre $(1/2, 1)$ and radius $\sqrt5/2$, and $c$ is at distance $1/2$ from that centre.

**Example (An inversion).** Let $c = (0, 0)$ and $R = 1$ in $\mathbb{R}^2$. Then $\iota(x) = x/\|x\|^2$. The points $x = (2, 0)$ and $y = (0, 2)$ go to $(1/2, 0)$ and $(0, 1/2)$, at distance $\sqrt2/2$. The lemma gives $\frac{1}{2 \cdot 2} \cdot 2\sqrt2 = \sqrt2/2$. The circle with centre $(1, 0)$ through the origin goes to the line $\{x_1 = 1/2\}$, the perpendicular bisector of $(0, 0)$ and $\iota((1, 0)) = (1, 0)$.

### The library around it

Most angle theorems in `Mathlib.Geometry.Euclidean.Angle.Sphere` need the plane instances; Thales and the tangent criterion do not. The file also holds `Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius`, the law of sines $a / \sin A = 2R$ in any dimension. The next section defines the circumradius.

Oriented angles mod $\pi$ appear as `(2 : ℤ) • θ` with `θ : Real.Angle`. Olympiad geometry calls this the method of directed angles.

Inversion is defined for a general Euclidean affine space and a real radius of any sign. The index of this edition has no declaration for the statement that inversion maps a sphere not through the centre to a sphere.

### Exercises

1. (A) On the unit circle, let $a = (1, 0)$, $c = (0, 1)$ and $b = (\cos t, \sin t)$ with $\pi/2 < t < 2\pi$. Compute $\angle\, a\, b\, c$ and check the inscribed angle theorem.
2. (A) In Mathlib, $\angle\, a\, a\, c = \pi/2$. Explain why, and explain why Thales' theorem holds with $b = a$.
3. (A) Show that Euler's quadrilateral theorem for a parallelogram is the parallelogram law.
4. (B) Let $a, b, c, d$ be on a line in this order. Prove $d(a, c)\, d(b, d) = d(a, b)\, d(c, d) + d(b, c)\, d(a, d)$, so that equality holds in Ptolemy's inequality.
5. (B) Let $a\, b\, c$ be a triangle with circumradius $R$ and with $\angle\, b\, a\, c \le \pi/2$. Use the unoriented inscribed angle theorem to prove $d(b, c) = 2R \sin \angle\, b\, a\, c$.
6. (B) Use the involution property and the theorem on the image of a sphere through the centre to find the image under inversion of a hyperplane that does not contain the centre.
7. (C) Show that a map whose derivative at each point is a positive multiple of an orthogonal map keeps unoriented angles between curves. Use `hasFDerivAt_inversion` to conclude that inversion is conformal away from its centre.

### Notes and history

The inscribed angle theorem is Proposition III.20 of Euclid's *Elements*, and the equality of angles in the same segment is III.21. Thales' theorem is III.31 there. Ptolemy's theorem appears in the *Almagest* of Claudius Ptolemy, where it is used to compute tables of chords. Inversion as a transformation was developed in the nineteenth century. The file `Mathlib.Geometry.Euclidean.Angle.Sphere` lists Joseph Myers as author, `Mathlib.Geometry.Euclidean.Sphere.Ptolemy` lists Manuel Candales and Benjamin Davidson, the inversion files list Yury Kudryashov, and `Mathlib.Geometry.Euclidean.EulerQuadrilateral` lists Daniel Liao.

### Reference

<?reference?>
