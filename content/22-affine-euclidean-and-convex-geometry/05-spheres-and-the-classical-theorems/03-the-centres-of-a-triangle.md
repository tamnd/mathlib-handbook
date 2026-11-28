---
title: The centres of a triangle
kind: theory
modules:
  - Mathlib.Geometry.Euclidean.Circumcenter
  - Mathlib.Geometry.Euclidean.Altitude
  - Mathlib.Geometry.Euclidean.MongePoint
  - Mathlib.Geometry.Euclidean.NinePointCircle
  - Mathlib.Geometry.Euclidean.Simplex
  - Mathlib.Geometry.Euclidean.Incenter.Basic
  - Mathlib.Geometry.Euclidean.Incenter.SouthPole
  - Mathlib.Geometry.Euclidean.Angle.Bisector
  - Mathlib.Geometry.Euclidean.Angle.Incenter
  - Mathlib.Geometry.Euclidean.Volume.Def
  - Mathlib.Geometry.Euclidean.Volume.Basic
  - Mathlib.Geometry.Euclidean.Volume.Triangle
  - Mathlib.Geometry.Euclidean.Volume.Incenter
  - Mathlib.Geometry.Euclidean.Volume.Measure
  - Mathlib.Geometry.Euclidean.Volume.MeasureSimplex
  - Mathlib.Geometry.Euclidean.Incenter
explains:
  E3: [Affine.Simplex.circumsphere, Affine.Simplex.circumcenter, Affine.Simplex.circumradius, Affine.Simplex.altitude, Affine.Simplex.height, Affine.Simplex.mongePoint, Affine.Triangle.orthocenter, Affine.Triangle.orthocenter_mem_altitude, Affine.Simplex.ninePointCircle, Affine.Triangle.altitudeFoot_mem_ninePointCircle, Affine.Simplex.insphere, Affine.Simplex.incenter, Affine.Simplex.volume, Affine.Simplex.volume_eq_inradius_mul, Affine.Triangle.volume_eq_sqrt_mul_sub_mul_sub_mul_sub]
  E2: [Affine.Simplex.circumsphere_unique_dist_eq, EuclideanGeometry.existsUnique_dist_eq_of_insert, Affine.Simplex.dist_circumcenter_eq_circumradius, Affine.Simplex.circumcenter_mem_affineSpan, EuclideanGeometry.exists_circumsphere_eq_of_cospherical, Affine.Simplex.altitudeFoot, Affine.Simplex.mongePoint_eq_smul_vsub_vadd_circumcenter, Affine.Simplex.mongePlane, Affine.Triangle.orthocenter_eq_mongePoint, Affine.Triangle.orthocenter_eq_smul_vsub_vadd_circumcenter, Affine.Triangle.altitude_eq_mongePlane, Affine.Triangle.dist_orthocenter_reflection_circumcenter, EuclideanGeometry.OrthocentricSystem, Affine.Simplex.AcuteAngled, Affine.Simplex.eulerPoint, Affine.Triangle.eulerPoint_eq_midpoint, Affine.Simplex.faceOppositeCentroid_mem_ninePointCircle, Affine.Simplex.isDiameter_ninePointCircle, Affine.Simplex.ninePointCircle_eq_circumsphere_medial, Affine.Simplex.excenterWeightsUnnorm, Affine.Simplex.ExcenterExists, Affine.Simplex.exsphere, Affine.Simplex.excenter, Affine.Simplex.inradius, Affine.Simplex.touchpoint, Affine.Simplex.dist_incenter, Affine.Simplex.incenter_mem_interior, Affine.Triangle.angle_incenter_eq_angle_div_two, EuclideanGeometry.dist_orthogonalProjection_eq_iff_oangle_eq, Affine.Simplex.southPole, Affine.Triangle.dist_southPole_point_eq_dist_southPole_incenter, Affine.Simplex.volume_eq, Affine.Simplex.volume_pos, Affine.Triangle.volume_eq_height_mul, Affine.Triangle.volume_eq_mul_sin]
  E1: auto
families: []
requires: [V07, V16.C06, V16.C07, V22.C02, V22.C03, V22.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The centres of a triangle

### Overview

This section treats the classical centres of a triangle: the circumcentre, the centroid, the orthocentre, the incentre, the centre of the nine-point circle and the excentres. Mathlib defines most of them for a simplex of any dimension. A triangle is a 2-simplex, as in Chapter 2.

The section proves that each simplex has a unique circumsphere, that the altitudes of a triangle meet on the Euler line, that the nine-point circle passes through nine points, and that the inradius gives the area formula $\text{area} = r \cdot s$. The proofs use vectors from the circumcentre, the orthogonal projections of Chapter 3 and Thales' theorem.

### Definitions

Let $s$ be an $n$-simplex in a Euclidean affine space $P$, with vertices $p_0, \dots, p_n$ and affine span $A$. The face opposite $p_i$ is the simplex on the other $n$ vertices.

**Definition (Circumsphere).** The *circumsphere* of $s$ is the unique sphere with centre in $A$ that contains all the vertices. Its centre is the *circumcentre* $o$ and its radius the *circumradius* $R$. For a triangle these are the circumcircle and its centre.

::: mathlib
`Affine.Simplex.circumsphere` · `Mathlib.Geometry.Euclidean.Circumcenter`

`s.circumsphere : Sphere P` is defined by choice from the existence and uniqueness theorem below, and `s.circumcenter` and `s.circumradius` are its two fields. The property of the choice is `circumsphere_unique_dist_eq`. The centre must lie in the span, because a triangle in $\mathbb{R}^3$ lies on many spheres. Common lemmas are `dist_circumcenter_eq_circumradius` and `circumcenter_mem_affineSpan`.

<?decl Affine.Simplex.circumsphere?>
:::

**Definition (Altitude, foot, height).** The *altitude* from $p_i$ is the line in $A$ through $p_i$ orthogonal to the opposite face. Its *foot* is the orthogonal projection of $p_i$ onto the affine span of the opposite face, and the *height* $h_i$ is the distance from $p_i$ to the foot.

::: mathlib
`Affine.Simplex.altitude` · `Mathlib.Geometry.Euclidean.Altitude`

`s.altitude i` is the intersection of `AffineSubspace.mk' (s.points i) (direction of the opposite face).orthogonal` with the span of the simplex. `s.altitudeFoot i` is `(s.faceOpposite i).orthogonalProjectionSpan (s.points i)` and `s.height i` is `dist (s.points i) (s.altitudeFoot i)`. The foot and the height need `[NeZero n]`, because a 0-simplex has no opposite face.

<?decl Affine.Simplex.height?>
:::

**Definition (Monge point and orthocentre).** Let $g$ be the centroid of $s$ and $n \ge 2$. The *Monge point* of $s$ is $o + \frac{n + 1}{n - 1}(g - o)$. For a triangle, $n = 2$, the Monge point is $o + 3(g - o)$ and it is called the *orthocentre* $h$.

So the orthocentre is defined by its position on the line through $o$ and $g$, and its property is a theorem. This definition works in each dimension: the Monge point is the common point of the *Monge planes*, which are the altitudes for a triangle.

::: mathlib
`Affine.Simplex.mongePoint` · `Mathlib.Geometry.Euclidean.MongePoint`

`s.mongePoint` is `((n + 1 : ℕ) / (n - 1 : ℕ) : ℝ) • (centroid -ᵥ s.circumcenter) +ᵥ s.circumcenter`, as `mongePoint_eq_smul_vsub_vadd_circumcenter` states. For `n = 1` the division by zero gives the circumcentre, a value of no geometric meaning. `Affine.Triangle.orthocenter t` is `t.mongePoint` (`orthocenter_eq_mongePoint`), and `orthocenter_eq_smul_vsub_vadd_circumcenter` gives `3 • (centroid -ᵥ circumcenter) +ᵥ circumcenter`.

<?decl Affine.Triangle.orthocenter?>
:::

**Definition (Nine-point circle).** The *nine-point circle* of a triangle has centre $o + \frac32 (g - o)$ and radius $R/2$. In dimension $n$ the same construction, with centre $o + \frac{n+1}{n}(g - o)$ and radius $R/n$, gives the $3(n+1)$-point sphere.

**Definition (Insphere and excentres).** The *insphere* of $s$ is a sphere with centre $i$ in the interior of $s$ that is tangent to the affine span of each face. Its centre is the *incentre* and its radius the *inradius* $r$. An *exsphere* is tangent to the spans of all faces with its centre on the other side of some faces.

::: mathlib
`Affine.Simplex.insphere` · `Mathlib.Geometry.Euclidean.Incenter.Basic`

Mathlib defines the excentres first. For a finite set `signs` of indices, the unnormalized weight of vertex `i` is `excenterWeightsUnnorm signs i = (if i ∈ signs then -1 else 1) * (s.height i)⁻¹`. `s.excenter signs` is the normalized affine combination, `ExcenterExists signs` says that the sum is not zero, and `s.exsphere signs` is the sphere. The insphere is the case `signs = ∅`. `touchpoint signs i` is the projection of the centre onto face `i`. `s.incenter` and `s.inradius` are the fields of `s.insphere`.

<?decl Affine.Simplex.insphere?>
:::

**Definition (Volume of a simplex).** The *volume* of a 0-simplex is $1$, and the volume of an $(n+1)$-simplex is $\frac{1}{n+1} h_0 \cdot V_0$, where $V_0$ is the volume of the face opposite $p_0$. For a triangle this is half the base times the height, the area.

::: mathlib
`Affine.Simplex.volume` · `Mathlib.Geometry.Euclidean.Volume.Def`

The definition is the recursion above. `volume_eq` shows that the base can be the face opposite any vertex, and `volume_pos` that the volume is positive. The file `Mathlib.Geometry.Euclidean.Volume.MeasureSimplex` proves that it is the Hausdorff measure of the closed simplex.

<?decl Affine.Simplex.volume?>
:::

### Theorems and proofs

**Theorem (Circumsphere).** Let $p_0, \dots, p_n$ be affinely independent and $A$ their affine span. There is exactly one sphere with centre in $A$ that contains all $p_i$.

*Proof.* Induction on $n$. For $n = 0$ the sphere is $S(p_0, 0)$, and its centre must be $p_0$ because $A = \{p_0\}$. For the step, let $B$ be the span of $p_0, \dots, p_{n-1}$ and $S(c, \rho)$ the unique sphere for these points with $c \in B$. Let $p = p_n \notin B$, and let $q$ be its orthogonal projection onto $B$. Put $y = d(p, q) > 0$, $x = d(c, q)$, $e = (p - q)/y$, and look for the new centre in the form $c' = c + t e$. Since $e$ is orthogonal to $B$, Pythagoras gives $d(c', p_j)^2 = \rho^2 + t^2$ for $j < n$ and $d(c', p)^2 = x^2 + (y - t)^2$. These are equal exactly when $t = (x^2 + y^2 - \rho^2)/(2y)$. This gives existence. For uniqueness, let $c''$ be a centre in $A$ for all the points, and let $c_B$ be its projection onto $B$. Then $d(c'', p_j)^2 = d(c'', c_B)^2 + d(c_B, p_j)^2$ for $j < n$, so $c_B$ is equidistant from $p_0, \dots, p_{n-1}$, and $c_B = c$ by the induction hypothesis. So $c'' = c + t e$ for some $t$, and $t$ is the unique solution above. $\square$

::: mathlib
`Affine.Simplex.circumsphere_unique_dist_eq` · `Mathlib.Geometry.Euclidean.Circumcenter`

The statement has an existence part and a uniqueness part. The induction step is `EuclideanGeometry.existsUnique_dist_eq_of_insert`, whose proof uses the numbers $x$, $y$ and $t$ above. The lemma `exists_circumsphere_eq_of_cospherical` says that in an $n$-dimensional space, all $n$-simplices with vertices in one cospherical set have the same circumsphere.

<?decl Affine.Simplex.circumsphere_unique_dist_eq?>
:::

For the next theorems write vectors from the circumcentre: $a = p_0 - o$, $b = p_1 - o$, $c = p_2 - o$ for a triangle $p_0 p_1 p_2$. Then $\|a\| = \|b\| = \|c\| = R$ and the centroid is $g = o + \frac13(a + b + c)$, so the orthocentre is
$$h = o + a + b + c.$$

**Theorem (Orthocentre).** The three altitudes of a triangle pass through the orthocentre $h$. So they meet in one point, and $o$, $g$, $h$ lie on one line, the *Euler line*, with $h - o = 3(g - o)$.

*Proof.* The point $h$ is in the plane $A$ of the triangle. Since $h - p_0 = b + c$,
$$\langle h - p_0, p_1 - p_2 \rangle = \langle b + c, b - c\rangle = \|b\|^2 - \|c\|^2 = 0.$$
So $h$ lies on the line in $A$ through $p_0$ orthogonal to the side $p_1 p_2$, which is the altitude from $p_0$. The same computation works for the other two vertices. The Euler line statement is the definition of $h$. $\square$

::: mathlib
`Affine.Triangle.orthocenter_mem_altitude` · `Mathlib.Geometry.Euclidean.MongePoint`

The statement is `t.orthocenter ∈ t.altitude i₁` for each `i₁ : Fin 3`. Mathlib proves it from `altitude_eq_mongePlane` and the general fact that the Monge point lies on each Monge plane. The file also has `dist_orthocenter_reflection_circumcenter` and the predicate `EuclideanGeometry.OrthocentricSystem`.

<?decl Affine.Triangle.orthocenter_mem_altitude?>
:::

**Theorem (Nine-point circle).** Let $N = o + \frac12(a + b + c)$, the midpoint of $o$ and $h$. The circle with centre $N$ and radius $R/2$ in the plane of the triangle passes through the three midpoints of the sides, the three midpoints of $h$ and a vertex, and the three feet of the altitudes.

*Proof.* The midpoint of $p_1 p_2$ is $m_0 = o + \frac12(b + c)$, so $m_0 - N = -\frac12 a$, a vector of length $R/2$. The midpoint of $h$ and $p_0$ is $e_0 = o + \frac12(2a + b + c)$, so $e_0 - N = \frac12 a$, also of length $R/2$. So $m_0$ and $e_0$ are on the circle and they are the ends of a diameter. Let $f_0$ be the foot of the altitude from $p_0$. The point $e_0$ is on the altitude, by the theorem above, and $m_0$ is on the side $p_1 p_2$. If $f_0 = m_0$, there is nothing to prove. Otherwise the lines $f_0 e_0$ and $f_0 m_0$ are orthogonal, so $\angle\, e_0\, f_0\, m_0 = \pi/2$, and Thales' theorem puts $f_0$ on the circle with diameter $e_0 m_0$. The other vertices are the same. $\square$

::: mathlib
`Affine.Triangle.altitudeFoot_mem_ninePointCircle` · `Mathlib.Geometry.Euclidean.NinePointCircle`

The statement is `t.altitudeFoot i ∈ t.ninePointCircle` for each vertex. The midpoints of the sides are the centroids of the faces, and `faceOppositeCentroid_mem_ninePointCircle` puts them on the circle in each dimension. The points $e_i$ are `eulerPoint`, with `eulerPoint_eq_midpoint` for a triangle, and `isDiameter_ninePointCircle` is the diameter of the proof. `ninePointCircle_eq_circumsphere_medial` says that the nine-point circle is the circumcircle of the medial triangle.

<?decl Affine.Triangle.altitudeFoot_mem_ninePointCircle?>
:::

**Theorem (Incentre).** Let $s$ be an $n$-simplex with $n \ge 1$. Put $w_j = h_j^{-1} / \sum_k h_k^{-1}$ and $i = \sum_j w_j p_j$. Then $i$ is in the interior of $s$, and its distance to the span of each face is $r = (\sum_k h_k^{-1})^{-1}$. So $S(i, r)$ is the insphere.

*Proof.* The weights are positive and sum to $1$, so $i$ is an interior point. Fix a face, opposite $p_j$, and let $f$ be the foot of the altitude from $p_j$. Put $\delta(x) = \sigma_v(f, x)$, the signed distance of Chapter 3 along $v = p_j - f$. Then $\delta(x)$ is the distance from $x$ to the span of the face for $x$ on the side of $p_j$. The function $\delta$ is affine, it is $0$ at each vertex of the face and $h_j$ at $p_j$. So $\delta(i) = \sum_k w_k \delta(p_k) = w_j h_j = (\sum_k h_k^{-1})^{-1}$. This is the same number for each face. $\square$

The same computation with weights $\pm h_j^{-1}$ gives the excentres, when the sum of the weights is not zero. For a triangle, $a h_0 = b h_1 = c h_2$, so $h_j^{-1}$ is proportional to the opposite side. This gives $i = (a p_0 + b p_1 + c p_2)/(a + b + c)$.

::: mathlib
`Affine.Simplex.incenter` · `Mathlib.Geometry.Euclidean.Incenter.Basic`

`incenter_mem_interior` and `dist_incenter` (the distance to each touchpoint is `s.inradius`) are the two parts of the theorem. In a triangle, `Affine.Triangle.angle_incenter_eq_angle_div_two` says that the incentre bisects each angle. Its proof uses the bisector criterion `dist_orthogonalProjection_eq_iff_oangle_eq` of `Mathlib.Geometry.Euclidean.Angle.Bisector`.

<?decl Affine.Simplex.incenter?>
:::

**Theorem (Volume and inradius).** For an $n$-simplex with faces of volume $F_0, \dots, F_n$, the volume is $V = \frac1n\, r \sum_j F_j$. For a triangle with semiperimeter $\sigma$, the area is $r \sigma$.

*Proof.* With the face opposite $p_j$ as base, $V = \frac1n h_j F_j$, so $h_j^{-1} = F_j/(nV)$. Then $r^{-1} = \sum_j h_j^{-1} = \sum_j F_j/(nV)$. $\square$

::: mathlib
`Affine.Simplex.volume_eq_inradius_mul` · `Mathlib.Geometry.Euclidean.Volume.Incenter`

The statement is `s.volume = (↑n)⁻¹ * s.inradius * ∑ i, (s.faceOpposite i).volume`. The general form for exspheres is `ExcenterExists.volume_eq_exradius_mul`.

<?decl Affine.Simplex.volume_eq_inradius_mul?>
:::

**Theorem (Heron).** A triangle with sides $a, b, c$ and semiperimeter $\sigma = (a+b+c)/2$ has area $\sqrt{\sigma(\sigma - a)(\sigma - b)(\sigma - c)}$.

*Proof.* The area is $\frac12 a c \sin\beta$, where $\beta$ is the angle between the sides $a$ and $c$. The law of cosines gives $\cos\beta = (a^2 + c^2 - b^2)/(2ac)$, and $\sin\beta \ge 0$. So $16\,\text{area}^2 = 4a^2c^2 - (a^2 + c^2 - b^2)^2$, and this factors as $(a + b + c)(-a + b + c)(a - b + c)(a + b - c)$. $\square$

::: mathlib
`Affine.Triangle.volume_eq_sqrt_mul_sub_mul_sub_mul_sub` · `Mathlib.Geometry.Euclidean.Volume.Triangle`

The proof goes through `volume_eq_height_mul` and `volume_eq_mul_sin`, then a `linear_combination` with the law of cosines and $\sin^2 + \cos^2 = 1$, as in the proof above.

<?decl Affine.Triangle.volume_eq_sqrt_mul_sub_mul_sub_mul_sub?>
:::

### Examples

**Example (A right triangle).** Let $p_0 = (0, 0)$, $p_1 = (4, 0)$, $p_2 = (0, 3)$. By Thales the circumcentre is the midpoint of the hypotenuse, $o = (2, 3/2)$, and $R = 5/2$. The centroid is $g = (4/3, 1)$, so $h = o + 3(g - o) = (0, 0)$: the orthocentre is the vertex with the right angle. The nine-point centre is $N = (1, 3/4)$ with radius $5/4$. It passes through the midpoint $(2, 0)$ of a leg, and $d((2, 0), N)^2 = 1 + 9/16 = 25/16$.

**Example (Inradius and Heron).** In the same triangle, $\sigma = 6$ and Heron gives $\sqrt{6 \cdot 2 \cdot 3 \cdot 1} = 6$, the area $\frac12 \cdot 4 \cdot 3$. So $r = 6/6 = 1$. The weights $h_j^{-1}$ are proportional to the opposite sides $5, 3, 4$, so $i = (5(0,0) + 3(4,0) + 4(0,3))/12 = (1, 1)$, at distance $1$ from both axes.

**Example (An equilateral triangle).** For an equilateral triangle $o = g$, so $h = g$ and the Euler line is not defined. All four centres coincide, and $r = R/2$: the incircle is the nine-point circle.

### The library around it

A simplex in Mathlib is `Affine.Simplex ℝ P n`, a family `Fin (n + 1) → P` with a proof of affine independence (Chapter 2), and `Affine.Triangle ℝ P` is the case `n = 2`. Only the orthocentre and some angle statements are special to triangles. `Affine.Simplex.AcuteAngled` in `Mathlib.Geometry.Euclidean.Simplex` says that each angle at a vertex is acute.

The excentres use a `Finset` of signs, because in dimension $3$ or more the number of exspheres depends on the simplex. The file `Mathlib.Geometry.Euclidean.Incenter.SouthPole` defines the *south pole* of a vertex, the second point where the line from the vertex through the incentre meets the circumcircle. `Affine.Triangle.dist_southPole_point_eq_dist_southPole_incenter` is the incenter-excenter lemma: the south pole of $p_0$ is equidistant from $p_1$ and from the incentre.

The module `Mathlib.Geometry.Euclidean.Volume.Measure` gives the measure that matches this volume. The Euclidean Hausdorff measure `MeasureTheory.Measure.euclideanHausdorffMeasure d`, with notation `μHE[d]`, is the $d$-dimensional Hausdorff measure multiplied by a constant. The constant is chosen so that `μHE[d]` is the Lebesgue measure on `EuclideanSpace ℝ (Fin d)`: this is `EuclideanSpace.euclideanHausdorffMeasure_eq_volume`, and `InnerProductSpace.euclideanHausdorffMeasure_eq_volume` gives the same for any inner product space of dimension $d$. The measure is defined on any metric space, so it measures a $d$-dimensional set inside a space of higher dimension. Isometries preserve it (`Isometry.euclideanHausdorffMeasure_image`), and so does the inclusion of an affine subspace (`AffineSubspace.euclideanHausdorffMeasure_coe_image`). A homothety of ratio $c$ multiplies it by $\|c\|^d$ (`MeasureTheory.euclideanHausdorffMeasure_homothety_image`). For $d_1 < d_2$, `MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top` says that a set has $d_2$-measure $0$ or $d_1$-measure $\infty$.

The module `Mathlib.Geometry.Euclidean.Volume.MeasureSimplex` connects the two notions. `Affine.Simplex.euclideanHausdorffMeasure_real_closedInterior` proves that the measure of the closed simplex satisfies the recursion of the definition, $\mu(S) = \frac{1}{n+1} h_i \, \mu(F_i)$ for each vertex $i$, and `Affine.Simplex.volume_eq_euclideanHausdorffMeasure_real_closedInterior` concludes that `s.volume` is the `μHE[n]` measure of `s.closedInterior`. When the simplex fills its space, `Affine.Simplex.volume_eq_volume_real_closedInterior` gives the Lebesgue measure.

The index of this edition has no declaration for Feuerbach's theorem, that the nine-point circle touches the incircle and the three excircles.

### Exercises

1. (A) Find the circumcentre, centroid, orthocentre and nine-point centre of the triangle $(0, 0)$, $(6, 0)$, $(2, 4)$. Check that they lie on one line.
2. (A) Show that the incentre of the triangle $(0, 0)$, $(5, 0)$, $(0, 12)$ is $(2, 2)$.
3. (A) Use Mathlib's definition of `mongePoint` to explain the value of `s.mongePoint` for a 1-simplex.
4. (B) Show that $h = o$ if and only if the triangle is equilateral.
5. (B) Prove that the reflection of $h$ in the side $p_1 p_2$ lies on the circumcircle. Use the formula $h = o + a + b + c$.
6. (B) Let $p_0 p_1 p_2 p_3$ be a regular tetrahedron with edge $1$ in $\mathbb{R}^3$. Compute its height, its volume and its inradius, and check the formula $V = \frac13 r \sum_j F_j$.
7. (B) Prove that the excentre opposite $p_0$ of a triangle is $(-a p_0 + b p_1 + c p_2)/(-a + b + c)$, and that its distance to each side line is $\text{area}/(\sigma - a)$.
8. (C) Show that for an $n$-simplex with $n \ge 2$, the point $o + \frac{n+1}{n-1}(g - o)$ lies on the hyperplane through the centroid of $p_2, \dots, p_n$ that is orthogonal to $p_1 - p_0$. Use vectors from $o$.

### Notes and history

The line through the circumcentre, the centroid and the orthocentre is named after Leonhard Euler. The area formula is named after Heron of Alexandria. The nine-point circle is often credited to Karl Wilhelm Feuerbach, who proved its tangency to the incircle and the excircles. The Monge point is named after Gaspard Monge. The source files list Joseph Myers as author of `Circumcenter`, `Altitude`, `MongePoint`, `Incenter.Basic`, `Incenter.SouthPole`, `Angle.Bisector` and `Angle.Incenter`, Joseph Myers and Chu Zheng for `Simplex`, Weiyi Wang for `NinePointCircle` and the volume files, and Weiyi Wang and Matt Kempster for `Volume.Triangle`.

### Reference

<?reference?>
