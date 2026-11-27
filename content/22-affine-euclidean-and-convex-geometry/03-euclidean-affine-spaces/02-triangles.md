---
title: Triangles
kind: theory
modules:
  - Mathlib.Geometry.Euclidean.Triangle
  - Mathlib.Geometry.Euclidean.Congruence
  - Mathlib.Geometry.Euclidean.Similarity
  - Mathlib.Geometry.Euclidean.BritishFlag
  - Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
explains:
  E3: [EuclideanGeometry.law_cos, EuclideanGeometry.angle_add_angle_add_angle_eq_pi, EuclideanGeometry.angle_eq_angle_of_dist_eq, EuclideanGeometry.law_sin, EuclideanGeometry.side_angle_side, EuclideanGeometry.angle_side_angle, EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two]
  E2: [EuclideanGeometry.angle_eq_of_congruent, EuclideanGeometry.similar_of_angle_angle, EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi, EuclideanGeometry.exterior_angle_eq_angle_add_angle, EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq, EuclideanGeometry.angle_lt_iff_dist_lt]
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

## Triangles

### Overview

This section proves the classical theorems on a triangle from the inner product: the law of cosines, Pythagoras, the isosceles triangle, the angle sum, the law of sines and the congruence criteria, with the non-degeneracy hypotheses that Mathlib needs.

Fix three points $A, B, C$ of a Euclidean affine space $P$. Write $a = d(B, C)$, $b = d(C, A)$, $c = d(A, B)$, and $\alpha = \angle BAC$, $\beta = \angle ABC$, $\gamma = \angle BCA$.

### Definitions

**Definition (Congruent and similar triangles).** The triangles $(A, B, C)$ and $(A', B', C')$ are *congruent* if $d(A, B) = d(A', B')$, $d(B, C) = d(B', C')$ and $d(C, A) = d(C', A')$. They are *similar* if there is $r > 0$ with $d(A', B') = r\, d(A, B)$, $d(B', C') = r\, d(B, C)$ and $d(C', A') = r\, d(C, A)$.

A triangle here is an ordered triple of points, not necessarily distinct.

::: mathlib
`Congruent` · `Mathlib.Topology.MetricSpace.Congruence`

`Congruent v₁ v₂`, notation `v₁ ≅ v₂`, says that two families `v₁ v₂ : ι → P` have the same pairwise `edist`. A triangle is the family `![a, b, c] : Fin 3 → P`. `Similar v₁ v₂`, notation `∼`, asks the same up to a factor `r ≠ 0`.

<?decl Congruent?>
:::

### Theorems and proofs

**Theorem (Law of cosines).** $c^2 = a^2 + b^2 - 2ab\cos\gamma$.

*Proof.* $A - B = (A - C) - (B - C)$. So $c^2 = \|A - C\|^2 - 2\langle A - C, B - C\rangle + \|B - C\|^2 = b^2 - 2\langle A - C, B - C\rangle + a^2$. By Section 1, $\langle A - C, B - C\rangle = ab\cos\gamma$ for all points, also when $C = A$ or $C = B$. $\square$

**Corollary (Pythagoras and its converse).** $c^2 = a^2 + b^2$ if and only if $\gamma = \pi/2$.

*Proof.* By the proof above, $c^2 = a^2 + b^2$ if and only if $\langle A - C, B - C\rangle = 0$. By Section 1 this holds if and only if $\gamma = \pi/2$. $\square$

::: mathlib
`EuclideanGeometry.law_cos` · `Mathlib.Geometry.Euclidean.Triangle`

`law_cos p₁ p₂ p₃ : dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ - 2 * dist p₁ p₂ * dist p₃ p₂ * Real.cos (∠ p₁ p₂ p₃)` has no hypothesis. The vertex is `p₂`. Pythagoras with its converse is `dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two`.

<?decl EuclideanGeometry.law_cos?>
<?decl EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two?>
:::

**Theorem (Pons asinorum).** If $b = c$, then $\beta = \gamma$.

*Proof.* By the law of cosines at $B$ and at $C$, $\langle A - B, C - B\rangle = (c^2 + a^2 - b^2)/2$ and $\langle A - C, B - C\rangle = (a^2 + b^2 - c^2)/2$. Let $b = c$. If $B = C$, then $\beta = \gamma = \pi/2$. If $c = 0$, then $A = B = C$. Otherwise $\cos\beta = a/(2c) = a/(2b) = \cos\gamma$, and $\cos$ is injective on $[0, \pi]$. $\square$

**Theorem (Angle sum).** If $A \ne B$, then $\alpha + \beta + \gamma = \pi$.

*Proof.* First let $A, B, C$ be non-collinear. Put $e_1 = (B - A)/c$. The vector $w = (C - A) - \langle C - A, e_1\rangle e_1$ is orthogonal to $e_1$. It is nonzero, since $C - A$ is not a multiple of $B - A$. Put $e_2 = w/\|w\|$. As in the proof of the triangle inequality for angles, $C - A = b\cos\alpha\, e_1 + b\sin\alpha\, e_2$, with $\sin\alpha > 0$ since $\alpha \in (0, \pi)$. In the orthonormal pair $e_1, e_2$ the vectors are
$$B - A = (c, 0),\quad C - A = (b\cos\alpha, b\sin\alpha),\quad C - B = (b\cos\alpha - c, b\sin\alpha).$$
So $a^2 = (b\cos\alpha - c)^2 + b^2\sin^2\alpha$. The formula for the cosine gives
$$\cos\beta = \frac{\langle A - B, C - B\rangle}{ca} = \frac{c - b\cos\alpha}{a}, \qquad \cos\gamma = \frac{\langle A - C, B - C\rangle}{ab} = \frac{b - c\cos\alpha}{a}.$$
From $\sin\beta \ge 0$ and $\sin^2\beta = 1 - \cos^2\beta = b^2\sin^2\alpha / a^2$ follows $\sin\beta = b\sin\alpha/a$. Now
$$\cos(\alpha + \beta) = \frac{\cos\alpha\,(c - b\cos\alpha) - b\sin^2\alpha}{a} = \frac{c\cos\alpha - b}{a} = -\cos\gamma = \cos(\pi - \gamma),$$
$$\sin(\alpha + \beta) = \frac{\sin\alpha\,(c - b\cos\alpha) + b\sin\alpha\cos\alpha}{a} = \frac{c\sin\alpha}{a} > 0.$$
Since $\alpha + \beta \in (0, 2\pi)$ and its sine is positive, $\alpha + \beta \in (0, \pi)$. Also $\pi - \gamma \in [0, \pi]$, and $\cos$ is injective on $[0, \pi]$. So $\alpha + \beta = \pi - \gamma$.

Now the degenerate cases with $A \ne B$. If $C = A$, then $\beta = \angle ABA = 0$ and $\gamma = \alpha = \pi/2$. If $C = B$, then $\alpha = 0$ and $\beta = \gamma = \pi/2$. If the three points are distinct and collinear, exactly one of them lies strictly between the other two. Its angle is $\pi$ by Section 1, and the other two angles are $0$. $\square$

**Corollary (Law of sines).** $a\sin\beta = b\sin\alpha$, and the same for each pair of sides.

*Proof.* For a non-collinear triangle this is the formula $\sin\beta = b\sin\alpha/a$ of the proof. For distinct collinear points each sine is $0$. If $A = B \ne C$, then $\alpha = \beta = \pi/2$ and $a = b$. If $C = A \ne B$, then $b = 0$ and $\beta = 0$. If $C = B \ne A$, then $a = 0$ and $\alpha = 0$. If all three are equal, all sides are $0$. $\square$

::: mathlib
`EuclideanGeometry.angle_add_angle_add_angle_eq_pi` · `Mathlib.Geometry.Euclidean.Triangle`

`angle_add_angle_add_angle_eq_pi {p₁ p₂} (p₃) (h : p₂ ≠ p₁) : ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π`. Only one pair of points must differ, by the case study above. `law_sin p₁ p₂ p₃ : sin (∠ p₁ p₂ p₃) * dist p₂ p₃ = sin (∠ p₃ p₁ p₂) * dist p₃ p₁` has no hypothesis.

<?decl EuclideanGeometry.angle_add_angle_add_angle_eq_pi?>
<?decl EuclideanGeometry.law_sin?>
<?decl EuclideanGeometry.angle_eq_angle_of_dist_eq?>
:::

**Theorem (Congruence criteria).** The triangles $(A, B, C)$ and $(A', B', C')$ are congruent in each of these cases.

1. (SSS) $c = c'$, $a = a'$, $b = b'$.
2. (SAS) $c = c'$, $\beta = \beta'$, $a = a'$.
3. (ASA) $A, B, C$ are not collinear, $\beta = \beta'$, $a = a'$, $\gamma = \gamma'$.
4. (AAS) $A, B, C$ are not collinear, $\beta = \beta'$, $\gamma = \gamma'$, $b = b'$.

*Proof.* (1) This is the definition. (2) The law of cosines at $B$ gives $b^2 = c^2 + a^2 - 2ca\cos\beta$, and the same expression for $b'^2$. So $b = b'$, and (1) applies. (3) First, $A', B', C'$ are not collinear. Indeed $a' = a > 0$, so $B' \ne C'$. If $A' = B'$, then $\gamma' = \angle B'C'B' = 0$, but $\gamma \in (0, \pi)$. If $A' = C'$, then $\beta' = 0$ in the same way. If the three primed points are distinct and collinear, one of $\beta', \gamma'$ is $0$ or $\pi$. Now the angle sum gives $\alpha' = \pi - \beta' - \gamma' = \alpha$, and $\sin\alpha > 0$. The law of sines gives $b = a\sin\beta/\sin\alpha = b'$. Then (2) applies to $(B, C, A)$. (4) Here $C' \ne A'$, and the same case study as in (3) shows that the primed points are not collinear; for $B' = C'$ it gives $\beta' = \gamma' = \pi/2$, which is impossible as $\alpha > 0$. So $\alpha' = \alpha$. Then (3) applies to $(B, C, A)$, with the side $b$ between the angles $\gamma$ and $\alpha$. $\square$

SAS needs no non-degeneracy, but ASA and AAS do. Congruent triangles have equal angles, `angle_eq_of_congruent`. For similarity Mathlib has AA for a non-collinear triangle (`similar_of_angle_angle`), and SSS similarity is the definition.

::: mathlib
`EuclideanGeometry.side_angle_side` · `Mathlib.Geometry.Euclidean.Congruence`

`side_angle_side (h : ∠ a b c = ∠ a' b' c') (hd₁ : dist a b = dist a' b') (hd₂ : dist b c = dist b' c') : ![a, b, c] ≅ ![a', b', c']`. `angle_side_angle` adds the hypothesis `¬Collinear ℝ {a, b, c}`, as in the proof above.

<?decl EuclideanGeometry.side_angle_side?>
<?decl EuclideanGeometry.angle_side_angle?>
:::

### Examples

**Example (A 3-4-5 triangle).** Let $A = (0, 0)$, $B = (4, 0)$, $C = (0, 3)$. Then $c = 4$, $b = 3$, $a = 5$, and $\alpha = \pi/2$ since $25 = 16 + 9$. The law of cosines gives $\cos\beta = (c^2 + a^2 - b^2)/(2ca) = 4/5$.

**Counterexample (ASA for a degenerate triangle).** On the line $\mathbb{R}$ let $B = 0$, $C = 2$, $A = 1$, and $B' = 0$, $C' = 2$, $A' = 1/2$. Then $\beta = \beta' = 0$, $\gamma = \gamma' = 0$ and $a = a' = 2$. But $c = 1 \ne 1/2 = c'$. The hypothesis $\neg\operatorname{Collinear}$ of `angle_side_angle` excludes this.

### The library around it

`exterior_angle_eq_angle_add_angle` is the exterior angle theorem, and `angle_lt_iff_dist_lt` puts the larger angle opposite the larger side. `Triangle` and `BritishFlag` also hold the theorems of Apollonius (`dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq`), Stewart and the British flag. The converse of pons asinorum, `dist_eq_of_angle_eq_angle_of_angle_ne_pi`, needs $\alpha \ne \pi$: on a line with $B = 0$, $A = 1$, $C = 3$, $\beta = \gamma = 0$ but $b \ne c$. Heron's formula is in `Mathlib.Geometry.Euclidean.Volume.Triangle`, with the area of a triangle, and Chapter 5 proves it.

### Exercises

1. (A) Compute the angles of the triangle with sides $a = 7$, $b = 5$, $c = 3$. Show that $\alpha = 2\pi/3$.
2. (A) Show that an equilateral triangle has three angles $\pi/3$.
3. (B) Prove the exterior angle theorem from the angle sum.
4. (B) Show that $\gamma > \pi/2$ if and only if $c^2 > a^2 + b^2$.
5. (C) Prove that $\beta < \gamma$ implies $b < c$ for a non-collinear triangle. Hint: the law of sines and $\sin\gamma - \sin\beta = 2\cos\frac{\beta+\gamma}{2}\sin\frac{\gamma-\beta}{2}$.
6. (C) Show that SSA fails: give two non-congruent triangles with $c = c'$, $a = a'$ and $\gamma = \gamma'$.

### Notes and history

The pons asinorum is Proposition 5 of Book I of Euclid, and the angle sum is Proposition 32. The file `Mathlib.Geometry.Euclidean.Triangle` has the authors Joseph Myers and Manuel Candales in its header, `Congruence` has Jovan Gerbscheid and Chu Zheng, `Similarity` has Chu Zheng, and `BritishFlag` has Daniel Liao.

### Reference

<?reference?>
