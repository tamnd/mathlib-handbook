---
title: Orientations and oriented angles
kind: theory
modules:
  - Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
  - Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
explains:
  E3: [Orientation.oangle, EuclideanGeometry.oangle, Orientation.oangle_add, Orientation.oangle_rev, Orientation.oangle_eq_angle_or_eq_neg_angle, EuclideanGeometry.oangle_rotate_sign, EuclideanGeometry.oangle_eq_oangle_of_dist_eq]
  E2: [Orientation.oangle_self, Orientation.oangle_add_cyc3, Orientation.oangle_map_complex, Orientation.angle_eq_abs_oangle_toReal, EuclideanGeometry.oangle_rev, EuclideanGeometry.oangle_add, EuclideanGeometry.oangle_self_left, EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear, EuclideanGeometry.oangle_swap₁₂_sign, EuclideanGeometry.oangle_eq_pi_iff_sbtw, Sbtw.oangle_sign_eq, EuclideanGeometry.oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq, EuclideanGeometry.two_zsmul_oangle_of_parallel, EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi]
  E1: auto
families: []
requires: [V07, V13, V15.C06, V16.C06, V22.C01, V22.C02, V22.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Orientations and oriented angles

### Overview

The angle $\angle(x, y)$ of Chapter 3 lies in $[0, \pi]$ and does not see the order of $x$ and $y$. In an oriented plane the oriented angle also records whether the turn from $x$ to $y$ is counterclockwise or clockwise. It takes values in $\mathbb{R}/2\pi\mathbb{Z}$, and its main property is additivity: $\measuredangle(x, y) + \measuredangle(y, z) = \measuredangle(x, z)$.

### Definitions

Let $V$ be a real inner product space of dimension $2$. An *orientation* of $V$ is a class of ordered bases under change of basis with positive determinant (Volume 7). Fix one of the two orientations, and call its bases *positive*.

**Definition (Complex coordinate).** Let $(e_1, e_2)$ be a positive orthonormal basis of $V$. For $x = x_1 e_1 + x_2 e_2$ put $\hat x = x_1 + i x_2 \in \mathbb{C}$.

The map $x \mapsto \hat x$ is a linear isometry, and $\overline{\hat x}\,\hat y = \langle x, y\rangle + i\,\omega(x, y)$ with $\omega(x, y) = x_1 y_2 - x_2 y_1$, the signed area of the parallelogram on $x, y$.

**Definition (Oriented angle).** For $x, y \in V$ the *oriented angle* is
$$\measuredangle(x, y) = \arg\bigl(\overline{\hat x}\,\hat y\bigr) \in \mathbb{R}/2\pi\mathbb{Z}.$$
Since $\arg 0 = 0$, it is $0$ if $x = 0$ or $y = 0$.

This does not depend on the basis: a second positive orthonormal basis gives $\hat x' = \bar u\,\hat x$ with $|u| = 1$, since the change of basis is a rotation. Then $\overline{\hat x'}\,\hat y' = u\bar u\,\overline{\hat x}\,\hat y = \overline{\hat x}\,\hat y$.

::: mathlib
`Orientation.oangle` · `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic`

`o.oangle x y : Real.Angle` is `Complex.arg (o.kahler x y)`, where `Real.Angle` is $\mathbb{R}/2\pi\mathbb{Z}$ and `o.kahler x y = ⟪x, y⟫ + o.areaForm x y • Complex.I` is $\overline{\hat x}\,\hat y$ without a basis. The lemma `oangle_map_complex` gives `o.oangle x y = Complex.arg (conj (f x) * f y)` for an isometry `f : V ≃ₗᵢ[ℝ] ℂ` that carries `o` to `Complex.orientation`.

<?decl Orientation.oangle?>
:::

**Definition (Oriented angle at a point).** Let $P$ be a Euclidean affine plane over $V$. For $A, B, C \in P$ put $\measuredangle ABC = \measuredangle(A - B, C - B)$.

::: mathlib
`EuclideanGeometry.oangle` · `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine`

`EuclideanGeometry.oangle p₁ p₂ p₃` is `o.oangle (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)`, with notation `∡ p₁ p₂ p₃`. The orientation comes from an instance `[Module.Oriented ℝ V (Fin 2)]`. The value is `0` when `p₁ = p₂` (`oangle_self_left`).

<?decl EuclideanGeometry.oangle?>
:::

### Theorems and proofs

**Theorem (Rules for oriented angles).** Let $x, y, z \in V$.

1. $\measuredangle(y, x) = -\measuredangle(x, y)$.
2. If $x, y, z \ne 0$, then $\measuredangle(x, y) + \measuredangle(y, z) = \measuredangle(x, z)$.
3. If $x \ne 0$, then $\measuredangle(x, x) = 0$ and $\measuredangle(-x, x) = \pi$.
4. If $x, y \ne 0$, then $\measuredangle(-x, y) = \measuredangle(x, y) + \pi$. For $r > 0$, $\measuredangle(r x, y) = \measuredangle(x, y)$.

*Proof.* Put $k(x, y) = \overline{\hat x}\,\hat y$. Modulo $2\pi$, $\arg(zw) = \arg z + \arg w$ for $z, w \ne 0$, $\arg \bar z = -\arg z$, and $\arg(rz) = \arg z$ for $r > 0$ (Volume 15). (1) $k(y, x) = \overline{k(x, y)}$. If $k(x, y) = 0$ both sides are $0$. (2) $k(x, y)\,k(y, z) = \overline{\hat x}\,\hat y\,\overline{\hat y}\,\hat z = \|y\|^2\, k(x, z)$, and the factor $\|y\|^2 > 0$ does not change the argument. All three numbers are nonzero, so the arguments add. (3) $k(x, x) = |\hat x|^2 > 0$ and $k(-x, x) = -|\hat x|^2 < 0$, with arguments $0$ and $\pi$. (4) $k(-x, y) = -k(x, y)$, and $\arg(-z) = \arg z + \pi$ modulo $2\pi$ for $z \ne 0$. Also $k(rx, y) = r\,k(x, y)$. $\square$

Parts (1) and (2) give the cyclic rule $\measuredangle(x, y) + \measuredangle(y, z) + \measuredangle(z, x) = 0$ for nonzero vectors.

**Theorem (Oriented and unoriented angles).** Let $x, y \ne 0$. Then $\cos\measuredangle(x, y) = \cos\angle(x, y)$, and $\measuredangle(x, y) = \angle(x, y)$ or $\measuredangle(x, y) = -\angle(x, y)$. The sign of $\measuredangle(x, y)$ is the sign of $\omega(x, y)$. Also $\angle(x, y)$ is the absolute value of the representative of $\measuredangle(x, y)$ in $(-\pi, \pi]$.

*Proof.* Let $z = k(x, y) = \langle x, y\rangle + i\,\omega(x, y)$, so $|z| = \|x\|\,\|y\|$. Write $\theta = \arg z \in (-\pi, \pi]$. Then $\cos\theta = \operatorname{Re} z / |z| = \langle x, y\rangle / (\|x\|\,\|y\|) = \cos\angle(x, y)$. Since $\cos$ is injective on $[0, \pi]$ and $|\theta| \in [0, \pi]$ with $\cos|\theta| = \cos\theta$, it follows that $|\theta| = \angle(x, y)$. The sign of $\theta$ is that of $\sin\theta = \operatorname{Im} z / |z| = \omega(x, y)/|z|$. $\square$

**Corollary (Zero and straight oriented angles).** $\measuredangle(x, y) = 0$ if and only if $x = 0$, $y = 0$ or $y$ is a positive multiple of $x$. For $x, y \ne 0$, $\measuredangle(x, y) = \pi$ if and only if $y$ is a negative multiple of $x$. Hence $\measuredangle(x, y) \in \{0, \pi\}$ if and only if $x, y$ are linearly dependent.

*Proof.* For nonzero vectors, $\measuredangle(x, y) = 0$ if and only if $\angle(x, y) = 0$ by the theorem, and Chapter 3 applies. The case $\pi$ is the same. $\square$

::: mathlib
`Orientation.oangle_add` · `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic`

`oangle_add (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) : o.oangle x y + o.oangle y z = o.oangle x z`. `oangle_rev` has no hypothesis, and `oangle_add_cyc3` is the cyclic rule. `oangle_eq_angle_or_eq_neg_angle (hx : x ≠ 0) (hy : y ≠ 0)` gives the two cases of the theorem. `angle_eq_abs_oangle_toReal` is the last sentence.

<?decl Orientation.oangle_add?>
<?decl Orientation.oangle_rev?>
<?decl Orientation.oangle_eq_angle_or_eq_neg_angle?>
:::

By the corollary, $\measuredangle ABC \in \{0, \pi\}$, and so its sign is $0$, exactly for collinear $A, B, C$ (`oangle_eq_zero_or_eq_pi_iff_collinear`).

**Theorem (Sign of a triangle).** For all $A, B, C$, the oriented angles $\measuredangle ABC$, $\measuredangle BCA$ and $\measuredangle CAB$ have the same sign. Exchanging two points changes the sign.

*Proof.* The sign of $\measuredangle(x, y)$ is the sign of $\omega(x, y)$, also for a zero vector. Put $u = A - B$ and $w = C - B$. The sign of $\measuredangle ABC$ is the sign of $\omega(u, w)$. For $\measuredangle BCA$ the vectors are $B - C = -w$ and $A - C = u - w$. Since $\omega$ is bilinear and antisymmetric, $\omega(-w, u - w) = -\omega(w, u) + \omega(w, w) = \omega(u, w)$. Apply this twice to get $\measuredangle CAB$. For the exchange, $\measuredangle CBA = -\measuredangle ABC$ by rule (1). $\square$

**Theorem (Oriented angle sum).** If $A, B, C$ are pairwise distinct, then $\measuredangle ABC + \measuredangle BCA + \measuredangle CAB = \pi$ in $\mathbb{R}/2\pi\mathbb{Z}$.

*Proof.* Put $u = B - A$, $v = C - B$, $w = A - C$. They are nonzero. By rule (4) and rule (1),
$$\measuredangle ABC = \measuredangle(-u, v) = \measuredangle(u, v) + \pi,\quad \measuredangle BCA = \measuredangle(-v, w) = \measuredangle(v, w) + \pi,\quad \measuredangle CAB = \measuredangle(-w, u) = \measuredangle(w, u) + \pi.$$
The cyclic rule gives $\measuredangle(u, v) + \measuredangle(v, w) + \measuredangle(w, u) = 0$. So the sum is $3\pi = \pi$ modulo $2\pi$. $\square$

The proof does not use $u + v + w = 0$: modulo $2\pi$ the sum is a formal identity. With the sign theorem it gives the sum of Chapter 3: for a non-collinear triangle with positive sign, the unoriented angles have a sum $\equiv \pi$ modulo $2\pi$ in $(0, 3\pi)$, so equal to $\pi$.

**Corollary (Isosceles triangle).** If $d(A, B) = d(A, C)$, then $\measuredangle ABC = \measuredangle BCA$. If also $B \ne C$, then $\measuredangle CAB = \pi - 2\measuredangle ABC$.

*Proof.* If $A, B, C$ are not collinear, $\angle ABC = \angle BCA$ by Chapter 3, and the signs are equal by the sign theorem. If they are collinear, then $B = C$ or $A$ is the midpoint of $B$ and $C$, and both angles are $0$. For the second claim, $B \ne C$ forces $A \ne B$, $A \ne C$; apply the angle sum. $\square$

::: mathlib
`EuclideanGeometry.oangle_rotate_sign` · `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine`

`oangle_rotate_sign p₁ p₂ p₃ : (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign` and `oangle_swap₁₂_sign : -(∡ p₁ p₂ p₃).sign = (∡ p₂ p₁ p₃).sign` are the sign theorem. The angle sum is `oangle_add_oangle_add_oangle_eq_pi` in `Mathlib.Geometry.Euclidean.Triangle`, with three hypotheses of distinctness. The isosceles case `oangle_eq_oangle_of_dist_eq` has no other hypothesis, and `oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq` needs `p₂ ≠ p₃`.

<?decl EuclideanGeometry.oangle_rotate_sign?>
<?decl EuclideanGeometry.oangle_eq_oangle_of_dist_eq?>
<?decl EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi?>
:::

### Examples

**Example (Angles in $\mathbb{C}$).** Take $V = \mathbb{C}$ with the orientation of the basis $(1, i)$, so $\hat x = x$. Then $\measuredangle(1, i) = \pi/2$ and $\measuredangle(i, 1) = -\pi/2$. For the triangle $A = 0$, $B = 1$, $C = i$: $\measuredangle ABC = \arg(\overline{(-1)}(i - 1)) = \arg(1 - i) = -\pi/4$, $\measuredangle BCA = \arg(\overline{(1 - i)}(-i)) = \arg(1 - i) = -\pi/4$ and $\measuredangle CAB = \arg(\bar i \cdot 1) = -\pi/2$. The sum is $-\pi = \pi$ modulo $2\pi$, and all three signs are $-1$. The turn from the ray $BA$ to the ray $BC$ is clockwise.

**Counterexample (Additivity with a zero vector).** Let $x = 1$, $y = 0$, $z = i$ in $\mathbb{C}$. Then $\measuredangle(x, y) + \measuredangle(y, z) = 0 \ne \pi/2 = \measuredangle(x, z)$. So `oangle_add` needs three nonzero vectors.

### The library around it

`Sbtw.oangle_sign_eq`: if $B$ is strictly between $A$ and $C$, then $\measuredangle AXB$ and $\measuredangle BXC$ have the same sign. `oangle_eq_pi_iff_sbtw` is the straight angle. Lemmas with `two_zsmul` work with $2\measuredangle$, the angle between lines, as `two_zsmul_oangle_of_parallel`.

### Exercises

1. (A) Compute $\measuredangle(1, -1 + \sqrt 3\, i)$ and $\measuredangle(-1 + \sqrt 3\, i, 1)$ in $\mathbb{C}$.
2. (A) Show that $\measuredangle(x, -y) = \measuredangle(x, y) + \pi$ for $x, y \ne 0$.
3. (B) Show that reversing the orientation replaces each $\measuredangle(x, y)$ by $-\measuredangle(x, y)$.
4. (B) Let $ABC$ be a triangle with $\measuredangle ABC = \pi/2$. Show that $\measuredangle BCA + \measuredangle CAB = \pi/2$ in $\mathbb{R}/2\pi\mathbb{Z}$.
5. (B) Show that $\measuredangle(x, y) = \measuredangle(x', y')$ for nonzero vectors if and only if $\measuredangle(x, x') = \measuredangle(y, y')$.
6. (C) Show that $2\measuredangle(x, y)$ depends only on the lines $\mathbb{R}x$ and $\mathbb{R}y$ for nonzero $x, y$.

### Notes and history

The file `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` has the authors Joseph Myers and Heather Macbeth in its header, and `Angle.Oriented.Affine` has Joseph Myers.

### Reference

<?reference?>
