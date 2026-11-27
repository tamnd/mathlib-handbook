---
title: Rotations and right-angled triangles
kind: theory
modules:
  - Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
  - Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
  - Mathlib.Geometry.Euclidean.Angle.Oriented.Projection
explains:
  E3: [Orientation.rotation, Orientation.rotation_rotation, Orientation.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero, Orientation.exists_linearIsometryEquiv_eq_of_det_pos, Orientation.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two, EuclideanGeometry.oangle_right_eq_arctan_of_oangle_eq_pi_div_two, EuclideanGeometry.oangle_self_orthogonalProjection]
  E2: [Orientation.rotation_apply, Orientation.rotation_symm, Orientation.rotation_pi, Orientation.rotation_pi_div_two, Orientation.rotation_trans, Orientation.det_rotation, Orientation.rotation_map_complex, Orientation.rotation_oangle_eq_iff_norm_eq, Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two, EuclideanGeometry.dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint, Orientation.oangle_add_right_smul_rotation_pi_div_two, EuclideanGeometry.cos_oangle_right_of_oangle_eq_pi_div_two, EuclideanGeometry.cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two, EuclideanGeometry.two_zsmul_oangle_self_orthogonalProjection]
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

## Rotations and right-angled triangles

### Overview

In an oriented plane each angle $\theta \in \mathbb{R}/2\pi\mathbb{Z}$ gives a rotation $\rho_\theta$. The oriented angle from $x$ to $y$ is the rotation that turns the ray of $x$ into the ray of $y$. The rotation by $\pi/2$ describes right angles and the trigonometry of right-angled triangles.

### Definitions

Keep the oriented plane $V$ of Section 1, its complex coordinate $x \mapsto \hat x$ for a positive orthonormal basis, and the area form $\omega$.

**Definition (Right-angle rotation).** $J : V \to V$ is the linear map with $\widehat{Jx} = i\,\hat x$.

Then $J$ is an isometry, $J^2 = -1$, and $\langle Jx, y\rangle = \operatorname{Re}(-i\,\overline{\hat x}\,\hat y) = \omega(x, y)$, so $\langle Jx, x\rangle = 0$.

**Definition (Rotation).** For $\theta \in \mathbb{R}/2\pi\mathbb{Z}$ the *rotation* by $\theta$ is $\rho_\theta(x) = \cos\theta\, x + \sin\theta\, Jx$.

Then $\widehat{\rho_\theta x} = (\cos\theta + i\sin\theta)\hat x = e^{i\theta}\hat x$.

::: mathlib
`Orientation.rotation` · `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation`

`o.rotation θ : V ≃ₗᵢ[ℝ] V` is a linear isometric equivalence, and `rotation_apply` is the formula `o.rotation θ x = Real.Angle.cos θ • x + Real.Angle.sin θ • J x`. Here `J` is `o.rightAngleRotation` from `Mathlib.Analysis.InnerProductSpace.TwoDim`. `rotation_map_complex` is the complex model: if `f : V ≃ₗᵢ[ℝ] ℂ` carries `o` to `Complex.orientation`, then `f (o.rotation θ x) = θ.toCircle * f x`.

<?decl Orientation.rotation?>
:::

### Theorems and proofs

**Theorem (Algebra of rotations).** For all $\theta, \psi$:

1. $\rho_\theta$ is a linear isometry, and $\rho_\theta \circ \rho_\psi = \rho_{\theta + \psi}$.
2. $\rho_0 = \mathrm{id}$, $\rho_\pi = -\mathrm{id}$, $\rho_{\pi/2} = J$, and $\rho_\theta^{-1} = \rho_{-\theta}$.
3. For $x \ne 0$ the vectors $x, Jx$ form a basis, the matrix of $\rho_\theta$ in it is $\begin{pmatrix} \cos\theta & -\sin\theta \\ \sin\theta & \cos\theta \end{pmatrix}$, and $\det \rho_\theta = 1$.

*Proof.* In the complex coordinate, $\rho_\theta$ is multiplication by $e^{i\theta}$, and $|e^{i\theta}| = 1$. So $\rho_\theta$ is an isometry, and $e^{i\theta}e^{i\psi} = e^{i(\theta + \psi)}$ gives (1). The values $e^{0} = 1$, $e^{i\pi} = -1$ and $e^{i\pi/2} = i$ give (2), and then (1) gives the inverse. For (3), $x$ and $Jx$ are orthogonal and nonzero, so they form a basis. From $\rho_\theta x = \cos\theta\, x + \sin\theta\, Jx$ and $\rho_\theta(Jx) = \cos\theta\, Jx - \sin\theta\, x$ (use $J^2 = -1$) comes the matrix. Its determinant is $\cos^2\theta + \sin^2\theta = 1$. $\square$

**Theorem (Rotations and oriented angles).** For all $x, y$ and $\theta$, $\measuredangle(\rho_\theta x, \rho_\theta y) = \measuredangle(x, y)$. If $x \ne 0$, then $\measuredangle(x, \rho_\theta x) = \theta$. If $x, y \ne 0$, then $\measuredangle(\rho_\theta x, y) = \measuredangle(x, y) - \theta$.

*Proof.* $\overline{e^{i\theta}\hat x}\,e^{i\theta}\hat y = \overline{\hat x}\,\hat y$ gives the first claim. Next, $\overline{\hat x}\,e^{i\theta}\hat x = \|x\|^2 e^{i\theta}$, a positive multiple of $e^{i\theta}$, with argument $\theta$. For the third, $\rho_\theta x \ne 0$, so additivity gives $\measuredangle(\rho_\theta x, y) = \measuredangle(\rho_\theta x, x) + \measuredangle(x, y) = -\theta + \measuredangle(x, y)$. $\square$

**Theorem (The angle as a rotation).** Let $x, y \ne 0$. Then $\measuredangle(x, y) = \theta$ if and only if $y = r\,\rho_\theta x$ for some $r > 0$. In particular $\rho_{\measuredangle(x, y)}\, x = y$ if and only if $\|x\| = \|y\|$.

*Proof.* If $y = r\rho_\theta x$ with $r > 0$, then $\measuredangle(x, y) = \measuredangle(x, \rho_\theta x) = \theta$. Conversely, put $z = \rho_\theta x \ne 0$. Then $\measuredangle(z, y) = \measuredangle(x, y) - \theta = 0$, so $y$ is a positive multiple of $z$ by Section 1. For the second claim, with $\theta = \measuredangle(x, y)$ the first claim gives $y = r z$ with $r > 0$ and $\|z\| = \|x\|$. So $z = y$ if and only if $r = 1$, that is $\|y\| = \|x\|$. $\square$

::: mathlib
`Orientation.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero` · `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation`

`oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero (hx : x ≠ 0) (hy : y ≠ 0) θ : o.oangle x y = θ ↔ ∃ r, 0 < r ∧ y = r • o.rotation θ x`. The special case `rotation_oangle_eq_iff_norm_eq` needs no hypothesis. The group laws are `rotation_rotation`, `rotation_trans` and `rotation_symm`, and `det_rotation` is the determinant.

<?decl Orientation.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero?>
<?decl Orientation.rotation_rotation?>
:::

**Theorem (Rotations are the direct isometries).** Let $f : V \to V$ be a linear isometry with $\det f > 0$. Then $f = \rho_\theta$ for some $\theta$.

*Proof.* Choose a unit vector $x$, and let $\theta = \measuredangle(x, f x)$. Since $\|f x\| = \|x\|$, the theorem above gives $\rho_\theta x = f x$. Put $g = \rho_{-\theta} \circ f$. It is a linear isometry with $g x = x$ and $\det g = \det f > 0$. The vector $g(Jx)$ is a unit vector, and $\langle g(Jx), x\rangle = \langle g(Jx), g x\rangle = \langle Jx, x\rangle = 0$. The vectors orthogonal to $x$ are the multiples of $Jx$, so $g(Jx) = \pm Jx$. The matrix of $g$ in the basis $x, Jx$ is $\operatorname{diag}(1, \pm 1)$, and $\det g > 0$ forces the sign $+$. So $g = \mathrm{id}$ and $f = \rho_\theta$. $\square$

::: mathlib
`Orientation.exists_linearIsometryEquiv_eq_of_det_pos` · `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation`

`exists_linearIsometryEquiv_eq_of_det_pos {f : V ≃ₗᵢ[ℝ] V} (hd : 0 < LinearMap.det f.toLinearEquiv) : ∃ θ, f = o.rotation θ`.

<?decl Orientation.exists_linearIsometryEquiv_eq_of_det_pos?>
:::

**Theorem (Right angles by rotation).** For $x, y \in V$, $\langle x, y\rangle = 0$ if and only if $x = 0$ or $y = r\,Jx$ for some $r \in \mathbb{R}$. For distinct points $A, B$ of the plane $P$ with midpoint $M$, $d(A, X) = d(B, X)$ if and only if $X = M + r\,J(B - A)$ for some $r$.

*Proof.* Let $x \ne 0$ and write $y = a x + b Jx$ in the basis $x, Jx$. Then $\langle x, y\rangle = a\|x\|^2$, which is $0$ if and only if $a = 0$. For the second claim, Chapter 3 shows that $d(A, X) = d(B, X)$ if and only if $\langle B - A, X - M\rangle = 0$. Apply the first claim with $x = B - A \ne 0$. $\square$

**Theorem (Oriented right-angled triangle).** Let $x, y \in V$ with $\measuredangle(x, y) = \pi/2$. Then
$$\measuredangle(x, x + y) = \arctan\frac{\|y\|}{\|x\|},\qquad \cos\measuredangle(x, x + y) = \frac{\|x\|}{\|x + y\|},\qquad \tan\measuredangle(x, x + y) = \frac{\|y\|}{\|x\|}.$$

*Proof.* Here $x, y \ne 0$, and the rotation theorem gives $y = s\,Jx$ with $s = \|y\|/\|x\| > 0$. In the complex coordinate, $\overline{\hat x}\,(\hat x + i s\hat x) = \|x\|^2(1 + is)$. The real part is positive, so the argument is $\arctan s$. Its cosine is $1/\sqrt{1 + s^2} = \|x\|/\|x + y\|$ by Pythagoras. The tangent is $s$. $\square$

In point form, let $\measuredangle ABC = \pi/2$. Then $A \ne B$ and $C \ne B$, and $A \ne C$ by Pythagoras. By the sign theorem of Section 1, $\measuredangle BCA$ has the sign of $\measuredangle ABC$, which is $+1$, so $\measuredangle BCA = \angle BCA$. Since $\langle B - C, A - B\rangle = 0$, $\langle B - C, A - C\rangle = \|B - C\|^2$, and
$$\cos\measuredangle BCA = \frac{d(C, B)}{d(A, C)},\quad \sin\measuredangle BCA = \frac{d(A, B)}{d(A, C)},\quad \measuredangle BCA = \arctan\frac{d(A, B)}{d(C, B)}.$$
The sine comes from $\sin^2 = 1 - \cos^2$, Pythagoras and $\sin\angle BCA \ge 0$. The angle lies in $(0, \pi/2)$ and its tangent is $d(A, B)/d(C, B)$, which gives the arctangent.

::: mathlib
`EuclideanGeometry.oangle_right_eq_arctan_of_oangle_eq_pi_div_two` · `Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle`

`oangle_right_eq_arctan_of_oangle_eq_pi_div_two (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : ∡ p₂ p₃ p₁ = Real.arctan (dist p₁ p₂ / dist p₃ p₂)`. The siblings `cos_oangle_right_of_oangle_eq_pi_div_two`, `sin_` and `cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two` give the other ratios. The vector form is `Orientation.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two`.

<?decl EuclideanGeometry.oangle_right_eq_arctan_of_oangle_eq_pi_div_two?>
<?decl Orientation.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two?>
:::

**Theorem (Angle at the foot).** Let $s$ be a line in the plane, $X \notin s$, $H$ the orthogonal projection of $X$ on $s$, and $Y \in s$ with $Y \ne H$. Then $\measuredangle XHY = \pi/2$ or $\measuredangle XHY = -\pi/2$, and so $2\measuredangle XHY = \pi$.

*Proof.* $X - H \ne 0$ because $X \notin s$, and $Y - H \ne 0$. The vector $X - H$ is orthogonal to the direction of $s$ (Chapter 3), so $\angle XHY = \pi/2$. By Section 1, $\measuredangle XHY = \pm\angle XHY$. $\square$

::: mathlib
`EuclideanGeometry.oangle_self_orthogonalProjection` · `Mathlib.Geometry.Euclidean.Angle.Oriented.Projection`

`oangle_self_orthogonalProjection p (hp : p ∉ s) (h : p' ∈ s) (hp' : p' ≠ orthogonalProjection s p) : ∡ p (orthogonalProjection s p) p' = ↑(π / 2) ∨ ... = ↑(-π / 2)`, for any `s` with an orthogonal projection. `two_zsmul_oangle_self_orthogonalProjection` gives the doubled form `= π`.

<?decl EuclideanGeometry.oangle_self_orthogonalProjection?>
:::

### Examples

**Example (The 3-4-5 triangle, oriented).** In $\mathbb{C}$ take $B = 0$, $A = 4$, $C = 3i$. Then $\measuredangle ABC = \arg(\bar 4 \cdot 3i) = \pi/2$. Next $\measuredangle BCA = \arg\bigl(\overline{(-3i)}(4 - 3i)\bigr) = \arg(9 + 12i) = \arctan(4/3)$, and $d(A, B)/d(C, B) = 4/3$.

**Counterexample (A reflection).** Let $\sigma(a, b) = (a, -b)$ on $\mathbb{R}^2$. It is a linear isometry with $\det\sigma = -1$. In the complex model $\widehat{\sigma x} = \overline{\hat x}$, so $\measuredangle(\sigma x, \sigma y) = \arg(\hat x\,\overline{\hat y}) = -\measuredangle(x, y)$. For $x = (1, 0)$, $y = (0, 1)$ this is $-\pi/2 \ne \pi/2$. So $\sigma$ is not a rotation, and the hypothesis $\det f > 0$ is needed.

### The library around it

`oangle_add_right_smul_rotation_pi_div_two` gives $\measuredangle(x, x + r\,Jx) = \arctan r$, the core of the right-triangle theorem. `inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two` and `dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint` are the right-angle theorem. In a right triangle the doubled angle determines the angle: `oangle_eq_oangle_of_two_zsmul_eq_of_angle_eq_pi_div_two`.

### Exercises

1. (A) Compute $\rho_{3\pi/4}(2, 0)$ in $\mathbb{R}^2$.
2. (A) Show that $\langle \rho_\theta x, x\rangle = \cos\theta\,\|x\|^2$.
3. (B) Show that two rotations commute, and that $\rho_\theta$ commutes with $J$.
4. (B) Let $ABC$ be a triangle with $\measuredangle ABC = -\pi/2$. State and prove the formula for $\measuredangle BCA$ as an arctangent.
5. (B) Show that a linear isometry $f$ of $V$ with $\det f < 0$ satisfies $\measuredangle(fx, fy) = -\measuredangle(x, y)$.
6. (C) Let $A \ne B$ with midpoint $M$. Show that $2\measuredangle AXB = \pi$ or $X \in \{A, B\}$ if and only if $d(M, X) = d(M, A)$. Hint: $2\measuredangle AXB = \pi$ means $\angle AXB = \pi/2$ with $X \ne A, B$.

### Notes and history

Plane rotations as multiplication by unit complex numbers go back to Wessel and Argand around 1800. The header of `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` names Joseph Myers and Heather Macbeth, and the headers of `Angle.Oriented.RightAngle` and `Angle.Oriented.Projection` name Joseph Myers.

### Reference

<?reference?>
