---
title: Projections and perpendicular bisectors
kind: theory
modules:
  - Mathlib.Geometry.Euclidean.Projection
  - Mathlib.Geometry.Euclidean.PerpBisector
  - Mathlib.Geometry.Euclidean.SignedDist
  - Mathlib.Geometry.Euclidean.Angle.Unoriented.Projection
explains:
  E3: [EuclideanGeometry.orthogonalProjection, EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem, EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq, EuclideanGeometry.reflection, AffineSubspace.perpBisector, AffineSubspace.mem_perpBisector_iff_dist_eq, signedDist]
  E2: [EuclideanGeometry.dist_orthogonalProjection_eq_infDist, EuclideanGeometry.reflection_perpBisector_left, AffineSubspace.mem_perpBisector_iff_inner_eq_zero, AffineSubspace.perpBisector_eq_top, EuclideanGeometry.dist_lt_of_sbtw_of_mem_perpBisector, signedDist_apply_apply, signedDist_triangle, abs_signedDist_le_dist]
  E1: auto
families: []
requires: [V07, V13, V15.C06, V16.C06, V16.C07, V22.C01, V22.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Projections and perpendicular bisectors

### Overview

Volume 16, Chapter 7 proves that a complete subspace $W$ of an inner product space gives $V = W \oplus W^\perp$. This section moves that result to affine subspaces: it builds the foot of the perpendicular from a point to an affine subspace, and from it the reflection, the perpendicular bisector of two points and the signed distance.

Throughout, $s$ is a nonempty affine subspace of $P$ with direction $W$.

### Definitions

**Definition (Orthogonal projection).** Let $W$ be complete. The *orthogonal projection* of $p \in P$ onto $s$ is the unique point $\pi_s(p) \in s$ with $p - \pi_s(p) \in W^\perp$.

::: mathlib
`EuclideanGeometry.orthogonalProjection` · `Mathlib.Geometry.Euclidean.Projection`

`orthogonalProjection (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] : P →ᴬ[𝕜] s` is a continuous affine map with values in the subtype `s`, over a field `𝕜` with `[RCLike 𝕜]`. The two instances are the hypotheses; Mathlib finds `HasOrthogonalProjection` for each complete subspace. The value lies in `s`, so a proof often needs the coercion `(orthogonalProjection s p : P)`. The characterization is `coe_orthogonalProjection_eq_iff_mem : orthogonalProjection s p = q ↔ q ∈ s ∧ p -ᵥ q ∈ s.direction.orthogonal`.

<?decl EuclideanGeometry.orthogonalProjection?>
<?decl EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem?>
:::

**Definition (Reflection).** The *reflection* in $s$ is $\rho_s(p) = \pi_s(p) + (\pi_s(p) - p)$, the point with $\pi_s(p)$ as the midpoint of $p$ and $\rho_s(p)$.

**Definition (Perpendicular bisector).** For $a, b \in P$ with midpoint $m$, the *perpendicular bisector* is the affine subspace $\{x \in P : \langle x - m, b - a\rangle = 0\}$. It passes through $m$ and has direction $(\mathbb{R}(b - a))^\perp$.

**Definition (Signed distance).** Let $v \in V$ and $p, q \in P$. The *signed distance* from $p$ to $q$ along $v$ is $\sigma_v(p, q) = \langle v/\|v\|, q - p\rangle$ for $v \ne 0$, and $0$ for $v = 0$.

### Theorems and proofs

**Theorem (The foot of the perpendicular).** Let $W$ be complete and $p \in P$. There is exactly one $q \in s$ with $p - q \in W^\perp$. For each $x \in s$,
$$d(p, x)^2 = d(p, q)^2 + d(q, x)^2.$$
So $q$ is the unique point of $s$ nearest to $p$, and $d(p, q) = \inf_{x \in s} d(p, x)$.

*Proof.* Existence. Choose $o \in s$. By Volume 16, Chapter 7, $p - o = w + w'$ with $w \in W$ and $w' \in W^\perp$. Put $q = o + w$. Then $q \in s$, since $s = o + W$, and $p - q = w' \in W^\perp$. Uniqueness. Let $q, q' \in s$ both have the property. Then $q - q' \in W$, and $q - q' = (p - q') - (p - q) \in W^\perp$. A vector in $W \cap W^\perp$ is orthogonal to itself, so $q = q'$. The identity. For $x \in s$, $p - x = (p - q) + (q - x)$ with $p - q \in W^\perp$ and $q - x \in W$. Pythagoras for vectors gives the identity. It shows $d(p, x) \ge d(p, q)$, with equality only for $x = q$. $\square$

**Corollary (Properties of the projection).** (1) $\pi_s(p) = p$ if and only if $p \in s$. (2) $\pi_s(\pi_s(p)) = \pi_s(p)$. (3) $\pi_s$ is an affine map whose linear part is the orthogonal projection onto $W$.

*Proof.* (1) If $p \in s$, then $q = p$ has the property, since $0 \in W^\perp$. Conversely $\pi_s(p) \in s$. (2) follows from (1). (3) For $p, p'$, the proof of existence with the same $o$ gives $\pi_s(p) - \pi_s(p') = w_p - w_{p'}$, the projection of $p - p'$ onto $W$. $\square$

::: mathlib
`EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq` · `Mathlib.Geometry.Euclidean.Projection`

The identity of the theorem is stated with products of distances, for `hp₁ : p₁ ∈ s`. `dist_orthogonalProjection_eq_infDist` says `dist p (orthogonalProjection s p) = Metric.infDist p s`.

<?decl EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq?>
:::

**Theorem (Reflection).** $\rho_s$ is an isometry of $P$ onto itself, $\rho_s \circ \rho_s$ is the identity, and $\rho_s(p) = p$ if and only if $p \in s$.

*Proof.* Let $p, p' \in P$ with feet $q, q'$. Write $p - p' = (q - q') + r$ with $r = (p - q) - (p' - q') \in W^\perp$ and $q - q' \in W$. Then $\rho_s(p) - \rho_s(p') = 2(q - q') - (p - p') = (q - q') - r$. By Pythagoras both $p - p'$ and $(q - q') - r$ have the squared norm $\|q - q'\|^2 + \|r\|^2$. Next, $\rho_s(p) - q = q - p \in W^\perp$ and $q \in s$, so $\pi_s(\rho_s(p)) = q$ by uniqueness. Hence $\rho_s(\rho_s(p)) = q + (q - \rho_s(p)) = q + (p - q) = p$. So $\rho_s$ is a bijection. Finally $\rho_s(p) = p$ if and only if $q - p = 0$, that is $p \in s$ by the corollary. $\square$

**Theorem (Perpendicular bisector).** A point $x$ lies on the perpendicular bisector of $a$ and $b$ if and only if $d(x, a) = d(x, b)$. The reflection in the perpendicular bisector exchanges $a$ and $b$.

*Proof.* Let $m$ be the midpoint, so $(x - a) + (x - b) = 2(x - m)$ and $(x - b) - (x - a) = a - b$. Then
$$d(x, a)^2 - d(x, b)^2 = \langle (x - a) - (x - b), (x - a) + (x - b)\rangle = 2\langle b - a, x - m\rangle.$$
The left side is $0$ if and only if $x$ is on the bisector. For the reflection let $L$ be the bisector. If $a = b$, then $L = P$ and $\rho_L$ is the identity. Otherwise $m \in L$, and $a - m = \frac12(a - b)$ is a multiple of $b - a$. It is orthogonal to $(\mathbb{R}(b - a))^\perp$, the direction of $L$. So $\pi_L(a) = m$ and $\rho_L(a) = 2m - a = b$. $\square$

::: mathlib
`AffineSubspace.perpBisector` · `Mathlib.Geometry.Euclidean.PerpBisector`

`perpBisector p₁ p₂ : AffineSubspace ℝ P` is the affine subspace through the midpoint with the kernel of $\langle p_2 - p_1, \cdot\rangle$ as direction. The theorem is `mem_perpBisector_iff_dist_eq : c ∈ perpBisector p₁ p₂ ↔ dist c p₁ = dist c p₂`, and the inner product form is `mem_perpBisector_iff_inner_eq_zero`. `perpBisector_eq_top`: the bisector is `⊤` if and only if `p₁ = p₂`. `reflection_perpBisector_left` gives `reflection (perpBisector a b) a = b` with no hypothesis.

<?decl AffineSubspace.perpBisector?>
<?decl AffineSubspace.mem_perpBisector_iff_dist_eq?>
<?decl EuclideanGeometry.reflection?>
:::

**Theorem (Signed distance).** For all $v \in V$ and $p, q, r \in P$: (1) $\sigma_v(p, q) + \sigma_v(q, r) = \sigma_v(p, r)$. (2) $|\sigma_v(p, q)| \le d(p, q)$. (3) For $v \ne 0$, equality holds in (2) if and only if $q - p$ is a multiple of $v$.

*Proof.* Let $v \ne 0$ and $e = v/\|v\|$; for $v = 0$ all claims hold with $\sigma = 0$, and in (3) the only multiple of $0$ is $0$. (1) $\langle e, q - p\rangle + \langle e, r - q\rangle = \langle e, r - p\rangle$. (2) Cauchy-Schwarz: $|\langle e, q - p\rangle| \le \|e\|\,\|q - p\|$ and $\|e\| = 1$. (3) This is the equality case of Cauchy-Schwarz from Section 1. $\square$

::: mathlib
`signedDist` · `Mathlib.Geometry.Euclidean.SignedDist`

`signedDist v : P →ᴬ[ℝ] P →ᴬ[ℝ] ℝ` lives in the root namespace. `signedDist_apply_apply` gives `signedDist v p q = ⟪normalize v, q -ᵥ p⟫`; `normalize 0 = 0` gives the value $0$ for $v = 0$. `signedDist_triangle` is part (1), and `abs_signedDist_le_dist` part (2).

<?decl signedDist?>
:::

**Theorem (Angles at the foot).** Let $p \in P$, $q = \pi_s(p)$ and $x \in s$. Then $\angle pqx = \pi/2$ and $d(p, q) = \sin(\angle pxq)\, d(p, x)$.

*Proof.* $\langle p - q, x - q\rangle = 0$ since $p - q \in W^\perp$ and $x - q \in W$. Section 1 gives $\angle pqx = \pi/2$, also when $x = q$ or $p = q$. The law of sines of Section 2 for the triangle $(p, x, q)$ says $d(p, q)\sin\angle pqx = d(p, x)\sin\angle pxq$, with no hypothesis, and $\sin(\pi/2) = 1$. $\square$

### Examples

**Example (A plane in $\mathbb{R}^3$).** Let $s = \{x + y + z = 1\}$ and $p = (1, 1, 1)$. The direction $W$ is $n^\perp$ with $n = (1, 1, 1)$, so $W^\perp = \mathbb{R}n$. The foot has the form $q = p - t n$ with $q \in s$: $3 - 3t = 1$, so $t = 2/3$ and $q = (1/3, 1/3, 1/3)$. The distance is $\|t n\| = 2/\sqrt 3$, and the reflection is $\rho_s(p) = q - (p - q) = (-1/3, -1/3, -1/3)$. With $o = (1, 0, 0) \in s$, the signed distance along $n$ is $\langle n/\sqrt 3, p - o\rangle = 2/\sqrt 3$.

**Counterexample (A subspace that is not closed).** In the Hilbert space $\ell^2$ let $W$ be the subspace of sequences with finitely many nonzero terms, and $s = W$. Let $p = (1, 1/2, 1/4, \ldots)$. Truncations of $p$ lie in $W$ and tend to $p$, so $\inf_{x \in s} d(p, x) = 0$. But $p \notin W$, so no point of $s$ has distance $0$, and $p$ has no foot. The instance `HasOrthogonalProjection` excludes this case.

### The library around it

`EuclideanGeometry.dist_lt_of_sbtw_of_mem_perpBisector`: if $\operatorname{Sbtw}(a, b, c)$ and $x$ is on the bisector of $a$ and $b$, then $d(x, b) < d(x, c)$.

Order matters: `signedDist v p q = - signedDist v q p`.

### Exercises

1. (A) Find the foot of the perpendicular from $(3, 1)$ to the line $y = x$ in $\mathbb{R}^2$, and the reflection of $(3, 1)$ in that line.
2. (A) Show that the distance from $p$ to the hyperplane $\{x : \langle n, x\rangle = c\}$, $n \ne 0$, is $|\langle n, p\rangle - c| / \|n\|$.
3. (A) Show that $\rho_s$ is affine.
4. (B) Show that $\pi_s \circ \rho_s = \pi_s$.
5. (B) Let $a, b, c$ be three non-collinear points of a plane. Show that the perpendicular bisectors of $ab$ and $bc$ meet in one point, and that it lies on the bisector of $ca$.
6. (C) Let $s \subseteq t$ be affine subspaces with complete directions. Show that $\pi_s \circ \pi_t = \pi_s$.

### Notes and history

The file `Mathlib.Geometry.Euclidean.Projection` has the authors Joseph Myers and Manuel Candales in its header, `PerpBisector` has Yury Kudryashov and Joseph Myers, and `SignedDist` and `Angle.Unoriented.Projection` have Joseph Myers.

### Reference

<?reference?>
