---
title: Affine independence, bases and dimension
kind: theory
modules:
  - Mathlib.LinearAlgebra.AffineSpace.Independent
  - Mathlib.LinearAlgebra.AffineSpace.Basis
  - Mathlib.LinearAlgebra.AffineSpace.Matrix
  - Mathlib.LinearAlgebra.AffineSpace.Dimension
  - Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
  - Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
  - Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid
explains:
  E3: [AffineIndependent, affineIndependent_iff_linearIndependent_vsub, AffineIndependent.affineCombination_eq_iff_eq, AffineBasis, AffineBasis.coord, AffineIndependent.card_le_finrank_succ, Collinear, affineIndependent_iff_not_collinear_set, Affine.Simplex, Affine.Simplex.point_vsub_centroid_eq_smul_vsub]
  E2: [affineIndependent_iff_of_fintype, AffineIndependent.injective, AffineIndependent.mono, AffineEquiv.affineIndependent_iff, AffineBasis.coord_apply, AffineBasis.sum_coord_apply_eq_one, AffineBasis.exists_affineBasis, AffineBasis.card_eq_finrank_add_one, AffineBasis.toMatrix, AffineSubspace.dim, AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one, collinear_iff_of_mem, Coplanar, Affine.Triangle, Affine.Simplex.faceOpposite, Affine.Simplex.closedInterior, Affine.Simplex.median, Affine.Simplex.centroid_mem_median]
  E1: auto
families: []
requires: [V07, V22.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Affine independence, bases and dimension

### Overview

A family of points is affinely independent if no nontrivial weighted difference of its points vanishes. An affine basis is an independent family that spans the space and gives barycentric coordinates. In dimension $n$ it has $n + 1$ points. A simplex is an independent family of $n + 1$ points, and its medians meet at the centroid.

Throughout, $k$ is a ring, $P$ is an affine space over a $k$-module $V$, and $p : \iota \to P$ is a family of points.

### Definitions

**Definition (affine independence).** The family $p$ is *affinely independent* if for each finite $s \subseteq \iota$ and weights $w$ with $\sum_{i \in s} w_i = 0$ and $\sum_{i \in s} w_i (p_i -_v b) = 0$, all $w_i$ with $i \in s$ are $0$.

::: mathlib
`AffineIndependent` · `Mathlib.LinearAlgebra.AffineSpace.Independent`

`AffineIndependent k p` is `∀ (s : Finset ι) (w : ι → k), ∑ i ∈ s, w i = 0 → s.weightedVSub p w = 0 → ∀ i ∈ s, w i = 0`. See also `affineIndependent_iff_of_fintype`, `AffineIndependent.injective`, `AffineIndependent.mono` and `AffineEquiv.affineIndependent_iff`.

<?decl AffineIndependent?>
:::

**Definition (affine basis and barycentric coordinates).** An *affine basis* of $P$ is an affinely independent family $b : \iota \to P$ whose affine span is $P$. The unique weights $\lambda_i(q)$ of sum $1$ with $q = \sum_i \lambda_i(q) b_i$ are the *barycentric coordinates* of $q$.

::: mathlib
`AffineBasis` · `Mathlib.LinearAlgebra.AffineSpace.Basis`

`structure AffineBasis (ι k P)` holds a family with the proofs `AffineBasis.ind` of independence and `AffineBasis.tot` of spanning. Existence over a division ring is `AffineBasis.exists_affineBasis`.

<?decl AffineBasis?>
:::

**Definition (collinear, coplanar).** Let $k$ be a division ring. A set $S \subseteq P$ is *collinear* if its vector span has dimension at most $1$, and *coplanar* if it has dimension at most $2$.

::: mathlib
`Collinear` · `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional`

`Collinear k s` is `Module.rank k (vectorSpan k s) ≤ 1`, so it needs no finite dimension. `Coplanar k s` is the same with `2`.

<?decl Collinear?>
:::

**Definition (simplex).** An *$n$-simplex* is an affinely independent family of $n + 1$ points, indexed by $\{0, \dots, n\}$. A *triangle* is a $2$-simplex.

::: mathlib
`Affine.Simplex` · `Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic`

`structure Affine.Simplex (k P) (n : ℕ)` has the fields `points : Fin (n + 1) → P` and `independent : AffineIndependent k points`. `Affine.Triangle k P` is `Simplex k P 2`. Faces are `Affine.Simplex.faceOpposite`, and `Affine.Simplex.closedInterior` holds the points with all coordinates in $[0, 1]$.

<?decl Affine.Simplex?>
:::

### Theorems and proofs

**Theorem (independence through differences).** Let $j \in \iota$. The family $p$ is affinely independent if and only if the vectors $p_i -_v p_j$, $i \neq j$, are linearly independent.

*Proof.* Suppose $p$ is affinely independent and $\sum_{i \in s} c_i (p_i -_v p_j) = 0$ with $j \notin s$. The weights $c_i$ on $s$ and $w_j = -\sum_i c_i$ have sum $0$, and with base point $p_j$ their weighted difference is $\sum_{i \in s} c_i (p_i -_v p_j) = 0$. So all $c_i = 0$. Conversely, let $\sum_{i \in s} w_i = 0$ with weighted difference $0$. By Section 2 the base point does not matter; take $p_j$. The term for $j$ vanishes, so linear independence gives $w_i = 0$ for $i \neq j$, and then $w_j = 0$. $\square$

::: mathlib
`affineIndependent_iff_linearIndependent_vsub` · `Mathlib.LinearAlgebra.AffineSpace.Independent`

`affineIndependent_iff_linearIndependent_vsub k p i1 : AffineIndependent k p ↔ LinearIndependent k fun i : {x // x ≠ i1} => (p i -ᵥ p i1 : V)`.

<?decl affineIndependent_iff_linearIndependent_vsub?>
:::

**Theorem (unique weights).** The family $p$ is affinely independent if and only if two affine combinations over the same finite set $s$ that are equal have the same weights on $s$.

*Proof.* By Section 2, the difference of the combinations with weights $w$ and $w'$ of sum $1$ is the weighted difference with weights $w - w'$, of sum $0$. If $p$ is independent, this gives $w = w'$ on $s$. Conversely, let $\sum_{i \in s} u_i = 0$ with weighted difference $0$ and $s$ nonempty. Fix $j \in s$, let $w'$ be $1$ at $j$ and $0$ elsewhere, and $w = w' + u$. The two combinations are equal, so $u = 0$ on $s$. $\square$

::: mathlib
`AffineIndependent.affineCombination_eq_iff_eq` · `Mathlib.LinearAlgebra.AffineSpace.Independent`

For an affinely independent family, `AffineIndependent.affineCombination_eq_iff_eq` compares two affine combinations over the same `Finset` with weights of sum `1`.

<?decl AffineIndependent.affineCombination_eq_iff_eq?>
:::

**Theorem (barycentric coordinates).** Let $b$ be an affine basis and $i \in \iota$. There is a unique map $\lambda_i : P \to k$ such that each $q \in P$ is $\sum_i \lambda_i(q) b_i$ with $\sum_i \lambda_i(q) = 1$ and only finitely many $\lambda_i(q) \neq 0$. Each $\lambda_i$ is affine, and $\lambda_i(b_j) = \delta_{ij}$.

*Proof.* By Section 2, each $q$ is an affine combination of the $b_i$, and by the theorem on unique weights the weights are unique. Fix $j$. By the first theorem, $(b_i -_v b_j)_{i \neq j}$ is a linear basis of $V$, and $q -_v b_j = \sum_{i \neq j} c_i (b_i -_v b_j)$. So $\lambda_i(q) = c_i$ for $i \neq j$ and $\lambda_j(q) = 1 - \sum_{i \neq j} c_i$, which are affine in $q$. Last, $b_j$ has weight $1$ at $j$. $\square$

::: mathlib
`AffineBasis.coord` · `Mathlib.LinearAlgebra.AffineSpace.Basis`

`b.coord i : P →ᵃ[k] k`. See `AffineBasis.coord_apply` and `AffineBasis.sum_coord_apply_eq_one`. The matrix `AffineBasis.toMatrix` holds the coordinates of one family in a basis.

<?decl AffineBasis.coord?>
:::

**Theorem (counting points).** Let $k$ be a division ring and $V$ of finite dimension $n$. An affinely independent finite family has at most $n + 1$ points, and it spans $P$ if and only if it has exactly $n + 1$ points. So each affine basis of $P$ has $n + 1$ points.

*Proof.* Fix $j$. By the first theorem, the $m - 1$ vectors $p_i -_v p_j$ for $i \neq j$ are linearly independent, where $m$ is the number of points. They span the vector span, of dimension $m - 1 \le n$. The family spans $P$ if and only if its vector span is $V$, since a nonempty affine subspace is $p_j$ plus its direction. A subspace of dimension $m - 1$ equals $V$ if and only if $m - 1 = n$, by Volume 7. $\square$

::: mathlib
`AffineIndependent.card_le_finrank_succ` · `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional`

`AffineIndependent.card_le_finrank_succ : AffineIndependent k p → Fintype.card ι ≤ finrank k (vectorSpan k (Set.range p)) + 1`. The criterion for spanning is `AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one`; `AffineBasis.card_eq_finrank_add_one` counts an affine basis.

<?decl AffineIndependent.card_le_finrank_succ?>
:::

**Theorem (three points).** Over a division ring, three points $p_1, p_2, p_3$ are affinely independent if and only if $\{p_1, p_2, p_3\}$ is not collinear.

*Proof.* By the first theorem, the points are affinely independent if and only if $u = p_2 -_v p_1$ and $v = p_3 -_v p_1$ are linearly independent. The vector span of the set is spanned by $u$ and $v$, since $p_3 -_v p_2 = v - u$. Two vectors are linearly independent if and only if their span has dimension $2$. $\square$

::: mathlib
`affineIndependent_iff_not_collinear_set` · `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional`

The statement is `AffineIndependent k ![p₁, p₂, p₃] ↔ ¬Collinear k {p₁, p₂, p₃}`. See also `collinear_iff_of_mem`.

<?decl affineIndependent_iff_not_collinear_set?>
:::

**Theorem (medians of a simplex).** Let $k$ have characteristic $0$, and let $g$ be the centroid of an $n$-simplex with vertices $p_0, \dots, p_n$, $n \ge 1$. Let $f_i$ be the centroid of the face opposite $p_i$. Then $p_i -_v g = n(g -_v f_i)$. So $g$ lies on each median, the line through $p_i$ and $f_i$, and divides it in the ratio $n : 1$.

*Proof.* Fix a base point $o$ and write $\bar x = x -_v o$. Then $(n + 1)\bar g = \sum_j \bar p_j = \bar p_i + n \bar f_i$. So $\bar p_i - \bar g = (n + 1)\bar g - n\bar f_i - \bar g = n(\bar g - \bar f_i)$. The left side is $p_i -_v g$ and the right side is $n(g -_v f_i)$, by Chasles. $\square$

::: mathlib
`Affine.Simplex.point_vsub_centroid_eq_smul_vsub` · `Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid`

`s.point_vsub_centroid_eq_smul_vsub i : s.points i -ᵥ s.centroid = (n : k) • (s.centroid -ᵥ s.faceOppositeCentroid i)`. The median is `Affine.Simplex.median s i` and `Affine.Simplex.centroid_mem_median` places the centroid on it.

<?decl Affine.Simplex.point_vsub_centroid_eq_smul_vsub?>
:::

### Examples

**Example (coordinates in a triangle).** Let $b_0 = (0, 0)$, $b_1 = (1, 0)$, $b_2 = (0, 1)$ in $\mathbb{R}^2$. Then $(x, y) = (1 - x - y) b_0 + x b_1 + y b_2$, so $\lambda_0 = 1 - x - y$, $\lambda_1 = x$, $\lambda_2 = y$. The centroid $(\tfrac13, \tfrac13)$ has coordinates $(\tfrac13, \tfrac13, \tfrac13)$. The point $(1, 1)$ has coordinates $(-1, 1, 1)$, so it is outside the closed triangle. For the medians, $f_0 = (\tfrac12, \tfrac12)$ and $p_0 -_v g = 2(g -_v f_0)$.

**Counterexample (weights are not unique without independence).** The four points $(0,0)$, $(1,0)$, $(0,1)$, $(1,1)$ of $\mathbb{R}^2$ are dependent, by the counting theorem. The point $(\tfrac12, \tfrac12)$ is $\tfrac12(1,0) + \tfrac12(0,1)$ and also $\tfrac12(0,0) + \tfrac12(1,1)$. So the theorem on unique weights needs independence.

### The library around it

The file `Mathlib.LinearAlgebra.AffineSpace.Dimension` defines `AffineSubspace.dim s`, which is `⊥` for the empty subspace and the rank of the direction otherwise.

Chapter 3 builds the Euclidean geometry of triangles on these simplices.

### Exercises

1. (A) Find the barycentric coordinates of $(2, 3)$ with respect to $(1, 1)$, $(3, 1)$, $(1, 4)$.
2. (A) Show that two points are affinely independent if and only if they are distinct, over a nontrivial ring.
3. (A) Show that an affine equivalence maps affine bases to affine bases.
4. (B) Show that a subfamily of an affinely independent family is affinely independent.
5. (B) In $\mathbb{R}^3$, show that four points are affinely independent if and only if the $3 \times 3$ determinant of $p_2 - p_1$, $p_3 - p_1$, $p_4 - p_1$ is nonzero.
6. (C) Show that an affine map $f : P \to Q$ is determined by its values on an affine basis, and that any choice of values in $Q$ gives an affine map. Hint: use barycentric coordinates.

### Notes and history

The files on independence, finite dimension and simplices have the author Joseph Myers, with Chu Zheng for centroids of simplices. Oliver Nash wrote the files on affine bases and their matrices. The file on dimensions of affine subspaces has the authors Xavier Allamigeon, Arne Kuhrs, Louis Theran, Vlad Tsyrklevich and Juni Vogt.

### Reference

<?reference?>
