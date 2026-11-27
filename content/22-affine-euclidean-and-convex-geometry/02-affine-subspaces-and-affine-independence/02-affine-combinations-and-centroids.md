---
title: Affine combinations and centroids
kind: theory
modules:
  - Mathlib.LinearAlgebra.AffineSpace.Combination
  - Mathlib.LinearAlgebra.AffineSpace.Centroid
  - Mathlib.LinearAlgebra.AffineSpace.Ceva
explains:
  E3: [Finset.weightedVSubOfPoint, Finset.weightedVSub, Finset.affineCombination, Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one, Finset.map_affineCombination, mem_affineSpan_iff_eq_affineCombination, Finset.centroid, Affine.Triangle.prod_eq_prod_one_sub_of_mem_line_point_lineMap]
  E2: [Finset.weightedVSubOfPoint_apply, Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero, Finset.affineCombination_eq_linear_combination, Finset.affineCombination_vsub, mem_vectorSpan_iff_eq_weightedVSub, Finset.centroidWeights, Finset.centroid_pair, centroid_mem_affineSpan_of_card_ne_zero, AffineIndependent.exists_affineCombination_eq_smul_eq_of_fintype, Affine.Triangle.prod_div_one_sub_eq_one_of_mem_line_point_lineMap]
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

## Affine combinations and centroids

### Overview

Points of an affine space have no sum, but a sum $\sum_i w_i p_i$ with weights of sum $1$ makes sense: it does not depend on a choice of origin. This is an affine combination, or barycenter; with weights of sum $0$ the sum is a vector. This section shows that affine maps preserve these sums and that the affine span of a family is the set of its affine combinations. It ends with centroids and Ceva's theorem.

Throughout, $k$ is a ring, $P$ an affine space over a $k$-module $V$, $p : \iota \to P$ a family of points and $s \subseteq \iota$ finite.

### Definitions

**Definition (weighted sums).** For weights $w : \iota \to k$ and a base point $b \in P$, put $W_b(w) = \sum_{i \in s} w_i (p_i -_v b) \in V$. If $\sum_{i \in s} w_i = 1$, the *affine combination* of the $p_i$ with weights $w$ is the point $W_b(w) +_v b$. If $\sum_{i \in s} w_i = 0$, the *weighted difference* is the vector $W_b(w)$.

By the next lemma neither depends on $b$. The affine combination is written $\sum_i w_i p_i$.

::: mathlib
`Finset.affineCombination` · `Mathlib.LinearAlgebra.AffineSpace.Combination`

`s.weightedVSubOfPoint p b : (ι → k) →ₗ[k] V` is $W_b$, by `Finset.weightedVSubOfPoint_apply`. `s.weightedVSub p` is $W_b$ for a fixed choice of `b`, and `s.affineCombination k p : (ι → k) →ᵃ[k] P` is `w ↦ W_b(w) +ᵥ b` for that `b`. Both are defined for all weights.

<?decl Finset.affineCombination?>
:::

**Definition (centroid).** Let $k$ be a division ring and $|s| \neq 0$ in $k$. The *centroid* of the points $p_i$, $i \in s$, is the affine combination with all weights $1/|s|$.

::: mathlib
`Finset.centroid` · `Mathlib.LinearAlgebra.AffineSpace.Centroid`

`s.centroid k p` is `s.affineCombination k p (s.centroidWeights k)`, where `Finset.centroidWeights` is the constant `(#s : k)⁻¹`.

<?decl Finset.centroid?>
:::

### Theorems and proofs

**Lemma (independence of the base point).** For $b, b' \in P$, $W_{b'}(w) = W_b(w) + \big(\sum_{i \in s} w_i\big)(b -_v b')$. So $W_b(w)$ does not depend on $b$ when $\sum w_i = 0$, and $W_b(w) +_v b$ does not depend on $b$ when $\sum w_i = 1$.

*Proof.* By Chasles, $p_i -_v b' = (p_i -_v b) + (b -_v b')$. Multiply by $w_i$ and sum. If $\sum w_i = 0$, the correction is $0$. If $\sum w_i = 1$, then $W_{b'}(w) +_v b' = (W_b(w) + (b -_v b')) +_v b' = W_b(w) +_v b$ by the axioms. $\square$

::: mathlib
`Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one` · `Mathlib.LinearAlgebra.AffineSpace.Combination`

`(h : ∑ i ∈ s, w i = 1) (b : P) : s.affineCombination k p w = s.weightedVSubOfPoint p b w +ᵥ b`. The form for weights of sum `0` is `Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero`. In a module, `Finset.affineCombination_eq_linear_combination` gives `∑ i ∈ s, w i • p i` when the sum is `1`.

<?decl Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one?>
:::

The difference of two affine combinations is the weighted difference with weights $w - w'$, by `Finset.affineCombination_vsub`.

**Theorem (affine maps preserve affine combinations).** Let $f : P \to Q$ be affine with linear part $L$ and $\sum_{i \in s} w_i = 1$. Then $f(\sum_i w_i p_i) = \sum_i w_i f(p_i)$.

*Proof.* Fix $b$. Then $f(W_b(w) +_v b) = L(W_b(w)) +_v f(b) = \sum_i w_i L(p_i -_v b) +_v f(b) = \sum_i w_i (f(p_i) -_v f(b)) +_v f(b)$, which is the affine combination of the $f(p_i)$ with base point $f(b)$. $\square$

::: mathlib
`Finset.map_affineCombination` · `Mathlib.LinearAlgebra.AffineSpace.Combination`

For `hw : s.sum w = 1` and `f : P →ᵃ[k] P₂`, the result is `f (s.affineCombination k p w) = s.affineCombination k (f ∘ p) w`.

<?decl Finset.map_affineCombination?>
:::

**Theorem (affine span as combinations).** Let $k$ be nontrivial. A point $q$ is in the affine span of $\{p_i : i \in \iota\}$ if and only if $q = \sum_{i \in s} w_i p_i$ for a finite $s$ and weights with $\sum_{i \in s} w_i = 1$. A vector is in the vector span if and only if it is a weighted difference with weights of sum $0$.

*Proof.* Let $q = \sum_{i \in s} w_i p_i$ with $\sum w_i = 1$. Since $1 \neq 0$, some $j \in s$ exists, and $q = \sum_i w_i(p_i -_v p_j) +_v p_j$ is in the affine span by Section 1. Conversely, by Section 1 a point of the affine span is $v +_v p_j$ with $v$ in the vector span. Write $v = \sum_m c_m (p_{a_m} -_v p_{b_m})$, a finite sum. Then $v +_v p_j$ is the affine combination with weight $1$ at $j$, plus $c_m$ at $a_m$ and $-c_m$ at $b_m$ for each $m$, with base point $p_j$. These weights have sum $1$. The statement for vectors has the same proof, without the point $p_j$. $\square$

::: mathlib
`mem_affineSpan_iff_eq_affineCombination` · `Mathlib.LinearAlgebra.AffineSpace.Combination`

`[Nontrivial k] : p1 ∈ affineSpan k (Set.range p) ↔ ∃ s w, ∑ i ∈ s, w i = 1 ∧ p1 = s.affineCombination k p w`. The form for vectors is `mem_vectorSpan_iff_eq_weightedVSub`.

<?decl mem_affineSpan_iff_eq_affineCombination?>
:::

**Theorem (centroids).** Let $k$ be a division ring of characteristic $0$. The centroid of two points is their midpoint, the centroid lies in the affine span, and affine maps preserve centroids.

*Proof.* For $s = \{1, 2\}$ and base point $p_1$, the centroid is $\tfrac12(p_1 -_v p_1) + \tfrac12(p_2 -_v p_1) +_v p_1 = \tfrac12(p_2 -_v p_1) +_v p_1$. The weights have sum $|s| \cdot |s|^{-1} = 1$, so the last two claims follow from the two previous theorems. $\square$

The Lean names are `Finset.centroid_pair` and `centroid_mem_affineSpan_of_card_ne_zero`.

**Theorem (Ceva).** Let $k$ be a commutative ring with no zero divisors and $P_0, P_1, P_2$ an affinely independent triple, with indices modulo $3$. For $i = 0, 1, 2$, let $r_i \in k$ and $Q_i = (1 - r_i) P_{i+1} + r_i P_{i+2}$, a point on the line $P_{i+1}P_{i+2}$. If the three lines $P_i Q_i$ pass through a common point $X$, then $r_0 r_1 r_2 = (1 - r_0)(1 - r_1)(1 - r_2)$.

*Proof.* By Section 3, each point of the plane of the triangle has unique barycentric coordinates: weights $(a_0, a_1, a_2)$ with sum $1$ and $X = \sum_j a_j P_j$. Fix $i$. Since $X$ is on the line $P_i Q_i$, $X = (1 - t)P_i + tQ_i$ for some $t$, so
$$X = (1 - t) P_i + t(1 - r_i) P_{i+1} + t r_i P_{i+2}.$$
By uniqueness, $a_{i+1} = t(1 - r_i)$ and $a_{i+2} = t r_i$. So $a_{i+1} r_i = a_{i+2} (1 - r_i)$ for each $i$. Multiply the three equations: $(a_0 a_1 a_2) \prod r_i = (a_0 a_1 a_2) \prod (1 - r_i)$. If no $a_j$ is $0$, cancel, since $k$ has no zero divisors. Otherwise, by symmetry, let $a_0 = 0$, so $a_1 + a_2 = 1$. The equations give $a_1(1 - r_2) = 0$, $a_2 r_1 = 0$ and $a_1 r_0 = a_2(1 - r_0)$. If $a_1, a_2 \neq 0$, then $r_2 = 1$ and $r_1 = 0$. If $a_2 = 0$, then $a_1 = 1$, $r_2 = 1$ and $r_0 = 0$. If $a_1 = 0$, then $r_1 = 0$ and $r_0 = 1$. In each case both products are $0$. $\square$

::: mathlib
`Affine.Triangle.prod_eq_prod_one_sub_of_mem_line_point_lineMap` · `Mathlib.LinearAlgebra.AffineSpace.Ceva`

For `t : Triangle k P` and `r : Fin 3 → k`, with `hp' : ∀ i : Fin 3, p' ∈ line[k, t.points i, AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i)]`, the conclusion is `∏ i, r i = ∏ i, (1 - r i)`. The proof in Mathlib uses `AffineIndependent.exists_affineCombination_eq_smul_eq_of_fintype` for the weights of the common point. The classical form, over a field with each `r i ≠ 0`, is `Affine.Triangle.prod_div_one_sub_eq_one_of_mem_line_point_lineMap`.

<?decl Affine.Triangle.prod_eq_prod_one_sub_of_mem_line_point_lineMap?>
:::

If all $r_i \neq 0$, then no $r_i$ is $1$, so $\prod r_i / (1 - r_i) = 1$, with the signed ratios $r_i/(1 - r_i)$ in which $Q_i$ divides the sides.

### Examples

**Example (a centroid).** In $\mathbb{R}^2$, the centroid of $(0, 0)$, $(3, 0)$, $(0, 6)$ is $\tfrac13((0,0) + (3,0) + (0,6)) = (1, 2)$, by `Finset.affineCombination_eq_linear_combination`. The affine map $f(x, y) = (y, x + 1)$ sends the vertices to $(0, 1)$, $(0, 4)$, $(6, 1)$, with centroid $(2, 2) = f(1, 2)$. For the medians, $r_i = \tfrac12$ and $\prod r_i = \tfrac18 = \prod(1 - r_i)$, as Ceva's theorem requires.

**Counterexample (weights of sum other than 1).** In $\mathbb{R}$ as an affine space, take $p_1 = 1$, $p_2 = 3$ and weights $w_1 = w_2 = 1$. With base point $0$, $W_0(w) +_v 0 = 1 + 3 = 4$. With base point $1$, $W_1(w) +_v 1 = (0 + 2) + 1 = 3$. The result depends on the base point, so a sum of points with weight sum $2$ has no meaning.

### The library around it

The file `Mathlib.LinearAlgebra.AffineSpace.Combination` also treats line maps and homotheties of affine combinations. `Finset.centroid` is defined for all `s`, so results about it need `#s ≠ 0` in `k`, often with `CharZero k`. Section 3 defines affine independence, under which the weights of an affine combination are unique.

### Exercises

1. (A) Compute $\tfrac12 p_1 + \tfrac14 p_2 + \tfrac14 p_3$ for $p_1 = (4, 0)$, $p_2 = (0, 8)$, $p_3 = (0, 0)$ with two base points.
2. (A) Show that $\sum_i w_i p_i -_v q = \sum_i w_i (p_i -_v q)$ for each $q \in P$ when $\sum w_i = 1$.
3. (A) Show that the centroid of a triangle is $\tfrac23$ of the way from each vertex to the midpoint of the opposite side.
4. (B) Show that a subset of $P$ is an affine subspace if and only if it contains all affine combinations of its points, over any ring $k$.
5. (B) (Associativity of barycenters.) Let $s = s_1 \sqcup s_2$, with nonzero weight sums $\sigma_1, \sigma_2$ in a field and $\sigma_1 + \sigma_2 = 1$. Show that $\sum_{i \in s} w_i p_i = \sigma_1 g_1 + \sigma_2 g_2$, where $g_j$ is the combination over $s_j$ with weights $w_i / \sigma_j$.
6. (C) Prove the converse of Ceva's theorem over a field: if $\prod r_i = \prod (1 - r_i)$, the $r_i$ are not $0$ or $1$, and two of the lines $P_i Q_i$ meet, then the third line passes through their common point.

### Notes and history

Barycentric coordinates are due to Möbius, in his book of 1827 on the barycentric calculus. Ceva published his theorem in 1678. The files on combinations, centroids and Ceva's theorem have the author Joseph Myers.

### Reference

<?reference?>
