---
title: Normed torsors and affine isometries
kind: api
modules:
  - Mathlib.Analysis.Normed.Group.AddTorsor
  - Mathlib.Analysis.Normed.Affine.AddTorsor
  - Mathlib.Analysis.Normed.Affine.AddTorsorBases
  - Mathlib.Analysis.Normed.Affine.AsymptoticCone
  - Mathlib.Analysis.Normed.Affine.Ceva
  - Mathlib.Analysis.Normed.Affine.ContinuousAffineMap
  - Mathlib.Analysis.Normed.Affine.Convex
  - Mathlib.Analysis.Normed.Affine.Isometry
  - Mathlib.Analysis.Normed.Affine.MazurUlam
  - Mathlib.Analysis.Normed.Affine.Simplex
explains:
  E2: [dist_eq_norm_vsub, dist_lineMap_lineMap, dist_midpoint_midpoint_le, AffineMap.ofMapMidpoint, IsometryEquiv.toRealAffineIsometryEquiv, ContinuousAffineMap.norm_def, AffineBasis.interior_convexHull, isBounded_iff_asymptoticCone_subset_singleton, Affine.Triangle.prod_dist_eq_prod_dist_of_mem_line_of_mem_line]
  E1: auto
families: []
requires: [V07, V13]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Normed torsors and affine isometries

### Overview

A Euclidean plane has no origin. Its points form an affine space: the difference of two points is a vector, and a point plus a vector is a point. When the vectors form a normed space, the affine space has a metric, $d(p, q) = \|p - q\|$. Mathlib calls this structure a normed torsor. The class `NormedAddTorsor V P` says that the group `V` acts on the metric space `P` freely and transitively, and that the distance of `P` comes from the norm of `V`. Each normed group is a normed torsor over itself, so every result of this section also holds in a normed space.

This section treats the files on normed torsors. They give the metric rules for translations, midpoints, homotheties and lines, the norm on continuous affine maps, the affine isometries, and the theorem of Mazur and Ulam. Smaller files treat the interior of a simplex, the asymptotic cone of a set, the theorem of Ceva and the regular simplices. The geometry of Euclidean spaces uses this section as its base.

### The library around it

**The class.** The file `Mathlib.Analysis.Normed.Group.AddTorsor` defines `NormedAddTorsor`. Its field says that $d(p, q) = \|p -ᵥ q\|$, which the lemma `dist_eq_norm_vsub` states. The instance `SeminormedAddCommGroup.toNormedAddTorsor` makes each normed group a torsor over itself, and `instNormedAddTorsorProd` makes products of torsors torsors. An affine subspace of a torsor is again a torsor by `AffineSubspace.toNormedAddTorsor`. The definition `metricSpaceOfNormedAddCommGroupOfAddTorsor` goes the other way: it builds the metric of an affine space from the norm of its vectors.

The rules for distances follow from `dist_eq_norm_vsub` and the axioms of a torsor. The table lists the main ones.

| Lean name | Statement |
|---|---|
| `dist_vadd_cancel_left` | $d(v + x, v + y) = d(x, y)$ |
| `dist_vadd_cancel_right` | $d(v_1 + x, v_2 + x) = \|v_1 - v_2\|$ |
| `dist_vadd_left` | $d(v + x, x) = \|v\|$ |
| `dist_vsub_cancel_right` | $d(x - z, y - z) = d(x, y)$ |
| `dist_vadd_vadd_le` | $d(v + p, v' + p') \le d(v, v') + d(p, p')$ |
| `dist_vsub_vsub_le` | $d(p_1 - p_2, p_3 - p_4) \le d(p_1, p_3) + d(p_2, p_4)$ |

Each rule has a form for the nonnegative distance and often for the extended distance, such as `nnDist_vadd_left`. The maps $v \mapsto v + p$ and $p \mapsto q - p$ are isometric equivalences, `IsometryEquiv.vaddConst` and `IsometryEquiv.constVSub`. The operations are uniformly continuous (`uniformContinuous_vadd`, `uniformContinuous_vsub`), and `LipschitzWith.vadd` adds the Lipschitz constants.

**Lines, midpoints and homotheties.** The file `Mathlib.Analysis.Normed.Affine.AddTorsor` computes distances along the affine maps of linear algebra. The line map $c \mapsto p_1 + c(p_2 - p_1)$ is `AffineMap.lineMap p₁ p₂`, and the homothety with center $p$ and ratio $c$ is `AffineMap.homothety p c`. The basic rule is `dist_lineMap_lineMap`:
$$d(\operatorname{line}(c_1), \operatorname{line}(c_2)) = |c_1 - c_2| \, d(p_1, p_2).$$
Proof: the difference of the two points is $(c_1 - c_2)(p_2 - p_1)$, and the norm is homogeneous. The special cases are `dist_lineMap_left`, `dist_lineMap_right` and the forms for midpoints, such as `dist_left_midpoint`, which gives $d(p_1, m) = \|2\|^{-1} d(p_1, p_2)$. The factor $\|2\|$ is there because the field is general: over $\mathbb{Q}_2$ it is $1/2$. The homotheties scale all distances by $\|c\|$ (`dist_homothety`), and `Metric.image_homothety_ball` gives the image of a ball. The estimate `dist_midpoint_midpoint_le` says that the midpoint map is $1/2$ Lipschitz on each variable.

The same file holds a converse that the theorem of Mazur and Ulam uses. A continuous map $f$ between real normed torsors that keeps midpoints is affine. This is `AffineMap.ofMapMidpoint`. The idea: such a map, after translations, is additive, and a continuous additive map between real spaces is linear. The dilation `DilationEquiv.smulTorsor` is the map $x \mapsto c + kx$ from a normed space onto a torsor, with ratio $\|k\|$.

**Continuous affine maps.** The file `Mathlib.Analysis.Normed.Affine.ContinuousAffineMap` puts a norm on the space of continuous affine maps $f$ from a normed space $V$ to a normed space $W$. The definition is `ContinuousAffineMap.norm_def`: $\|f\| = \max(\|f(0)\|, \|f_{\mathrm{lin}}\|)$, where $f_{\mathrm{lin}}$ is the linear part `ContinuousAffineMap.contLinear f`. With this norm, `ContinuousAffineMap.decompLinearIsometryEquiv` is a linear isometric equivalence with the product of $W$ and the space of continuous linear maps, for the sup norm. The composition satisfies `ContinuousAffineMap.norm_comp_le`, with an extra term $\|f(0)\|$. The choice of the max norm is a convention. It makes the decomposition an isometry.

**Affine isometries.** The file `Mathlib.Analysis.Normed.Affine.Isometry` defines `AffineIsometry`, an affine map whose linear part is a linear isometry, with notation `P →ᵃⁱ[𝕜] P₂`, and the equivalences `AffineIsometryEquiv`, with notation `P ≃ᵃⁱ[𝕜] P₂`. The API follows the pattern of `LinearIsometry`: the maps `AffineIsometry.isometry`, `AffineIsometry.dist_map`, the linear part `AffineIsometry.linearIsometry`, and the coercions from linear isometries `LinearIsometry.toAffineIsometry`. The main equivalences are the translations `AffineIsometryEquiv.vaddConst` and `AffineIsometryEquiv.constVAdd`, the map `AffineIsometryEquiv.constVSub`, and the point reflection `AffineIsometryEquiv.pointReflection`. The point reflection through the midpoint of $x$ and $y$ swaps $x$ and $y$ (`AffineIsometryEquiv.pointReflection_midpoint_left`), and `AffineIsometryEquiv.dist_pointReflection_self_real` gives $d(s_x(y), y) = 2 d(x, y)$ over $\mathbb{R}$. An affine subspace and its image under an isometry are isometric by `AffineSubspace.isometryEquivMap`.

**The theorem of Mazur and Ulam.** The file `Mathlib.Analysis.Normed.Affine.MazurUlam` proves that a surjective isometry between real normed torsors is affine. The bundled form is `IsometryEquiv.toRealAffineIsometryEquiv`: from $f : P \simeq_i Q$ it gives an affine isometric equivalence with the same underlying map. The linear forms are `IsometryEquiv.toRealLinearIsometryEquivOfMapZero`, for an isometry with $f(0) = 0$, and `IsometryEquiv.toRealLinearIsometryEquiv`, with $g(x) = f(x) - f(0)$. The key step is `IsometryEquiv.map_midpoint`: the isometry keeps midpoints. Its proof uses `IsometryEquiv.midpoint_fixed`. Let $z$ be the midpoint of $x$ and $y$, and let $c$ be the supremum of $d(e(z), z)$ over all isometries $e$ that fix $x$ and $y$. The point reflection through $z$ turns such an $e$ into a second such isometry $e'$ with $d(e'(z), z) = 2 d(e(z), z)$. So $2c \le c$, and $c = 0$. The theorem then follows from `AffineMap.ofMapMidpoint`. The theorem is false over $\mathbb{C}$: complex conjugation is an isometry of $\mathbb{C}$ that is not complex linear.

**Simplices and convex hulls.** The file `Mathlib.Analysis.Normed.Affine.AddTorsorBases` studies the interior of a simplex. For an affine basis $b$ of a finite dimensional real space, `AffineBasis.interior_convexHull` says that the interior of the convex hull of the points of $b$ is the set where all barycentric coordinates are positive. The barycentric coordinates are continuous and open (`continuous_barycentric_coord`, `isOpenMap_barycentric_coord`). A convex set has nonempty interior if and only if its affine span is the whole space: `Convex.interior_nonempty_iff_affineSpan_eq_top`. An open nonempty set spans the whole space (`IsOpen.affineSpan_eq_top`). The file `Mathlib.Analysis.Normed.Affine.Convex` adds that $d(x, y) + d(y, z) = d(x, z)$ when $y$ is between $x$ and $z$ (`Wbtw.dist_add_dist`, `dist_add_dist_of_mem_segment`), and that each neighbourhood of a point contains a simplex with the point in its interior (`exists_mem_interior_convexHull_affineBasis`).

**Asymptotic cones.** The asymptotic cone of a set $s$ in a real affine space is the set of directions $v$ such that $s$ has points arbitrarily far in directions near $v$. The file `Mathlib.Analysis.Normed.Affine.AsymptoticCone` proves that, in finite dimension, a set is bounded if and only if its asymptotic cone is contained in $\{0\}$: `isBounded_iff_asymptoticCone_subset_singleton`. The direction "bounded implies trivial cone" holds in all dimensions (`asymptoticCone_subset_singleton_of_bounded`). The converse uses the compactness of the unit sphere, through `AffineSpace.cobounded_eq_iSup_sphere_asymptoticNhds`.

**Ceva and regular simplices.** The file `Mathlib.Analysis.Normed.Affine.Ceva` proves the theorem of Ceva in a normed torsor. Let $t$ be a triangle with vertices $A_0, A_1, A_2$, and let $p_i$ be a point on the line through $A_{i+1}$ and $A_{i+2}$. If the three lines from $A_i$ to $p_i$ meet at one point, then
$$\prod_i d(A_{i+1}, p_i) = \prod_i d(p_i, A_{i+2}).$$
This is `Affine.Triangle.prod_dist_eq_prod_dist_of_mem_line_of_mem_line`, and the quotient form is `Affine.Triangle.prod_dist_div_dist_eq_one_of_mem_line_of_mem_line`. The proof writes each $p_i$ with `AffineMap.lineMap` and uses `dist_lineMap_right` and `dist_left_lineMap`. The file `Mathlib.Analysis.Normed.Affine.Simplex` defines three predicates on a simplex: `Affine.Simplex.Equilateral` (all edges have the same length), `Affine.Simplex.Scalene` (all edges have different lengths) and `Affine.Simplex.Regular` (each permutation of the vertices comes from an isometry). A regular simplex is equilateral (`Affine.Simplex.Regular.equilateral`). For a triangle, `Affine.Triangle.equilateral_iff_dist_01_eq_02_and_dist_01_eq_12` reduces the condition to two equalities.

#### Common errors

1. Writing `p - q` for two points of a torsor. The difference of points is `p -ᵥ q`, and the sum of a vector and a point is `v +ᵥ p`. In a normed group the two forms agree, and `vsub_eq_sub` rewrites one into the other.
2. Expecting the theorem of Mazur and Ulam over $\mathbb{C}$ or without surjectivity. `IsometryEquiv.toRealAffineIsometryEquiv` gives an affine map over $\mathbb{R}$ only, and it needs an `IsometryEquiv`, not only an isometry.
3. Forgetting the factor $\|2\|$ in the midpoint lemmas. Over a general normed field, `dist_left_midpoint` has $\|2\|^{-1}$, not $1/2$. Over $\mathbb{R}$, `Real.norm_two` simplifies it.

### Exercises

1. (A) Use `dist_eq_norm_vsub` and the axioms of a torsor to prove `dist_vadd_cancel_left`.
2. (A) Use `dist_lineMap_lineMap` to compute the distance from $p_1$ to the point $\operatorname{line}(1/3)$ of the segment from $p_1$ to $p_2$.
3. (B) Show that the map $z \mapsto \bar{z}$ on $\mathbb{C}$ gives, by `IsometryEquiv.toRealAffineIsometryEquiv`, a real affine isometry, and that it is not complex affine.
4. (B) Prove that a map between real normed spaces that keeps midpoints and is continuous is affine, with the steps of `AffineMap.ofMapMidpoint`.
5. (B) Give a closed unbounded subset of $\mathbb{R}^2$ whose asymptotic cone is a single ray, and check the result with `not_bounded_iff_exists_ne_zero_mem_asymptoticCone`.
6. (C) Prove `IsometryEquiv.midpoint_fixed` for an isometry of $\mathbb{R}^2$ that fixes two points, with the argument of halving distances.

### Reference

<?reference?>
