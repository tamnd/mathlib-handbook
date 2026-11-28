---
title: Strictly convex and uniformly convex spaces
kind: api
modules:
  - Mathlib.Analysis.Convex.Strict
  - Mathlib.Analysis.Convex.Strict.Extreme
  - Mathlib.Analysis.Convex.StrictConvexSpace
  - Mathlib.Analysis.Convex.StrictConvexBetween
  - Mathlib.Analysis.Convex.TriangleEquality
  - Mathlib.Analysis.Convex.Uniform
  - Mathlib.Analysis.Convex.ContinuousLinearEquiv
  - Mathlib.Analysis.Convex.LinearIsometry
  - Mathlib.Analysis.InnerProductSpace.Convex
explains:
  E2: [StrictConvex, StrictConvexSpace, StrictConvexSpace.of_norm_add, not_sameRay_iff_norm_add_lt, norm_combo_lt_of_ne, StrictConvexSpace.extremePoints_closedBall_eq_sphere, Isometry.affineIsometryOfStrictConvexSpace, norm_sum_eq_iff_exists_smul, UniformConvexSpace, InnerProductSpace.toUniformConvexSpace]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Strictly convex and uniformly convex spaces

### Overview

A set $s$ in a topological vector space is strictly convex when, for any two distinct points $x, y \in s$, each point of the open segment between them is in the interior of $s$. A closed disc in the plane is strictly convex, and a closed square is not, because a segment on an edge stays on the boundary. A normed space is strictly convex when its closed balls are strictly convex sets. Equivalently, the unit sphere contains no segment, or the triangle inequality $\|x + y\| \le \|x\| + \|y\|$ is an equality only when $x$ and $y$ point in the same direction. The spaces $L^p$ for $1 < p < \infty$ and all inner product spaces are strictly convex, while $\ell^1$ and $\ell^\infty$ are not.

Strict convexity has geometric consequences. In a strictly convex space, a point $y$ with $d(x, y) + d(y, z) = d(x, z)$ lies on the segment from $x$ to $z$, so segments are the only geodesics. From this, every isometry between real normed spaces with strictly convex target is affine, without the surjectivity that the Mazur Ulam theorem needs. The extreme points of a closed ball are exactly the points of its sphere.

A uniformly convex space has a quantitative form: for each $\varepsilon > 0$ there is $\delta > 0$ such that two unit vectors at distance at least $\varepsilon$ have a midpoint of norm at most $1 - \delta / 2$. Uniform convexity implies strict convexity. Every inner product space is uniformly convex, by the parallelogram law.

### The library around it

The file `Mathlib.Analysis.Convex.Strict` defines `StrictConvex 𝕜 s` in an ordered module with a topology. The basic lemmas are `StrictConvex.convex`, `StrictConvex.inter`, `StrictConvex.add`, `StrictConvex.smul`, `StrictConvex.neg`, `StrictConvex.affine_image`, `StrictConvex.linear_preimage` and `Directed.strictConvex_iUnion`. The empty set, a singleton and the whole space are strictly convex, by `strictConvex_empty`, `strictConvex_singleton` and `strictConvex_univ`, and so are all the intervals of an ordered field. For open sets, strict convexity is convexity, by `IsOpen.strictConvex_iff` and `Convex.strictConvex_of_isOpen`. On the scalars, `strictConvex_iff_convex` says the same for all sets. The lemma `StrictConvex.openSegment_subset` restates the definition with segments. The files `Mathlib.Analysis.Convex.ContinuousLinearEquiv` and `Mathlib.Analysis.Convex.LinearIsometry` transfer the notion along equivalences: `ContinuousLinearEquiv.strictConvex_image` and `ContinuousLinearEquiv.strictConvex_preimage` for sets, and `LinearIsometryEquiv.strictConvexSpace_iff`, `LinearIsometry.strictConvexSpace_range_iff` and `Submodule.instStrictConvexSpace` for spaces. The last one is an instance, so each submodule of a strictly convex space is a strictly convex space with no extra work. It follows from `LinearIsometry.strictConvexSpace`, which pulls strict convexity back along a linear isometry, applied to the inclusion of the submodule. The lemma `StrictConvex.linearIsometry_preimage` is the form for sets.

The file `Mathlib.Analysis.Convex.StrictConvexSpace` defines the class `StrictConvexSpace 𝕜 E` for a normed space over an ordered normed field. Its field says that each closed ball `Metric.closedBall 0 r` with `0 < r` is strictly convex, and `strictConvexSpace_iff` restates this. Several constructors avoid a check on all radii: `StrictConvexSpace.of_strictConvex_unitClosedBall` uses only the unit ball, `StrictConvexSpace.of_norm_combo_lt_one` uses convex combinations of unit vectors, and `StrictConvexSpace.of_norm_add` asks that `‖x + y‖ = 2` for unit vectors implies `SameRay ℝ x y`. The instance `Real.instStrictConvexSpace` covers `ℝ`.

The main consequences in this file all take `StrictConvexSpace ℝ E`. The lemma `norm_combo_lt_of_ne` says that a combination with positive weights of two distinct points of norm at most $r$ has norm less than $r$, and `combo_mem_ball_of_ne` and `openSegment_subset_ball_of_ne` give the same in a ball around any center. The lemma `norm_midpoint_lt_iff` treats midpoints of two vectors with equal norms. The triangle inequality forms are `not_sameRay_iff_norm_add_lt`, `sameRay_iff_norm_add`, `norm_add_lt_of_not_sameRay` and `sameRay_iff_norm_sub`, together with `lt_norm_sub_of_not_sameRay` and `abs_lt_norm_sub_of_not_sameRay` for the reverse inequality.

The file `Mathlib.Analysis.Convex.TriangleEquality` extends the equality case to finite sums. `norm_sum_eq_iff_pairwise_sameRay` says that $\|\sum_i v_i\| = \sum_i \|v_i\|$ if and only if the vectors are pairwise in the same ray, and `norm_sum_eq_iff_exists_smul` says that this holds if and only if there is one vector `c` with $v_i = \|v_i\| c$ for each $i$. The lemma `normalize_eq_of_pairwise_sameRay` gives the common direction, and `sum_ne_zero_of_pairwise_sameRay` excludes cancellation.

The file `Mathlib.Analysis.Convex.StrictConvexBetween` uses the betweenness relations `Wbtw` and `Sbtw` of affine geometry in a metric torsor over a strictly convex space. The lemma `dist_add_dist_eq_iff` says that `dist a b + dist b c = dist a c` if and only if `Wbtw ℝ a b c`, and `dist_lt_dist_add_dist_iff` is the strict form. The lemmas `Wbtw.dist_le_max_dist` and `Sbtw.dist_lt_max_dist` compare distances from a point to a segment, and `Collinear.wbtw_of_dist_eq_of_dist_le` gives betweenness on a line from distances. The definition `Isometry.affineIsometryOfStrictConvexSpace` turns an isometry `f : PF → PE` into an affine isometry, and `Isometry.coe_affineIsometryOfStrictConvexSpace` says that the underlying function is `f`. The proof shows that `f` maps midpoints to midpoints, since the midpoint is the only point at half distance from both ends, and a continuous map that preserves midpoints is affine.

The file `Mathlib.Analysis.Convex.Strict.Extreme` relates strict convexity to extreme points, a notion from the theory of extreme and exposed points. The lemma `StrictConvex.extremePoints_eq_sdiff_interior` says that the extreme points of a strictly convex set are the points not in its interior, and `StrictConvexSpace.extremePoints_closedBall_eq_sphere` gives the sphere as the set of extreme points of a ball. The lemma `extremePoints_closedBall_subset_sphere` holds in every normed space, and `disjoint_interior_extremePoints` says that an interior point is never extreme.

The file `Mathlib.Analysis.Convex.Uniform` defines the class `UniformConvexSpace E` for a seminormed group. Its field `UniformConvexSpace.uniform_convex` gives, for each `0 < ε`, a `0 < δ` with `‖x + y‖ ≤ 2 - δ` for unit vectors at distance at least `ε`. The lemmas `exists_forall_sphere_dist_add_le_two_sub`, `exists_forall_closed_ball_dist_add_le_two_sub` and `exists_forall_closed_ball_dist_add_le_two_mul_sub` extend the bound from the sphere to the ball and to other radii. The instance `UniformConvexSpace.toStrictConvexSpace` gives strict convexity. Its proof uses `StrictConvexSpace.of_norm_add`: if two unit vectors $x \ne y$ have $\|x + y\| = 2$, take $\varepsilon = \|x - y\| > 0$, and the field gives $\|x + y\| \le 2 - \delta < 2$, a contradiction. So $x = y$, and two equal vectors are in the same ray. The file `Mathlib.Analysis.InnerProductSpace.Convex` holds the instance `InnerProductSpace.toUniformConvexSpace`. The proof uses the parallelogram law: for unit vectors, $\|x + y\|^2 = 4 - \|x - y\|^2 \le 4 - \varepsilon^2$.

#### Common errors

1. `StrictConvexSpace 𝕜 E` has the scalar field as an argument. Most lemmas use `StrictConvexSpace ℝ E`, so for a complex space the instance over `ℝ` must come from the real structure, which needs `NormedSpace ℝ E`.
2. `StrictConvex 𝕜 s` is about the interior of `s`, so it depends on the topology. A closed segment in the plane is convex but not strictly convex, because its interior is empty.
3. `Isometry.affineIsometryOfStrictConvexSpace` needs the strict convexity of the target, not the source. An isometry into $\ell^\infty$ need not be affine.

### Exercises

1. (A) Prove that `ℝ` is a strictly convex space from `Real.instStrictConvexSpace`, and deduce that a submodule of a strictly convex space is strictly convex with `Submodule.instStrictConvexSpace`.
2. (A) Show that in a strictly convex space, `‖x + y‖ = ‖x‖ + ‖y‖` with `x ≠ 0` implies `y = t • x` for some `0 ≤ t`, with `sameRay_iff_norm_add`.
3. (B) Prove that the max norm on `ℝ × ℝ` is not strictly convex, with two unit vectors whose midpoint has norm $1$.
4. (B) Prove that a closed convex set in a strictly convex space has at most one point of smallest norm.
5. (B) Prove that the closed unit ball of a Hilbert space has the sphere as its set of extreme points.
6. (C) Prove that a uniformly convex Banach space has the property that each bounded sequence $x_n$ with $\|x_n\| \to 1$ and $\|x_n + x_m\| \to 2$ is Cauchy.

### Reference

<?reference?>
