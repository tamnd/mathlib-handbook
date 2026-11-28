---
title: Topology of convex sets
kind: api
modules:
  - Mathlib.Analysis.Convex.Topology
  - Mathlib.Analysis.Convex.Body
  - Mathlib.Analysis.Convex.Contractible
  - Mathlib.Analysis.Convex.PathConnected
  - Mathlib.Analysis.Convex.MetricSpace
  - Mathlib.Analysis.Convex.TotallyBounded
  - Mathlib.Analysis.Convex.Measure
  - Mathlib.Analysis.Convex.AmpleSet
  - Mathlib.Analysis.Convex.PartitionOfUnity
  - Mathlib.Analysis.Convex.EGauge
  - Mathlib.Analysis.Convex.GaugeRescale
explains:
  E2: [Convex.combo_interior_closure_mem_interior, closedConvexHull, Convex.closure_interior_eq_closure_of_nonempty_interior, ConvexBody, Convex.contractibleSpace, Convex.isPathConnected, Convex.addHaar_frontier, exists_continuous_forall_mem_convex_of_local, egauge, exists_homeomorph_image_interior_closure_frontier_eq_unitBall]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C03, V16.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Topology of convex sets

### Overview

In a topological vector space, the closure and the interior of a convex set are convex. The basic tool is a statement on segments: if $x$ is an interior point of a convex set $s$ and $y$ is in the closure of $s$, then each point of the half open segment from $x$ to $y$, except $y$, is interior. From this, a convex set with nonempty interior has the same closure as its interior, and the interior of its closure is its interior.

Convex sets have simple topology. A nonempty convex set is path connected, and even contractible, by the straight line homotopy to a point. In a finite dimensional space the boundary of a convex set has Lebesgue measure zero. A bounded convex set with nonempty interior in a finite dimensional normed space is homeomorphic to the closed unit ball, by a map that takes the interior to the open ball and the frontier to the sphere. The map rescales each ray from an interior point with the gauge of Chapter 5.

The section also covers convex bodies, the nonempty compact convex sets, with the Hausdorff distance, and the theorem that a continuous selection exists for a family of convex sets when local selections exist, by a partition of unity.

### The library around it

The file `Mathlib.Analysis.Convex.Topology` works in a topological vector space `E` over an ordered field `𝕜`. The closure results are `Convex.closure` and `Convex.interior`. The segment lemma is `Convex.combo_interior_closure_mem_interior`: for $x$ in the interior, $y$ in the closure, $a > 0$, $b \ge 0$ and $a + b = 1$, the point $a x + b y$ is in the interior. The proof uses a homothety. If $U$ is a neighborhood of $x$ inside $s$, then the homothety with center $a x + b y$ and ratio $-b / a$ maps a point near $y$ to a point near $x$. Choose a point $y' \in s$ close enough to $y$ that its image $x'$ lies in $U$. Then $a x + b y$ is a convex combination of $x'$ and $y'$, and the same combination of $U$ and $y'$ is an open set inside $s$ that contains it. Its variants are `Convex.openSegment_interior_closure_subset_interior`, `Convex.add_smul_mem_interior` and the forms with the set itself in place of its closure. The consequences are `Convex.closure_interior_eq_closure_of_nonempty_interior` and `Convex.interior_closure_eq_interior_of_nonempty_interior`. The lemma `Convex.strictConvex` gives a test for strict convexity in terms of the frontier. The file defines `closedConvexHull 𝕜`, the smallest closed convex set that contains `s`, as a closure operator, and `closedConvexHull_eq_closure_convexHull` says that it is the closure of the convex hull. The hull of an open set is open, `IsOpen.convexHull`, and the hull of a finite set is compact, `Set.Finite.isCompact_convexHull`. On the real line, `Real.convex_iff_isPreconnected` says that convex and preconnected are the same, and `Real.closedBall_eq_segment` and `Real.ball_eq_openSegment` describe balls. The lemmas `Convex.nhdsWithin_sdiff_eq_nhdsNE` and its variants compare neighborhood filters inside a convex subset of the line.

The file `Mathlib.Analysis.Convex.Body` defines the structure `ConvexBody V`, a nonempty compact convex set in a real topological vector space. The fields give `ConvexBody.convex`, `ConvexBody.isCompact` and `ConvexBody.nonempty`. Convex bodies form an additive commutative monoid under the Minkowski sum, `ConvexBody.instAddCommMonoid`, with an action of `ℝ≥0`, `ConvexBody.instModuleNNReal`. In a normed space, `ConvexBody.instMetricSpace` uses the Hausdorff distance, and `ConvexBody.hausdorffDist_coe` says that this distance agrees with `Metric.hausdorffDist` on the underlying sets. The lemma `ConvexBody.iInter_smul_eq_self` says that a body that contains `0` is the intersection of its dilates by factors $1 + u_n$ for a sequence $u_n \to 0$.

The file `Mathlib.Analysis.Convex.PathConnected` defines the straight path `Path.segment a b`, with `Path.range_segment` for its range, and proves `Convex.isPathConnected`, `Convex.isConnected` and `StarConvex.isPathConnected`. A submodule is path connected by `Submodule.isPathConnected`, and the whole space is path connected by `IsTopologicalAddGroup.pathConnectedSpace`. The lemma `isPathConnected_compl_of_isPathConnected_compl_zero` passes path connectedness of the complement of a point to the complement of a submodule of a complement. The file `Mathlib.Analysis.Convex.Contractible` proves `StarConvex.contractibleSpace`, `Convex.contractibleSpace` and `RealTopologicalVectorSpace.contractibleSpace`, each with the homotopy $(t, x) \mapsto (1 - t) x + t x_0$.

The file `Mathlib.Analysis.Convex.MetricSpace` works with the abstract convex spaces of `Convexity.ConvexSpace`, where convex combinations are an operation and not sums in a module. The class `Convexity.IsConvexDist` says that the distance is convex in each argument. The lemma `Convexity.dist_iConvexComb_le` bounds the distance between two convex combinations with the same weights by the combination of the distances, and `Convexity.continuous_convexCombPair` says that the combination of two points is continuous. A normed space is an example by `Convexity.instIsConvexDistOfIsAffineConvexSpaceReal`.

Three short files complete the picture. `Mathlib.Analysis.Convex.TotallyBounded` proves `totallyBounded_convexHull`: in a locally convex space, the hull of a totally bounded set is totally bounded. `Mathlib.Analysis.Convex.Measure` proves `Convex.addHaar_frontier`, which says that the frontier of a convex set has measure zero for every Haar measure on a finite dimensional real space, and so `Convex.nullMeasurableSet`. `Mathlib.Analysis.Convex.AmpleSet` defines `AmpleSet s`: the convex hull of each connected component of `s` is the whole space. This notion comes from convex integration. The main example is `AmpleSet.of_one_lt_codim`, the complement of a submodule of codimension at least $2$.

The file `Mathlib.Analysis.Convex.PartitionOfUnity` proves `exists_continuous_forall_mem_convex_of_local`. Let `X` be paracompact and normal, and let `t x` be a convex set for each `x`. If near each point there is a continuous `g` with `g y ∈ t y`, then there is one continuous `g` on all of `X` with this property. The proof glues the local maps with a partition of unity, and `PartitionOfUnity.finsum_smul_mem_convex` says that the glued value stays in the convex set. The variant `exists_continuous_forall_mem_convex_of_local_const` uses constant local maps.

The file `Mathlib.Analysis.Convex.EGauge` defines `egauge 𝕜 s x`, a gauge with values in `ℝ≥0∞`, as the infimum of `‖c‖ₑ` over scalars `c` with `x ∈ c • s`. Unlike `gauge`, it needs no order on `𝕜` and no convexity, and it takes the value `⊤` when no scalar works. The lemmas `le_egauge_iff` and `egauge_lt_iff` unfold the infimum, `egauge_le_one` holds on `s`, and `mem_of_egauge_lt_one` holds for a balanced set. The lemmas `egauge_add_add_le`, `egauge_pi` and `egauge_prod_mk` treat sums and products, and `Seminorm.le_egauge_unitBall` and `Seminorm.div_le_egauge_ball` compare the gauge of a seminorm ball with the seminorm.

The file `Mathlib.Analysis.Convex.GaugeRescale` defines `gaugeRescale s t x`, the multiple of `x` whose gauge for `t` is the gauge of `x` for `s`, as `gauge_gaugeRescale` says. For two convex bounded neighborhoods of `0`, `gaugeRescaleHomeomorph s t` is a homeomorphism of `E` that maps `s` onto `t`. With `t` the unit ball, this gives `exists_homeomorph_image_interior_closure_frontier_eq_unitBall`, which maps the interior, closure and frontier of `s` to the open ball, closed ball and sphere.

#### Common errors

1. `Convex.interior` needs `ZeroLEOneClass 𝕜` and a continuous scalar action by constants. Over `ℝ` in a normed space these instances are automatic, but in a general setting they may need a hypothesis.
2. `closedConvexHull 𝕜 s` is not the convex hull of the closure in general. In infinite dimensions the hull of a compact set need not be closed. The lemma `closedConvexHull_eq_closure_convexHull` takes the closure after the hull, not before it.
3. `egauge` and `gauge` are different functions. The value `egauge 𝕜 s x` is in `ℝ≥0∞` and the value `gauge s x` is in `ℝ`, so a lemma on one does not apply to the other without a conversion.

### Exercises

1. (A) Prove that the closure of a convex set is convex from `Convex.closure`, and deduce that a closed ball in a normed space is convex.
2. (A) Prove that a nonempty convex set in a real normed space is connected, with `Convex.isPathConnected`.
3. (B) Show that the interior of a convex set in `ℝ^2` with nonempty interior is dense in it, with `Convex.closure_interior_eq_closure_of_nonempty_interior`.
4. (B) Prove that a convex set in `ℝ^n` is Lebesgue measurable, with `Convex.nullMeasurableSet`.
5. (C) Prove that any two compact convex sets with nonempty interior in `ℝ^n` are homeomorphic, with `exists_homeomorph_image_interior_closure_frontier_eq_unitBall`.

### Reference

<?reference?>
