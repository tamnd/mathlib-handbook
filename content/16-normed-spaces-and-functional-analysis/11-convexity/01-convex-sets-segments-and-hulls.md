---
title: Convex sets, segments and hulls
kind: api
modules:
  - Mathlib.Analysis.Convex.Segment
  - Mathlib.Analysis.Convex.Basic
  - Mathlib.Analysis.Convex.Star
  - Mathlib.Analysis.Convex.Hull
  - Mathlib.Analysis.Convex.Combination
  - Mathlib.Analysis.Convex.Join
  - Mathlib.Analysis.Convex.StoneSeparation
  - Mathlib.Analysis.Convex.NNReal
explains:
  E2: [segment, openSegment, Convex, convex_iff_segment_subset, StarConvex, Finset.centerMass, Convex.sum_mem, convexHull_eq, convexJoin, exists_convex_convex_compl_subset]
  E1: auto
families: []
requires: [V07, V16.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Convex sets, segments and hulls

### Overview

A set $s$ in a vector space over an ordered field is convex when it contains the segment between any two of its points. The segment $[x, y]$ is the set of points $a x + b y$ with $a, b \ge 0$ and $a + b = 1$. Mathlib states all of this without a norm. The scalars form an ordered semiring `𝕜` and the space is a module `E` over it, so the same definitions serve for real vector spaces, for $\mathbb{Q}$ vector spaces, and for modules over `NNReal`. The normed space structure of the rest of this volume enters only in Section 4.

The convex hull of $s$ is the smallest convex set that contains $s$. It is the set of all convex combinations $\sum_i w_i z_i$ of points $z_i \in s$, with $w_i \ge 0$ and $\sum_i w_i = 1$. This description reduces many questions on hulls to finite sums, and so the library has a large calculus of weighted means of finite families, the center of mass.

The section ends with the separation theorem of Stone. If $s$ and $t$ are disjoint convex sets, then there is a convex set $C$ that contains $s$, whose complement is convex and contains $t$. This is a purely algebraic form of separation. It needs no topology, and it is the step before the geometric Hahn Banach theorem of Chapter 5.

### The library around it

The file `Mathlib.Analysis.Convex.Segment` defines `segment 𝕜 x y` and `openSegment 𝕜 x y`. The closed one uses weights $a, b \ge 0$, the open one uses $a, b > 0$, and `openSegment_subset_segment` compares them. In a module over a ring, `segment_eq_image` gives the segment as the image of `Set.Icc 0 1` under $\theta \mapsto (1 - \theta) x + \theta y$, and `segment_eq_image_lineMap` gives the same image with `AffineMap.lineMap x y`. On the scalars themselves, `segment_eq_uIcc` says that `segment 𝕜 x y` is the unordered interval `Set.uIcc x y`. The lemma `mem_segment_iff_sameRay` says that $x \in [y, z]$ if and only if $x - y$ and $z - x$ are in the same ray. The rest of the file has lemmas on translates, on images under linear and affine maps, and on segments in products and in function types, such as `Prod.segment_subset` and `Pi.segment_subset`. The lemma `Convex.combo_le_max` is the order fact $a x + b y \le \max(x, y)$ that later sections use for quasiconvex functions.

The file `Mathlib.Analysis.Convex.Basic` defines `Convex 𝕜 s`. The definition says that `s` is star convex at each of its points, so `Convex.starConvex` is immediate, and `convex_iff_segment_subset` gives the usual form. Other forms are `convex_iff_openSegment_subset`, `convex_iff_pointwise_add_subset`, which says that $a s + b s \subseteq s$, and `convex_iff_forall_pos`. The closure properties are `Convex.inter`, `convex_iInter`, `convex_sInter`, `Convex.prod`, `convex_pi`, `Convex.add`, `Convex.smul`, `Convex.neg`, `Convex.linear_image`, `Convex.linear_preimage`, `Convex.is_linear_preimage` and `Convex.affine_image`. A directed union of convex sets is convex by `Directed.convex_iUnion`. The basic examples are `convex_segment`, `convex_univ`, `convex_singleton`, `convex_Icc` and the other intervals, the half spaces `convex_halfSpace_le` and `convex_halfSpace_lt`, `convex_hyperplane`, `Submodule.convex` and `AffineSubspace.convex`. On the scalars, `convex_iff_ordConnected` says that a convex subset of `𝕜` is exactly an order connected set. For convex `s` and $p, q \ge 0$, `Convex.add_smul` gives $(p + q) s = p s + q s$. The convex sets of `Set E` form an additive submonoid, `convexAddSubmonoid 𝕜 E`.

The file `Mathlib.Analysis.Convex.Star` defines `StarConvex 𝕜 x s`: each segment from `x` to a point of `s` lies in `s`. Star convex sets are closed under union at the same center, `StarConvex.union` and `starConvex_iUnion`, which convex sets are not. The file also has the analogues of the closure properties above, and `starConvex_iff_ordConnected` for the scalars. Star convex sets are contractible, which is a result of Section 4.

The file `Mathlib.Analysis.Convex.Hull` defines `convexHull 𝕜` as a `ClosureOperator (Set E)`, so `subset_convexHull`, `convexHull_mono` and idempotence come from the general theory of closure operators. The lemma `convexHull_min` says that a convex set that contains `s` contains its hull, and `Convex.convexHull_eq` says that a convex set is its own hull. The lemma `convexHull_eq_iInter` gives the hull as the intersection of all convex sets that contain `s`. Small cases are `convexHull_singleton`, `convexHull_pair`, which is a segment, and `convexHull_empty`. The hull commutes with affine maps by `AffineMap.image_convexHull`, and it lies in the affine span by `convexHull_subset_affineSpan`.

The file `Mathlib.Analysis.Convex.Combination` defines `Finset.centerMass t w z`, the point $(\sum_{i \in t} w_i)^{-1} \sum_{i \in t} w_i z_i$. When the weights sum to $1$, `Finset.centerMass_eq_of_sum_1` reduces it to the plain sum. The lemma `Convex.centerMass_mem` says that a convex set contains the center of mass of its points for nonnegative weights with a positive sum, and `Convex.sum_mem` is the version for weights that sum to $1$. Conversely, `convex_iff_sum_mem` characterizes convexity by finite sums. The description of the hull is `convexHull_eq`: a point is in the hull of `s` if and only if it is a center of mass of finitely many points of `s`. The variants `Finset.mem_convexHull`, `Set.Finite.convexHull_eq` and `mem_convexHull_iff_exists_fintype` treat finite sets and finite index types. With an affine basis `b`, `AffineBasis.convexHull_eq_nonneg_coord` says that the hull of the basis points is the set where each barycentric coordinate is nonnegative. The lemmas `convexHull_add`, `convexHull_sum`, `convexHull_prod` and `convexHull_pi` say that the hull commutes with sums and products of sets, and `convexHullAddMonoidHom` packs the first fact as an additive monoid map. The lemma `convexHull_eq_union_convexHull_finite_subsets` reduces the hull of any set to hulls of finite subsets.

The file `Mathlib.Analysis.Convex.Join` defines `convexJoin 𝕜 s t`, the union of the segments from a point of `s` to a point of `t`, as `mem_convexJoin` says. The join is commutative and associative, `convexJoin_comm` and `convexJoin_assoc`. The two hull lemmas are `convexHull_insert`, which builds the hull of `insert x s` as the join of `{x}` with the hull of `s`, and `Convex.convexHull_union`, which says that the hull of the union of two nonempty convex sets is their join. This gives a proof of hull facts by induction on a finite set.

The file `Mathlib.Analysis.Convex.StoneSeparation` holds the theorem `exists_convex_convex_compl_subset`. The proof applies Zorn's lemma to the convex sets that contain `s` and are disjoint from `t`, and takes a maximal one `C`. The key step is the lemma `not_disjoint_segment_convexHull_triple`, a fact on segments in a triangle, which shows that the complement of `C` is convex. The file `Mathlib.Analysis.Convex.NNReal` compares the scalars `NNReal` and `ℝ`: `NNReal.convex_iff` says that the two notions of convexity agree, and `NNReal.segment_eq_Icc` computes segments in `NNReal`.

#### Common errors

1. The scalar field is an explicit argument. Write `Convex ℝ s` and `convexHull ℝ s`, not `Convex s`. If the field is a metavariable, the elaborator cannot infer it from `s`.
2. `convexHull 𝕜` is a closure operator, not a function. To apply it to a set, write `convexHull 𝕜 s`, which uses the coercion to a function. A lemma on closure operators, such as `ClosureOperator.monotone`, applies to `convexHull 𝕜` directly.
3. `Finset.centerMass` divides by the sum of the weights. If the weights sum to zero, the value is zero, so state the positive sum hypothesis before a membership lemma.

### Exercises

1. (A) Prove that the image of a convex set under an affine map is convex, from `Convex.linear_image` and translation.
2. (A) Prove that a convex subset of `ℝ` is an interval, with `convex_iff_ordConnected`.
3. (A) Show that `convexHull ℝ {x, y} = segment ℝ x y` from `convexHull_pair`.
4. (B) Prove that the hull of a finite set is compact in a normed space, with `Set.Finite.convexHull_eq` and the compactness of the standard simplex.
5. (B) Prove the Radon theorem in the plane for four points, with `Finset.centerMass`.
6. (C) Deduce from `exists_convex_convex_compl_subset` that two disjoint convex sets in `ℝ` are separated by a point.

### Reference

<?reference?>
