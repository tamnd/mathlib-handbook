---
title: Convex functions and the Jensen inequality
kind: api
modules:
  - Mathlib.Analysis.Convex.Function
  - Mathlib.Analysis.Convex.Jensen
  - Mathlib.Analysis.Convex.Slope
  - Mathlib.Analysis.Convex.Mul
  - Mathlib.Analysis.Convex.Piecewise
  - Mathlib.Analysis.Convex.Quasiconvex
  - Mathlib.Analysis.Convex.Strong
  - Mathlib.Analysis.Convex.Extrema
  - Mathlib.Analysis.Convex.StrictCombination
explains:
  E2: [ConvexOn, StrictConvexOn, ConvexOn.convex_epigraph, ConvexOn.map_sum_le, StrictConvexOn.map_sum_eq_iff, convexOn_iff_slope_mono_adjacent, QuasiconvexOn, UniformConvexOn, StrongConvexOn, IsMinOn.of_isLocalMinOn_of_convexOn]
  E1: auto
families: []
requires: [V07, V13, V16.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Convex functions and the Jensen inequality

### Overview

A function $f$ on a convex set $s$ is convex when $f(a x + b y) \le a f(x) + b f(y)$ for all $x, y \in s$ and all $a, b \ge 0$ with $a + b = 1$. Equivalently, the epigraph $\{(x, t) : x \in s, f(x) \le t\}$ is a convex set. A concave function is one whose negative is convex, and a strictly convex function has strict inequality for $x \ne y$ and $a, b > 0$. In Mathlib these notions take three type arguments: the scalars `𝕜`, the domain `E`, and an ordered module `β` of values. So one definition covers real functions and functions into an ordered vector space.

The Jensen inequality extends the definition from two points to finitely many: $f(\sum_i w_i x_i) \le \sum_i w_i f(x_i)$ for nonnegative weights that sum to $1$. For a strictly convex function, equality holds only when all points with positive weight are equal. With the description of the convex hull from Section 1, it also gives the maximum principle: a convex function on the hull of a finite set $t$ is bounded by its maximum on $t$.

On the real line, convexity is a condition on slopes. The function $f$ is convex on an interval if and only if, for $x < y < z$, the slope from $x$ to $y$ is at most the slope from $y$ to $z$. This is the basis for the tests with derivatives in Section 3.

### The library around it

The file `Mathlib.Analysis.Convex.Function` defines `ConvexOn 𝕜 s f`, `ConcaveOn 𝕜 s f`, `StrictConvexOn 𝕜 s f` and `StrictConcaveOn 𝕜 s f`. Each one is the conjunction of `Convex 𝕜 s` and the inequality. The lemma `convexOn_iff_forall_pos` drops the cases $a = 0$ and $b = 0$, and `convexOn_iff_div` uses weights $a / (a + b)$ and $b / (a + b)$. The epigraph form is `ConvexOn.convex_epigraph`, with the converse `convexOn_of_convex_epigraph`, and the sublevel sets are convex by `ConvexOn.convex_le` and `ConvexOn.convex_lt`. The algebra of convex functions is in `ConvexOn.add`, `ConvexOn.smul`, `ConvexOn.sup`, `ConvexOn.comp_affineMap`, `ConvexOn.comp_linearMap` and `ConvexOn.comp`, which composes with a convex function that is monotone on the image. The lemma `ConvexOn.dual` passes to the order dual of `β`, which turns a convex function into a concave one, and `neg_convexOn_iff` does the same with a sign in an ordered group. A linear map is convex and concave, by `LinearMap.convexOn` and `LinearMap.concaveOn`. On a linear order, `LinearOrder.convexOn_of_lt` lets a proof check only the case $x < y$. The lemma `ConvexOn.le_on_segment` says that on a segment the function is at most the larger value at the end points.

The file `Mathlib.Analysis.Convex.Jensen` holds the inequality. `ConvexOn.map_sum_le` is the form with weights that sum to $1$, and `ConvexOn.map_centerMass_le` is the form with `Finset.centerMass`. The concave forms are `ConcaveOn.le_map_sum` and `ConcaveOn.le_map_centerMass`. The strict form `StrictConvexOn.map_sum_lt` needs two distinct points with positive weight, and `StrictConvexOn.map_sum_eq_iff` says that equality holds if and only if each point is the weighted mean. The maximum principle is `ConvexOn.exists_ge_of_mem_convexHull`: for `x` in the hull of `t`, there is `y ∈ t` with `f x ≤ f y`. The proof of `ConvexOn.map_sum_le` is by induction on the finite set. For a new point $p_0$ with weight $w_0 < 1$, write $\sum_i w_i p_i = w_0 p_0 + (1 - w_0) q$, where $q$ is the mean of the other points with the weights $w_i / (1 - w_0)$. The point $q$ is in $s$ by `Convex.sum_mem`, so the definition of convexity and the induction hypothesis for $q$ give the bound. The variants `ConvexOn.le_sup_of_mem_convexHull`, `ConvexOn.bddAbove_convexHull` and `ConvexOn.le_max_of_mem_segment` give the bound in other forms.

The file `Mathlib.Analysis.Convex.Slope` works with `f : 𝕜 → 𝕜` for a linearly ordered field `𝕜`. The criterion is `convexOn_iff_slope_mono_adjacent`, with the two directions `ConvexOn.slope_mono_adjacent` and `convexOn_of_slope_mono_adjacent`, and the strict and concave analogues. The lemma `ConvexOn.secant_mono` says that the slope $(f(x) - f(a)) / (x - a)$ is monotone in $x$ for a fixed base point $a$. The lemma `ConvexOn.strictMonoOn` says that once a convex function increases, it is strictly increasing to the right of that point.

The file `Mathlib.Analysis.Convex.Mul` treats products. `ConvexOn.mul` says that the product of two nonnegative convex functions is convex when they vary in the same direction, a condition stated with `MonovaryOn`. Its consequences are `ConvexOn.pow`, `convexOn_pow` on `Set.Ici 0`, `Even.convexOn_pow` on all of `𝕜`, and `convexOn_zpow` on `Set.Ioi 0`. The lemma `ConvexOn.mul_concaveOn` treats a nonnegative convex function times a nonpositive concave one that vary in opposite directions, with `AntivaryOn`, and the result is concave. The lemmas `ConvexOn.smul''` and `ConcaveOn.smul_convexOn` are the forms for a scalar function times a vector function. The file `Mathlib.Analysis.Convex.Piecewise` glues two functions at a point: the lemma `convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic` says that if `f` is convex and monotone on the right of `e`, `g` is convex and antitone on the left, and the values agree at `e`, then the glued function is convex.

The file `Mathlib.Analysis.Convex.Quasiconvex` defines `QuasiconvexOn 𝕜 s f`, which says that each sublevel set is convex, `QuasiconcaveOn 𝕜 s f` and `QuasilinearOn 𝕜 s f` for both. The lemma `quasiconvexOn_iff_le_max` gives the form $f(a x + b y) \le \max(f(x), f(y))$, and `ConvexOn.quasiconvexOn` says that a convex function is quasiconvex. On the scalars, `quasilinearOn_iff_monotoneOn_or_antitoneOn` says that a quasilinear function on a convex set is monotone or antitone.

The file `Mathlib.Analysis.Convex.Strong` works in a real normed space. The definition `UniformConvexOn s φ f` asks for $f(a x + b y) \le a f(x) + b f(y) - a b \, \varphi(\|x - y\|)$, and `StrongConvexOn s m f` is the case $\varphi(r) = (m / 2) r^2$. The lemma `strongConvexOn_iff_convex` says that `f` is `m` strongly convex if and only if $f - (m / 2) \|x\|^2$ is convex, which holds in an inner product space. The lemma `UniformConvexOn.strictConvexOn` gives strict convexity when $\varphi(r) > 0$ for $r \ne 0$.

The file `Mathlib.Analysis.Convex.Extrema` proves that a local minimum of a convex function is a global minimum. The main form is `IsMinOn.of_isLocalMinOn_of_convexOn`, which works on a convex set `s` in a real topological vector space, and `IsMinOn.of_isLocalMin_of_convex_univ` is the version on the whole space. The proof compares the value at `a` with the values on a short segment from `a` towards `x`.

The file `Mathlib.Analysis.Convex.StrictCombination` applies the strict Jensen idea to norms in a strictly convex space, which is the class of Section 6. The lemma `norm_sum_lt_of_strictConvexSpace` says that a convex combination of points in a closed ball of radius $r$ has norm less than $r$ when two distinct points have positive weight. The lemma `StrictConvex.centerMass_mem_interior` is the form for a strictly convex set, and `Affine.Simplex.dist_lt_of_mem_interior_of_strictConvexSpace` applies it to the vertices of a simplex.

#### Common errors

1. `ConvexOn 𝕜 s f` includes `Convex 𝕜 s`. A proof by `refine ⟨?_, ?_⟩` must also prove the convexity of the domain, and `ConvexOn.subset` needs it for the smaller set.
2. `ConvexOn.comp` needs the outer function to be monotone on the image. The composition of two convex functions is not convex in general, for example $x \mapsto -x$ after $x \mapsto x^2$.
3. `StrongConvexOn s m f` uses the factor $m / 2$, so the function $\|x\|^2$ is `StrongConvexOn s 2`, not `StrongConvexOn s 1`.

### Exercises

1. (A) Prove that $x \mapsto |x|$ is convex on `ℝ` from `LinearMap.convexOn` and `ConvexOn.sup`.
2. (A) Derive the inequality of arithmetic and quadratic means from `ConvexOn.map_sum_le` and `Even.convexOn_pow`.
3. (A) Show that a convex function on `ℝ` that is bounded above is constant, with `ConvexOn.secant_mono`.
4. (B) Prove that the maximum of a convex function on a compact convex polytope is attained at a vertex, with `ConvexOn.exists_ge_of_mem_convexHull`.
5. (B) Prove that a strictly convex function has at most one minimum on a convex set.
6. (C) Prove that a strongly convex continuous function on a closed convex set in a Hilbert space attains its minimum.

### Reference

<?reference?>
