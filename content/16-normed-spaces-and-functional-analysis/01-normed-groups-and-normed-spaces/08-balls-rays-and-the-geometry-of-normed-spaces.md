---
title: Balls, rays and the geometry of normed spaces
kind: api
modules:
  - Mathlib.Analysis.Normed.Module.Ball.Action
  - Mathlib.Analysis.Normed.Module.Ball.Homeomorph
  - Mathlib.Analysis.Normed.Module.Ball.Pointwise
  - Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
  - Mathlib.Analysis.Normed.Module.Ray
  - Mathlib.Analysis.Normed.Module.Normalize
  - Mathlib.Analysis.Normed.Module.Connected
  - Mathlib.Analysis.Normed.Module.Convex
  - Mathlib.Analysis.Normed.Module.Extr
  - Mathlib.Analysis.Normed.Module.Span
explains:
  E2: [ball_add_ball, disjoint_ball_ball_iff, OpenPartialHomeomorph.univUnitBall_apply, homeomorphUnitSphereProd, SameRay.norm_add, NormedSpace.norm_normalize, isConnected_sphere, convexHull_sphere_eq_closedBall, IsMaxFilter.norm_add_sameRay, LinearEquiv.toSpanNonzeroSingleton_homothety]
  E1: auto
families: []
requires: [V07, V13, V15]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Balls, rays and the geometry of normed spaces

### Overview

In a metric space, a ball is only a set of points near a center. In a normed space over $\mathbb{R}$, a ball has more structure. It is convex, it is the image of the unit ball by a homothety and a translation, and it is homeomorphic to the whole space. The sum of two balls is a ball, and the distance between two disjoint balls is the sum of the radii. This section treats the files of the library that hold these facts.

The section also treats rays. Two vectors $x$ and $y$ are on the same ray when one of them is a nonnegative multiple of the other. In a normed space, this condition is equivalent to the equality $\|x + y\| = \|x\| + \|y\|$ in a strictly convex space, and it gives the direction $x / \|x\|$ of a nonzero vector. The last files give the connectedness of spheres and of complements of countable sets, the convexity of the norm, a remark on maxima of the norm, and the continuous coordinate on a line. The section uses the pointwise operations on sets of the section on uniformity, pointwise sets and bounded sets.

### The library around it

**Pointwise operations on balls.** The file `Mathlib.Analysis.Normed.Module.Ball.Pointwise` computes sums, differences and multiples of balls. The family `ball_add_ball`, `ball_add_closedBall`, `closedBall_add_ball` and `closedBall_add_closedBall` says that
$$B(a, \varepsilon) + B(b, \delta) = B(a + b, \varepsilon + \delta),$$
with a closed ball on the right only when both balls are closed. The family `ball_sub_ball` and its relatives does the same for differences. Proof sketch of `ball_add_ball`: the inclusion $\subseteq$ is the triangle inequality. For the converse, take $z$ with $\|z - a - b\| < \varepsilon + \delta$ and put $x = a + t(z - a - b)$ with $t = \varepsilon / (\varepsilon + \delta)$. Then $\|x - a\| < \varepsilon$ and $\|z - x - b\| < \delta$. This needs the real scalars: the result is false in a general metric group. The lemma `exists_dist_lt_lt` and its forms with non-strict inequalities, such as `exists_dist_le_le`, give the point between two points that the proof uses.

The multiples of balls are `smul_ball`, `smul_closedBall` and `smul_sphere`: for $c \ne 0$, $c \cdot B(x, r) = B(cx, \|c\| r)$. The affine forms `affinity_unitBall` and `affinity_unitClosedBall` say that $x + r \cdot B(0, 1) = B(x, r)$. The thickenings follow the same rules: `cthickening_ball` gives $\overline{N}_\varepsilon(B(x, \delta)) = \overline{B}(x, \varepsilon + \delta)$, and `closure_thickening` says that the closure of an open thickening is the closed thickening. The disjointness criterion is `disjoint_ball_ball_iff`: for positive radii, the balls $B(x, \delta)$ and $B(y, \varepsilon)$ are disjoint if and only if $\delta + \varepsilon \le d(x, y)$. For two closed balls, `disjoint_closedBall_closedBall_iff` has a strict inequality. The scaling of diameters and distances is `diam_smul₀`, `infDist_smul₀` and `ediam_smul₀`.

**Actions on balls.** The file `Mathlib.Analysis.Normed.Module.Ball.Action` makes the closed unit ball of the field act on balls and closed balls with center $0$, and the unit sphere of the field act on balls, closed balls and spheres with center $0$. The instances are `mulActionClosedBallBall`, `mulActionClosedBallClosedBall`, `mulActionSphereBall`, `mulActionSphereClosedBall` and `mulActionSphereSphere`. The file also gives the compatibility instances, such as `isScalarTower_sphere_sphere_sphere`, and the continuity instances, such as `continuousSMul_sphere_sphere`. The lemma `ne_neg_of_mem_sphere` says that a point $x$ of a sphere of nonzero radius satisfies $x \ne -x$, when the scalar field has characteristic zero.

**Homeomorphisms.** The file `Mathlib.Analysis.Normed.Module.Ball.Homeomorph` builds an explicit homeomorphism from a real normed space $E$ onto its open unit ball. The map is
$$x \mapsto \frac{x}{\sqrt{1 + \|x\|^2}},$$
with inverse $y \mapsto y / \sqrt{1 - \|y\|^2}$. These formulas are `OpenPartialHomeomorph.univUnitBall_apply` and `OpenPartialHomeomorph.univUnitBall_symm_apply`. The bundled map is `Homeomorph.unitBall`. The partial homeomorphism `OpenPartialHomeomorph.unitBallBall` sends the unit ball onto a ball $B(c, r)$ by $a \mapsto r a + c$, and `OpenPartialHomeomorph.univBall` composes the two maps, so that it sends all of $E$ onto $B(c, r)$. The file is stated for a metric torsor `P` over `E`, so the center $c$ can be a point of an affine space.

The file `Mathlib.Analysis.Normed.Module.Ball.RadialEquiv` gives the polar coordinates of a real normed space. The map `homeomorphUnitSphereProd` is a homeomorphism from $E \setminus \{0\}$ onto the product of the unit sphere and the interval $(0, \infty)$. It sends $x$ to the pair $(x / \|x\|, \|x\|)$, and the inverse sends $(u, t)$ to $t u$. The form `homeomorphSphereProd` uses a sphere of radius $r > 0$. The lemma `IsOpen.smul_sphere` says that the product of an open set of radii and an open set of the sphere is open.

**Rays.** The predicate `SameRay ℝ x y` of linear algebra says that $x = 0$, or $y = 0$, or $x = r y$ with $r > 0$. The file `Mathlib.Analysis.Normed.Module.Ray` relates it to the norm. If $x$ and $y$ are on the same ray, then $\|x + y\| = \|x\| + \|y\|$ and $\|x - y\| = |\|x\| - \|y\||$: these are `SameRay.norm_add` and `SameRay.norm_sub`. The criterion `sameRay_iff_norm_smul_eq` says that $x$ and $y$ are on the same ray if and only if $\|x\| y = \|y\| x$. The form `sameRay_iff_inv_norm_smul_eq_of_ne` compares the directions of two nonzero vectors. On a ray, the norm is injective: this is `norm_injOn_ray_left`, and its consequence `SameRay.norm_eq_iff` says that two vectors on the same ray with the same norm are equal.

The file `Mathlib.Analysis.Normed.Module.Normalize` names the direction. `NormedSpace.normalize x` is $\|x\|^{-1} x$, and it is $0$ for $x = 0$. The lemma `NormedSpace.norm_normalize` says that its norm is $1$ for $x \ne 0$, and `NormedSpace.norm_smul_normalize` gives back $x = \|x\| \cdot \operatorname{normalize}(x)$. The scaling rule `NormedSpace.normalize_smul` multiplies the direction by the sign of the scalar, and `NormedSpace.sameRay_iff_normalize_eq_of_ne` says that two nonzero vectors are on the same ray if and only if they have the same direction.

**Connectedness and convexity.** The file `Mathlib.Analysis.Normed.Module.Connected` proves that balls are path connected and contractible (`Metric.isPathConnected_ball`, `Metric.contractibleSpace_ball`). The main results use the dimension. If the real dimension of $E$ is at least $2$, the complement of a countable set is path connected (`Set.Countable.isPathConnected_compl_of_one_lt_rank`), and so is each sphere (`isConnected_sphere`, `isPathConnected_sphere`). A subspace of codimension at least $2$ has a connected complement: `isConnected_compl_of_one_lt_codim`. The hypothesis is written `1 < Module.rank ℝ E`, a cardinal inequality, so it also covers infinite dimensional spaces.

The file `Mathlib.Analysis.Normed.Module.Convex` holds the convexity facts. Balls are convex (`convex_ball`, `convex_closedBall`), the norm is a convex function (`convexOn_norm`, `convexOn_univ_norm`), and a thickening of a convex set is convex (`Convex.thickening`). The convex hull has the same diameter as the set (`convexHull_diam`), and the convex hull of a sphere is the closed ball (`convexHull_sphere_eq_closedBall`). A real normed space is path connected by the instance `NormedSpace.instPathConnectedSpace`. Proof sketch of `convexHull_sphere_eq_closedBall` for $r > 0$: a point $y$ of the closed ball is on the segment between the two points where the line through $x$ and $y$ meets the sphere.

**Maxima of the norm.** The file `Mathlib.Analysis.Normed.Module.Extr` proves one remark. Suppose that $\|f\|$ has a maximum at $c$ along a filter, and that $y$ is on the same ray as $f(c)$. Then $x \mapsto \|f(x) + y\|$ also has a maximum at $c$. This is `IsMaxFilter.norm_add_sameRay`. The proof is short: $\|f(x) + y\| \le \|f(x)\| + \|y\| \le \|f(c)\| + \|y\| = \|f(c) + y\|$, where the last equality is `SameRay.norm_add`. The file gives the forms for `IsMaxOn`, `IsLocalMaxOn` and `IsLocalMax`, and the case $y = f(c)$ as `IsMaxFilter.norm_add_self`. The theory of strictly convex spaces and the maximum modulus principle of complex analysis use it.

**Lines.** The file `Mathlib.Analysis.Normed.Module.Span` studies the span of one vector. `LinearMap.toSpanSingleton_homothety` says that $\|c x\| = \|x\| \|c\|$, so the map $c \mapsto c x$ is a homothety with ratio $\|x\|$. For $x \ne 0$, `ContinuousLinearEquiv.toSpanNonzeroSingleton` is the continuous linear equivalence from the field onto the line $\mathbb{K} x$, and `ContinuousLinearEquiv.coord` is its inverse, the coordinate on the line. For a unit vector, `LinearIsometryEquiv.toSpanUnitSingleton` is an isometry. The lemma `ContinuousLinearEquiv.coord_norm'` computes the norm of the coordinate, and the chapter on the theorem of Hahn and Banach extends this functional from the line to the whole space.

#### Common errors

1. Using `ball_add_ball` with a zero radius. The open ball of radius $0$ is empty, so the hypotheses $0 < \varepsilon$ and $0 < \delta$ are necessary. For radius $0$, use the closed forms.
2. Expecting $\|x + y\| = \|x\| + \|y\|$ to imply `SameRay ℝ x y`. The converse holds only in a strictly convex space. In $\mathbb{R}^2$ with the sup norm, $(1, 0)$ and $(1, 1)$ give equality but are not on the same ray.
3. Forgetting that `NormedSpace.normalize 0 = 0`. A lemma such as `NormedSpace.norm_normalize` needs the hypothesis $x \ne 0$.

### Exercises

1. (A) Use `smul_ball` and `affinity_unitBall` to show that the image of $B(0, 1)$ by $x \mapsto 3x + a$ is $B(a, 3)$.
2. (A) Prove `SameRay.norm_add` from the definition of `SameRay` and the homogeneity of the norm.
3. (B) Show that two closed balls $\overline{B}(x, \delta)$ and $\overline{B}(y, \varepsilon)$ with $\delta + \varepsilon = d(x, y)$ meet, and find the common point.
4. (B) Show that the sphere of $\mathbb{R}$ is not connected, and explain which hypothesis of `isConnected_sphere` fails.
5. (B) Check the formula of `OpenPartialHomeomorph.univUnitBall_symm_apply` by composing it with the formula of `OpenPartialHomeomorph.univUnitBall_apply`.
6. (C) Prove that the complement of a countable set in $\mathbb{R}^2$ is path connected, with the idea of the proof of `Set.Countable.isPathConnected_compl_of_one_lt_rank`: through each point pass uncountably many lines.

### Reference

<?reference?>
