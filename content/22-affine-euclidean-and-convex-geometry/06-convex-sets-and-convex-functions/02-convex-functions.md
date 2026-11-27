---
title: Convex functions and affine maps
kind: theory
modules:
  - Mathlib.Geometry.Convex.ConvexSpace.AffineMap
  - Mathlib.Geometry.Convex.ConvexSpace.AffineMapCone
  - Mathlib.Geometry.Convex.ConvexSpace.Topology
  - Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology
  - Mathlib.Geometry.Convex.AffineMap.Defs
explains:
  E3: [Convexity.ConvexSpace.AffineMap, Convexity.StdSimplex.affineMapMk, Convexity.StdSimplex.affineMap_ext, Convexity.StdSimplex.continuous_of_isAffineMap, Convexity.StdSimplex.topologicalSpace, Convexity.ConvexSpace.AffineMap.cone]
  E2: [Convexity.ConvexSpace.AffineMap.isAffineMap, Convexity.ConvexSpace.AffineMap.comp, Convexity.StdSimplex.affineMapMk_single, Convexity.ConvexSpace.AffineMap.cone_single_zero, Convexity.ConvexSpace.AffineMap.cone_single_succ, Convexity.StdSimplex.continuous_iff]
  E1: auto
families: []
requires: [V07, V13, V15.C04, V16.C05, V22.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Convex functions and affine maps

### Overview

A convex function lies below its chords. Volume 15, Chapter 4 treats convex functions of one real variable and their derivatives. This section works on a convex subset of a real vector space and proves the epigraph test, the finite Jensen inequality, the maximum principle and the fact that a local minimum is global. It then turns to affine maps of the convex spaces of Section 1 of this chapter, and proves that $\Delta_R(M)$ is the free convex space on $M$.

### Definitions

Let $E$ be a real vector space and $S \subseteq E$ convex.

**Definition (convex function).** A function $f : S \to \mathbb{R}$ is *convex* if $f(s x + t y) \le s f(x) + t f(y)$ for all $x, y \in S$ and $s, t \ge 0$ with $s + t = 1$. It is *concave* if $-f$ is convex.

**Definition (epigraph).** The *epigraph* of $f : S \to \mathbb{R}$ is the set $\mathrm{epi}(f) = \{ (x, r) \in E \times \mathbb{R} : x \in S,\ f(x) \le r \}$.

**Definition (affine map of convex spaces).** Let $X$, $Y$ be convex spaces over $R$. A *bundled affine map* $X \to Y$ is a pair of a function $f$ and a proof that $f(c(w)) = c(f_*w)$ for all $w \in \Delta_R(X)$. Bundled affine maps are closed under composition.

**Definition (free convex space).** For a set $M$ the set $\Delta_R(M)$ is a convex space with the combination $\mu$ that flattens a distribution of distributions. The *vertices* are the point masses $\delta_m$.

### Theorems and proofs

**Theorem (epigraph test).** A function $f : S \to \mathbb{R}$ is convex if and only if $\mathrm{epi}(f)$ is a convex subset of $E \times \mathbb{R}$.

*Proof.* If $f$ is convex and $(x, r)$, $(y, q)$ lie in the epigraph, then $f(s x + t y) \le s f(x) + t f(y) \le s r + t q$, so $s(x, r) + t(y, q) \in \mathrm{epi}(f)$. Conversely, if the epigraph is convex, it contains $(s x + t y, s f(x) + t f(y))$, which says $f(s x + t y) \le s f(x) + t f(y)$. $\square$

**Theorem (Jensen, finite form).** Let $f : S \to \mathbb{R}$ be convex, $x_1, \dots, x_n \in S$ and $w_1, \dots, w_n \ge 0$ with $\sum w_i = 1$. Then $f\big(\sum w_i x_i\big) \le \sum w_i f(x_i)$.

*Proof.* Induct on $n$. For $n = 1$, $w_1 = 1$ and both sides are $f(x_1)$. Let $n \ge 2$. If $w_n = 1$, all other weights are $0$ and both sides are $f(x_n)$. Otherwise put $a = w_n < 1$ and $y = \sum_{i<n} \frac{w_i}{1-a} x_i$. Then $y \in S$ by Section 1, and $f(y) \le \sum_{i<n} \frac{w_i}{1-a} f(x_i)$ by induction. Now $\sum w_i x_i = (1-a) y + a x_n$, so convexity gives
$$f\Big(\sum_i w_i x_i\Big) \le (1-a) f(y) + a f(x_n) \le \sum_{i<n} w_i f(x_i) + w_n f(x_n). \qquad \square$$

**Corollary (maximum principle).** Let $f : S \to \mathbb{R}$ be convex and $T \subseteq S$ finite and nonempty. For each $x$ in the convex hull of $T$, $f(x) \le \max_{y \in T} f(y)$. So $f$ attains its maximum on the hull at a point of $T$.

*Proof.* Write $x = \sum_{y \in T} w_y\, y$ with $w_y \ge 0$ and $\sum w_y = 1$. Jensen gives $f(x) \le \sum w_y f(y) \le \sum w_y \max_T f = \max_T f$. $\square$

**Theorem (local minima are global).** Let $E$ be a real topological vector space, $S \subseteq E$ convex, $f : S \to \mathbb{R}$ convex, and $a \in S$ a local minimum of $f$ on $S$. Then $f(a) \le f(x)$ for all $x \in S$.

*Proof.* Let $x \in S$. The map $t \mapsto a + t(x - a)$ is continuous and sends $0$ to $a$. So for a small $t \in (0, 1]$ the point $a + t(x-a)$ lies in $S$ and near $a$, and $f(a) \le f(a + t(x-a))$. Convexity gives $f(a + t(x-a)) \le (1-t) f(a) + t f(x)$. So $f(a) \le (1-t) f(a) + t f(x)$, that is $t f(a) \le t f(x)$. Divide by $t > 0$. $\square$

A function that is both convex and concave preserves binary combinations, so by Section 1 it is an affine map of convex spaces from $S$ to $\mathbb{R}$.

**Theorem (free convex space).** Let $M$ be a set and $X$ a convex space over $R$. For each map $g : M \to X$ there is exactly one affine map $\hat g : \Delta_R(M) \to X$ with $\hat g(\delta_m) = g(m)$ for all $m$. It is $\hat g(w) = c(g_* w)$.

*Proof.* First, each $w \in \Delta_R(M)$ is the combination of its vertices in the convex space $\Delta_R(M)$: the distribution $\delta_*w$ on $\Delta_R(M)$ puts weight $w(m)$ on $\delta_m$, and its flattening is $\sum_m w(m) \delta_m = w$. So $w = \mu(\delta_* w)$.

Uniqueness. If $h$ is affine with $h(\delta_m) = g(m)$, then $h(w) = h(\mu(\delta_* w)) = c(h_* \delta_* w) = c((h \circ \delta)_* w) = c(g_* w)$.

Existence. Put $\hat g(w) = c(g_* w)$. Then $\hat g(\delta_m) = c(\delta_{g(m)}) = g(m)$ by axiom 1. Let $F \in \Delta_R(\Delta_R(M))$. Push-forward commutes with flattening, so $g_*\mu(F) = \mu((g_*)_* F)$. Axiom 2 for $X$ applied to $(g_*)_*F$ gives
$$\hat g(\mu(F)) = c(\mu((g_*)_*F)) = c(c_*(g_*)_*F) = c(\hat g_* F).$$
So $\hat g$ is affine. $\square$

**Theorem (continuity on a finite simplex).** Let $\iota$ be finite, $E$ a real topological vector space, and $f : \Delta_\mathbb{R}(\iota) \to E$ affine, where $\Delta_\mathbb{R}(\iota) \subseteq \mathbb{R}^\iota$ has the subspace topology. Then $f$ is continuous.

*Proof.* By the uniqueness above, $f(w) = \sum_{i \in \iota} w(i)\, f(\delta_i)$. Each coordinate $w \mapsto w(i)$ is continuous, and scalar multiplication and finite sums are continuous in $E$. $\square$

### Examples

**Example (a maximum at a vertex).** Let $f(u, v) = u^2 + v^2$ on the triangle $T$ with vertices $(0,0)$, $(2,0)$ and $(0,1)$. The function is convex, because it is a sum of convex functions of one variable (Volume 15, Chapter 4). The values at the vertices are $0$, $4$ and $1$. By the maximum principle, $\max_T f = 4$, attained at $(2, 0)$.

**Counterexample (the maximum principle needs convexity).** Let $g(u, v) = -(u^2 + v^2)$ on the square with vertices $(\pm 1, \pm 1)$. The values at the vertices are all $-2$, but $g(0,0) = 0 > -2$. The function $g$ is concave, not convex, and its maximum lies in the interior.

**Example (an affine map from a simplex).** Let $g : \{0, 1, 2\} \to \mathbb{R}^2$ send $0, 1, 2$ to $(0,0)$, $(1,0)$ and $(0,1)$. Then $\hat g(w) = (w(1), w(2))$. The image is the triangle with these vertices. With $g(2) = (2, 0)$ instead, the image is the segment from $(0,0)$ to $(2,0)$, and $\hat g$ is not injective: the barycenter of the three vertices and the vertex $\delta_1$ both map to $(1, 0)$.

### The library around it

::: mathlib
`ConvexOn` · `Mathlib.Analysis.Convex.Function`

`ConvexOn 𝕜 s f` asks that `s` is convex and that `f (a • x + b • y) ≤ a • f x + b • f y`. It belongs to Volume 16. The epigraph test is `convexOn_iff_convex_epigraph`, the finite Jensen inequality is `ConvexOn.map_sum_le` in `Mathlib.Analysis.Convex.Jensen`, the maximum principle is `ConvexOn.exists_ge_of_mem_convexHull`, and the statement on local minima is `IsMinOn.of_isLocalMinOn_of_convexOn`.

<?decl ConvexOn?>
:::

::: mathlib
`Convexity.ConvexSpace.AffineMap` · `Mathlib.Geometry.Convex.ConvexSpace.AffineMap`

The structure `ConvexSpace.AffineMap R X Y` bundles a function with `isAffineMap_toFun`. `AffineMap.comp` composes, and `AffineMap.isAffineMap` gives the unbundled predicate.

<?decl Convexity.ConvexSpace.AffineMap?>
:::

::: mathlib
`Convexity.StdSimplex.affineMapMk` · `Mathlib.Geometry.Convex.ConvexSpace.AffineMap`

`StdSimplex.affineMapMk f` is the extension $\hat g$ of the theorem on free convex spaces. `affineMapMk_single` gives its value at a vertex, `StdSimplex.affineMap_ext` is the uniqueness.

<?decl Convexity.StdSimplex.affineMap_ext?>
:::

::: mathlib
`Convexity.ConvexSpace.AffineMap.cone` · `Mathlib.Geometry.Convex.ConvexSpace.AffineMapCone`

Given an affine map `s` out of the simplex on `Fin n` and a point `y`, `s.cone y` is the affine map out of the simplex on `Fin (n + 1)` that sends vertex `0` to `y` (`cone_single_zero`) and vertex `i.succ` to the image of vertex `i` (`cone_single_succ`). Chapter 8 uses it.

<?decl Convexity.ConvexSpace.AffineMap.cone?>
:::

::: mathlib
`Convexity.StdSimplex.topologicalSpace` · `Mathlib.Geometry.Convex.ConvexSpace.Topology`

The instance gives `StdSimplex R M` the final topology for the finite pieces, and `StdSimplex.continuous_iff` tests continuity on them.

<?decl Convexity.StdSimplex.continuous_iff?>
:::

::: mathlib
`Convexity.StdSimplex.continuous_of_isAffineMap` · `Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology`

An affine map from `StdSimplex R ι` to a topological module `E` with `IsModuleConvexSpace R E` is continuous, for any `ι`.

<?decl Convexity.StdSimplex.continuous_of_isAffineMap?>
:::

### Exercises

1. (A) Show that $f(x) = \|x\|$ is convex on a normed space, and that its epigraph is a convex cone.
2. (A) Find the maximum of $f(u, v) = (u - 1)^2 + v^2$ on the square $[0,2] \times [0,2]$, and check that it is attained at a vertex.
3. (B) Show that the supremum of a family of convex functions $S \to \mathbb{R}$ is convex where it is finite. Hint: the epigraph of the supremum is the intersection of the epigraphs.
4. (B) Show that a strictly convex function on a convex set has at most one minimum point.
5. (B) In the free convex space $\Delta_\mathbb{R}(\{0,1\})$ compute $\mu(F)$ for $F = \tfrac12 \delta_{\delta_0} + \tfrac12 \delta_{v}$ with $v = \tfrac13\delta_0 + \tfrac23\delta_1$.
6. (C) Let $X$ be a convex space and $A \subseteq X$. Show that the image of $\widehat{\iota_A} : \Delta_R(A) \to X$, where $\iota_A$ is the inclusion, is the smallest convex subset of $X$ that contains $A$. Hint: the stability theorem of Section 1.

### Notes and history

Jensen published the inequality for convex functions in 1906. The Mathlib files on bundled affine maps, the cone construction and the topology on the simplex name Joël Riou as an author, and the file on affine maps also names Yaël Dillies.

### Reference

<?reference?>
