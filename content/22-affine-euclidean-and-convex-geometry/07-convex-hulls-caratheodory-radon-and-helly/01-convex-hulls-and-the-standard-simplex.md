---
title: Convex hulls and the standard simplex
kind: theory
modules:
  - Mathlib.Geometry.Convex.Hull
  - Mathlib.Analysis.Convex.StdSimplex
  - Mathlib.Analysis.Convex.Independent
  - Mathlib.Geometry.Convex.ConvexSpace.Barycenter
  - Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
  - Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
explains:
  E3: [Convexity.convexHull, Convexity.mem_convexHull_iff, Set.convexHull_eq_range_iConvexComb, Convexity.IsAffineMap.image_convexHull, ConvexIndependent, convexIndependent_set_iff_notMem_convexHull_sdiff, Convexity.StdSimplex.barycenter, Convexity.StdSimplex.compactSpace]
  E2: [Convexity.convexHull_min, Convexity.convexHull_eq_iInter, Convexity.convexHull_convexHull_union, Convexity.IsConvexSet.sdiff_singleton_iff_notMem_convexHull, Convexity.ConvexSpace.AffineMap.convex_range, convexIndependent_iff_finset, Convexity.StdSimplex.subBarycenter, Convexity.StdSimplex.weights_barycenter_apply, Convexity.StdSimplex.pathConnectedSpace, Convexity.StdSimplex.homeomorphI]
  E1: auto
families: []
requires: [V07, V13, V16.C05, V22.C01, V22.C02, V22.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Convex hulls and the standard simplex

### Overview

The convex hull of a set $A$ is the smallest convex set that contains $A$. This section proves, in any convex space, that it is the set of all convex combinations of points of $A$. It then studies the standard simplex and convex independence.

### Definitions

Let $X$ be a convex space over an ordered semiring $R$, as in Chapter 6.

**Definition (convex hull).** The *convex hull* of $A \subseteq X$ is
$$\mathrm{conv}(A) = \bigcap \{ C \subseteq X : A \subseteq C,\ C \text{ convex} \}.$$

The intersection is convex by the stability theorem of Chapter 6, Section 1. So $\mathrm{conv}(A)$ is the smallest convex set that contains $A$. The map $A \mapsto \mathrm{conv}(A)$ is a closure operator.

**Definition (standard simplex).** For a finite set $M$ the *standard simplex* on $M$ is $\Delta_R(M)$, the set of functions $w : M \to R$ with $w \ge 0$ and $\sum_m w(m) = 1$. Its *vertices* are the point masses $\delta_m$. The simplex $\Delta_n = \Delta_\mathbb{R}(\{0, \dots, n\})$ has dimension $n$.

**Definition (barycenter).** For a nonempty finite set $S \subseteq M$, the *barycenter* $b_S \in \Delta_K(M)$ over a field $K$ has weight $1/|S|$ at each point of $S$ and $0$ elsewhere. The barycenter of the simplex is $b_M$.

**Definition (convex independence).** Let $E$ be a vector space over an ordered field $K$. A family $(p_i)_{i \in I}$ in $E$ is *convex independent* if, for every $J \subseteq I$ and $i \in I$, $p_i \in \mathrm{conv}\{p_j : j \in J\}$ implies $i \in J$.

### Theorems and proofs

**Theorem (the hull from inside).** Let $A \subseteq X$, let $\iota : A \to X$ be the inclusion and $\hat\iota : \Delta_R(A) \to X$ its affine extension, $\hat\iota(w) = c(\iota_* w)$. Then $\mathrm{conv}(A) = \hat\iota(\Delta_R(A))$. So $x \in \mathrm{conv}(A)$ if and only if $x = c(w)$ for a distribution $w$ with finite support in $A$.

*Proof.* The map $\hat\iota$ is affine by the theorem on free convex spaces (Chapter 6, Section 2). By the stability theorem, its image $B = \hat\iota(\Delta_R(A))$ is convex. It contains each $a \in A$, because $\hat\iota(\delta_a) = a$. So $\mathrm{conv}(A) \subseteq B$. Conversely, let $C$ be convex with $A \subseteq C$. For $w \in \Delta_R(A)$, the distribution $\iota_* w$ has support in $A \subseteq C$, so $c(\iota_* w) \in C$. So $B \subseteq C$ for every such $C$, and $B \subseteq \mathrm{conv}(A)$. $\square$

In a vector space $E$ over $\mathbb{R}$ this says: $x \in \mathrm{conv}(A)$ if and only if $x = \sum_{k=1}^n w_k a_k$ with $a_k \in A$, $w_k \ge 0$ and $\sum w_k = 1$.

**Theorem (rules for hulls).** Let $A, B \subseteq X$ and let $f : X \to Y$ be affine.

1. $\mathrm{conv}(\mathrm{conv}(A) \cup B) = \mathrm{conv}(A \cup B)$.
2. $f(\mathrm{conv}(A)) = \mathrm{conv}(f(A))$.

*Proof.* (1) The set on the right is convex and contains $A$, so it contains $\mathrm{conv}(A)$. It also contains $B$. So it contains $\mathrm{conv}(A) \cup B$ and its hull. The other inclusion follows from $A \cup B \subseteq \mathrm{conv}(A) \cup B$ and monotonicity.

(2) The set $f(\mathrm{conv}(A))$ is convex by the stability theorem and contains $f(A)$, so it contains $\mathrm{conv}(f(A))$. Conversely, $f^{-1}(\mathrm{conv}(f(A)))$ is convex by the stability theorem and contains $A$. So it contains $\mathrm{conv}(A)$, which means $f(\mathrm{conv}(A)) \subseteq \mathrm{conv}(f(A))$. $\square$

**Theorem (removing one point).** Let $S \subseteq X$ be convex and $x \in X$. Then $S \setminus \{x\}$ is convex if and only if $x \notin \mathrm{conv}(S \setminus \{x\})$.

*Proof.* If $S \setminus \{x\}$ is convex, it is its own hull, and it does not contain $x$. Conversely, suppose $x \notin \mathrm{conv}(S \setminus \{x\})$. By monotonicity, $\mathrm{conv}(S \setminus \{x\}) \subseteq \mathrm{conv}(S) = S$. It does not contain $x$, so it lies in $S \setminus \{x\}$. It also contains $S \setminus \{x\}$. So $S \setminus \{x\}$ equals its hull and is convex. $\square$

Chapter 8 calls such a point $x$ of $S$ an extreme point.

**Theorem (the simplex is compact and path-connected).** Let $M$ be finite and nonempty. Then $\Delta_\mathbb{R}(M) \subseteq \mathbb{R}^M$ is compact and path-connected.

*Proof.* The set is the intersection of the closed half-spaces $\{w(m) \ge 0\}$ with the closed hyperplane $\{\sum_m w(m) = 1\}$, so it is closed. Each coordinate of a point lies in $[0, 1]$, so it is bounded. By the theorem of Heine and Borel (Volume 13) it is compact. It is convex and nonempty, so the segment from any point to any other is a path inside it. $\square$

**Theorem (affine independence implies convex independence).** Let $(p_i)_{i \in I}$ be affinely independent in $E$, in the sense of Volume 22, Chapter 2. Then $(p_i)$ is convex independent.

*Proof.* Let $J \subseteq I$ and suppose $p_i \in \mathrm{conv}\{p_j : j \in J\}$. Write $p_i = \sum_{j \in J_0} w_j p_j$ with $J_0 \subseteq J$ finite, $w_j \ge 0$ and $\sum w_j = 1$. Suppose $i \notin J$. Then the coefficients $1$ at $i$ and $-w_j$ at $j \in J_0$ give an affine relation $p_i - \sum_j w_j p_j = 0$ whose coefficients sum to $1 - 1 = 0$. The coefficient at $i$ is $1 \ne 0$. This contradicts affine independence. So $i \in J$. $\square$

### Examples

**Example (barycentric coordinates in a triangle).** Let $a = (0,0)$, $b = (4, 0)$ and $c = (0, 2)$ in $\mathbb{R}^2$. The point $x = (1, 1)$ is $w_a a + w_b b + w_c c$ with $4 w_b = 1$ and $2 w_c = 1$. So $w_b = \tfrac14$, $w_c = \tfrac12$ and $w_a = 1 - \tfrac14 - \tfrac12 = \tfrac14$. All three weights are positive, so $x$ lies in the interior of the triangle.

**Example (a hull of four points).** Let $A = \{(0,0), (2,0), (0,2), (1, \tfrac12)\}$. The fourth point is $\tfrac12 (0,0) + \tfrac14 (2,0) + \tfrac14 (0,2)$, so it lies in the hull of the other three. So $\mathrm{conv}(A)$ is the triangle with vertices $(0,0)$, $(2,0)$, $(0,2)$, and the family $A$ is not convex independent. By contrast, the four vertices of a square are convex independent, but they are not affinely independent in $\mathbb{R}^2$, because four points in the plane always satisfy an affine relation. So the converse of the last theorem fails.

**Counterexample (the hull of a closed set need not be closed).** Let $A = \{(0,0)\} \cup \{(t, 1) : t \in \mathbb{R}\}$, a closed subset of $\mathbb{R}^2$. A point $(u, v)$ with $0 < v \le 1$ is $(1 - v)(0,0) + v(u/v, 1)$. So
$$\mathrm{conv}(A) = \{(0, 0)\} \cup \{(u, v) : 0 < v \le 1\}.$$
The points $(1, 1/n)$ lie in it and tend to $(1, 0)$, which does not.

### The library around it

Two hulls exist in Mathlib. The hull `convexHull 𝕜 s` of Volume 16 lives in a module. The hull of this section, `Convexity.convexHull R`, lives in any convex space.

::: mathlib
`Convexity.convexHull` · `Mathlib.Geometry.Convex.Hull`

`Convexity.convexHull R : ClosureOperator (Set X)`. `mem_convexHull_iff` and `convexHull_eq_iInter` give the description from outside, and `convexHull_min` the minimality. The rules of this section are `convexHull_convexHull_union` and `IsAffineMap.image_convexHull`, and the lemma on removing a point is `IsConvexSet.sdiff_singleton_iff_notMem_convexHull`.

<?decl Convexity.mem_convexHull_iff?>
:::

::: mathlib
`Set.convexHull_eq_range_iConvexComb` · `Mathlib.Analysis.Convex.StdSimplex`

In a module over a linearly ordered field with `IsModuleConvexSpace`, the hull of Volume 16 is the range of `StdSimplex.affineMapMk` applied to the inclusion of `s`. `ConvexSpace.AffineMap.convex_range` is the convexity of such a range.

<?decl Set.convexHull_eq_range_iConvexComb?>
:::

The older standard simplex of that file, a set of functions, is deprecated in favour of the type `Convexity.StdSimplex`.

::: mathlib
`Convexity.StdSimplex.barycenter` · `Mathlib.Geometry.Convex.ConvexSpace.Barycenter`

`StdSimplex.barycenter` for a nonempty finite type, with `weights_barycenter_apply` giving the weight $1/|M|$. `StdSimplex.subBarycenter S hS` is the barycenter $b_S$ of a nonempty `Finset`.

<?decl Convexity.StdSimplex.barycenter?>
:::

::: mathlib
`Convexity.StdSimplex.compactSpace` · `Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex`

The instance `CompactSpace (StdSimplex R M)` for finite `M` and a ring `R` with compact closed intervals. The instance `StdSimplex.pathConnectedSpace` gives path-connectedness over `ℝ`, and `StdSimplex.homeomorphI` identifies the simplex on `Fin 2` with the unit interval.

<?decl Convexity.StdSimplex.compactSpace?>
:::

::: mathlib
`ConvexIndependent` · `Mathlib.Analysis.Convex.Independent`

`ConvexIndependent 𝕜 p` for a family `p : ι → E`. `convexIndependent_set_iff_notMem_convexHull_sdiff` states it for a set: no point lies in the hull of the others. `convexIndependent_iff_finset` restricts to finite sets of indices, with the theorem of Caratheodory of Section 2.

<?decl convexIndependent_set_iff_notMem_convexHull_sdiff?>
:::

The source of `Mathlib.Analysis.Convex.Independent` lists the theorem that affine independence implies convex independence as a TODO, and the index of this edition has no declaration for it.

### Exercises

1. (A) Find the barycentric coordinates of $(2, 1)$ with respect to the triangle with vertices $(0,0)$, $(4,0)$, $(0,4)$.
2. (A) Show that $\mathrm{conv}\{x, y\} = [x, y]$ in any convex space.
3. (B) Show that $\mathrm{conv}(A + B) = \mathrm{conv}(A) + \mathrm{conv}(B)$ for subsets of a real vector space. Hint: use the rule for affine images with the map $(a, b) \mapsto a + b$ and the product of hulls.
4. (B) Show that the points of the parabola $\{(t, t^2) : t \in \mathbb{R}\}$ are convex independent.
5. (B) Show that the convex hull of a finite set in $\mathbb{R}^n$ is compact. Hint: it is the image of a standard simplex under a continuous map.
6. (C) Let $p_1, \dots, p_n$ be points of a real vector space. Show that the map $\Delta_{n-1} \to E$, $w \mapsto \sum w_i p_i$, is injective if and only if the points are affinely independent.

### Notes and history

The convex hull and barycentric coordinates go back to Mobius, who introduced barycentric coordinates in 1827. The Mathlib file on hulls in convex spaces names Yaël Dillies as its author. The file on the standard simplex names Alexander Bentkamp, Yury Kudryashov, Yaël Dillies and Joël Riou, and the file on convex independence names Yaël Dillies and Bhavik Mehta.

### Reference

<?reference?>
