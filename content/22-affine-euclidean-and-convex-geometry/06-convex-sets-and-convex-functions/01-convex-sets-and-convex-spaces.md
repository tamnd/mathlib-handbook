---
title: Convex sets and convex spaces
kind: theory
modules:
  - Mathlib.Geometry.Convex.ConvexSpace.Defs
  - Mathlib.Geometry.Convex.ConvexSpace.Module
  - Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
  - Mathlib.Geometry.Convex.ConvexSpace.Prod
  - Mathlib.LinearAlgebra.ConvexSpace
  - Mathlib.LinearAlgebra.ConvexSpace.AffineSpace
  - Mathlib.Geometry.Convex.Set
  - Mathlib.Geometry.Convex.Segment
  - Mathlib.Geometry.Convex.Star
  - Mathlib.Analysis.Convex.Visible
explains:
  E3: [Convexity.ConvexSpace, Convexity.StdSimplex, Convexity.IsConvexSet, Convexity.IsConvexSet.of_convexCombPair_mem, Convexity.IsStarConvexSet, Convexity.IsAffineMap, IsVisible, IsClosed.exists_wbtw_isVisible]
  E2: [Convexity.convexCombPair, Convexity.ConvexSpace.assoc, Convexity.ConvexSpace.sConvexComb_single, Convexity.StdSimplex.single, Convexity.IsConvexSet.sInter, Convexity.IsConvexSet.sUnion, Convexity.IsConvexSet.preimage, Convexity.IsConvexSet.image, Convexity.IsStarConvexSet.union, Convexity.ConvexSpace.ofModule, Convexity.ConvexSpace.ofAddTorsor, AffineMap.isAffineMap]
  E1: auto
families: []
requires: [V07, V13, V16.C05, V22.C01, V22.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Convex sets and convex spaces

### Overview

Volume 16, Chapter 5 defines a convex set in a real vector space. This section asks what structure a set needs so that "a convex combination of points" makes sense. The answer is a *convex space*: a set with an operation that sends each finite probability distribution on the set to a point, subject to two axioms. Vector spaces and affine spaces are convex spaces, and so are semilattices.

### Definitions

Fix an ordered semiring $R$, for example $\mathbb{R}$ or $\mathbb{Q}$.

**Definition (finitely supported probability distribution).** A *finitely supported probability distribution* on a set $X$ is a function $w : X \to R$ with finite support, $w \ge 0$ and $\sum_x w(x) = 1$. The set of these is $\Delta_R(X)$. The *point mass* $\delta_x$ has weight $1$ at $x$. A map $g : X \to Y$ pushes $w$ forward to $g_*w$, with $(g_*w)(y) = \sum_{g(x) = y} w(x)$. A distribution $F$ on $\Delta_R(X)$ *flattens* to $\mu(F) \in \Delta_R(X)$, with $\mu(F)(x) = \sum_{v} F(v)\, v(x)$.

**Definition (convex space).** A *convex space* over $R$ is a set $X$ with a map $c : \Delta_R(X) \to X$ such that

1. $c(\delta_x) = x$ for each $x \in X$, and
2. $c(c_* F) = c(\mu(F))$ for each $F \in \Delta_R(\Delta_R(X))$.

So a convex space is an algebra for the monad $\Delta_R$. For $s, t \ge 0$ with $s + t = 1$ write $s x + t y$ for $c(s\delta_x + t\delta_y)$, even when $X$ has no addition.

**Definition (convex set, segment, star-convex set).** A subset $S$ of a convex space $X$ is *convex* if $c(w) \in S$ for each $w$ whose support lies in $S$. The *segment* $[x, y]$ is the set of the points $s x + t y$. A set $S$ is *star-convex at* $x$ if $[x, y] \subseteq S$ for each $y \in S$.

**Definition (affine map).** A map $f : X \to Y$ of convex spaces is *affine* if $f(c(w)) = c(f_* w)$ for each $w$.

**Definition (visibility).** Let $S$ be a subset of an affine space over an ordered field. The point $y$ is *visible from* $x$ *through* $S$ if no $z \in S$ lies strictly between $x$ and $y$, in the sense of $\mathrm{Sbtw}$ of Chapter 2.

### Theorems and proofs

**Lemma (splitting a combination).** Let $X$ be a convex space over an ordered field $K$. Let $w \in \Delta_K(X)$, let $x_0$ be in the support of $w$ with $a = w(x_0) < 1$, and let $w'$ have $w'(x_0) = 0$ and $w'(x) = w(x)/(1-a)$ for $x \ne x_0$. Then $c(w) = a x_0 + (1-a) c(w')$.

*Proof.* Let $F = a\,\delta_{\delta_{x_0}} + (1-a)\,\delta_{w'}$. Its flattening is $a\,\delta_{x_0} + (1-a) w' = w$. The push-forward $c_*F$ has weight $a$ at $c(\delta_{x_0}) = x_0$ and weight $1 - a$ at $c(w')$. Axiom 2 gives $a x_0 + (1-a) c(w') = c(c_*F) = c(\mu(F)) = c(w)$. $\square$

**Theorem (binary combinations suffice).** Over an ordered field, $S \subseteq X$ is convex if and only if $s x + t y \in S$ for all $x, y \in S$ and all $s, t \ge 0$ with $s + t = 1$.

*Proof.* One direction is the definition applied to $s\delta_x + t\delta_y$. Conversely, induct on the number $n$ of points in the support of $w$. If $n = 1$, then $w = \delta_x$ and $c(w) = x \in S$. If $n \ge 2$, pick $x_0$ in the support, so $a = w(x_0) < 1$. The support of $w'$ has $n - 1$ points of $S$, so $c(w') \in S$, and the lemma writes $c(w)$ as a binary combination of $x_0$ and $c(w')$. $\square$

**Theorem (stability of convexity).** Let $f : X \to Y$ be affine.

1. Each intersection of convex sets is convex.
2. The union of a directed family of convex sets is convex.
3. Images and preimages of convex sets under $f$ are convex.

*Proof.* (1) If the support of $w$ lies in each $S_i$, then $c(w) \in S_i$ for each $i$. (2) The support of $w$ is finite, so it lies in one member $S_j$. (3) Let $v$ have support in $f(S)$. Pick $x_y \in S$ with $f(x_y) = y$ for each $y$ in the support, and let $w$ put weight $v(y)$ on $x_y$. Then $c(v) = c(f_*w) = f(c(w)) \in f(S)$. If $w$ has support in $f^{-1}(T)$, then $f(c(w)) = c(f_*w) \in T$. $\square$

A convex set is star-convex at each of its points, and a union of sets that are star-convex at $x$ is star-convex at $x$. Both follow from the definitions.

**Theorem (a visible point on each segment).** Let $V$ be a real topological vector space, $S \subseteq V$ closed, $y \in S$ and $x \in V$. Then some $z \in S \cap [x, y]$ is visible from $x$ through $S$.

*Proof.* Let $\ell(t) = x + t(y - x)$. The set $A = [0,1] \cap \ell^{-1}(S)$ is closed in $[0,1]$ and contains $1$, so it has a least element $t_0$. Put $z = \ell(t_0)$. If $z = x$, nothing lies strictly between $x$ and $x$. Otherwise a point $u \in S$ strictly between $x$ and $z$ is $\ell(r t_0)$ with $0 < r < 1$, so $r t_0 \in A$, against the choice of $t_0$. $\square$

### Examples

**Example (a combination in the plane).** In $\mathbb{R}^2$ take the weights $1/2$, $1/4$, $1/4$ at $p = (0,0)$, $q = (4,0)$ and $r = (0,4)$. The lemma with $x_0 = p$ gives $w'$ with weights $1/2$ at $q$ and $r$, so $c(w') = (2, 2)$ and $c(w) = \tfrac12 (0,0) + \tfrac12 (2,2) = (1,1)$, as the direct sum gives.

**Example (a convex space that is not a vector space).** Let $X = \{0, 1\}$ and let $c(w)$ be the largest point of the support of $w$. Axiom 1 is clear. For axiom 2, the support of $\mu(F)$ is the union of the supports of the $v$ with $F(v) > 0$, so its largest point is the largest $c(v)$, which is $c(c_*F)$. Here $\tfrac12 \cdot 0 + \tfrac12 \cdot 1 = \tfrac12 \cdot 1 + \tfrac12 \cdot 1$. In a vector space this would force $0 = 1$, so no injective affine map sends $X$ into a vector space.

**Counterexample (star-convex but not convex).** The union $S$ of the two coordinate axes in $\mathbb{R}^2$ is star-convex at $0$. But $\tfrac12 (1,0) + \tfrac12 (0,1) \notin S$. So the stability theorem needs directedness for unions.

### The library around it

The predicate `Convex` of Volume 16 lives in a module. The theory in `Mathlib.Geometry.Convex` works in any convex space.

::: mathlib
`Convexity.StdSimplex` · `Mathlib.Geometry.Convex.ConvexSpace.Defs`

`StdSimplex R X` is $\Delta_R(X)$, with a field `weights : X →₀ R`. `StdSimplex.single` is the point mass.

<?decl Convexity.StdSimplex?>
:::

::: mathlib
`Convexity.ConvexSpace` · `Mathlib.Geometry.Convex.ConvexSpace.Defs`

The class holds `sConvexComb : StdSimplex R X → X` and the axioms `ConvexSpace.sConvexComb_single` and `ConvexSpace.assoc`. `convexCombPair` is the binary combination. A module is not an instance: `Convexity.ConvexSpace.ofModule` and `Convexity.ConvexSpace.ofAddTorsor` build the structures.

<?decl Convexity.ConvexSpace?>
:::

::: mathlib
`Convexity.IsConvexSet` · `Mathlib.Geometry.Convex.Set`

`IsConvexSet.of_convexCombPair_mem` reduces convexity to binary combinations. The stability results are `IsConvexSet.sInter`, `IsConvexSet.sUnion` (with a `DirectedOn` hypothesis), `IsConvexSet.image` and `IsConvexSet.preimage`.

<?decl Convexity.IsConvexSet.of_convexCombPair_mem?>
:::

The predicate `IsStarConvexSet R x s` has the union rule `IsStarConvexSet.union`.

<?decl Convexity.IsStarConvexSet?>

::: mathlib
`Convexity.IsAffineMap` · `Mathlib.Geometry.Convex.ConvexSpace.Defs`

A structure with one field, `map_sConvexComb`. `AffineMap.isAffineMap` makes the affine maps of Chapter 1 affine. The converse is a TODO in the source.

<?decl Convexity.IsAffineMap?>
:::

The module `Mathlib.Geometry.Convex.ConvexSpace.Prod` gives the convex space structures on products. The instances are `Prod.instConvexSpace` on $X \times Y$, `Pi.instConvexSpaceForall` on $\prod_i X_i$ and `Finsupp.instConvexSpace` on `ι →₀ X`. In each case a combination is computed in each coordinate. The simp lemmas say this for each form of combination: `Prod.fst_convexCombPair`, `Prod.fst_iConvexComb` and `Prod.fst_sConvexComb` for the first coordinate, the `snd` forms for the second coordinate, and `Pi.convexCombPair_apply`, `Pi.iConvexComb_apply` and `Finsupp.convexCombPair_apply` for the other two products. The projections are affine (`Prod.isAffineMap_fst`, `Prod.isAffineMap_snd`, `Pi.isAffineMap_eval`, `Finsupp.isAffineMap_eval`). A map into a product is affine if and only if each coordinate is affine: this is `Convexity.isAffineMap_prod_iff`, `Convexity.isAffineMap_pi_iff` and `Convexity.isAffineMap_finsupp_iff`, and `Convexity.IsAffineMap.prodMk` builds the pair map $x \mapsto (f(x), g(x))$.

::: mathlib
`IsVisible` · `Mathlib.Analysis.Convex.Visible`

`IsVisible 𝕜 s x y` says that no `z ∈ s` satisfies `Sbtw 𝕜 x z y`. The theorem of this section is `IsClosed.exists_wbtw_isVisible`.

<?decl IsClosed.exists_wbtw_isVisible?>
:::

### Exercises

1. (A) In $\mathbb{R}^3$ compute $c(w)$ for the weights $1/3$, $1/3$, $1/6$, $1/6$ at $e_1$, $e_2$, $e_3$, $0$, directly and by the splitting lemma.
2. (A) Show that the open segment $]x, y[$ in a real vector space is convex.
3. (B) Find all points at which $\{(u,v) : u \le 0 \text{ or } v \le 0\}$ is star-convex.
4. (B) Show that every subset of the convex space $\{0, 1\}$ of the examples is convex.
5. (C) Let $L$ be a join-semilattice. Show that $c(w) = \bigvee \mathrm{supp}(w)$ makes $L$ a convex space. Hint: follow the example.
6. (C) Show that the theorem on visible points fails for some set that is not closed. Hint: an open disc.

### Notes and history

Axioms for abstract convex combinations go back to M. H. Stone's postulates for the barycentric calculus (1949). The Mathlib files on convex spaces name Kim Morrison, Andrew Yang and Yaël Dillies as authors, and the files on convex sets, segments, star-convex sets and visibility name Yaël Dillies.

### Reference

<?reference?>
