---
title: Examples, interior and boundary
kind: theory
modules:
  - Mathlib.Geometry.Manifold.Instances.Real
  - Mathlib.Geometry.Manifold.Instances.Icc
  - Mathlib.Geometry.Manifold.Instances.Sphere
  - Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
  - Mathlib.Geometry.Manifold.Instances.Quotient
  - Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
  - Mathlib.Geometry.Manifold.Complex
  - Mathlib.Geometry.Manifold.Metrizable
explains:
  E3: [ModelWithCorners.IsInteriorPoint, ModelWithCorners.boundary, modelWithCornersEuclideanHalfSpace, ModelWithCorners.isInteriorPoint_iff_of_mem_atlas]
  E2: [EuclideanHalfSpace, EuclideanQuadrant, modelWithCornersEuclideanQuadrant, range_modelWithCornersEuclideanHalfSpace, interior_range_modelWithCornersEuclideanHalfSpace, frontier_range_modelWithCornersEuclideanHalfSpace, modelWithCornersEuclideanHalfSpace_symm_apply, range_modelWithCornersEuclideanQuadrant, interior_range_modelWithCornersEuclideanQuadrant, IccLeftChart, IccRightChart, instIccChartedSpace, instIsManifoldIcc, boundary_Icc, Icc_isBoundaryPoint_bot, Icc_isInteriorPoint_interior, stereographic, stereographic', EuclideanSpace.instIsManifoldSphere, Units.instChartedSpace, Units.instIsManifoldModelWithCornersSelf, Units.contMDiff_val, MulAction.instChartedSpaceQuotient, ModelWithCorners.IsBoundaryPoint, ModelWithCorners.interior, ModelWithCorners.isInteriorPoint_iff, ModelWithCorners.isInteriorPoint_or_isBoundaryPoint, ModelWithCorners.compl_interior, ModelWithCorners.mem_interior_range_of_mem_interior_range_of_mem_atlas, ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas, ModelWithCorners.isOpen_interior, ModelWithCorners.isClosed_boundary, DifferentiableAt.mem_interior_convex_of_surjective_fderiv, BoundarylessManifold, ModelWithCorners.instBoundarylessManifold, ModelWithCorners.Boundaryless.iff_boundary_eq_empty, ModelWithCorners.interior_prod, ModelWithCorners.boundary_prod, MDifferentiable.exists_eq_const_of_compactSpace, MDifferentiable.apply_eq_of_compactSpace, Manifold.metrizableSpace]
  E1: auto
families: []
requires: [V23.C01, V16.C01, V16.C05, V17.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Examples, interior and boundary

### Overview

This section gives the half space and the quadrant, the models of manifolds with boundary and with corners, and the standard examples of Mathlib: the interval, the sphere, the units of a Banach algebra and quotients. It then defines interior and boundary points. A point is interior when its preferred extended chart sends it into the interior of the range of the model. The main theorem says that on a $C^1$ manifold the choice of the chart does not change this. The proof uses the theorem of Hahn and Banach and the vanishing of a derivative at a local maximum.

### Definitions

Write $\mathbb{R}^n$ for the Euclidean space of dimension $n$, with coordinates $y_0, \dots, y_{n-1}$.

**Definition (Half space and quadrant).** For $n \ge 1$, the *half space* is $H^n = \{y \in \mathbb{R}^n : y_0 \ge 0\}$, with the induced topology. The *quadrant* is $Q^n = \{y : y_i \ge 0 \text{ for all } i\}$. The model $\mathcal{R}\partial^n : H^n \to \mathbb{R}^n$ is the inclusion, with inverse the map that replaces $y_0$ by $\max(y_0, 0)$. The model of $Q^n$ is the inclusion, with inverse that replaces each $y_i$ by $\max(y_i, 0)$. The model $\mathcal{R}^n$ is the trivial model of $\mathbb{R}^n$.

These are models with corners: the inverses are continuous, and the ranges are closed and convex with nonempty interior.

::: mathlib
`modelWithCornersEuclideanHalfSpace` · `Mathlib.Geometry.Manifold.Instances.Real`

`EuclideanHalfSpace n` needs `[NeZero n]` and is a subtype of `EuclideanSpace ℝ (Fin n)`. The model is `modelWithCornersEuclideanHalfSpace n`, with notation `𝓡∂ n` in the scope `Manifold`, and `𝓡 n` is `𝓘(ℝ, EuclideanSpace ℝ (Fin n))`. The quadrant is `EuclideanQuadrant n` with model `modelWithCornersEuclideanQuadrant n`.

<?decl modelWithCornersEuclideanHalfSpace?>
<?decl EuclideanHalfSpace?>
<?decl modelWithCornersEuclideanQuadrant?>
:::

**Definition (Interior and boundary points).** Let $I : H \to E$ be a model and $M$ a charted space over $H$. A point $x \in M$ is an *interior point* if $\hat\varphi_x(x)$ lies in the interior of $\hat\varphi_x.\mathrm{target}$. Otherwise it is a *boundary point*. The *interior* of $M$ is the set of interior points, and the *boundary* $\partial M$ is the set of boundary points.

The target is the intersection of $\mathrm{range}\, I$ with an open set that contains $\hat\varphi_x(x)$, so $x$ is interior exactly when $\hat\varphi_x(x) \in \mathrm{int}(\mathrm{range}\, I)$.

**Definition (Manifold without boundary).** $M$ is *boundaryless* for $I$ if every point of $M$ is an interior point.

::: mathlib
`ModelWithCorners.IsInteriorPoint` · `Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary`

`I.IsInteriorPoint x` and `I.IsBoundaryPoint x` are the predicates, and `I.interior M` and `I.boundary M` the sets, with `M` explicit. The definition unfolds by `isInteriorPoint_iff`. Every point is in exactly one of the two (`isInteriorPoint_or_isBoundaryPoint`, `compl_interior`). The class `BoundarylessManifold I M` is a property of the manifold. It differs from the class `I.Boundaryless` of Section 1, a property of the model, and the instance `ModelWithCorners.instBoundarylessManifold` derives the first from the second. The lemma `Boundaryless.iff_boundary_eq_empty` gives the characterisation by the boundary.

<?decl ModelWithCorners.IsInteriorPoint?>
<?decl ModelWithCorners.boundary?>
<?decl BoundarylessManifold?>
:::

### Theorems and proofs

**Theorem (The half space).** The range of $\mathcal{R}\partial^n$ is $\{y_0 \ge 0\}$, its interior is $\{y_0 > 0\}$ and its frontier is $\{y_0 = 0\}$.

*Proof.* The model is the inclusion of $H^n$, so its range is $\{y_0 \ge 0\}$. The set $U = \{y_0 > 0\}$ is the preimage of an open set under the continuous map $y \mapsto y_0$, so it is open, and it lies in the range. So $U$ lies in the interior. Conversely, let $y$ be in the range with $y_0 = 0$, and let $e_0$ be the first basis vector. For every $\varepsilon > 0$, the point $y - \varepsilon e_0$ is at distance $\varepsilon$ from $y$ and is not in the range. So $y$ is not in the interior. The range is closed, so the frontier is the range minus the interior, $\{y_0 = 0\}$. $\square$

**Lemma (A surjective derivative into a convex set).** Let $E, F$ be real normed spaces, and let $s \subseteq F$ be closed and convex with nonempty interior. Let $f : E \to F$ be differentiable at $z$, and let $u$ be a neighbourhood of $z$ with $f(u) \subseteq s$. If $Df(z)$ is surjective, then $f(z) \in \mathrm{int}\, s$.

*Proof.* Assume $f(z) \notin \mathrm{int}\, s$. The interior of a convex set is convex, and it is open. By the geometric form of the theorem of Hahn and Banach (Volume 16, Chapter 5), there is a continuous linear form $\lambda$ on $F$ with $\lambda(a) < \lambda(f(z))$ for all $a \in \mathrm{int}\, s$. A closed convex set with nonempty interior is the closure of its interior, so by continuity $\lambda(a) \le \lambda(f(z))$ for all $a \in s$. Since $f(u) \subseteq s$, the function $\lambda \circ f$ has a local maximum at $z$. It is differentiable at $z$, so its derivative $\lambda \circ Df(z)$ is zero. Now take $a \in \mathrm{int}\, s$. Since $Df(z)$ is surjective, there is $v$ with $Df(z)v = f(z) - a$. Then $0 = \lambda(Df(z)v) = \lambda(f(z)) - \lambda(a) > 0$, a contradiction. $\square$

**Theorem (Interior points do not depend on the chart).** Let $M$ be a $C^n$ manifold with $n \ge 1$, let $e$ be a chart in the atlas and let $x \in e.\mathrm{source}$. Then $x$ is an interior point if and only if $e_I(x) \in \mathrm{int}(e_I.\mathrm{target})$.

*Proof.* It suffices to show: for charts $e, e'$ in the atlas with $x$ in both sources, $e_I(x) \in \mathrm{int}(e_I.\mathrm{target})$ implies $e'_I(x) \in \mathrm{int}(e'_I.\mathrm{target})$. The theorem follows with $\varphi_x$ as $e$ or as $e'$. If $\mathbb{K}$ is not $\mathbb{R}$ or $\mathbb{C}$, then $\mathrm{range}\, I = E$ by Section 1, and every point is interior. So assume that $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, and regard $E$ as a real normed space.

Let $z = e_I(x)$ and $\Phi = \Phi_{e, e'}$, with source $S = e_I.\mathrm{target} \cap (e_I^{-1})^{-1}(e'.\mathrm{source})$. The set $(e_I^{-1})^{-1}(e'.\mathrm{source})$ is a neighbourhood of $z$ (Section 2, Exercise 4), and $e_I.\mathrm{target}$ is one by hypothesis. So $S$ is a neighbourhood of $z$. By Section 2, $\Phi$ is $C^n$ on $S$ with $n \ge 1$, so it is differentiable at $z$, and its derivative within $S$ is its derivative $D\Phi(z)$. By Section 2, this derivative is invertible, so it is surjective, also as a real linear map. The map $\Phi$ sends $S$ into $\mathrm{range}\, I$, which is closed and convex with nonempty interior. The lemma gives $e'_I(x) = \Phi(z) \in \mathrm{int}(\mathrm{range}\, I)$. Finally $e'_I.\mathrm{target} = (I^{-1})^{-1}(e'.\mathrm{target}) \cap \mathrm{range}\, I$. The first set is open and contains $e'_I(x)$, so its intersection with $\mathrm{int}(\mathrm{range}\, I)$ is an open subset of the target that contains $e'_I(x)$. $\square$

**Corollary (Interior and boundary).** On a $C^n$ manifold with $n \ge 1$, the interior is open and the boundary is closed. A point $x$ is a boundary point if and only if $e_I(x)$ is in the frontier of $e_I.\mathrm{target}$, for any chart $e$ of the atlas at $x$.

*Proof.* Let $x$ be an interior point. The set $V = \{y \in \varphi_x.\mathrm{source} : \hat\varphi_x(y) \in \mathrm{int}(\hat\varphi_x.\mathrm{target})\}$ is open, because $\hat\varphi_x$ is continuous on the open source. It contains $x$. By the theorem with $e = \varphi_x$, every point of $V$ is an interior point. So the interior is open, and the boundary, its complement, is closed. For the second claim, $e_I(x)$ lies in the target, so it is in the frontier of the target exactly when it is not in the interior, and the theorem applies. $\square$

**Theorem (The boundary of an interval).** Let $a < b$. The interval $[a, b]$ is a $C^\infty$ manifold with model $\mathcal{R}\partial^1$, with the charts $z \mapsto z - a$ on $[a, b)$ and $z \mapsto b - z$ on $(a, b]$. Its boundary is $\{a, b\}$.

*Proof.* The charts map $[a, b)$ and $(a, b]$ homeomorphically onto $[0, b - a)$, which is open in $H^1$. The change of charts on $(a, b)$ is $t \mapsto (b - a) - t$ on $(0, b - a)$, an affine map, so it is $C^\infty$. Apply the corollary. The first chart sends $a$ to $0$, in the frontier of $[0, b - a)$, and the second sends $b$ to $0$. So $a$ and $b$ are boundary points. A point $p$ with $a < p < b$ goes to $p - a \in (0, b - a)$, an interior point of the target. $\square$

::: mathlib
`ModelWithCorners.isInteriorPoint_iff_of_mem_atlas` · `Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary`

The theorem has the hypotheses `[IsManifold I n M]`, `n ≠ 0`, `e ∈ atlas H M` and `x ∈ e.source`. Its core `mem_interior_range_of_mem_interior_range_of_mem_atlas` follows the proof above. The corollaries are `isBoundaryPoint_iff_of_mem_atlas`, `isOpen_interior` and `isClosed_boundary`, all with `n ≠ 0`. The half space lemmas are `range_modelWithCornersEuclideanHalfSpace`, `interior_range_modelWithCornersEuclideanHalfSpace` and `frontier_range_modelWithCornersEuclideanHalfSpace`. The interval has the charts `IccLeftChart` and `IccRightChart`, and `boundary_Icc : boundary (Icc x y) = {⊥, ⊤}` under `[Fact (x < y)]`.

<?decl ModelWithCorners.isInteriorPoint_iff_of_mem_atlas?>
<?decl DifferentiableAt.mem_interior_convex_of_surjective_fderiv?>
<?decl ModelWithCorners.isOpen_interior?>
<?decl boundary_Icc?>
:::

### Examples

**Example (The sphere).** Let $E$ be a real inner product space of dimension $n + 1$ and $S$ its unit sphere. For a unit vector $v$, the stereographic projection from $v$ maps $S \setminus \{v\}$ onto the hyperplane $v^\perp$ by $x \mapsto \frac{2}{1 - \langle v, x \rangle}\, p(x)$, with $p$ the orthogonal projection onto $v^\perp$. After an isometry $v^\perp \cong \mathbb{R}^n$, the projections from $v$ and $-v$ cover $S$, and the changes of charts are analytic. Mathlib uses the projection from $-x$ as the chart at $x$, and `EuclideanSpace.instIsManifoldSphere` gives an analytic manifold with model $\mathcal{R}^n$.

**Example (Units of a Banach algebra).** Let $R$ be a complete normed ring. The units $R^\times$ form an open subset of $R$, and the inclusion $R^\times \to R$ is a single chart with source $R^\times$ (`Units.chartAt_source`). The changes of charts are identities, so $R^\times$ is a manifold with the trivial model of $R$ for every $n$ (`Units.instIsManifoldModelWithCornersSelf`).

**Example (Quotients).** If a group $G$ acts on a charted space $M$ freely, properly discontinuously and continuously, and $M$ is Hausdorff and locally compact, the quotient map is a covering map. So it is a local homeomorphism, and the charts of $M$ give charts of the quotient (`MulAction.instChartedSpaceQuotient`). The index of this edition has no declaration for the manifold structure of the quotient of a smooth action.

**Example (Products).** The boundary of $M \times N$ is $(\partial M \times N) \cup (M \times \partial N)$ (`boundary_prod`), and the interior is the product of the interiors (`interior_prod`).

**Example (A boundaryless manifold with a boundary model).** The open half space $\{y_0 > 0\}$ is an open subset of $H^n$ and a manifold with model $\mathcal{R}\partial^n$. It is a `BoundarylessManifold`, but the model is not `Boundaryless`.

### The library around it

The module `Mathlib.Geometry.Manifold.Complex` proves the maximum modulus principle on complex manifolds. Its main result says that a holomorphic function $f : M \to F$ on a compact connected complex manifold without boundary is constant (`MDifferentiable.exists_eq_const_of_compactSpace`). The proof replaces $f$ by $f - f(b)$ and uses the maximum modulus principle in charts to show that $\|f\|$ is constant. The module `Mathlib.Geometry.Manifold.Metrizable` proves that a $\sigma$-compact Hausdorff manifold with a finite dimensional real model is metrizable (`Manifold.metrizableSpace`). The proof shows that the manifold is locally compact, so regular, and second countable, and applies the metrization theorem of Urysohn.

The module `Mathlib.Geometry.Manifold.Instances.Icc` proves that the inclusion of $[a, b]$ in $\mathbb{R}$ is smooth. Diffeomorphisms, defined in Chapter 3, preserve the boundary (`Diffeomorph.image_boundary`).

Common errors of a learner:

- Confusing `I.Boundaryless`, a property of the model, with `BoundarylessManifold I M`, a property of `M`.
- Using `isInteriorPoint_iff_of_mem_atlas` on a $C^0$ manifold. The hypothesis `n ≠ 0` is needed, and for topological manifolds the library has no chart independence.
- Writing `𝓡∂ 0`. The half space needs `NeZero n`.

### Exercises

1. (A) Prove that the interior of the quadrant $Q^n$ is $\{y : y_i > 0 \text{ for all } i\}$.
2. (A) Show that the change of charts of the two charts of $[a, b]$ is $t \mapsto (b - a) - t$, and compute the source.
3. (A) Show that the boundary of a manifold whose model is boundaryless is empty.
4. (B) Prove the step of the lemma that a closed convex set with nonempty interior is the closure of its interior. Hint: for $a$ in the set and $c$ in the interior, the points $c + t(a - c)$ with $t < 1$ are in the interior.
5. (B) Show that the boundary of $[0, 1]^2$ for the model $\mathcal{R}\partial^1 \times \mathcal{R}\partial^1$ is the union of the four edges. Hint: use the theorem on products and the boundary of an interval.
6. (B) Compute the stereographic projection of the circle from $(0, 1)$ and from $(0, -1)$, and the change of charts.
7. (C) Show that the half space $H^1$ and the line $\mathbb{R}$ are not diffeomorphic as $C^1$ manifolds, with the boundary.
8. (C) Show that if $M$ is a $C^1$ manifold with model $\mathcal{R}\partial^n$, then $\partial M$ with the restrictions of the charts is a charted space over $\mathbb{R}^{n-1}$, for $n \ge 2$.

### Notes and history

Manifolds with boundary appear in the work on Stokes' theorem in the first half of the twentieth century, and manifolds with corners in the work of Cerf and Douady. For topological manifolds the result is the invariance of domain of Brouwer, from 1912, and the docstring of the Mathlib theorem leaves the infinite dimensional topological case open. The stereographic projection is classical.

### Reference

<?reference?>
