---
title: Models with corners
kind: theory
modules:
  - Mathlib.Geometry.Manifold.IsManifold.Basic
explains:
  E3: [ModelWithCorners, contDiffGroupoid, IsManifold]
  E2: [modelWithCornersSelf, ModelWithCorners.Boundaryless, ModelWithCorners.prod, ModelWithCorners.range_prod, ModelWithCorners.isClosedEmbedding, ModelWithCorners.range_eq_closure_interior, ModelWithCorners.uniqueDiffOn, ModelWithCorners.convex_range, ModelWithCorners.map_nhds_eq, ModelWithCorners.ofConvexRange, ModelWithCorners.toHomeomorph, contDiffPregroupoid, contDiffGroupoid_le, contDiffGroupoid_zero_eq, contDiffGroupoid_prod, isManifold_of_contDiffOn, IsManifold.mk', IsManifold.of_le, instIsManifoldModelSpace, IsManifold.prod, TopologicalSpace.Opens.instIsManifoldSubtypeMem, IsManifold.maximalAtlas, TangentSpace]
  E1: auto
families: []
requires: [V23.C01, V16.C01, V17.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Models with corners

### Overview

To differentiate a change of charts, its domain must sit in a normed space. A model with corners is an embedding $I$ of the model space $H$ into a normed space $E$, and a change of charts $e$ of $H$ is read as the map $I \circ e \circ I^{-1}$ between subsets of $E$. For a manifold without boundary, $H = E$ and $I = \mathrm{id}$. For a manifold with boundary, $H$ is a half space and $I$ its inclusion. The image of $I$ need not be open, so the derivatives are derivatives within a set, and the set must determine them. Convexity and a nonempty interior ensure this.

This section defines models with corners and the groupoid of $C^n$ maps of a model, and with it the class of $C^n$ manifolds. The order $n$ runs over $\mathbb{N} \cup \{\infty, \omega\}$, so that one class covers topological ($n = 0$), $C^k$, smooth ($n = \infty$) and analytic ($n = \omega$) manifolds.

### Definitions

Let $\mathbb{K}$ be a nontrivially normed field, $E$ a normed space over $\mathbb{K}$, and $H$ a topological space.

**Definition (Model with corners).** A *model with corners* is a map $I : H \to E$ with a map $I^{-1} : E \to H$ such that:

1. $I^{-1}(I(x)) = x$ for every $x \in H$, and $I(I^{-1}(y)) = y$ for $y$ in the range of $I$;
2. $I$ and $I^{-1}$ are continuous;
3. the range of $I$ has nonempty interior;
4. if $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, the range of $I$ is convex over $\mathbb{R}$; otherwise the range of $I$ is $E$.

The model is *boundaryless* if its range is $E$. Then $I$ is a homeomorphism from $H$ to $E$.

Condition 2 asks that $I^{-1}$ be continuous on all of $E$, not only on the range. For a half space this holds with the map that replaces the first coordinate $y_0$ by $\max(y_0, 0)$. The *trivial model* of $E$ is $I = \mathrm{id}_E$. The *product* of models $I : H \to E$ and $I' : H' \to E'$ is $I \times I' : H \times H' \to E \times E'$, with range $\mathrm{range}\, I \times \mathrm{range}\, I'$.

::: mathlib
`ModelWithCorners` · `Mathlib.Geometry.Manifold.IsManifold.Basic`

`ModelWithCorners 𝕜 E H` extends `PartialEquiv H E` with the fields `source_eq : source = univ`, `convex_range'`, `nonempty_interior'`, `continuous_toFun` and `continuous_invFun`. The field `convex_range'` is an `if`: when `IsRCLikeNormedField 𝕜` holds the range is convex over `ℝ`, and otherwise it is `univ`. Over `ℝ` the constructor `ModelWithCorners.ofConvexRange` avoids the `if`. The trivial model is `modelWithCornersSelf 𝕜 E`, with the notation `𝓘(𝕜, E)` in the scope `Manifold`. The product is `ModelWithCorners.prod`, a model on `ModelProd H H'`, with `ModelWithCorners.range_prod`. `ModelWithCorners.Boundaryless I` is a class with the field `range_eq_univ`, and under it `I.toHomeomorph : H ≃ₜ E`.

<?decl ModelWithCorners?>
<?decl modelWithCornersSelf?>
<?decl ModelWithCorners.prod?>
<?decl ModelWithCorners.Boundaryless?>
:::

**Definition (Groupoid of $C^n$ maps).** Let $I$ be a model with corners and $n \in \mathbb{N} \cup \{\infty, \omega\}$. For a map $f : H \to H$ and an open set $u \subseteq H$, let $P_n(f, u)$ say that $I \circ f \circ I^{-1}$ is $C^n$ on $I^{-1}(u) \cap \mathrm{range}\, I$. The *groupoid of $C^n$ maps* $G_n(I)$ is the groupoid of the pregroupoid $P_n$.

So $e \in G_n(I)$ when $e$ is $C^n$ on its source and $e^{-1}$ is $C^n$ on its target, both read in $E$. The set $I^{-1}(u) \cap \mathrm{range}\, I$ is $I(u)$, since $I$ is a bijection onto its range.

**Definition ($C^n$ manifold).** A charted space $M$ over $H$ is a *$C^n$ manifold* with model $I$ if it has the groupoid $G_n(I)$: every change of charts $e^{-1} \gg e'$ of the atlas is in $G_n(I)$.

::: mathlib
`IsManifold` · `Mathlib.Geometry.Manifold.IsManifold.Basic`

`contDiffPregroupoid n I` has the property `ContDiffOn 𝕜 n (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)`, and `contDiffGroupoid n I` is its groupoid. `IsManifold I n M` is a class in `Prop` that extends `HasGroupoid M (contDiffGroupoid n I)`, with `n : WithTop ℕ∞`, written `ℕ∞ω`. It assumes no separation and no countability. `isManifold_of_contDiffOn` builds an instance from the smoothness of the changes of charts, and `IsManifold.mk'` from a `HasGroupoid` instance. The set `IsManifold.maximalAtlas I n M` is the maximal atlas of Chapter 1 for this groupoid.

<?decl contDiffGroupoid?>
<?decl contDiffPregroupoid?>
<?decl IsManifold?>
<?decl isManifold_of_contDiffOn?>
:::

### Theorems and proofs

**Theorem (A model is a closed embedding).** Let $I$ be a model with corners. Then $I$ is a homeomorphism from $H$ onto its range, and the range is closed in $E$.

*Proof.* The map $I$ is continuous and injective, and its inverse on the range is the restriction of the continuous map $I^{-1}$. So $I$ is a homeomorphism onto its range. For $y \in E$, condition 1 gives: $y \in \mathrm{range}\, I$ if and only if $I(I^{-1}(y)) = y$. The set of $y$ where the two continuous maps $I \circ I^{-1}$ and $\mathrm{id}_E$ agree is closed, since $E$ is Hausdorff. $\square$

So the neighbourhoods of $I(x)$ in the range are the images of the neighbourhoods of $x$: $I$ maps the filter $\mathcal{N}(x)$ to $\mathcal{N}_{\mathrm{range}\, I}(I(x))$.

**Theorem (The range is the closure of its interior).** Let $I$ be a model with corners. Then $\mathrm{range}\, I = \overline{\mathrm{int}(\mathrm{range}\, I)}$.

*Proof.* Write $C = \mathrm{range}\, I$. Since $C$ is closed, $\overline{\mathrm{int}\, C} \subseteq C$. If $\mathbb{K}$ is not $\mathbb{R}$ or $\mathbb{C}$, then $C = E$ and the claim is clear. Otherwise $C$ is convex over $\mathbb{R}$. Choose $y \in \mathrm{int}\, C$ and $r > 0$ with $B(y, r) \subseteq C$. Let $x \in C$ and $0 < t \le 1$. For $z \in B(y, r)$, the point $(1 - t)x + tz$ is in $C$ by convexity. These points form the ball $B((1 - t)x + ty, tr)$. So $(1 - t)x + ty \in \mathrm{int}\, C$. As $t \to 0$ these points tend to $x$, so $x \in \overline{\mathrm{int}\, C}$. $\square$

A consequence is that derivatives within $\mathrm{range}\, I$ are unique: a convex set with nonempty interior is a set of unique differentiability in the sense of Volume 17. So the derivative of a change of charts at a boundary point is well defined.

**Theorem ($C^n$ maps form a pregroupoid).** The property $P_n$ is a pregroupoid. So $G_n(I)$ is a structure groupoid.

*Proof.* Write $\hat f = I \circ f \circ I^{-1}$ and $\hat u = I^{-1}(u) \cap \mathrm{range}\, I$.

Composition. Let $P_n(f, u)$ and $P_n(g, v)$, and let $w = u \cap f^{-1}(v)$ be open. For $y \in \hat w$, $x = I^{-1}(y) \in w$, so $\hat f(y) = I(f(x))$ is in the range and $I^{-1}(\hat f(y)) = f(x) \in v$. So $\hat f$ maps $\hat w$ into $\hat v$. On $\hat w$, $\hat g \circ \hat f = I \circ g \circ I^{-1} \circ I \circ f \circ I^{-1} = \widehat{g \circ f}$, since $I^{-1} \circ I = \mathrm{id}$. Since $\hat w \subseteq \hat u$, the composition of $C^n$ maps of Volume 17 gives that $\widehat{g \circ f}$ is $C^n$ on $\hat w$.

Identity. $\widehat{\mathrm{id}} = I \circ I^{-1}$ is the identity on $\mathrm{range}\, I = \widehat{H}$, so it is $C^n$ there.

Locality. Let each $x \in u$ have an open $v \ni x$ with $P_n(f, u \cap v)$. The sets $\widehat{u \cap v} = \hat u \cap (I^{-1})^{-1}(v)$ are relatively open in $\hat u$ and cover it, since $I^{-1}$ is continuous. Being $C^n$ on a set is a local property within the set, so $\hat f$ is $C^n$ on $\hat u$.

Congruence. If $g = f$ on $u$, then $\hat g = \hat f$ on $\hat u$. $\square$

**Theorem (Order and the case $n = 0$).** If $m \le n$, then $G_n(I) \subseteq G_m(I)$. The groupoid $G_0(I)$ is the groupoid of all partial homeomorphisms of $H$.

*Proof.* A map that is $C^n$ on a set is $C^m$ on it. For the second claim, let $e$ be a partial homeomorphism of $H$. On $\widehat{e.\mathrm{source}}$, $\hat e$ is the composition of the continuous map $I^{-1}$, the map $e$ continuous on $e.\mathrm{source}$, and the continuous $I$. So $\hat e$ is continuous there, which is $C^0$. The same holds for $e^{-1}$. $\square$

So every $C^n$ manifold is a $C^m$ manifold for $m \le n$, and a $C^0$ manifold is a charted space with no further condition.

**Theorem (Products).** If $e \in G_n(I)$ and $e' \in G_n(I')$, then $e \times e' \in G_n(I \times I')$. If $M$ and $M'$ are $C^n$ manifolds with models $I$ and $I'$, then $M \times M'$ is a $C^n$ manifold with model $I \times I'$.

*Proof.* On the product set, $\widehat{e \times e'} = \hat e \times \hat e'$, and $\widehat{e.\mathrm{source} \times e'.\mathrm{source}} = \widehat{e.\mathrm{source}} \times \widehat{e'.\mathrm{source}}$, because the range of $I \times I'$ is the product of the ranges. A product of maps that are $C^n$ on two sets is $C^n$ on the product set. The same holds for the inverse. The changes of charts of $M \times M'$ are $(e \times e')^{-1} \gg (f \times f') = (e^{-1} \gg f) \times (e'^{-1} \gg f')$, so they are in $G_n(I \times I')$. $\square$

### Examples

**Example (Normed spaces).** A normed space $E$ is a $C^n$ manifold with the trivial model, for every $n$. Its atlas is $\{\mathrm{id}\}$, and the only change of charts is the identity. More generally the model space $H$ of any model $I$ is a $C^n$ manifold with model $I$ (`instIsManifoldModelSpace`).

**Example (Open subsets).** An open subset of a $C^n$ manifold is a $C^n$ manifold with the same model. The groupoid $G_n(I)$ is closed under restriction, since a restriction of a $C^n$ map to an open set is $C^n$, and Chapter 1, Section 2 applies. This is the instance `TopologicalSpace.Opens.instIsManifoldSubtypeMem`.

**Example (The circle).** The circle with the two stereographic charts of Chapter 1, Section 1 is a $C^\omega$ manifold with the trivial model of $\mathbb{R}$. Its only nontrivial changes of charts are $t \mapsto 1/t$ on $\mathbb{R} \setminus \{0\}$, which is analytic and its own inverse.

**Example (The cube chart).** The charted space $\mathbb{R}_c$ of Chapter 1, Section 2 is a $C^\infty$ manifold with the trivial model, and the union of its atlas with the atlas $\{\mathrm{id}\}$ is a $C^0$ atlas but not a $C^1$ atlas.

::: mathlib
`ModelWithCorners.range_eq_closure_interior` · `Mathlib.Geometry.Manifold.IsManifold.Basic`

The closed embedding is `ModelWithCorners.isClosedEmbedding`, and `ModelWithCorners.map_nhds_eq` says `map I (𝓝 x) = 𝓝[range I] (I x)`. The theorem on the closure of the interior is `ModelWithCorners.range_eq_closure_interior`, and the unique derivatives are `ModelWithCorners.uniqueDiffOn : UniqueDiffOn 𝕜 (range I)`. The order and the case $n = 0$ are `contDiffGroupoid_le` and `contDiffGroupoid_zero_eq`, and the products are `contDiffGroupoid_prod` and the instance `IsManifold.prod`. `IsManifold.of_le` lowers the order.

<?decl ModelWithCorners.range_eq_closure_interior?>
<?decl ModelWithCorners.uniqueDiffOn?>
<?decl ModelWithCorners.isClosedEmbedding?>
<?decl contDiffGroupoid_zero_eq?>
<?decl IsManifold.prod?>
:::

### The library around it

The documentation of the module recommends a form for theorems on manifolds without boundary: `{I : ModelWithCorners ℝ E E} [I.Boundaryless]` with `[ChartedSpace E M] [IsManifold I n M]`, and not the fixed model `𝓘(ℝ, E)` or the Euclidean model `𝓡 n`. The tangent bundle of a manifold over $\mathbb{R}^n$ is modelled on $\mathbb{R}^n \times \mathbb{R}^n$, not on $\mathbb{R}^{2n}$, and the product model on $E \times F$ is not equal by definition to the trivial model of $E \times F$. A theorem with a fixed model does not apply to them. The module also defines `TangentSpace I x`, which is $E$ by definition, for Chapter 4, and the instance `IsManifold.disjointUnion`.

Common errors of a learner:

- Writing `IsManifold 𝓘(ℝ, E) ∞ M` with `[ChartedSpace H M]` for a different `H`. The model space of the charted space must be the `H` of the model.
- Assuming that `IsManifold` gives a Hausdorff or second countable space. Add `[T2Space M]` and `[SecondCountableTopology M]` when needed.
- Confusing `n = ∞` and `n = ω`. In `WithTop ℕ∞`, `∞` is the coercion of `⊤ : ℕ∞` and means $C^\infty$. The top element `ω` means analytic.
- Expecting $I^{-1}$ to be defined only on the range. It is a total continuous map $E \to H$.

### Exercises

1. (A) Show that the identity of $E$ is a model with corners, and that it is boundaryless.
2. (A) Let $I : [0, \infty) \to \mathbb{R}$ be the inclusion and $I^{-1}(y) = \max(y, 0)$. Show that $I$ is a model with corners.
3. (A) Show that $G_\infty(I) = \bigcap_{k \in \mathbb{N}} G_k(I)$.
4. (B) Let $C \subseteq \mathbb{R}^2$ be the closed set $\{(u, v) : v \ge |u|^{1/2}\}$, which is not convex. Show that $C$ is the closure of its interior, and explain which condition of a model with corners fails for the inclusion of $C$.
5. (B) Prove that the changes of charts of $M \times M'$ are products of changes of charts, as used in the proof of the theorem on products.
6. (B) Show that a $C^n$ manifold with $n \ge 1$ and the trivial model of $\mathbb{R}$ can have the chart $t \mapsto t + t^3$, and that it cannot have both charts $t \mapsto t$ and $t \mapsto t^3$ in one $C^1$ atlas.
7. (C) Let $\mathbb{K} = \mathbb{Q}_p$. Show that a model with corners over $\mathbb{K}$ is a homeomorphism $H \to E$, and that every $C^n$ manifold over $\mathbb{K}$ is a manifold without boundary.

### Notes and history

Manifolds with corners were introduced by Cerf (1961) and Douady (1961) in their work on spaces of embeddings. The definition of Mathlib is wider: any closed convex range with nonempty interior is allowed, which covers half spaces, quadrants and more general convex models. The order $\omega$ for analytic manifolds was added to the same class, so that one theory covers $C^k$, $C^\infty$ and analytic structures.

### Reference

<?reference?>
