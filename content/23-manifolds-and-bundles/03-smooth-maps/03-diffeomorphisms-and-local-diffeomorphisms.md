---
title: Diffeomorphisms and local diffeomorphisms
kind: theory
modules:
  - Mathlib.Geometry.Manifold.Diffeomorph
  - Mathlib.Geometry.Manifold.LocalDiffeomorph
  - Mathlib.Geometry.Diffeology.Basic
explains:
  E3: [Diffeomorph, IsLocalDiffeomorphAt, IsLocalDiffeomorph, IsLocalDiffeomorph.diffeomorphOfBijective]
  E2: [Diffeomorph.toHomeomorph, Diffeomorph.refl, Diffeomorph.symm, Diffeomorph.trans, Diffeomorph.contMDiff, Diffeomorph.toContMDiffMap, Diffeomorph.prodCongr, Diffeomorph.prodComm, Diffeomorph.contMDiff_comp_diffeomorph_iff, Diffeomorph.contMDiff_diffeomorph_comp_iff, ContinuousLinearEquiv.toDiffeomorph, ModelWithCorners.transContinuousLinearEquiv, ContinuousLinearEquiv.toTransContinuousLinearEquiv, PartialDiffeomorph, IsLocalDiffeomorphOn, isLocalDiffeomorph_iff, Diffeomorph.isLocalDiffeomorph, IsLocalDiffeomorph.isLocalHomeomorph, IsLocalDiffeomorph.isOpenMap, IsLocalDiffeomorph.isOpen_range, IsLocalDiffeomorphAt.comp, IsLocalDiffeomorphAt.contMDiffAt, IsLocalDiffeomorphAt.localInverse, IsLocalDiffeomorphAt.isInvertible_mfderiv, Diffeomorph.isInvertible_mfderiv, DiffeologicalSpace, Diffeology.IsPlot, Diffeology.DSmooth, Diffeology.dTopology, Diffeology.IsContDiffCompatible, NormedSpace.toDiffeology]
  E1: auto
families: []
requires: [V23.C01, V23.C02, V17.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Diffeomorphisms and local diffeomorphisms

### Overview

Two $C^n$ manifolds are the same for analysis when there is a bijection between them that is $C^n$ in both directions. Such a map is a diffeomorphism. A local diffeomorphism is a map that agrees near each point with a diffeomorphism between open sets. Covering maps of manifolds, such as the map from the line to the circle, are local diffeomorphisms that are not injective.

This section defines both notions, proves that diffeomorphisms form a groupoid and preserve smoothness, and proves that a local diffeomorphism is an open map and that a bijective local diffeomorphism is a diffeomorphism. The derivative of a diffeomorphism is invertible at every point, but the derivative belongs to Chapter 4, so this section only states that fact.

### Definitions

Fix models $I$ and $J$ over $\mathbb{K}$, charted spaces $M$ over $H$ and $N$ over $G$, and $n$.

**Definition (Diffeomorphism).** A *$C^n$ diffeomorphism* $M \to N$ is a bijection $h : M \to N$ such that $h$ and $h^{-1}$ are $C^n$.

**Definition (Partial diffeomorphism).** A *partial diffeomorphism* is a bijection $\Phi : U \to V$ between open sets $U \subseteq M$ and $V \subseteq N$ such that $\Phi$ is $C^n$ on $U$ and $\Phi^{-1}$ is $C^n$ on $V$.

**Definition (Local diffeomorphism).** A map $f : M \to N$ is a *local diffeomorphism at $x$* if there is a partial diffeomorphism $\Phi : U \to V$ with $x \in U$ and $f = \Phi$ on $U$. It is a *local diffeomorphism on $s$* if it is one at every point of $s$, and a *local diffeomorphism* if it is one at every point.

::: mathlib
`Diffeomorph` · `Mathlib.Geometry.Manifold.Diffeomorph`

`Diffeomorph I J M N n` extends `M ≃ N` with the fields `contMDiff_toFun` and `contMDiff_invFun`. The notation is `M ≃ₘ^n⟮I, J⟯ N` in the scope `Manifold`. The groupoid operations are `Diffeomorph.refl I M n`, `Diffeomorph.symm` and `Diffeomorph.trans`, and `Diffeomorph.toHomeomorph` forgets the smoothness. The products are `Diffeomorph.prodCongr` and `Diffeomorph.prodComm`.

<?decl Diffeomorph?>
<?decl Diffeomorph.trans?>
:::

::: mathlib
`IsLocalDiffeomorphAt` · `Mathlib.Geometry.Manifold.LocalDiffeomorph`

`IsLocalDiffeomorphAt I J n f x` says `∃ Φ : PartialDiffeomorph I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source`. The structure `PartialDiffeomorph` extends `PartialEquiv M N` with open source and target and the two smoothness conditions. Its docstring calls it auxiliary and asks that it not be used outside its file, so statements should use the predicates. `IsLocalDiffeomorphOn I J n f s` and `IsLocalDiffeomorph I J n f` follow, with `isLocalDiffeomorph_iff`.

<?decl IsLocalDiffeomorphAt?>
<?decl IsLocalDiffeomorph?>
:::

### Theorems and proofs

**Theorem (The groupoid of diffeomorphisms).** The identity of $M$ is a $C^n$ diffeomorphism. The inverse of a $C^n$ diffeomorphism is one, and so is the composite of two. Each $C^n$ diffeomorphism is a homeomorphism.

*Proof.* The identity is its own inverse and is $C^n$ (Section 1). The inverse $h^{-1}$ has inverse $h$, and both are $C^n$. For $h : M \to N$ and $k : N \to P$, the composite $k \circ h$ has inverse $h^{-1} \circ k^{-1}$. Both are composites of $C^n$ maps, so they are $C^n$ by the composition theorem of Section 1. A $C^n$ map is continuous, so $h$ and $h^{-1}$ are continuous, and $h$ is a homeomorphism. $\square$

**Theorem (Diffeomorphisms preserve smoothness).** Let $h : M \to N$ be a $C^n$ diffeomorphism and $m \le n$. A map $f : N \to M'$ is $C^m$ if and only if $f \circ h$ is $C^m$. A map $g : M' \to M$ is $C^m$ if and only if $h \circ g$ is $C^m$.

*Proof.* The maps $h$ and $h^{-1}$ are $C^n$, so they are $C^m$. If $f$ is $C^m$, then $f \circ h$ is $C^m$ by composition. If $f \circ h$ is $C^m$, then $f = (f \circ h) \circ h^{-1}$ is $C^m$ by composition. The second claim has the same proof with $h$ on the left: $g = h^{-1} \circ (h \circ g)$. $\square$

**Theorem (Local diffeomorphisms are open).** A local diffeomorphism $f : M \to N$ is $C^n$ and a local homeomorphism. It is an open map, and its range is open. Every diffeomorphism is a local diffeomorphism.

*Proof.* Let $x \in M$ and let $\Phi : U \to V$ be a partial diffeomorphism with $x \in U$ and $f = \Phi$ on $U$. Then $f$ is $C^n$ on the open set $U$, so $f$ is $C^n$ at $x$. The maps $\Phi$ and $\Phi^{-1}$ are $C^n$ on the open sets $U$ and $V$, so they are continuous there. So $\Phi$ is a homeomorphism from $U$ onto the open set $V$, and $f$ is a local homeomorphism at $x$. Let $W \subseteq M$ be open. For $x \in W$, with $\Phi$ as above, $f(W \cap U) = \Phi(W \cap U)$ is open in $V$, since $\Phi$ is a homeomorphism, so it is open in $N$. It contains $f(x)$ and lies in $f(W)$. So $f(W)$ is open. The range is $f(M)$. For a diffeomorphism $h$, take $\Phi = h$ with $U = M$ and $V = N$. $\square$

**Theorem (A bijective local diffeomorphism is a diffeomorphism).** Let $f : M \to N$ be a local diffeomorphism and a bijection. Then $f$ is a $C^n$ diffeomorphism.

*Proof.* By the theorem above, $f$ is $C^n$. Let $g$ be the inverse of $f$, and let $y \in N$. Put $x = g(y)$, and let $\Phi : U \to V$ be a partial diffeomorphism with $x \in U$ and $f = \Phi$ on $U$. Then $V$ is an open set that contains $\Phi(x) = f(x) = y$. Let $v \in V$. The point $u = \Phi^{-1}(v)$ lies in $U$, and $f(u) = \Phi(u) = v$. Since $f$ is injective, $g(v) = u$. So $g = \Phi^{-1}$ on $V$. The map $\Phi^{-1}$ is $C^n$ on the open set $V$, so it is $C^n$ at $y$. The map $g$ agrees with it on the neighbourhood $V$ of $y$, so $g$ is $C^n$ at $y$. Hence $g$ is $C^n$, and $f$ is a diffeomorphism. $\square$

::: mathlib
`IsLocalDiffeomorph.diffeomorphOfBijective` · `Mathlib.Geometry.Manifold.LocalDiffeomorph`

`hf.diffeomorphOfBijective hf'` takes `hf : IsLocalDiffeomorph I J n f` and `hf' : Function.Bijective f` and returns a `Diffeomorph I J M N n`. The other results are `IsLocalDiffeomorph.isLocalHomeomorph`, `IsLocalDiffeomorph.isOpenMap`, `IsLocalDiffeomorph.isOpen_range` and `Diffeomorph.isLocalDiffeomorph`. The smoothness theorem is `Diffeomorph.contMDiff_comp_diffeomorph_iff`, with the hypothesis `m ≤ n`, and `Diffeomorph.contMDiff_diffeomorph_comp_iff`. A local diffeomorphism at `x` has a local inverse `IsLocalDiffeomorphAt.localInverse`, and local diffeomorphisms compose (`IsLocalDiffeomorphAt.comp`).

<?decl IsLocalDiffeomorph.diffeomorphOfBijective?>
<?decl Diffeomorph.contMDiff_comp_diffeomorph_iff?>
<?decl IsLocalDiffeomorph.isOpenMap?>
:::

### Examples

**Example (Linear equivalences).** A continuous linear equivalence $L : E \to E'$ is a $C^\omega$ diffeomorphism for the trivial models (`ContinuousLinearEquiv.toDiffeomorph`). Both $L$ and $L^{-1}$ are continuous linear maps, which are $C^\omega$ by Section 2.

**Example (Changing the model).** Given a model $I : H \to E$ and a continuous linear equivalence $L : E \to F$, the composite $L \circ I$ is a model $H \to F$ (`ModelWithCorners.transContinuousLinearEquiv`). The identity of $M$ is a diffeomorphism from $M$ with the model $I$ to $M$ with the model $L \circ I$ (`ContinuousLinearEquiv.toTransContinuousLinearEquiv`). In charts it is $L$ on the range of $I$. This lets one replace a finite dimensional model by $\mathbb{K}^d$.

**Example (A homeomorphism that is not a diffeomorphism).** The map $t \mapsto t^3$ of $\mathbb{R}$ is a $C^\omega$ bijection and a homeomorphism. Its inverse $s \mapsto s^{1/3}$ is not differentiable at $0$, so it is not a $C^1$ diffeomorphism. It is a local diffeomorphism on $\mathbb{R} \setminus \{0\}$ but not at $0$.

**Example (Two atlases, one manifold).** Let $M$ be the set $\mathbb{R}$ with the single chart $\varphi(t) = t^3$. Then $\varphi : M \to \mathbb{R}$, with the trivial model on $\mathbb{R}$, is a $C^\omega$ diffeomorphism. In charts, $\varphi$ becomes $\mathrm{id} \circ \varphi \circ \varphi^{-1} = \mathrm{id}$, and $\varphi^{-1}$ becomes $\varphi \circ \varphi^{-1} = \mathrm{id}$. The atlases $\{\varphi\}$ and $\{\mathrm{id}\}$ on the set $\mathbb{R}$ are not compatible, as Section 2, Exercise 6 shows, but the two manifolds are diffeomorphic.

**Example (Products).** If $h : M \to M'$ and $k : N \to N'$ are diffeomorphisms, then $h \times k$ is one for the product models (`Diffeomorph.prodCongr`), with inverse $h^{-1} \times k^{-1}$, by Section 2. The swap $M \times N \to N \times M$ is a diffeomorphism (`Diffeomorph.prodComm`).

### The library around it

Chapter 4 defines the derivative $\mathrm{mfderiv}$. With it, `Diffeomorph.isInvertible_mfderiv` and `IsLocalDiffeomorphAt.isInvertible_mfderiv` say that the derivative of a diffeomorphism, or of a local diffeomorphism at $x$, is invertible, under the hypothesis `n ≠ 0`. The converse, the inverse function theorem on manifolds, needs a complete model space. Chapter 2, Section 3 uses diffeomorphisms to show that they preserve interior and boundary.

The module `Mathlib.Geometry.Diffeology.Basic` starts a different approach to smooth spaces. A diffeological space is a type $X$ with, for every $n$, a set of maps $\mathbb{R}^n \to X$, the *plots*. The plots contain the constant maps, are closed under composition with smooth maps $\mathbb{R}^m \to \mathbb{R}^n$, and form a local condition. The class is `DiffeologicalSpace`, and `Diffeology.IsPlot p` says that `p : EuclideanSpace ℝ (Fin n) → X` is a plot. A map is smooth (`Diffeology.DSmooth`) if its composite with every plot is a plot. Every diffeology defines a topology, the D-topology `Diffeology.dTopology`, in which a set is open when its preimage under every plot is open. A finite dimensional real normed space has the diffeology of its $C^\infty$ maps, `NormedSpace.toDiffeology`, and the class `Diffeology.IsContDiffCompatible` says that a diffeology is this one. It is a definition and not an instance, to avoid two instances on spaces such as `Fin n → ℝ`. Diffeological spaces include quotients and spaces of maps, which are not manifolds.

Common errors of a learner:

- Confusing `Diffeomorph` with `OpenPartialHomeomorph` in the maximal atlas. A chart is a partial map into the model, and a diffeomorphism is a global bijection between manifolds.
- Using `PartialDiffeomorph` in statements. Its docstring reserves it for its file.
- Expecting a bijective $C^\infty$ map to be a diffeomorphism, as in the example of $t \mapsto t^3$.
- Applying `contMDiff_comp_diffeomorph_iff` with $m > n$. The hypothesis `m ≤ n` is required.

### Exercises

1. (A) Show that the swap $M \times N \to N \times M$ is a diffeomorphism.
2. (A) Show that the composite of two local diffeomorphisms is a local diffeomorphism.
3. (A) Show that the restriction of a local diffeomorphism to an open subset is a local diffeomorphism.
4. (B) Show that $t \mapsto t + t^3$ is a $C^\infty$ diffeomorphism of $\mathbb{R}$. Hint: its derivative never vanishes, and the inverse function theorem of Volume 17 applies.
5. (B) Show that an injective local diffeomorphism $f : M \to N$ is a diffeomorphism onto the open subset $f(M)$.
6. (B) Show that the image of a local diffeomorphism $f : M \to N$ with $M$ compact and nonempty and $N$ connected and Hausdorff is all of $N$.
7. (C) Show that the map $\mathbb{R} \to S^1$, $t \mapsto (\cos t, \sin t)$, is a local diffeomorphism, using the stereographic charts of the circle.
8. (C) Show that the D-topology of the diffeology `NormedSpace.toDiffeology` on a finite dimensional real normed space is the norm topology. Hint: a linear equivalence $\mathbb{R}^d \to X$ is a plot, and every plot is continuous.

### Notes and history

The notion of diffeomorphism is as old as the notion of a differentiable manifold. Diffeological spaces were introduced by Souriau around 1980, and the book of Iglesias-Zemmour develops their theory. The example of the chart $t \mapsto t^3$ shows that a smooth structure is a maximal atlas only up to diffeomorphism.

### Reference

<?reference?>
