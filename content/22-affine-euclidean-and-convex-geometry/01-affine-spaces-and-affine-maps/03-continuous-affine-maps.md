---
title: Continuous affine maps
kind: theory
modules:
  - Mathlib.Topology.Algebra.Affine
  - Mathlib.Topology.Algebra.ContinuousAffineMap
  - Mathlib.Topology.Algebra.ContinuousAffineMap.Topology
  - Mathlib.Topology.Algebra.ContinuousAffineEquiv
  - Mathlib.Topology.Algebra.AffineSubspace
explains:
  E3: [AffineMap.continuous_linear_iff, AffineMap.homothety_isOpenMap, ContinuousAffineMap, ContinuousAffineMap.contLinear, ContinuousAffineEquiv, ContinuousAffineMap.decompHomeomorph, AffineSubspace.isClosed_direction_iff]
  E2: [AffineMap.isOpenMap_linear_iff, AffineMap.lineMap_continuous, eventually_homothety_mem_of_mem_interior, ContinuousAffineMap.decomp, ContinuousAffineMap.comp, ContinuousAffineEquiv.toHomeomorph, ContinuousAffineMap.continuous_rng_iff, AffineSubspace.subtypeA]
  E1: auto
families: []
requires: [V07, V13, V16.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Continuous affine maps

### Overview

When the space of vectors carries a topology, an affine space carries one too, and the translations and differences are continuous. Then an affine map is continuous exactly when its linear part is continuous, and the same holds for open maps and embeddings. This section proves these transfers, defines continuous affine maps and equivalences, describes the topology on the space of continuous affine maps, and shows that an affine subspace is closed exactly when its direction is closed.

### Definitions

**Definition (topological torsor).** Let $V$ be a topological additive group and $P$ a torsor over $V$ with a topology. Then $P$ is a *topological torsor* if the maps $V \times P \to P$, $(v, p) \mapsto v +_v p$, and $P \times P \to V$, $(p, q) \mapsto p -_v q$, are continuous.

For each $p$, the maps $v \mapsto v +_v p$ and $q \mapsto q -_v p$ are then continuous and inverse to each other, so each one is a homeomorphism between $V$ and $P$.

::: mathlib
`IsTopologicalAddTorsor` · `Mathlib.Topology.Algebra.Group.Torsor`

`IsTopologicalAddTorsor P` extends `ContinuousVAdd V P` with `continuous_vsub`. The homeomorphism $v \mapsto v +_v p$ is `Homeomorph.vaddConst`.

<?decl IsTopologicalAddTorsor?>
:::

**Definition (continuous affine map).** A *continuous affine map* $P \to Q$ between topological torsors is an affine map that is continuous. A *continuous affine equivalence* is an affine equivalence $f$ such that $f$ and $f^{-1}$ are continuous.

::: mathlib
`ContinuousAffineMap` · `Mathlib.Topology.Algebra.ContinuousAffineMap`

`ContinuousAffineMap R P Q` extends `P →ᵃ[R] Q` with the field `cont : Continuous toFun`. The notation is `P →ᴬ[R] Q`. Composition is `ContinuousAffineMap.comp`.

<?decl ContinuousAffineMap?>
:::

::: mathlib
`ContinuousAffineEquiv` · `Mathlib.Topology.Algebra.ContinuousAffineEquiv`

`ContinuousAffineEquiv k P₁ P₂` extends `P₁ ≃ᵃ[k] P₂` with `continuous_toFun` and `continuous_invFun`. The notation is `P₁ ≃ᴬ[k] P₂`. `ContinuousAffineEquiv.toHomeomorph` forgets the affine structure. The docstring lists the group structure on `P ≃ᴬ[k] P` as future work.

<?decl ContinuousAffineEquiv?>
:::

### Theorems and proofs

**Theorem (transfer to the linear part).** Let $P$ and $Q$ be topological torsors over $V$ and $W$, and $f : P \to Q$ affine with linear part $L$. Then $f$ is continuous if and only if $L$ is continuous. The same holds for the properties: open map, embedding, closed embedding, open embedding.

*Proof.* Fix $p \in P$. By Section 2, $f = \tau \circ L \circ \sigma$ with $\sigma(q) = q -_v p$ and $\tau(w) = w +_v f(p)$. By the remark after the definition, $\sigma : P \to V$ and $\tau : W \to Q$ are homeomorphisms. So $L = \tau^{-1} \circ f \circ \sigma^{-1}$. Each of the five properties is preserved by composition on both sides with homeomorphisms. So $f$ has the property if and only if $L$ has it. $\square$

::: mathlib
`AffineMap.continuous_linear_iff` · `Mathlib.Topology.Algebra.Affine`

`AffineMap.continuous_linear_iff : Continuous f.linear ↔ Continuous f` for `f : P →ᵃ[R] Q` between topological torsors. The other forms, such as `AffineMap.isOpenMap_linear_iff`, have similar names. The linear part of a continuous affine map is the continuous linear map `ContinuousAffineMap.contLinear`, built with this theorem.

<?decl AffineMap.continuous_linear_iff?>
:::

::: mathlib
`ContinuousAffineMap.contLinear` · `Mathlib.Topology.Algebra.ContinuousAffineMap`

`f.contLinear : V →L[R] W` is the linear part of `f : P →ᴬ[R] Q` as a continuous linear map. For modules, `ContinuousAffineMap.decomp` gives $f = L + f(0)$ with $L$ continuous linear.

<?decl ContinuousAffineMap.contLinear?>
:::

**Theorem (line maps and homotheties).** Let $k$ be a commutative topological ring, $V$ a topological $k$-module with continuous scalar multiplication, and $P$ a topological torsor over $V$. Then $(p_0, p_1, c) \mapsto \ell_{p_0 p_1}(c)$ is continuous, and so is each homothety $h_{x, t}$. If $k$ is a field and $t \neq 0$, then $h_{x, t}$ is a homeomorphism, so it is an open map.

*Proof.* The map is $(p_0, p_1, c) \mapsto c(p_1 -_v p_0) +_v p_0$, a composite of $-_v$, scalar multiplication and $+_v$, all continuous. A homothety is $h_{x, t}(p) = \ell_{x p}(t)$. For $t \neq 0$, $h_{x, t} \circ h_{x, t^{-1}} = h_{x, 1} = \mathrm{id}$ by the rule $h_{x, r} \circ h_{x, s} = h_{x, rs}$ of Section 2, and in the same way in the other order. So $h_{x, t}$ is a homeomorphism with inverse $h_{x, t^{-1}}$. $\square$

::: mathlib
`AffineMap.homothety_isOpenMap` · `Mathlib.Topology.Algebra.Affine`

`AffineMap.homothety_isOpenMap x t (ht : t ≠ 0) : IsOpenMap (homothety x t)`, over a field. Continuity of the line map is `AffineMap.lineMap_continuous`. By continuity in $\delta$, `eventually_homothety_mem_of_mem_interior` says that $h_{x, \delta}(y)$ stays in $s$ for $\delta$ near $1$ when $y$ is in the interior of $s$; Chapter 6 uses it.

<?decl AffineMap.homothety_isOpenMap?>
:::

**Theorem (closed affine subspaces).** Let $V$ be a topological group in which points are closed, and $s$ an affine subspace of a topological torsor $P$ over $V$. Then $s$ is closed in $P$ if and only if its direction $D$ is closed in $V$.

*Proof.* If $s$ is empty, then $D = \{0\}$, which is closed since points of $V$ are closed, and the empty set is closed. So both sides hold. Otherwise fix $p \in s$. By Chapter 2, $s = \{q : q -_v p \in D\}$, so $s$ is the image of $D$ under the homeomorphism $v \mapsto v +_v p$. A homeomorphism maps closed sets to closed sets, and its inverse does too. $\square$

::: mathlib
`AffineSubspace.isClosed_direction_iff` · `Mathlib.Topology.Algebra.AffineSubspace`

`AffineSubspace.isClosed_direction_iff [T1Space V] (s) : IsClosed (s.direction : Set V) ↔ IsClosed (s : Set P)`. The hypothesis `T1Space V` covers the empty subspace. The same file gives the inclusion `AffineSubspace.subtypeA` as a continuous affine map.

<?decl AffineSubspace.isClosed_direction_iff?>
:::

**Theorem (the space of continuous affine maps).** Give the continuous affine maps $V \to Q$, from a topological module over a normed field, the coarsest topology for which evaluation at each point and the linear part are continuous. Then $f \mapsto (f(0), L_f)$ is a homeomorphism onto $Q \times \mathcal L(V, W)$, where $\mathcal L(V, W)$ is the space of continuous linear maps.

*Proof.* The map is a bijection: its inverse sends $(q, L)$ to $v \mapsto L(v) +_v q$, which is continuous and affine. The map is continuous, since evaluation at $0$ and the linear part are continuous for this topology. For the inverse, the map $(q, L) \mapsto L(v) +_v q$ is continuous for each $v$, since evaluation of continuous linear maps at a point is continuous; and the linear part of the inverse is the projection to $L$. By the definition of the topology, these two facts give continuity of the inverse. $\square$

::: mathlib
`ContinuousAffineMap.decompHomeomorph` · `Mathlib.Topology.Algebra.ContinuousAffineMap.Topology`

`ContinuousAffineMap.decompHomeomorph R V Q : (V →ᴬ[R] Q) ≃ₜ (Q × (V →L[R] W))`. In the file, the topology on `P →ᴬ[R] Q` is induced by `fun f => (⇑f, f.contLinear)`. The criterion for continuity of a map into this space is `ContinuousAffineMap.continuous_rng_iff`.

<?decl ContinuousAffineMap.decompHomeomorph?>
:::

### Examples

**Example (a continuous affine equivalence of the plane).** The map $f(x, y) = (2x + y + 1, x - 3)$ of Section 2 has the linear part $L(x, y) = (2x + y, x)$, which is continuous on $\mathbb{R}^2$. So $f$ is continuous. Its inverse $(u, v) \mapsto (v + 3, u - 2v - 7)$ is affine with continuous linear part, so $f$ is a continuous affine equivalence.

**Counterexample (an affine map that is not continuous).** Let $c_{00}$ be the space of real sequences with finite support, with the norm $\|x\|_\infty = \max_n |x_n|$. The map $\varphi(x) = \sum_n n x_n$ is linear. It is not continuous: the unit vector $e_n$ has norm $1$ and $\varphi(e_n) = n$. So $f = \varphi + 1$ is an affine map that is not continuous. The affine subspace $\{f = 0\} = \{\varphi = -1\}$ has the direction $\ker \varphi$, which is not closed: $\ker \varphi$ is a hyperplane, and a hyperplane that is the kernel of a discontinuous linear form is dense. By the theorem on closed affine subspaces, $\{f = 0\}$ is not closed.

### The library around it

In finite dimension over a complete nontrivially normed field, Volume 16, Chapter 3 proves that each linear map is continuous (`LinearMap.continuous_of_finiteDimensional`) and that each finite dimensional subspace is closed (`Submodule.isClosed_of_finiteDimensional`). The transfer theorem then gives the affine forms in `Mathlib.Analysis.Normed.Module.FiniteDimension`.

::: mathlib
`AffineMap.continuous_of_finiteDimensional` · `Mathlib.Analysis.Normed.Module.FiniteDimension`

An affine map between normed affine spaces over a complete field, with a finite dimensional domain, is continuous. The companion results are `AffineSubspace.isClosed_of_finiteDimensional`, which says that an affine subspace with finite dimensional direction is closed, and `AffineEquiv.toContinuousAffineEquiv`, which upgrades an affine equivalence in finite dimension.

<?decl AffineMap.continuous_of_finiteDimensional?>
:::

Chapter 3 uses continuous affine maps for isometries: the Mazur-Ulam theorem says that a surjective isometry of real normed spaces is affine, hence a continuous affine equivalence.

### Exercises

1. (A) Show that each translation $v +_v \cdot$ of a topological torsor is a homeomorphism, and that each point reflection is a homeomorphism.
2. (A) Let $f : \mathbb{R}^2 \to \mathbb{R}$, $f(x, y) = 3x - y + 2$. Show that $f$ is an open map and that the level set $\{f = 0\}$ is closed.
3. (A) Let $P$ be a topological torsor and $x, y \in P$. Show that $t \mapsto \ell_{x y}(t)$ is continuous on $k$ and that the midpoint map $P \times P \to P$ is continuous when $2$ is invertible in $k$.
4. (B) Let $V$ be a topological module with continuous scalar multiplication and $s$ an affine subspace of a topological torsor $P$ over $V$. Show that the closure of $s$ is an affine subspace with direction the closure of the direction of $s$, when $s$ is nonempty. Hint: use the homeomorphism $v \mapsto v +_v p$ and the fact that the closure of a submodule is a submodule.
5. (B) Let $U$ be an open subset of a real topological vector space and $x, y \in U$. Show that $h_{x, \delta}(y) \in U$ for $\delta$ near $1$. Give an open $U \subseteq \mathbb{R}$ and $x, y \in U$ such that $h_{x, \delta}(y) \notin U$ for some $\delta \in [0, 1]$.
6. (C) In the counterexample, show directly that $\ker \varphi$ is dense in $c_{00}$. Hint: for $x \in c_{00}$ and large $N$, subtract $\varphi(x) e_N / N$.

### Notes and history

The file `Mathlib.Topology.Algebra.Affine` has the authors Frédéric Dupuis and Attila Gáspár. The structure of continuous affine maps is due to Oliver Nash, and the structure of continuous affine equivalences is due to Michael Rothgang. The topology on continuous affine maps (2026, Attila Gáspár) and the topology of affine subspaces (2025, Joseph Myers) are recent additions.

### Reference

<?reference?>
