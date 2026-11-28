---
title: Functions that vanish at infinity, functions with compact support, and maps that fix zero
kind: api
modules:
  - Mathlib.Topology.ContinuousMap.ZeroAtInfty
  - Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
  - Mathlib.Topology.ContinuousMap.CompactlySupported
  - Mathlib.Topology.ContinuousMap.ContinuousMapZero
  - Mathlib.Topology.ContinuousMap.ContinuousMapZero.Unitization
explains:
  E2: [ZeroAtInftyContinuousMap.isBounded_image, ZeroAtInftyContinuousMap.isClosed_range_toBCF, ZeroAtInftyContinuousMap.instCompleteSpace, ZeroAtInftyContinuousMap.unitizationEquiv, CompactlySupportedContinuousMapClass.instZeroAtInftyContinuousMapClass, ContinuousMapZero.unitizationStarAlgEquiv]
  E1: auto
families: []
requires: [V04, V05, V13.C01, V13.C02, V13.C03, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Functions that vanish at infinity, functions with compact support, and maps that fix zero

### Overview

Section 3 studies the bounded continuous functions on a space $X$. This section studies three smaller spaces of continuous functions. A function vanishes at infinity if it is small outside a large compact set. A function has compact support if it is zero outside a compact set. A map between pointed spaces fixes zero if it sends $0$ to $0$.

Each of the three spaces is a ring without a unit, in general. The constant function $1$ does not vanish at infinity on $\mathbb{R}$, it does not have compact support, and it does not send $0$ to $0$. Each space becomes a unital ring when one adds the constants. The library proves this in a concrete form for two of them: adding the constants to the functions that vanish at infinity on $X$ gives the continuous functions on the one-point compactification of $X$, and adding the constants to the maps that fix zero gives all the continuous maps.

The functions with compact support are the test functions of measure theory. The theorem of Riesz, Markov and Kakutani in Volume 18 represents a positive linear functional on them as an integral. The maps that fix zero are the setting of the non-unital continuous functional calculus of the library.

### The library around it

#### Functions that vanish at infinity

The module `Mathlib.Topology.ContinuousMap.ZeroAtInfty` defines the structure `ZeroAtInftyContinuousMap α β`, with the notation `C₀(α, β)` and the other notation `α →C₀ β`. A term is a continuous map $f$ with $f(x) \to 0$ along the cocompact filter, `Filter.cocompact α` of Section 1. This is the field `ZeroAtInftyContinuousMapClass.zero_at_infty`. In words: for each neighbourhood $V$ of $0$, there is a compact set $K$ with $f(x) \in V$ for $x \notin K$. The class `ZeroAtInftyContinuousMapClass` follows the pattern of `ContinuousMapClass`, and the docstring of the module asks to state results for the class when possible. On a compact space each continuous map vanishes at infinity, because the cocompact filter is the bottom filter: `ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty` is the bijection with `C(α, β)`.

The algebraic structure is pointwise, as in Section 2: `C₀(α, β)` is an additive group, a module, and a non-unital ring when $\beta$ is one. The constant $1$ is not in the space in general, so the space has no unit. Composition on the right needs a map that sends the cocompact filter to the cocompact filter, so it takes a `CocompactMap` of Section 1 (`ZeroAtInftyContinuousMap.comp`).

**Proposition.** Let $\beta$ be a metric space with a point $0$. Each $f \in C_0(\alpha, \beta)$ is bounded.

*Proof.* Choose a compact set $K$ with $d(f(x), 0) < 1$ for $x \notin K$. The image $f(K)$ is compact, so it is bounded. Thus the range of $f$ is contained in the union of $f(K)$ and the ball of radius $1$ about $0$, a bounded set. $\square$

This is `ZeroAtInftyContinuousMap.isBounded_image`. It gives the map `ZeroAtInftyContinuousMap.toBCF` into the bounded continuous functions `α →ᵇ β`. The map is injective, and the metric of `C₀(α, β)` is defined so that it preserves distances (`ZeroAtInftyContinuousMap.dist_toBCF_eq_dist`).

**Proposition.** The range of `ZeroAtInftyContinuousMap.toBCF` is closed in `α →ᵇ β`. So `C₀(α, β)` is complete when $\beta$ is complete.

*Proof.* Let $f$ be a uniform limit of functions $f_n$ that vanish at infinity. Fix $\varepsilon > 0$, and choose $n$ with $d(f_n(x), f(x)) < \varepsilon / 2$ for each $x$. Choose a compact set $K$ with $d(f_n(x), 0) < \varepsilon / 2$ for $x \notin K$. Then $d(f(x), 0) < \varepsilon$ for $x \notin K$, so $f$ vanishes at infinity. A closed subset of the complete space of Section 3 is complete. $\square$

This is `ZeroAtInftyContinuousMap.isClosed_range_toBCF` and the instance `ZeroAtInftyContinuousMap.instCompleteSpace`. With the norm of the target, `C₀(α, β)` is a non-unital normed ring (`ZeroAtInftyContinuousMap.instNonUnitalNormedRing`) and a C*-ring when $\beta$ is one (`ZeroAtInftyContinuousMap.instCStarRing`). Each function that vanishes at infinity is uniformly continuous (`ZeroAtInftyContinuousMap.uniformContinuous`).

#### The unitization and the one-point compactification

Chapter 5 builds the one-point compactification `OnePoint X` of a space $X$, with the new point `OnePoint.infty`. A function $f$ that vanishes at infinity extends to `OnePoint X` by the value $0$ at the new point, and the extension is continuous. This is `ZeroAtInftyContinuousMap.toOnePoint`. The construction needs $X$ to be an $R_1$ space, so that the closure of a compact set is compact.

The unitization of a non-unital ring $A$ over $R$ is the ring $R \times A$ with the product $(r, a)(s, b) = (rs, rb + sa + ab)$. Its element $(r, a)$ stands for $r \cdot 1 + a$. The module `Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization` proves:

**Theorem.** Let $X$ be an $R_1$ space and $R$ a topological ring. The map $(r, f) \mapsto r + \tilde f$, where $\tilde f$ is the extension of $f$ by $0$, is a bijection from the unitization of `C₀(X, R)` to `C(OnePoint X, R)`. It is an isomorphism of star algebras.

*Proof sketch.* The inverse sends $g$ to the pair $(g(\infty), g - g(\infty))$. The function $g - g(\infty)$ restricted to $X$ vanishes at infinity, because the neighbourhoods of $\infty$ in `OnePoint X` are the complements of the closed compact sets of $X$. The two maps are inverse, and the first map respects the product by the formula for the product of the unitization. $\square$

The bijection is `ZeroAtInftyContinuousMap.unitizationEquiv`, and the star algebra form is `ZeroAtInftyContinuousMap.unitizationStarAlgEquiv`. The value at the new point is the scalar part (`ZeroAtInftyContinuousMap.unitizationEquiv_apply_infty`). The inverse map is built from `ContinuousMap.toZeroAtInfty`, and `ContinuousMap.toZeroAtInfty_apply` says that it sends $g$ to $x \mapsto g(x) - g(\infty)$.

#### Functions with compact support

The module `Mathlib.Topology.ContinuousMap.CompactlySupported` defines the structure `CompactlySupportedContinuousMap α β`, with the notations `C_c(α, β)` and `α →C_c β`. A term is a continuous map with compact support: the closure of the set where $f \ne 0$ is compact. The field is `CompactlySupportedContinuousMapClass.hasCompactSupport`. On a compact space each continuous map has compact support (`CompactlySupportedContinuousMapClass.of_compactSpace`).

A function with compact support vanishes at infinity: outside its support it is equal to $0$. The library records this as an instance, `CompactlySupportedContinuousMapClass.instZeroAtInftyContinuousMapClass`, so each lemma about the class of functions that vanish at infinity applies to `C_c(α, β)`. In particular, a function with compact support to a metric space is bounded, and `CompactlySupportedContinuousMap.toBoundedContinuousFunction` is the map to `α →ᵇ β`. Section 3 describes the same set as the ideal `compactlySupported α γ` of `α →ᵇ γ`.

The space is a non-unital ring, a module and a star ring, with pointwise operations (`CompactlySupportedContinuousMap.instStarRing`). It is not complete for the supremum norm in general: on $\mathbb{R}$, the uniform limits of functions with compact support are the functions that vanish at infinity. Composition on the right takes a cocompact map (`CompactlySupportedContinuousMap.comp`).

The real and the nonnegative functions have their own API, because measure theory uses both. The map `CompactlySupportedContinuousMap.nnrealPart` sends $f$ to its positive part $\max(f, 0)$ as a function to $\mathbb{R}_{\ge 0}$. The map `CompactlySupportedContinuousMap.toReal` goes back. The order on `C_c(α, ℝ≥0)` is the pointwise order, and $f_1 \le f_2$ gives $g$ with $f_1 + g = f_2$ (`CompactlySupportedContinuousMap.exists_add_of_le`). A positive linear functional on `C_c(α, ℝ)` restricts to a linear functional on `C_c(α, ℝ≥0)` (`CompactlySupportedContinuousMap.toNNRealLinear`). This is the form in which the theorem of Riesz, Markov and Kakutani takes its input.

#### Maps that fix zero

The module `Mathlib.Topology.ContinuousMap.ContinuousMapZero` defines the structure `ContinuousMapZero X R`, with the notation `C(X, R)₀`. Both $X$ and $R$ have a point $0$, and a term is a continuous map $f$ with $f(0) = 0$. A typical domain is a subset $s$ of $\mathbb{C}$ that contains $0$. The instance `Set.zeroOfFactMem` gives $s$ the point $0$ from a hypothesis `Fact (0 ∈ s)`, and `ContinuousMapZero.id s` is the inclusion of $s$.

The docstring of the module gives a rule: use the coercion of `C(X, R)₀` to `C(X, R)` from the class `ContinuousMapClass`, not the structure projection `ContinuousMapZero.toContinuousMap`. The instances pass through the coercion. The coercion is an embedding for the compact-open topology (`ContinuousMapZero.isEmbedding_toContinuousMap`) and an isometry for the supremum metric on a compact space (`ContinuousMapZero.isometry_toContinuousMap`).

The pointwise operations make `C(X, R)₀` a non-unital commutative ring (`ContinuousMapZero.instNonUnitalCommRing`), with the order and the star of $R$. It is complete when `C(X, R)` is complete and $R$ is $T_1$ (`ContinuousMapZero.instCompleteSpaceOfT1SpaceOfContinuousMap`), because the condition $f(0) = 0$ is closed. A map $g \in C(X, R)$ gives the map $g - g(0)$ that fixes zero (`ContinuousMap.toContinuousMapZero`, with `ContinuousMap.toContinuousMapZero_apply`).

The approximation theorem of Section 2 has a form for this space. For a compact set $s \subseteq \mathbb{C}$ with $0 \in s$, the polynomials in $z$ and $\bar z$ with no constant term are dense in `C(s, ℂ)₀` (`ContinuousMapZero.adjoin_id_dense`). The induction rule `ContinuousMapZero.induction_on` turns this into a proof method, as `ContinuousMap.induction_on_of_compact` does in Section 2.

The module `Mathlib.Topology.ContinuousMap.ContinuousMapZero.Unitization` proves the unitization statement for this space.

**Theorem.** The map $(r, f) \mapsto r + f$ is an isomorphism of star algebras from the unitization of `C(X, R)₀` to `C(X, R)`.

*Proof.* The inverse sends $g$ to $(g(0), g - g(0))$. The function $g - g(0)$ fixes zero. The composition in each order is the identity: $g(0) + (g - g(0)) = g$, and $(r + f)(0) = r$ because $f(0) = 0$. The map respects the product: $(r + f)(s + h) = rs + (rh + sf + fh)$, which is the product formula of the unitization. $\square$

This is `ContinuousMapZero.unitizationStarAlgEquiv`. It lets a result for unital algebras pass to the non-unital algebra `C(X, R)₀`.

#### Common errors

1. Looking for the constant $1$ in `C₀(α, β)`, `C_c(α, β)` or `C(X, R)₀`. These rings have no unit when the space is not compact or when $0 \ne 1$. Use the unitization, or the coercion to `C(X, R)`.
2. Expecting `C_c(α, β)` to be complete. Its completion for the supremum norm is `C₀(α, β)`, for a locally compact Hausdorff space $\alpha$.
3. Using the projection `ContinuousMapZero.toContinuousMap` in a statement. The instances use the coercion from `ContinuousMapClass`, and the projection is not reducibly equal to it, so instance search and rewriting can fail.

### Exercises

1. (A) Show that $x \mapsto e^{-x^2}$ vanishes at infinity on $\mathbb{R}$ and does not have compact support.
2. (A) Show that each continuous function on a compact space has compact support, with `CompactlySupportedContinuousMapClass.of_compactSpace`.
3. (B) Show that the uniform limit on $\mathbb{R}$ of a sequence of functions with compact support vanishes at infinity. Give a function that vanishes at infinity and is such a limit.
4. (B) Let $X = \mathbb{N}$ with the discrete topology. Describe `OnePoint X` as a subspace of $\mathbb{R}$, and describe the unitization equivalence for `C₀(ℕ, ℝ)`.
5. (B) Prove that `ContinuousMap.toContinuousMapZero` is additive and that it is the identity on the maps that fix zero.
6. (C) Let $\alpha$ be locally compact and Hausdorff. Prove that `C_c(α, ℝ)` is dense in `C₀(α, ℝ)`. Use the lemma of Urysohn of Chapter 8.

### Reference

<?reference?>
