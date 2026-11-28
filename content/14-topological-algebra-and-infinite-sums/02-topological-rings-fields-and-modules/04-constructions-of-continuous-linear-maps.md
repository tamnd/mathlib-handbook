---
title: Constructions of continuous linear maps
kind: api
modules:
  - Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
  - Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
  - Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
  - Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
  - Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
  - Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
  - Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
  - Mathlib.Topology.Algebra.Module.Determinant
  - Mathlib.Topology.Algebra.Module.Equiv.Pi
  - Mathlib.Topology.Algebra.Module.Equiv.Prod
  - Mathlib.Topology.Algebra.Module.Equiv.Submodule
  - Mathlib.Topology.Algebra.Module.Equiv
  - Mathlib.Topology.Algebra.Module.LinearMap
  - Mathlib.Topology.Algebra.Module.LinearMapPiProd
  - Mathlib.Topology.Algebra.Module.TransferInstance
  - Mathlib.Topology.Instances.Shrink
explains:
  E2: [ContinuousLinearMap.prod, ContinuousLinearMap.coprod, ContinuousLinearMap.pi, ContinuousLinearMap.codRestrict, Submodule.mkQL, Submodule.liftQL, ContinuousLinearMap.IsInvertible, ContinuousLinearMap.inverse, ContinuousLinearMap.extend, ContinuousLinearEquiv.prodCongr]
  E1: auto
families: []
requires: [V07, V13.C01, V13.C04, V14.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Constructions of continuous linear maps

### Overview

Section 2 of this chapter defines the type `M →L[R] M₂` of continuous linear maps and the type `M ≃L[R] M₂` of continuous linear equivalences. This section lists the standard ways to build new maps from old ones. A pair of maps gives a map into a product, and a map on each factor gives a map out of a product. A map restricts to a submodule and descends to a quotient. An invertible map has an inverse, and a map on a dense subspace extends to the whole space.

The constructions copy the linear constructions of Volume 7. Each one adds a proof of continuity, and most of them come with a lemma that the underlying linear map is the linear construction. The section also lists the continuous linear equivalences between products, Pi types and submodules, and the way to move a topology and a module structure along an equivalence.

### The library around it

#### Products and Pi types

The module `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd` has the maps that come with products. The names follow the linear names of `LinearMap`.

| Lean name | Statement |
|---|---|
| `ContinuousLinearMap.fst`, `ContinuousLinearMap.snd` | the projections $M_1 \times M_2 \to M_i$ |
| `ContinuousLinearMap.inl`, `ContinuousLinearMap.inr` | the inclusions $M_i \to M_1 \times M_2$ |
| `ContinuousLinearMap.prod` | $f$ and $g$ give $x \mapsto (f x, g x)$ |
| `ContinuousLinearMap.coprod` | $f$ and $g$ give $(x, y) \mapsto f x + g y$ |
| `ContinuousLinearMap.prodMap` | $f$ and $g$ give $(x, y) \mapsto (f x, g y)$ |
| `ContinuousLinearMap.pi` | a family $f_i : M \to \varphi_i$ gives $M \to \prod_i \varphi_i$ |
| `ContinuousLinearMap.proj` | the projection $\prod_i \varphi_i \to \varphi_i$ |
| `ContinuousLinearMap.single` | the inclusion $\varphi_i \to \prod_i \varphi_i$ |
| `ContinuousLinearMap.piMap` | a family $f_i : \varphi_i \to \psi_i$ gives $\prod_i \varphi_i \to \prod_i \psi_i$ |
| `Pi.compRightL` | for $f : \alpha \to \iota$, the map $x \mapsto x \circ f$ |

The universal properties are bijections. `ContinuousLinearMap.prodEquiv` identifies pairs of maps into $M_2$ and $M_3$ with maps into $M_2 \times M_3$. `ContinuousLinearMap.coprodEquiv` is the linear equivalence between pairs of maps out of $M_1$ and $M_2$ and maps out of $M_1 \times M_2$. The extensionality lemma `ContinuousLinearMap.prod_ext` says that two maps out of a product are equal when they agree after `ContinuousLinearMap.inl` and after `ContinuousLinearMap.inr`. The simp lemmas `ContinuousLinearMap.fst_comp_prod`, `ContinuousLinearMap.snd_comp_prod` and `ContinuousLinearMap.coprod_comp_inl` compute the composites.

The kernel and range lemmas follow the linear ones: `ContinuousLinearMap.ker_prod`, `ContinuousLinearMap.range_prod_eq`, `ContinuousLinearMap.range_coprod` and `ContinuousLinearMap.ker_coprod_of_disjoint_range`. The last says that when the ranges of $f_1$ and $f_2$ are disjoint, the kernel of `ContinuousLinearMap.coprod` is the product of the kernels.

The modules `Mathlib.Topology.Algebra.Module.LinearMap`, `Mathlib.Topology.Algebra.Module.LinearMapPiProd` and `Mathlib.Topology.Algebra.Module.Equiv` have no live declarations of their own; they collect imports.

#### Restriction to submodules

The inclusion of a submodule $p$ is `Submodule.subtypeL p`, and `Submodule.isEmbedding_subtypeL` says that it is an embedding. For a closed submodule, `Submodule.isClosedEmbedding_subtypeL` gives a closed embedding. The restrictions are these.

1. `ContinuousLinearMap.domRestrict f p` is $f$ on the submodule $p$ of the domain.
2. `ContinuousLinearMap.codRestrict f p h` is $f$ with values in $p$, given a proof $h$ that $f x \in p$ for each $x$.
3. `ContinuousLinearMap.restrict f h` maps $p$ to $q$ when $f(p) \subseteq q$.
4. `ContinuousLinearMap.rangeRestrict f` is $f$ with values in its range.

The lemma `ContinuousLinearMap.restrict_eq_codRestrict_domRestrict` relates them. A right inverse gives a projection: for $f_1 : M_1 \to M_2$ and a right inverse $f_2$, the map `ContinuousLinearMap.projKerOfRightInverse f₁ f₂ h` is the projection $x \mapsto x - f_2(f_1 x)$ onto the kernel of $f_1$. It is the identity on the kernel, by `ContinuousLinearMap.projKerOfRightInverse_apply_idem`.

#### Restriction of scalars

If $R$ acts through $A$ on both modules, a continuous $A$-linear map is continuous $R$-linear. This is `ContinuousLinearMap.restrictScalars`, and it needs the instance `LinearMap.CompatibleSMul M₁ M₂ R A`. The function does not change (`ContinuousLinearMap.coe_restrictScalars`). The map `ContinuousLinearMap.restrictScalarsₗ` is the same operation as a linear map between the spaces of maps. The typical use is a complex linear map seen as a real linear map.

#### Quotients

For a submodule $S$ of a topological module $M$, the quotient $M / S$ has the quotient topology. The quotient map is `Submodule.mkQL S : M →L[R] M ⧸ S`. It is an open quotient map (`Submodule.isOpenQuotientMap_mkQL`), because the saturation of an open set $U$ is the union $\bigcup_{s \in S} (s + U)$ of open sets. A map $f$ with $S \subseteq \ker f$ descends to `Submodule.liftQL S f h : M ⧸ S →SL[σ] M₂`, and `Submodule.coe_liftQL` gives its values on classes. The quotient is Hausdorff exactly when $S$ is closed.

#### Invertible maps and the inverse

The predicate `ContinuousLinearMap.IsInvertible f` says that $f$ is the map of a continuous linear equivalence. The lemma `ContinuousLinearMap.isInvertible_iff_isHomeomorph` says that this holds exactly when $f$ is a homeomorphism. The function `ContinuousLinearMap.inverse f : M₂ →L[R] M` is the inverse when $f$ is invertible and $0$ otherwise, as `ContinuousLinearMap.inverse_of_not_isInvertible` states. This choice of a junk value makes `ContinuousLinearMap.inverse` a total function, and it is the reason most lemmas need the hypothesis `ContinuousLinearMap.IsInvertible f`.

| Lean name | Statement |
|---|---|
| `ContinuousLinearMap.inverse_equiv` | the inverse of the map of `e` is the map of the inverse equivalence |
| `ContinuousLinearMap.IsInvertible.inverse_comp_self` | $f^{-1} \circ f = \mathrm{id}$ |
| `ContinuousLinearMap.IsInvertible.self_comp_inverse` | $f \circ f^{-1} = \mathrm{id}$ |
| `ContinuousLinearMap.IsInvertible.comp` | a composite of invertible maps is invertible |
| `ContinuousLinearMap.IsInvertible.inverse_inverse` | $(f^{-1})^{-1} = f$ |
| `ContinuousLinearMap.inverse_eq_ringInverse` | for an endomorphism, `ContinuousLinearMap.inverse` agrees with `Ring.inverse` |
| `ContinuousLinearMap.inverse_id` | the inverse of the identity is the identity |

#### Idempotent maps

An idempotent map $p = p \circ p$ is a projection. The module `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent` proves that its range is closed in a $T_1$ space (`ContinuousLinearMap.IsIdempotentElem.isClosed_range`), because the range is the kernel of $\mathrm{id} - p$. The lemma `ContinuousLinearMap.IsIdempotentElem.commute_iff` says that $p$ commutes with $T$ if and only if $T$ maps the range and the kernel of $p$ into themselves.

#### Extension from a dense subspace

Let $e : E \to E_l$ be a uniform embedding with dense range and let $F$ be complete. A map $f : E \to F$ then extends to $E_l$. The extension is `ContinuousLinearMap.extend f e`. The lemma `ContinuousLinearMap.extend_eq` says that $(\mathrm{extend}\ f\ e)(e x) = f x$, and `ContinuousLinearMap.extend_unique` says that a continuous linear map with this property is the extension. The proof uses the extension of uniformly continuous maps from Chapter 3, and then checks linearity by density. This is how a map on a dense subspace of a Banach space extends to the whole space.

#### Determinant

The determinant of a continuous endomorphism is `ContinuousLinearMap.det f`, the determinant of the linear map. It is $1$ when the module is not free and finite. The lemmas `ContinuousLinearMap.det_pi` and `ContinuousLinearEquiv.det_coe_symm` compute it for a diagonal map and for an inverse.

#### Equivalences

The modules `Mathlib.Topology.Algebra.Module.Equiv.Prod`, `Mathlib.Topology.Algebra.Module.Equiv.Pi` and `Mathlib.Topology.Algebra.Module.Equiv.Submodule` contain the standard isomorphisms.

| Lean name | Statement |
|---|---|
| `ContinuousLinearEquiv.prodCongr` | $e_1$ and $e_2$ give $M_1 \times M_3 \simeq M_2 \times M_4$ |
| `ContinuousLinearEquiv.prodComm` | $M \times M_2 \simeq M_2 \times M$ |
| `ContinuousLinearEquiv.prodAssoc` | $(M \times M_2) \times M_3 \simeq M \times (M_2 \times M_3)$ |
| `ContinuousLinearEquiv.prodUnique` | $M \times M_2 \simeq M$ when $M_2$ has one element |
| `ContinuousLinearEquiv.piCongrLeft` | a bijection of index types gives an equivalence of Pi types |
| `ContinuousLinearEquiv.piCongrRight` | a family of equivalences gives an equivalence of Pi types |
| `ContinuousLinearEquiv.piFinTwo` | $\prod_{i : \mathrm{Fin}\ 2} M_i \simeq M_0 \times M_1$ |
| `ContinuousLinearEquiv.funUnique` | functions on a type with one element are the values |
| `ContinuousLinearEquiv.ofSubmodules` | an equivalence that maps $p$ onto $q$ gives $p \simeq q$ |
| `Submodule.topContEquiv` | the top submodule is the whole module |

`ContinuousLinearMap.iInfKerProjEquiv` identifies the joint kernel of the projections $\mathrm{proj}_j$ for $j \in J$ with the product over a complementary set $I$.

#### Transfer of structure

The module `Mathlib.Topology.Algebra.Module.TransferInstance` moves a topological module structure along an equivalence of types. For an additive equivalence $e : \alpha \simeq \beta$ and a topological module $\beta$, `AddEquiv.continuousLinearEquiv R e` is a continuous linear equivalence, where $\alpha$ carries the transported topology and module structure. The special case `Shrink.continuousLinearEquiv` uses the type `Shrink α` in a smaller universe. Its topology comes from the module `Mathlib.Topology.Instances.Shrink`, where `Shrink.homeomorph` is the homeomorphism $X \simeq$ `Shrink X`.

#### Common errors

1. `ContinuousLinearMap.inverse f` is $0$ when $f$ is not invertible. A rewrite with `ContinuousLinearMap.IsInvertible.inverse_comp_self` needs a proof of `ContinuousLinearMap.IsInvertible f`; without it, the goal is false in general.
2. `ContinuousLinearMap.coprod` needs `ContinuousAdd M` on the target, because the sum $f x + g y$ must be continuous. The map `ContinuousLinearMap.prod` needs no such instance.
3. `ContinuousLinearMap.extend f e` asks for `IsUniformInducing e` and `DenseRange e` only in the lemmas, not in the definition. Without them, the definition still exists, but `ContinuousLinearMap.extend_eq` does not apply.

### Exercises

1. (A) Show that `ContinuousLinearMap.coprod (ContinuousLinearMap.inl R M M₂) (ContinuousLinearMap.inr R M M₂)` is the identity of $M \times M_2$.
2. (A) Prove that the range of a continuous idempotent map on a Hausdorff topological vector space is closed, from the identity $\operatorname{range} p = \ker(\mathrm{id} - p)$.
3. (B) For a continuous linear equivalence $e$, prove that `ContinuousLinearMap.inverse` of its map is the map of the inverse equivalence, and then find the lemma in the library.
4. (B) Show that the quotient map $\mathbb{R}^2 \to \mathbb{R}^2 / L$ by a line $L$ is open, and identify the quotient with $\mathbb{R}$ by `Submodule.liftQL`.
5. (C) Use `ContinuousLinearMap.extend` to extend the map $f \mapsto \int_0^1 f$ from continuous functions to the completion of this space for the $L^1$ norm, and state which hypotheses must be checked.

### Reference

<?reference?>
