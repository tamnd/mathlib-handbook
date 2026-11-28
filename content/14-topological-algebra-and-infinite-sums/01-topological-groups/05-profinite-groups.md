---
title: Profinite groups
kind: api
modules:
  - Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
  - Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
  - Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
explains:
  E2: [ProfiniteGrp, ProfiniteGrp.of, ProfiniteGrp.limit, ProfiniteGrp.isoLimittoFiniteQuotientFunctor, ProfiniteGrp.toLimit_injective, ProfiniteGrp.ProfiniteCompletion.completion, ProfiniteGrp.ProfiniteCompletion.adjunction, ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite]
  E1: auto
families: []
requires: [V05, V13.C01, V13.C04, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Profinite groups

### Overview

A profinite group is a topological group that is compact, Hausdorff and totally disconnected. The $p$-adic integers $\mathbb{Z}_p$ and the Galois group of an infinite Galois extension are examples. Each profinite group is the limit of its finite quotients, and each limit of finite groups is profinite. So a profinite group is a group that finite groups approximate.

Mathlib treats profinite groups as a category, `ProfiniteGrp`, built on the category `Profinite` of profinite spaces. This section describes the objects and morphisms of the category, its limits, the theorem that a profinite group is the limit of its finite quotients, and the profinite completion of a discrete group.

### The library around it

#### Objects and morphisms

An object of `ProfiniteGrp` is a structure with three fields: a profinite space `toProfinite`, a `Group` structure on it, and a proof of `IsTopologicalGroup`. The coercion to a type is `instCoeSortProfiniteGrpType`. There are three ways to build an object.

1. `ProfiniteGrp.of G` takes a type `G` with a group structure, a topology, and the instances `IsTopologicalGroup G`, `CompactSpace G` and `TotallyDisconnectedSpace G`. Hausdorff follows from the other conditions, so it is not an argument.
2. `ProfiniteGrp.ofProfinite G` takes an object `G : Profinite` and a group structure on it.
3. `ProfiniteGrp.ofFiniteGrp` turns a finite group (an object of `FiniteGrp`) with the discrete topology into a profinite group.

The library also builds new objects from old ones. `ProfiniteGrp.ofClosedSubgroup` turns a closed subgroup (a `ClosedSubgroup`) into a profinite group, because a closed subset of a compact space is compact. `ProfiniteGrp.pi` is the product of a family of profinite groups. `ProfiniteGrp.ofContinuousMulEquiv` transports the structure along a continuous isomorphism `G ≃ₜ* H`.

A morphism `A ⟶ B` is a continuous group homomorphism. The structure `ProfiniteGrp.Hom` wraps a `ContinuousMonoidHom`, and `ProfiniteGrp.Hom.hom` unwraps it. The usual lemmas for a concrete category hold.

| Lean name | Statement |
|---|---|
| `ProfiniteGrp.ofHom` | a continuous homomorphism of types gives a morphism of objects |
| `ProfiniteGrp.hom_ofHom` | `Hom.hom (ofHom f) = f` |
| `ProfiniteGrp.ofHom_hom` | `ofHom (Hom.hom f) = f` |
| `ProfiniteGrp.hom_ext` | two morphisms are equal if their homomorphisms are equal |
| `ProfiniteGrp.hom_comp` | the homomorphism of `f ≫ g` is `(Hom.hom g).comp (Hom.hom f)` |
| `ProfiniteGrp.coe_comp` | the function of `f ≫ g` is the composite of the functions |
| `ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso` | a continuous isomorphism gives an isomorphism in the category |

The forgetful functors go to `Profinite`, to `GrpCat` and to types. The instance names are long, because Lean generates them. The instance `ProfiniteGrp.instHasForget₂ContinuousMonoidHomCarrierToTopTotallyDisconnectedSpaceToProfiniteProfiniteContinuousMap` gives the functor to `Profinite`, and the library proves that this functor is faithful, reflects isomorphisms and preserves limits. A continuous bijective homomorphism of profinite groups is therefore an isomorphism, because a continuous bijection from a compact space to a Hausdorff space is a homeomorphism.

#### Limits

The category has all small limits. For a functor `F : J ⥤ ProfiniteGrp`, the object `ProfiniteGrp.limit F` is the subgroup `ProfiniteGrp.limitConePtAux F` of the product $\prod_j F(j)$ that consists of the compatible families. This subgroup is closed, so it is compact. The cone is `ProfiniteGrp.limitCone`, and `ProfiniteGrp.limitConeIsLimit` proves the universal property. The instance `ProfiniteGrp.instHasLimit` records the result. Elements of the limit are equal when all their coordinates are equal: this is `ProfiniteGrp.limit_ext`. The lemmas `ProfiniteGrp.limit_one_val` and `ProfiniteGrp.limit_mul_val` compute the coordinates of $1$ and of a product.

#### A profinite group is the limit of its finite quotients

Let $P$ be a profinite group. For each open normal subgroup $U$ the quotient $P/U$ is finite, because $P$ is compact and the cosets of $U$ form an open cover by disjoint sets. The module `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits` builds the diagram of these quotients.

1. `ProfiniteGrp.toFiniteQuotientFunctor P` sends $U$ to the finite group $P/U$, and `ProfiniteGrp.diagram P` is the same functor with values in `ProfiniteGrp`.
2. `ProfiniteGrp.proj U : P ⟶ P.diagram.obj U` is the quotient map.
3. `ProfiniteGrp.cone P` is the cone with vertex $P$ and these projections.
4. `ProfiniteGrp.toLimit P : P ⟶ ProfiniteGrp.limit P.diagram` is the induced morphism.

The main theorem is `ProfiniteGrp.isoLimittoFiniteQuotientFunctor`, an isomorphism $P \cong \lim_U P/U$. The proof has two parts. `ProfiniteGrp.toLimit_injective` uses that the open normal subgroups form a basis of neighbourhoods of $1$ in a compact totally disconnected group, and that $P$ is Hausdorff. So their intersection is $\{1\}$. `ProfiniteGrp.toLimit_surjective` uses compactness: the image of `ProfiniteGrp.toLimit` is compact, hence closed, and it is dense, because it maps onto each finite quotient. The results `ProfiniteGrp.isIso_toLimit` and `ProfiniteGrp.isLimitCone` state the same theorem in the language of categories. The form `ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor` gives the isomorphism as a `ContinuousMulEquiv`.

#### The profinite completion

Let $G$ be a group with no topology, an object of `GrpCat`. Its profinite completion is

$$\widehat{G} = \lim_{N} G/N,$$

where $N$ runs over the normal subgroups of finite index, ordered by inclusion. The module `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion` builds it in these steps.

| Lean name | Statement |
|---|---|
| `ProfiniteGrp.ProfiniteCompletion.finiteGrpDiagram` | the functor $N \mapsto G/N$ into `FiniteGrp` |
| `ProfiniteGrp.ProfiniteCompletion.diagram` | the same functor into `ProfiniteGrp` |
| `ProfiniteGrp.ProfiniteCompletion.completion` | the limit $\widehat{G}$ |
| `ProfiniteGrp.ProfiniteCompletion.eta` | the homomorphism $\eta : G \to \widehat{G}$ |
| `ProfiniteGrp.ProfiniteCompletion.denseRange` | the image of $\eta$ is dense |
| `ProfiniteGrp.ProfiniteCompletion.lift` | a homomorphism $G \to P$ to a profinite group extends to $\widehat{G} \to P$ |
| `ProfiniteGrp.ProfiniteCompletion.lift_eta` | the extension agrees with the homomorphism on $G$ |
| `ProfiniteGrp.ProfiniteCompletion.lift_unique` | two morphisms from $\widehat{G}$ that agree on $G$ are equal |

These facts make the completion a functor `ProfiniteGrp.profiniteCompletion : GrpCat ⥤ ProfiniteGrp` that is left adjoint to the forgetful functor. The adjunction is `ProfiniteGrp.ProfiniteCompletion.adjunction`, and its bijection on morphisms is `ProfiniteGrp.ProfiniteCompletion.homEquiv`.

The proof of `ProfiniteGrp.ProfiniteCompletion.lift` uses the subgroups `ProfiniteGrp.ProfiniteCompletion.preimage f H`: for an open normal subgroup $H$ of $P$, the preimage $f^{-1}(H)$ has finite index in $G$. The quotient map $G/f^{-1}(H) \to P/H$ is `ProfiniteGrp.ProfiniteCompletion.quotientMap`. The bridge between the two kinds of subgroup is `OpenNormalSubgroup.toFiniteIndexNormalSubgroup`: in a compact group each open normal subgroup has finite index. This map is injective and monotone.

The map $\eta$ is injective exactly when $G$ is residually finite, that is, when the finite index normal subgroups of $G$ meet in $\{1\}$. This is `ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite`, with the predicate `Group.ResiduallyFinite`. The form `ProfiniteGrp.ProfiniteCompletion.mono_eta_iff_residuallyFinite` says the same in the category. For $G = \mathbb{Z}$ the map is injective, and $\widehat{\mathbb{Z}} \cong \prod_p \mathbb{Z}_p$.

Each definition has an additive twin through `to_additive`, such as `ProfiniteAddGrp` and `OpenNormalAddSubgroup.toFiniteIndexNormalAddSubgroup`.

#### Common errors

1. An element `x : P` for `P : ProfiniteGrp` has the type `↑P.toProfinite.toTop`. Lemmas about groups apply, but a goal can show this long form. Use `ProfiniteGrp.coe_of` to go back to the type in `ProfiniteGrp.of G`.
2. A morphism `f : A ⟶ B` is not a function. Apply `ProfiniteGrp.Hom.hom f` first, or use the coercion that `ProfiniteGrp.instCoeFunHomForallCarrierToTopTotallyDisconnectedSpaceToProfinite` gives.
3. The completion is defined for an object of `GrpCat`, not for a type. Write `GrpCat.of G` to apply it to a group type `G`.

### Exercises

1. (A) Show that a finite group with the discrete topology satisfies the three instances that `ProfiniteGrp.of` needs.
2. (A) Use `ProfiniteGrp.ofClosedSubgroup` to explain why the center of a profinite group is a profinite group.
3. (B) Prove that the open normal subgroups of $\mathbb{Z}_p$ are the subgroups $p^n \mathbb{Z}_p$, and describe the diagram of `ProfiniteGrp.diagram` for $\mathbb{Z}_p$.
4. (B) Give a group that is not residually finite, and deduce from `ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite` that $\eta$ is not injective for it.
5. (C) Prove that a profinite group with the discrete topology is finite, and deduce that $\eta : \mathbb{Z} \to \widehat{\mathbb{Z}}$ is not surjective.

### Reference

<?reference?>
