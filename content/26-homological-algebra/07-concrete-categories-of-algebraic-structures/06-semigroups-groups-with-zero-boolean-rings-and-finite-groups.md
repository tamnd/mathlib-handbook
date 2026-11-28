---
title: Semigroups, groups with zero, Boolean rings and finite groups
kind: api
modules:
  - Mathlib.Algebra.Category.Semigrp.Basic
  - Mathlib.Algebra.Category.GrpWithZero
  - Mathlib.Algebra.Category.BoolRing
  - Mathlib.Algebra.Category.Grp.FiniteGrp
  - Mathlib.Algebra.Category.Grp.IsFinite
explains:
  E2: [Semigrp, MagmaCat, MulEquiv.toSemigrpIso, mulEquivIsoSemigrpIso, GrpWithZero, BoolRing, boolRingCatEquivBoolAlg, FiniteGrp, AddCommGrpCat.instIsSerreClassIsFinite]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V25.C02, V05, V04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Semigroups, groups with zero, Boolean rings and finite groups

### Overview

Section 1 builds the categories of monoids, groups and rings with one pattern: a bundled object, a wrapped morphism, and forgetful functors. This section treats the smaller categories of algebra that follow the same pattern: magmas and semigroups, groups with zero, Boolean rings and finite groups. Each is a short file, and most of its declarations are the standard lemmas of a concrete category. A reader who knows the pattern of `MonCat` can read these files at once.

Two facts in these files carry mathematical content. The first is the equivalence between Boolean rings and Boolean algebras. The second is that the finite abelian groups form a Serre class in $\mathbf{Ab}$: they are closed under subobjects, quotients and extensions. Serre classes appear in homological algebra when one computes modulo a class of objects, for example modulo finite groups.

### The library around it

#### The pattern of a concrete category

Each category in this section has the same set of declarations, with the same names. The table shows them for `Semigrp`:

| Lean name | Statement |
|---|---|
| `Semigrp.of` | bundles a type with a semigroup structure |
| `Semigrp.carrier` | the underlying type of an object |
| `Semigrp.Hom` | the structure that wraps a `MulHom` |
| `Semigrp.Hom.hom` | the homomorphism of a morphism |
| `Semigrp.ofHom` | the morphism of a homomorphism |
| `Semigrp.hom_ofHom` | `(ofHom f).hom = f` |
| `Semigrp.ofHom_hom` | `ofHom f.hom = f` |
| `Semigrp.hom_ext` | morphisms with equal homomorphisms are equal |
| `Semigrp.hom_comp` | the homomorphism of `f ≫ g` is `g.hom.comp f.hom` |
| `Semigrp.coe_comp` | the function of `f ≫ g` is the composite of the functions |
| `Semigrp.comp_apply` | `(f ≫ g) x = g (f x)` |

The wrapper `Semigrp.Hom` exists for the reason given in Section 1: if a morphism were literally a `MulHom`, the composition of the category and the composition of homomorphisms would be two different operations on one type, and their simp lemmas would conflict. The instance `Semigrp.instConcreteCategoryMulHomCarrier` makes the category concrete, so the general lemmas of concrete categories also apply.

#### Magmas and semigroups

A magma is a set with a binary operation and no axioms. A semigroup is a magma whose operation is associative. The file `Mathlib.Algebra.Category.Semigrp.Basic` defines `MagmaCat`, with objects `MagmaCat.of M` for a type with `Mul M`, and `Semigrp`, with objects `Semigrp.of M` for a type with `Semigroup M`. The morphisms of both are the maps that preserve the operation, the `MulHom` of the library. The additive twins are `AddMagmaCat` and `AddSemigrp`.

The forgetful functor from semigroups to magmas is `Semigrp.hasForgetToMagmaCat`. It is full, by `Semigrp.forget₂_full`, because a morphism of semigroups is only a map that preserves the operation, and the associativity is a property of the objects. So $\mathbf{Semigrp}$ is a full subcategory of $\mathbf{Magma}$.

The file also relates isomorphisms in the category to isomorphisms of the structures. `MulEquiv.toSemigrpIso` sends a multiplicative equivalence $e \colon X \simeq Y$ to an isomorphism of objects, and `CategoryTheory.Iso.semigrpIsoToMulEquiv` goes back. Together they give `mulEquivIsoSemigrpIso`, an isomorphism of types between `X ≃* Y` and `Semigrp.of X ≅ Semigrp.of Y`. Proof: the two maps are mutually inverse because a morphism and its homomorphism determine each other, by `Semigrp.hom_ext`. The magma versions are `MulEquiv.toMagmaCatIso`, `CategoryTheory.Iso.magmaCatIsoToMulEquiv` and `mulEquivIsoMagmaIso`. The forgetful functors to types reflect isomorphisms, by `Semigrp.forgetReflectsIsos` and `MagmaCat.forgetReflectsIsos`: a bijective homomorphism has an inverse map, and the inverse preserves the operation.

Section 1 uses `Semigrp` for the adjunction `MonCat.adjoinOneAdj`, which adjoins a unit to a semigroup. The file records as a TODO that limits and free objects of semigroups are not yet in the library.

#### Groups with zero

A group with zero is a monoid with an element $0$ such that $0 \neq 1$, $0 \cdot x = x \cdot 0 = 0$, and each nonzero element has an inverse. A field is an example, with its multiplication. The file `Mathlib.Algebra.Category.GrpWithZero` defines the category `GrpWithZero`, whose morphisms are the monoid homomorphisms that preserve $0$, the `MonoidWithZeroHom` of the library. The lemma `GrpWithZero.hom_comp` states that composition is `MonoidWithZeroHom.comp`. The constructor `GrpWithZero.of` bundles a type, and `GrpWithZero.Iso.mk` builds an isomorphism from a multiplicative equivalence.

There are two forgetful functors. `GrpWithZero.hasForgetToMon` keeps the monoid. `GrpWithZero.hasForgetToBipointed` keeps the set with the two points $0$ and $1$, an object of the category `Bipointed`. A morphism preserves both points, so this functor is well defined. The category is declared as a large category, `GrpWithZero.instLargeCategory`.

#### Boolean rings

A Boolean ring is a ring in which $x^2 = x$ for each $x$. Each Boolean ring is commutative and has characteristic $2$: from $(x + y)^2 = x + y$ one gets $xy + yx = 0$, and with $y = x$ one gets $2x = 0$, so $xy = -yx = yx$. The file `Mathlib.Algebra.Category.BoolRing` defines the category `BoolRing`, with objects `BoolRing.of R` for a type with `BooleanRing R`, and morphisms the ring homomorphisms. The functor `BoolRing.hasForgetToCommRing` sends a Boolean ring to its commutative ring. `BoolRing.Iso.mk` builds an isomorphism from a ring equivalence.

The main result is the equivalence `boolRingCatEquivBoolAlg : BoolRing ≌ BoolAlg` with the category of Boolean algebras. It is built from the two functors `BoolRing.hasForgetToBoolAlg` and `BoolAlg.hasForgetToBoolRing`, and the lemmas `boolRingCatEquivBoolAlg_functor` and `boolRingCatEquivBoolAlg_inverse` name them. The dictionary is
$$x \wedge y = xy, \qquad x \vee y = x + y + xy, \qquad x^{c} = 1 + x$$
in one direction, and
$$x + y = (x \wedge y^{c}) \vee (x^{c} \wedge y), \qquad xy = x \wedge y$$
in the other. On types the two directions are the synonyms `AsBoolAlg` and `AsBoolRing`. A ring homomorphism preserves $xy$ and $x + y + xy$ and sends $1$ to $1$, so it is a morphism of bounded lattices. A morphism of Boolean algebras preserves the complement, so it preserves the symmetric difference, and it is a ring homomorphism. So the two functors are inverse on morphisms as well as on objects.

#### Finite groups

The file `Mathlib.Algebra.Category.Grp.FiniteGrp` defines `FiniteGrp`, the category of finite groups. An object is a structure with a group `FiniteGrp.toGrp`, an object of `GrpCat`, and a proof `FiniteGrp.isFinite` that its carrier is finite. The morphisms are those of `GrpCat`, so `FiniteGrp` is a full subcategory. The constructors `FiniteGrp.of` and `FiniteGrp.ofHom` take a type with `Group` and `Finite` instances and a `MonoidHom`. The additive twin is `FiniteAddGrp`. Volume 14 uses `FiniteGrp` to build profinite groups as limits of finite groups.

#### The Serre class of finite abelian groups

Let $\mathcal{A}$ be an abelian category. A Serre class is a class $\mathcal{S}$ of objects, closed under isomorphisms, that contains $0$ and such that, for each short exact sequence $0 \to A \to B \to C \to 0$, the object $B$ is in $\mathcal{S}$ if and only if $A$ and $C$ are in $\mathcal{S}$. The predicate is `CategoryTheory.ObjectProperty.IsSerreClass`.

The file `Mathlib.Algebra.Category.Grp.IsFinite` defines `AddCommGrpCat.isFinite`, the property of an abelian group to be finite, with `AddCommGrpCat.prop_isFinite_iff` as its unfolding. The instance `AddCommGrpCat.instIsSerreClassIsFinite` proves that it is a Serre class. Proof: for $0 \to A \to B \to C \to 0$ exact, $A$ injects into $B$ and $C$ is a quotient of $B$, so $B$ finite gives $A$ and $C$ finite. Conversely $|B| = |A| \cdot |C|$, because $B$ is the disjoint union of the cosets of $A$, which are in bijection with $C$.

#### Common errors

1. `Semigrp.of M` needs an instance `Semigroup M`, and `MagmaCat.of M` needs only `Mul M`. A monoid gives both through the instance path, but the morphisms of `Semigrp` do not need to preserve $1$.
2. The morphisms of `GrpWithZero` must preserve $0$. A monoid homomorphism between groups with zero that does not send $0$ to $0$, such as the constant map $1$, is not a morphism of `GrpWithZero`.
3. The operations of the Boolean algebra of a Boolean ring live on the synonym `AsBoolAlg R`, not on the ring $R$ itself. Writing `x ⊔ y` for two elements of $R$ asks for a lattice structure that $R$ does not have.

### Exercises

1. (A) Show that the map $(\mathbb{N}, \max) \to (\mathbb{N}, +)$, $n \mapsto n$, is not a morphism of magmas, and find all morphisms of magmas $(\mathbb{N}, +) \to (\mathbb{N}, \max)$.
2. (A) Show that $\mathbb{Z}/2$ is a Boolean ring, and that $\mathcal{P}(X)$ with symmetric difference and intersection is a Boolean ring for each set $X$.
3. (B) Prove that a morphism of groups with zero sends nonzero elements to nonzero elements. Give a morphism $\mathbb{F}_4 \to \{0, 1\}$ of groups with zero, and deduce that a morphism need not be injective.
4. (B) Describe the image of the finite Boolean ring $(\mathbb{Z}/2)^n$ under the equivalence `boolRingCatEquivBoolAlg`, and deduce that each finite Boolean algebra has $2^n$ elements.
5. (B) Show that the finitely generated abelian groups form a Serre class in $\mathbf{Ab}$, and that the torsion free abelian groups do not.
6. (C) Prove that the morphisms of Boolean rings $R \to \mathbb{Z}/2$ correspond to the prime ideals of $R$, and that each prime ideal of a Boolean ring is maximal.

### Reference

<?reference?>
