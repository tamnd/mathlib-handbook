---
title: Exact functors, maps of Ext groups and the t-structure
kind: api
modules:
  - Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
  - Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
  - Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
  - Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
  - Mathlib.Algebra.Homology.DerivedCategory.TStructure
  - Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
explains:
  E2: [CategoryTheory.Functor.mapDerivedCategory, CategoryTheory.Functor.mapDerivedCategoryFactors, CategoryTheory.Abelian.Ext.mapExactFunctor, CategoryTheory.Abelian.Ext.mapExactFunctor_comp, CategoryTheory.Adjunction.extEquiv, CategoryTheory.Functor.mapExt_bijective_of_preservesProjectiveObjects, DerivedCategory.TStructure.t, DerivedCategory.isGE_iff, DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE, DerivedCategory.Plus]
  E1: auto
families: []
requires: [V25.C04, V25.C05, V26.C02, V26.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Exact functors, maps of Ext groups and the t-structure

### Overview

An exact functor $F : A \to B$ between abelian categories sends quasi-isomorphisms of complexes to quasi-isomorphisms. So it induces a functor $D(A) \to D(B)$ on the derived categories of Section 1, and this functor is triangulated. On the groups $\operatorname{Ext}^n(X, Y)$ of Section 2 it gives maps $\operatorname{Ext}^n_A(X, Y) \to \operatorname{Ext}^n_B(FX, FY)$ that respect the composition, the classes of short exact sequences and the maps of degree $0$. For an adjunction between exact functors the Hom bijection extends to all Ext groups. For a fully faithful exact functor that preserves projective or injective objects the maps of Ext groups are bijective.

The second part of the section defines the canonical t-structure on $D(A)$. An object $X$ is in $D^{\ge n}$ if its cohomology is zero in degrees below $n$, and in $D^{\le n}$ if its cohomology is zero in degrees above $n$. The full subcategories of bounded below, bounded above and bounded objects come from it. Each object of $D^{\ge a} \cap D^{\le b}$ is the image of a complex that is strictly concentrated in degrees $a$ to $b$, a consequence of the truncations of Chapter 2, Section 6.

Throughout, $A$ and $B$ are abelian categories with derived categories, and functors are additive and preserve finite limits and finite colimits.

### The library around it

#### The functor on derived categories

The functor `CategoryTheory.Functor.mapDerivedCategory` of an exact functor $F$ goes from the derived category of $A$ to the derived category of $B$. It is obtained from the universal property of the localization, so its main data are isomorphisms that say what it does on the images of complexes:

| Lean name | Statement |
|---|---|
| `CategoryTheory.Functor.mapDerivedCategoryFactors` | $Q \circ F_D \cong F_C \circ Q$, where $F_C$ is the functor on cochain complexes |
| `CategoryTheory.Functor.mapDerivedCategoryFactorsh` | the same from the homotopy category, with the functor $Q_h$ |
| `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` | the functor commutes with the single functor in each degree |
| `CategoryTheory.Functor.mapDerivedCategoryIdIso` | the functor of the identity is the identity |
| `CategoryTheory.Functor.mapDerivedCategoryCompIso` | the functor of a composition is the composition |
| `CategoryTheory.NatTrans.mapDerivedCategory` | a natural transformation of exact functors gives one of the induced functors |

Instances make the functor commute with the shift and make it triangulated, by `CategoryTheory.Functor.instIsTriangulatedDerivedCategoryMapDerivedCategory`, and they give linearity when $F$ is linear. The isomorphisms commute with the shift too. The module does not build the pseudofunctor from abelian categories to triangulated categories; it gives only the isomorphisms for the identity and for compositions.

#### Maps of Ext groups

The map `CategoryTheory.Abelian.Ext.mapExactFunctor` sends an element of $\operatorname{Ext}^n(X, Y)$ to an element of $\operatorname{Ext}^n(FX, FY)$. The bundled forms are `CategoryTheory.Functor.mapExtAddHom`, an additive map, and `CategoryTheory.Functor.mapExtLinearMap`, an $R$-linear map for a linear functor. The compatibilities are:

| Lean name | Statement |
|---|---|
| `CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀` | on $\operatorname{Ext}^0$ the map is $f \mapsto F(f)$ |
| `CategoryTheory.Abelian.Ext.mapExactFunctor₀` | the same as an equation of functions through the identification of $\operatorname{Ext}^0$ with Hom |
| `CategoryTheory.Abelian.Ext.mapExactFunctor_comp` | the map respects the Yoneda product $\alpha \cdot \beta$ |
| `CategoryTheory.Abelian.Ext.mapExactFunctor_extClass` | the class of a short exact sequence goes to the class of its image |
| `CategoryTheory.Abelian.Ext.id_mapExactFunctor` | the identity functor gives the identity |
| `CategoryTheory.Abelian.Ext.comp_mapExactFunctor` | a composition of functors gives the composition of the maps |
| `CategoryTheory.DerivedCategory.map_triangleOfSESδ` | the functor on derived categories sends the connecting morphism of a short exact sequence to the connecting morphism of the image |

The map needs `CategoryTheory.HasExt` for both categories, so that the Ext groups are small. An instance shows that the morphism groups in the derived category of $B$ between images of objects of $A$ are small, so the construction of Section 2 applies to them.

#### Adjunctions and bijections

Let $F : A \to B$ and $G : B \to A$ be exact with an adjunction $F \dashv G$. The isomorphism `CategoryTheory.Adjunction.extEquiv` is
$$\operatorname{Ext}^n_B(FX, Y) \cong \operatorname{Ext}^n_A(X, GY),$$
and `CategoryTheory.Adjunction.extLinearEquiv` is its linear form. On degree $0$ it is the Hom bijection of the adjunction, by `CategoryTheory.Adjunction.extEquiv_mk₀`, and it is natural in both variables by the lemmas `CategoryTheory.Adjunction.extEquiv_naturality_left` and `CategoryTheory.Adjunction.extEquiv_naturality_right`.

The module `Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective` has two theorems. If $F$ is exact, full and faithful, $A$ has enough projectives and $F$ preserves projective objects, then the maps of Ext groups are bijective, by `CategoryTheory.Functor.mapExt_bijective_of_preservesProjectiveObjects`. The dual statement with injectives is `CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects`.

#### The canonical t-structure

The t-structure `DerivedCategory.TStructure.t` on the derived category has the predicates `DerivedCategory.IsGE` and `DerivedCategory.IsLE` as its classes $D^{\ge n}$ and $D^{\le n}$. They are type classes, and they are computed with the homology functors:

| Lean name | Statement |
|---|---|
| `DerivedCategory.isGE_iff` | $X$ is in $D^{\ge n}$ iff $H^i(X) = 0$ for $i < n$ |
| `DerivedCategory.isLE_iff` | $X$ is in $D^{\le n}$ iff $H^i(X) = 0$ for $i > n$ |
| `DerivedCategory.isGE_Q_obj_iff` | the image of a complex is in $D^{\ge n}$ iff the complex satisfies `CochainComplex.IsGE` |
| `DerivedCategory.isLE_Q_obj_iff` | the same for $D^{\le n}$ |
| `DerivedCategory.exists_iso_Q_obj_of_isGE` | an object of $D^{\ge n}$ is the image of a complex that is strictly zero below $n$ |
| `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE` | an object of $D^{\ge a} \cap D^{\le b}$ is the image of a complex strictly concentrated in $[a, b]$ |
| `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE` | an object of $D^{\ge n} \cap D^{\le n}$ is a single complex in degree $n$ |

Instances say that the single complex in degree $n$ is in $D^{\ge n}$ and in $D^{\le n}$. The full subcategories are `DerivedCategory.Plus`, `DerivedCategory.Minus` and `DerivedCategory.Bounded`, with the inclusions `DerivedCategory.Plus.ι`, `DerivedCategory.Minus.ι` and `DerivedCategory.Bounded.ι`. The bounded below derived category of Section 1 is this `DerivedCategory.Plus`.

The module `Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure` proves `CategoryTheory.HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE`: if $K$ and $L$ each have cohomology in a single degree, then the morphisms from $K$ to the shifts of $L$ in the derived category form small types. An instance gives the case of degree $0$.

#### Common errors

1. `CategoryTheory.Functor.mapDerivedCategory` needs the instances that $F$ preserves finite limits and finite colimits. An additive functor that is only right exact does not give this functor; its derived functor needs the resolutions of Chapter 4.
2. `DerivedCategory.IsGE` is a condition on homology. It does not say that a chosen complex is zero below $n$. To get such a complex, use `DerivedCategory.exists_iso_Q_obj_of_isGE`, which gives a new complex up to isomorphism.
3. The map of Ext groups is not injective in general, even for a faithful functor. The forgetful functor from $\mathbb{Z}[x]$-modules to abelian groups sends a nonsplit extension of $\mathbb{Z}$ by $\mathbb{Z}$, with $x$ acting as a nilpotent matrix, to a split one. The bijectivity results need $F$ full and faithful and a condition on projective or injective objects.

### Exercises

1. (A) Show that the image of $\operatorname{Ext}^0(X, Y)$ under the map of the identity functor is the identity, from `CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀`.
2. (A) For a ring $R$ and the forgetful functor from $R$-modules to abelian groups, say whether it induces a functor on derived categories, and why.
3. (B) Use `CategoryTheory.Abelian.Ext.mapExactFunctor_extClass` to show that an exact functor sends a split short exact sequence to a sequence with zero Ext class.
4. (B) Show that an object of the derived category that is in $D^{\ge 1}$ and in $D^{\le 0}$ is zero.
5. (B) Show that the complex $\mathbb{Z}/4 \xrightarrow{2} \mathbb{Z}/4$ of abelian groups in degrees $0$ and $1$ is in $D^{\ge 0} \cap D^{\le 1}$, but that its image in the derived category is isomorphic to no single complex.
6. (C) For an exact fully faithful functor with an exact right adjoint, deduce from `CategoryTheory.Adjunction.extEquiv` that the maps of Ext groups are bijective.

### Reference

<?reference?>
