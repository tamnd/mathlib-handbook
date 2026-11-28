---
title: Limits, global sections and monoidal structures
kind: api
modules:
  - Mathlib.CategoryTheory.Sites.Limits
  - Mathlib.CategoryTheory.Sites.ConstantSheaf
  - Mathlib.CategoryTheory.Sites.GlobalSections
  - Mathlib.CategoryTheory.Sites.SheafHom
  - Mathlib.CategoryTheory.Sites.CartesianMonoidal
  - Mathlib.CategoryTheory.Sites.CartesianClosed
  - Mathlib.CategoryTheory.Sites.Monoidal
explains:
  E2: [CategoryTheory.Sheaf.isSheaf_of_isLimit, CategoryTheory.Sheaf.isColimitSheafifyCocone, CategoryTheory.constantSheaf, CategoryTheory.constantSheafAdj, CategoryTheory.Sheaf.Γ, CategoryTheory.Sheaf.ΓNatIsoLim, CategoryTheory.sheafHom, CategoryTheory.sheafHomSectionsEquiv, CategoryTheory.Sheaf.tensorProd_isSheaf, CategoryTheory.Sheaf.monoidalCategory]
  E1: auto
families: []
requires: [V24.C04, V24.C05, V24.C07, V25.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Limits, global sections and monoidal structures

### Overview

The sheaves on a site $(C, J)$ with values in a category $A$ form a full subcategory of the presheaves. Limits of presheaves are computed objectwise, and a limit of sheaves is again a sheaf, because the sheaf condition is itself a limit condition and limits commute with limits. So the inclusion of sheaves creates limits. Colimits are different: the objectwise colimit of sheaves need not be a sheaf, and the colimit in the sheaf category is the sheafification of the presheaf colimit. This section gives these two facts and then the first constructions that use them.

The constant sheaf on an object $M$ of $A$ is the sheafification of the constant presheaf. It is left adjoint to the global sections functor. When $C$ has a terminal object $T$, the global sections of $F$ are $F(T)$, and in general they are the limit of $F$ over $C^{\mathrm{op}}$. The morphisms between two sheaves form a sheaf of types, whose sections over $X$ are the morphisms between the restrictions to the slice over $X$. Finally, the section puts monoidal structures on the sheaf category: the cartesian structure from finite products, a closed structure when the presheaves are cartesian closed, and a general monoidal structure that the sheafification functor carries from the presheaves when the class $W_J$ of Section 5 is stable under tensor products.

The section uses the limits, adjunctions and monoidal categories of Volume 24, the sheafification of Section 3 and the localization of Chapter 4. Chapter 10 uses the constant sheaf and global sections for sheaf cohomology.

### The library around it

**Limits.** The module `Mathlib.CategoryTheory.Sites.Limits` starts from a cone $E$ over a diagram of sheaves that is a limit cone of presheaves. The cone `Sheaf.multiforkEvaluationCone` and the limit `Sheaf.isLimitMultiforkOfIsLimit` check the multifork form of the sheaf condition of Section 2 for its point, and `Sheaf.isSheaf_of_isLimit` concludes that the limit presheaf is a sheaf. The instances `Sheaf.createsLimitsOfShape` and `Sheaf.createsLimits` say that `sheafToPresheaf J D` creates limits. Then `Sheaf.instHasLimitsOfShape`, `Sheaf.hasLimitsOfSize`, `Sheaf.instHasFiniteLimits` and `Sheaf.instHasFiniteProducts` give the limits of sheaves, and `Sheaf.instPreservesFiniteLimitsFunctorOppositeSheafToPresheafOfHasFiniteLimits` says that the inclusion preserves finite limits.

For colimits, the module assumes `HasWeakSheafify J D`. For a colimit cocone $E$ of presheaves over a diagram of sheaves, `Sheaf.sheafifyCocone E` sheafifies the cocone point, and `Sheaf.isColimitSheafifyCocone` proves that it is a colimit cocone of sheaves. This gives `Sheaf.instHasColimitsOfShape`, `Sheaf.instHasColimitsOfSize`, `Sheaf.instHasFiniteColimits` and `Sheaf.instHasFiniteCoproducts`. When each presheaf colimit of the diagram is already a sheaf, `Sheaf.createsColimitOfIsSheaf` says that the inclusion creates the colimit.

**The constant sheaf.** The module `Mathlib.CategoryTheory.Sites.ConstantSheaf` works with a terminal object $T$ of $C$. The adjunction `constantPresheafAdj D hT` says that the constant presheaf functor is left adjoint to evaluation at $T$: a morphism from the constant presheaf on $M$ to $P$ is the same thing as a morphism $M \to P(T)$, because each object maps uniquely to $T$. The functor `constantSheaf J D` is the composite of the constant presheaf functor with sheafification, and `constantSheafAdj J D hT` composes the two adjunctions:
$$\operatorname{Hom}_{\mathrm{Sh}}(\underline{M}, F) \cong \operatorname{Hom}_A(M, F(T)).$$
The class `Sheaf.IsConstant J F` says that $F$ is in the essential image of `constantSheaf J D`. If the constant sheaf functor is fully faithful, `Sheaf.isConstant_iff_isIso_counit_app` says that $F$ is constant exactly when the counit of the adjunction at $F$ is an isomorphism. The lemmas `Sheaf.isConstant_iff_mem_essImage` and `Sheaf.isConstant_of_iso` give other forms. The isomorphism `constantCommuteCompose` says that the constant sheaf functor commutes with the composition with a functor $U : D \to B$ that preserves sheafification, and `equivCommuteConstant` says that it commutes with the equivalence of sheaf categories of a dense subsite of Chapter 9. Then `Sheaf.isConstant_iff_of_equivalence` transports the property along that equivalence.

**Global sections.** In `Mathlib.CategoryTheory.Sites.GlobalSections`, the class `HasGlobalSectionsFunctor J A` asks that the constant sheaf functor has a right adjoint, and `Sheaf.Γ J A` is that right adjoint, with the adjunction `constantSheafΓAdj J A`. This definition works without a terminal object. Two instances give the class: `hasGlobalSectionsFunctor_of_hasTerminal` for a site with a terminal object, and `hasGlobalSectionsFunctor_of_hasLimitsOfShape` when $A$ has limits of shape $C^{\mathrm{op}}$. The comparisons are:

1. `Sheaf.ΓNatIsoSheafSections`: on a site with a terminal object $T$, the functor $\Gamma$ is isomorphic to the sections over $T$.
2. `Sheaf.ΓNatIsoLim`: $\Gamma$ is isomorphic to the limit of the underlying presheaf. The cone `Sheaf.coneΓ` and the proof `Sheaf.isLimitConeΓ` say that $\Gamma(F)$ is a limit even when $A$ does not have all limits of that shape.
3. `Sheaf.ΓObjEquivSections` and `Sheaf.ΓNatIsoSectionsFunctor`: for sheaves of types, $\Gamma(F)$ is the type of sections of the presheaf, that is the compatible families of elements.
4. `Sheaf.ΓObjEquivHom` and `Sheaf.ΓNatIsoCoyoneda`: for sheaves of types, $\Gamma(F)$ is the type of morphisms from the constant sheaf on a one point type, a terminal sheaf, to $F$.

The equivalence `Sheaf.ΓHomEquiv` and its four naturality lemmas give the adjunction in the form of morphisms from the constant presheaf, and `Sheaf.ΓRes` and `Sheaf.natTransΓRes` are the restriction maps from $\Gamma$ to the sections over an object.

**The sheaf of morphisms.** The module `Mathlib.CategoryTheory.Sites.SheafHom` defines, for presheaves $F$ and $G$, the presheaf of types `presheafHom F G`. Its value at $X$ is the type of morphisms between the restrictions of $F$ and $G$ to `Over X`. The equivalence `presheafHomSectionsEquiv` identifies its sections with the morphisms $F \to G$. The lemma `presheafHom_isSheafFor` checks the sheaf condition for one sieve from a limit property of $G$, and `Presheaf.IsSheaf.hom` concludes that `presheafHom F G` is a sheaf when $G$ is a sheaf. For two sheaves, `sheafHom F G` is this sheaf, `sheafHom'Iso` compares its underlying presheaf with `presheafHom`, and `sheafHomSectionsEquiv` identifies the global sections with the morphisms $F \to G$ of sheaves.

**Cartesian and closed structures.** If $A$ has a `CartesianMonoidalCategory` structure, the presheaves on $C$ with values in $A$ have the objectwise structure. The module `Mathlib.CategoryTheory.Sites.CartesianMonoidal` proves `Sheaf.tensorProd_isSheaf` and `Sheaf.tensorUnit_isSheaf`: the objectwise product and the terminal presheaf are sheaves, because they are limits. The instance `Sheaf.instIsMonoidalFunctorOppositeIsSheaf` says that the sheaf property is closed under the tensor product, and the cartesian monoidal structure on `Sheaf J A` follows by inference. The lemmas `sheafToPresheaf_μ`, `sheafToPresheaf_ε` and their duals say that the inclusion is monoidal with identity structure maps. The module `Mathlib.CategoryTheory.Sites.CartesianClosed` has one instance, `instMonoidalClosedSheafOfHasSheafifyOfFunctorOpposite`: if sheafification exists and the presheaf category is cartesian closed, the sheaf category is cartesian closed. The proof is the general fact that a reflective subcategory whose reflector preserves finite products is an exponential ideal.

**Monoidal structure by localization.** The module `Mathlib.CategoryTheory.Sites.Monoidal` treats a general monoidal category $A$. The objectwise tensor product of two sheaves is not a sheaf in general, for example for sheaves of abelian groups. So the library sheafifies it, and it uses the localization theory of Chapter 4. If the class $W_J$ of Section 5 is stable under tensor products, in the sense of `MorphismProperty.IsMonoidal`, then the localization `presheafToSheaf J A` carries a monoidal structure, and `Sheaf.monoidalCategory J A` is the resulting structure on `Sheaf J A`. The instance `Sheaf.instMonoidalFunctorOppositePresheafToSheaf` makes sheafification a monoidal functor. The definitions `Sheaf.braidedCategory` and `Sheaf.symmetricCategory` give the braided and symmetric cases. These are definitions, not instances, because they can conflict with the cartesian structure.

The hypothesis on $W_J$ holds in two cases in the library. If $A$ is braided and closed and the enriched hom presheaves exist, the instance `GrothendieckTopology.W.monoidal` gives it. Its proof uses `Presheaf.isSheaf_functorEnrichedHom`, that the enriched hom into a sheaf is a sheaf, through `Presheaf.functorEnrichedHomCoyonedaObjEquiv`. The lemmas `GrothendieckTopology.W.whiskerLeft` and `GrothendieckTopology.W.whiskerRight` are the two halves. The lemma `GrothendieckTopology.W.transport_isMonoidal` moves the hypothesis along a dense subsite, and Chapter 9 gives a third source by a conservative family of points.

#### Common errors

1. Colimits of sheaves are not objectwise. A cocone of presheaves that is a colimit gives a colimit of sheaves only after `Sheaf.sheafifyCocone`. Lemmas about objectwise colimits do not apply to sheaves directly.
2. `Sheaf.Γ J A` needs `HasGlobalSectionsFunctor J A`. On a site without a terminal object, give the limits of shape $C^{\mathrm{op}}$ in $A$, or the instance search fails.
3. `Sheaf.monoidalCategory J A` is not an instance. For sheaves with values in a cartesian monoidal category, the inferred structure is the cartesian one, and a local instance of the other structure makes two different tensor products.

### Exercises

1. (A) Use `constantSheafAdj` to show that, for a site with a terminal object, the morphisms from the constant sheaf on $M$ to $F$ correspond to the morphisms $M \to F(T)$.
2. (A) Describe `sheafHom F G` on the site of open sets of a space, and check with `sheafHomSectionsEquiv` that its global sections are the morphisms $F \to G$.
3. (B) Prove on paper that the product of two sheaves of types, computed objectwise, satisfies the sheaf condition, and compare with `Sheaf.tensorProd_isSheaf`.
4. (B) Let $C$ be the two point discrete category with the trivial topology. Show that `Sheaf.ΓNatIsoLim` identifies $\Gamma(F)$ with $F(a) \times F(b)$.
5. (B) Give two sheaves of abelian groups on the open sets of a space whose objectwise tensor product is not a sheaf, and explain why `Sheaf.monoidalCategory` sheafifies the product.
6. (C) On a site with a terminal object $T$, use `constantSheafAdj`, `constantSheafΓAdj` and the uniqueness of adjoints to construct an isomorphism between `Sheaf.Γ J D` and the sections over $T$, and compare it with `Sheaf.ΓNatIsoSheafSections`.

### Reference

<?reference?>
