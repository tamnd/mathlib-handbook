---
title: Continuous and cocontinuous functors
kind: api
modules:
  - Mathlib.CategoryTheory.Sites.Continuous
  - Mathlib.CategoryTheory.Sites.CoverPreserving
  - Mathlib.CategoryTheory.Sites.CoverLifting
  - Mathlib.CategoryTheory.Sites.Pullback
  - Mathlib.CategoryTheory.Sites.Adjunction
  - Mathlib.CategoryTheory.Sites.InducedTopology
explains:
  E2: [CategoryTheory.Functor.IsContinuous, CategoryTheory.Functor.sheafPushforwardContinuous, CategoryTheory.Functor.isContinuous_of_coverPreserving, CategoryTheory.Functor.IsCocontinuous, CategoryTheory.ran_isSheaf_of_isCocontinuous, CategoryTheory.Functor.sheafAdjunctionCocontinuous, CategoryTheory.Functor.sheafAdjunctionContinuous, CategoryTheory.Functor.inducedTopology, CategoryTheory.Functor.le_inducedTopology_iff, CategoryTheory.Sheaf.adjunction]
  E1: auto
families: []
requires: [V24.C02, V24.C05, V25.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Continuous and cocontinuous functors

### Overview

A continuous map $f : X \to Y$ of topological spaces gives a functor $f^{-1}$ from the open sets of $Y$ to the open sets of $X$. The pushforward of a sheaf $F$ on $X$ is $f_* F = F \circ f^{-1}$, and the pullback $f^*$ is its left adjoint. For general sites, the library starts from a functor $F : C \to D$ between the underlying categories. A sheaf $G$ on $(D, K)$ gives the presheaf $G \circ F^{\mathrm{op}}$ on $C$. The functor $F$ is continuous when this presheaf is always a sheaf for $J$. Then the precomposition is a functor of sheaf categories, and its left adjoint, when it exists, is the pullback.

There is a second notion. A functor $F$ is cocontinuous when it pulls covering sieves back to covering sieves. Then the right Kan extension along $F^{\mathrm{op}}$ sends sheaves to sheaves, and it gives a pushforward in the other direction. The six modules of this section hold these two notions, the cover preserving functors that help to prove continuity, the pullback of sheaves, the adjunctions between sheaf categories with different coefficients, and the topologies that a functor induces on its source.

The section uses the sieves, the topologies and the sheafification of Chapter 6, and the adjunctions and Kan extensions of Volume 24. Section 2 uses these notions to study dense subsites, and Section 3 uses them to study points.

### The library around it

**Continuous functors.** The module `Mathlib.CategoryTheory.Sites.Continuous` fixes $F : C \to D$ and topologies $J$ on $C$ and $K$ on $D$. The class `Functor.IsContinuous F J K` asks that $G \circ F^{\mathrm{op}}$ is a $J$ sheaf of types for each $K$ sheaf $G$ of types in one large universe. The choice of one universe makes the class easy to check. The lemma `Functor.op_comp_isSheaf_of_types` then gives the same property for sheaves of types in any universe, and `Functor.op_comp_isSheaf` gives it for sheaves with values in any category $A$. The reason is the usual one: a presheaf with values in $A$ is a sheaf when each functor $\operatorname{Hom}(a, -)$ sends it to a sheaf of types. The instances `Functor.isContinuous_id` and `Functor.isContinuous_comp` give the identity and the composition, and `Functor.isContinuous_of_iso` moves the class along a natural isomorphism.

For a continuous functor, `Functor.sheafPushforwardContinuous F A J K : Sheaf K A ⥤ Sheaf J A` is the precomposition with $F^{\mathrm{op}}$. The isomorphism `Functor.sheafPushforwardContinuousCompSheafToPresheafIso` says that it lies over the precomposition of presheaves. The family `Functor.sheafPushforwardContinuousId`, `Functor.sheafPushforwardContinuousComp` and their primed forms gives the pseudofunctorial isomorphisms, and `Functor.sheafPushforwardContinuousNatTrans` and `Functor.sheafPushforwardContinuousIso` give the action of natural transformations. An adjunction $F \dashv G$ between two continuous functors gives `Adjunction.sheafPushforwardContinuous`, an adjunction between the two pushforwards in the same order: the pushforward along $F$ is left adjoint to the pushforward along $G$. The proof whiskers the adjunction $G^{\mathrm{op}} \dashv F^{\mathrm{op}}$ with the presheaf.

Two criteria for continuity are in the module. The lemma `Functor.W_map_of_adjunction_of_isContinuous` says: if $H$ is a left adjoint of the precomposition of presheaves with $F^{\mathrm{op}}$, then $H$ sends a morphism that becomes an isomorphism after sheafification for $J$ to one that becomes an isomorphism after sheafification for $K$. The lemma `Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy` works with precoverages: if $F$ sends each covering family of $J$ to a covering family of $K$ and preserves the relevant pullbacks, then $F$ is continuous for the generated topologies. The module also maps 1-hypercovers. The pre-1-hypercover `PreOneHypercover.map` is the image of a pre-1-hypercover by $F$, the equivalence `PreOneHypercover.isLimitMapMultiforkEquiv` compares the two multiforks, and `GrothendieckTopology.OneHypercover.map` is the image when it is a 1-hypercover again. The abbreviation `Functor.PreservesOneHypercovers` states that this holds for all 1-hypercovers.

**Cover preserving functors.** A sieve $S$ on $X$ has an image sieve `S.functorPushforward F` on $F(X)$. The structure `CoverPreserving J K F` says that the image of each $J$ covering sieve is a $K$ covering sieve. The structure `CompatiblePreserving K F` says that $F$ sends compatible families of elements of $G \circ F^{\mathrm{op}}$ to compatible families of $G$. The main result of `Mathlib.CategoryTheory.Sites.CoverPreserving` is `Functor.isContinuous_of_coverPreserving`: a functor that is compatible preserving and cover preserving is continuous. Here is the proof sketch. Let $G$ be a $K$ sheaf and let $x$ be a compatible family of $G \circ F^{\mathrm{op}}$ on a $J$ covering sieve $S$. The image family is compatible on the $K$ covering sieve `S.functorPushforward F`, so it has a unique amalgamation in $G(F(X))$. This element is an amalgamation of $x$, and it is unique because any amalgamation of $x$ is an amalgamation of the image family. The converse direction holds in part. The lemma `CoverPreserving.of_isContinuous` says that a continuous functor is cover preserving. The lemma `Functor.isContinuous_iff_coverPreserving` says that for a representably flat functor the two notions agree. The theorems `idCoverPreserving` and `CoverPreserving.comp` give the identity and the composition, and `Functor.PreservesOneHypercovers.of_coverPreserving` says that a cover preserving functor that preserves pullbacks preserves 1-hypercovers.

**Cocontinuous functors.** The module `Mathlib.CategoryTheory.Sites.CoverLifting` defines the class `Functor.IsCocontinuous F J K`. Its field `Functor.cover_lift` says: for a $K$ covering sieve $R$ on $F(X)$, the sieve `R.pullback F` on $X$ is a $J$ covering sieve. The instances `isCocontinuous_id` and `isCocontinuous_comp` give the identity and the composition. The main theorem is `ran_isSheaf_of_isCocontinuous`: for a cocontinuous $F$ and a $J$ sheaf $P$, the right Kan extension `F.op.ran.obj P` is a $K$ sheaf. The proof checks the multifork form of the sheaf condition directly, with the explicit limit formula of the pointwise right Kan extension. The functor `Functor.sheafPushforwardCocontinuous F A J K : Sheaf J A ⥤ Sheaf K A` is the resulting pushforward. When $F$ is both continuous and cocontinuous, `Functor.sheafAdjunctionCocontinuous` gives the adjunction

$$F^{\mathrm{cont}}_* \dashv F^{\mathrm{cocont}}_*,$$

with the continuous pushforward on the left. The proof restricts the adjunction between the precomposition and the right Kan extension to the full subcategories of sheaves. The isomorphism `Functor.pushforwardContinuousSheafificationCompatibility` says that the continuous pushforward commutes with sheafification in this case.

**Pullback of sheaves.** In `Mathlib.CategoryTheory.Sites.Pullback`, the functor `Functor.sheafPullback F A J K : Sheaf J A ⥤ Sheaf K A` is a chosen left adjoint of the continuous pushforward, when one exists. It goes in the same direction as $F$. The adjunction is `Functor.sheafAdjunctionContinuous`. The definition `Functor.sheafPullbackConstruction.sheafPullback` gives an explicit construction: restrict to presheaves, take the left Kan extension along $F^{\mathrm{op}}$, and sheafify for $K$. Its adjunction `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` is the composition of the Kan extension adjunction with the sheafification adjunction, restricted to sheaves, and `Functor.sheafPullbackConstruction.sheafPullbackIso` compares it with the abstract pullback.

**Change of coefficients.** The module `Mathlib.CategoryTheory.Sites.Adjunction` keeps the site fixed and changes the category of values. An adjunction $G \dashv F$ with $F : D \to E$ gives `Sheaf.adjunction J adj : Sheaf.composeAndSheafify J G ⊣ sheafCompose J F`. The right adjoint composes a sheaf with $F$, which needs `HasSheafCompose J F`. The left adjoint composes with $G$ and then sheafifies. The lemma `Sheaf.preservesSheafification_of_adjunction` says that the left adjoint $G$ preserves sheafification. For a concrete category $D$, the abbreviation `sheafForget J` is the forgetful functor to sheaves of types.

**Induced topologies.** The module `Mathlib.CategoryTheory.Sites.InducedTopology` goes the other way: it starts from a topology $K$ on $D$ and builds topologies on $C$. The topology `Functor.inducedTopology F K` is the finest topology for which each sheaf $G \circ F^{\mathrm{op}}$ is a sheaf, for $G$ a $K$ sheaf of types. It is the finest topology on $C$ that makes $F$ continuous, and `Functor.le_inducedTopology_iff` states this universal property: $J \le$ `F.inducedTopology K` if and only if $F$ is continuous for $J$ and $K$. The lemma `Functor.mem_inducedTopology_iff` describes its covering sieves with a left adjoint of the precomposition. The topology `Functor.restrictedTopology F K` is generated by the families whose image generates a $K$ covering sieve, see `Functor.mem_restrictedTopology_of_functorPushforward_mem`. In general $F$ need not be continuous for it. When $F$ is continuous for it, `Functor.restrictedTopology_eq_inducedTopology` says that the two topologies agree.

#### Common errors

1. A user confuses the two pushforwards. `Functor.sheafPushforwardContinuous` goes from sheaves on $D$ to sheaves on $C$, against the direction of $F$. `Functor.sheafPushforwardCocontinuous` goes from sheaves on $C$ to sheaves on $D$, in the direction of $F$. In the case of a continuous map $f$ of spaces, the first is the usual $f_*$ for $F = f^{-1}$.
2. A user expects `Functor.IsCocontinuous` to mean that $F$ preserves colimits. In this file the word follows the terminology of sites: it means that $F$ lifts covering sieves.
3. A user tries to prove `Functor.IsContinuous` from `CoverPreserving` alone. The library needs `CompatiblePreserving` too, or a representably flat functor with `Functor.isContinuous_iff_coverPreserving`.

### Exercises

1. (A) Show that `Functor.sheafPushforwardContinuous` for the identity functor is isomorphic to the identity functor, with `Functor.sheafPushforwardContinuousId`.
2. (A) Let $F$ be continuous for $J$ and $K$, and let $J' \le J$. Show that $F$ is continuous for $J'$ and $K$, with `Functor.le_inducedTopology_iff`.
3. (B) Prove that a cocontinuous functor $F$ and a cocontinuous functor $G$ compose to a cocontinuous functor, from the field `Functor.cover_lift` and the pullback of sieves along a composition.
4. (B) Let $f : X \to Y$ be a continuous map of spaces. Show that $f^{-1}$ on open sets is cover preserving for the topologies of open covers.
5. (B) Let $F$ be continuous and cocontinuous. Write the unit of `Functor.sheafAdjunctionCocontinuous` for a sheaf $G$ on $D$ in terms of the counit of the right Kan extension.
6. (C) Prove `Functor.isContinuous_of_coverPreserving` for sheaves of types, with the image of a compatible family.

### Reference

<?reference?>
