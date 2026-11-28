---
title: Locally injective and locally surjective morphisms
kind: api
modules:
  - Mathlib.CategoryTheory.Sites.LocallyInjective
  - Mathlib.CategoryTheory.Sites.LocallySurjective
  - Mathlib.CategoryTheory.Sites.LocallyBijective
  - Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
  - Mathlib.CategoryTheory.Sites.LocallyFullyFaithful
  - Mathlib.CategoryTheory.Sites.EpiMono
  - Mathlib.CategoryTheory.Sites.Localization
  - Mathlib.CategoryTheory.Sites.LocalProperties
  - Mathlib.CategoryTheory.Sites.RegularEpi
  - Mathlib.CategoryTheory.Sites.Subsheaf
explains:
  E2: [CategoryTheory.Presheaf.IsLocallyInjective, CategoryTheory.Presheaf.IsLocallySurjective, CategoryTheory.Sheaf.isLocallySurjective_iff_epi, CategoryTheory.Sheaf.isLocallyInjective_iff_injective, CategoryTheory.GrothendieckTopology.W, CategoryTheory.GrothendieckTopology.W_iff_isLocallyBijective, CategoryTheory.Sheaf.isLocallyBijective_iff_isIso, CategoryTheory.Functor.IsLocallyFull, CategoryTheory.Subfunctor.sheafify, CategoryTheory.Sheaf.isIso_iff_of_coversTop]
  E1: auto
families: []
requires: [V24.C04, V24.C05, V25.C03, V25.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Locally injective and locally surjective morphisms

### Overview

A morphism of sheaves of abelian groups on a space is an epimorphism when it is surjective on stalks, and this does not imply that it is surjective on each open set. The exponential map from the sheaf of continuous functions to the sheaf of nowhere zero continuous functions on $\mathbb{C} \setminus \{0\}$ is the standard example: each local section has a logarithm on small open sets, but the identity function has no global logarithm. The right notion is local: a section of the target is, on a cover, the image of sections of the source. The same idea gives local injectivity: two sections with the same image agree on a cover.

For presheaves on a site $(C, J)$ with values in a concrete category $A$, this section defines locally injective and locally surjective morphisms and proves the expected facts. A morphism of sheaves of types is a monomorphism exactly when it is injective on sections, and an epimorphism exactly when it is locally surjective. A morphism of presheaves becomes an isomorphism after sheafification exactly when it is locally injective and locally surjective. The class $W_J$ of these morphisms gives a description of the sheaf category as a localization of the presheaf category. The section ends with subsheaves, images of morphisms of sheaves of types and the regularity of the sheaf category.

The section uses the sheafification of Section 3, the localization of Chapter 4, and the morphism properties and the regular epimorphisms of Chapter 3. The test on a cover of the terminal object uses the sites over an object of Chapter 9.

### The library around it

**Local injectivity.** The module `Mathlib.CategoryTheory.Sites.LocallyInjective` works with a morphism $\varphi : F_1 \to F_2$ of presheaves with values in a concrete category $D$. For two sections $x, y$ of $F_1$ over $U$, `Presheaf.equalizerSieve x y` is the sieve of the arrows $f : V \to U$ with $f^* x = f^* y$. The class `Presheaf.IsLocallyInjective J φ` asks that this sieve is covering whenever $\varphi(x) = \varphi(y)$, and `Presheaf.isLocallyInjective_iff_equalizerSieve_mem_imp` states this form. A morphism injective on each object is locally injective, by `Presheaf.isLocallyInjective_of_injective`. When $F_1$ is separated, `Presheaf.isLocallyInjective_iff_injective_of_separated` gives the converse. For sheaves this is `Sheaf.isLocallyInjective_iff_injective`, under the hypothesis that the composition with the forgetful functor preserves sheaves, and then `Sheaf.mono_of_isLocallyInjective` gives a monomorphism. The lemmas `Presheaf.isLocallyInjective_comp`, `Presheaf.isLocallyInjective_of_isLocallyInjective` and `Presheaf.comp_isLocallyInjective_iff` treat composition. The instances `Presheaf.isLocallyInjective_toPlus` and `Presheaf.isLocallyInjective_toSheafify` say that the plus construction and sheafification are locally injective.

**Local surjectivity.** In `Mathlib.CategoryTheory.Sites.LocallySurjective`, for a section $s$ of $G$ over $U$, `Presheaf.imageSieve f s` is the sieve of the arrows $g : V \to U$ such that $g^* s$ lies in the image of $f$. The class `Presheaf.IsLocallySurjective J f` asks that each image sieve is covering. The function `Presheaf.localPreimage` picks a preimage on each arrow of the sieve, and `Presheaf.app_localPreimage` is its defining property. The lemma `Presheaf.isLocallySurjective_iff_range_sheafify_eq_top` gives the second form: the sheafification of the image subpresheaf is the whole presheaf. The lemmas `Presheaf.isLocallySurjective_comp`, `Presheaf.isLocallySurjective_of_isLocallySurjective` and `Presheaf.comp_isLocallySurjective_iff` handle composition. The two mixed lemmas `Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective` and `Presheaf.isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective` give the two out of three properties that a localization needs.

The sheaf form is `Sheaf.IsLocallySurjective`. The lemma `Sheaf.epi_of_isLocallySurjective` gives an epimorphism. For sheaves of types, `Sheaf.isLocallySurjective_iff_epi` gives the converse, and `Sheaf.isLocallySurjective_iff_isIso` says that $f$ is locally surjective when the inclusion `Sheaf.imageι f` of its image is an isomorphism. The isomorphism `Presheaf.sheafificationIsoImagePresheaf` identifies the sheafification of a presheaf of types with the sheafification of the image of `toSheafify`.

**Locally bijective morphisms and the class $W_J$.** The module `Mathlib.CategoryTheory.Sites.Localization` defines `GrothendieckTopology.W J`, the class of morphisms of presheaves that become isomorphisms after sheafification. The lemma `GrothendieckTopology.W_iff` states this with `presheafToSheaf J A`, and `GrothendieckTopology.W_eq_inverseImage_isomorphisms` states it as an equality of morphism properties. The unit `toSheafify J P` is in $W_J$ by `GrothendieckTopology.W_toSheafify`. The instance `GrothendieckTopology.instIsLocalizationFunctorOppositeSheafPresheafToSheafW` is the main result: sheafification is a localization functor for $W_J$. With Chapter 4, this means that each functor on presheaves that inverts $W_J$ factors through sheaves, uniquely up to a unique isomorphism. The lemma `GrothendieckTopology.W_eq_inverseImage_isomorphisms_of_adjunction` gives the same description for any left adjoint of the inclusion of sheaves, and `Sieve.W_shrinkFunctor_ι_of_mem` says that the inclusion of a covering sieve into the shrunk Yoneda presheaf is in $W_J$.

The module `Mathlib.CategoryTheory.Sites.LocallyBijective` connects the two pictures. The class `GrothendieckTopology.WEqualsLocallyBijective J A` asks that a morphism is in $W_J$ if and only if it is locally injective and locally surjective. Then `GrothendieckTopology.W_iff_isLocallyBijective` states the equivalence, and `GrothendieckTopology.W_of_isLocallyBijective` is one direction. The constructor `GrothendieckTopology.WEqualsLocallyBijective.mk'` reduces the class to the property for `toSheafify J P` alone. An instance gives the class for types in the universe `max u v`, and a second instance gives it for a concrete category whose forgetful functor reflects isomorphisms and commutes with sheafification. For sheaves, `Sheaf.isLocallyBijective_iff_isIso` says that a morphism is locally injective and locally surjective exactly when it is an isomorphism, if the forgetful functor reflects isomorphisms.

**Factorization and epimorphisms.** In `Mathlib.CategoryTheory.Sites.EpiMono`, `Sheaf.locallySurjective J A` and `Sheaf.locallyInjective J A` are the two classes as morphism properties of `Sheaf J A`. When $A$ has a functorial factorization of maps into a surjection and an injection, `Sheaf.functorialLocallySurjectiveInjectiveFactorization` factors each morphism of sheaves as a locally surjective morphism and a locally injective morphism. If the sheaf category is also balanced, `Sheaf.isLocallySurjective_iff_epi'` gives that the epimorphisms are the locally surjective morphisms. The module `Mathlib.CategoryTheory.Sites.RegularEpi` uses such factorizations. The lemma `isRegularEpiCategory_sheaf` says that `Sheaf J D` is a regular epi category if $D$ is one, has pullbacks and pushouts, sheafification exists, the sheaf category is balanced, and each epimorphism of sheaves factors as an epimorphism and a monomorphism of presheaves. The instance `instIsRegularEpiCategorySheafTypeOfHasSheafify` gives the case of sheaves of types.

**Precomposition with a functor.** The module `Mathlib.CategoryTheory.Sites.PreservesLocallyBijective` fixes $H : C \to D$ and topologies $J$ and $K$. For a cocontinuous functor of Chapter 9, `Presheaf.isLocallyInjective_whisker` and `Presheaf.isLocallySurjective_whisker` say that precomposition with $H^{\mathrm{op}}$ keeps the two properties. When $H$ is also cover preserving and cover dense, `Presheaf.isLocallyInjective_whisker_iff` and `Presheaf.isLocallySurjective_whisker_iff` give the converse.

**Locally full and locally faithful functors.** In `Mathlib.CategoryTheory.Sites.LocallyFullyFaithful`, for $G : C \to D$ and a morphism $f : G(U) \to G(V)$, the sieve `Functor.imageSieve G f` contains the arrows $i : W \to U$ such that $G(i) \circ f$ is the image of an arrow of $C$. The class `Functor.IsLocallyFull G K` asks that the pushforward of each such sieve is covering for $K$. For two arrows $f_1, f_2 : U \to V$, `Sieve.equalizer f₁ f₂` is the sieve of the arrows that equalize them, and `Functor.IsLocallyFaithful G K` asks that its pushforward is covering when $G(f_1) = G(f_2)$. Full and faithful functors have the two properties, by `Functor.IsLocallyFull.of_full` and `Functor.IsLocallyFaithful.of_faithful`. The lemmas `Functor.IsLocallyFull.ext` and `Functor.IsLocallyFaithful.ext` give the main use: two sections of a sheaf over $G(U)$ are equal when they agree on the images of the arrows of $C$. Chapter 9 uses these classes for dense subsites.

**Properties that are local on the base.** The module `Mathlib.CategoryTheory.Sites.LocalProperties` has two lemmas. For a family $X$ that covers the terminal object, as in Section 4, `Sheaf.isIso_of_coversTop` and `Sheaf.isIso_iff_of_coversTop` say that a morphism of sheaves is an isomorphism when it is one after the pullback `GrothendieckTopology.overPullback` to each slice `Over (X i)`.

**Subsheaves and images.** In `Mathlib.CategoryTheory.Sites.Subsheaf`, a subfunctor $G$ of a presheaf of types $F$ has the sheafification `Subfunctor.sheafify J G`: a section of $F$ belongs to it when its restriction to a covering sieve lies in $G$. The lemmas `Subfunctor.le_sheafify`, `Subfunctor.sheafify_le` and `Subfunctor.sheafify_sheafify` give the closure operator properties. If $F$ is a sheaf, `Subfunctor.sheafify_isSheaf` says that the result is a sheaf, and `Subfunctor.isSheaf_iff` characterizes the subfunctors that are sheaves. A morphism $G \to F'$ into a sheaf extends to `Subfunctor.sheafifyLift`, and `Subfunctor.to_sheafify_lift_unique` gives uniqueness. Each subfunctor of a separated presheaf is separated, by `Subfunctor.isSeparated`. For a morphism $f$ of sheaves of types, `Sheaf.image f` is the sheafified image, with `Sheaf.toImage f` and `Sheaf.imageι f`, and `imageFactorization` turns it into an image factorization. The instance `instHasImagesSheafType` gives images in the category of sheaves of types.

#### Common errors

1. `Presheaf.IsLocallyInjective` and `Presheaf.IsLocallySurjective` need a concrete category of values. For sheaves of modules or of abelian groups, the forgetful functor is part of the statement, and many lemmas also ask for `J.HasSheafCompose (forget A)`.
2. `Sheaf.isLocallySurjective_iff_epi` is for sheaves of types. For other values use `Sheaf.isLocallySurjective_iff_epi'`, which needs a functorial factorization in $A$ and a balanced sheaf category.
3. `Subfunctor.sheafify J G` is a subfunctor of $F$, and it is a sheaf only when $F$ is one.

### Exercises

1. (A) Use `Presheaf.isLocallySurjective_toSheafify` and `Presheaf.isLocallyInjective_toSheafify` to prove that `toSheafify J P` is in $W_J$ for $P$ with values in types, through `GrothendieckTopology.W_iff_isLocallyBijective`.
2. (A) Show that `Presheaf.equalizerSieve x x` is the top sieve.
3. (B) Prove on paper that a locally surjective morphism of sheaves of types is an epimorphism: two morphisms $a, b : G \to H$ with $a f = b f$ agree on each image sieve, so they agree by the sheaf condition for $H$.
4. (B) On the site of open sets of $\mathbb{C} \setminus \{0\}$, explain why the exponential map of sheaves of continuous functions is locally surjective and is not surjective on global sections.
5. (B) Use `Sheaf.isLocallyBijective_iff_isIso` and `Sheaf.isLocallyInjective_iff_injective` to prove that a morphism of sheaves of types that is injective on sections and locally surjective is an isomorphism.
6. (C) Let $H : C \to D$ be cover preserving, cocontinuous and cover dense. Use `Presheaf.isLocallyInjective_whisker_iff`, `Presheaf.isLocallySurjective_whisker_iff` and `Sheaf.isLocallyBijective_iff_isIso` to prove that a morphism of sheaves of types on $D$ is an isomorphism when its restriction to $C$ is an isomorphism of presheaves.

### Reference

<?reference?>
