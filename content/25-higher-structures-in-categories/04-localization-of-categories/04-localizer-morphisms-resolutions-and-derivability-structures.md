---
title: Localizer morphisms, resolutions and derivability structures
kind: api
modules:
  - Mathlib.CategoryTheory.Localization.LocalizerMorphism
  - Mathlib.CategoryTheory.Localization.Resolution
  - Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
  - Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
  - Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
  - Mathlib.CategoryTheory.Localization.DerivabilityStructure.DerivesTriangulated
  - Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
  - Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfLocalizedEquivalences
  - Mathlib.CategoryTheory.Localization.DerivabilityStructure.PointwiseLeftDerived
  - Mathlib.CategoryTheory.Localization.DerivabilityStructure.PointwiseRightDerived
  - Mathlib.CategoryTheory.Localization.DerivabilityStructure.Product
explains:
  E2: [CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence, CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_unit_of_unit, CategoryTheory.LocalizerMorphism.essSurj_of_hasRightResolutions, CategoryTheory.LocalizerMorphism.isIso_iff_of_hasRightResolutions, CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure, CategoryTheory.LocalizerMorphism.Derives.isRightDerivedFunctor_iff_isIso, CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_of_functorial_resolutions, CategoryTheory.LocalizerMorphism.hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V25.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Localizer morphisms, resolutions and derivability structures

### Overview

Sections 1 and 2 localize one category at one class of morphisms. Many constructions compare two localizations. The homotopy category of a model category is the localization of the whole category at the weak equivalences, and it is also the localization of the full subcategory of cofibrant objects. The derived category of an abelian category with enough injectives is a localization of all complexes, and it is also a localization of the bounded below complexes of injectives. A comparison of this kind is a functor $\Phi : C_1 \to C_2$ that sends the class $W_1$ into the class $W_2$. Mathlib calls such a functor a localizer morphism.

The modules of this section study localizer morphisms. The first module defines them and asks when $\Phi$ induces an equivalence of localized categories. The second module defines resolutions: a right resolution of an object $X_2$ of $C_2$ is an object $X_1$ of $C_1$ with a morphism $X_2 \to \Phi(X_1)$ in $W_2$. The other modules treat derivability structures. A right derivability structure is a localizer morphism that has enough resolutions and makes a certain square of localized categories exact. When $\Phi$ is a right derivability structure, a functor $F$ on $C_2$ that inverts nothing in $W_2$ can still have a right derived functor, and the derived functor is computed on objects of the form $\Phi(X_1)$. This is the abstract form of the computation of derived functors with injective resolutions.

The text uses the classes of morphisms of Chapter 3 and the localization functors of Section 1. It also uses Guitart exact squares (`TwoSquare.GuitartExact`) and right derived functors (`Functor.IsRightDerivedFunctor`) from the general category theory of the library. The text recalls what it needs of them.

### The library around it

#### Localizer morphisms

A localizer morphism `LocalizerMorphism W₁ W₂` is a structure with two fields. The field `functor` is a functor $\Phi : C_1 \to C_2$, and the field `map` is the proof that $W_1 \le W_2.\mathrm{inverseImage}(\Phi)$, that is, $\Phi(f) \in W_2$ for each $f \in W_1$. The usual operations exist: the identity `LocalizerMorphism.id`, the composition `LocalizerMorphism.comp`, the opposite `LocalizerMorphism.op`, the product `LocalizerMorphism.prod`, the morphism `LocalizerMorphism.arrow` on the categories of arrows, and `LocalizerMorphism.ofEq` for an equality $W_1 = W_2$ of classes on one category. In the arrow category the class is `MorphismProperty.arrow`, and in a product it is `MorphismProperty.prod`.

Let $L_1 : C_1 \to D_1$ and $L_2 : C_2 \to D_2$ be localization functors for $W_1$ and $W_2$. The lemma `LocalizerMorphism.inverts` says that $L_2 \circ \Phi$ inverts $W_1$. So the universal property of $L_1$ gives a functor `LocalizerMorphism.localizedFunctor` $\bar\Phi : D_1 \to D_2$ with an isomorphism $\bar\Phi \circ L_1 \cong L_2 \circ \Phi$. The class `LocalizerMorphism.IsLocalizedEquivalence` says that $\bar\Phi$ is an equivalence. The definition fixes the localizations that Section 1 constructs. The lemma `LocalizerMorphism.IsLocalizedEquivalence.mk'` shows that the choice does not matter: if $G : D_1 \to D_2$ is an equivalence with $G \circ L_1 \cong L_2 \circ \Phi$ for some localizations $L_1$ and $L_2$, then $\Phi$ is a localized equivalence. Conversely, `LocalizerMorphism.isEquivalence_iff` and the instance `LocalizerMorphism.IsLocalizedEquivalence.isLocalization` give that $L_2 \circ \Phi$ is a localization functor for $W_1$ when $\Phi$ is a localized equivalence. Two easy sources of localized equivalences are `LocalizerMorphism.IsLocalizedEquivalence.of_equivalence` and `LocalizerMorphism.isLocalizedEquivalence_of_isInduced`. The second one applies when $\Phi$ is an equivalence of categories and $W_1$ is induced by $W_2$, which is the class `LocalizerMorphism.IsInduced`.

The main test is `LocalizerMorphism.isLocalizedEquivalence_of_unit_of_unit`. Let $\Psi$ be a localizer morphism in the other direction, and let $\varepsilon_1 : 1 \to \Psi \circ \Phi$ and $\varepsilon_2 : 1 \to \Phi \circ \Psi$ be natural transformations whose components are in $W_1$ and $W_2$. Then $\Phi$ is a localized equivalence. The proof is short. After localization, the components of $\varepsilon_1$ and $\varepsilon_2$ become isomorphisms, so $L_1(\varepsilon_1)$ is an isomorphism $L_1 \cong L_1 \circ \Psi \circ \Phi$. The uniqueness of lifts along a localization turns it into an isomorphism $1 \cong \bar\Psi \circ \bar\Phi$, and $\varepsilon_2$ gives $1 \cong \bar\Phi \circ \bar\Psi$. Thus $\bar\Phi$ is an equivalence. The natural transformations need not satisfy triangle identities, because $W_1$ and $W_2$ are only inverted, not controlled.

The class `LocalizerMorphism.IsLocalizedFullyFaithful` asks only that $\bar\Phi$ be fully faithful, and `LocalizerMorphism.fullyFaithfulLocalizedFunctor` gives the data. The lemma `LocalizerMorphism.isLocalization_of_isLocalizedFullyFaithful` proves that a functor $L_1$ is a localization at $W_1$ when it is essentially surjective and fits in a square $L_2 \circ \Phi \cong F \circ L_1$ with $F$ fully faithful.

#### Resolutions

A right resolution `LocalizerMorphism.RightResolution` of $X_2 \in C_2$ is a pair of an object $X_1 \in C_1$ and a morphism $w : X_2 \to \Phi(X_1)$ in $W_2$. A morphism of right resolutions is a morphism $f : X_1 \to X_1'$ in $W_1$ that makes the triangle commute. So the right resolutions of $X_2$ form a category. Left resolutions `LocalizerMorphism.LeftResolution` use morphisms $\Phi(X_1) \to X_2$. The equivalence `LocalizerMorphism.LeftResolution.opEquivalence` identifies the opposite of the category of left resolutions of $X_2$ with the category of right resolutions of $X_2$ for $\Phi^{\mathrm{op}}$. Most results come in a right form, and the left form follows by duality.

The class `LocalizerMorphism.HasRightResolutions` says that each object of $C_2$ has a right resolution. Two consequences come at once. First, `LocalizerMorphism.essSurj_of_hasRightResolutions`: the functor $L_2 \circ \Phi$ is essentially surjective. Indeed, each object of $D_2$ is isomorphic to $L_2(X_2)$, and a resolution $w : X_2 \to \Phi(X_1)$ gives an isomorphism $L_2(w) : L_2(X_2) \cong L_2(\Phi(X_1))$. Second, `LocalizerMorphism.isIso_iff_of_hasRightResolutions`: a natural transformation $\alpha : F \to G$ of functors $D_2 \to H$ is an isomorphism if and only if $\alpha_{L_2(\Phi(X_1))}$ is an isomorphism for each $X_1 \in C_1$. The proof is the same remark: each object of $D_2$ is isomorphic to one of the form $L_2(\Phi(X_1))$, and naturality carries the isomorphism. The lemmas `LocalizerMorphism.hasRightResolutions_iff_op` and `LocalizerMorphism.hasLeftResolutions_iff_op` exchange the two kinds, and `LocalizerMorphism.RightResolution.prod` builds resolutions in a product.

#### Derivability structures

A square of functors $T : C_1 \to C_2$, $L : C_1 \to D_1$, $R : C_2 \to D_2$, $B : D_1 \to D_2$ with $\alpha : T \circ R \to L \circ B$ is Guitart exact, `TwoSquare.GuitartExact`, when pointwise left Kan extensions along $L$ and $R$ are compatible with it. The test `TwoSquare.guitartExact_iff_isConnected_downwards` says that this holds when certain categories of factorizations are connected. A right derivability structure `LocalizerMorphism.IsRightDerivabilityStructure` is a localizer morphism $\Phi$ such that $\Phi$ has right resolutions and the square formed by $\Phi$, $L_1$, $L_2$ and $\bar\Phi$ is Guitart exact. The definition uses the constructed localizations. By `LocalizerMorphism.isRightDerivabilityStructure_iff`, the condition holds for one choice of $L_1$, $L_2$ and $\bar\Phi$ if and only if it holds for all choices, and the instance `LocalizerMorphism.guitartExact_of_isRightDerivabilityStructure` gives the exact square for any choice. The left notion `LocalizerMorphism.IsLeftDerivabilityStructure` is dual, and `LocalizerMorphism.isRightDerivabilityStructure_iff_op` passes between them.

Guitart exactness is hard to check by hand. The module `Constructor` gives the practical test `LocalizerMorphism.IsRightDerivabilityStructure.mk'`. Its hypotheses are four:

| Hypothesis | Lean form |
| --- | --- |
| each category of right resolutions is connected | `∀ X₂, IsConnected (Φ.RightResolution X₂)` |
| the arrow morphism has right resolutions | `Φ.arrow.HasRightResolutions` |
| $W_2$ contains the identities | `W₂.ContainsIdentities` |
| $\Phi$ is a localized equivalence | `Φ.IsLocalizedEquivalence` |

The resolutions of arrows let the proof lift a morphism of $C_2$ to a morphism between resolutions, and connectedness makes the choice irrelevant after localization.

#### Functorial resolutions and changes of model

Often the resolutions are functorial. The module `OfFunctorialResolutions` assumes a functor $\rho : C_2 \to C_1$ and a natural transformation $i : 1 \to \Phi \circ \rho$ whose components are in $W_2$. Under the extra hypotheses that $\Phi$ is fully faithful, $W_1$ is induced by $W_2$, and $W_2$ is multiplicative and has the two out of three property, `LocalizerMorphism.isRightDerivabilityStructure_of_functorial_resolutions` says that $\Phi$ is a right derivability structure. The proof checks the four hypotheses of `IsRightDerivabilityStructure.mk'`. The pair $(\rho(X_2), i_{X_2})$ is a resolution of $X_2$, and the naturality of $i$ gives resolutions of arrows (`LocalizerMorphism.hasRightResolutions_arrow_of_functorial_resolutions`). Any resolution $w : X_2 \to \Phi(X_1)$ connects to $(\rho(X_2), i_{X_2})$ through $\rho(w)$ and $i_{\Phi(X_1)}$, because $\Phi$ is fully faithful. This gives `LocalizerMorphism.isConnected_rightResolution_of_functorial_resolutions`. Last, $\rho$ is a localizer morphism back (`LocalizerMorphism.functorialRightResolutions.localizerMorphismInv`), and `isLocalizedEquivalence_of_unit_of_unit` gives the localized equivalence, which is `LocalizerMorphism.isLocalizedEquivalence_of_functorial_right_resolutions`.

The module `OfLocalizedEquivalences` changes the model. It takes a commutative square of localizer morphisms $T$, $L$, $R$, $B$ in which $L$ and $R$ are localized equivalences. The lemma `LocalizerMorphism.isRightDerivabilityStructure_iff_of_isLocalizedEquivalence` says that $T$ is a right derivability structure if and only if $B$ is one, under resolution conditions. The variant `LocalizerMorphism.isRightDerivabilityStructure_of_equivalences` is for the case where $L$ and $R$ are equivalences on the localized categories, such as quotient functors to homotopy categories. The module `Product` gives the instances `LocalizerMorphism.instIsRightDerivabilityStructureProdProdProd` and `LocalizerMorphism.instIsLeftDerivabilityStructureProdProdProd` for products of derivability structures.

#### Derived functors through a derivability structure

Let $F : C_2 \to H$ be a functor. A right derived functor of $F$ for $W_2$ is a functor $RF : D_2 \to H$ with $\alpha : F \to RF \circ L_2$ that is initial among such pairs, which is the class `Functor.IsRightDerivedFunctor`. The predicate `LocalizerMorphism.Derives` says that $F \circ \Phi$ inverts $W_1$. So $F$ need not invert $W_2$, but it behaves well on the objects $\Phi(X_1)$.

The central result of `Derives` is `LocalizerMorphism.Derives.isRightDerivedFunctor_iff_isIso`. If $\Phi$ is a right derivability structure and $F$ derives along $\Phi$, then a pair $(RF, \alpha)$ is a right derived functor if and only if $\alpha_{\Phi(X_1)}$ is an isomorphism for each $X_1 \in C_1$. In words, the derived functor agrees with $F$ on the objects that come from $C_1$, and the resolutions compute it on the other objects. The lemma `LocalizerMorphism.Derives.hasPointwiseRightDerivedFunctor` gives the existence of a pointwise right derived functor, and `LocalizerMorphism.Derives.isIso` gives the isomorphism at $\Phi(X_1)$ for any right derived functor. The module `DerivesTriangulated` adds that the derived functor is triangulated in a triangulated setting: `LocalizerMorphism.Derives.isTriangulated_of_isRightDerivedFunctor` and `LocalizerMorphism.Derives.isTriangulated_of_isLeftDerivedFunctor`. Chapter 5 treats triangulated categories.

The modules `PointwiseRightDerived` and `PointwiseLeftDerived` remove the hypothesis that $F$ derives. The result `LocalizerMorphism.hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure` says that $F$ has a pointwise right derived functor for $W_2$ if and only if $F \circ \Phi$ has one for $W_1$. The reason is the Guitart exact square: a pointwise Kan extension along $L_1$ transfers along the square to a pointwise Kan extension along $L_2$. The comparison morphism `LocalizerMorphism.rightDerivedFunctorComparison` from $R(F \circ \Phi)$ to $(RF) \circ \bar\Phi$ satisfies `LocalizerMorphism.rightDerivedFunctorComparison_fac`, and `LocalizerMorphism.isIso_iff_of_isRightDerivabilityStructure` gives a test for it to be an isomorphism. The left versions, such as `LocalizerMorphism.hasPointwiseLeftDerivedFunctor_iff_of_isLeftDerivabilityStructure`, are dual.

#### Common errors

1. A user proves `IsLocalizedEquivalence` by hand with the constructed localizations of Section 1. It is shorter to use `IsLocalizedEquivalence.mk'` with the localizations at hand, or `isLocalizedEquivalence_of_unit_of_unit` when a functor back exists.
2. A user confuses the direction of resolutions. A right resolution of $X_2$ is a morphism $X_2 \to \Phi(X_1)$, as an injective resolution maps into a complex of injectives. A left resolution is a morphism $\Phi(X_1) \to X_2$, as a projective resolution.
3. A user expects `Derives` to say that $F$ inverts $W_2$. It says only that $F \circ \Phi$ inverts $W_1$. The functor $F$ itself can send a morphism of $W_2$ to a morphism that is not an isomorphism.

### Exercises

1. (A) Show that the identity `LocalizerMorphism.id W` is a localized equivalence, and that the composition of two localized equivalences is a localized equivalence.
2. (A) Let $\Phi$ have right resolutions. Show that a functor $D_2 \to H$ is determined up to isomorphism by its composition with $L_2 \circ \Phi$, in the sense that a natural transformation that is an isomorphism on each $L_2(\Phi(X_1))$ is an isomorphism.
3. (B) Let $C_1 \subseteq C_2$ be a reflective full subcategory with unit $\eta : X \to \iota(r(X))$. Let $W_2$ be the morphisms that $r$ inverts and $W_1$ the induced class. Use functorial resolutions to show that the inclusion is a right derivability structure.
4. (B) Prove `LocalizerMorphism.essSurj_of_hasRightResolutions` from the definitions, and state the left version with `LocalizerMorphism.essSurj_of_hasLeftResolutions`.
5. (B) Let $\Phi$ be a right derivability structure and let $F : C_2 \to H$ invert $W_2$. Show that $F$ derives along $\Phi$, and that the functor induced by $F$ on $D_2$ is a right derived functor of $F$.
6. (C) For an abelian category with enough injectives, take $C_1$ to be the bounded below complexes of injectives with the homotopy equivalences and $C_2$ the bounded below complexes with the quasi-isomorphisms. Explain which hypotheses of `IsRightDerivabilityStructure.mk'` the existence of injective resolutions gives, and which need a separate argument.

### Reference

<?reference?>
