---
title: Localization of products, multifunctors and monoidal structures
kind: api
modules:
  - Mathlib.CategoryTheory.Localization.Prod
  - Mathlib.CategoryTheory.Localization.Pi
  - Mathlib.CategoryTheory.Localization.FiniteProducts
  - Mathlib.CategoryTheory.Localization.Bifunctor
  - Mathlib.CategoryTheory.Localization.Trifunctor
  - Mathlib.CategoryTheory.Localization.Quadrifunctor
  - Mathlib.CategoryTheory.Localization.Monoidal.Basic
  - Mathlib.CategoryTheory.Localization.Monoidal.Braided
  - Mathlib.CategoryTheory.Localization.Monoidal.Functor
explains:
  E2: [CategoryTheory.Functor.IsLocalization.prod, CategoryTheory.Functor.IsLocalization.pi, CategoryTheory.Localization.preservesFiniteProducts, CategoryTheory.Localization.lift₂, CategoryTheory.Localization.natTrans₂_ext, CategoryTheory.Localization.associator, CategoryTheory.MorphismProperty.IsMonoidal, CategoryTheory.Localization.Monoidal.functorMonoidalOfComp]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V24.C04, V24.C07, V25.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Localization of products, multifunctors and monoidal structures

### Overview

Section 1 lifts a functor $F : C \to E$ that inverts $W$ to a functor on the localization $C[W^{-1}]$. Many constructions need more: a tensor product $C \times C \to C$, a Hom bifunctor, or a functor of three or four variables such as the two sides of an associator. The modules of this section extend the universal property to functors of several variables. The base result is that a product of localization functors is a localization functor. After it, a bifunctor $C_1 \to C_2 \to E$ that inverts $W_1$ and $W_2$ in each variable lifts to the localized categories, and a natural transformation of lifted bifunctors is determined by its values on the objects that come from $C_1$ and $C_2$.

The same idea gives two applications. The first one is that a localization functor preserves finite products, when the class $W$ is stable under finite products. The second one is that a monoidal structure on $C$ descends to $C[W^{-1}]$ when $W$ is compatible with the tensor product. The localized category is then monoidal, braided or symmetric when $C$ is, and the localization functor is monoidal.

The text uses the localization functors and liftings of Section 1, the classes of morphisms of Chapter 3, and the monoidal categories of Volume 24.

### The library around it

#### Products of localizations

Let $L_1 : C_1 \to D_1$ and $L_2 : C_2 \to D_2$ be localization functors for $W_1$ and $W_2$. The class of morphisms `MorphismProperty.prod` $W_1 \times W_2$ on $C_1 \times C_2$ contains the pairs $(f_1, f_2)$ with $f_1 \in W_1$ and $f_2 \in W_2$. The instance `Functor.IsLocalization.prod` says that the product functor `Functor.prod` $L_1 \times L_2$ is a localization functor for $W_1 \times W_2$, when both classes contain the identities (`MorphismProperty.ContainsIdentities`).

The proof has two steps. The first step, `Localization.Construction.prodIsLocalization`, treats the constructed localizations of Section 1. It checks the strict universal property `Localization.StrictUniversalPropertyFixedTarget.prod`. Let $F : C_1 \times C_2 \to E$ invert $W_1 \times W_2$. For a fixed $X_2$, the functor $X_1 \mapsto F(X_1, X_2)$ inverts $W_1$, because $(f_1, 1_{X_2})$ is in $W_1 \times W_2$. So it lifts to $D_1$. The same argument in the second variable gives the lift `Localization.StrictUniversalPropertyFixedTarget.prodLift` on $D_1 \times D_2$. The identities are needed here: a morphism $(f_1, f_2)$ factors as $(f_1, 1) \circ (1, f_2)$, and each factor is in $W_1 \times W_2$ only when the identities are. The second step transports the result to any localization functors by `Functor.IsLocalization.of_equivalences`.

The module `Pi` extends the result to a finite family. The instance `Functor.IsLocalization.pi` says that for a finite type $J$ and localization functors $L_j : C_j \to D_j$ for classes $W_j$ that contain the identities, the functor `Functor.pi` $\prod_j L_j$ is a localization functor for `MorphismProperty.pi` $\prod_j W_j$. The proof is an induction on the finite type. The empty product is trivial, and a type `Option J` splits off one factor, so the binary case applies. A second instance of the module gives the same result for functor categories `Discrete J ⥤ C`, with the class `MorphismProperty.functorCategory`.

#### Finite products in the localized category

Let $C$ have finite products, and let $W$ contain the identities and be stable under finite products (`MorphismProperty.IsStableUnderFiniteProducts`). Then `Localization.hasFiniteProducts` says that the localized category $D$ has finite products, and `Localization.preservesFiniteProducts` says that $L$ preserves them. The per-shape forms are `Localization.hasProductsOfShape` and `Localization.preservesProductsOfShape`, with the hypothesis `MorphismProperty.IsStableUnderProductsOfShape`.

The proof is a short use of the module `Pi`. The product functor $\lim : (\mathrm{Discrete}\,J \to C) \to C$ is right adjoint to the constant functor. Stability of $W$ under products says that $\lim$ sends $W^J$ into $W$, so it lifts to the localizations. By the instance above, $(\mathrm{Discrete}\,J \to C) \to (\mathrm{Discrete}\,J \to D)$ is a localization functor. The adjunction lifts to an adjunction `Localization.HasProductsOfShapeAux.adj` between the constant functor of $D$ and the lifted product functor. A category in which the constant functor has a right adjoint has the products of shape $J$. The same adjunction shows that $L$ sends the limit cone of $C$ to a limit cone of $D$. The instances for the constructed localization `W.Localization` follow at once.

#### Bifunctors

The module `Bifunctor` reduces bifunctors to functors on a product. The predicate `MorphismProperty.IsInvertedBy₂` $W_1\,W_2\,F$ says that the uncurried functor $C_1 \times C_2 \to E$ of $F : C_1 \to C_2 \to E$ inverts $W_1 \times W_2$. The class `Localization.Lifting₂` $L_1\,L_2\,W_1\,W_2\,F\,F'$ is the bifunctor form of `Localization.Lifting`: it holds data `Localization.Lifting₂.iso`, an isomorphism $F'(L_1 -, L_2 -) \cong F$.

Under the predicate, `Localization.lift₂` $F\,hF\,L_1\,L_2$ is a bifunctor $D_1 \to D_2 \to E$. It is the curried form of the lift of the uncurried functor along $L_1 \times L_2$, so it exists by the instance `Functor.IsLocalization.prod`. It has an instance of `Lifting₂`, and the lemmas `Localization.lift₂_iso_hom_app_app₁` and its companion describe the components of the isomorphism. The instances `Localization.Lifting₂.flip`, `Localization.Lifting₂.uncurry` and `Localization.Lifting₂.compRight` pass the lifting through the swap of variables, the uncurrying, and a composition on the right. The definitions `Localization.Lifting₂.fst` and `Localization.Lifting₂.snd` give the partial liftings in one variable.

The morphisms follow the same pattern. If $F_1'$ and $F_2'$ lift $F_1$ and $F_2$, then a natural transformation $\tau : F_1 \to F_2$ lifts to `Localization.lift₂NatTrans` $\tau$, and an isomorphism lifts to `Localization.lift₂NatIso`. The lemma `Localization.lift₂NatTrans_app_app` computes the lift on objects $L_1 X_1$ and $L_2 X_2$. The extensionality lemma `Localization.natTrans₂_ext` says that two natural transformations $\tau, \tau' : F_1' \to F_2'$ are equal when
$$\tau_{L_1 X_1, L_2 X_2} = \tau'_{L_1 X_1, L_2 X_2} \quad \text{for all } X_1 \in C_1,\ X_2 \in C_2.$$
The proof uncurries both transformations and applies the one-variable lemma `Localization.natTrans_ext` to $L_1 \times L_2$. Uncurrying is injective on natural transformations, so the result follows.

#### Trifunctors and quadrifunctors

The modules `Trifunctor` and `Quadrifunctor` repeat the pattern for three and four variables. The names follow a fixed scheme, with the number of variables as a subscript:

| Two variables | Three variables | Four variables |
| --- | --- | --- |
| `MorphismProperty.IsInvertedBy₂` | `MorphismProperty.IsInvertedBy₃` | `MorphismProperty.IsInvertedBy₄` |
| `Localization.Lifting₂` | `Localization.Lifting₃` | `Localization.Lifting₄` |
| `Localization.lift₂` | `Localization.lift₃` | `Localization.lift₄` |
| `Localization.lift₂NatTrans` | `Localization.lift₃NatTrans` | `Localization.lift₄NatTrans` |
| `Localization.lift₂NatIso` | `Localization.lift₃NatIso` | `Localization.lift₄NatIso` |
| `Localization.natTrans₂_ext` | `Localization.natTrans₃_ext` | `Localization.natTrans₄_ext` |

The trifunctor module has one more result, the localized associator. Let $F_{12} : C_1 \to C_2 \to C_{12}$ and $G : C_{12} \to C_3 \to C$ give the trifunctor `bifunctorComp₁₂` $(X_1, X_2, X_3) \mapsto G(F_{12}(X_1, X_2), X_3)$, and let $F$ and $G_{23}$ give `bifunctorComp₂₃` $(X_1, X_2, X_3) \mapsto F(X_1, G_{23}(X_2, X_3))$. The definitions `Localization.Lifting₃.bifunctorComp₁₂` and `Localization.Lifting₃.bifunctorComp₂₃` show that these compositions are compatible with liftings of the four bifunctors. So an isomorphism between the two trifunctors on $C$ lifts to an isomorphism `Localization.associator` between the two trifunctors built from the lifted bifunctors. The lemma `Localization.associator_hom_app_app_app` gives its components on objects of the form $L_i X_i$. The quadrifunctor module serves one purpose in the library: the pentagon axiom is an equation between natural transformations of four variables, and `natTrans₄_ext` reduces it to objects of $C$.

#### Monoidal localization

Let $C$ be monoidal. The class `MorphismProperty.IsMonoidal` $W$ says that $W$ is multiplicative and stable under whiskering on both sides: $X \triangleleft g \in W$ and $f \triangleright Y \in W$ for $f, g \in W$. The constructor `MorphismProperty.IsMonoidal.mk'` asks instead that $f \otimes g \in W$ for $f, g \in W$. The lemma `MorphismProperty.tensorHom_mem` gives the converse, by $f \otimes g = (f \triangleright Y_1) \circ (X_2 \triangleleft g)$ and the stability of $W$ under composition. An instance gives `IsMonoidal` for the inverse image of $W$ under a monoidal functor.

Let $L : C \to D$ be a localization functor for a monoidal class $W$, and let $\varepsilon : L(\mathbf{1}) \cong u$ be an isomorphism to an object $u$ of $D$. The type synonym `LocalizedMonoidal` $L\,W\,\varepsilon$ is $D$ with a monoidal structure, and `Localization.Monoidal.toMonoidalCategory` is $L$ as a functor to it. The object $u$ lets the user choose a convenient unit, for example the ring itself in a derived category. The construction has these steps.

1. The lemma `Localization.Monoidal.isInvertedBy₂` says that $(X, Y) \mapsto L(X \otimes Y)$ inverts $W$ in each variable. The reason is the factorization of $f \otimes g$ above. So the tensor product lifts to the bifunctor `Localization.Monoidal.tensorBifunctor` on $D$, with the isomorphism `Localization.Monoidal.μ` $X\,Y : L X \otimes L Y \cong L(X \otimes Y)$.
2. The unitors `Localization.Monoidal.leftUnitor` and `Localization.Monoidal.rightUnitor` are lifts of the unitors of $C$, composed with $\varepsilon$. The associator `Localization.Monoidal.associator` is an instance of `Localization.associator`.
3. The pentagon follows from `natTrans₄_ext` (the lemma `Localization.Monoidal.pentagon_natTrans`), and the triangle from `natTrans₂_ext` (`Localization.Monoidal.triangle_natTrans`). The constructor `MonoidalCategory.ofBifunctor` then gives the instance.

The functor `toMonoidalCategory` $L\,W\,\varepsilon$ is monoidal, with $\mu$ as tensor comparison and $\varepsilon^{-1}$ as unit comparison. The lemma `Localization.Monoidal.associator_hom_app` and the naturality lemmas such as `Localization.Monoidal.μ_natural_left` compute with the structure.

The module `Monoidal.Braided` adds the braiding. When $C$ is braided, the braiding of $C$ lifts to `Localization.Monoidal.braidingNatIso`, an isomorphism between the tensor bifunctor and its flip. The hexagon axioms reduce by `natTrans₃_ext` to `Localization.Monoidal.map_hexagon_forward` and `Localization.Monoidal.map_hexagon_reverse`, which hold in $C$. This gives the instance `Localization.Monoidal.instBraidedCategoryLocalizedMonoidal`, and the localization functor is braided. When $C$ is symmetric, `Localization.Monoidal.instSymmetricCategoryLocalizedMonoidal` makes the localized category symmetric.

The module `Monoidal.Functor` gives a universal property. Let $L : C \to D$ be a monoidal localization functor, and let $F : D \to E$ be a functor to a monoidal category with a lifting $F \circ L \cong G$, where $G : C \to E$ is monoidal. Then `Localization.Monoidal.functorMonoidalOfComp` is a monoidal structure on $F$. Its tensor comparison at $L X$ and $L Y$ is given by `Localization.Monoidal.functorMonoidalOfComp_μ`: it is the comparison of $G$, transported along the lifting isomorphism and the comparison of $L$. The key step is `Localization.Monoidal.curriedTensorPreIsoPost`, the lift of $G(-) \otimes G(-) \cong G(- \otimes -)$ to $F(-) \otimes F(-) \cong F(- \otimes -)$ by `lift₂NatIso`. The instance `Localization.Monoidal.lifting_isMonoidal` then says that the lifting isomorphism is a monoidal natural transformation. The definition is not an instance, because $F$ can carry another monoidal structure.

#### Common errors

1. A user forgets the hypothesis `W.ContainsIdentities`. Without it the product $L_1 \times L_2$ need not be a localization functor, and `lift₂` does not apply. Most classes of weak equivalences contain the identities, so the instance is usually found, but a class defined by hand needs it.
2. A user puts the monoidal instance on $D$ itself. The structure lives on the type synonym `LocalizedMonoidal L W ε`, and the functor to it is `toMonoidalCategory L W ε`, not $L$. A lemma about $L$ must be stated for this functor to use the monoidal structure.
3. A user tries to prove an equation of lifted natural transformations by evaluation at all objects of $D$. The objects of $D$ are only isomorphic to objects $L X$, so this is hard. The lemmas `natTrans₂_ext`, `natTrans₃_ext` and `natTrans₄_ext` reduce the equation to objects of the form $L X$, where `lift₂NatTrans_app_app` computes it.

### Exercises

1. (A) Let $W_1$ and $W_2$ contain the identities. Show that a morphism $(f_1, f_2)$ of $C_1 \times C_2$ is a composition of two morphisms of $W_1 \times W_2$ when $f_1 \in W_1$ and $f_2 \in W_2$, and explain why this fails without identities.
2. (A) Prove `MorphismProperty.tensorHom_mem` from `whiskerLeft_mem`, `whiskerRight_mem` and the fact that $W$ is multiplicative.
3. (B) Let $L : C \to D$ be a localization functor, and let $W$ be stable under binary products. Show directly that $L(X \times Y)$ is a product of $L X$ and $L Y$ in $D$, using only `Functor.IsLocalization.prod` and the lift of the product bifunctor.
4. (B) Let $R$ be a commutative ring and let $W$ be the quasi-isomorphisms between bounded above complexes of projective $R$-modules. Show that $W$ is monoidal for the tensor product of complexes, and state what `LocalizedMonoidal` gives.
5. (B) Let $F_1', F_2' : D_1 \to D_2 \to D_3 \to E$ lift $F_1$ and $F_2$. Prove `natTrans₃_ext` from `natTrans₂_ext` and the one-variable `Localization.natTrans_ext`.
6. (C) Let $C$ be symmetric monoidal and let $W$ be monoidal. Use `natTrans₂_ext` to show that the lifted braiding of `LocalizedMonoidal L W ε` composed with its flip is the identity, so that the localized category is symmetric.

### Reference

<?reference?>
