---
title: Closure properties of presentable objects and pure morphisms
kind: api
modules:
  - Mathlib.CategoryTheory.Presentable.Retracts
  - Mathlib.CategoryTheory.Presentable.Limits
  - Mathlib.CategoryTheory.Presentable.PreservesCardinalPresentable
  - Mathlib.CategoryTheory.Presentable.Adjunction
  - Mathlib.CategoryTheory.Presentable.Dense
  - Mathlib.CategoryTheory.Presentable.EssentiallyLarge
  - Mathlib.CategoryTheory.Presentable.IsDiscrete
  - Mathlib.CategoryTheory.Presentable.ColimitPresentation
  - Mathlib.CategoryTheory.Presentable.Directed
  - Mathlib.CategoryTheory.Presentable.CardinalPure
explains:
  E2: [CategoryTheory.Retract.isCardinalPresentable, CategoryTheory.isCardinalPresentable_of_isColimit, CategoryTheory.Functor.isCardinalAccessible_of_isLimit, CategoryTheory.Functor.PreservesCardinalPresentable, CategoryTheory.Adjunction.isCardinalPresentable_leftAdjoint_obj, CategoryTheory.Adjunction.isCardinalLocallyPresentable, CategoryTheory.isCardinalFilteredGenerator_isCardinalPresentable, CategoryTheory.IsCardinalFiltered.exists_cardinal_directed, CategoryTheory.IsCardinalPure, CategoryTheory.exists_colimitsOfShape_splitMonomorphisms_of_isCardinalPure]
  E1: auto
families: []
requires: [V24.C02, V24.C04, V24.C05, V25.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Closure properties of presentable objects and pure morphisms

### Overview

Section 1 defines a $\kappa$-presentable object $X$ for a regular cardinal $\kappa$: the functor $\mathrm{Hom}(X, -)$ commutes with $\kappa$-filtered colimits. This section collects the operations that keep this property. A retract of a $\kappa$-presentable object is $\kappa$-presentable. A colimit of fewer than $\kappa$ such objects is $\kappa$-presentable, because limits of fewer than $\kappa$ sets commute with $\kappa$-filtered colimits of sets. A left adjoint keeps $\kappa$-presentable objects when its right adjoint is $\kappa$-accessible. The last fact also moves the structure of a locally presentable category to a reflective full subcategory, and to an equivalent category.

The section then gives three tools for the theory. In a $\kappa$-accessible category, each object is the canonical $\kappa$-filtered colimit of the $\kappa$-presentable objects over it, so these objects form a dense subcategory. Each $\kappa$-filtered category has a final functor from a $\kappa$-directed partially ordered set, so a user can replace filtered diagrams by directed ones. And the $\kappa$-pure morphisms, which generalize the pure submodules of algebra, are monomorphisms in a $\kappa$-accessible category and are $\kappa$-filtered colimits of split monomorphisms.

In the text, $\kappa$ is a regular cardinal, written `κ : Cardinal.{w}` with the instance `[Fact κ.IsRegular]`. The library writes `IsCardinalPresentable X κ` for the class of Section 1 and `isCardinalPresentable C κ` for the corresponding property of objects.

### The library around it

**Retracts and small colimits.** In `Mathlib.CategoryTheory.Presentable.Retracts`, `Retract.isCardinalPresentable` says that if $Y$ is a retract of a $\kappa$-presentable object $X$, then $Y$ is $\kappa$-presentable. The instance `instIsStableUnderRetractsIsCardinalPresentable` states the same fact for the property `isCardinalPresentable C κ`. The module `Mathlib.CategoryTheory.Presentable.Limits` contains the main closure result. Let $K$ be a category with `HasCardinalLT (Arrow K) κ`, that is, with fewer than $\kappa$ morphisms. The lemma `Functor.isCardinalAccessible_of_isLimit` says that a limit, indexed by $K$, of $\kappa$-accessible functors $C \to \mathrm{Type}$ is $\kappa$-accessible. Its proof works with elements: the auxiliary lemmas `Functor.Accessible.Limits.isColimitMapCocone.surjective` and `Functor.Accessible.Limits.isColimitMapCocone.injective` check the two halves of the colimit property in types, and each uses that a family of fewer than $\kappa$ indices in a $\kappa$-filtered category has an upper bound.

**Theorem.** Let $Y : K \to C$ be a diagram with fewer than $\kappa$ morphisms in $K$, and let each $Y(k)$ be $\kappa$-presentable. Then the colimit of $Y$ is $\kappa$-presentable.

*Proof sketch.* The functor $\mathrm{Hom}(\operatorname{colim} Y, -)$ is the limit over $K^{\mathrm{op}}$ of the functors $\mathrm{Hom}(Y(k), -)$. Each of them is $\kappa$-accessible, and the previous lemma applies. ∎

This is `isCardinalPresentable_of_isColimit` for a locally small category, and `isCardinalPresentable_of_isColimit'` with the size condition replaced by a limit hypothesis on types. The lemma `isClosedUnderColimitsOfShape_isCardinalPresentable` states it as a closure property of `isCardinalPresentable C κ`. For $\kappa = \aleph_0$, it says that finite colimits of finitely presentable objects are finitely presentable.

**Functors and adjunctions.** The class `Functor.PreservesCardinalPresentable F κ`, in `Mathlib.CategoryTheory.Presentable.PreservesCardinalPresentable`, says that $F$ sends $\kappa$-presentable objects to $\kappa$-presentable objects. There are instances for the identity and for composites, and `Functor.PreservesCardinalPresentable.of_iso` moves the class along an isomorphism of functors. The module `Mathlib.CategoryTheory.Presentable.Adjunction` gives the main source of the class.

**Proposition.** Let $F \dashv G$ be an adjunction, with $G : D \to C$ a $\kappa$-accessible functor. If $X$ is $\kappa$-presentable in $C$, then $F(X)$ is $\kappa$-presentable in $D$.

*Proof sketch.* For a $\kappa$-filtered diagram $(Y_j)$ in $D$,
$$\mathrm{Hom}(F X, \operatorname{colim} Y_j) \cong \mathrm{Hom}(X, G(\operatorname{colim} Y_j)) \cong \mathrm{Hom}(X, \operatorname{colim} G Y_j) \cong \operatorname{colim} \mathrm{Hom}(X, G Y_j) \cong \operatorname{colim} \mathrm{Hom}(F X, Y_j).$$
The second step uses that $G$ is $\kappa$-accessible, and the third that $X$ is $\kappa$-presentable. ∎

This is `Adjunction.isCardinalPresentable_leftAdjoint_obj`. When $G$ is also fully faithful, each object $Y$ of $D$ is isomorphic to $F(G(Y))$, so the images under $F$ of a generating family of $C$ generate $D$. This gives `Adjunction.isCardinalFilteredGenerator`, `Adjunction.hasCardinalFilteredGenerator`, `Adjunction.isCardinalLocallyPresentable` and `Adjunction.isCardinalAccessibleCategory`. An equivalence is such an adjunction, and `Equivalence.isCardinalLocallyPresentable`, `Equivalence.isLocallyPresentable`, `Equivalence.isCardinalAccessibleCategory` and `Equivalence.isAccessibleCategory` move each structure along it.

**Density and size.** In `Mathlib.CategoryTheory.Presentable.Dense`, `isCardinalFilteredGenerator_isCardinalPresentable` says that in a $\kappa$-accessible category, the $\kappa$-presentable objects themselves form a $\kappa$-filtered generator. An instance says that the inclusion of their full subcategory is a dense functor (`Functor.IsDense`): each object $X$ is the colimit over the category of $\kappa$-presentable objects over $X$, and another instance says that this category is $\kappa$-filtered. The instance `IsCardinalAccessibleCategory.final_toCostructuredArrow` compares a given $\kappa$-filtered presentation of $X$ with this canonical one. The module `Mathlib.CategoryTheory.Presentable.EssentiallyLarge` uses the small generator: `HasCardinalFilteredGenerator.exists_equivalence` says that the category is equivalent to a category with objects in `Type (w + 1)` and morphisms in `Type w`. The module `Mathlib.CategoryTheory.Presentable.IsDiscrete` gives the smallest example: in a discrete category each object is $\kappa$-presentable, by `IsDiscrete.isCardinalPresentable`, and a category with exactly one object and one morphism is locally presentable.

**Directed posets and nested presentations.** The module `Mathlib.CategoryTheory.Presentable.Directed` proves the result of Deligne in SGA 4. The lemma `IsCardinalFiltered.exists_cardinal_directed` says that for a small $\kappa$-filtered category $J$ there are a $\kappa$-directed partial order $\alpha$ and a final functor $\alpha \to J$. The case $\kappa = \aleph_0$ is `IsFiltered.exists_directed`. The proof uses the partial order of the finite diagrams in $J$ with a unique terminal object, `IsCardinalFiltered.exists_cardinal_directed.DiagramWithUniqueTerminal`. These diagrams need not be subcategories. The module `Mathlib.CategoryTheory.Presentable.ColimitPresentation` works with the structure `Limits.ColimitPresentation J X` of a diagram over $J$ with colimit $X$. If each object of the diagram has a presentation by finitely presentable objects over a filtered category, then `Limits.ColimitPresentation.bind` gives a presentation of $X$ over the category `Limits.ColimitPresentation.Total`, whose objects are the pairs $(j, i)$. An instance says that this category is filtered.

**Pure morphisms.** In `Mathlib.CategoryTheory.Presentable.CardinalPure`, a morphism $f : X \to Y$ is $\kappa$-pure, `IsCardinalPure κ f`, when each commutative square from a morphism $l : X' \to Y'$ between $\kappa$-presentable objects to $f$ has a morphism $\rho : Y' \to X$ that makes the upper triangle commute. The property is `isCardinalPure C κ`. Instances say that split monomorphisms are $\kappa$-pure, that $\kappa$-pure morphisms are stable under composition, and that they are stable under $\kappa$-filtered colimits. The lemma `IsCardinalPure.of_postcomp` says that if $g \circ f$ is $\kappa$-pure, so is $f$. In a $\kappa$-accessible category, `IsCardinalAccessibleCategory.mono_iff` tests monomorphisms on $\kappa$-presentable objects, and then `IsCardinalPure.mono` and `isCardinalPure_le_monomorphisms` say that $\kappa$-pure morphisms are monomorphisms. With pushouts, `exists_colimitsOfShape_splitMonomorphisms_of_isCardinalPure` says that a $\kappa$-pure morphism is a $\kappa$-filtered colimit of split monomorphisms. The instance `IsCardinalPure.map` says that a $\kappa$-accessible functor sends $\kappa$-pure morphisms to $\kappa$-pure morphisms.

#### Common errors

1. `isCardinalPresentable_of_isColimit` counts the morphisms of the index category, with `HasCardinalLT (Arrow K) κ`, not its objects. A diagram with few objects and many morphisms does not satisfy the hypothesis.
2. `Adjunction.isCardinalPresentable_leftAdjoint_obj` needs the right adjoint to be $\kappa$-accessible. A left adjoint alone need not keep $\kappa$-presentable objects.
3. A user expects `IsCardinalPure κ f` to imply that $f$ is a monomorphism in any category. The library proves this only in a $\kappa$-accessible category, where the $\kappa$-presentable objects detect equality of morphisms.

### Exercises

1. (A) Use `Retract.isCardinalPresentable` to show that a direct summand of a finitely presentable module is finitely presentable.
2. (A) Show with `isCardinalPresentable_of_isColimit` that the coproduct of two $\kappa$-presentable objects in a locally small category with the needed colimits is $\kappa$-presentable.
3. (B) Let $i : D \to C$ be the inclusion of a reflective full subcategory, with reflector $L$, and let $i$ be $\kappa$-accessible. Show that $L$ preserves $\kappa$-presentable objects and that $D$ is locally $\kappa$-presentable when $C$ is.
4. (B) In the category of abelian groups, show that each split monomorphism is $\aleph_0$-pure by the instance of the library, and check the definition by hand for the inclusion $\mathbb Z \to \mathbb Z \oplus \mathbb Z$.
5. (B) Use `IsFiltered.exists_directed` to explain why a filtered colimit in a category can be computed as a colimit over a directed partial order.
6. (C) Prove on paper that $\kappa$-pure morphisms are stable under composition, and compare the proof with the instance `instIsCardinalPureComp`.

### Reference

<?reference?>
