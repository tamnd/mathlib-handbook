---
title: Sharply smaller cardinals, uniformization and orthogonal reflection
kind: api
modules:
  - Mathlib.CategoryTheory.Presentable.CardinalDirectedPoset
  - Mathlib.CategoryTheory.Presentable.SharplyLT.Basic
  - Mathlib.CategoryTheory.Presentable.SharplyLT.Lemmas
  - Mathlib.CategoryTheory.Presentable.Uniformization
  - Mathlib.CategoryTheory.Presentable.Comma
  - Mathlib.CategoryTheory.Presentable.SolutionSetCondition
  - Mathlib.CategoryTheory.Presentable.OrthogonalReflection
explains:
  E2: [CategoryTheory.CardinalDirectedPoset, CategoryTheory.CardinalDirectedPoset.isCardinalPresentable_iff, Cardinal.SharplyLT, Cardinal.SharplyLT.tfae, Cardinal.SharplyLT.exists_of_small, CategoryTheory.IsCardinalAccessibleCategory.uniformization, CategoryTheory.Comma.isAccessibleCategory, CategoryTheory.SolutionSetCondition.of_isCardinalAccessible, CategoryTheory.OrthogonalReflection.isIso_toSucc_iff, CategoryTheory.MorphismProperty.isLocallyPresentable_isLocal]
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

## Sharply smaller cardinals, uniformization and orthogonal reflection

### Overview

A $\kappa$-accessible category need not be $\lambda$-accessible for each regular $\lambda > \kappa$. The correct relation between the two cardinals is the relation "sharply smaller", written $\kappa \lhd \lambda$. When $\kappa \lhd \lambda$, each $\kappa$-accessible category is $\lambda$-accessible. There are many such $\lambda$: for each small family of regular cardinals there is a regular cardinal that is sharply greater than all of them. This gives the uniformization theorem. For an accessible functor $F : C \to D$ between accessible categories, there is one regular cardinal $\kappa$ such that $C$ and $D$ are $\kappa$-accessible, $F$ is $\kappa$-accessible, and $F$ preserves $\kappa$-presentable objects.

This section describes the category of $\kappa$-directed partial orders that defines the relation, the relation itself, and the uniformization theorem. Two applications follow: comma categories of accessible functors are accessible, and an accessible functor satisfies the solution set condition of the adjoint functor theorem. The last part is the orthogonal reflection construction. For a small class $W$ of morphisms between $\kappa$-presentable objects in a locally $\kappa$-presentable category, the full subcategory of the $W$-local objects is reflective and locally presentable. The construction uses a transfinite iteration, as in the small object argument of Chapter 3.

### The library around it

**The category of directed posets.** In `Mathlib.CategoryTheory.Presentable.CardinalDirectedPoset`, `CardinalDirectedPoset κ` is the full subcategory of `PartOrdEmb`, the category of partial orders and order embeddings, on the $\kappa$-directed partial orders. The predicate is `PartOrdEmb.isCardinalFiltered κ`, so "$\kappa$-directed" and "$\kappa$-filtered" mean the same here. The lemmas `CardinalDirectedPoset.Hom.injective` and `CardinalDirectedPoset.Hom.le_iff_le` say that a morphism is an injective map that keeps and reflects the order. The instance `CardinalDirectedPoset.instIsCardinalAccessibleCategory` says that this category is $\kappa$-accessible: each $\kappa$-directed order is the $\kappa$-filtered union of its $\kappa$-directed subsets of size less than $\kappa$ with a top element. For a regular $\kappa' \ge \kappa$, `CardinalDirectedPoset.isCardinalPresentable_iff` says that an object $J$ is $\kappa'$-presentable if and only if its underlying type has fewer than $\kappa'$ elements.

**Sharply smaller cardinals.** In `Mathlib.CategoryTheory.Presentable.SharplyLT.Basic`, the structure `Cardinal.SharplyLT κ₁ κ₂` has two fields: $\kappa_1 < \kappa_2$, and `CardinalDirectedPoset κ₁` is $\kappa_2$-accessible. The lemma `Cardinal.SharplyLT.tfae` gives the equivalence of these conditions, for $\kappa_1 < \kappa_2$:

1. `Cardinal.SharplyLT κ₁ κ₂`;
2. `CardinalDirectedPoset κ₁` is $\kappa_2$-accessible;
3. each $\kappa_1$-accessible category, with objects in `Type (w + 1)` and morphisms in `Type w`, is $\kappa_2$-accessible;
4. for each type $X$ with fewer than $\kappa_2$ elements, the subsets of $X$ of size less than $\kappa_1$ have a cofinal family of size less than $\kappa_2$;
5. in each $\kappa_1$-directed order, each subset $A$ of size less than $\kappa_2$ is contained in a $\kappa_1$-directed subset of size less than $\kappa_2$.

The lemma `Cardinal.SharplyLT.isCardinalAccessibleCategory` gives the third condition for a category of any size. The generator is `Cardinal.SharplyLT.generator`, the $\kappa_2$-small $\kappa_1$-filtered colimits of $\kappa_1$-presentable objects, and `Cardinal.SharplyLT.isCardinalFilteredGenerator` says that it is a $\kappa_2$-filtered generator. The relation is transitive by `Cardinal.SharplyLT.trans`. The module `Mathlib.CategoryTheory.Presentable.SharplyLT.Lemmas` gives sources of the relation. The lemma `Cardinal.SharplyLT.of_pow_lt` says that $\kappa_1 \lhd \kappa_2$ when $\kappa_1 < \kappa_2$ and $\beta^\alpha < \kappa_2$ for all $\alpha < \kappa_1$ and $\beta < \kappa_2$. Then `Cardinal.SharplyLT.succ_two_pow_of_le` says that $\kappa_1$ is sharply smaller than the successor of $2^{\kappa_2}$ when $\kappa_1 \le \kappa_2$ and $\kappa_2$ is infinite. So `Cardinal.SharplyLT.exists_of_small` gives, for a small family of regular cardinals, a regular cardinal that is sharply greater than each of them, and `Cardinal.SharplyLT.exists_of_pair` and `Cardinal.SharplyLT.exists_of_triple` are the cases of two and three cardinals.

**Uniformization.** The module `Mathlib.CategoryTheory.Presentable.Uniformization` first proves `Cardinal.SharplyLT.exists_retract_of_isCardinalPresentable`: if $\kappa_1 \lhd \kappa_2$, then each $\kappa_2$-presentable object of a $\kappa_1$-accessible category is a retract of a colimit of $\kappa_1$-presentable objects over a $\kappa_1$-directed order with fewer than $\kappa_2$ elements.

**Theorem (uniformization).** Let $F : C \to D$ be an accessible functor between accessible categories. There is a regular cardinal $\kappa$ such that $C$ and $D$ are $\kappa$-accessible, $F$ is $\kappa$-accessible, and $F$ preserves $\kappa$-presentable objects.

*Proof sketch.* Choose $\kappa_1$ such that $C$ and $D$ are $\kappa_1$-accessible and $F$ is $\kappa_1$-accessible. The $\kappa_1$-presentable objects of $C$ form an essentially small family, so their images under $F$ are $\mu$-presentable for one $\mu$. Choose $\kappa \rhd \kappa_1$ with $\kappa \ge \mu$. Then $C$ and $D$ are $\kappa$-accessible. A $\kappa$-presentable object $X$ of $C$ is a retract of a colimit of fewer than $\kappa$ objects that $F$ sends to $\kappa$-presentable objects. The functor $F$ keeps this colimit, since the index order is $\kappa_1$-directed, so $F(X)$ is $\kappa$-presentable by the closure properties of Section 3. ∎

This is `IsCardinalAccessibleCategory.uniformization`. The version for a small family of functors is `IsCardinalAccessibleCategory.uniformization_of_small`, and the version for two functors with different sources and targets is `IsCardinalAccessibleCategory.uniformization_pair`.

**Comma categories and the solution set condition.** In `Mathlib.CategoryTheory.Presentable.Comma`, the instance `Comma.isCardinalAccessibleCategory` says that `Comma F₁ F₂` is $\kappa$-accessible when $F_1$ and $F_2$ are $\kappa$-accessible functors between $\kappa$-accessible categories and $F_1$ preserves $\kappa$-presentable objects. Its $\kappa$-presentable objects are the objects whose two components are $\kappa$-presentable: this is `Comma.isCardinalPresentable_iff`. With uniformization, the instance `Comma.isAccessibleCategory` says that the comma category of two accessible functors into an accessible category is accessible. Instances give the same result for `Arrow`, `Over`, `Under`, `StructuredArrow` and `CostructuredArrow`, and say that the projection functors are accessible. In `Mathlib.CategoryTheory.Presentable.SolutionSetCondition`, the lemma `SolutionSetCondition.of_isCardinalAccessible` says that an accessible functor between accessible categories satisfies `SolutionSetCondition`: for each object $A$ of the target there is a small family of morphisms $A \to F(B_i)$ through which each morphism $A \to F(X)$ factors.

**Orthogonal reflection.** In `Mathlib.CategoryTheory.Presentable.OrthogonalReflection`, let `W : MorphismProperty C`. An object $Z$ is $W$-local (`MorphismProperty.isLocal`) when each $f : X \to Y$ in $W$ gives a bijection $\mathrm{Hom}(Y, Z) \to \mathrm{Hom}(X, Z)$. The construction has two steps for each object $Z$. The morphism `OrthogonalReflection.toStep W Z` attaches, for each $f$ in $W$ and each $X \to Z$, an extension along $f$, by coproducts and a pushout as in the small object argument. The morphism `OrthogonalReflection.fromStep W Z` then coequalizes each pair of morphisms $Y \to$ `OrthogonalReflection.step W Z` that agree after composition with some $f$ in $W$. The composite is `OrthogonalReflection.toSucc W Z`, and `OrthogonalReflection.isIso_toSucc_iff` says that it is an isomorphism if and only if $Z$ is $W$-local. The iteration of this step up to the ordinal of $\kappa$ gives `OrthogonalReflection.reflection W Z κ`, and `OrthogonalReflection.isLocal_reflectionObj` says that its target is $W$-local when the sources and targets of the morphisms in $W$ are $\kappa$-presentable.

The main results are `MorphismProperty.isRightAdjoint_ι_isLocal`, which says that the inclusion of the $W$-local objects has a left adjoint, and `MorphismProperty.isLocallyPresentable_isLocal`, which says that the full subcategory of $W$-local objects is locally $\kappa$-presentable. Both need a small $W$ whose morphisms have $\kappa$-presentable sources and targets. The lemma `MorphismProperty.isClosedUnderCardinalFilteredColimits_isLocal` gives the closure under $\kappa$-filtered colimits that the second result uses, together with `Adjunction.isCardinalLocallyPresentable` of Section 3.

#### Common errors

1. A user tries to pass from a $\kappa_1$-accessible category to a $\kappa_2$-accessible one with only $\kappa_1 < \kappa_2$. The library needs `Cardinal.SharplyLT κ₁ κ₂`, and the inequality alone is not enough.
2. `IsCardinalAccessibleCategory.uniformization` is an existence statement. The cardinal that it gives is not the cardinal of the hypotheses, so the instances for the old cardinal do not apply to the new one.
3. A user takes `OrthogonalReflection.toSucc W Z` for the reflection of $Z$. It is only one step of the construction, and its target need not be $W$-local. The reflection is the transfinite iteration `OrthogonalReflection.reflection W Z κ`.

### Exercises

1. (A) Use `CardinalDirectedPoset.isCardinalPresentable_iff` to describe the finitely presentable objects of `CardinalDirectedPoset ℵ₀`.
2. (A) State `Cardinal.SharplyLT.trans` and derive it from the third condition of `Cardinal.SharplyLT.tfae`.
3. (B) Use `Cardinal.SharplyLT.exists_of_pair` and `Cardinal.SharplyLT.isCardinalAccessibleCategory` to show that a $\kappa_1$-accessible category and a $\kappa_2$-accessible category are both $\kappa$-accessible for one regular $\kappa$.
4. (B) Show that `Arrow C` is accessible when $C$ is accessible, and name the instance of the library.
5. (B) Let $W$ consist of one morphism $f : \emptyset \to \{\ast\}$ in the category of sets. Describe the $W$-local objects, and compute `OrthogonalReflection.toSucc W Z` for a set $Z$.
6. (C) Combine `SolutionSetCondition.of_isCardinalAccessible` with `isRightAdjoint_of_preservesLimits_of_solutionSetCondition` to show that a continuous accessible functor between locally presentable categories has a left adjoint.

### Reference

<?reference?>
