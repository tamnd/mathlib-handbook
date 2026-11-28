---
title: Closure of properties of objects under limits and colimits
kind: api
modules:
  - Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
  - Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
  - Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
  - Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
  - Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
  - Mathlib.CategoryTheory.ObjectProperty.BinaryProductsClosure
  - Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
  - Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
  - Mathlib.CategoryTheory.ObjectProperty.IsClosedUnderCardinalFilteredColimits
  - Mathlib.CategoryTheory.ObjectProperty.HasCardinalLT
  - Mathlib.CategoryTheory.ObjectProperty.Small
  - Mathlib.CategoryTheory.ObjectProperty.Ind
  - Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
  - Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.ExactColimits
explains:
  E2: [CategoryTheory.ObjectProperty.colimitsOfShape, CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape, CategoryTheory.ObjectProperty.colimitsOfShape_eq_unop_limitsOfShape, CategoryTheory.ObjectProperty.limitsClosure_le, CategoryTheory.ObjectProperty.isEssentiallySmall_limitsClosure, CategoryTheory.ObjectProperty.EssentiallySmall.exists_eq_isoClosure_ofObj, CategoryTheory.ObjectProperty.ind_ind, CategoryTheory.ObjectProperty.preservesLimitsOfShape_eq_iInf]
  E1: auto
families: []
requires: [V24.C02, V24.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Closure of properties of objects under limits and colimits

### Overview

Section 1 defined a property of objects `P : ObjectProperty C` and its full subcategory. Many properties of interest are closed under some limits or colimits. The finitely presentable objects are closed under finite colimits, the injective objects are closed under products, the sheaves are closed under all limits, and the functors that preserve finite limits are closed under filtered colimits of sets. These modules give one language for all such statements. They define the objects that are limits or colimits of a given shape of objects of $P$, the type classes that say that $P$ is closed under limits or colimits of a shape, and the smallest property that contains $P$ and is closed.

The second theme is size. A closure under colimits is built by iteration, and a reader needs to know that the result is still essentially small when $P$ is. The modules on smallness, on cardinal bounds and on ind-objects give the tools for this. The last two modules apply the language to functor categories: the functors that preserve a class of limits form a property of objects of `J ⥤ C`, and its closure under colimits is a form of the commutation of limits and colimits.

### The library around it

#### Limits and colimits of a shape

Fix a category $J$. For `P : ObjectProperty C` there are two properties. The property `ObjectProperty.strictLimitsOfShape` holds exactly for the chosen objects `limit F`, where `F : J ⥤ C` has a limit and each `F.obj j` satisfies $P$. The property `ObjectProperty.limitsOfShape` holds for each object $X$ that is the point of some limit cone of such a functor. It is defined as the nonempty type of data `ObjectProperty.LimitOfShape`, a structure that extends `Limits.LimitPresentation` with the field `prop_diag_obj`. The colimit side is the same: `ObjectProperty.strictColimitsOfShape`, `ObjectProperty.colimitsOfShape` and the structure `ObjectProperty.ColimitOfShape`, which extends `Limits.ColimitPresentation`. The strict form exists only for a size argument: it is small when $P$, $J$ and the hom types are small, and `ObjectProperty.isoClosure_strictColimitsOfShape` says that its closure under isomorphisms is `colimitsOfShape`.

The data `ColimitOfShape J X` has a small calculus. The function `ObjectProperty.ColimitOfShape.colimit` gives the chosen colimit, `ObjectProperty.ColimitOfShape.ofIso` moves the data along an isomorphism $X \cong Y$, `ObjectProperty.ColimitOfShape.ofLE` enlarges $P$, and `ObjectProperty.ColimitOfShape.reindex` changes the index along a final functor $J' \to J$. The last gives `ObjectProperty.colimitsOfShape_le_of_final` and, for an equivalence $J \simeq J'$, the equality `ObjectProperty.colimitsOfShape_congr`. The dual statements for limits use initial functors, as in `ObjectProperty.limitsOfShape_le_of_initial`.

**Definition.** The property $P$ is *closed under colimits of shape $J$* if $\mathrm{colim}_J(P) \le P$, where $\mathrm{colim}_J(P)$ is `colimitsOfShape P J`. The class is `ObjectProperty.IsClosedUnderColimitsOfShape`, with the one field `colimitsOfShape_le`. The limit form is `ObjectProperty.IsClosedUnderLimitsOfShape`.

A closed property need not be closed under isomorphisms: for an empty $J$ the class only asks that $P$ contains the initial objects. To prove the class, the constructor `ObjectProperty.IsClosedUnderColimitsOfShape.mk'` asks only for the strict colimits, when $P$ is already closed under isomorphisms. To use the class, the lemmas `ObjectProperty.prop_of_isColimit` and `ObjectProperty.prop_colimit` give $P(c_{\mathrm{pt}})$ for a colimit cocone $c$ of a diagram in $P$. The limit forms are `ObjectProperty.prop_of_isLimit` and `ObjectProperty.prop_limit`. The class passes to infima of properties, to inverse images along a functor that preserves the colimits (`ObjectProperty.IsClosedUnderColimitsOfShape.inverseImage`), and along equivalences of index categories (`ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence`).

**Proposition (duality).** For each $P$ and $J$,
$$\mathrm{colim}_J(P) = \bigl(\lim_{J^{\mathrm{op}}}(P^{\mathrm{op}})\bigr)^{\mathrm{unop}},$$
and $P$ is closed under colimits of shape $J$ if and only if $P^{\mathrm{op}}$ is closed under limits of shape $J^{\mathrm{op}}$.

*Proof.* A cocone $c$ over $F : J \to C$ is a colimit if and only if $c^{\mathrm{op}}$ is a limit cone over $F^{\mathrm{op}} : J^{\mathrm{op}} \to C^{\mathrm{op}}$. The objects of the diagram are the same, so the property of each $F(j)$ does not change. This proves the equality, and the second statement follows because $Q \mapsto Q^{\mathrm{op}}$ preserves the order. $\square$

The equality is `ObjectProperty.colimitsOfShape_eq_unop_limitsOfShape`, and the equivalence is `ObjectProperty.isClosedUnderColimitsOfShape_iff_op`. There are eight such lemmas for the four combinations of `op` and `unop`, and instances apply them in each direction. Many colimit results of the library come from their limit forms by this duality. For an empty index, `ObjectProperty.colimitsOfShape_isEmpty_iff` says that $\mathrm{colim}_J(P)$ holds exactly for the initial objects, whatever $P$ is.

**Proposition (retracts).** If $P$ is closed under coequalizers, then $P$ is stable under retracts.

*Proof.* Let $i : X \to Y$ and $r : Y \to X$ with $r \circ i = 1_X$, and let $P(Y)$ hold. Then $r$ is a coequalizer of $i \circ r$ and $1_Y$. Indeed $r \circ (i \circ r) = r = r \circ 1_Y$. If $s : Y \to Z$ has $s \circ i \circ r = s$, then $s \circ i$ is a map $X \to Z$ with $(s \circ i) \circ r = s$, and it is unique because $r$ is a split epimorphism. The diagram has the object $Y$ twice, so $P(X)$ holds. $\square$

In Lean this is an instance from `IsClosedUnderColimitsOfShape P WalkingParallelPair` to `ObjectProperty.IsStableUnderRetracts`, and the dual instance is also there.

#### Products and finite limits

The common shapes have their own names. The abbreviation `ObjectProperty.IsClosedUnderBinaryProducts` is closure under limits of shape `Discrete WalkingPair`, and the class `ObjectProperty.IsClosedUnderFiniteProducts` asks for closure under `Discrete J` for each finite type $J$. The lemma `ObjectProperty.IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape` checks the class at any universe, and the constructor `ObjectProperty.IsClosedUnderFiniteProducts.mk'` builds it from binary products and the empty product, when $C$ has finite products. The use lemmas follow one pattern: `ObjectProperty.prop_prod`, `ObjectProperty.prop_terminal`, `ObjectProperty.prop_product`, `ObjectProperty.prop_of_isLimit_fan` and `ObjectProperty.prop_of_isLimit_binaryFan`, and the coproduct forms `ObjectProperty.prop_coprod`, `ObjectProperty.prop_initial` and `ObjectProperty.prop_coproduct`. A property with `ObjectProperty.ContainsZero` that is closed under isomorphisms is closed under the empty product and the empty coproduct, by an instance.

The class `ObjectProperty.IsClosedUnderFiniteLimits` asks for closure under limits of shape $J$ for each finite category $J$, and `ObjectProperty.IsClosedUnderFiniteColimits` is the dual. Under these classes, instances give `HasFiniteLimits P.FullSubcategory` and `PreservesFiniteLimits P.ι`. So a full subcategory closed under finite limits inherits the finite limits of $C$, and the inclusion preserves them.

#### Closures

**Definition.** Let $(J_a)_{a \in A}$ be a family of categories. The *closure* $\overline{P}$ of $P$ under limits of the shapes $J_a$ is the smallest property that contains $P$, is closed under isomorphisms and is closed under limits of each shape $J_a$.

The Lean definition `ObjectProperty.limitsClosure` is an inductive predicate with two rules: each object of $P$ is in the closure, and a limit of a diagram of shape $J_a$ in the closure is in the closure. The abbreviation `ObjectProperty.limitClosure` takes one shape. The colimit forms are `ObjectProperty.colimitsClosure` and `ObjectProperty.colimitClosure`, and `ObjectProperty.colimitsClosure_eq_unop_limitsClosure` relates the two. The abbreviations `ObjectProperty.binaryProductsClosure` and `ObjectProperty.binaryCoproductsClosure` take the shape `Discrete WalkingPair`.

**Proposition (universal property).** If $Q$ is closed under isomorphisms and under limits of each shape $J_a$, and $P \le Q$, then $\overline{P} \le Q$.

*Proof.* Induction on the two rules. An object of $P$ is in $Q$. If $X$ is a limit of a diagram $F$ of shape $J_a$ whose objects are in $\overline{P}$, then by induction they are in $Q$, so $X$ is in $Q$ by the closure of $Q$. $\square$

This is `ObjectProperty.limitsClosure_le`, and the colimit form is `ObjectProperty.colimitsClosure_le`. The usual corollaries follow: `ObjectProperty.le_limitsClosure`, `ObjectProperty.limitsClosure_monotone`, `ObjectProperty.limitsClosure_eq_self` for a closed $P$, and `ObjectProperty.limitsClosure_isoClosure`. For binary products the lemma `ObjectProperty.binaryProductsClosure_le_iff` shows that $\overline{P} \le Q$ if and only if $P \le Q$.

The closure is not small in general, because the inductive definition does not show its size. The file `LimitsClosure` gives a second construction. The step `ObjectProperty.strictLimitsClosureStep` adds to $P$ the chosen limits of diagrams in $P$, and `ObjectProperty.strictLimitsClosureIter` iterates the step along a well-ordered type, with suprema at limit stages.

**Theorem (smallness of the closure).** Let $P$ be essentially $w$-small, let $C$ be locally $w$-small, and let $A$ and each $J_a$ be $w$-small with $w$-small hom types. Then the closure of $P$ under limits of the shapes $J_a$ is essentially $w$-small.

*Proof sketch.* Choose a regular cardinal $\kappa$ such that each $J_a$ has fewer than $\kappa$ objects. Each stage of the iteration is small, by induction. At the stage $\kappa$, a diagram of shape $J_a$ in the union of the earlier stages has fewer than $\kappa$ objects. Each object comes from a stage below $\kappa$, and $\kappa$ is regular, so the whole diagram comes from one stage below $\kappa$. So the stage $\kappa$ is stable under the step (`ObjectProperty.strictLimitsClosureStep_strictLimitsClosureIter_eq_self`). Its closure under isomorphisms is then the closure $\overline{P}$ (`ObjectProperty.isoClosure_strictLimitsClosureIter_eq_limitsClosure`), and it is small. $\square$

The result is `ObjectProperty.isEssentiallySmall_limitsClosure`, also as an instance for both limits and colimits. The module `ColimitsCardinalClosure` takes for the family all the small categories $J$ with fewer than $\kappa$ arrows, given by `SmallCategoryCardinalLT.categoryFamily`. The result `ObjectProperty.colimitsCardinalClosure` is essentially small when $P$ is, and `ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure` shows that it is closed under colimits of each such shape $J$, not only those of the family. For a regular $\kappa$ it is stable under retracts, by the proposition on retracts above.

#### Size

The module `Small` defines `ObjectProperty.Small`, an abbreviation for `Small.{w} (Subtype P)`, and the class `ObjectProperty.EssentiallySmall`: $P$ is contained in the closure under isomorphisms of a small property. Instances show that both notions pass to `op`, to finite and small suprema, to infima, and to the image under a functor. The lemma `ObjectProperty.Small.exists_eq_ofObj` writes a small property as `ObjectProperty.ofObj X` for a family $X : I \to C$ with $I$ in the universe $w$.

**Proposition.** If $P$ is closed under isomorphisms and essentially $w$-small, then there are a type $I$ in universe $w$ and a family $X : I \to C$ with $P = \mathrm{isoClosure}(\{X_i\})$.

*Proof.* By definition $P \le \mathrm{isoClosure}(Q)$ for a small $Q$. Replace $Q$ by the objects of $Q$ that are isomorphic to an object of $P$. This is still small, by `ObjectProperty.Small.of_le`, and it is contained in $P$ because $P$ is closed under isomorphisms. So $P = \mathrm{isoClosure}(Q)$, and $Q$ has the form `ofObj X`. $\square$

This is `ObjectProperty.EssentiallySmall.exists_eq_isoClosure_ofObj`. The bridge to the classes of Volume 24 is `essentiallySmall_iff_objectPropertyEssentiallySmall`: a category is essentially $w$-small if and only if it is locally $w$-small and its top property is essentially $w$-small. The module `HasCardinalLT` gives the finer bound `ObjectProperty.HasCardinalLT`, the condition that fewer than $\kappa$ objects satisfy $P$, with `ObjectProperty.HasCardinalLT.sup` and `ObjectProperty.HasCardinalLT.iSup` for unions.

#### Filtered colimits and ind-objects

For a regular cardinal $\kappa$, the class `ObjectProperty.IsClosedUnderCardinalFilteredColimits` asks that $P$ is closed under colimits of shape $J$ for each small $\kappa$-filtered category $J$. A full subcategory with this property is *accessibly embedded*. Such a property is closed under isomorphisms, by `ObjectProperty.IsClosedUnderCardinalFilteredColimits.isClosedUnderIsomorphisms`: the category with one object is $\kappa$-filtered, and an object isomorphic to $X$ is a colimit of the constant diagram at $X$. When $C$ has $\kappa$-filtered colimits, instances give the same colimits in `P.FullSubcategory`, and the inclusion `P.ι` is `Functor.IsCardinalAccessible`.

The module `Ind` defines `ObjectProperty.ind`: $X$ satisfies `ind P` if $X$ is the colimit of a small filtered diagram of objects of $P$. The lemma `ObjectProperty.le_ind` gives $P \le \mathrm{ind}(P)$, and `ObjectProperty.of_essentiallySmall_index` allows an essentially small index category.

**Theorem.** If each object of $P$ is finitely presentable and $C$ is locally $w$-small, then $\mathrm{ind}(\mathrm{ind}(P)) = \mathrm{ind}(P)$.

The proof writes a filtered colimit of filtered colimits as one filtered colimit, and uses that each map from a finitely presentable object to a filtered colimit factors through a stage. The theorem is `ObjectProperty.ind_ind`. In a finitely accessible category, `ObjectProperty.ind_iff_exists` gives a test: $X$ satisfies `ind P` if and only if each map $Z \to X$ from a finitely presentable $Z$ factors through an object of $P$. The lemmas `ObjectProperty.ind_inverseImage_le` and `ObjectProperty.ind_inverseImage_eq_of_isEquivalence` move `ind` along functors, and the instance `ObjectProperty.isClosedUnderLimitsOfShape_ind_discrete` gives closure under products when products commute with filtered colimits in the sense of `Limits.IsIPCOfShape`.

#### Functors that preserve limits

The module `FunctorCategory.PreservesLimits` turns the classes of preservation of Volume 24 into properties of objects of the functor category `J ⥤ C`. For `F : K ⥤ J`, the property `ObjectProperty.preservesLimit` holds for the functors $G$ with `PreservesLimit F G`, and `ObjectProperty.preservesLimitsOfShape`, `ObjectProperty.preservesFiniteLimits` and the colimit forms follow the same pattern. The simp lemmas such as `ObjectProperty.preservesLimit_iff` unfold the property to the class.

**Proposition.** A functor preserves the limits of shape $K$ if and only if it preserves the limit of each functor $F : K \to J$: as properties, $\mathrm{pres}_K = \bigwedge_F \mathrm{pres}_F$.

*Proof.* This is the definition of `PreservesLimitsOfShape` as a class with one field over all $F$. $\square$

This is `ObjectProperty.preservesLimitsOfShape_eq_iInf`, with the forms `ObjectProperty.preservesColimitsOfShape_eq_iInf`, `ObjectProperty.preservesFiniteLimits_eq_iInf` and `ObjectProperty.preservesFiniteColimits_eq_iInf`. Since closure under retracts and isomorphisms passes to infima, each of these properties is stable under retracts. The infimum also transfers closure under colimits: the property `preservesColimit F` is closed under all colimits of shape $K'$ that exist in $C$, since colimits commute with colimits, and so is `preservesColimitsOfShape K`.

The module `FunctorCategory.ExactColimits` treats the mixed case. If the functor `colim` of shape $K'$ preserves the limits of shape $K$, then the functors $J \to C$ that preserve limits of shape $K$ are closed under colimits of shape $K'$. The proof computes the colimit $G$ of the diagram pointwise, as $j \mapsto \mathrm{colim}_{k'} G_{k'}(j)$, and writes $G$ as the composite of the flipped diagram $J \to (K' \to C)$ with `colim`. Both factors preserve limits of shape $K$. With `HasExactColimitsOfShape`, the same holds for the functors that preserve finite limits.

#### Common errors

1. `colimitsOfShape P J` and `strictColimitsOfShape P J` are different properties. Only the first is closed under isomorphisms. A lemma that needs `IsClosedUnderIsomorphisms` does not apply to the strict form.
2. `IsClosedUnderColimitsOfShape P J` is a class for one shape $J$. A statement for all small filtered categories must quantify over $J$ in a fixed universe, as `IsClosedUnderCardinalFilteredColimits` does. For finite products the class `IsClosedUnderFiniteProducts` quantifies over `Type`, and `IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape` moves between universes.
3. `ObjectProperty.ind` has a universe parameter, written `ind.{w} P`. Without it Lean can choose a universe that does not match the size of the index categories, and the goal does not close.

### Exercises

1. (A) Prove that a property closed under binary products and the empty product is closed under all finite products, by induction on the size of the index.
2. (A) Show that `colimitsOfShape P J` for an empty $J$ holds exactly for the initial objects, and deduce that a property closed under colimits of the empty shape contains all initial objects.
3. (B) In the category of abelian groups, describe the closure of $\{\mathbb{Z}\}$ under finite products and the closure of $\{\mathbb{Z}\}$ under all small colimits.
4. (B) Prove that the closure of $P$ under limits of the shapes $J_a$ is the intersection of all properties $Q \ge P$ that are closed under isomorphisms and under these limits.
5. (B) Let $C$ be the category of sets. Show that a filtered colimit of functors $J \to C$ that preserve finite limits preserves finite limits, from the commutation of filtered colimits with finite limits in sets.
6. (C) Let $P$ be the finite sets in the category of sets. Show that `ind P` holds for every set, and that $\mathrm{ind}(\mathrm{ind}(P)) = \mathrm{ind}(P)$ in this case without the general theorem.

### Reference

<?reference?>
