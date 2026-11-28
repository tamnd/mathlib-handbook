---
title: Morphism properties, limits, descent and locality
kind: api
modules:
  - Mathlib.CategoryTheory.MorphismProperty.Limits
  - Mathlib.CategoryTheory.MorphismProperty.Descent
  - Mathlib.CategoryTheory.MorphismProperty.Local
  - Mathlib.CategoryTheory.MorphismProperty.LocalClosure
  - Mathlib.CategoryTheory.MorphismProperty.LocalEpi
  - Mathlib.CategoryTheory.MorphismProperty.Concrete
  - Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
  - Mathlib.CategoryTheory.MorphismProperty.IsSmall
  - Mathlib.CategoryTheory.MorphismProperty.HasCardinalLT
  - Mathlib.CategoryTheory.MorphismProperty.Ind
  - Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
  - Mathlib.CategoryTheory.MorphismProperty.Quotient
explains:
  E2: [CategoryTheory.MorphismProperty.isStableUnderBaseChange_iff_pullbacks_le, CategoryTheory.MorphismProperty.universally_eq_iff, CategoryTheory.MorphismProperty.diagonal_isomorphisms, CategoryTheory.MorphismProperty.functorCategory_monomorphisms, CategoryTheory.MorphismProperty.iff_of_isPullback, CategoryTheory.MorphismProperty.IsLocalAtTarget.mk_of_isStableUnderBaseChange, CategoryTheory.MorphismProperty.sourceLocalClosure.le_of_isLocalAtSource, CategoryTheory.ObjectProperty.localEpi_top_eq_epimorphisms, CategoryTheory.MorphismProperty.le_ind, CategoryTheory.MorphismProperty.quotient_iff]
  E1: auto
families: []
requires: [V24.C01, V24.C04, V25.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Morphism properties, limits, descent and locality

### Overview

Section 1 defined a property of morphisms as a predicate `MorphismProperty C` and studied closure under isomorphisms and under composition. Geometry asks for more. A class such as the flat maps must be stable under base change, and it must be local on the target: a map is flat when it is flat over each member of an open cover.

This section describes the part of the library that relates a morphism property to limits, colimits and covers. The module `Mathlib.CategoryTheory.MorphismProperty.Limits` holds the stability classes for base change, cobase change, limits and colimits of a fixed shape, and the two operations `diagonal` and `universally`. Descent and locality for a precoverage come next. Smaller modules treat concrete categories, functor categories, size, the ind-closure, and quotient categories.

The text writes $g \circ f$ for the composite, and Mathlib writes `f ≫ g`. In a pullback square, the map $X \times_S Y \to X$ is the *base change* of $g : Y \to S$ along $f : X \to S$.

### The library around it

#### Base change and cobase change

The class `MorphismProperty.IsStableUnderBaseChange P` has one field `of_isPullback`: for each pullback square `IsPullback f' g' g f`, if $P(g)$ then $P(g')$. The dual class `IsStableUnderCobaseChange` asks the same for pushout squares. The lemmas `pullback_fst`, `pullback_snd`, `pushout_inl` and `pushout_inr` apply the classes to the chosen pullbacks and pushouts of `HasPullback` and `HasPushout`. To prove the class, the constructor `IsStableUnderBaseChange.mk'` asks only about the chosen pullbacks, for a property that respects isomorphisms. The instances cover the basic cases: `IsStableUnderBaseChange.isomorphisms`, `IsStableUnderBaseChange.monomorphisms`, `IsStableUnderCobaseChange.epimorphisms`, the top property, and the intersection of two stable properties. The instance `IsStableUnderBaseChange.op` passes to the opposite category, where the class becomes cobase change.

The class of all base changes of morphisms of $P$ is `P.pullbacks`, and the dual is `P.pushouts`. It is the smallest stable class above $P$.

**Proposition.** $P$ is stable under base change if and only if $\mathrm{pullbacks}(P) \le P$. This is `isStableUnderBaseChange_iff_pullbacks_le`.

*Proof.* A morphism of $\mathrm{pullbacks}(P)$ is a base change of a morphism of $P$, so stability gives one direction. Conversely, if $g'$ is a base change of $g \in P$, then $g' \in \mathrm{pullbacks}(P) \le P$. $\square$

Some classes are stable only along some maps, or have pullbacks only along some maps. The library has a relative form for each condition.

| Lean name | Statement |
|---|---|
| `MorphismProperty.HasPullbacksAlong` | each $g \in P$ with the codomain of $f$ has a pullback along $f$ |
| `MorphismProperty.HasPullbacks` | each $f \in P$ has a pullback along every map |
| `MorphismProperty.IsStableUnderBaseChangeAlong` | each base change of $g \in P$ along the fixed map $f$ is in $P$ |
| `MorphismProperty.IsStableUnderBaseChangeAgainst` | $P$ is stable under base change along each map of a second class $P'$ |
| `MorphismProperty.isStableUnderBaseChangeAgainst_top_iff` | stability against $\top$ is stability under base change |

The cobase change forms, such as `IsStableUnderCobaseChangeAlong`, are dual.

#### Limits and colimits of a fixed shape

Let $J$ be a category and $W$ a property of morphisms. For a natural transformation $\alpha : F_1 \to F_2$ of functors $J \to C$, write $W(\alpha)$ when each component $\alpha_j$ is in $W$. This is the property `W.functorCategory J` on the functor category. The class `W.limitsOfShape J` holds the maps $\lim F_1 \to \lim F_2$ induced by such $\alpha$, for any limit cones. The dual is `W.colimitsOfShape J`. The classes `IsStableUnderLimitsOfShape W J` and `IsStableUnderColimitsOfShape W J` say that these maps are in $W$, and `isStableUnderLimitsOfShape_iff_limitsOfShape_le` gives the same equivalence as for base change.

The products and coproducts are the discrete shapes: `IsStableUnderProductsOfShape W J` and `IsStableUnderCoproductsOfShape W J` are abbreviations for the shape `Discrete J`. The classes `IsStableUnderFiniteProducts`, `IsStableUnderFiniteCoproducts`, `IsStableUnderCoproducts` and `IsStableUnderFilteredColimits` ask for all finite, all small or all filtered shapes. The class `W.coproducts` is the union of the classes `W.colimitsOfShape (Discrete J)` over $J$ in a universe `w`.

#### The diagonal and the universal closure

For $f : X \to Y$ in a category with pullbacks, the diagonal $\Delta_f : X \to X \times_Y X$ is the map with both components the identity. The property `P.diagonal` holds for $f$ when $P(\Delta_f)$, and `diagonal_iff` unfolds it.

**Proposition.** The diagonal of the isomorphisms is the class of monomorphisms. This is `diagonal_isomorphisms`.

*Proof.* The two projections $p_1, p_2 : X \times_Y X \to X$ satisfy $p_1 \circ \Delta_f = p_2 \circ \Delta_f = 1_X$. If $\Delta_f$ is an isomorphism, then $p_1 = p_2$, and $f \circ u = f \circ v$ gives $u = p_1 \circ (u, v) = p_2 \circ (u, v) = v$. If $f$ is a monomorphism, then $f \circ p_1 = f \circ p_2$ gives $p_1 = p_2$, so $\Delta_f \circ p_1 = 1$ and $\Delta_f$ is an isomorphism. $\square$

The instances say that `P.diagonal` respects isomorphisms, is stable under composition and is stable under base change, when $P$ is. The lemma `hasOfPostcompProperty_iff_le_diagonal` relates the diagonal to cancellation: for $P$ multiplicative and stable under base change, $P(g \circ f)$ and $Q(g)$ give $P(f)$ for all $f$ exactly when $Q \le \mathrm{diagonal}(P)$.

The property `P.universally` holds for $f$ when each base change of $f$ is in $P$. It is the largest property below $P$ that is stable under base change. The lemma `universally_le` gives $\mathrm{universally}(P) \le P$, and `universally_inf` and `universally_mono` describe the operation as a monotone map that preserves intersections.

**Proposition.** $\mathrm{universally}(P) = P$ if and only if $P$ is stable under base change. This is `universally_eq_iff`.

*Proof.* The class `universally P` is stable under base change by the pasting of pullback squares, which gives one direction. If $P$ is stable, each base change of $f \in P$ is in $P$, so $P \le \mathrm{universally}(P)$, and `universally_le` gives the other inclusion. $\square$

#### Descent

The module `Mathlib.CategoryTheory.MorphismProperty.Descent` is about the converse of base change. The class `P.DescendsAlong Q` says: for a pullback square with $f : X \to Z$ in $Q$ and $g : Y \to Z$, if the base change $X \times_Z Y \to X$ of $g$ is in $P$, then $g$ is in $P$. In geometry $Q$ is a class of covers, such as the faithfully flat maps.

**Proposition.** If $P$ is stable under base change and descends along $Q$, then for a pullback square with $f \in Q$, the base change of $g$ is in $P$ if and only if $g$ is in $P$. This is `iff_of_isPullback`, and `pullback_fst_iff` and `pullback_snd_iff` are the forms for chosen pullbacks.

The class is closed under intersection (`DescendsAlong.inf`), and `DescendsAlong.of_le` makes $Q$ smaller. An instance says that `P.diagonal` descends along $Q$ when $P$ does. When the isomorphisms descend along $P$, the lemma `faithful_overPullback_of_isomorphisms_descendsAlong` says that base change `Over.pullback f` along $f \in P$ is a faithful functor. The dual class `CodescendsAlong` is about pushout squares, with the lemmas `of_isPushout_of_codescendsAlong`, `pushout_inl_iff` and `pushout_inr_iff`.

#### Locality for a precoverage

Let $K$ be a precoverage on $C$: for each object $Y$, a set of families $\{U_i \to Y\}$, the covers. The class `P.IsLocalAtTarget K` asks that $P$ respects isomorphisms and that for each cover $\{U_i \to Y\}$ of $K$, a map $f : X \to Y$ is in $P$ if and only if each base change $X \times_Y U_i \to U_i$ is in $P$. The class `P.IsLocalAtSource K` asks that $f$ is in $P$ if and only if each composite $U_i \to X \to Y$ is in $P$, for a cover $\{U_i \to X\}$.

The library states the condition with zero hypercovers, the type `Precoverage.ZeroHypercover K Y` of indexed covering families. The lemmas `IsLocalAtTarget.iff_of_zeroHypercover` and `IsLocalAtSource.iff_of_zeroHypercover` are the main way to use the classes. There are four constructors for each class: `mk_of_iff`, `mk_of_iff_of_zeroHypercover`, `mk_of_small` for covers indexed by a small type, and, at the target, `IsLocalAtTarget.mk_of_isStableUnderBaseChange`.

**Proposition.** Let $K$ have pullbacks and let $P$ be stable under base change. If $P(f)$ follows from $P$ for all base changes of $f$ over a cover, then $P$ is local at the target. This is `IsLocalAtTarget.mk_of_isStableUnderBaseChange`.

*Proof.* The hypothesis gives one direction of the equivalence. The other direction is the stability: the base change of $f \in P$ along $U_i \to Y$ is in $P$. $\square$

The module `Mathlib.CategoryTheory.MorphismProperty.LocalClosure` defines `sourceLocalClosure K P`. It is an inductive property: it contains $P$, it respects isomorphisms, and it is closed under the two operations of the definition of `IsLocalAtSource`. An instance says that it is local at the source.

**Proposition.** If $P \le Q$ and $Q$ is local at the source, then $\mathrm{sourceLocalClosure}(K, P) \le Q$. This is `sourceLocalClosure.le_of_isLocalAtSource`.

*Proof.* Induction on the four constructors. The case of $P$ is the hypothesis $P \le Q$, the case of an isomorphism of arrows uses that $Q$ respects isomorphisms, and the two other cases are the two fields of `IsLocalAtSource` for $Q$. $\square$

With `sourceLocalClosure.le`, the closure is the smallest property above $P$ that is local at the source.

#### Local epimorphisms

Let $P$ be a property of objects. The property of morphisms `P.localEpi` holds for $f : X \to Y$ when $u \circ f = v \circ f$ implies $u = v$ for all $u, v : Y \to Z$ with $Z$ in $P$. For presheaves with $P$ the sheaves for a topology, the local epimorphisms are the maps that become epimorphisms after sheafification.

**Proposition.** For the top property, the local epimorphisms are the epimorphisms. This is `localEpi_top_eq_epimorphisms`.

*Proof.* With no condition on $Z$, the definition is the definition of an epimorphism. $\square$

The class is multiplicative and stable under cobase change, and `localEpi.of_epi` says that each epimorphism is a local epimorphism. For an adjunction $F \dashv G$ with $G$ fully faithful, `localEpi_mem_range_iff_epi` says that $f$ is a local epimorphism for the image of $G$ if and only if $F(f)$ is an epimorphism.

#### Concrete categories and functor categories

In a concrete category the module `Mathlib.CategoryTheory.MorphismProperty.Concrete` defines `MorphismProperty.injective C`, `MorphismProperty.surjective C` and `MorphismProperty.bijective C` by the underlying functions. They are multiplicative and respect isomorphisms, and `bijective_eq_sup` says that the bijective maps are the intersection of the two other classes. The abbreviation `ConcreteCategory.HasSurjectiveInjectiveFactorization C` asks that each map is a surjection followed by an injection, and `functorialSurjectiveInjectiveFactorizationData` gives a functorial factorization in the category of types, through the image of the map.

The module `Mathlib.CategoryTheory.MorphismProperty.FunctorCategory` transfers stability to `W.functorCategory J`. Limits, colimits, pullbacks and pushouts in $J \to C$ are computed objectwise when they exist in $C$. So the instances `IsStableUnderLimitsOfShape.functorCategory` and `IsStableUnderColimitsOfShape.functorCategory` transfer stability, and the same holds for base change, cobase change, retracts and transfinite compositions.

**Proposition.** If $C$ has pullbacks, a natural transformation is a monomorphism if and only if each component is a monomorphism. This is `functorCategory_monomorphisms`.

*Proof sketch.* A map $\alpha$ is a monomorphism exactly when its diagonal is an isomorphism, by `diagonal_isomorphisms`. Pullbacks in $J \to C$ are computed objectwise, so the diagonal of $\alpha$ has the diagonals of the $\alpha_j$ as components. A natural transformation is an isomorphism when each component is one. $\square$

The lemmas `functorCategory_isomorphisms` and `functorCategory_epimorphisms` are the other two cases.

#### Size, ind-closure, object properties and quotients

The class `MorphismProperty.IsSmall.{w} W` says that the set `W.toSet` of arrows in $W$ is `w`-small, and `isSmall_iff_eq_ofHoms` says that $W$ is then `MorphismProperty.ofHoms f` for a family $f$ indexed by a small type. The abbreviation `W.HasCardinalLT κ` says that this set has cardinality less than $\kappa$. The lemmas `HasCardinalLT.sup` and `HasCardinalLT.iSup` bound unions.

The module `Mathlib.CategoryTheory.MorphismProperty.Ind` defines `P.ind`. A map $f : X \to Y$ is in `P.ind` when $Y$ is a filtered colimit of objects $Y_i$ and $f$ factors as $X \to Y_i \to Y$ with $X \to Y_i$ in $P$, compatibly in $i$. Ind-étale maps of rings are the main example.

**Proposition.** $P \le \mathrm{ind}(P)$. This is `le_ind`.

*Proof.* Take the index category with one object and the constant diagram at $Y$. Then $f$ factors as $f$ followed by $1_Y$. $\square$

The class is stable under cobase change when $P$ is. When each map of $P$ is finitely presentable, `ind_ind` gives $\mathrm{ind}(\mathrm{ind}(P)) = \mathrm{ind}(P)$. The class `PreIndSpreads P` says that a map of $P$ out of a filtered colimit is a pushout of a map of $P$ out of one stage. With it, `IsStableUnderComposition.ind_of_preIndSpreads` and `IsMultiplicative.ind_of_preIndSpreads` transfer composition to `P.ind`.

For two object properties $P$ and $Q$, `MorphismProperty.ofObjectProperty P Q` holds for $f : X \to Y$ when $P(X)$ and $Q(Y)$. The lemma `ofObjectProperty_inverseImage` computes its inverse image along a functor.

Let `homRel` be a relation on morphisms that is stable under composition on both sides. The class `W.HasQuotient homRel` says that related maps are both in $W$ or both not in $W$. Then `W.quotient homRel` is the property of the quotient category `Quotient homRel` of the images of maps of $W$.

**Proposition.** For $f$ in $C$, the image of $f$ in the quotient is in `W.quotient homRel` if and only if $f$ is in $W$. This is `quotient_iff`.

*Proof sketch.* If the image of $f$ equals the image of some $f' \in W$, then $f$ and $f'$ are related by the equivalence relation that `homRel` generates. The lemma `HasQuotient.iff_of_eqvGen` extends the hypothesis to this relation by induction, so $f \in W$. $\square$

So $W$ is the inverse image of `W.quotient homRel` under the quotient functor.

#### Common errors

1. The base change in `IsStableUnderBaseChange` goes from the right map of the square `IsPullback f' g' g f` to the left map $g'$. The name `pullback_snd` gives $P$ for `pullback.snd f g` from $P(f)$, and `pullback_fst` gives $P$ for `pullback.fst f g` from $P(g)$. Read the statement before applying the lemma.
2. `P.diagonal` uses the chosen pullback $X \times_Y X$, so it needs `HasPullbacks C`. The property `P.universally` needs no such instance, because it quantifies over all pullback squares. Do not look for a `HasPullbacks` argument in the lemmas on `universally`.
3. `IsLocalAtTarget P K` takes a precoverage `K`, not a Grothendieck topology. For a topology, pass the precoverage of its covering families, and use the zero hypercover lemmas rather than the presieve fields.

### Exercises

1. (A) Show that the top property and the isomorphisms are stable under base change, and that $\mathrm{pullbacks}(\mathrm{pullbacks}(P)) = \mathrm{pullbacks}(P)$.
2. (A) Show that $\mathrm{universally}(P \cap Q) = \mathrm{universally}(P) \cap \mathrm{universally}(Q)$, as in `universally_inf`.
3. (B) In a category with pullbacks, show that a property stable under base change and composition is stable under products of two maps over a base: if $f : X \to S$ and $g : Y \to S$ are in $P$, then $X \times_S Y \to S$ is in $P$.
4. (B) Show that if $P$ and $W$ descend along $Q$, then $P \cap W$ descends along $Q$, and that $P$ descends along each class $W \le Q$.
5. (B) Let $F \dashv G$ with $G$ fully faithful. Show that the unit $\eta_X$ is a local epimorphism for the image of $G$, using `localEpi_mem_range_iff_epi`.
6. (C) In the category of types, show that `MorphismProperty.surjective` is stable under base change and descends along the surjective maps.

### Reference

<?reference?>
