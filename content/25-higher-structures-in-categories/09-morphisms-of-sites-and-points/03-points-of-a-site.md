---
title: Points of a site
kind: api
modules:
  - Mathlib.CategoryTheory.Sites.Point.Basic
  - Mathlib.CategoryTheory.Sites.Point.Category
  - Mathlib.CategoryTheory.Sites.Point.Presheaf
  - Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
  - Mathlib.CategoryTheory.Sites.Point.Skyscraper
  - Mathlib.CategoryTheory.Sites.Point.Conservative
  - Mathlib.CategoryTheory.Sites.Point.Map
  - Mathlib.CategoryTheory.Sites.Point.Comap
  - Mathlib.CategoryTheory.Sites.Point.Over
  - Mathlib.CategoryTheory.Sites.Point.Monoidal
  - Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
  - Mathlib.CategoryTheory.Sites.LocalSite
explains:
  E2: [CategoryTheory.GrothendieckTopology.Point, CategoryTheory.GrothendieckTopology.Point.presheafFiber, CategoryTheory.GrothendieckTopology.Point.sheafFiber, CategoryTheory.GrothendieckTopology.Point.W_isInvertedBy_presheafFiber, CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction, CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints, CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.W_iff, CategoryTheory.GrothendieckTopology.pointBotPresheafFiberIso, CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso, CategoryTheory.GrothendieckTopology.IsLocalSite]
  E1: auto
families: []
requires: [V24.C04, V24.C05, V24.C07, V25.C03, V25.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Points of a site

### Overview

A point $x$ of a topological space gives the stalk functor $F \mapsto F_x = \operatorname{colim}_{U \ni x} F(U)$. This functor commutes with finite limits and with all colimits, and a morphism of sheaves is an isomorphism when it is an isomorphism on all stalks. A general site need not have points of this kind. So the library defines a point of a site $(C, J)$ by its fiber functor $C \to \mathsf{Type}$, which plays the part of $U \mapsto \{x\} \cap U$. The stalk of a presheaf is then a filtered colimit over the elements of this functor.

The eleven modules of this section define points, the fiber functors on presheaves and on sheaves, and the skyscraper sheaves, which are right adjoint to the fiber functors. They also define conservative families of points, and they move points along continuous and cocontinuous functors and to the sites over an object. The last two modules make the fiber functors monoidal.

The section uses the continuous and cocontinuous functors of Section 1, the sites over an object of Section 2, the filtered colimits and adjunctions of Volume 24, and the object properties of Chapter 3.

### The library around it

**Points and fibers.** In `Mathlib.CategoryTheory.Sites.Point.Basic`, a point `Φ : J.Point` of the site $(C, J)$ is a structure `GrothendieckTopology.Point` with four fields. The field `GrothendieckTopology.Point.fiber` is a functor $C \to \mathsf{Type}\ w$. The field `GrothendieckTopology.Point.isCofiltered` asks that the category of elements of the fiber is cofiltered, and `GrothendieckTopology.Point.initiallySmall` asks that it is initially small. The field `GrothendieckTopology.Point.jointly_surjective` is the covering condition: for a covering sieve $R$ of $X$ and $x \in \Phi(X)$, there is a morphism $f : Y \to X$ in $R$ and $y \in \Phi(Y)$ with $\Phi(f)(y) = x$. For the space case, $\Phi(U)$ is a point of $U$ or empty, and the covering condition says that a point of $U$ lies in a member of each open cover of $U$.

The fiber of a presheaf $P : C^{\mathrm{op}} \to A$ is the colimit

$$\Phi^*P = \operatorname{colim}_{(X, x)} P(X),$$

over the opposite of the category of elements, which is filtered. The functor is `GrothendieckTopology.Point.presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A`. The maps into the colimit are `GrothendieckTopology.Point.toPresheafFiber`, with the natural form `GrothendieckTopology.Point.toPresheafFiberNatTrans`. The colimit cocone is `GrothendieckTopology.Point.presheafFiberCocone`, the proof that it is a colimit is `GrothendieckTopology.Point.isColimitPresheafFiberCocone`, and `GrothendieckTopology.Point.presheafFiberDesc` constructs morphisms out of the fiber. For a concrete category $A$, the lemma `GrothendieckTopology.Point.toPresheafFiber_jointly_surjective` says that each element of the fiber comes from some $P(X)$, and `GrothendieckTopology.Point.toPresheafFiber_eq_iff'` says when two such elements agree. The isomorphism `GrothendieckTopology.Point.shrinkYonedaCompPresheafFiberIso` says that the fiber of a representable presheaf is the fiber functor itself. The fiber functor on sheaves is `GrothendieckTopology.Point.sheafFiber : Sheaf J A ⥤ A`, the restriction of the presheaf fiber.

A key fact is that sheafification does not change the fiber. The lemma `GrothendieckTopology.Point.W_isInvertedBy_presheafFiber` says that the presheaf fiber inverts each morphism of `J.W`, that is, each morphism that becomes an isomorphism after sheafification. The proof sketch for sheaves of types: a morphism in `J.W` is locally injective and locally surjective. By the covering condition of the point, local surjectivity gives surjectivity on the colimit, and local injectivity gives injectivity. The isomorphism `GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso` in `Mathlib.CategoryTheory.Sites.Point.Skyscraper` then identifies the fiber of the sheafification with the fiber of the presheaf. Instances show that the presheaf fiber preserves colimits, and that the two fibers preserve finite limits when $A$ has exact filtered colimits. The isomorphisms `GrothendieckTopology.Point.presheafFiberCompIso` and `GrothendieckTopology.Point.sheafFiberCompIso` say that the fibers commute with a functor $A \to B$ that preserves filtered colimits. The fiber of the terminal object is a point: see `GrothendieckTopology.Point.isTerminalFiberObj` and `GrothendieckTopology.Point.uniqueFiberObj`.

**The category of points.** In `Mathlib.CategoryTheory.Sites.Point.Category`, a morphism $\Phi_1 \to \Phi_2$ of points, `GrothendieckTopology.Point.Hom`, is a natural transformation $\Phi_2.\mathrm{fiber} \to \Phi_1.\mathrm{fiber}$ in the opposite direction. The instance `GrothendieckTopology.Point.instCategory` makes points a category. A morphism of points induces natural transformations of fibers: `GrothendieckTopology.Point.Hom.presheafFiber` and `GrothendieckTopology.Point.Hom.sheafFiber`, with the lemmas `GrothendieckTopology.Point.Hom.presheafFiber_comp` and `GrothendieckTopology.Point.Hom.presheafFiber_id`.

**Examples and a constructor.** The module `Mathlib.CategoryTheory.Sites.Point.Presheaf` treats the trivial topology $\bot$, whose sheaves are all presheaves. Each object $X$ gives the point `GrothendieckTopology.pointBot X`, with the functor $\operatorname{Hom}(X, -)$ as fiber. Then `GrothendieckTopology.pointBotPresheafFiberIso` says that its fiber functor is the evaluation at $X$. The proof is short: the category of elements of $\operatorname{Hom}(X, -)$ has the initial object $(X, \mathrm{id})$, so the colimit over its opposite is the value at $X$. The family `GrothendieckTopology.pointsBot C` of these points is conservative by `GrothendieckTopology.isConservative_pointsBot`, and `GrothendieckTopology.pointBotFunctor` makes the construction a functor. The module `Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered` gives the constructor `GrothendieckTopology.Point.ofIsCofiltered`. It takes a functor $p : N \to C$ from a cofiltered and initially small category, with a covering condition, and its fiber is $X \mapsto \operatorname{colim}_U \operatorname{Hom}(p(U), X)$. For a space, $N$ is the poset of open neighbourhoods of the point. The cocone `GrothendieckTopology.Point.presheafFiberOfIsCofilteredCocone` and `GrothendieckTopology.Point.isColimitPresheafFiberOfIsCofilteredCocone` compute the fiber of a presheaf as a colimit over $N$.

**Skyscraper sheaves.** For a point $\Phi$ and an object $M$ of $A$, the skyscraper presheaf `GrothendieckTopology.Point.skyscraperPresheaf` sends $X$ to the product $\prod_{x \in \Phi(X)} M$. The equivalence `GrothendieckTopology.Point.skyscraperPresheafHomEquiv` is a bijection $(\Phi^* P \to M) \simeq (P \to \text{skyscraper}(M))$: a morphism out of a colimit is a compatible family of morphisms $P(X) \to M$, one for each $x \in \Phi(X)$, and this is a morphism into the product. This gives `GrothendieckTopology.Point.skyscraperPresheafAdjunction`. The lemma `GrothendieckTopology.Point.isSheaf_skyscraperPresheaf` says that the skyscraper presheaf is a sheaf. The sheaf version is `GrothendieckTopology.Point.skyscraperSheafFunctor`, and `GrothendieckTopology.Point.skyscraperSheafAdjunction` says $\Phi^* \dashv \text{skyscraper}$. So the sheaf fiber is a left adjoint and commutes with all colimits.

**Conservative families.** The module `Mathlib.CategoryTheory.Sites.Point.Conservative` takes a family `P : ObjectProperty J.Point`. The structure `ObjectProperty.IsConservativeFamilyOfPoints` asks that the fiber functors on sheaves of types jointly reflect isomorphisms. The class `GrothendieckTopology.HasEnoughPoints` asks for a small conservative family. The constructor `ObjectProperty.IsConservativeFamilyOfPoints.mk'` checks the condition with sieves: a sieve $S$ on $X$ covers if each element of each fiber at $X$ lifts along some morphism of $S$. For a family with this property, the fiber functors with values in a suitable concrete category $A$ jointly reflect isomorphisms (`ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms`), monomorphisms and epimorphisms, and they are jointly faithful. The lemma `ObjectProperty.IsConservativeFamilyOfPoints.W_iff` says that a morphism $f$ of presheaves lies in `J.W` if and only if each presheaf fiber of $f$ is an isomorphism. In this way, questions about sheafification reduce to stalks, as for spaces.

**Moving points.** A cocontinuous functor $F : C \to D$ sends a point $\Phi$ of $C$ to the point `GrothendieckTopology.Point.map Φ F K` of $D$, in `Mathlib.CategoryTheory.Sites.Point.Map`. Its presheaf fiber is the fiber of $\Phi$ applied to $P \circ F^{\mathrm{op}}$: this is `GrothendieckTopology.Point.presheafFiberMapIso`. The sheaf version for a functor that is also continuous is `GrothendieckTopology.Point.sheafFiberMapIso`. In the other direction, `Mathlib.CategoryTheory.Sites.Point.Comap` takes a representably flat and cover preserving functor $F : C \to D$ and a point $\Phi$ of $D$. The point `GrothendieckTopology.Point.comap` of $C$ has the fiber $\Phi \circ F$. The isomorphism `GrothendieckTopology.Point.sheafFiberComapIso` says that its sheaf fiber is the pullback of Section 1 followed by the fiber of $\Phi$, as for the stalk $(f^* F)_x = F_{f(x)}$ of spaces. The isomorphism `GrothendieckTopology.Point.skyscraperSheafFunctorCompSheafPushforwardContinuous` gives the pushforward of a skyscraper sheaf. The module `Mathlib.CategoryTheory.Sites.Point.Over` restricts a point $\Phi$ with $x \in \Phi(X)$ to the point `GrothendieckTopology.Point.over Φ x` of the site over $X$. The lemma `ObjectProperty.IsConservativeFamilyOfPoints.over` moves conservative families there, and an instance says that `J.over X` has enough points when $J$ has.

**Monoidal fibers.** The module `Mathlib.CategoryTheory.Sites.Point.Monoidal` takes a monoidal category $A$ whose tensor product commutes with filtered colimits in each variable. Then the instances `GrothendieckTopology.Point.instMonoidalFunctorOppositePresheafFiber` and `GrothendieckTopology.Point.instMonoidalSheafSheafFiber` make the two fiber functors monoidal. The module `Mathlib.CategoryTheory.Sites.Point.IsMonoidalW` uses this: for a conservative family of points, `ObjectProperty.IsConservativeFamilyOfPoints.isMonoidal_W` says that `J.W` is stable under tensor products. This is the hypothesis that the monoidal structure on sheaves of Chapter 6 needs.

**Local sites.** The module `Mathlib.CategoryTheory.Sites.LocalSite` gives a site with a canonical point. The class `GrothendieckTopology.IsLocalSite J` asks for a terminal object $T$ whose only covering sieve is the maximal sieve, and `GrothendieckTopology.IsLocalSite.from_terminal_mem_of_mem` says that each covering sieve then contains every morphism from $T$. Each category with a terminal object is a local site for the trivial topology. The point `GrothendieckTopology.IsLocalSite.point J` has the fiber $X \mapsto \mathrm{Hom}(T, X)$, and `GrothendieckTopology.IsLocalSite.pointSheafFiberIso` says that its sheaf fiber is the global sections functor `Sheaf.Γ` of Chapter 6. So the skyscraper sheaf of this point is a right adjoint of $\Gamma$: it is `GrothendieckTopology.IsLocalSite.coconstantSheaf`, with the adjunction `GrothendieckTopology.IsLocalSite.ΓCoconstantSheafAdj`. The functor takes an explicit universe argument, as in `coconstantSheaf.{w} J A`. By `GrothendieckTopology.IsLocalSite.fullyFaithfulCoconstantSheaf` it is fully faithful, and the adjoint triple `GrothendieckTopology.IsLocalSite.constantΓCoconstantTriple` then gives `GrothendieckTopology.IsLocalSite.fullyFaithfulConstantSheaf`: on a local site, the constant sheaf functor is fully faithful.

#### Common errors

1. A user expects a morphism of points $\Phi_1 \to \Phi_2$ to be a natural transformation $\Phi_1.\mathrm{fiber} \to \Phi_2.\mathrm{fiber}$. The field `GrothendieckTopology.Point.Hom.hom` goes in the opposite direction.
2. A user looks for the fiber of a sheaf as a colimit over open neighbourhoods. The general definition uses the category of elements of the fiber functor. Only points from `GrothendieckTopology.Point.ofIsCofiltered` come with a colimit over a given index category $N$.
3. A user tries to use `ObjectProperty.IsConservativeFamilyOfPoints.W_iff` with no `HasWeakSheafify` instance or with a coefficient category without products. Both are hypotheses of the lemma.

### Exercises

1. (A) Use `GrothendieckTopology.Point.isTerminalFiberObj` to show that the fiber of the terminal sheaf of types is a one point type.
2. (A) Show that the identity natural transformation gives the identity morphism of a point, with `GrothendieckTopology.Point.id_hom`.
3. (B) For a topological space $X$ and a point $x$, describe the point of the site of open sets of $X$ whose fiber sends $U$ to $\{x\} \cap U$, and check the covering condition `GrothendieckTopology.Point.jointly_surjective`.
4. (B) Use `GrothendieckTopology.Point.skyscraperSheafAdjunction` to show that the sheaf fiber preserves all colimits that exist in `Sheaf J A`.
5. (B) Prove `GrothendieckTopology.pointBotPresheafFiberIso` for presheaves of types from the initial object of the category of elements of a representable functor.
6. (C) Let $P$ be a conservative family of points. Show that a morphism of sheaves of types is a monomorphism if and only if each fiber map is injective.

### Reference

<?reference?>
