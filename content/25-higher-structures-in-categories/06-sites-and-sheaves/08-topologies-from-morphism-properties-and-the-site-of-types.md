---
title: Topologies from morphism properties and the site of types
kind: api
modules:
  - Mathlib.CategoryTheory.Sites.MorphismProperty
  - Mathlib.CategoryTheory.Sites.Finite
  - Mathlib.CategoryTheory.Sites.Types
explains:
  E2: [CategoryTheory.MorphismProperty.precoverage, CategoryTheory.MorphismProperty.coverage, CategoryTheory.MorphismProperty.pretopology, CategoryTheory.MorphismProperty.grothendieckTopology, CategoryTheory.MorphismProperty.grothendieckTopology_eq_toGrothendieck_pretopology, CategoryTheory.Precoverage.morphismProperty, CategoryTheory.Precoverage.galoisConnection_morphismProperty_precoverage, CategoryTheory.Precoverage.finite, CategoryTheory.typesGrothendieckTopology, CategoryTheory.typeEquiv]
  E1: auto
families: []
requires: [V24.C03, V24.C04, V25.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Topologies from morphism properties and the site of types

### Overview

Many sites of geometry have the same form. A class $P$ of morphisms is given, for example the open immersions or the étale morphisms of schemes. A family $(f_i : X_i \to X)$ is a cover when each $f_i$ is in $P$ and the family is jointly surjective. The second condition is a precoverage of its own, so the general construction is the precoverage of the families with all members in $P$, and the site is the intersection of this precoverage with the surjective families. When $P$ contains the isomorphisms, is stable under composition and is stable under base change, the families with members in $P$ form a pretopology.

This section describes that construction, together with two small examples of sites. The first example is the finite precoverage, whose covers are the families with finitely many arrows. The second is the site of types: the category of types with the topology of jointly surjective families. Its sheaves of types are the same as types, and its topology is the canonical topology. The section uses the morphism properties of Chapter 3, the precoverages of Section 4, the sieves and sheaves of Sections 1 and 2, and the Yoneda lemma of Volume 24.

### The library around it

**The precoverage of a morphism property.** In `Mathlib.CategoryTheory.Sites.MorphismProperty`, a morphism property `P : MorphismProperty C` gives the precoverage `MorphismProperty.precoverage P`. A presieve $R$ on $X$ is a cover when each arrow of $R$ is in $P$. The two simp lemmas `MorphismProperty.ofArrows_mem_precoverage` and `MorphismProperty.singleton_mem_precoverage` restate this for a presieve given by a family and for a presieve with one arrow. The empty presieve is always a cover, by `MorphismProperty.bot_mem_precoverage`, so this precoverage alone does not ask for surjectivity.

The properties of $P$ give the properties of the precoverage of Section 4, as instances:

1. If $P$ contains the identities and respects isomorphisms, the precoverage has `Precoverage.HasIsos`.
2. If $P$ is stable under base change, the precoverage has `Precoverage.IsStableUnderBaseChange`.
3. If $P$ is stable under composition, the precoverage has `Precoverage.IsStableUnderComposition`.

The construction is monotone, by `MorphismProperty.precoverage_monotone`, and it sends an intersection of properties to an intersection of precoverages, by `MorphismProperty.precoverage_inf`. This is the form that the geometric sites use: the étale precoverage is the intersection of the precoverage of étale morphisms with the precoverage of surjective families. The lemma `MorphismProperty.comap_precoverage` says that the pullback of the precoverage along a functor $F$ is the precoverage of `P.inverseImage F`. The top property gives the top precoverage, by `MorphismProperty.precoverage_top`.

**Coverages, pretopologies and topologies.** If $P$ is stable under base change and has the pullbacks it needs (`MorphismProperty.HasPullbacks`), then `MorphismProperty.coverage P` is a coverage with the same covers, and `MorphismProperty.grothendieckTopology P` is the topology that it generates. If $C$ has all pullbacks and $P$ is also multiplicative (`MorphismProperty.IsMultiplicative`), then `MorphismProperty.pretopology P` is the pretopology `(MorphismProperty.precoverage P).toPretopology`. The lemma `MorphismProperty.coverage_eq_toCoverage_pretopology` says that the two routes give the same coverage, and `MorphismProperty.grothendieckTopology_eq_toGrothendieck_pretopology` says that they give the same topology. The lemmas `MorphismProperty.pretopology_monotone` and `MorphismProperty.pretopology_inf` repeat the order facts for pretopologies.

**From a precoverage back to a property.** In the other direction, `Precoverage.morphismProperty K` is the smallest morphism property that contains each member of each cover of $K$. The lemma `Precoverage.morphismProperty_le_iff_le_precoverage` says that `K.morphismProperty ≤ P` holds exactly when $K$ is less than or equal to the precoverage of $P$, and `Precoverage.galoisConnection_morphismProperty_precoverage` states this as a Galois connection:
$$\operatorname{mor}(K) \le P \iff K \le \operatorname{prec}(P).$$
The usual consequences follow. The lemma `Precoverage.le_precoverage_morphismProperty` says that $K \le \operatorname{prec}(\operatorname{mor}(K))$, `MorphismProperty.morphismProperty_precoverage` says that $\operatorname{mor}(\operatorname{prec}(P)) = P$, and `Precoverage.morphismProperty_sup` and `Precoverage.morphismProperty_bot` say that $\operatorname{mor}$ keeps joins and the bottom element. So a morphism property is the same as a precoverage of the special form "all members are in $P$". An instance says that `K.morphismProperty` contains the identities when $K$ has `Precoverage.HasIsos`.

**The finite precoverage.** The module `Mathlib.CategoryTheory.Sites.Finite` defines `Precoverage.finite C`. A presieve $R$ is a cover when the set of its arrows, as pairs of an object and a morphism, is finite: `Precoverage.mem_finite_iff` states this with `Presieve.uncurry`. The lemma `Precoverage.ofArrows_mem_finite` says that each family indexed by a finite type is a cover, and an instance gives `Precoverage.HasIsos`. With pullbacks, `Pretopology.finite C` is the pretopology with the same covers, and `Pretopology.ofArrows_mem_finite` is the same lemma for it. The intersection of this precoverage with another one keeps only the finite covers, as in the definition of quasi-compact covers.

**The site of types.** The module `Mathlib.CategoryTheory.Sites.Types` defines the topology `typesGrothendieckTopology` on `Type u`. A sieve $S$ on a type $\alpha$ is a cover when for each $x : \alpha$ the map from the one point type with value $x$ is in $S$. So $S$ covers when its arrows are jointly surjective. Two special sieves appear in the proofs. The sieve `discreteSieve α` contains the maps whose image has at most one point, and `discreteSieve_mem` says that it covers. The presieve `discretePresieve α` contains the maps from a type with one point, and `generate_discretePresieve_mem` says that the sieve that it generates covers.

Each representable presheaf is a sheaf for this topology, by `Presieve.isSheaf_yoneda'` and `Presheaf.isSheaf_yoneda'`. So `yoneda'` is a functor from types to sheaves, and `yoneda'_comp` says that its composite with `sheafToPresheaf` is `yoneda`. The converse is the main point. For a sheaf $S$, `eval S α` sends $s \in S(\alpha)$ to the function $x \mapsto s|_x$ with values in $S(\mathrm{pt})$, where $\mathrm{pt}$ is the one point type. The map `typesGlue` goes back: a function $\alpha \to S(\mathrm{pt})$ is a compatible family on `discretePresieve α`, and the sheaf condition glues it. The lemmas `eval_typesGlue` and `typesGlue_eval` say that the two maps are inverse, `evalEquiv` is the bijection $S(\alpha) \simeq (\alpha \to S(\mathrm{pt}))$, and `equivYoneda` and `equivYoneda'` are the isomorphisms of $S$ with the representable sheaf of $S(\mathrm{pt})$.

The result is the equivalence `typeEquiv : Type u ≌ Sheaf typesGrothendieckTopology (Type u)`. Its functor is `yoneda'`, and its inverse evaluates a sheaf at the one point type. The instance `subcanonical_typesGrothendieckTopology` says that the topology is subcanonical, and `typesGrothendieckTopology_eq_canonical` says that it is equal to `Sheaf.canonicalTopology (Type u)`. The proof of the second fact uses the sheaf of maps to a type with two elements: if a sieve is not jointly surjective, this sheaf has two different sections that agree on the sieve.

#### Common errors

1. `MorphismProperty.precoverage P` contains the empty family of each object, so the topology that it generates has each object covered by the empty sieve. A user who wants a geometric site must intersect it with a precoverage of surjective families.
2. `MorphismProperty.pretopology P` needs `HasPullbacks C` and `P.IsMultiplicative`, while `MorphismProperty.coverage P` needs only the pullbacks along the members of $P$. The second is the correct choice in a category without all pullbacks.
3. `Precoverage.mem_finite_iff` counts pairs of an object and an arrow, not indices. A family indexed by an infinite type with finitely many different arrows still gives a finite presieve, and `Precoverage.ofArrows_mem_finite` asks for a finite index type only as a sufficient condition.

### Exercises

1. (A) Use `MorphismProperty.singleton_mem_precoverage` to show that a single arrow $f$ is a cover for the precoverage of $P$ if and only if $P(f)$ holds.
2. (A) Show that the precoverage of `MorphismProperty.isomorphisms C` has `Precoverage.HasIsos`, and name the instance that the library uses.
3. (B) Prove `Precoverage.le_precoverage_morphismProperty` from `Precoverage.galoisConnection_morphismProperty_precoverage`.
4. (B) Let $P$ and $Q$ be multiplicative and stable under base change. Use `MorphismProperty.pretopology_inf` to describe the covers of the pretopology of $P \sqcap Q$ in terms of the covers for $P$ and for $Q$.
5. (B) For a sheaf $S$ on the site of types, compute `evalEquiv` for the empty type, and show that $S(\emptyset)$ has exactly one element.
6. (C) Prove on paper that `typesGrothendieckTopology` is the canonical topology of `Type u`: use `typesGrothendieckTopology_eq_canonical` as a guide, and give the two sections of the sheaf of maps to a type with two elements in detail.

### Reference

<?reference?>
