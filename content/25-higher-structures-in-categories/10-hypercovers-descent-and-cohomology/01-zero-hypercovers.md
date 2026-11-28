---
title: Zero-hypercovers and families of covers
kind: api
modules:
  - Mathlib.CategoryTheory.Sites.Hypercover.Zero
  - Mathlib.CategoryTheory.Sites.Hypercover.ZeroFamily
explains:
  E2: [CategoryTheory.PreZeroHypercover, CategoryTheory.Precoverage.ZeroHypercover, CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover, CategoryTheory.PreZeroHypercover.presieve₀_eq_presieve₀_iff, CategoryTheory.Precoverage.ZeroHypercover.bind, CategoryTheory.Precoverage.equivPreZeroHypercoverFamily]
  E1: auto
families: []
requires: [V24.C04, V25.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Zero-hypercovers and families of covers

### Overview

A presieve on an object $S$ is a set of morphisms with target $S$. It forgets two things: the order of the morphisms and their repetitions. In practice a cover is given as an indexed family $(f_i : X_i \to S)_{i \in I}$. The family $\{U_1, U_2\}$ of two open sets is not the same as the family $\{U_1, U_2, U_2\}$, but the two families give the same presieve. A construction that works with the components of a cover, such as a Čech complex or the gluing of morphisms, needs the index type. The library calls an indexed family of morphisms into $S$ a *pre-0-hypercover* of $S$, and it calls such a family a *0-hypercover* for a precoverage $J$ when the presieve that it generates is covering for $J$.

This section describes the category of pre-0-hypercovers, the constructions on them (pullback, refinement, intersection, disjoint union), the small 0-hypercovers, and the correspondence between precoverages and families of pre-0-hypercovers. The precoverages themselves are in Chapter 6. The 1-hypercovers of the next section add a cover of each fibre product $X_i \times_S X_j$, and they build on the objects of this section.

### The library around it

#### Pre-0-hypercovers and their morphisms

The structure `PreZeroHypercover S` has three fields: an index type `I₀`, a family of objects `X : I₀ → C`, and a family of morphisms `f : (i : I₀) → X i ⟶ S`. The index type lives in a universe `w` that is a parameter of the structure. The presieve `E.presieve₀` is `Presieve.ofArrows E.X E.f`, and `E.sieve₀` is the sieve that it generates. Each presieve comes from a pre-0-hypercover: `Presieve.preZeroHypercover R` is indexed by the morphisms of $R$, and `Presieve.exists_eq_preZeroHypercover` says that $R$ equals the presieve of some pre-0-hypercover.

A morphism $E \to F$ of pre-0-hypercovers of $S$ is a *refinement*: a map of indices $s_0 : I_0(E) \to I_0(F)$ and morphisms $h_0(i) : X_i \to Y_{s_0(i)}$ over $S$, so that $h_0(i) \circ g_{s_0(i)} = f_i$ in the textbook order. The structure is `PreZeroHypercover.Hom`, with the fields `s₀`, `h₀` and `w₀`. With `PreZeroHypercover.Hom.id` and `PreZeroHypercover.Hom.comp`, the pre-0-hypercovers of $S$ form a category. An isomorphism is built by `PreZeroHypercover.isoMk` from an equivalence of the index types and isomorphisms of the components, and `PreZeroHypercover.equivOfIso` recovers the equivalence of index types from an isomorphism.

**Proposition.** Two pre-0-hypercovers $E$ and $F$ of $S$ have the same presieve if and only if their deduplications are equal. This is `PreZeroHypercover.presieve₀_eq_presieve₀_iff`.

*Proof sketch.* The deduplication `E.shrink` is indexed by the morphisms of the presieve `E.presieve₀`, with the morphism itself as component. So it depends only on the presieve. Conversely, the presieve of `E.shrink` is the presieve of $E$, by `PreZeroHypercover.presieve₀_shrink`. ∎

The deduplication lives in the universe `max u v` of the morphisms of $C$, whatever the universe of $E$. The refinements `PreZeroHypercover.toShrink` and `PreZeroHypercover.fromShrink` go in both directions, so $E$ and `E.shrink` refine each other.

#### Constructions

The library gives the usual operations on covers as definitions on pre-0-hypercovers. Each has a version for 0-hypercovers below, with a hypothesis on the precoverage.

| Lean name | Construction |
|---|---|
| `PreZeroHypercover.singleton f` | the family with one morphism $f : X \to S$ |
| `PreZeroHypercover.empty` | the empty family |
| `PreZeroHypercover.pullback₁ f E` | the components $T \times_S X_i$ for $f : T \to S$ |
| `PreZeroHypercover.pullback₂ f E` | the components $X_i \times_S T$ |
| `PreZeroHypercover.bind E F` | refine each $X_i$ by a family $F_i$ of $X_i$ |
| `PreZeroHypercover.inter E F` | the components $X_i \times_S Y_j$ |
| `PreZeroHypercover.sum E F` | the disjoint union of the two families |
| `PreZeroHypercover.add E f` | add one morphism to the family |
| `PreZeroHypercover.restrictIndex E g` | precompose the index with $g : \iota \to I_0$ |
| `PreZeroHypercover.reindex E e` | change the index along an equivalence |
| `PreZeroHypercover.sigmaOfIsColimit E hc` | one component, a coproduct of the $X_i$ |
| `PreZeroHypercover.map F E` | the image under a functor $F$ |
| `PreZeroHypercover.pushforward E g` | compose each $f_i$ with $g : S \to T$ |

The intersection has the universal property of a product in the category of pre-0-hypercovers: `PreZeroHypercover.interFst`, `PreZeroHypercover.interSnd` and `PreZeroHypercover.interLift`. The disjoint union has the universal property of a coproduct: `PreZeroHypercover.sumInl`, `PreZeroHypercover.sumInr` and `PreZeroHypercover.sumLift`. The lemmas `PreZeroHypercover.presieve₀_pullback₁`, `PreZeroHypercover.presieve₀_sum` and `PreZeroHypercover.presieve₀_singleton` compute the presieves of these constructions. For a cover $\{U_i\}$ of $X$ and morphisms $X \to Z \leftarrow Y$, `PreZeroHypercover.pullbackCoverOfLeft` is the cover $\{U_i \times_Z Y\}$ of $X \times_Z Y$, and `PreZeroHypercover.pullbackCoverOfLeftIsoPullback₁` identifies it with the pullback of the cover along the first projection.

#### Zero-hypercovers for a precoverage

Let $J$ be a precoverage on $C$. The structure `Precoverage.ZeroHypercover J S` extends `PreZeroHypercover S` by the field `mem₀ : presieve₀ ∈ J.coverings S`. The class `Precoverage.RespectsIso J` says that $J$ is closed under isomorphic presieves, and then `PreZeroHypercover.presieve₀_mem_of_iso` moves the covering condition along an isomorphism of pre-0-hypercovers.

**Proposition.** A presieve $R$ on $X$ is covering for $J$ if and only if it is the presieve `Presieve.ofArrows 𝒰.X 𝒰.f` of a 0-hypercover $\mathcal{U}$ of $X$. This is `Precoverage.mem_iff_exists_zeroHypercover`.

*Proof.* If $R$ is covering, take the pre-0-hypercover of $R$ indexed by its morphisms. Its presieve is $R$, so it is a 0-hypercover. Conversely, the presieve of a 0-hypercover is covering by the field `mem₀`. ∎

The constructions keep the covering condition under the matching stability axiom of $J$. The pullbacks `Precoverage.ZeroHypercover.pullback₁` and `pullback₂` need `J.IsStableUnderBaseChange` and the existence of the pullbacks. The refinement needs composition:

**Proposition.** If $J$ is stable under composition, $E$ is a 0-hypercover of $T$ and $F_i$ is a 0-hypercover of $X_i$ for each $i$, then the family of composites $Y_{ij} \to X_i \to T$ is a 0-hypercover of $T$. This is `Precoverage.ZeroHypercover.bind`.

*Proof.* The presieve of `E.bind F` is the composite of the presieve of $E$ with the presieves of the $F_i$. Stability under composition is exactly the statement that this composite is covering. ∎

In the same way, `Precoverage.ZeroHypercover.inter` needs stability under base change and composition, and `Precoverage.ZeroHypercover.sum` needs `J.IsStableUnderSup`. The definitions `Precoverage.ZeroHypercover.add` and `Precoverage.ZeroHypercover.singleton` take the covering condition as an argument. The definition `Precoverage.ZeroHypercover.weaken` moves a 0-hypercover for $K$ to a finer precoverage $L \ge K$. The 0-hypercovers of $S$ form a category, `Precoverage.ZeroHypercover.instCategory`, whose morphisms are refinements of the underlying families.

#### Small 0-hypercovers

The index type of a 0-hypercover can be large, for example when it is indexed by all morphisms of a sieve. Many constructions need a small index. The class `Precoverage.ZeroHypercover.Small` says that some index type $\iota$ in a smaller universe and some map $\iota \to I_0$ give a restriction that is still covering, and `Precoverage.ZeroHypercover.Small.exists_restrictIndex_mem` states it. The definition `Precoverage.ZeroHypercover.restrictIndexOfSmall` performs the restriction. The class `Precoverage.Small` asks this for every 0-hypercover, and `Precoverage.Small.zeroHypercoverSmall` gives the instance. A 0-hypercover whose index type is small is small, by `Precoverage.ZeroHypercover.instSmallOfSmallI₀`.

#### Families of pre-0-hypercovers

A precoverage is a property of presieves. Sometimes it is easier to state a property of indexed families, for example "a finite family of open immersions that are jointly surjective". Such a property defines a precoverage only when it does not see repetitions. The structure `PreZeroHypercoverFamily C` holds, for each object $X$, a property of the pre-0-hypercovers of $X$ in the universe `max u v`, together with the field `iff_shrink`: a family has the property if and only if its deduplication has it.

**Theorem.** The precoverages on $C$ correspond bijectively to the pre-0-hypercover families on $C$. This is the equivalence `Precoverage.equivPreZeroHypercoverFamily`.

*Proof sketch.* A family $P$ gives the precoverage `P.precoverage`: a presieve $R$ is covering when $R$ is the presieve of a family with the property $P$, by `PreZeroHypercoverFamily.mem_precoverage_iff`. A precoverage $J$ gives the family `J.preZeroHypercoverFamily` of the families whose presieve is covering. This property depends only on the presieve, so it is invariant under deduplication. The two maps are inverse: a family with the property has the same presieve as its deduplication, and `PreZeroHypercover.presieve₀_eq_presieve₀_iff` shows that a family is determined up to deduplication by its presieve. ∎

The axioms of a precoverage translate to the family. The lemmas `Precoverage.HasIsos.of_preZeroHypercoverFamily`, `Precoverage.IsStableUnderComposition.of_preZeroHypercoverFamily`, `Precoverage.IsStableUnderSup.of_preZeroHypercoverFamily` and `Precoverage.IsStableUnderBaseChange.of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms` check them on the families. For example, stability under composition holds if `E.bind F` has the property when $E$ and each $F_i$ have it.

#### Common errors

1. A 0-hypercover is not a presieve. Two 0-hypercovers with the same presieve can have different index types, and they are only isomorphic after deduplication. Use `PreZeroHypercover.presieve₀_eq_presieve₀_iff` or `E.shrink` to compare them.
2. The constructions on `Precoverage.ZeroHypercover` need instances on the precoverage, such as `J.IsStableUnderBaseChange` for `pullback₁` and `J.IsStableUnderComposition` for `bind`. When an instance is missing, build the pre-0-hypercover first and prove the covering condition by hand.
3. The universe `w` of the index type is a parameter. A lemma for `PreZeroHypercover.{w}` does not apply to a family in another universe until it is moved by `shrink`, `restrictIndexOfSmall` or `reindex`.

### Exercises

1. (A) Show that the presieve of `PreZeroHypercover.sum E F` is the union of the presieves of $E$ and $F$, and that the presieve of `singleton f` is the presieve with the one arrow $f$.
2. (A) Give two pre-0-hypercovers of an open set $U$ of a space with the same presieve that are not isomorphic, and check that their deduplications are equal.
3. (B) Show that `PreZeroHypercover.inter E F`, with `PreZeroHypercover.interFst` and `PreZeroHypercover.interSnd`, is a product of $E$ and $F$ in the category of pre-0-hypercovers of $S$, when $C$ has pullbacks.
4. (B) Show that the property "the family is finite and jointly surjective" on families of continuous maps into a compact Hausdorff space is invariant under deduplication, and describe the precoverage that it defines.
5. (B) Show that the intersection of two 0-hypercovers of $T$ refines both of them, and that its presieve is covering when $J$ is stable under base change and composition.
6. (C) Let $J$ be a precoverage such that each covering presieve has a set of arrows of size in a universe $w'$. Show that $J$ satisfies `Precoverage.Small` in the universe $w'$, by restricting each 0-hypercover to one index for each arrow of its presieve.

### Reference

<?reference?>
