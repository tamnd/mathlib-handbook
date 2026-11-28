---
title: One-hypercovers and the sheaf condition
kind: api
modules:
  - Mathlib.CategoryTheory.Sites.Hypercover.One
  - Mathlib.CategoryTheory.Sites.Hypercover.Saturate
  - Mathlib.CategoryTheory.Sites.Hypercover.IsSheaf
  - Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
  - Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical
  - Mathlib.CategoryTheory.Sites.Hypercover.Homotopy
  - Mathlib.CategoryTheory.Sites.CoproductSheafCondition
explains:
  E2: [CategoryTheory.PreOneHypercover, CategoryTheory.GrothendieckTopology.OneHypercover, CategoryTheory.GrothendieckTopology.OneHypercover.isLimitMultifork, CategoryTheory.GrothendieckTopology.OneHypercoverFamily.isSheaf_iff, CategoryTheory.Presheaf.isSheaf_iff_of_isGeneratedByOneHypercovers, CategoryTheory.PreOneHypercover.Homotopy.isLimitMultiforkEquiv, CategoryTheory.GrothendieckTopology.HOneHypercover.isCofiltered_of_hasPullbacks, CategoryTheory.GrothendieckTopology.OneHypercover.glueMorphisms, CategoryTheory.Presieve.isSheafFor_sigmaDesc_iff]
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

## One-hypercovers and the sheaf condition

### Overview

Let $(f_i : X_i \to S)$ be a cover. The sheaf condition for a presheaf $F$ says that $F(S)$ is the equalizer of the two maps $\prod_i F(X_i) \rightrightarrows \prod_{i,j} F(X_i \times_S X_j)$. This form needs the fibre products. In many sites the fibre products do not exist, or they are too large to handle, and it is enough to cover each fibre product $X_i \times_S X_j$ by a family $(Y_k)$. A *1-hypercover* is a cover $(X_i \to S)$ together with such a cover of each fibre product. Then $F(S)$ is the multiequalizer of the maps $F(X_i) \rightrightarrows F(Y_k)$.

This section describes the 1-hypercovers of the library, the multifork that a presheaf gives on a 1-hypercover, the characterization of sheaves by 1-hypercovers, the strong sheaf condition for presheaves of types, the gluing of morphisms in a subcanonical topology, and the category of 1-hypercovers up to homotopy. The 0-hypercovers of the previous section are the first layer of a 1-hypercover.

### The library around it

#### Pre-1-hypercovers

The structure `PreOneHypercover S` extends `PreZeroHypercover S`. For each pair of indices $i_1, i_2$ it has an index type `I₁ i₁ i₂`, objects `Y j` for `j : I₁ i₁ i₂`, and two projections `p₁ j : Y j ⟶ X i₁` and `p₂ j : Y j ⟶ X i₂` with `p₁ j ≫ f i₁ = p₂ j ≫ f i₂`. When the fibre product exists, `PreOneHypercover.toPullback` is the induced morphism $Y_j \to X_{i_1} \times_S X_{i_2}$, and `PreOneHypercover.sieve₁'` is the sieve on the fibre product that these morphisms generate. The sieve `PreOneHypercover.sieve₁` is the same sieve, described on an object $W$ with two morphisms to $X_{i_1}$ and $X_{i_2}$, without the fibre product.

Each presheaf $F : C^{op} \to A$ gives the multicospan `PreOneHypercover.multicospanIndex E F`. Its left objects are the $F(X_i)$, its right objects are the $F(Y_j)$, and its two maps are $F(p_1)$ and $F(p_2)$. The multifork `PreOneHypercover.multifork E F` has the point $F(S)$ and the maps $F(f_i)$. The sheaf condition along $E$ is that this multifork is a limit.

The library gives several constructions of pre-1-hypercovers.

1. `PreZeroHypercover.toPreOneHypercover` takes the fibre products themselves as the cover of the fibre products, when they exist.
2. `PreZeroHypercover.saturate` is the largest pre-1-hypercover on a pre-0-hypercover. Its index at $(i_1, i_2)$ is the type of all commutative squares $W \to X_{i_1}$, $W \to X_{i_2}$ over $S$, the structure `PreZeroHypercover.Relation`. The equivalence `PreZeroHypercover.sectionsSaturateEquiv` says that, for a presheaf of types, the sections of its multicospan are the compatible families on the 0-hypercover.
3. `PreZeroHypercover.refineOneHypercover` covers each fibre product by a 0-hypercover.
4. `PreOneHypercover.trivial` has the one component $S$, and `PreOneHypercover.inter` is the intersection of two pre-1-hypercovers.
5. `PreOneHypercover.sigmaOfIsColimit` replaces the families by their coproducts. By `PreOneHypercover.isLimitSigmaOfIsColimitEquiv`, the multifork of $E$ is a limit if and only if the fork of the coproduct is one, for a presheaf that turns these coproducts into products.

A refinement of pre-1-hypercovers, `PreOneHypercover.Hom`, is a refinement of the 0-parts with compatible maps `s₁` and `h₁` on the 1-parts. A refinement $E \to F$ gives a morphism between the limits of the multiforks, `PreOneHypercover.Hom.mapMultiforkOfIsLimit`. The constructor `PreOneHypercover.isoMk` builds an isomorphism from the conditions in one direction, and `PreOneHypercover.isLimitEquivOfIso` says that isomorphic pre-1-hypercovers satisfy the sheaf condition together.

#### 1-hypercovers for a topology

Let $J$ be a Grothendieck topology on $C$. A 1-hypercover, `GrothendieckTopology.OneHypercover J S`, is a pre-1-hypercover such that `sieve₀` is covering for $J$ (the field `mem₀`) and each sieve `sieve₁ p₁ p₂` is covering (the field `mem₁`). When the fibre products exist, the constructor `GrothendieckTopology.OneHypercover.mk'` checks the second condition on the sieves `sieve₁'` of the fibre products. Each covering sieve gives a 1-hypercover: `GrothendieckTopology.Cover.oneHypercover` is indexed by the arrows of the sieve, and it uses all pullback cones as the 1-components.

**Theorem.** Let $F$ be a sheaf for $J$ with values in $A$ and let $E$ be a 1-hypercover of $S$. Then $F(S)$ is the multiequalizer of the maps $F(X_{i_1}) \rightrightarrows F(Y_j)$. This is `GrothendieckTopology.OneHypercover.isLimitMultifork`.

*Proof sketch.* It suffices to treat a presheaf of types, after evaluation at the objects of $A$ through the Yoneda embedding. Let $(s_i)$ be a family with $F(p_1)(s_{i_1}) = F(p_2)(s_{i_2})$ for all $j$. For two indices $i_1, i_2$ and a pair of morphisms $a : W \to X_{i_1}$, $b : W \to X_{i_2}$ over $S$, the sections $F(a)(s_{i_1})$ and $F(b)(s_{i_2})$ agree on the covering sieve `sieve₁ a b`, so they are equal because $F$ is separated. Then $(s_i)$ is a compatible family on the covering sieve `sieve₀`, and it glues to a unique section on $S$. ∎

The converse holds for each family of 1-hypercovers that generates the topology. A `GrothendieckTopology.OneHypercoverFamily J` is a predicate on the 1-hypercovers of each object. The class `GrothendieckTopology.OneHypercoverFamily.IsGenerating` says that each covering sieve contains the sieve `sieve₀` of a 1-hypercover in the family.

**Theorem.** Let $H$ be a generating family of 1-hypercovers. A presheaf $P$ is a sheaf if and only if the multifork of $P$ is a limit for each 1-hypercover in $H$. This is `GrothendieckTopology.OneHypercoverFamily.isSheaf_iff`.

*Proof sketch.* One direction is the previous theorem. For the other, let $R$ be a covering sieve and let $E \in H$ have `sieve₀` in $R$. A compatible family on $R$ restricts to a compatible family on the $X_i$, and the limit property of the multifork of $E$ glues it to a section on $S$. The uniqueness uses the limit property again, and a second 1-hypercover of $H$ inside the pullbacks of $R$ gives the agreement on all of $R$. ∎

The class `GrothendieckTopology.IsGeneratedByOneHypercovers J` says that the 1-hypercovers with index types in a universe $w$ generate $J$. The instance `GrothendieckTopology.instIsGeneratedByOneHypercovers` gives it in the universe `max u v`, by the 1-hypercovers of covering sieves. So `Presheaf.isSheaf_iff_of_isGeneratedByOneHypercovers` states the sheaf condition as the limit condition on all 1-hypercovers. The point of a smaller universe $w$ is that the limits of the multiforks then exist in categories with only $w$-small limits.

#### Presheaves of types

For a presheaf of types, the module `Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes` gives a version of the condition that is local. The structure `PreOneHypercover.IsStronglySheafFor E F` asks that $F$ is a sheaf for the presieve `presieve₀` of $E$ and separated for each sieve of the 1-part. The weaker `PreOneHypercover.IsStronglySeparatedFor` asks separation for both. The definition `PreOneHypercover.IsStronglySheafFor.amalgamate` glues a compatible family, and `PreOneHypercover.IsStronglySheafFor.isLimitMultifork` gives the limit property. A sheaf satisfies the strong condition for each 1-hypercover, by `GrothendieckTopology.OneHypercover.isStronglySheafFor`.

The lemma `GrothendieckTopology.OneHypercover.isSheafFor_of_pullback` says that the sheaf property for a presieve $R$ is local on the target: if $F$ is a sheaf for $J$, $E$ is a 1-hypercover, and $F$ is a sheaf for the pullbacks of $R$ to the $X_i$ and to the $Y_j$, then $F$ is a sheaf for $R$. With pairwise pullbacks, `PreZeroHypercover.sectionsEquivOfHasPullbacks` identifies the sections of the multicospan with the compatible families on the 0-hypercover.

#### Universal coproducts

The module `Mathlib.CategoryTheory.Sites.CoproductSheafCondition` replaces a family by one morphism. Let $(f_i : X_i \to S)$ be a family, let $c$ be a coproduct $\coprod_i X_i$ that is a universal colimit (`IsUniversalColimit`), and let $F$ be a presheaf that preserves the products of the $F(X_i)$ and of the $F(X_i \times_S X_j)$. Then `Presieve.isSheafFor_sigmaDesc_iff` says that $F$ is a sheaf for the single morphism $\coprod_i X_i \to S$ if and only if $F$ is a sheaf for the family $(f_i)$. The general form is `PreZeroHypercover.isLimitSigmaOfIsColimitEquiv`: for a pre-0-hypercover $E$ and the one-object pre-0-hypercover `PreZeroHypercover.sigmaOfIsColimit`, the multifork of $F$ on the second is a limit exactly when the multifork on $E$ is a limit. The universal coproduct makes $(\coprod_i X_i) \times_S (\coprod_j X_j)$ the coproduct of the $X_i \times_S X_j$, and the product hypothesis on $F$ then identifies the two multiforks.

#### Gluing morphisms

Let $J$ be subcanonical, so that each representable presheaf is a sheaf. Then morphisms glue along covers.

**Proposition.** Let $E$ be a 1-hypercover of $S$ and let $g_i : X_i \to T$ be morphisms with $g_{i_1} \circ p_1(j) = g_{i_2} \circ p_2(j)$ for all $j$. There is a unique $g : S \to T$ with $g \circ f_i = g_i$. The morphism is `GrothendieckTopology.OneHypercover.glueMorphisms`, and the equation is `GrothendieckTopology.OneHypercover.f_glueMorphisms`.

*Proof.* Apply `GrothendieckTopology.OneHypercover.isLimitMultifork` to the sheaf $\mathrm{Hom}(-, T)$. The family $(g_i)$ is a cone over its multicospan, so it factors uniquely through $\mathrm{Hom}(S, T)$. ∎

The 0-hypercover version `Precoverage.ZeroHypercover.glueMorphisms` uses the pairwise pullbacks, and `Precoverage.ZeroHypercover.hom_ext` says that two morphisms that agree on a cover are equal. With these tools, the module proves that isomorphisms are local on the target for a subcanonical precoverage, and `Precoverage.ZeroHypercover.isPullback_of_forall_isPullback` checks that a square is a pullback after base change to the members of a cover.

#### Homotopies of refinements

Two refinements $f, g : E \to F$ of pre-1-hypercovers induce the same map on the limits of the multiforks for each sheaf, but they need not be equal. The structure `PreOneHypercover.Homotopy f g` gives, for each $i$, an index $H(i)$ of the 1-part of $F$ over $(s_0^f(i), s_0^g(i))$ and a morphism $a(i) : X_i \to Y_{H(i)}$ with $a(i) \circ p_1 = h_0^f(i)$ and $a(i) \circ p_2 = h_0^g(i)$. The lemma `PreOneHypercover.Homotopy.mapMultiforkOfIsLimit_eq` says that homotopic refinements induce the same map.

**Proposition.** If $f : E \to F$ and $g : F \to E$ are refinements whose composites are homotopic to the identities, then the multifork of a presheaf on $E$ is a limit if and only if the multifork on $F$ is a limit. This is `PreOneHypercover.Homotopy.isLimitMultiforkEquiv`.

The relation `GrothendieckTopology.OneHypercover.homotopicRel` is not an equivalence relation: it is not even reflexive in general. The category `GrothendieckTopology.HOneHypercover J S` is the quotient of the category of 1-hypercovers by the congruence that this relation generates, with the projection `GrothendieckTopology.OneHypercover.toHOneHypercover`. Given $f, g : E \to F$, the construction `GrothendieckTopology.OneHypercover.cylinder` gives a 1-hypercover $W$ with a refinement $h : W \to E$ such that $h \circ f$ and $h \circ g$ are homotopic. With `GrothendieckTopology.OneHypercover.exists_nonempty_homotopy`, this yields the theorem `GrothendieckTopology.HOneHypercover.isCofiltered_of_hasPullbacks`: if $C$ has pullbacks, the category of 1-hypercovers of $S$ up to homotopy is cofiltered.

#### Common errors

1. The 1-part of a 1-hypercover covers the pairs of morphisms into $X_{i_1}$ and $X_{i_2}$, not only the fibre product. Use `sieve₁` when the fibre products are not known to exist, and `sieve₁'` with `mk'` when they are.
2. The universe of the index types matters. `Presheaf.isSheaf_iff_of_isGeneratedByOneHypercovers` uses the universe of the instance, which is `max u v` by default. A statement about small 1-hypercovers needs the class `IsGeneratedByOneHypercovers.{w}` as a hypothesis.
3. A homotopy is data and not a relation. `GrothendieckTopology.OneHypercover.homotopicRel` is not reflexive, so do not use it as a setoid. Work in `HOneHypercover` instead.

### Exercises

1. (A) For a pre-0-hypercover with pairwise pullbacks, show that the multifork of `PreZeroHypercover.toPreOneHypercover` is the usual equalizer diagram of the sheaf condition.
2. (A) Show that the identity refinement of a 1-hypercover is homotopic to itself when the 1-part contains the diagonal, and give a 1-hypercover where no homotopy from the identity to itself exists.
3. (B) Prove `GrothendieckTopology.OneHypercover.isLimitMultifork` for presheaves of types from the definition of a sheaf, as in the sketch.
4. (B) Let $X$ be a topological space and $(U_i)$ an open cover of an open set $U$. Build a 1-hypercover of $U$ whose 1-part covers each $U_i \cap U_j$ by an open cover, and write out the multiequalizer condition.
5. (B) Use `Precoverage.ZeroHypercover.glueMorphisms` to show that, in a subcanonical topology, a morphism that is an isomorphism after base change to each member of a cover is an isomorphism, when pullbacks exist.
6. (C) Show that the category of 1-hypercovers of $S$ up to homotopy is cofiltered when $C$ has pullbacks: give the common refinement of two 1-hypercovers and the equalizing refinement of two parallel refinements.

### Reference

<?reference?>
