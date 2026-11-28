---
title: Dense subsites and sites over an object
kind: api
modules:
  - Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
  - Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
  - Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense
  - Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
  - Mathlib.CategoryTheory.Sites.Equivalence
  - Mathlib.CategoryTheory.Sites.Over
  - Mathlib.CategoryTheory.Sites.SubcanonicalOver
  - Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
explains:
  E2: [CategoryTheory.Functor.IsCoverDense, CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom, CategoryTheory.Functor.IsCoverDense.iso_of_restrict_iso, CategoryTheory.Functor.IsDenseSubsite, CategoryTheory.Functor.IsDenseSubsite.sheafEquiv, CategoryTheory.Functor.isEquivalence_of_isOneHypercoverDense, CategoryTheory.Functor.sheafInducedTopologyEquivOfIsCoverDense, CategoryTheory.Equivalence.sheafCongr, CategoryTheory.GrothendieckTopology.over, CategoryTheory.GrothendieckTopology.mem_over_iff]
  E1: auto
families: []
requires: [V24.C02, V24.C05, V25.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Dense subsites and sites over an object

### Overview

The sheaves on a space are determined by their values on a basis of the topology. The categorical form of this fact is the comparison lemma. Let $G : C \to D$ be a functor into a site $(D, K)$ such that each object of $D$ is covered by images of objects of $C$. Under some conditions on $G$, the restriction of sheaves along $G$ is an equivalence between the sheaves on $D$ and the sheaves on $C$ for a suitable topology. Then $(C, J)$ is a dense subsite of $(D, K)$. The library uses this result in several places: to replace a large site by a small one, to transport sheafification, and to compare sites of schemes.

The second subject of the section is the site over an object. For a site $(C, J)$ and an object $X$, the category `Over X` of morphisms $Y \to X$ has a topology `J.over X`, and a sheaf on $C$ restricts to a sheaf on this site. This is the categorical form of the restriction of a sheaf to an open subset. The eight modules of this section hold these two subjects and the transport of a topology along an equivalence of categories.

The section uses the continuous and cocontinuous functors of Section 1 and the sheaves of Chapter 6.

### The library around it

**Cover dense functors.** The module `Mathlib.CategoryTheory.Sites.DenseSubsite.Basic` starts with the sieve `Sieve.coverByImage G U` of the morphisms into $U$ that factor through an object $G(Y)$. The presieve `Presieve.coverByImage G U` is the same family. The class `Functor.IsCoverDense G K` asks that this sieve covers each $U$ for $K$: this is the field `Functor.IsCoverDense.is_cover`. Two further classes control the morphisms. The class `Functor.IsLocallyFull G K` says that each morphism $G(X) \to G(Y)$ is locally in the image of $G$, and `Functor.IsLocallyFaithful G K` says that two morphisms with the same image are locally equal.

The main results say that a sheaf on $D$ is determined by its restriction to $C$. Let $G$ be cover dense and locally full, let $\mathcal F$ be a presheaf and $\mathcal F'$ a sheaf on $D$. Then the equivalence `Functor.IsCoverDense.restrictHomEquivHom` identifies the morphisms $\mathcal F \to \mathcal F'$ with the morphisms $\mathcal F \circ G^{\mathrm{op}} \to \mathcal F' \circ G^{\mathrm{op}}$. The construction of the inverse is `Functor.IsCoverDense.sheafHom`. Here is the proof sketch for sheaves of types. Let $\alpha$ be a morphism of the restrictions, and let $s \in \mathcal F(U)$. For each $f : G(Y) \to U$ in the cover by images, the element $\alpha_Y(\mathcal F(f)(s))$ lies in $\mathcal F'(G(Y))$. Local fullness makes this family compatible, and the sheaf condition of $\mathcal F'$ glues it to one element of $\mathcal F'(U)$. The internal steps are `Functor.IsCoverDense.Types.presheafHom` and `Functor.IsCoverDense.sheafCoyonedaHom`, which reduce the general case to sheaves of types by the functors $\operatorname{Hom}(a, -)$. Two consequences follow. The theorem `Functor.IsCoverDense.iso_of_restrict_iso` says that a morphism of sheaves whose restriction is an isomorphism is an isomorphism. The isomorphisms `Functor.IsCoverDense.sheafIso` and `Functor.IsCoverDense.Types.presheafIso` lift an isomorphism of restrictions. The lemma `Functor.whiskerLeft_obj_map_bijective_of_isCoverDense` gives the bijection on morphisms for a full functor. The lemma `Functor.IsCoverDense.compatiblePreserving` says that a cover dense, locally full and locally faithful functor is compatible preserving, so `Functor.IsCoverDense.isContinuous` makes it continuous when it is cover preserving.

**Dense subsites.** The class `Functor.IsDenseSubsite J K G` asks that $G$ is cover dense, locally full and locally faithful, and that a sieve $S$ on $X$ covers for $J$ if and only if its image covers $G(X)$ for $K$. The last condition is `Functor.IsDenseSubsite.functorPushforward_mem_iff`. A dense subsite is continuous and cocontinuous by instances, and `Functor.IsDenseSubsite.coverPreserving` gives the cover preserving property. The lemmas `Functor.IsDenseSubsite.imageSieve_mem` and `Functor.IsDenseSubsite.equalizer_mem` restate local fullness and local faithfulness with sieves. For a sheaf on $C$, `Functor.IsDenseSubsite.mapPreimage` gives the action of a morphism $G(X) \to G(Y)$ of $D$, and the lemmas `Functor.IsDenseSubsite.mapPreimage_comp` and its relatives make this action functorial.

When the pushforward `G.sheafPushforwardContinuous A J K` is an equivalence, sheafification moves from $C$ to $D$. The functor `Functor.IsDenseSubsite.sheafifyOfIsEquivalence` sheafifies a presheaf on $D$ through $C$, `Functor.IsDenseSubsite.sheafifyAdjunctionOfIsEquivalence` makes it left adjoint to the inclusion, and `Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence` and `Functor.IsDenseSubsite.hasSheafify_of_isEquivalence` give the instances. The equivalence itself is `Functor.IsDenseSubsite.sheafEquiv : Sheaf J A ≌ Sheaf K A`, and `Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility` says that it commutes with sheafification.

Two modules prove that the pushforward is an equivalence. In `Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv`, the coefficient category $A$ has the limits over the comma categories of $G^{\mathrm{op}}$. The instance `Functor.IsDenseSubsite.instIsIsoSheafAppCounitSheafAdjunctionCocontinuous` says that the counit of the adjunction of Section 1 between the continuous and the cocontinuous pushforward is an isomorphism, and `Functor.IsDenseSubsite.instIsEquivalenceSheafSheafPushforwardContinuous` deduces the equivalence. In `Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense`, the hypothesis is on the site and not on $A$. The structure `Functor.OneHypercoverDenseData J₀ J X` is a 1-hypercover of $X$ in $C$ whose objects come from $C_0$, and `Functor.PreOneHypercoverDenseData` is its version with no covering conditions. The class `Functor.IsOneHypercoverDense` asks that such data exist for each object, with index types in a universe $w$. Then `Functor.isEquivalence_of_isOneHypercoverDense` says that the pushforward is an equivalence when $A$ has limits of size $w$. The proof builds the inverse by hand: `Functor.OneHypercoverDenseData.essSurj.sheaf` extends a sheaf $G_0$ on $C_0$ to $C$ by the limit of $G_0$ over the data of each object, and `Functor.OneHypercoverDenseData.essSurj.sheafIso` shows that it restricts to $G_0$. The lemma `Functor.OneHypercoverDenseData.isSheaf_iff` gives the sheaf condition on $C$ in terms of $C_0$ and the data, and `Functor.IsOneHypercoverDense.of_hasPullbacks` gives the class for a fully faithful functor into a category with pullbacks.

**Induced topologies on a dense subcategory.** The module `Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology` treats the case where only $K$ is given. The class `Functor.LocallyCoverDense G K` says that for each $K$ covering sieve $T$ on $G(X)$, the morphisms of $T$ that come from $C$ generate a covering sieve. The lemma `Functor.locallyCoverDense_of_isCoverDense` gives it for a cover dense and locally full functor. For a locally cover dense, locally full and locally faithful $G$, the lemma `Functor.mem_restrictedTopology_iff` describes the restricted topology of Section 1, and `Functor.coverPreserving_restrictedTopology` says that $G$ preserves covers for it. When $G$ is also cover dense, `Functor.mem_inducedTopology_iff_of_isCoverDense` says: $S$ covers for the induced topology if and only if its image covers for $K$. Then $G$ is a dense subsite for the induced topology. The comparison lemma in its classical form is `Functor.sheafInducedTopologyEquivOfIsCoverDense`: for small sites and a complete category $A$, the sheaves on $(D, K)$ and on $C$ with the induced topology are equivalent.

**Equivalences of sites.** The module `Mathlib.CategoryTheory.Sites.Equivalence` takes an equivalence $e : C \simeq D$ of categories, possibly in different universes, and a topology $J$ on $C$. An equivalence is cover dense, and the inverse functor induces a topology on $D$ for which $e$ is a dense subsite. The lemma `Equivalence.isDenseSubsite_functor_of_isCocontinuous` gives the dense subsite property when both functors are cocontinuous. The equivalence `Equivalence.sheafCongr J K e A : Sheaf J A ≌ Sheaf K A` precomposes with the two functors of $e$. Sheafification moves along $e$: `Equivalence.transportAndSheafify` transports a presheaf to $D$, sheafifies it there and transports it back, `Equivalence.transportSheafificationAdjunction` is the adjunction, and `Equivalence.hasSheafify` and `Equivalence.hasSheafCompose` move the instances. For an essentially small site, `smallSheafify` and `smallSheafificationAdjunction` sheafify through the small model, and `hasSheafifyEssentiallySmallSite` and `hasLimitsEssentiallySmallSite` give the instances.

**Sites over an object.** The module `Mathlib.CategoryTheory.Sites.Over` builds the topology `GrothendieckTopology.over J X` on `Over X`. The key tool is the order isomorphism `Sieve.overEquiv Y : Sieve Y ≃o Sieve Y.left`. A sieve on an object $Y \to X$ of `Over X` is the same as a sieve on $Y$ in $C$, because a morphism into $Y$ over $X$ is just a morphism into $Y$. The lemma `Sieve.overEquiv_iff` gives the membership, and the family `Sieve.overEquiv_pullback`, `Sieve.overEquiv_top` and its relatives give the behaviour under the operations on sieves. Then `GrothendieckTopology.mem_over_iff` says that $S$ covers $Y$ for `J.over X` if and only if `Sieve.overEquiv Y S` covers $Y$ for $J$. The precoverage version is `Precoverage.over`.

Instances make `Over.forget X` continuous and cocontinuous, and the same holds for `Over.map f`. The functor `Over.pullback f` is continuous when $C$ has pullbacks. The pushforward along `Over.forget X` is `GrothendieckTopology.overPullback J A X : Sheaf J A ⥤ Sheaf (J.over X) A`, and for a sheaf `F` the restriction is `Sheaf.over F X`, written `F.over X`. A morphism $f : X \to Y$ gives `GrothendieckTopology.overMapPullback J A f : Sheaf (J.over Y) A ⥤ Sheaf (J.over X) A`, with the coherence isomorphisms `GrothendieckTopology.overMapPullbackId` and `GrothendieckTopology.overMapPullbackComp`. The isomorphism `Sheaf.pushforwardOverMapIso` identifies the pushforward of `F.over Y` along `Over.map f` with `F.over X`, and `Sheaf.toPushforwardOverPullback` is the comparison morphism along `Over.pullback f`.

The module `Mathlib.CategoryTheory.Sites.SubcanonicalOver` holds one result, `GrothendieckTopology.subcanonical_over`: if $J$ is subcanonical, then so is `J.over X`. The module `Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver` packages the restrictions into the pseudofunctor `GrothendieckTopology.pseudofunctorOver J A` from `LocallyDiscrete Cᵒᵖ` to `Cat`. It sends $X$ to `Sheaf (J.over X) A` and a morphism $f$ to `GrothendieckTopology.overMapPullback J A f`. This is the pseudofunctor that the descent theory of Chapter 10 applies to sheaves.

#### Common errors

1. A user tries to apply `Functor.IsDenseSubsite.sheafEquiv` with no instance that the pushforward is an equivalence. The equivalence needs either the limits of `Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv` in $A$ or the class `Functor.IsOneHypercoverDense` with limits of size $w$.
2. A user confuses `Functor.inducedTopology` and `Functor.restrictedTopology`. They agree when $G$ is continuous for the restricted topology, by `Functor.restrictedTopology_eq_inducedTopology`, but in general only the induced topology makes $G$ continuous.
3. A user tries to rewrite a covering sieve of `J.over X` directly as a sieve of $C$. The sieves live on different objects. Use `Sieve.overEquiv` and `GrothendieckTopology.mem_over_iff` to move between them.

### Exercises

1. (A) Show that the identity functor of a site is cover dense, from `Functor.IsCoverDense.is_cover` and the maximal sieve.
2. (A) Use `GrothendieckTopology.mem_over_iff` to show that the maximal sieve of an object of `Over X` covers for `J.over X`.
3. (B) Let $X$ be a topological space and let $B$ be a basis of its topology, viewed as a full subcategory of the opens. Show that the inclusion is cover dense for the topology of open covers.
4. (B) Prove that a morphism $\alpha$ of sheaves on $D$ with $\alpha \circ G^{\mathrm{op}} = 0$ is zero, for a cover dense and locally full $G$ and sheaves of abelian groups, with `Functor.IsCoverDense.restrictHomEquivHom`.
5. (B) Show that `Sieve.overEquiv Y` sends the maximal sieve to the maximal sieve, from `Sieve.overEquiv_iff`.
6. (C) For an equivalence $e : C \simeq D$ and a topology $J$ on $C$, describe the covering sieves of the induced topology on $D$ and prove that the equivalence `Equivalence.sheafCongr` exists in the case of sheaves of types.

### Reference

<?reference?>
