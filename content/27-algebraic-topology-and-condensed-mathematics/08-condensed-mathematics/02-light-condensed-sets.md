---
title: Light condensed sets
kind: theory
modules:
  - Mathlib.Condensed.Light.Basic
  - Mathlib.Condensed.Light.Explicit
  - Mathlib.Condensed.Light.Functors
  - Mathlib.Condensed.Light.EffectiveEpi
  - Mathlib.Condensed.Light.Epi
  - Mathlib.Condensed.Light.Limits
  - Mathlib.Condensed.Light.Instances
  - Mathlib.Condensed.Light.Small
  - Mathlib.Condensed.Light.TopComparison
  - Mathlib.Condensed.Light.TopCatAdjunction
  - Mathlib.Condensed.Light.Module
  - Mathlib.Condensed.Light.AB
  - Mathlib.Condensed.Light.Monoidal
  - Mathlib.Condensed.Light.InternallyProjective
  - Mathlib.Condensed.Light.Sequence
explains:
  E3: [LightCondensed, LightCondSet, LightCondensed.equalizerCondition, LightCondSet.epi_iff_locallySurjective_on_lightProfinite, LightCondensed.equivSmall, LightCondSet.topCatAdjunction, LightCondSet.fullyFaithfulSequentialToLightCondSet, LightCondMod, LightCondensed.instCountableAB4StarLightCondMod, LightCondensed.instMonoidalClosedLightCondMod, LightCondensed.internallyProjective_iff_tensor_condition, LightCondensed.internallyProjective_free_natUnionInfty]
  E2: [LightCondensed.ofSheafLightProfinite, LightCondMod.epi_iff_locallySurjective_on_lightProfinite, LightCondMod.factorsThru_lightProfinite_epi_of_epi, lightProfiniteToLightCondSet, LightProfinite.toCondensed, lightProfiniteToLightCondSetFullyFaithful, TopCat.toLightCondSet, topCatToLightCondSet, lightCondSetToTopCat, LightCondSet.toTopCat, LightCondSet.topCatAdjunctionCounit_bijective, LightCondSet.sequentialAdjunction, LightCondSet.sequentialAdjunctionHomeo, LightCondAb, LightCondensed.free, LightCondensed.forget, LightCondensed.freeForgetAdjunction, LightCondensed.instIsGrothendieckAbelianLightCondMod, LightCondensed.instSmallHom, LightProfinite.hasSheafify, LightCondensed.ihomPoints, LightCondensed.free_lightProfinite_internallyProjective_iff_tensor_condition]
  E1: auto
families: []
requires: [V24.C07, V25.C02, V25.C06, V27.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Light condensed sets

### Overview

Section 1 built condensed sets on all compact Hausdorff spaces. That site is large, so the values of a condensed set over `CompHaus.{u}` live in the next universe, and the category of condensed abelian groups has no set of generators in the universe of its morphisms. Clausen and Scholze later proposed a smaller variant. A *light condensed set* is a sheaf on light profinite sets, the profinite sets with countably many clopen subsets. Up to isomorphism these form a set, so the universe does not rise, and light condensed abelian groups form a Grothendieck abelian category.

The price is that no infinite light profinite set is Stonean, so the simple sheaf condition of Section 1 on Stonean spaces is not available. The section shows what replaces it. Epimorphisms are tested by local surjectivity, and countable products of epimorphisms stay epimorphisms. The comparison with topological spaces now works for sequential spaces in place of compactly generated ones, because the test space $\mathbb{N} \cup \{\infty\}$ of convergent sequences is light.

Light condensed modules also carry a closed symmetric monoidal structure. An object $P$ is internally projective if the internal hom out of $P$ preserves epimorphisms. Mathlib proves that the free module on $\mathbb{N} \cup \{\infty\}$ is internally projective, a fact that the theory of Clausen and Scholze uses often.

### Definitions

**Definition (Light condensed object).** The category `LightCondensed C` is the category of sheaves on `LightProfinite.{u}` for the coherent topology with values in $C$. The covering families are the finite jointly surjective families, as in Section 1. A *light condensed set* is a light condensed object in `Type u`, and a *light condensed $R$-module* is one in `ModuleCat R`.

**Definition (Light condensed set of a space).** For a topological space $Y$, the light condensed set $\underline{Y}$ has the value $C(S, Y)$ at a light profinite set $S$.

**Definition (Locally surjective).** A morphism $f : X \to Y$ of light condensed sets is *locally surjective* if for each $S$ and $y \in Y(S)$ there are a surjection $\pi : S' \to S$ and $x \in X(S')$ with $f(x) = \pi^\ast y$.

**Definition (Internally projective object).** In a closed monoidal category with internal hom $\underline{\mathrm{Hom}}(P, -)$, an object $P$ is *internally projective* if $\underline{\mathrm{Hom}}(P, -)$ preserves epimorphisms.

### Theorems and proofs

**Proposition (Explicit sheaf condition).** A presheaf on `LightProfinite` is a light condensed object if and only if it sends finite coproducts to products and satisfies the equalizer condition for surjections.

*Proof.* The proof of the explicit sheaf condition in Section 1 uses only finite coproducts, pullbacks along surjections and the fact that surjections are effective epimorphisms. Light profinite sets have all three: a finite coproduct and a fibre product of light profinite sets are light, since they are closed subspaces of finite products, and Section 7.2 identifies the effective epimorphisms with the surjections. $\square$

**Proposition (No infinite Stonean light sets).** An infinite light profinite set $S$ is not extremally disconnected.

*Proof.* A light profinite set is second countable and compact Hausdorff, so it is metrizable; fix a metric $d$. Since $S$ is infinite and compact, it contains a sequence of distinct points with a limit $x$, and after removing $x$ and passing to a subsequence, $x_n \neq x$ and $d(x_{n+1}, x) < d(x_n, x)/3$. Let $r_n = d(x_n, x)/3$ and $V_n$ the open ball of radius $r_n$ about $x_n$. For $m > n$, points of $V_m$ have distance $< d(x_m, x) + r_m < \tfrac{4}{9} d(x_n, x)$ from $x$, and points of $V_n$ have distance $> \tfrac{2}{3} d(x_n, x)$ from $x$. So the $V_n$ are pairwise disjoint, and none contains $x$. Let $U = \bigcup_n V_{2n}$. Then $x \in \overline{U}$, since $x_{2n} \to x$. Each $x_{2n+1}$ has the open neighbourhood $V_{2n+1}$, disjoint from $U$, so $x_{2n+1} \notin \overline{U}$. As $x_{2n+1} \to x$, every neighbourhood of $x$ meets the complement of $\overline{U}$. So $\overline{U}$ is not open. $\square$

**Theorem (Epimorphisms).** A morphism of light condensed sets or modules is an epimorphism if and only if it is locally surjective.

*Proof.* This is the general description of epimorphisms of sheaves in Volume 25, Chapter 6, for the coherent topology on `LightProfinite`. A sieve on $S$ is covering exactly when it contains a finite jointly surjective family, and such a family can be replaced by the single surjection from its coproduct. $\square$

**Theorem (Countable AB4*).** In light condensed $R$-modules, a countable product of epimorphisms is an epimorphism. So countable products are exact.

*Proof.* Let $f_n : A_n \to B_n$ be epimorphisms for $n \in \mathbb{N}$. Products of sheaves are computed pointwise. Let $y = (y_n)_n \in \prod_n B_n(S)$. For each $n$, local surjectivity gives a surjection $\pi_n : S_n \to S$ and $x_n \in A_n(S_n)$ with $f_n(x_n) = \pi_n^\ast y_n$. Let $S' = \{(s_n)_n \in \prod_n S_n \mid \pi_n(s_n) = \pi_0(s_0) \text{ for all } n\}$. It is closed in a countable product of light profinite sets, so it is compact, Hausdorff, totally disconnected and second countable, that is, light. The map $q : S' \to S$, $(s_n) \mapsto \pi_0(s_0)$, is surjective: for $s \in S$ choose $s_n \in \pi_n^{-1}(s)$ for each $n$. Let $p_n : S' \to S_n$ be the projections, so $\pi_n \circ p_n = q$. The element $(p_n^\ast x_n)_n \in \prod_n A_n(S')$ maps to $(p_n^\ast \pi_n^\ast y_n)_n = q^\ast y$. So the product map is locally surjective. Kernels commute with products, so a countable product of short exact sequences is short exact. $\square$

The proof needs countability at one place: an uncountable product of light profinite sets is not second countable, so $S'$ would leave the site.

**Theorem (Essential smallness).** Every light profinite set is homeomorphic to a closed subset of the Cantor set $\{0, 1\}^{\mathbb{N}}$. So `LightProfinite.{u}` is essentially small, and light condensed objects are equivalent to sheaves on a small site.

*Proof.* By Section 7.2, $S = \lim_n S_n$ with finite $S_n$, and $S$ is a closed subspace of $\prod_n S_n$. Embed each $S_n$ into $\{0,1\}^{k_n}$ for some $k_n$. Then $\prod_n S_n$ embeds as a closed subspace of $\prod_n \{0,1\}^{k_n} \cong \{0,1\}^{\mathbb{N}}$. The closed subsets of the Cantor set form a set, so the isomorphism classes of light profinite sets form a set, and the full subcategory on a choice of representatives is small and equivalent to `LightProfinite.{u}`. An equivalence of sites gives an equivalence of sheaf categories. $\square$

**Corollary (Grothendieck abelian).** Light condensed $R$-modules form a Grothendieck abelian category, and the morphisms between two of them form a set in `Type u`.

*Proof.* Sheaves of modules on a small site form a Grothendieck abelian category: they have exact filtered colimits, and the sheafified free modules on the representable presheaves form a generating set (Volume 25). The smallness of the morphisms follows from the equivalence. $\square$

**Theorem (Sequential spaces embed).** The functor $Y \mapsto \underline{Y}$ from `TopCat.{u}` to light condensed sets has a left adjoint. The counit $\underline{Y}(\ast) \to Y$ is a continuous bijection, and it is a homeomorphism if and only if $Y$ is sequential. So $Y \mapsto \underline{Y}$ is fully faithful on sequential spaces.

*Proof.* The adjunction and the bijectivity of the counit are proved as in Section 1, with light profinite sets in place of compact Hausdorff spaces. The topology on $\underline{Y}(\ast) = Y$ is the final topology for all continuous maps $S \to Y$ with $S$ light. Let $Y$ be sequential and let $A \subseteq Y$ have closed preimages under all these maps. Let $y_n \to y$ with $y_n \in A$. The map $c : \mathbb{N} \cup \{\infty\} \to Y$ with $c(n) = y_n$ and $c(\infty) = y$ is continuous, and $c^{-1}(A)$ is closed and contains $\mathbb{N}$, so it contains $\infty$, and $y \in A$. So $A$ is sequentially closed, hence closed. Conversely, if the counit is a homeomorphism, let $A$ be sequentially closed in $Y$. For a continuous $f : S \to Y$ with $S$ light, $f^{-1}(A)$ is sequentially closed in $S$, since $f$ preserves convergent sequences. A metrizable space is sequential, so $f^{-1}(A)$ is closed. So $A$ is closed in the final topology, which is the topology of $Y$. Full faithfulness follows as in Section 1. $\square$

**Theorem (Test for internal projectivity).** Let $P$ be a light condensed $R$-module, and write $R[S]$ for the free module on the light condensed set of $S$. Then $P$ is internally projective if and only if for every epimorphism $e : A \to B$, every $S$ and every $g : P \otimes R[S] \to B$, there are a surjection $\pi : S' \to S$ and $g' : P \otimes R[S'] \to A$ with $e \circ g' = g \circ (P \otimes R[\pi])$.

*Proof.* For each $S$ there is a natural bijection $\underline{\mathrm{Hom}}(P, B)(S) \cong \mathrm{Hom}(P \otimes R[S], B)$. It comes from the Yoneda lemma, $M(S) \cong \mathrm{Hom}(R[S], M)$, and the tensor and hom adjunction. By the theorem on epimorphisms, $\underline{\mathrm{Hom}}(P, e)$ is an epimorphism exactly when it is locally surjective. Under the bijection, an element of $\underline{\mathrm{Hom}}(P, B)(S)$ is a map $g$, its restriction along $\pi$ is $g \circ (P \otimes R[\pi])$, and its image of $g'$ is $e \circ g'$. So local surjectivity is the stated condition. $\square$

**Theorem (The free module on a convergent sequence).** For a commutative ring $R$ in `Type`, the module $R[\mathbb{N} \cup \{\infty\}]$ is internally projective in light condensed $R$-modules.

*Proof.* By the test, it suffices to lift maps $R[\mathbb{N} \cup \{\infty\}] \otimes R[S] \to B$ through an epimorphism $A \to B$ after a surjective change of $S$. The tensor product of free modules is $R[S \times (\mathbb{N} \cup \{\infty\})]$, so the map is an element of $B(S \times (\mathbb{N} \cup \{\infty\}))$. Local surjectivity gives a surjection $\pi : T \to S \times (\mathbb{N} \cup \{\infty\})$ and a lift over $T$. The key step, the lemma `aux` in `Condensed.Light.Sequence`, replaces $T$ by a product form: it builds a surjection $S' \to S$ and a surjection $T' \to S' \times (\mathbb{N} \cup \{\infty\})$ through $T$ that splits over $\infty$. The space $S'$ is a fibre product, over $S$, of the fibres of $T$ over the points of $\mathbb{N} \cup \{\infty\}$, built as in the proof of countable AB4*. On $S' \times (\mathbb{N} \cup \{\infty\})$ the lift is then corrected at $\infty$ with the splitting, which gives $g'$. This outline follows the structure of the source. $\square$

### Examples

**Example (Convergent sequences in ℝ).** The value of $\underline{\mathbb{R}}$ at $\mathbb{N} \cup \{\infty\}$ is the set of continuous maps $c$, that is, the convergent sequences $(c(n))_n$ together with their limit $c(\infty)$. Restriction along the inclusion $\{\infty\} \to \mathbb{N} \cup \{\infty\}$ sends $c$ to its limit, and restriction along the constant map $\mathbb{N} \cup \{\infty\} \to \{\ast\}$ sends a point to the constant sequence. Since $\mathbb{R}$ is metrizable, hence sequential, the theorem shows that a morphism $\underline{\mathbb{R}} \to \underline{\mathbb{R}}$ is the same as a continuous map $\mathbb{R} \to \mathbb{R}$. A function $f : \mathbb{R} \to \mathbb{R}$ that preserves limits of sequences already gives a morphism, and it is continuous, as it must be.

**Counterexample (The convergent sequence is not Stonean).** In $\mathbb{N} \cup \{\infty\}$, the set $E$ of even numbers is open, its closure is $E \cup \{\infty\}$, and every neighbourhood of $\infty$ contains odd numbers. So the closure is not open. This is the proposition above for the sequence $x_n = n$. A consequence: the surjection $p : (E \cup \{\infty\}) \sqcup ((\mathbb{N} \setminus E) \cup \{\infty\}) \to \mathbb{N} \cup \{\infty\}$ from two copies of the space, one with the even and one with the odd numbers, has no continuous section. A section $\sigma$ sends $\infty$ into one copy, say the even one, and that copy is clopen, so $\sigma^{-1}$ of it is a neighbourhood of $\infty$, which contains odd numbers that $\sigma$ must send to the odd copy. So $\mathbb{N} \cup \{\infty\}$ is not projective, and the covering by $p$ cannot be removed.

**Example (Light condensed set of a light profinite set).** For a light profinite $T$, `LightProfinite.toCondensed T` is the representable sheaf $S \mapsto C(S, T)$. At a finite $S$ with $k$ points its value is $T^k$. The functor $T \mapsto \underline{T}$ is fully faithful by the Yoneda lemma, since the coherent topology is subcanonical.

### The library around it

::: mathlib
`LightCondensed` · `Mathlib.Condensed.Light.Basic`

`LightCondensed.{u} C` is `Sheaf (coherentTopology LightProfinite.{u}) C`. The abbreviation `LightCondSet.{u}` takes values in `Type u`, without the universe bump of `CondensedSet`. The docstring follows the lectures of Clausen and Scholze on light condensed sets.

<?decl LightCondensed?>
:::

::: mathlib
`LightCondensed.equalizerCondition` · `Mathlib.Condensed.Light.Explicit`

A light condensed object satisfies the equalizer condition; `LightCondensed.ofSheafLightProfinite` builds a light condensed object from a presheaf with the explicit conditions.

<?decl LightCondensed.equalizerCondition?>
:::

::: mathlib
`LightCondSet.epi_iff_locallySurjective_on_lightProfinite` · `Mathlib.Condensed.Light.Epi`

The theorem on epimorphisms for light condensed sets. The module version is `LightCondMod.epi_iff_locallySurjective_on_lightProfinite`, and `LightCondMod.factorsThru_lightProfinite_epi_of_epi` restates it as the existence of a surjection and a lift, which the proof for $\mathbb{N} \cup \{\infty\}$ uses.

<?decl LightCondSet.epi_iff_locallySurjective_on_lightProfinite?>
:::

::: mathlib
`LightCondensed.equivSmall` · `Mathlib.Condensed.Light.Small`

The equivalence of `LightCondensed C` with sheaves on a small model of `LightProfinite`. From it, the instance `LightCondensed.instSmallHom` makes the morphism types small, and the module `Condensed.Light.Instances` provides sheafification, for example `LightProfinite.hasSheafify`.

<?decl LightCondensed.equivSmall?>
:::

::: mathlib
`LightCondensed.instCountableAB4StarLightCondMod` · `Mathlib.Condensed.Light.AB`

The instance `CountableAB4Star (LightCondMod R)`. The source derives it from the exactness of limits of shape `Discrete ℕ`, which comes from the preservation of epimorphisms by countable products. The same file has `LightCondensed.instIsGrothendieckAbelianLightCondMod`, from `CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`.

<?decl LightCondensed.instCountableAB4StarLightCondMod?>
:::

::: mathlib
`LightCondSet.fullyFaithfulSequentialToLightCondSet` · `Mathlib.Condensed.Light.TopCatAdjunction`

Full faithfulness on sequential spaces. The adjunction is `LightCondSet.topCatAdjunction : lightCondSetToTopCat ⊣ topCatToLightCondSet`, and `LightCondSet.topCatAdjunctionCounit_bijective` is the bijectivity of the counit. Both functors stay in `TopCat.{u}`.

<?decl LightCondSet.fullyFaithfulSequentialToLightCondSet?>
:::

::: mathlib
`LightCondensed.internallyProjective_free_natUnionInfty` · `Mathlib.Condensed.Light.Sequence`

The statement `InternallyProjective ((free R).obj (ℕ∪{∞}).toCondensed)` for `R : Type` with `[CommRing R]`. The ring is in `Type`, so the result is about `LightCondMod.{0} R`. The test is `LightCondensed.internallyProjective_iff_tensor_condition`, its form for free modules on light profinite sets is `LightCondensed.free_lightProfinite_internallyProjective_iff_tensor_condition`, and the bijection with maps out of a tensor product is `LightCondensed.ihomPoints`. The monoidal closed structure is the instance `LightCondensed.instMonoidalClosedLightCondMod`.

<?decl LightCondensed.internallyProjective_free_natUnionInfty?>
:::

Common errors of a learner:

- The Stonean method of Section 1 does not apply. Test epimorphisms with local surjectivity, not with values on special spaces.
- `LightCondSet.{u}` lives in `Type u`, while `CondensedSet.{u}` lives in `Type (u+1)`. Do not mix the universes of the two functors to `TopCat`.
- The countable AB4* instance does not give exactness of uncountable products.
- `ℕ∪{∞}` is scoped notation in the namespace `LightProfinite`.

### Exercises

1. (A) Show that a finite product and a finite coproduct of light profinite sets are light. *Hint:* countably many clopen sets.
2. (A) Compute $\underline{Y}(\{0, 1, 2\})$ for a space $Y$, and the restriction maps to $\underline{Y}(\{0\})$.
3. (A) Show that $\{0,1\}^{\mathbb{R}}$ is profinite but not light. *Hint:* a second countable compact Hausdorff space has at most $2^{\aleph_0}$ points; alternatively, count clopen sets.
4. (B) Show that the left adjoint $\underline{Y} \mapsto \underline{Y}(\ast)$ sends the light condensed set of a space $Y$ to its sequential coreflection: the set $Y$ with the sequentially open sets as open sets.
5. (B) Show that a light condensed set is determined by its values on the spaces $\{0, 1\}^{\mathbb{N}}$ and on finite sets. *Hint:* a closed subset of the Cantor set is a retract of it, or use the explicit sheaf condition with a surjection from a coproduct.
6. (B) Show that $\underline{\mathrm{Hom}}(R[\ast], M) \cong M$ for every light condensed module $M$, and conclude that $R[\ast]$ is internally projective. *Hint:* $R[\ast]$ is the unit of the tensor product.
7. (C) Show that $P \oplus Q$ is internally projective if and only if $P$ and $Q$ are. Deduce that $R[F]$ is internally projective for every finite set $F$. *Hint:* $\underline{\mathrm{Hom}}(P \oplus Q, -) \cong \underline{\mathrm{Hom}}(P, -) \times \underline{\mathrm{Hom}}(Q, -)$, a retract of an epimorphism is an epimorphism, and $R[F] \cong R[\ast]^{F}$.

### Notes and history

Clausen and Scholze introduced light condensed sets in lectures after their work of 2019 on condensed mathematics; the docstring of `Condensed.Light.Basic` links to the video lectures. The internal projectivity of $\mathbb{Z}[\mathbb{N} \cup \{\infty\}]$ appears in these lectures as a basic tool. The index of this edition has no declaration for the computation of solid modules in the light setting.

The Mathlib Author of `Condensed.Light.EffectiveEpi` and `Condensed.Light.Sequence` is listed in each file as Jonas van der Schaaf with Dagur Asgeirsson. `Condensed.Light.Instances` is by Joël Riou. `Condensed.Light.AB`, `Condensed.Light.Basic`, `Condensed.Light.Epi`, `Condensed.Light.Explicit`, `Condensed.Light.Functors`, `Condensed.Light.InternallyProjective`, `Condensed.Light.Limits`, `Condensed.Light.Module`, `Condensed.Light.Monoidal`, `Condensed.Light.Small`, `Condensed.Light.TopComparison` and `Condensed.Light.TopCatAdjunction` are by Dagur Asgeirsson.

### Reference

<?reference?>
