---
title: Condensed sets and condensed modules
kind: theory
modules:
  - Mathlib.Condensed.Basic
  - Mathlib.Condensed.Equivalence
  - Mathlib.Condensed.Explicit
  - Mathlib.Condensed.Functors
  - Mathlib.Condensed.EffectiveEpi
  - Mathlib.Condensed.Epi
  - Mathlib.Condensed.Limits
  - Mathlib.Condensed.TopComparison
  - Mathlib.Condensed.TopCatAdjunction
  - Mathlib.Condensed.Module
  - Mathlib.Condensed.AB
  - Mathlib.Condensed.Discrete.Basic
  - Mathlib.Condensed.Discrete.Characterization
  - Mathlib.Condensed.Discrete.Colimit
  - Mathlib.Condensed.Discrete.LocallyConstant
  - Mathlib.Condensed.Discrete.Module
  - Mathlib.Condensed.Solid
explains:
  E3: [Condensed, CondensedSet, Condensed.equalizerCondition, Condensed.ofSheafStonean, Condensed.StoneanCompHaus.equivalence, topCatToCondensedSet, CondensedSet.topCatAdjunction, CondensedSet.topCatAdjunctionCounit_bijective, CondensedSet.epi_iff_surjective_on_stonean, CondensedMod, Condensed.hasExactColimitsOfShape, Condensed.discrete, CondensedSet.LocallyConstant.iso, CondensedSet.isDiscrete_tfae, CondensedMod.IsSolid]
  E2: [Condensed.hom_ext, Condensed.ofSheafCompHaus, Condensed.ofSheafProfinite, Condensed.ProfiniteCompHaus.equivalence, Condensed.isSheafProfinite, Condensed.isSheafStonean, compHausToCondensed, profiniteToCondensed, CompHaus.toCondensed, Condensed.ulift, TopCat.toCondensedSet, factorsThrough_of_pullbackCondition, equalizerCondition_yonedaPresheaf, condensedSetToTopCat, CondensedSet.toTopCat, CondensedSet.compactlyGeneratedAdjunction, CondensedSet.fullyFaithfulCompactlyGeneratedToCondensedSet, CondensedSet.epi_iff_locallySurjective_on_compHaus, CondensedMod.epi_iff_surjective_on_stonean, CondensedAb, Condensed.free, Condensed.forget, Condensed.freeForgetAdjunction, Condensed.hasExactLimitsOfShape, Condensed.underlying, Condensed.discreteUnderlyingAdj, Condensed.IsDiscrete, CondensedMod.isDiscrete_tfae, CondensedSet.LocallyConstant.functor, CondensedSet.LocallyConstant.functorFullyFaithful, CompHausLike.LocallyConstant.functor, CompHausLike.LocallyConstant.adjunction, Condensed.isoLocallyConstantOfIsColimit, CondensedMod.LocallyConstant.functor, Condensed.finFree, Condensed.profiniteFree, Condensed.profiniteSolid, Condensed.profiniteSolidification]
  E1: auto
families: []
requires: [V07, V24.C05, V25.C02, V25.C06, V27.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Condensed sets and condensed modules

### Overview

Topological abelian groups do not form an abelian category. The identity map from $\mathbb{R}$ with the discrete topology to $\mathbb{R}$ with the usual topology is injective and surjective, but it is not an isomorphism, and it has no cokernel that sees the difference. Condensed mathematics fixes this. It replaces a space $X$ by the functor $S \mapsto C(S, X)$ on compact Hausdorff spaces $S$, and it allows all functors of this kind that satisfy a sheaf condition.

A *condensed set* is a sheaf on the category `CompHaus` of Section 7.2 for the coherent topology. Its value at the one point space is its set of points, and its value at $S$ is the set of "families of points parametrized continuously by $S$". Condensed abelian groups and condensed modules are sheaves with values in abelian groups and modules. They form an abelian category with exact products and exact filtered colimits.

This section follows the folder `Condensed` of Mathlib. It proves the explicit sheaf condition, shows that Stonean spaces give a site with a simpler condition, and constructs the functor from topological spaces with its left adjoint. It then studies epimorphisms, the AB axioms, discrete condensed sets, and the definition of solid modules.

### Definitions

**Definition (Coherent topology).** On `CompHaus`, a sieve on $S$ is *covering* for the coherent topology if it contains a finite family $(S_i \to S)_i$ whose images cover $S$. By Section 7.2 such a family is effective epimorphic, and the precoherence of `CompHaus` makes this a Grothendieck topology (Volume 25, Chapter 6).

**Definition (Condensed object).** For a category $A$, the category `Condensed A` of *condensed objects* in $A$ is the category of sheaves on `CompHaus.{u}` for the coherent topology with values in $A$. A *condensed set* is a condensed object in `Type (u+1)`, and a *condensed $R$-module* is a condensed object in `ModuleCat R`. For $R = \mathbb{Z}$ these are the *condensed abelian groups*.

**Definition (Equalizer condition).** A presheaf $X$ on `CompHaus` satisfies the *equalizer condition* if for every surjection $\pi : S' \to S$ with projections $p_1, p_2 : S' \times_S S' \to S'$, the diagram $X(S) \to X(S') \rightrightarrows X(S' \times_S S')$ is an equalizer.

**Definition (Condensed set of a space).** For a topological space $Y$, the condensed set $\underline{Y}$ has $\underline{Y}(S) = C(S, Y)$, with restriction by composition.

**Definition (Discrete condensed object).** The *discrete* condensed object on $M \in A$ is the sheafification of the constant presheaf with value $M$. A condensed object is *discrete* if it is isomorphic to one of this form.

**Definition (Solid module).** For a finite set $T$, let $R[T]$ be the free condensed $R$-module on $T$. For a profinite $S$, the module $R[S]^{\blacksquare}$ is the right Kan extension of $T \mapsto R[T]$ from finite sets to profinite sets, evaluated at $S$. There is a natural map $R[S] \to R[S]^{\blacksquare}$. A condensed $R$-module $M$ is *solid* if every morphism $R[S] \to M$ extends uniquely along this map.

### Theorems and proofs

**Theorem (Explicit sheaf condition).** A presheaf $X$ on `CompHaus` is a sheaf for the coherent topology if and only if it sends finite coproducts to products and satisfies the equalizer condition.

*Proof.* Let $X$ be a sheaf. The empty family covers the empty space, so $X(\emptyset)$ is a point. For a finite coproduct $S = \bigsqcup_i S_i$, the inclusions cover $S$, and $S_i \times_S S_j$ is empty for $i \neq j$ and equal to $S_i$ for $i = j$. So a matching family is any element of $\prod_i X(S_i)$, and the sheaf condition says that $X(S) \to \prod_i X(S_i)$ is a bijection. For a surjection $\pi : S' \to S$, the one element family $\{\pi\}$ covers $S$, and the sheaf condition for it is the equalizer condition.

Conversely, let $X$ have both properties, and let $(f_i : S_i \to S)_{i \in F}$ be a finite covering family. Let $T = \bigsqcup_i S_i$ and $\pi : T \to S$ the induced surjection. Then $T \times_S T = \bigsqcup_{i,j} S_i \times_S S_j$, since pullbacks in `CompHaus` are subspaces of products and commute with finite coproducts. A matching family $(x_i)_i$ with $x_i \in X(S_i)$ is the same as an element $x \in X(T) = \prod_i X(S_i)$ whose two pullbacks agree in $X(T \times_S T) = \prod_{i,j} X(S_i \times_S S_j)$. The equalizer condition gives a unique $s \in X(S)$ with $\pi^\ast s = x$, that is, $f_i^\ast s = x_i$ for all $i$. Finite jointly surjective families are stable under pullback, and they generate the coherent topology. A presheaf that satisfies the sheaf condition for each family of such a generating set is a sheaf (Volume 25, Chapter 6). So $X$ is a sheaf. $\square$

**Theorem (Sheaves on Stonean spaces).** A presheaf on `Stonean` is a sheaf for the coherent topology if and only if it sends finite coproducts to products. Restriction along `Stonean` $\to$ `CompHaus` is an equivalence between condensed objects and these sheaves.

*Proof.* A sheaf sends finite coproducts to products, by the first part of the previous proof; it uses only finite coproducts and their intersections, which exist in `Stonean`. Conversely, let $(f_i : S_i \to S)_i$ be a finite covering family of a Stonean space $S$. The coproduct $T = \bigsqcup_i S_i$ is Stonean and $T \to S$ is surjective. By the theorem of Gleason, $S$ is projective, so there is a section $\sigma : S \to T$. The sets $U_i = \sigma^{-1}(S_i)$ form a finite clopen partition of $S$, and $f_i \circ \sigma$ restricted to $U_i$ is the inclusion $U_i \to S$. So every covering sieve contains the sieve of a finite clopen partition. The coherent topology on `Stonean` is the extensive topology, and the sheaves for the extensive topology are the presheaves that send finite coproducts to products (Volume 25, Chapter 6). For the equivalence, every compact Hausdorff space is the image of a Stonean space by Section 7.2, so `Stonean` is a dense subsite of `CompHaus`, and the comparison lemma of Volume 25, Chapter 6 gives the equivalence. $\square$

The same comparison lemma gives the equivalence with sheaves on `Profinite`, because a profinite set covers each compact Hausdorff space.

**Theorem (Spaces give condensed sets).** For every topological space $Y$, $\underline{Y}$ is a condensed set.

*Proof.* Use the explicit condition. A continuous map out of $\bigsqcup_i S_i$ is a family of continuous maps out of the $S_i$, and there is one map out of $\emptyset$. Let $\pi : S' \to S$ be surjective. It is a closed map, so a quotient map. A continuous $g : S' \to Y$ has the form $h \circ \pi$ for a continuous $h$ exactly when $g$ is constant on the fibres of $\pi$. Since $S' \times_S S'$ is the set of pairs $(a, b)$ with $\pi(a) = \pi(b)$, this says $g \circ p_1 = g \circ p_2$. The map $h$ is unique because $\pi$ is surjective. $\square$

**Theorem (The left adjoint).** The functor $Y \mapsto \underline{Y}$ from `TopCat` to condensed sets has a left adjoint. It sends $X$ to the set $X(\ast)$ with the final topology for the maps $\hat x : S \to X(\ast)$, $s \mapsto s^\ast x$, for all $S$ and $x \in X(S)$. Here $s^\ast x$ is the restriction of $x$ along the map $s : \ast \to S$. For each space $Y$ the counit $\underline{Y}(\ast) \to Y$ is bijective, and it is a homeomorphism if and only if $Y$ is compactly generated.

*Proof.* Let $f : X \to \underline{Y}$ be a morphism. For $x \in X(S)$ and $s \in S$, naturality along $s : \ast \to S$ gives $f_S(x)(s) = f_\ast(s^\ast x)$. So $f$ is determined by the map $g = f_\ast : X(\ast) \to Y$, and $g \circ \hat x = f_S(x)$ is continuous for all $x$. This says that $g$ is continuous for the final topology. Conversely, let $g : X(\ast) \to Y$ be continuous for the final topology. Put $f_S(x) = g \circ \hat x$, which is continuous. For $\varphi : T \to S$ and $t \in T$, $f_T(\varphi^\ast x)(t) = g((\varphi \circ t)^\ast x) = f_S(x)(\varphi(t))$, so $f$ is natural. The two constructions are inverse, and they are natural in $X$ and $Y$.

For the counit, $\underline{Y}(\ast) = C(\ast, Y)$ is the set $Y$. Its topology is the final topology for all continuous maps $S \to Y$ from compact Hausdorff spaces. This topology is finer than the topology of $Y$, so the counit is the identity map, a continuous bijection. It is a homeomorphism exactly when the topology of $Y$ is already final for these maps, which is the definition of a compactly generated space. $\square$

**Corollary (Compactly generated spaces embed).** The functor $Y \mapsto \underline{Y}$ is fully faithful on compactly generated spaces.

*Proof.* A right adjoint is fully faithful on the objects where the counit is an isomorphism (Volume 24, Chapter 5). $\square$

**Theorem (Epimorphisms).** A morphism $f : X \to Y$ of condensed sets or condensed modules is an epimorphism if and only if $f_S : X(S) \to Y(S)$ is surjective for every Stonean space $S$.

*Proof.* In a category of sheaves, a morphism is an epimorphism if and only if it is locally surjective (Volume 25, Chapter 6). Here locally surjective means: for each $S$ and $y \in Y(S)$ there are a surjection $\pi : S' \to S$ and $x \in X(S')$ with $f(x) = \pi^\ast y$. If $f$ is surjective on Stonean spaces, choose a Stonean $S'$ and a surjection $\pi : S' \to S$, and lift $\pi^\ast y$. Conversely, let $f$ be locally surjective and $S$ Stonean. For $y \in Y(S)$ take $\pi$ and $x$ as above, and a section $\sigma$ of $\pi$. Then $f(\sigma^\ast x) = \sigma^\ast \pi^\ast y = y$. $\square$

**Theorem (AB axioms).** Condensed $R$-modules form an abelian category in which products, coproducts and filtered colimits are exact.

*Proof.* Sheaves with values in an abelian category with enough limits and colimits form an abelian category (Volume 25, Chapter 2). By the theorem on Stonean spaces, work with presheaves on `Stonean` that send finite coproducts to products. The pointwise product of such presheaves has the same property, since products commute with products. The pointwise direct sum and the pointwise filtered colimit have it too, because in `ModuleCat R` finite products are direct sums and commute with direct sums and filtered colimits. So limits, direct sums and filtered colimits are computed pointwise on Stonean spaces. By the previous theorem, epimorphisms are the pointwise surjections there, and kernels are pointwise. So a sequence is short exact if and only if it is short exact at each Stonean $S$. Exactness of products, direct sums and filtered colimits then holds because it holds in `ModuleCat R`. $\square$

**Theorem (Discrete objects are locally constant).** For a set $M$, the discrete condensed set on $M$ is isomorphic to $S \mapsto \mathrm{LC}(S, M)$, the set of locally constant maps.

*Proof.* The presheaf $L(S) = \mathrm{LC}(S, M)$ is $\underline{M}$ for the discrete space $M$, so it is a sheaf. It suffices to show that maps $L \to F$ to a sheaf $F$ correspond to maps $M \to F(\ast)$, because the discrete object is left adjoint to $F \mapsto F(\ast)$. A map $L \to F$ gives $M = L(\ast) \to F(\ast)$. Conversely, let $g : M \to F(\ast)$. A locally constant $u : S \to M$ on a compact space has finitely many values $m_1, \ldots, m_n$, and its fibres $S_j$ are clopen, so $S = \bigsqcup_j S_j$. As $F(S) = \prod_j F(S_j)$, there is a unique element of $F(S)$ whose restriction to $S_j$ is the pullback of $g(m_j)$ along $S_j \to \ast$. This defines a natural map $L \to F$, and the two constructions are inverse. $\square$

### Examples

**Example (A condensed group with no points).** Let $\mathbb{R}_\delta$ be the discrete condensed group on $\mathbb{R}$ and $\underline{\mathbb{R}}$ the condensed group of the real line. The identity gives a monomorphism $\mathbb{R}_\delta \to \underline{\mathbb{R}}$. Its cokernel $Q$ is computed pointwise on Stonean spaces. At the point, $Q(\ast) = \mathbb{R}/\mathbb{R} = 0$. At $\beta\mathbb{N}$, continuous maps to $\mathbb{R}$ are bounded sequences and locally constant maps are sequences with finitely many values. So $Q(\beta\mathbb{N})$ contains the class of $(1/(n+1))_n$, which is not $0$. So $Q \neq 0$ although its underlying group is $0$, and the map $\mathbb{R}_\delta \to \underline{\mathbb{R}}$ is not an epimorphism.

**Counterexample (The counit can fail).** Let $Y$ be an uncountable set with the cocountable topology. An infinite subset $A$ is not compact: choose distinct $a_1, a_2, \ldots$ in $A$; the open sets $Y \setminus \{a_k \mid k > n\}$ cover $A$ with no finite subcover. So a continuous map $S \to Y$ from a compact space has finite image. A finite subspace of $Y$ is discrete, because finite sets are closed. So every continuous $S \to Y$ is locally constant. The final topology on $\underline{Y}(\ast)$ is then discrete, and the counit is the identity from discrete $Y$ to $Y$, which is not a homeomorphism.

**Example (A discrete condensed set on a profinite set).** For $M = \{0, 1\}$ and $S = \mathbb{N} \cup \{\infty\}$, the value $\mathrm{LC}(S, M)$ consists of the sequences that are eventually constant, with the value at $\infty$ the eventual value. Each factors through a finite quotient $\{0, \dots, n, \infty\}$, which is the colimit formula of `CondensedSet.isDiscrete_tfae`.

### The library around it

::: mathlib
`Condensed` · `Mathlib.Condensed.Basic`

`Condensed.{u} C` is `Sheaf (coherentTopology CompHaus.{u}) C`, and `CondensedSet.{u}` is `Condensed.{u} (Type (u + 1))`. The universe rises because `CompHaus.{u}` is a large category. An object `X` has the presheaf `X.obj`, and a morphism `f` has components `f.hom.app`. `Condensed.hom_ext` checks equality on components.

<?decl Condensed?>
:::

::: mathlib
`Condensed.equalizerCondition` · `Mathlib.Condensed.Explicit`

Every condensed object satisfies `EqualizerCondition X.obj`, from `CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition`. The constructors `Condensed.ofSheafCompHaus`, `Condensed.ofSheafProfinite` and `Condensed.ofSheafStonean` build condensed objects from presheaves with the explicit conditions.

<?decl Condensed.equalizerCondition?>
:::

::: mathlib
`CategoryTheory.coherentTopology` · `Mathlib.CategoryTheory.Sites.Coherent.Basic`

The coherent topology on a precoherent category, generated by finite effective epimorphic families. Volume 25, Chapter 6 treats it with the regular and the extensive topology.

<?decl CategoryTheory.coherentTopology?>
:::

::: mathlib
`CondensedSet.topCatAdjunction` · `Mathlib.Condensed.TopCatAdjunction`

The adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` between `CondensedSet.{u}` and `TopCat.{u+1}`. The underlying space is `CondensedSet.toTopCat`. The lemma `CondensedSet.topCatAdjunctionCounit_bijective` is the bijectivity of the counit, and `CondensedSet.fullyFaithfulCompactlyGeneratedToCondensedSet` is the corollary. The sheaf property of `TopCat.toCondensedSet` in `Condensed.TopComparison` rests on `factorsThrough_of_pullbackCondition` and `equalizerCondition_yonedaPresheaf`.

<?decl CondensedSet.topCatAdjunction?>
:::

::: mathlib
`CondensedSet.epi_iff_surjective_on_stonean` · `Mathlib.Condensed.Epi`

The criterion `Epi f ↔ ∀ S : Stonean, Function.Surjective (f.hom.app (op S.compHaus))`. The variant with local surjectivity on `CompHaus` is `CondensedSet.epi_iff_locallySurjective_on_compHaus`, and `CondensedMod.epi_iff_surjective_on_stonean` is the version for modules.

<?decl CondensedSet.epi_iff_surjective_on_stonean?>
:::

::: mathlib
`Condensed.hasExactColimitsOfShape` · `Mathlib.Condensed.AB`

Filtered colimits and coproducts in `CondensedMod R` are exact, which gives AB5 and AB4. The partner `Condensed.hasExactLimitsOfShape` gives AB4*, the exactness of products. The free functor `Condensed.free R` is left adjoint to `Condensed.forget R` through `Condensed.freeForgetAdjunction`.

<?decl Condensed.hasExactColimitsOfShape?>
:::

::: mathlib
`CondensedSet.isDiscrete_tfae` · `Mathlib.Condensed.Discrete.Characterization`

Seven equivalent conditions for `X.IsDiscrete`: the counit of `Condensed.discreteUnderlyingAdj` is an isomorphism, `X` is in the essential image of `Condensed.discrete` or of `CondensedSet.LocallyConstant.functor`, the restriction to `Profinite` is constant, and for every profinite `S` the value `X(S)` is the colimit of `X(S_i)` over the finite quotients `S_i`. The module version is `CondensedMod.isDiscrete_tfae`.

<?decl CondensedSet.isDiscrete_tfae?>
:::

::: mathlib
`CondensedMod.IsSolid` · `Mathlib.Condensed.Solid`

The class asks that `Hom(-, A)` sends `(Condensed.profiniteSolidification R).app S` to an isomorphism for every profinite `S`. Here `Condensed.profiniteSolid R` is the right Kan extension of `Condensed.finFree R` along `FintypeCat.toProfinite`. The source says in a TODO that this is not the correct definition for a general ring `R`, and that the right one goes through finite type `ℤ`-algebras and `ℤ[X]`. A second TODO asks to prove that `(profiniteSolid ℤ).obj S` is solid. So the index of this edition has no declaration for the computation of $\mathbb{Z}[S]^{\blacksquare}$ as a product of copies of $\mathbb{Z}$.

<?decl CondensedMod.IsSolid?>
:::

Common errors of a learner:

- A condensed set over `CompHaus.{u}` takes values in `Type (u+1)`. A map from a type in `Type u` needs `ULift`, and `Condensed.ulift` moves condensed sets across universes.
- The value `X(∗)` is only the set of points. Two condensed sets with the same points can differ, as the example $Q$ shows.
- Pointwise surjectivity on `CompHaus` is too strong a test for epimorphisms. Use Stonean spaces, or local surjectivity.
- `Condensed.discrete` is the constant sheaf. Its value at $S$ is $\mathrm{LC}(S, M)$, not $M$.

### Exercises

1. (A) Show that $\underline{Y}(\ast) = Y$ as a set and that $\underline{Y}(\{0, 1\}) = Y \times Y$. *Hint:* the two point space is a coproduct.
2. (A) Show that a condensed set $X$ has $X(\emptyset)$ a point. *Hint:* the empty family covers $\emptyset$.
3. (A) For a set $M$, compute the discrete condensed set on $M$ at a finite set $T$. *Hint:* a map from a finite discrete space is locally constant.
4. (B) Show that $Y \mapsto \underline{Y}$ preserves limits. *Hint:* it is a right adjoint, or compute $C(S, \lim Y_j)$.
5. (B) Show that a metrizable space is compactly generated, and conclude that $Y \mapsto \underline{Y}$ is fully faithful on metrizable spaces. *Hint:* sequences and $\mathbb{N} \cup \{\infty\}$.
6. (B) Show that the cokernel $Q$ in the first example has $Q(S) = 0$ for every finite $S$.
7. (C) Show that a morphism $X \to Y$ of condensed sets is a monomorphism if and only if $X(S) \to Y(S)$ is injective for every $S$. *Hint:* limits of sheaves are computed pointwise, and $f$ is mono exactly when its kernel pair is trivial.

### Notes and history

Clausen and Scholze introduced condensed sets in 2019, in lecture notes of Scholze on condensed mathematics; the docstring of `Condensed.Solid` cites Definition 5.1 of these notes for solid modules. The Liquid Tensor Experiment, completed in 2022, verified in Lean a main theorem of their theory of liquid vector spaces.

The Mathlib Author of `Condensed.Basic` is Adam Topaz. `Condensed.Equivalence` is by Adam Topaz, Nikolas Kuhn and Dagur Asgeirsson, and `Condensed.Explicit` by Dagur Asgeirsson, Riccardo Brasca and Filippo A. E. Nuccio. `Condensed.EffectiveEpi` is by Jonas van der Schaaf and Dagur Asgeirsson. `Condensed.AB`, `Condensed.Epi`, `Condensed.Functors`, `Condensed.Limits`, `Condensed.Module`, `Condensed.Solid`, `Condensed.TopComparison`, `Condensed.TopCatAdjunction` and the files in `Condensed.Discrete` are by Dagur Asgeirsson.

### Reference

<?reference?>
