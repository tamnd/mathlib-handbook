---
title: Polish spaces and standard Borel spaces
kind: api
modules:
  - Mathlib.MeasureTheory.Constructions.Polish.Basic
  - Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
explains:
  E2: [MeasureTheory.AnalyticSet.measurableSet_of_compl, Continuous.measurableEmbedding, PolishSpace.borelSchroederBernstein, MeasureTheory.exists_measurableEmbedding_real, Measurable.measurableSet_preimage_iff_of_surjective]
  E1: auto
families: []
requires: [V03, V13]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Polish spaces and standard Borel spaces

### Overview

A Polish space is a separable topological space whose topology comes from a complete metric. The real line, $\mathbb{R}^n$, the Cantor space $\{0, 1\}^{\mathbb{N}}$, the Baire space $\mathbb{N}^{\mathbb{N}}$, every separable Banach space and every closed or open subset of a Polish space are Polish. Volume 13 treats these spaces as topological spaces. This section treats their Borel sets. Descriptive set theory proves that the Borel σ-algebras of Polish spaces behave much better than general σ-algebras: an injective measurable map sends Borel sets to Borel sets, a continuous image of a Borel set has a Borel complement only when it is Borel, and two uncountable Polish spaces have isomorphic Borel σ-algebras.

A measurable space is *standard Borel* if its σ-algebra is the Borel σ-algebra of some Polish topology. This is the setting in which probability theory works without pathologies. The disintegration of measures and the existence of conditional distributions assume it. The section explains the class `StandardBorelSpace`, the analytic sets, the separation and image theorems, and the classification of standard Borel spaces up to isomorphism. It needs Sections 1 and 3 of this chapter and the Polish spaces of Volume 13.

### The library around it

#### Standard Borel spaces

The class `StandardBorelSpace α` holds for a measurable space $\alpha$ if there is a topology on $\alpha$ that is Polish and whose Borel σ-algebra is the given one (the field `StandardBorelSpace.polish`). The topology is not part of the data, because several Polish topologies give the same Borel sets. The lemma `MeasureTheory.borel_eq_borel_of_le` makes this precise for comparable topologies: if $t \le t'$ are two Polish topologies on the same type, they have the same Borel sets. To compute with one chosen topology, `upgradeStandardBorel` produces a structure `UpgradedStandardBorel α` that holds the topology, and its fields `UpgradedStandardBorel.toPolishSpace` and `UpgradedStandardBorel.toBorelSpace` give the two instances.

The instance `standardBorel_of_polish` gives the class to a Polish space with its Borel σ-algebra. The class is stable under the usual constructions:

| Lean name | Statement |
|---|---|
| `StandardBorelSpace.prod` | a product of two standard Borel spaces is standard Borel |
| `StandardBorelSpace.pi_countable` | a countable product of standard Borel spaces is standard Borel |
| `MeasurableSet.standardBorel` | a measurable subset of a standard Borel space is standard Borel |
| `standardBorelSpace_of_discreteMeasurableSpace` | a countable type with all sets measurable is standard Borel |
| `countablyGenerated_of_standardBorel` | the σ-algebra is countably generated |
| `measurableSingleton_of_standardBorel` | singletons are measurable |

The third line uses a strong fact. A Borel set $s$ of a Polish space need not be open or closed, but there is a finer Polish topology with the same Borel sets in which $s$ is clopen. Mathlib calls such a set *clopenable*, and `MeasureTheory.isClopenable_iff_measurableSet` states that in a Polish space the clopenable sets are exactly the Borel sets. The form `MeasurableSet.isClopenable'` states it for a standard Borel space. A clopen subset of a Polish space is Polish, so a Borel subset becomes Polish for the finer topology.

#### Analytic sets and the separation theorem

**Definition (Analytic set).** A subset $s$ of a topological space is *analytic* if it is empty or the image of a continuous map $\mathbb{N}^{\mathbb{N}} \to \alpha$. This is `MeasureTheory.AnalyticSet`.

Every Polish space is a continuous image of $\mathbb{N}^{\mathbb{N}}$ when it is not empty. So the continuous image of a Polish space is analytic (`MeasureTheory.analyticSet_range_of_polishSpace`), and a continuous image of an analytic set is analytic (`MeasureTheory.AnalyticSet.image_of_continuous`). The analytic sets are closed under countable unions and countable intersections (`MeasureTheory.AnalyticSet.iUnion`, `MeasureTheory.AnalyticSet.iInter`), and every Borel set of a Polish space is analytic (`MeasurableSet.analyticSet`).

An analytic set need not be Borel. The main theorem of the theory says when it is. Two sets $s$ and $t$ are *measurably separable* if there is a measurable $u$ with $s \subseteq u$ and $t \cap u = \emptyset$ (`MeasureTheory.MeasurablySeparable`). The separation theorem of Lusin, `MeasureTheory.AnalyticSet.measurablySeparable`, says that two disjoint analytic sets in a Hausdorff space with measurable open sets are measurably separable. Its proof splits $\mathbb{N}^{\mathbb{N}}$ into cylinders and finds a pair of cylinders that cannot be separated in each step. A sequence of such pairs converges to two points with the same image, which contradicts the disjointness. The step on the cylinders is `MeasureTheory.measurablySeparable_range_of_disjoint`.

**Theorem (Suslin).** In a Hausdorff space where open sets are measurable, a set $s$ such that $s$ and its complement are both analytic is measurable.

*Proof.* The sets $s$ and $s^c$ are disjoint and analytic. By the separation theorem there is a measurable $u$ with $s \subseteq u$ and $s^c \cap u = \emptyset$. The second condition says $u \subseteq s$. So $s = u$ is measurable. $\square$

This is `MeasureTheory.AnalyticSet.measurableSet_of_compl`.

#### Images of Borel sets

**Theorem (Lusin and Souslin).** Let $\gamma$ be Polish, $\beta$ Hausdorff with measurable open sets, and $f : \gamma \to \beta$ continuous and injective. Then $f$ sends Borel sets to measurable sets.

The proof refines the topology of $\gamma$ so that a given Borel set becomes clopen, and it uses the separation theorem on the images of the disjoint pieces of a countable partition. The basic form is `MeasureTheory.measurableSet_range_of_continuous_injective`, for the range of $f$. The general form is `MeasurableSet.image_of_continuousOn_injOn`, for a Borel set $s$ on which $f$ is continuous and injective. The variants `MeasurableSet.image_of_monotoneOn` and `MeasurableSet.image_of_antitoneOn` treat a monotone map between ordered spaces, which need not be continuous.

**Corollary (Continuous injections are measurable embeddings).** Let $\gamma$ be Polish with its Borel σ-algebra, and $\beta$ Hausdorff with its Borel σ-algebra. A continuous injective $f : \gamma \to \beta$ is a measurable embedding.

*Proof.* The map $f$ is continuous, so it is measurable. It is injective. A measurable embedding needs also that $f(s)$ is measurable for each measurable $s$, and this is the theorem of Lusin and Souslin. $\square$

This is `Continuous.measurableEmbedding`, with the form `ContinuousOn.measurableEmbedding` on a measurable subset. A measurable injective map from a standard Borel space to a countably separated space is a measurable embedding too (`Measurable.measurableEmbedding`). The proof makes the map continuous: `Measurable.exists_continuous` gives a finer Polish topology on the domain for which a measurable map with second countable range is continuous.

**Proposition (Quotient σ-algebras).** Let $X$ be standard Borel, $Z$ countably separated, and $f : X \to Z$ measurable and surjective. Then a set $s \subseteq Z$ is measurable if and only if $f^{-1}(s)$ is measurable.

*Proof sketch.* One direction is measurability of $f$. For the other, assume that $f^{-1}(s)$ is measurable. Choose a Polish topology on $X$, and refine it so that $f$ is continuous into a second countable space that carries the countably many separating sets of $Z$. Then $s = f(f^{-1}(s))$ and $s^c = f(f^{-1}(s^c))$, because $f$ is surjective. Both are continuous images of Borel sets, so both are analytic, and the theorem of Suslin gives that $s$ is measurable. $\square$

This is `Measurable.measurableSet_preimage_iff_of_surjective`. Its form for σ-algebras is `Measurable.map_measurableSpace_eq`: the push forward of the σ-algebra of $X$ along $f$ is the σ-algebra of $Z$. A consequence for topological quotients is the instance `Quotient.borelSpace`: the quotient of a Polish space by an equivalence relation, when it is second countable and $T_0$, carries the Borel σ-algebra of its quotient topology. The instances `QuotientGroup.borelSpace` and `CosetSpace.borelSpace` treat the quotient of a Polish group by a closed subgroup.

#### Isomorphism of standard Borel spaces

**Theorem (Borel form of Schröder and Bernstein).** Let $\alpha$ and $\beta$ be standard Borel, and $f : \alpha \to \beta$ and $g : \beta \to \alpha$ measurable and injective. Then $\alpha$ and $\beta$ are isomorphic as measurable spaces.

*Proof sketch.* By the corollary above, $f$ and $g$ send measurable sets to measurable sets. The classical proof of Schröder and Bernstein defines $A_0 = \alpha \setminus g(\beta)$, $A_{n + 1} = g(f(A_n))$ and $A = \bigcup_n A_n$. Each $A_n$ is measurable, so $A$ is measurable. The bijection is $f$ on $A$ and $g^{-1}$ on $\alpha \setminus A$. It is measurable on each of the two measurable pieces, and so is its inverse. $\square$

This is `PolishSpace.borelSchroederBernstein`. With it the library classifies the standard Borel spaces. Every uncountable standard Borel space is isomorphic to the Cantor space, by `PolishSpace.measurableEquivNatBoolOfNotCountable`, because an uncountable Polish space contains a closed copy of the Cantor space, and a countable family of measurable sets that separates the points gives a measurable injection into the Cantor space; the theorem above then applies. So any two uncountable standard Borel spaces are isomorphic (`PolishSpace.measurableEquivOfNotCountable`). A bijection between two standard Borel spaces that is only an `Equiv` gives a measurable equivalence when the spaces are both countable or both uncountable, through `PolishSpace.Equiv.measurableEquiv`.

The module `Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal` draws the consequence that matters for probability.

**Corollary (Embedding in the line).** Every standard Borel space is isomorphic to a measurable subset of $\mathbb{R}$.

*Proof.* If $\alpha$ is uncountable, it is isomorphic to $\mathbb{R}$ itself, by the classification. If $\alpha$ is countable and infinite, its σ-algebra contains the singletons and is countably generated, so every subset is measurable. It is then isomorphic to $\mathbb{N} \subseteq \mathbb{R}$ (`MeasureTheory.measurableEquiv_range_natCast_of_infinite_of_countable`). If $\alpha$ is finite with $n$ points, it is isomorphic to $\{0, \dots, n - 1\}$. Each of these subsets of $\mathbb{R}$ is measurable. $\square$

This is `MeasureTheory.exists_subset_real_measurableEquiv`, and `MeasureTheory.exists_measurableEmbedding_real` gives a measurable embedding into $\mathbb{R}$. The function `MeasureTheory.embeddingReal Ω` is a chosen such embedding, with `MeasureTheory.measurable_embeddingReal` and `MeasureTheory.measurableEmbedding_embeddingReal`. The probability library uses it to reduce a statement about a random variable in a standard Borel space to a statement about a real random variable.

#### Other results of the module

The module `Mathlib.MeasureTheory.Constructions.Polish.Basic` also proves measurability results that need completeness of the target. In a completely metrizable second countable space, the set of points where a sequence of measurable functions converges is measurable (`MeasureTheory.measurableSet_exists_tendsto`), and so is the set where it converges to a given measurable limit (`MeasureTheory.measurableSet_tendsto_fun`). The sum of a series of measurable functions is measurable (`Measurable.tsum`, with `Measurable.tprod` for products). One result uses a measure: a measure on a standard Borel space that takes only the values $0$ and $1$ is a Dirac mass (`MeasureTheory.IsZeroOneMeasure.exists_eq_dirac`). The Dirac mass is defined in Chapter 2.

#### Common errors

1. A learner assumes a topology on a type with `StandardBorelSpace` and uses `IsOpen`. The class gives no topology. Call `upgradeStandardBorel` to fix one, and keep in mind that the open sets depend on the choice.
2. A learner applies `Continuous.measurableEmbedding` with a domain that is only second countable. The theorem needs a Polish domain: on a general domain the image of a Borel set can fail to be Borel.
3. A learner expects every analytic set to be measurable. The continuous image of a Borel set can fail to be Borel; Suslin's theorem needs the complement to be analytic too.

### Exercises

1. (A) Show that an open subset and a closed subset of a Polish space are standard Borel, with `MeasurableSet.standardBorel`.
2. (A) Show that the graph of a measurable map between standard Borel spaces is a measurable subset of the product, and deduce that the graph is standard Borel.
3. (B) Let $f : \alpha \to \beta$ be a measurable bijection between standard Borel spaces. Show that its inverse is measurable.
4. (B) Show that the image of a measurable set under a measurable map between standard Borel spaces is analytic in every Polish topology of the target.
5. (B) Show that $[0, 1]$ and $\mathbb{R}$ are isomorphic as measurable spaces, without the general classification: build two measurable injections and apply the theorem of Schröder and Bernstein.
6. (C) Show that a countably generated measurable space whose singletons are measurable embeds into the Cantor space by a measurable injection. Explain why this does not make it standard Borel.

### Reference

<?reference?>
