---
title: Local integrability and strong measurability
kind: api
modules:
  - Mathlib.MeasureTheory.Function.LocallyIntegrable
  - Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
  - Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
  - Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
  - Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
  - Mathlib.MeasureTheory.Function.AlmostCompactRange
  - Mathlib.MeasureTheory.Function.FactorsThrough
  - Mathlib.MeasureTheory.Function.Piecewise
  - Mathlib.MeasureTheory.Function.AEMeasurableSequence
  - Mathlib.MeasureTheory.Function.AEMeasurableOrder
explains:
  E2: [MeasureTheory.LocallyIntegrable, MeasureTheory.LocallyIntegrableOn, MeasureTheory.locallyIntegrable_iff, Continuous.locallyIntegrable, MeasureTheory.integrable_iff_integrableAtFilter_cocompact, MeasureTheory.StronglyMeasurable.tsum, MeasureTheory.StronglyMeasurable.limUnder, Measurable.exists_eq_measurable_comp, aeSeq]
  E1: auto
families: []
requires: [V13, V18.C01, V18.C02, V18.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Local integrability and strong measurability

### Overview

Many functions of analysis are not integrable on the whole space but are integrable on every bounded part of it. A polynomial on $\mathbb{R}$, the function $1/\sqrt{|x|}$, and every continuous function are examples. Such a function is *locally integrable*. Local integrability is the hypothesis of the Lebesgue differentiation theorem, of the theory of distributions, and of convolution with a function of compact support.

The Bochner integral of this chapter works with strongly measurable functions, the functions that are limits of simple functions. Section 1 gives the definition and the basic closure properties. Proofs need more of them: strong measurability of series, of limits, of inner products, of functions defined by cases. They also need facts that turn an almost everywhere statement into an everywhere statement on a measurable set.

This section is a guide to both families of results. It needs Sections 1 and 2 of this chapter, the measurable functions of Chapter 1, the measures of Chapter 2 and the topology of Volume 13.

### The library around it

#### Locally integrable functions

The predicate `MeasureTheory.LocallyIntegrable f μ` says that every point has a neighbourhood on which `f` is integrable. In Lean this is `∀ x, IntegrableAtFilter f (𝓝 x) μ`. The predicate `MeasureTheory.IntegrableAtFilter f l μ` says that `f` is integrable on some set of the filter `l`. The predicate `MeasureTheory.LocallyIntegrableOn f s μ` is the relative version: every point of `s` has a neighbourhood within `s` on which `f` is integrable. The measure is an `autoParam` with default `volume`, so `LocallyIntegrable f` means local integrability for Lebesgue measure.

On a locally compact space, local integrability is integrability on compact sets. This is `MeasureTheory.locallyIntegrable_iff`:
$$f \text{ locally integrable} \iff \int_K \|f\| \, d\mu < \infty \text{ for every compact } K.$$
One direction holds without local compactness: `MeasureTheory.LocallyIntegrable.integrableOn_isCompact` says that a locally integrable function is integrable on each compact set. The proof covers the compact set by finitely many neighbourhoods on which $f$ is integrable. The relative version is `MeasureTheory.locallyIntegrableOn_iff`, for a locally closed set.

On a second countable space, `MeasureTheory.LocallyIntegrable.exists_nat_integrableOn` gives a sequence of open sets that covers the space with `f` integrable on each set. The lemma `MeasureTheory.LocallyIntegrable.aestronglyMeasurable` proves that a locally integrable function is almost everywhere strongly measurable, on a second countable space.

The basic sources of locally integrable functions are:

| Lean name | Statement |
|---|---|
| `MeasureTheory.Integrable.locallyIntegrable` | an integrable function is locally integrable |
| `MeasureTheory.MemLp.locallyIntegrable` | a function in $L^p$, $1 \le p$, is locally integrable for a locally finite measure |
| `MeasureTheory.locallyIntegrable_const` | a constant is locally integrable for a locally finite measure |
| `Continuous.locallyIntegrable` | a continuous function is locally integrable for a locally finite measure |
| `Monotone.locallyIntegrable` | a monotone function on an order with the order topology is locally integrable |

The closure properties have the usual names: `MeasureTheory.LocallyIntegrable.add`, `MeasureTheory.LocallyIntegrable.sub`, `MeasureTheory.LocallyIntegrable.neg`, `MeasureTheory.LocallyIntegrable.smul`, `MeasureTheory.LocallyIntegrable.indicator`, `MeasureTheory.locallyIntegrable_finsetSum`. The lemma `MeasureTheory.LocallyIntegrable.mono` says that a function dominated by a locally integrable function is locally integrable. The predicate depends only on the class of `f`, by `MeasureTheory.locallyIntegrable_congr`.

The product of a locally integrable function and a continuous function is locally integrable. This is `MeasureTheory.LocallyIntegrable.continuous_mul` and its variants, on a locally compact Hausdorff space. If the continuous factor has compact support, the product is integrable on the whole space: `MeasureTheory.LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`. This is the fact that makes a locally integrable function a distribution.

#### Integrability on compact sets and at infinity

A continuous function is integrable on every compact set: `ContinuousOn.integrableOn_compact` for a measure that is finite on compact sets. On an order with compact closed intervals, `Continuous.integrableOn_Icc` and `ContinuousOn.integrableOn_Icc` give the case of intervals. A continuous function with compact support is integrable on the whole space, by `Continuous.integrable_of_hasCompactSupport`. Monotone functions on compact sets are integrable, by `MonotoneOn.integrableOn_isCompact`, and are in $L^p$, by `MonotoneOn.memLp_isCompact`.

Integrability on the whole space splits into a local part and a part at infinity. The lemma `MeasureTheory.integrable_iff_integrableAtFilter_cocompact` says that `f` is integrable if and only if it is integrable at the filter `cocompact` and locally integrable. On the line, `MeasureTheory.integrable_iff_integrableAtFilter_atBot_atTop` splits the part at infinity into the two ends. The lemma `MeasureTheory.integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin` treats a half line: integrability on $(a, \infty)$ is integrability near $a$ from the right, near $+\infty$, and local integrability on the half line. This is how one proves that an improper integral converges.

#### Strong measurability of limits and series

The file `Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable` proves that strong measurability passes to limits along a countably generated filter.

| Lean name | Statement |
|---|---|
| `MeasureTheory.StronglyMeasurable.limUnder` | `fun x ↦ limUnder l (f · x)` is strongly measurable, in a completely metrizable space |
| `MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto` | the set of points where the sequence converges is measurable |
| `MeasureTheory.StronglyMeasurable.tsum` | the sum of a countable series of strongly measurable functions is strongly measurable |
| `MeasureTheory.StronglyMeasurable.hasSum` | the same when the sum is given by `HasSum` at every point |
| `MeasureTheory.StronglyMeasurable.tprod` | the multiplicative version, for infinite products |

The function `limUnder` returns a junk value at points where the limit does not exist. The theorem holds because the set of these points is measurable and the junk value is a constant. The hypothesis of complete metrizability is needed for this: it makes the set of convergence a countable intersection of countable unions of measurable sets. The almost everywhere versions are `MeasureTheory.AEStronglyMeasurable.tsum` and `MeasureTheory.AEStronglyMeasurable.tprod`.

#### Other closure properties

The file `Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner` proves that the inner product of two strongly measurable functions with values in an inner product space is strongly measurable: `MeasureTheory.StronglyMeasurable.inner` and `MeasureTheory.AEStronglyMeasurable.inner`. The lemmas `MeasureTheory.AEStronglyMeasurable.re` and `MeasureTheory.AEStronglyMeasurable.im` treat the real and imaginary parts.

The file `Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas` has results that need more structure:

1. `ContinuousLinearMap.aestronglyMeasurable_comp₂` says that $x \mapsto B(f(x), g(x))$ is almost everywhere strongly measurable for a continuous bilinear map $B$.
2. `MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMap` evaluates a family of operators at a fixed vector.
3. `MeasureTheory.MeasurePreserving.aestronglyMeasurable_comp_iff` transports the property along a measure preserving embedding.
4. `aestronglyMeasurable_withDensity_iff` relates the property for `μ.withDensity f` to the property of `f • g` for `μ`.

The file `Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal` proves that a measurable function with values in $[0, \infty]$ and finite integral is finitely strongly measurable: `ENNReal.finStronglyMeasurable_of_measurable`. Its support is σ-finite.

The file `Mathlib.MeasureTheory.Function.Piecewise` treats a function defined by cases on a countable partition. For an `IndexedPartition s` with measurable pieces, `IndexedPartition.measurable_piecewise`, `IndexedPartition.stronglyMeasurable_piecewise` and `IndexedPartition.aestronglyMeasurable_piecewise` say that the function equal to $f_i$ on $s_i$ has the property if each $f_i$ has it.

#### Compact range up to a small set

The file `Mathlib.MeasureTheory.Function.AlmostCompactRange` proves a form of tightness for one function. For a finite measure and a strongly measurable map into a completely metrizable space, the lemma `MeasureTheory.StronglyMeasurable.exists_isCompact_measure_preimage_compl_le` gives for each $\varepsilon > 0$ a compact set $L$ with $\nu(g^{-1}(L)^c) < \varepsilon$. The proof applies the inner regularity of the image measure on a Polish space. The filter form `MeasureTheory.StronglyMeasurable.tendsto_measure_comap_cocompact_nhds_zero` says the same with the filter `cocompact`.

#### Factorization through a measurable map

The file `Mathlib.MeasureTheory.Function.FactorsThrough` proves the lemma of Doob and Dynkin. Let $f : X \to Y$ be measurable and give $X$ the σ-algebra `MeasurableSpace.comap f`. If $g : X \to Z$ is measurable for this σ-algebra and $Z$ is standard Borel, then $g = h \circ f$ for a measurable $h : Y \to Z$. This is `Measurable.exists_eq_measurable_comp`. The version for strongly measurable maps into a completely metrizable space is `MeasureTheory.StronglyMeasurable.exists_eq_measurable_comp`. In probability, this says that a random variable measurable for the σ-algebra of $f$ is a function of $f$. The weaker lemma `Measurable.factorsThrough` only says that $g$ is constant on the fibres of $f$.

#### Almost everywhere measurable sequences

The file `Mathlib.MeasureTheory.Function.AEMeasurableSequence` solves a recurring problem. Let $f_n$ be almost everywhere measurable functions that satisfy a property $p$ at almost every point, for example monotonicity in $n$. Each $f_n$ has a measurable version `AEMeasurable.mk`, but the versions need not satisfy $p$. The function `aeSeq hf p` is a sequence of measurable functions with three properties. Each term is measurable, by `aeSeq.measurable`. Each term is equal to $f_n$ almost everywhere, by `aeSeq.aeSeq_n_eq_fun_n_ae`. The sequence satisfies $p$ at every point of a measurable set `aeSeqSet hf p` of full measure, by `aeSeq.prop_of_mem_aeSeqSet` and `aeSeq.measure_compl_aeSeqSet_eq_zero`. Outside that set the terms are a constant. The lemmas `aeSeq.iSup` and `aeSeq.iInf` say that the suprema of the two sequences agree almost everywhere.

The file `Mathlib.MeasureTheory.Function.AEMeasurableOrder` gives a criterion for almost everywhere measurability of a function into a dense linear order. If for all $p < q$ in a countable dense set the sets $\{f < p\}$ and $\{q < f\}$ have measurable supersets whose intersection is null, then $f$ is almost everywhere measurable: `MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets`. The version for $[0, \infty]$ is `ENNReal.aemeasurable_of_exist_almost_disjoint_supersets`.

#### Common errors

1. Applying `MeasureTheory.locallyIntegrable_iff` on a space that is not locally compact. Only the direction from local integrability to integrability on compact sets holds in general.
2. Forgetting the measure in `LocallyIntegrable f`. Without a measure the predicate is for `volume`, which is wrong on a space with another measure. Write the measure when it is not Lebesgue measure.
3. Using `AEMeasurable.mk` for each term of a sequence and expecting the property of the sequence to survive. Use `aeSeq`.

### Exercises

1. (A) Show that $x \mapsto 1/\sqrt{|x|}$ is locally integrable on $\mathbb{R}$ but not integrable.
2. (A) Show that every polynomial function on $\mathbb{R}$ is locally integrable, with `Continuous.locallyIntegrable`.
3. (B) Show that if $f$ is locally integrable on $\mathbb{R}$ and $\varphi$ is continuous with compact support, then $\int f \varphi$ exists.
4. (B) Show that the pointwise limit of a sequence of strongly measurable functions with values in a Banach space is strongly measurable.
5. (B) Let $f, g : \Omega \to \mathbb{R}$ be measurable and let $g$ be measurable for the σ-algebra generated by $f$. Show that $g = h \circ f$ for a measurable $h$.
6. (C) Prove that for a finite measure on a Polish space and every $\varepsilon > 0$ there is a compact set of measure at least $\mu(X) - \varepsilon$, with the identity map and the lemmas of this section.

### Reference

<?reference?>
