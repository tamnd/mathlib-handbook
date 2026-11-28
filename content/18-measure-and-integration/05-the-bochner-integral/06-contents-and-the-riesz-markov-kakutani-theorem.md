---
title: Contents and the Riesz-Markov-Kakutani theorem
kind: api
modules:
  - Mathlib.MeasureTheory.Measure.Content
  - Mathlib.MeasureTheory.Measure.RegularityCompacts
  - Mathlib.MeasureTheory.Integral.Regular
  - Mathlib.MeasureTheory.Integral.CompactlySupported
  - Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
  - Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
  - Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
explains:
  E2: [MeasureTheory.Content.measure_eq_content_of_regular, MeasureTheory.Content.outerMeasure_opens, MeasureTheory.Content.borel_le_caratheodory, MeasureTheory.innerRegular_isCompact_isClosed_measurableSet_of_finite, IsOpen.measure_eq_biSup_integral_continuous, IsCompact.measure_eq_biInf_integral_hasCompactSupport, NNRealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure, RealRMK.rieszMeasure_integralPositiveLinearMap, MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported]
  E1: auto
families: []
requires: [V13, V16, V18.C02, V18.C03, V18.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Contents and the Riesz-Markov-Kakutani theorem

### Overview

A measure on a locally compact Hausdorff space gives a linear functional on the continuous functions with compact support: $f \mapsto \int f \, d\mu$. This functional is positive, because the integral of a nonnegative function is nonnegative. The Riesz-Markov-Kakutani theorem gives the converse. Every positive linear functional $\Lambda$ on the compactly supported continuous functions is the integral against exactly one regular measure $\mu$:

$$\Lambda(f) = \int_X f \, d\mu.$$

This section explains how Mathlib proves the theorem. The first tool is a content: a function on compact sets that is monotone, additive on disjoint compact sets and subadditive. Mathlib extends each content to a Borel measure, and the Haar measure of Chapter 3, Section 2 also uses this extension. The second tool is the description of the measure of open and compact sets by integrals of continuous functions. The theorem itself comes in two versions, one for functionals with values in `NNReal` and one for real positive linear maps. The section also has the inner regularity results for finite measures on Polish spaces. The integral is the Bochner integral of Section 2.

### The library around it

#### Contents

The structure `MeasureTheory.Content G` on a topological space $G$ has a function from `TopologicalSpace.Compacts G` to `NNReal` with three properties. It is monotone, `MeasureTheory.Content.mono`. It is additive on disjoint compact sets, `MeasureTheory.Content.sup_disjoint`, under the hypothesis that the two sets are closed. It is subadditive, `MeasureTheory.Content.sup_le`. The value on the empty set is $0$, `MeasureTheory.Content.empty`. The constructor is `MeasureTheory.Content.mk`. A content is finite on each compact set, since its values are in `NNReal`.

The extension goes in three steps. The inner content of an open set $U$ is the supremum of $\lambda(K)$ over the compact sets $K \subseteq U$, `MeasureTheory.Content.innerContent`. It is countably subadditive on open sets, `MeasureTheory.Content.innerContent_iSup_nat`, in an `R1Space`. The outer measure `MeasureTheory.Content.outerMeasure` is the outer measure induced by the inner content: the value on a set $A$ is the infimum of the inner content of the open sets that contain $A$, `MeasureTheory.Content.outerMeasure_eq_iInf`. On open sets the two agree, `MeasureTheory.Content.outerMeasure_opens`. The theorem of Carathéodory then gives a measure. The key fact is `MeasureTheory.Content.borel_le_caratheodory`: every Borel set is Carathéodory measurable for this outer measure. The measure `MeasureTheory.Content.measure` is the restriction of the outer measure to the Borel sets, and `MeasureTheory.Content.measure_apply` says that it agrees with the outer measure on measurable sets.

The measure need not agree with the content on compact sets. It gives to a compact set $K$ a value at least $\lambda(K)$, because each open set that contains $K$ has inner content at least $\lambda(K)$, `MeasureTheory.Content.le_innerContent`. A content is regular, `MeasureTheory.Content.ContentRegular`, when $\lambda(K)$ is the infimum of $\lambda(L)$ over the compact sets $L$ whose interior contains $K$, for every compact $K$. For a regular content, the measure extends it: `MeasureTheory.Content.measure_eq_content_of_regular` gives $\mu(K) = \lambda(K)$. The Haar measure `MeasureTheory.Measure.haar` comes from the content `MeasureTheory.Measure.haar.haarContent`, and the lemma `MeasureTheory.Content.is_mul_left_invariant_innerContent` transfers left invariance from the content to the inner content.

#### Regularity on Polish spaces

The file `Mathlib.MeasureTheory.Measure.RegularityCompacts` proves that a finite measure on a Polish space is inner regular for compact sets. The hypotheses are `SecondCountableTopology` and `TopologicalSpace.IsCompletelyPseudoMetrizableSpace`. The first step is tightness: for each $\varepsilon > 0$ some set $K$ with compact closure has $\mu(K^c) < \varepsilon$, `MeasureTheory.exists_isCompact_closure_measure_compl_lt`. The proof takes a dense sequence, covers the space by finitely many balls of radius $1/n$ with large measure for each $n$, and takes the intersection over $n$. This set is totally bounded, so its closure is compact by completeness.

From tightness, `MeasureTheory.innerRegularWRT_isCompact_isClosed` approximates closed sets from inside by compact closed sets, and `MeasureTheory.innerRegular_isCompact_isClosed_measurableSet_of_finite` does the same for all measurable sets. The statements use the predicate `MeasureTheory.Measure.InnerRegularWRT`. The file also gives instances, so that a finite measure on a Polish space is `MeasureTheory.Measure.InnerRegular` without a proof by the user.

#### Measures of open and compact sets by integrals

The file `Mathlib.MeasureTheory.Integral.Regular` writes the measure of open and compact sets with continuous functions. For a finite measure $\mu$ that is inner regular for compact sets on a normal Hausdorff space, `IsOpen.measure_eq_biSup_integral_continuous` gives

$$\mu(U) = \sup \left\{ \int f \, d\mu : f \text{ continuous}, \ 0 \le f \le 1, \ f = 0 \text{ outside } U \right\}.$$

For a compact set $k$ in a locally compact regular space, `IsCompact.measure_eq_biInf_integral_hasCompactSupport` gives $\mu(k)$ as the infimum of $\int f \, d\mu$ over the nonnegative continuous functions $f$ with compact support and $f = 1$ on $k$. Both proofs use the lemma of Urysohn to make functions between a compact set and an open set. Both formulas use `ENNReal.ofReal` of the real integral, because the measure takes values in `ENNReal`.

#### The integral as a linear map

The file `Mathlib.MeasureTheory.Integral.CompactlySupported` turns the integral into a map on the type `CompactlySupportedContinuousMap X E` of continuous functions with compact support. Such a function is integrable for each measure that is finite on compact sets, `CompactlySupportedContinuousMap.integrable`. The map `CompactlySupportedContinuousMap.integralLinearMap μ` is the integral as an `NNReal` linear map on functions with values in `NNReal`. The map `CompactlySupportedContinuousMap.integralPositiveLinearMap μ` is the integral as a real positive linear map, a term of `PositiveLinearMap`. The notation for this type is `→ₚ[ℝ]`.

#### The theorem for functions with values in NNReal

Let $X$ be a locally compact Hausdorff space and $\Lambda$ an `NNReal` linear map on `CompactlySupportedContinuousMap X NNReal`. Linearity over `NNReal` gives positivity at once. The content `rieszContent Λ` gives to a compact set $K$ the infimum of $\Lambda(f)$ over the functions $f \ge 1$ on $K$; the auxiliary function is `rieszContentAux` and its bound is `rieszContentAux_le`. The content is regular, `contentRegular_rieszContent`. The measure `NNRealRMK.rieszMeasure Λ` is the measure of this content on the Borel sets.

The main theorem is `NNRealRMK.integral_rieszMeasure`: for each $f$,

$$\int_X f \, d\mu_\Lambda = \Lambda(f).$$

A version for the lower Lebesgue integral of Chapter 4 is `NNRealRMK.lintegral_rieszMeasure`. The measure is regular, by the instance `NNRealRMK.rieszMeasure_regular`. Uniqueness has two forms: `NNRealRMK.rieszMeasure_integralLinearMap` gives back a regular measure from its integral map, and `NNRealRMK.integralLinearMap_inj` says that two regular measures with the same integral map are equal.

The proof of the formula compares both sides on a partition of the range of $f$. Cut $[0, \|f\|]$ into intervals of length $\varepsilon$, and cut $f$ into pieces with a partition of unity subordinate to the open sets where $f$ is in each interval. On each piece, the measure and $\Lambda$ are both close to the length of the interval times the measure of a set. The error is a constant times $\varepsilon$.

#### The theorem for real positive linear maps

For real functions the hypothesis of positivity is explicit. Let $\Lambda$ be a term of `CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ`. The measure `RealRMK.rieszMeasure Λ` is built from the restriction of $\Lambda$ to nonnegative functions, and `RealRMK.integral_rieszMeasure` gives $\int f \, d\mu_\Lambda = \Lambda(f)$ for each real $f$. The measure is regular, `RealRMK.regular_rieszMeasure`. The two directions of the bijection are `RealRMK.integralPositiveLinearMap_rieszMeasure` and `RealRMK.rieszMeasure_integralPositiveLinearMap`.

Uniqueness gives a useful test for the equality of two measures. `MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported` says: two regular measures that have the same integral on each real continuous function with compact support are equal. The `NNReal` form is `MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported_nnreal`. The lemma `RealRMK.measure_le_of_isCompact_of_integral` is an order version: if $\int f \, d\mu \le \int f \, d\nu$ for all $f$, then $\mu(K) \le \nu(K)$ for each compact $K$, when $\nu$ is outer regular.

The file also replaces a finite measure by a regular one with the same integrals. On a compact Hausdorff space, `MeasureTheory.Measure.exists_regular_eq_of_compactSpace` gives a regular finite measure $\nu$ with $\int g \, d\mu = \int g \, d\nu$ for every bounded continuous $g$. The lemma `MeasureTheory.Measure.exists_innerRegular_eq_of_isCompact` does the same for a measure that lives on a compact set.

#### Common errors

1. Expecting `MeasureTheory.Content.measure` to agree with the content on compact sets. This holds only for a regular content, by `MeasureTheory.Content.measure_eq_content_of_regular`. Without regularity, the measure of $K$ can be larger than $\lambda(K)$.
2. Applying the uniqueness results to measures that are not regular. `MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported` needs the class `MeasureTheory.Measure.Regular` for both measures. On a second countable locally compact space every measure that is finite on compact sets is regular, but in general this is a hypothesis to supply.
3. Passing a real linear map that is not marked as positive. `RealRMK.rieszMeasure` takes a `PositiveLinearMap`, so the proof of positivity is part of the term. A linear map of type `→ₗ[ℝ]` does not fit.

### Exercises

1. (A) Let $\lambda(K)$ be the number of points of a compact set $K \subseteq \mathbb{Z}$ with the discrete topology. Show that $\lambda$ is a content and that its measure is the counting measure.
2. (A) Let $\Lambda(f) = f(0)$ on the compactly supported continuous functions on $\mathbb{R}$. Show that $\Lambda$ is positive and find the measure `RealRMK.rieszMeasure Λ`.
3. (B) Use `IsCompact.measure_eq_biInf_integral_hasCompactSupport` to show that two finite measures on $\mathbb{R}$ that are inner regular and have the same integrals on compactly supported continuous functions agree on compact sets.
4. (B) Let $\lambda(K) = 1$ when $0 \in K$ and $\lambda(K) = 0$ otherwise, for compact $K \subseteq \mathbb{R}$. Show that $\lambda$ is a regular content and that its measure is the Dirac measure at $0$.
5. (B) Prove the tightness step of `MeasureTheory.exists_isCompact_closure_measure_compl_lt` for the space $\mathbb{N}^{\mathbb{N}}$ with the product topology.
6. (C) Prove `NNRealRMK.integral_rieszMeasure` for a space $X$ that is a finite discrete set, and explain which steps of the general proof become trivial.

### Reference

<?reference?>
