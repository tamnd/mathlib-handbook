---
title: Measures on topological spaces
kind: api
modules:
  - Mathlib.MeasureTheory.Measure.OpenPos
  - Mathlib.MeasureTheory.Measure.Support
  - Mathlib.MeasureTheory.Measure.EverywherePos
  - Mathlib.MeasureTheory.Measure.Interval
  - Mathlib.MeasureTheory.Measure.Doubling
  - Mathlib.MeasureTheory.Measure.SeparableMeasure
  - Mathlib.MeasureTheory.Measure.ContinuousPreimage
  - Mathlib.MeasureTheory.Order.UpperLower
  - Mathlib.MeasureTheory.Topology
explains:
  E2: [Continuous.ae_eq_iff_eq, MeasureTheory.Measure.interior_eq_empty_of_null, MeasureTheory.Measure.support_eq_sInter, MeasureTheory.Measure.measure_compl_support, MeasureTheory.Measure.everywherePosSubset_ae_eq, MeasureTheory.Ioo_ae_eq_Icc', IsUnifLocDoublingMeasure.exists_measure_closedBall_le_mul, MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite, IsAntichain.volume_eq_zero]
  E1: auto
families: []
requires: [V13, V18.C01, V18.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Measures on topological spaces

### Overview

The Lebesgue measure has two properties that link it to the topology of $\mathbb{R}^n$. Every nonempty open set has positive measure, and every point has measure zero. Many measures of analysis share these properties, and Mathlib states them as classes and predicates that apply to any measure on a topological space. This section collects them: measures that are positive on open sets, the support of a measure, everywhere positive sets, the almost everywhere equality of intervals, doubling measures on metric spaces, and separable measures.

The section also has two results on the Lebesgue measure of $\mathbb{R}^n$ that use the order: the frontier of an upper set is a null set, and an antichain is a null set. The examples use the Lebesgue measure `MeasureTheory.MeasureSpace.volume` of Sections 1 and 2. The results on regularity of measures, inner and outer approximation by compact and open sets, are in Section 1.

### The library around it

#### Measures positive on open sets

The class `MeasureTheory.Measure.IsOpenPosMeasure μ` says that each nonempty open set has positive measure, `IsOpen.measure_pos`. The Lebesgue measure and every Haar measure are instances. Equivalent forms are `IsOpen.measure_eq_zero_iff`, which says that an open set is null only when it is empty, and `MeasureTheory.Measure.measure_pos_of_nonempty_interior`. For a metric space, balls of positive radius have positive measure, `Metric.measure_ball_pos`. On an order, `MeasureTheory.Measure.measure_Ioo_pos` gives $\mu((a, b)) > 0$ if and only if $a < b$, in a densely ordered space.

The main consequence: a null set has empty interior, `MeasureTheory.Measure.interior_eq_empty_of_null`. The interior is an open subset of a null set, so it is null and hence empty. In the same way, an almost everywhere statement holds on a dense set, `MeasureTheory.Measure.dense_of_ae`. For continuous functions this turns almost everywhere equality into equality, `Continuous.ae_eq_iff_eq`:
$$f =_{\mu\text{-a.e.}} g \iff f = g$$
for continuous $f, g$ with values in a Hausdorff space. Proof: the set $\{x \mid f(x) \neq g(x)\}$ is open because the target is Hausdorff and $f$, $g$ are continuous. It is null, so it is empty. The versions on a set, `MeasureTheory.Measure.eqOn_of_ae_eq` and `MeasureTheory.Measure.eqOn_Icc_of_ae_eq`, need the set to be in the closure of its interior. The class is stable: a nonzero scalar multiple keeps it, `MeasureTheory.Measure.isOpenPosMeasure_smul`, a larger measure keeps it, `LE.le.isOpenPosMeasure`, and so does the image under a continuous surjection, `Continuous.isOpenPosMeasure_map`. In a Hausdorff space, a σ-compact null set is meagre, `IsMeagre.of_isSigmaCompact_null`.

#### The support of a measure

The support `MeasureTheory.Measure.support μ` is the set of points $x$ such that every neighbourhood of $x$ has positive measure. The definition in Lean uses the filter of small sets of the neighbourhood filter, `MeasureTheory.Measure.mem_support_iff`. The complement of the support is the union of the open null sets, so the support is closed, `MeasureTheory.Measure.isClosed_support`, and it is the smallest closed set with a null complement, `MeasureTheory.Measure.support_eq_sInter`:
$$\operatorname{supp} \mu = \bigcap \{ t \mid t \text{ closed}, \ \mu(t^c) = 0 \}.$$
Is the complement of the support a null set? It is a union of open null sets, but the union can be uncountable. In a hereditarily Lindelöf space, for example a second countable space, a countable subfamily covers the union, and so $\mu((\operatorname{supp}\mu)^c) = 0$, `MeasureTheory.Measure.measure_compl_support`. In the language of filters, the support is in `ae μ`, `MeasureTheory.Measure.support_mem_ae`. Other versions replace the Lindelöf hypothesis by regularity of the measure, `MeasureTheory.Measure.measure_compl_support_of_regular` and `MeasureTheory.Measure.measure_compl_support_of_innerRegular`.

The support behaves well under the operations of Chapter 2. The support of a sum is the union of the supports, `MeasureTheory.Measure.support_add`. A smaller or absolutely continuous measure has a smaller support, `MeasureTheory.Measure.support_mono` and `MeasureTheory.Measure.AbsolutelyContinuous.support_mono`. A measure that is positive on open sets has the whole space as its support, `MeasureTheory.Measure.support_eq_univ`, and the zero measure has empty support, `MeasureTheory.Measure.support_zero`.

#### Everywhere positive sets

A set $s$ is everywhere positive for $\mu$ when each point of $s$ has only neighbourhoods $n$ within $s$ of positive measure. This is `MeasureTheory.Measure.IsEverywherePos μ s`; open sets are examples for an open positive measure, `IsOpen.isEverywherePos`. Every set $s$ contains a largest candidate, `MeasureTheory.Measure.everywherePosSubset μ s`, the set of points of $s$ all of whose neighbourhoods in $s$ have positive measure. For an inner regular measure and a measurable $s$, the difference is a null set, `MeasureTheory.Measure.everywherePosSubset_ae_eq`, and the candidate is everywhere positive, `MeasureTheory.Measure.isEverywherePos_everywherePosSubset`. The proof uses inner regularity: a compact subset of the removed part is covered by finitely many null neighbourhoods. These results support the uniqueness of Haar measure, where `MeasureTheory.Measure.IsEverywherePos.IsGdelta_of_isMulLeftInvariant` says that a compact closed everywhere positive set is a $G_\delta$ set.

#### Intervals up to null sets

The file `Mathlib.MeasureTheory.Measure.Interval` says that the end points of an interval do not matter when they have measure zero. For a measure with $\mu(\{a\}) = 0 = \mu(\{b\})$, `MeasureTheory.Ioo_ae_eq_Icc'` gives $(a, b) = [a, b]$ almost everywhere. The difference is a subset of $\{a, b\}$, a null set. The other pairs have names of the same form, such as `MeasureTheory.Ioc_ae_eq_Icc'` and `MeasureTheory.Iio_ae_eq_Iic'`. The prime marks the version with explicit hypotheses on the points; the version for the class `MeasureTheory.NullSingletonClass` of measures with null points has no prime. The file also gives the limits of the measures of rays and intervals: `MeasureTheory.tendsto_measure_Iic_atTop` says that $\mu((-\infty, x]) \to \mu(\alpha)$ as $x \to \infty$, by continuity from below, and `MeasureTheory.biSup_measure_Iic` is the version with a countable cofinal set.

#### Doubling measures

A measure on a metric space is uniformly locally doubling when there is a constant $C$ with
$$\mu(B(x, 2\varepsilon)) \le C \, \mu(B(x, \varepsilon))$$
for all $x$ and all small enough $\varepsilon > 0$, with closed balls. The class is `IsUnifLocDoublingMeasure`, and `IsUnifLocDoublingMeasure.exists_measure_closedBall_le_mul` gives the constant. The function `IsUnifLocDoublingMeasure.doublingConstant` chooses one. An induction on the number of doublings gives a bound for any ratio of radii, `IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul`: for $t \le K$ and small $r$, $\mu(B(x, tr)) \le C_K \, \mu(B(x, r))$, where $C_K$ is `IsUnifLocDoublingMeasure.scalingConstantOf μ K`. The Lebesgue measure and every Haar measure on a finite dimensional space are doubling. Doubling measures are the setting of the Vitali covering theorem and the Lebesgue differentiation theorem of Chapter 8.

#### Separable measures

A family $\mathcal{A}$ of measurable sets is measure dense for $\mu$, `MeasureTheory.Measure.MeasureDense μ 𝒜`, when it approximates each measurable set of finite measure: `MeasureTheory.Measure.MeasureDense.approx` gives $t \in \mathcal{A}$ with $\mu(s \mathbin{\triangle} t) < \varepsilon$. The family of all measurable sets is measure dense, `MeasureTheory.measureDense_measurableSet`. A measure is separable, the class `MeasureTheory.IsSeparable`, when a countable family is measure dense. The main source of examples: if $\mathcal{A}$ is an algebra of sets that generates the σ-algebra and $\mu$ is finite, then $\mathcal{A}$ is measure dense, `MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite`. The proof shows that the sets that can be approximated form a σ-algebra; it is the same argument as in Chapter 2, Section 5. A countable generating family generates a countable algebra, so a σ-finite measure on a countably generated space is separable, `MeasureTheory.isSeparable_of_sigmaFinite`. The use of this class is in Chapter 7: for a separable measure and a separable Banach space $E$, the space $L^p(\mu, E)$ with $1 \le p < \infty$ is second countable, `MeasureTheory.Lp.SecondCountableTopology`.

#### Preimages under continuous maps

The file `Mathlib.MeasureTheory.Measure.ContinuousPreimage` studies a family $f_z$ of continuous measure preserving maps that depends continuously on a parameter $z$. For a set $t$ of finite measure, the set of parameters $z$ with $f_z^{-1}(t) = s$ almost everywhere is closed, `MeasureTheory.isClosed_setOfPred_preimage_ae_eq`. The analytic content is `MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero`: if $f_a \to g$ in the compact open topology, then $\mu(f_a^{-1}(s) \mathbin{\triangle} g^{-1}(s)) \to 0$. The proof approximates $s$ from inside by a compact set and from outside by an open set. Dynamics and ergodic theory, Volume 21, use these results.

#### Order and the Lebesgue measure

The file `Mathlib.MeasureTheory.Order.UpperLower` is about the Lebesgue measure on $\mathbb{R}^\iota$ for a finite type $\iota$, with the coordinatewise order. The frontier of an upper set or a lower set is a null set, `IsUpperSet.null_frontier` and `IsLowerSet.null_frontier`. The idea: near a point of the frontier, a small cube in the direction of increase lies inside the set, and a small cube in the other direction lies outside, so the frontier has density less than $1$ at each of its points; by the Lebesgue density theorem it is null. It follows that an order connected set is null measurable, `Set.OrdConnected.nullMeasurableSet`, and an antichain is a null set, `IsAntichain.volume_eq_zero`. For the last result, an antichain is order connected and has empty interior, so it lies in its own frontier. The file `Mathlib.MeasureTheory.Topology` has one lemma, `ae_restrict_le_codiscreteWithin`: for a second countable space and a measure with no point masses, a set whose complement in $U$ is discrete is almost all of $U$.

#### Common errors

1. Assuming $\mu((\operatorname{supp}\mu)^c) = 0$ for every measure. This needs a hereditarily Lindelöf space or a regular measure; the lemma `MeasureTheory.Measure.measure_compl_support` has the class `HereditarilyLindelofSpace` as a hypothesis.
2. Using `Continuous.ae_eq_iff_eq` for a measure that is not positive on open sets. For the Dirac measure at $0$ on $\mathbb{R}$, any two continuous functions with the same value at $0$ are equal almost everywhere.
3. Mixing the primed and the unprimed interval lemmas. `MeasureTheory.Ioo_ae_eq_Icc'` needs the two hypotheses $\mu(\{a\}) = 0$ and $\mu(\{b\}) = 0$; the unprimed version needs the class `MeasureTheory.NullSingletonClass`.

### Exercises

1. (A) Compute the support of $\delta_0 + \lambda|_{[1, 2]}$ on $\mathbb{R}$, where $\lambda$ is the Lebesgue measure.
2. (A) Let $\mu$ be positive on open sets. Show that a closed set of full measure is the whole space.
3. (B) Give a measure on an uncountable discrete space for which the complement of the support is not a null set.
4. (B) Show that the Lebesgue measure on $\mathbb{R}$ is doubling with constant $2$, and that the measure $e^{x^2} \, dx$ is not uniformly locally doubling.
5. (B) Prove that an antichain in $\mathbb{R}^2$ for the coordinatewise order is the graph of a decreasing function on a subset of $\mathbb{R}$, and deduce `IsAntichain.volume_eq_zero` in dimension $2$.
6. (C) Prove `MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite` from the approximation result of Chapter 2, Section 5.

### Reference

<?reference?>
