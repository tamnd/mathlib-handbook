---
title: The variation of a vector measure
kind: api
modules:
  - Mathlib.MeasureTheory.Measure.PreVariation
  - Mathlib.MeasureTheory.VectorMeasure.Variation.Defs
  - Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
  - Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
  - Mathlib.MeasureTheory.VectorMeasure.Variation.Semivariation
  - Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
explains:
  E2: [MeasureTheory.preVariation, MeasureTheory.IsSigmaSubadditiveSetFun, MeasureTheory.VectorMeasure.variation, MeasureTheory.VectorMeasure.norm_measure_le_variation, MeasureTheory.VectorMeasure.variation_le_of_forall_eNorm_le, MeasureTheory.SignedMeasure.totalVariation_eq_variation, MeasureTheory.VectorMeasure.semivariation, MeasureTheory.VectorMeasure.norm_apply_le_bound, BoundedVariationOn.vectorMeasure, BoundedVariationOn.vectorMeasure_Ioc]
  E1: auto
families: []
requires: [V13, V15, V16, V18.C02, V18.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The variation of a vector measure

### Overview

The size of a vector measure $\mu$ on a set $A$ is not $\|\mu(A)\|$: the values on the parts of $A$ can cancel. The variation of $\mu$ measures the total mass without cancellation:

$$|\mu|(A) = \sup \sum_k \|\mu(A_k)\|,$$

where the supremum is over the finite partitions of $A$ into measurable sets. The variation is a measure, the smallest measure that dominates $\|\mu\|$ on every set. For a signed measure it is the total variation $s^+ + s^-$ of Section 2. For a vector measure with values in an infinite dimensional Banach space, the variation can be infinite even though all values $\mu(A)$ are bounded. In finite dimension this does not occur: each coordinate of $\mu$ is a signed measure with finite total variation, and all norms on the space are equivalent.

This section describes the general construction of a measure from a subadditive set function, the variation and its rules, the semivariation that gives a uniform bound on the values of $\mu$, and the vector measure $df$ of a function $f$ of bounded variation on the real line. Section 4 uses the variation to define the integral against a vector measure.

### The library around it

#### Measures from subadditive set functions

The file `Mathlib.MeasureTheory.Measure.PreVariation` has a construction that does not use vector measures. The predicate `MeasureTheory.IsSigmaSubadditiveSetFun f` says that a function $f$ from sets to $[0, \infty]$ satisfies $f(\bigcup_i A_i) \le \sum_i f(A_i)$ for every sequence of disjoint measurable sets. For such an $f$ with $f(\emptyset) = 0$, the function `MeasureTheory.preVariationFun f` is

$$A \mapsto \sup_{(A_k)} \sum_k f(A_k)$$

over the finite measurable partitions of $A$, and `MeasureTheory.preVariation f` is the measure that it defines. Its value on a measurable set is the supremum, `MeasureTheory.preVariation_apply`. The countable additivity is the main step: `MeasureTheory.preVariation.iUnion` proves it by combining finite partitions of the pieces. The partitions are of type `Finpartition`, and `Finpartition.toMeasurableSet` restricts them to measurable sets.

#### The variation

The variation `MeasureTheory.VectorMeasure.variation μ` is `MeasureTheory.preVariation` of $A \mapsto \|\mu(A)\|_e$, `MeasureTheory.VectorMeasure.variation_apply`. The extended norm is subadditive because $\mu$ is countably additive, `MeasureTheory.VectorMeasure.isSigmaSubadditiveSetFun_eNorm`. The definition works for values in any normed additive monoid with an extended norm, which includes $[0, \infty]$. For a measure seen as a vector measure, the variation is the measure itself, `MeasureTheory.VectorMeasure.variation_eq_ennrealToMeasure`. The variant `MeasureTheory.VectorMeasure.ennrealVariation` is the same measure as a vector measure with values in $[0, \infty]$, and $\mu$ is absolutely continuous with respect to it, `MeasureTheory.VectorMeasure.absolutelyContinuous`.

The basic bound is $\|\mu(A)\| \le |\mu|(A)$. With extended norms it is `MeasureTheory.VectorMeasure.eNorm_measure_le_variation`, and with real norms it is `MeasureTheory.VectorMeasure.norm_measure_le_variation`, which needs $|\mu|(A) < \infty$. The variation is the smallest measure with this property: if $\|\mu(A)\|_e \le m(A)$ for every measurable $A$, then $|\mu| \le m$, `MeasureTheory.VectorMeasure.variation_le_of_forall_eNorm_le`.

The variation is subadditive, $|\mu + \nu| \le |\mu| + |\nu|$, `MeasureTheory.VectorMeasure.variation_add_le`, and it does not change under negation, `MeasureTheory.VectorMeasure.variation_neg`. It commutes with restriction, `MeasureTheory.VectorMeasure.variation_restrict`, and for a point mass it is $\|v\| \, \delta_x$, `MeasureTheory.VectorMeasure.variation_dirac`. A scalar multiple has the variation $|c\mu| = \|c\| \, |\mu|$, `MeasureTheory.VectorMeasure.variation_smul`, and $|\mu| = 0$ only for $\mu = 0$, `MeasureTheory.VectorMeasure.variation_eq_zero`. The image under a measurable map $\varphi$ has a smaller variation, $|\varphi_* \mu| \le \varphi_* |\mu|$, `MeasureTheory.VectorMeasure.variation_map_le`, since the sets $\varphi^{-1}(B_k)$ form only some of the partitions of the space. For a measurable embedding the two are equal, `MeasurableEmbedding.variation_map`. To approach the variation from below, `MeasureTheory.VectorMeasure.exists_lt_sum_of_lt_variation` gives a finite partition with a sum larger than any number below $|\mu|(A)$.

#### Signed measures

For a signed measure, the file `Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure` proves that the variation is the total variation of the Jordan decomposition, `MeasureTheory.SignedMeasure.totalVariation_eq_variation`. The two definitions are different: one is a supremum over partitions, the other is $s^+ + s^-$. The Hahn set $P$ gives the partition $\{A \cap P, A \setminus P\}$ that attains the supremum. For a finite measure $\mu$, the variation of `μ.toSignedMeasure` is $\mu$, `MeasureTheory.Measure.variation_toSignedMeasure`.

#### The semivariation and the bound

For a vector measure $\mu$ with values in a real normed space $E$, the semivariation is

$$\|\mu\|(A) = \sup_{\|\ell\| \le 1} |\ell \circ \mu|(A),$$

the supremum over the continuous linear forms of norm at most $1$ of the variation of the signed measure $\ell \circ \mu$. This is `MeasureTheory.VectorMeasure.semivariation`. It is between the norm and the variation:

$$\|\mu(A)\| \le \|\mu\|(A) \le |\mu|(A),$$

`MeasureTheory.VectorMeasure.eNorm_apply_le_semivariation` and `MeasureTheory.VectorMeasure.semivariation_le_variation`. Unlike the variation, the semivariation is always finite. The reason is the property of signed measures in Section 2: the variation of a signed measure on $A$ is at most twice the largest value $|s(B)|$ for $B \subseteq A$. The semivariation inherits this: `MeasureTheory.VectorMeasure.exists_subset_lt_eNorm_apply_of_lt_semivariation` gives $B \subseteq A$ with $\|\mu\|(A) \le 2 \|\mu(B)\|$ up to a small error. The number `MeasureTheory.VectorMeasure.bound μ` is the semivariation of the whole space, and `MeasureTheory.VectorMeasure.norm_apply_le_bound` gives $\|\mu(A)\| \le$ this bound for every $A$. So every vector measure is bounded.

#### The vector measure of a function of bounded variation

A function $f : \mathbb{R} \to E$ of bounded variation, with $E$ complete, defines a vector measure $df$ that generalizes the Stieltjes measures of Chapter 3. The construction `BoundedVariationOn.vectorMeasure` works on a dense linear order with compact intervals and a second countable order topology, for example $\mathbb{R}$. The value on a half open interval is the difference of right limits, `BoundedVariationOn.vectorMeasure_Ioc`:

$$df((a, b]) = f(b^+) - f(a^+).$$

The values on the other kinds of intervals and on points are `BoundedVariationOn.vectorMeasure_Icc`, `BoundedVariationOn.vectorMeasure_Ioo` and `BoundedVariationOn.vectorMeasure_singleton`. The construction is an application of the extension theorem of Section 1: the additive content on the intervals $(a, b]$ is dominated by the Stieltjes measure of the variation of $f$. The variation of $df$ is finite, and it is at most the variation of $f$, `BoundedVariationOn.variation_vectorMeasure_univ_le`.

#### Common errors

1. Expecting the variation of a vector measure to be finite. The variation is a measure that can take the value $\infty$ when $E$ has infinite dimension; `MeasureTheory.VectorMeasure.norm_measure_le_variation` has the hypothesis that it is finite. The semivariation and `MeasureTheory.VectorMeasure.bound` are always finite.
2. Using countable partitions in the definition. The supremum in `MeasureTheory.preVariationFun` is over finite partitions. With countable partitions the value is the same for a countably additive $\mu$, but the library states the results for finite ones.
3. Taking $df([a, b]) = f(b) - f(a)$. For a function with jumps, the value depends on the type of interval and on the left and right limits; it is $f(b^+) - f(a^-)$ for a closed interval.

### Exercises

1. (A) Compute the variation of $\mu = \delta_0 - 2 \delta_1 + i \delta_2$, a complex measure, on the set $\{0, 1, 2\}$, with `MeasureTheory.VectorMeasure.variation_dirac`.
2. (A) Let $f$ be the indicator of $[0, \infty)$ on $\mathbb{R}$. Compute $df$ on $(-1, 1]$ and on $\{0\}$.
3. (B) Prove $\|\mu(A)\| \le |\mu|(A)$ directly from the definition of the variation as a supremum.
4. (B) For a signed measure $s$, prove that $|s|(A) \le 2 \sup_{B \subseteq A} |s(B)|$.
5. (B) Let $f : [0, 1] \to E$ be Lipschitz with constant $L$. Show that the variation of $df$ is at most $L$ times Lebesgue measure.
6. (C) Let $r_n$ be the Rademacher functions on $[0, 1]$, with $r_n = \pm 1$ on the dyadic intervals of length $2^{-n}$, and let $\mu(A) = \sum_n (\int_A r_n \, d\lambda) \, e_n$ in $\ell^2$. Show that $\mu$ is a vector measure and that its variation on $[0, 1]$ is infinite. Compute a bound for its semivariation.

### Reference

<?reference?>
