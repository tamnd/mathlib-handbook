---
title: Vector measures and signed measures
kind: api
modules:
  - Mathlib.MeasureTheory.VectorMeasure.Defs
  - Mathlib.MeasureTheory.VectorMeasure.Basic
  - Mathlib.MeasureTheory.VectorMeasure.Operations
  - Mathlib.MeasureTheory.VectorMeasure.Order
  - Mathlib.MeasureTheory.VectorMeasure.Relations
  - Mathlib.MeasureTheory.VectorMeasure.AddContent
  - Mathlib.MeasureTheory.VectorMeasure.WithDensity
  - Mathlib.MeasureTheory.Measure.Complex
explains:
  E2: [MeasureTheory.VectorMeasure, MeasureTheory.SignedMeasure, MeasureTheory.VectorMeasure.hasSum_of_disjoint_iUnion, MeasureTheory.Measure.toSignedMeasure, MeasureTheory.VectorMeasure.equivMeasure, MeasureTheory.VectorMeasure.restrict, MeasureTheory.VectorMeasure.AbsolutelyContinuous, MeasureTheory.VectorMeasure.MutuallySingular, MeasureTheory.VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure, MeasureTheory.Measure.withDensityᵥ]
  E1: auto
families: []
requires: [V13, V16, V18.C01, V18.C02, V18.C04, V18.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Vector measures and signed measures

### Overview

A measure takes values in $[0, \infty]$. Many set functions of analysis are countably additive but take values that can be negative or complex: the difference $\mu - \nu$ of two finite measures, the function $A \mapsto \int_A f \, d\mu$ for an integrable real $f$, or a charge distribution in physics. A vector measure is a countably additive function from the measurable sets to a topological additive monoid $M$. With $M = \mathbb{R}$ it is a signed measure, with $M = \mathbb{C}$ a complex measure, and with $M = [0, \infty]$ it is a measure again.

This section gives the definition, the operations, the order on signed measures, the relations of absolute continuity and singularity, and the two main ways to build vector measures: from an additive content dominated by a measure, and from a density $f$ by $A \mapsto \int_A f \, d\mu$. Section 2 decomposes signed measures, Section 3 defines the variation, and Section 4 integrates against a vector measure.

### The library around it

#### The definition

The structure `MeasureTheory.VectorMeasure α M` needs an additive commutative monoid $M$ with a topology. A vector measure $v$ has a function on sets with three properties: $v(\emptyset) = 0$, $v(A) = 0$ for a set $A$ that is not measurable, and for every sequence of pairwise disjoint measurable sets $A_i$,

$$\sum_i v(A_i) = v\Big(\bigcup_i A_i\Big),$$

where the sum is the unconditional sum `HasSum`. The theorem `MeasureTheory.VectorMeasure.hasSum_of_disjoint_iUnion` gives this for any countable index type, and `MeasureTheory.VectorMeasure.of_disjoint_iUnion` gives the same statement with `tsum` when $M$ is Hausdorff. Unconditional convergence is a strong condition: in $\mathbb{R}$, it is absolute convergence. A vector measure is defined on all sets, like a measure in Mathlib, but it is $0$ outside the measurable sets. It does not come from an outer measure.

The abbreviations `MeasureTheory.SignedMeasure α` and `MeasureTheory.ComplexMeasure α` stand for vector measures with values in $\mathbb{R}$ and in $\mathbb{C}$. A signed measure is always finite: its values are real numbers. The finite additivity rules are `MeasureTheory.VectorMeasure.of_union`, `MeasureTheory.VectorMeasure.of_sdiff` and `MeasureTheory.VectorMeasure.of_compl`. Continuity along a monotone sequence of sets is `MeasureTheory.VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat`.

#### Measures as vector measures

A measure is a vector measure with values in $[0, \infty]$, and the equivalence `MeasureTheory.VectorMeasure.equivMeasure` identifies the two types. The map `MeasureTheory.Measure.toENNRealVectorMeasure` is one direction. A finite measure $\mu$ gives a signed measure `μ.toSignedMeasure` with values $\mu(A)$ as real numbers, `MeasureTheory.Measure.toSignedMeasure_apply_measurable`. This map is additive, and the difference of two finite measures is the first example of a signed measure: `MeasureTheory.Measure.toSignedMeasure_sub_apply` computes $(\mu - \nu)(A) = \mu(A) - \nu(A)$. Note that this subtraction is in signed measures; the subtraction of Chapter 2 in the type of measures is truncated and gives a different result.

A complex measure is a pair of signed measures, its real and imaginary parts, `MeasureTheory.ComplexMeasure.re` and `MeasureTheory.ComplexMeasure.im`. The equivalence is `MeasureTheory.ComplexMeasure.equivSignedMeasure`, and the inverse map is `MeasureTheory.SignedMeasure.toComplexMeasure`.

#### Operations

The vector measures with values in $M$ form an additive monoid, a group when $M$ is a topological group, and a module over a ring that acts continuously on $M$. The operations are pointwise, `add_apply` and `smul_apply`. The point mass `MeasureTheory.VectorMeasure.dirac x m` has the value $m$ on the measurable sets that contain $x$.

The restriction `MeasureTheory.VectorMeasure.restrict v A` has the value $v(B \cap A)$ on a measurable $B$, `MeasureTheory.VectorMeasure.restrict_apply`, when $A$ is measurable; it is $0$ when $A$ is not measurable. The image `MeasureTheory.VectorMeasure.map v f` under a measurable $f$ has the value $v(f^{-1}(B))$, and it is $0$ when $f$ is not measurable. A continuous additive map $M \to N$ turns a vector measure with values in $M$ into one with values in $N$, `MeasureTheory.VectorMeasure.mapRange`; the linear version is `MeasureTheory.VectorMeasure.mapRangeL`. The restriction to a smaller sigma algebra is `MeasureTheory.VectorMeasure.trim`.

#### The order

When $M$ has a partial order, vector measures are ordered by $v \le w$ if $v(A) \le w(A)$ for every measurable $A$, `MeasureTheory.VectorMeasure.le_iff`. The notation `v ≤[A] w` means `v.restrict A ≤ w.restrict A`: the inequality holds on all measurable subsets of $A$. A set $A$ is positive for a signed measure $s$ if `0 ≤[A] s`, and negative if `s ≤[A] 0`. On a positive set, $s$ restricts to a measure, `MeasureTheory.SignedMeasure.toMeasureOfZeroLE`, and on a negative set, $-s$ does, `MeasureTheory.SignedMeasure.toMeasureOfLEZero`. These are the parts of the Jordan decomposition of Section 2.

#### Absolute continuity and singularity

For vector measures $v$ and $w$ with values in different monoids, `MeasureTheory.VectorMeasure.AbsolutelyContinuous v w`, with notation `v ≪ᵥ w`, means that $w(A) = 0$ implies $v(A) = 0$ for every measurable $A$. The relation `MeasureTheory.VectorMeasure.MutuallySingular v w`, with notation `v ⟂ᵥ w`, means that there is a measurable $S$ such that $v$ is $0$ on the subsets of $S$ and $w$ is $0$ on the subsets of the complement. To compare a signed measure with a measure $\mu$, apply these to `μ.toENNRealVectorMeasure`.

The definition of absolute continuity uses only the zero sets of $w$, not those of its variation. For a signed measure $w$, a set with $w(A) = 0$ can contain parts of positive and negative mass that cancel. The usual relation uses the zero sets of the variation $|w|$, and the two differ: for $w = \delta_0 - \delta_1$ and $A = \{0, 1\}$, $w(A) = 0$ but $\delta_0(A) = 1$. In practice $w$ is a measure, and the difference does not occur.

#### Extension from an additive content

The file `Mathlib.MeasureTheory.VectorMeasure.AddContent` builds vector measures from finitely additive functions. The construction `MeasureTheory.VectorMeasure.of_additive_of_le_measure` takes a finitely additive $m$ with values in a normed group and a finite measure $\mu$ with $\|m(A)\| \le \mu(A)$, and returns a vector measure. The bound by $\mu$ gives the countable additivity: the tails of a disjoint union have small $\mu$ measure. The theorem `MeasureTheory.VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure` extends an additive content on a semiring of sets $C$, bounded by $\mu$ on $C$, to a vector measure bounded by $\mu$ on all sets, when $E$ is a Banach space. This is the vector form of the Carathéodory extension of Chapter 2.

#### Densities

For an integrable $f : X \to E$, `μ.withDensityᵥ f` is the vector measure

$$A \mapsto \int_A f \, d\mu,$$

`MeasureTheory.withDensityᵥ_apply`. It is $0$ when $f$ is not integrable. The map $f \mapsto \mu.\text{withDensityᵥ}\, f$ is linear, and it is injective up to equality almost everywhere, `MeasureTheory.Integrable.ae_eq_of_withDensityᵥ_eq`. The measure is absolutely continuous with respect to $\mu$, `MeasureTheory.Measure.withDensityᵥ_absolutelyContinuous`. For a real $f$, it is the difference of the two measures with densities $f^+$ and $f^-$, `MeasureTheory.withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part`. The theorem of Radon and Nikodym of Section 2 says that every signed measure absolutely continuous with respect to a sigma finite $\mu$ is of this form.

#### Common errors

1. Subtracting measures in the wrong type. For measures $\mu$ and $\nu$, `μ - ν` is a measure and is truncated at $0$. To get the signed difference, write `μ.toSignedMeasure - ν.toSignedMeasure`, which needs both measures to be finite.
2. Forgetting that `MeasureTheory.Measure.withDensityᵥ` is $0$ for a function that is not integrable. A theorem about `μ.withDensityᵥ f` usually has the hypothesis `MeasureTheory.Integrable f μ`.
3. Reading `v ≤[A] w` as $v(A) \le w(A)$. It is the inequality on every measurable subset of $A$, a much stronger condition.

### Exercises

1. (A) Let $\mu$ be Lebesgue measure on $[0, 1]$ and $\nu = \delta_0$. Compute `(μ.toSignedMeasure - ν.toSignedMeasure)` on $[0, 1/2]$ and on $(0, 1]$, and give a positive set and a negative set for it.
2. (A) Show from `MeasureTheory.withDensityᵥ_apply` that the signed measure with density $f(x) = x - 1/2$ on $[0, 1]$ has the value $0$ on $[0, 1]$, and find its largest value on a subinterval.
3. (B) Show that a vector measure with values in $\mathbb{R}$ cannot have $v(\{n\}) = (-1)^n / n$ for all $n \ge 1$ on $\mathbb{N}$ with the power set as sigma algebra. Use `MeasureTheory.VectorMeasure.hasSum_of_disjoint_iUnion`.
4. (B) Show that `v ≪ᵥ μ.toENNRealVectorMeasure` and `v ⟂ᵥ μ.toENNRealVectorMeasure` together give $v = 0$.
5. (B) Let $m$ be the finitely additive function on the intervals $[a, b) \subseteq [0, 1)$ with $m([a, b)) = g(b) - g(a)$ for a Lipschitz $g$. Use `MeasureTheory.VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure` to extend $m$ to a signed measure.
6. (C) Explain why the definition of a vector measure uses `HasSum` and not convergence of the partial sums in the order $1, 2, 3, \dots$.

### Reference

<?reference?>
