---
title: The Hahn, Jordan and Lebesgue decompositions of signed measures
kind: api
modules:
  - Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn
  - Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
  - Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
  - Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue
  - Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
  - Mathlib.MeasureTheory.VectorMeasure.TotalVariation
explains:
  E2: [MeasureTheory.SignedMeasure.exists_subset_restrict_nonpos, MeasureTheory.SignedMeasure.exists_compl_positive_negative, MeasureTheory.SignedMeasure.of_symmDiff_compl_positive_negative, MeasureTheory.JordanDecomposition, MeasureTheory.SignedMeasure.toJordanDecomposition, MeasureTheory.SignedMeasure.totalVariation, MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_posPart, MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq, MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq, MeasureTheory.VectorMeasure.etvDist]
  E1: auto
families: []
requires: [V18.C02, V18.C04, V18.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Hahn, Jordan and Lebesgue decompositions of signed measures

### Overview

A signed measure $s$ is the difference of two finite measures, and there is a best choice of the two. The Hahn decomposition divides the space into a positive set $P$ and a negative set $N = P^c$. The Jordan decomposition then writes $s = s^+ - s^-$ with $s^+(A) = s(A \cap P)$ and $s^-(A) = -s(A \cap N)$. These two measures are mutually singular, and they are unique with this property. Their sum $|s| = s^+ + s^-$ is the total variation of $s$.

With the Jordan decomposition, the theorems of Chapter 4 for measures pass to signed measures. This section describes the Lebesgue decomposition of a signed measure with respect to a measure $\mu$, the Radon-Nikodym derivative of a signed measure, the same results for complex measures, and the total variation distance between two vector measures.

Chapter 4, Section 3 has a Hahn decomposition for two finite measures $\mu$ and $\nu$ in the type of measures. The file `Mathlib.MeasureTheory.Measure.Decomposition.Hahn` there and the file `Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn` here prove related statements in two different languages.

### The library around it

#### The Hahn decomposition

The proof starts with a lemma on negative sets. If $s(A) < 0$, then $A$ contains a negative set $B$ with $s(B) < 0$, `MeasureTheory.SignedMeasure.exists_subset_restrict_nonpos`. The proof removes from $A$, step by step, subsets of large positive measure. The removed sets are disjoint and their measures form a convergent series, so the sizes go to $0$, and the remaining set is negative.

The Hahn decomposition follows. Let $c$ be the infimum of $s(B)$ over the negative sets $B$; this set of values is `MeasureTheory.SignedMeasure.measureOfNegatives`, and it is bounded below because $s$ is finite. A sequence of negative sets with values that tend to $c$ has a negative union $N$ with $s(N) = c$, and the lemma above shows that the complement of $N$ is positive. The result is `MeasureTheory.SignedMeasure.exists_compl_positive_negative`: there is a measurable $P$ with

$$0 \le s \text{ on } P, \qquad s \le 0 \text{ on } P^c,$$

in the notation `0 ≤[P] s` and `s ≤[Pᶜ] 0` of Section 1. The version with two complementary sets is `MeasureTheory.SignedMeasure.exists_isCompl_positive_negative`. The decomposition is unique up to null sets: for two Hahn decompositions $P$ and $Q$, `MeasureTheory.SignedMeasure.of_symmDiff_compl_positive_negative` gives $s(P \mathbin{\triangle} Q) = 0$. The lemma states only that $s(P \mathbin{\triangle} Q) = 0$, but every subset of $P \mathbin{\triangle} Q$ also has value $0$, since it is the union of a subset of $P \setminus Q$, which is positive and negative, and a subset of $Q \setminus P$.

#### The Jordan decomposition

The structure `MeasureTheory.JordanDecomposition α` has two finite measures `MeasureTheory.JordanDecomposition.posPart` and `MeasureTheory.JordanDecomposition.negPart` and a proof that they are mutually singular, `MeasureTheory.JordanDecomposition.mutuallySingular`. Its signed measure is the difference, `MeasureTheory.JordanDecomposition.toSignedMeasure`. The map `MeasureTheory.SignedMeasure.toJordanDecomposition` goes the other way. It is defined from a Hahn decomposition $P$ with the measures `MeasureTheory.SignedMeasure.toMeasureOfZeroLE` on $P$ and `MeasureTheory.SignedMeasure.toMeasureOfLEZero` on $P^c$, `MeasureTheory.SignedMeasure.toJordanDecomposition_spec`. The two maps are inverse:

- `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition` gives $s^+ - s^- = s$;
- `MeasureTheory.SignedMeasure.toJordanDecomposition_eq` says that every Jordan decomposition of $s$ is this one.

The equivalence is `MeasureTheory.SignedMeasure.toJordanDecompositionEquiv`. The Jordan decompositions carry a negation, which exchanges the two parts, and a multiplication by real numbers, which exchanges the parts and multiplies them by $|r|$ when $r < 0$, `MeasureTheory.JordanDecomposition.real_smul_neg`. The map from signed measures respects both operations, `MeasureTheory.SignedMeasure.toJordanDecomposition_neg` and `MeasureTheory.SignedMeasure.toJordanDecomposition_smul_real`. In particular $|-s| = |s|$, `MeasureTheory.SignedMeasure.totalVariation_neg`. The value on a set is `MeasureTheory.SignedMeasure.apply_eq_posPart_real_sub_negPart_real`. The uniqueness follows from the uniqueness of the Hahn decomposition: for mutually singular $\mu$ and $\nu$ with $s = \mu - \nu$, the set where $\nu$ vanishes is a Hahn set for $s$.

The total variation `MeasureTheory.SignedMeasure.totalVariation s` is the measure $s^+ + s^-$. It is finite, and $|s|(A) = 0$ implies $s(A) = 0$, `MeasureTheory.SignedMeasure.null_of_totalVariation_zero`. Two signed measures are mutually singular exactly when their total variations are, `MeasureTheory.SignedMeasure.mutuallySingular_iff`, and $|s| \ll \mu$ exactly when both parts are, `MeasureTheory.SignedMeasure.totalVariation_absolutelyContinuous_iff`. Section 3 defines the variation of a general vector measure, and shows that it agrees with this one.

For two finite measures, the file `Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub` computes the decomposition of $\mu - \nu$ in the type of signed measures. The positive part is the truncated difference $\mu - \nu$ of measures, `MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_posPart`, and the negative part is $\nu - \mu$. This connects the two subtractions of Section 1.

#### The Lebesgue decomposition and the Radon-Nikodym theorem

A signed measure $s$ has a Lebesgue decomposition with respect to $\mu$ when both $s^+$ and $s^-$ have one; the class is `MeasureTheory.SignedMeasure.HaveLebesgueDecomposition`. This holds for every sigma finite $\mu$, `MeasureTheory.SignedMeasure.haveLebesgueDecomposition_of_sigmaFinite`. The singular part `MeasureTheory.SignedMeasure.singularPart s μ` is the difference of the singular parts of $s^+$ and $s^-$, and the derivative `MeasureTheory.SignedMeasure.rnDeriv s μ` is the difference of their derivatives, a real integrable function, `MeasureTheory.SignedMeasure.integrable_rnDeriv`. The decomposition is `MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq`:

$$s = s_\perp + f \mu, \qquad f = \frac{ds}{d\mu},$$

with $s_\perp$ mutually singular with $\mu$. It is unique: `MeasureTheory.SignedMeasure.toJordanDecomposition_eq_of_eq_add_withDensity` computes the Jordan decomposition of $t + f\mu$ for a singular $t$. Both parts are additive. The singular part of $s + t$ is the sum of the singular parts, `MeasureTheory.SignedMeasure.singularPart_add`. The derivative of $s + t$ is the sum of the derivatives only almost everywhere, `MeasureTheory.SignedMeasure.rnDeriv_add`, because the derivative is a function chosen by the definition and is unique only up to null sets.

The Radon-Nikodym theorem for signed measures is `MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq`: for a sigma finite $\mu$, $s \ll \mu$ exactly when $s = \frac{ds}{d\mu} \, \mu$. Here $s \ll \mu$ is written `MeasureTheory.VectorMeasure.AbsolutelyContinuous s μ.toENNRealVectorMeasure`. For a complex measure, the real and imaginary parts give the same results: `MeasureTheory.ComplexMeasure.singularPart_add_withDensity_rnDeriv_eq` is the Lebesgue decomposition with a complex derivative.

#### The total variation distance

The file `Mathlib.MeasureTheory.VectorMeasure.TotalVariation` defines a distance on the vector measures with values in a normed group. The extended distance `MeasureTheory.VectorMeasure.etvDist μ ν` is the supremum over finite measurable partitions $(A_k)$ of the space of

$$\sum_k \|\mu(A_k) - \nu(A_k)\|,$$

`MeasureTheory.VectorMeasure.etvDist_eq_iSup_finPartition_eNorm`. It is symmetric, it satisfies the triangle inequality, `MeasureTheory.VectorMeasure.etvDist_triangle`, and it is $0$ only for equal measures, `MeasureTheory.VectorMeasure.etvDist_eq_zero_iff`. For signed measures it is $|\mu - \nu|$ of the whole space. Chapter 13 uses a total variation distance between finite measures.

#### Common errors

1. Expecting a unique Hahn set. Only the Jordan decomposition is unique. Two Hahn sets $P$ and $Q$ differ by a set on which $s$ vanishes, and a lemma about $P$ does not transfer to $Q$ without `MeasureTheory.SignedMeasure.of_symmDiff_compl_positive_negative`.
2. Confusing $|s(A)|$ with $|s|(A)$. The total variation of a set is $s^+(A) + s^-(A)$, which is at least $|s(A)|$ and usually larger.
3. Applying the Radon-Nikodym theorem without sigma finiteness. The theorem needs `MeasureTheory.SigmaFinite μ`; the signed measure $s$ itself is always finite.

### Exercises

1. (A) Find the Hahn decomposition and the Jordan decomposition of the signed measure with density $f(x) = \sin x$ with respect to Lebesgue measure on $[0, 2\pi]$. Compute $|s|([0, 2\pi])$.
2. (A) For $s = \delta_0 - 2\delta_1 + 3\delta_2$ on $\{0, 1, 2\}$, give all Hahn sets of $s$ and the measures $s^+$, $s^-$, $|s|$.
3. (B) Prove that every subset of $P \mathbin{\triangle} Q$ has value $0$ for two Hahn sets $P$ and $Q$.
4. (B) Let $\mu$ and $\nu$ be finite. Use `MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_posPart` to show that $(\mu - \nu) + \nu = \mu$ for measures exactly when $\nu \le \mu$.
5. (B) Show that $|s|(A)$ is the supremum of $\sum_k |s(A_k)|$ over finite measurable partitions of $A$.
6. (C) Compute `MeasureTheory.VectorMeasure.etvDist` between $\delta_x$ and $\delta_y$ for $x \ne y$, and between two probability measures with densities $f$ and $g$ with respect to $\mu$.

### Reference

<?reference?>
