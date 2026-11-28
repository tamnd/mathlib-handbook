---
title: Tightness, the theorem of Prokhorov and the total variation distance
kind: api
modules:
  - Mathlib.MeasureTheory.Measure.Tight
  - Mathlib.MeasureTheory.Measure.TightNormed
  - Mathlib.MeasureTheory.Measure.Prokhorov
  - Mathlib.MeasureTheory.Measure.TotalVariation.Defs
  - Mathlib.MeasureTheory.Measure.TotalVariation.Basic
explains:
  E2: [MeasureTheory.IsTightMeasureSet, MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le, MeasureTheory.isTightMeasureSet_singleton, MeasureTheory.isTightMeasureSet_iff_tendsto_measure_norm_gt, isCompact_closure_of_isTightMeasureSet, MeasureTheory.isTightMeasureSet_of_isCompact_closure, MeasureTheory.etvDist, MeasureTheory.tvDist, MeasureTheory.etvDist_eq_lintegral_eNorm_rnDeriv_add_singularPart, MeasureTheory.IsHahnDecomposition.tvDist_eq]
  E1: auto
families: []
requires: [V13, V16, V18.C02, V18.C04, V18.C05, V18.C12]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Tightness, the theorem of Prokhorov and the total variation distance

### Overview

A sequence of probability measures can lose mass at infinity. The point masses $\delta_n$ on $\mathbb{R}$ have no weak limit: for a continuous $f$ with compact support, $\int f \, d\delta_n \to 0$, and the only candidate limit is the zero measure, which is not a probability measure. A set $S$ of measures is tight if the mass stays on compact sets uniformly: for every $\varepsilon > 0$ there is a compact $K$ with $\mu(K^c) \le \varepsilon$ for all $\mu \in S$.

The theorem of Prokhorov says that tightness is the right condition for compactness. On a Hausdorff space, a tight set of probability measures has a compact closure in the topology of weak convergence. On a complete separable metric space, the converse holds. So every tight sequence has a weakly convergent subsequence, the main tool to construct limits in probability theory.

This section also describes the total variation distance between finite measures. It defines a much stronger convergence than weak convergence: $\delta_{1/n}$ converges weakly to $\delta_0$, but its total variation distance to $\delta_0$ is $2$ for every $n$.

### The library around it

#### Tight sets of measures

The definition `MeasureTheory.IsTightMeasureSet S` says that the supremum of the measures in $S$ tends to $0$ along the complements of compact sets, in the form of a limit along the filter of small sets of the cocompact filter. The usual form is `MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le`: for every $\varepsilon > 0$ there is a compact $K$ with $\mu(K^c) \le \varepsilon$ for all $\mu \in S$.

A single finite measure is tight on a complete separable metric space, `MeasureTheory.isTightMeasureSet_singleton`. The proof uses the inner regularity of finite measures on such spaces, and the general form is `MeasureTheory.isTightMeasureSet_singleton_of_innerRegular`. On a compact space every set is tight, `MeasureTheory.IsTightMeasureSet.of_compactSpace`. Tightness passes to subsets, finite unions and intersections, `MeasureTheory.IsTightMeasureSet.subset` and `MeasureTheory.IsTightMeasureSet.union`, and to images under a continuous map, `MeasureTheory.IsTightMeasureSet.map`, because the image of a compact set is compact. A set of measures on a product is tight when the sets of the two marginals are tight, `MeasureTheory.IsTightMeasureSet.prodMk`: the product of the two compact sets has a complement of small measure.

#### Tightness in normed spaces

The file `Mathlib.MeasureTheory.Measure.TightNormed` gives criteria in normed spaces. In a proper space, where closed balls are compact, a set $S$ is tight if and only if

$$\sup_{\mu \in S} \mu(\{x : \|x\| > r\}) \to 0 \quad (r \to \infty),$$

`MeasureTheory.isTightMeasureSet_iff_tendsto_measure_norm_gt`. The form with closed balls is `MeasureTheory.isTightMeasureSet_iff_tendsto_measure_compl_closedBall`. For a sequence of finite measures, a limit superior is enough, `MeasureTheory.isTightMeasureSet_range_iff_tendsto_limsup_measure_norm_gt`: the first measures of the sequence are tight one at a time. In a finite dimensional inner product space, it is enough to control the projections on the vectors $y$: $S$ is tight if and only if $\sup_{\mu \in S} \mu(\{x : |\langle y, x \rangle| > r\}) \to 0$ for every $y$, `MeasureTheory.isTightMeasureSet_iff_inner_tendsto`. This criterion is the link with characteristic functions in Section 4, since the characteristic function controls the laws of the projections.

#### The theorem of Prokhorov

The file `Mathlib.MeasureTheory.Measure.Prokhorov` proves the two directions. On a Hausdorff space with the Borel σ-algebra, a tight set of probability measures has a compact closure, `isCompact_closure_of_isTightMeasureSet`. The proof is a compactness argument in the space of finite measures. Let $K_n$ be compact sets and $u_n \to 0$ numbers. The set of finite measures $\mu$ with mass at most $C$ and $\mu(K_n^c) \le u_n$ for every $n$ is compact, `isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le`, if the space is normal or the sets $K_n$ increase. The probability form is `isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le`. A tight set of probability measures is in such a set: take $K_n$ with $\mu(K_n^c) \le 1/n$ for all $\mu$ in the set, and replace $K_n$ by $K_1 \cup \dots \cup K_n$ to make the sequence increase. On a compact space this gives `isCompact_setOfPred_finiteMeasure_le_of_compactSpace`: the finite measures of mass at most $C$ form a compact set. So the probability measures on a compact Hausdorff space form a compact space, `instCompactSpaceProbabilityMeasure`.

The converse needs more of the space. On a complete separable metric space, a set of probability measures with a compact closure is tight, `MeasureTheory.isTightMeasureSet_of_isCompact_closure`. The proof uses `MeasureTheory.exists_measure_iUnion_gt_of_isCompact_closure`: for an open cover $(U_i)$ of the space and $\varepsilon > 0$, a finite union $U_0 \cup \dots \cup U_k$ has measure larger than $1 - \varepsilon$ for all the measures of the set. With covers by balls of radius $1/m$ and errors $\varepsilon 2^{-m}$, the intersection over $m$ of the finite unions has measure at least $1 - \varepsilon$ for every measure of the set. The closure of this intersection is totally bounded and closed, so it is compact by completeness.

#### The total variation distance

For two measures $\mu$ and $\nu$, the total variation distance `MeasureTheory.etvDist μ ν` is the total variation of the signed measure $\mu - \nu$ on the whole space:

$$\|\mu - \nu\|_{TV} = \sup \sum_k |\mu(A_k) - \nu(A_k)|,$$

the supremum over the finite measurable partitions $(A_k)$, `MeasureTheory.etvDist_eq_iSup_finPartition_eNorm`. It is the distance `MeasureTheory.VectorMeasure.etvDist` of Chapter 12, Section 2 for the signed measures of $\mu$ and $\nu$, `MeasureTheory.etvDist_eq_etvDist_toSignedMeasure`. The value is in $[0, \infty]$, and it is $\infty$ when one of the measures is not finite, `MeasureTheory.etvDist_of_not_isFiniteMeasure`. The real version `MeasureTheory.tvDist` has the value $0$ in that case, `MeasureTheory.tvDist_of_not_isFiniteMeasure`, and it agrees with the extended version on finite measures, `MeasureTheory.ofReal_tvDist`. Note that this distance has no factor $1/2$: two mutually singular probability measures have the distance $2$, `MeasureTheory.tvDist_of_mutuallySingular`.

The distance is symmetric, `MeasureTheory.tvDist_comm`, it satisfies the triangle inequality, `MeasureTheory.tvDist_triangle`, and it is $0$ only for equal finite measures, `MeasureTheory.tvDist_eq_zero_iff`. For $\mu \le \nu$, it is the difference of the masses, `MeasureTheory.etvDist_of_le`. It is additive over a set and its complement, `MeasureTheory.tvDist_restrict_add_compl`.

The file `Mathlib.MeasureTheory.Measure.TotalVariation.Basic` computes the distance from the Lebesgue decomposition of Chapter 4. For finite $\mu$ and $\nu$, `MeasureTheory.etvDist_eq_lintegral_eNorm_rnDeriv_add_singularPart` gives

$$\|\mu - \nu\|_{TV} = \int \Big|1 - \frac{d\mu}{d\nu}\Big| \, d\nu + \mu_s(X),$$

where $\mu_s$ is the singular part of $\mu$ with respect to $\nu$. For $\mu \ll \nu$ the second term is $0$, `MeasureTheory.tvDist_eq_integral_abs_rnDeriv_of_ac`. With a Hahn decomposition $s$ for $\mu$ and $\nu$ in the sense of Chapter 4, the distance is $\nu(s) - \mu(s) + \mu(s^c) - \nu(s^c)$, `MeasureTheory.IsHahnDecomposition.tvDist_eq`.

#### Common errors

1. Expecting a weakly convergent sequence to converge in total variation. The two topologies differ: $\delta_{1/n} \to \delta_0$ weakly, but `MeasureTheory.tvDist_of_mutuallySingular` gives the distance $2$ for every $n$.
2. Using the factor $1/2$ of some texts. In Mathlib, `MeasureTheory.tvDist` is the full total variation of $\mu - \nu$, and its value for probability measures is between $0$ and $2$.
3. Applying the converse of Prokhorov on a space that is not complete. `MeasureTheory.isTightMeasureSet_of_isCompact_closure` needs a complete separable metric space; the direction from tightness to compactness, `isCompact_closure_of_isTightMeasureSet`, needs only a Hausdorff space.

### Exercises

1. (A) Show that the set $\{\delta_n : n \in \mathbb{N}\}$ of probability measures on $\mathbb{R}$ is not tight, with `MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le`.
2. (A) Compute `MeasureTheory.tvDist` between the uniform probability measures on $[0, 1]$ and on $[0, 2]$ with `MeasureTheory.tvDist_eq_integral_abs_rnDeriv_of_ac`.
3. (B) Show that the Gaussian measures with mean $0$ and variances $\sigma^2 \le 1$ form a tight set, with `MeasureTheory.isTightMeasureSet_iff_tendsto_measure_norm_gt` and the inequality of Chebyshev.
4. (B) Show that the uniform measures on $[0, n]$, $n \ge 1$, do not form a tight set, and that their integrals of each continuous function with compact support tend to $0$.
5. (B) Prove `MeasureTheory.etvDist_of_le` from the definition with partitions.
6. (C) Use the theorem of Prokhorov to show that every sequence of probability measures on $[0, 1]$ has a weakly convergent subsequence, and give a sequence with two different limits along two subsequences.

### Reference

<?reference?>
