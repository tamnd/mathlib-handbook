---
title: The Portmanteau theorem and the Lévy-Prokhorov metric
kind: api
modules:
  - Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
  - Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
  - Mathlib.MeasureTheory.Measure.Portmanteau
  - Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
explains:
  E2: [HasOuterApproxClosed, MeasureTheory.ext_of_forall_lintegral_eq_of_IsFiniteMeasure, Measure.ext_of_integral_mul_boundedContinuousFunction, MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto, MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto, MeasureTheory.tendsto_of_forall_isOpen_le_liminf, MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto, MeasureTheory.levyProkhorovEDist, MeasureTheory.left_measure_le_of_levyProkhorovEDist_lt, MeasureTheory.LevyProkhorov.probabilityMeasureHomeomorph]
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

## The Portmanteau theorem and the Lévy-Prokhorov metric

### Overview

Section 1 defines the weak convergence of probability measures by the integrals of bounded continuous functions. The theorem of Portmanteau gives equivalent conditions in terms of sets. For probability measures $\mu_n$ and $\mu$ on a metric space, the following are equivalent:

1. $\int f \, d\mu_n \to \int f \, d\mu$ for every bounded continuous $f$;
2. the same for every bounded Lipschitz $f$;
3. $\limsup \mu_n(F) \le \mu(F)$ for every closed $F$;
4. $\mu(G) \le \liminf \mu_n(G)$ for every open $G$;
5. $\mu_n(E) \to \mu(E)$ for every Borel $E$ with $\mu(\partial E) = 0$.

The inequalities in 3 and 4 can be strict: for $\mu_n = \delta_{1/n}$ and $\mu = \delta_0$, the open set $(0, 1)$ has $\mu_n$ measure $1$ and $\mu$ measure $0$.

On a separable metric space, the topology of weak convergence comes from a metric, the Lévy-Prokhorov metric. This section describes the approximation of closed sets by continuous functions that the proofs need, the theorem of Portmanteau, and the Lévy-Prokhorov metric.

### The library around it

#### Outer approximation of closed sets

The class `HasOuterApproxClosed X` says that for every closed set $F$ there is a sequence of bounded continuous functions $f_n : X \to [0, 1]$ with $f_n = 1$ on $F$ and $f_n \to \mathbf{1}_F$ pointwise. The sequence is `IsClosed.apprSeq`, with the properties `HasOuterApproxClosed.apprSeq_apply_le_one`, `HasOuterApproxClosed.apprSeq_apply_eq_one` and `HasOuterApproxClosed.tendsto_apprSeq`. On a pseudometrizable space there is an instance, `instHasOuterApproxClosedOfPseudoMetrizableSpace`: the functions are $x \mapsto \max(0, 1 - (n + 1) \, d(x, F))$, the thickened indicators of the topology files, for a metric that gives the topology.

With dominated convergence, the class gives $\int f_n \, d\mu \to \mu(F)$ for a finite $\mu$, `HasOuterApproxClosed.tendsto_lintegral_apprSeq`. So the integrals of bounded continuous functions determine the values of $\mu$ on closed sets, and by the π-λ theorem of Chapter 1 on all Borel sets. This is `MeasureTheory.ext_of_forall_lintegral_eq_of_IsFiniteMeasure` for nonnegative functions and lower integrals, and `MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure` for real functions.

The file `Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd` proves the same uniqueness on products with fewer test functions. Two finite measures on $Z \times T$ are equal if they have the same integrals of all functions $f(z) g(t)$ with $f$ and $g$ bounded and continuous, `Measure.ext_of_integral_mul_boundedContinuousFunction`. The variants for finite products of spaces are `Measure.ext_of_integral_prod_mul_prod_boundedContinuousFunction` and its relatives. The proof uses the rectangles with closed sides, a π-system that generates the product σ-algebra, and approximates the indicator of each side.

#### The theorem of Portmanteau

The file `Mathlib.MeasureTheory.Measure.Portmanteau` proves the equivalences. Weak convergence gives the inequality for closed sets, `MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`. The proof takes the functions of `IsClosed.apprSeq`: for each $k$, $\limsup \mu_n(F) \le \lim \int f_k \, d\mu_n = \int f_k \, d\mu$, and the right side tends to $\mu(F)$. For finite measures, the same is `MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto`. The inequality for open sets follows by complements, `MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto`, and the two forms are equivalent for probability measures, `MeasureTheory.limsup_measure_closed_le_iff_liminf_measure_open_ge`.

The two inequalities give the convergence on the sets with a null boundary, `MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`: the interior of $E$ is open, its closure is closed, and both have the measure $\mu(E)$ when $\mu(\partial E) = 0$. For a set that is closed and open, the boundary is empty, `MeasureTheory.ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto`.

The converse directions need a countably generated filter, for example the filter `Filter.atTop` on $\mathbb{N}$. The inequality for open sets implies weak convergence, `MeasureTheory.tendsto_of_forall_isOpen_le_liminf`. The proof writes the integral of a nonnegative $f$ as $\int_0^\infty \mu(\{f > t\}) \, dt$, the layer cake formula, applies the inequality to the open sets $\{f > t\}$ and then the lemma of Fatou of Chapter 4. Its lower integral form is `MeasureTheory.lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`. The inequality for closed sets also implies weak convergence, `MeasureTheory.tendsto_of_forall_isClosed_limsup_le`. On a pseudo extended metric space, it is enough to test bounded Lipschitz functions, `MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto`.

To use the convergence on sets with a null boundary, the proofs need many such sets. The theorem `MeasureTheory.exists_null_frontier_thickening` gives, for a set $s$ and an interval $(a, b)$ of radii, a radius $r$ with $\mu(\partial s_r) = 0$, where $s_r$ is the open $r$ thickening of $s$. The reason is that the boundaries of the thickenings for different radii are disjoint, and a finite measure has at most countably many disjoint sets of positive measure.

A convergence on a π-system is enough when the π-system is fine: `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem` says that on a second countable space, if $\mu_n(s) \to \mu(s)$ for every $s$ in a π-system $S$ that contains a neighborhood basis inside every open set, then $\mu_n \to \mu$.

#### The Lévy-Prokhorov metric

For two measures $\mu$ and $\nu$ on a pseudo extended metric space, the Lévy-Prokhorov distance `MeasureTheory.levyProkhorovEDist μ ν` is the infimum of the $\varepsilon > 0$ such that

$$\mu(B) \le \nu(B_\varepsilon) + \varepsilon \quad \text{and} \quad \nu(B) \le \mu(B_\varepsilon) + \varepsilon$$

for every measurable $B$, where $B_\varepsilon$ is the open $\varepsilon$ thickening of $B$. Its value is in $[0, \infty]$. The real version is `MeasureTheory.levyProkhorovDist`. The definition gives the inequalities back for a larger $\varepsilon$, `MeasureTheory.left_measure_le_of_levyProkhorovEDist_lt` and `MeasureTheory.right_measure_le_of_levyProkhorovEDist_lt`. The distance is symmetric, `MeasureTheory.levyProkhorovEDist_comm`, and it satisfies the triangle inequality, `MeasureTheory.levyProkhorovEDist_triangle`, since the thickening of a thickening is in a thickening of the sum of the radii. For finite measures it is at most the larger of the two masses, `MeasureTheory.levyProkhorovEDist_le_max_measure_univ`.

The type of probability measures has the topology of weak convergence, so the metric lives on a type synonym, `MeasureTheory.LevyProkhorov`, with the maps `MeasureTheory.LevyProkhorov.toMeasure` and `MeasureTheory.LevyProkhorov.ofMeasure`. The instance `MeasureTheory.LevyProkhorov.levyProkhorovDist_metricSpace_probabilityMeasure` makes it a metric space; distinct measures have positive distance because they differ on a closed set. Convergence in this metric implies weak convergence, `MeasureTheory.LevyProkhorov.le_convergenceInDistribution`, through the bound of `MeasureTheory.BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt` on integrals. On a separable space the converse holds, and the identity is a homeomorphism, `MeasureTheory.LevyProkhorov.probabilityMeasureHomeomorph`. The proof of the converse uses a partition of the space into countably many sets of small diameter, `MeasureTheory.SeparableSpace.exists_measurable_partition_diam_le`.

#### Common errors

1. Expecting $\mu_n(E) \to \mu(E)$ for every Borel $E$. The theorem `MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto` needs $\mu(\partial E) = 0$, and the example of $\delta_{1/n}$ with $E = \{0\}$ shows that this hypothesis is necessary.
2. Using the converse directions with a general filter. The theorems `MeasureTheory.tendsto_of_forall_isOpen_le_liminf` and `MeasureTheory.tendsto_of_forall_isClosed_limsup_le` have the hypothesis that the filter is countably generated.
3. Putting the metric on `MeasureTheory.ProbabilityMeasure Ω` directly. The type has a topology already, and a second metric structure would conflict with it. The metric is on the synonym `MeasureTheory.LevyProkhorov`, and `MeasureTheory.LevyProkhorov.probabilityMeasureHomeomorph` connects the two.

### Exercises

1. (A) For $\mu_n = \delta_{1/n}$ and $\mu = \delta_0$, compute $\limsup \mu_n(F)$ and $\mu(F)$ for the closed sets $F = \{0\}$ and $F = [-1, 0]$, and check the inequality of `MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`.
2. (A) Compute `MeasureTheory.levyProkhorovEDist` between $\delta_x$ and $\delta_y$ on $\mathbb{R}$ for $|x - y| < 1$ and for $|x - y| \ge 1$.
3. (B) Show that the functions $f_n(x) = \max(0, 1 - (n + 1) \, d(x, F))$ satisfy the three conditions of `HasOuterApproxClosed`.
4. (B) Let $\mu_n$ be the uniform measure on $\{1/n, \dots, n/n\}$ and $\mu$ Lebesgue measure on $[0, 1]$. Show that $\mu_n(\mathbb{Q} \cap [0, 1]) \not\to \mu(\mathbb{Q} \cap [0, 1])$, and explain why this does not contradict `MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`.
5. (B) Prove `MeasureTheory.limsup_measure_closed_le_iff_liminf_measure_open_ge` from $\mu(G^c) = 1 - \mu(G)$ for probability measures.
6. (C) Prove the claim behind `MeasureTheory.exists_null_frontier_thickening`: for $r < r'$, the boundaries of the $r$ and $r'$ thickenings of a set are disjoint.

### Reference

<?reference?>
