---
title: Finite measures, probability measures and the topology of weak convergence
kind: api
modules:
  - Mathlib.MeasureTheory.Measure.FiniteMeasure
  - Mathlib.MeasureTheory.Measure.ProbabilityMeasure
  - Mathlib.MeasureTheory.Measure.FiniteMeasureExt
  - Mathlib.MeasureTheory.Measure.FiniteMeasurePi
  - Mathlib.MeasureTheory.Measure.FiniteMeasureProd
  - Mathlib.MeasureTheory.Measure.DiracProba
  - Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
explains:
  E2: [MeasureTheory.FiniteMeasure, MeasureTheory.ProbabilityMeasure, MeasureTheory.FiniteMeasure.testAgainstNN, MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto, MeasureTheory.FiniteMeasure.toWeakDualBCNN, MeasureTheory.FiniteMeasure.normalize, MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish, MeasureTheory.FiniteMeasure.prod, MeasureTheory.isEmbedding_diracProba, BoundedContinuousFunction.integrable]
  E1: auto
families: []
requires: [V13, V16, V18.C02, V18.C04, V18.C05, V18.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Finite measures, probability measures and the topology of weak convergence

### Overview

A sequence of measures $\mu_n$ on a topological space converges weakly to $\mu$ if

$$\int f \, d\mu_n \to \int f \, d\mu$$

for every bounded continuous function $f$. This is the convergence of the central limit theorem: the laws of the normalized sums converge weakly to the Gaussian law, but the measures of a fixed set need not converge. For example, $\delta_{1/n}$ converges weakly to $\delta_0$, but $\delta_{1/n}(\{0\}) = 0$ for every $n$ and $\delta_0(\{0\}) = 1$.

To make weak convergence a convergence in a topological space, Mathlib defines two new types: `MeasureTheory.FiniteMeasure Ω`, the finite measures on $\Omega$, and `MeasureTheory.ProbabilityMeasure Ω`, the probability measures. Each type has the topology of weak convergence. This section describes the two types, their topology, the integrals of bounded continuous functions, the uniqueness of a measure from the integrals of a separating algebra, products of finite measures, and the embedding $x \mapsto \delta_x$. Section 2 gives the other descriptions of weak convergence, Section 3 the theorem of Prokhorov and Section 4 the characteristic functions.

### The library around it

#### Integrals of bounded continuous functions

The file `Mathlib.MeasureTheory.Integral.BoundedContinuousFunction` collects the facts that make the definition work. A bounded continuous function $f : X \to E$ is integrable for every finite measure on the Borel sets, `BoundedContinuousFunction.integrable`, and its integral satisfies $\|\int f \, d\mu\| \le \mu(X) \, \|f\|$, `BoundedContinuousFunction.norm_integral_le_mul_norm`, where $\|f\|$ is the sup norm. For a nonnegative $f$, the lower integral is finite, `BoundedContinuousFunction.lintegral_lt_top_of_nnreal`, and its real value is the Bochner integral, `BoundedContinuousFunction.toReal_lintegral_coe_eq_integral`.

The file also has a criterion for weak convergence of probability measures. If $\int f \, d\mu \le \liminf \int f \, d\mu_n$ for every nonnegative bounded continuous $f$, then the integrals of every bounded continuous function converge, `BoundedContinuousFunction.tendsto_integral_of_forall_integral_le_liminf_integral`. The proof applies the hypothesis to $f + \|f\|$ and $\|f\| - f$, which are nonnegative, and gets the bounds for the lower and the upper limit. The integral is $1$ on constants for probability measures, so the constant does not change the limits.

#### The types and their values

A term of `MeasureTheory.FiniteMeasure Ω` is a measure together with a proof that it is finite. The coercion to a function on sets takes values in `ℝ≥0`, the nonnegative reals, not in `ℝ≥0∞`: the value $\mu(A)$ is a finite number. The total mass $\mu(\Omega)$ is `MeasureTheory.FiniteMeasure.mass`. The type has the operations of an additive monoid and a scalar multiplication by `ℝ≥0`, and the image under a measurable map is `MeasureTheory.FiniteMeasure.map`, with the value $\mu(f^{-1}(B))$ on a measurable $B$, `MeasureTheory.FiniteMeasure.map_apply`. The restriction to a set is `MeasureTheory.FiniteMeasure.restrict`.

The type `MeasureTheory.ProbabilityMeasure Ω` has the measures with $\mu(\Omega) = 1$. There is no addition on it, but there is the image under a measurable map, `MeasureTheory.ProbabilityMeasure.map`. The map `MeasureTheory.ProbabilityMeasure.toFiniteMeasure` forgets that the mass is $1$. In the other direction, a nonzero finite measure has a normalized form, `MeasureTheory.FiniteMeasure.normalize`, and every finite measure is its mass times its normalization, `MeasureTheory.FiniteMeasure.self_eq_mass_smul_normalize`. For a measure with an instance `MeasureTheory.IsProbabilityMeasure`, the term of the new type is `MeasureTheory.Measure.toProbabilityMeasure`.

#### The topology of weak convergence

The topology on `MeasureTheory.FiniteMeasure Ω` is induced by the pairing with nonnegative bounded continuous functions. The pairing `MeasureTheory.FiniteMeasure.testAgainstNN μ f` is $\int f \, d\mu$ for $f : \Omega \to \mathbb{R}_{\ge 0}$ bounded and continuous, as an element of `ℝ≥0`. It is Lipschitz in $f$ with the constant $\mu(\Omega)$, `MeasureTheory.FiniteMeasure.testAgainstNN_lipschitz`. The map `MeasureTheory.FiniteMeasure.toWeakDualBCNN` sends $\mu$ to this pairing, an element of a weak dual space, and the topology is the topology induced by this map. The map is injective and an embedding, `MeasureTheory.FiniteMeasure.isEmbedding_toWeakDualBCNN`.

The convergence in this topology is weak convergence. The criterion `MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto` says that $\mu_n \to \mu$ if and only if $\int f \, d\mu_n \to \int f \, d\mu$ for every real bounded continuous $f$. The variants with nonnegative functions and lower integrals are `MeasureTheory.FiniteMeasure.tendsto_iff_forall_lintegral_tendsto` and `MeasureTheory.FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto`, and the one with values in $\mathbb{C}$ is `MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto`. The mass is continuous, `MeasureTheory.FiniteMeasure.continuous_mass`, since the constant $1$ is a test function. The image under a continuous map is continuous, `MeasureTheory.FiniteMeasure.continuous_map`, since $f \circ g$ is bounded and continuous when $f$ is.

The type `MeasureTheory.ProbabilityMeasure Ω` has the topology induced from finite measures, and `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` is the same criterion. Normalization is continuous where the mass is not $0$: `MeasureTheory.FiniteMeasure.tendsto_normalize_iff_tendsto` says that $\mu_n \to \mu$ if and only if the masses and the normalized measures converge.

#### Uniqueness from integrals

A finite measure on a space with enough bounded continuous functions is determined by its integrals of them. The general result, `MeasureTheory.FiniteMeasure.ext_of_forall_integral_eq`, needs the class `HasOuterApproxClosed` of Section 2, which holds on metric spaces. The file `Mathlib.MeasureTheory.Measure.FiniteMeasureExt` proves a stronger result with fewer test functions. Let $A$ be a star subalgebra of the bounded continuous functions with values in $\mathbb{R}$ or $\mathbb{C}$ that separates points. On a Polish space, two finite measures with the same integrals of all $g \in A$ are equal, `MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish`. The variant for a complete second countable space with an extended pseudometric is `MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable`. The proof approximates a function of $A$ by the bounded functions $x \mapsto f(x) e^{-\varepsilon f(x)^2}$ and lets $\varepsilon$ tend to $0$. The main application is the uniqueness theorem for characteristic functions of Section 4: the functions $x \mapsto e^{i \langle t, x \rangle}$ span such an algebra.

#### Products

The files `Mathlib.MeasureTheory.Measure.FiniteMeasureProd` and `Mathlib.MeasureTheory.Measure.FiniteMeasurePi` define the product of two finite measures, `MeasureTheory.FiniteMeasure.prod`, and of a finite family, `MeasureTheory.FiniteMeasure.pi`. The values on rectangles are the products, `MeasureTheory.FiniteMeasure.prod_prod` and `MeasureTheory.FiniteMeasure.pi_pi`, and the mass of the product is the product of the masses, `MeasureTheory.FiniteMeasure.mass_prod`. The same definitions exist for probability measures, and the marginals of a product are the factors, `MeasureTheory.ProbabilityMeasure.map_fst_prod`. On second countable pseudometrizable spaces, the product is continuous for the weak topology, `MeasureTheory.ProbabilityMeasure.continuous_prod` and `MeasureTheory.ProbabilityMeasure.continuous_pi`: if $\mu_n \to \mu$ and $\nu_n \to \nu$, then $\mu_n \otimes \nu_n \to \mu \otimes \nu$.

#### Point masses

The file `Mathlib.MeasureTheory.Measure.DiracProba` studies the map `MeasureTheory.diracProba` from $X$ to the probability measures, $x \mapsto \delta_x$. It is continuous, `MeasureTheory.continuous_diracProba`. On a completely regular space that is T0, it is a topological embedding, `MeasureTheory.isEmbedding_diracProba`: $\delta_{x_n} \to \delta_x$ if and only if $x_n \to x$, `MeasureTheory.tendsto_diracProba_iff_tendsto`. The proof of the converse uses a bounded continuous function that is $1$ at $x$ and $0$ outside a given neighborhood, `CompletelyRegularSpace.exists_BCNN`. So $X$ is homeomorphic to the set of point masses, `MeasureTheory.diracProbaHomeomorph`.

#### Common errors

1. Expecting the values of a finite measure in `ℝ≥0∞`. The coercion of `MeasureTheory.FiniteMeasure Ω` to a function on sets takes values in `ℝ≥0`. To use a theorem about measures, apply it to the underlying measure, `MeasureTheory.FiniteMeasure.toMeasure`, and convert with `MeasureTheory.FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure`.
2. Expecting the measures of sets to converge. Weak convergence does not give $\mu_n(A) \to \mu(A)$ for every measurable $A$; the theorem of Portmanteau in Section 2 gives it for the sets with $\mu(\partial A) = 0$.
3. Normalizing the zero measure. `MeasureTheory.FiniteMeasure.normalize` of a measure with mass $0$ is a point mass by convention, and the theorems about the normalization have the hypothesis $\mu \ne 0$.

### Exercises

1. (A) Show that $\delta_{1/n} \to \delta_0$ in `MeasureTheory.ProbabilityMeasure ℝ` with `MeasureTheory.tendsto_diracProba_iff_tendsto`, and compute $\delta_{1/n}(\{0\})$ and $\delta_0(\{0\})$.
2. (A) Let $\mu_n$ be the uniform probability measure on $\{1/n, 2/n, \dots, n/n\}$. Show that $\mu_n$ converges to Lebesgue measure on $[0, 1]$ with `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` and Riemann sums.
3. (B) Show that $n \delta_n$ does not converge in `MeasureTheory.FiniteMeasure ℝ`, and that $\delta_n$ has no limit in `MeasureTheory.ProbabilityMeasure ℝ`.
4. (B) Prove the bound of `BoundedContinuousFunction.norm_integral_le_mul_norm` from the bound $\|f(x)\| \le \|f\|$ for every $x$.
5. (B) Prove `MeasureTheory.FiniteMeasure.tendsto_zero_of_tendsto_zero_mass`: if the masses of $\mu_n$ tend to $0$, then $\mu_n \to 0$. Use the bound $\int f \, d\mu_n \le \|f\| \, \mu_n(\Omega)$.
6. (C) Show that the functions $x \mapsto \cos(t x)$ for $t \in \mathbb{R}$ span a star subalgebra of the bounded continuous functions on $\mathbb{R}$ that does not separate points. Find two different probability measures with the same integrals of all these functions, and explain which hypothesis of `MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish` fails.

### Reference

<?reference?>
