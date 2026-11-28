---
title: "Lp spaces: the working API"
kind: api
modules:
  - Mathlib.MeasureTheory.Function.LpSpace.CompleteOfCompleteLp
  - Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
  - Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
  - Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
  - Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
  - Mathlib.MeasureTheory.Function.LpSpace.Indicator
  - Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
  - Mathlib.MeasureTheory.Function.LpOrder
  - Mathlib.MeasureTheory.Function.AEEqFun.DomAct
  - Mathlib.MeasureTheory.Function.L1Space.AEEqFun
  - Mathlib.MeasureTheory.Function.SimpleFuncDense
explains:
  E2: [MeasureTheory.indicatorConstLp, MeasureTheory.norm_indicatorConstLp, BoundedContinuousFunction.toLp, ContinuousMap.toLp, MeasureTheory.Lp.coeFn_le, MeasureTheory.Lp.coeFn_tsum, MeasureTheory.Integrable.toL1, MeasureTheory.SimpleFunc.approxOn, DomMulAct.norm_smul_Lp, MeasureTheory.Lp.compMeasurePreserving_continuous]
  E1: auto
families: []
requires: [V13, V18.C01, V18.C04, V18.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lp spaces: the working API

### Overview

Section 2 of this chapter builds the space `MeasureTheory.Lp E p μ` of classes of functions and proves that it is complete. An element of this space is not a function. It is a class of functions modulo equality almost everywhere, stored as an element of the type `α →ₘ[μ] E` of Chapter 5. This choice makes the norm a true norm, but it makes simple objects harder to write. To use the indicator of a set as an element of $L^p$, a continuous function as an element of $L^p$, or a translate of an element of $L^p$, Mathlib needs a definition for each, with lemmas that relate it to the function it comes from.

This section is a guide to these definitions. It covers indicators and constants, continuous functions, the order on $L^p$ for real functions, series in $L^p$, the space $L^1$ as a space of integrable classes, the approximation of measurable functions by simple functions, and the action of a group on $L^p$ by composition. The section needs Sections 1 and 2 of this chapter, the measurable group actions of Chapter 1, the integrable functions of Chapter 5 and the continuous functions of Volume 13.

### The library around it

#### Indicators and constants

For a measurable set `s` of finite measure and a vector `c : E`, the element `MeasureTheory.indicatorConstLp p hs hμs c` of `Lp E p μ` is the class of the function $c \, \mathbf{1}_s$. The two proofs `hs : MeasurableSet s` and `hμs : μ s ≠ ⊤` are explicit arguments. They are needed because the indicator of a set of infinite measure is not in $L^p$ for $p < \infty$.

The lemma `MeasureTheory.norm_indicatorConstLp` computes the norm: `‖indicatorConstLp p hs hμs c‖ = ‖c‖ * μ.real s ^ (1 / p.toReal)` for $0 < p < \infty$. The version for $p = \infty$ is `MeasureTheory.norm_indicatorConstLp_top`. The lemma `MeasureTheory.indicatorConstLp_coeFn` says that the class has the function `s.indicator fun _ ↦ c` as a representative. Since an element of `Lp` is a class, this holds only almost everywhere. The lemmas `MeasureTheory.indicatorConstLp_coeFn_mem` and `MeasureTheory.indicatorConstLp_coeFn_notMem` give the value at almost every point inside and outside the set.

The map from sets to indicators is continuous for the measure of the symmetric difference. The lemma `MeasureTheory.tendsto_indicatorConstLp_set` says: if `μ (symmDiff (t b) s)` tends to zero, then the indicators of `t b` tend to the indicator of `s` in $L^p$, for $1 \le p < \infty$. Density arguments use this fact to move from sets to functions.

For a finite measure, `MeasureTheory.Lp.const` is the additive map that sends a vector to the class of the constant function. The linear and continuous linear versions are `MeasureTheory.Lp.constₗ` and `MeasureTheory.Lp.constL`. The lemma `MeasureTheory.Lp.norm_const` computes the norm.

The same file has two criteria for membership in $L^p$ on a topological space. `Continuous.memLp_of_hasCompactSupport` says that a continuous function with compact support is in $L^p$ for every measure that is finite on compact sets. `HasCompactSupport.memLp_of_bound` replaces continuity by a bound and measurability.

#### Continuous functions in Lp

On a topological measure space with a finite measure, a bounded continuous function is in $L^p$ for every $p$. The map `BoundedContinuousFunction.toLp p μ 𝕜` is the continuous linear map from bounded continuous functions to `Lp E p μ`. On a compact space, `ContinuousMap.toLp p μ 𝕜` does the same for all continuous functions. The field `𝕜` fixes the scalars for the linearity.

| Lean name | Statement |
|---|---|
| `BoundedContinuousFunction.coeFn_toLp` | the class has the function as a representative, almost everywhere |
| `BoundedContinuousFunction.toLp_norm_le` | the operator norm of `toLp` is bounded by a power of `μ univ` |
| `BoundedContinuousFunction.toLp_injective` | the map is injective when the measure is positive on open sets |
| `ContinuousMap.toLp_norm_eq_toLp_norm_coe` | the two maps agree on a compact space |
| `MeasureTheory.Lp.boundedContinuousFunction` | the subgroup of classes that have a bounded continuous representative |

The injectivity needs the class `MeasureTheory.Measure.IsOpenPosMeasure`. Without it, two different continuous functions can agree almost everywhere: for a Dirac measure at a point, all continuous functions with the same value at that point have the same class.

The density of these subspaces is in `Mathlib.MeasureTheory.Function.ContinuousMapDense`, which Section 2 describes. The file `Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving` uses this density. It proves `MeasureTheory.Lp.compMeasurePreserving_continuous`: the map $(g, f) \mapsto f \circ g$ is jointly continuous, where $g$ runs over the continuous measure preserving maps with the compact open topology and $f$ over $L^p$, for $1 \le p < \infty$. The lemmas `Filter.Tendsto.compMeasurePreservingLp` and `Continuous.compMeasurePreservingLp` are the forms for limits and continuous families.

#### Group actions on Lp

A group that acts on the space $\alpha$ acts on functions on $\alpha$ by composition: $(c \cdot f)(x) = f(c \cdot x)$. This is a right action. Mathlib turns it into a left action with the type `Mᵈᵐᵃ`, the domain action of `M`, which Section 4 of Chapter 1 also uses. For an element `c : M`, the element `DomMulAct.mk c` acts on functions on the left.

The file `Mathlib.MeasureTheory.Function.AEEqFun.DomAct` makes `Mᵈᵐᵃ` act on `α →ₘ[μ] β` when `M` acts measurably on `α`. The lemma `DomMulAct.mk_smul_mk_aeeqFun` computes the action on a class when the measure is invariant, with the class `MeasureTheory.SMulInvariantMeasure`. The file `Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic` restricts the action to `Lp E p μ` when `M` acts by measure preserving maps. The lemma `DomMulAct.mk_smul_toLp` computes `DomMulAct.mk c • MemLp.toLp f hf`, and `DomMulAct.norm_smul_Lp` says that the action is isometric. The additive versions have the prefix `DomAddAct` and use `+ᵥ` for translations, such as the translations of $\mathbb{R}^n$.

The file `Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous` proves the instance `MeasureTheory.Lp.instContinuousSMulDomMulAct`: for a topological group that acts continuously and a locally finite measure with enough regularity, the action on $L^p$ is jointly continuous for $p < \infty$. For $\mathbb{R}^n$ this says that $\|f(\cdot + h) - f\|_p \to 0$ as $h \to 0$, the continuity of translation in $L^p$.

#### Order

For real functions, the space $L^p$ is a lattice. The file `Mathlib.MeasureTheory.Function.LpOrder` gives the order and the lattice operations. The lemma `MeasureTheory.Lp.coeFn_le` says that `f ≤ g` in $L^p$ if and only if the representatives satisfy `↑f ≤ᵐ[μ] ↑g`. The lemmas `MeasureTheory.Lp.coeFn_sup`, `MeasureTheory.Lp.coeFn_inf` and `MeasureTheory.Lp.coeFn_abs` compute the representatives of `f ⊔ g`, `f ⊓ g` and `|f|`. The instance `MeasureTheory.Lp.instHasSolidNorm` says that $|f| \le |g|$ implies $\|f\| \le \|g\|$, for $1 \le p$. The predicate versions `MeasureTheory.MemLp.sup`, `MeasureTheory.MemLp.inf` and `MeasureTheory.MemLp.abs` work on functions.

#### Series in Lp

The file `Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum` treats series that converge absolutely in $L^p$. The lemma `MeasureTheory.Lp.coeFn_tsum` says: if `∑' n, ‖f n‖ₑ ≠ ⊤`, then the sum in $L^p$ is represented almost everywhere by the pointwise sum of the representatives. The lemma `MeasureTheory.Lp.hasSum_coeFn_tsum` says that the pointwise series converges almost everywhere. This is the step in the proof of the theorem of Riesz and Fischer that extracts an almost everywhere convergent subsequence.

The file `Mathlib.MeasureTheory.Function.LpSpace.CompleteOfCompleteLp` proves the converse direction of completeness: `MeasureTheory.completeSpace_of_completeSpace_Lp` says that if `Lp E p μ` is complete and nontrivial, then `E` is complete.

#### The space L1

The file `Mathlib.MeasureTheory.Function.L1Space.AEEqFun` relates the space `Lp β 1 μ` to integrable functions. The predicate `MeasureTheory.AEEqFun.Integrable` says that a class is integrable, and `MeasureTheory.AEEqFun.integrable_iff_mem_L1` says that this is membership in $L^1$. For an integrable function `f` with proof `hf`, the element `MeasureTheory.Integrable.toL1 f hf` is its class in $L^1$. The lemma `MeasureTheory.Integrable.toL1_eq_toL1_iff` says that two functions have the same class if and only if they are equal almost everywhere. The lemma `MeasureTheory.L1.norm_def` says that the norm is `(∫⁻ a, ‖↑↑f a‖ₑ ∂μ).toReal`, and `MeasureTheory.Integrable.norm_toL1` computes the norm of `toL1`. The Bochner integral of Chapter 5 is first defined on this space.

#### Approximation by simple functions

The file `Mathlib.MeasureTheory.Function.SimpleFuncDense` builds a sequence of simple functions that converges to a measurable function. The construction is `MeasureTheory.SimpleFunc.approxOn f hf s y₀ h₀ n`. It needs a separable set `s` that contains the values of `f` and a point `y₀ ∈ s`. At step `n`, it sends `x` to the point of $\{y_0, z_0, \ldots, z_n\}$ closest to `f x`, where $z_k$ is a dense sequence in `s`. The function `MeasureTheory.SimpleFunc.nearestPt` is the map to the closest point. The lemma `MeasureTheory.SimpleFunc.tendsto_approxOn` gives pointwise convergence when `f x` is in the closure of `s`. The lemma `MeasureTheory.SimpleFunc.edist_approxOn_le` gives the bound that makes dominated convergence work: the distance from the approximation to `f x` is at most the distance from `y₀` to `f x`, for every `n`. The density of simple functions in $L^p$, in Section 2, rests on these two facts.

#### Common errors

1. Expecting `indicatorConstLp p hs hμs c` to be equal to the indicator function at every point. It is a class, and its representative agrees with the indicator only almost everywhere. Use `MeasureTheory.indicatorConstLp_coeFn`.
2. Writing the action of `c` on an element of $L^p$ as `c • f` with `c : M`. The action is by `DomMulAct.mk c`, and the action of `M` itself, if one exists, acts on the values.
3. Using `BoundedContinuousFunction.toLp_injective` for a measure that is not positive on open sets. The map is not injective in this case.

### Exercises

1. (A) Compute the norm of `indicatorConstLp 2 hs hμs (3 : ℝ)` in `Lp ℝ 2 μ` when `μ s = 4`.
2. (A) Show that for real `f` and `g` in $L^p$, `f ⊔ g` has the representative `fun x ↦ max (f x) (g x)` almost everywhere.
3. (B) Show that the indicators of the sets $[0, 1/n]$ tend to zero in $L^1(\mathbb{R})$.
4. (B) Show that a measurable function with values in a separable normed space is the pointwise limit of simple functions, with `MeasureTheory.SimpleFunc.approxOn`.
5. (B) Show that for $f \in L^1(\mathbb{R})$ the map $h \mapsto f(\cdot + h)$ is continuous into $L^1(\mathbb{R})$.
6. (C) Prove that $L^\infty([0, 1])$ is not separable, with the indicators of the intervals $[0, t]$.

### Reference

<?reference?>
