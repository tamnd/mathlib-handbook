---
title: Extending set functions to integrable functions
kind: api
modules:
  - Mathlib.MeasureTheory.Integral.FinMeasAdditive
  - Mathlib.MeasureTheory.Integral.SetToL1
  - Mathlib.MeasureTheory.Integral.SetToL1.SimpleFunc
  - Mathlib.MeasureTheory.Integral.SetToL1.L1
  - Mathlib.MeasureTheory.Integral.SetToL1.Function
  - Mathlib.MeasureTheory.Integral.SetToL1.ChangeMeasure
  - Mathlib.MeasureTheory.Integral.SetToL1.DominatedConvergence
explains:
  E2: [MeasureTheory.FinMeasAdditive, MeasureTheory.DominatedFinMeasAdditive, MeasureTheory.FinMeasAdditive.map_iUnion_fin_meas_set_eq_sum, MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm, MeasureTheory.L1.setToL1_indicatorConstLp, MeasureTheory.L1.setToL1_unique, MeasureTheory.setToFun_eq, MeasureTheory.setToFun_indicator_const, MeasureTheory.setToFun_congr_measure, MeasureTheory.tendsto_setToFun_of_dominated_convergence]
  E1: auto
families: []
requires: [V13, V16, V18.C02, V18.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Extending set functions to integrable functions

### Overview

The Bochner integral of Section 2 starts from one value on each set: the integral of the indicator of $s$ times a vector $x$ is $\mu(s) x$. Linearity fixes the integral of each simple function, and continuity in the $L^1$ norm fixes it on the whole space $L^1$. Mathlib does this construction once, for a general family of linear maps $T(s)$ in place of $x \mapsto \mu(s) x$, and the Bochner integral is one instance. The conditional expectation of an integrable function is another instance in the library.

The input is a function $T$ from sets to continuous linear maps $E \to F$ with two properties. It is additive on disjoint measurable sets of finite measure, and it is dominated: $\|T(s)\| \le C \mu(s)$. The output is a function `MeasureTheory.setToFun μ T hT` from functions $\alpha \to E$ to $F$, with the value $T(s)x$ on the indicator of $s$ times $x$. It is linear, continuous in $L^1$, and it satisfies a dominated convergence theorem. This section describes the steps of the construction and the main results. Most users meet these names only through the proofs of the integral lemmas, and the section helps to read those proofs.

### The library around it

#### Additive and dominated set functions

The file `Mathlib.MeasureTheory.Integral.FinMeasAdditive` has the hypotheses. A function $T$ from sets to an additive monoid is `MeasureTheory.FinMeasAdditive μ T` when $T(s \cup t) = T(s) + T(t)$ for disjoint measurable sets $s, t$ of finite measure. The extension to finite unions is `MeasureTheory.FinMeasAdditive.map_iUnion_fin_meas_set_eq_sum`, under the extra hypothesis $T(\emptyset) = 0$. The predicate `MeasureTheory.DominatedFinMeasAdditive μ T C` adds the bound $\|T(s)\| \le C \mu(s)$ for each measurable set of finite measure, where $\mu(s)$ is the real value `μ.real s`.

The class is stable under the natural operations. Sums of dominated maps are dominated, `MeasureTheory.DominatedFinMeasAdditive.add`, with the sum of the constants. A dominated map for $\mu$ is dominated for each larger measure, `MeasureTheory.DominatedFinMeasAdditive.of_measure_le`. The Bochner integral uses `MeasureTheory.weightedSMul μ`, the map $s \mapsto (x \mapsto \mu(s) x)$, and `MeasureTheory.dominatedFinMeasAdditive_weightedSMul` gives the constant $1$.

#### Simple functions

For a simple function $f$, `MeasureTheory.SimpleFunc.setToSimpleFunc T f` is the finite sum

$$\sum_{x \in \operatorname{range} f} T(f^{-1}(\{x\}))\, x.$$

This sum is linear in $f$ when $T$ is additive, `MeasureTheory.SimpleFunc.setToSimpleFunc_add`, and it is linear in $T$, `MeasureTheory.SimpleFunc.setToSimpleFunc_add_left`. Its value on an indicator is $T(s)x$, `MeasureTheory.SimpleFunc.setToSimpleFunc_indicator`. The norm bound `MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm` gives

$$\|T f\| \le C \sum_{x} \mu(f^{-1}(\{x\})) \|x\|,$$

and the right side is $C$ times the $L^1$ norm of $f$. This is the estimate that makes the extension by continuity possible. For an order on $E$ and $F$, a $T$ with nonnegative values on nonnegative vectors is monotone, `MeasureTheory.SimpleFunc.setToSimpleFunc_mono`.

#### The extension to L1

The file `Mathlib.MeasureTheory.Integral.SetToL1.SimpleFunc` moves the sum to the subspace of simple functions in $L^1$, the type `α →₁ₛ[μ] E`. The map `MeasureTheory.L1.SimpleFunc.setToL1S T` is the sum on a representative, and `MeasureTheory.L1.SimpleFunc.setToL1SCLM α E μ hT` is the same map as a continuous linear map, with norm at most $C$, `MeasureTheory.L1.SimpleFunc.norm_setToL1SCLM_le`.

The file `Mathlib.MeasureTheory.Integral.SetToL1.L1` extends this map to all of $L^1$. Simple functions are dense in $L^1$, and $F$ is complete, so the continuous linear map extends in a unique way. The result is `MeasureTheory.L1.setToL1 hT`, a term of `Lp E 1 μ →L[ℝ] F`. Its value on the class of an indicator is $T(s)x$, `MeasureTheory.L1.setToL1_indicatorConstLp`. Uniqueness is `MeasureTheory.L1.setToL1_unique`: a continuous linear map that agrees with the sum on simple functions is `MeasureTheory.L1.setToL1 hT`. It is Lipschitz with constant $C$, `MeasureTheory.L1.setToL1_lipschitzWith`, and its norm is at most $C$, `MeasureTheory.L1.norm_setToL1_le`.

#### The extension to functions

The file `Mathlib.MeasureTheory.Integral.SetToL1.Function` defines `MeasureTheory.setToFun μ T hT f`. For an integrable $f$, it is the value of `MeasureTheory.L1.setToL1 hT` on the class of $f$, `MeasureTheory.setToFun_eq`. For a function that is not integrable, the value is $0$, `MeasureTheory.setToFun_undef`. This is the same convention as for the Bochner integral, and for the same reason: a total function is easier to use than a function with a proof argument.

The basic rules have the names of the integral rules. The value on an indicator is `MeasureTheory.setToFun_indicator_const`. The map is additive in $f$, `MeasureTheory.setToFun_add`, homogeneous, `MeasureTheory.setToFun_smul`, and it depends only on the class of $f$ almost everywhere, `MeasureTheory.setToFun_congr_ae`. For an ordered $F$, it is monotone, `MeasureTheory.setToFun_mono`. The link to the Bochner integral is `MeasureTheory.integral_eq_setToFun`: the integral is `MeasureTheory.setToFun` for `MeasureTheory.weightedSMul μ`.

A typical proof in the file of the Bochner integral is short for this reason. To prove $\int (f + g) = \int f + \int g$, rewrite both sides with `MeasureTheory.integral_eq_setToFun` and apply `MeasureTheory.setToFun_add`. The same pattern gives the rules for scalar multiples, for almost everywhere equal functions, for monotonicity and for limits. A user who defines a new integral, for example an integral against an operator valued set function, gets all these rules at once by giving $T$ and a proof of `MeasureTheory.DominatedFinMeasAdditive`. The constant $C$ appears only in the norm bounds, and it can be any real number for which the bound holds.

#### Change of measure and dominated convergence

The file `Mathlib.MeasureTheory.Integral.SetToL1.ChangeMeasure` compares the extensions for two measures. If $\mu \le c \mu'$ and $\mu' \le c' \mu$ with finite constants, then the two extensions of the same $T$ agree, `MeasureTheory.setToFun_congr_measure`. For a sum of measures and a sum of maps, `MeasureTheory.setToFun_add_measure` gives the sum of the extensions. The lemma `MeasureTheory.continuous_L1_toL1` is the technical tool: the map from $L^1(\mu)$ to $L^1(\mu')$ is continuous when $\mu' \le c' \mu$.

The file `Mathlib.MeasureTheory.Integral.SetToL1.DominatedConvergence` proves the dominated convergence theorem for the extension. Under the usual hypotheses, a sequence $f_n$ of measurable functions bounded by an integrable function and converging almost everywhere to $f$, `MeasureTheory.tendsto_setToFun_of_dominated_convergence` gives $T f_n \to T f$. The proof reduces to the theorem in $L^1$ and uses that `MeasureTheory.L1.setToL1 hT` is continuous. The file also has the continuity of parametric extensions, `MeasureTheory.continuous_setToFun_of_dominated`, and the series rule `MeasureTheory.setToFun_tsum`. The norm bound on functions is `MeasureTheory.norm_setToFun_le_mul_norm`.

#### Common errors

1. Expecting a proof of additivity on all disjoint sets. `MeasureTheory.FinMeasAdditive` asks for additivity only on measurable sets of finite measure, and a map $T$ can have any value on sets of infinite measure. The construction never uses those values.
2. Using a codomain $F$ that is not complete. The extension from simple functions to $L^1$ needs `CompleteSpace F`, and lemmas such as `MeasureTheory.setToFun_eq` have it as a hypothesis. Without it, `MeasureTheory.setToFun` is $0$ on every function.
3. Proving a property of the integral by hand when the general lemma exists. Most properties of `MeasureTheory.integral` come from a lemma on `MeasureTheory.setToFun` with `MeasureTheory.integral_eq_setToFun`. A new integral like construction should also go through `MeasureTheory.setToFun` to get these lemmas.

### Exercises

1. (A) Show that $T(s) = \mu(s \cap A) \cdot \mathrm{id}$ is dominated additive with constant $1$, and identify `MeasureTheory.setToFun μ T hT f` with the integral of $f$ over $A$.
2. (A) Compute `MeasureTheory.SimpleFunc.setToSimpleFunc T f` for the simple function $f = 2 \cdot \mathbf{1}_{[0,1]} + 5 \cdot \mathbf{1}_{(1,3]}$ and $T = $ `MeasureTheory.weightedSMul volume`.
3. (B) Show that if $T$ and $T'$ are dominated additive with constants $C$ and $C'$, then `MeasureTheory.setToFun` for $T + T'$ is the sum of the two extensions.
4. (B) Let $\nu$ be a finite measure with $\nu \le \mu$. Show that $T(s) = \nu(s) \cdot \mathrm{id}$ is dominated additive for $\mu$, and that `MeasureTheory.setToFun μ T hT f` is the $\nu$ integral of each $\mu$ integrable $f$.
5. (B) Derive the dominated convergence theorem for the Bochner integral from `MeasureTheory.tendsto_setToFun_of_dominated_convergence`.
6. (C) Prove `MeasureTheory.L1.setToL1_unique` from the density of simple functions in $L^1$.

### Reference

<?reference?>
