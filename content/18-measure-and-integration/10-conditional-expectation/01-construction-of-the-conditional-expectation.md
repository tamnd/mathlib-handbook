---
title: Construction of the conditional expectation
kind: api
modules:
  - Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
  - Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1
  - Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
  - Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
  - Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
  - Mathlib.MeasureTheory.Function.AEEqOfIntegral
  - Mathlib.MeasureTheory.Function.AEEqOfLIntegral
explains:
  E2: [MeasureTheory.condExp, MeasureTheory.setIntegral_condExp, MeasureTheory.integral_condExp, MeasureTheory.condExp_condExp_of_le, MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq, MeasureTheory.condExpL2, MeasureTheory.condExpL1CLM, MeasureTheory.lpMeas, MeasureTheory.lpMeasToLpTrimLie, MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite]
  E1: auto
families: []
requires: [V18.C02, V18.C04, V18.C05, V18.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Construction of the conditional expectation

### Overview

Let $(\alpha, m_0, \mu)$ be a measure space and let $m \le m_0$ be a smaller σ-algebra. The σ-algebra $m$ describes partial information: an $m$-measurable function depends only on what $m$ can see. The conditional expectation of an integrable function $f$ with respect to $m$ is the $m$-measurable function $g$ with
$$\int_s g \, d\mu = \int_s f \, d\mu \quad \text{for every } m\text{-measurable set } s.$$
It is the best guess of $f$ from the information in $m$. Probability theory uses it for martingales, conditional laws and Markov processes.

The function $g$ is unique up to a null set. Its existence is a theorem. The classical proof uses the theorem of Radon and Nikodym. Mathlib uses a different proof, which works for functions with values in any complete normed space. It defines the conditional expectation first on $L^2$, as an orthogonal projection, then extends it to $L^1$ by continuity, and finally to functions. This section explains the three steps, the final definition `MeasureTheory.condExp` and the uniqueness lemmas that most proofs use.

The section needs the measures of Chapter 2, the integrals of Chapters 4 and 5 and the spaces $L^p$ of Chapter 7. Section 2 of this chapter gives the properties of the conditional expectation, and Volume 20 builds martingales on it.

### The library around it

#### The definition and the notation

The function `MeasureTheory.condExp m μ f` has the notation `μ[f | m]` after `open MeasureTheory`. The definition has three cases.

1. If $m \le m_0$, the restriction of $\mu$ to $m$ is σ-finite and $f$ is integrable, then the value is $f$ itself when $f$ is $m$-strongly measurable. Otherwise it is a strongly measurable representative of the class in $L^1$ that the construction gives.
2. If $m \not\le m_0$, the value is $0$, by `MeasureTheory.condExp_of_not_le`.
3. If the restriction of $\mu$ to $m$ is not σ-finite, or $f$ is not integrable, the value is $0$, by `MeasureTheory.condExp_of_not_sigmaFinite` and `MeasureTheory.condExp_of_not_integrable`.

The restriction of $\mu$ to $m$ is the measure `μ.trim hm` of Chapter 2, where `hm : m ≤ m₀`. Many lemmas take the class `SigmaFinite (μ.trim hm)` as an instance argument. On a finite measure space the instance is automatic.

The junk value $0$ makes the function total. It has a cost: the lemmas that give the defining property need the hypotheses again. The first case gives a function that is equal to $f$ when $f$ is already $m$-strongly measurable, and not only almost everywhere equal. The lemma `MeasureTheory.condExp_of_stronglyMeasurable` states this equality.

#### The defining property

The main lemmas are these.

| Lean name | Statement |
|---|---|
| `MeasureTheory.stronglyMeasurable_condExp` | `μ[f \| m]` is $m$-strongly measurable |
| `MeasureTheory.integrable_condExp` | `μ[f \| m]` is integrable |
| `MeasureTheory.setIntegral_condExp` | $\int_s \mu[f \mid m] \, d\mu = \int_s f \, d\mu$ for $s$ in $m$ and $f$ integrable |
| `MeasureTheory.integral_condExp` | $\int \mu[f \mid m] \, d\mu = \int f \, d\mu$ |
| `MeasureTheory.condExp_condExp_of_le` | $\mu[\mu[f \mid m_2] \mid m_1] = \mu[f \mid m_1]$ a.e. for $m_1 \le m_2$ |
| `MeasureTheory.condExp_bot` | for a probability measure, $\mu[f \mid \bot]$ is the constant $\int f \, d\mu$ |

The first two lemmas hold with no hypothesis, since the junk value $0$ is measurable and integrable. The third lemma needs `hm`, the σ-finite instance, the integrability of $f$ and the measurability of $s$ for $m$. The fifth lemma is the tower property. The coarser σ-algebra wins.

Linearity holds almost everywhere. The lemma `MeasureTheory.condExp_add` needs both functions integrable, and `MeasureTheory.condExp_smul` needs no hypothesis. The lemma `MeasureTheory.condExp_zero` is an equality. The lemma `MeasureTheory.condExp_const` says that the conditional expectation of a constant is the constant, on a finite measure space. The lemma `MeasureTheory.condExp_congr_ae` says that functions equal almost everywhere have conditional expectations equal almost everywhere. The lemma `MeasureTheory.condExp_mono` is monotonicity, for functions with values in an ordered space.

#### Uniqueness

The usual way to compute a conditional expectation is to guess it and check the defining property. The lemma `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq` does this. It takes a function $g$ that is $m$-strongly measurable up to a null set and has
$$\int_s g \, d\mu = \int_s f \, d\mu$$
for every $m$-measurable set $s$ of finite measure. It also needs $g$ integrable on those sets. Then $g = \mu[f \mid m]$ almost everywhere.

The proof rests on lemmas of the file `Mathlib.MeasureTheory.Function.AEEqOfIntegral`. They say that a function is determined by its integrals over measurable sets.

| Lean name | Statement |
|---|---|
| `MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite` | $\mu$ σ-finite, $f$ and $g$ integrable on sets of finite measure with equal integrals there: $f = g$ a.e. |
| `MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq` | the same for integrable $f$ and $g$ and any $\mu$ |
| `MeasureTheory.ae_le_of_forall_setIntegral_le` | inequalities of integrals give $f \le g$ a.e. for real functions |
| `MeasureTheory.ae_eq_zero_of_forall_dual` | a function with values in a normed space is zero a.e. when every continuous linear form of it is zero a.e. |
| `MeasureTheory.ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero` | on a locally compact space, integrals over compact sets suffice |

The lemma `MeasureTheory.ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim` is the form for a sub-σ-algebra. It only tests sets of $m$, and it needs $f$ finitely strongly measurable for `μ.trim hm`.

The file `Mathlib.MeasureTheory.Function.AEEqOfLIntegral` has the same results for functions with values in $[0, \infty]$. The lemma `MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite` is the version for lower integrals. The lemma `MeasureTheory.withDensity_eq_iff` says that two densities give the same measure if and only if they are equal almost everywhere. The lemma `MeasureTheory.lintegral_eq_lintegral_of_isPiSystem` reduces the test to a π-system that generates the σ-algebra.

#### Step one: the orthogonal projection on $L^2$

The space `MeasureTheory.lpMeas F 𝕜 m p μ` is the submodule of `Lp F p μ` of classes that have an $m$-strongly measurable representative. The lemma `MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable` states the membership condition. The linear isometry `MeasureTheory.lpMeasToLpTrimLie` identifies this submodule with `Lp F p (μ.trim hm)`. Since that space is complete, so is the submodule, and `MeasureTheory.isComplete_aestronglyMeasurable` states this. This is where the seminorms of `μ.trim hm` from Chapter 7 enter.

A closed submodule of a Hilbert space has an orthogonal projection. The map `MeasureTheory.condExpL2 E 𝕜 hm` is the orthogonal projection of `Lp E 2 μ` onto `lpMeas E 𝕜 m 2 μ`. It is a continuous linear map of norm at most one. The lemma `MeasureTheory.inner_condExpL2_left_eq_right` says that it is self adjoint. The lemma `MeasureTheory.condExpL2_indicator_of_measurable` says that it fixes the indicator of a set in $m$.

#### Step two: the extension to $L^1$

The functions in $L^2$ are not all integrable on a space of infinite measure, so the extension to $L^1$ goes through indicators. For a set $s$ of finite measure and a vector $c$, `MeasureTheory.condExpIndSMul hm hs hμs c` is the projection of the indicator of $s$ with value $c$. The function `MeasureTheory.condExpInd` collects these into a map on sets that is additive on disjoint sets and bounded by the measure. Chapter 5 builds the Bochner integral from such a map. The same machine gives a continuous linear map
$$\texttt{condExpL1CLM} : L^1(\mu; F) \to L^1(\mu; F).$$
This is `MeasureTheory.condExpL1CLM F hm μ`. The lemma `MeasureTheory.setIntegral_condExpL1CLM` gives the defining property on $L^1$, and `MeasureTheory.condExpL1CLM_lpMeas` says that it fixes the classes with an $m$-measurable representative.

The function `MeasureTheory.condExpL1 hm μ f` applies this map to the class of $f$ when $f$ is integrable, and gives $0$ otherwise. The lemma `MeasureTheory.condExpL1_eq` states the first case. The lemma `MeasureTheory.condExp_ae_eq_condExpL1` says that the final function `condExp` is a representative of this class.

#### Step three: limits and continuity

The continuity of `condExpL1CLM` gives limit theorems. The lemma `MeasureTheory.tendsto_condExpL1_of_dominated_convergence` is a dominated convergence theorem: if $f_n \to f$ almost everywhere with an integrable bound, the classes `condExpL1 hm μ (f n)` converge in $L^1$ to the class for $f$. The lemma `MeasureTheory.tendsto_condExp_unique` identifies the limit of conditional expectations. The lemma `MeasureTheory.condExp_tsum` treats series with $\sum_i \int \|f_i\| \, d\mu < \infty$. The lemma `ContinuousLinearMap.comp_condExp_comm` says that a continuous linear map commutes with the conditional expectation.

For induction on $L^p$, `MeasureTheory.Lp.induction_stronglyMeasurable` proves a property for all classes of $L^p$ with $p < \infty$ that have an $m$-strongly measurable representative, from indicators of sets in $m$, sums and closedness. This is the standard pattern for statements about $m$-measurable functions in $L^p$.

#### Common errors

1. Applying `MeasureTheory.setIntegral_condExp` to a set that is only measurable for $m_0$. The set must be measurable for $m$, and the proof term is `MeasurableSet[m] s`.
2. Forgetting the σ-finite instance. On an infinite measure space the restriction to $m$ may fail to be σ-finite, and then `μ[f | m]` is $0$. Supply `SigmaFinite (μ.trim hm)` with `haveI`.
3. Expecting equalities. Most lemmas give equality almost everywhere, written `=ᵐ[μ]`. Use `Filter.EventuallyEq.trans` to chain them.

### Exercises

1. (A) Show that $\mu[f \mid m_0] = f$ for an integrable $f$ that is strongly measurable for $m_0$.
2. (A) Show that $\int \mu[f \mid m] \, d\mu = \int f \, d\mu$ for an integrable real function on a probability space.
3. (B) Let $m$ be generated by a set $s$ with $0 < \mu(s) < 1$. Compute $\mu[f \mid m]$ on a probability space.
4. (B) Show that $\mu[\mu[f \mid m] \mid m] = \mu[f \mid m]$ almost everywhere.
5. (B) Show that two integrable real functions with equal integrals over every measurable set are equal almost everywhere.
6. (C) Prove that `condExpL2` restricted to classes in $L^1 \cap L^2$ agrees almost everywhere with `condExp`.

### Reference

<?reference?>
