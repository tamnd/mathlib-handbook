---
title: Properties of the conditional expectation
kind: api
modules:
  - Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
  - Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
  - Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
  - Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
  - Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner
  - Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
  - Mathlib.MeasureTheory.Function.ConditionalLExpectation
explains:
  E2: [MeasureTheory.condExp_indicator, MeasureTheory.condExp_mul_of_stronglyMeasurable_left, MeasureTheory.condExp_stronglyMeasurable_mul_of_bound, MeasureTheory.eLpNorm_condExp_le_eLpNorm, ConvexOn.map_condExp_le, Convex.condExp_mem, MeasureTheory.Integrable.uniformIntegrable_condExp, MeasureTheory.condLExp, MeasureTheory.setLIntegral_condLExp, MeasureTheory.rnDeriv_ae_eq_condExp]
  E1: auto
families: []
requires: [V18.C04, V18.C05, V18.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Properties of the conditional expectation

### Overview

Section 1 of this chapter defines the conditional expectation `μ[f | m]` and proves its defining property. Proofs in probability use a short list of further rules. A factor that is measurable for $m$ comes out of the conditional expectation. The conditional expectation contracts every $L^p$ norm. It satisfies the inequality of Jensen for convex functions. It agrees with the density of a restricted measure. This section explains these rules.

The section also explains the conditional expectation `MeasureTheory.condLExp` of functions with values in $[0, \infty]$. It needs no integrability, since the lower integral of a nonnegative function always exists. The section needs the integrals of Chapters 4 and 5 and the spaces $L^p$ of Chapter 7.

### The library around it

#### Indicators and restrictions

The conditional expectation is local on sets of $m$. The lemma `MeasureTheory.condExp_indicator` says
$$\mu[\mathbf{1}_s f \mid m] = \mathbf{1}_s \, \mu[f \mid m] \quad \text{a.e.}$$
for an integrable $f$ and a set $s$ that is measurable for $m$. The lemma `MeasureTheory.condExp_restrict_ae_eq_restrict` says that the conditional expectation for the restricted measure `μ.restrict s` agrees on $s$ with the conditional expectation for $\mu$. The lemma `MeasureTheory.condExp_ae_eq_restrict_zero` says that if $f$ is zero almost everywhere on $s$, then so is `μ[f | m]`. The lemma `MeasureTheory.condExp_ae_eq_restrict_of_measurableSpace_eq_on` compares two σ-algebras that have the same traces on $s$.

#### Pulling out what is known

The rule "take out what is known" says
$$\mu[f g \mid m] = f \, \mu[g \mid m] \quad \text{a.e.}$$
when $f$ is measurable for $m$. The file `Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut` has several forms.

| Lean name | Hypotheses |
|---|---|
| `MeasureTheory.condExp_mul_of_stronglyMeasurable_left` | $f$ strongly measurable for $m$, $f g$ and $g$ integrable |
| `MeasureTheory.condExp_mul_of_aestronglyMeasurable_left` | the same with $f$ almost everywhere strongly measurable for $m$ |
| `MeasureTheory.condExp_mul_of_stronglyMeasurable_right` | the known factor on the right |
| `MeasureTheory.condExp_stronglyMeasurable_mul_of_bound` | $\mu$ finite, $f$ bounded and strongly measurable for $m$, $g$ integrable |
| `MeasureTheory.condExp_smul_of_aestronglyMeasurable_left` | a real factor $f$ and a vector function $g$ |
| `MeasureTheory.condExp_bilin_of_stronglyMeasurable_left` | a continuous bilinear map in place of the product |

The form with a bound needs only the integrability of $g$, since a bounded $f$ keeps $f g$ integrable. The general forms need the integrability of the product as a hypothesis. The proof starts from simple functions, by `MeasureTheory.condExp_stronglyMeasurable_simpleFunc_mul`, and passes to the limit.

#### Order and norms

For real functions, the conditional expectation preserves the order. The lemma `MeasureTheory.condExp_nonneg` says that it maps nonnegative functions to functions that are nonnegative almost everywhere. Section 1 gives `MeasureTheory.condExp_mono`. The file `Mathlib.MeasureTheory.Function.ConditionalExpectation.Real` collects the estimates that follow.

| Lean name | Statement |
|---|---|
| `MeasureTheory.abs_condExp_ae_le_condExp_abs` | $\lvert \mu[f \mid m] \rvert \le \mu[\lvert f \rvert \mid m]$ a.e. |
| `MeasureTheory.integral_norm_condExp_le` | $\int \lVert \mu[f \mid m] \rVert \, d\mu \le \int \lVert f \rVert \, d\mu$ |
| `MeasureTheory.setIntegral_abs_condExp_le` | the same over a set of $m$ |
| `MeasureTheory.eLpNorm_condExp_le_eLpNorm` | $\lVert \mu[f \mid m] \rVert_p \le \lVert f \rVert_p$ for $p \ge 1$ |
| `MeasureTheory.MemLp.condExp` | $f \in L^p$ gives $\mu[f \mid m] \in L^p$ for $p \ge 1$ |
| `MeasureTheory.ae_bdd_condExp_of_ae_bdd` | $\lvert f \rvert \le R$ a.e. gives $\lvert \mu[f \mid m] \rvert \le R$ a.e. |
| `MeasureTheory.MemLp.essSup_norm_condExp_le_essSup_norm` | the essential supremum does not grow |

The lemma `MeasureTheory.eLpNorm_one_condExp_le_eLpNorm` is the case $p = 1$. It is the base of the others. The lemma `MeasureTheory.MemLp.lpNorm_condExp_le_lpNorm` is the form with the real valued norm `lpNorm`.

A family of conditional expectations of one function is uniformly integrable. The lemma `MeasureTheory.Integrable.uniformIntegrable_condExp` states this for a finite measure, any family of sub-σ-algebras and $p = 1$. Together with the theorem of Vitali of Chapter 7, it gives the convergence in $L^1$ of the martingales $\mu[g \mid \mathcal{F}_n]$ of Volume 20.

#### The inequality of Jensen

Let $\varphi$ be convex. The conditional inequality of Jensen says
$$\varphi(\mu[f \mid m]) \le \mu[\varphi \circ f \mid m] \quad \text{a.e.}$$
The file `Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen` has it in several forms. The lemma `ConvexOn.map_condExp_le` takes $\varphi$ convex and lower semicontinuous on a closed set $s$, with $f \in s$ almost everywhere, and $f$ and $\varphi \circ f$ integrable. The lemma `ConvexOn.map_condExp_le_univ` is the case $s = E$. The lemma `ConvexOn.map_condExp_le_of_finiteDimensional` drops the semicontinuity in finite dimension, where every convex function on the whole space is continuous. The lemmas `ConcaveOn.condExp_map_le` and `ConcaveOn.condExp_map_le_univ` reverse the inequality for concave functions.

Two special cases have their own names. The lemma `norm_condExp_le` is the case $\varphi = \lVert \cdot \rVert$. The lemma `Integrable.norm_condExp_rpow_le` is the case $\varphi = \lVert \cdot \rVert^p$ with $p \ge 1$. The lemma `Convex.condExp_mem` is a related fact: if $f$ takes values in a closed convex set almost everywhere, so does `μ[f | m]`.

#### The density of a restricted measure

The classical construction of the conditional expectation uses the theorem of Radon and Nikodym. Mathlib proves that the two constructions agree. The lemma `MeasureTheory.rnDeriv_ae_eq_condExp` says that for an integrable real $f$, the density of the signed measure $f \mu$ restricted to $m$ with respect to $\mu$ restricted to $m$ is `μ[f | m]` almost everywhere.

The file `Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym` goes the other way. For finite $\mu$ with $\mu \ll \nu$, the lemma `MeasureTheory.rnDeriv_trim` says that the density of `μ.trim hm` with respect to `ν.trim hm` is the conditional expectation of the density $d\mu / d\nu$. The lemma `MeasureTheory.rnDeriv_map` is the version for the image measures under a measurable map $g$. There the sub-σ-algebra is the one that $g$ generates.

#### The conditional expectation of nonnegative functions

The function `MeasureTheory.condLExp m P X` has the notation `P⁻[X | m]` after `open MeasureTheory`. It takes $X : \Omega \to [0, \infty]$. If $m \le m_0$ and `P.trim hm` is σ-finite, its value is $X$ when $X$ is measurable for $m$, and otherwise the density of `(P.withDensity X).trim hm` with respect to `P.trim hm`. In the other cases its value is $0$.

| Lean name | Statement |
|---|---|
| `MeasureTheory.setLIntegral_condLExp` | $\int^{-}_s P^{-}[X \mid m] \, dP = \int^{-}_s X \, dP$ for $s$ in $m$ |
| `MeasureTheory.lintegral_condLExp` | the same over the whole space |
| `MeasureTheory.ae_eq_condLExp` | an $m$-measurable $Y$ with the same integrals over sets of $m$ equals `P⁻[X \| m]` a.e. |
| `MeasureTheory.condLExp_eq_self` | `P⁻[X \| m] = X` for $X$ measurable for $m$ |
| `MeasureTheory.condLExp_mono` | $X \le Y$ a.e. gives the same for the conditional expectations |
| `MeasureTheory.condLExp_tsum` | the conditional expectation of a series is the series of the conditional expectations |
| `MeasureTheory.condLExp_bot` | for a probability measure, `P⁻[X \| ⊥]` is the constant $\int^{-} X \, dP$ |
| `MeasureTheory.condLExp_ne_top` | a finite lower integral gives a finite conditional expectation a.e. |

The series lemma has no summability hypothesis. This is the main advantage of the nonnegative version. Additivity is `MeasureTheory.condLExp_add_left`, with one function almost everywhere measurable.

The file `Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner` relates the two versions. The lemma `MeasureTheory.toReal_condLExp` says that the real part of `μ⁻[f | m]` is the conditional expectation of the real part of $f$, when $\int^{-} f \, d\mu < \infty$. The lemma `MeasureTheory.condLExp_ofReal` says the converse for an integrable nonnegative real $f$.

#### Common errors

1. Pulling out a factor that is only measurable for $m_0$. The rule needs the factor measurable for $m$. The hypothesis is `StronglyMeasurable[m] f`, not `StronglyMeasurable f`.
2. Omitting the integrability of the product. The general lemmas need `Integrable (f * g) μ`. If $f$ is bounded, use `MeasureTheory.condExp_stronglyMeasurable_mul_of_bound` instead.
3. Using the real conditional expectation for a series of nonnegative terms. The lemma for series of real functions needs a summability hypothesis. Work with `MeasureTheory.condLExp` and convert with `MeasureTheory.toReal_condLExp` at the end.

### Exercises

1. (A) Show that $\mu[f \mid m] \ge 0$ almost everywhere for an integrable $f \ge 0$.
2. (A) Show that $\mu[\mathbf{1}_s \mid m] = \mathbf{1}_s$ almost everywhere for a set $s$ in $m$ on a finite measure space.
3. (B) Show that $\mu[f g \mid m] = f \, \mu[g \mid m]$ almost everywhere when $f$ is bounded and measurable for $m$ and $g$ is integrable.
4. (B) Deduce $(\mu[f \mid m])^2 \le \mu[f^2 \mid m]$ almost everywhere from the inequality of Jensen, for $f \in L^2$ on a probability space.
5. (B) Show that $\mu[f \mid m]$ is in $L^2$ when $f$ is in $L^2$.
6. (C) Prove that $\int^{-} \sum_n P^{-}[X_n \mid m] \, dP = \sum_n \int^{-} X_n \, dP$ for measurable $X_n \ge 0$.

### Reference

<?reference?>
