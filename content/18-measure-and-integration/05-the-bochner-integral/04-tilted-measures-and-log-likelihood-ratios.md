---
title: Tilted measures, log-likelihood ratios and the method of exhaustion
kind: api
modules:
  - Mathlib.MeasureTheory.Measure.Decomposition.Exhaustion
  - Mathlib.MeasureTheory.Measure.WithDensityFinite
  - Mathlib.MeasureTheory.Measure.Tilted
  - Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
  - Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
explains:
  E2: [MeasureTheory.measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet, MeasureTheory.toFinite_apply_eq_zero_iff, MeasureTheory.isProbabilityMeasure_tilted, MeasureTheory.tilted_tilted, MeasureTheory.exp_llr_of_ac, MeasureTheory.integral_rnDeriv_mul_log, MeasureTheory.le_integral_rnDeriv_of_ac]
  E1: auto
families: []
requires: [V13, V18.C01, V18.C02, V18.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Tilted measures, log-likelihood ratios and the method of exhaustion

### Overview

Chapter 4, Section 3 proved the theorem of Radon and Nikodym and defined the derivative `μ.rnDeriv ν`. This section collects five modules that build on the derivative and on densities. Two of them are structural. The method of exhaustion splits a measure into a σ-finite part and a part that takes only the values $0$ and $\infty$. The finite version of an s-finite measure replaces a measure by an equivalent probability measure. The other three modules belong to probability and statistics. They define the exponentially tilted measure $\mu_f$ with density $e^f / \int e^f \, d\mu$, the log-likelihood ratio $\log \frac{d\mu}{d\nu}$, and the inequality of Jensen for the integral of a convex function of the derivative.

The statements use the Bochner integral of Sections 1 and 2 of this chapter, because the normalizing constant $\int e^f \, d\mu$ and the log-likelihood ratio are real numbers that can be negative or need a sign.

### The library around it

#### The method of exhaustion

Let $\mu$ be an s-finite measure, a countable sum of finite measures. A measure of this kind can be far from σ-finite: the measure $\infty \cdot \delta_0$ is s-finite, but no set of finite measure contains the point $0$. The module `Mathlib.MeasureTheory.Measure.Decomposition.Exhaustion` separates the two behaviours.

**Theorem (exhaustion).** Let $\mu$ be s-finite. There is a measurable set $S$ such that $\mu$ restricted to $S$ is σ-finite, and each $t \subseteq S^c$ has $\mu(t) = 0$ or $\mu(t) = \infty$.

*Proof sketch.* First let $\nu$ be a finite measure with the same null sets as $\mu$; the next subsection constructs it. Let $c$ be the supremum of $\nu(s)$ over the measurable $s$ on which $\mu$ is σ-finite. Choose $s_n$ with $\nu(s_n) \to c$ and put $S = \bigcup_n s_n$. A countable union of sets on which $\mu$ is σ-finite has the same property, so $\nu(S) = c$. Let $t \subseteq S^c$ with $\mu(t) < \infty$. Then $\mu$ is σ-finite on $S \cup t$, so $\nu(S \cup t) \le c$, and $\nu(t) = 0$. The two measures have the same null sets, so $\mu(t) = 0$. $\square$

The set is `μ.sigmaFiniteSet`, with `MeasureTheory.measurableSet_sigmaFiniteSet` and the dichotomy `MeasureTheory.measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet`. An instance gives `SigmaFinite (μ.restrict μ.sigmaFiniteSet)`. The measure $\mu$ is σ-finite exactly when the rest is null, `MeasureTheory.measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite`. The general form `μ.sigmaFiniteSetWRT ν` works relative to a second measure $\nu$: on its complement each set has $\nu(t) = 0$ or $\mu(t) = \infty$ (`MeasureTheory.measure_eq_top_of_subset_compl_sigmaFiniteSetWRT`). The auxiliary sets `μ.sigmaFiniteSetGE ν n` approximate the supremum, and `MeasureTheory.tendsto_measure_sigmaFiniteSetGE` states the convergence. Finally `MeasureTheory.restrict_compl_sigmaFiniteSetWRT` shows that $\mu$ is $\infty \cdot \nu$ on the complement when $\mu \ll \nu$. This decomposition extends the Radon-Nikodym theorem from σ-finite to s-finite measures.

#### A finite measure with the same null sets

**Proposition.** Each s-finite measure $\mu$ has a finite measure $\mu'$ with the same null sets. If $\mu \ne 0$, the measure $\mu'$ can be a probability measure.

*Proof.* Write $\mu = \sum_n \mu_n$ with $\mu_n$ finite, and put $\mu' = \sum_n 2^{-n-1} \mu_n / (1 + \mu_n(X))$. Then $\mu'(X) \le \sum_n 2^{-n-1} = 1$. A set is $\mu$-null if and only if it is $\mu_n$-null for each $n$, if and only if it is $\mu'$-null. If $\mu \ne 0$, then $\mu'(X) > 0$, and $\mu' / \mu'(X)$ is a probability measure. $\square$

The module `Mathlib.MeasureTheory.Measure.WithDensityFinite` chooses such a finite measure, with $\mu$ itself when $\mu$ is already finite, and defines `μ.toFinite` as this measure divided by its total mass. It is a finite measure by an instance, and a probability measure when `NeZero μ`. The main lemma is `MeasureTheory.toFinite_apply_eq_zero_iff`, `μ.toFinite s = 0 ↔ μ s = 0`. The forms with filters and absolute continuity are `MeasureTheory.ae_toFinite`, `MeasureTheory.absolutelyContinuous_toFinite` and `MeasureTheory.toFinite_absolutelyContinuous`. The lemma `MeasureTheory.toFinite_eq_self` says that nothing changes for a probability measure. With `μ.toFinite`, the module also proves `MeasureTheory.restrict_compl_sigmaFiniteSet`: on the complement of `μ.sigmaFiniteSet`, $\mu$ equals $\infty$ times the finite measure.

#### Tilted measures

**Definition (tilted measure).** Let $f : X \to \mathbb{R}$ with $e^f$ integrable for $\mu$. The *tilted measure* is
$$\mu_f(A) = \int_A \frac{e^{f(x)}}{\int e^{f} \, d\mu} \, d\mu(x).$$

This is `μ.tilted f` in `Mathlib.MeasureTheory.Measure.Tilted`. The definition is a density in the sense of Chapter 4, `MeasureTheory.tilted_eq_withDensity_nnreal`, so all lemmas of `MeasureTheory.Measure.withDensity` apply. It has junk values: when $e^f$ is not integrable, the normalizing integral is $0$ and the measure is $0$ (`MeasureTheory.tilted_of_not_integrable`), and the same holds when $f$ is not a.e. measurable (`MeasureTheory.tilted_of_not_aemeasurable`).

**Proposition.** If $\mu \ne 0$ and $e^f$ is integrable, then $\mu_f$ is a probability measure.

*Proof.* The integrand is positive, so $Z = \int e^f \, d\mu > 0$. Then $\mu_f(X) = Z^{-1} \int e^f \, d\mu = 1$. $\square$

This is `MeasureTheory.isProbabilityMeasure_tilted`. The tilt by a constant normalizes: `MeasureTheory.tilted_const` gives $\mu$ back for a probability measure, and `MeasureTheory.tilted_const'` gives $\mu(X)^{-1} \mu$ in general. The integral against $\mu_f$ is `MeasureTheory.integral_tilted`, $\int g \, d\mu_f = \int (e^f / Z) \, g \, d\mu$, with the forms `MeasureTheory.lintegral_tilted` and `MeasureTheory.setIntegral_tilted`.

**Proposition.** If $e^f$ is integrable for $\mu$, then $(\mu_f)_g = \mu_{f + g}$ for each $g$.

*Proof.* Put $Z_f = \int e^f \, d\mu$. The measure $\mu_f$ has density $e^f / Z_f$, so $(\mu_f)_g$ has density $\frac{e^g}{Z'} \cdot \frac{e^f}{Z_f}$ with $Z' = \int e^g \, d\mu_f = Z_{f+g} / Z_f$. The product is $e^{f+g} / Z_{f+g}$, the density of $\mu_{f+g}$. When $e^{f+g}$ is not integrable, both sides are $0$. $\square$

This is `MeasureTheory.tilted_tilted`. It gives `MeasureTheory.tilted_comm` and `MeasureTheory.tilted_neg_same`: tilting by $f$ and then by $-f$ gives $\mu$ back for a probability measure. The derivatives are explicit: `MeasureTheory.rnDeriv_tilted_left_self` gives $d\mu_f / d\mu = e^f / Z$ a.e., and `MeasureTheory.rnDeriv_tilted_left` and `MeasureTheory.rnDeriv_tilted_right` handle a tilt on either side of `MeasureTheory.Measure.rnDeriv`. The tilted measure is equivalent to $\mu$: `MeasureTheory.tilted_absolutelyContinuous` and `MeasureTheory.absolutelyContinuous_tilted`.

#### The log-likelihood ratio

**Definition (log-likelihood ratio).** For measures $\mu$ and $\nu$, the *log-likelihood ratio* is the function $x \mapsto \log \frac{d\mu}{d\nu}(x)$, with the real part of the derivative.

This is `MeasureTheory.llr μ ν` in `Mathlib.MeasureTheory.Measure.LogLikelihoodRatio`. It is measurable (`MeasureTheory.measurable_llr`, `MeasureTheory.stronglyMeasurable_llr`). The logarithm of Mathlib satisfies $\log 0 = 0$, so the function is defined everywhere, and a theorem about it needs the hypothesis $\mu \ll \nu$ to say anything about the points where the derivative vanishes.

**Proposition.** If $\mu \ll \nu$, then $e^{\mathrm{llr}(\mu, \nu)} = \frac{d\mu}{d\nu}$, $\mu$-a.e.

*Proof.* The set $\{d\mu / d\nu = 0\}$ is $\mu$-null, because its $\mu$-measure is the integral of the derivative over it. On the set $\{0 < d\mu/d\nu < \infty\}$, $\exp \circ \log$ is the identity. The set where the derivative is $\infty$ is $\nu$-null, hence $\mu$-null. $\square$

This is `MeasureTheory.exp_llr_of_ac`, with the variants `MeasureTheory.exp_llr`, `MeasureTheory.exp_neg_llr` and `MeasureTheory.neg_llr`, which states $-\mathrm{llr}(\mu, \nu) = \mathrm{llr}(\nu, \mu)$ a.e. for equivalent measures. The self ratio vanishes, `MeasureTheory.llr_self`. The family `MeasureTheory.llr_smul_left`, `MeasureTheory.llr_smul_right`, `MeasureTheory.llr_smul_same` and the forms with an `NNReal` scalar, such as `MeasureTheory.llr_smul_nnreal_left`, computes the effect of a scalar on either measure.

The integral of the log-likelihood ratio is the Kullback-Leibler divergence. The module proves the identity that connects the two usual formulas.

**Proposition.** If $\mu \ll \nu$, then $\int \frac{d\mu}{d\nu} \log \frac{d\mu}{d\nu} \, d\nu = \int \mathrm{llr}(\mu, \nu) \, d\mu$.

*Proof.* The integral of $g$ against $\mu$ equals the integral of $\frac{d\mu}{d\nu} g$ against $\nu$, by the theorem of Radon and Nikodym. Apply it to $g = \mathrm{llr}(\mu, \nu)$. $\square$

This is `MeasureTheory.integral_rnDeriv_mul_log`, and `MeasureTheory.integrable_rnDeriv_mul_log_iff` compares the integrability conditions. The tilted measures enter through `MeasureTheory.llr_tilted_left` and `MeasureTheory.llr_tilted_right`. For instance $\mathrm{llr}(\mu_f, \nu) = f - \log Z + \mathrm{llr}(\mu, \nu)$, $\mu$-a.e. The integrated forms `MeasureTheory.integral_llr_tilted_left` and `MeasureTheory.integral_llr_tilted_right` are the variational identities of large deviations theory.

#### Jensen's inequality for the derivative

**Theorem.** Let $\mu$ be finite, $\nu$ a probability measure and $\mu \ll \nu$. Let $f$ be convex and continuous on $[0, \infty)$ with $f(\frac{d\mu}{d\nu})$ integrable for $\nu$. Then $f(\mu(X)) \le \int f\big(\frac{d\mu}{d\nu}\big) \, d\nu$.

*Proof.* By the inequality of Jensen for the probability measure $\nu$, $f\big(\int \frac{d\mu}{d\nu} \, d\nu\big) \le \int f\big(\frac{d\mu}{d\nu}\big) \, d\nu$. Since $\mu \ll \nu$, the integral of the derivative is $\mu(X)$. $\square$

This is `MeasureTheory.le_integral_rnDeriv_of_ac` in `Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv`. The form `MeasureTheory.mul_le_integral_rnDeriv_of_ac` drops the hypothesis that $\nu$ has mass $1$ and reads $\nu(X) f(\mu(X)/\nu(X)) \le \int f(\frac{d\mu}{d\nu}) \, d\nu$. These inequalities are the basis of the theory of $f$-divergences: for $f(t) = t \log t$ they give the nonnegativity of the Kullback-Leibler divergence between probability measures. The same module proves `MeasureTheory.Measure.integrable_toReal_rnDeriv`, the integrability of the derivative of a finite measure, and versions for kernels, `MeasureTheory.lintegral_rnDeriv_compProd` and `ConvexOn.apply_rnDeriv_ae_le_integral`.

#### Common errors

1. A learner uses `μ.tilted f` without the hypothesis that $e^f$ is integrable. The measure is then $0$, and lemmas such as `MeasureTheory.isProbabilityMeasure_tilted` need the hypothesis explicitly.
2. A learner forgets that `Real.log 0 = 0`. The function `MeasureTheory.llr μ ν` is $0$ where the derivative is $0$, not $-\infty$, so most identities hold only $\mu$-a.e. and need $\mu \ll \nu$.
3. A learner expects `μ.toFinite` to be a restriction of $\mu$. It is a different measure with the same null sets; it keeps the filter `ae μ`, not the values of $\mu$.

### Exercises

1. (A) Show that $\mu_f = \mu_g$ when $f = g$ a.e., and compare with `MeasureTheory.tilted_congr`.
2. (A) Compute the tilt of the standard Gaussian measure on $\mathbb{R}$ by $f(x) = tx$.
3. (B) Show that the Bernoulli measure with parameter $p$ on $\{0, 1\}$ tilted by $f(x) = tx$ is the Bernoulli measure with parameter $p e^t / (1 - p + p e^t)$.
4. (B) Let $\mu$ and $\nu$ be probability measures with $\mu \ll \nu$. Show that $\int \mathrm{llr}(\mu, \nu) \, d\mu \ge 0$ when it is integrable. Hint: apply the inequality of Jensen above to $f(t) = t \log t$.
5. (B) Let $\mu = \lambda + \infty \cdot \delta_0$ on $\mathbb{R}$, with $\lambda$ the Lebesgue measure. Show that $\mu$ is s-finite but not σ-finite, and describe the set `μ.sigmaFiniteSet` up to a $\mu$-null set.
6. (C) Prove the Radon-Nikodym theorem for $\mu \ll \nu$ with $\nu$ s-finite and $\mu$ σ-finite, from the σ-finite case and `MeasureTheory.toFinite_apply_eq_zero_iff`.

### Reference

<?reference?>
