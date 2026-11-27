---
title: The Kullback-Leibler divergence
kind: theory
modules:
  - Mathlib.InformationTheory.KullbackLeibler.KLFun
  - Mathlib.InformationTheory.KullbackLeibler.Basic
explains:
  E3: [InformationTheory.klFun, InformationTheory.klDiv, InformationTheory.klDiv_eq_integral_klFun, InformationTheory.integral_llr_add_sub_measure_univ_nonneg, InformationTheory.klDiv_eq_zero_iff, InformationTheory.strictConvexOn_klFun]
  E2: [InformationTheory.klFun_apply, InformationTheory.klFun_nonneg, InformationTheory.klFun_eq_zero_iff, InformationTheory.hasDerivAt_klFun, InformationTheory.convexOn_klFun, InformationTheory.integral_klFun_rnDeriv, InformationTheory.integrable_klFun_rnDeriv_iff, InformationTheory.klDiv_of_not_ac, InformationTheory.klDiv_of_not_integrable, InformationTheory.klDiv_ne_top_iff, InformationTheory.klDiv_of_ac_of_integrable, InformationTheory.klDiv_self, InformationTheory.klDiv_zero_left, InformationTheory.klDiv_zero_right, InformationTheory.toReal_klDiv, InformationTheory.toReal_klDiv_of_measure_eq, InformationTheory.mul_log_le_klDiv, InformationTheory.mul_klFun_le_toReal_klDiv, InformationTheory.klDiv_smul_same]
  E1: auto
families: []
requires: [V15, V18.C04, V18.C05, V20.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Kullback-Leibler divergence

### Overview

The Kullback-Leibler divergence $\mathrm{KL}(\mu \,\|\, \nu)$ measures how far a measure $\mu$ is from a reference measure $\nu$. For probability measures it is the mean, under $\mu$, of the logarithm of the density $d\mu/d\nu$. In statistics it is the expected evidence per observation for $\mu$ against $\nu$, and in coding it is the extra length of a code that is optimal for $\nu$ when the source has law $\mu$. Mathlib defines it for two finite measures, with values in $[0, \infty]$, and adds a mass term so that it stays nonnegative. This section defines the convex function $x \log x + 1 - x$ behind it, proves Gibbs' inequality and the case of equality, and computes the divergence of two Bernoulli and two Gaussian laws.

### Definitions

In this section $\mu$ and $\nu$ are finite measures on a measurable space $\alpha$, and $\mu(\alpha)$, $\nu(\alpha)$ are their total masses. If $\mu \ll \nu$, the theorem of Radon and Nikodym of Volume 18, Chapter 4, gives the density $f = d\mu/d\nu$, finite $\nu$-a.e., and $\mu = f \cdot \nu$.

**Definition (The function $\varphi$).** For real $x$, put $\varphi(x) = x \log x + 1 - x$, so $\varphi(0) = 1$ and $\varphi(1) = 0$.

::: mathlib
`InformationTheory.klFun` · `Mathlib.InformationTheory.KullbackLeibler.KLFun`

`klFun x = x * log x + 1 - x` (`klFun_apply`), a function `ℝ → ℝ`. Mathlib uses it only on `Ici 0`. Its derivative at `x ≠ 0` is `log x` (`hasDerivAt_klFun`), and `not_differentiableAt_klFun_zero` says that it has no derivative at $0$.

<?decl InformationTheory.klFun?>
:::

**Definition (Log-likelihood ratio).** If $\mu \ll \nu$, the *log-likelihood ratio* is $\log f$. It is finite $\mu$-a.e., because $\mu(\{f = 0\}) = \int_{\{f = 0\}} f \, d\nu = 0$.

::: mathlib
`MeasureTheory.llr` · `Mathlib.MeasureTheory.Measure.LogLikelihoodRatio`

`llr μ ν x = log (μ.rnDeriv ν x).toReal` (`llr_def`). The density `μ.rnDeriv ν` has values in `ℝ≥0∞`, and `Real.log 0 = 0`, so `llr` is a total real function.

<?decl MeasureTheory.llr?>
:::

**Definition (Kullback-Leibler divergence).** If $\mu \ll \nu$ and $\log f$ is $\mu$-integrable, then
$$\mathrm{KL}(\mu \,\|\, \nu) = \int \log f \, d\mu + \nu(\alpha) - \mu(\alpha).$$
Otherwise $\mathrm{KL}(\mu \,\|\, \nu) = \infty$.

For probability measures the mass term $\nu(\alpha) - \mu(\alpha)$ is $0$, and $\mathrm{KL}(\mu \,\|\, \nu) = \int \log \frac{d\mu}{d\nu} \, d\mu$. For finite measures the term keeps the value nonnegative (Example 3) and makes $\mathrm{KL}(c\mu \,\|\, c\nu) = c\, \mathrm{KL}(\mu \,\|\, \nu)$ for $c \ge 0$.

::: mathlib
`InformationTheory.klDiv` · `Mathlib.InformationTheory.KullbackLeibler.Basic`

`klDiv μ ν : ℝ≥0∞` is `if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ) else ∞`. The logarithm is natural, so the unit is the nat. The cases are `klDiv_of_ac_of_integrable`, `klDiv_of_not_ac` and `klDiv_of_not_integrable`, and `klDiv_ne_top_iff` says that the value is finite if and only if both conditions hold. Further values: `klDiv_self` for a σ-finite measure, `klDiv_zero_left` ($\nu(\alpha)$) and `klDiv_zero_right` ($\infty$ for $\mu \neq 0$). The scaling is `klDiv_smul_same`.

<?decl InformationTheory.klDiv?>
:::

### Theorems and proofs

**Lemma (Properties of $\varphi$).** On $[0, \infty)$, $\varphi \ge 0$, $\varphi(x) = 0$ if and only if $x = 1$, and $\varphi$ is strictly convex.

*Proof.* For $x > 0$, $\log(1/x) \le 1/x - 1$, with equality only at $x = 1$. Multiply by $x$: $-x \log x \le 1 - x$, that is $\varphi(x) \ge 0$. Also $\varphi(0) = 1$. On $(0, \infty)$, $\varphi''(x) = 1/x > 0$, so $\varphi$ is strictly convex there. As $\varphi$ is continuous at $0$, it is strictly convex on $[0, \infty)$. $\square$

::: mathlib
`InformationTheory.strictConvexOn_klFun` · `Mathlib.InformationTheory.KullbackLeibler.KLFun`

`StrictConvexOn ℝ (Ici 0) klFun`. The other facts are `convexOn_klFun`, `klFun_nonneg` with the hypothesis `0 ≤ x`, and `klFun_eq_zero_iff : 0 ≤ x → (klFun x = 0 ↔ x = 1)`.

<?decl InformationTheory.strictConvexOn_klFun?>
:::

**Theorem (Integral form).** Let $\mu \ll \nu$. Then $\varphi(f)$ is $\nu$-integrable if and only if $\log f$ is $\mu$-integrable, and then
$$\int \varphi(f) \, d\nu = \int \log f \, d\mu + \nu(\alpha) - \mu(\alpha).$$
So $\mathrm{KL}(\mu \,\|\, \nu) = \int \varphi(f) \, d\nu$ when $\mu \ll \nu$ and $\log f$ is integrable.

*Proof.* As $\mu = f \cdot \nu$, a function $g$ is $\mu$-integrable if and only if $f g$ is $\nu$-integrable, and then $\int g \, d\mu = \int f g \, d\nu$. For $g = \log f$, the product $f \log f$ is $0$ on $\{f = 0\}$, a $\mu$-null set. The functions $f$ and $1$ are $\nu$-integrable, with integrals $\mu(\alpha)$ and $\nu(\alpha)$, because the measures are finite. So $\varphi(f) = f \log f + 1 - f$ is $\nu$-integrable exactly when $f \log f$ is, and the formula follows. $\square$

::: mathlib
`InformationTheory.klDiv_eq_integral_klFun` · `Mathlib.InformationTheory.KullbackLeibler.Basic`

For finite measures, `klDiv μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν) else ⊤`. The two steps are `integrable_klFun_rnDeriv_iff` and `integral_klFun_rnDeriv`. The form `klDiv_eq_lintegral_klFun` needs no integrability, because a lower integral is always defined.

<?decl InformationTheory.klDiv_eq_integral_klFun?>
:::

**Theorem (Gibbs' inequality).** If $\mu \ll \nu$ and $\log f$ is $\mu$-integrable, then $\int \log f \, d\mu + \nu(\alpha) - \mu(\alpha) \ge 0$. For probability measures, $\int \log \frac{d\mu}{d\nu} \, d\mu \ge 0$.

*Proof.* The left side is $\int \varphi(f) \, d\nu$, and $\varphi(f) \ge 0$. $\square$

So the `ENNReal.ofReal` of the definition only converts a nonnegative real number. Then `toReal_klDiv` recovers the real formula.

::: mathlib
`InformationTheory.integral_llr_add_sub_measure_univ_nonneg` · `Mathlib.InformationTheory.KullbackLeibler.Basic`

`μ ≪ ν → Integrable (llr μ ν) μ → 0 ≤ ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ`. For measures of equal mass, `toReal_klDiv_of_measure_eq` gives `(klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ` without the hypothesis of integrability. In the case without it, both sides are $0$, the junk values of `toReal ∞` and of the integral.

<?decl InformationTheory.integral_llr_add_sub_measure_univ_nonneg?>
:::

**Theorem (Equality).** $\mathrm{KL}(\mu \,\|\, \nu) = 0$ if and only if $\mu = \nu$.

*Proof.* If $\mu = \nu$, then $f = 1$ $\nu$-a.e., $\log f = 0$ and the masses agree. Conversely, let $\mathrm{KL}(\mu \,\|\, \nu) = 0$. The value is finite, so $\mu \ll \nu$, $\log f$ is integrable, and $\int \varphi(f) \, d\nu = 0$. A nonnegative function with integral $0$ is $0$ a.e., so $\varphi(f) = 0$ and $f = 1$ $\nu$-a.e. by the lemma. Then $\mu = f \cdot \nu = \nu$. $\square$

::: mathlib
`InformationTheory.klDiv_eq_zero_iff` · `Mathlib.InformationTheory.KullbackLeibler.Basic`

`klDiv μ ν = 0 ↔ μ = ν` for finite measures. The last step of the proof is `Measure.withDensity_rnDeriv_eq` of Volume 18.

<?decl InformationTheory.klDiv_eq_zero_iff?>
:::

**Theorem (Mass bound).** $\mathrm{KL}(\mu \,\|\, \nu) \ge \mu(\alpha) \log \frac{\mu(\alpha)}{\nu(\alpha)} + \nu(\alpha) - \mu(\alpha)$.

*Proof.* Assume the value is finite, so $\mu \ll \nu$. If $\nu(\alpha) = 0$, then $\mu = 0$ and both sides are $0$. Otherwise $\bar\nu = \nu / \nu(\alpha)$ is a probability measure, and Jensen's inequality for the convex $\varphi$ gives
$$\int \varphi(f) \, d\nu = \nu(\alpha) \int \varphi(f) \, d\bar\nu \ge \nu(\alpha)\, \varphi\Big(\int f \, d\bar\nu\Big) = \nu(\alpha)\, \varphi\Big(\frac{\mu(\alpha)}{\nu(\alpha)}\Big).$$
The right side is the bound. $\square$

::: mathlib
`InformationTheory.mul_log_le_klDiv` · `Mathlib.InformationTheory.KullbackLeibler.Basic`

`ENNReal.ofReal (μ.real univ * log (μ.real univ / ν.real univ) + ν.real univ - μ.real univ) ≤ klDiv μ ν`, with no hypotheses beyond finiteness. The form with $\varphi$ is `mul_klFun_le_toReal_klDiv`.

<?decl InformationTheory.mul_log_le_klDiv?>
:::

### Examples

**Example (Two Bernoulli laws).** Let $\mu$ give the values $1, 0$ the probabilities $\frac12, \frac12$, and $\nu$ the probabilities $\frac14, \frac34$. Then
$$\mathrm{KL}(\mu \,\|\, \nu) = \tfrac12 \log 2 + \tfrac12 \log \tfrac23 = \tfrac12 \log \tfrac43 \approx 0.1438,$$
while $\mathrm{KL}(\nu \,\|\, \mu) = \frac14 \log \frac12 + \frac34 \log \frac32 \approx 0.1308$. The divergence is not symmetric.

**Example (Two Gaussian laws).** Let $\mu = N(m_1, \sigma_1^2)$ and $\nu = N(m_2, \sigma_2^2)$ on $\mathbb{R}$. The ratio of the densities gives
$$\log f(x) = \log \frac{\sigma_2}{\sigma_1} - \frac{(x - m_1)^2}{2\sigma_1^2} + \frac{(x - m_2)^2}{2\sigma_2^2}.$$
Under $\mu$, the mean of $(x - m_1)^2$ is $\sigma_1^2$ and the mean of $(x - m_2)^2$ is $\sigma_1^2 + (m_1 - m_2)^2$. So
$$\mathrm{KL}(\mu \,\|\, \nu) = \log \frac{\sigma_2}{\sigma_1} + \frac{\sigma_1^2 + (m_1 - m_2)^2}{2 \sigma_2^2} - \frac12.$$
For equal variances it is $(m_1 - m_2)^2 / (2\sigma^2)$.

**Example (The mass term).** Let $P$ be a probability measure. For $\mu = P/2$ and $\nu = P$, $f = \frac12$ and $\int \log f \, d\mu = -\frac12 \log 2 \approx -0.347$, a negative number. The mass term adds $\frac12$, and $\mathrm{KL}(P/2 \,\|\, P) = \varphi(\frac12) \approx 0.153$. For $\mu = 2P$, $\mathrm{KL}(2P \,\|\, P) = 2 \log 2 - 1 \approx 0.386$. In both cases the mass bound is an equality, because $f$ is constant.

**Counterexample (No absolute continuity).** For the Dirac measures $\delta_0$ and $\delta_1$ on $\mathbb{R}$, $\delta_0 \not\ll \delta_1$, so $\mathrm{KL}(\delta_0 \,\|\, \delta_1) = \infty$.

### The library around it

Section 4 of this chapter proves the chain rule and the data processing inequality. The index of this edition has no declaration for the divergence of two finite distributions given by vectors, for Pinsker's inequality, or for the entropy of a distribution as $\log n - \mathrm{KL}(p \,\|\, u)$.

Common errors of a learner:

- `klDiv` is in `ℝ≥0∞`. For real computations, use `toReal_klDiv` and check that the value is finite.
- The mass term matters for measures that are not probability measures. `klDiv μ ν` is not `∫ x, llr μ ν x ∂μ` in general.
- `klDiv_self` needs only `SigmaFinite`, but most other lemmas need `IsFiniteMeasure` for both measures.

### Exercises

1. (A) Compute $\mathrm{KL}(\mu \,\|\, \nu)$ for $\mu = \mathrm{Bern}(p)$ and $\nu = \mathrm{Bern}(q)$ with $0 < q < 1$, and check that it is $0$ only for $p = q$.
2. (A) Show that $\mathrm{KL}(\mu \,\|\, \nu) = \log n - H(p)$ when $\mu = p$ is a distribution on $n$ points and $\nu$ is uniform.
3. (A) Let $\mu$ and $\nu$ be exponential laws with rates $a$ and $b$. Show that $\mathrm{KL}(\mu \,\|\, \nu) = \log(a/b) + b/a - 1$.
4. (B) On $\{1, 2, \ldots\}$ let $\mu(\{n\}) = \frac{1}{n(n+1)}$ and $\nu(\{n\}) = 2^{-n}$. Show that $\mu \ll \nu$ but that $\log f$ is not $\mu$-integrable, so $\mathrm{KL}(\mu \,\|\, \nu) = \infty$.
5. (B) Show that $\mathrm{KL}(c\mu \,\|\, c\nu) = c\, \mathrm{KL}(\mu \,\|\, \nu)$ for $c > 0$. For $\mu = t\nu$, $0 < t < 1$, $\nu \neq 0$, show that $\int \log f \, d\mu < 0$ but $\mathrm{KL}(t\nu \,\|\, \nu) = \nu(\alpha)\, \varphi(t) > 0$.
6. (C) Show that $\mathrm{KL}$ is jointly convex: for $0 \le t \le 1$, $\mathrm{KL}(t\mu_1 + (1-t)\mu_2 \,\|\, t\nu_1 + (1-t)\nu_2) \le t\,\mathrm{KL}(\mu_1 \,\|\, \nu_1) + (1-t)\,\mathrm{KL}(\mu_2 \,\|\, \nu_2)$ on a finite set. Hint: the function $(a, b) \mapsto a \log(a/b) + b - a$ is convex on $(0, \infty)^2$.

### Notes and history

Kullback and Leibler introduced the divergence in 1951 in a paper on information and sufficiency. Gibbs' inequality takes its name from the work of Gibbs in statistical mechanics. The divergence is the $f$-divergence of $\varphi$, a notion of Csiszár and of Ali and Silvey from the 1960s.

### Reference

<?reference?>
