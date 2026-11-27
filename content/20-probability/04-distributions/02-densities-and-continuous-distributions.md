---
title: Densities and continuous distributions
kind: theory
modules:
  - Mathlib.Probability.Density
  - Mathlib.Probability.Distributions.Uniform
  - Mathlib.Probability.Distributions.Exponential
  - Mathlib.Probability.Distributions.Gamma
  - Mathlib.Probability.Distributions.Beta
  - Mathlib.Probability.Distributions.Pareto
  - Mathlib.Probability.Distributions.Cauchy
explains:
  E3: [MeasureTheory.HasPDF, MeasureTheory.pdf, MeasureTheory.pdf.IsUniform, ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure, ProbabilityTheory.cauchyMeasure, ProbabilityTheory.IndepFun.pdf_add_eq_lconvolution_pdf]
  E2: [MeasureTheory.map_eq_withDensity_pdf, Real.hasPDF_iff, MeasureTheory.pdf.integral_mul_eq_integral, MeasureTheory.pdf.indepFun_iff_pdf_prod_eq_pdf_mul_pdf, MeasureTheory.pdf.IsUniform.measure_preimage, MeasureTheory.pdf.IsUniform.integral_eq, MeasureTheory.Measure.uniformOfFinset, ProbabilityTheory.exponentialPDFReal, ProbabilityTheory.cdf_expMeasure_eq, ProbabilityTheory.gammaPDFReal, ProbabilityTheory.lintegral_gammaPDF_eq_one, ProbabilityTheory.betaMeasure, ProbabilityTheory.paretoMeasure, ProbabilityTheory.cauchyPDFReal_def]
  E1: auto
families: []
requires: [V03, V13, V15, V20.C01, V20.C02, V20.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Densities and continuous distributions

### Overview

Many laws on $\mathbb{R}$ give probability $0$ to each point, and are given by a density instead: a nonnegative function $f$ with $P(X \in A) = \int_A f(x)\, dx$. The Radon-Nikodym theorem of Volume 18 says exactly when a density exists: when the law is absolutely continuous with respect to the Lebesgue measure. This section defines densities, shows how to compute expectations and laws of sums with them, and presents the uniform, exponential, gamma, beta, Pareto and Cauchy laws. The Gaussian law has Section 3 to itself.

### Definitions

**Definition (Density).** Let $X$ be a random variable with values in a measurable space $E$ with a reference measure $\mu$, usually the Lebesgue measure on $\mathbb{R}^d$. A *density* of $X$ is a measurable $f : E \to [0, \infty]$ with
$$P(X \in A) = \int_A f\, d\mu \quad \text{for all measurable } A.$$
Two densities of $X$ are equal $\mu$-a.e. A real variable has a density if and only if its law is absolutely continuous with respect to the Lebesgue measure, by the Radon-Nikodym theorem. Then $F(x) = \int_{-\infty}^x f(t)\, dt$, and $F' = f$ a.e.

::: mathlib
`MeasureTheory.HasPDF` · `Mathlib.Probability.Density`

`HasPDF X ℙ μ` is a class: `X` is a.e. measurable, the law `ℙ.map X` has a Lebesgue decomposition with respect to `μ`, and it is absolutely continuous with respect to `μ`. The default `μ` is `volume`. For real variables `Real.hasPDF_iff` gives the form of the text: a.e. measurability and `ℙ.map X ≪ volume`.

<?decl MeasureTheory.HasPDF?>
:::

::: mathlib
`MeasureTheory.pdf` · `Mathlib.Probability.Density`

`pdf X ℙ μ : E → ℝ≥0∞` is the Radon-Nikodym derivative `(ℙ.map X).rnDeriv μ`. It is defined for all `X`, and under `HasPDF X ℙ μ`, `map_eq_withDensity_pdf` gives `ℙ.map X = μ.withDensity (pdf X ℙ μ)`, which is the definition of the text. For a real variable, `pdf.integral_mul_eq_integral` is $E[X] = \int x f(x)\, dx$.

<?decl MeasureTheory.pdf?>
:::

**Definition (Uniform law).** Let $S \subseteq \mathbb{R}^d$ be measurable with $0 < \lambda(S) < \infty$. A variable $X$ is *uniform on $S$* if $P(X \in A) = \lambda(A \cap S)/\lambda(S)$; its density is $\mathbf{1}_S/\lambda(S)$.

::: mathlib
`MeasureTheory.pdf.IsUniform` · `Mathlib.Probability.Distributions.Uniform`

`IsUniform X s ℙ μ` says `ℙ.map X = (μ s)⁻¹ • μ.restrict s`, which is the measure `μ[|s]` of Chapter 1, $\mu$ conditioned on $s$. `IsUniform.measure_preimage` is the formula of the text, and `IsUniform.integral_eq` gives the mean $\lambda(s)^{-1}\int_s x\, dx$. The discrete uniform law on a finset is `Measure.uniformOfFinset`, which replaces the older `PMF.uniformOfFinset`.

<?decl MeasureTheory.pdf.IsUniform?>
:::

**Definition (The standard laws with a density).** For parameters $r, a, b > 0$, $x_0 \in \mathbb{R}$ and $\gamma > 0$:

| law | density | where |
|---|---|---|
| exponential $\operatorname{Exp}(r)$ | $r e^{-rx}$ | $x \ge 0$ |
| gamma $\Gamma(a, r)$ | $\frac{r^a}{\Gamma(a)} x^{a-1}e^{-rx}$ | $x \ge 0$ |
| beta $B(a, b)$ | $\frac{x^{a-1}(1-x)^{b-1}}{B(a, b)}$ | $0 < x < 1$ |
| Pareto with scale $t$ and shape $r$ | $r t^r x^{-r-1}$ | $x \ge t$ |
| Cauchy with location $x_0$, scale $\gamma$ | $\frac{\gamma}{\pi((x - x_0)^2 + \gamma^2)}$ | $x \in \mathbb{R}$ |

Here $\Gamma(a) = \int_0^\infty x^{a-1}e^{-x}\, dx$ and $B(a, b) = \Gamma(a)\Gamma(b)/\Gamma(a + b)$. The density is $0$ outside the given range. $\operatorname{Exp}(r) = \Gamma(1, r)$.

::: mathlib
`ProbabilityTheory.expMeasure` · `Mathlib.Probability.Distributions.Exponential`

`expMeasure r = volume.withDensity (exponentialPDF r)`, where `exponentialPDF r x = ENNReal.ofReal (exponentialPDFReal r x)` and `exponentialPDFReal r x = if 0 ≤ x then r * exp (-(r * x)) else 0`. `cdf_expMeasure_eq` gives the distribution function $1 - e^{-rx}$ for $x \ge 0$. Each of the laws of the table follows the same pattern: a real density `...PDFReal`, the density `...PDF` in `ℝ≥0∞`, the measure, the proof that the total mass is `1`, and the distribution function.

<?decl ProbabilityTheory.expMeasure?>
:::

::: mathlib
`ProbabilityTheory.gammaMeasure` · `Mathlib.Probability.Distributions.Gamma`

`gammaMeasure a r` is the law $\Gamma(a, r)$ with shape `a` and rate `r`, with density `gammaPDFReal a r x = if 0 ≤ x then r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x)) else 0`. `lintegral_gammaPDF_eq_one` needs `0 < a` and `0 < r`. The beta law is `betaMeasure` in `Mathlib.Probability.Distributions.Beta`, and the Pareto law is `paretoMeasure` in `Mathlib.Probability.Distributions.Pareto`.

<?decl ProbabilityTheory.gammaMeasure?>
:::

::: mathlib
`ProbabilityTheory.cauchyMeasure` · `Mathlib.Probability.Distributions.Cauchy`

`cauchyMeasure x₀ γ` for `γ : ℝ≥0`, with `cauchyPDFReal_def : cauchyPDFReal x₀ γ x = π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹`. For `γ = 0` the measure is `dirac x₀` (`cauchyMeasure_zero_scale`).

<?decl ProbabilityTheory.cauchyMeasure?>
:::

### Theorems and proofs

**Theorem (Expectations with a density).** Let $X$ have the density $f$ and let $g$ be measurable. Then $E|g(X)| = \int |g(x)| f(x)\, dx$, and if this is finite, $E[g(X)] = \int g(x) f(x)\, dx$.

*Proof.* By the transfer formula of Chapter 3, $E[g(X)] = \int g\, dP_X$. The law is $P_X = f \cdot \lambda$, and Volume 18 gives $\int g\, d(f\lambda) = \int g f\, d\lambda$, first for indicators, then by linearity and monotone convergence. $\square$

**Theorem (Change of variables).** Let $X$ have the density $f_X$ on an open interval $I$, and let $\varphi : I \to J$ be a $C^1$ bijection with $\varphi' \neq 0$. Then $Y = \varphi(X)$ has the density $f_Y(y) = f_X(\varphi^{-1}(y))\,|(\varphi^{-1})'(y)|$ on $J$.

*Proof.* For measurable $A \subseteq J$, $P(Y \in A) = P(X \in \varphi^{-1}(A)) = \int_{\varphi^{-1}(A)} f_X(x)\, dx$. The substitution $x = \varphi^{-1}(y)$ of Volume 18 turns this into $\int_A f_X(\varphi^{-1}(y))\,|(\varphi^{-1})'(y)|\, dy$. $\square$

**Theorem (Density of a sum).** Let $X, Y$ be independent real variables with densities $f$ and $g$. Then $X + Y$ has the density
$$(f * g)(z) = \int f(x) g(z - x)\, dx.$$

*Proof.* By Chapter 2, $P(X + Y \le z) = \int P(Y \le z - x) f(x)\, dx = \int \int_{-\infty}^{z} g(t - x)\, dt\, f(x)\, dx$. Tonelli's theorem exchanges the integrals: $P(X + Y \le z) = \int_{-\infty}^z (f * g)(t)\, dt$. $\square$

::: mathlib
`ProbabilityTheory.IndepFun.pdf_add_eq_lconvolution_pdf` · `Mathlib.Probability.Density`

For a group `G` with a left invariant s-finite measure `μ`, `HasPDF X ℙ μ`, `HasPDF Y ℙ μ` and `IndepFun X Y ℙ`: `pdf (X + Y) ℙ μ =ᵐ[μ] (pdf X ℙ μ) ⋆ₗ[μ] (pdf Y ℙ μ)`, the convolution of functions with values in `ℝ≥0∞`. The product form `IndepFun.pdf_mul_eq_mlconvolution_pdf` is the multiplicative version. Independence is characterised by `pdf.indepFun_iff_pdf_prod_eq_pdf_mul_pdf`: the joint density is the product of the densities.

<?decl ProbabilityTheory.IndepFun.pdf_add_eq_lconvolution_pdf?>
:::

**Theorem (Sums of exponential variables).** If $X_1, \ldots, X_n$ are independent with law $\operatorname{Exp}(r)$, then $X_1 + \cdots + X_n$ has the law $\Gamma(n, r)$. More generally, $\Gamma(a, r) * \Gamma(b, r) = \Gamma(a + b, r)$.

*Proof.* For $z > 0$,
$$\int_0^z \frac{r^a x^{a-1}e^{-rx}}{\Gamma(a)}\frac{r^b (z - x)^{b-1}e^{-r(z-x)}}{\Gamma(b)}\, dx = \frac{r^{a+b}e^{-rz}}{\Gamma(a)\Gamma(b)}\int_0^z x^{a-1}(z-x)^{b-1}\, dx.$$
The substitution $x = zu$ gives $\int_0^z x^{a-1}(z-x)^{b-1}\, dx = z^{a+b-1}B(a, b)$, and $B(a, b) = \Gamma(a)\Gamma(b)/\Gamma(a+b)$. The result is the density of $\Gamma(a + b, r)$. Induction gives the first claim. $\square$

### Examples

**Example (Lack of memory).** If $X \sim \operatorname{Exp}(r)$, then $P(X > s + t \mid X > s) = e^{-r(s+t)}/e^{-rs} = e^{-rt} = P(X > t)$. A light bulb with an exponential lifetime that still works at time $s$ is as good as new. The exponential laws are the only laws on $[0, \infty)$ with this property, the continuous analogue of the geometric law of Section 1.

**Example (Minimum of exponential variables).** Let $X_1, \ldots, X_n$ be independent with $X_i \sim \operatorname{Exp}(r_i)$. Then $P(\min_i X_i > t) = \prod_i e^{-r_i t} = e^{-(r_1 + \cdots + r_n)t}$, so $\min_i X_i \sim \operatorname{Exp}(r_1 + \cdots + r_n)$. Also $P(X_1 = \min_i X_i) = r_1/(r_1 + \cdots + r_n)$.

**Counterexample (The Cauchy law has no mean).** Let $X$ have the standard Cauchy density $1/(\pi(1 + x^2))$. Then $E|X| = \frac{2}{\pi}\int_0^\infty \frac{x}{1 + x^2}\, dx = \infty$, so $X$ is not integrable. The law of large numbers of Chapter 5 does not apply: the average of $n$ independent standard Cauchy variables is again standard Cauchy (an exercise of Section 3 proves it with characteristic functions), so the averages do not converge to a constant.

**Example (The quantile transform).** Let $U$ be uniform on $(0, 1)$ and let $F$ be a continuous strictly increasing distribution function. Then $X = F^{-1}(U)$ has $P(X \le x) = P(U \le F(x)) = F(x)$. For $F(x) = 1 - e^{-rx}$ this gives $X = -\log(1 - U)/r \sim \operatorname{Exp}(r)$. Computer programs sample from laws in this way.

### The library around it

`Mathlib.Probability.Density` develops `HasPDF` and `pdf` for any reference measure: congruence lemmas, the integral formulas `pdf.lintegral_pdf_mul` and `pdf.integral_pdf_smul`, the push forward along a quasi measure preserving map (`pdf.quasiMeasurePreserving_hasPDF`), and the results on sums and products of independent variables. The named laws each live in a short file with the same structure. The index of this edition has no declaration for the mean, the variance or the characteristic function of `expMeasure`, `gammaMeasure`, `betaMeasure`, `paretoMeasure` or `cauchyMeasure`; the exercises below compute some of them on paper.

Common errors of a learner:

- `pdf X ℙ` is defined for all `X`, with the value `0` when the law has no Lebesgue decomposition. A theorem about `pdf` needs the instance `HasPDF X ℙ`.
- The densities of the named laws are in `ℝ≥0∞` (`exponentialPDF`) and in `ℝ` (`exponentialPDFReal`). The measure uses the first.
- `cauchyMeasure` takes the scale as `γ : ℝ≥0`, while `gammaMeasure` takes the shape and the rate as real numbers with separate positivity hypotheses.

### Exercises

1. (A) Let $X \sim \operatorname{Exp}(r)$. Show that $E[X] = 1/r$ and $\operatorname{Var}(X) = 1/r^2$.
2. (A) Let $U$ be uniform on $(0, 1)$. Find the density of $U^2$ and of $-\log U$.
3. (A) Show that the beta law $B(1, 1)$ is uniform on $(0, 1)$.
4. (B) Let $X \sim \Gamma(a, r)$. Show that $E[X^k] = \Gamma(a + k)/(\Gamma(a) r^k)$ and deduce the mean $a/r$ and the variance $a/r^2$.
5. (B) Let $X, Y$ be independent and uniform on $(0, 1)$. Find the density of $X/Y$.
6. (B) Let $X \sim \operatorname{Exp}(1)$ and $Y \sim \operatorname{Exp}(1)$ be independent. Show that $X/(X + Y)$ is uniform on $(0, 1)$ and independent of $X + Y$.
7. (B) Let $X$ have a Pareto law with scale $t$ and shape $r$. For which $p$ is $E[X^p]$ finite?
8. (C) Show that if $U_1, \ldots, U_n$ are i.i.d. uniform on $(0, 1)$, the $k$-th smallest of them has the law $B(k, n - k + 1)$.

### Notes and history

The exponential law appears as the law of waiting times in the theory of the Poisson process. The Cauchy law appears in Poisson's work of 1824, as a counterexample to Laplace's approximation of averages by the Gaussian law; Cauchy studied it in 1853. Pareto introduced his law in 1896 to describe the distribution of incomes.

### Reference

<?reference?>
