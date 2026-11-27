---
title: The Gaussian distribution
kind: theory
modules:
  - Mathlib.Probability.Distributions.Gaussian.Real
  - Mathlib.Probability.Distributions.Gaussian.Basic
  - Mathlib.Probability.Distributions.Gaussian.CharFun
  - Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def
  - Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
  - Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
  - Mathlib.Probability.Distributions.Gaussian.Multivariate
explains:
  E3: [ProbabilityTheory.gaussianReal, ProbabilityTheory.charFun_gaussianReal, ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun, ProbabilityTheory.IsGaussian, ProbabilityTheory.HasGaussianLaw, ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_eq_zero, ProbabilityTheory.multivariateGaussian]
  E2: [ProbabilityTheory.gaussianPDFReal_def, ProbabilityTheory.integral_gaussianPDFReal_eq_one, ProbabilityTheory.integral_id_gaussianReal, ProbabilityTheory.variance_id_gaussianReal, ProbabilityTheory.mgf_gaussianReal, ProbabilityTheory.gaussianReal_map_const_mul, ProbabilityTheory.gaussianReal_map_add_const, ProbabilityTheory.gaussianReal_conv_gaussianReal, ProbabilityTheory.IsGaussian.map_eq_gaussianReal, ProbabilityTheory.isGaussian_conv, ProbabilityTheory.IsGaussian.ext, ProbabilityTheory.HasGaussianLaw.add, ProbabilityTheory.IndepFun.hasGaussianLaw, ProbabilityTheory.iIndepFun.hasGaussianLaw, ProbabilityTheory.iIndepFun.hasGaussianLaw_fun_sum, ProbabilityTheory.charFun_multivariateGaussian, ProbabilityTheory.covarianceBilin_multivariateGaussian, ProbabilityTheory.stdGaussian, ProbabilityTheory.charFun_stdGaussian, ProbabilityTheory.map_pi_eq_stdGaussian]
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

## The Gaussian distribution

### Overview

The Gaussian law is the limit law of the central limit theorem of Chapter 5, and it is the law that many models of noise use. Three properties make it special. It is closed under affine maps and under sums of independent variables. Its characteristic function has the simple form $e^{i t \mu - v t^2/2}$. In the multivariate case, the mean and the covariance determine the law, and for a jointly Gaussian pair, covariance $0$ is the same as independence. This section states these properties and shows how Mathlib defines Gaussian measures, first on $\mathbb{R}$ and then on any normed space.

### Definitions

**Definition (Real Gaussian law).** Let $\mu \in \mathbb{R}$ and $v > 0$. The *Gaussian law* $N(\mu, v)$ is the law on $\mathbb{R}$ with density
$$g_{\mu, v}(x) = \frac{1}{\sqrt{2 \pi v}} \exp\left(-\frac{(x - \mu)^2}{2 v}\right).$$
For $v = 0$ the law $N(\mu, 0)$ is the Dirac measure $\delta_\mu$. The law $N(0, 1)$ is the *standard* Gaussian law.

::: mathlib
`ProbabilityTheory.gaussianReal` · `Mathlib.Probability.Distributions.Gaussian.Real`

`gaussianReal μ v : Measure ℝ` takes the mean `μ : ℝ` and the variance `v : ℝ≥0`. It is `dirac μ` when `v = 0` and `volume.withDensity (gaussianPDF μ v)` otherwise. The real density `gaussianPDFReal μ v` has the formula of the text by `gaussianPDFReal_def`, and `integral_gaussianPDFReal_eq_one` says that it has total mass $1$ for `v ≠ 0`. The variance is a parameter of type `ℝ≥0`, so a variance $c^2 v$ appears in the statements as `⟨c ^ 2, _⟩ * v`.

<?decl ProbabilityTheory.gaussianReal?>
:::

**Definition (Characteristic function).** The *characteristic function* of a probability measure $\nu$ on a real inner product space $E$ is $\varphi_\nu(t) = \int e^{i \langle x, t\rangle}\, d\nu(x)$. It has $|\varphi_\nu| \le 1$ and $\varphi_\nu(0) = 1$. The characteristic function of $\nu * \rho$ is $\varphi_\nu \varphi_\rho$, and $\varphi$ determines the measure. Volume 18 proves the last fact.

::: mathlib
`MeasureTheory.charFun` · `Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic`

`charFun μ t` is the integral of `Complex.exp (inner ℝ x t * I)`. The product rule for convolutions is `charFun_conv`, and the uniqueness is `Measure.ext_of_charFun`. Both are in the measure theory part of the library, and this volume only uses them.

<?decl MeasureTheory.charFun?>
:::

**Definition (Gaussian measure).** Let $E$ be a real topological vector space. A probability measure $\nu$ on $E$ is *Gaussian* if for each continuous linear form $L : E \to \mathbb{R}$ the image $L_* \nu$ is a real Gaussian law $N(m, v)$ for some $m$ and $v \ge 0$. A random variable $X : \Omega \to E$ has a *Gaussian law* if its law is Gaussian. A pair $(X, Y)$ is *jointly Gaussian* if the variable $\omega \mapsto (X(\omega), Y(\omega))$ has a Gaussian law.

::: mathlib
`ProbabilityTheory.IsGaussian` · `Mathlib.Probability.Distributions.Gaussian.Basic`

`IsGaussian μ` is a class. Its field `IsGaussian.map_eq_gaussianReal` says that for each `L : StrongDual ℝ E`, `μ.map L = gaussianReal (∫ x, L x ∂μ) (variance L μ).toNNReal`. So the definition gives the mean and the variance of $L_*\nu$ explicitly. `isGaussian_conv` says that the convolution of two Gaussian measures is Gaussian.

<?decl ProbabilityTheory.IsGaussian?>
:::

::: mathlib
`ProbabilityTheory.HasGaussianLaw` · `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def`

`HasGaussianLaw X P` is a structure with one field: `IsGaussian (P.map X)`. A pair is jointly Gaussian when `HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P`. The lemmas `HasGaussianLaw.add`, `HasGaussianLaw.sub` and `HasGaussianLaw.smul` take this joint hypothesis, and not two separate hypotheses on `X` and `Y`.

<?decl ProbabilityTheory.HasGaussianLaw?>
:::

**Definition (Multivariate Gaussian law).** Let $m \in \mathbb{R}^n$ and let $S$ be a positive semidefinite $n \times n$ matrix. The law $N(m, S)$ on $\mathbb{R}^n$ is the Gaussian measure with mean $m$ and covariance matrix $S$. Its characteristic function is $\exp(i \langle t, m\rangle - \tfrac12 t^\top S t)$. The *standard* Gaussian measure on a finite dimensional inner product space is the law of $\sum_k Z_k e_k$ for an orthonormal basis $(e_k)$ and i.i.d. standard Gaussian $Z_k$.

::: mathlib
`ProbabilityTheory.multivariateGaussian` · `Mathlib.Probability.Distributions.Gaussian.Multivariate`

`multivariateGaussian μ S : Measure (EuclideanSpace ℝ ι)` takes the mean and a matrix. For `S.PosSemidef`, `charFun_multivariateGaussian` gives the characteristic function of the text and `covarianceBilin_multivariateGaussian` gives the covariance $x^\top S y$. The standard measure is `stdGaussian E`, with `charFun_stdGaussian` equal to $e^{-\|t\|^2/2}$, and `map_pi_eq_stdGaussian` identifies it with the product of standard real laws.

<?decl ProbabilityTheory.multivariateGaussian?>
:::

### Theorems and proofs

**Theorem (Moments).** If $X \sim N(\mu, v)$, then $E[X] = \mu$, $\operatorname{Var}(X) = v$ and $E[e^{tX}] = e^{\mu t + v t^2/2}$ for all real $t$.

*Proof.* For $v = 0$ all three are clear. For $v > 0$, put $Z = (X - \mu)/\sqrt{v}$, which has density $e^{-z^2/2}/\sqrt{2\pi}$. Complete the square: $tz - z^2/2 = t^2/2 - (z - t)^2/2$. So $E[e^{tZ}] = e^{t^2/2} \int e^{-(z - t)^2/2}\, dz/\sqrt{2\pi} = e^{t^2/2}$, by translation invariance of the Lebesgue measure. The moment generating function is finite near $0$, so by Chapter 3 its derivatives at $0$ are the moments: $E[Z] = 0$ and $E[Z^2] = 1$. Then $X = \mu + \sqrt{v} Z$ gives the three formulas. $\square$

::: mathlib
`ProbabilityTheory.mgf_gaussianReal` · `Mathlib.Probability.Distributions.Gaussian.Real`

From `HasLaw X (gaussianReal μ v) p`, the lemma gives `mgf X p t = exp (μ * t + v * t ^ 2 / 2)`. The mean and the variance of the identity are `integral_id_gaussianReal` and `variance_id_gaussianReal`.

<?decl ProbabilityTheory.mgf_gaussianReal?>
:::

**Theorem (Characteristic function).** The characteristic function of $N(\mu, v)$ is $\varphi(t) = e^{i t \mu - v t^2/2}$.

*Proof.* The function $z \mapsto E[e^{zX}]$ is analytic on $\mathbb{C}$, because the Gaussian density decreases faster than each exponential. It is equal to $e^{\mu z + v z^2/2}$ on $\mathbb{R}$, by the theorem above, and the right side is analytic too. By the identity theorem of Volume 15, the two are equal on $\mathbb{C}$. Put $z = it$. $\square$

::: mathlib
`ProbabilityTheory.charFun_gaussianReal` · `Mathlib.Probability.Distributions.Gaussian.Real`

`charFun (gaussianReal μ v) t = exp (t * μ * I - v * t ^ 2 / 2)`. The complex version `complexMGF_gaussianReal` is the analytic function of the proof.

<?decl ProbabilityTheory.charFun_gaussianReal?>
:::

**Theorem (Affine maps and sums).** If $X \sim N(\mu, v)$ and $a, b \in \mathbb{R}$, then $aX + b \sim N(a\mu + b, a^2 v)$. If $X \sim N(\mu_1, v_1)$ and $Y \sim N(\mu_2, v_2)$ are independent, then $X + Y \sim N(\mu_1 + \mu_2, v_1 + v_2)$.

*Proof.* The characteristic function of $aX + b$ is $e^{itb}\varphi_X(at) = \exp(it(a\mu + b) - a^2 v t^2/2)$. For the sum, independence gives $\varphi_{X+Y} = \varphi_X \varphi_Y = \exp(it(\mu_1 + \mu_2) - (v_1 + v_2)t^2/2)$. In both cases the uniqueness of the characteristic function identifies the law. $\square$

::: mathlib
`ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun` · `Mathlib.Probability.Distributions.Gaussian.Real`

From `IndepFun X Y P`, `HasLaw X (gaussianReal m₁ v₁) P` and `HasLaw Y (gaussianReal m₂ v₂) P`, the conclusion is `P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)`. The measure form is `gaussianReal_conv_gaussianReal`. The affine maps are `gaussianReal_map_const_mul` and `gaussianReal_map_add_const`.

<?decl ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun?>
:::

**Theorem (Mean and covariance determine a Gaussian measure).** Let $\nu$ and $\rho$ be Gaussian measures on a separable real Hilbert space with the same mean and the same covariance bilinear form. Then $\nu = \rho$.

*Proof.* For $t \in E$, the form $L = \langle \cdot, t\rangle$ maps $\nu$ to $N(\langle m, t\rangle, C(t, t))$, where $m$ is the mean and $C$ is the covariance. So $\varphi_\nu(t) = \varphi_{L_*\nu}(1) = \exp(i\langle m, t\rangle - C(t, t)/2)$. The same formula holds for $\rho$, so $\varphi_\nu = \varphi_\rho$, and the uniqueness theorem gives $\nu = \rho$. $\square$

::: mathlib
`ProbabilityTheory.IsGaussian.ext` · `Mathlib.Probability.Distributions.Gaussian.CharFun`

The hypotheses are `∫ x, id x ∂μ = ∫ x, id x ∂ν` and `covarianceBilin μ = covarianceBilin ν`, for two measures with `IsGaussian` instances on a complete second countable inner product space. The form `covarianceBilin` is from Chapter 3.

<?decl ProbabilityTheory.IsGaussian.ext?>
:::

**Theorem (Uncorrelated jointly Gaussian variables are independent).** Let $(X, Y)$ be a jointly Gaussian pair of real variables with $\operatorname{Cov}(X, Y) = 0$. Then $X$ and $Y$ are independent.

*Proof.* Let $\nu$ be the law of $(X, Y)$ on $\mathbb{R}^2$ and let $\rho = \mathcal{L}(X) \otimes \mathcal{L}(Y)$. Each marginal is Gaussian, so $\rho$ is Gaussian: its characteristic function is the product $\varphi_X(s)\varphi_Y(t)$, the exponential of a quadratic polynomial. The measures $\nu$ and $\rho$ have the same mean $(E X, E Y)$. Their covariance matrices are both $\operatorname{diag}(\operatorname{Var} X, \operatorname{Var} Y)$, because $\operatorname{Cov}(X, Y) = 0$. By the theorem above, $\nu = \rho$, and this is the independence of $X$ and $Y$ by the criterion of Chapter 2. $\square$

::: mathlib
`ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_eq_zero` · `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence`

From `HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P` and `covariance X Y P = 0`, the conclusion is `IndepFun X Y P`. The converse direction of the proof, a product of Gaussian laws is Gaussian, is `IndepFun.hasGaussianLaw` for two variables and `iIndepFun.hasGaussianLaw` for a finite family. Then `iIndepFun.hasGaussianLaw_fun_sum` says that the sum of an independent finite family of Gaussian variables is Gaussian.

<?decl ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_eq_zero?>
:::

### Examples

**Example (Average of Gaussian measurements).** Let $X_1, \ldots, X_n$ be independent with law $N(\mu, \sigma^2)$, for example $n$ measurements of a length $\mu$ with an instrument of error $\sigma$. By the theorem on sums, $X_1 + \cdots + X_n \sim N(n\mu, n\sigma^2)$, and by the affine rule, $\bar X_n \sim N(\mu, \sigma^2/n)$. So $P(|\bar X_n - \mu| \ge 1.96\, \sigma/\sqrt{n}) = 0.05$ exactly, by a table of the standard law. Chebyshev's bound of Chapter 3 only gives $1/1.96^2 \approx 0.26$.

**Counterexample (Gaussian marginals, covariance $0$, not independent).** Let $X \sim N(0, 1)$ and let $\varepsilon$ be a random sign, independent of $X$, with $P(\varepsilon = 1) = P(\varepsilon = -1) = 1/2$. Put $Y = \varepsilon X$. By the symmetry of $N(0, 1)$, $Y \sim N(0, 1)$. Also $\operatorname{Cov}(X, Y) = E[\varepsilon] E[X^2] = 0$. But $|X| = |Y|$, so $X$ and $Y$ are not independent: $P(|X| \le 1, |Y| > 1) = 0$, while $P(|X| \le 1) P(|Y| > 1) > 0$. The pair is not jointly Gaussian, and $X + Y = (1 + \varepsilon)X$ is $0$ with probability $1/2$ without being $0$ almost surely, so it is not Gaussian. The hypothesis of `HasGaussianLaw.add` and of `HasGaussianLaw.indepFun_of_covariance_eq_zero` is the joint law, and this example shows that it cannot be replaced by the two marginals.

**Example (Standard Gaussian vector).** Let $Z = (Z_1, \ldots, Z_n)$ have i.i.d. standard Gaussian coordinates, and let $A$ be an $n \times n$ matrix with $A A^\top = S$. Then $m + AZ$ has characteristic function $\exp(i\langle t, m\rangle - \tfrac12 |A^\top t|^2) = \exp(i \langle t, m\rangle - \tfrac12 t^\top S t)$, so its law is $N(m, S)$. This construction shows that $N(m, S)$ exists for each positive semidefinite $S$; take for $A$ the square root of $S$.

### The library around it

The real Gaussian law is in `Mathlib.Probability.Distributions.Gaussian.Real`, with the density `gaussianPDF`, the mean, the variance, the moment generating function, the characteristic function and many affine rules (`gaussianReal_map_neg`, `gaussianReal_map_sub_const`, `gaussianReal_const_mul` for a variable with a Gaussian law). The class `IsGaussian` is in `Gaussian.Basic` and works on any topological vector space. `Gaussian.CharFun` proves that the characteristic function of a Gaussian measure has the form of the text, with `isGaussian_iff_charFun_eq` as a criterion. The files `HasGaussianLaw.*` give the random variable form and the results on independence; a version for an infinite family, `HasGaussianLaw.iIndepFun_of_covariance_eq_zero`, is in the same file. Gaussian processes are in Chapter 8.

Common errors of a learner:

- `gaussianReal μ v` takes the variance, not the standard deviation, and the variance is in `ℝ≥0`.
- A pair of variables with Gaussian laws is not jointly Gaussian in general. `HasGaussianLaw X P` and `HasGaussianLaw Y P` do not give `HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P`; independence does, by `IndepFun.hasGaussianLaw`.
- `multivariateGaussian μ S` is defined for every matrix `S`, with a junk value when `S` is not positive semidefinite (`multivariateGaussian_of_not_posSemidef`).

### Exercises

1. (A) Let $X \sim N(\mu, v)$ with $v > 0$. Show that $(X - \mu)/\sqrt{v} \sim N(0, 1)$, and express $P(X \le x)$ with the distribution function $\Phi$ of $N(0, 1)$.
2. (A) Let $Z \sim N(0, 1)$. Show that $E[Z^{2k}] = (2k - 1)(2k - 3) \cdots 3 \cdot 1$ and $E[Z^{2k+1}] = 0$, with the moment generating function.
3. (A) Let $Z \sim N(0, 1)$. Show that $Z^2$ has the law $\Gamma(1/2, 1/2)$ of Section 2.
4. (B) Let $X, Y$ be i.i.d. $N(0, 1)$. Show that $X + Y$ and $X - Y$ are independent, first with `HasGaussianLaw.indepFun_of_covariance_eq_zero` and then by a direct calculation with densities.
5. (B) The standard Cauchy law has the characteristic function $e^{-|t|}$; prove it with the residue theorem of Volume 15, or take it as given. Let $X_1, \ldots, X_n$ be i.i.d. standard Cauchy. Show that $\varphi_{\bar X_n}(t) = \varphi_{X_1}(t/n)^n = e^{-|t|}$, and conclude that $\bar X_n$ is standard Cauchy. The index of this edition has no declaration for the characteristic function of `cauchyMeasure`.
6. (B) Prove the Gaussian tail bound $P(Z \ge x) \le e^{-x^2/2}$ for $Z \sim N(0, 1)$ and $x \ge 0$, with the Chernoff bound of Chapter 3. Compare it with $P(Z \ge x) \le e^{-x^2/2}/(x\sqrt{2\pi})$.
7. (B) Let $(X, Y)$ be jointly Gaussian with mean $0$, $\operatorname{Var} X = \operatorname{Var} Y = 1$ and $\operatorname{Cov}(X, Y) = r$ with $|r| < 1$. Find $a$ such that $Y - aX$ is independent of $X$, and deduce the law of $Y$ given $X$ in the sense of Chapter 6.
8. (C) Let $\nu$ be a Gaussian measure on $\mathbb{R}^n$. Show that $\nu$ is the law of $m + AZ$ for a matrix $A$ and a standard Gaussian vector $Z$, and that $\nu$ has a density if and only if its covariance matrix is invertible.

### Notes and history

De Moivre found the Gaussian curve in 1733 as the limit of the binomial law with parameter $1/2$. Laplace extended the result and used the curve in the theory of errors, and Gauss derived the law in 1809 from the principle that the arithmetic mean is the most probable value of a measured quantity. The theorem that the sum of two independent variables is Gaussian only if each is Gaussian is due to Cramér (1936). Gaussian measures on infinite dimensional spaces, defined through the continuous linear forms as here, are the subject of the theory of abstract Wiener spaces.

### Reference

<?reference?>
