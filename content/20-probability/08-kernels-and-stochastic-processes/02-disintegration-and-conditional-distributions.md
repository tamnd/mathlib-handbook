---
title: Disintegration and conditional distributions
kind: theory
modules:
  - Mathlib.Probability.Kernel.Disintegration.Basic
  - Mathlib.Probability.Kernel.Disintegration.CondCDF
  - Mathlib.Probability.Kernel.Disintegration.StandardBorel
  - Mathlib.Probability.Kernel.Disintegration.Unique
  - Mathlib.Probability.Kernel.Disintegration.Integral
  - Mathlib.Probability.Kernel.CondDistrib
  - Mathlib.Probability.HasCondDistrib
  - Mathlib.Probability.Kernel.Posterior
explains:
  E3: [MeasureTheory.Measure.condKernel, MeasureTheory.Measure.IsCondKernel, ProbabilityTheory.condCDF, ProbabilityTheory.condDistrib, ProbabilityTheory.HasCondDistrib, ProbabilityTheory.posterior]
  E2: [MeasureTheory.Measure.disintegrate, MeasureTheory.Measure.integral_condKernel, MeasureTheory.Measure.instIsMarkovKernelCondKernel, ProbabilityTheory.condKernel_compProd, ProbabilityTheory.Kernel.condKernel, ProbabilityTheory.measure_condCDF_Iic, ProbabilityTheory.condCDF_ae_eq, ProbabilityTheory.instIsMarkovKernelCondDistrib, ProbabilityTheory.compProd_map_condDistrib, ProbabilityTheory.condDistrib_comp_map, ProbabilityTheory.condDistrib_ae_eq_condExp, ProbabilityTheory.setLIntegral_preimage_condDistrib, ProbabilityTheory.condDistrib_const, ProbabilityTheory.HasLaw.prodMk_of_hasCondDistrib, ProbabilityTheory.HasCondDistrib.hasLaw_of_const, ProbabilityTheory.HasCondDistrib.comp_left, ProbabilityTheory.HasCondDistrib.of_compProd, ProbabilityTheory.instIsMarkovKernelPosterior, ProbabilityTheory.swap_compProd_posterior, ProbabilityTheory.posterior_posterior, ProbabilityTheory.Kernel.boolKernel, ProbabilityTheory.posterior_boolKernel_apply_true]
  E1: auto
families: []
requires: [V03, V13, V15, V20.C01, V20.C02, V20.C03, V20.C04, V20.C05, V20.C06, V20.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Disintegration and conditional distributions

### Overview

Section 1 builds a joint law $\mu \otimes \kappa$ on $X \times Y$ from a law $\mu$ and a kernel $\kappa$. This section goes in the other direction. A finite measure $\rho$ on $X \times Y$ is a *disintegration* problem: find a kernel $\kappa$ with $\rho = \rho_X \otimes \kappa$, where $\rho_X$ is the first marginal. The kernel $\kappa(x)$ is the conditional law of the second coordinate given that the first is $x$. If $Y$ is a standard Borel space, such a kernel exists and is unique $\rho_X$-a.e. The conditional distribution of a variable given another variable and the posterior of Bayesian statistics are applications of this result.

### Definitions

**Definition (Conditional kernel).** Let $\rho$ be a finite measure on $X \times Y$ with first marginal $\rho_X$. A *conditional kernel* for $\rho$ is a Markov kernel $\kappa$ from $X$ to $Y$ with $\rho_X \otimes \kappa = \rho$, that is,
$$\rho(A \times B) = \int_A \kappa(x)(B)\, \rho_X(dx) \quad \text{for all measurable } A, B.$$

::: mathlib
`MeasureTheory.Measure.IsCondKernel` · `Mathlib.Probability.Kernel.Disintegration.Basic`

`ρ.IsCondKernel ρCond` is a class that says `ρ.fst ⊗ₘ ρCond = ρ`. `Measure.disintegrate` extracts the equation. The class lets the library state results for each conditional kernel, and the canonical one below is an instance.

<?decl MeasureTheory.Measure.IsCondKernel?>
:::

::: mathlib
`MeasureTheory.Measure.condKernel` · `Mathlib.Probability.Kernel.Disintegration.StandardBorel`

`ρ.condKernel : Kernel α Ω` is a conditional kernel for a finite measure `ρ` on `α × Ω`, for a standard Borel `Ω` and any measurable space `α`. It is a Markov kernel (`Measure.instIsMarkovKernelCondKernel`). `Measure.integral_condKernel` is the iterated integral $\int_X \int_Y f(x, y)\, \kappa(x)(dy)\, \rho_X(dx) = \int f\, d\rho$. `condKernel_compProd` is the uniqueness: the conditional kernel of `μ ⊗ₘ κ` is `κ`, `μ`-a.e. `Kernel.condKernel` is the form for a kernel to a product space, with parameters.

<?decl MeasureTheory.Measure.condKernel?>
:::

**Definition (Conditional distribution function).** For a finite measure $\rho$ on $X \times \mathbb{R}$, a *conditional distribution function* is a map $F : X \times \mathbb{R} \to [0, 1]$ such that $F(x, \cdot)$ is a distribution function for each $x$, $F(\cdot, t)$ is measurable for each $t$, and $\rho(A \times (-\infty, t]) = \int_A F(x, t)\, \rho_X(dx)$.

::: mathlib
`ProbabilityTheory.condCDF` · `Mathlib.Probability.Kernel.Disintegration.CondCDF`

`condCDF ρ a` is a Stieltjes function, the conditional distribution function at `a`. Its measure is a probability measure with `measure_condCDF_Iic`. It is built from the Radon-Nikodym derivatives `preCDF ρ r` of the measures $A \mapsto \rho(A \times (-\infty, r])$ with respect to $\rho_X$, for rational $r$. `condCDF_ae_eq` says that `condCDF` agrees with these derivatives a.e.

<?decl ProbabilityTheory.condCDF?>
:::

**Definition (Conditional distribution).** Let $X : \Omega \to E$ and $Y : \Omega \to F$ be measurable, with $F$ standard Borel. The *conditional distribution* of $Y$ given $X$ is a Markov kernel $\kappa$ from $E$ to $F$ such that the law of $(X, Y)$ is $\mathcal{L}(X) \otimes \kappa$. It is the conditional kernel of the law of $(X, Y)$.

::: mathlib
`ProbabilityTheory.condDistrib` · `Mathlib.Probability.Kernel.CondDistrib`

`condDistrib Y X μ : Kernel β Ω` is `(μ.map (fun a ↦ (X a, Y a))).condKernel`. It is a Markov kernel (`instIsMarkovKernelCondDistrib`). `compProd_map_condDistrib` is the defining property `μ.map X ⊗ₘ condDistrib Y X μ = μ.map (X, Y)`, and `condDistrib_comp_map` gives the law of `Y` back. `condDistrib_ae_eq_condExp` connects it with Chapter 6: `condDistrib Y X μ (X a) s` is a.e. the conditional probability $P(Y \in s \mid X)$. `setLIntegral_preimage_condDistrib` is $\int_{\{X \in t\}} \kappa(X)(s)\, dP = P(X \in t, Y \in s)$.

<?decl ProbabilityTheory.condDistrib?>
:::

::: mathlib
`ProbabilityTheory.HasCondDistrib` · `Mathlib.Probability.HasCondDistrib`

`HasCondDistrib Y X κ P` says that `κ` is the conditional distribution of `Y` given `X` under `P`, in the a.e. sense. It is the analogue of `HasLaw` from Chapter 1, and it does not need a standard Borel space. `HasLaw.prodMk_of_hasCondDistrib` gives the law `Q ⊗ₘ κ` of `(X, Y)` from the law `Q` of `X`. `HasCondDistrib.hasLaw_of_const` says that a constant conditional distribution is the law of `Y`. `HasCondDistrib.comp_left` and `HasCondDistrib.of_compProd` are the rules for a function of `Y` and for the chain rule of conditional laws.

<?decl ProbabilityTheory.HasCondDistrib?>
:::

**Definition (Posterior).** Let $\mu$ be a prior law on a parameter space $\Theta$ and let $\kappa$ be a kernel from $\Theta$ to a sample space $X$: the law of the data given the parameter. The *posterior* is a kernel $\kappa^\dagger$ from $X$ to $\Theta$ with
$$(\kappa \circ \mu) \otimes \kappa^\dagger = \operatorname{swap}_*(\mu \otimes \kappa).$$
It is the conditional law of the parameter given the data.

::: mathlib
`ProbabilityTheory.posterior` · `Mathlib.Probability.Kernel.Posterior`

`posterior κ μ`, with the notation `κ†μ`, is defined for a standard Borel parameter space `Ω`, through `condKernel`. It is a Markov kernel (`instIsMarkovKernelPosterior`). `swap_compProd_posterior` is the defining equation, and `posterior_posterior` says that the posterior of the posterior is `κ`, a.e. For the kernel `Kernel.boolKernel μ ν` from `Bool`, `posterior_boolKernel_apply_true` is Bayes' formula with Radon-Nikodym derivatives.

<?decl ProbabilityTheory.posterior?>
:::

### Theorems and proofs

**Theorem (Disintegration on the real line).** Let $\rho$ be a finite measure on $X \times \mathbb{R}$. Then $\rho$ has a conditional kernel.

*Proof sketch.* For rational $r$, the measure $A \mapsto \rho(A \times (-\infty, r])$ is below $\rho_X$, so it has a Radon-Nikodym derivative $G_r$ with $0 \le G_r \le 1$ a.e. (Volume 18). For $r < s$, $G_r \le G_s$ a.e., and $G_r \to 0$ as $r \to -\infty$ and $G_r \to 1$ as $r \to \infty$ a.e., by the monotone convergence theorem. There are countably many rationals, so off one null set $N$ all these properties hold. For $x \notin N$, let $F(x, t) = \inf_{r > t,\, r \in \mathbb{Q}} G_r(x)$: it is a distribution function. For $x \in N$, let $F(x, \cdot)$ be a fixed distribution function. Then $\kappa(x)$, the measure of $F(x, \cdot)$, is a Markov kernel, and $\rho(A \times (-\infty, t]) = \int_A F(x, t)\, \rho_X(dx)$ for all $t$. The sets $A \times (-\infty, t]$ form a $\pi$-system that generates the product $\sigma$-algebra, so $\rho = \rho_X \otimes \kappa$. $\square$

**Theorem (Disintegration on a standard Borel space).** If $Y$ is standard Borel, then each finite measure on $X \times Y$ has a conditional kernel, and it is unique $\rho_X$-a.e.

*Proof.* A standard Borel space has a measurable embedding $\iota : Y \to \mathbb{R}$ with a measurable image. Disintegrate the image measure of $\rho$ on $X \times \mathbb{R}$. The kernel gives full measure to $\iota(Y)$ for $\rho_X$-a.e. $x$, so it pulls back to $Y$, after a change on a null set. For the uniqueness, two conditional kernels $\kappa$ and $\kappa'$ give $\int_A \kappa(x)(B)\, d\rho_X = \int_A \kappa'(x)(B)\, d\rho_X$ for all $A$, so $\kappa(x)(B) = \kappa'(x)(B)$ a.e. for each $B$. Use a countable $\pi$-system that generates the $\sigma$-algebra of $Y$. $\square$

Mathlib follows these steps: `condCDF` for the real case, and `Measure.condKernel` through the embedding.

**Theorem (Conditional expectation as an integral).** If $Y$ is real and integrable and $\kappa$ is the conditional distribution of $Y$ given $X$, then $E[Y \mid X] = \int y\, \kappa(X)(dy)$ a.s. More generally, $E[g(X, Y) \mid X] = \int g(X, y)\, \kappa(X)(dy)$ for an integrable $g(X, Y)$.

*Proof.* The right side is $\sigma(X)$-measurable. For a set $\{X \in A\}$, the iterated integral formula for $\mathcal{L}(X) \otimes \kappa$ gives $E[g(X, Y) \mathbf{1}_A(X)] = \int_A \int g(x, y)\, \kappa(x)(dy)\, \mathcal{L}(X)(dx)$. $\square$

### Examples

**Example (The Gaussian pair).** Let $(X, Y)$ be a centred Gaussian vector with unit variances and correlation $r \in (-1, 1)$. Then $Y = rX + \sqrt{1 - r^2}\, Z$ with $Z$ standard Gaussian and independent of $X$. So the conditional distribution of $Y$ given $X = x$ is $\mathcal{N}(rx, 1 - r^2)$, and $\kappa(x) = \mathcal{N}(rx, 1 - r^2)$ is a conditional kernel. It agrees with the regression of Chapter 6: $E[Y \mid X] = rX$.

**Example (Bayes for a diagnostic test).** A disease has the prior probability $0.01$. A test is positive with probability $0.99$ for an ill person and $0.05$ for a healthy person. With $\Theta = \{\text{ill}, \text{healthy}\}$ and $X = \{+, -\}$, the posterior is
$$\kappa^\dagger(+)(\{\text{ill}\}) = \frac{0.01 \cdot 0.99}{0.01 \cdot 0.99 + 0.99 \cdot 0.05} = \frac{0.0099}{0.0594} = \frac{1}{6} \approx 0.167.$$
A positive result raises the probability from $1\%$ to about $17\%$ only.

**Counterexample (The Borel-Kolmogorov paradox).** Let a point be uniform on the sphere $S^2$. Given that it is on the equator, its longitude is uniform. Given that it is on the meridian of longitude $0$ and its antipode, its latitude $\theta$ is not uniform: it has the density $\frac{1}{2}\cos\theta$ on $[-\pi/2, \pi/2]$, from the conditional distribution of the latitude given the longitude. The equator and a full meridian are congruent great circles, so the two answers show that a conditional law on one null event has no meaning. A conditional distribution is a kernel, defined a.e. for a given variable, and its value at one point depends on the variable.

### The library around it

The directory `Mathlib/Probability/Kernel/Disintegration/` has the construction. `CondCDF.lean` does the real case for measures, `StandardBorel.lean` extends it to standard Borel spaces and to kernels, `Unique.lean` proves the uniqueness, and `Integral.lean` has the integral formulas, such as `setIntegral_condKernel`. `Kernel.condKernel` needs either a countable source or a countably generated $\sigma$-algebra, which is the `CountableOrCountablyGenerated` class.

Chapter 6 uses `condDistrib` to build `condExpKernel`, and the distribution function `ProbabilityTheory.cdf` of Chapter 4 is built from `condCDF` with the measure on `Unit × ℝ`.

### Exercises

1. (A) Let $\rho = \mu \times \nu$ be a product of probability measures. Prove that the constant kernel $\kappa(x) = \nu$ is a conditional kernel for $\rho$.
2. (A) For a finite set $X \times Y$ with $\rho(\{(x, y)\}) = p_{xy}$, compute the conditional kernel and explain the choice at points $x$ with $\sum_y p_{xy} = 0$.
3. (A) In the Bayes example, compute the posterior probability of illness after two independent positive tests.
4. (B) Prove that $Y$ and $X$ are independent if and only if the conditional distribution of $Y$ given $X$ is a.e. constant.
5. (B) Let $\Theta$ have the uniform law on $[0, 1]$, and given $\Theta = \theta$ let $X$ be the number of successes in $n$ Bernoulli trials with parameter $\theta$. Prove that the posterior given $X = k$ is the Beta law with parameters $k + 1$ and $n - k + 1$.
6. (B) Let $(X, Y)$ have the density $f$ on $\mathbb{R}^2$. Prove that $\kappa(x)(dy) = f(x, y) / f_X(x)\, dy$ is a conditional kernel where $f_X(x) > 0$.
7. (C) Compute the density of the latitude in the Borel-Kolmogorov paradox, with the change of variables to longitude and latitude.

### Notes and history

Kolmogorov discussed the paradox of the sphere in his *Grundbegriffe* of 1933, and used it to explain that conditional probability with respect to a null event depends on the $\sigma$-algebra. The existence of regular conditional probabilities on Polish spaces is a classical result of measure theory. Bayes' paper on inverse probability was published in 1763, after his death.

### Reference

<?reference?>
