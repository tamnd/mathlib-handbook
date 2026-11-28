---
title: Gaussian measures on Banach spaces and Gaussian processes
kind: api
modules:
  - Mathlib.Probability.Moments.CovarianceBilinDual
  - Mathlib.Probability.Distributions.Fernique
  - Mathlib.Probability.Distributions.Gaussian.Fernique
  - Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
  - Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
  - Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess
explains:
  E2: [ProbabilityTheory.covarianceBilinDual, ProbabilityTheory.covarianceBilinDual_apply, ProbabilityTheory.isPosSemidef_covarianceBilinDual, ContinuousLinearMap.rotation, ProbabilityTheory.exists_integrable_exp_sq_of_map_rotation_eq_self, ProbabilityTheory.IsGaussian.exists_integrable_exp_sq, ProbabilityTheory.IsGaussian.memLp_id, ProbabilityTheory.IsGaussianProcess.of_isGaussianProcess, ProbabilityTheory.IsGaussianProcess.iIndepFun_of_covariance_eq_zero, ProbabilityTheory.HasIndepIncrements.isGaussianProcess]
  E1: auto
families: []
requires: [V18, V20.C02, V20.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Gaussian measures on Banach spaces and Gaussian processes

### Overview

Section 3 defined a Gaussian measure on a normed space $E$ by its one dimensional images. A finite measure $\mu$ on $E$ is Gaussian when, for each continuous linear form $L$ on $E$, the image measure $L_* \mu$ is a Gaussian law on $\mathbb{R}$, possibly with variance $0$. The definition does not ask $E$ to have a finite dimension, and it does not ask $\mu$ to have moments. This section describes three results that the definition makes possible, and the extension of the notion from measures to processes.

The first result is the covariance of a measure on a Banach space. In finite dimension the covariance is a matrix. In general it is a bilinear form on the dual space: the covariance of $L_1$ and $L_2$ is the covariance of the two real random variables $L_1$ and $L_2$ under $\mu$.

The second result is the theorem of Fernique. A Gaussian measure on a separable Banach space has a square exponential moment: there is $C > 0$ with
$$\int \exp(C \|x\|^2) \, d\mu(x) < \infty.$$
So the norm of a Gaussian vector has tails like those of a real Gaussian variable, and it has finite moments of all orders. This is surprising at first, because the definition controls only the one dimensional images, and the norm on an infinite dimensional space is not a function of finitely many of them.

The third result is about processes. A process $(X_t)_{t \in T}$ is Gaussian when each finite vector $(X_{t_1}, \dots, X_{t_n})$ has a Gaussian law. Section 3 of Chapter 8 gives the definition. The modules of this section prove that linear operations preserve Gaussian processes, that uncorrelated parts of a Gaussian process are independent, and that a process with independent Gaussian increments is a Gaussian process.

### The library around it

#### The covariance on the dual

The module `Mathlib.Probability.Moments.CovarianceBilinDual` works with a measure $\mu$ on a normed space $E$ and the dual space `StrongDual` $\mathbb{R}$ $E$. The map `StrongDual.toLp` $\mu$ $p$ sends a continuous linear form to its class in $L^p(\mu)$. It is a continuous linear map when the identity of $E$ is in $L^p(\mu)$, and it is $0$ otherwise. The form `ProbabilityTheory.uncenteredCovarianceBilinDual` $\mu$ is the inner product in $L^2(\mu)$ of the images of $L_1$ and $L_2$.

The form `ProbabilityTheory.covarianceBilinDual` $\mu$ is the uncentered form of the image of $\mu$ under $x \mapsto x - \int x \, d\mu$. It is a continuous bilinear form on the dual. The theorem `ProbabilityTheory.covarianceBilinDual_apply` computes it, for a finite measure on a Banach space with a second moment:
$$\mathrm{Cov}_\mu(L_1, L_2) = \int (L_1(x) - \mu[L_1]) (L_2(x) - \mu[L_2]) \, d\mu(x).$$
The theorem `ProbabilityTheory.covarianceBilinDual_self_eq_variance` gives the variance of $L$ on the diagonal, and `ProbabilityTheory.covarianceBilinDual_eq_covariance` gives the covariance of the two real variables. The form is symmetric and nonnegative, so it is positive semidefinite by `ProbabilityTheory.isPosSemidef_covarianceBilinDual`. Without a second moment, the form is $0$ by convention, by `ProbabilityTheory.covarianceBilinDual_of_not_memLp`.

#### The theorem of Fernique for rotation invariant measures

The module `Mathlib.Probability.Distributions.Fernique` proves the theorem in a form that does not mention Gaussian measures. The map `ContinuousLinearMap.rotation` $\theta$ is the rotation of angle $\theta$ on $E \times E$:
$$(x, y) \mapsto (\cos \theta \, x + \sin \theta \, y, \; -\sin \theta \, x + \cos \theta \, y).$$
The hypothesis is that the product measure $\mu \otimes \mu$ is invariant under the rotation of angle $-\pi/4$. The key estimate is `ProbabilityTheory.measure_le_mul_measure_gt_le_of_map_rotation_eq_self`:
$$\mu(\|x\| \le a) \, \mu(\|x\| > b) \le \mu\Big(\|x\| > \frac{b - a}{\sqrt{2}}\Big)^2.$$
Its proof rotates the product of two bands in the plane. Iterated along a sequence of thresholds that grows like $(\sqrt{2})^n$, the estimate gives a square exponential decay of the tail. The main theorem `ProbabilityTheory.exists_integrable_exp_sq_of_map_rotation_eq_self` concludes that $x \mapsto \exp(C \|x\|^2)$ is integrable for some $C > 0$, for each finite measure on a second countable normed space with this invariance.

#### The theorem of Fernique for Gaussian measures

The module `Mathlib.Probability.Distributions.Gaussian.Fernique` applies this to Gaussian measures. The theorem `ProbabilityTheory.IsGaussian.map_rotation_eq_self` says that a centered Gaussian measure $\mu$ on a separable Banach space has a product $\mu \otimes \mu$ that is invariant under each rotation. The proof compares characteristic functions on the dual: for a centered Gaussian measure, the characteristic function at $L$ is $\exp(-\mathrm{Var}(L)/2)$, and the rotation preserves this expression. A general Gaussian measure is not centered, so the proof applies the result to the convolution of $\mu$ with its image under $x \mapsto -x$, which is centered and Gaussian.

The result is `ProbabilityTheory.IsGaussian.exists_integrable_exp_sq`: for a Gaussian measure on a second countable Banach space, there is $C > 0$ such that $x \mapsto \exp(C \|x\|^2)$ is integrable. The consequence `ProbabilityTheory.IsGaussian.memLp_id` says that the identity is in $L^p(\mu)$ for each finite $p$. So a Gaussian measure has a mean and a covariance, and `ProbabilityTheory.IsGaussian.integral_dual` gives $\mu[L] = L(\int x \, d\mu)$ for each form $L$. A Gaussian measure that is not a Dirac mass has no atoms, by the instance `ProbabilityTheory.IsGaussian.noAtoms`.

#### Gaussian processes

A process $X : T \to \Omega \to E$ is a Gaussian process under $P$ when, for each finite set $I \subseteq T$, the vector $(X_t)_{t \in I}$ has a Gaussian law. The predicate `ProbabilityTheory.IsGaussianProcess` of Chapter 8 records this. The module `Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic` gives its closure properties. The theorem `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_eval` says that each $X_t$ is Gaussian, and the lemmas `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_add`, `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_sum` and `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_increments` give the sums and the increments. The general statement is `ProbabilityTheory.IsGaussianProcess.of_isGaussianProcess`: if each $Y_s$ is a continuous linear image of finitely many values of a Gaussian process $X$, then $Y$ is a Gaussian process. The special cases are a change of index set, a linear map applied to each value, a scalar factor, and the shift $t \mapsto X_{t_0 + t} - X_{t_0}$, in `ProbabilityTheory.IsGaussianProcess.shift`. A modification of a Gaussian process is a Gaussian process, by `ProbabilityTheory.IsGaussianProcess.congr`.

The module `Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence` extends the theorem of Section 3 on uncorrelated Gaussian vectors. The theorem `ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_eq_zero` says that two real processes $X$ and $Y$ that are jointly Gaussian are independent when $\mathrm{Cov}(X_s, Y_t) = 0$ for all $s$ and $t$. The theorem `ProbabilityTheory.IsGaussianProcess.iIndepFun_of_covariance_eq_zero` is the version for a family of processes. The variants `ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_strongDual` and `ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_inner` treat processes with values in a normed space and in a Hilbert space.

The module `Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess` proves `ProbabilityTheory.HasIndepIncrements.isGaussianProcess`. Let $T$ have a least element $\bot$, and let $X$ have independent increments, Gaussian values $X_t$, and $X_\bot = 0$ almost surely. Then $X$ is a Gaussian process. The proof writes $(X_{t_1}, \dots, X_{t_n})$ as a linear image of the increments, and the vector of independent Gaussian increments is Gaussian. This theorem is a step in the construction of Brownian motion.

#### Common errors

1. The form `ProbabilityTheory.covarianceBilinDual` is $0$ when the identity is not in $L^2(\mu)$. A lemma that computes it needs the hypothesis of a second moment. For a Gaussian measure, `ProbabilityTheory.IsGaussian.memLp_id` gives this hypothesis.
2. The theorem of Fernique needs a second countable space, so that the product $\sigma$-algebra on $E \times E$ is the Borel $\sigma$-algebra. A nonseparable Banach space does not satisfy the hypothesis.
3. A process with Gaussian values $X_t$ need not be a Gaussian process. The condition is on all finite vectors, and `ProbabilityTheory.HasIndepIncrements.isGaussianProcess` needs independent increments to close this gap.

### Exercises

1. (A) Show that the covariance form of a Dirac mass is $0$, and that the covariance form of the image of $\mu$ under $x \mapsto x + c$ is the covariance form of $\mu$.
2. (A) Let $\mu$ be the standard Gaussian measure on $\mathbb{R}^n$. Show that $\mu \otimes \mu$ is invariant under each rotation of $\mathbb{R}^n \times \mathbb{R}^n$ of the form above, with the density of $\mu \otimes \mu$.
3. (B) Prove the band estimate $\mu(\|x\| \le a) \, \mu(\|x\| > b) \le \mu(\|x\| > (b - a)/\sqrt{2})^2$ for a measure with a rotation invariant product. Use the triangle inequality for $\|x - y\|$ and $\|x + y\|$.
4. (B) Show that a real process $X$ is a Gaussian process if and only if each finite linear combination $\sum_i c_i X_{t_i}$ has a Gaussian law.
5. (B) Let $X$ be a centered real Gaussian process. Show that $X_s$ and $X_t - \frac{\mathrm{Cov}(X_s, X_t)}{\mathrm{Var}(X_s)} X_s$ are independent when $\mathrm{Var}(X_s) > 0$.
6. (C) Deduce from the theorem of Fernique that a Gaussian measure on a separable Banach space has $\int \|x\|^p \, d\mu < \infty$ for each $p < \infty$, and give a bound in terms of the constant $C$ and the integral of $\exp(C \|x\|^2)$.

### Reference

<?reference?>
