---
title: Variance and covariance
kind: theory
modules:
  - Mathlib.Probability.Moments.Variance
  - Mathlib.Probability.Moments.Covariance
  - Mathlib.Probability.Moments.CovarianceBilin
explains:
  E3: [ProbabilityTheory.variance, ProbabilityTheory.evariance, ProbabilityTheory.covariance, ProbabilityTheory.meas_ge_le_variance_div_sq, ProbabilityTheory.IndepFun.variance_sum]
  E2: [ProbabilityTheory.variance_eq_sub, ProbabilityTheory.variance_eq_integral, ProbabilityTheory.variance_nonneg, ProbabilityTheory.variance_const_mul, ProbabilityTheory.variance_add, ProbabilityTheory.variance_sum, ProbabilityTheory.IndepFun.variance_add, ProbabilityTheory.covariance_eq_sub, ProbabilityTheory.covariance_self, ProbabilityTheory.IndepFun.covariance_eq_zero, ProbabilityTheory.evariance_lt_top_iff_memLp, ProbabilityTheory.ae_eq_integral_of_variance_eq_zero, ProbabilityTheory.variance_le_sq_of_bounded, ProbabilityTheory.covarianceBilin, ProbabilityTheory.isPosSemidef_covarianceBilin]
  E1: auto
families: []
requires: [V03, V13, V15, V20.C01, V20.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Variance and covariance

### Overview

The expectation gives the centre of a law. The variance measures its spread: it is the mean square distance of the variable from its expectation. Two facts make the variance the main tool of elementary probability. Chebyshev's inequality turns a bound on the variance into a bound on the probability of a large deviation. And the variance of a sum of independent variables is the sum of the variances, so the spread of a sum of $n$ variables grows like $\sqrt{n}$, not like $n$. These two facts together give the weak law of large numbers in Chapter 5. The covariance measures the linear dependence of two variables and is the correction term in the variance of a sum of dependent variables.

### Definitions

**Definition (Variance).** Let $X$ be a real variable with $E[X^2] < \infty$, and put $m = E[X]$. The *variance* of $X$ is
$$\operatorname{Var}(X) = E[(X - m)^2],$$
and the *standard deviation* is $\sigma(X) = \sqrt{\operatorname{Var}(X)}$. For a variable with $E[X^2] = \infty$, the variance is $+\infty$ in $[0, \infty]$.

A variable with $E[X^2] < \infty$ is *square integrable*, or in $L^2$. On a probability space $L^2 \subseteq L^1$ by the Cauchy-Schwarz inequality, so $m$ exists.

::: mathlib
`ProbabilityTheory.evariance` · `Mathlib.Probability.Moments.Variance`

`evariance X μ : ℝ≥0∞` is `∫⁻ ω, ‖X ω - μ[X]‖ₑ ^ 2 ∂μ`, the extended variance, which may be `∞`. For a finite measure and a.e. strongly measurable `X`, `evariance_lt_top_iff_memLp` says that it is finite if and only if `MemLp X 2 μ`.

<?decl ProbabilityTheory.evariance?>
:::

::: mathlib
`ProbabilityTheory.variance` · `Mathlib.Probability.Moments.Variance`

`variance X μ : ℝ` is `(evariance X μ).toReal`, so it has the junk value `0` for a variable not in $L^2$. The notation `Var[X; μ]` is available, and `Var[X]` for the measure `volume`. The lemma `variance_eq_integral` gives the formula of the definition for a.e. measurable `X`. Most lemmas about `variance` take `MemLp X 2 μ` as a hypothesis.

<?decl ProbabilityTheory.variance?>
:::

**Definition (Covariance).** Let $X, Y \in L^2$. The *covariance* of $X$ and $Y$ is
$$\operatorname{Cov}(X, Y) = E[(X - E[X])(Y - E[Y])].$$
The variables are *uncorrelated* if $\operatorname{Cov}(X, Y) = 0$. If both variances are positive, the *correlation* is $\rho(X, Y) = \operatorname{Cov}(X, Y)/(\sigma(X)\sigma(Y))$, and the Cauchy-Schwarz inequality gives $|\rho| \le 1$.

For a random vector $X = (X_1, \ldots, X_d)$ in $L^2$, the *covariance matrix* is $C_{ij} = \operatorname{Cov}(X_i, X_j)$. It is symmetric and positive semidefinite, because $u^T C u = \operatorname{Var}(u_1 X_1 + \cdots + u_d X_d) \ge 0$.

::: mathlib
`ProbabilityTheory.covariance` · `Mathlib.Probability.Moments.Covariance`

`covariance X Y μ = ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ`, with the notation `cov[X, Y; μ]`. It has no integrability hypothesis in the definition, and many algebraic lemmas (`covariance_comm`, `covariance_const_mul_left`, `covariance_add_left`) hold with `MemLp` hypotheses. `covariance_self` says `cov[X, X; μ] = Var[X; μ]`.

<?decl ProbabilityTheory.covariance?>
:::

::: mathlib
`ProbabilityTheory.covarianceBilin` · `Mathlib.Probability.Moments.CovarianceBilin`

For a measure `μ` on a real inner product space `E`, `covarianceBilin μ : E →L[ℝ] E →L[ℝ] ℝ` is the continuous bilinear form $(x, y) \mapsto \int \langle x, z - m\rangle\langle y, z - m\rangle\, d\mu(z)$, where $m$ is the mean. It is the covariance matrix without a basis. `isPosSemidef_covarianceBilin` is the positivity of the text. Section 3 of Chapter 4 uses it for the Gaussian laws in several dimensions.

<?decl ProbabilityTheory.covarianceBilin?>
:::

### Theorems and proofs

**Theorem (Rules for the variance).** Let $X, Y \in L^2$ and $a, b \in \mathbb{R}$.

1. $\operatorname{Var}(X) = E[X^2] - (E[X])^2$.
2. $\operatorname{Var}(aX + b) = a^2 \operatorname{Var}(X)$.
3. $\operatorname{Var}(X) = 0$ if and only if $X = E[X]$ a.s.
4. $\operatorname{Var}(X + Y) = \operatorname{Var}(X) + 2\operatorname{Cov}(X, Y) + \operatorname{Var}(Y)$, and $\operatorname{Cov}(X, Y) = E[XY] - E[X]E[Y]$.

*Proof.* 1. Expand $(X - m)^2 = X^2 - 2mX + m^2$ and use linearity with $E[1] = 1$: $E[X^2] - 2m^2 + m^2$. 2. $aX + b - E[aX + b] = a(X - m)$. 3. $E[(X - m)^2] = 0$ for a nonnegative variable means $(X - m)^2 = 0$ a.s. 4. Put $\bar X = X - E[X]$ and $\bar Y = Y - E[Y]$. Then $(\bar X + \bar Y)^2 = \bar X^2 + 2\bar X \bar Y + \bar Y^2$; take expectations. The second formula is the expansion of $E[\bar X \bar Y]$ as in 1. $\square$

::: mathlib
`ProbabilityTheory.variance_eq_sub` · `Mathlib.Probability.Moments.Variance`

For a probability measure and `MemLp X 2 μ`: `variance X μ = μ[X ^ 2] - μ[X] ^ 2`. The other rules are `variance_const_mul`, `variance_add_const`, `ae_eq_integral_of_variance_eq_zero` and `variance_add`. For a finite family, `variance_sum` gives `Var[∑ i, X i] = ∑ i, ∑ j, cov[X i, X j]`.

<?decl ProbabilityTheory.variance_eq_sub?>
:::

**Theorem (Variance of a sum of independent variables).** Let $X_1, \ldots, X_n \in L^2$ be pairwise independent. Then
$$\operatorname{Var}(X_1 + \cdots + X_n) = \operatorname{Var}(X_1) + \cdots + \operatorname{Var}(X_n).$$

*Proof.* For $i \neq j$, $X_i$ and $X_j$ are independent, so $E[X_i X_j] = E[X_i]E[X_j]$ by Section 1, and $\operatorname{Cov}(X_i, X_j) = 0$. Expand the variance of the sum as $\sum_{i,j} \operatorname{Cov}(X_i, X_j)$, which is the iterated form of rule 4. Only the terms with $i = j$ remain. $\square$

Only pairwise independence is used, in fact only that the variables are pairwise uncorrelated. Etemadi's strong law in Chapter 5 uses this weak hypothesis.

::: mathlib
`ProbabilityTheory.IndepFun.variance_sum` · `Mathlib.Probability.Moments.Variance`

For a finset `s`, `∀ i ∈ s, MemLp (X i) 2 μ` and `(s : Set ι).Pairwise (fun i j ↦ IndepFun (X i) (X j) μ)`: `Var[∑ i ∈ s, X i; μ] = ∑ i ∈ s, Var[X i; μ]`. The hypothesis is pairwise independence, as in the text. The case of two variables is `IndepFun.variance_add`, and the step through the covariance is `IndepFun.covariance_eq_zero`.

<?decl ProbabilityTheory.IndepFun.variance_sum?>
:::

**Theorem (Chebyshev's inequality).** Let $X \in L^2$ and $c > 0$. Then
$$P(|X - E[X]| \ge c) \le \frac{\operatorname{Var}(X)}{c^2}.$$

*Proof.* Apply Markov's inequality of Section 1 to the nonnegative variable $(X - E[X])^2$ and the level $c^2$: $P((X - E[X])^2 \ge c^2) \le E[(X - E[X])^2]/c^2$. The event on the left is $\{|X - E[X]| \ge c\}$. $\square$

::: mathlib
`ProbabilityTheory.meas_ge_le_variance_div_sq` · `Mathlib.Probability.Moments.Variance`

For a finite measure, `MemLp X 2 μ` and `0 < c`: `μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (Var[X; μ] / c ^ 2)`. The form with `evariance` needs no `MemLp` hypothesis: `meas_ge_le_evariance_div_sq`.

<?decl ProbabilityTheory.meas_ge_le_variance_div_sq?>
:::

**Theorem (Bounded variables).** If $a \le X \le b$ a.s., then $\operatorname{Var}(X) \le (b - a)^2/4$.

*Proof.* Put $c = (a + b)/2$. Then $|X - c| \le (b - a)/2$. The function $t \mapsto E[(X - t)^2]$ has its minimum at $t = E[X]$, because $E[(X - t)^2] = \operatorname{Var}(X) + (E[X] - t)^2$. So $\operatorname{Var}(X) \le E[(X - c)^2] \le (b - a)^2/4$. $\square$

This is `variance_le_sq_of_bounded`. Equality holds for the variable that takes the values $a$ and $b$ with probability $1/2$ each.

### Examples

**Example (The binomial variance).** Let $S_n = X_1 + \cdots + X_n$ with $X_i$ independent and $P(X_i = 1) = p$, $P(X_i = 0) = 1 - p$. Then $E[X_i] = p$ and $E[X_i^2] = p$, so $\operatorname{Var}(X_i) = p - p^2 = p(1 - p)$. By the theorem on sums,
$$E[S_n] = np, \qquad \operatorname{Var}(S_n) = np(1 - p).$$
A direct computation from the binomial law needs the identities $\sum_k k\binom{n}{k}p^k(1-p)^{n-k} = np$ and $\sum_k k(k-1)\binom{n}{k}p^k(1-p)^{n-k} = n(n-1)p^2$. The decomposition into indicators avoids them.

**Example (Chebyshev for a poll).** A poll asks $n$ people, chosen independently, a yes or no question. The true proportion of yes is $p$. The proportion in the sample is $S_n/n$, with mean $p$ and variance $p(1-p)/n \le 1/(4n)$. Chebyshev gives
$$P(|S_n/n - p| \ge 0.05) \le \frac{1}{4n (0.05)^2} = \frac{100}{n}.$$
For an error probability of at most $5\%$, $n = 2000$ is sufficient. The central limit theorem of Chapter 5 shows that $n \approx 385$ is sufficient, and the Chernoff bound of Section 3 gives an exponential bound.

**Counterexample (Uncorrelated is not independent).** Let $U$ be uniform on $[0, 2\pi]$, $X = \cos U$ and $Y = \sin U$. Then $E[X] = E[Y] = 0$ and $E[XY] = \frac{1}{2\pi}\int_0^{2\pi} \cos u \sin u\, du = 0$, so $\operatorname{Cov}(X, Y) = 0$. But $X^2 + Y^2 = 1$, so $P(|X| > 0.8, |Y| > 0.8) = 0 \neq P(|X| > 0.8)P(|Y| > 0.8)$, and the variables are not independent.

**Example (The number of fixed points).** In the example of Section 1, $F = \sum_i \mathbf{1}_{A_i}$ with $P(A_i) = 1/n$ and $P(A_i \cap A_j) = 1/(n(n-1))$ for $i \neq j$. So $\operatorname{Cov}(\mathbf{1}_{A_i}, \mathbf{1}_{A_j}) = \frac{1}{n(n-1)} - \frac{1}{n^2} = \frac{1}{n^2(n-1)}$, and
$$\operatorname{Var}(F) = n \cdot \frac{1}{n}\Big(1 - \frac1n\Big) + n(n-1) \cdot \frac{1}{n^2(n-1)} = 1.$$
The mean and the variance of $F$ are both $1$, as for a Poisson law with parameter $1$, which is the limit law of $F$.

### The library around it

`Mathlib.Probability.Moments.Variance` has about seventy lemmas: algebraic rules (`variance_neg`, `variance_sub`, `variance_smul`), the law form `variance_map` (the variance depends only on the law), the bounds `variance_le_expectation_sq` and `variance_le_sub_mul_sub` (the Bhatia-Davis inequality $\operatorname{Var}(X) \le (b - E X)(E X - a)$), and the sums. `Mathlib.Probability.Moments.Covariance` has the bilinearity of `covariance` in many forms, with sums over finsets (`covariance_sum_sum`). `Mathlib.Probability.Moments.CovarianceBilin` has the covariance form on an inner product space and the covariance operator `covarianceOperator`.

Common errors of a learner:

- `variance X μ = 0` does not mean that `X` is a.s. constant: the junk value is `0` for `X ∉ L²`. Use `evariance`, or carry `MemLp X 2 μ`.
- `MemLp X 2 μ` is the hypothesis, not `Integrable (X ^ 2) μ`. The bridge is `memLp_two_iff_integrable_sq`.
- The variance is defined with `μ[X]`, the integral, so for a measure that is not a probability measure the formulas change. `variance_eq_sub` needs `IsProbabilityMeasure μ`.

### Exercises

1. (A) Compute the variance of the result of a fair die.
2. (A) Let $X$ be uniform on $[a, b]$. Show that $\operatorname{Var}(X) = (b - a)^2/12$.
3. (A) Show that $\operatorname{Cov}(X, Y) = 0$ when $X$ is a.s. constant, and that $\operatorname{Cov}$ is bilinear and symmetric.
4. (B) Let $X_1, \ldots, X_n \in L^2$ be i.i.d. with variance $\sigma^2$, and let $\bar X = \frac1n \sum_i X_i$. Show that $E\big[\sum_i (X_i - \bar X)^2\big] = (n - 1)\sigma^2$.
5. (B) An urn holds $r$ red and $b$ blue balls. Draw $n$ balls without replacement and let $R$ be the number of red balls. Compute $E[R]$ and $\operatorname{Var}(R)$ with indicators.
6. (B) Prove the Cantelli inequality: for $X \in L^2$ with mean $0$ and variance $\sigma^2$, and $c > 0$, $P(X \ge c) \le \sigma^2/(\sigma^2 + c^2)$. Apply Markov to $(X + t)^2$ and choose $t$.
7. (B) Find three variables $X, Y, Z$ that are pairwise uncorrelated but with $\operatorname{Var}(X + Y + Z) \neq \operatorname{Var}(X) + \operatorname{Var}(Y) + \operatorname{Var}(Z)$, or show that none exist.
8. (C) Let $X$ and $Y$ take only two values each. Show that $X$ and $Y$ are independent if and only if they are uncorrelated.

### Notes and history

Chebyshev published his inequality in 1867, and his student Markov gave the form with moments in his work on the law of large numbers. Bienaymé had stated an equivalent inequality in 1853, and the result is also called the Bienaymé-Chebyshev inequality. The additivity of the variance for independent variables is also due to Bienaymé (1853). The words variance and standard deviation come from statistics: Pearson introduced the standard deviation in 1894, and Fisher the variance in 1918.

### Reference

<?reference?>
