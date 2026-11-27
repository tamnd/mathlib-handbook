---
title: The laws of large numbers
kind: theory
modules:
  - Mathlib.Probability.StrongLaw
explains:
  E3: [ProbabilityTheory.strong_law_ae, ProbabilityTheory.strong_law_ae_real, ProbabilityTheory.strong_law_Lp]
  E2: [ProbabilityTheory.truncation, ProbabilityTheory.abs_truncation_le_bound, ProbabilityTheory.truncation_eq_self, ProbabilityTheory.tendsto_integral_truncation, ProbabilityTheory.IdentDistrib.truncation, ProbabilityTheory.tsum_prob_mem_Ioi_lt_top, ProbabilityTheory.sum_variance_truncation_le, ProbabilityTheory.strong_law_ae_of_measurable]
  E1: auto
families: []
requires: [V03, V13, V15, V20.C01, V20.C02, V20.C03, V20.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The laws of large numbers

### Overview

Toss a fair coin many times. The proportion of heads comes near $1/2$. The laws of large numbers make this statement exact: the average $\bar X_n = (X_1 + \cdots + X_n)/n$ of i.i.d. integrable variables converges to the common mean $E[X_1]$. The weak law says that the convergence is in probability, and the strong law says that it is almost sure. This section defines the modes of convergence, proves the weak law with Chebyshev's inequality, and proves the strong law in the form of Etemadi, which needs only pairwise independence. Mathlib has the strong law, and its almost sure form implies the weak law.

### Definitions

**Definition (Modes of convergence).** Let $Y, Y_1, Y_2, \ldots$ be random variables with values in a normed space on $(\Omega, \mathcal{F}, P)$.

- $Y_n \to Y$ *almost surely* if $P(\{\omega : Y_n(\omega) \to Y(\omega)\}) = 1$.
- $Y_n \to Y$ *in probability* if $P(\|Y_n - Y\| > \varepsilon) \to 0$ for each $\varepsilon > 0$.
- $Y_n \to Y$ *in $L^p$*, for $1 \le p < \infty$, if $E\|Y_n - Y\|^p \to 0$.

Almost sure convergence and $L^p$ convergence each imply convergence in probability, and a sequence that converges in probability has a subsequence that converges almost surely. Volume 18 proves these facts for convergence in measure. The converse implications are false (exercise 2).

::: mathlib
`MeasureTheory.TendstoInMeasure` · `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`

`TendstoInMeasure μ f l g` is convergence in probability along a filter `l`. The implications of the text are `tendstoInMeasure_of_tendsto_ae`, `tendstoInMeasure_of_tendsto_eLpNorm` and `TendstoInMeasure.exists_seq_tendsto_ae`. Almost sure convergence has no separate name: it is `∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (𝓝 (g ω))`.

<?decl MeasureTheory.TendstoInMeasure?>
:::

**Definition (Truncation).** For a real variable $X$ and $A > 0$, the *truncation* of $X$ at $A$ is $X \mathbf{1}_{\{|X| < A\}}$ in the symmetric form, or $X \mathbf{1}_{\{X \le A\}}$ for a nonnegative $X$. A truncated variable is bounded, so it has all moments, and its expectation tends to $E[X]$ as $A \to \infty$ by dominated convergence.

::: mathlib
`ProbabilityTheory.truncation` · `Mathlib.Probability.StrongLaw`

`truncation f A` is `(Set.Ioc (-A) A).indicator id ∘ f`. The bounds are `abs_truncation_le_bound` and `abs_truncation_le_abs_self`, `truncation_eq_self` says that the truncation does not change $f$ where $|f| < A$, and `tendsto_integral_truncation` is the convergence of the expectations. `IdentDistrib.truncation` says that the truncations of two identically distributed variables are identically distributed.

<?decl ProbabilityTheory.truncation?>
:::

### Theorems and proofs

**Theorem (Weak law, with finite variance).** Let $X_1, X_2, \ldots$ be pairwise uncorrelated real variables with the same mean $m$ and variances bounded by $\sigma^2$. Then $\bar X_n \to m$ in probability, and also in $L^2$.

*Proof.* The variance of a sum of uncorrelated variables is the sum of the variances (Chapter 3). So $\operatorname{Var}(\bar X_n) = n^{-2}\sum_{k \le n}\operatorname{Var}(X_k) \le \sigma^2/n$, and $E|\bar X_n - m|^2 = \operatorname{Var}(\bar X_n) \to 0$. Chebyshev's inequality gives $P(|\bar X_n - m| \ge \varepsilon) \le \sigma^2/(n\varepsilon^2) \to 0$. $\square$

The index of this edition has no declaration for the weak law of large numbers as a named theorem. It follows from `strong_law_ae` and `tendstoInMeasure_of_tendsto_ae`, and for the version with finite variance from `IndepFun.variance_sum` and `meas_ge_le_variance_div_sq` of Chapter 3.

**Theorem (Strong law, Etemadi).** Let $X_1, X_2, \ldots$ be pairwise independent, identically distributed and integrable variables with values in a real Banach space, with mean $m = E[X_1]$. Then $\bar X_n \to m$ almost surely.

*Proof (real case).* Write $X = X^+ - X^-$. The positive parts $X_k^+$ are again pairwise independent and identically distributed, so it is sufficient to treat $X_k \ge 0$.

*Step 1: truncation.* Put $Y_k = X_k \mathbf{1}_{\{X_k \le k\}}$ and $T_n = Y_1 + \cdots + Y_n$. Then $\sum_k P(X_k \ne Y_k) = \sum_k P(X_1 > k) \le E[X_1] < \infty$. By the first Borel-Cantelli lemma of Chapter 2, almost surely $X_k = Y_k$ for all large $k$. So it is sufficient to prove $T_n/n \to m$. Also $E[Y_k] \to m$ by monotone convergence, so $E[T_n]/n \to m$ by Cesàro.

*Step 2: a subsequence.* Fix $\alpha > 1$ and put $k_n = \lfloor \alpha^n \rfloor$. The $Y_k$ are pairwise independent, so by Chebyshev,
$$\sum_n P\left(|T_{k_n} - E T_{k_n}| > \varepsilon k_n\right) \le \frac{1}{\varepsilon^2}\sum_n \frac{1}{k_n^2}\sum_{j \le k_n}\operatorname{Var}(Y_j) \le \frac{C}{\varepsilon^2}\sum_j \frac{E[Y_j^2]}{j^2}.$$
The interchange of the sums uses $\sum_{n : k_n \ge j} k_n^{-2} \le C' j^{-2}$. A direct calculation with the law of $X_1$ gives $\sum_j E[Y_j^2]/j^2 \le 2E[X_1] + 1 < \infty$. By Borel-Cantelli, $T_{k_n}/k_n \to m$ almost surely.

*Step 3: the gaps.* The $Y_k$ are nonnegative, so $T_n$ increases with $n$. For $k_n \le j \le k_{n+1}$, $T_{k_n}/k_{n+1} \le T_j/j \le T_{k_{n+1}}/k_n$, and $k_{n+1}/k_n \to \alpha$. So $m/\alpha \le \liminf T_j/j \le \limsup T_j/j \le \alpha m$ almost surely. Take $\alpha = 1 + 1/r$ for $r = 1, 2, \ldots$ and intersect the countably many events of probability $1$. $\square$

The Banach space case follows by approximation of $X_1$ with simple functions of $X_1$: the real case applies to each coordinate of a simple function, and the error is small in $L^1$, so its average is small almost surely by the real case applied to $\|X_k - s(X_k)\|$.

::: mathlib
`ProbabilityTheory.strong_law_ae` · `Mathlib.Probability.StrongLaw`

The hypotheses are `Integrable (X 0) μ`, pairwise independence in the form `Pairwise ((IndepFun · · μ) on X)`, and `∀ i, IdentDistrib (X i) (X 0) μ μ`. The conclusion is that a.e. `(n : ℝ)⁻¹ • ∑ i ∈ range n, X i ω` tends to `∫ x, X 0 x ∂μ`. The variables are indexed from `0`, so the average of the first `n` is over `range n`. The proof in the file follows the three steps above; the inequalities of step 2 are `sum_variance_truncation_le` and `tsum_prob_mem_Ioi_lt_top`, and the Banach space case goes through `strong_law_ae_of_measurable`.

<?decl ProbabilityTheory.strong_law_ae?>
:::

::: mathlib
`ProbabilityTheory.strong_law_ae_real` · `Mathlib.Probability.StrongLaw`

The real case, with the conclusion in the form `(∑ i ∈ range n, X i ω) / n`. It has the same three hypotheses.

<?decl ProbabilityTheory.strong_law_ae_real?>
:::

**Theorem (Strong law in $L^p$).** Under the hypotheses of the strong law, if also $E\|X_1\|^p < \infty$ for some $1 \le p < \infty$, then $\bar X_n \to m$ in $L^p$.

*Proof.* The averages converge almost surely. The family $\{\|\bar X_n\|^p\}$ is uniformly integrable: by convexity, $\|\bar X_n\|^p \le n^{-1}\sum_k \|X_k\|^p$, and the right side is an average of identically distributed variables, which is a uniformly integrable family. By Vitali's convergence theorem of Volume 18, almost sure convergence and uniform integrability give $L^p$ convergence. $\square$

::: mathlib
`ProbabilityTheory.strong_law_Lp` · `Mathlib.Probability.StrongLaw`

For `1 ≤ p`, `p ≠ ∞` and `MemLp (X 0) p μ`, with pairwise independence and identical laws, `eLpNorm (fun ω ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, X i ω - ∫ x, X 0 x ∂μ) p μ` tends to `0`.

<?decl ProbabilityTheory.strong_law_Lp?>
:::

### Examples

**Example (Borel's normal numbers).** Take $\Omega = [0, 1)$ with the Lebesgue measure and let $X_k(\omega)$ be the $k$-th binary digit of $\omega$. The digits are i.i.d. Bernoulli with parameter $1/2$, as Chapter 2 shows. By the strong law, for almost every $\omega$ the proportion of digits $1$ among the first $n$ digits tends to $1/2$. The same argument in base $b$, applied to the indicator that a block of $\ell$ digits is a given word $w$, and a countable intersection over all $b$ and $w$, give Borel's theorem: almost every real number is normal in each base. The proof gives no explicit normal number.

**Example (Monte Carlo integration).** Let $f : [0, 1]^d \to \mathbb{R}$ be integrable and let $U_1, U_2, \ldots$ be i.i.d. uniform on $[0, 1]^d$. By the strong law, $n^{-1}\sum_{k \le n} f(U_k) \to \int f$ almost surely. If $f$ is square integrable with variance $\sigma^2$, then the $L^2$ error is $\sigma/\sqrt{n}$, which does not depend on $d$. For $f(x) = \mathbf{1}_{\{x_1^2 + x_2^2 \le 1\}}$ on $[0, 1]^2$ the limit is $\pi/4$, and $\sigma^2 = (\pi/4)(1 - \pi/4) \approx 0.169$, so $10^6$ points give $\pi$ with an error near $4 \cdot 0.41/1000 \approx 0.0016$.

**Counterexample (Without a mean, no law).** Let $X_1, X_2, \ldots$ be i.i.d. standard Cauchy. Section 4.3 shows that $\bar X_n$ is standard Cauchy for each $n$. So $P(|\bar X_n| > 1) = 1/2$ for all $n$, and $\bar X_n$ does not converge in probability to a constant. The integrability hypothesis of `strong_law_ae` cannot be removed.

### The library around it

`Mathlib.Probability.StrongLaw` has the strong law in three forms: `strong_law_ae_real`, `strong_law_ae` for Banach space values and `strong_law_Lp`. The truncation lemmas are public. The independence hypothesis is pairwise, through `Pairwise ((IndepFun · · μ) on X)`, and the mutual independence `iIndepFun X μ` of Chapter 2 gives it with `iIndepFun.indepFun`. To build an i.i.d. sequence with a given law, use `exists_iid` or the product measure `Measure.infinitePi` of Chapter 2. The ergodic theorem, which is a law of large numbers for stationary sequences, is in the dynamics part of the library and is outside this volume.

Common errors of a learner:

- The mean in the conclusion is `∫ x, X 0 x ∂μ`, the mean of the first variable, and not a separate parameter.
- The average is a real scalar times a sum, `(n : ℝ)⁻¹ • ∑ ...`. For `n = 0` this is `0`, which does not change the limit.
- `strong_law_ae` has no hypothesis `IsProbabilityMeasure μ`, while `strong_law_ae_of_measurable` has it. A user of `strong_law_ae` does not supply the instance.

### Exercises

1. (A) Let $S_n$ be the number of heads in $n$ tosses of a fair coin. Find $n$ such that Chebyshev's inequality gives $P(|S_n/n - 1/2| \ge 0.01) \le 0.05$.
2. (A) On $[0, 1]$ with the Lebesgue measure, give a sequence that converges in probability to $0$ but not almost surely, and a sequence that converges almost surely to $0$ but not in $L^1$.
3. (A) Let $X_1, X_2, \ldots$ be i.i.d. with $E|X_1| < \infty$. Show that $\max_{k \le n}|X_k|/n \to 0$ almost surely.
4. (B) Let $X_1, X_2, \ldots$ be i.i.d. with $E[X_1^+] = \infty$ and $E[X_1^-] < \infty$. Show that $\bar X_n \to \infty$ almost surely, with the strong law applied to truncations.
5. (B) Prove the strong law with a fourth moment: if the $X_k$ are i.i.d. with $E[X_1] = 0$ and $E[X_1^4] < \infty$, then $E[S_n^4] \le 3n^2 E[X_1^4]$, so $\sum_n P(|S_n| > \varepsilon n) < \infty$.
6. (B) Let $X_1, X_2, \ldots$ be i.i.d. with $E[X_1^2] < \infty$. Show that the empirical variance $n^{-1}\sum_{k \le n}(X_k - \bar X_n)^2$ converges almost surely to $\operatorname{Var}(X_1)$.
7. (B) Let $F_n(x) = n^{-1}\#\{k \le n : X_k \le x\}$ be the empirical distribution function of an i.i.d. sequence with distribution function $F$. Show that $F_n(x) \to F(x)$ almost surely for each $x$, and state the result in Lean with `strong_law_ae_real` and the indicator of `Set.Iic x`.
8. (C) Prove the Glivenko-Cantelli theorem: $\sup_x |F_n(x) - F(x)| \to 0$ almost surely.

### Notes and history

Jacob Bernoulli proved the weak law for Bernoulli variables in the *Ars Conjectandi*, published in 1713 after his death. Chebyshev gave the proof with the variance in 1867. Borel proved the strong law for binary digits in 1909, with the theorem on normal numbers. Kolmogorov proved the strong law for i.i.d. integrable variables in 1933, and Etemadi gave the proof with pairwise independence in 1981.

### Reference

<?reference?>
