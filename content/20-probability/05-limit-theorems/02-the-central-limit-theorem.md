---
title: The central limit theorem
kind: theory
modules:
  - Mathlib.Probability.CentralLimitTheorem
  - Mathlib.Probability.Independence.CharacteristicFunction
  - Mathlib.Probability.CramerWold
explains:
  E3: [ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum, ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub, ProbabilityTheory.IndepFun.charFun_map_add_eq_mul, tendstoInDistribution_iff_tendstoInDistribution_inner]
  E2: [ProbabilityTheory.charFun_inv_sqrt_mul_sum, ProbabilityTheory.tendsto_charFun_inv_sqrt_mul_pow, ProbabilityTheory.iIndepFun.charFun_map_sum_eq_prod, ProbabilityTheory.indepFun_iff_charFun_prod, ProbabilityTheory.iIndepFun_iff_charFun_pi, ProbabilityTheory.charFun_map_add_prod_eq_mul, TendstoInDistribution.of_inner]
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

## The central limit theorem

### Overview

The law of large numbers says that $S_n/n \to m$. The central limit theorem gives the size and the shape of the error: for i.i.d. variables with mean $m$ and variance $\sigma^2$, the law of $(S_n - nm)/(\sigma\sqrt{n})$ converges to $N(0, 1)$. The convergence is convergence in distribution, a weak mode of convergence that only concerns the laws. This section defines it, states the Lévy continuity theorem that connects it to characteristic functions, proves the theorem, and gives its multivariate form through the Cramér-Wold device. All three results are in Mathlib.

### Definitions

**Definition (Convergence in distribution).** Let $Y_n$ be random variables, each on its own probability space, and let $Y$ be a random variable, all with values in a metric space $E$. Then $Y_n \to Y$ *in distribution* if $E[f(Y_n)] \to E[f(Y)]$ for each bounded continuous $f : E \to \mathbb{R}$. Equivalently, the laws $\mathcal{L}(Y_n)$ converge weakly to $\mathcal{L}(Y)$. For real variables this is the same as $F_{Y_n}(x) \to F_Y(x)$ at each point $x$ where $F_Y$ is continuous (exercise 6).

::: mathlib
`MeasureTheory.TendstoInDistribution` · `Mathlib.MeasureTheory.Function.ConvergenceInDistribution`

`TendstoInDistribution X l Y P P'` takes a family `X i : Ω i → E` on spaces `Ω i` with probability measures `P i`, a filter `l`, and a limit `Y : Ω' → E` on `(Ω', P')`. It says that the laws, as elements of `ProbabilityMeasure E`, converge in the topology of weak convergence. When all the `X n` are on the same space, the family of measures is the constant `fun _ ↦ P`.

<?decl MeasureTheory.TendstoInDistribution?>
:::

**Definition (Characteristic function of a variable).** The characteristic function of a variable $X$ with values in a real inner product space is the characteristic function of its law: $\varphi_X(t) = E[e^{i\langle X, t\rangle}]$. Section 4.3 defines it for measures.

### Theorems and proofs

**Theorem (Independence and characteristic functions).** Let $X$ and $Y$ be variables with values in inner product spaces. They are independent if and only if $\varphi_{(X, Y)}(s, t) = \varphi_X(s)\varphi_Y(t)$ for all $s, t$. If $X$ and $Y$ are independent with values in the same space, then $\varphi_{X+Y} = \varphi_X\varphi_Y$.

*Proof.* If $X$ and $Y$ are independent, the law of $(X, Y)$ is the product of the laws (Chapter 2), and Fubini gives $E[e^{i\langle X, s\rangle}e^{i\langle Y, t\rangle}] = \varphi_X(s)\varphi_Y(t)$. Conversely, the right side is the characteristic function of the product law. The characteristic function determines the measure, so the law of $(X, Y)$ is the product law. For the sum, put $s = t$ and use $\langle X + Y, t\rangle = \langle X, t\rangle + \langle Y, t\rangle$. $\square$

::: mathlib
`ProbabilityTheory.IndepFun.charFun_map_add_eq_mul` · `Mathlib.Probability.Independence.CharacteristicFunction`

For a.e. measurable `X` and `Y` with `IndepFun X Y P`, `charFun (P.map (X + Y)) = charFun (P.map X) * charFun (P.map Y)`. The criterion for independence is `indepFun_iff_charFun_prod`, on the space `WithLp 2 (E × F)` so that the pair has an inner product. The versions for finite families are `iIndepFun.charFun_map_sum_eq_prod` and `iIndepFun_iff_charFun_pi`, and `charFun_map_add_prod_eq_mul` is the measure form.

<?decl ProbabilityTheory.IndepFun.charFun_map_add_eq_mul?>
:::

**Theorem (Lévy continuity theorem).** Let $Y_n$ and $Y$ be variables with values in $\mathbb{R}^d$. Then $Y_n \to Y$ in distribution if and only if $\varphi_{Y_n}(t) \to \varphi_Y(t)$ for each $t$.

*Proof (sketch).* One direction is the definition, applied to the bounded continuous functions $\cos\langle\cdot, t\rangle$ and $\sin\langle\cdot, t\rangle$. For the converse, the convergence of $\varphi_{Y_n}$ near $0$ implies that the laws are tight, with the bound $P(|Y_n| > 2/u) \le u^{-1}\int_{-u}^u (1 - \varphi_{Y_n}(s))\, ds$ in dimension $1$. By Prokhorov's theorem each subsequence has a subsequence that converges in distribution, and the limit has the characteristic function $\varphi_Y$, so the limit is $\mathcal{L}(Y)$. A sequence whose subsequences all have subsequences with the same limit converges. Volume 18 has the details. $\square$

::: mathlib
`MeasureTheory.TendstoInDistribution.of_tendsto_charFun` · `Mathlib.MeasureTheory.Measure.LevyConvergence`

On a finite dimensional inner product space, pointwise convergence of the characteristic functions of the laws gives `TendstoInDistribution`. The other direction is `TendstoInDistribution.tendsto_charFun`.

<?decl MeasureTheory.TendstoInDistribution.of_tendsto_charFun?>
:::

**Theorem (Central limit theorem).** Let $X_1, X_2, \ldots$ be i.i.d. real variables with $E[X_1] = 0$ and $E[X_1^2] = 1$, and let $Z \sim N(0, 1)$. Then $S_n/\sqrt{n} \to Z$ in distribution.

*Proof.* By independence, $\varphi_{S_n/\sqrt{n}}(t) = \varphi(t/\sqrt{n})^n$, where $\varphi = \varphi_{X_1}$. The variable $X_1$ has two moments, so $\varphi$ is twice differentiable at $0$ with $\varphi(0) = 1$, $\varphi'(0) = iE[X_1] = 0$ and $\varphi''(0) = -E[X_1^2] = -1$. Taylor's theorem gives $\varphi(u) = 1 - u^2/2 + o(u^2)$ as $u \to 0$. So
$$\varphi(t/\sqrt{n})^n = \left(1 - \frac{t^2}{2n} + o\!\left(\frac1n\right)\right)^n \to e^{-t^2/2}.$$
The limit of $(1 + z_n/n)^n$ with complex $z_n \to z$ is $e^z$, by the same argument as for real numbers. The function $e^{-t^2/2}$ is the characteristic function of $N(0, 1)$, by Section 4.3. The Lévy continuity theorem ends the proof. $\square$

::: mathlib
`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum` · `Mathlib.Probability.CentralLimitTheorem`

The hypotheses are `HasLaw Y (gaussianReal 0 1) P'`, `∫ x, X 0 x ∂P = 0`, `∫ x, (X 0 ^ 2) x ∂P = 1`, `iIndepFun X P` and `∀ i, IdentDistrib (X i) (X 0) P P`. The conclusion is `TendstoInDistribution (fun n ω ↦ (√n)⁻¹ * ∑ k ∈ range n, X k ω) atTop Y (fun _ ↦ P) P'`. The two steps of the proof are `charFun_inv_sqrt_mul_sum`, which is the formula $\varphi(t/\sqrt n)^n$, and `tendsto_charFun_inv_sqrt_mul_pow`, which is the limit $e^{-t^2/2}$.

<?decl ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum?>
:::

The general case with mean $m$ and variance $\sigma^2 > 0$ follows from the standard case applied to $(X_k - m)/\sigma$.

::: mathlib
`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub` · `Mathlib.Probability.CentralLimitTheorem`

For `MemLp (X 0) 2 P`, with i.i.d. hypotheses, `(√n)⁻¹ * (∑ k ∈ range n, X k ω - n * ∫ x, X 0 x ∂P)` converges in distribution to `Y` with `HasLaw Y (gaussianReal 0 (variance (X 0) P).toNNReal) P'`. This form has no division by $\sigma$, so it also holds when the variance is $0$, with the limit $\delta_0$.

<?decl ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub?>
:::

**Theorem (Cramér-Wold device).** Let $Y_n$ and $Y$ be variables with values in a finite dimensional inner product space $E$. Then $Y_n \to Y$ in distribution if and only if $\langle Y_n, t\rangle \to \langle Y, t\rangle$ in distribution for each $t \in E$.

*Proof.* If $Y_n \to Y$ in distribution, then $\langle Y_n, t\rangle \to \langle Y, t\rangle$, because $x \mapsto \langle x, t\rangle$ is continuous. Conversely, $\varphi_{Y_n}(t) = \varphi_{\langle Y_n, t\rangle}(1) \to \varphi_{\langle Y, t\rangle}(1) = \varphi_Y(t)$, and the Lévy continuity theorem in $E$ ends the proof. $\square$

::: mathlib
`tendstoInDistribution_iff_tendstoInDistribution_inner` · `Mathlib.Probability.CramerWold`

The statement of the text for a sequence on one space `(Ω, P)` and a limit on `(Ω', P')`, with a.e. measurability of all the variables. The name has no namespace. The direction from the inner products to the vector is `TendstoInDistribution.of_inner`.

<?decl tendstoInDistribution_iff_tendstoInDistribution_inner?>
:::

The multivariate central limit theorem follows: if $X_1, X_2, \ldots$ are i.i.d. in $\mathbb{R}^d$ with mean $0$ and covariance matrix $S$, then $\langle S_n, t\rangle/\sqrt{n} \to N(0, t^\top S t)$ for each $t$, by the real theorem, and the Cramér-Wold device gives $S_n/\sqrt{n} \to N(0, S)$. The index of this edition has no declaration for the multivariate central limit theorem as a named theorem.

### Examples

**Example (De Moivre-Laplace).** Toss a fair coin $n = 10\,000$ times and let $S_n$ be the number of heads. Then $E[S_n] = 5000$ and $\sigma(S_n) = \sqrt{n/4} = 50$. By the central limit theorem,
$$P(S_n \ge 5100) = P\left(\frac{S_n - 5000}{50} \ge 2\right) \approx 1 - \Phi(2) \approx 0.0228.$$
With the continuity correction, $P(S_n \ge 5100) = P(S_n > 5099.5) \approx 1 - \Phi(1.99) \approx 0.0233$; the exact binomial value is near $0.023$. Chebyshev's inequality gives only $P(|S_n - 5000| \ge 100) \le 1/4$, and Hoeffding's inequality of Chapter 3 gives $P(S_n \ge 5100) \le e^{-2} \approx 0.135$.

**Example (Confidence interval).** Let $X_1, \ldots, X_n$ be i.i.d. with unknown mean $m$ and known variance $\sigma^2$. By the central limit theorem, $P(|\bar X_n - m| \le 1.96\,\sigma/\sqrt{n}) \to 0.95$. So $[\bar X_n - 1.96\,\sigma/\sqrt n, \bar X_n + 1.96\,\sigma/\sqrt n]$ contains $m$ with probability near $0.95$ for large $n$. For Gaussian $X_k$ the probability is exactly $0.95$ for each $n$, by Section 4.3.

**Counterexample (Infinite variance).** Let $X_1, X_2, \ldots$ be i.i.d. standard Cauchy. Then $S_n/\sqrt{n} = \sqrt{n}\,\bar X_n$ has the law of $\sqrt{n} X_1$, so $P(|S_n/\sqrt n| \le K) = P(|X_1| \le K/\sqrt n) \to 0$ for each $K$. No normalization by $\sqrt n$ gives a limit, and the correct normalization is $n$, with a Cauchy limit. The hypothesis $E[X_1^2] < \infty$ of the theorem cannot be removed.

### The library around it

`Mathlib.Probability.CentralLimitTheorem` has the real theorem in two forms and the two steps of its proof. The characteristic functions of measures, the Lévy continuity theorem and the weak convergence of probability measures are in the measure theory part, which Volume 18 describes. `Mathlib.Probability.Independence.CharacteristicFunction` has the criteria for independence and the product formulas, also for the dual characteristic function `charFunDual` on a normed space without an inner product. `Mathlib.Probability.CramerWold` has the Cramér-Wold device. The index of this edition has no declaration for the Lindeberg or Lyapunov forms of the theorem, or for the Berry-Esseen bound on the rate of convergence.

Common errors of a learner:

- `TendstoInDistribution` is about laws. It does not imply that the variables converge in probability, and the limit can be on another space.
- The second moment hypothesis is `∫ x, (X 0 ^ 2) x ∂P = 1`, with no separate hypothesis of square integrability. The equation gives it: a function that is not integrable has the integral `0`, and `0 ≠ 1`. With a hypothesis `= 0` this argument fails.
- The CLT needs mutual independence `iIndepFun X P`, while the strong law needs only pairwise independence.

### Exercises

1. (A) A fair die is thrown $600$ times. Estimate the probability that the sum of the results is larger than $2200$.
2. (A) Use the central limit theorem to find the limit of $e^{-n}\sum_{k=0}^n n^k/k!$ as $n \to \infty$, with a sum of $n$ independent Poisson variables with parameter $1$.
3. (A) Show that $(1 + z_n/n)^n \to e^z$ if $z_n \to z$ in $\mathbb{C}$.
4. (B) Let $X_1, X_2, \ldots$ be i.i.d. with mean $m \ne 0$ and variance $\sigma^2$. Use the delta method to find the limit law of $\sqrt{n}(\bar X_n^2 - m^2)$.
5. (B) Show that $S_n/\sqrt n$ in the central limit theorem does not converge in probability. Use the independence of $S_n$ and $S_{2n} - S_n$.
6. (B) Prove that for real variables, convergence in distribution is equivalent to $F_{Y_n}(x) \to F_Y(x)$ at the continuity points of $F_Y$.
7. (B) Let $X_n \sim \operatorname{Bin}(n, \lambda/n)$. Show with characteristic functions that $X_n \to \operatorname{Poi}(\lambda)$ in distribution, and compare with the Poisson limit theorem of Section 4.1.
8. (C) Prove the multivariate central limit theorem in Lean from `tendstoInDistribution_inv_sqrt_mul_sum_sub` and `tendstoInDistribution_iff_tendstoInDistribution_inner`, and state the hypotheses on the covariance.

### Notes and history

De Moivre proved the theorem for the binomial law with parameter $1/2$ in 1733, and Laplace extended it to other parameters and to more general sums in his *Théorie analytique des probabilités* of 1812. Lyapunov gave a rigorous proof under a moment condition in 1901, with characteristic functions, and Lindeberg gave his condition in 1922. Pólya introduced the name "central limit theorem" in 1920. Lévy published his continuity theorem in 1925. Cramér and Wold published their device in 1936.

### Reference

<?reference?>
