---
title: Martingale convergence
kind: theory
modules:
  - Mathlib.Probability.Martingale.Upcrossing
  - Mathlib.Probability.Martingale.Convergence
  - Mathlib.Probability.Martingale.BorelCantelli
  - Mathlib.Probability.Process.LimitProcess
explains:
  E3: [MeasureTheory.upcrossingsBefore, MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part, MeasureTheory.Submartingale.ae_tendsto_limitProcess, MeasureTheory.Submartingale.tendsto_eLpNorm_one_limitProcess, MeasureTheory.tendsto_ae_condExp, MeasureTheory.ae_mem_limsup_atTop_iff]
  E2: [MeasureTheory.upperCrossingTime, MeasureTheory.lowerCrossingTime, MeasureTheory.upcrossings, MeasureTheory.upcrossingStrat, MeasureTheory.Submartingale.sum_upcrossingStrat_mul, MeasureTheory.Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part, MeasureTheory.Submartingale.upcrossings_ae_lt_top, MeasureTheory.tendsto_of_upcrossings_lt_top, MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd, MeasureTheory.Submartingale.memLp_limitProcess, MeasureTheory.Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable, MeasureTheory.Martingale.ae_eq_condExp_limitProcess, MeasureTheory.tendsto_eLpNorm_condExp, MeasureTheory.Filtration.limitProcess, MeasureTheory.Filtration.HasLimitProcess, MeasureTheory.Filtration.limitProcess_ae_eq, MeasureTheory.Submartingale.bddAbove_iff_exists_tendsto, MeasureTheory.Martingale.ae_not_tendsto_atTop_atTop, MeasureTheory.tendsto_sum_indicator_atTop_iff]
  E1: auto
families: []
requires: [V03, V13, V15, V20.C01, V20.C02, V20.C03, V20.C04, V20.C05, V20.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Martingale convergence

### Overview

A martingale that is bounded in $L^1$ converges almost surely. This is Doob's convergence theorem, and its proof counts the upcrossings of an interval: a sequence that crosses an interval $[a, b]$ infinitely often does not converge, and a submartingale crosses each interval only finitely often in expectation. If the martingale is also uniformly integrable, the convergence holds in $L^1$, and the martingale is the sequence of conditional expectations of its limit. The section ends with two applications: Lévy's upward theorem and Lévy's extension of the Borel-Cantelli lemma.

### Definitions

All processes in this section are real and indexed by $\mathbb{N}$, on a probability space with a filtration $(\mathcal{F}_n)$. Let $\mathcal{F}_\infty = \sigma\big(\bigcup_n \mathcal{F}_n\big)$.

**Definition (Upcrossings).** Let $a < b$ and let $x_0, x_1, \ldots$ be a real sequence. Define times $\sigma_0 = 0$ and, for $k \ge 1$,
$$\sigma_k = \inf\{n \ge \tau_{k-1} : x_n \le a\}, \qquad \tau_k = \inf\{n \ge \sigma_k : x_n \ge b\},$$
with $\tau_0 = 0$. The *number of upcrossings* of $[a, b]$ before time $N$ is $U_N[a, b] = \max\{k : \tau_k < N\}$, and the total number is $U[a, b] = \sup_N U_N[a, b] \in \mathbb{N} \cup \{\infty\}$.

::: mathlib
`MeasureTheory.upcrossingsBefore` · `Mathlib.Probability.Martingale.Upcrossing`

`upcrossingsBefore a b f N ω : ℕ` is $U_N[a, b]$ for the path $n \mapsto f\,n\,\omega$. The times are `lowerCrossingTime a b f N n` and `upperCrossingTime a b f N n`, which are built with `hittingBtwn` of Section 1 and are cut at $N$. `upcrossings a b f ω` is the total number, in `ℝ≥0∞`. `upcrossingStrat a b f N n` is the indicator of the times between a lower and the next upper crossing: it is the strategy "buy below $a$, sell above $b$", shifted by one index so that it is adapted. `Submartingale.sum_upcrossingStrat_mul` says that the gain of this strategy on a submartingale is a submartingale.

<?decl MeasureTheory.upcrossingsBefore?>
:::

**Definition (Uniform integrability).** A family $(X_i)$ of integrable variables is *uniformly integrable* if $\sup_i E[|X_i| ; |X_i| > K] \to 0$ as $K \to \infty$. Volume 18, Measure and integration, studies this notion and proves Vitali's convergence theorem: a.s. convergence and uniform integrability give $L^1$ convergence.

**Definition (Limit process).** For a process $X$, the *limit process* is a fixed $\mathcal{F}_\infty$-measurable variable $X_\infty$ with $X_n \to X_\infty$ a.s., if there is one.

::: mathlib
`MeasureTheory.Filtration.limitProcess` · `Mathlib.Probability.Process.LimitProcess`

`HasLimitProcess X 𝓕 P` says that `X` converges a.s. to a `⨆ n, 𝓕 n`-strongly measurable variable. `limitProcess X 𝓕 P` is then such a limit, chosen with the axiom of choice, and is `0` if there is none. `limitProcess_ae_eq` says that it is a.s. equal to each limit of this kind. The convergence theorems below are stated with `limitProcess`.

<?decl MeasureTheory.Filtration.limitProcess?>
:::

### Theorems and proofs

**Theorem (Doob's upcrossing inequality).** Let $X$ be a submartingale and let $a < b$. Then
$$(b - a)\, E\big[U_N[a, b]\big] \le E\big[(X_N - a)^+\big].$$

*Proof.* Let $Y_n = (X_n - a)^+ + a = \max(X_n, a)$, a submartingale by Jensen's inequality for the convex increasing function $x \mapsto \max(x, a)$. $Y$ and $X$ have the same upcrossings of $[a, b]$. Let $H$ be the predictable strategy that is $1$ between each lower crossing and the next upper crossing, and $0$ elsewhere. Each completed upcrossing gives a gain of at least $b - a$ to $H \cdot Y$, and an unfinished one gives a gain $\ge 0$, because $Y \ge a$. So $(H \cdot Y)_N \ge (b - a) U_N[a, b]$. The strategy $1 - H$ is predictable with values in $[0, 1]$, so $E[((1 - H) \cdot Y)_N] \ge 0$ by Section 2. Then
$$(b - a) E[U_N] \le E[(H \cdot Y)_N] \le E[(H \cdot Y)_N] + E[((1 - H) \cdot Y)_N] = E[Y_N - Y_0] \le E[(X_N - a)^+]. \quad \square$$

::: mathlib
`MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part` · `Mathlib.Probability.Martingale.Upcrossing`

This is the inequality, for a finite measure. `Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part` is the form for the total number of upcrossings, with the supremum over $N$ on the right and lower Lebesgue integrals.

<?decl MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part?>
:::

**Theorem (Doob's convergence theorem).** Let $X$ be a submartingale with $\sup_n E|X_n| < \infty$. Then $X_n$ converges a.s. to an integrable $\mathcal{F}_\infty$-measurable limit $X_\infty$.

*Proof.* By the upcrossing inequality and monotone convergence, $(b - a) E[U[a, b]] \le \sup_N E[(X_N - a)^+] \le \sup_N E|X_N| + |a| < \infty$, so $U[a, b] < \infty$ a.s. The union over the countably many rational pairs $a < b$ is still a null set, so a.s. all rational intervals have finitely many upcrossings. On this event, $\liminf X_n = \limsup X_n$: if $\liminf X_n < a < b < \limsup X_n$ for rationals $a, b$, the path crosses $[a, b]$ infinitely often. By Fatou's lemma, $E[\liminf |X_n|] \le \sup_n E|X_n| < \infty$, so the limit is finite a.s. and integrable. Each $X_n$ is $\mathcal{F}_\infty$-measurable, so the limit is too. $\square$

::: mathlib
`MeasureTheory.Submartingale.ae_tendsto_limitProcess` · `Mathlib.Probability.Martingale.Convergence`

The hypothesis is `⨆ n, eLpNorm (f n) 1 μ < ⊤`, and the conclusion is the a.s. convergence to `limitProcess f ℱ μ`. The proof follows the steps above: `Submartingale.upcrossings_ae_lt_top` for the rational intervals, and `tendsto_of_upcrossings_lt_top` for the deterministic step. `Submartingale.exists_ae_tendsto_of_bdd` is the form without the limit process, and `Submartingale.memLp_limitProcess` says that the limit is in $L^p$ if the process is bounded in $L^p$.

<?decl MeasureTheory.Submartingale.ae_tendsto_limitProcess?>
:::

A non-negative supermartingale $X$ has $E|X_n| = E[X_n] \le E[X_0]$, so $-X$ is an $L^1$ bounded submartingale and $X$ converges a.s.

**Theorem ($L^1$ convergence).** Let $X$ be a uniformly integrable submartingale. Then $X_n \to X_\infty$ a.s. and in $L^1$. If $X$ is a martingale, then $X_n = E[X_\infty \mid \mathcal{F}_n]$ a.s. for each $n$.

*Proof.* Uniform integrability implies $\sup_n E|X_n| < \infty$, so the a.s. convergence follows from Doob's theorem, and Vitali's theorem gives the $L^1$ convergence. For a martingale and $A \in \mathcal{F}_n$, $E[X_n \mathbf{1}_A] = E[X_m \mathbf{1}_A]$ for each $m \ge n$, and the right side tends to $E[X_\infty \mathbf{1}_A]$ by the $L^1$ convergence. $\square$

::: mathlib
`MeasureTheory.Submartingale.tendsto_eLpNorm_one_limitProcess` · `Mathlib.Probability.Martingale.Convergence`

This is the $L^1$ convergence for a uniformly integrable submartingale. The hypothesis is `UniformIntegrable f 1 μ`, from the measure theory part of the library. `Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable` is the a.s. part, and `Martingale.ae_eq_condExp_limitProcess` is the representation $X_n = E[X_\infty \mid \mathcal{F}_n]$.

<?decl MeasureTheory.Submartingale.tendsto_eLpNorm_one_limitProcess?>
:::

**Theorem (Lévy's upward theorem).** For an integrable $Z$, $E[Z \mid \mathcal{F}_n] \to E[Z \mid \mathcal{F}_\infty]$ a.s. and in $L^1$.

*Proof.* $M_n = E[Z \mid \mathcal{F}_n]$ is a martingale, and it is uniformly integrable, because a family of conditional expectations of one integrable variable is uniformly integrable (Volume 18). So $M_n \to M_\infty$ a.s. and in $L^1$, and $M_n = E[M_\infty \mid \mathcal{F}_n]$. For $A \in \mathcal{F}_n$, $E[M_\infty \mathbf{1}_A] = E[Z \mathbf{1}_A]$. The sets $A$ in $\bigcup_n \mathcal{F}_n$ form a $\pi$-system that generates $\mathcal{F}_\infty$, so the equality holds for all $A \in \mathcal{F}_\infty$ by the $\pi$-$\lambda$ theorem, and $M_\infty = E[Z \mid \mathcal{F}_\infty]$. $\square$

::: mathlib
`MeasureTheory.tendsto_ae_condExp` · `Mathlib.Probability.Martingale.Convergence`

`tendsto_ae_condExp g` is the a.s. form, with the limit `μ[g | ⨆ n, ℱ n]`, and `tendsto_eLpNorm_condExp` is the $L^1$ form. In the Lean statements, `g` is a real function with no integrability hypothesis: for a non-integrable `g`, both sides are `0`.

<?decl MeasureTheory.tendsto_ae_condExp?>
:::

**Theorem (Lévy's extension of Borel-Cantelli).** Let $A_n \in \mathcal{F}_n$ be events. Then, a.s., $A_n$ occurs infinitely often if and only if $\sum_n P(A_{n+1} \mid \mathcal{F}_n) = \infty$.

*Proof sketch.* Let $X_n = \sum_{k < n} \mathbf{1}_{A_{k+1}}$. Its predictable part is $C_n = \sum_{k < n} P(A_{k+1} \mid \mathcal{F}_k)$, and the martingale part $M = X - C$ has increments bounded by $1$. A martingale with bounded increments either converges or oscillates between $-\infty$ and $+\infty$, a.s.: this is `Submartingale.bddAbove_iff_exists_tendsto` with `Martingale.ae_not_tendsto_atTop_atTop`. In both cases, $X_n \to \infty$ if and only if $C_n \to \infty$. $\square$

::: mathlib
`MeasureTheory.ae_mem_limsup_atTop_iff` · `Mathlib.Probability.Martingale.BorelCantelli`

`ae_mem_limsup_atTop_iff μ hs` states that a.e. `ω ∈ limsup s atTop` if and only if the sum of the conditional probabilities `μ[(s (k + 1)).indicator 1 | ℱ k]` tends to infinity. The general statement for an adapted process with bounded increments is `tendsto_sum_indicator_atTop_iff`. For independent events the conditional probabilities are constants, and the result gives the second Borel-Cantelli lemma of Chapter 2.

<?decl MeasureTheory.ae_mem_limsup_atTop_iff?>
:::

### Examples

**Example (Pólya's urn).** An urn contains one red and one black ball. At each step, draw a ball uniformly, and return it with one more ball of the same colour. Let $R_n$ be the number of red balls after $n$ steps, so the urn has $n + 2$ balls, and let $Y_n = R_n / (n + 2)$. Then
$$E[Y_{n+1} \mid \mathcal{F}_n] = \frac{1}{n+3}\Big(R_n + \frac{R_n}{n+2}\Big) = \frac{R_n}{n+2} = Y_n,$$
so $Y$ is a martingale with values in $[0, 1]$. It is uniformly integrable, so it converges a.s. and in $L^1$ to a limit $Y_\infty$. An induction shows that $R_n$ is uniform on $\{1, \ldots, n+1\}$, so $Y_\infty$ is uniform on $[0, 1]$. The limit proportion is random: the first draws have a lasting effect.

**Counterexample (Double or nothing).** Let $\xi_1, \xi_2, \ldots$ be i.i.d. with $P(\xi_k = 2) = P(\xi_k = 0) = 1/2$, and let $X_n = \xi_1 \cdots \xi_n$. Then $X$ is a non-negative martingale with $E[X_n] = 1$, so it converges a.s., and the limit is $0$, because $P(X_n \ne 0) = 2^{-n}$. But $E[X_n] = 1$ does not tend to $E[0] = 0$. The convergence does not hold in $L^1$, and $X$ is not uniformly integrable: $E[X_n ; X_n > K] = 1$ for $2^n > K$. The representation $X_n = E[X_\infty \mid \mathcal{F}_n]$ fails too.

**Example (Kolmogorov's zero-one law again).** Let $X_1, X_2, \ldots$ be independent, let $\mathcal{F}_n = \sigma(X_1, \ldots, X_n)$, and let $A$ be a tail event. Then $A$ is independent of each $\mathcal{F}_n$, so $P(A \mid \mathcal{F}_n) = P(A)$. By Lévy's upward theorem, $P(A \mid \mathcal{F}_n) \to \mathbf{1}_A$ a.s., because $A \in \mathcal{F}_\infty$. So $\mathbf{1}_A = P(A)$ a.s., and $P(A) \in \{0, 1\}$.

### The library around it

The convergence theorems are in `Mathlib/Probability/Martingale/Convergence.lean`, for real processes on $\mathbb{N}$ and a finite measure. The upcrossing machinery is in `Upcrossing.lean`, and the results on bounded increments and the conditional Borel-Cantelli lemma are in `BorelCantelli.lean`. The index of this edition has no declaration for Doob's $L^p$ maximal inequality $\| \max_{k \le n} |M_k| \|_p \le \frac{p}{p-1} \|M_n\|_p$, nor for Lévy's downward theorem for a decreasing filtration, nor for backward martingales.

`Mathlib/Probability/Process/LimitProcess.lean` has algebraic rules for limit processes, such as `HasLimitProcess.add` and `limitProcess_fun_add`, which let a proof compute the limit of a sum of convergent processes.

### Exercises

1. (A) Prove that a martingale bounded in $L^2$ converges a.s. and in $L^2$. Use the orthogonality of increments from Section 2.
2. (A) Let $S_n$ be the simple symmetric random walk. Prove that $S_n$ does not converge, and deduce that $\sup_n E|S_n| = \infty$.
3. (A) Prove that a non-negative supermartingale converges a.s. Show with double or nothing that the limit can have a smaller mean.
4. (B) In Pólya's urn, prove by induction that $P(R_n = k) = 1/(n+1)$ for $k = 1, \ldots, n+1$.
5. (B) Start Pólya's urn with $r$ red and $s$ black balls. Prove that $Y_\infty$ has the Beta law with parameters $r$ and $s$. Use the moments $E[Y_\infty^k]$.
6. (B) Let $X_1, X_2, \ldots$ be independent with mean $0$ and $\sum_k \operatorname{Var}(X_k) < \infty$. Prove that $\sum_k X_k$ converges a.s.
7. (B) Let $Z \in L^1$ be $\mathcal{F}_\infty$-measurable. Prove that $E[Z \mid \mathcal{F}_n] \to Z$ a.s. Apply it to the binary digits of a uniform variable on $[0, 1]$.
8. (C) Let $\mu$ and $\nu$ be probability measures on $(\Omega, \mathcal{F}_\infty)$ with $\nu \ll \mu$ on each $\mathcal{F}_n$, and let $L_n$ be the density on $\mathcal{F}_n$. Prove that $L_n$ is a $\mu$-martingale that converges a.s. Prove that $\nu \ll \mu$ on $\mathcal{F}_\infty$ if and only if $(L_n)$ is uniformly integrable.

### Notes and history

Doob proved the convergence theorem for martingales and the upcrossing inequality, and gave them in his book *Stochastic Processes* of 1953. Lévy proved the upward theorem for conditional probabilities in the 1930s. Pólya studied the urn scheme in a paper with Eggenberger of 1923, as a model of contagion.

### Reference

<?reference?>
