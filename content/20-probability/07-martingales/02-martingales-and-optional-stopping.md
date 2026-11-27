---
title: Martingales and optional stopping
kind: theory
modules:
  - Mathlib.Probability.Martingale.Basic
  - Mathlib.Probability.Martingale.Centering
  - Mathlib.Probability.Martingale.OptionalStopping
  - Mathlib.Probability.Martingale.OptionalSampling
explains:
  E3: [MeasureTheory.Martingale, MeasureTheory.Submartingale, MeasureTheory.Submartingale.stoppedProcess, MeasureTheory.Submartingale.expected_stoppedValue_mono, MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le, MeasureTheory.maximal_ineq, MeasureTheory.martingalePart, MeasureTheory.predictablePart]
  E2: [MeasureTheory.Supermartingale, MeasureTheory.martingale_condExp, MeasureTheory.Martingale.condExp_ae_eq, MeasureTheory.Martingale.setIntegral_eq, MeasureTheory.Martingale.integrable, MeasureTheory.Martingale.add, MeasureTheory.Martingale.neg, MeasureTheory.Martingale.smul, MeasureTheory.Martingale.submartingale, MeasureTheory.Martingale.supermartingale, MeasureTheory.martingale_iff, MeasureTheory.martingale_nat, MeasureTheory.submartingale_nat, MeasureTheory.supermartingale_nat, MeasureTheory.Submartingale.sum_mul_sub, MeasureTheory.submartingale_iff_expected_stoppedValue_mono, MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le_const, MeasureTheory.martingalePart_add_predictablePart, MeasureTheory.martingale_martingalePart, MeasureTheory.isPredictable_predictablePart, MeasureTheory.martingalePart_eq_sum, MeasureTheory.Submartingale.monotone_predictablePart, MeasureTheory.Martingale.predictablePart_eq_zero]
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

## Martingales and optional stopping

### Overview

A martingale is the model of a fair game: the expected future value, given the information of today, is the value of today. A submartingale is a game that is favourable, and a supermartingale is a game that is unfavourable. The main result of this section is the optional stopping theorem: a player cannot change a fair game into a favourable one with a bounded stopping rule. The section also gives the Doob decomposition of an adapted process into a martingale and a predictable part, and Doob's maximal inequality. The gambler's ruin is the main example.

### Definitions

Fix a filtered probability space $(\Omega, \mathcal{F}, (\mathcal{F}_i), P)$, as in Section 1.

**Definition (Martingale).** An adapted process $(X_i)$ of integrable variables is a *martingale* if $E[X_j \mid \mathcal{F}_i] = X_i$ a.s. for all $i \le j$. It is a *submartingale* if $E[X_j \mid \mathcal{F}_i] \ge X_i$ a.s., and a *supermartingale* if $E[X_j \mid \mathcal{F}_i] \le X_i$ a.s.

On the time set $\mathbb{N}$, the tower property reduces the condition to one step: $X$ is a martingale if and only if $E[X_{n+1} \mid \mathcal{F}_n] = X_n$ a.s. for each $n$. A martingale has a constant mean, $E[X_n] = E[X_0]$, and a submartingale has an increasing mean.

::: mathlib
`MeasureTheory.Martingale` · `Mathlib.Probability.Martingale.Basic`

`Martingale f ℱ μ` is the conjunction of `StronglyAdapted ℱ f` and `∀ i j, i ≤ j → μ[f j | ℱ i] =ᵐ[μ] f i`. The values are in a Banach space `E`. The integrability is not a field: it follows from the equality, because a conditional expectation is integrable (`Martingale.integrable`). `Martingale.condExp_ae_eq` and `Martingale.setIntegral_eq` extract the property. `martingale_condExp f ℱ μ` is the martingale $E[f \mid \mathcal{F}_i]$ of a fixed variable. `Martingale.add`, `Martingale.neg` and `Martingale.smul` are the algebraic rules. `martingale_nat` proves the property on `ℕ` from one step.

<?decl MeasureTheory.Martingale?>
:::

::: mathlib
`MeasureTheory.Submartingale` · `Mathlib.Probability.Martingale.Basic`

`Submartingale f ℱ μ` is adaptedness, the inequality `f i ≤ᵐ[μ] μ[f j | ℱ i]` for `i ≤ j`, and integrability of each `f i`. `Supermartingale` has the opposite inequality. `Martingale.submartingale` and `Martingale.supermartingale` are the inclusions, and `martingale_iff` says that a process is a martingale if and only if it is both. `submartingale_nat` and `supermartingale_nat` reduce the condition to one step on `ℕ`.

<?decl MeasureTheory.Submartingale?>
:::

**Definition (Discrete stochastic integral).** For a predictable process $H$ and an adapted process $X$ on $\mathbb{N}$, the *martingale transform* is $(H \cdot X)_n = \sum_{k=0}^{n-1} H_{k+1}(X_{k+1} - X_k)$. It is the gain of a player who stakes $H_{k+1}$ on step $k+1$.

**Definition (Doob decomposition).** For an adapted integrable process $X$ on $\mathbb{N}$, the *predictable part* is
$$A_n = \sum_{k=0}^{n-1} E[X_{k+1} - X_k \mid \mathcal{F}_k],$$
and the *martingale part* is $M_n = X_n - A_n$.

::: mathlib
`MeasureTheory.martingalePart` · `Mathlib.Probability.Martingale.Centering`

`martingalePart f ℱ μ n` and `predictablePart f ℱ μ n` are $M_n$ and $A_n$, and `martingalePart_add_predictablePart` is the identity $M + A = X$. `martingalePart_eq_sum` writes $M_n$ as a sum. `martingale_martingalePart` says that $M$ is a martingale, and `isPredictable_predictablePart` says that $A$ is predictable. `Submartingale.monotone_predictablePart` says that $A$ is a.s. increasing for a submartingale, and `Martingale.predictablePart_eq_zero` says that $A = 0$ for a martingale.

<?decl MeasureTheory.martingalePart?>
:::

::: mathlib
`MeasureTheory.predictablePart` · `Mathlib.Probability.Martingale.Centering`

`predictablePart f ℱ μ n` is the sum `∑ i ∈ Finset.range n, μ[f (i + 1) - f i | ℱ i]`. It is the compensator of $X$ in discrete time.

<?decl MeasureTheory.predictablePart?>
:::

### Theorems and proofs

**Theorem (Martingale transforms).** Let $X$ be a submartingale and let $H$ be predictable with $0 \le H_n \le R$. Then $H \cdot X$ is a submartingale. If $X$ is a martingale and $H$ is bounded and predictable, then $H \cdot X$ is a martingale.

*Proof.* $H \cdot X$ is adapted and integrable, because $H$ is bounded. By the pull out property, $E[(H \cdot X)_{n+1} - (H \cdot X)_n \mid \mathcal{F}_n] = H_{n+1}\, E[X_{n+1} - X_n \mid \mathcal{F}_n]$, which is $\ge 0$ for a submartingale and $0$ for a martingale. $\square$

In Mathlib the first claim is `Submartingale.sum_mul_sub`. Its statement uses an adapted $\xi$ and the sum $\sum_{k < n} \xi_k (X_{k+1} - X_k)$, which is the transform with $H_{k+1} = \xi_k$.

**Theorem (Stopped submartingales).** If $X$ is a submartingale on $\mathbb{N}$ and $\tau$ is a stopping time, then the stopped process $X^\tau$ is a submartingale. The same holds for martingales.

*Proof.* $X^\tau_n = X_0 + (H \cdot X)_n$ with $H_k = \mathbf{1}_{\{\tau \ge k\}}$. The event $\{\tau \ge k\} = \{\tau \le k-1\}^c$ is in $\mathcal{F}_{k-1}$, so $H$ is predictable, and $0 \le H \le 1$. Apply the theorem above. For a martingale, apply the result to $X$ and $-X$. $\square$

In Mathlib this is `Submartingale.stoppedProcess`, for real processes.

**Theorem (Optional stopping, bounded times).** Let $X$ be a submartingale on $\mathbb{N}$ and let $\sigma \le \tau \le N$ be stopping times. Then $E[X_\sigma] \le E[X_\tau]$. For a martingale, $E[X_\sigma] = E[X_\tau] = E[X_0]$.

*Proof.* Let $H_k = \mathbf{1}_{\{\sigma < k \le \tau\}} = \mathbf{1}_{\{\tau \ge k\}} - \mathbf{1}_{\{\sigma \ge k\}}$. It is predictable with values in $\{0, 1\}$, and $(H \cdot X)_N = X_\tau - X_\sigma$. By the theorem on transforms, $E[(H \cdot X)_N] \ge E[(H \cdot X)_0] = 0$. $\square$

In Mathlib this is `Submartingale.expected_stoppedValue_mono`. `submartingale_iff_expected_stoppedValue_mono` is the converse: an adapted integrable process with $E[X_\sigma] \le E[X_\tau]$ for all bounded stopping times $\sigma \le \tau$ is a submartingale.

**Theorem (Optional sampling).** Let $X$ be a martingale and let $\sigma \le \tau \le N$ be stopping times. Then $E[X_\tau \mid \mathcal{F}_\sigma] = X_\sigma$ a.s.

*Proof.* $X_\sigma$ is $\mathcal{F}_\sigma$-measurable by Section 1. Let $A \in \mathcal{F}_\sigma$. Then $A \in \mathcal{F}_\tau$ too, and $A \in \mathcal{F}_N$. Let $\rho_A = \rho$ on $A$ and $\rho_A = N$ on $A^c$, for $\rho = \sigma$ or $\rho = \tau$. This is a stopping time: for $i < N$, $\{\rho_A \le i\} = A \cap \{\rho \le i\} \in \mathcal{F}_i$, and for $i \ge N$, $\{\rho_A \le i\} = \Omega$. Optional stopping for the martingale gives $E[X_{\rho_A}] = E[X_N]$, which is $E[X_\rho \mathbf{1}_A] = E[X_N \mathbf{1}_A]$. So $E[X_\sigma \mathbf{1}_A] = E[X_\tau \mathbf{1}_A]$ for each $A \in \mathcal{F}_\sigma$. $\square$

In Mathlib this is `Martingale.stoppedValue_ae_eq_condExp_of_le`, and `Martingale.stoppedValue_ae_eq_condExp_of_le_const` is the case $\tau = N$. These results hold for a general time set with countable range of the times.

**Theorem (Doob's maximal inequality).** Let $X$ be a non-negative submartingale and let $\varepsilon > 0$. Then
$$\varepsilon\, P\Big(\max_{k \le n} X_k \ge \varepsilon\Big) \le E\Big[X_n ; \max_{k \le n} X_k \ge \varepsilon\Big] \le E[X_n].$$

*Proof.* Let $\tau = \min(\inf\{k : X_k \ge \varepsilon\}, n)$, a stopping time bounded by $n$, and let $A = \{\max_{k \le n} X_k \ge \varepsilon\}$. On $A$, $X_\tau \ge \varepsilon$, and on $A^c$, $\tau = n$. Optional stopping gives $E[X_\tau] \le E[X_n]$, which is $E[X_\tau ; A] + E[X_n ; A^c] \le E[X_n ; A] + E[X_n ; A^c]$. So $\varepsilon P(A) \le E[X_\tau ; A] \le E[X_n ; A]$. $\square$

In Mathlib this is `maximal_ineq`, with `ε : ℝ≥0` and the measure in `ℝ≥0∞`. For a martingale $M$ with $M_n \in L^2$, apply it to the submartingale $M_n^2$: this gives Kolmogorov's inequality $P(\max_{k \le n} |M_k| \ge \varepsilon) \le E[M_n^2] / \varepsilon^2$.

### Examples

**Example (The gambler's ruin).** A gambler starts with $a$ units, $0 < a < N$, and bets one unit on each toss of a fair coin. The fortune is $S_n = a + X_1 + \cdots + X_n$, with i.i.d. signs $X_k$. The gambler stops at $\tau = \inf\{n : S_n \in \{0, N\}\}$, a stopping time by Section 1.

First, $\tau < \infty$ a.s. In each block of $N$ consecutive tosses, the event that all tosses are $+1$ has probability $2^{-N}$, and on this event the walk leaves $(0, N)$ during the block. The blocks are independent, so $P(\tau > kN) \le (1 - 2^{-N})^k \to 0$. The same bound gives $E[\tau] < \infty$.

Second, $S$ is a martingale, so $S^\tau$ is a martingale with $0 \le S^\tau_n \le N$, and $E[S_{\min(n, \tau)}] = a$. As $n \to \infty$, $S_{\min(n, \tau)} \to S_\tau$ a.s., and the dominated convergence theorem gives $E[S_\tau] = a$. Since $S_\tau \in \{0, N\}$,
$$P(S_\tau = N) = \frac{a}{N}.$$

Third, $S_n^2 - n$ is a martingale, since $E[S_{n+1}^2 - S_n^2 \mid \mathcal{F}_n] = E[2 S_n X_{n+1} + 1 \mid \mathcal{F}_n] = 1$. Optional stopping at $\min(n, \tau)$ gives $E[S_{\min(n,\tau)}^2] = a^2 + E[\min(n, \tau)]$. Let $n \to \infty$: dominated convergence on the left and monotone convergence on the right give $E[S_\tau^2] = a^2 + E[\tau]$. Since $E[S_\tau^2] = N^2 \cdot a / N = aN$,
$$E[\tau] = a(N - a).$$
For $a = 10$ and $N = 20$, the game lasts $100$ tosses on average.

**Counterexample (Doubling the stake).** The doubling strategy of Section 1 has the gain $1$ at the first win, so $(H \cdot S)_\tau = 1$ a.s. for the a.s. finite time $\tau$ of the first win. But $H \cdot S$ is a martingale with mean $0$. The optional stopping theorem fails here because $\tau$ is not bounded, and the losses before the first win are not bounded below: the expected maximal loss is infinite. Each extension of the theorem to unbounded times needs a hypothesis of this kind, such as $E[\tau] < \infty$ with bounded increments, or uniform integrability of $X^\tau$.

**Example (Doob decomposition of the square).** For the walk $S$, $S_n^2$ is a submartingale. Its predictable part is $A_n = \sum_{k < n} E[S_{k+1}^2 - S_k^2 \mid \mathcal{F}_k] = n$, and its martingale part is $S_n^2 - n$, the martingale of the gambler's ruin. In general, for a martingale $M \in L^2$, the predictable part of $M^2$ is the *predictable quadratic variation* $\langle M \rangle_n = \sum_{k < n} E[(M_{k+1} - M_k)^2 \mid \mathcal{F}_k]$.

### The library around it

Martingales in Mathlib take values in a Banach space, and submartingales in an ordered Banach space; the optional stopping theorems are stated for real processes. The theorems above use bounded stopping times. The index of this edition has no declaration for the optional stopping theorem with $E[\tau] < \infty$ and bounded increments, which the gambler's ruin uses through dominated convergence.

`Mathlib/Probability/Martingale/OptionalSampling.lean` contains several forms of optional sampling for a general time set, for example `Martingale.stoppedValue_min_ae_eq_condExp`, which conditions the value at $\min(\sigma, \tau)$. `Mathlib/Probability/Martingale/Centering.lean` contains the Doob decomposition and its uniqueness for predictable parts with value $0$ at time $0$. The declaration `smul_le_stoppedValue_hittingBtwn` is the form of the maximal inequality with hitting times that the proof uses.

### Exercises

1. (A) Let $X_1, X_2, \ldots$ be independent integrable variables with mean $0$. Prove that $S_n = X_1 + \cdots + X_n$ is a martingale for the natural filtration.
2. (A) Let $X_1, X_2, \ldots$ be independent non-negative variables with mean $1$. Prove that the product $X_1 \cdots X_n$ is a martingale.
3. (A) Prove that a convex function of a martingale is a submartingale, when it is integrable. Deduce that $|M_n|$ and $M_n^2$ are submartingales.
4. (B) In the gambler's ruin with a biased coin, $P(X_k = 1) = p \ne 1/2$ and $q = 1 - p$, prove that $(q/p)^{S_n}$ is a martingale and compute $P(S_\tau = N)$.
5. (B) In the biased game of Exercise 4, prove that $S_n - n(p - q)$ is a martingale and compute $E[\tau]$.
6. (B) Prove that the Doob decomposition is unique: if $X = M + A = M' + A'$ with martingales $M, M'$ and predictable $A, A'$ with $A_0 = A'_0 = 0$, then $A = A'$ a.s.
7. (B) For a martingale $M$ with $M_n \in L^2$, prove that the increments are orthogonal: $E[(M_{k+1} - M_k)(M_{j+1} - M_j)] = 0$ for $j < k$. Deduce $E[M_n^2] = E[M_0^2] + \sum_{k < n} E[(M_{k+1} - M_k)^2]$.
8. (C) Let $S$ be the simple symmetric walk from $0$ and let $\tau = \inf\{n : S_n = 1\}$. Prove that $\tau < \infty$ a.s. with the gambler's ruin and $N \to \infty$, and that $E[\tau] = \infty$. Use the fact that $E[\tau] < \infty$ and bounded increments imply $E[S_\tau] = E[S_0]$.

### Notes and history

The word martingale first meant a betting system, of the doubling kind in the counterexample above. Ville used it for a sequence of this kind in his thesis of 1939. Lévy studied sums with the martingale property in the 1930s. Doob developed the general theory, with optional stopping, the decomposition and the maximal inequality, in his book *Stochastic Processes* of 1953. The maximal inequality for sums of independent variables is due to Kolmogorov.

### Reference

<?reference?>
