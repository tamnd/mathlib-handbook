---
title: Filtrations and stopping times
kind: theory
modules:
  - Mathlib.Probability.Process.Filtration
  - Mathlib.Probability.Process.Adapted
  - Mathlib.Probability.Process.Predictable
  - Mathlib.Probability.Process.Stopping
  - Mathlib.Probability.Process.HittingTime
explains:
  E3: [MeasureTheory.Filtration, MeasureTheory.StronglyAdapted, MeasureTheory.IsStoppingTime, MeasureTheory.IsStoppingTime.measurableSpace, MeasureTheory.stoppedValue, MeasureTheory.hittingAfter]
  E2: [MeasureTheory.Filtration.mono, MeasureTheory.Filtration.le, MeasureTheory.Filtration.const, MeasureTheory.Filtration.natural, MeasureTheory.Filtration.stronglyAdapted_natural, MeasureTheory.Adapted, MeasureTheory.stronglyAdapted_iff_adapted, MeasureTheory.IsStronglyProgressive, MeasureTheory.StronglyAdapted.isStronglyProgressive_of_discrete, MeasureTheory.IsStronglyPredictable, MeasureTheory.IsStronglyPredictable.stronglyAdapted, MeasureTheory.IsStronglyPredictable.measurable_add_one, MeasureTheory.isStoppingTime_const, MeasureTheory.isStoppingTime_of_measurableSet_eq, MeasureTheory.IsStoppingTime.measurableSet_le, MeasureTheory.IsStoppingTime.measurableSet_eq, MeasureTheory.IsStoppingTime.min, MeasureTheory.IsStoppingTime.max, MeasureTheory.IsStoppingTime.add_const, MeasureTheory.IsStoppingTime.measurableSpace_mono, MeasureTheory.stoppedProcess, MeasureTheory.stoppedProcess_eq_stoppedValue, MeasureTheory.integrable_stoppedValue, MeasureTheory.hittingAfter_le_iff, MeasureTheory.hittingAfter_eq_top_iff, MeasureTheory.Adapted.isStoppingTime_hittingAfter, MeasureTheory.hittingBtwn, MeasureTheory.hittingBtwn_le, MeasureTheory.Adapted.isStoppingTime_hittingBtwn, MeasureTheory.stoppedValue_hittingBtwn_mem]
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

## Filtrations and stopping times

### Overview

A random process changes in time, and the information about it grows in time. A filtration is the model of this information: an increasing family of $\sigma$-algebras, one for each time. A process is adapted if its value at each time is known from the information at that time. A stopping time is a random time that a player can use without knowledge of the future: at each time, the information tells whether the time has come. This section defines these objects, shows that the first time a process enters a set is a stopping time, and defines the value of a process at a stopping time. Section 2 uses these objects to state the optional stopping theorem.

### Definitions

**Definition (Filtration).** Let $(\Omega, \mathcal{F})$ be a measurable space and let $I$ be a preordered set of times, usually $\mathbb{N}$ or $[0, \infty)$. A *filtration* is a family $(\mathcal{F}_i)_{i \in I}$ of $\sigma$-algebras with $\mathcal{F}_i \subseteq \mathcal{F}_j \subseteq \mathcal{F}$ for $i \le j$. A *filtered probability space* is a probability space with a filtration.

::: mathlib
`MeasureTheory.Filtration` · `Mathlib.Probability.Process.Filtration`

`Filtration ι m` is a structure with a monotone map `seq : ι → MeasurableSpace Ω` and the proof `le'` that each `seq i` is below the ambient σ-algebra `m`. It coerces to a function, so `ℱ i` is the σ-algebra at time `i`. `Filtration.mono` and `Filtration.le` are the two properties. `Filtration.const ι m' hm'` is the constant filtration. Filtrations form a complete lattice. The class `SigmaFiniteFiltration μ ℱ` asks that `μ.trim (ℱ.le i)` is σ-finite for each `i`; it holds for a finite measure, and the conditional expectations of the next sections need it.

<?decl MeasureTheory.Filtration?>
:::

**Definition (Adapted process, natural filtration).** A process $(X_i)_{i \in I}$ with values in a measurable space is *adapted* to $(\mathcal{F}_i)$ if $X_i$ is $\mathcal{F}_i$-measurable for each $i$. The *natural filtration* of $X$ is $\mathcal{F}^X_i = \sigma(X_j : j \le i)$. It is the smallest filtration to which $X$ is adapted.

::: mathlib
`MeasureTheory.StronglyAdapted` · `Mathlib.Probability.Process.Adapted`

Mathlib has two forms. `Adapted ℱ u` asks that each `u i` is `ℱ i`-measurable, for codomains with a σ-algebra. `StronglyAdapted ℱ u` asks that each `u i` is `ℱ i`-strongly measurable, for codomains with a topology. The martingale files use the strong form, because the Bochner integral and `condExp` use strong measurability. For second countable pseudometrizable Borel codomains, such as $\mathbb{R}$, the two forms agree (`stronglyAdapted_iff_adapted`). `Filtration.natural u hum` is the natural filtration of a strongly measurable process, and `Filtration.stronglyAdapted_natural` says that `u` is strongly adapted to it.

<?decl MeasureTheory.StronglyAdapted?>
:::

For a continuous time set, adaptedness is too weak for some arguments. A process is *progressively measurable* if, for each $i$, the map $(j, \omega) \mapsto X_j(\omega)$ on $\{j \le i\} \times \Omega$ is measurable for the product of the Borel $\sigma$-algebra and $\mathcal{F}_i$. In Mathlib this is `IsStronglyProgressive`, and `StronglyAdapted.isStronglyProgressive_of_discrete` proves it from adaptedness for a discrete time set. A process $(H_n)_{n \in \mathbb{N}}$ is *predictable* if $H_0$ is $\mathcal{F}_0$-measurable and $H_{n+1}$ is $\mathcal{F}_n$-measurable for each $n$: its value at time $n+1$ is known at time $n$. Mathlib defines `IsStronglyPredictable` for a general time set, through the predictable $\sigma$-algebra `Filtration.predictable` on $I \times \Omega$. On $\mathbb{N}$, `IsStronglyPredictable.measurable_add_one` gives the measurability of $H_{n+1}$ for $\mathcal{F}_n$, and `IsStronglyPredictable.stronglyAdapted` says that a predictable process is adapted.

**Definition (Stopping time).** A *stopping time* for $(\mathcal{F}_i)$ is a map $\tau : \Omega \to I \cup \{\infty\}$ with $\{\tau \le i\} \in \mathcal{F}_i$ for each $i \in I$. The value $\infty$ means that the time never comes.

::: mathlib
`MeasureTheory.IsStoppingTime` · `Mathlib.Probability.Process.Stopping`

`IsStoppingTime ℱ τ` takes `τ : Ω → WithTop ι` and asks `MeasurableSet[ℱ i] {ω | τ ω ≤ i}` for each `i`. The type `WithTop ι` adds the value `⊤` for "never". `isStoppingTime_const` gives the constant times. On a countable time set, `isStoppingTime_of_measurableSet_eq` proves the property from the sets $\{\tau = i\}$, and `IsStoppingTime.measurableSet_eq` gives these sets back. `IsStoppingTime.min`, `IsStoppingTime.max` and `IsStoppingTime.add_const` are the closure properties.

<?decl MeasureTheory.IsStoppingTime?>
:::

**Definition (The σ-algebra at a stopping time).** For a stopping time $\tau$, the $\sigma$-algebra of the events known at time $\tau$ is
$$\mathcal{F}_\tau = \{A \in \mathcal{F} : A \cap \{\tau \le i\} \in \mathcal{F}_i \text{ for all } i\}.$$

::: mathlib
`MeasureTheory.IsStoppingTime.measurableSpace` · `Mathlib.Probability.Process.Stopping`

`hτ.measurableSpace` is $\mathcal{F}_\tau$, defined from a proof `hτ : IsStoppingTime ℱ τ`. `IsStoppingTime.measurableSpace_mono` says that $\tau \le \sigma$ implies $\mathcal{F}_\tau \subseteq \mathcal{F}_\sigma$.

<?decl MeasureTheory.IsStoppingTime.measurableSpace?>
:::

**Definition (Stopped value, stopped process).** For a process $X$ and a random time $\tau$, the *stopped value* is $X_\tau(\omega) = X_{\tau(\omega)}(\omega)$, and the *stopped process* is $X^\tau_i = X_{\min(i, \tau)}$.

::: mathlib
`MeasureTheory.stoppedValue` · `Mathlib.Probability.Process.Stopping`

`stoppedValue u τ ω` is `u (τ ω) ω`, where the value `τ ω` in `WithTop ι` is sent back to `ι`. On the event $\{\tau = \infty\}$ this gives a junk value, so the results about it use bounded times or the event $\{\tau < \infty\}$. `stoppedProcess u τ i` is the stopped process, and `stoppedProcess_eq_stoppedValue` writes it as the stopped value at $\min(i, \tau)$. `integrable_stoppedValue` gives the integrability of $X_\tau$ for a stopping time bounded by a constant $N$, from the integrability of each $X_n$.

<?decl MeasureTheory.stoppedValue?>
:::

**Definition (Hitting time).** For a process $X$, a set $B$ and a time $n$, the *hitting time* of $B$ after $n$ is
$$\tau_B = \inf\{j \ge n : X_j \in B\},$$
with $\inf \varnothing = \infty$.

::: mathlib
`MeasureTheory.hittingAfter` · `Mathlib.Probability.Process.HittingTime`

`hittingAfter u s n ω : WithTop ι` is the first time `j ≥ n` with `u j ω ∈ s`, or `⊤` if there is none (`hittingAfter_eq_top_iff`). `hittingAfter_le_iff` says that $\tau_B \le i$ if and only if $X_j \in B$ for some $j \in [n, i]$, on a well founded time set. The older form `hittingBtwn u s n m` takes values in `ι`: it is the first hitting time in $[n, m]$, with the value $m$ if there is none (`hittingBtwn_le`). `stoppedValue_hittingBtwn_mem` says that the process at this time is in the set when the set is reached.

<?decl MeasureTheory.hittingAfter?>
:::

### Theorems and proofs

**Theorem (Hitting times are stopping times).** Let $(X_n)_{n \in \mathbb{N}}$ be adapted and let $B$ be measurable. Then $\tau_B$ is a stopping time.

*Proof.* For each $i$, $\{\tau_B \le i\} = \bigcup_{j = n}^{i} \{X_j \in B\}$. Each set in the union is in $\mathcal{F}_j \subseteq \mathcal{F}_i$, and the union is finite. $\square$

In Mathlib this is `Adapted.isStoppingTime_hittingAfter`, and `Adapted.isStoppingTime_hittingBtwn` is the bounded form. The Lean statement holds on a time set with a countable order structure and the order topology; the proof is the same.

**Theorem (Closure properties).** If $\sigma$ and $\tau$ are stopping times, then $\min(\sigma, \tau)$ and $\max(\sigma, \tau)$ are stopping times, and so is $\tau + c$ for a constant $c \ge 0$.

*Proof.* $\{\min(\sigma, \tau) \le i\} = \{\sigma \le i\} \cup \{\tau \le i\}$ and $\{\max(\sigma, \tau) \le i\} = \{\sigma \le i\} \cap \{\tau \le i\}$. For $\tau + c$, $\{\tau + c \le i\} = \{\tau \le i - c\}$ is in $\mathcal{F}_{i - c} \subseteq \mathcal{F}_i$ if $c \le i$, and is empty if $c > i$. $\square$

**Theorem (Measurability of the stopped value).** If $X$ is adapted and $\tau$ is a stopping time with values in a countable set, then $X_\tau \mathbf{1}_{\{\tau < \infty\}}$ is $\mathcal{F}_\tau$-measurable, and $\tau$ is $\mathcal{F}_\tau$-measurable.

*Proof.* For the second claim, $\{\tau \le j\} \cap \{\tau \le i\} = \{\tau \le \min(i, j)\} \in \mathcal{F}_i$. For the first claim, for a measurable $B$,
$$\{X_\tau \in B, \tau < \infty\} \cap \{\tau \le i\} = \bigcup_{j \le i} \{X_j \in B\} \cap \{\tau = j\},$$
and each set in the union is in $\mathcal{F}_j \subseteq \mathcal{F}_i$. $\square$

### Examples

**Example (A gambler who quits).** Let $X_1, X_2, \ldots$ be i.i.d. signs with $P(X_k = 1) = P(X_k = -1) = 1/2$, let $S_n = X_1 + \cdots + X_n$ be the fortune of a gambler, and let $\mathcal{F}_n = \sigma(X_1, \ldots, X_n)$. The time $\tau = \inf\{n : S_n \in \{-a, b\}\}$, at which the gambler is ruined or reaches the target, is a stopping time by the theorem above. In Lean it is `hittingAfter S {-a, b} 0`, and `Adapted.isStoppingTime_hittingAfter` gives the property. The rule "stop after the third loss" is a stopping time too.

**Counterexample (A last exit is not a stopping time).** In the same game, fix $N$ and let $\lambda = \max\{n \le N : S_n = 0\}$, the last visit to $0$ before time $N$. The event $\{\lambda \le 1\}$ is the event that $S_n \ne 0$ for $2 \le n \le N$. It depends on $X_2, \ldots, X_N$, and it is not in $\mathcal{F}_1$: for $N = 3$, the outcome $X_1 = 1$ is compatible with $S_2 = 0$ and with $S_2 = 2$. A player cannot use $\lambda$ as a rule, because the rule needs knowledge of the future.

**Example (A predictable strategy).** In the game above, the stake $H_{n+1}$ on toss $n+1$ is chosen from the results of the first $n$ tosses, so $(H_n)$ is predictable. The doubling strategy has $H_1 = 1$, and $H_{n+1} = 2H_n$ after a loss and $H_{n+1} = 0$ after the first win. The gain of a strategy is the discrete stochastic integral $(H \cdot S)_n = \sum_{k \le n} H_k (S_k - S_{k-1})$. Section 2 shows that the gain is a martingale for a bounded predictable $H$.

### The library around it

The files `Mathlib/Probability/Process/Filtration.lean`, `Adapted.lean`, `Predictable.lean`, `Stopping.lean` and `HittingTime.lean` contain this section. The time set is a general preorder, and most results need a linear order, a countable order structure or the order topology. This makes the same definitions serve for discrete and continuous time.

In this edition, stopping times take values in `WithTop ι`. A file written against an older Mathlib that uses `τ : Ω → ι` needs coercions. `hittingBtwn` keeps the older convention, and `hittingAfter` is the form for unbounded searches. The file `Mathlib/Probability/Process/LocalProperty.lean` defines localizing sequences of stopping times (`ProbabilityTheory.IsLocalizingSequence`), which the theory of local martingales needs. The index of this edition has no declaration for the stochastic integral in continuous time.

`Filtration.piLE` is the filtration of the coordinates $\omega_j$ with $j \le i$ on a product space $\prod_j \Omega_j$, and Chapter 8 uses it for the trajectories of a Markov chain.

### Exercises

1. (A) Prove that a constant $\tau = c$ is a stopping time, and that a stopping time on $\mathbb{N}$ for the trivial filtration $\mathcal{F}_i = \{\varnothing, \Omega\}$ is constant.
2. (A) Let $\tau$ be a stopping time on $\mathbb{N}$. Prove that $\{\tau = n\}$ and $\{\tau < n\}$ are in $\mathcal{F}_n$, and that $\{\tau > n\}$ is in $\mathcal{F}_n$.
3. (A) Prove that $\tau - 1$ is not a stopping time in general, with the hitting time of the random walk.
4. (B) Prove that $\mathcal{F}_\tau$ is a $\sigma$-algebra, and that $\mathcal{F}_\tau = \mathcal{F}_n$ if $\tau = n$ is constant.
5. (B) Let $\sigma \le \tau$ be stopping times. Prove that $\mathcal{F}_\sigma \subseteq \mathcal{F}_\tau$, and that $\{\sigma < \tau\}$ is in $\mathcal{F}_\sigma \cap \mathcal{F}_\tau$ for times in $\mathbb{N}$.
6. (B) Let $\tau_1$ be the first time the random walk reaches $1$ and let $\tau_2$ be the first time after $\tau_1$ that it reaches $0$. Prove that $\tau_2$ is a stopping time.
7. (B) Prove that the stopped process $X^\tau$ of an adapted process on $\mathbb{N}$ is adapted. Use $X^\tau_n = \sum_{k < n} X_k \mathbf{1}_{\{\tau = k\}} + X_n \mathbf{1}_{\{\tau \ge n\}}$.
8. (C) On the time set $[0, \infty)$, let $X$ be continuous and adapted, and let $F$ be closed. Prove that $\inf\{t : X_t \in F\}$ is a stopping time. Explain why the proof fails for an open set, and why it works for an open set with the filtration $\mathcal{F}_{t+} = \bigcap_{s > t} \mathcal{F}_s$.

### Notes and history

The notion of a stopping time is older than the general theory: Wald used random sample sizes of this kind in sequential analysis in the 1940s. Doob gave the general definitions of filtrations, adapted processes and stopping times in his book *Stochastic Processes* of 1953, which is the start of the modern theory of martingales.

### Reference

<?reference?>
