---
title: The Borel-Cantelli lemmas and the zero-one law
kind: theory
modules:
  - Mathlib.Probability.BorelCantelli
  - Mathlib.Probability.Independence.ZeroOne
explains:
  E3: [ProbabilityTheory.measure_limsup_eq_one, ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop, ProbabilityTheory.indep_limsup_atTop_self]
  E2: [ProbabilityTheory.measure_eq_zero_or_one_of_indepSet_self, ProbabilityTheory.measure_eq_zero_or_one_of_indep_self, ProbabilityTheory.indep_biSup_compl, ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atBot, ProbabilityTheory.indep_limsup_atBot_self, ProbabilityTheory.Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop]
  E1: auto
families: []
requires: [V03, V13, V15, V20.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Borel-Cantelli lemmas and the zero-one law

### Overview

Many events of probability concern the long run of a sequence: a coin shows heads infinitely often, a random series converges, the averages of a sequence have a limit. This section gives two tools for such events. The Borel-Cantelli lemmas decide whether infinitely many events of a sequence occur, from the sum of their probabilities. Kolmogorov's zero-one law says that an event which depends only on the tail of an independent sequence has probability $0$ or $1$. Both tools give a qualitative answer, and a probabilist uses them to reduce a question to the computation of a series.

### Definitions

**Definition (Limit superior of events).** For events $A_1, A_2, \ldots$ the event
$$\limsup_n A_n = \bigcap_{n \ge 1} \bigcup_{k \ge n} A_k$$
is the set of the outcomes in infinitely many $A_k$. Probabilists write it $\{A_n \text{ i.o.}\}$, for "infinitely often". The event $\liminf_n A_n = \bigcup_n \bigcap_{k \ge n} A_k$ is the set of the outcomes in all $A_k$ from some index on. The complement of $\limsup_n A_n$ is $\liminf_n A_n^c$.

::: mathlib
`Filter.limsup` · `Mathlib.Order.LiminfLimsup`

For `s : ℕ → Set Ω`, the term `Filter.limsup s Filter.atTop` is the limit superior in the complete lattice `Set Ω`. The lemma `Filter.blimsup_eq_iInf_biSup_of_nat` and its relatives rewrite it as `⋂ n, ⋃ i ≥ n, s i`, and `Filter.mem_limsup_iff_frequently_mem` says that `ω` is in it if and only if `∃ᶠ n in atTop, ω ∈ s n`.
:::

**Definition (Tail σ-algebra).** Let $(\mathcal{F}_n)_{n \ge 1}$ be σ-algebras on $\Omega$. The *tail σ-algebra* is
$$\mathcal{T} = \bigcap_{n \ge 1} \sigma\Big(\bigcup_{k \ge n} \mathcal{F}_k\Big).$$
An event of $\mathcal{T}$ is a *tail event*. For a sequence of random variables $X_n$, take $\mathcal{F}_n = \sigma(X_n)$. A tail event is then an event that does not change if finitely many of the $X_n$ change.

::: mathlib
`Filter.limsup` of σ-algebras · `Mathlib.Probability.Independence.ZeroOne`

Mathlib writes the tail σ-algebra as `limsup s atTop` for `s : ι → MeasurableSpace Ω`, in the complete lattice of σ-algebras. This is `⨅ n, ⨆ i ≥ n, s i`, the formula above. The same expression with a general filter in place of `atTop` gives the general zero-one law `measure_zero_or_one_of_measurableSet_limsup`.
:::

### Theorems and proofs

**Theorem (First Borel-Cantelli lemma).** If $\sum_n P(A_n) < \infty$, then $P(\limsup_n A_n) = 0$. Independence is not necessary.

*Proof.* For each $n$, $\limsup_k A_k \subseteq \bigcup_{k \ge n} A_k$, so $P(\limsup_k A_k) \le \sum_{k \ge n} P(A_k)$. The right side is the tail of a convergent series and tends to $0$. $\square$

This is a theorem of measure theory and holds for each measure. Mathlib keeps it with the measure theory.

::: mathlib
`MeasureTheory.measure_limsup_atTop_eq_zero` · `Mathlib.MeasureTheory.OuterMeasure.BorelCantelli`

`∑' i, μ (s i) ≠ ∞ → μ (limsup s atTop) = 0`. The hypothesis is on the sum in `ℝ≥0∞`, so no summability proof is necessary; the sets need not be measurable.

<?decl MeasureTheory.measure_limsup_atTop_eq_zero?>
:::

**Theorem (Second Borel-Cantelli lemma).** If the events $A_n$ are independent and $\sum_n P(A_n) = \infty$, then $P(\limsup_n A_n) = 1$.

*Proof.* It is sufficient to show $P\big(\bigcap_{k \ge n} A_k^c\big) = 0$ for each $n$, because the complement of $\limsup_n A_n$ is the countable union of these events. The complements $A_k^c$ are independent. For $m \ge n$, independence and the inequality $1 - x \le e^{-x}$ give
$$P\Big(\bigcap_{k = n}^m A_k^c\Big) = \prod_{k = n}^m (1 - P(A_k)) \le \exp\Big(-\sum_{k = n}^m P(A_k)\Big).$$
As $m \to \infty$ the sum tends to $\infty$, so the right side tends to $0$. The left side tends to $P\big(\bigcap_{k \ge n} A_k^c\big)$ by continuity from above. $\square$

The proof uses mutual independence through the product formula for finitely many events. Pairwise independence is sufficient, with a proof through Chebyshev's inequality of Chapter 3 (Exercise 6).

::: mathlib
`ProbabilityTheory.measure_limsup_eq_one` · `Mathlib.Probability.BorelCantelli`

For measurable `s : ℕ → Set Ω`, `iIndepSet s μ` and `∑' n, μ (s n) = ∞`, the conclusion is `μ (limsup s atTop) = 1`. The measure is a probability measure. The Mathlib proof is not the proof above: it goes through the martingale version of Borel-Cantelli in `Mathlib.Probability.Martingale.BorelCantelli` (Chapter 7), applied to the filtration of the events.

<?decl ProbabilityTheory.measure_limsup_eq_one?>
:::

**Theorem (Kolmogorov's zero-one law).** Let $(\mathcal{F}_n)$ be independent σ-algebras, all contained in the σ-algebra of the space. Then each tail event has probability $0$ or $1$.

*Proof.* Put $\mathcal{G}_n = \sigma(\mathcal{F}_1 \cup \cdots \cup \mathcal{F}_n)$ and $\mathcal{H}_n = \sigma\big(\bigcup_{k > n} \mathcal{F}_k\big)$. The grouping theorem of Section 1 says that $\mathcal{G}_n$ and $\mathcal{H}_n$ are independent. The tail σ-algebra $\mathcal{T}$ is contained in each $\mathcal{H}_n$, so $\mathcal{T}$ is independent of each $\mathcal{G}_n$.

The union $\bigcup_n \mathcal{G}_n$ is an increasing union of σ-algebras, so it is a π-system. It is independent of $\mathcal{T}$, and the π-system criterion of Section 1 gives that $\mathcal{T}$ is independent of $\mathcal{G}_\infty = \sigma\big(\bigcup_n \mathcal{G}_n\big)$. But $\mathcal{T} \subseteq \mathcal{G}_\infty$. So $\mathcal{T}$ is independent of itself.

Let $T \in \mathcal{T}$. Then $P(T) = P(T \cap T) = P(T)^2$, so $P(T) \in \{0, 1\}$. $\square$

::: mathlib
`ProbabilityTheory.indep_limsup_atTop_self` · `Mathlib.Probability.Independence.ZeroOne`

For `s : ι → MeasurableSpace Ω` with `∀ n, s n ≤ m0` and `iIndep s μ`, over a directed index without maximum: `Indep (limsup s atTop) (limsup s atTop) μ`. This is the step "independent of itself" of the proof. The last step is `measure_eq_zero_or_one_of_indep_self`, and for one event `measure_eq_zero_or_one_of_indepSet_self`. The first step of the proof is `indep_biSup_compl`: the σ-algebras of the indices in `t` and of the indices in `tᶜ` are independent.

<?decl ProbabilityTheory.indep_limsup_atTop_self?>
:::

::: mathlib
`ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop` · `Mathlib.Probability.Independence.ZeroOne`

The zero-one law in the form for use: under the same hypotheses, `MeasurableSet[limsup s atTop] t → μ t = 0 ∨ μ t = 1`. The form with `atBot` is `measure_zero_or_one_of_measurableSet_limsup_atBot`. As for all of Chapter 2, the file proves the result for kernels first (`Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop`) and gets the result for measures with a constant kernel. The same file has the conditional form with `condExp`, for Chapter 6.

<?decl ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop?>
:::

### Examples

**Example (Infinitely many heads).** Toss a fair coin infinitely often, on the product space of Section 2. Let $A_n$ be the event that toss $n$ shows heads. The events are independent and $\sum_n P(A_n) = \sum_n 1/2 = \infty$. By the second lemma, heads appears infinitely often with probability $1$. Let $B_n$ be the event that tosses $n, n+1, \ldots, n + k - 1$ all show heads, for a fixed $k$. The events $B_k, B_{2k}, B_{3k}, \ldots$ use disjoint blocks of tosses, so they are independent, and each has probability $2^{-k}$. So each finite word appears infinitely often in the sequence of tosses, with probability $1$.

**Example (Long runs).** Let $\ell_n$ be the length of the run of heads that starts at toss $n$. Then $P(\ell_n \ge r) = 2^{-r}$. Take $r_n = \lceil (1 + \varepsilon) \log_2 n \rceil$. Then $\sum_n P(\ell_n \ge r_n) \le \sum_n n^{-1-\varepsilon} < \infty$, so the first lemma gives that a.s. $\ell_n < (1+\varepsilon)\log_2 n$ for all large $n$. This is half of the theorem of Erdős and Rényi that the longest run in $n$ tosses is about $\log_2 n$. The other half uses the second lemma on disjoint blocks.

**Counterexample (The second lemma needs independence).** Let $U$ be uniform on $[0, 1]$ and $A_n = \{U < 1/n\}$. Then $\sum_n P(A_n) = \sum_n 1/n = \infty$, but $\limsup_n A_n = \{U = 0\}$, which has probability $0$. The events are not independent: $A_{n+1} \subseteq A_n$.

**Example (Tail events of a random series).** Let $(X_n)$ be independent real variables. The event $\{\sum_n X_n \text{ converges}\}$ is a tail event, because a change of finitely many terms does not change the convergence. So the series converges with probability $0$ or $1$. The same holds for $\{\limsup_n (X_1 + \cdots + X_n)/n \le c\}$ for each $c$. So $\limsup_n (X_1 + \cdots + X_n)/n$ is a.s. equal to a constant in $[-\infty, \infty]$. The strong law of Chapter 5 identifies the constant. The sum itself, $\sum_n X_n$ where it converges, is not a tail variable, and its law can be any law.

### The library around it

The files of this section are short. `Mathlib.Probability.BorelCantelli` has the second lemma `measure_limsup_eq_one` and the results on the filtration `filtrationOfSet` generated by a sequence of events, which the proof uses. `Mathlib.Probability.Independence.ZeroOne` has the zero-one law for a general filter (`measure_zero_or_one_of_measurableSet_limsup`), the cases `atTop` and `atBot`, and the conditional forms `condIndep_limsup_atTop_self` and `condExp_zero_or_one_of_measurableSet_limsup_atTop`, which need a standard Borel space.

The first lemma lives in measure theory, in `Mathlib.MeasureTheory.OuterMeasure.BorelCantelli`, and has the variant `measure_limsup_cofinite_eq_zero` for the filter of cofinite sets.

Common errors of a learner:

- The tail σ-algebra in Mathlib is `limsup s atTop` for σ-algebras, not the limit superior of events. A tail event `t` is given by `MeasurableSet[limsup s atTop] t`.
- The zero-one law needs `∀ n, s n ≤ m0`, which says that each σ-algebra of the family is part of the σ-algebra of the space. For `s n = MeasurableSpace.comap (X n) mβ` this follows from the measurability of `X n` (`Measurable.comap_le`).
- The second lemma in Mathlib asks for `iIndepSet`, mutual independence, though the pairwise form is true.

### Exercises

1. (A) Let $P(A_n) = 1/n^2$. Show that a.s. only finitely many $A_n$ occur, without an assumption of independence.
2. (A) Let $X_n$ be independent with $P(X_n = 1) = p_n$ and $P(X_n = 0) = 1 - p_n$. Show that $X_n \to 0$ a.s. if and only if $\sum_n p_n < \infty$.
3. (A) Show that $\liminf_n A_n \subseteq \limsup_n A_n$ and that $(\limsup_n A_n)^c = \liminf_n A_n^c$.
4. (B) Let $X_n$ be i.i.d. and exponential with parameter $1$, that is $P(X_n > t) = e^{-t}$. Show that $\limsup_n X_n / \log n = 1$ a.s.
5. (B) Let $(X_n)$ be i.i.d. real variables. Show that $E|X_1| < \infty$ if and only if $P(|X_n| > n \text{ i.o.}) = 0$. Use $\sum_n P(|X_1| > n) \le E|X_1| \le 1 + \sum_n P(|X_1| > n)$.
6. (C) Let $A_n$ be pairwise independent with $\sum_n P(A_n) = \infty$. Put $S_n = \sum_{k \le n} \mathbf{1}_{A_k}$ and $m_n = E S_n$. Use the variance of Chapter 3 to show $\operatorname{Var}(S_n) \le m_n$, then Chebyshev to show $P(S_n \le m_n/2) \le 4/m_n$. Conclude $P(S_n \to \infty) = 1$.
7. (B) Let $(X_n)$ be independent. Show that the radius of convergence of the power series $\sum_n X_n z^n$ is a.s. a constant.

### Notes and history

Borel proved the first lemma and a form of the second in his paper of 1909 on denumerable probabilities, where he also proved that almost all numbers are normal. Cantelli gave the general first lemma in 1917. Kolmogorov stated the zero-one law in his book of 1933, *Grundbegriffe der Wahrscheinlichkeitsrechnung*. The pairwise form of the second lemma is due to Erdős and Rényi (1959).

### Reference

<?reference?>
