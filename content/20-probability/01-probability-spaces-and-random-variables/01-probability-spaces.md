---
title: Probability spaces and conditional probability
kind: theory
modules:
  - Mathlib.Probability.Notation
  - Mathlib.Probability.ConditionalProbability
  - Mathlib.Probability.UniformOn
explains:
  E3: [ProbabilityTheory.cond, ProbabilityTheory.uniformOn, ProbabilityTheory.cond_add_cond_compl_eq, ProbabilityTheory.cond_eq_inv_mul_cond_mul]
  E2: [ProbabilityTheory.cond_apply, ProbabilityTheory.cond_mul_eq_inter, ProbabilityTheory.cond_isProbabilityMeasure, ProbabilityTheory.cond_cond_eq_cond_inter, ProbabilityTheory.cond_univ, ProbabilityTheory.uniformOn_apply_finset, ProbabilityTheory.isProbabilityMeasure_uniformOn, ProbabilityTheory.uniformOn_univ, ProbabilityTheory.uniformOn_compl, ProbabilityTheory.sum_meas_smul_cond_fiber]
  E1: auto
families: []
requires: [V03, V13, V15]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Probability spaces and conditional probability

### Overview

A probability space is a model of a random experiment. It has three parts: the set $\Omega$ of the possible outcomes, the family $\mathcal{F}$ of the events, which are the sets of outcomes that the model can measure, and the probability $P$, which gives each event a number in $[0, 1]$. Kolmogorov's axioms say that $P$ is a measure of total mass $1$. So probability theory starts as a part of measure theory, and Volume 18, Measure and integration, gives all the tools of this section.

The section states the axioms, derives the first rules of computation, and builds the finite uniform spaces of classical probability. Then it defines the conditional probability $P(B \mid A)$ and proves the law of total probability and Bayes' formula. The examples compute with dice, with the birthday problem and with a medical test.

Mathlib has no type of probability spaces. A probability space is a measurable space `Ω` with a measure `μ` and the class `IsProbabilityMeasure μ`. The conditional probability is a new measure `ProbabilityTheory.cond μ s`, written `μ[|s]`.

### Definitions

**Definition (Probability space).** A *probability space* is a triple $(\Omega, \mathcal{F}, P)$. Here $\Omega$ is a set, $\mathcal{F}$ is a σ-algebra of subsets of $\Omega$, and $P : \mathcal{F} \to [0, 1]$ satisfies

1. $P(\Omega) = 1$;
2. if $A_1, A_2, \ldots \in \mathcal{F}$ are pairwise disjoint, then $P\big(\bigcup_n A_n\big) = \sum_n P(A_n)$.

The elements of $\mathcal{F}$ are *events*. An event $A$ with $P(A) = 1$ holds *almost surely*, written a.s. An event with $P(A) = 0$ is a *null event*.

So $P$ is a measure on $(\Omega, \mathcal{F})$ with $P(\Omega) = 1$. A property of the outcomes holds almost surely when the set where it fails is contained in a null event. The words "almost surely" of probability are the words "almost everywhere" of measure theory.

The σ-algebra is not a formality. On $\Omega = [0, 1]$ with the length measure, not every subset has a length (Volume 18 constructs a Vitali set). So a model of "a uniform random point of $[0, 1]$" must restrict the events to the Borel sets or the Lebesgue measurable sets. On a finite or countable $\Omega$ the problem does not appear, and one takes $\mathcal{F} = \mathcal{P}(\Omega)$.

::: mathlib
`MeasureTheory.IsProbabilityMeasure` · `Mathlib.MeasureTheory.Measure.Typeclasses.Probability`

A class on a measure `μ : Measure Ω`, with one field `measure_univ : μ univ = 1`. It is a class, not a structure that bundles `Ω` and `μ`, so each lemma about measures applies to `μ` without a conversion. The values of `μ` are in `ℝ≥0∞`, the extended nonnegative reals. The real number $P(A)$ is `μ.real A`, which is `(μ A).toReal`. Lemmas such as `prob_le_one` and `prob_compl_eq_one_sub` are stated in `ℝ≥0∞`, and the forms with `.real` have the prefix `probReal`.

<?decl MeasureTheory.IsProbabilityMeasure?>
:::

::: mathlib
`ProbabilityTheory.termℙ` · `Mathlib.Probability.Notation`

The file `Mathlib.Probability.Notation` is opened with `open ProbabilityTheory`. It defines `ℙ` for the measure `volume` of a type with a `MeasureSpace` instance, `𝔼[X]` for `∫ ω, X ω ∂volume`, `𝔼[X | m]` for the conditional expectation, `X =ₐₛ Y` and `X ≤ₐₛ Y` for the relations almost everywhere with respect to `volume`, and `∂P/∂Q` for the Radon-Nikodym derivative. Most theorems of the library take an explicit measure `μ` and do not use `ℙ`. The notation fits a text with one fixed probability space.
:::

**Definition (Uniform probability on a finite set).** Let $S \subseteq \Omega$ be finite and nonempty. The *uniform probability on $S$* is
$$U_S(A) = \frac{|A \cap S|}{|S|} \qquad (A \subseteq \Omega).$$

This is the classical probability of Laplace: the number of favourable cases divided by the number of possible cases. It is a probability measure, since $U_S(\Omega) = |S|/|S| = 1$ and the cardinality of a disjoint union is the sum of the cardinalities.

::: mathlib
`ProbabilityTheory.uniformOn` · `Mathlib.Probability.UniformOn`

`uniformOn s` is the counting measure restricted to `s` and divided by `count s`. It is defined for every set `s`. If `s` is infinite, `count s = ∞` and the measure is `0`. If `s` is empty, it is `0` too. So `isProbabilityMeasure_uniformOn` needs `s.Finite` and `s.Nonempty`. For finsets, `uniformOn_apply_finset` gives `(s ∩ t).card / s.card`, and on a `Fintype` the lemma `uniformOn_univ` gives `count s / Fintype.card Ω`.

<?decl ProbabilityTheory.uniformOn?>
:::

**Definition (Conditional probability).** Let $A$ be an event with $P(A) > 0$. The *conditional probability of $B$ given $A$* is
$$P(B \mid A) = \frac{P(A \cap B)}{P(A)}.$$

The map $B \mapsto P(B \mid A)$ is a probability measure. It is nonnegative, its value at $\Omega$ is $P(A)/P(A) = 1$, and it is countably additive because $B \mapsto P(A \cap B)$ is. It describes the experiment for an observer who knows that $A$ has occurred: the outcomes outside $A$ get probability $0$, and the outcomes in $A$ keep their relative weights.

::: mathlib
`ProbabilityTheory.cond` · `Mathlib.Probability.ConditionalProbability`

`cond μ s` is the measure `(μ s)⁻¹ • μ.restrict s`, with the notation `μ[|s]`, and `μ[t|s]` is its value at `t`. The definition has no hypothesis. If `μ s = 0`, then `(μ s)⁻¹ = ∞` in `ℝ≥0∞`, but `μ.restrict s = 0`, and `∞ • 0 = 0`; so `μ[|s] = 0` is the junk value. The lemma `cond_isProbabilityMeasure` makes `μ[|s]` a probability measure when `μ` is finite and `μ s ≠ 0`. The value is computed by `cond_apply`: `μ[t|s] = (μ s)⁻¹ * μ (s ∩ t)` for measurable `s`. The notation `μ[|X ← x]` conditions on the event `X = x`.

<?decl ProbabilityTheory.cond?>
:::

### Theorems and proofs

**Proposition (First rules).** Let $(\Omega, \mathcal{F}, P)$ be a probability space and $A, B \in \mathcal{F}$.

1. $P(\emptyset) = 0$ and $P(A^c) = 1 - P(A)$.
2. If $A \subseteq B$, then $P(A) \le P(B)$ and $P(B \setminus A) = P(B) - P(A)$.
3. $P(A \cup B) = P(A) + P(B) - P(A \cap B)$.
4. For each sequence of events, $P\big(\bigcup_n A_n\big) \le \sum_n P(A_n)$.

*Proof.* 1. Apply additivity to $\Omega = \Omega \cup \emptyset \cup \emptyset \cup \cdots$. This gives $1 = 1 + \sum_{n \ge 2} P(\emptyset)$, so $P(\emptyset) = 0$. Then finite additivity holds, because a finite family can be extended with empty sets. From $\Omega = A \cup A^c$, disjoint, $1 = P(A) + P(A^c)$.

2. $B = A \cup (B \setminus A)$ is a disjoint union, so $P(B) = P(A) + P(B \setminus A)$. Both claims follow, since $P(B \setminus A) \ge 0$ and all values are finite.

3. Write $A \cup B = A \cup (B \setminus (A \cap B))$, a disjoint union. By part 2 applied to $A \cap B \subseteq B$,
$$P(A \cup B) = P(A) + P(B) - P(A \cap B).$$

4. Let $B_1 = A_1$ and $B_n = A_n \setminus (A_1 \cup \cdots \cup A_{n-1})$. The $B_n$ are disjoint, $B_n \subseteq A_n$, and $\bigcup_n B_n = \bigcup_n A_n$. So $P(\bigcup_n A_n) = \sum_n P(B_n) \le \sum_n P(A_n)$ by part 2. $\square$

In Mathlib these rules are the general lemmas of measures: `measure_mono`, `measure_union_add_inter`, `measure_iUnion_le` (in `ℝ≥0∞`), and `prob_compl_eq_one_sub` for the complement. Part 4 is the *union bound*. It is the most used inequality of probability.

**Theorem (Law of total probability).** Let $A_1, \ldots, A_n$ be a partition of $\Omega$ into events with $P(A_i) > 0$. For each event $B$,
$$P(B) = \sum_{i=1}^n P(B \mid A_i)\, P(A_i).$$

*Proof.* The sets $B \cap A_i$ are disjoint and their union is $B$. So $P(B) = \sum_i P(B \cap A_i)$. By the definition of the conditional probability, $P(B \cap A_i) = P(B \mid A_i) P(A_i)$. $\square$

The same proof works for a countable partition, with a series in place of the finite sum.

::: mathlib
`ProbabilityTheory.cond_add_cond_compl_eq` · `Mathlib.Probability.ConditionalProbability`

The case $n = 2$, with the partition $s, s^c$: `μ[t|s] * μ s + μ[t|sᶜ] * μ sᶜ = μ t` for a finite measure and a measurable `s`. There is no hypothesis `μ s ≠ 0`. If `μ s = 0`, then `μ[t|s] = 0` by the junk value, and the term is $0 \cdot 0$, which is the correct value of $P(t \cap s)$. The form for the fibres of a random variable `X` with finitely many values is `sum_meas_smul_cond_fiber`: the sum of `μ (X ⁻¹' {x}) • μ[|X ← x]` over `x` is `μ`.

<?decl ProbabilityTheory.cond_add_cond_compl_eq?>
:::

**Theorem (Bayes' formula).** Let $A, B$ be events with $P(A) > 0$ and $P(B) > 0$. Then
$$P(B \mid A) = \frac{P(A \mid B)\, P(B)}{P(A)}.$$
If $B_1, \ldots, B_n$ is a partition of $\Omega$ into events of positive probability, then
$$P(B_j \mid A) = \frac{P(A \mid B_j)\, P(B_j)}{\sum_{i=1}^n P(A \mid B_i)\, P(B_i)}.$$

*Proof.* Both $P(B \mid A) P(A)$ and $P(A \mid B) P(B)$ are equal to $P(A \cap B)$. Divide by $P(A)$. For the second form, replace $P(A)$ in the denominator by the law of total probability for the partition $(B_i)$. $\square$

::: mathlib
`ProbabilityTheory.cond_eq_inv_mul_cond_mul` · `Mathlib.Probability.ConditionalProbability`

The statement is `μ[t|s] = (μ s)⁻¹ * μ[s|t] * μ t` for measurable `s` and `t` and a finite measure `μ`. As above, no positivity is assumed: when a probability is $0$ both sides reduce to the junk value $0$. In `ℝ≥0∞` the product `(μ s)⁻¹ * μ[s|t] * μ t` is computed without care for division by zero, but a user who needs a real number applies `ENNReal.toReal` at the end.

<?decl ProbabilityTheory.cond_eq_inv_mul_cond_mul?>
:::

**Proposition (Conditioning twice).** If $P(A \cap B) > 0$, then conditioning on $A$ and then on $B$ is conditioning on $A \cap B$: $P_A(C \mid B) = P(C \mid A \cap B)$, where $P_A = P(\cdot \mid A)$.

*Proof.* $P_A(B) = P(A \cap B)/P(A) > 0$. By the definition,
$$P_A(C \mid B) = \frac{P_A(B \cap C)}{P_A(B)} = \frac{P(A \cap B \cap C)/P(A)}{P(A \cap B)/P(A)} = \frac{P(A \cap B \cap C)}{P(A \cap B)}. \quad \square$$

In Mathlib this is `cond_cond_eq_cond_inter`: `μ[|s][|t] = μ[|s ∩ t]`.

### Examples

**Example (Two dice).** Let $\Omega = \{1, \ldots, 6\}^2$ with the uniform probability, so each of the 36 outcomes has probability $1/36$. Let $S$ be the event that the sum is $8$, and $D$ the event that the two dice show the same number. The outcomes of $S$ are $(2,6), (3,5), (4,4), (5,3), (6,2)$, so $P(S) = 5/36$. $D$ has 6 outcomes, and $S \cap D = \{(4,4)\}$. So
$$P(D \mid S) = \frac{1/36}{5/36} = \frac{1}{5}, \qquad P(S \mid D) = \frac{1/36}{6/36} = \frac{1}{6}.$$
The two conditional probabilities differ, and Bayes' formula links them: $P(D \mid S) = P(S \mid D) P(D)/P(S) = (1/6)(1/6)/(5/36) = 1/5$.

**Example (The birthday problem).** Choose the birthdays of $k$ people uniformly in $\{1, \ldots, 365\}^k$. The event that all birthdays differ has $365 \cdot 364 \cdots (365 - k + 1)$ outcomes. So
$$p_k = P(\text{all differ}) = \prod_{j=0}^{k-1} \Big(1 - \frac{j}{365}\Big).$$
The inequality $1 - x \le e^{-x}$ gives $p_k \le \exp\big(-\sum_{j < k} j/365\big) = \exp(-k(k-1)/730)$. For $k = 23$ the exponent is $-506/730 \approx -0.693$, so $p_{23} \le 0.500$. The exact product is $p_{23} \approx 0.4927$. So in a group of 23 people two share a birthday with probability more than $1/2$.

**Example (A medical test).** A disease affects $1\%$ of a population. A test detects it with probability $0.95$ for a sick person and gives a false positive with probability $0.02$ for a healthy person. Let $M$ be the event "sick" and $T$ the event "positive". The law of total probability gives
$$P(T) = 0.95 \cdot 0.01 + 0.02 \cdot 0.99 = 0.0095 + 0.0198 = 0.0293.$$
Bayes' formula gives $P(M \mid T) = 0.0095/0.0293 \approx 0.324$. So two thirds of the positive results are false. The error of a learner is to confuse $P(T \mid M) = 0.95$ with $P(M \mid T)$.

**Counterexample (Conditioning on a null event).** On $[0, 1]$ with the length measure, the event $A = \{1/2\}$ has $P(A) = 0$. The quotient $P(B \cap A)/P(A)$ is $0/0$, and the definition gives nothing. Yet "the law of $Y$ given $X = x$" for a continuous variable $X$ conditions on the null events $\{X = x\}$. Chapter 6 and Chapter 8 solve this problem with the conditional expectation and with the disintegration of measures. In Mathlib the formula `μ[|s]` returns the measure $0$ here, which is a junk value and not a conditional law.

### The library around it

The file `Mathlib.Probability.ConditionalProbability` has the API of `cond`: `cond_apply` and `cond_apply'` compute a value, `cond_mul_eq_inter` gives $P(t \mid s) P(s) = P(s \cap t)$, `cond_univ` says that conditioning on $\Omega$ changes nothing, `cond_empty` and `cond_eq_zero` give the junk cases, and `ae_cond_mem` says that `μ[|s]`-almost every point lies in `s`. The file `Mathlib.Probability.UniformOn` gives the same API for the uniform measure: `uniformOn_compl`, `uniformOn_union`, `uniformOn_inter`, and `uniformOn_pi`, which identifies the uniform measure on a product of finite sets with the product of the uniform measures. Chapter 2 uses that lemma for independent coins.

Common errors of a learner:

- A value `μ A` is in `ℝ≥0∞`. Subtraction there truncates, so `1 - μ A` is correct only because `μ A ≤ 1`. For real computations use `μ.real`.
- `μ[t|s]` is the probability of `t` given `s`. The order of the arguments is the order of the notation $P(t \mid s)$, but `cond μ s` takes the conditioning set first.
- `uniformOn s` on an infinite set `s` is the zero measure, not a probability.

### Exercises

1. (A) Show that $P(A \cap B) \ge P(A) + P(B) - 1$ for all events $A, B$. Deduce that if $P(A) = P(B) = 0.9$, then $P(A \cap B) \ge 0.8$.
2. (A) Three fair coins are tossed. Compute the probability of at least two heads given that the first coin shows heads.
3. (A) Prove inclusion-exclusion for three events: $P(A \cup B \cup C) = \sum P(A) - \sum P(A \cap B) + P(A \cap B \cap C)$.
4. (B) Prove $P(A_1 \cap \cdots \cap A_n) = P(A_1) P(A_2 \mid A_1) \cdots P(A_n \mid A_1 \cap \cdots \cap A_{n-1})$ when the conditioning events have positive probability. Use it to compute the probability that 4 cards drawn from 52 are all aces.
5. (B) In the medical test, the test is repeated on a person with a first positive result, and the two results are independent given the state of the person. Compute the probability of the disease after two positive results.
6. (B) Find the smallest $k$ with $p_k < 1/2$ in the birthday problem, and show that $p_k \ge 1 - k(k-1)/730$. Hint: the union bound over the pairs.
7. (C) Show that there is no probability measure on $\mathcal{P}(\mathbb{N})$ that gives the same value to all singletons. Then show that the "density" $d(A) = \lim_N |A \cap \{1, \ldots, N\}|/N$, where it exists, is finitely additive but not countably additive.

### Notes and history

The axioms are due to Kolmogorov, in *Grundbegriffe der Wahrscheinlichkeitsrechnung* (1933). Before them, probability had no agreed foundation, and the paradoxes of Bertrand showed that "a random chord" has no meaning without a model. The formula of Bayes appears in his posthumous essay of 1763, and Laplace stated the general form. The birthday problem is a standard example of Feller, *An Introduction to Probability Theory and Its Applications*, Volume 1. In Mathlib, probability is built on the measure theory of `Mathlib.MeasureTheory`, and the conditional measure `cond` is one of the first definitions of the `Probability` folder.

### Reference

<?reference?>
