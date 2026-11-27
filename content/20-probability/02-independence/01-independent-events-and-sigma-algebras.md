---
title: Independent events and σ-algebras
kind: theory
modules:
  - Mathlib.Probability.Independence.Basic
  - Mathlib.Probability.Independence.Kernel.Indep
explains:
  E3: [ProbabilityTheory.IndepSet, ProbabilityTheory.Indep, ProbabilityTheory.iIndep, ProbabilityTheory.IndepSets.indep, ProbabilityTheory.indep_iSup_of_disjoint]
  E2: [ProbabilityTheory.IndepSets, ProbabilityTheory.iIndepSet, ProbabilityTheory.iIndepSets, ProbabilityTheory.Indep_iff, ProbabilityTheory.IndepSets_iff, ProbabilityTheory.iIndep_iff, ProbabilityTheory.iIndepSet_iff, ProbabilityTheory.iIndepSet_iff_meas_biInter, ProbabilityTheory.indepSet_iff_measure_inter_eq_mul, ProbabilityTheory.IndepSet_iff_Indep, ProbabilityTheory.Indep.symm, ProbabilityTheory.iIndep.indep, ProbabilityTheory.iIndepSets.iIndep, ProbabilityTheory.Kernel.Indep]
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

## Independent events and σ-algebras

### Overview

Independence is the notion that separates probability from general measure theory. Two events are independent when the knowledge that one has occurred does not change the probability of the other. In formulas, $P(A \cap B) = P(A) P(B)$. The definition extends to families of events, to σ-algebras and, in the next section, to random variables.

This section defines independence of two events, of a family of events and of a family of σ-algebras. It shows by an example that pairwise independence is weaker than mutual independence. The main theorem is the π-system criterion: to check that two σ-algebras are independent, it is enough to check the product formula on two generating π-systems. A corollary groups independent σ-algebras into disjoint blocks and keeps independence.

### Definitions

**Definition (Independent events).** Two events $A$ and $B$ are *independent* if $P(A \cap B) = P(A) P(B)$. A family $(A_i)_{i \in I}$ of events is *(mutually) independent* if
$$P\Big(\bigcap_{i \in J} A_i\Big) = \prod_{i \in J} P(A_i)$$
for each finite set $J \subseteq I$. The family is *pairwise independent* if $A_i$ and $A_j$ are independent for all $i \ne j$.

If $P(A) > 0$, independence says $P(B \mid A) = P(B)$. The product form is preferred because it is symmetric and has no condition on $P(A)$. An event of probability $0$ or $1$ is independent of each event.

**Definition (Independent classes and σ-algebras).** Let $\mathcal{C}_1, \mathcal{C}_2$ be families of events. They are *independent* if $P(A_1 \cap A_2) = P(A_1) P(A_2)$ for all $A_1 \in \mathcal{C}_1$ and $A_2 \in \mathcal{C}_2$. A family $(\mathcal{C}_i)_{i \in I}$ is *independent* if for each finite $J \subseteq I$ and each choice $A_i \in \mathcal{C}_i$ ($i \in J$), $P(\bigcap_{i \in J} A_i) = \prod_{i \in J} P(A_i)$. When the $\mathcal{C}_i$ are sub-σ-algebras of $\mathcal{F}$, this is the *independence of σ-algebras*.

Independence of events is a special case: the events $(A_i)$ are independent if and only if the σ-algebras $\sigma(A_i) = \{\emptyset, A_i, A_i^c, \Omega\}$ are independent. One direction is clear. For the other, the product formula for a choice that uses $A_i^c$ follows from the formula for $A_i$ by subtraction: $P(A_i^c \cap B) = P(B) - P(A_i \cap B) = (1 - P(A_i)) P(B)$ when $B$ is an intersection of the other chosen events. Induction on the number of complements gives all cases.

::: mathlib
`ProbabilityTheory.Indep` · `Mathlib.Probability.Independence.Basic`

`Indep m₁ m₂ μ` says that the σ-algebras `m₁ m₂ : MeasurableSpace Ω` are independent for `μ`; `Indep_iff` unfolds it to the product formula for all `m₁`-measurable `t1` and `m₂`-measurable `t2`. In Mathlib a σ-algebra is a term of type `MeasurableSpace Ω`, and sub-σ-algebras are ordered by `≤`. The measure is an `autoParam` with default `volume`. The definition is `Kernel.Indep m₁ m₂ (Kernel.const Unit μ) (Measure.dirac ())`: independence with respect to a kernel, read at a single point. So each theorem proved for kernels gives the theorem for measures, and the same proof also gives the conditional independence of Chapter 6.

<?decl ProbabilityTheory.Indep?>
:::

::: mathlib
`ProbabilityTheory.IndepSet` · `Mathlib.Probability.Independence.Basic`

`IndepSet s t μ` is defined as the independence of the σ-algebras `generateFrom {s}` and `generateFrom {t}`, as in the remark above (`IndepSet_iff_Indep`). For measurable sets and a probability measure, `indepSet_iff_measure_inter_eq_mul` gives the product formula `μ (s ∩ t) = μ s * μ t`. The families are `iIndepSet` for sets, `iIndepSets` for classes of sets and `iIndep` for σ-algebras, with the characterisations `iIndepSet_iff_meas_biInter` and `iIndep_iff` over finsets.

<?decl ProbabilityTheory.IndepSet?>
:::

::: mathlib
`ProbabilityTheory.iIndep` · `Mathlib.Probability.Independence.Basic`

`iIndep m μ` for `m : ι → MeasurableSpace Ω`. The index type `ι` is arbitrary. `iIndep.indep` extracts the independence of two members with different indices, which is the direction "mutual implies pairwise".

<?decl ProbabilityTheory.iIndep?>
:::

### Theorems and proofs

**Counterexample (Pairwise is not mutual).** Toss two fair coins. Let $A$ = "the first coin shows heads", $B$ = "the second coin shows heads", $C$ = "the two coins agree". On the four equally likely outcomes, $P(A) = P(B) = P(C) = 1/2$, and
$$P(A \cap B) = P(A \cap C) = P(B \cap C) = P(\{HH\}) = \tfrac14.$$
So the three events are pairwise independent. But $A \cap B \cap C = \{HH\}$ has probability $1/4 \ne 1/8$. The events are not mutually independent: $A$ and $B$ together determine $C$.

**Theorem (π-system criterion).** Let $\mathcal{P}_1, \mathcal{P}_2$ be π-systems of events, that is, families closed under finite intersections. If $\mathcal{P}_1$ and $\mathcal{P}_2$ are independent, then the σ-algebras $\sigma(\mathcal{P}_1)$ and $\sigma(\mathcal{P}_2)$ are independent.

*Proof.* The plan is to enlarge one side at a time with the π-λ theorem of Volume 18. Recall that a *λ-system* (Dynkin system) is a family that contains $\Omega$, is closed under complements, and is closed under countable disjoint unions. The π-λ theorem says that a λ-system that contains a π-system $\mathcal{P}$ contains $\sigma(\mathcal{P})$.

Step 1. Fix $B \in \mathcal{P}_2$ and let
$$\mathcal{L}_B = \{A \in \mathcal{F} : P(A \cap B) = P(A) P(B)\}.$$
It contains $\Omega$. If $A \in \mathcal{L}_B$, then $P(A^c \cap B) = P(B) - P(A \cap B) = P(B) - P(A)P(B) = P(A^c) P(B)$, so $A^c \in \mathcal{L}_B$. If $A_1, A_2, \ldots \in \mathcal{L}_B$ are disjoint, then the sets $A_n \cap B$ are disjoint and
$$P\Big(\bigcup_n A_n \cap B\Big) = \sum_n P(A_n \cap B) = \sum_n P(A_n) P(B) = P\Big(\bigcup_n A_n\Big) P(B).$$
So $\mathcal{L}_B$ is a λ-system. It contains $\mathcal{P}_1$ by hypothesis, so it contains $\sigma(\mathcal{P}_1)$. Thus $\sigma(\mathcal{P}_1)$ and $\mathcal{P}_2$ are independent.

Step 2. Fix $A \in \sigma(\mathcal{P}_1)$ and let $\mathcal{L}'_A = \{B \in \mathcal{F} : P(A \cap B) = P(A) P(B)\}$. The same computation shows that it is a λ-system, and Step 1 shows that it contains $\mathcal{P}_2$. So it contains $\sigma(\mathcal{P}_2)$. $\square$

The proof extends to finite and then to arbitrary families: if $(\mathcal{P}_i)_{i \in I}$ is an independent family of π-systems, then $(\sigma(\mathcal{P}_i))_{i \in I}$ is independent. For a finite $J$ one replaces the classes one at a time, with the intersection of the other chosen events as the fixed set $B$.

::: mathlib
`ProbabilityTheory.IndepSets.indep` · `Mathlib.Probability.Independence.Basic`

The hypotheses are: `m1 ≤ _mΩ` and `m2 ≤ _mΩ` (the σ-algebras are sub-σ-algebras of the ambient one), `IsPiSystem p1` and `IsPiSystem p2`, `m1 = generateFrom p1` and `m2 = generateFrom p2`, and `IndepSets p1 p2 μ`. The measure needs `IsZeroOrProbabilityMeasure μ`, which allows the zero measure as a degenerate case. The proof in Mathlib uses `MeasurableSpace.induction_on_inter`, the π-λ induction principle, as Step 1 and Step 2 do. The family form is `iIndepSets.iIndep`. The primed form `IndepSets.indep'` takes measurability of the members of `p1` and `p2` and generates the σ-algebras itself.

<?decl ProbabilityTheory.IndepSets.indep?>
:::

**Theorem (Grouping).** Let $(\mathcal{G}_i)_{i \in I}$ be independent sub-σ-algebras, and let $S, T \subseteq I$ be disjoint. Then $\mathcal{G}_S = \sigma\big(\bigcup_{i \in S} \mathcal{G}_i\big)$ and $\mathcal{G}_T = \sigma\big(\bigcup_{i \in T} \mathcal{G}_i\big)$ are independent.

*Proof.* Let $\mathcal{P}_S$ be the family of finite intersections $\bigcap_{i \in J} A_i$ with $J \subseteq S$ finite and $A_i \in \mathcal{G}_i$. It is a π-system, since the intersection of two such sets is again of this form (where an index appears twice, intersect the two sets of $\mathcal{G}_i$). It generates $\mathcal{G}_S$, because it contains each $\mathcal{G}_i$ for $i \in S$ and is contained in $\mathcal{G}_S$. Define $\mathcal{P}_T$ in the same way. For $C = \bigcap_{i \in J} A_i \in \mathcal{P}_S$ and $D = \bigcap_{i \in K} B_i \in \mathcal{P}_T$, the index sets $J$ and $K$ are disjoint, so mutual independence gives
$$P(C \cap D) = \prod_{i \in J} P(A_i) \prod_{i \in K} P(B_i) = P(C) P(D).$$
By the π-system criterion, $\mathcal{G}_S$ and $\mathcal{G}_T$ are independent. $\square$

::: mathlib
`ProbabilityTheory.indep_iSup_of_disjoint` · `Mathlib.Probability.Independence.Basic`

From `∀ i, m i ≤ _mΩ`, `iIndep m μ` and `Disjoint S T` it gives `Indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) μ`. The supremum `⨆` in the lattice of σ-algebras is the σ-algebra generated by the union, which is $\mathcal{G}_S$. The variants `indep_iSup_of_directed_le`, `indep_iSup_of_monotone` and `indep_iSup_of_antitone` pass independence to the supremum of a directed family. The zero-one law of Section 3 uses them.

<?decl ProbabilityTheory.indep_iSup_of_disjoint?>
:::

### Examples

**Example (The digits of a uniform number).** Let $\Omega = [0, 1)$ with the Lebesgue measure and let $d_n(\omega) \in \{0, 1\}$ be the $n$-th binary digit of $\omega$ (with the expansion that does not end in $1, 1, 1, \ldots$). The event $\{d_1 = a_1, \ldots, d_n = a_n\}$ is an interval of length $2^{-n}$, so $P(d_1 = a_1, \ldots, d_n = a_n) = 2^{-n}$. Summing over the digits that are not fixed shows $P(d_i = a_i \text{ for } i \in J) = 2^{-|J|}$ for each finite $J$. So the events $A_n = \{d_n = 1\}$ are mutually independent, each with probability $1/2$. The interval $[0, 1)$ with its length measure is a model of an infinite sequence of fair coin tosses.

**Example (Two dice).** With two dice, let $A$ = "the first die is even" and $B$ = "the sum is $7$". Then $P(A) = 1/2$, $P(B) = 6/36 = 1/6$, and $A \cap B = \{(2,5), (4,3), (6,1)\}$, so $P(A \cap B) = 3/36 = 1/12 = P(A)P(B)$. The events are independent. With $B'$ = "the sum is $8$", $P(B') = 5/36$ and $A \cap B' = \{(2,6), (4,4), (6,2)\}$, so $P(A \cap B') = 3/36 \ne (1/2)(5/36)$. Independence is a numerical coincidence of the model, not a property that one can see from the description of the events.

**Counterexample (Independence needs a π-system).** Let $\Omega = \{1, 2, 3, 4\}$ with the uniform probability, $\mathcal{C}_1 = \{\{1, 2\}, \{1, 3\}\}$ and $\mathcal{C}_2 = \{\{1, 4\}\}$. Each set has probability $1/2$, and each intersection $\{1\}$ has probability $1/4$, so $\mathcal{C}_1$ and $\mathcal{C}_2$ are independent. But $\{1, 2\} \cap \{1, 3\} = \{1\}$ and $P(\{1\} \cap \{1, 4\}) = 1/4 \ne (1/4)(1/2)$. So $\sigma(\mathcal{C}_1)$ is not independent of $\mathcal{C}_2$. The criterion fails because $\mathcal{C}_1$ is not closed under intersection.

### The library around it

The API of the file `Mathlib.Probability.Independence.Basic` follows a pattern. For each of the six notions `IndepSets`, `IndepSet`, `Indep`, `iIndepSets`, `iIndepSet`, `iIndep` there is a characterisation lemma `*_iff` with the product formula, a symmetry lemma `.symm` for the binary forms, monotonicity lemmas `indep_of_indep_of_le_left` and `indep_of_indep_of_le_right`, and the conversions between them: `iIndep.iIndepSets`, `iIndepSet_iff_iIndep`, `Indep.indepSets`. The trivial cases are `indep_bot_left` and `indep_bot_right` for the trivial σ-algebra `⊥`. The file `Mathlib.Probability.Independence.Kernel.Indep` contains the same lemmas for `Kernel.Indep`, and most proofs of the measure version are one line that applies the kernel version.

Common errors of a learner:

- `iIndep m μ` with `m : ℕ → MeasurableSpace Ω` is about the σ-algebras `m n`, which must be sub-σ-algebras of the ambient one. Many lemmas ask for `∀ n, m n ≤ mΩ` as a separate hypothesis.
- Pairwise independence of a family is `Pairwise (fun i j ↦ Indep (m i) (m j) μ)`, not `iIndep`. The strong law of Chapter 5 needs only the pairwise form.
- `IndepSet s t μ` for nonmeasurable sets has no product formula. The lemma `indepSet_iff_measure_inter_eq_mul` asks for `MeasurableSet s` and `MeasurableSet t`.

### Exercises

1. (A) Show that if $A$ and $B$ are independent, then so are $A$ and $B^c$, $A^c$ and $B^c$.
2. (A) Show that an event $A$ is independent of itself if and only if $P(A) \in \{0, 1\}$.
3. (A) Three dice are thrown. Are the events "the first two dice agree", "the last two agree" and "the first and the third agree" pairwise independent? Mutually independent?
4. (B) Let $A_1, \ldots, A_n$ be independent. Show that $P(\bigcup_i A_i) = 1 - \prod_i (1 - P(A_i))$, and deduce $P(\bigcup_i A_i) \ge 1 - \exp(-\sum_i P(A_i))$.
5. (B) Let $p$ be prime and $\Omega = \{1, \ldots, p\}$ with the uniform probability. Show that two events $A, B$ with $0 < P(A), P(B) < 1$ are never independent.
6. (B) Show that the family $\{d_1 = 1\}, \{d_2 = 1\}, \{d_1 = d_2\}$ of binary digits is pairwise independent but not independent, and identify it with the counterexample with two coins.
7. (C) Let $(\mathcal{G}_i)_{i \in I}$ be a family of σ-algebras such that for each finite $J$, the family $(\mathcal{G}_i)_{i \in J}$ is independent. Show that $(\mathcal{G}_i)_{i \in I}$ is independent, and explain why the definition was chosen with finite subfamilies.

### Notes and history

The product rule for independent events was used from the beginnings of probability, and de Moivre stated it in *The Doctrine of Chances* (1718). The definition of independence for σ-algebras and the reduction to π-systems belong to the measure theoretic probability of Kolmogorov. The example of three pairwise independent events that are not independent is due to Bernstein. In Mathlib, independence was first defined for measures and later rebuilt on kernels, so that conditional independence would reuse the same proofs.

### Reference

<?reference?>
