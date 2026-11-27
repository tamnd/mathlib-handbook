---
title: Outer measures and the theorem of Carathéodory
kind: theory
modules:
  - Mathlib.MeasureTheory.OuterMeasure.Defs
  - Mathlib.MeasureTheory.OuterMeasure.Basic
  - Mathlib.MeasureTheory.OuterMeasure.Caratheodory
  - Mathlib.MeasureTheory.OuterMeasure.OfFunction
  - Mathlib.MeasureTheory.OuterMeasure.Induced
  - Mathlib.MeasureTheory.OuterMeasure.Operations
  - Mathlib.MeasureTheory.Measure.OuterMeasure
explains:
  E3: [MeasureTheory.OuterMeasure, MeasureTheory.OuterMeasure.ofFunction, MeasureTheory.OuterMeasure.IsCaratheodory, MeasureTheory.OuterMeasure.caratheodory, MeasureTheory.OuterMeasure.toMeasure]
  E2: [MeasureTheory.OuterMeasure.ofFunction_le, MeasureTheory.OuterMeasure.ofFunction_apply, MeasureTheory.OuterMeasure.isCaratheodory_iff_le, MeasureTheory.OuterMeasure.f_iUnion, MeasureTheory.OuterMeasure.ofFunction_caratheodory, MeasureTheory.inducedOuterMeasure, MeasureTheory.inducedOuterMeasure_caratheodory, MeasureTheory.OuterMeasure.trim, MeasureTheory.OuterMeasure.trim_eq, MeasureTheory.Measure.toOuterMeasure, MeasureTheory.Measure.ofMeasurable, MeasureTheory.toMeasure_apply, MeasureTheory.le_toOuterMeasure_caratheodory, MeasureTheory.OuterMeasure.boundedBy]
  E1: auto
families: []
requires: [V03, V04, V13, V18.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Outer measures and the theorem of Carathéodory

### Overview

Section 1 gives no way to construct a measure beyond sums of Dirac masses. This section extends a set function to a measure in two steps. First, a function $m$ on a family of sets gives an *outer measure* $\mu^*$ on all subsets, by covers: $\mu^*(A)$ is the infimum of $\sum_n m(E_n)$ over the countable covers of $A$. An outer measure is only subadditive. Second, the theorem of Carathéodory selects a σ-algebra of sets on which $\mu^*$ is countably additive.

### Definitions

**Definition (outer measure).** An *outer measure* on a set $X$ is a map $\mu^* : \mathcal{P}(X) \to [0, \infty]$ with $\mu^*(\emptyset) = 0$, $\mu^*(A) \le \mu^*(B)$ for $A \subseteq B$, and $\mu^*\big(\bigcup_n A_n\big) \le \sum_n \mu^*(A_n)$ for each sequence of sets.

::: mathlib
`MeasureTheory.OuterMeasure` · `Mathlib.MeasureTheory.OuterMeasure.Defs`

A structure with `measureOf`, `empty`, `mono` and `iUnion_nat`, the last only for disjoint sequences; subadditivity follows, `measure_iUnion_le`. The class `OuterMeasureClass` covers `OuterMeasure` and `Measure`.

<?decl MeasureTheory.OuterMeasure?>
:::

**Definition (outer measure of a function).** Let $m : \mathcal{P}(X) \to [0, \infty]$ satisfy $m(\emptyset) = 0$. Put
$$\mu^*(A) = \inf \Big\{ \sum_n m(E_n) : A \subseteq \bigcup_n E_n \Big\}.$$
When $m$ is given only on a family $\mathcal{R}$ with $\emptyset \in \mathcal{R}$, extend it by $m(E) = \infty$ for $E \notin \mathcal{R}$. Then only covers by members of $\mathcal{R}$ count.

::: mathlib
`MeasureTheory.OuterMeasure.ofFunction` · `Mathlib.MeasureTheory.OuterMeasure.OfFunction`

`OuterMeasure.ofFunction m m_empty`, with the infimum over the sequences `f : ℕ → Set α` with `s ⊆ ⋃ i, f i`; the value is `ofFunction_apply`, true by `rfl`. The proposition below gives `ofFunction_le`: `ofFunction m m_empty s ≤ m s`.

<?decl MeasureTheory.OuterMeasure.ofFunction?>
<?decl MeasureTheory.OuterMeasure.ofFunction_apply?>
<?decl MeasureTheory.OuterMeasure.ofFunction_le?>
:::

::: mathlib
`MeasureTheory.inducedOuterMeasure` · `Mathlib.MeasureTheory.OuterMeasure.Induced`

For `m : ∀ s, P s → ℝ≥0∞`, it is `ofFunction (extend m)`, with the value `∞` outside `P`: the second form of the definition.

<?decl MeasureTheory.inducedOuterMeasure?>
:::

**Definition (Carathéodory measurable set).** Let $\mu^*$ be an outer measure on $X$. A set $A \subseteq X$ is *Carathéodory measurable* if
$$\mu^*(T) = \mu^*(T \cap A) + \mu^*(T \setminus A) \quad \text{for each } T \subseteq X.$$
The set $T$ is a test set. The inequality $\le$ always holds by subadditivity, so $A$ is Carathéodory measurable if and only if $\mu^*(T \cap A) + \mu^*(T \setminus A) \le \mu^*(T)$ for each $T$, and it suffices to check the $T$ with $\mu^*(T) < \infty$.

::: mathlib
`MeasureTheory.OuterMeasure.IsCaratheodory` · `Mathlib.MeasureTheory.OuterMeasure.Caratheodory`

`IsCaratheodory m s` is `∀ t, m t = m (t ∩ s) + m (t \ s)`.

<?decl MeasureTheory.OuterMeasure.IsCaratheodory?>
:::

### Theorems and proofs

**Proposition (the outer measure of a function).** Let $m : \mathcal{P}(X) \to [0, \infty]$ with $m(\emptyset) = 0$. Then $\mu^*$ is an outer measure, and $\mu^*(A) \le m(A)$ for each $A$.

*Proof.* The cover $A, \emptyset, \emptyset, \dots$ gives $\mu^*(A) \le m(A)$; with $A = \emptyset$ it gives $\mu^*(\emptyset) = 0$. If $A \subseteq B$, each cover of $B$ covers $A$, so $\mu^*(A) \le \mu^*(B)$. Let $(A_n)$ be a sequence and $\varepsilon > 0$. If $\sum_n \mu^*(A_n) = \infty$ there is nothing to prove. Otherwise choose for each $n$ a cover $(E_{n,k})_k$ of $A_n$ with $\sum_k m(E_{n,k}) \le \mu^*(A_n) + \varepsilon 2^{-n-1}$. The family $(E_{n,k})_{n,k}$ is countable and covers $\bigcup_n A_n$, so
$$\mu^*\Big(\bigcup_n A_n\Big) \le \sum_{n,k} m(E_{n,k}) \le \sum_n \mu^*(A_n) + \varepsilon.$$
Let $\varepsilon \to 0$. $\square$

**Theorem (Carathéodory).** Let $\mu^*$ be an outer measure on $X$, and let $\mathcal{M}$ be the family of its Carathéodory measurable sets. Then $\mathcal{M}$ is a σ-algebra, the restriction of $\mu^*$ to $\mathcal{M}$ is a measure, and each set $N$ with $\mu^*(N) = 0$ is in $\mathcal{M}$.

*Proof.* Step 1: null sets and complements. If $\mu^*(N) = 0$, then $\mu^*(T \cap N) + \mu^*(T \setminus N) \le 0 + \mu^*(T)$, so $N \in \mathcal{M}$. In particular $\emptyset \in \mathcal{M}$. The condition is symmetric in $A$ and $A^c$, since $T \setminus A = T \cap A^c$, so $\mathcal{M}$ is closed under complements.

Step 2: finite unions. Let $A, B \in \mathcal{M}$ and $T \subseteq X$. Test $A$ with $T$, then $B$ with $T \setminus A$:
$$\mu^*(T) = \mu^*(T \cap A) + \mu^*((T \setminus A) \cap B) + \mu^*(T \setminus (A \cup B)).$$
Since $T \cap (A \cup B) = (T \cap A) \cup ((T \setminus A) \cap B)$, subadditivity gives $\mu^*(T) \ge \mu^*(T \cap (A \cup B)) + \mu^*(T \setminus (A \cup B))$. So $A \cup B \in \mathcal{M}$, and $\mathcal{M}$ is an algebra of sets.

Step 3: disjoint sums. Let $A_1, \dots, A_n \in \mathcal{M}$ be pairwise disjoint and $S_n = A_1 \cup \dots \cup A_n$. It is claimed that $\mu^*(T \cap S_n) = \sum_{k \le n} \mu^*(T \cap A_k)$ for each $T$. For $n = 1$ this is clear. Test $A_n$ with $T \cap S_n$: since the sets are disjoint, $T \cap S_n \cap A_n = T \cap A_n$ and $T \cap S_n \setminus A_n = T \cap S_{n-1}$, so $\mu^*(T \cap S_n) = \mu^*(T \cap A_n) + \mu^*(T \cap S_{n-1})$, and induction gives the claim.

Step 4: countable disjoint unions. Let $(A_k)$ be pairwise disjoint in $\mathcal{M}$ and $S = \bigcup_k A_k$. By Step 2, $S_n \in \mathcal{M}$, and $T \setminus S_n \supseteq T \setminus S$. By Step 3 and monotonicity,
$$\mu^*(T) = \mu^*(T \cap S_n) + \mu^*(T \setminus S_n) \ge \sum_{k \le n} \mu^*(T \cap A_k) + \mu^*(T \setminus S).$$
Let $n \to \infty$, and use subadditivity:
$$\mu^*(T) \ge \sum_k \mu^*(T \cap A_k) + \mu^*(T \setminus S) \ge \mu^*(T \cap S) + \mu^*(T \setminus S).$$
So $S \in \mathcal{M}$. With $T = S$ the first inequality gives $\mu^*(S) \ge \sum_k \mu^*(A_k)$, and subadditivity gives the converse, so $\mu^*$ is countably additive on $\mathcal{M}$.

Step 5: countable unions. For any sequence $(A_k)$ in $\mathcal{M}$, the sets $B_k = A_k \setminus (A_0 \cup \dots \cup A_{k-1})$ are in the algebra $\mathcal{M}$, pairwise disjoint, with the same union. By Step 4 the union is in $\mathcal{M}$. $\square$

::: mathlib
`MeasureTheory.OuterMeasure.isCaratheodory_iff_le` · `Mathlib.MeasureTheory.OuterMeasure.Caratheodory`

`isCaratheodory_iff_le` reduces the condition to the one inequality `m (t ∩ s) + m (t \ s) ≤ m t`. Step 4 is `f_iUnion`: `m (⋃ i, s i) = ∑' i, m (s i)` for disjoint Carathéodory measurable sets. The theorem as a construction is `m.caratheodory : MeasurableSpace α`. Mathlib builds it from a Dynkin system closed under intersections, so it uses Chapter 1, Section 2 in place of Step 5.

<?decl MeasureTheory.OuterMeasure.isCaratheodory_iff_le?>
<?decl MeasureTheory.OuterMeasure.f_iUnion?>
<?decl MeasureTheory.OuterMeasure.caratheodory?>
:::

::: mathlib
`MeasureTheory.OuterMeasure.toMeasure` · `Mathlib.MeasureTheory.Measure.OuterMeasure`

`m.toMeasure h` is a measure for `h : ms ≤ m.caratheodory`. By `toMeasure_apply`, `m.toMeasure h s = m s` for a measurable `s`; on other sets the value is `m.trim s`.

<?decl MeasureTheory.OuterMeasure.toMeasure?>
<?decl MeasureTheory.toMeasure_apply?>
:::

**Theorem (extension of a premeasure).** Let $\mathcal{R}$ be a ring of sets on $X$ and let $m : \mathcal{R} \to [0, \infty]$ satisfy $m(\emptyset) = 0$ and $m\big(\bigcup_n E_n\big) = \sum_n m(E_n)$ for each pairwise disjoint sequence in $\mathcal{R}$ whose union is in $\mathcal{R}$. Let $\mu^*$ be the outer measure of $m$. Then $\mu^*(E) = m(E)$ for $E \in \mathcal{R}$, and each member of $\mathcal{R}$ is Carathéodory measurable. So $\mu^*$ restricted to $\sigma(\mathcal{R})$ is a measure that extends $m$.

*Proof.* First, $m$ is additive and monotone on $\mathcal{R}$: for $E \subseteq F$ in $\mathcal{R}$, $m(F) = m(E) + m(F \setminus E) \ge m(E)$.

Values. The proposition gives $\mu^*(E) \le m(E)$. Let $E \subseteq \bigcup_n E_n$ with $E_n \in \mathcal{R}$. The sets $B_n = E \cap E_n \setminus (E_0 \cup \dots \cup E_{n-1})$ are in $\mathcal{R}$, pairwise disjoint, with union $E$. So $m(E) = \sum_n m(B_n) \le \sum_n m(E_n)$. Take the infimum over the covers: $m(E) \le \mu^*(E)$.

Measurability. Let $A \in \mathcal{R}$ and $T \subseteq X$, and let $(E_n)$ be a cover of $T$ by members of $\mathcal{R}$. The sets $E_n \cap A$ cover $T \cap A$, and the sets $E_n \setminus A$ cover $T \setminus A$, and all are in $\mathcal{R}$. By additivity,
$$\sum_n m(E_n) = \sum_n m(E_n \cap A) + \sum_n m(E_n \setminus A) \ge \mu^*(T \cap A) + \mu^*(T \setminus A).$$
Take the infimum over the covers: $\mu^*(T) \ge \mu^*(T \cap A) + \mu^*(T \setminus A)$. Then $\mathcal{R} \subseteq \mathcal{M}$, so $\sigma(\mathcal{R}) \subseteq \mathcal{M}$, and Carathéodory's theorem ends the proof. $\square$

It is unique when $X$ is a countable union of members of $\mathcal{R}$ of finite measure; Section 3 proves this with the π-λ theorem.

::: mathlib
`MeasureTheory.OuterMeasure.ofFunction_caratheodory` · `Mathlib.MeasureTheory.OuterMeasure.Caratheodory`

The measurability step: if `m (t ∩ s) + m (t \ s) ≤ m t` for all `t`, with `m` the function itself, then `s` is measurable for `(ofFunction m h₀).caratheodory`. For the induced outer measure, `inducedOuterMeasure_caratheodory` tests only the sets `t` with `P`.

<?decl MeasureTheory.OuterMeasure.ofFunction_caratheodory?>
<?decl MeasureTheory.inducedOuterMeasure_caratheodory?>
:::

::: mathlib
`MeasureTheory.Measure.ofMeasurable` · `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`

The theorem for the ring of all measurable sets: a countably additive `m` on the measurable sets gives a `Measure`.

<?decl MeasureTheory.Measure.ofMeasurable?>
:::

::: mathlib
`MeasureTheory.OuterMeasure.trim` · `Mathlib.MeasureTheory.OuterMeasure.Induced`

`m.trim` is the outer measure induced by the values of `m` on measurable sets; `trim_eq` gives `m.trim s = m s` for a measurable `s`. The outer measure `μ.toOuterMeasure` of a measure is trimmed, and `le_toOuterMeasure_caratheodory` says that its Carathéodory σ-algebra contains the measurable sets.

<?decl MeasureTheory.OuterMeasure.trim?>
<?decl MeasureTheory.OuterMeasure.trim_eq?>
<?decl MeasureTheory.Measure.toOuterMeasure?>
<?decl MeasureTheory.le_toOuterMeasure_caratheodory?>
:::

### Examples

**Example (a two-valued outer measure).** On a set $X$ with at least two points let $\mu^*(\emptyset) = 0$ and $\mu^*(A) = 1$ for $A \ne \emptyset$. It is an outer measure. Let $A \ne \emptyset, X$. With $T = X$, $\mu^*(X \cap A) + \mu^*(X \setminus A) = 2 > 1 = \mu^*(X)$, so $A$ is not Carathéodory measurable. Thus $\mathcal{M} = \{\emptyset, X\}$. It is `boundedBy` of the constant $1$.

::: mathlib
`MeasureTheory.OuterMeasure.boundedBy` · `Mathlib.MeasureTheory.OuterMeasure.OfFunction`

`boundedBy m` is `ofFunction` of `m` with the value on `∅` set to $0$.

<?decl MeasureTheory.OuterMeasure.boundedBy?>
:::

**Counterexample (countable additivity on the ring is necessary).** Let $\mathcal{R}$ be the algebra of the finite and the cofinite subsets of $\mathbb{N}$, with $m(E) = 0$ for $E$ finite and $m(E) = 1$ for $E$ cofinite. Two cofinite sets meet, so $m$ is finitely additive. But $\mathbb{N} = \bigcup_n \{n\}$, and the cover by singletons gives $\mu^*(\mathbb{N}) \le \sum_n m(\{n\}) = 0 \ne 1 = m(\mathbb{N})$. So $\mu^*$ does not extend $m$, and no measure on $\sigma(\mathcal{R}) = \mathcal{P}(\mathbb{N})$ does.

### The library around it

The file `Mathlib.MeasureTheory.OuterMeasure.Operations` makes the outer measures on `α` a complete lattice and defines `map`, `comap` and `restrict`. The construction of Chapter 3 for the length of intervals goes through `MeasureTheory.AddContent`, a finitely additive function on a semiring of sets (Chapter 1, Section 2). From a countably subadditive content, `MeasureTheory.AddContent.measure` gives a measure.

Common errors of a learner:

- Confusing `OuterMeasure.trim` with `Measure.trim`. The second restricts to a smaller σ-algebra.
- Expecting `m.toMeasure h s = m s` for each set. It holds for measurable sets, and in general the value is `m.trim s`.

### Exercises

1. (A) Show that $\mu^*(A) = 0$ for $A$ countable and $\mu^*(A) = 1$ for $A$ uncountable is an outer measure on $\mathbb{R}$, and find its Carathéodory measurable sets.
2. (A) Show that the sum of two outer measures is an outer measure.
3. (A) Let $\mu^*$ be an outer measure and $A$ Carathéodory measurable. Show that $\mu^*(A \cup B) + \mu^*(A \cap B) = \mu^*(A) + \mu^*(B)$ for each $B$.
4. (B) Let $\mu$ be a measure on $(X, \Sigma)$ and $\mu^*(A) = \inf\{\mu(B) : B \in \Sigma, A \subseteq B\}$. Show that each Carathéodory measurable set of finite outer measure differs from a member of $\Sigma$ by a set of outer measure $0$.
5. (B) Show that in the theorem of Carathéodory, the restriction of $\mu^*$ to $\mathcal{M}$ is a complete measure: each subset of a null set of $\mathcal{M}$ is in $\mathcal{M}$.
6. (B) Find an outer measure $\mu^*$ on $\{1, 2, 3\}$ for which $\mathcal{M} = \{\emptyset, \{1\}, \{2, 3\}, X\}$. Hint: combine a Dirac mass at $1$ with the first example on $\{2, 3\}$.
7. (C) Let $\mathcal{R}$ be the ring of finite unions of intervals $(a, b]$ in $\mathbb{R}$ and $m$ the total length. Show that $m$ is countably additive on $\mathcal{R}$. Hint: use the compactness of $[a + \varepsilon, b]$.

### Notes and history

Carathéodory gave the definition of measurable sets by the test-set condition, and proved the theorem, in 1914. Before that, Lebesgue's thesis of 1902 had defined the measurable subsets of an interval by the equality of an outer and an inner measure. The Mathlib files `OuterMeasure.Caratheodory`, `OfFunction` and `Induced` have the authors Johannes Hölzl and Mario Carneiro.

### Reference

<?reference?>
