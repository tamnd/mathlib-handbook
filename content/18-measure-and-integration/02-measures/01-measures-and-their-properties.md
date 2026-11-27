---
title: Measures and their properties
kind: theory
modules:
  - Mathlib.MeasureTheory.Measure.MeasureSpaceDef
  - Mathlib.MeasureTheory.Measure.Basic
  - Mathlib.MeasureTheory.Measure.Continuity
  - Mathlib.MeasureTheory.Measure.Dirac.Def
  - Mathlib.MeasureTheory.Measure.Count
  - Mathlib.MeasureTheory.Measure.Typeclasses.Finite
  - Mathlib.MeasureTheory.Measure.Typeclasses.Probability
  - Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
  - Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
explains:
  E3: [MeasureTheory.Measure, MeasureTheory.measure_iUnion, MeasureTheory.tendsto_measure_iUnion_atTop, MeasureTheory.tendsto_measure_iInter_atTop, MeasureTheory.measure_limsup_atTop_eq_zero, MeasureTheory.Measure.dirac, MeasureTheory.Measure.count, MeasureTheory.IsFiniteMeasure, MeasureTheory.IsProbabilityMeasure, MeasureTheory.SigmaFinite]
  E2: [MeasureTheory.Measure.ext, MeasureTheory.measure_union, MeasureTheory.measure_mono, MeasureTheory.measure_iUnion_le, MeasureTheory.measure_sdiff, MeasureTheory.measure_union_add_inter, MeasureTheory.Measure.count_apply, MeasureTheory.SFinite]
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

## Measures and their properties

### Overview

A measure on a measurable space gives each measurable set a size in $[0, \infty]$, with the size of a countable disjoint union equal to the sum of the sizes. This section defines measures and derives their basic properties from countable additivity: monotonicity, subadditivity, and the two continuity properties along monotone sequences. The last theorem is the first Borel-Cantelli lemma.

### Definitions

The values of a measure are in the *extended nonnegative reals* $[0, \infty] = [0, \infty) \cup \{\infty\}$, the type `ℝ≥0∞` of Mathlib. Its rules are: $a + \infty = \infty$ for each $a$; $a \cdot \infty = \infty$ for $a > 0$ and $0 \cdot \infty = 0$; the subtraction is truncated, $a - b = 0$ for $a \le b$, and $\infty - \infty = 0$. It is a complete lattice, and each series converges to the supremum of its partial sums, in any order. Because of the truncation, the lemmas with a subtraction ask for a finite value.

**Definition (measure).** Let $(X, \Sigma)$ be a measurable space. A *measure* on $(X, \Sigma)$ is a map $\mu : \Sigma \to [0, \infty]$ with $\mu(\emptyset) = 0$ and
$$\mu\Big(\bigcup_n A_n\Big) = \sum_n \mu(A_n)$$
for each sequence $(A_n)$ of pairwise disjoint sets in $\Sigma$. The triple $(X, \Sigma, \mu)$ is a *measure space*.

::: mathlib
`MeasureTheory.Measure` · `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`

`Measure α` extends the structure `OuterMeasure α` of Section 2 with the field `m_iUnion`, countable additivity on measurable sets, and the field `trim_le`. So `μ s` is defined for each set `s`, measurable or not. The field `trim_le` makes `μ s` the infimum of `μ t` over the measurable `t ⊇ s`. The class `MeasureSpace α` gives a type a default measure, written `volume`.

<?decl MeasureTheory.Measure?>
:::

::: mathlib
`MeasureTheory.Measure.ext` · `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`

From `∀ s, MeasurableSet s → μ₁ s = μ₂ s` it gives `μ₁ = μ₂`. Section 3 needs agreement on a π-system only.

<?decl MeasureTheory.Measure.ext?>
:::

::: mathlib
`MeasureTheory.measure_iUnion` · `Mathlib.MeasureTheory.Measure.NullMeasurable`

Countable additivity for an index type with `[Countable ι]`, with the hypotheses `hn : Pairwise (Disjoint on f)` and `h : ∀ i, MeasurableSet (f i)`. The form `measure_iUnion₀` asks for null measurable sets that are disjoint up to null sets.

<?decl MeasureTheory.measure_iUnion?>
:::

**Definition (Dirac and counting measures).** Let $(X, \Sigma)$ be a measurable space. For $a \in X$, the *Dirac measure* $\delta_a$ is $\delta_a(A) = 1$ if $a \in A$ and $\delta_a(A) = 0$ otherwise. The *counting measure* is $\#(A)$, the number of elements of $A$ if $A$ is finite and $\infty$ otherwise.

Both are measures. For $\delta_a$: the point $a$ is in at most one of pairwise disjoint sets $A_n$, so both sides of countable additivity are $1$ if $a \in \bigcup_n A_n$ and $0$ otherwise. For $\#$: if the disjoint union is finite, each $A_n$ is finite, only finitely many are nonempty, and the sum counts each element once; if it is infinite, either some $A_n$ is infinite or infinitely many $A_n$ are nonempty, and both sides are $\infty$.

::: mathlib
`MeasureTheory.Measure.dirac` · `Mathlib.MeasureTheory.Measure.Dirac.Def`

`dirac a` is built from `OuterMeasure.dirac a`, which is $1$ on each set that contains `a`. On a measurable set, `dirac_apply'` gives the value `s.indicator 1 a`. With `[MeasurableSingletonClass α]`, `dirac_apply` gives it on each set.

<?decl MeasureTheory.Measure.dirac?>
:::

::: mathlib
`MeasureTheory.Measure.count` · `Mathlib.MeasureTheory.Measure.Count`

`count` is defined as `sum dirac`, the sum of the Dirac measures at all points. On a measurable set, `count_apply` gives `count s = s.encard`, and `count_apply_infinite` gives `∞` for an infinite set.

<?decl MeasureTheory.Measure.count?>
<?decl MeasureTheory.Measure.count_apply?>

<?decl MeasureTheory.Measure.count_apply?>
:::

**Definition (finite, probability, σ-finite and s-finite measures).** A measure $\mu$ on $X$ is *finite* if $\mu(X) < \infty$, and a *probability measure* if $\mu(X) = 1$. It is *σ-finite* if $X = \bigcup_n A_n$ for a sequence of measurable sets with $\mu(A_n) < \infty$. It is *s-finite* if $\mu = \sum_n \mu_n$ for a sequence of finite measures $\mu_n$.

A finite measure is σ-finite, and a σ-finite measure is s-finite: with $A_n$ as in the definition and $B_n = A_n \setminus (A_0 \cup \dots \cup A_{n-1})$, the measures $\mu_n(A) = \mu(A \cap B_n)$ are finite and have the sum $\mu$. The Lebesgue measure of Chapter 3 and the counting measure on $\mathbb{N}$ are σ-finite and not finite.

::: mathlib
`MeasureTheory.IsFiniteMeasure` · `Mathlib.MeasureTheory.Measure.Typeclasses.Finite`

A class with the field `measure_univ_lt_top : μ univ < ∞`. Then `measure_ne_top` gives `μ s ≠ ∞` for each set.

<?decl MeasureTheory.IsFiniteMeasure?>
:::

::: mathlib
`MeasureTheory.IsProbabilityMeasure` · `Mathlib.MeasureTheory.Measure.Typeclasses.Probability`

A class with the field `measure_univ : μ univ = 1`, and an instance to `IsFiniteMeasure`. The lemma `prob_compl_eq_one_sub` gives `μ sᶜ = 1 - μ s` for a measurable `s`.

<?decl MeasureTheory.IsProbabilityMeasure?>
:::

::: mathlib
`MeasureTheory.SigmaFinite` · `Mathlib.MeasureTheory.Measure.Typeclasses.SFinite`

A class with the field `out' : Nonempty (μ.FiniteSpanningSetsIn univ)`. The function `spanningSets μ` chooses a monotone measurable sequence of sets of finite measure with union `univ`.

<?decl MeasureTheory.SigmaFinite?>
:::

::: mathlib
`MeasureTheory.SFinite` · `Mathlib.MeasureTheory.Measure.Typeclasses.SFinite`

A class: `μ = Measure.sum m` for a sequence `m` of finite measures. There is an instance from `SigmaFinite`. Many theorems of Chapter 6 on products need only this class.

<?decl MeasureTheory.SFinite?>
:::

### Theorems and proofs

**Proposition (basic properties).** Let $\mu$ be a measure and let $A, B, A_n$ be measurable.

1. If $A \cap B = \emptyset$, then $\mu(A \cup B) = \mu(A) + \mu(B)$.
2. If $A \subseteq B$, then $\mu(A) \le \mu(B)$, and $\mu(B \setminus A) = \mu(B) - \mu(A)$ if $\mu(A) < \infty$.
3. $\mu(A \cup B) + \mu(A \cap B) = \mu(A) + \mu(B)$.
4. $\mu\big(\bigcup_n A_n\big) \le \sum_n \mu(A_n)$.

*Proof.* (1) Apply countable additivity to $A, B, \emptyset, \emptyset, \dots$. (2) $B$ is the disjoint union of $A$ and $B \setminus A$, so $\mu(B) = \mu(A) + \mu(B \setminus A) \ge \mu(A)$; if $\mu(A) < \infty$, subtract $\mu(A)$. (3) $A \cup B$ is the disjoint union of $A$ and $B \setminus A$, and $B$ is the disjoint union of $A \cap B$ and $B \setminus A$. So both sides equal $\mu(A) + \mu(A \cap B) + \mu(B \setminus A)$. (4) Put $B_n = A_n \setminus (A_0 \cup \dots \cup A_{n-1})$. The sets $B_n$ are measurable, pairwise disjoint, with $B_n \subseteq A_n$ and $\bigcup_n B_n = \bigcup_n A_n$, as in Chapter 1, Section 2. So $\mu\big(\bigcup_n A_n\big) = \sum_n \mu(B_n) \le \sum_n \mu(A_n)$ by (2). $\square$

::: mathlib
`MeasureTheory.measure_union` · `Mathlib.MeasureTheory.Measure.Basic`

Statement 1, with `hd : Disjoint s₁ s₂` and `h : MeasurableSet s₂`. Only one set must be measurable.

<?decl MeasureTheory.measure_union?>
:::

::: mathlib
`MeasureTheory.measure_mono` · `Mathlib.MeasureTheory.OuterMeasure.Basic`

`s ⊆ t → μ s ≤ μ t`, and statement 4, `μ (⋃ i, s i) ≤ ∑' i, μ (s i)`, hold for arbitrary sets and each outer measure, so they are stated for the class `OuterMeasureClass`.

<?decl MeasureTheory.measure_mono?>
<?decl MeasureTheory.measure_iUnion_le?>
:::

::: mathlib
`MeasureTheory.measure_sdiff` · `Mathlib.MeasureTheory.Measure.Basic`

Statement 2: `μ (s₁ \ s₂) = μ s₁ - μ s₂` from `s₂ ⊆ s₁`, `NullMeasurableSet s₂ μ` and `μ s₂ ≠ ∞`. Statement 3 is `measure_union_add_inter`, for a measurable `t`; it has no subtraction, so it needs no finiteness.

<?decl MeasureTheory.measure_sdiff?>
<?decl MeasureTheory.measure_union_add_inter?>
:::

**Theorem (continuity from below).** Let $A_0 \subseteq A_1 \subseteq \dots$ be measurable. Then $\mu\big(\bigcup_n A_n\big) = \lim_n \mu(A_n) = \sup_n \mu(A_n)$.

*Proof.* Put $B_0 = A_0$ and $B_n = A_n \setminus A_{n-1}$ for $n \ge 1$. The sets $B_n$ are measurable and pairwise disjoint, $A_n = B_0 \cup \dots \cup B_n$, and $\bigcup_n B_n = \bigcup_n A_n$. So
$$\mu\Big(\bigcup_n A_n\Big) = \sum_n \mu(B_n) = \sup_n \sum_{k \le n} \mu(B_k) = \sup_n \mu(A_n).$$
The sequence $\mu(A_n)$ increases, so its supremum is its limit. $\square$

**Theorem (continuity from above).** Let $A_0 \supseteq A_1 \supseteq \dots$ be measurable with $\mu(A_0) < \infty$. Then $\mu\big(\bigcap_n A_n\big) = \lim_n \mu(A_n) = \inf_n \mu(A_n)$.

*Proof.* The sets $A_0 \setminus A_n$ increase, with union $A_0 \setminus \bigcap_n A_n$. By continuity from below and statement 2, with the finite values $\mu(A_n) \le \mu(A_0)$,
$$\mu(A_0) - \mu\Big(\bigcap_n A_n\Big) = \lim_n \big(\mu(A_0) - \mu(A_n)\big) = \mu(A_0) - \lim_n \mu(A_n).$$
All terms are finite, so $\mu\big(\bigcap_n A_n\big) = \lim_n \mu(A_n)$. $\square$

::: mathlib
`MeasureTheory.tendsto_measure_iUnion_atTop` · `Mathlib.MeasureTheory.Measure.Continuity`

Continuity from below as a limit: for `hm : Monotone s`, `Tendsto (μ ∘ s) atTop (𝓝 (μ (⋃ n, s n)))`. `Monotone.measure_iUnion` gives the supremum. There is no measurability hypothesis: Mathlib replaces each `s n` by a measurable hull `toMeasurable μ (s n)` of the same measure.

<?decl MeasureTheory.tendsto_measure_iUnion_atTop?>
:::

::: mathlib
`MeasureTheory.tendsto_measure_iInter_atTop` · `Mathlib.MeasureTheory.Measure.Continuity`

Continuity from above, with `hs : ∀ i, NullMeasurableSet (s i) μ`, `hm : Antitone s` and `hf : ∃ i, μ (s i) ≠ ∞`. Here the measurability hypothesis is needed: measurable hulls are too large for an intersection. The form `Antitone.measure_iInter` gives the infimum.

<?decl MeasureTheory.tendsto_measure_iInter_atTop?>
:::

**Theorem (first Borel-Cantelli lemma).** Let $(A_n)$ be measurable sets with $\sum_n \mu(A_n) < \infty$. Then the set $\limsup_n A_n = \bigcap_N \bigcup_{n \ge N} A_n$ of the points that are in infinitely many $A_n$ has measure $0$.

*Proof.* For each $N$, $\limsup_n A_n \subseteq \bigcup_{n \ge N} A_n$, so by monotonicity and subadditivity $\mu(\limsup_n A_n) \le \sum_{n \ge N} \mu(A_n)$. The series converges to a finite value, so its tails tend to $0$ (Volume 15, Chapter 1). Thus $\mu(\limsup_n A_n) = 0$. $\square$

The proof uses only monotonicity and subadditivity, so it holds for outer measures too.

::: mathlib
`MeasureTheory.measure_limsup_atTop_eq_zero` · `Mathlib.MeasureTheory.OuterMeasure.BorelCantelli`

For `s : ℕ → Set α` and `hs : ∑' i, μ (s i) ≠ ∞`, `μ (limsup s atTop) = 0`. Here `limsup s atTop` is the filter `limsup` in `Set α`, the set of the theorem. The form `measure_limsup_cofinite_eq_zero` allows any index type.

<?decl MeasureTheory.measure_limsup_atTop_eq_zero?>
:::

### Examples

**Example (Dirac and counting measures).** On $\mathbb{N}$ with all sets measurable, $\delta_3(\{1, 2, 3\}) = 1$, $\delta_3(2\mathbb{N}) = 0$, $\#(\{1, 2, 3\}) = 3$ and $\#(2\mathbb{N}) = \infty$. The measure $\mu = \sum_n 2^{-n-1} \delta_n$ is a probability measure, with $\mu(2\mathbb{N}) = \sum_k 2^{-2k-1} = \tfrac12 \cdot \tfrac{1}{1 - 1/4} = \tfrac23$.

**Counterexample (continuity from above needs a finite value).** On $\mathbb{N}$ let $A_n = \{n, n + 1, n + 2, \dots\}$. The sets decrease, and $\bigcap_n A_n = \emptyset$. But $\#(A_n) = \infty$ for each $n$, so $\lim_n \#(A_n) = \infty \ne 0 = \#\big(\bigcap_n A_n\big)$. For the finite $\mu$ of the previous example, $\mu(A_n) = 2^{-n} \to 0$.

### The library around it

Most lemmas on measures have the prefix `measure_` and are in the namespace `MeasureTheory`: `measure_empty`, `measure_union_le`, `measure_compl`, `measure_biUnion_finset`, `measure_iUnion_null` (a countable union of null sets is null) and `measure_mono_null`.

Common errors of a learner:

- Writing `μ (s \ t) = μ s - μ t` without the hypotheses of `measure_sdiff`. With `μ t = ∞` the right side is `0` by truncation.
- Expecting `μ s = 0` to fail for a set that is not measurable. A measure has a value on each set.
- Applying continuity from above to the counting measure on infinite sets.

### Exercises

1. (A) Show that a finite sum $\sum_{i=1}^n c_i \delta_{a_i}$ with $c_i \ge 0$ is a measure.
2. (A) Let $\mu$ be a probability measure and $A, B$ measurable. Show that $\mu(A \cap B) \ge \mu(A) + \mu(B) - 1$.
3. (A) Let $\mu$ be a measure and $A$ measurable. Show that $\nu(B) = \mu(A \cap B)$ is a measure.
4. (B) Prove the inclusion-exclusion formula for three sets of finite measure. Hint: apply statement 3 twice.
5. (B) Let $\mu$ be a finite measure on $\mathbb{R}$ with the Borel sets. Show that the set of the $x$ with $\mu(\{x\}) > 0$ is countable. Hint: for each $k$ only finitely many $x$ have $\mu(\{x\}) > 1/k$.
6. (B) Let $F(t) = \mu((-\infty, t])$ for a finite measure $\mu$ on $\mathbb{R}$. Show that $F$ is increasing and right continuous. Hint: continuity from above.
7. (C) Let $\mu \ne 0$ be a σ-finite measure. Show that there is a probability measure $\nu$ with the same null sets as $\mu$. Show with a one-point space that the converse fails. Hint: $\nu(A) = c \sum_n 2^{-n} \mu(A \cap B_n) / (1 + \mu(B_n))$ for disjoint $B_n$ of finite measure that cover $X$.

### Notes and history

Lebesgue's thesis of 1902 constructed the countably additive measure of length on the line. The lemma of Borel and Cantelli carries the names of Émile Borel and Francesco Paolo Cantelli. The Mathlib files `Measure.MeasureSpaceDef` and `Measure.Basic` have the authors Johannes Hölzl and Mario Carneiro, and `OuterMeasure.BorelCantelli` has the authors Markus Himmel and Yury Kudryashov.

### Reference

<?reference?>
