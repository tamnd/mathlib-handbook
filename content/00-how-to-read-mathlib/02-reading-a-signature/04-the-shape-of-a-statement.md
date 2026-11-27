---
title: The shape of a statement
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C01]
reads_with: ["MIL Ch. 3", "MIL Ch. 4"]
lean:
  - MathlibHandbook/V00/C02/Examples.lean
  - MathlibHandbook/V00/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The shape of a statement

### Overview

The earlier sections read the arguments of a declaration. This section reads what comes after the last colon: the statement. A statement of Mathlib uses a small number of forms. They are the arrow, the two quantifiers, the equivalence, the membership in a set, and the limit in the form of a filter. Each form has a fixed reading in the language of a textbook, and Mathlib writes each form in a fixed way. This section gives the readings, proves that the forms with filters say what a textbook says, and shows how the shape of a statement tells the reader how to use it.

### Arrows and quantifiers

**Definition (Reading of the forms).** The table gives the reading of each form of a proposition.

| Lean | Reading |
|---|---|
| `P → Q` | if $P$, then $Q$ |
| `P → Q → R` | if $P$ and $Q$, then $R$ |
| `∀ x, P x` | for all $x$, $P(x)$ |
| `∃ x, P x` | there is an $x$ with $P(x)$ |
| `P ↔ Q` | $P$ if and only if $Q$ |
| `¬ P` | not $P$, defined as `P → False` |
| `∀ x ∈ s, P x` | for all $x$ in $s$, $P(x)$ |
| `∃ x ∈ s, P x` | there is an $x$ in $s$ with $P(x)$ |
| `∀ ε > 0, P ε` | for all $\varepsilon > 0$, $P(\varepsilon)$ |

The arrow groups to the right, so `P → Q → R` is `P → (Q → R)`. Section 2.1 proved that this is the same as `P ∧ Q → R`. Mathlib prefers the form with two arrows, because each hypothesis is then a separate argument.

The bounded forms are abbreviations. The form `∀ x ∈ s, P x` is `∀ x, x ∈ s → P x`, and `∃ x ∈ s, P x` is `∃ x, x ∈ s ∧ P x`. The form `∀ ε > 0, P ε` is `∀ ε, ε > 0 → P ε`. So the bounded universal quantifier hides an arrow, and the bounded existential quantifier hides a conjunction. In a proof, `intro x hx` takes apart the first, and `obtain ⟨x, hx, h⟩ := ...` takes apart the second.

### Statements about sets

A set `s : Set α` is a predicate on `α`. The statement `x ∈ s` is a proposition. Mathlib states each operation on sets by a lemma on membership, with a name `Set.mem_` followed by the name of the operation. These lemmas have the attribute `simp`, so `simp` turns a statement on sets into a statement in logic.

::: mathlib
`Set.mem_image` · `Mathlib.Data.Set.Operations`

The image `f '' s` is the set $f(s)$. The lemma says that $y \in f(s)$ if and only if there is an $x \in s$ with $f(x) = y$. The right side is a bounded existential statement, so it hides a conjunction `x ∈ s ∧ f x = y`. The function and the set are explicit, so `Set.mem_image f s y` is the instance at given terms.

<?decl Set.mem_image?>
:::

::: mathlib
`Set.mem_preimage` · `Mathlib.Data.Set.Operations`

The preimage `f ⁻¹' s` is the set $f^{-1}(s)$. Here all arguments are implicit, because the statement shows them. The two sides are equal by definition, and the lemma is a tool for `rw` and `simp`.

<?decl Set.mem_preimage?>
:::

**Theorem (Image and preimage).** Let $f : \alpha \to \beta$, $s \subseteq \alpha$ and $t \subseteq \beta$. Then $f(s) \subseteq t$ if and only if $s \subseteq f^{-1}(t)$.

*Proof.* Suppose $f(s) \subseteq t$, and let $x \in s$. Then $f(x) \in f(s)$, with the witness $x$. So $f(x) \in t$, and that means $x \in f^{-1}(t)$. For the other direction, suppose $s \subseteq f^{-1}(t)$, and let $y \in f(s)$. There is an $x \in s$ with $f(x) = y$. Then $x \in f^{-1}(t)$, so $f(x) \in t$, and so $y \in t$. $\square$

::: mathlib
`Set.image_subset_iff` · `Mathlib.Data.Set.Image`

The statement is an equivalence, with all arguments implicit. Each side has the form `⊆`, which is `∀ x, x ∈ a → x ∈ b`. The attribute `simp` says that Mathlib prefers the right side: a statement on a preimage is easier to take apart than a statement on an image, because it has no existential quantifier.

<?decl Set.image_subset_iff?>
:::

### Equivalences and the direction of rewriting

An equivalence `P ↔ Q` is a lemma for rewriting. The tactic `rw [h]` replaces `P` by `Q` in the goal. So the order of the two sides is a choice, and Mathlib makes the same choice in each file: the left side is the more complex form, and the right side is the simpler form. The lemma `Nat.cast_le : ↑m ≤ ↑n ↔ m ≤ n` of Section 2.3 is an example: the casts are on the left.

An equivalence has two directions, `h.1 : P → Q` and `h.2 : Q → P`, also written `h.mp` and `h.mpr`. Section 2.1 used them.

### Inequalities in normal form

Mathlib states inequalities with `<` and `≤`, not with `>` and `≥`. The term `a > b` is notation for `b < a`, so the two are the same proposition. The rule is for the statements of lemmas: a lemma says `0 < a`, not `a > 0`. The exception is the bounded quantifier `∀ ε > 0`, which reads better in the order of a textbook. When the reader searches for a lemma, the search must use `<`: Chapter 4.

### Limits as filters

A textbook defines the limit of a sequence with $\varepsilon$ and $N$, the limit of a function at a point with $\varepsilon$ and $\delta$, and the limit at infinity with a third form. Mathlib has one definition for all these limits.

**Definition (Filter).** A *filter* on a set $X$ is a family $F$ of subsets of $X$ such that $X \in F$; if $A \in F$ and $A \subseteq B$, then $B \in F$; and if $A, B \in F$, then $A \cap B \in F$.

A filter is a notion of "large set". Two filters appear in most statements. The filter `Filter.atTop` on `ℕ` contains the sets that contain all $n \ge N$ for some $N$: the sets of "all large $n$". The filter `nhds a` on a metric space contains the sets that contain a ball around $a$: the neighbourhoods of $a$.

**Definition (Limit along filters).** Let $f : X \to Y$, $F$ a filter on $X$ and $G$ a filter on $Y$. Then $f$ *tends to* $G$ along $F$, written `Filter.Tendsto f F G`, if $f^{-1}(B) \in F$ for each $B \in G$.

So `Filter.Tendsto u atTop (nhds a)` says: for each neighbourhood $B$ of $a$, the set of $n$ with $u_n \in B$ contains all large $n$. That is the limit of a sequence.

**Theorem (Limits of sequences).** Let $(u_n)$ be a sequence in a metric space and $a$ a point. Then `Filter.Tendsto u atTop (nhds a)` holds if and only if for each $\varepsilon > 0$ there is an $N$ with $d(u_n, a) < \varepsilon$ for all $n \ge N$.

*Proof.* Suppose the limit along filters. Let $\varepsilon > 0$. The open ball $B(a, \varepsilon)$ contains a ball around $a$, so it is in `nhds a`. So the set $\{n : u_n \in B(a, \varepsilon)\}$ is in `atTop`, and it contains all $n \ge N$ for some $N$. For these $n$, $d(u_n, a) < \varepsilon$. For the other direction, suppose the condition with $\varepsilon$ and $N$. Let $B$ be in `nhds a`. Then $B$ contains a ball $B(a, \varepsilon)$ with $\varepsilon > 0$. Take $N$ for this $\varepsilon$. For $n \ge N$, $u_n \in B(a, \varepsilon) \subseteq B$. So the set $\{n : u_n \in B\}$ contains all $n \ge N$, and it is in `atTop`. $\square$

::: mathlib
`Metric.tendsto_atTop` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

This is the theorem above. The index type `β` is any nonempty type with a join `SemilatticeSup`, not only `ℕ`. The right side is the definition of a textbook, with `dist (u n) a` for $d(u_n, a)$. To prove a limit with $\varepsilon$ and $N$, rewrite the goal with this lemma and then use `intro ε hε`.

<?decl Metric.tendsto_atTop?>
:::

The advantage of filters is that one lemma covers all kinds of limits. The composition of limits is one lemma, `Filter.Tendsto.comp`, and it holds for sequences, for limits at a point, for limits at infinity and for one-sided limits.

::: mathlib
`Filter.Tendsto.comp` · `Mathlib.Order.Filter.Tendsto`

If $g$ tends to $z$ along $y$ and $f$ tends to $y$ along $x$, then $g \circ f$ tends to $z$ along $x$. The proof is one line from the definition: $(g \circ f)^{-1}(C) = f^{-1}(g^{-1}(C))$. The name starts with `Filter.Tendsto`, so dot notation applies: `hg.comp hf`.

<?decl Filter.Tendsto.comp?>
:::

**Example (The sequence 1/n).** Mathlib states the limit $1/n \to 0$ as follows.

::: mathlib
`tendsto_one_div_atTop_nhds_zero_nat` · `Mathlib.Analysis.SpecificLimits.Basic`

The sequence is `fun n ↦ 1 / ↑n`, with the cast of Section 2.3. The target type `𝕜` is any division semiring of characteristic zero with a topology in which the multiplication by nonnegative rationals is continuous. So the lemma holds in `ℝ`, `ℚ` and `ℂ`. For $n = 0$ the term is $1/0 = 0$, by the convention of Chapter 5. That changes no limit.

<?decl tendsto_one_div_atTop_nhds_zero_nat?>
:::

**Theorem (1/n tends to 0 in ℝ).** For each $\varepsilon > 0$ there is an $N$ with $|1/n| < \varepsilon$ for all $n \ge N$.

*Proof.* Let $\varepsilon > 0$. The reals are Archimedean, so there is a natural number $N$ with $1/\varepsilon < N$. Then $N > 0$. Let $n \ge N$. Then $n \ge N > 1/\varepsilon > 0$, so $1/n \le 1/N < \varepsilon$, and $|1/n| = 1/n$. $\square$

::: mathlib
`exists_nat_gt` · `Mathlib.Algebra.Order.Archimedean.Defs`

This is the Archimedean property used in the proof: for each $x$ there is a natural number $n$ with $x < \bar n$. The class `Archimedean` is the hypothesis, and `ℝ` and `ℚ` have it.

<?decl exists_nat_gt?>
:::

### Continuity

Mathlib defines continuity by open sets: `Continuous f` says that the preimage of each open set is open. It is a structure with one field, so the proof of continuity is a term `⟨h⟩`. On a metric space the definition with $\varepsilon$ and $\delta$ is a theorem.

::: mathlib
`Metric.continuous_iff` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

The right side has four quantifiers: `∀ b`, `∀ ε > 0`, `∃ δ > 0`, `∀ a`. They are the quantifiers of the textbook definition in the same order. The bounded form `∃ δ > 0` hides a conjunction, so a proof gives a pair: the number `δ` and a proof of `δ > 0`, then the rest.

<?decl Metric.continuous_iff?>
:::

**Example (Reading a statement of four quantifiers).** In `ℝ` the distance is `dist x y = |x - y|`, the lemma `Real.dist_eq`. So for $f : \mathbb{R} \to \mathbb{R}$ the right side of `Metric.continuous_iff` reads: for each $b$ and each $\varepsilon > 0$ there is a $\delta > 0$ such that $|a - b| < \delta$ implies $|f(a) - f(b)| < \varepsilon$. For $f(x) = 2x$, a proof takes $\delta = \varepsilon / 2$: then $|2a - 2b| = 2|a - b| < 2\delta = \varepsilon$.

### How the shape tells the use

The shape of a statement tells the reader which tactic uses it.

1. A statement `P → Q` or `∀ x, P x`: use `apply h` on a goal `Q`, or `h x` for an instance.
2. A statement `a = b` or `P ↔ Q`: use `rw [h]` or `simp [h]`.
3. A statement `∃ x, P x`: use `obtain ⟨x, hx⟩ := h` in a hypothesis.
4. A statement `P ∧ Q`: use `h.1` and `h.2`, or `obtain ⟨hp, hq⟩ := h`.
5. A goal `∃ x, P x`: use `refine ⟨t, ?_⟩` or `use t` with a witness `t`.

Chapter 3 shows these tactics in full proofs.

### Common errors

1. Reading `∃ x ∈ s, P x` as `∃ x, x ∈ s → P x`. That form is almost always true, since a term outside `s` is a witness. The right form has a conjunction.
2. Searching for `a > 0` in the names. Lemma names use `pos` and the statement uses `0 < a`.
3. Proving a limit by the definition with filters. Rewrite with `Metric.tendsto_atTop` first, or use a lemma on limits.
4. Reading `f '' s` as `f s`. The term `f s` applies `f` to the set, and it is a type error when `f : α → β`.

### Exercises

1. (A) Write the statement "each element of $s$ is at most $5$" with a bounded quantifier, and then without it.
2. (A) Write the negation of `∃ x ∈ s, P x` as a bounded universal statement, and prove the equivalence on paper.
3. (A) Let $f(x) = x^2$ on $\mathbb{R}$. Give $f(\{-1, 2\})$ and $f^{-1}(\{4\})$.
4. (B) Prove on paper that $f(f^{-1}(t)) \subseteq t$ for each $f$ and $t$. Find the lemma for this in `Mathlib.Data.Set.Image` and read its signature.
5. (B) Give the filter form of "$f(x) \to L$ as $x \to a$" for $f : \mathbb{R} \to \mathbb{R}$, and prove that it is the definition with $\varepsilon$ and $\delta$ in which the condition $0 < |x - a| < \delta$ is replaced by $|x - a| < \delta$. Which filter gives the form with $x \ne a$?
6. (B) Prove that $1/\sqrt{n} \to 0$ with $\varepsilon$ and $N$. Then write it as a composition of two limits along filters.
7. (C) Prove that a filter on $\mathbb{N}$ which contains each set with finite complement and does not contain $\emptyset$ contains no finite set. Then show that `atTop` on `ℕ` is the filter of sets with finite complement.

### Notes and history

Henri Cartan introduced filters in 1937 to unify the notions of limit in topology, and Bourbaki used them in the *General Topology*. Johannes Hölzl, Fabian Immler and Brian Huffman used filters for limits in Isabelle/HOL, and Mathlib took the same approach. Patrick Massot and Johannes Hölzl wrote much of the topology of Mathlib in this form.
