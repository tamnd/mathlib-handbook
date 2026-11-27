---
title: Reading a tactic proof
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C02]
reads_with: ["MIL Ch. 2", "MIL Ch. 3", "TPIL"]
lean:
  - MathlibHandbook/V00/C03/Examples.lean
  - MathlibHandbook/V00/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Reading a tactic proof

### Overview

Most proofs in Mathlib are tactic proofs. A tactic proof is hard to read on paper, because the text shows the steps but not the state between the steps. In an editor the infoview shows the state. This section explains the state, the *goal*, gives the common tactics with their effect on the goal, and reads two proofs step by step with the goal after each step. The reader can then read a tactic proof with or without the editor, and translate it into a proof of a textbook.

### The goal

**Definition (Goal).** A *goal* is a list of hypotheses, each a name with a type, and a target, a type after the sign `⊢`. To close a goal is to give a term of the target type, with the hypotheses as free variables.

A tactic proof starts with one goal: the hypotheses of the theorem and its statement. Each tactic changes the list of goals. Some tactics close a goal, some replace it by a new goal, and some split it into several goals. The proof is complete when no goal is left.

**Example (The first goal).** For the theorem `and_swap_tactic` of Section 3.1, the first goal is

```text
p q : Prop
⊢ p ∧ q → q ∧ p
```

The two hypotheses are the propositions `p` and `q`. The target is an implication.

### The common tactics

The table lists the tactics that appear in most proofs, with their reading in a proof of a textbook.

| Tactic | Effect on the goal | Reading |
|---|---|---|
| `intro h` | target `P → Q` becomes `Q`, with `h : P` | suppose $P$ |
| `intro x` | target `∀ x, P x` becomes `P x` | let $x$ be given |
| `exact t` | closes the goal with the term `t` | this is `t` |
| `apply h` | with `h : P → Q`, target `Q` becomes `P` | by `h`, it is enough to prove $P$ |
| `refine ⟨t, ?_⟩` | target `∃ x, P x` becomes `P t` | take $x = t$ |
| `use t` | the same, and tries to close the rest | take $x = t$ |
| `obtain ⟨x, hx⟩ := h` | splits `h : ∃ x, P x` or `h : P ∧ Q` | choose $x$ with $P(x)$ |
| `constructor` | target `P ∧ Q` becomes two goals `P` and `Q` | prove each part |
| `rw [h]` | rewrites with `h : a = b` | substitute $b$ for $a$ |
| `simp` | rewrites with the lemmas marked `simp` | simplify |
| `ring` | closes an identity of commutative rings | expand both sides |
| `linarith` | closes a linear inequality from hypotheses | add the hypotheses |
| `norm_num` | closes an arithmetic statement on numerals | compute |
| `positivity` | closes `0 < e` or `0 ≤ e` | each part is positive |
| `omega` | closes a linear statement on `ℕ` and `ℤ` | arithmetic on integers |
| `induction n with ...` | splits into base case and step | by induction on $n$ |
| `by_contra h` | target `P` becomes `False`, with `h : ¬ P` | suppose not |
| `exact?` | searches for a lemma that closes the goal | |

The tactic `rcases` splits a hypothesis `h : P ∨ Q` into two goals, one with `P` and one with `Q`: the two cases of a paper proof. The first group of tactics builds the term of the proof piece by piece: `intro` makes a `fun`, `exact` gives a term, `refine` gives a term with holes. The second group, from `rw` on, calls a procedure that finds the term. The procedures are the reason a tactic proof is short.

### Reading the swap proof

**Example (The goals of a short proof).** The proof `and_swap_tactic` has three tactics.

<?lean MathlibHandbook/V00/C03/Examples.lean#and_swap_tactic?>

After `intro h` the goal is

```text
p q : Prop
h : p ∧ q
⊢ q ∧ p
```

After `obtain ⟨hp, hq⟩ := h` the hypothesis `h` is gone, and two hypotheses are in its place:

```text
p q : Prop
hp : p
hq : q
⊢ q ∧ p
```

The tactic `exact ⟨hq, hp⟩` closes the goal, and the infoview shows `No goals`. On paper: suppose $p \wedge q$. Then $p$ and $q$. So $q \wedge p$.

### Reading a calculation

**Example (The goals of a calc proof).** The proof `calc_proof` of Section 3.1 is a term, not a tactic proof, but each step has its own goal.

<?lean MathlibHandbook/V00/C03/Examples.lean#calc_proof?>

The first step `a ≤ b := hab` asks for a proof of `a ≤ b`, and the hypothesis `hab` is one. The second step `_ < c := hbc` asks for `b < c`, where `_` is the right side of the step before. The last step asks for `c < c + 1`, and the core lemma `Nat.lt_succ_self c` is a proof. Lean then checks that the chain gives the target `a < c + 1`.

### An induction

The next proof is a classical identity. It is not in the companion package, and the text below shows it as it appears in an editor.

**Theorem (Sum of odd numbers).** For each $n \in \mathbb{N}$, $\sum_{i=0}^{n-1} (2i + 1) = n^2$.

*Proof.* By induction on $n$. For $n = 0$ the sum is empty, so it is $0 = 0^2$. Suppose $\sum_{i=0}^{n-1}(2i+1) = n^2$. Then
$$\sum_{i=0}^{n}(2i+1) = \sum_{i=0}^{n-1}(2i+1) + (2n+1) = n^2 + 2n + 1 = (n+1)^2.$$
The first step splits off the last term, the second is the hypothesis of the induction, and the third is the square of a sum. $\square$

In Lean, with `open Finset`, the statement and its proof read as follows.

```lean
theorem sum_odd (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring
```

The first goal is

```text
n : ℕ
⊢ ∑ i ∈ range n, (2 * i + 1) = n ^ 2
```

The tactic `induction n with` splits it into two goals, one for each case of the definition of `ℕ`. The case `zero` has the goal

```text
⊢ ∑ i ∈ range 0, (2 * i + 1) = 0 ^ 2
```

and `simp` closes it with the lemmas `Finset.range_zero`, `Finset.sum_empty` and the computation $0^2 = 0$. The case `succ` has the goal

```text
n : ℕ
ih : ∑ i ∈ range n, (2 * i + 1) = n ^ 2
⊢ ∑ i ∈ range (n + 1), (2 * i + 1) = (n + 1) ^ 2
```

The name `ih` is the hypothesis of the induction, and the name `n` is reused for the new variable. The rewrite with `sum_range_succ` splits off the last term, and the rewrite with `ih` replaces the sum by `n ^ 2`. The goal is then

```text
n : ℕ
ih : ∑ i ∈ range n, (2 * i + 1) = n ^ 2
⊢ n ^ 2 + (2 * n + 1) = (n + 1) ^ 2
```

and `ring` closes it. Each line of the Lean proof is a sentence of the paper proof.

::: mathlib
`Finset.sum_range_succ` · `Mathlib.Algebra.BigOperators.Group.Finset.Basic`

The sum over $\{0, \dots, n\}$ is the sum over $\{0, \dots, n-1\}$ plus the last term. The function `f` and the number `n` are explicit, but `rw` finds them from the goal. The lemma is the first step of most proofs by induction on a sum. The product version is `Finset.prod_range_succ`. Mathlib states the product lemma, and the attribute `to_additive` makes the sum lemma from it, Chapter 4.

<?decl Finset.sum_range_succ?>
:::

### Tactics that hide the step

A procedure as `simp`, `ring` or `linarith` closes a goal with no trace of the steps. To see what it did, use these tools.

1. `simp?` closes the goal as `simp` does and prints the call `simp only [...]` with the list of lemmas it used.
2. `show t` states the goal in a given form. It fails if `t` is not the goal up to definitions. It is a check for the reader.
3. `have h : t := by ...` proves an intermediate statement, as a sentence "first, $t$" of a paper proof.
4. The cursor in the editor, put after a tactic, shows the goal at that point.

**Example (A procedure and its trace).** For the goal `⊢ ∑ i ∈ range 0, (2 * i + 1) = 0 ^ 2`, the call `simp?` prints a line of the form `simp only [range_zero, sum_empty, ...]`. The list depends on the version of Mathlib. The proof with `simp only` and the list is more stable than `simp`, because a new lemma marked `simp` cannot change it. Mathlib asks for `simp only` in each place that is not the last step of a goal.

### Structure of a long proof

A long proof of Mathlib uses `have` for each lemma of the paper proof, and bullets `·` for the goals after a split.

```lean
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b + a := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < a * b + a := add_pos h1 ha
  exact h2
```

The first goal has the hypotheses `ha` and `hb`. After the first `have`, the goal has a new hypothesis `h1 : 0 < a * b`. After the second, it has `h2`. The last line closes the goal. On paper: first $ab > 0$, since $a, b > 0$. Then $ab + a > 0$, as a sum of two positive numbers. The lemmas `mul_pos` and `add_pos` are those of Section 2.2. The tactic `positivity` proves the whole statement in one step.

### Common errors

1. Reading a tactic proof with no goal view. The text `rw [h]` does not say which goal it changes. Open the file in an editor, or rebuild the goals by hand from the table above.
2. Expecting `simp` to close a goal it only changes. If `simp` does not close the goal, the next tactic sees the simplified goal, and that goal can be hard to predict. Use `simp?` to see it.
3. Writing `rw [h]` with `h : a = b` when the goal has `b`, not `a`. The tactic rewrites from left to right. Use `rw [← h]` for the other direction.
4. Losing track of the goals after a split. Each bullet `·` works on one goal, and an error message says which goal is open.

### Exercises

1. (A) Write the goal after `intro x hx` for the target `∀ x : ℝ, 0 < x → 0 < x ^ 2`.
2. (A) Translate the tactic proof `intro h; exact h.1` into a sentence of a textbook and into a term.
3. (B) Write the goals after each step of `constructor; · exact hq; · exact hp` for the goal `hp : p, hq : q ⊢ q ∧ p`.
4. (B) Give a paper proof and a tactic proof of $\sum_{i=0}^{n-1} i^3 = \left(\sum_{i=0}^{n-1} i\right)^2$, with the goal after each step. Hint: prove $4 \sum_{i<n} i^3 = n^2 (n-1)^2$ first, by induction.
5. (B) Rewrite the proof of `sum_odd` with `calc` in the case `succ`, with one step for each equation of the paper proof.
6. (C) The statement `∀ n : ℕ, 2 ∣ n * (n + 1)` has a proof by induction and a proof by cases on the parity of $n$. Write the goals of each proof, and say which tactic closes each final goal.

### Notes and history

Tactics come from the LCF system of Robin Milner and his group at Edinburgh in the 1970s, where a tactic was a program that reduces a goal to subgoals. The goal view of Lean 4 is the infoview of the extension for VS Code, written by Wojciech Nawrocki, Edward Ayers and others. The style rules of Mathlib, as the use of `simp only` inside a proof, are in the contribution guide of the project.
