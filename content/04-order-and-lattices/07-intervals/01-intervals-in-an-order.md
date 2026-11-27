---
title: Intervals in an order
kind: theory
modules:
  - Mathlib.Order.Interval.Set.Defs
  - Mathlib.Order.Interval.Set.Basic
explains:
  E3: [Set.Icc]
  E2: [Set.mem_Icc, Set.Icc_subset_Icc, Set.nonempty_Icc, Set.Icc_eq_empty, Set.Ico, Set.Ioo]
  E1: [Set.Ici, Set.Iic, Set.Ioi, Set.mem_Ioo, Set.mem_Ico, Set.mem_Ici, Set.Icc_self, Set.Ioo_subset_Icc_self, Set.Icc_subset_Icc_iff, Set.left_mem_Icc, Set.right_mem_Icc, Set.Ico_union_Ico_eq_Ico, Set.uIcc, Finset.Icc]
families: []
requires: [V04.C01, V01.C02]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C07/Examples.lean
  - MathlibHandbook/V04/C07/Exercises.lean
  - MathlibHandbook/V04/C07/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Intervals in an order

### Overview

An interval is a set of the elements between two bounds. Mathlib defines the intervals for each preorder, not only for `ℝ`. The names have a code of two letters after `I`. The first letter is for the left end and the second letter is for the right end. The letter `c` means closed, so the end is in the interval. The letter `o` means open, so the end is not in the interval. The letter `i` means infinite, so there is no bound on that side. So `Set.Icc a b` is $[a, b]$, `Set.Ico a b` is $[a, b)$ and `Set.Ioi a` is $(a, \infty)$. This section shows the eight intervals, how to prove a membership, and the main lemmas.

### Definitions

**Definition (Bounded intervals).** For $a$ and $b$ in a preorder:

- `Set.Icc a b` is $\{x \mid a \le x \land x \le b\}$.
- `Set.Ico a b` is $\{x \mid a \le x \land x < b\}$.
- `Set.Ioc a b` is $\{x \mid a < x \land x \le b\}$.
- `Set.Ioo a b` is $\{x \mid a < x \land x < b\}$.

**Definition (Unbounded intervals).** `Set.Ici a` is $\{x \mid a \le x\}$ and `Set.Ioi a` is $\{x \mid a < x\}$. `Set.Iic b` and `Set.Iio b` are the duals. In each name, the letter `i` stands for the side with no bound.

**Definition (Unordered interval).** In a lattice, `Set.uIcc a b` is `Set.Icc (a ⊓ b) (a ⊔ b)`. It does not depend on the order of $a$ and $b$, and it has the notation `[[a, b]]` in the scope `Interval`.

### Theorems and proofs

**Theorem (Inclusion).** If $a_2 \le a_1$ and $b_1 \le b_2$, then $[a_1, b_1] \subseteq [a_2, b_2]$.

*Proof.* Let $x \in [a_1, b_1]$. Then $a_2 \le a_1 \le x$ and $x \le b_1 \le b_2$, so $x \in [a_2, b_2]$. $\square$

**Theorem (Nonempty interval).** The interval $[a, b]$ is nonempty if and only if $a \le b$.

*Proof.* If $a \le b$, then $a \in [a, b]$. Conversely, if $x \in [a, b]$, then $a \le x \le b$, so $a \le b$ by transitivity. $\square$

**Theorem (Empty interval).** In a linear order, if $b < a$, then $[a, b] = \emptyset$.

*Proof.* If $x \in [a, b]$, then $a \le b$ by the previous theorem. This contradicts $b < a$. $\square$

**Theorem (Union).** In a linear order, if $a \le b \le c$, then $[a, b) \cup [b, c) = [a, c)$.

*Proof.* An element of $[a, b)$ or of $[b, c)$ is in $[a, c)$ because $b \le c$ and $a \le b$. Conversely, let $x \in [a, c)$. By totality, $x < b$ or $b \le x$. In the first case $x \in [a, b)$, and in the second case $x \in [b, c)$. $\square$

::: mathlib
`Set.Icc` · `Mathlib.Order.Interval.Set.Defs`

The definition is `{x | a ≤ x ∧ x ≤ b}`. The lemma `Set.mem_Icc` is a `simp` lemma, so `simp` turns a membership into two inequalities. Each interval has the same kind of lemma, for example `Set.mem_Ioo` and `Set.mem_Ici`.

<?decl Set.Icc?>
:::

::: mathlib
`Set.Icc_subset_Icc` · `Mathlib.Order.Interval.Set.Basic`

The lemma takes the two inequalities of the ends. The lemma `Set.Icc_subset_Icc_iff` gives the equivalence for a nonempty interval.

<?decl Set.Icc_subset_Icc?>
:::

::: mathlib
`Set.Icc_eq_empty` · `Mathlib.Order.Interval.Set.Basic`

The hypothesis is `¬a ≤ b`, so it applies in a preorder. In a linear order, `not_le.mpr` gives the hypothesis from `b < a`. The lemma `Set.nonempty_Icc` states the equivalence of the theorem above.

<?decl Set.Icc_eq_empty?>
:::

### Examples

**Example (Membership).**

<?lean MathlibHandbook/V04/C07/Examples.lean#mem?>

**Example (A number in an open interval).** The tactic `norm_num` unfolds the membership and proves the inequalities.

<?lean MathlibHandbook/V04/C07/Examples.lean#half?>

**Example (Inclusion).**

<?lean MathlibHandbook/V04/C07/Examples.lean#subset?>

**Example (An empty interval).**

<?lean MathlibHandbook/V04/C07/Examples.lean#empty?>

**Example (A singleton).**

<?lean MathlibHandbook/V04/C07/Examples.lean#self?>

**Example (Union).**

<?lean MathlibHandbook/V04/C07/Examples.lean#union?>

**Example (A finite interval).** On a locally finite order such as `ℕ`, `Finset.Icc` is the interval as a finite set, and `decide` computes it.

<?lean MathlibHandbook/V04/C07/Examples.lean#finset?>

**Counterexample (The ends in the wrong order).** The statement `Set.Icc a b = Set.Icc b a` is false. On `ℝ`, `Set.Icc 0 1` contains $\frac{1}{2}$, and `Set.Icc 1 0` is empty. Use `Set.uIcc` when the order of the ends is not known.

### The library around it

The file `Mathlib.Order.Interval.Set.Basic` has the lemmas for a preorder and a partial order, and `Mathlib.Order.Interval.Set.LinearOrder` has the lemmas that need a linear order, such as `Set.Ico_union_Ico_eq_Ico`. The intervals of `Finset` start in `Mathlib.Order.Interval.Finset.Defs`, and they need the class `LocallyFiniteOrder`. The lemmas on the arithmetic of intervals, such as `Set.sub_mem_Icc_iff_left`, are in `Mathlib.Algebra.Order.Interval.Set.Group`, and the images of an interval under a shift by a constant are in `Mathlib.Algebra.Order.Interval.Set.Monoid`. In analysis, `Set.Icc a b` is the domain of an integral and of a continuous function on a compact interval. The tactic `simp` with `Set.mem_Icc` and the tactic `linarith` prove most goals of membership.

### Exercises

1. (A) Write $(0, 1]$ and $[2, \infty)$ with the names of Mathlib.
2. (A) Give the elements of `Finset.Ico 2 6` in `ℕ`.
3. (B) Show that `Set.Ioo a b ⊆ Set.Ico a b`.
4. (B) Show that `Set.Ici a ∩ Set.Iic b = Set.Icc a b`.
5. (B) Show that `Set.Ioo a b` is empty when $b \le a$.
6. (L) Prove that $3 \in [1, 5]$ in `ℝ`. The solution is `mem_Icc_example`.
7. (L) Prove that `Set.Ioo a b ⊆ Set.Icc a b`. The solution is `Ioo_subset_Icc_example`.
8. (L) Prove that $[0, 1]$ is nonempty in `ℝ`. The solution is `nonempty_Icc_example`.

### Notes and history

The notation $[a, b]$ for a closed interval became common in the twentieth century, but the notations for half-open intervals differ between books, for example $[a, b[$ in French texts. The names of Mathlib avoid the question, because they are plain identifiers with no brackets.

### Reference

<?reference?>
