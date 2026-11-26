---
title: Names and search
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C02]
reads_with: ["MSG", "MIL Ch. 2"]
lean:
  - MathlibHandbook/V00/C04/Examples.lean
  - MathlibHandbook/V00/C04/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Names and search

### Overview

Mathlib has more than 250,000 theorems, and a user cannot remember their names. The names follow a convention, so the user can often guess the name from the statement. When the guess fails, search tools find the lemma from its statement. This section shows the convention and the tools.

### The naming convention

The name of a lemma reads its statement. The rules are in the style guide of Mathlib. The main rules are these.

1. Each symbol has a word: `mul` for `*`, `add` for `+`, `sub` for `-`, `div` for `/`, `neg` for unary `-`, `inv` for `⁻¹`, `pow` for `^`, `le` for `≤`, `lt` for `<`, `eq` for `=`, `ne` for `≠`, `zero` for `0`, `one` for `1`.
2. The words `pos` for `0 < x`, `nonneg` for `0 ≤ x`, `neg` for `x < 0` and `nonpos` for `x ≤ 0` name the sign of a term.
3. The name reads the conclusion first. The hypotheses come after the word `of`.
4. An equivalence has `iff` in the name. A lemma about one type is in the namespace of the type, as `Nat.` or `Finset.`.
5. A name ends with `'` when it is a variant of the name without the mark.

**Example (A name that reads the left side).** The statement of `two_mul` is `2 * a = a + a`. The name reads `2 * a` as `two_mul`.

<?lean MathlibHandbook/V00/C04/Examples.lean#two_mul?>

**Example (A name that reads the conclusion).** The conclusion of `add_pos` is that a sum is positive.

<?lean MathlibHandbook/V00/C04/Examples.lean#add_pos?>

**Example (A hypothesis in the name).** The name `mul_le_mul_of_nonneg_left` reads the conclusion `a * b ≤ a * c`, then the hypothesis `0 ≤ a` after `of`, and `left` says that `a` is on the left.

<?lean MathlibHandbook/V00/C04/Examples.lean#mul_le_mul_of_nonneg_left?>

**Example (A namespace).** A lemma about finite sums is in the namespace `Finset`. The command `open Finset` lets the proof write `sum_range_succ` and not `Finset.sum_range_succ`.

<?lean MathlibHandbook/V00/C04/Examples.lean#sum_range_succ?>

::: mathlib
`Finset.sum_range_succ` · `Mathlib.Algebra.BigOperators.Group.Finset.Basic`

The lemma splits off the last term of a sum over `range (n + 1)`. It is the step of most proofs by induction on a finite sum.

<?decl Finset.sum_range_succ?>
:::

### The search tools

When the name is not clear, use a tool.

1. The tactic `exact?` searches for a lemma that closes the goal. It prints the line `Try this: exact name args` in the editor. Copy the line into the proof.
2. The tactic `apply?` searches for a lemma whose conclusion matches the goal. It prints the lemma and the goals that remain.
3. The tactic `rw?` searches for an equation that rewrites the goal.
4. Loogle, at loogle.lean-lang.org, searches by the form of the statement. The query `?a * 2 = ?a + ?a` finds `mul_two`.
5. The search of mathlib.tamnd.com searches the names and the statements in words of the handbook.

The tactics `exact?`, `apply?` and `rw?` are tools for the editor. A finished proof uses the line that they print, and not the tactic.

### Exercises

1. (A) Guess the name of the lemma `a + 0 = a`. Check the guess on the site.
2. (A) Guess the name of the lemma `0 < a → 0 < b → 0 < a * b`.
3. (B) The lemma `sub_nonneg` is an equivalence. Guess its statement from the name.
4. (L) Prove `MathlibHandbook.V00.C04.Exercises.mul_two_example` with one lemma. Find it by its name.
5. (L) Prove `MathlibHandbook.V00.C04.Exercises.mul_pos_example`.
6. (L) Prove `MathlibHandbook.V00.C04.Exercises.sum_range_one_example`.

### Notes and history

The naming convention is in the Mathlib style guide, in the part on naming. Volume 1 of the handbook gives the full convention, with the rules for structures, for `to_additive` and for the order of the words.
