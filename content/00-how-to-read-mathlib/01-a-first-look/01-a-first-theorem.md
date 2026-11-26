---
title: A first theorem
kind: guide
modules: []
explains: {}
families: []
requires: []
reads_with: ["MIL Ch. 1", "TPIL"]
lean:
  - MathlibHandbook/V00/C01/Examples.lean
  - MathlibHandbook/V00/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## A first theorem

### Overview

Mathlib is the library of mathematics for the Lean prover. At the Mathlib commit of this edition, it has 342,368 declarations, and 253,531 of them are theorems. The topics go from the natural numbers to schemes and manifolds. Each theorem in Mathlib has a proof that Lean checks. This section shows a first theorem, the form that Lean gives it, and the package that holds the examples of the handbook.

### A theorem in Lean

The identity $(a + b)^2 = a^2 + 2ab + b^2$ is true in each commutative ring. In Lean, the statement for the integers is a line of text, and the proof is one word.

**Example (The square of a sum).** The tactic `ring` proves each identity of commutative rings.

<?lean MathlibHandbook/V00/C01/Examples.lean#add_sq?>

Read the block from left to right. The word `theorem` starts a declaration. The name `add_sq_example` is the name of the declaration. The part `(a b : ℤ)` gives two integers $a$ and $b$. The part after the colon is the statement. The symbol `:=` starts the proof. The word `by` starts a proof by tactics, and `ring` is the tactic.

**Example (A sum of squares).** The tactic `positivity` proves that an expression is positive or not negative.

<?lean MathlibHandbook/V00/C01/Examples.lean#sq_nonneg_sum?>

The type `ℚ` is the field of rational numbers. The statement $0 \le a^2 + b^2$ is true in each ordered field, and `positivity` finds the proof from the form of the expression.

### The companion package

Each Lean block of the handbook is in the package `MathlibHandbook` of the repository tamnd/mathlib-lean. The examples of Volume $n$, Chapter $m$ are in the file `MathlibHandbook/V<n>/C<m>/Examples.lean`. Each example has an anchor, a comment `-- anchor: name` before it and `-- end: name` after it, and the handbook cuts the example out by its anchor. The build of the package checks each example, so each block in a book is correct for the Mathlib commit of the edition.

To work with the examples, install Lean with `elan`, clone the repository and run `lake exe cache get`, then `lake build`. The command `lake exe cache get` downloads the compiled files of Mathlib, so the first build takes minutes and not hours.

::: mathlib
`add_sq` · `Mathlib.Algebra.Ring.Defs`

Mathlib has the identity of this section as the lemma `add_sq`, for each commutative semiring. The example above proves it again with `ring` only to show the tactic.

<?decl add_sq?>
:::

### Exercises

1. (A) Write the statement of `add_sq_example` for the real numbers. Which part of the block changes?
2. (A) The tactic `ring` proves $(a - b)^2 = a^2 - 2ab + b^2$ in `ℤ`. Explain why it cannot prove this identity in `ℕ` with the same statement.
3. (L) Prove `MathlibHandbook.V00.C01.Exercises.sub_sq_example` in the file `MathlibHandbook/V00/C01/Exercises.lean`.
4. (L) Prove `MathlibHandbook.V00.C01.Exercises.sq_add_one_pos`: for each rational number $a$, $0 < a^2 + 1$.

### Notes and history

Mathlib started in 2017 as the mathematics library of Lean 3. The community moved it to Lean 4 from 2021 to 2023. The book *Mathematics in Lean* is the standard first text for it, and its Chapter 1 is a good companion to this chapter.
