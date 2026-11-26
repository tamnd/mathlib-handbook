---
title: Junk values
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C03]
reads_with: ["MIL Ch. 2"]
lean:
  - MathlibHandbook/V00/C05/Examples.lean
  - MathlibHandbook/V00/C05/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Junk values

### Overview

In Lean, each function is total: it has a value at each point of its domain type. Division on `ℚ` is a function from `ℚ × ℚ` to `ℚ`, so `1 / 0` has a value. Mathlib chooses the value `0`. A value that is outside the usual definition is a junk value. This section shows the junk values that a reader meets first, and the reason for them.

### The junk values

| Expression | Value in Mathlib | The usual law and its hypothesis |
|---|---|---|
| `a / 0` in a field | `0` | `a / a = 1` needs `a ≠ 0` |
| `a - b` in `ℕ` with `a < b` | `0` | `a - b + b = a` needs `b ≤ a` |
| `a / b` in `ℕ` | the quotient, rounded down | `a / b * b = a` needs `b ∣ a` |
| `√x` in `ℝ` with `x < 0` | `0` | `√x ^ 2 = x` needs `0 ≤ x` |
| `0⁻¹` in a field | `0` | `a * a⁻¹ = 1` needs `a ≠ 0` |

**Example (Division by zero).** The lemma `div_zero` states that `a / 0 = 0` in each group with zero.

<?lean MathlibHandbook/V00/C05/Examples.lean#div_zero?>

**Example (Subtraction in ℕ).** Subtraction in `ℕ` stops at zero. Lean computes the value, so `rfl` is a proof.

<?lean MathlibHandbook/V00/C05/Examples.lean#nat_sub?>

**Example (Division in ℕ).** Division in `ℕ` rounds down.

<?lean MathlibHandbook/V00/C05/Examples.lean#nat_div?>

**Example (The square root of a negative number).** The square root of a negative real number is zero.

<?lean MathlibHandbook/V00/C05/Examples.lean#sqrt_neg?>

**Example (A law with its hypothesis).** The law `a / a = 1` is false for `a = 0`, so the lemma `div_self` has the hypothesis `a ≠ 0`.

<?lean MathlibHandbook/V00/C05/Examples.lean#div_self?>

### Why Mathlib uses junk values

A total function is easier to use than a partial function. With a junk value, the expression `a / b` is a rational number for all `a` and `b`, and a statement can use it with no proof that `b ≠ 0`. The hypothesis goes to the lemmas that need it. Some laws stay true with the junk value and need no hypothesis: `(a + b) / c = a / c + b / c` is true also for `c = 0`.

The junk value never makes a false theorem. A theorem that uses `a / a = 1` must have the hypothesis `a ≠ 0`, because the lemma `div_self` asks for it. Volume 1 gives the full table of junk values of Mathlib.

::: mathlib
`div_self` · `Mathlib.Algebra.GroupWithZero.Units.Basic`

The element `a` is an implicit argument. The explicit argument is the proof of `a ≠ 0`, and Lean finds `a` from its type.

<?decl div_self?>
:::

### Exercises

1. (A) Give the value of `(5 : ℕ) - 7 + 7` in Mathlib. Compare it with `5`.
2. (A) Give the value of `(7 : ℤ) / 2` and of `(-7 : ℤ) / 2`. Check the second value in an editor with `#eval`.
3. (B) Show that `(a + b) / c = a / c + b / c` is true in `ℚ` for `c = 0`.
4. (L) Prove `MathlibHandbook.V00.C05.Exercises.zero_div_example`.
5. (L) Prove `MathlibHandbook.V00.C05.Exercises.nat_sub_add_example`.

### Notes and history

Kevin Buzzard explains the choice of junk values for a general reader in his blog post "Division by zero in type theory: a FAQ" (2020). The same choice is in Isabelle/HOL and in other provers.
