---
title: field_simp, positivity and gcongr
kind: tactic
modules: [Mathlib.Tactic.FieldSimp.Discharger, Mathlib.Tactic.Positivity.Core, Mathlib.Tactic.GCongr.Core]
explains:
  E2: [Mathlib.Tactic.FieldSimp.discharge, Mathlib.Meta.Positivity.core, Mathlib.Tactic.GCongr.gcongrExt]
  E1: [mul_le_mul_of_nonneg_right]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C02/Examples.lean, MathlibHandbook/V34/C02/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## field_simp, positivity and gcongr

### Overview

Three tactics do the steps of a computation in a field or in an ordered ring. The tactic `field_simp` clears the denominators of an equation. The tactic `positivity` proves that a term is positive, not negative or not zero. The tactic `gcongr` reduces an inequality between two terms of the same form to inequalities between their parts.

### What it does

The tactic `field_simp` moves all the fractions of the goal to one side and multiplies out. It needs to know that each denominator is not zero. Its discharger, `Mathlib.Tactic.FieldSimp.discharge`, looks for this fact in the hypotheses and tries `norm_num` and `positivity` on it.

The tactic `positivity` works on a goal `0 < e`, `0 ≤ e` or `e ≠ 0`. It goes through the term `e` from its leaves to its root. Each extension knows one operation: a square is not negative, a sum of a positive and a not negative term is positive, a quotient of positive terms is positive. A variable gets its sign from a hypothesis such as `hx : 0 < x`.

The tactic `gcongr` looks at the two sides of an inequality. If they have the same form, such as `a * c + 3` and `b * c + 3`, it uses the lemmas of the attribute `gcongr` to reduce the goal to the inequality between the parts that differ, here `a ≤ b`. It also makes side goals such as `0 ≤ c`, and it tries to close them with `positivity` and with the hypotheses.

### How to use it

Write `field_simp` with the facts `hx : x ≠ 0` in the context, and then `ring` if the goal is still open. Write `positivity` on a goal of sign. Write `gcongr` on an inequality whose two sides have the same form. If a side goal stays open, `gcongr` shows it as a new goal.

### What it cannot do

The tactic `field_simp` does not prove that a denominator is not zero when the context does not give it. On `1 / x + 1 = (1 + x) / x` with no hypothesis about `x`, it leaves the goal open.

The tactic `positivity` does not prove the sign of a variable with no hypothesis. On `0 < x` for `x : ℝ`, it fails. It also fails on a goal that is not of the form `0 < e`, `0 ≤ e` or `e ≠ 0`.

The tactic `gcongr` needs the same form on the two sides. On `x * 2 ≤ 2 * y`, the two sides have the factors in a different order, and `gcongr` leaves the goal open. Rewrite with `mul_comm` first. On `a * c ≤ b * c` with no fact about the sign of `c`, the side goal `0 ≤ c` stays open.

::: mathlib
`mul_le_mul_of_nonneg_right` · `Mathlib.Algebra.Order.GroupWithZero.Defs`

This is the lemma that `gcongr` uses for a product on the right. Its hypothesis on the sign of the factor is the side goal of `gcongr`. The core of `positivity` is `Mathlib.Meta.Positivity.core`, which runs each extension on the term.

<?decl mul_le_mul_of_nonneg_right?>
:::

### Examples

**Example (Clear a denominator).** With `hx : x ≠ 0`, the tactic `field_simp` closes the goal.

<?lean MathlibHandbook/V34/C02/Examples.lean#field_simp?>

**Example (A sum of squares).** The tactic `positivity` sees two squares and a positive numeral. In the second proof, it uses the hypothesis `hx : 0 < x` for the numerator and the denominator.

<?lean MathlibHandbook/V34/C02/Examples.lean#positivity?>

**Example (The same form on both sides).** The first goal reduces to `a ≤ b`, with the side goal `0 ≤ c` from the hypothesis `hc`. The second goal reduces to `x ≤ y`, with the side goal `0 ≤ x`.

<?lean MathlibHandbook/V34/C02/Examples.lean#gcongr?>

### Exercises

1. (L) Prove that `x ^ 4 + 2` is positive for each real `x` (`fourth_power_add_two_pos` in `Exercises.lean`).
2. (L) Prove `c * a + 1 ≤ c * b + 1` from `a ≤ b` and `0 ≤ c` (`mul_add_le_mul_add` in `Exercises.lean`).
3. (A) Tell which side goal `gcongr` makes on `x ^ 3 ≤ y ^ 3` from `x ≤ y`.
4. (B) Give a goal `0 < e` that is true and that `positivity` cannot prove. Tell which step of the term has no extension.
5. (B) Tell why `field_simp` needs the hypothesis `x ≠ 0` and why Mathlib does not add it.

### Reference

<?reference?>
