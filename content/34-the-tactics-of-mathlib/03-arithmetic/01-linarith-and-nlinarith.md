---
title: linarith and nlinarith
kind: tactic
modules: [Mathlib.Tactic.Linarith.Frontend]
explains:
  E2: [Mathlib.Tactic.Linarith.linarith]
  E1: [Mathlib.Tactic.Linarith.lt_irrefl, sq_nonneg]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C03/Examples.lean, MathlibHandbook/V34/C03/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## linarith and nlinarith

### Overview

The tactic `linarith` proves a goal that follows from the hypotheses by linear arithmetic over an ordered field. The tactic `nlinarith` adds products of the hypotheses first, so that it can also prove some goals of degree two.

### What it does

The tactic `linarith` adds the negation of the goal to the hypotheses. Then it looks for a combination of the hypotheses with coefficients that are not negative, whose sum is `0 < 0`. This sum is a contradiction by `Mathlib.Tactic.Linarith.lt_irrefl`. The search is the method of Fourier and Motzkin, or the simplex method in the default setting. A term such as `x * y` or `x ^ 2` is an atom for `linarith`: it does not look inside it.

The tactic `nlinarith` first collects the hypotheses and the terms of its list. It multiplies each pair of them and adds the products as new hypotheses. Then it calls the procedure of `linarith`. Thus `nlinarith` proves `x ^ 2 ≤ x` from `0 ≤ x` and `x ≤ 1`, because the product of `0 ≤ x` and `0 ≤ 1 - x` is the inequality that it needs.

### How to use it

Write `linarith` when the goal is a linear consequence of the context. Put a fact that is not in the context into the list: `linarith [sq_nonneg b]` adds `0 ≤ b ^ 2`. Write `linarith only [h1, h2]` to use only these hypotheses, which is faster in a large context.

Write `nlinarith` when the proof needs a product. Give it the square that a proof by hand uses: `nlinarith [sq_nonneg (a - b)]` proves `2 * a * b ≤ a ^ 2 + b ^ 2`.

### What it cannot do

The tactic `linarith` does not prove a fact about a product. On `0 ≤ a * a` it fails, because `a * a` is an atom with no hypothesis. It also does not substitute: on `x * y = 2 * y` with `h : x = 2`, it fails, because `x * y` and `y` are two different atoms. Use `rw [h]` or `subst h` first.

The tactic `nlinarith` does not find the right square by itself in all cases. On `2 * a * b ≤ a ^ 2 + b ^ 2` with no hint, it fails. It multiplies only pairs, so on `0 ≤ a * b * c` from `0 ≤ a`, `0 ≤ b` and `0 ≤ c`, it fails too. Give it the product `mul_nonneg (mul_nonneg ha hb) hc`, or use `positivity`.

Neither tactic knows the subtraction of `ℕ`. On `a - b + b = a` with `h : b ≤ a`, `linarith` fails, because `a - b` is an atom for it. Use `omega` for the subtraction of `ℕ` (next section).

::: mathlib
`Mathlib.Tactic.Linarith.linarith` · `Mathlib.Tactic.Linarith.Frontend`

This is the core procedure. It takes the goal and a list of terms, and it runs on all the suitable hypotheses of the context unless the flag `only_on` is true. The tactic `nlinarith` is the same procedure with a preprocessing step for the products.

<?decl Mathlib.Tactic.Linarith.linarith?>
:::

### Examples

**Example (A chain of inequalities).** The first goal is the sum of the two hypotheses. In the second goal, `linarith` uses `a + 2 * b ≤ c` and two times `0 ≤ b`.

<?lean MathlibHandbook/V34/C03/Examples.lean#linarith?>

**Example (A term in the list).** The fact `0 ≤ b ^ 2` is not in the context. The list of `linarith` adds it.

<?lean MathlibHandbook/V34/C03/Examples.lean#linarith_terms?>

**Example (A product of hypotheses).** The first proof gives `nlinarith` the square of `a - b`. The second proof needs no hint: the product of `h1` and `h2` is enough.

<?lean MathlibHandbook/V34/C03/Examples.lean#nlinarith?>

### Exercises

1. (L) Prove `x < z + 1` from `x ≤ y` and `y < z` (`lt_add_one_of_le_of_lt` in `Exercises.lean`).
2. (L) Prove `x ^ 3 ≤ x` from `0 ≤ x` and `x ≤ 1` (`cube_le_self` in `Exercises.lean`). Find the products that `nlinarith` needs.
3. (A) Tell why `linarith` fails on `x * y = 2 * y` with `h : x = 2`, and give a proof.
4. (B) Give the linear combination that `linarith` finds for the goal `a ≤ c` from `a + 2 * b ≤ c` and `0 ≤ b`.
5. (B) Tell why `nlinarith` with no hint fails on `0 ≤ a * b * c` from three hypotheses of sign.

### Reference

<?reference?>
