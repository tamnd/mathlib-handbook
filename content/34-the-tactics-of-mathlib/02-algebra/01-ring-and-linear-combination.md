---
title: ring and linear_combination
kind: tactic
modules: [Mathlib.Tactic.Ring.Basic, Mathlib.Tactic.LinearCombination]
explains:
  E2: [Mathlib.Tactic.Ring.proveEq, Mathlib.Tactic.LinearCombination.linearCombination]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C02/Examples.lean, MathlibHandbook/V34/C02/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## ring and linear_combination

### Overview

The tactic `ring` proves an equation that holds in every commutative ring, or in every commutative semiring. The tactic `linear_combination` proves an equation that follows from the hypotheses by a sum of multiples of them. Together they do most of the routine algebra of a proof.

### What it does

The tactic `ring` puts the two sides of the goal into a normal form and compares the results. The normal form is a sum of monomials with numeral coefficients, in a fixed order of the atoms. An atom is a subterm that `ring` cannot take apart, such as a variable or `Real.sqrt 2`. In a field, `ring` also knows the inverse of a numeral, so it proves `x / 2 + x / 2 = x`. The tactic `ring_nf` writes a term in the same normal form and does not need to close the goal.

The call `linear_combination e` takes a proof term `e` that is a sum of multiples of hypotheses. It subtracts the equation of `e` from the goal and calls `ring1` on the result. Thus it proves the goal when the goal minus `e` is an identity of rings.

### How to use it

Write `ring` at the end of a proof, when the goal is an identity. Write `ring_nf at h ⊢` to bring a hypothesis and the goal into the same form, and then `exact h`.

To use `linear_combination`, find the coefficients by hand. If the hypotheses are `h1 : a + b = 3` and `h2 : a - b = 1` and the goal is `a = 2`, then the goal is half the sum of the two equations. Write `linear_combination (h1 + h2) / 2`. A coefficient can be a term with variables, as in `linear_combination (x + y) * h`.

### What it cannot do

The tactic `ring` does not use the hypotheses. On the goal `a ^ 2 = b ^ 2` with the hypothesis `h : a = b`, `ring` leaves the goal open. Use `subst h` first, or `linear_combination (a + b) * h`.

The tactic `ring` does not know that `x / x = 1`. This is false for `x = 0` in Mathlib, where `x / 0 = 0`. Use `field_simp` with the hypothesis `x ≠ 0` (next section).

The tactic `linear_combination` does not find the coefficients. It also cannot use a hypothesis that is not an equation of the right form. On `x = 2` from `h : x ^ 2 = 4` and `0 < x`, the call `linear_combination h` fails, because the goal minus `h` is not an identity, and the sign condition is not linear algebra.

::: mathlib
`Mathlib.Tactic.Ring.proveEq` · `Mathlib.Tactic.Ring.Basic`

This is the frontend of `ring1`. It tries to close a goal that is an equation of semirings. The tactic `linear_combination` is the declaration `Mathlib.Tactic.LinearCombination.linearCombination` of the module `Mathlib.Tactic.LinearCombination`.
:::

### Examples

**Example (The cube of a sum).** The tactic `ring` expands both sides and compares the monomials.

<?lean MathlibHandbook/V34/C02/Examples.lean#ring_cube?>

**Example (Any commutative ring).** The first proof works in any commutative ring `R`. The second proof uses the inverse of the numeral 2 in `ℚ`.

<?lean MathlibHandbook/V34/C02/Examples.lean#ring_general?>

**Example (The normal form at a hypothesis).** The call `ring_nf` turns `x * 2 + x = 6` into `x * 3 = 6`, and it puts the goal into the same form.

<?lean MathlibHandbook/V34/C02/Examples.lean#ring_nf?>

**Example (A linear system).** Half the sum of the two hypotheses gives the goal. In the second proof, the coefficient is the term `x + y`.

<?lean MathlibHandbook/V34/C02/Examples.lean#linear_combination?>

### Exercises

1. (L) Prove the formula for the difference of two cubes (`diff_cubes` in `Exercises.lean`).
2. (L) Solve the system `2 * x + y = 5`, `x - y = 1` for `x` (`solve_system` in `Exercises.lean`). Find the coefficients first.
3. (A) Tell what `ring_nf` does to the term `(x + 1) * (x - 1)` in `ℚ`.
4. (B) Tell why `ring` cannot prove `x / x = 1` in `ℚ`. Give the value of `0 / 0` in Mathlib.
5. (B) Give a goal that `linear_combination` proves and `ring` does not. Tell what the coefficient is.

### Reference

<?reference?>
