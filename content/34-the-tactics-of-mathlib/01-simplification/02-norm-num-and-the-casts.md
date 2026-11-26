---
title: norm_num and the casts
kind: tactic
modules: [Mathlib.Tactic.NormNum.Prime]
explains:
  E2: [Mathlib.Meta.NormNum.evalNatPrime]
  E1: [Nat.cast_add, Nat.cast_lt]
families: [F-simp-cast]
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C01/Examples.lean, MathlibHandbook/V34/C01/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## norm_num and the casts

### Overview

The tactic `norm_num` computes with numerals. It proves goals such as `(2 : ℚ) / 3 + 1 / 6 = 5 / 6` and `Nat.Prime 97`. The tactics `push_cast` and `norm_cast` move and remove the casts between the number types `ℕ`, `ℤ`, `ℚ` and `ℝ`.

### What it does

The tactic `norm_num` is `simp` with a set of extensions. Each extension evaluates one kind of term on numerals: a sum, a product, a power, a quotient, a comparison, a divisibility, a primality and others. The result of an extension is a numeral and a proof. Thus `norm_num` decides an equation or an inequality between closed terms of numerals in an ordered field.

The tactic `push_cast` rewrites with the lemmas that move a cast, such as `Nat.cast_add`. It moves each cast from the outside of a term to its leaves. The tactic `norm_cast` does the opposite on a statement. It moves the casts up and removes them when the two sides have casts from the same type. The tactic `exact_mod_cast h` closes the goal with `h` after `norm_cast` on both.

### How to use it

Write `norm_num` on a goal of numerals. Write `norm_num at h` on a hypothesis. Write `norm_num [foo]` to add the lemma `foo`, as with `simp`. The extension for `Nat.Prime` is in the module `Mathlib.Tactic.NormNum.Prime`. Import it when the goal is about primality.

Write `push_cast` on a goal with a cast of a sum or of a product, and then use `ring` or `linarith`. Write `exact_mod_cast h` when `h` and the goal are the same statement with casts in other places.

### What it cannot do

The tactic `norm_num` does not do the algebra of a ring. On the goal `x + x = 2 * x` for `x : ℚ`, `norm_num` leaves the goal open. Use `ring`. It does not prove an inequality with a variable, such as `a ≤ a ^ 2` for `a : ℕ`.

The tactic `push_cast` does not move a cast through a subtraction of `ℕ`. The lemma `Nat.cast_sub` needs the hypothesis `b ≤ a`. Give this hypothesis to the tactic, as in `push_cast [h]`. Then the cast of `a - b` becomes the difference of the casts.

::: mathlib
`Nat.cast_add` · `Mathlib.Data.Nat.Cast.Defs`

The cast of a sum is the sum of the casts. The lemma has the attributes `simp` and `norm_cast`. The attribute `norm_cast` also gives it to `push_cast`, because the lemma moves a cast. The norm_num extension for primality is `Mathlib.Meta.NormNum.evalNatPrime`.

<?decl Nat.cast_add?>
:::

### Examples

**Example (A sum of fractions).** The tactic computes the sum in `ℚ`.

<?lean MathlibHandbook/V34/C01/Examples.lean#norm_num_rat?>

**Example (A prime and a composite).** The extension of `Mathlib.Tactic.NormNum.Prime` proves that 97 is prime and that 91 is not prime.

<?lean MathlibHandbook/V34/C01/Examples.lean#norm_num_prime?>

**Example (Push the cast).** The tactic `push_cast` changes the cast of `(n + 1) ^ 2` to `((n : ℤ) + 1) ^ 2`. Then `ring` closes the goal.

<?lean MathlibHandbook/V34/C01/Examples.lean#push_cast?>

**Example (Remove the cast).** The hypothesis is about integers and the goal is about natural numbers. The tactics `exact_mod_cast` and `norm_cast` see that they are the same statement.

<?lean MathlibHandbook/V34/C01/Examples.lean#norm_cast?>

### Exercises

1. (L) Prove `(3 : ℚ) ^ 2 - 1 / 2 = 17 / 2` with `norm_num` (`numeral_sum` in `Exercises.lean`).
2. (A) Tell why `norm_num` proves `¬ Nat.Prime 91`. Give the two factors.
3. (B) Give a goal with a cast of a subtraction of `ℕ` that `push_cast` cannot change. Then give the hypothesis that makes it work.
4. (L) Prove that the cast of `2 * n + 1` from `ℕ` to `ℤ` is `2 * (n : ℤ) + 1` (`cast_two_mul_add_one` in `Exercises.lean`).

### Reference

<?reference?>
