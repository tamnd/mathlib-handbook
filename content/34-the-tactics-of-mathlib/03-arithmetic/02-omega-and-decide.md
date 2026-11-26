---
title: omega and decide
kind: tactic
modules: []
explains:
  E1: [Nat.decidablePrime, Nat.decidableLoHi]
families: []
requires: [V00]
reads_with: ["LLR"]
lean: [MathlibHandbook/V34/C03/Examples.lean, MathlibHandbook/V34/C03/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## omega and decide

### Overview

The tactic `omega` decides linear arithmetic over `ℕ` and `ℤ`. The tactic `decide` evaluates a proposition with no free variable. Both tactics come from the core of Lean, not from Mathlib. Mathlib gives `decide` many of its instances: the decision procedures for primes and for ranges of numbers.

### What it does

The tactic `omega` works on the hypotheses and the goal that are facts of `ℕ` and `ℤ`: equations, inequalities, `∣` by a numeral, `%` and `/` by a numeral, and the subtraction of `ℕ`. It also handles `∧`, `∨`, `¬` and `→` between these facts. Its docstring says that the implementation does not have all the parts of the omega algorithm, so in rare cases it fails on a true goal of this class. In practice, it proves the goals of this class.

The tactic `decide` finds an instance of `Decidable p` for the goal `p`. It asks the kernel to evaluate the instance. If the result is `true`, the proof is done. The instance `Nat.decidablePrime` decides `Nat.Prime p` for a numeral `p`. The instance `Nat.decidableLoHi` decides a statement `∀ x, lo ≤ x → x < hi → P x` when `P` is decidable.

### How to use it

Write `omega` on a goal of `ℕ` or `ℤ` that has only addition, multiplication by a numeral, `%` and `/` by a numeral. It is the best tactic for a subtraction of `ℕ`, because it knows the cut off at zero.

Write `decide` on a closed goal of small size: a divisibility of numerals, a fact about the numbers below 10, a fact about a finite type. For a large computation, `decide` is slow. Use `norm_num` for primes and large numerals.

### What it cannot do

The tactic `omega` does not work with a product of two variables. On a goal with `x * y`, it fails even if a hypothesis says `x = 2`. It does not work over `ℝ` or `ℚ`; use `linarith` there. It does not prove `x * x = 2 → False`, because this is not linear, even though the fact is true.

The tactic `decide` does not work on a goal with a free variable. On `n + 0 = n` for a variable `n`, it fails with the message "Expected type must not contain free variables". On `∀ n : ℕ, n + 0 = n`, it fails because Lean finds no instance of `Decidable` for a statement about all the natural numbers.

::: mathlib
`Nat.decidablePrime` · `Mathlib.Data.Nat.Prime.Defs`

This instance is set up to work in the kernel, so `decide` proves `Nat.Prime p` for a small numeral `p`. The faster instance for `#eval` is `Nat.decidablePrime'`. For a large numeral, the docstring advises `norm_num`.

<?decl Nat.decidablePrime?>
:::

### Examples

**Example (Facts of the integers).** The first goal uses `%` by a numeral. The second goal says that an odd number is not even. The third goal has a subtraction of `ℕ`.

<?lean MathlibHandbook/V34/C03/Examples.lean#omega?>

**Example (A closed goal).** The first goal is a divisibility of numerals. The second goal is a statement about the ten numbers below 10, and `decide` checks each one.

<?lean MathlibHandbook/V34/C03/Examples.lean#decide?>

### Exercises

1. (L) Prove `n % 3 = 2` from `n % 6 = 5` (`mod_three_of_mod_six` in `Exercises.lean`).
2. (L) Prove `13 ∣ 1001` with `decide` (`thirteen_dvd` in `Exercises.lean`).
3. (A) Tell why `omega` fails on `x * y = 2 * y` with `h : x = 2`, and give a proof with `subst`.
4. (A) Tell what `decide` does on `∀ n < 5, n ^ 2 < 20`.
5. (B) Give a tactic that proves `∀ n : ℕ, n + 0 = n`, where `decide` fails.

### Reference

<?reference?>
