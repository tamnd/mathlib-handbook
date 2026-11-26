---
title: choose, lift and filter_upwards
kind: tactic
modules: [Mathlib.Tactic.Lift, Mathlib.Tactic.Choose]
explains:
  E2: [CanLift, Mathlib.Tactic.Lift.main, Mathlib.Tactic.Choose.choose1]
  E1: [Filter.mp_mem, Filter.Eventually.mono]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C05/Examples.lean, MathlibHandbook/V34/C05/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## choose, lift and filter_upwards

### Overview

Three tactics of Mathlib do common steps of analysis and of number theory. The tactic `choose` turns a hypothesis `∀ x, ∃ y, P x y` into a function `f` and the fact `∀ x, P x (f x)`. The tactic `lift` replaces a variable of a type with a variable of a smaller type, such as `ℤ` with `ℕ`. The tactic `filter_upwards` proves that a fact holds eventually from other facts that hold eventually.

### What it does

The call `choose f hf using h` takes `h : ∀ x, ∃ y, P x y`. It adds `f : X → Y` and `hf : ∀ x, P x (f x)` to the context. It uses the axiom of choice. It also works on more than one variable and on a plain `∃`.

The call `lift n to ℕ using h` takes a variable `n : ℤ` and a proof `h : 0 ≤ n`. It adds a variable `n : ℕ`, and it replaces each old `n` with the cast `↑n`. It works for each pair of types with an instance of the class `CanLift`.

The call `filter_upwards [h₁, h₂] with x hx₁ hx₂` takes facts `h₁ : ∀ᶠ x in F, p x` and `h₂ : ∀ᶠ x in F, q x`, and a goal `∀ᶠ x in F, r x`. It reduces the goal to `∀ x, p x → q x → r x`, with the names `x`, `hx₁` and `hx₂`. It uses the lemma `Filter.mp_mem` for each fact of the list.

### How to use it

Write `choose` when a proof needs a function that a hypothesis gives only one value at a time, as in a proof of the form "for each `n`, take `m` with `n < m`".

Write `lift` when a variable of `ℤ` or `ℝ` is not negative and the lemmas that the proof needs are for `ℕ` or for `NNReal`. Give the proof with `using`, or prove the side goal after the call.

Write `filter_upwards` on each goal `∀ᶠ x in F, r x` that follows from facts of the same filter. This is the step "for large `n`, both facts hold, so the goal holds" of a written proof.

### What it cannot do

The tactic `lift` needs the condition of `CanLift`. If no proof follows `using`, it does not prove the condition. It makes the goal `0 ≤ n` first, before the main goal.

The tactic `filter_upwards` works only on a goal of a filter. On a goal that is not of this form, such as `0 ≤ f 5`, it fails with a type mismatch.

The tactic `choose` needs a hypothesis of the form `∀ xs, ∃ a, p xs a` or `∀ xs, p xs ∧ q xs`. On a hypothesis `h : p` of a different form, it fails with the message "expected a term of the shape `∀ xs, ∃ a, p xs a` or `∀ xs, p xs ∧ q xs`".

::: mathlib
`CanLift` · `Mathlib.Tactic.Lift`

A class that tells that an element of `α` can be lifted to `β` when the condition `cond` holds. The tactic `lift` finds the instance and uses its condition as the side goal. The main procedure of the tactic is `Mathlib.Tactic.Lift.main`.

<?decl CanLift?>
:::

### Examples

**Example (A function from a hypothesis).** The hypothesis gives, for each `n`, a value `m` above it. The call `choose` makes the function `f`.

<?lean MathlibHandbook/V34/C05/Examples.lean#choose?>

**Example (From ℤ to ℕ).** After the call `lift`, the variable `n` is of `ℕ`, and the goal is `p ↑n`.

<?lean MathlibHandbook/V34/C05/Examples.lean#lift?>

**Example (For large n).** The two facts hold eventually. The call `filter_upwards` reduces the goal to a fact at each `n`.

<?lean MathlibHandbook/V34/C05/Examples.lean#filter_upwards?>

### Exercises

1. (L) Make a function `f` with `2 * n ≤ f n` for each `n` (`exists_bound_function` in `Exercises.lean`).
2. (L) Prove that `f n + g n ≤ 3` holds eventually from `f n ≤ 1` and `g n ≤ 2` eventually (`eventually_le_add` in `Exercises.lean`).
3. (A) Tell which goal `lift n to ℕ` makes when no proof follows `using`.
4. (A) Prove the first example of `filter_upwards` with `Filter.Eventually.mono` and `Filter.Eventually.and`.
5. (B) Tell which axiom the function of `choose` comes from, and why a proof by hand needs it too.

### Reference

<?reference?>
