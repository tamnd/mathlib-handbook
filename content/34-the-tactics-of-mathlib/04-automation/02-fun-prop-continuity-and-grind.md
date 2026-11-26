---
title: fun_prop, continuity and grind
kind: tactic
modules: [Mathlib.Tactic.FunProp.Core]
explains:
  E2: [Mathlib.Meta.FunProp.funProp]
  E1: [Continuous.add, Continuous.div₀]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C04/Examples.lean, MathlibHandbook/V34/C04/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## fun_prop, continuity and grind

### Overview

The tactic `fun_prop` proves a property of a function, such as `Continuous`, `Measurable` or `Differentiable`, from the parts of the function. The tactic `continuity` proves `Continuous` with a rule set of `aesop`. The tactic `grind` comes from the core of Lean. It proves goals by congruence closure, case splits and procedures for linear arithmetic and commutative rings.

### What it does

The tactic `fun_prop` takes the function apart. For `fun x => x ^ 2 + 3 * x`, it sees a sum, and it uses the lemma `Continuous.add`. Then it proves the property of each part: a power of the identity, and a constant times the identity. The lemmas that it uses have the attribute `fun_prop`. When a lemma has a hypothesis, `fun_prop` tries to prove it with a discharger, and it tells which hypothesis it could not prove.

The tactic `continuity` uses the lemmas of the attribute `continuity` as rules of `aesop`. It proves the same kind of goal by a search, not by taking the function apart.

The tactic `grind` puts the facts of the context and the negation of the goal into one store. It finds the terms that are equal by congruence: from `f (f x) = x` for each `x`, it gets `f (f (f a)) = f a`. It splits on `if` and on `∨`. It has procedures for linear arithmetic and for commutative rings.

### How to use it

Write `fun_prop` on a goal `Continuous f`, `Measurable f` or `Differentiable ℝ f` when `f` is made of known functions. If a lemma has a hypothesis such as `∀ x, g x ≠ 0`, use `fun_prop (disch := assumption)` or prove the hypothesis first.

Write `continuity` when `fun_prop` does not know a lemma that has the attribute `continuity`.

Write `grind` on a goal that needs equalities and case splits together, or on an identity of a commutative ring with a hypothesis.

### What it cannot do

The tactic `fun_prop` does not prove a false goal, and it tells which hypothesis is missing. On `Continuous (fun x : ℝ => 1 / x)`, it fails with the message "Failed to prove ∀ x, x ≠ 0 when applying Continuous.div₀". The goal is false in Mathlib, where `1 / 0 = 0`. The tactic `continuity` also fails on this goal, after the search of `aesop`.

The tactic `grind` does not do induction. On `2 ∣ n * (n + 1)`, it fails, though the goal is true. On `0 ≤ x ^ 2` for `x : ℝ`, it fails too, because the proof needs the sign of a square. Use `positivity` there.

::: mathlib
`Continuous.div₀` · `Mathlib.Topology.Algebra.GroupWithZero`

This lemma has the hypothesis that the denominator is not zero at each point. The message of `fun_prop` on `fun x => 1 / x` names this hypothesis. The core of `fun_prop` is `Mathlib.Meta.FunProp.funProp` in `Mathlib.Tactic.FunProp.Core`.

<?decl Continuous.div₀?>
:::

### Examples

**Example (A polynomial function).** The tactic `fun_prop` takes the sum and the products apart.

<?lean MathlibHandbook/V34/C04/Examples.lean#fun_prop?>

**Example (The same goal with continuity).** The tactic `continuity` finds the same proof by a search.

<?lean MathlibHandbook/V34/C04/Examples.lean#continuity?>

**Example (Congruence and arithmetic).** The first goal uses the hypothesis `h` at `f a`. The second goal is an identity of rings after the substitution of `x`. The third goal is linear arithmetic over `ℕ`.

<?lean MathlibHandbook/V34/C04/Examples.lean#grind?>

### Exercises

1. (L) Prove that `fun x => x ^ 3 - 2 * x + 1` is continuous on `ℝ` (`continuous_cubic` in `Exercises.lean`).
2. (L) Prove that an involution of `ℕ` is injective (`involution_injective` in `Exercises.lean`).
3. (A) Tell what message `fun_prop` gives on `Continuous (fun x : ℝ => 1 / x)`, and why the goal is false.
4. (B) Prove `2 ∣ n * (n + 1)` for `n : ℕ`. Tell why `grind` alone does not prove it.
5. (B) Tell the difference between the methods of `fun_prop` and `continuity`.

### Reference

<?reference?>
