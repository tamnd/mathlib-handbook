---
title: simp
kind: tactic
modules: []
explains:
  E1: [mul_comm, mul_left_comm]
families: [F-simp]
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C01/Examples.lean, MathlibHandbook/V34/C01/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## simp

### Overview

The tactic `simp` rewrites the goal with a large set of equations and equivalences, the simp set. It stops when no lemma of the set applies. If the result is `True`, the goal is closed. Use `simp` to remove the routine steps of a proof.

### What it does

A lemma of the simp set has the form `lhs = rhs` or `lhs ↔ rhs`. The tactic finds a subterm that matches `lhs` and replaces it with `rhs`. It does this again and again, inside out, until no lemma applies. A lemma gets into the simp set with the attribute `@[simp]`. Mathlib has many thousands of such lemmas. Each lemma must make a term simpler, so that the rewriting stops. A lemma with hypotheses applies only when `simp` can prove the hypotheses, with the same simp set.

### How to use it

Write `simp` to use the whole simp set on the goal. Write `simp [h, foo]` to add the hypothesis `h` and the lemma `foo` to the set. Write `simp only [foo, bar]` to use only the lemmas of the list. Write `simp at h` to simplify the hypothesis `h`, and `simp at *` to simplify all hypotheses and the goal.

The call `simp?` does the same work as `simp`, and then it suggests a `simp only` call with the lemmas that it used. Mathlib prefers `simp only` in the middle of a proof, because a change of the simp set can break a plain `simp` that does not close the goal. A plain `simp` is correct at the end of a proof, where it must close the goal.

A new lemma goes into the simp set with `@[simp]`. Put the attribute only on a lemma whose right side is simpler than its left side.

### What it cannot do

The tactic `simp` does not use commutativity by default. On the goal `a * b = b * a` for `a b : ℕ`, `simp` fails with the message that it made no progress. With `mul_comm` in the list, `simp` uses ordered rewriting. It rewrites only when the result is smaller in a fixed order of terms, so the rewriting stops.

The tactic does not prove an inequality that needs a computation, such as `a ≤ a ^ 2` for `a : ℕ`. It does not do the algebra of a ring. Use `ring` for an identity of a commutative ring, and `linarith` or `omega` for linear arithmetic (Chapter 3).

::: mathlib
`mul_comm` · `Mathlib.Algebra.Group.Semigroup`

The lemma `mul_comm` is not in the simp set. A simp set with `mul_comm` and `mul_left_comm` puts each product in a normal order.

<?decl mul_comm?>
:::

### Examples

**Example (The length of a list).** The simp set has the lemmas for `List.length` and `++`, so `simp` closes the goal.

<?lean MathlibHandbook/V34/C01/Examples.lean#simp_list?>

**Example (Only the given lemmas).** The call `simp only` rewrites with `Nat.add_zero` and with the hypothesis `h`.

<?lean MathlibHandbook/V34/C01/Examples.lean#simp_only?>

**Example (At a hypothesis).** The call `simp at h` turns `a * 1 + 0 = 3` into `a = 3`.

<?lean MathlibHandbook/V34/C01/Examples.lean#simp_at?>

**Example (A new simp lemma).** The attribute `@[simp]` puts `double_zero` into the simp set. Then a plain `simp` uses it.

<?lean MathlibHandbook/V34/C01/Examples.lean#simp_attr?>

**Example (Commutativity).** With `mul_comm` and `mul_left_comm`, the two sides get the same normal order.

<?lean MathlibHandbook/V34/C01/Examples.lean#simp_comm?>

### Exercises

1. (A) Run `simp?` on the goal of the first example. Write down the `simp only` call that it suggests.
2. (A) Find the name of a simp lemma about `List.reverse` in the Mathlib documentation. Tell why its right side is simpler than its left side.
3. (B) Tell why the lemma `a + b = b + a` must not have the attribute `@[simp]` without ordered rewriting.
4. (B) Give a goal that `simp only [h]` closes and a plain `simp` does not change in the same way.
5. (L) Prove that the length of `(xs ++ []).reverse` is the length of `xs` (`reverse_append_nil_length` in `Exercises.lean`).

### Reference

<?reference?>
