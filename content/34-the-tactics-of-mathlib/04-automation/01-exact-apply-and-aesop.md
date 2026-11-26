---
title: exact?, apply? and aesop
kind: tactic
modules: []
explains:
  E1: [Order.lt_add_one_iff, Set.mem_of_subset_of_mem]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C04/Examples.lean, MathlibHandbook/V34/C04/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## exact?, apply? and aesop

### Overview

The tactic `exact?` searches the library for one lemma that closes the goal. The tactic `apply?` searches for lemmas that apply to the goal, and it also shows the lemmas that leave new goals. The tactic `aesop` searches for a proof with a set of rules. The three tactics come from Lean and from the package Aesop, and they search all the declarations of Mathlib that the file imports.

### What it does

The tactic `exact?` looks at the conclusion of the goal. It finds the lemmas whose conclusion matches it, it applies each one, and it tries to close the new goals with the hypotheses. If one lemma works, it prints the suggestion "Try this: exact ..." and closes the goal.

The tactic `apply?` does the same search. It does not need to close the goal. It prints a list of suggestions, with the goals that each one leaves.

The tactic `aesop` makes a tree of goals. At each node it uses rules: `simp_all`, the splitting of `∧`, `↔` and `∃`, the introduction of variables, and the lemmas of the attribute `aesop`. A safe rule does not lose provability, and `aesop` uses it at once. An unsafe rule can lose provability, and `aesop` tries it with a priority and goes back if it fails.

### How to use it

Write `exact?` on a goal that a single lemma of the library proves. Then click the suggestion, so that the file has `exact Order.lt_add_one_iff.mpr h` and not `exact?`. A search in each build of the file is slow, and its result can change when the library changes.

Write `apply?` when `exact?` fails. Read the list and pick a lemma whose new goals are easy.

Write `aesop` on a goal of logic and sets: a goal that a person proves by unfolding the definitions and by taking apart each hypothesis. Add a lemma with `aesop (add safe h)` or `aesop (add unsafe 50% apply h)`.

### What it cannot do

The tactic `exact?` uses one lemma of the library, and it closes the new goals with the hypotheses only. It does not do a chain of rewrites. On `(a + b) * c = c * b + a * c` over `ℕ`, it fails with the message "`exact?` could not close the goal. Try `apply?` to see partial suggestions." Use `ring`.

The tactic `aesop` does not know the transitivity of `⊆` by default. On `s ⊆ u` from `h1 : s ⊆ t` and `h2 : t ⊆ u`, it fails with "made no progress". On the same goal, `apply?` finds a proof, because it can apply a lemma and then close the goal with `h1` and `h2`. A direct proof is `h1.trans h2`.

A search tactic does not tell why it fails. When it fails, the goal can be false, or the lemma can be absent, or the search can be too short.

::: mathlib
`Set.mem_of_subset_of_mem` · `Mathlib.Data.Set.Basic`

This is the lemma that `apply?` suggested for `x ∈ t` from `h : s ⊆ t` and `hx : x ∈ s`. The lemma `Order.lt_add_one_iff` of `Mathlib.Algebra.Order.SuccPred` is the suggestion of `exact?` in the first example.

<?decl Set.mem_of_subset_of_mem?>
:::

### Examples

**Example (The suggestions of exact?).** Each proof is the suggestion that `exact?` printed for the goal.

<?lean MathlibHandbook/V34/C04/Examples.lean#exact_search?>

**Example (The suggestion of apply?).** The first suggestion of `apply?` closes the goal with the two hypotheses.

<?lean MathlibHandbook/V34/C04/Examples.lean#apply_search?>

**Example (Logic and sets).** In the first goal, `aesop` splits the `∧`. In the second goal, it unfolds the union and uses `h`.

<?lean MathlibHandbook/V34/C04/Examples.lean#aesop?>

### Exercises

1. (L) Prove `x ∈ s ∪ t` from `x ∈ t` with `aesop` (`mem_union_of_mem_right` in `Exercises.lean`).
2. (A) Use `exact?` on the goal `a ≤ a + b` over `ℕ`. Write the suggestion into the file.
3. (A) Tell why the file must have the suggestion of `exact?` and not `exact?` itself.
4. (B) Make `aesop` prove `s ⊆ u` from `s ⊆ t` and `t ⊆ u` with the clause `(add unsafe apply Set.Subset.trans)`. Tell what the clause adds to the search.
5. (B) Tell the difference between a safe rule and an unsafe rule of `aesop`.

### Reference

<?reference?>
