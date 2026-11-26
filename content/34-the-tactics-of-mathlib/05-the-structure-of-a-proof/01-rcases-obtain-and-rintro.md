---
title: rcases, obtain and rintro
kind: tactic
modules: []
explains:
  E1: [Set.mem_inter_iff]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C05/Examples.lean, MathlibHandbook/V34/C05/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## rcases, obtain and rintro

### Overview

The tactic `rcases` takes a hypothesis apart with a pattern. The tactic `obtain` does the same, written as a step that names the result. The tactic `rintro` introduces variables and takes them apart in one step. The three tactics come from the core of Lean, and Mathlib uses them in almost each proof.

### What it does

A pattern tells the shape of the hypothesis. The pattern `⟨a, b⟩` takes apart a structure with two fields, such as `p ∧ q` or `∃ x, p x`. The pattern `a | b` takes apart an `∨`, and it gives one goal for each case. The pattern `rfl` substitutes an equation. The pattern `-` clears a part that the proof does not need. Patterns nest: `⟨x, hx | hx⟩` takes apart `∃ x, p x ∨ q x`.

The call `obtain pat := e` is the same as `rcases e with pat`. The call `obtain pat : t` makes the new goal `t` first, and then takes the proof apart. The call `rintro pat₁ pat₂` is `intro` followed by `rcases` on each variable.

### How to use it

Write `obtain ⟨n, hn⟩ := h` for a hypothesis `h : ∃ n, p n`. This is the step "take `n` with `p n`" of a written proof. Write `rcases h with rfl | rfl` when each case is an equation, and then close the goals with `<;>`. Write `rintro x ⟨hs, ht⟩` on a goal `s ∩ t ⊆ u`: an element of the intersection is a pair of facts, by `Set.mem_inter_iff`.

### What it cannot do

These tactics cannot take apart a proof of `∃` when the goal is data. In a definition of a natural number, `obtain ⟨n, hn⟩ := h` with `h : ∃ n, p n` fails, because a proof of a proposition cannot give data. Use `Classical.choose h` or the tactic `choose` (next section).

They do not prove anything by themselves. A pattern only changes the form of the context. The pattern must match the shape of the hypothesis.

::: mathlib
`Set.mem_inter_iff` · `Mathlib.Data.Set.Basic`

An element of `a ∩ b` is an element of `a` and of `b`. Because the membership in an intersection unfolds to `∧`, the pattern `⟨hs, ht⟩` of `rintro` takes it apart.

<?decl Set.mem_inter_iff?>
:::

### Examples

**Example (A conjunction).** The pattern `⟨hp, hq⟩` gives the two parts of `h`.

<?lean MathlibHandbook/V34/C05/Examples.lean#rcases_and?>

**Example (A disjunction of equations).** The pattern `rfl | rfl` gives two goals, `1 ^ 2 = 1` and `(-1) ^ 2 = 1`, and `norm_num` closes each one.

<?lean MathlibHandbook/V34/C05/Examples.lean#rcases_or?>

**Example (Take a witness).** The step `obtain` gives the witness `n` and the fact `hn`.

<?lean MathlibHandbook/V34/C05/Examples.lean#obtain?>

**Example (Introduce and take apart).** The call `rintro` introduces `x` and takes apart the fact `x ∈ s ∩ t`.

<?lean MathlibHandbook/V34/C05/Examples.lean#rintro?>

### Exercises

1. (L) Prove `∃ n, q n` from `∃ n, p n ∧ q n` (`exists_of_exists_and` in `Exercises.lean`). Use the pattern `-` for the part that the proof does not need.
2. (A) Write the pattern that takes apart `h : ∃ x, p x ∨ q x`. Tell how many goals it gives.
3. (A) Prove `s ∪ t ⊆ t ∪ s` with `rintro` and the pattern `x (hs | ht)`.
4. (B) Tell why `obtain` fails on an `∃` inside a definition of a natural number.

### Reference

<?reference?>
