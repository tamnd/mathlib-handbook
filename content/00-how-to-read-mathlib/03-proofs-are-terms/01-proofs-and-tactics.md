---
title: Proofs and tactics
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C02]
reads_with: ["TPIL", "MIL Ch. 2"]
lean:
  - MathlibHandbook/V00/C03/Examples.lean
  - MathlibHandbook/V00/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Proofs and tactics

### Overview

In Lean, a statement is a type, and a proof of the statement is a term of that type. Lean checks a proof as it checks the type of any term. A tactic proof is a program that makes the term step by step. This section shows the two forms of proof on the same statements, and the commands that show what a proof uses.

### Statements are types

The type `p ∧ q → q ∧ p` is a statement. A term of this type is a function that takes a proof of `p ∧ q` and gives a proof of `q ∧ p`.

| Statement | A proof is |
|---|---|
| `p → q` | a function from proofs of `p` to proofs of `q` |
| `p ∧ q` | a pair of a proof of `p` and a proof of `q` |
| `p ∨ q` | a proof of `p` or a proof of `q`, with a tag |
| `∀ x, P x` | a function that gives a proof of `P x` for each `x` |
| `∃ x, P x` | a pair of a witness `x` and a proof of `P x` |
| `¬ p` | a function from proofs of `p` to proofs of `False` |

### Two forms of the same proof

**Example (A proof as a term).** The term takes the pair `h` and gives the pair of its second and first parts.

<?lean MathlibHandbook/V00/C03/Examples.lean#and_swap_term?>

**Example (A proof by tactics).** The tactic `intro` takes the hypothesis. The tactic `obtain` cuts the pair into its parts. The tactic `exact` gives the final term.

<?lean MathlibHandbook/V00/C03/Examples.lean#and_swap_tactic?>

The two theorems have the same type. Lean stores a term for each of them, and the terms are almost the same. In an editor, the goal view shows the goal after each tactic. Read a tactic proof with the goal view open.

**Example (An existence proof).** The proof of an existence statement is the pair of a witness and a proof for it. Here the proof for the witness is `rfl`, because `4 * 4` and `16` compute to the same number.

<?lean MathlibHandbook/V00/C03/Examples.lean#exists_term?>

**Example (A proof for all n).** The proof of a statement for all `n` is a function of `n`.

<?lean MathlibHandbook/V00/C03/Examples.lean#forall_term?>

**Example (A chain of steps).** The block `calc` writes a chain of relations. Each step has its own proof, and Lean joins the steps by transitivity.

<?lean MathlibHandbook/V00/C03/Examples.lean#calc_proof?>

### What a proof uses

The command `#print axioms name` gives the axioms that the proof of `name` uses. Most proofs of Mathlib use three axioms: `propext` (two equivalent statements are equal), `Quot.sound` (the quotient of a relation identifies related elements) and `Classical.choice` (a nonempty type has an element). A proof that uses `sorryAx` is not complete. The companion package checks each example with this command, and it rejects each axiom outside the three.

::: mathlib
`Nat.strong_induction_on` · `Mathlib.Data.Nat.Init`

A lemma can take a proof as an argument. The principle of strong induction on `ℕ` takes the step of the induction as a function: for each `n`, a proof of `motive n` from proofs of `motive m` for all `m < n`.

<?decl Nat.strong_induction_on?>
:::

### Exercises

1. (A) Write the type of a proof of `p → (q → p)`. Give the term.
2. (A) Explain why `⟨4, rfl⟩` is not a proof of `∃ n : ℕ, n * n = 15`.
3. (B) Write a proof of `¬ (p ∧ ¬ p)` as a term.
4. (L) Prove `MathlibHandbook.V00.C03.Exercises.or_swap_term`, first as a term, then by tactics.
5. (L) Prove `MathlibHandbook.V00.C03.Exercises.exists_add_eq`.
6. (L) Prove `MathlibHandbook.V00.C03.Exercises.le_add_two` with `calc`.

### Notes and history

The identification of statements with types and of proofs with terms is the Curry and Howard correspondence. *Theorem Proving in Lean 4* gives the full account in its chapters on propositions and on quantifiers.
