---
title: Classical logic in Mathlib
kind: theory
modules:
  - Mathlib.Basic.Logic.Basic
explains:
  E3: [Classical.axiom_of_choice]
  E2: [by_contra, dec_em, Classical.dec]
  E1: auto
families: []
requires: [V00]
reads_with: ["TPIL", "MIL"]
lean:
  - MathlibHandbook/V01/C01/Examples.lean
  - MathlibHandbook/V01/C01/Exercises.lean
  - MathlibHandbook/V01/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Classical logic in Mathlib

### Overview

The logic of Lean is constructive at its core. Mathlib adds the axiom of choice and uses classical logic everywhere. This section shows the three axioms that Mathlib accepts, the law of the excluded middle, and proof by contradiction. It also explains the class `Decidable`. An `if` statement needs this class, and the tactic `decide` uses it to compute a proof.

### Definitions

**Definition (Proposition).** A proposition is a term of type `Prop`. A proof of a proposition `p` is a term of type `p`. Two proofs of the same proposition are equal.

**Definition (Choice).** The axiom `Classical.choice` takes a proof of `Nonempty α` and gives an element of `α`. It is the only axiom of Lean that gives data.

**Definition (Decidable proposition).** A proposition `p` is decidable when there is a term of type `Decidable p`. Such a term is either a proof of `p` or a proof of `¬p`, and Lean can compute which one.

### Theorems and proofs

**Theorem (Excluded middle).** For every proposition $p$, the statement $p \lor \lnot p$ is true.

*Proof.* Lean proves `Classical.em` from `Classical.choice`, propositional extensionality and function extensionality. The argument is the theorem of Diaconescu. $\square$

**Theorem (Proof by contradiction).** If $\lnot p$ implies a contradiction, then $p$ is true.

*Proof.* By the excluded middle, $p$ or $\lnot p$ is true. In the second case, the hypothesis gives `False`, and from `False` any statement follows. $\square$

**Theorem (Every proposition is decidable).** With classical logic, every proposition has a `Decidable` instance.

*Proof.* The instance `Classical.dec` chooses the proof of $p$ or of $\lnot p$ with `Classical.choice`. The result is a term of `Decidable p`, but it does not compute. $\square$

::: mathlib
`by_contra` · `Mathlib.Basic.Logic.Basic`

Mathlib states proof by contradiction as `by_contra`. The tactic of the same name applies it: after `by_contra h`, the hypothesis `h` is the negation of the goal, and the new goal is `False`. The lemma `dec_em` is the excluded middle for a decidable proposition, with no axiom.

<?decl by_contra?>
:::

::: mathlib
`Classical.axiom_of_choice` · `Mathlib.Basic.Logic.Basic`

Mathlib proves the usual form of the axiom of choice from `Classical.choice`. A relation that relates each `a` to some `b` contains the graph of a function.

<?decl Classical.axiom_of_choice?>
:::

### Examples

**Example (The excluded middle).** The term `Classical.em p` proves `p ∨ ¬p` for any `p`.

<?lean MathlibHandbook/V01/C01/Examples.lean#em?>

**Example (A proof by contradiction).** The tactic `by_contra hp` adds `hp : ¬p` and asks for `False`.

<?lean MathlibHandbook/V01/C01/Examples.lean#by_contra?>

**Example (A witness by choice).** From a proof of `∃ n, f n = 0`, the function `Classical.choose` gives a number, and `Classical.choose_spec` gives its property. The number has no formula. It exists only by the axiom.

<?lean MathlibHandbook/V01/C01/Examples.lean#choose?>

**Example (A proof by computation).** Equality and divisibility of natural numbers are decidable. The tactic `decide` evaluates the instance, and the result is a proof.

<?lean MathlibHandbook/V01/C01/Examples.lean#decide?>

**Example (An if statement).** The term `if n = 0 then 1 else n` uses the instance `Decidable (n = 0)`. The tactic `split_ifs` makes one goal for each branch.

<?lean MathlibHandbook/V01/C01/Examples.lean#dite?>

**Counterexample (An if statement with no instance).** For an arbitrary proposition `p`, the term `if p then 1 else 0` does not elaborate, because Lean finds no instance of `Decidable p`. After `open Classical`, the instance `Classical.dec` applies, and the term elaborates.

<?lean MathlibHandbook/V01/C01/Examples.lean#classical_if?>

### The library around it

The module `Mathlib.Basic.Logic.Basic` has about 250 lemmas about the connectives. Most have a name that gives the statement: `not_forall`, `not_exists`, `not_and_or` and `imp_iff_not_or`. The lemmas with the prefix `Decidable.` prove the same statements for decidable propositions with no axiom. The lemmas with the prefix `Classical.` use choice. In a proof, use the tactic `classical` at the start to make every proposition decidable for the rest of the proof. In a statement, add the hypothesis `[Decidable p]` and do not use `open Classical`, because a statement with a classical instance can disagree with a statement that uses another instance. The tactic `push_neg` moves a negation inward through quantifiers and connectives.

### Exercises

1. (A) Prove $\lnot\lnot p \to p$ on paper. Name the step that uses the excluded middle.
2. (A) Explain why `decide` can prove `2 ^ 10 = 1024` but cannot prove a statement about every natural number.
3. (B) Show that `Classical.choose` applied to two proofs of the same statement gives the same element.
4. (L) Prove `¬¬p ↔ p` in Lean. The solution is `not_not_example` in `Solutions.lean`.
5. (L) Prove that if not every natural number fails `P`, then some number has `P`. The solution is `exists_of_not_forall_not_example`.
6. (L) Prove `3 ∣ 123` with one tactic. The solution is `three_dvd_example`.

### Notes and history

Lean accepts three axioms: `propext`, `Quot.sound` and `Classical.choice`. The script `scripts/Axioms.lean` of the companion checks that no example uses another axiom. The proof of the excluded middle from choice is due to Diaconescu (1975). The design of `Decidable` follows the Lean 4 core library.

### Reference

<?reference?>
