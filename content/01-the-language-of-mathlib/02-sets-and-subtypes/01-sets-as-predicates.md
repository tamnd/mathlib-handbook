---
title: Sets as predicates
kind: theory
modules: []
explains:
  E2: [Set.mem_ofPred_eq]
  E1: [Set.ext, Set.ncard_coe_finset, Finset.coe_range, Finset.card_range, Fintype.card_fin, Fintype.card_coe]
families: []
requires: [V01.C01]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V01/C02/Examples.lean
  - MathlibHandbook/V01/C02/Exercises.lean
  - MathlibHandbook/V01/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sets as predicates

### Overview

In set theory, a set is the basic object, and every element belongs to many sets. In Lean, each term has exactly one type, and a type is not a set. Mathlib uses two tools instead. A set `s : Set α` is a predicate on the type `α`. A subtype `{x : α // p x}` is a new type whose terms are the elements of `α` with the property `p`, each with a proof. This section shows both tools, and it shows when to use `Finset` and `Fintype` for finite collections.

### Definitions

**Definition (Set).** For a type `α`, the type `Set α` is the type of functions `α → Prop`. The set `{x | p x}` is the predicate `p`, and `a ∈ s` means `s a`.

**Definition (Subtype).** For a predicate `p` on `α`, the subtype `{x : α // p x}` has as terms the pairs `⟨a, h⟩` with `a : α` and `h : p a`. The coercion `↑` sends the pair to `a`.

**Definition (Finset and Fintype).** A term of `Finset α` is a finite set of elements of `α`, given as a list with no repetition up to order. A `Fintype α` instance says that the type `α` itself is finite, and it gives the list of all its elements.

### Theorems and proofs

**Theorem (Membership is the predicate).** For a predicate $p$ and an element $a$, the statement $a \in \{x \mid p(x)\}$ is the statement $p(a)$.

*Proof.* Both sides are the same term after the definitions unfold, so `Iff.rfl` proves the equivalence. $\square$

**Theorem (Extensionality).** Two sets $s$ and $t$ of the same type are equal when $x \in s \leftrightarrow x \in t$ for every $x$.

*Proof.* Two predicates are equal when they agree at each point, by function extensionality and propositional extensionality. $\square$

**Theorem (One count in four forms).** The finset `Finset.range 3`, the type `Fin 3`, the subtype of the numbers in `Finset.range 3` and the set `Set.Iio 3` each have three elements.

*Proof.* The first two are the lemmas `Finset.card_range` and `Fintype.card_fin`. The subtype has the cardinality of the finset by `Fintype.card_coe`. The set is the coercion of the finset, and `Set.ncard_coe_finset` gives its cardinality. $\square$

::: mathlib
`Set.mem_ofPred_eq` · `Mathlib.Data.Set.Operations`

Mathlib states membership in `{y | p y}` as the equation `(x ∈ {y | p y}) = p x`. It is a simp lemma, so `simp` unfolds the membership. The older name `Set.mem_setOf_eq` is deprecated.

<?decl Set.mem_ofPred_eq?>
:::

### Examples

**Example (Membership by definition).** The membership `x ∈ {n | Even n}` is `Even x`, and `Iff.rfl` proves it.

<?lean MathlibHandbook/V01/C02/Examples.lean#mem_setOf?>

**Example (Two equal sets).** The set of natural numbers below `2` is `{0, 1}`. The tactic `ext` reduces the equation to membership, and `omega` closes the arithmetic.

<?lean MathlibHandbook/V01/C02/Examples.lean#set_ext?>

**Example (An element of a subtype).** The pair of `4` and a proof that `4` is even is a term of the subtype of even numbers. Its coercion is `4`.

<?lean MathlibHandbook/V01/C02/Examples.lean#subtype?>

**Example (Four forms of one statement).** The same count appears as a `Finset` card, a `Fintype` card of a type, a `Fintype` card of a subtype, and an `ncard` of a set.

<?lean MathlibHandbook/V01/C02/Examples.lean#four_forms?>

**Counterexample (A set is not a type).** The set `{n : ℕ | n < 3}` is a term, not a type. To use it as a type, Lean coerces it to the subtype `{n : ℕ // n ∈ {n | n < 3}}`. The two have different lemmas, so the form of a statement decides which lemmas apply.

### The library around it

Each operation on sets has a membership lemma with the name `Set.mem_` and the operation: `Set.mem_inter_iff`, `Set.mem_union`, `Set.mem_compl_iff` and `Set.mem_image`. These are simp lemmas, so `simp` reduces a statement about sets to a statement in logic. The finset operations have lemmas with the prefix `Finset.mem_`. A `Finset` has a `card`, and a set has an `ncard` (a natural number) and an `encard` (a value in `ℕ∞`). Use `Finset` for a finite collection that a proof must count or sum over. Use `Set` for a collection that can be infinite. Use a subtype when the elements must form a type, for example as the domain of a function.

### Exercises

1. (A) Write the set of even integers as a predicate.
2. (A) Explain why the membership `3 ∈ {n : ℕ | n < 5}` and the statement `3 < 5` have the same proof.
3. (B) Show that $\{n \in \mathbb{N} \mid n^2 < 10\} = \{0, 1, 2, 3\}$.
4. (L) Prove that an element of both sets is in the intersection. The solution is `mem_inter_example`.
5. (L) Prove that a set is a subset of its union with another set. The solution is `subset_union_example`.
6. (L) Prove that `Finset.range 5` has five elements. The solution is `card_range_five`.

### Notes and history

The choice of sets as predicates goes back to Lean 2 and the first library of Lean 3. Mathlib keeps `Set`, `Finset` and `Fintype` as separate tools, and it has lemmas that pass between them, for example `Finset.coe_range` and `Set.toFinset`.

### Reference

<?reference?>
