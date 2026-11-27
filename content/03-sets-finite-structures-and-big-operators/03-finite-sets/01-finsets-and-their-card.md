---
title: Finsets and their card
kind: theory
modules:
  - Mathlib.Data.Finset.Card
explains:
  E3: [Finset, Finset.card_union_add_card_inter]
  E2: [Finset.card, Finset.card_insert_of_notMem, Finset.filter, Finset.card_image_of_injective, Finset.card_powerset, Finset.induction_on]
  E1: auto
families: []
requires: [V03.C01, V03.C02]
reads_with: ["MIL", "MSG"]
lean:
  - MathlibHandbook/V03/C03/Examples.lean
  - MathlibHandbook/V03/C03/Exercises.lean
  - MathlibHandbook/V03/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Finsets and their card

### Overview

The type `Set α` of Chapter 1 holds any set, finite or not. A set has no card that a program can compute, because a predicate can be any proposition. The type `Finset α` holds the finite sets in a form that has data: a multiset with no repeated element. So `Finset.card` is a number, and for numbers `decide` can check a statement about a small finset. This section gives the structure, the operations insert, filter and image, and the counting rules for unions, subsets and power sets.

### Definitions

**Definition (Finset).** A term of `Finset α` is a structure with two fields: `val`, a multiset of `α`, and `nodup`, a proof that `val` has no repeated element. Two finsets are equal when they have the same elements. This is `Finset.ext`.

**Definition (Card).** `Finset.card s`, written `s.card` or `#s`, is the card of the multiset `s.val`.

**Definition (Insert, filter and image).** For `a : α`, `insert a s` adds `a` to `s`. The notation `{1, 2, 3}` uses insert. For a decidable predicate `p`, `s.filter p` is the finset of the elements of `s` that satisfy `p`. For `f : α → β`, `s.image f` is the finset of the values `f a` for `a ∈ s`. Insert and image need decidable equality, because they remove the repetitions.

**Definition (Range and power set).** `Finset.range n` is the finset of the numbers $0, 1, \ldots, n - 1$. `s.powerset` is the finset of the subsets of `s`.

### Theorems and proofs

**Theorem (Card of an insert).** If $a \notin s$, then $|s \cup \{a\}| = |s| + 1$.

*Proof.* The multiset of `insert a s` is `a ::ₘ s.val`, because $a$ is not in $s$. The card of a cons is the card plus one. $\square$

**Theorem (Inclusion and exclusion).** For finsets $s$ and $t$, $|s \cup t| + |s \cap t| = |s| + |t|$.

*Proof.* Use induction on $s$. For $s = \emptyset$ both sides are $|t|$. For an insert of $a \notin s$, if $a \in t$ the union keeps its card and the intersection gets one more element. If $a \notin t$ the union gets one more element and the intersection keeps its card. In both cases the two sides grow by one. $\square$

**Theorem (Card of the power set).** $|\mathcal{P}(s)| = 2^{|s|}$.

*Proof.* Use induction on $s$. A subset of $s \cup \{a\}$ either does not contain $a$, or is a subset of $s$ with $a$ added. The two kinds have the same number, so the count doubles. $\square$

::: mathlib
`Finset` · `Mathlib.Data.Finset.Defs`

The structure of the finite sets. The coercion `(s : Set α)` sends a finset to its set, and `Finset.coe_insert` and other `coe` lemmas move the operations across it.

<?decl Finset?>
:::

::: mathlib
`Finset.card_union_add_card_inter` · `Mathlib.Data.Finset.Card`

The rule of inclusion and exclusion for two finsets. The form with a sum on both sides needs no subtraction of natural numbers, so `omega` can use it easily.

<?decl Finset.card_union_add_card_inter?>
:::

### Examples

**Example (A finset of numbers).**

<?lean MathlibHandbook/V03/C03/Examples.lean#decide?>

**Example (Insert).**

<?lean MathlibHandbook/V03/C03/Examples.lean#insert?>

**Example (Filter).** The multiples of three below ten are $0, 3, 6, 9$.

<?lean MathlibHandbook/V03/C03/Examples.lean#filter?>

**Example (Image).** The map $n \mapsto 2n$ is injective, so the image has the same card.

<?lean MathlibHandbook/V03/C03/Examples.lean#image?>

**Example (Inclusion and exclusion).**

<?lean MathlibHandbook/V03/C03/Examples.lean#incl_excl?>

**Example (Power set).**

<?lean MathlibHandbook/V03/C03/Examples.lean#powerset?>

**Example (Induction).** The tactic `induction s using Finset.induction_on` gives a case for the empty finset and a case for `insert a s` with `a ∉ s`.

<?lean MathlibHandbook/V03/C03/Examples.lean#induction?>

**Counterexample (An image that is smaller).** For $f(n) = n \bmod 2$ and $s = \{0, 1, 2, 3\}$, the image is $\{0, 1\}$. So the card of an image can be smaller when $f$ is not injective. The general rule is `Finset.card_image_le`.

### The library around it

The order lemmas `Finset.card_le_card` and `Finset.card_lt_card` compare the cards of a subset and a set. `Finset.card_sdiff` gives the card of a difference, and `Finset.card_union_of_disjoint` the card of a disjoint union. `Finset.card_eq_zero` says that only the empty finset has card zero, and `Finset.Nonempty` is the predicate "has an element". The intervals `Finset.Icc a b` and `Finset.Ico a b` of a locally finite order are finsets, and `Nat.card_Icc` gives their card. The coercion to `Set α` and the lemma `Finset.coe_insert` connect this chapter with Chapter 1. When a proof needs a finset from a finite set, `Set.Finite.toFinset` of Chapter 5 makes it.

### Exercises

1. (A) Give the card of `(Finset.range 6).filter Even`.
2. (A) Explain why `Finset.image` needs decidable equality on the target type and `Finset.filter` does not.
3. (B) Use inclusion and exclusion to show that two subsets of $\{0, \ldots, 9\}$ with six elements each meet.
4. (L) Prove that a subset has a card that is not larger. The solution is `card_le_of_subset_example`.
5. (L) Prove that the card of a union is at most the sum of the cards. The solution is `card_union_le_example`.
6. (L) Prove that a filter does not make a finset larger. The solution is `card_filter_le_example`.
7. (L) Prove that the card of a product is the product of the cards. The solution is `card_product_example`.

### Notes and history

Finsets come from the Lean 3 library. Other systems often keep one type of sets and a predicate "is finite". Mathlib keeps both: `Finset α` for the computation and the sums, and `Set.Finite` for the statements about sets. MIL uses finsets for its chapter on combinatorics, and MSG shows how decidability lets `decide` count small cases.

### Reference

<?reference?>
