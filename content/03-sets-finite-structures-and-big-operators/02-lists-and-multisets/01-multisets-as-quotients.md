---
title: Multisets as a quotient of lists
kind: theory
modules:
  - Mathlib.Data.Multiset.Defs
explains:
  E3: [Multiset, Multiset.coe_eq_coe]
  E2: [Multiset.card, Multiset.count, Multiset.cons_swap, Multiset.card_add, Multiset.count_add]
  E1: auto
families: []
requires: [V01.C02, V03.C01]
reads_with: ["MIL", "TPIL"]
lean:
  - MathlibHandbook/V03/C02/Examples.lean
  - MathlibHandbook/V03/C02/Exercises.lean
  - MathlibHandbook/V03/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Multisets as a quotient of lists

### Overview

A list `[1, 2, 2]` has an order and can repeat an element. Many statements of mathematics do not use the order, for example "the multiset of the roots of a polynomial" or "the sum of the elements". Mathlib makes the type `Multiset α` as the quotient of `List α` by the relation "is a permutation of". A function on lists that gives the same value on each permutation then gives a function on multisets. This section shows the definition, the coercion from lists, the card and the count, and the sum of a multiset.

### Definitions

**Definition (Multiset).** `Multiset α` is the quotient of `List α` by the permutation relation. The coercion `(l : Multiset α)` sends a list to its class.

**Definition (Cons and zero).** The empty multiset is `0`. For `a : α` and `m : Multiset α`, the multiset `a ::ₘ m` adds one copy of `a` to `m`. The notation `{1, 2, 2}` is a multiset made with `::ₘ`.

**Definition (Card and count).** `Multiset.card m` is the number of elements of `m`, with repetition. `Multiset.count a m` is the number of copies of `a` in `m`. The count needs decidable equality on `α`.

**Definition (Sum of multisets).** The sum `s + t` puts the elements of the two multisets together. So the multisets of `α` are a commutative monoid under `+`.

### Theorems and proofs

**Theorem (Equality of multisets).** For lists $l_1$ and $l_2$, the multisets of $l_1$ and $l_2$ are equal if and only if $l_1$ is a permutation of $l_2$.

*Proof.* This is the property of a quotient: two elements have the same class if and only if they are related. $\square$

**Theorem (Cons commutes).** For all $a$, $b$ and $m$, $a ::_m b ::_m m = b ::_m a ::_m m$.

*Proof.* Take a list $l$ for $m$. The lists $a :: b :: l$ and $b :: a :: l$ are permutations of each other by one swap. $\square$

**Theorem (Card and count of a sum).** The card and the count are additive: $|s + t| = |s| + |t|$, and the count of $a$ in $s + t$ is the sum of the two counts.

*Proof.* For lists, the length of an append is the sum of the lengths, and the count of an append is the sum of the counts. Both functions give the same value on each permutation, so the statements pass to the quotient. $\square$

::: mathlib
`Multiset.coe_eq_coe` · `Mathlib.Data.Multiset.Defs`

The statement that two lists give the same multiset if and only if they are permutations. For lists of numbers, `decide` can then check the permutation.

<?decl Multiset.coe_eq_coe?>
:::

::: mathlib
`Multiset` · `Mathlib.Data.Multiset.Defs`

The type is a `Quotient` of lists. A proof about all multisets often starts with `induction m using Multiset.induction_on`, or with `Quotient.inductionOn` to work with a list.

<?decl Multiset?>
:::

### Examples

**Example (A permutation).** The lists `[1, 2, 3]` and `[3, 1, 2]` give the same multiset.

<?lean MathlibHandbook/V03/C02/Examples.lean#coe_eq?>

**Example (Cons commutes).**

<?lean MathlibHandbook/V03/C02/Examples.lean#cons_swap?>

**Example (Multiplicity).** The multiset `{1, 1, 2}` has two copies of `1`.

<?lean MathlibHandbook/V03/C02/Examples.lean#count?>

**Example (The card of a sum).**

<?lean MathlibHandbook/V03/C02/Examples.lean#card_add?>

**Example (Remove the repetitions).** `Multiset.dedup` keeps one copy of each element. The result has no repeated element, and the next chapter makes a finset from it.

<?lean MathlibHandbook/V03/C02/Examples.lean#dedup?>

**Example (The sum of a multiset).**

<?lean MathlibHandbook/V03/C02/Examples.lean#sum?>

**Counterexample (A product with no order).** The product of a multiset needs a commutative monoid. For a list of matrices the product depends on the order, so `List.prod` has no form on multisets for a monoid that is not commutative.

### The library around it

The predicate `Multiset.Nodup` says that a multiset has no repeated element, and `Multiset.toFinset` makes a finset from a multiset. The function `Multiset.map` applies a function to each element, and `Multiset.card_map` says that it keeps the card. The sum `Multiset.sum` and the product `Multiset.prod` are the base of `Finset.sum` and `Finset.prod`. The lemma `Multiset.sum_cons` gives the sum of `a ::ₘ m`. The multiset `Multiset.range n` holds the numbers below `n` once each. A reader seldom uses lists and multisets in a proof about finite sets, but the definitions of the finsets use them, and an error message can show them.

### Exercises

1. (A) Give the card and the count of `2` for the multiset `{2, 3, 2, 2}`.
2. (A) Explain why the function "the first element of a list" does not give a function on multisets.
3. (B) Show that the count of $a$ in $m$ is at most the card of $m$.
4. (L) Prove that the card of `a ::ₘ m` is the card of `m` plus one. The solution is `card_cons_example`.
5. (L) Prove that `a ::ₘ m` has one more copy of `a` than `m`. The solution is `count_cons_self_example`.
6. (L) Prove that `a` is an element of `a ::ₘ m`. The solution is `mem_cons_example`.
7. (L) Prove that the count in a sum is the sum of the counts. The solution is `count_add_example`.

### Notes and history

The construction of multisets as a quotient of lists comes from the first library of Lean 3. It uses the quotient types of the kernel of Lean, which TPIL explains. The same construction makes finsets, so a finset is a multiset with a proof that it has no repeated element.

### Reference

<?reference?>
