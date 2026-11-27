---
title: Set.Finite, Infinite and Nat.card
kind: theory
modules:
  - Mathlib.Data.Set.Finite.Basic
explains:
  E3: [Set.Finite, Nat.card]
  E2: [Set.Infinite, Finite, Infinite, Set.ncard, Set.Finite.subset, Finite.injective_iff_surjective]
  E1: auto
families: []
requires: [V03.C03, V03.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V03/C05/Examples.lean
  - MathlibHandbook/V03/C05/Exercises.lean
  - MathlibHandbook/V03/C05/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Set.Finite, Infinite and Nat.card

### Overview

The class `Fintype` of Chapter 4 is data: it holds a finset of all elements. In a proof, that data is often not available. For example, the set of the roots of a polynomial is finite, but a program cannot list the roots of a real polynomial. Mathlib therefore has the class `Finite α`, which says only that a finite type exists in bijection with `α`, and the predicate `Set.Finite s` for a set. Their negations are `Infinite α` and `Set.Infinite s`. The counts `Nat.card` and `Set.ncard` use no instance, and give $0$ for an infinite type or set. This section gives the definitions, the closure rules and the counts.

### Definitions

**Definition (Finite).** `Finite α` is a class with one field: there is an `n` and an equivalence between `α` and `Fin n`. It is a proposition, so two proofs of it are equal.

**Definition (Finite set).** For `s : Set α`, `s.Finite` is the statement `Finite s`, where `s` is a type by the coercion to a subtype. `s.Infinite` is `¬ s.Finite`.

**Definition (Infinite).** `Infinite α` is the class that says `α` is not finite.

**Definition (Card with no data).** `Nat.card α` is the card of `α` when `α` is finite and `0` when it is infinite. For a set, `Set.ncard s` is `Nat.card s`, and `Set.encard s` is a value in `ℕ∞` that is `⊤` for an infinite set.

### Theorems and proofs

**Theorem (Closure rules).** A subset of a finite set is finite. The union, the intersection with any set, the image and the product of finite sets are finite.

*Proof.* For a subset $u \subseteq s$, the inclusion of $u$ in $s$ is injective, and a type with an injective map to a finite type is finite. For the union, the map from $s \oplus t$ to $s \cup t$ is surjective, and the image of a finite type by a surjective map is finite. The other rules are similar. $\square$

**Theorem (Infinitely many primes).** The set of the prime numbers is infinite.

*Proof.* For each $n$, a prime factor of $n! + 1$ is larger than $n$, because no number from $2$ to $n$ divides $n! + 1$. So the set is not bounded above, and a set of natural numbers that is not bounded above is infinite. $\square$

**Theorem (Injective and surjective).** For a finite type $\alpha$ and $f : \alpha \to \alpha$, $f$ is injective if and only if $f$ is surjective.

*Proof.* If $f$ is injective, the image of $\alpha$ has $|\alpha|$ elements, so it is all of $\alpha$. If $f$ is surjective, it has a right inverse $g$. The map $g$ is injective, so it is surjective, and then $f$ is the inverse of $g$. $\square$

::: mathlib
`Set.Finite` · `Mathlib.Basic.Finite.Defs`

The predicate "the set is finite". The dot notation gives the closure rules: `hs.subset h`, `hs.union ht`, `hs.image f`. `Set.toFinite s` proves it when the subtype has a `Finite` instance, and `hs.toFinset` gives a finset with the same elements.

<?decl Set.Finite?>
:::

::: mathlib
`Nat.card` · `Mathlib.SetTheory.Cardinal.Finite`

The card of a type as a natural number, with the value `0` for an infinite type. Because of that value, a lemma about `Nat.card` often needs a `Finite` hypothesis. `Nat.card_eq_fintype_card` connects it with `Fintype.card`.

<?decl Nat.card?>
:::

### Examples

**Example (Numbers below n).**

<?lean MathlibHandbook/V03/C05/Examples.lean#finite_lt?>

**Example (A subset of a union).**

<?lean MathlibHandbook/V03/C05/Examples.lean#subset_union?>

**Example (An image).**

<?lean MathlibHandbook/V03/C05/Examples.lean#image?>

**Example (All natural numbers).**

<?lean MathlibHandbook/V03/C05/Examples.lean#infinite_univ?>

**Example (Primes).**

<?lean MathlibHandbook/V03/C05/Examples.lean#primes?>

**Example (Nat.card of a finite type).**

<?lean MathlibHandbook/V03/C05/Examples.lean#nat_card?>

**Example (The card of a set).**

<?lean MathlibHandbook/V03/C05/Examples.lean#ncard?>

**Counterexample (Injective but not surjective).** On `ℕ`, the map $n \mapsto n + 1$ is injective, but no $n$ goes to $0$. So the theorem on injective and surjective maps needs a finite type.

### The library around it

`Set.finite_range` says that the range of a map from a finite type is finite. `Set.infinite_of_not_bddAbove` gives an infinite set of numbers from an unbounded set. `Set.Finite.prod` is the closure rule for products. `Infinite.of_injective` makes an infinite type from an injective map out of an infinite type, and `Finite.of_injective` is the rule in the other direction. `Set.ncard_insert_of_notMem` is the insert rule for `Set.ncard`, like the rule for finsets in Chapter 3. `Set.Finite.toFinset` and `Finset.finite_toSet` move between finite sets and finsets.

### Exercises

1. (A) Give `Nat.card ℕ` and `Set.encard (Set.univ : Set ℕ)`.
2. (A) Explain why `Finite α` is a proposition but `Fintype α` is not.
3. (B) Prove that the set of the even numbers is infinite.
4. (L) Prove that the intersection with a finite set is finite. The solution is `finite_inter_example`.
5. (L) Prove that a set that contains an infinite set is infinite. The solution is `infinite_mono_example`.
6. (L) Prove that a map from a finite type to itself is injective if and only if it is surjective. The solution is `injective_surjective_example`.
7. (L) Prove that a type with an injective map from `ℕ` is infinite. The solution is `infinite_of_injective_example`.

### Notes and history

The proof of the infinitude of the primes is in Book IX of the Elements of Euclid. The value `0` of `Nat.card` on an infinite type is a convention, like the value `0` of a division by zero. It makes `Nat.card` a total function, and a lemma adds a `Finite` hypothesis when it needs one. MIL uses `Set.Finite` in its chapter on sets and functions.

### Reference

<?reference?>
