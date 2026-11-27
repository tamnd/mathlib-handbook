---
title: Cosets, the index and the order of an element
kind: theory
modules:
  - Mathlib.GroupTheory.Coset.Card
  - Mathlib.GroupTheory.OrderOfElement
  - Mathlib.GroupTheory.Index
explains:
  E3: [Subgroup.card_subgroup_dvd_card, orderOf_dvd_card]
  E2: [orderOf, Subgroup.index, Subgroup.card_mul_index, pow_card_eq_one]
  E1: auto
families: []
requires: [V05.C03]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C04/Examples.lean
  - MathlibHandbook/V05/C04/Exercises.lean
  - MathlibHandbook/V05/C04/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cosets, the index and the order of an element

### Overview

The left cosets of a subgroup $H$ cut the group into parts of the same size. If $G$ is finite, the order of $H$ then divides the order of $G$. This is the theorem of Lagrange. The number of cosets is the index of $H$. The order of an element $x$ is the least $n > 0$ with $x^n = 1$, and it is the order of the subgroup that $x$ generates. So the order of an element divides the order of the group. This section shows how Mathlib states these facts with `Nat.card`, `Subgroup.index` and `orderOf`.

### Definitions

**Definition (Left coset).** For $a \in G$ and a subgroup $H$, the left coset is $aH = \{a \cdot h : h \in H\}$. Two elements $a$ and $b$ are in the same left coset if and only if $a^{-1} \cdot b \in H$. The type of the left cosets is `G ⧸ H`.

**Definition (Index).** The index $[G : H]$ is the number of left cosets of $H$. In Mathlib it is `H.index : ℕ`, and its value is $0$ when there are infinitely many cosets.

**Definition (Order of an element).** The order of $x$ is the least $n > 0$ with $x^n = 1$. In Mathlib it is `orderOf x : ℕ`, and its value is $0$ when no such $n$ exists. This is a junk value, in the sense of Volume 1.

### Theorems and proofs

**Theorem (Lagrange).** If $H$ is a subgroup of a finite group $G$, then $|H| \cdot [G : H] = |G|$. So $|H|$ divides $|G|$.

*Proof.* The left cosets are a partition of $G$, because "same coset" is an equivalence relation. The map $h \mapsto a \cdot h$ is a bijection from $H$ to $aH$, by cancellation. So $G$ is the union of $[G : H]$ disjoint sets, each of size $|H|$. $\square$

**Theorem (Order of an element).** In a finite group, the order of $x$ divides $|G|$.

*Proof.* The powers of $x$ are a subgroup with exactly $\operatorname{orderOf}(x)$ elements $1, x, \dots, x^{n-1}$. Apply the theorem of Lagrange. $\square$

**Theorem (Power of the order).** In a finite group, $x^{|G|} = 1$.

*Proof.* Write $|G| = n \cdot k$ with $n = \operatorname{orderOf}(x)$. Then $x^{|G|} = (x^n)^k = 1$. $\square$

::: mathlib
`Subgroup.card_subgroup_dvd_card` · `Mathlib.GroupTheory.Coset.Card`

The theorem of Lagrange with `Nat.card`. It needs no finiteness, because `Nat.card` of an infinite type is $0$, and each number divides $0$.

<?decl Subgroup.card_subgroup_dvd_card?>
:::

::: mathlib
`orderOf_dvd_card` · `Mathlib.GroupTheory.OrderOfElement`

The order of an element divides `Fintype.card G`. The form `orderOf_dvd_natCard` uses `Nat.card` instead.

<?decl orderOf_dvd_card?>
:::

::: mathlib
`orderOf` · `Mathlib.GroupTheory.OrderOfElement`

The definition uses `Function.minimalPeriod` of the map $y \mapsto x \cdot y$. Use the lemmas `pow_orderOf_eq_one` and `orderOf_dvd_of_pow_eq_one`, not the definition.

<?decl orderOf?>
:::

::: mathlib
`Subgroup.index` · `Mathlib.GroupTheory.Index`

The index is `Nat.card (G ⧸ H)`. The lemma `Subgroup.index_mul_card` and its partner below connect it to the order of $H$.

<?decl Subgroup.index?>
:::

::: mathlib
`Subgroup.card_mul_index` · `Mathlib.GroupTheory.Index`

The equation $|H| \cdot [G : H] = |G|$ with `Nat.card`. It holds for each group, with the junk values.

<?decl Subgroup.card_mul_index?>
:::

::: mathlib
`pow_card_eq_one` · `Mathlib.GroupTheory.OrderOfElement`

The power of the order of the group is $1$. With $G = (\mathbb{{Z}}/p)^\times$, it gives the little theorem of Fermat.

<?decl pow_card_eq_one?>
:::

### Examples

**Example (The theorem of Lagrange).**

<?lean MathlibHandbook/V05/C04/Examples.lean#lagrange?>

**Example (The index).**

<?lean MathlibHandbook/V05/C04/Examples.lean#index?>

**Example (The order of an element).**

<?lean MathlibHandbook/V05/C04/Examples.lean#order_dvd?>

**Example (The power of the order).**

<?lean MathlibHandbook/V05/C04/Examples.lean#pow_card?>

**Example (A positive order).** In a finite group the junk value $0$ does not occur.

<?lean MathlibHandbook/V05/C04/Examples.lean#order_pos?>

### The library around it

Mathlib has two ways to count: `Fintype.card` needs an instance `Fintype`, and `Nat.card` works on each type. New lemmas prefer `Nat.card`. The cosets are in `Mathlib.GroupTheory.Coset.Defs`, with the relation `QuotientGroup.leftRel`. The right cosets use `MulOpposite`. The file `Mathlib.GroupTheory.OrderOfElement` also has `orderOf_pow`, the order of a power, and `IsOfFinOrder`, the predicate for an element of finite order. For an index, `Subgroup.index_dvd_card` and the tower law `Subgroup.relIndex_mul_index` are often useful.

### Exercises

1. (A) Give the value of `orderOf x` when $x$ has infinite order.
2. (A) Give the index of the bottom subgroup of a finite group $G$.
3. (B) Show that a group of prime order is cyclic.
4. (B) Show that a subgroup of index $2$ contains the square of each element.
5. (L) Prove that $x^{\operatorname{orderOf}(x)} = 1$. The solution is `pow_order_example`.
6. (L) Prove that $x^n = 1$ gives that the order of $x$ divides $n$. The solution is `order_dvd_example`.
7. (L) Prove that the order of $x$ is $1$ if and only if $x = 1$. The solution is `order_one_example`.
8. (L) Prove that the index of $H$ divides the order of $G$. The solution is `index_dvd_example`.

### Notes and history

Lagrange proved a special case in 1771, for the permutations of the roots of a polynomial. The general form for abstract groups came much later, with the work of Galois, Cauchy and Jordan. The converse is false: the alternating group $A_4$ has order $12$ but no subgroup of order $6$.

### Reference

<?reference?>
