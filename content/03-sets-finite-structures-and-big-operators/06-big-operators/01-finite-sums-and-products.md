---
title: Finite sums and products
kind: theory
modules:
  - Mathlib.Algebra.BigOperators.Group.Finset.Basic
explains:
  E3: [Finset.sum, Finset.sum_range_succ]
  E2: [Finset.prod, Finset.prod_range_succ, Finset.sum_range_id_mul_two, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_comm, Finset.sum_le_sum, Finset.card_eq_sum_ones]
  E1: auto
families: []
requires: [V03.C02, V03.C03]
reads_with: ["MIL", "MSG"]
lean:
  - MathlibHandbook/V03/C06/Examples.lean
  - MathlibHandbook/V03/C06/Exercises.lean
  - MathlibHandbook/V03/C06/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Finite sums and products

### Overview

A sum such as $1 + 2 + \cdots + n$ or a product such as $n!$ is a big operator. In Mathlib, the sum is over a finset, not over a list. So the sum does not depend on an order, and it needs a commutative monoid. The notation `∑ i ∈ s, f i` is `Finset.sum s f`, and `∏ i ∈ s, f i` is `Finset.prod s f`. Most proofs about the sum over `Finset.range n` use induction on `n` with the lemma `Finset.sum_range_succ`. This section gives the definitions, the induction, the linear rules, the order rule and the double sum.

### Definitions

**Definition (Sum and product over a finset).** For a commutative monoid `β`, a finset `s : Finset α` and `f : α → β`, `Finset.prod s f` is the product of the multiset `s.val.map f`. `Finset.sum s f` is the same for an additive commutative monoid. The lemmas for sums come from the lemmas for products with the attribute `to_additive`.

**Definition (Notation).** The notation `∑ i ∈ s, f i` is a sum over `s`, and `∑ i, f i` is a sum over `Finset.univ` of a finite type. The notation `∏` is the same for products. The notation needs `open Finset` or the namespace `BigOperators` in old files.

**Definition (Range).** `Finset.range n` is $\{0, \ldots, n - 1\}$. So `∑ i ∈ range n, f i` is $f(0) + \cdots + f(n - 1)$.

### Theorems and proofs

**Theorem (One more term).** $\sum_{i < n + 1} f(i) = \sum_{i < n} f(i) + f(n)$.

*Proof.* The finset `range (n + 1)` is `insert n (range n)`, and $n \notin$ `range n`. The sum over an insert of a new element is the sum plus the new term. $\square$

**Theorem (Gauss).** $2 \sum_{i < n} i = n(n - 1)$.

*Proof.* Use induction on $n$. For $n = 0$ both sides are $0$. For $n + 1$, the left side grows by $2n$, and $(n + 1) n - n(n - 1) = 2n$. $\square$

**Theorem (Linear rules).** $\sum (f + g) = \sum f + \sum g$, and $c \sum f = \sum c f$ in a semiring.

*Proof.* Use induction on the finset, with the rule for an insert. $\square$

**Theorem (Double sums).** $\sum_{i \in s} \sum_{j \in t} f(i, j) = \sum_{j \in t} \sum_{i \in s} f(i, j)$.

*Proof.* Both sides are the sum over the product $s \times t$. $\square$

::: mathlib
`Finset.sum` · `Mathlib.Algebra.BigOperators.Group.Finset.Defs`

The sum over a finset. The target type must be an additive commutative monoid. For a sum over an infinite type with finite support, see `finsum` and the `Finsupp.sum` of Chapter 7.

<?decl Finset.sum?>
:::

::: mathlib
`Finset.sum_range_succ` · `Mathlib.Algebra.BigOperators.Group.Finset.Basic`

The step of an induction on `n` for a sum over `range n`. After the `rw`, the induction hypothesis rewrites the first term, and `ring` or `omega` closes the goal.

<?decl Finset.sum_range_succ?>
:::

### Examples

**Example (A small sum).** $0 + 1 + 4 + 9 + 16 = 30$.

<?lean MathlibHandbook/V03/C06/Examples.lean#notation?>

**Example (Gauss).**

<?lean MathlibHandbook/V03/C06/Examples.lean#gauss?>

**Example (Odd numbers).** The sum of the first $n$ odd numbers is $n^2$. This is the usual pattern of an induction.

<?lean MathlibHandbook/V03/C06/Examples.lean#induction?>

**Example (Linear rules).**

<?lean MathlibHandbook/V03/C06/Examples.lean#linear?>

**Example (Factorial).**

<?lean MathlibHandbook/V03/C06/Examples.lean#factorial?>

**Example (Card as a sum).**

<?lean MathlibHandbook/V03/C06/Examples.lean#card?>

**Example (Order).**

<?lean MathlibHandbook/V03/C06/Examples.lean#le?>

**Counterexample (Subtraction in ℕ).** The Gauss formula has the form $2 \sum i = n(n - 1)$ and not $\sum i = n(n - 1)/2$. In `ℕ`, the subtraction and the division cut, so a form with no division is easier to use. The rule `Finset.sum_sub_distrib` needs an additive group, and it is false in `ℕ` in general.

### The library around it

`Finset.sum_const` and `Finset.prod_const` give the sum and the product of a constant. `Finset.sum_filter` changes a sum over a filter into a sum with an `if`. `Finset.sum_bij` and `Finset.sum_nbij` change the index by a bijection, and `Finset.sum_congr` changes the terms. `Finset.sum_product` and `Finset.sum_sigma` give the sums over products and dependent pairs. `Finset.sum_nonneg` and `Finset.abs_sum_le_sum_abs` are order rules. `Finset.sum_mul_sq_le_sq_mul_sq` is the inequality of Cauchy and Schwarz. `geom_sum_eq` gives the sum of a geometric progression in a field. The tactic `simp` knows `Finset.sum_range_zero` and `Finset.sum_range_succ`, and `decide` can compute a small sum of numbers.

### Exercises

1. (A) Write $\sum_{k=1}^{n} k^2$ as a sum over `Finset.range`.
2. (A) Explain why `Finset.sum` needs a commutative monoid and `List.sum` does not.
3. (B) Prove that $\sum_{i < n} 2^i = 2^n - 1$ in `ℕ`. Use the form $\sum_{i < n} 2^i + 1 = 2^n$.
4. (L) Prove the rule for the sum of a constant. The solution is `sum_const_example`.
5. (L) Prove that the product of a constant is a power. The solution is `prod_const_example`.
6. (L) Prove that two finite sums can change places. The solution is `sum_comm_example`.
7. (L) Prove that four times the sum of the cubes of $0, \ldots, n$ is $(n(n + 1))^2$. The solution is `sum_cubes_example`.

### Notes and history

The story says that Gauss found the sum of $1$ to $100$ as a child, with the pairs $1 + 100$, $2 + 99$ and so on. The notation $\sum$ comes from Euler. In Mathlib, the lemmas for sums are made from the lemmas for products by `to_additive`, so each lemma has two names. MIL uses big operators in its chapters on induction and on combinatorics.

### Reference

<?reference?>
