---
title: Lattices and bounded lattices
kind: theory
modules:
  - Mathlib.Order.Defs.Lattice
  - Mathlib.Order.BoundedOrder.Basic
explains:
  E3: [Lattice]
  E2: [sup_le_iff, le_inf_iff, DistribLattice, BoundedOrder, le_top, bot_le]
  E1: [SemilatticeSup, SemilatticeInf, sup_le, le_sup_left, le_sup_right, inf_le_left, inf_le_right, le_inf, sup_comm, inf_comm, sup_inf_self, inf_sup_left, OrderTop, OrderBot]
families: []
requires: [V04.C01]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C03/Examples.lean
  - MathlibHandbook/V04/C03/Exercises.lean
  - MathlibHandbook/V04/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lattices and bounded lattices

### Overview

A lattice is a partial order in which any two elements have a least upper bound and a greatest lower bound. Mathlib writes the least upper bound as $a \sqcup b$ (sup) and the greatest lower bound as $a \sqcap b$ (inf). The sets of a type, the propositions, and each linear order are lattices. A bounded lattice also has a least element $\bot$ and a greatest element $\top$. In Mathlib, the order is primary, and $\sqcup$ and $\sqcap$ are operations with axioms in terms of $\le$. This section shows the classes, the main lemmas, and the lattices that a reader meets most often.

### Definitions

**Definition (Join semilattice).** A `SemilatticeSup` is a partial order with an operation $\sqcup$ such that $a \le a \sqcup b$, $b \le a \sqcup b$, and $a \le c$ and $b \le c$ give $a \sqcup b \le c$.

**Definition (Meet semilattice).** A `SemilatticeInf` is a partial order with an operation $\sqcap$ such that $a \sqcap b \le a$, $a \sqcap b \le b$, and $c \le a$ and $c \le b$ give $c \le a \sqcap b$.

**Definition (Lattice).** A `Lattice` is a join semilattice and a meet semilattice on the same partial order.

**Definition (Distributive lattice).** A `DistribLattice` is a lattice in which $(a \sqcup b) \sqcap (a \sqcup c) \le a \sqcup (b \sqcap c)$ for all $a$, $b$ and $c$.

**Definition (Bounded order).** An `OrderBot` has an element $\bot$ with $\bot \le a$ for each $a$. An `OrderTop` has an element $\top$ with $a \le \top$ for each $a$. A `BoundedOrder` has both.

### Theorems and proofs

**Theorem (Universal property of the sup).** In a join semilattice, $a \sqcup b \le c \iff a \le c \land b \le c$.

*Proof.* If $a \sqcup b \le c$, then $a \le a \sqcup b \le c$ and $b \le a \sqcup b \le c$. The other direction is the third axiom. $\square$

**Theorem (Commutativity).** In a join semilattice, $a \sqcup b = b \sqcup a$.

*Proof.* By antisymmetry, it is sufficient to show $a \sqcup b \le b \sqcup a$ and the inequality in the other direction. By the universal property, $a \sqcup b \le b \sqcup a$ holds because $a \le b \sqcup a$ and $b \le b \sqcup a$. The other inequality has the same proof. $\square$

**Theorem (Absorption).** In a lattice, $a \sqcup (a \sqcap b) = a$.

*Proof.* The inequality $a \le a \sqcup (a \sqcap b)$ is an axiom. For the other inequality, $a \le a$ and $a \sqcap b \le a$, so $a \sqcup (a \sqcap b) \le a$ by the universal property. $\square$

::: mathlib
`Lattice` · `Mathlib.Order.Defs.Lattice`

The class extends `SemilatticeSup` and `SemilatticeInf`. The lemmas of the sup have the names `le_sup_left`, `le_sup_right` and `sup_le`, and the lemmas of the inf have the names `inf_le_left`, `inf_le_right` and `le_inf`.

<?decl Lattice?>
:::

::: mathlib
`sup_le_iff` · `Mathlib.Order.Defs.Lattice`

The lemma is a `simp` lemma. So `simp` splits a goal `a ⊔ b ≤ c` into two goals. The lemma `le_inf_iff` does the same for `a ≤ b ⊓ c`.

<?decl sup_le_iff?>
:::

::: mathlib
`BoundedOrder` · `Mathlib.Order.BoundedOrder.Basic`

The class extends `OrderTop` and `OrderBot`. The lemmas `bot_le` and `le_top` have no explicit argument, so `bot_le` is a proof of `⊥ ≤ a` for the `a` of the goal.

<?decl BoundedOrder?>
:::

### Examples

**Example (The least upper bound).**

<?lean MathlibHandbook/V04/C03/Examples.lean#sup_le?>

**Example (The greatest lower bound).**

<?lean MathlibHandbook/V04/C03/Examples.lean#le_inf_iff?>

**Example (A linear order).** In `ℕ`, the sup is the maximum and the inf is the minimum, and `decide` computes them.

<?lean MathlibHandbook/V04/C03/Examples.lean#nat?>

**Example (The lattice of sets).** For sets, `⊔` and `⊓` are the union and the intersection by definition.

<?lean MathlibHandbook/V04/C03/Examples.lean#set?>

**Example (Bounds).**

<?lean MathlibHandbook/V04/C03/Examples.lean#bounded?>

**Example (Distributivity).**

<?lean MathlibHandbook/V04/C03/Examples.lean#distrib?>

**Counterexample (A lattice that is not distributive).** The subgroups of the Klein four group are a lattice. Let $a$, $b$ and $c$ be its three subgroups of order 2. Then $a \sqcap (b \sqcup c) = a$, but $(a \sqcap b) \sqcup (a \sqcap c) = \bot$.

### The library around it

The sets, the finite sets, the propositions, the subgroups and the filters are lattices, and the lemmas of this section apply to each of them. For sets, Mathlib uses the notation `∪` and `∩`, and the two notations are equal by `rfl`. A linear order is a distributive lattice by an instance, so `max` and `min` are `⊔` and `⊓`. The class `BooleanAlgebra` adds a complement to a distributive lattice. The predicate `Disjoint a b` is in `Mathlib.Order.Disjoint`, and in a lattice with `⊥` the lemma `disjoint_iff` states that it means $a \sqcap b = \bot$. The tactic `simp` with `sup_le_iff` and `le_inf_iff` proves many goals on lattices.

### Exercises

1. (A) Give the sup and the inf of `{1, 2}` and `{2, 3}` in the lattice of the sets of `ℕ`.
2. (A) Give the sup and the inf of $4$ and $6$ in `ℕ` with the divisibility order.
3. (B) Show that $a \le b \iff a \sqcup b = b$ in a join semilattice.
4. (B) Show that $\sqcup$ is associative.
5. (B) Show that a linear order is a distributive lattice.
6. (L) Prove that $a \sqcup b = b \sqcup a$. The solution is `sup_comm_example`.
7. (L) Prove that $a \sqcap b \le a \sqcup b$. The solution is `inf_le_sup_example`.
8. (L) Prove the absorption law $a \sqcup a \sqcap b = a$. The solution is `sup_inf_absorb_example`.

### Notes and history

Dedekind studied lattices in 1897 under the name Dualgruppe, and Birkhoff made the theory a field of algebra with his book of 1940. Mathlib defines a lattice from the order and not from the algebraic laws, because most lattices in mathematics come with an order first.

### Reference

<?reference?>
