---
title: Preorders, partial orders and linear orders
kind: theory
modules:
  - Mathlib.Order.Defs.PartialOrder
  - Mathlib.Order.Defs.LinearOrder
explains:
  E3: [PartialOrder, LinearOrder]
  E2: [Preorder, le_antisymm, lt_iff_le_not_ge, le_total, not_lt]
  E1: [le_refl, le_trans, lt_irrefl, lt_of_le_of_lt, lt_of_lt_of_le, le_antisymm_iff, min_le_left, le_max_left]
families: []
requires: [V01]
reads_with: ["MIL", "TPIL"]
lean:
  - MathlibHandbook/V04/C01/Examples.lean
  - MathlibHandbook/V04/C01/Exercises.lean
  - MathlibHandbook/V04/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Preorders, partial orders and linear orders

### Overview

An order on a type is a relation `≤` with some axioms. Mathlib has a class for each set of axioms. A `Preorder` has a reflexive and transitive `≤`. A `PartialOrder` adds antisymmetry. A `LinearOrder` adds totality, so any two elements are comparable. Each class extends the class before it, so a lemma for a preorder applies to a partial order and to a linear order. The strict relation `<` is a field of the class, but an axiom fixes its meaning in terms of `≤`. This section shows the three classes, the definition of `<`, and the lemmas that a proof uses most often.

### Definitions

**Definition (Preorder).** A preorder on a type $\alpha$ is a relation $\le$ such that $a \le a$ for each $a$, and $a \le b$ and $b \le c$ give $a \le c$. The class `Preorder α` also has a relation $<$ and the axiom $a < b \iff a \le b \land \lnot (b \le a)$.

**Definition (Partial order).** A partial order is a preorder in which $a \le b$ and $b \le a$ give $a = b$. This property is antisymmetry.

**Definition (Linear order).** A linear order is a partial order in which $a \le b$ or $b \le a$ for any two elements. The class `LinearOrder α` also has the functions `min` and `max`, and a decision procedure for `≤`, `<` and `=`.

### Theorems and proofs

**Theorem (Irreflexivity).** In a preorder, $\lnot (a < a)$.

*Proof.* If $a < a$, then the axiom of $<$ gives $\lnot (a \le a)$. This is false by reflexivity. $\square$

**Theorem (Mixed transitivity).** In a preorder, $a < b$ and $b \le c$ give $a < c$.

*Proof.* From $a < b$ there is $a \le b$, so $a \le c$ by transitivity. If $c \le a$, then $b \le c \le a$ gives $b \le a$, and this contradicts $a < b$. So $\lnot (c \le a)$, and $a < c$. $\square$

**Theorem (Negation of a strict inequality).** In a linear order, $\lnot (a < b) \iff b \le a$.

*Proof.* If $b \le a$, then $a < b$ gives $\lnot (b \le a)$, a contradiction. Conversely, suppose $\lnot (a < b)$. By totality, $a \le b$ or $b \le a$. In the second case the proof is complete. In the first case, $\lnot (a < b)$ and $a \le b$ give $b \le a$ by the axiom of $<$. $\square$

::: mathlib
`PartialOrder` · `Mathlib.Order.Defs.PartialOrder`

The class extends `Preorder` with the field `le_antisymm`. The lemma `le_antisymm` takes the two inequalities and gives the equality. The lemma `le_antisymm_iff` states the equivalence, and it is the usual way to prove an equality with two inequalities.

<?decl PartialOrder?>
:::

::: mathlib
`LinearOrder` · `Mathlib.Order.Defs.LinearOrder`

The class has the field `le_total` and the decision procedures. So `if a ≤ b then x else y` is a correct term on each linear order. The lemmas `not_lt` and `not_le` turn a negated inequality into an inequality.

<?decl LinearOrder?>
:::

::: mathlib
`lt_iff_le_not_ge` · `Mathlib.Order.Defs.PartialOrder`

This lemma is the axiom that links `<` and `≤` in a preorder. It is a lemma, not a definition, so `<` on `ℕ` or `ℝ` can have its own definition, and the lemma then states the link.

<?decl lt_iff_le_not_ge?>
:::

### Examples

**Example (Transitivity).** The lemma `le_trans` chains two inequalities in any preorder.

<?lean MathlibHandbook/V04/C01/Examples.lean#preorder?>

**Example (Antisymmetry).** On `ℕ`, two inequalities give an equality.

<?lean MathlibHandbook/V04/C01/Examples.lean#antisymm?>

**Example (The strict order).**

<?lean MathlibHandbook/V04/C01/Examples.lean#lt?>

**Counterexample (A partial order that is not linear).** The subsets of `ℕ` with `⊆` are a partial order. The sets `{0}` and `{1}` are not comparable, so the order is not linear.

<?lean MathlibHandbook/V04/C01/Examples.lean#not_linear?>

**Example (Totality).** On `ℝ`, any two numbers are comparable.

<?lean MathlibHandbook/V04/C01/Examples.lean#total?>

**Example (A negated inequality).**

<?lean MathlibHandbook/V04/C01/Examples.lean#not_lt?>

**Example (Minimum and maximum).**

<?lean MathlibHandbook/V04/C01/Examples.lean#min_max?>

### The library around it

The classes are in `Mathlib.Order.Defs.PartialOrder` and `Mathlib.Order.Defs.LinearOrder`, and they have few imports. The names of the lemmas follow a pattern. A name such as `lt_of_le_of_lt` gives the conclusion first and then the hypotheses in order. The dot notation `h.trans` is a short form of `le_trans h`, and `h.le` turns `h : a < b` into `a ≤ b`. The tactic `order` proves many goals that follow from the axioms of a partial order, and `omega` and `linarith` prove goals on `ℕ`, `ℤ` and `ℝ`. The dual order `OrderDual α` reverses `≤`, so each lemma about lower bounds has a twin about upper bounds. A theorem about `<` in a linear order often comes from the lemma about `≤` and `not_le`.

### Exercises

1. (A) State the three axioms of a partial order.
2. (A) Give a preorder that is not a partial order.
3. (B) Show that in a preorder, $a < b$ and $b < c$ give $a < c$.
4. (B) Show that the divisibility relation on `ℕ` is a partial order and is not a linear order.
5. (B) Show that in a linear order, $\min(a, b) \le \max(a, b)$.
6. (L) Prove that $a < b$ and $b \le c$ give $a < c$ in a preorder. The solution is `lt_of_lt_of_le_example`.
7. (L) Prove that $a \le b$ and $b \le a$ give $b = a$ in a partial order. The solution is `eq_of_le_of_le_example`.
8. (L) Prove that $b \le \max(a, b)$ in a linear order. The solution is `le_max_example`.

### Notes and history

The axioms of a partial order go back to the work of Peirce and Schröder on the algebra of logic, and Hausdorff used them in his book on set theory in 1914. In Mathlib, the classes were first in the core library of Lean 3, and they moved to Mathlib with the port to Lean 4. The axiom for `<` in a preorder lets each type keep its own definition of the strict order.

### Reference

<?reference?>
