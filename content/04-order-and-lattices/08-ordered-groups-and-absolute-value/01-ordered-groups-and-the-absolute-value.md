---
title: Ordered groups and the absolute value
kind: theory
modules:
  - Mathlib.Algebra.Order.Monoid.Defs
  - Mathlib.Algebra.Order.Group.Unbundled.Abs
explains:
  E3: [IsOrderedAddMonoid]
  E2: [add_le_add, sub_nonneg, abs_nonneg, abs_add_le, abs_sub_comm, abs_le]
  E1: [IsOrderedMonoid, add_le_add_left, add_le_add_right, add_pos, neg_le_neg, sub_le_sub, abs_neg, abs_abs, abs_lt, le_abs_self, abs_sub_le]
families: []
requires: [V04.C01, V01.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C08/Examples.lean
  - MathlibHandbook/V04/C08/Exercises.lean
  - MathlibHandbook/V04/C08/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ordered groups and the absolute value

### Overview

The numbers `ℤ`, `ℚ` and `ℝ` have an addition and an order, and the addition keeps the order: $a \le b$ gives $a + c \le b + c$. A structure with this property is an ordered additive group. Mathlib does not have a single class for it. It uses three classes side by side: `AddCommGroup α` for the algebra, `PartialOrder α` for the order, and `IsOrderedAddMonoid α` for the link between them. This is the unbundled style of the order hierarchy. The absolute value $|a| = a \sqcup (-a)$ uses the lattice structure. This section shows the classes, the lemmas for inequalities with sums and differences, and the triangle inequality.

### Definitions

**Definition (Ordered additive monoid).** Let $\alpha$ be an additive commutative monoid with a preorder. The class `IsOrderedAddMonoid α` says that $a \le b$ gives $c + a \le c + b$ and $a + c \le b + c$ for each $c$. The multiplicative version is `IsOrderedMonoid`.

**Definition (Ordered additive group).** An ordered additive group is a type with the three instances `[AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]`. A linear ordered additive group uses `LinearOrder α` in the place of `PartialOrder α`.

**Definition (Absolute value).** In a lattice with a negation, the absolute value is $|a| = a \sqcup (-a)$. In a linear order, it is $\max(a, -a)$. Mathlib writes it `|a|`, and the name of the function is `abs`.

### Theorems and proofs

**Theorem (Addition of inequalities).** In an ordered additive monoid, $a \le b$ and $c \le d$ give $a + c \le b + d$.

*Proof.* The axiom gives $a + c \le b + c$ and $b + c \le b + d$. Transitivity gives $a + c \le b + d$. $\square$

**Theorem (Difference).** In an ordered additive group, $0 \le a - b \iff b \le a$.

*Proof.* If $b \le a$, add $-b$ on the two sides: $0 = b - b \le a - b$. If $0 \le a - b$, add $b$ on the two sides: $b \le a - b + b = a$. $\square$

**Theorem (Triangle inequality).** In a linear ordered additive group, $|a + b| \le |a| + |b|$.

*Proof.* The inequalities $a \le |a|$ and $b \le |b|$ give $a + b \le |a| + |b|$. The inequalities $-a \le |a|$ and $-b \le |b|$ give $-(a + b) \le |a| + |b|$. The maximum of $a + b$ and $-(a + b)$ is thus at most $|a| + |b|$. $\square$

**Theorem (Bound of an absolute value).** In a linear ordered additive group, $|a| \le r \iff -r \le a \land a \le r$.

*Proof.* The inequality $\max(a, -a) \le r$ is equivalent to $a \le r$ and $-a \le r$, and $-a \le r$ is equivalent to $-r \le a$. $\square$

::: mathlib
`IsOrderedAddMonoid` · `Mathlib.Algebra.Order.Monoid.Defs`

The class is a `Prop` mixin with the fields `add_le_add_left` and `add_le_add_right`. It does not extend the algebra or the order, so a declaration takes the three instances as separate arguments.

<?decl IsOrderedAddMonoid?>
:::

::: mathlib
`abs_add_le` · `Mathlib.Algebra.Order.Group.Unbundled.Abs`

The lemma is the triangle inequality. The lemma `abs_sub_le` is the form with three points, $|a - c| \le |a - b| + |b - c|$, and it is in `Mathlib.Algebra.Order.Group.Abs`.

<?decl abs_add_le?>
:::

::: mathlib
`abs_le` · `Mathlib.Algebra.Order.Group.Abs`

The lemma turns a bound on `|a|` into two inequalities, and `abs_lt` does the same for a strict bound. Both are the usual first step in a proof with an epsilon.

<?decl abs_le?>
:::

### Examples

**Example (Addition of inequalities).**

<?lean MathlibHandbook/V04/C08/Examples.lean#add_le_add?>

**Example (The class).** A lemma on a general ordered group takes the three instances. The lemma `add_le_add_right` adds the same term $c$ on the left of the two sides.

<?lean MathlibHandbook/V04/C08/Examples.lean#class?>

**Example (A difference).**

<?lean MathlibHandbook/V04/C08/Examples.lean#sub_nonneg?>

**Example (Basic properties of the absolute value).**

<?lean MathlibHandbook/V04/C08/Examples.lean#abs?>

**Example (The triangle inequality).**

<?lean MathlibHandbook/V04/C08/Examples.lean#triangle?>

**Example (A bound).**

<?lean MathlibHandbook/V04/C08/Examples.lean#abs_le?>

**Example (Symmetry of the distance).**

<?lean MathlibHandbook/V04/C08/Examples.lean#dist?>

**Counterexample (An order that addition does not keep).** Give `ℤ` the order in which $a \preceq b$ if and only if $|a| < |b|$, or $|a| = |b|$ and $a \le b$. Then $-1 \preceq 1$. Add $-1$ to the two sides, and the results are $-2$ and $0$. But $|0| < |-2|$, so $-2 \preceq 0$ is false, and addition does not keep this order.

### The library around it

The lemmas for the order and the addition are in `Mathlib.Algebra.Order.Monoid.Unbundled.Basic` and in `Mathlib.Algebra.Order.Group.Unbundled.Basic`. Their hypotheses are the classes `CovariantClass` and `ContravariantClass`, and `IsOrderedAddMonoid` gives them. The multiplicative lemmas have the names with `mul` and a prime, for example `mul_le_mul'`, so that they do not clash with the lemmas of ordered rings. The ordered rings and fields use the class `IsStrictOrderedRing` in the same unbundled style. The tactics `linarith` and `positivity` prove most goals on ordered groups and fields, and `gcongr` proves goals such as `a + c ≤ b + c` from `a ≤ b`. On `ℝ`, the distance of the metric space is `dist a b = |a - b|`, by the lemma `Real.dist_eq`.

### Exercises

1. (A) Give the three instances that a lemma on a linear ordered additive group takes.
2. (A) Give the value of `|(-3 : ℤ)|` and of `|(0 : ℤ)|`.
3. (B) Show that $a \le b$ gives $-b \le -a$ in an ordered additive group.
4. (B) Show that $\bigl||a| - |b|\bigr| \le |a - b|$.
5. (B) Show that $|a| = 0$ if and only if $a = 0$.
6. (L) Prove that a sum of two positive reals is positive. The solution is `add_pos_example`.
7. (L) Prove that $|-x| = |x|$. The solution is `abs_neg_example`.
8. (L) Prove the triangle inequality for three points. The solution is `abs_sub_le_example`.

### Notes and history

Mathlib had the bundled classes `OrderedAddCommGroup` and `LinearOrderedAddCommGroup` for many years. In 2025, the library replaced them with the mixins `IsOrderedAddMonoid` and `IsOrderedMonoid`, because the bundled classes made a large number of classes for each combination of algebra and order. An older text or proof that uses the bundled names needs the three instances instead.

### Reference

<?reference?>
