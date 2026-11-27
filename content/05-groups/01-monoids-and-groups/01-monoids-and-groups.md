---
title: Monoids and groups
kind: theory
modules:
  - Mathlib.Algebra.Group.Defs
  - Mathlib.Algebra.Group.Basic
explains:
  E3: [Group]
  E2: [Monoid, CommGroup, inv_mul_cancel, mul_inv_rev, mul_left_cancel]
  E1: auto
families: []
requires: [V01.C04, V01.C06]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C01/Examples.lean
  - MathlibHandbook/V05/C01/Exercises.lean
  - MathlibHandbook/V05/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Monoids and groups

### Overview

A group is a set with a product, a unit and inverses that obey three axioms. Mathlib builds the class `Group` on a chain of smaller classes. A semigroup has an associative product, a monoid adds a unit, and a group adds an inverse with `a⁻¹ * a = 1`. Each lemma about a group is proved once, at the smallest class where it holds. This section shows the chain of classes, the first lemmas about inverses and cancellation, the additive copy of each lemma, and the tactic `group`.

### Definitions

**Definition (Monoid).** A monoid is a type $M$ with an associative product and an element $1$, such that $1 \cdot a = a$ and $a \cdot 1 = a$ for each $a$. In Mathlib, `Monoid M` also gives the power `a ^ n` for `n : ℕ`.

**Definition (Group).** A group is a monoid $G$ with a map $a \mapsto a^{-1}$ such that $a^{-1} \cdot a = 1$ for each $a$. Mathlib also puts the division $a / b$ and the power $a ^ n$ for `n : ℤ` in the class, with axioms that say that they have the usual values.

**Definition (Commutative group).** A commutative group is a group with $a \cdot b = b \cdot a$ for all $a$ and $b$. The class is `CommGroup G`.

**Definition (Additive group).** An additive group has the operation $+$, the unit $0$ and the inverse $-a$. The class `AddGroup A` is the additive copy of `Group`. Mathlib does not prove its lemmas again. The attribute `to_additive` makes each additive lemma from the multiplicative lemma, and it changes the name: `mul` becomes `add`, `inv` becomes `neg` and `one` becomes `zero`.

### Theorems and proofs

**Theorem (Right inverse).** In a group, $a \cdot a^{-1} = 1$.

*Proof.* Put $b = a^{-1}$. Then $b^{-1} \cdot b = 1$. So $a \cdot b = 1 \cdot (a \cdot b) = (b^{-1} \cdot b) \cdot (a \cdot b) = b^{-1} \cdot ((b \cdot a) \cdot b) = b^{-1} \cdot b = 1$. $\square$

**Theorem (Cancellation).** If $a \cdot b = a \cdot c$, then $b = c$.

*Proof.* Multiply both sides on the left by $a^{-1}$ and use associativity. Then $b = a^{-1} \cdot a \cdot b = a^{-1} \cdot a \cdot c = c$. $\square$

**Theorem (Inverse of a product).** $(a \cdot b)^{-1} = b^{-1} \cdot a^{-1}$.

*Proof.* The product $(a \cdot b) \cdot (b^{-1} \cdot a^{-1})$ is $1$ by associativity. An inverse is unique, because cancellation gives $c = d$ from $x \cdot c = 1 = x \cdot d$. $\square$

::: mathlib
`Group` · `Mathlib.Algebra.Group.Defs`

The class extends `DivInvMonoid`, which has the inverse, the division and the integer power. The one new axiom is `inv_mul_cancel`. The lemma `mul_inv_cancel` for the other side is a theorem, not an axiom.

<?decl Group?>
:::

::: mathlib
`inv_mul_cancel` · `Mathlib.Algebra.Group.Defs`

The axiom of the inverse. Its additive copy is `neg_add_cancel`. Old versions of Mathlib called it `mul_left_inv`.

<?decl inv_mul_cancel?>
:::

::: mathlib
`mul_inv_rev` · `Mathlib.Algebra.Group.DivInvMonoid`

The lemma holds in each `DivisionMonoid`, so it also holds for the units of a ring. The `rev` in the name says that the order of the factors reverses.

<?decl mul_inv_rev?>
:::

::: mathlib
`mul_left_cancel` · `Mathlib.Algebra.Group.Semigroup`

The lemma needs only the class `IsLeftCancelMul`. A group is an instance, and so is the monoid `ℕ` under addition, with the additive copy `add_left_cancel`.

<?decl mul_left_cancel?>
:::

::: mathlib
`Monoid` · `Mathlib.Algebra.Group.Monoid`

The class has the fields `one_mul`, `mul_one` and the power `npow` with its axioms. A monoid need not have inverses: `ℕ` under multiplication is a monoid.

<?decl Monoid?>
:::

::: mathlib
`CommGroup` · `Mathlib.Algebra.Group.Defs`

The class extends `Group` and `CommMonoid`. A lemma that needs commutativity, such as `mul_mul_mul_comm`, asks for `CommMonoid` or `CommGroup`.

<?decl CommGroup?>
:::

### Examples

**Example (The axioms).** The three axioms of a group are three lemmas.

<?lean MathlibHandbook/V05/C01/Examples.lean#group_axioms?>

**Example (Inverse of a product).**

<?lean MathlibHandbook/V05/C01/Examples.lean#mul_inv_rev?>

**Example (Cancellation).**

<?lean MathlibHandbook/V05/C01/Examples.lean#cancel?>

**Example (The additive copy).** The lemma `neg_add_cancel` is the additive copy of `inv_mul_cancel`.

<?lean MathlibHandbook/V05/C01/Examples.lean#additive?>

**Example (A commutative group).** The proof rewrites with `mul_comm` and then cancels.

<?lean MathlibHandbook/V05/C01/Examples.lean#comm_group?>

**Example (The tactic group).** The tactic `group` normalizes the two sides with the axioms of a group.

<?lean MathlibHandbook/V05/C01/Examples.lean#group_tactic?>

### The library around it

The classes are in `Mathlib.Algebra.Group.Defs` and the files next to it. The lemmas are in `Mathlib.Algebra.Group.Basic`. The names follow the shape of the statement: `mul_inv_cancel` is $a \cdot a^{-1} = 1$, and `inv_mul_cancel` is $a^{-1} \cdot a = 1$. To find a lemma, write its statement and use `exact?`. For an equation that follows from the axioms only, use `group`. In a commutative group with additive notation, use `abel`. With the multiplicative notation, `simp only [mul_comm, mul_left_comm, mul_assoc]` often works. Each additive lemma has its multiplicative lemma, so search for one name and change `mul` to `add` to get the other.

### Exercises

1. (A) Name the class of Mathlib for a type with an associative product and a unit, but with no inverse.
2. (A) Give the additive name of the lemma `mul_inv_rev`.
3. (B) Prove that the unit of a monoid is unique.
4. (B) Show that a group in which $a \cdot a = 1$ for each $a$ is commutative.
5. (L) Prove that $(a^{-1})^{-1} = a$ in a group. The solution is `inv_inv_example`.
6. (L) Prove that $a \cdot b = 1$ gives $a^{-1} = b$. The solution is `inv_unique_example`.
7. (L) Prove that $-(a + b) = -b + -a$ in an additive group. The solution is `add_neg_rev_example`.
8. (L) Prove that conjugation by $g$ respects products. The solution is `conj_mul_example`.

### Notes and history

The axioms with one unit and one inverse on one side only go back to the work of Dickson and Huntington near 1905. Mathlib takes the left inverse as the axiom and proves the right inverse. The attribute `to_additive` was written for Lean 3 and was ported to Lean 4. It halves the work on the library, because each multiplicative file gives its additive copy.

### Reference

<?reference?>
