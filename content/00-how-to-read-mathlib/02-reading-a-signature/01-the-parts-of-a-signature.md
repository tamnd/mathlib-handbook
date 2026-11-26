---
title: The parts of a signature
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C01]
reads_with: ["TPIL", "MIL Ch. 2"]
lean:
  - MathlibHandbook/V00/C02/Examples.lean
  - MathlibHandbook/V00/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The parts of a signature

### Overview

Each declaration of Mathlib has a signature: its name, its arguments and its type. The Mathlib box of each section of the handbook shows the signature. This section shows how to read it. A reader who can read a signature can use a lemma without its proof.

### The four kinds of argument

The signature of `mul_comm` is in the box below. Read it from left to right.

::: mathlib
`mul_comm` · `Mathlib.Algebra.Group.Semigroup`

The lemma `mul_comm` states that multiplication is commutative in each commutative magma. A commutative group, a commutative ring and a field are all commutative magmas, so the lemma applies to each of them.

<?decl mul_comm?>
:::

The signature has four kinds of argument.

1. An implicit argument is in braces, as `{G : Type u_1}`. Lean finds its value from the other arguments or from the goal. The user does not give it.
2. An instance argument is in square brackets, as `[inst : CommMagma G]`. Lean finds its value by the instance search. The value is a structure, here the proof that the multiplication of `G` is commutative.
3. An explicit argument is in parentheses, as `(a b : G)`. The user gives it.
4. A strict implicit argument is in double braces, as `⦃x : α⦄`. Lean fills it only when an explicit argument after it is given. This kind is rare.

The part after the last colon is the statement. Here it is `a * b = b * a`. When the statement has `∀` at the start, as in the box of `mul_comm`, the variables after `∀` are the arguments of the lemma.

### Using a lemma

**Example (Explicit arguments).** The arguments `a` and `b` of `add_comm` are explicit, so the proof gives them.

<?lean MathlibHandbook/V00/C02/Examples.lean#explicit_args?>

**Example (Implicit arguments).** The type `ℤ` and the instance are implicit. Lean finds them from `a` and `b`.

<?lean MathlibHandbook/V00/C02/Examples.lean#implicit_args?>

**Example (All arguments explicit).** The symbol `@` makes each argument explicit. The symbol `_` asks Lean to find the instance.

<?lean MathlibHandbook/V00/C02/Examples.lean#at_explicit?>

**Example (An instance argument).** The argument `[Group G]` gives the group structure of `G`. The lemma `mul_inv_cancel` then applies to each element of `G`.

<?lean MathlibHandbook/V00/C02/Examples.lean#instance_args?>

**Example (An equivalence).** A lemma with `↔` gives two implications. The field `.mp` is the implication from left to right, and `.mpr` is the implication from right to left.

<?lean MathlibHandbook/V00/C02/Examples.lean#iff_use?>

**Example (A named argument).** An explicit argument can go by its name, in any position.

<?lean MathlibHandbook/V00/C02/Examples.lean#named_args?>

### Universes

A type of types has a level. `Type` is `Type 0`, and `Type 1` is the type of `Type 0`. A signature writes `Type u_1` or `Type*` when the lemma is true at each level. For most uses of the handbook, the level has no effect, and the reader can read `Type u_1` as "a type".

### Exercises

1. (A) In the signature of `mul_comm`, which arguments must a user give? Which ones does Lean find?
2. (A) Write the signature of `add_comm` from memory, then compare it with its page on the site.
3. (B) The lemma `Nat.pos_iff_ne_zero` has the statement `0 < n ↔ n ≠ 0`. Write the type of `Nat.pos_iff_ne_zero.mp`.
4. (L) Prove `MathlibHandbook.V00.C02.Exercises.add_comm_three` with `rw` and `add_comm`.
5. (L) Prove `MathlibHandbook.V00.C02.Exercises.inv_mul_example`. Find the lemma by its name: the inverse of `a`, times `a` times `b`, on the left.
6. (L) Prove `MathlibHandbook.V00.C02.Exercises.pos_of_ne_zero_example` with the `.mpr` direction of a lemma.

### Notes and history

The four kinds of argument are part of the type theory of Lean. *Theorem Proving in Lean 4* explains them in its chapter on dependent type theory. The Mathlib box of the handbook prints the signature that Lean prints with the command `#check @name`.
