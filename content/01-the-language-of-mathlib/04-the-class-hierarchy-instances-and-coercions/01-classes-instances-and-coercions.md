---
title: Classes, instances and coercions
kind: theory
modules:
  - Mathlib.Basic.FunLike.Basic
  - Mathlib.Algebra.HierarchyDesign
explains:
  E3: [DFunLike]
  E2: [DFunLike.ext, DFunLike.coe_injective]
  E1: [Rat.instField, map_add, map_one, map_mul, Nat.cast_add, Nat.cast_inj]
families: []
requires: [V01.C03]
reads_with: ["TPIL", "MIL"]
lean:
  - MathlibHandbook/V01/C04/Examples.lean
  - MathlibHandbook/V01/C04/Exercises.lean
  - MathlibHandbook/V01/C04/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Classes, instances and coercions

### Overview

A textbook says "let $K$ be a field" and then uses the axioms of a field. Mathlib does the same with a type class: the hypothesis `[Field K]` is an argument that Lean finds by itself. One lemma about all fields then applies to `ℚ`, to `ℝ` and to each finite field. This section shows the instance search, the bundled homs such as `ℤ →+* ℚ`, and the coercions between number types.

### Definitions

**Definition (Class and instance).** A class is a structure that Lean can find by instance search. An instance is a term of the class that Lean registers for this search. An argument in square brackets, such as `[Field K]`, is an instance argument.

**Definition (Bundled hom).** A ring hom `f : R →+* S` is a structure with a function and proofs that it preserves `0`, `1`, `+` and `*`. The class `FunLike` lets Lean apply `f` to an element as a function.

**Definition (Coercion).** A coercion is a function that Lean inserts when a term has the wrong type. The arrow `↑` shows it. For example, `((n : ℕ) : ℤ)` is the integer of the natural number `n`.

### Theorems and proofs

**Theorem (A lemma for all fields).** For a field $K$ and $a, b \in K$ with $b \neq 0$, the equation $(a / b) \cdot b = a$ holds.

*Proof.* By definition, $a / b = a \cdot b^{-1}$, and $b^{-1} \cdot b = 1$ because $b \neq 0$. $\square$

**Theorem (A hom preserves the operations).** For a ring hom $f$, the equations $f(a + b) = f(a) + f(b)$ and $f(1) = 1$ hold.

*Proof.* These are fields of the structure. In Mathlib, the lemmas `map_add` and `map_one` state them for each class of homs that has the property. $\square$

**Theorem (Equal homs).** Two homs with the same function are equal.

*Proof.* The other fields are proofs, and two proofs of one proposition are equal. So the structure is fixed by its function. $\square$

::: mathlib
`Rat.instField` · `Mathlib.Algebra.Field.Rat`

This is the instance that makes `ℚ` a field. The instance search finds it when a lemma needs `[Field ℚ]`, so a proof never names it.

<?decl Rat.instField?>
:::

::: mathlib
`map_add` · `Mathlib.Algebra.Group.Hom.Defs`

The lemma is for each type `F` of homs with a class that says they preserve addition. So it applies to `→+`, to `→+*`, to linear maps and to each other bundled hom.

<?decl map_add?>
:::

::: mathlib
`DFunLike` · `Mathlib.Basic.FunLike.Basic`

The class `DFunLike F α β` says that each term of `F` is a function. It gives the coercion to a function and the lemma `DFunLike.coe_injective`. The extensionality lemma `DFunLike.ext` follows from it.

<?decl DFunLike?>
:::

### Examples

**Example (The instance search).** Lean finds the field structure of `ℚ`.

<?lean MathlibHandbook/V01/C04/Examples.lean#field_rat?>

**Example (A field lemma on ℚ).** The lemma `div_mul_cancel₀` is for all groups with zero. It applies to `ℚ` through the instance.

<?lean MathlibHandbook/V01/C04/Examples.lean#div_mul_cancel?>

**Example (A ring hom preserves addition and one).**

<?lean MathlibHandbook/V01/C04/Examples.lean#map_add?>

<?lean MathlibHandbook/V01/C04/Examples.lean#map_one?>

**Example (Push a cast).** The tactic `push_cast` moves the coercion from `ℕ` to `ℤ` past the addition.

<?lean MathlibHandbook/V01/C04/Examples.lean#push_cast?>

**Example (Remove a cast).** The tactic `exact_mod_cast` uses that the coercion from `ℕ` to `ℤ` is injective.

<?lean MathlibHandbook/V01/C04/Examples.lean#exact_mod_cast?>

### The library around it

The algebraic classes form a hierarchy: `Monoid`, `Group`, `Ring`, `CommRing`, `Field` and many more. Each class extends the classes below it, so a field is also a ring and a group under addition. The library note `LibraryNote.the_algebraic_hierarchy` explains the design. The homs have their own notation: `→*` for monoids, `→+` for additive monoids, `→+*` for rings and `→ₗ[R]` for linear maps. The cast lemmas have names such as `Nat.cast_add`, `Nat.cast_mul` and `Nat.cast_inj`. The tactics `push_cast`, `norm_cast` and `exact_mod_cast` use them, so a proof seldom names them.

### Exercises

1. (A) Name three instances that Lean finds for `ℝ`.
2. (A) Explain why `map_add` applies to a linear map.
3. (B) Show that a ring hom $f$ satisfies $f(-a) = -f(a)$.
4. (L) Prove that a ring hom preserves multiplication. The solution is `map_mul_example`.
5. (L) Prove that the cast from `ℕ` to `ℚ` preserves addition. The solution is `cast_add_example`.
6. (L) Prove that $2 \cdot 2^{-1} = 1$ in `ℚ`. The solution is `two_mul_inv_example`.

### Notes and history

Type classes in a proof assistant come from Haskell, through Isabelle and Coq. The bundled homs and the class `FunLike` replaced an older design of Mathlib, in which a hom was a function and a separate predicate. The new design lets one lemma, such as `map_add`, serve each kind of hom.

### Reference

<?reference?>
