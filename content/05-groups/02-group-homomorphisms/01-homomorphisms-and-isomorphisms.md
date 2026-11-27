---
title: Homomorphisms and isomorphisms
kind: theory
modules:
  - Mathlib.Algebra.Group.Hom.Defs
  - Mathlib.Algebra.Group.Equiv.Defs
explains:
  E3: [MonoidHom]
  E2: [map_mul, map_one, map_inv, MonoidHom.comp, MulEquiv]
  E1: auto
families: []
requires: [V05.C01]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C02/Examples.lean
  - MathlibHandbook/V05/C02/Exercises.lean
  - MathlibHandbook/V05/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Homomorphisms and isomorphisms

### Overview

A homomorphism is a map between groups that respects the product. Mathlib has a type for the homomorphisms, `G →* H`, and each element of it is a map with two proofs. A homomorphism of monoids respects the product and the unit. For groups, the unit and the inverses follow from the product. This section shows the type of homomorphisms, the lemmas `map_mul`, `map_one` and `map_inv`, the composite, and the isomorphisms `G ≃* H`.

### Definitions

**Definition (Monoid homomorphism).** A monoid homomorphism $f : M \to N$ is a map with $f(1) = 1$ and $f(a \cdot b) = f(a) \cdot f(b)$. In Mathlib it is the structure `MonoidHom M N`, with the notation `M →* N`. A term `f : M →* N` coerces to a function, so `f a` makes sense.

**Definition (Composite).** If $f : G \to H$ and $g : H \to K$ are homomorphisms, then $g \circ f$ is a homomorphism. In Mathlib it is `g.comp f`.

**Definition (Isomorphism).** An isomorphism $G \cong H$ is a bijective homomorphism. Mathlib stores it as an equivalence that respects the product: `MulEquiv G H`, with the notation `G ≃* H`. The inverse map is `e.symm`.

### Theorems and proofs

**Theorem (Unit).** If $G$ and $H$ are groups and $f(a \cdot b) = f(a) \cdot f(b)$ for all $a$ and $b$, then $f(1) = 1$.

*Proof.* $f(1) = f(1 \cdot 1) = f(1) \cdot f(1)$. Cancel $f(1)$ on the left. $\square$

**Theorem (Inverse).** A homomorphism of groups has $f(a^{-1}) = f(a)^{-1}$.

*Proof.* $f(a^{-1}) \cdot f(a) = f(a^{-1} \cdot a) = f(1) = 1$. An inverse is unique, so $f(a^{-1}) = f(a)^{-1}$. $\square$

**Theorem (Composite).** The composite of two homomorphisms is a homomorphism.

*Proof.* $g(f(a \cdot b)) = g(f(a) \cdot f(b)) = g(f(a)) \cdot g(f(b))$, and $g(f(1)) = g(1) = 1$. $\square$

::: mathlib
`MonoidHom` · `Mathlib.Algebra.Group.Hom.Defs`

The structure has the function, the field `map_one'` and the field `map_mul'`. Use the lemmas `map_one` and `map_mul` in a proof, not the fields. The additive copy is `AddMonoidHom`, with the notation `A →+ B`.

<?decl MonoidHom?>
:::

::: mathlib
`map_mul` · `Mathlib.Algebra.Group.Hom.Defs`

The lemma is stated for each type with the class `MulHomClass`. So one lemma covers monoid homomorphisms, isomorphisms and ring homomorphisms.

<?decl map_mul?>
:::

::: mathlib
`map_one` · `Mathlib.Algebra.Group.Hom.Defs`

The lemma holds for each type with the class `OneHomClass`. A `simp` call uses it with no argument.

<?decl map_one?>
:::

::: mathlib
`map_inv` · `Mathlib.Algebra.Group.Hom.Defs`

The lemma needs only that the source and the target are `DivisionMonoid`s. Its partner `map_div` gives the division.

<?decl map_inv?>
:::

::: mathlib
`MonoidHom.comp` · `Mathlib.Algebra.Group.Hom.Defs`

The argument order follows the function composite: `g.comp f` applies `f` first. The lemma `MonoidHom.comp_apply` unfolds it at a point.

<?decl MonoidHom.comp?>
:::

::: mathlib
`MulEquiv` · `Mathlib.Algebra.Group.Equiv.Defs`

The structure extends the equivalence `G ≃ H` from Volume 1 with the field `map_mul'`. The inverse `e.symm` is again a `MulEquiv`, and `e.toMonoidHom` forgets the inverse.

<?decl MulEquiv?>
:::

### Examples

**Example (Products and the unit).**

<?lean MathlibHandbook/V05/C02/Examples.lean#map_mul?>

**Example (Inverses).**

<?lean MathlibHandbook/V05/C02/Examples.lean#map_inv?>

**Example (A homomorphism from a map).** On a commutative group, the square map is a homomorphism. The constructor `MonoidHom.mk'` needs only the product, because the source is a group.

<?lean MathlibHandbook/V05/C02/Examples.lean#hom_mk?>

**Example (The composite).**

<?lean MathlibHandbook/V05/C02/Examples.lean#comp?>

**Example (An isomorphism and its inverse).**

<?lean MathlibHandbook/V05/C02/Examples.lean#mul_equiv?>

### The library around it

The general lemmas `map_mul`, `map_one`, `map_inv`, `map_div` and `map_pow` are stated for a class of maps, not for `MonoidHom`. This is the design of the class `FunLike` from Volume 1. One lemma then works for `G →* H`, for `G ≃* H` and for a ring homomorphism. The lemmas that are special to `MonoidHom`, such as `MonoidHom.id_apply` and `MonoidHom.comp_apply`, have the prefix `MonoidHom.`. The homomorphisms of a monoid to a commutative monoid are themselves a commutative monoid, and Mathlib gives that instance too. For the additive side, change `Monoid` to `AddMonoid` and `mul` to `add`.

### Exercises

1. (A) Write the type of the additive homomorphisms from `ℤ` to `ℚ`.
2. (A) Explain why `g.comp f` applies `f` first.
3. (B) Show that the map $x \mapsto x^{-1}$ on a group $G$ is a homomorphism if and only if $G$ is commutative.
4. (B) Show that the composite of two isomorphisms is an isomorphism.
5. (L) Prove that $f(a^n) = f(a)^n$. The solution is `map_pow_example`.
6. (L) Prove that $f(a / b) = f(a) / f(b)$ for groups. The solution is `map_div_example`.
7. (L) Prove that the identity homomorphism sends $x$ to $x$. The solution is `id_apply_example`.

### Notes and history

The bundled homomorphism, a structure with the map and the proofs, replaced the old predicate `is_monoid_hom` in Lean 3. The change made the composite and the inverse into terms with a type, so `simp` can use them. The classes such as `MonoidHomClass` came later, so that one lemma covers each kind of map.

### Reference

<?reference?>
