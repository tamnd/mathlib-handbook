---
title: Injective and surjective functions, and equivalences
kind: theory
modules:
  - Mathlib.Logic.Function.Basic
  - Mathlib.Logic.Equiv.Defs
explains:
  E3: [Equiv]
  E2: [Function.Bijective, Function.injective_iff_hasLeftInverse, Equiv.bijective, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  E1: auto
families: []
requires: [V01.C02]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V01/C03/Examples.lean
  - MathlibHandbook/V01/C03/Exercises.lean
  - MathlibHandbook/V01/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Injective and surjective functions, and equivalences

### Overview

A function `f : α → β` in Lean is defined at every element of `α`. Its properties, such as injectivity, are predicates in the namespace `Function`. A bijection with a chosen inverse is the structure `Equiv`, written `α ≃ β`. This section gives the definitions, the basic theorems, and the reason why Mathlib prefers `Equiv` to a bijective function.

### Definitions

**Definition (Injective, surjective, bijective).** A function $f : \alpha \to \beta$ is injective when $f(a) = f(b)$ implies $a = b$. It is surjective when each $b$ has some $a$ with $f(a) = b$. It is bijective when it is both.

**Definition (Left inverse).** A function $g : \beta \to \alpha$ is a left inverse of $f$ when $g(f(a)) = a$ for every $a$. In Lean, this is `Function.LeftInverse g f`.

**Definition (Equivalence).** An equivalence `e : α ≃ β` is a structure with four fields: a function `toFun`, a function `invFun`, and proofs that each is a left inverse of the other.

### Theorems and proofs

**Theorem (Composite of injections).** If $f$ and $g$ are injective, then $g \circ f$ is injective.

*Proof.* If $g(f(a)) = g(f(b))$, then $f(a) = f(b)$ because $g$ is injective, and $a = b$ because $f$ is injective. $\square$

**Theorem (Left inverse).** A function with a left inverse is injective. Conversely, a function from a nonempty type that is injective has a left inverse.

*Proof.* If $g \circ f = \mathrm{id}$ and $f(a) = f(b)$, then $a = g(f(a)) = g(f(b)) = b$. For the converse, send $b$ to some $a$ with $f(a) = b$ when such an $a$ exists, and to a fixed element otherwise. This step uses choice. $\square$

**Theorem (An equivalence is bijective).** The function of an equivalence is bijective.

*Proof.* The inverse is a left inverse, so the function is injective. The inverse is also a right inverse, so the function is surjective. $\square$

::: mathlib
`Function.injective_iff_hasLeftInverse` · `Mathlib.Logic.Function.Basic`

Mathlib states the theorem for a nonempty domain. The direction from right to left is `Function.LeftInverse.injective`, and it needs no hypothesis.

<?decl Function.injective_iff_hasLeftInverse?>
:::

::: mathlib
`Equiv` · `Mathlib.Logic.Equiv.Defs`

An equivalence carries its inverse as data, so `e.symm` is a function and needs no choice. The simp lemmas `Equiv.symm_apply_apply` and `Equiv.apply_symm_apply` cancel the inverse. The lemma `Equiv.bijective` gives the bijection.

<?decl Equiv?>
:::

### Examples

**Example (A composite of injections).** The term `hg.comp hf` proves that `g ∘ f` is injective.

<?lean MathlibHandbook/V01/C03/Examples.lean#injective_comp?>

**Example (Doubling is injective).** After `intro a b h`, the hypothesis is `2 * a = 2 * b`, and `omega` gives `a = b`.

<?lean MathlibHandbook/V01/C03/Examples.lean#double_injective?>

**Counterexample (Doubling is not surjective).** No natural number doubles to `1`.

<?lean MathlibHandbook/V01/C03/Examples.lean#double_not_surjective?>

**Example (Injective by a left inverse).** The function `n ↦ n - 3` is a left inverse of `n ↦ n + 3` on `ℕ`, so `n ↦ n + 3` is injective. It is not a right inverse, because subtraction on `ℕ` stops at `0`.

<?lean MathlibHandbook/V01/C03/Examples.lean#leftInverse?>

**Example (The swap of a product).** The equivalence `Equiv.prodComm ℕ ℤ` swaps the two coordinates. It is bijective.

<?lean MathlibHandbook/V01/C03/Examples.lean#equiv?>

<?lean MathlibHandbook/V01/C03/Examples.lean#equiv_symm?>

### The library around it

The namespace `Function` has the lemmas of each property in a fixed pattern: `Function.Injective.comp`, `Function.Surjective.comp` and `Function.Bijective.comp` for composites, and `Function.Bijective.injective` and `Function.Bijective.surjective` for the parts. The type `α ≃ β` has many named equivalences: `Equiv.refl`, `Equiv.symm`, `Equiv.trans`, `Equiv.prodComm`, `Equiv.sumComm` and the equivalences of `Fin`. An equivalence that also preserves structure has its own type, for example `≃*` for groups and `≃+*` for rings. Each of these coerces to a function, by the class `FunLike` of Chapter 4.

### Exercises

1. (A) Show that the composite of two surjective functions is surjective.
2. (A) Give a function $\mathbb{N} \to \mathbb{N}$ that is surjective and not injective.
3. (B) Show that a function with a left inverse and a right inverse is bijective, and that the two inverses are equal.
4. (C) Show that there is no surjection from a set onto its power set. Compare with `Function.cantor_surjective`.
5. (L) Prove that adding one is injective on `ℕ`. The solution is `injective_add_one`.
6. (L) Prove that the identity function is surjective. The solution is `surjective_id_example`.
7. (L) Prove that an equivalence undoes its inverse. The solution is `apply_symm_apply_example`.

### Notes and history

The structure `Equiv` comes from the Lean 3 library. Mathlib prefers an equivalence to a proof of bijectivity, because the inverse of a bijective function needs choice and does not compute. The theorem of Cantor in exercise 4 is `Function.cantor_surjective`.

### Reference

<?reference?>
