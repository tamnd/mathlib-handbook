---
title: The type of finitely supported functions
kind: theory
modules:
  - Mathlib.Data.Finsupp.Defs
explains:
  E3: [Finsupp, Finsupp.single]
  E2: [Finsupp.support, Finsupp.mem_support_iff, Finsupp.sum, Finsupp.single_add, Finsupp.add_apply, Finsupp.ext]
  E1: auto
families: []
requires: [V03.C03, V03.C06]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V03/C07/Examples.lean
  - MathlibHandbook/V03/C07/Exercises.lean
  - MathlibHandbook/V03/C07/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The type of finitely supported functions

### Overview

A polynomial $3 + 2X^5$ is a function from the exponents to the coefficients: it sends $0$ to $3$, $5$ to $2$ and each other number to $0$. The factorization $12 = 2^2 \cdot 3$ is a function from the primes to the exponents with the same property. In both cases the function is zero at all but finitely many points. The type `α →₀ M` of Mathlib holds these functions, together with the finset of the points where the value is not zero. With that finset, a sum over all points with a nonzero value is a finite sum. This section gives the type, the functions with one point, the pointwise addition and the sum.

### Definitions

**Definition (Finitely supported function).** For a type `α` and a type `M` with a zero, a term `f : α →₀ M` is a structure with three fields: a finset `f.support`, a function `α → M`, and a proof that `a ∈ f.support` if and only if `f a ≠ 0`. The coercion lets `f a` give the value.

**Definition (Single).** `Finsupp.single a b` is the function with the value `b` at `a` and `0` at each other point.

**Definition (Addition).** When `M` is an additive monoid, `f + g` is the pointwise sum. With it, `α →₀ M` is an additive monoid, and it is a commutative group when `M` is one.

**Definition (Sum).** For `g : α → M → N`, `f.sum g` is the sum of `g a (f a)` over `a ∈ f.support`.

### Theorems and proofs

**Theorem (Values of single).** The value of $\mathrm{single}(a, b)$ at $a$ is $b$, and at $a' \ne a$ it is $0$. If $b \ne 0$, the support is $\{a\}$.

*Proof.* This comes from the definition, which uses an `if` on the equality $a' = a$. $\square$

**Theorem (Extensionality).** If $f(a) = g(a)$ for each $a$, then $f = g$.

*Proof.* The functions are equal. The supports are then equal, because each is the finset of the points with a nonzero value. $\square$

**Theorem (Induction).** A statement about all $f : \alpha \to_0 M$ follows from the statement for $0$ and from a step from $f$ to $\mathrm{single}(a, b) + f$ with $a \notin \mathrm{supp}(f)$ and $b \ne 0$.

*Proof.* Use induction on the card of the support. A function with a nonempty support is a single plus a function with a smaller support. $\square$

::: mathlib
`Finsupp` · `Mathlib.Data.Finsupp.Defs`

The structure of the finitely supported functions, with the notation `α →₀ M`. The support is data, so the definitions in this file often use classical logic to decide if a value is zero.

<?decl Finsupp?>
:::

::: mathlib
`Finsupp.single` · `Mathlib.Data.Finsupp.Single`

The function with one point. The lemmas `Finsupp.single_eq_same` and `Finsupp.single_eq_of_ne` give its values, and `simp` uses them. The basis of a free module and the monomials of a polynomial are made from it.

<?decl Finsupp.single?>
:::

### Examples

**Example (The values of single).**

<?lean MathlibHandbook/V03/C07/Examples.lean#single?>

**Example (Pointwise sum).**

<?lean MathlibHandbook/V03/C07/Examples.lean#add?>

**Example (Single is additive).**

<?lean MathlibHandbook/V03/C07/Examples.lean#single_add?>

**Example (A support).**

<?lean MathlibHandbook/V03/C07/Examples.lean#support?>

**Example (Membership in the support).**

<?lean MathlibHandbook/V03/C07/Examples.lean#mem_support?>

**Example (The sum of a single).**

<?lean MathlibHandbook/V03/C07/Examples.lean#sum?>

**Counterexample (A function with infinite support).** The constant function $1$ on `ℕ` has no term in `ℕ →₀ ℤ`, because it is not zero at infinitely many points.

### The library around it

`Finsupp.induction` is the induction principle above, and `Finsupp.sum_add_index` gives the sum of $f + g$ when $g$ is additive in its second argument. `Finsupp.mapRange` applies a function to the values, and `Finsupp.mapDomain` moves the points. `Finsupp.onFinset` makes a term from a function and a finset that contains its support. `Finsupp.equivFunOnFinite` is the equivalence with all functions when `α` is finite. `Finsupp.linearCombination` is the linear map of the linear combinations, and `Finsupp.toMultiset` sends a function to `ℕ` to a multiset. The type of polynomials, `Polynomial`, holds an `ℕ →₀ R`, and `Nat.factorization` gives an `ℕ →₀ ℕ`. For a dependent type of values, Mathlib has `DFinsupp`.

### Exercises

1. (A) Give the support of `Finsupp.single 3 0 + Finsupp.single 4 1` in `ℕ →₀ ℤ`.
2. (A) Explain why the support of a sum $f + g$ can be smaller than the union of the supports.
3. (B) Show that `Finsupp.single a` is injective.
4. (L) Prove that the value of `single a b` at `a` is `b`. The solution is `single_eq_same_example`.
5. (L) Prove that the value of `single a b` at a point other than `a` is zero. The solution is `single_eq_of_ne_example`.
6. (L) Prove the rule of extensionality. The solution is `ext_example`.
7. (L) Prove that the zero function has an empty support. The solution is `support_zero_example`.

### Notes and history

The finitely supported functions from a set $X$ to a ring $R$ are the free module on $X$. In algebra they are often written as the direct sum $\bigoplus_{x \in X} R$. Mathlib uses `Finsupp` for the free modules, the polynomials in many variables and the monoid algebras. MIL uses it in its chapter on linear algebra for the coordinates in a basis.

### Reference

<?reference?>
