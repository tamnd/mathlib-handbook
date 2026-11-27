---
title: Fin n and ZMod n
kind: theory
modules:
  - Mathlib.Data.Fin.Basic
  - Mathlib.Data.ZMod.Defs
  - Mathlib.Data.ZMod.Basic
explains:
  E3: [ZMod, ZMod.intCast_zmod_eq_zero_iff_dvd]
  E2: [ZMod.val, ZMod.val_lt, ZMod.natCast_self, ZMod.intCast_eq_intCast_iff, ZMod.natCast_zmod_val]
  E1: auto
families: []
requires: [V02.C03, V02.C05]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V02/C06/Examples.lean
  - MathlibHandbook/V02/C06/Exercises.lean
  - MathlibHandbook/V02/C06/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Fin n and ZMod n

### Overview

Lean has two types for the numbers modulo $n$. The type `Fin n` is in the core of Lean: a term is a natural number with a proof that it is less than $n$. It is the normal index type, for example for the entries of a vector of length $n$. The type `ZMod n` is in Mathlib: it is the commutative ring $\mathbb{Z} / n \mathbb{Z}$. For $n > 0$, `ZMod n` is `Fin n` by definition, and for $n = 0$ it is `ℤ`. So `ZMod n` is a ring for each $n$, and it is the type to use for number theory. This section shows the two types, the function `ZMod.val`, and the lemmas that connect `ZMod n` with divisibility and congruences.

### Definitions

**Definition (Fin n).** A term of `Fin n` is a pair of a natural number `x.val` and a proof `x.isLt : x.val < n`. The operations `+` and `*` on `Fin n` are the operations on `ℕ` followed by the remainder modulo $n$.

**Definition (ZMod n).** `ZMod n` is defined by cases: `ZMod 0` is `ℤ`, and `ZMod (n + 1)` is `Fin (n + 1)`. The instance `ZMod.commRing` gives a commutative ring for each $n$.

**Definition (The value of a residue).** For $x \in \mathbb{Z} / n \mathbb{Z}$, `ZMod.val x` is the natural number $r$ with $0 \leq r < n$ in the class of $x$. For $n = 0$, it is the absolute value of $x$.

### Theorems and proofs

**Theorem (Zero in ZMod n).** For $a \in \mathbb{Z}$, the class of $a$ in $\mathbb{Z} / b \mathbb{Z}$ is zero if and only if $b \mid a$.

*Proof.* The ring $\mathbb{Z} / b \mathbb{Z}$ has characteristic $b$. So the kernel of the cast $\mathbb{Z} \to \mathbb{Z} / b \mathbb{Z}$ is the ideal $b \mathbb{Z}$, and the class of $a$ is zero if and only if $a \in b \mathbb{Z}$. $\square$

**Theorem (Equations are congruences).** For $a, b \in \mathbb{Z}$, the classes of $a$ and $b$ in $\mathbb{Z} / c \mathbb{Z}$ are equal if and only if $a \equiv b \pmod c$.

*Proof.* The classes are equal if and only if the class of $b - a$ is zero. By the theorem above, this holds if and only if $c \mid b - a$, which is the congruence by Chapter 3. $\square$

**Theorem (The value is a representative).** For $n > 0$ and $x \in \mathbb{Z} / n \mathbb{Z}$, the value $r = \operatorname{val}(x)$ satisfies $r < n$, and the class of $r$ is $x$.

*Proof.* For $n > 0$, $x$ is a term of `Fin n`, and $r$ is its value, so $r < n$. The cast of $r$ is the class of $r$ modulo $n$, and this is $x$ since $r < n$. $\square$

### Mathlib boxes

::: mathlib
`ZMod` · `Mathlib.Data.ZMod.Defs`

The definition by cases makes `ZMod n` computable, so `decide` proves a closed statement in `ZMod 7`. For a prime $p$ with the instance `Fact p.Prime`, `ZMod p` is a field, and `ZMod.pow_card` in `Mathlib.FieldTheory.Finite.Basic` gives the little theorem of Fermat.

<?decl ZMod?>
:::

::: mathlib
`ZMod.intCast_zmod_eq_zero_iff_dvd` · `Mathlib.Data.ZMod.Basic`

The divisibility is in `ℤ`, so the modulus is the cast `(b : ℤ)`. The form for a natural number is `ZMod.natCast_eq_zero_iff`.

<?decl ZMod.intCast_zmod_eq_zero_iff_dvd?>
:::

::: mathlib
`ZMod.intCast_eq_intCast_iff` · `Mathlib.Data.ZMod.Basic`

The lemma moves an equation of casts to a congruence. A proof about a congruence often goes the other way: it moves to `ZMod n`, where `ring` and `decide` work.

<?decl ZMod.intCast_eq_intCast_iff?>
:::

### Examples

**Example (Addition in Fin 5).** The sum of $3$ and $4$ is $7 = 5 + 2$.

<?lean MathlibHandbook/V02/C06/Examples.lean#fin_add?>

**Example (The value of a sum in Fin n).**

<?lean MathlibHandbook/V02/C06/Examples.lean#fin_val_add?>

**Example (An inverse in ZMod 7).**

<?lean MathlibHandbook/V02/C06/Examples.lean#zmod_compute?>

**Example (The cast of n).**

<?lean MathlibHandbook/V02/C06/Examples.lean#natCast_self?>

**Example (A multiple of the modulus).**

<?lean MathlibHandbook/V02/C06/Examples.lean#intCast_zero?>

**Example (Equations and congruences).**

<?lean MathlibHandbook/V02/C06/Examples.lean#intCast_eq?>

**Example (The representative).**

<?lean MathlibHandbook/V02/C06/Examples.lean#val?>

### The library around it

The file `Mathlib.Data.Fin.Basic` has the lemmas about `Fin n`, for example `Fin.val_add_eq_ite`, `Fin.le_iff_val_le_val` and `Fin.natCast_self`. The tuples `Fin n → α` and the operations on them are in `Mathlib/Data/Fin/Tuple`. The file `Mathlib.Data.ZMod.Basic` has `ZMod.charP`, `ZMod.val_natCast`, `ZMod.natCast_mod`, `ZMod.intCast_mod` and `ZMod.natCast_eq_natCast_iff`. The number of elements is `ZMod.card`. The field structure for a prime is `ZMod.instField` in `Mathlib.Algebra.Field.ZMod`, and the theory of the units and of the quadratic residues is in the volume on number theory. Use `Fin n` for an index and `ZMod n` for arithmetic: the order on `ZMod n` is not compatible with the ring operations.

### Exercises

1. (A) Give the values of `(7 : Fin 5)`, `ZMod.val (-1 : ZMod 6)` and `ZMod.val (-1 : ZMod 0)`.
2. (A) Explain why `ZMod 0` is `ℤ` and not a type with one element.
3. (B) Show that $n^2 + 1$ is never divisible by $3$, with a computation in `ZMod 3`.
4. (B) Show that `ZMod n` is a field if and only if $n$ is prime.
5. (L) Prove that $2 \cdot 4 = 1$ in `ZMod 7`. The solution is `two_mul_four_zmod_seven`.
6. (L) Prove that $2$ is not a square in `ZMod 5`. The solution is `sq_ne_two_zmod_five`.
7. (L) Prove that an integer that is zero in `ZMod 9` is a multiple of $9$. The solution is `dvd_of_intCast_eq_zero`.
8. (L) Prove that the value of a term of `Fin 10` is less than $10$. The solution is `fin_val_lt`.

### Notes and history

The ring $\mathbb{Z} / n \mathbb{Z}$ is the quotient of Gauss's congruences. The choice of Mathlib to define `ZMod n` by cases on $n$, and not as a quotient of `ℤ`, makes the ring computable and makes `ZMod 0` equal to `ℤ`. So a theorem for each $n$ covers the integers too.

### Reference

<?reference?>
