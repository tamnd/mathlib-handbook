---
title: Fin n and ZMod n
kind: theory
modules:
  - Mathlib.Data.Fin.Basic
  - Mathlib.Data.ZMod.Defs
  - Mathlib.Data.ZMod.Basic
explains:
  E3: [ZMod, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.commRing]
  E2: [ZMod.val, ZMod.val_lt, ZMod.natCast_self, ZMod.intCast_eq_intCast_iff, ZMod.natCast_zmod_val, ZMod.charP, ZMod.val_add, ZMod.val_mul, ZMod.natCast_eq_natCast_iff, ZMod.val_natCast, ZMod.intCast_surjective]
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

Chapter 3 defined the congruence $a \equiv b \pmod n$ and proved that it is compatible with the sum and the product. This section turns the congruence into a ring, $\mathbb{Z}/n\mathbb{Z}$, so that an equation in the ring is a congruence of integers and the tools of a ring apply.

Lean has two types for the numbers modulo $n$. The type `Fin n` is in the core of Lean: a term is a natural number with a proof that it is less than $n$, and it is the normal type of indices. The type `ZMod n` is in Mathlib: it is the commutative ring $\mathbb{Z}/n\mathbb{Z}$ for each $n$, and it is the type for number theory. The section proves that the operations on the classes are well defined and that each class has exactly one representative in $\{0, \dots, n - 1\}$.

### Definitions

**Definition (Fin n).** For $n \in \mathbb{N}$, $\operatorname{Fin}(n) = \{x \in \mathbb{N} : x < n\}$, with $x + y = (x + y) \bmod n$ and $x \cdot y = (x y) \bmod n$.

In Lean a term `x : Fin n` is a pair of a value `x.val` and a proof `x.isLt : x.val < n`. The type `Fin 0` is empty, so it is not a ring.

**Definition (The ring ℤ/nℤ).** Let $n \in \mathbb{N}$. The *class* of $a \in \mathbb{Z}$ modulo $n$ is $[a] = \{b \in \mathbb{Z} : b \equiv a \pmod n\}$. The set $\mathbb{Z}/n\mathbb{Z}$ of the classes has $[a] + [b] = [a + b]$ and $[a] \cdot [b] = [a b]$.

So $[a] = [b]$ if and only if $a \equiv b \pmod n$. For $n = 0$ the congruence is equality, and $\mathbb{Z}/0\mathbb{Z}$ is a copy of $\mathbb{Z}$.

**Definition (ZMod n).** In Mathlib, `ZMod 0` is `ℤ`, and `ZMod (n + 1)` is `Fin (n + 1)`. The cast from $\mathbb{Z}$ to `ZMod n` takes $a$ to the term that represents its class.

::: mathlib
`ZMod` · `Mathlib.Data.ZMod.Defs`

The definition by cases makes `ZMod n` computable, so `decide` proves a closed statement in `ZMod 7`, and a theorem for each `n : ℕ` covers `ℤ` too. The price is that a proof often needs a case split on `n` or the instance `NeZero n`.

<?decl ZMod?>
:::

::: mathlib
`ZMod.commRing` · `Mathlib.Data.ZMod.Defs`

The ring instance is also defined by cases, so `ring`, `linear_combination` and `simp` work in `ZMod n`.

<?decl ZMod.commRing?>
:::

**Definition (The value of a class).** For $n > 0$ and $x \in \mathbb{Z}/n\mathbb{Z}$, $\operatorname{val}(x)$ is the natural number $r$ with $0 \le r < n$ and $[r] = x$. For $n = 0$, it is the absolute value of the integer $x$, a junk value that forgets the sign.

::: mathlib
`ZMod.val` · `Mathlib.Data.ZMod.Basic`

For `n + 1` it is `Fin.val`, and for `0` it is `Int.natAbs`. Most lemmas about `val` need `[NeZero n]`, which Lean finds for a numeral.

<?decl ZMod.val?>
:::

**Definition (Characteristic).** A ring $R$ has *characteristic* $n$ if, for each $k \in \mathbb{N}$, $\uparrow k = 0$ in $R$ if and only if $n \mid k$.

### Theorems and proofs

**Theorem (The operations are well defined).** Let $a \equiv a'$ and $b \equiv b' \pmod n$. Then $a + b \equiv a' + b'$ and $a b \equiv a' b' \pmod n$. So $\mathbb{Z}/n\mathbb{Z}$ is a commutative ring, and $a \mapsto [a]$ is a surjective map of rings.

*Proof.* The difference $(a' + b') - (a + b) = (a' - a) + (b' - b)$ is a sum of two multiples of $n$, and so is $a' b' - a b = a' (b' - b) + b (a' - a)$. So the operations do not depend on the representatives.

Each axiom of a commutative ring is an equation between expressions. For classes, each side is the class of the same expression in the representatives, and the equation holds in $\mathbb{Z}$. For example, $[a]([b] + [c]) = [a (b + c)] = [a b + a c] = [a][b] + [a][c]$. The map $a \mapsto [a]$ keeps the operations by the definition. $\square$

**Theorem (Representatives).** Let $n > 0$. Each class of $\mathbb{Z}/n\mathbb{Z}$ contains exactly one integer $r$ with $0 \le r < n$. So $\mathbb{Z}/n\mathbb{Z}$ has exactly $n$ elements.

*Proof.* Existence. The division with remainder gives $a = n q + r$ with $0 \le r < n$, so $[r] = [a]$. Uniqueness. If $0 \le r, r' < n$ and $n \mid r - r'$, then $-n < r - r' < n$, so $r - r' = 0$. $\square$

So $[a] \mapsto r$ is a bijection onto $\operatorname{Fin}(n)$, and this is why `Fin n` can carry the ring for $n > 0$.

::: mathlib
`ZMod.val_lt` · `Mathlib.Data.ZMod.Basic`

The value is less than `n`, with `[NeZero n]`.

<?decl ZMod.val_lt?>
:::

::: mathlib
`ZMod.natCast_zmod_val` · `Mathlib.Data.ZMod.Basic`

The cast of the value is the term: `((a.val : ℕ) : ZMod n) = a`.

<?decl ZMod.natCast_zmod_val?>
:::

::: mathlib
`ZMod.val_natCast` · `Mathlib.Data.ZMod.Basic`

The value of a cast is `a % n`, for each `n`, because `a % 0 = a`.

<?decl ZMod.val_natCast?>
:::

::: mathlib
`ZMod.intCast_surjective` · `Mathlib.Data.ZMod.Basic`

Each class has an integer representative. A proof can start with `obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x`.

<?decl ZMod.intCast_surjective?>
:::

**Theorem (Characteristic of ℤ/nℤ).** For $a \in \mathbb{Z}$, $[a] = 0$ in $\mathbb{Z}/n\mathbb{Z}$ if and only if $n \mid a$. So $\mathbb{Z}/n\mathbb{Z}$ has characteristic $n$.

*Proof.* $[a] = [0]$ if and only if $n \mid a - 0$. For $k \in \mathbb{N}$, the cast $\uparrow k$ is $[k]$, because $a \mapsto [a]$ is a map of rings and the cast from $\mathbb{N}$ is unique (Chapter 5). $\square$

::: mathlib
`ZMod.intCast_zmod_eq_zero_iff_dvd` · `Mathlib.Data.ZMod.Basic`

The divisibility is in `ℤ`, so the modulus is the cast `(b : ℤ)`. The form for `ℕ` is `ZMod.natCast_eq_zero_iff`.

<?decl ZMod.intCast_zmod_eq_zero_iff_dvd?>
:::

::: mathlib
`ZMod.charP` · `Mathlib.Data.ZMod.Basic`

The instance `CharP (ZMod n) n`, so the general lemmas about characteristic apply.

<?decl ZMod.charP?>
:::

::: mathlib
`ZMod.natCast_self` · `Mathlib.Data.ZMod.Basic`

The `simp` lemma `(n : ZMod n) = 0`.

<?decl ZMod.natCast_self?>
:::

**Corollary (Equations are congruences).** For $a, b \in \mathbb{Z}$, $[a] = [b]$ in $\mathbb{Z}/n\mathbb{Z}$ if and only if $a \equiv b \pmod n$.

*Proof.* $[a] = [b]$ if and only if $[b - a] = 0$, that is, $n \mid b - a$. $\square$

::: mathlib
`ZMod.intCast_eq_intCast_iff` · `Mathlib.Data.ZMod.Basic`

It turns an equation of casts into `a ≡ b [ZMOD c]`. A proof often goes the other way: it moves to `ZMod n`, where `ring` and `decide` work, and comes back.

<?decl ZMod.intCast_eq_intCast_iff?>
:::

::: mathlib
`ZMod.natCast_eq_natCast_iff` · `Mathlib.Data.ZMod.Basic`

The form for `ℕ`, with `a ≡ b [MOD c]`.

<?decl ZMod.natCast_eq_natCast_iff?>
:::

**Theorem (Values of a sum and a product).** Let $n > 0$ and $x, y \in \mathbb{Z}/n\mathbb{Z}$. Then $\operatorname{val}(x + y) = (\operatorname{val}(x) + \operatorname{val}(y)) \bmod n$ and $\operatorname{val}(x y) = (\operatorname{val}(x) \operatorname{val}(y)) \bmod n$.

*Proof.* Let $x = [r]$ and $y = [s]$ with $r, s$ the values. Then $t = (r + s) \bmod n$ has $0 \le t < n$ and $[t] = x + y$, so $t$ is the value by uniqueness. The product is the same with $r s$. $\square$

::: mathlib
`ZMod.val_add` · `Mathlib.Data.ZMod.Basic`

It needs `[NeZero n]`. The form with a case split for `Fin n` is `Fin.val_add_eq_ite`.

<?decl ZMod.val_add?>
:::

::: mathlib
`ZMod.val_mul` · `Mathlib.Data.ZMod.Basic`

It needs no `NeZero`, because $|a b| = |a| |b|$ for `n = 0`.

<?decl ZMod.val_mul?>
:::

### Examples

**Example (Addition in Fin 5).** $3 + 4 = 7 = 5 + 2$, so the sum is $2$ in `Fin 5`.

<?lean MathlibHandbook/V02/C06/Examples.lean#fin_add?>

**Example (The value of a sum in Fin n).**

<?lean MathlibHandbook/V02/C06/Examples.lean#fin_val_add?>

**Example (An inverse in ZMod 7).** $3 \cdot 5 = 15 = 2 \cdot 7 + 1$, so $[3][5] = [1]$.

<?lean MathlibHandbook/V02/C06/Examples.lean#zmod_compute?>

**Example (The cast of n).**

<?lean MathlibHandbook/V02/C06/Examples.lean#natCast_self?>

**Example (A multiple of the modulus).**

<?lean MathlibHandbook/V02/C06/Examples.lean#intCast_zero?>

**Example (Equations and congruences).**

<?lean MathlibHandbook/V02/C06/Examples.lean#intCast_eq?>

**Example (The representative).**

<?lean MathlibHandbook/V02/C06/Examples.lean#val?>

**Example (No divisibility by 3).** Claim: $3 \nmid a^2 + 1$ for each $a \in \mathbb{Z}$. By the theorem on characteristic it suffices to show $[a]^2 + 1 \ne 0$ in $\mathbb{Z}/3\mathbb{Z}$. For $[a] = [0], [1], [2]$, the value of $[a]^2 + 1$ is $1$, $2$ or $2$. Three cases replace all the integers.

**Counterexample (The order of Fin n).** In `Fin 5`, $3 < 4$, but $3 + 1 = 4$ and $4 + 1 = 0$. So the order is not compatible with the addition.

### The library around it

The file `Mathlib.Data.Fin.Basic` has `Fin.ext_iff`, `Fin.val_add_eq_ite` and the maps `Fin.castSucc` and `Fin.succ` into `Fin (n + 1)`. The file `Mathlib.Data.ZMod.Basic` has the cast lemmas such as `ZMod.natCast_mod`, the value lemmas, and `ZMod.card`. A rule of use: take `Fin n` for an index and `ZMod n` for arithmetic.

### Exercises

1. (A) Give the values of `(7 : Fin 5)`, `ZMod.val (-1 : ZMod 6)` and `ZMod.val (-1 : ZMod 0)`. *Hint.* For $n = 0$ the value is the absolute value.
2. (A) Compute $[2]^{10}$ in $\mathbb{Z}/11\mathbb{Z}$, one square at a time. *Hint.* $2^5 = 32$.
3. (B) Show that a square is congruent to $0$, $1$ or $4$ modulo $8$, and deduce that no integer $\equiv 7 \pmod 8$ is a sum of three squares. *Hint.* Compute the squares in $\mathbb{Z}/8\mathbb{Z}$.
4. (C) Let $m \mid n$. Show that $[a]_n \mapsto [a]_m$ is a well defined surjective map of rings $\mathbb{Z}/n\mathbb{Z} \to \mathbb{Z}/m\mathbb{Z}$, and that there is no map of rings in the other direction when $0 < m < n$. *Hint.* A map of rings sends $\uparrow m$ to $\uparrow m$.
5. (L) Prove that $2 \cdot 4 = 1$ in `ZMod 7`. The solution is `two_mul_four_zmod_seven`.
6. (L) Prove that $2$ is not a square in `ZMod 5`. The solution is `sq_ne_two_zmod_five`.
7. (L) Prove that an integer that is zero in `ZMod 9` is a multiple of $9$. The solution is `dvd_of_intCast_eq_zero`.
8. (L) Prove that the value of a term of `Fin 10` is less than $10$. The solution is `fin_val_lt`.

### Notes and history

The ring $\mathbb{Z}/n\mathbb{Z}$ is the algebraic form of the congruences of Gauss's *Disquisitiones Arithmeticae* (1801). Mathlib defines `ZMod n` by cases on $n$ and not as a quotient of `ℤ`, so the ring computes and `ZMod 0` is `ℤ`.

### Reference

<?reference?>
