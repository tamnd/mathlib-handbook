---
title: Units of ZMod n, the field ZMod p and the theorems of Fermat, Euler and Wilson
kind: theory
modules:
  - Mathlib.Data.ZMod.Basic
  - Mathlib.Data.Nat.Totient
explains:
  E3: [ZMod.unitOfCoprime, Nat.totient, ZMod.isUnit_iff_coprime]
  E2: [ZMod.unitsEquivCoprime, ZMod.mul_inv_eq_gcd, ZMod.card_units_eq_totient, Nat.totient_prime, Nat.totient_mul, Nat.totient_prime_pow, Nat.totient_eq_card_coprime, ZMod.inv_zero, ZMod.val_coe_unit_coprime]
  E1: auto
families: []
requires: [V02.C02, V02.C03]
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

## Units of ZMod n, the field ZMod p and the theorems of Fermat, Euler and Wilson

### Overview

In $\mathbb{Z}$ only $\pm 1$ have an inverse, but in $\mathbb{Z}/n\mathbb{Z}$ many classes have one: $[3][5] = [1]$ in $\mathbb{Z}/7\mathbb{Z}$. This section finds all of them with Bézout's identity of Chapter 2: the class of $a$ has an inverse if and only if $\gcd(a, n) = 1$. For a prime $p$ each nonzero class then has an inverse, so $\mathbb{Z}/p\mathbb{Z}$ is a field.

The invertible classes form a finite group. A short argument about this group gives Euler's theorem $a^{\varphi(n)} = 1$, and for a prime it gives Fermat's little theorem in the language of rings. The section ends with Wilson's theorem, $(p - 1)! \equiv -1 \pmod p$.

### Definitions

**Definition (Unit).** An element $u$ of a commutative ring $R$ is a *unit* if there is $v \in R$ with $u v = 1$. The element $v$ is the *inverse* $u^{-1}$. The set of the units is $R^\times$.

The inverse is unique: if $u v = 1 = u w$, then $v = v (u w) = (v u) w = w$. The units form a group under the multiplication, because $(u u')^{-1} = u'^{-1} u^{-1}$.

::: mathlib
`ZMod.inv_zero` · `Mathlib.Data.ZMod.Basic`

The predicate `IsUnit a` says that `a` has an inverse, and the type `(ZMod n)ˣ` has the units as terms. The ring `ZMod n` also has an operation `a⁻¹` for each `a`. For a class that is not a unit it is a junk value, for example `(0 : ZMod n)⁻¹ = 0`.

<?decl ZMod.inv_zero?>
:::

**Definition (Euler's function).** For $n \ge 1$, $\varphi(n)$ is the number of $k \in \{0, 1, \dots, n - 1\}$ with $\gcd(k, n) = 1$.

For $n \ge 2$ the number $0$ is not counted, and $\varphi(1) = 1$. The first values are $\varphi(1), \dots, \varphi(10) = 1, 1, 2, 2, 4, 2, 6, 4, 6, 4$.

::: mathlib
`Nat.totient` · `Mathlib.Data.Nat.Totient`

The card of `(Finset.range n).filter n.Coprime`, so `Nat.totient 0 = 0`, a junk value. After `open Nat` the notation is `φ n`.

<?decl Nat.totient?>
:::

::: mathlib
`Nat.totient_eq_card_coprime` · `Mathlib.Data.Nat.Totient`

The definition as a lemma.

<?decl Nat.totient_eq_card_coprime?>
:::

**Definition (Field).** A commutative ring $K$ is a *field* if $0 \ne 1$ in $K$ and each nonzero element is a unit.

A field has no zero divisors: if $x y = 0$ and $x \ne 0$, then $y = x^{-1} x y = 0$.

### Theorems and proofs

**Theorem (Units of ℤ/nℤ).** Let $n \in \mathbb{N}$ and $a \in \mathbb{Z}$. The class $[a]$ is a unit of $\mathbb{Z}/n\mathbb{Z}$ if and only if $\gcd(a, n) = 1$.

*Proof.* Suppose $\gcd(a, n) = 1$. Bézout's identity gives $x, y \in \mathbb{Z}$ with $a x + n y = 1$. The class of $n y$ is $0$, so $[a][x] = [1 - n y] = [1]$.

Conversely, suppose $[a][x] = [1]$. Then $a x - 1 = n y$ for some $y \in \mathbb{Z}$. Let $d = \gcd(a, n)$. Then $d \mid a x - n y = 1$, so $d = 1$. $\square$

The proof is a method: the extended Euclidean algorithm computes $x$, and $[x]$ is the inverse.

::: mathlib
`ZMod.isUnit_iff_coprime` · `Mathlib.Data.ZMod.Basic`

The statement is `IsUnit (m : ZMod n) ↔ m.Coprime n` for `m n : ℕ`. The predicate `Nat.Coprime m n` is `Nat.gcd m n = 1`, from the core of Lean.

<?decl ZMod.isUnit_iff_coprime?>
:::

::: mathlib
`ZMod.unitOfCoprime` · `Mathlib.Data.ZMod.Basic`

The first half of the proof as a function: from `x : ℕ` and `x.Coprime n` to a term of `(ZMod n)ˣ`.

<?decl ZMod.unitOfCoprime?>
:::

::: mathlib
`ZMod.val_coe_unit_coprime` · `Mathlib.Data.ZMod.Basic`

The second half: the value of a unit is coprime to `n`.

<?decl ZMod.val_coe_unit_coprime?>
:::

::: mathlib
`ZMod.mul_inv_eq_gcd` · `Mathlib.Data.ZMod.Basic`

The statement is `a * a⁻¹ = gcd(a.val, n)`. So the junk inverse is not arbitrary: the product is `1` exactly for a unit.

<?decl ZMod.mul_inv_eq_gcd?>
:::

**Corollary (Number of units).** For $n \ge 1$, $\mathbb{Z}/n\mathbb{Z}$ has exactly $\varphi(n)$ units.

*Proof.* The classes are $[0], \dots, [n - 1]$, all distinct, by the previous section. By the theorem, $[k]$ is a unit if and only if $\gcd(k, n) = 1$. $\square$

::: mathlib
`ZMod.card_units_eq_totient` · `Mathlib.Data.Nat.Totient`

It needs `[NeZero n]`: `(ZMod 0)ˣ` is $\{1, -1\}$, but `Nat.totient 0 = 0`.

<?decl ZMod.card_units_eq_totient?>
:::

::: mathlib
`ZMod.unitsEquivCoprime` · `Mathlib.Data.ZMod.Basic`

The bijection behind the count, from `(ZMod n)ˣ` to the classes whose value is coprime to `n`.

<?decl ZMod.unitsEquivCoprime?>
:::

**Theorem (ℤ/nℤ is a field exactly for a prime).** The ring $\mathbb{Z}/n\mathbb{Z}$ is a field if and only if $n$ is prime.

*Proof.* Suppose $n = p$ is prime. Then $[1] \ne [0]$, because $p \nmid 1$. Let $0 < a < p$. A common divisor of $a$ and $p$ is $1$ or $p$, and $p \nmid a$, so $\gcd(a, p) = 1$ and $[a]$ is a unit.

Conversely, suppose $\mathbb{Z}/n\mathbb{Z}$ is a field. For $n = 0$ the ring is $\mathbb{Z}$, where $[2]$ has no inverse. For $n = 1$, $0 = 1$. So $n \ge 2$. If $n = a b$ with $1 < a, b < n$, then $[a], [b] \ne 0$ but $[a][b] = 0$, and a field has no zero divisors. So $n$ is prime. $\square$

::: mathlib
`ZMod.instField` · `Mathlib.Algebra.Field.ZMod`

The instance needs `[Fact p.Prime]`. The class `Fact P` wraps a proposition so that the instance system can find it: `haveI := Fact.mk hp` for `hp : p.Prime`.

<?decl ZMod.instField?>
:::

**Theorem (Euler).** Let $n \ge 1$ and let $u$ be a unit of $\mathbb{Z}/n\mathbb{Z}$. Then $u^{\varphi(n)} = 1$. So if $\gcd(a, n) = 1$, then $a^{\varphi(n)} \equiv 1 \pmod n$.

*Proof.* Let $g_1, \dots, g_m$ be the units, with $m = \varphi(n)$. The map $x \mapsto u x$ sends units to units, and it is injective, because $u x = u y$ gives $x = u^{-1} u x = y$. An injective map from a finite set to itself is a bijection, so $u g_1, \dots, u g_m$ are $g_1, \dots, g_m$ in another order. The multiplication is commutative, so
$$(u g_1)(u g_2) \cdots (u g_m) = g_1 g_2 \cdots g_m.$$
The left side is $u^m P$ with $P = g_1 \cdots g_m$, a unit. Multiplication by $P^{-1}$ gives $u^m = 1$. For the congruence, $[a]$ is a unit, so $[a^{\varphi(n)}] = [1]$. $\square$

::: mathlib
`ZMod.pow_totient` · `Mathlib.FieldTheory.Finite.Basic`

The statement is `x ^ n.totient = 1` for `x : (ZMod n)ˣ`.

<?decl ZMod.pow_totient?>
:::

::: mathlib
`Nat.ModEq.pow_totient` · `Mathlib.FieldTheory.Finite.Basic`

The form `x ^ φ n ≡ 1 [MOD n]` with the hypothesis `x.Coprime n`.

<?decl Nat.ModEq.pow_totient?>
:::

**Corollary (Fermat's little theorem).** Let $p$ be prime. For each $a \in \mathbb{Z}/p\mathbb{Z}$ with $a \ne 0$, $a^{p - 1} = 1$. For each $a \in \mathbb{Z}/p\mathbb{Z}$, $a^p = a$.

*Proof.* The numbers $1, \dots, p - 1$ are coprime to $p$, so $\varphi(p) = p - 1$. Each $a \ne 0$ is a unit, and Euler's theorem gives $a^{p - 1} = 1$. Multiply by $a$. For $a = 0$, $a^p = 0 = a$. $\square$

::: mathlib
`Nat.totient_prime` · `Mathlib.Data.Nat.Totient`

The value $\varphi(p) = p - 1$.

<?decl Nat.totient_prime?>
:::

::: mathlib
`Nat.totient_prime_pow` · `Mathlib.Data.Nat.Totient`

The value $\varphi(p^k) = p^{k - 1}(p - 1)$ for $k > 0$: the $p^{k - 1}$ multiples of $p$ are the numbers that are not coprime.

<?decl Nat.totient_prime_pow?>
:::

::: mathlib
`Nat.totient_mul` · `Mathlib.Data.Nat.Totient`

The rule $\varphi(m n) = \varphi(m) \varphi(n)$ for coprime $m, n$. Exercise 6 asks for a proof.

<?decl Nat.totient_mul?>
:::

::: mathlib
`ZMod.pow_card_sub_one_eq_one` · `Mathlib.FieldTheory.Finite.Basic`

The statement is `a ^ (p - 1) = 1` for `a : ZMod p` with `a ≠ 0` and `[Fact p.Prime]`.

<?decl ZMod.pow_card_sub_one_eq_one?>
:::

::: mathlib
`ZMod.pow_card` · `Mathlib.FieldTheory.Finite.Basic`

The form $x^p = x$. It needs no hypothesis on `x` and has no subtraction in the exponent, so it is often the better form.

<?decl ZMod.pow_card?>
:::

**Theorem (Wilson).** Let $p$ be prime. Then $(p - 1)! \equiv -1 \pmod p$.

*Proof.* For $p = 2$: $1! = 1 \equiv -1$. Let $p$ be odd, and work in the field $K = \mathbb{Z}/p\mathbb{Z}$. The product of its nonzero elements $[1], \dots, [p - 1]$ is $[(p - 1)!]$. In a field, $x = x^{-1}$ means $x^2 - 1 = (x - 1)(x + 1) = 0$, so $x = 1$ or $x = -1$, and $1 \ne -1$ because $p$ is odd. So the other nonzero elements split into pairs $\{x, x^{-1}\}$ with product $1$. The full product is $1 \cdot (-1) = -1$. $\square$

::: mathlib
`ZMod.wilsons_lemma` · `Mathlib.NumberTheory.Wilson`

The statement is `((p - 1)! : ZMod p) = -1` with `[Fact p.Prime]`. The proof in Mathlib uses `FiniteField.prod_univ_units_id_eq_neg_one`: the product of all units of a finite field is `-1`.

<?decl ZMod.wilsons_lemma?>
:::

### Examples

**Example (An inverse by the extended Euclidean algorithm).** Find $[5]^{-1}$ in $\mathbb{Z}/17\mathbb{Z}$. Euclid gives $17 = 3 \cdot 5 + 2$ and $5 = 2 \cdot 2 + 1$. Back: $1 = 5 - 2 \cdot 2 = 7 \cdot 5 - 2 \cdot 17$. So $[5]^{-1} = [7]$. Check: $35 = 2 \cdot 17 + 1$.

**Example (A large power).** Compute $2^{100} \bmod 13$. By Fermat, $2^{12} \equiv 1 \pmod{13}$. Since $100 = 8 \cdot 12 + 4$, $2^{100} \equiv 2^4 = 16 \equiv 3 \pmod{13}$.

**Example (Wilson for p = 7).** $6! = 720 = 102 \cdot 7 + 6 \equiv -1 \pmod 7$. The pairs of the proof are $\{2, 4\}$ and $\{3, 5\}$, and $1$ and $6$ are their own inverses.

**Example (The units of ℤ/12ℤ).** The units are $[1], [5], [7], [11]$, so $\varphi(12) = 4$. Each squares to $1$, so $\varphi(n)$ is not always the least exponent with $u^{\varphi(n)} = 1$.

**Counterexample (ℤ/6ℤ is not a field).** $[2][3] = [0]$ with nonzero factors. The class $[2]$ is not a unit, and Euler's theorem fails for it: $[2]^{\varphi(6)} = [4] \ne [1]$.

### The library around it

The units of `ZMod n` have the API of a general group of units: `Units.val`, `IsUnit.unit` and the coercion `(ZMod n)ˣ → ZMod n`. Other lemmas are `ZMod.isUnit_prime_iff_not_dvd`, `ZMod.coe_unitOfCoprime` and `Nat.sum_totient`, the identity $\sum_{d \mid n} \varphi(d) = n$. Fermat and Euler for a general finite field are in `Mathlib.FieldTheory.Finite.Basic`, and Wilson's theorem with its converse `Nat.prime_iff_fac_equiv_neg_one` is in `Mathlib.NumberTheory.Wilson`.

### Exercises

1. (A) Find the inverse of $[11]$ in $\mathbb{Z}/26\mathbb{Z}$ with the extended Euclidean algorithm, and check it. *Hint.* $26 = 2 \cdot 11 + 4$.
2. (A) Compute $\varphi(n)$ for $n = 15, 16, 18, 30$. *Hint.* Use $\varphi(p^k) = p^{k - 1}(p - 1)$ and the multiplicativity.
3. (A) Compute $3^{1000} \bmod 7$ and $7^{222} \bmod 10$. *Hint.* For the second, $\varphi(10) = 4$.
4. (A) Give the value of `(4 : ZMod 6) * (4 : ZMod 6)⁻¹` in Mathlib. *Hint.* Use `ZMod.mul_inv_eq_gcd`.
5. (B) Prove the converse of Wilson's theorem: if $n > 1$ and $(n - 1)! \equiv -1 \pmod n$, then $n$ is prime. *Hint.* A factor $1 < a < n$ of $n$ divides $(n - 1)!$.
6. (B) Prove $\varphi(m n) = \varphi(m) \varphi(n)$ for coprime $m, n$. *Hint.* Use the Chinese remainder theorem, and that a pair is a unit of $R \times S$ if and only if each part is a unit.
7. (B) Let $p \equiv 1 \pmod 4$ be prime. Show that $x^2 = -1$ has a solution in $\mathbb{Z}/p\mathbb{Z}$. *Hint.* Write $(p - 1)! = \prod_{k=1}^{(p-1)/2} k (p - k)$ and use Wilson's theorem.
8. (C) Show that $a^{561} \equiv a \pmod{561}$ for each $a$, so the converse of Fermat's theorem is false. *Hint.* $561 = 3 \cdot 11 \cdot 17$, and $560$ is a multiple of $2$, $10$ and $16$.

### Notes and history

Fermat stated his little theorem in a letter of 1640, without a proof. Euler published a proof in 1736 and proved the general form with $\varphi$ in 1763. Wilson's theorem is named after John Wilson, a student of Waring, and Lagrange gave the first published proof in 1771.

### Reference

<?reference?>
