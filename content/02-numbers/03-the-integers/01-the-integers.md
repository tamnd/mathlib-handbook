---
title: The integers
kind: theory
modules:
  - Mathlib.Data.Int.Init
  - Mathlib.Data.Int.ModEq
explains:
  E3: [Int.ModEq]
  E2: [Int.induction_on, Int.emod_two_eq_zero_or_one, Int.modEq_iff_dvd, Int.ModEq.add, Int.ModEq.pow]
  E1: auto
families: []
requires: [V02.C02]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V02/C03/Examples.lean
  - MathlibHandbook/V02/C03/Exercises.lean
  - MathlibHandbook/V02/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The integers

### Overview

The core of Lean defines `ℤ` as an inductive type with two constructors: `Int.ofNat n` for $n \geq 0$ and `Int.negSucc n` for $-(n + 1)$. So each integer has one form, and the kernel computes with it. The core also gives the ring operations, the division `/` and the remainder `%`. Mathlib gives the induction on `ℤ`, the congruence relation `Int.ModEq` and the lemmas that connect `ℤ` with `ℕ`. This section shows these tools and the conventions of division.

### Definitions

**Definition (The integers).** The type `ℤ` has the constructors `Int.ofNat : ℕ → ℤ` and `Int.negSucc : ℕ → ℤ`. The cast `(n : ℤ)` of a natural number is `Int.ofNat n`, and `Int.negSucc n` is the integer $-(n + 1)$.

**Definition (Euclidean division).** For $a, b \in \mathbb{Z}$ with $b \neq 0$, the integers $q = a / b$ and $r = a \% b$ satisfy $a = b q + r$ and $0 \leq r < |b|$. Lean writes `Int.ediv` and `Int.emod` for them. The junk values are $a / 0 = 0$ and $a \% 0 = a$.

**Definition (Congruence).** For $a, b, n \in \mathbb{Z}$, the relation $a \equiv b \pmod n$ holds if $a \% n = b \% n$. Mathlib writes it `a ≡ b [ZMOD n]`, and the definition is `Int.ModEq n a b`.

**Definition (Absolute value as a natural number).** `Int.natAbs a` is the natural number $|a|$, and `Int.toNat a` is $a$ for $a \geq 0$ and $0$ for $a < 0$.

### Theorems and proofs

**Theorem (Induction on ℤ).** Let $P$ be a property of integers. If $P(0)$ holds, $P(i)$ gives $P(i + 1)$ for each $i \geq 0$, and $P(-i)$ gives $P(-i - 1)$ for each $i \geq 0$, then $P(n)$ holds for each $n \in \mathbb{Z}$.

*Proof.* Ordinary induction on $i$ gives $P(i)$ for each $i \geq 0$, from the first two hypotheses. Ordinary induction on $i$ gives $P(-i)$ for each $i \geq 0$, from the first and the third. Each integer is $i$ or $-i$ for some $i \geq 0$. $\square$

**Theorem (Congruence and divisibility).** $a \equiv b \pmod n$ if and only if $n \mid b - a$.

*Proof.* Write $a = n q_1 + r_1$ and $b = n q_2 + r_2$ with the Euclidean division. Then $b - a = n (q_2 - q_1) + (r_2 - r_1)$. If $r_1 = r_2$, then $n \mid b - a$. If $n \mid b - a$, then $n \mid r_2 - r_1$, and $|r_2 - r_1| < |n|$, so $r_2 = r_1$. The case $n = 0$ is direct. $\square$

**Theorem (Congruence is compatible with the ring operations).** If $a \equiv b$ and $c \equiv d \pmod n$, then $a + c \equiv b + d$, $a c \equiv b d$ and $a^k \equiv b^k \pmod n$.

*Proof.* By the theorem above, $n \mid b - a$ and $n \mid d - c$. Then $(b + d) - (a + c)$ is the sum of the two differences, and $b d - a c = b (d - c) + c (b - a)$. So $n$ divides both. The case of the powers follows by induction on $k$. $\square$

### Mathlib boxes

::: mathlib
`Int.ModEq` · `Mathlib.Data.Int.ModEq`

The modulus is the first argument, so `Int.ModEq n a b` is `a ≡ b [ZMOD n]`. The relation is decidable, so `decide` proves a congruence of numbers. For `ℕ`, the relation is `Nat.ModEq`, with the notation `[MOD n]`.

<?decl Int.ModEq?>
:::

::: mathlib
`Int.induction_on` · `Mathlib.Data.Int.Init`

The three hypotheses are the case $0$, the step up from $i$ and the step down from $-i$, where `i : ℕ`. Use it with `refine Int.induction_on n ?_ ?_ ?_`.

<?decl Int.induction_on?>
:::

::: mathlib
`Int.ModEq.pow` · `Mathlib.Data.Int.ModEq`

The exponent is the first explicit argument. With dot notation, `h.pow k` takes `h : a ≡ b [ZMOD n]` to `a ^ k ≡ b ^ k [ZMOD n]`.

<?decl Int.ModEq.pow?>
:::

### Examples

**Example (Division and remainder).** The quotient of $-7$ by $2$ is $-4$, and the remainder is $1$.

<?lean MathlibHandbook/V02/C03/Examples.lean#div_mod?>

**Example (Induction on ℤ).** The product of two consecutive integers is even. The two steps use the hypothesis and a term that is a multiple of $2$.

<?lean MathlibHandbook/V02/C03/Examples.lean#induction_on?>

**Example (Parity).**

<?lean MathlibHandbook/V02/C03/Examples.lean#emod_two?>

**Example (A congruence of numbers).**

<?lean MathlibHandbook/V02/C03/Examples.lean#modeq?>

**Example (Congruence as divisibility).**

<?lean MathlibHandbook/V02/C03/Examples.lean#modeq_iff_dvd?>

**Example (Arithmetic of congruences).**

<?lean MathlibHandbook/V02/C03/Examples.lean#modeq_arith?>

### The library around it

The file `Mathlib.Data.Int.Init` has the basic lemmas about `ℤ`, for example `Int.natAbs_sq`. The file `Mathlib.Data.Int.ModEq` has `Int.ModEq` and its lemmas: `Int.ModEq.refl`, `Int.ModEq.symm`, `Int.ModEq.trans`, `Int.ModEq.mul` and `Int.modEq_zero_iff_dvd`. The parity of an integer is in `Mathlib.Algebra.Ring.Int.Parity`, with `Int.even_or_odd` and `Int.even_or_odd'`. The units of `ℤ` are $1$ and $-1$, and `Int.isUnit_iff` says it. The ring `ZMod n` of Chapter 6 is the quotient of `ℤ` by the congruence, and many proofs move a congruence to an equation in `ZMod n`. The tactic `omega` proves linear goals with `/` and `%` by a number, so it often closes a goal about a remainder.

### Exercises

1. (A) Give the values of `(-7 : ℤ) / 0`, `(-7 : ℤ) % 0` and `Int.toNat (-3)` in Mathlib.
2. (A) Explain why `Int.ModEq` takes the modulus as its first argument.
3. (B) Show that the square of an odd integer is congruent to $1$ modulo $8$.
4. (B) Show that $a \equiv b \pmod n$ gives $a \equiv b \pmod m$ for each $m \mid n$.
5. (L) Prove that the remainder of $n^2$ modulo $4$ is $0$ or $1$. The solution is `sq_emod_four`.
6. (L) Prove that a congruence gives a congruence of the powers. The solution is `modEq_pow_of_modEq`.
7. (L) Prove that a congruence gives a statement of divisibility. The solution is `dvd_sub_of_modEq`.
8. (L) Prove that $10^k \equiv 1 \pmod 9$ for each $k$. The solution is `ten_pow_modEq_one`.

### Notes and history

Gauss introduced the notation of congruences in the Disquisitiones Arithmeticae of 1801. The Euclidean convention for division, with a remainder that is not negative, is the convention of Lean 4 and of Mathlib. Many programming languages round the quotient toward zero instead, and then the remainder of a negative number can be negative. The core of Lean keeps that form as `Int.tdiv` and `Int.tmod`.

### Reference

<?reference?>
