---
title: Congruences and modular arithmetic
kind: theory
modules:
  - Mathlib.Data.Int.ModEq
  - Mathlib.Data.Nat.ModEq
explains:
  E3: [Int.ModEq, Nat.ModEq, Nat.chineseRemainder]
  E2: [Int.modEq_iff_dvd, Int.ModEq.add, Int.ModEq.mul, Int.ModEq.pow, Int.ModEq.cancel_left_div_gcd, Nat.ModEq.cancel_left_of_coprime, Int.modEq_and_modEq_iff_modEq_mul]
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

## Congruences and modular arithmetic

### Overview

Two integers are congruent modulo $n$ if they have the same remainder after division by $n$. Congruence is compatible with addition and multiplication, so a computation modulo $n$ can replace each number by its remainder at each step.

This section proves the rules of congruences, the criteria for inverses and for linear congruences, the Chinese remainder theorem, and Fermat's little theorem. In Mathlib, the relations are `Int.ModEq` with the notation `a ≡ b [ZMOD n]` and `Nat.ModEq` with `a ≡ b [MOD n]`. Chapter 6 gives the same arithmetic as equations in the ring `ZMod n`.

### Definitions

**Definition (Congruence).** Let $n \in \mathbb{Z}$. Two integers $a$ and $b$ are congruent modulo $n$, written $a \equiv b \pmod n$, if $a \% n = b \% n$. The integer $n$ is the modulus.

*Remark.* The first theorem below shows that this agrees with the textbook definition $n \mid b - a$. Congruence modulo $0$ is equality, since $a \% 0 = a$.

::: mathlib
`Int.ModEq` · `Mathlib.Data.Int.ModEq`

The definition is `Int.ModEq n a b := a % n = b % n`, with the modulus first, and the notation `a ≡ b [ZMOD n]` puts it last. The relation is decidable, so `decide` proves a congruence of literals.

<?decl Int.ModEq?>
:::

**Definition (Congruence of natural numbers).** For $a, b, n \in \mathbb{N}$, $a \equiv b \pmod n$ if $a \% n = b \% n$ in $\mathbb{N}$.

::: mathlib
`Nat.ModEq` · `Mathlib.Data.Nat.ModEq`

The notation is `a ≡ b [MOD n]`. The lemmas have the same names as for `ℤ`. Because of the truncated subtraction of `ℕ`, the characterization `Nat.modEq_iff_dvd` is a statement in `ℤ`: `(n : ℤ) ∣ b - a`.

<?decl Nat.ModEq?>
:::

**Definition (Inverse modulo n).** An integer $x$ is an inverse of $a$ modulo $n$ if $a x \equiv 1 \pmod n$.

### Theorems and proofs

**Theorem (Congruence and divisibility).** For $a, b, n \in \mathbb{Z}$, $a \equiv b \pmod n$ if and only if $n \mid b - a$.

*Proof.* For $n = 0$ both sides say $a = b$. Let $n \neq 0$, and write $a = n q_1 + r_1$ and $b = n q_2 + r_2$ with $0 \leq r_1, r_2 < |n|$. Then $b - a = n (q_2 - q_1) + (r_2 - r_1)$. If $r_1 = r_2$, then $n \mid b - a$. Conversely, if $n \mid b - a$, then $n \mid r_2 - r_1$. But $|r_2 - r_1| < |n|$, and the only multiple of $n$ with this property is $0$. So $r_1 = r_2$. $\square$

::: mathlib
`Int.modEq_iff_dvd` · `Mathlib.Data.Int.ModEq`

The statement is `a ≡ b [ZMOD n] ↔ n ∣ b - a`. Note the order `b - a`. The special case `Int.modEq_zero_iff_dvd` says that `a ≡ 0 [ZMOD n] ↔ n ∣ a`.

<?decl Int.modEq_iff_dvd?>
:::

**Theorem (Congruence is compatible with the ring operations).** If $a \equiv b \pmod n$ and $c \equiv d \pmod n$, then $a + c \equiv b + d$, $a - c \equiv b - d$, $a c \equiv b d$ and $a^k \equiv b^k \pmod n$ for each $k \in \mathbb{N}$.

*Proof.* By the theorem above, $n \mid b - a$ and $n \mid d - c$. The sum and the difference are direct. For the product, $b d - a c = b (d - c) + c (b - a)$. For the powers, use induction on $k$ and the rule for the product. $\square$

::: mathlib
`Int.ModEq.mul` · `Mathlib.Data.Int.ModEq`

For `h₁ : a ≡ b [ZMOD n]` and `h₂ : c ≡ d [ZMOD n]`, the terms `h₁.add h₂` (the lemma `Int.ModEq.add`), `h₁.sub h₂` and `h₁.mul h₂` are the congruences of the sum, the difference and the product. For a power, `Int.ModEq.pow k h₁` has the exponent first. There is no rule for an exponent modulo $n$: $1 \equiv 4 \pmod 3$, but $2^1 \not\equiv 2^4 \pmod 3$.

<?decl Int.ModEq.mul?>
:::

**Theorem (Cancellation).** Let $\gcd(c, n) = 1$. If $c a \equiv c b \pmod n$, then $a \equiv b \pmod n$. In general, $c a \equiv c b \pmod n$ gives $a \equiv b \pmod{n / \gcd(c, n)}$ for $n \neq 0$.

*Proof.* The hypothesis says $n \mid c (b - a)$. Let $g = \gcd(c, n)$, $c = g c'$ and $n = g n'$, with $\gcd(c', n') = 1$ (Chapter 2). Then $n' \mid c' (b - a)$, and Euclid's lemma for coprime numbers gives $n' \mid b - a$. If $g = 1$, then $n' = n$. $\square$

::: mathlib
`Int.ModEq.cancel_left_div_gcd` · `Mathlib.Data.Int.ModEq`

The statement has the hypothesis `0 < m` and the conclusion `a ≡ b [ZMOD m / ↑(m.gcd c)]`. The form for `ℕ` with a coprime factor is `Nat.ModEq.cancel_left_of_coprime`, with the hypothesis `m.gcd c = 1`.

<?decl Int.ModEq.cancel_left_div_gcd?>
:::

**Theorem (Inverses).** Let $n \geq 1$. The integer $a$ has an inverse modulo $n$ if and only if $\gcd(a, n) = 1$. The inverse is unique modulo $n$.

*Proof.* If $\gcd(a, n) = 1$, Bézout's identity gives $a x + n y = 1$, so $a x \equiv 1 \pmod n$. Conversely, if $a x - 1 = n k$, each common divisor of $a$ and $n$ divides $a x - n k = 1$. If $a x \equiv 1 \equiv a x'$, cancellation gives $x \equiv x'$. $\square$

**Theorem (Linear congruences).** Let $n \geq 1$ and $d = \gcd(a, n)$. The congruence $a x \equiv b \pmod n$ has a solution if and only if $d \mid b$, and then it has exactly $d$ solutions modulo $n$.

*Proof.* The congruence holds if and only if $a x + n y = b$ for some $y$, and by Bézout's identity these $b$ are the multiples of $d$. Exercise 4 asks for the number of solutions. $\square$

**Theorem (Chinese remainder theorem).** Let $m, n \geq 1$ with $\gcd(m, n) = 1$, and let $a, b \in \mathbb{Z}$. There is an integer $x$ with $x \equiv a \pmod m$ and $x \equiv b \pmod n$. If $x$ and $x'$ are two such integers, then $x \equiv x' \pmod{m n}$.

*Proof.* Existence. Bézout's identity gives $u, v$ with $u m + v n = 1$. Let $x = a v n + b u m$. Modulo $m$, the second term is $0$, and $v n = 1 - u m \equiv 1$. So $x \equiv a \pmod m$. Modulo $n$, the first term is $0$, and $u m = 1 - v n \equiv 1$. So $x \equiv b \pmod n$.

Uniqueness. Suppose $x$ and $x'$ both satisfy the two congruences. Then $m \mid x - x'$ and $n \mid x - x'$. Write $x - x' = m k$. Then $n \mid m k$, and $\gcd(n, m) = 1$, so $n \mid k$ by Euclid's lemma for coprime numbers. Thus $m n \mid x - x'$. $\square$

::: mathlib
`Nat.chineseRemainder` · `Mathlib.Data.Nat.ModEq`

The function takes `co : n.Coprime m` and `a b : ℕ`, and returns a term of the subtype `{k // k ≡ a [MOD n] ∧ k ≡ b [MOD m]}`. It computes. The uniqueness is `Int.modEq_and_modEq_iff_modEq_mul`: for coprime `m` and `n`, a congruence modulo `m * n` is the same as the two congruences.

<?decl Nat.chineseRemainder?>
:::

**Lemma (The middle binomial coefficients).** Let $p$ be a prime and $0 < k < p$. Then $p \mid \binom{p}{k}$.

*Proof.* From $\binom{p}{k} \cdot k! \, (p - k)! = p!$, the prime $p$ divides the left side. Each factor of $k!$ and of $(p - k)!$ is between $1$ and $p - 1$, so by Euclid's lemma $p \nmid k! \, (p - k)!$. Euclid's lemma again gives $p \mid \binom{p}{k}$. $\square$

**Theorem (Fermat's little theorem).** Let $p$ be a prime and $a \in \mathbb{Z}$. Then $a^p \equiv a \pmod p$. If $p \nmid a$, then $a^{p - 1} \equiv 1 \pmod p$.

*Proof.* Step 1: the first claim for $a \in \mathbb{N}$, by induction on $a$. For $a = 0$, $0^p = 0$ since $p \geq 1$. Suppose $a^p \equiv a$. By the binomial theorem,

$$(a + 1)^p = a^p + \sum_{k = 1}^{p - 1} \binom{p}{k} a^k + 1.$$

Each term of the sum is a multiple of $p$ by the lemma. So $(a + 1)^p \equiv a^p + 1 \equiv a + 1 \pmod p$.

Step 2: the first claim for $a \in \mathbb{Z}$. Let $r = a \% p$. Then $0 \leq r < p$, so $r \in \mathbb{N}$, and $a \equiv r \pmod p$. The compatibility with powers and Step 1 give $a^p \equiv r^p \equiv r \equiv a$.

Step 3: the second claim. If $p \nmid a$, then $\gcd(a, p) = 1$, because the only positive divisors of $p$ are $1$ and $p$. Step 2 says $a \cdot a^{p - 1} \equiv a \cdot 1 \pmod p$. Cancel $a$. $\square$

::: mathlib
`Int.ModEq.pow_card_sub_one_eq_one` · `Mathlib.FieldTheory.Finite.Basic`

The statement is `n ^ (p - 1) ≡ 1 [ZMOD p]` for a prime `p` and `IsCoprime n p`. The first claim is `Int.ModEq.pow_prime_eq_self`. Mathlib does not use the binomial proof: it derives the congruences from `ZMod.pow_card`, the statement `x ^ p = x` in the field `ZMod p`. The file is in Volume 11.

<?decl Int.ModEq.pow_card_sub_one_eq_one?>
:::

**Theorem (Euler).** Let $n \geq 1$ and $\gcd(a, n) = 1$, and let $\varphi(n)$ be the number of $r \in \{1, \dots, n\}$ with $\gcd(r, n) = 1$. Then $a^{\varphi(n)} \equiv 1 \pmod n$.

For a prime $p$, $\varphi(p) = p - 1$, and this is the second claim of Fermat's theorem. Chapter 6 proves Euler's theorem in the group of units of `ZMod n`: multiplication by $a$ permutes the units, and the group has $\varphi(n)$ elements.

::: mathlib
`Nat.ModEq.pow_totient` · `Mathlib.FieldTheory.Finite.Basic`

The statement is `x ^ n.totient ≡ 1 [MOD n]` for `x.Coprime n`, with the function `Nat.totient`. Mathlib proves it from `ZMod.pow_totient` in the group `(ZMod n)ˣ`.

<?decl Nat.ModEq.pow_totient?>
:::

### Examples

**Example (A large power).** Compute $3^{100} \bmod 7$. Since $7 \nmid 3$, Fermat gives $3^6 \equiv 1 \pmod 7$. Divide: $100 = 6 \cdot 16 + 4$. So $3^{100} = (3^6)^{16} \cdot 3^4 \equiv 3^4 = 81 \pmod 7$. So $3^{100} \equiv 4 \pmod 7$.

**Example (A congruence of numbers in Lean).** The kernel decides the congruence $17 \equiv 2 \pmod 5$ by the computation of $17 \% 5 = 2 = 2 \% 5$.

<?lean MathlibHandbook/V02/C03/Examples.lean#modeq?>

**Example (A linear congruence).** Solve $6 x \equiv 4 \pmod{10}$. Here $\gcd(6, 10) = 2$ divides $4$, so there are two solutions. Divide by $2$: $3 x \equiv 2 \pmod 5$. The inverse of $3$ modulo $5$ is $2$, so $x \equiv 4 \pmod 5$, and the solutions modulo $10$ are $4$ and $9$.

**Example (A system of congruences).** Solve $x \equiv 2 \pmod 3$, $x \equiv 3 \pmod 5$, $x \equiv 2 \pmod 7$. Among $3, 8, 13, \dots$, the number $8$ is $\equiv 2 \pmod 3$, so the first two congruences are $x \equiv 8 \pmod{15}$. Put $x = 8 + 15 t$. Modulo $7$ this is $1 + t \equiv 2$, so $t \equiv 1$ and $x \equiv 23 \pmod{105}$.

**Example (Congruence as divisibility).**

<?lean MathlibHandbook/V02/C03/Examples.lean#modeq_iff_dvd?>

**Example (Arithmetic of congruences).** From $a \equiv b$, the rules give $a^2 + a \equiv b^2 + b$. The proof term combines the rule for powers and the rule for sums.

<?lean MathlibHandbook/V02/C03/Examples.lean#modeq_arith?>

**Counterexample (Cancellation needs coprimality).** In $\mathbb{Z}$, $2 \cdot 1 \equiv 2 \cdot 4 \pmod 6$, because $8 - 2 = 6$. But $1 \not\equiv 4 \pmod 6$. Here $\gcd(2, 6) = 2$, and the general form of cancellation gives only $1 \equiv 4 \pmod 3$, which is true.

### The library around it

The files `Mathlib.Data.Int.ModEq` and `Mathlib.Data.Nat.ModEq` have parallel families of lemmas, including the change of modulus `Int.ModEq.of_dvd`. The lemma `Int.mod_modEq` says that `a % n ≡ a [ZMOD n]`. Products of congruences are in `Mathlib.Algebra.BigOperators.ModEq`. The tactic `decide` proves congruences of literals.

### Exercises

1. (A) Compute $2^{50} \bmod 7$ and $7^{222} \bmod 10$. *Hint.* Find a small power that is $\equiv 1$.
2. (A) Find the inverse of $7$ modulo $26$, and solve $7 x \equiv 3 \pmod{26}$. *Hint.* Run the extended Euclidean algorithm on $26$ and $7$.
3. (A) Solve the system $x \equiv 1 \pmod 4$, $x \equiv 2 \pmod 9$. *Hint.* Follow the proof of the Chinese remainder theorem.
4. (B) Show that $a x \equiv b \pmod n$ with $d = \gcd(a, n) \mid b$ has exactly $d$ solutions in $\{0, \dots, n - 1\}$. *Hint.* Divide by $d$ and use an inverse of $a / d$ modulo $n / d$.
5. (B) Show that $a^5 \equiv a \pmod{30}$ for each integer $a$. *Hint.* Prove the congruence modulo $2$, $3$ and $5$ with Fermat, then use the uniqueness part of the Chinese remainder theorem.
6. (C) Prove the Chinese remainder theorem for $k$ moduli $n_1, \dots, n_k$ that are pairwise coprime. *Hint.* Induction on $k$: $n_1 \cdots n_{k - 1}$ is coprime to $n_k$.
7. (L) Prove that a congruence gives a congruence of the powers. The solution is `modEq_pow_of_modEq`.
8. (L) Prove that a congruence gives a statement of divisibility. The solution is `dvd_sub_of_modEq`.
9. (L) Prove that $10^k \equiv 1 \pmod 9$ for each $k$. The solution is `ten_pow_modEq_one`.

### Notes and history

Gauss introduced the notation $a \equiv b \pmod n$ in the *Disquisitiones Arithmeticae* (1801). The system of the example above is the problem of the *Sunzi Suanjing*. The standard reference is Hardy and Wright, *An Introduction to the Theory of Numbers*, Chapters 5 and 6.

### Reference

<?reference?>
