---
title: Sums of two and four squares
kind: theory
modules:
  - Mathlib.NumberTheory.SumTwoSquares
  - Mathlib.NumberTheory.SumFourSquares
  - Mathlib.NumberTheory.Zsqrtd.GaussianInt
explains:
  E3: [Nat.sq_add_sq_mul, ZMod.isSquare_neg_one_iff', Nat.Prime.sum_four_squares, Nat.sum_four_squares]
  E2: [sq_add_sq_mul, Nat.Prime.sq_add_sq, ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime, ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime, Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one, ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three, ZMod.isSquare_neg_one_mul, euler_four_squares, Nat.euler_four_squares, Int.exists_sq_add_sq_add_one_eq_mul, Int.sq_add_sq_of_two_mul_sq_add_sq, Int.lt_of_sum_four_squares_eq_mul]
  E1: auto
families: [ZMod.isSquare_neg_one_*]
requires: [V02.C02, V06.C06, V12.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sums of two and four squares

### Overview

This section extends Fermat's theorem on primes $p \equiv 1 \pmod 4$ (Volume 6, Chapter 6) to all natural numbers. A number $n \ge 1$ is a sum of two squares if and only if each prime $q \equiv 3 \pmod 4$ divides $n$ to an even power. The proof needs two facts: a product of two sums of two squares is again one, and a prime $q \equiv 3 \pmod 4$ cannot divide $x^2 + y^2$ with $\gcd(x, y) = 1$.

Four squares are enough for every number. Lagrange proved in 1770 that each natural number is a sum of four squares. The proof has an identity of Euler for products and a descent for primes, which is also the route of Mathlib.

### Definitions

**Definition (Sum of $k$ squares).** A natural number $n$ is a sum of $k$ squares if there are integers $x_1, \dots, x_k$ with $n = x_1^2 + \cdots + x_k^2$.

Remarks. Zero is allowed among the $x_i$, and the signs do not matter, so the $x_i$ can be taken in $\mathbb{N}$, as Mathlib does.

**Definition (Square modulo $n$).** An integer $a$ is a square modulo $n$ if $a \equiv x^2 \pmod n$ for some integer $x$, that is, if the class of $a$ is a square in $\mathbb{Z}/n$.

Remarks. Here only $a = -1$ matters. By Euler's criterion (Chapter 3, Section 1), or by the lemma of Volume 6, Chapter 6, $-1$ is a square modulo an odd prime $q$ if and only if $q \equiv 1 \pmod 4$.

::: mathlib
`ZMod.isSquare_neg_one_iff'` · `Mathlib.NumberTheory.SumTwoSquares`

For a squarefree `n`, `IsSquare (-1 : ZMod n)` holds if and only if no divisor `q` of `n` satisfies `q % 4 = 3`. The form with prime factors is `ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three`. The proof uses the Chinese remainder theorem through `ZMod.isSquare_neg_one_mul`.

<?decl ZMod.isSquare_neg_one_iff'?>
:::

### Theorems and proofs

**Lemma (Identity of Diophantus).** For all $x, y, u, v$ in a commutative ring,
$$(x^2 + y^2)(u^2 + v^2) = (xu - yv)^2 + (xv + yu)^2.$$
So a product of two sums of two squares is a sum of two squares.

*Proof.* Expand both sides. The right side is $x^2u^2 - 2xuyv + y^2v^2 + x^2v^2 + 2xvyu + y^2u^2$, and the middle terms cancel. In $\mathbb{Z}[i]$ the identity is $N(\alpha)N(\beta) = N(\alpha\beta)$ for $\alpha = x + yi$ and $\beta = u + vi$ (Volume 6, Chapter 6). $\square$

::: mathlib
`Nat.sq_add_sq_mul` · `Mathlib.NumberTheory.SumTwoSquares`

The lemma for `ℕ`: from `a = x ^ 2 + y ^ 2` and `b = u ^ 2 + v ^ 2` it gives `∃ r s, a * b = r ^ 2 + s ^ 2`. The version for a commutative ring is `sq_add_sq_mul`. The proof passes to `ℤ`, since subtraction in `ℕ` truncates.

<?decl Nat.sq_add_sq_mul?>
:::

**Lemma (Primitive sums of two squares).** Let $n = x^2 + y^2$ with $\gcd(x, y) = 1$. Then $-1$ is a square modulo $n$. In particular, no prime $q \equiv 3 \pmod 4$ divides $n$.

*Proof.* Let $p$ be a prime divisor of $n$. If $p \mid y$, then $p \mid n - y^2 = x^2$, so $p \mid x$, against $\gcd(x, y) = 1$. So $\gcd(y, n) = 1$, and $y$ has an inverse $y'$ modulo $n$ (Volume 2, Chapter 6). Multiply $x^2 + y^2 \equiv 0 \pmod n$ by $y'^2$:
$$(xy')^2 + 1 \equiv 0 \pmod n.$$
So $-1 \equiv (xy')^2$ is a square modulo $n$. If a prime $q$ divides $n$, then $-1$ is also a square modulo $q$, and so $q = 2$ or $q \equiv 1 \pmod 4$. $\square$

::: mathlib
`ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime` · `Mathlib.NumberTheory.SumTwoSquares`

The first claim, for natural numbers. The integer form with `IsCoprime` is `ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime`. The second claim is `Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one`, with `p ∈ n.primeFactors` as the hypothesis on `p`.

<?decl ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime?>
:::

**Theorem (Sums of two squares).** Let $n \ge 1$. Then $n$ is a sum of two squares if and only if, for each prime $q \equiv 3 \pmod 4$, the exponent of $q$ in $n$ is even.

*Proof.* Suppose first the condition on the exponents. Write $n = a^2 b$ with $b$ squarefree: put the even part of each exponent into $a^2$ and the remaining exponent $0$ or $1$ into $b$. By the condition, no prime $q \equiv 3 \pmod 4$ divides $b$. So $b$ is a product of distinct primes $p$ with $p = 2$ or $p \equiv 1 \pmod 4$. Each of them is a sum of two squares: $2 = 1^2 + 1^2$, and Fermat's theorem of Volume 6, Chapter 6 covers the others. By the identity of Diophantus and induction on the number of factors, $b = u^2 + v^2$. Then $n = (au)^2 + (av)^2$.

Conversely, suppose $n = x^2 + y^2$, and let $q \equiv 3 \pmod 4$ be prime. Put $d = \gcd(x, y)$, which is not $0$ since $n \ge 1$. Write $x = dx'$ and $y = dy'$ with $\gcd(x', y') = 1$. Then
$$n = d^2 (x'^2 + y'^2).$$
By the last lemma, $q$ does not divide $x'^2 + y'^2$. So the exponent of $q$ in $n$ is its exponent in $d^2$, which is even. $\square$

::: mathlib
`Nat.Prime.sq_add_sq` · `Mathlib.NumberTheory.SumTwoSquares`

The prime case of Volume 6, Chapter 6, with the hypothesis `p % 4 ≠ 3`. The index of this edition has no declaration for the characterization of all $n$ by the exponents. The pieces are in the index, and a Lean proof assembles them as the paper proof does.

<?decl Nat.Prime.sq_add_sq?>
:::

**Lemma (Euler's four squares identity).** In a commutative ring,
$$(a^2 + b^2 + c^2 + d^2)(x^2 + y^2 + z^2 + w^2) = z_1^2 + z_2^2 + z_3^2 + z_4^2,$$
where
$$\begin{aligned} z_1 &= ax - by - cz - dw, & z_2 &= ay + bx + cw - dz, \\ z_3 &= az - bw + cx + dy, & z_4 &= aw + bz - cy + dx. \end{aligned}$$

*Proof.* Expand. Each of the sixteen products $a^2x^2, a^2y^2, \dots, d^2w^2$ appears once among the squares of the $z_i$. Each mixed product appears twice with opposite signs; for example $2axby$ has the sign $-$ in $z_1^2$ and $+$ in $z_2^2$. The identity is the multiplicativity of the quaternion norm. $\square$

::: mathlib
`euler_four_squares` · `Mathlib.NumberTheory.SumFourSquares`

The identity in a commutative ring, proved by `ring`. The version for `ℕ` is `Nat.euler_four_squares`.

<?decl euler_four_squares?>
:::

**Lemma (A multiple of $p$).** Let $p$ be an odd prime. There are integers $a, b$ and $k$ with $0 < k < p$ and $a^2 + b^2 + 1 = kp$.

*Proof.* The plan: count squares modulo $p$. The squares $a^2$ for $a = 0, 1, \dots, \frac{p-1}{2}$ are pairwise distinct modulo $p$: if $a^2 \equiv a'^2$, then $p \mid (a - a')(a + a')$, and $0 < a + a' < p$ unless $a = a' = 0$, so $p \mid a - a'$ and $a = a'$. So the set $A = \{a^2 \bmod p\}$ has $\frac{p+1}{2}$ elements. In the same way the set $B = \{-1 - b^2 \bmod p\}$ for $b = 0, \dots, \frac{p-1}{2}$ has $\frac{p+1}{2}$ elements. Since $|A| + |B| = p + 1 > p$, the two sets meet: $a^2 \equiv -1 - b^2 \pmod p$ for some $a, b$ in the range. So $a^2 + b^2 + 1 = kp$ with $k \ge 1$. The bound $a, b \le \frac{p-1}{2} < \frac p2$ gives
$$kp = a^2 + b^2 + 1 < \frac{p^2}{4} + \frac{p^2}{4} + 1 < p^2,$$
so $k < p$. $\square$

::: mathlib
`Int.exists_sq_add_sq_add_one_eq_mul` · `Mathlib.NumberTheory.SumFourSquares`

The lemma for every prime `p`. For $p = 2$ take $a = 1$, $b = 0$, $k = 1$.

<?decl Int.exists_sq_add_sq_add_one_eq_mul?>
:::

**Theorem (Lagrange, primes).** Every prime $p$ is a sum of four squares.

*Proof.* For $p = 2 = 1 + 1 + 0 + 0$ there is nothing to prove. Let $p$ be odd. By the last lemma some multiple $kp$ with $0 < k < p$ is a sum of four squares, namely $a^2 + b^2 + 1^2 + 0^2$. Let $m$ be the least positive integer such that $mp$ is a sum of four squares. Then $m < p$. Suppose $m > 1$. The plan: build a smaller multiple, which contradicts the choice of $m$.

Write $mp = x_1^2 + x_2^2 + x_3^2 + x_4^2$.

Case $m$ even. Then $x_1 + x_2 + x_3 + x_4 \equiv x_1^2 + \cdots + x_4^2 \equiv 0 \pmod 2$, so an even number of the $x_i$ are odd. Number them so that $x_1 \equiv x_2$ and $x_3 \equiv x_4 \pmod 2$. Then
$$\frac m2 p = \left(\frac{x_1 - x_2}{2}\right)^2 + \left(\frac{x_1 + x_2}{2}\right)^2 + \left(\frac{x_3 - x_4}{2}\right)^2 + \left(\frac{x_3 + x_4}{2}\right)^2,$$
with integer terms, since $\left(\frac{s - t}{2}\right)^2 + \left(\frac{s + t}{2}\right)^2 = \frac{s^2 + t^2}{2}$. This contradicts the choice of $m$.

Case $m$ odd, so $m \ge 3$. For each $i$ choose $y_i \equiv x_i \pmod m$ with $|y_i| \le \frac{m-1}{2}$. Then
$$y_1^2 + y_2^2 + y_3^2 + y_4^2 \equiv x_1^2 + \cdots + x_4^2 = mp \equiv 0 \pmod m,$$
so $\sum y_i^2 = mr$ for an integer $r \ge 0$, and $mr < 4 \cdot \frac{m^2}{4} = m^2$ gives $r < m$. If $r = 0$, all $y_i = 0$, so $m \mid x_i$ for each $i$, and $m^2 \mid mp$. Then $m \mid p$ with $1 < m < p$, which is false. So $0 < r < m$.

Apply Euler's identity to $(a, b, c, d) = (x_1, x_2, x_3, x_4)$ and $(x, y, z, w) = (y_1, -y_2, -y_3, -y_4)$. The second quadruple also has the sum of squares $mr$, so
$$m^2 rp = (mp)(mr) = z_1^2 + z_2^2 + z_3^2 + z_4^2,$$
with
$$\begin{aligned} z_1 &= x_1y_1 + x_2y_2 + x_3y_3 + x_4y_4, & z_2 &= -x_1y_2 + x_2y_1 - x_3y_4 + x_4y_3, \\ z_3 &= -x_1y_3 + x_2y_4 + x_3y_1 - x_4y_2, & z_4 &= -x_1y_4 - x_2y_3 + x_3y_2 + x_4y_1. \end{aligned}$$
Each $z_i$ is divisible by $m$. Indeed, modulo $m$ replace each $y_j$ by $x_j$. Then $z_1 \equiv x_1^2 + x_2^2 + x_3^2 + x_4^2 = mp \equiv 0$, and $z_2 \equiv -x_1x_2 + x_2x_1 - x_3x_4 + x_4x_3 = 0$; the same cancellation happens in $z_3$ and $z_4$. So $z_i = m t_i$ with integers $t_i$, and
$$rp = t_1^2 + t_2^2 + t_3^2 + t_4^2$$
with $0 < r < m$. This contradicts the choice of $m$. So $m = 1$. $\square$

**Theorem (Lagrange).** Every natural number is a sum of four squares.

*Proof.* $0 = 0^2 + 0^2 + 0^2 + 0^2$ and $1 = 1^2 + 0^2 + 0^2 + 0^2$. Every $n \ge 2$ is a product of primes (Volume 2, Chapter 2). Each prime is a sum of four squares by the last theorem, and a product of two sums of four squares is one by Euler's identity. Induction on the number of prime factors finishes the proof. $\square$

::: mathlib
`Nat.Prime.sum_four_squares` · `Mathlib.NumberTheory.SumFourSquares`

The prime case. The even case is the lemma `Int.sq_add_sq_of_two_mul_sq_add_sq`, which turns $2m = x^2 + y^2$ into $m = \left(\frac{x - y}{2}\right)^2 + \left(\frac{x + y}{2}\right)^2$, and the bound $r < m$ is `Int.lt_of_sum_four_squares_eq_mul`.

<?decl Nat.Prime.sum_four_squares?>
:::

::: mathlib
`Nat.sum_four_squares` · `Mathlib.NumberTheory.SumFourSquares`

The theorem of Lagrange for every `n : ℕ`, by induction on the prime factorization.

<?decl Nat.sum_four_squares?>
:::

### Examples

**Example (Two squares by factorization).** Take $n = 1105 = 5 \cdot 13 \cdot 17$. All three primes are $\equiv 1 \pmod 4$: $5 = 2^2 + 1^2$, $13 = 3^2 + 2^2$, $17 = 4^2 + 1^2$. The identity of Diophantus gives $5 \cdot 13 = (2 \cdot 3 - 1 \cdot 2)^2 + (2 \cdot 2 + 1 \cdot 3)^2 = 4^2 + 7^2 = 65$. Then $65 \cdot 17 = (4 \cdot 4 - 7 \cdot 1)^2 + (4 \cdot 1 + 7 \cdot 4)^2 = 9^2 + 32^2 = 81 + 1024 = 1105$. Other choices of signs give other representations, for example $1105 = 33^2 + 4^2$.

**Counterexample (An odd exponent).** The number $21 = 3 \cdot 7$ is not a sum of two squares: the candidates $21 - 0, 21 - 1, 21 - 4, 21 - 9, 21 - 16$ are $21, 20, 17, 12, 5$, and none is a square. The theorem predicts this from the odd exponent of $3$.

**Counterexample (Three squares are not enough).** A square is $0$, $1$ or $4$ modulo $8$. A sum of three of these values is never $7$ modulo $8$. So $7 = 2^2 + 1^2 + 1^2 + 1^2$ needs four squares, and so does every $n \equiv 7 \pmod 8$. Gauss proved that $n$ is a sum of three squares if and only if $n$ is not of the form $4^a(8b + 7)$. The index of this edition has no declaration for this theorem of the three squares.

**Example (The descent for $p = 7$).** The lemma searches $a, b \le 3$ with $7 \mid a^2 + b^2 + 1$ and finds $3^2 + 2^2 + 1 = 14 = 2 \cdot 7$, so $m \le 2$ with $14 = 3^2 + 2^2 + 1^2 + 0^2$. The even case pairs $3$ with $1$ and $2$ with $0$: $7 = \left(\frac{3-1}{2}\right)^2 + \left(\frac{3+1}{2}\right)^2 + \left(\frac{2-0}{2}\right)^2 + \left(\frac{2+0}{2}\right)^2 = 1 + 4 + 1 + 1$.

### The library around it

The file `Mathlib.NumberTheory.SumTwoSquares` has the identity, the prime case and the lemmas `ZMod.isSquare_neg_one_*`. The file `Mathlib.NumberTheory.SumFourSquares` has Euler's identity, the lemmas of the descent and the two theorems.

`Mathlib.NumberTheory.Zsqrtd.GaussianInt` gives a second route to the prime case through the Gaussian integers. `GaussianInt` is the abbreviation `ℤ√(-1)`, so an element has fields `re` and `im`, and `Zsqrtd.norm x` is $a^2 + b^2$ for $x = a + bi$. The ring hom `GaussianInt.toComplex` embeds it in `ℂ`, with `GaussianInt.toComplex_def`, `GaussianInt.toComplex_injective` and one simp lemma per ring operation, and `GaussianInt.intCast_real_norm` says that the norm is `Complex.normSq` of the image. Division `GaussianInt.div_def` rounds the real and imaginary parts of $x \bar y / N(y)$ to the nearest integers, so `GaussianInt.normSq_div_sub_div_lt_one` holds and `GaussianInt.norm_mod_lt` says that the remainder has smaller norm. This gives the instance `GaussianInt.instEuclideanDomain`, hence unique factorization. The bridge to this section is `GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible`: a prime $p$ that is not irreducible in `GaussianInt` is a sum of two squares, because a proper factor $x$ of $p$ has norm $p$. The other lemmas, such as `GaussianInt.norm_nonneg`, `GaussianInt.norm_eq_zero` and `GaussianInt.natAbs_norm_eq`, move between the integer norm and its absolute value.

Common errors of a learner:

- `IsSquare (-1 : ZMod n)` depends on `n` through the type. For `n = 0` the ring `ZMod 0` is `ℤ`, where $-1$ is not a square.
- In `ℕ`, the term $xu - yv$ of the identity of Diophantus truncates at $0$. Work in `ℤ` and take `natAbs` at the end.

### Exercises

1. (A) Decide which of $90$, $91$, $98$, $99$ and $325$ are sums of two squares. Write the ones that are as sums of two squares.
2. (A) Write $1105$ as a sum of two squares in four ways, up to order and signs.
3. (A) Write $79$ as a sum of four squares, and show that it is not a sum of three squares.
4. (B) Show that $n$ is a sum of two squares of rational numbers if and only if it is a sum of two squares of integers.
5. (B) Show that a number $n \equiv 3 \pmod 4$ is not a sum of two squares without the theorem, and deduce that it has a prime factor $q \equiv 3 \pmod 4$ with an odd exponent.
6. (B) Let $r_2(n)$ be the number of pairs $(x, y) \in \mathbb{Z}^2$ with $x^2 + y^2 = n$. Compute $r_2(5)$, $r_2(25)$ and $r_2(65)$, and guess a formula in terms of the divisors of $n$.
7. (B) Show that every $n \ge 169$ is a sum of five positive squares. Hint: write $n - 169$ as a sum of $k \le 4$ positive squares, and use $169 = 13^2 = 12^2 + 5^2 = 12^2 + 4^2 + 3^2 = 10^2 + 8^2 + 2^2 + 1^2 = 12^2 + 4^2 + 2^2 + 2^2 + 1^2$.
8. (B) Show that no number of the form $4^a(8b + 7)$ is a sum of three squares. Hint: if $4n = x^2 + y^2 + z^2$, then $x, y, z$ are even.
9. (C) Show that $n \ge 1$ is a sum of two squares if and only if $n = a^2 b$ for some $a, b \ge 1$ such that $-1$ is a square modulo $b$. Hint: one direction is the lemma on primitive sums; for the other use `ZMod.isSquare_neg_one_iff'` on the squarefree part.

### Notes and history

Girard and Fermat stated the theorem on sums of two squares for all $n$, and Euler proved it. Bachet stated in 1621 that every number is a sum of four squares, and Lagrange gave the first proof in 1770, with the identity of Euler, who found it in 1748. Gauss proved the three squares theorem in the *Disquisitiones Arithmeticae* (1801), after a partial proof by Legendre. A reference for all of this section is Ireland and Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 17, and Hardy and Wright, *An Introduction to the Theory of Numbers*, Chapter 20.

### Reference

<?reference?>
