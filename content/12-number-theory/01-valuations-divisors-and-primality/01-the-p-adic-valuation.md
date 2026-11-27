---
title: The p-adic valuation
kind: theory
modules:
  - Mathlib.NumberTheory.Padics.PadicVal.Defs
  - Mathlib.NumberTheory.Padics.PadicVal.Basic
  - Mathlib.NumberTheory.Multiplicity
explains:
  E3: [padicValInt, padicValRat, multiplicity_factorial, multiplicity_choose, Nat.multiplicity_pow_sub_pow]
  E2: [Nat.multiplicity_mul, padicValInt.mul, padicValRat.mul, padicValRat_def, multiplicity_dvd_iff_le, padicValRat.min_le_padicValRat_add, padicValRat.add_eq_of_lt, sub_one_mul_multiplicity_choose_eq_sub_sum_digits, Nat.multiplicity_pow_two_sub_pow]
  E1: auto
families: []
requires: [V02.C02, V02.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The p-adic valuation

### Overview

For a fixed prime $p$, the exponent of $p$ in the factorization of $n$ (Volume 2, Chapter 2) is a number $v_p(n)$, the $p$-adic valuation of $n$. For example, the number of zeros at the end of $100!$ is $\min(v_2(100!), v_5(100!))$.

This section proves the two rules of $v_p$ and the formulas of Legendre, Kummer and the lifting the exponent lemma. In this edition of Mathlib the valuation on $\mathbb{N}$ is the general function `multiplicity`.

### Definitions

**Definition (The $p$-adic valuation on $\mathbb{Z}$).** Let $p$ be a prime and $n$ a nonzero integer. The $p$-adic valuation $v_p(n)$ is the largest natural number $k$ with $p^k \mid n$.

The largest $k$ exists, because $p^k \mid n$ implies $p^k \leq |n|$. On paper $v_p(0) = \infty$. If $n = \pm p_1^{e_1} \cdots p_r^{e_r}$ with distinct primes, then $v_{p_i}(n) = e_i$, by the uniqueness of the factorization. By the definition, for $n \neq 0$,
$$p^k \mid n \iff k \leq v_p(n).$$
So to prove $v_p(n) = k$, it is sufficient to show $p^k \mid n$ and $p^{k+1} \nmid n$.

::: mathlib
`padicValNat` · `Mathlib.Data.Nat.PadicValNat`

The valuation on `ℕ` with the junk value `padicValNat p 0 = 0`. In this edition the library states its theorems with `multiplicity p n`, and the two agree by `Nat.padicValNat_def`. The old names such as `padicValNat.mul` are deprecated aliases of names such as `Nat.multiplicity_mul`.

<?decl padicValNat?>
:::

::: mathlib
`multiplicity` · `Mathlib.RingTheory.Multiplicity`

In any monoid, `multiplicity a b` is the largest `n` with `a ^ n ∣ b`, and `0` when every power divides `b`. The version with the value `⊤` is `emultiplicity`. So `multiplicity p 0 = 0`, and many theorems need `n ≠ 0`.

<?decl multiplicity?>
:::

::: mathlib
`multiplicity_dvd_iff_le` · `Mathlib.NumberTheory.Padics.PadicVal.Basic`

The equivalence $p^k \mid n \iff k \leq v_p(n)$ for `n ≠ 0`. The prime is an instance `[Fact p.Prime]`; from a hypothesis `hp : p.Prime`, supply it with `haveI := Fact.mk hp`.

<?decl multiplicity_dvd_iff_le?>
:::

::: mathlib
`padicValInt` · `Mathlib.NumberTheory.Padics.PadicVal.Basic`

The valuation on `ℤ` with values in `ℕ`, defined as `multiplicity p z.natAbs`.

<?decl padicValInt?>
:::

**Definition (The $p$-adic valuation on $\mathbb{Q}$).** For $x = a/b$ with $a, b$ nonzero integers, put $v_p(x) = v_p(a) - v_p(b) \in \mathbb{Z}$.

The value does not depend on the fraction: if $a/b = c/d$, then $ad = bc$, and the product rule below gives $v_p(a) + v_p(d) = v_p(b) + v_p(c)$. For example $v_2(12/7) = 2$ and $v_7(12/7) = -1$.

::: mathlib
`padicValRat` · `Mathlib.NumberTheory.Padics.PadicVal.Basic`

The valuation on `ℚ` with values in `ℤ`, and `padicValRat p 0 = 0`. By `padicValRat_def` it is `padicValInt p q.num - multiplicity p q.den` on the reduced fraction; `padicValRat.defn` gives the same value for any fraction.

<?decl padicValRat?>
:::

### Theorems and proofs

**Theorem (The product rule).** For a prime $p$ and nonzero integers $a, b$, $v_p(ab) = v_p(a) + v_p(b)$. The same holds for nonzero rationals, and $v_p(x/y) = v_p(x) - v_p(y)$.

*Proof.* Write $a = p^\alpha a'$ and $b = p^\beta b'$ with $\alpha = v_p(a)$, $\beta = v_p(b)$. Then $p \nmid a'$, since otherwise $p^{\alpha+1} \mid a$, and $p \nmid b'$. So $ab = p^{\alpha+\beta} a'b'$ and $p^{\alpha + \beta} \mid ab$. By Euclid's lemma, $p \nmid a'b'$, so $p^{\alpha+\beta+1} \nmid ab$. For $x = a/b$ and $y = c/d$, $xy = ac/bd$, and the rule for integers gives $v_p(xy) = v_p(a) + v_p(c) - v_p(b) - v_p(d)$. The quotient rule follows from $v_p(y) + v_p(x/y) = v_p(x)$. $\square$

So $v_p : \mathbb{Q}^\times \to \mathbb{Z}$ is a group homomorphism.

::: mathlib
`Nat.multiplicity_mul` · `Mathlib.NumberTheory.Padics.PadicVal.Basic`

The product rule on `ℕ`, with `a ≠ 0` and `b ≠ 0`. The versions on `ℤ` and `ℚ` are `padicValInt.mul` and `padicValRat.mul`, and `padicValRat.div` and `padicValRat.pow` are the quotient and the power.

<?decl Nat.multiplicity_mul?>
:::

**Theorem (The ultrametric inequality).** Let $x, y \in \mathbb{Q}$ be nonzero with $x + y \neq 0$. Then $v_p(x + y) \geq \min(v_p(x), v_p(y))$, with equality when $v_p(x) \neq v_p(y)$.

*Proof.* Write $x = p^a u / w$ and $y = p^b u'/w'$ with $u, w, u', w'$ prime to $p$, and assume $a \leq b$. Then
$$x + y = p^a \cdot \frac{u w' + p^{b-a} u' w}{w w'}.$$
The numerator $N$ is a nonzero integer and $p \nmid ww'$, so $v_p(x + y) = a + v_p(N) \geq a$. If $a < b$, then $N \equiv uw' \not\equiv 0 \pmod p$, so $v_p(N) = 0$. $\square$

::: mathlib
`padicValRat.min_le_padicValRat_add` · `Mathlib.NumberTheory.Padics.PadicVal.Basic`

The inequality, with only the hypothesis `q + r ≠ 0`; the junk value at `0` makes the other cases trivial. The case of equality is `padicValRat.add_eq_of_lt`.

<?decl padicValRat.min_le_padicValRat_add?>
:::

**Theorem (Legendre's formula).** For a prime $p$ and $n \geq 0$,
$$v_p(n!) = \sum_{i \geq 1} \left\lfloor \frac{n}{p^i} \right\rfloor ,$$
and $(p - 1)\, v_p(n!) = n - s_p(n)$, where $s_p(n)$ is the sum of the digits of $n$ in base $p$.

*Proof.* By the product rule, $v_p(n!) = \sum_{m=1}^{n} v_p(m)$, and $v_p(m)$ is the number of $i \geq 1$ with $p^i \mid m$. Count the pairs $(m, i)$ with $p^i \mid m$ in the other order:
$$v_p(n!) = \sum_{i \geq 1} \#\{ m \leq n : p^i \mid m \} = \sum_{i \geq 1} \left\lfloor \frac{n}{p^i} \right\rfloor ,$$
since the multiples of $p^i$ up to $n$ are $p^i, 2p^i, \dots, \lfloor n/p^i \rfloor p^i$. For the second formula write $n = \sum_j d_j p^j$ with digits $0 \leq d_j < p$. Then $\lfloor n/p^i \rfloor = \sum_{j \geq i} d_j p^{j-i}$, so
$$\sum_{i \geq 1} \left\lfloor \frac{n}{p^i} \right\rfloor = \sum_{j} d_j \sum_{i=1}^{j} p^{j-i} = \sum_{j} d_j \frac{p^j - 1}{p - 1},$$
and multiplication by $p - 1$ gives $n - s_p(n)$. $\square$

::: mathlib
`multiplicity_factorial` · `Mathlib.NumberTheory.Padics.PadicVal.Basic`

Legendre's formula as `∑ i ∈ Finset.Ico 1 b, n / p ^ i` for any `b > Nat.log p n`. Division in `ℕ` is the floor, and any large bound `b` works. The digit form is `Nat.Prime.sub_one_mul_multiplicity_factorial` in `Mathlib.Data.Nat.Multiplicity`.

<?decl multiplicity_factorial?>
:::

**Theorem (Kummer).** For $0 \leq k \leq n$, $v_p\binom{n}{k}$ is the number of $i \geq 1$ with $(k \bmod p^i) + ((n - k) \bmod p^i) \geq p^i$, that is, the number of carries in the addition of $k$ and $n - k$ in base $p$. Equivalently, $(p - 1)\, v_p\binom{n}{k} = s_p(k) + s_p(n - k) - s_p(n)$.

*Proof.* By Legendre's formula,
$$v_p\binom{n}{k} = \sum_{i \geq 1} \left( \left\lfloor \frac{n}{p^i} \right\rfloor - \left\lfloor \frac{k}{p^i} \right\rfloor - \left\lfloor \frac{n-k}{p^i} \right\rfloor \right).$$
Write $k = q_1 p^i + r_1$ and $n - k = q_2 p^i + r_2$ with $0 \leq r_1, r_2 < p^i$. Then $n = (q_1 + q_2)p^i + r_1 + r_2$ with $r_1 + r_2 < 2p^i$, so the term of index $i$ is $1$ if $r_1 + r_2 \geq p^i$ and $0$ otherwise. The lowest $i$ digits of $k$ and $n - k$ represent $r_1$ and $r_2$, so $r_1 + r_2 \geq p^i$ exactly when the addition carries from position $i - 1$ to position $i$. The digit form follows from Legendre's formula for $n$, $k$ and $n - k$. $\square$

::: mathlib
`multiplicity_choose` · `Mathlib.NumberTheory.Padics.PadicVal.Basic`

Kummer's theorem as the cardinality of the set of `i ∈ Finset.Ico 1 b` with `p ^ i ≤ k % p ^ i + (n - k) % p ^ i`. The library has no notion of a carry; this set plays its role. The digit form is `sub_one_mul_multiplicity_choose_eq_sub_sum_digits`, with `(p.digits k).sum` for $s_p(k)$.

<?decl multiplicity_choose?>
:::

**Theorem (Lifting the exponent).** Let $p$ be an odd prime, $x \neq y$ integers with $p \mid x - y$ and $p \nmid x$, and $n \geq 1$. Then
$$v_p(x^n - y^n) = v_p(x - y) + v_p(n).$$

*Proof.* Put $S_m = \sum_{i=0}^{m-1} x^i y^{m-1-i}$, so $x^m - y^m = (x - y) S_m$ and $v_p(x^m - y^m) = v_p(x - y) + v_p(S_m)$.

Step 1: if $p \nmid m$, then $v_p(S_m) = 0$. Since $y \equiv x \pmod p$, each term is $\equiv x^{m-1}$, so $S_m \equiv m x^{m-1} \not\equiv 0 \pmod p$.

Step 2: $v_p(S_p) = 1$. Write $y = x + t$ with $p \mid t$. Then $y^j \equiv x^j + j x^{j-1} t \pmod{p^2}$, so
$$S_p \equiv \sum_{i=0}^{p-1} \left( x^{p-1} + (p - 1 - i) x^{p-2} t \right) = p\, x^{p-1} + p \cdot \frac{p-1}{2}\, x^{p-2} t \pmod{p^2}.$$
Since $p$ is odd, $(p-1)/2$ is an integer, and the second term is divisible by $p^2$. So $S_p \equiv p x^{p-1} \pmod{p^2}$, and $v_p(S_p) = 1$ because $p \nmid x$.

Step 3: $x^p, y^p$ satisfy the hypotheses again, so by induction $v_p(x^{p^a} - y^{p^a}) = v_p(x - y) + a$. Write $n = p^a m$ with $p \nmid m$ and apply Step 1 to $X = x^{p^a}$, $Y = y^{p^a}$ and the exponent $m$: $v_p(x^n - y^n) = v_p(X - Y) = v_p(x - y) + v_p(n)$. $\square$

::: mathlib
`Nat.multiplicity_pow_sub_pow` · `Mathlib.NumberTheory.Multiplicity`

The theorem on `ℕ`, with `Odd p`, `y < x` (so the subtraction does not truncate), `p ∣ x - y`, `¬p ∣ x` and `n ≠ 0`. The version on `ℤ` is `Int.emultiplicity_pow_sub_pow`. The form for $p = 2$ is `Nat.multiplicity_pow_two_sub_pow`: $v_2(x^n - y^n) + 1 = v_2(x + y) + v_2(x - y) + v_2(n)$ for odd $x, y$ and even $n$.

<?decl Nat.multiplicity_pow_sub_pow?>
:::

### Examples

**Example (The zeros at the end of $100!$).** By Legendre's formula, $v_5(100!) = 20 + 4 = 24$ and $v_2(100!) = 50 + 25 + 12 + 6 + 3 + 1 = 97$. So $100!$ ends in $\min(97, 24) = 24$ zeros. The digit form checks the first value: $100 = 400_5$, so $s_5(100) = 4$ and $(100 - 4)/4 = 24$.

**Example (The central binomial coefficient).** For $p = 2$, Kummer's theorem gives $v_2\binom{2n}{n} = 2 s_2(n) - s_2(2n) = s_2(n)$, since the binary digits of $2n$ are those of $n$ moved one place. For $n = 10 = 1010_2$, $s_2(10) = 2$, and indeed $\binom{20}{10} = 184756 = 4 \cdot 46189$ with $46189$ odd.

**Example (Lifting the exponent).** With $p = 3$, $x = 4$, $y = 1$, the lemma gives $v_3(4^9 - 1) = 1 + v_3(9) = 3$. A check: $4^9 - 1 = 262143 = 27 \cdot 9709$, and $9709 = 3 \cdot 3236 + 1$.

**Counterexample (The prime $2$).** Take $p = 2$, $x = 3$, $y = 1$, $n = 2$. Then $v_2(3^2 - 1) = v_2(8) = 3$, but $v_2(3 - 1) + v_2(2) = 2$. The proof fails at Step 2: $S_2 = x + y = 4$ has $v_2(S_2) = 2$. The form for $p = 2$ gives the right value, $v_2(4) + v_2(2) + v_2(2) - 1 = 3$. The hypothesis $p \nmid x$ is needed too: for $p = 3$, $x = 6$, $y = 3$, $n = 2$, $v_3(27) = 3 \neq 1 = v_3(3) + v_3(2)$.

### The library around it

Besides the theorems above, `Mathlib.NumberTheory.Padics.PadicVal.Basic` has `Nat.multiplicity_prime_pow`, `multiplicity_primes`, `dvd_iff_multiplicity_ne_zero` and the bound `multiplicity_le_nat_log`. The families `padicValInt.*` and `padicValRat.*` are parallel, linked by `padicValRat.of_nat`. `Mathlib.NumberTheory.Multiplicity` also has the forms with a sum, `*_pow_add_pow`.

Common errors of a learner:

- `multiplicity p 0 = 0`, so the product rule needs `a ≠ 0` and `b ≠ 0`. On paper $v_p(0) = \infty$ and the rule holds without them.
- `x ^ n - y ^ n` in `ℕ` truncates to $0$ when $x < y$; this is why `Nat.multiplicity_pow_sub_pow` has `y < x`.
- Equality in the ultrametric inequality needs $v_p(x) \neq v_p(y)$: $v_p(1) = v_p(p - 1) = 0$, but $v_p(1 + (p - 1)) = 1$.

### Exercises

1. (A) Compute $v_3(1000!)$, $v_7(1000!)$ and the number of zeros at the end of $1000!$. Hint: the last one is $249$.
2. (A) Compute $v_7\binom{100}{50}$ with Kummer's theorem. Hint: write $50$ in base $7$.
3. (A) Show that $v_p(n!) < n/(p - 1)$ for $n \geq 1$. Hint: the digit form and $s_p(n) \geq 1$.
4. (B) Show that $p^{v_p\binom{n}{k}} \leq n$ for $0 \leq k \leq n$, $n \geq 1$. Hint: a carry at index $i$ needs $p^i \leq n$. Chapter 7 uses this bound for Bertrand's postulate.
5. (B) Find the largest $k$ with $3^k \mid 10^{81} - 1$ and the largest $k$ with $7^k \mid 2^{42} - 1$. Hint: for the second, use $2^{42} = 8^{14}$.
6. (B) Prove $v_p(x^n + y^n) = v_p(x + y) + v_p(n)$ for odd $p$, $p \mid x + y$, $p \nmid x$, $x + y \neq 0$ and odd $n$. Hint: replace $y$ by $-y$.
7. (C) Prove the form for $p = 2$. Hint: for $n = 2^a m$ with $m$ odd, factor $x^{2^a} - y^{2^a} = (x - y)(x + y)(x^2 + y^2) \cdots (x^{2^{a-1}} + y^{2^{a-1}})$; each factor after the second is $2$ times an odd number.
8. (C) Show that $1 + \frac12 + \dots + \frac1n$ is not an integer for $n \geq 2$. Hint: exactly one $m \leq n$ has the largest $v_2(m)$; use the case of equality in the ultrametric inequality.

### Notes and history

Legendre gave the formula for $v_p(n!)$ in the second edition (1808) of his *Essai sur la théorie des nombres*. Kummer proved the theorem on carries in 1852. A standard reference is Ireland and Rosen, *A Classical Introduction to Modern Number Theory*.

In this edition the theorems on `ℕ` move from `padicValNat` to `multiplicity`, and the old names stay as deprecated aliases.

### Reference

<?reference?>
