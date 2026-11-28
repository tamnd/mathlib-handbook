---
title: Digits, logarithms and square roots in ℕ
kind: api
modules:
  - Mathlib.Data.Nat.Digits.Defs
  - Mathlib.Data.Nat.Digits.Lemmas
  - Mathlib.Data.Nat.Digits.Div
  - Mathlib.Data.Nat.Log
  - Mathlib.Data.Nat.Sqrt
  - Mathlib.Data.Nat.NthRoot.Defs
explains:
  E2: [Nat.ofDigits_digits, Nat.digits_add_two_add_one, Nat.modEq_nine_digits_sum, Nat.length_digits, Nat.le_log_iff_pow_le, Nat.clog_le_iff_le_pow, Nat.le_sqrt, Nat.sqrt_add_eq]
  E1: auto
families: []
requires: [V01.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Digits, logarithms and square roots in ℕ

### Overview

Each natural number $n$ has a unique expansion $n = d_0 + d_1 b + \cdots + d_{\ell - 1} b^{\ell - 1}$ in a base $b \geq 2$, with digits $0 \leq d_i < b$ and a last digit $d_{\ell - 1} \neq 0$. The modules of this section define the list of digits, the inverse map from lists to numbers, and the divisibility tests by the sum of the digits. They also define three functions that invert powers: the floor logarithm $\lfloor \log_b n \rfloor$, the ceiling logarithm $\lceil \log_b n \rceil$, and the floor square root $\lfloor \sqrt{n} \rfloor$, all with values in $\mathbb{N}$.

These functions appear in the bounds of number theory and combinatorics. The number of digits of $n$ is $\lfloor \log_b n \rfloor + 1$, the exponent of a prime in a binomial coefficient is at most $\lfloor \log_p n \rfloor$, and a number $n > 1$ with no prime factor at most $\lfloor \sqrt{n} \rfloor$ is prime. The section uses the division algorithm of Chapter 2 and the congruences of Chapter 3.

### The library around it

#### The digits and the inverse map

The function `Nat.digits b n` is the list of the digits of $n$ in base $b$, with the least significant digit first. So `Nat.digits 10 123` is `[3, 2, 1]`. For $b \geq 2$ the list comes from the division algorithm: the first digit is $n \bmod b$, and the rest is the list of digits of $\lfloor n / b \rfloor$. The lemma `Nat.digits_add_two_add_one` states this recursion for $n + 1$ in the base $b + 2$, and `Nat.digits_def'` and `Nat.digits_eq_cons_digits_div` state it under the hypotheses $1 < b$ and $n \neq 0$. The number $0$ has the empty list of digits, by `Nat.digits_zero`. The definition also gives values for the bases $0$ and $1$: `Nat.digits_one` says that the digits of $n$ in base $1$ are $n$ ones, and `Nat.digits_zero_succ'` says that in base $0$ the list is $[n]$ for $n \neq 0$.

The inverse map is `Nat.ofDigits b L`, the value $\sum_i L_i b^i$ of a list $L$. Its base $b$ can be in any semiring, so the same function computes the value of a list in $\mathbb{Z}$ or in `ZMod k`. The defining equations are `Nat.ofDigits_nil` and `Nat.ofDigits_cons`: $\mathrm{ofDigits}_b(d :: L) = d + b \cdot \mathrm{ofDigits}_b(L)$. The main theorem is `Nat.ofDigits_digits`:
$$\mathrm{ofDigits}_b(\mathrm{digits}_b(n)) = n \quad \text{for all } b, n.$$
*Proof.* For $b \geq 2$, strong induction on $n$. For $n = 0$ both sides are $0$. For $n > 0$, the digits of $n$ are $(n \bmod b) :: \mathrm{digits}_b(\lfloor n / b \rfloor)$, and $\lfloor n / b \rfloor < n$. So the value is $(n \bmod b) + b \lfloor n / b \rfloor$ by the induction hypothesis, and this is $n$ by the division algorithm. The bases $0$ and $1$ are direct computations. $\square$

So `Nat.digits b` is injective (`Nat.digits.injective`, `Nat.digits_inj_iff`). In the other direction, `Nat.digits_ofDigits` says that a list $L$ is the list of digits of its value when all its entries are smaller than $b$ and its last entry is not $0$. The conditions are the properties of a list of digits: `Nat.digits_lt_base` says each digit is less than $b$, and `Nat.getLast_digit_ne_zero` says that the last digit is not $0$.

The library has lemmas for each operation on lists.

| Lean name | Statement |
|---|---|
| `Nat.ofDigits_append` | $\mathrm{ofDigits}_b(L_1 \mathbin{+\!+} L_2) = \mathrm{ofDigits}_b(L_1) + b^{|L_1|} \mathrm{ofDigits}_b(L_2)$ |
| `Nat.digits_add` | $\mathrm{digits}_b(x + b y) = x :: \mathrm{digits}_b(y)$ for $x < b$, if $x \neq 0$ or $y \neq 0$ |
| `Nat.digits_base_pow_mul` | the digits of $b^k m$ are $k$ zeros and then the digits of $m$, for $m > 0$ |
| `Nat.self_mod_pow_eq_ofDigits_take` | $n \bmod b^i$ is the value of the first $i$ digits |
| `Nat.self_div_pow_eq_ofDigits_drop` | $\lfloor n / b^i \rfloor$ is the value of the digits after the first $i$ |
| `Nat.getD_digits` | the digit at place $i$ is $\lfloor n / b^i \rfloor \bmod b$ |
| `Nat.ofDigits_lt_base_pow_length` | a list of $\ell$ digits less than $b$ has value less than $b^\ell$ |
| `Nat.digit_sum_le` | the sum of the digits of $n$ is at most $n$ |

The module `Mathlib.Data.Nat.Digits.Lemmas` adds the number of digits and lists of a fixed length. The lemma `Nat.length_digits` says that for $1 < b$ and $n \neq 0$ the list has $\lfloor \log_b n \rfloor + 1$ entries. *Proof.* Let $\ell$ be the length. The value of $\ell$ digits less than $b$ is less than $b^\ell$, so $n < b^\ell$. The last digit is at least $1$, so $b^{\ell - 1} \leq n$. Thus $\ell - 1$ is the largest $k$ with $b^k \leq n$, which is $\lfloor \log_b n \rfloor$. $\square$ The forms `Nat.digits_length_le_iff` and `Nat.lt_digits_length_iff` state $|\mathrm{digits}_b(n)| \leq k \iff n < b^k$ and its negation. The function `Nat.digitsAppend b l n` pads the list of digits with zeros to length $l$. With it, `Nat.bijOn_ofDigits` says that `Nat.ofDigits b` is a bijection from the lists of length $l$ with entries less than $b$ onto $\{0, \ldots, b^l - 1\}$. The finite set of these lists is `List.fixedLengthDigits`, with $b^l$ elements by `List.card_fixedLengthDigits`. For base $2$, `Nat.digits_two_eq_bits` relates the digits to the list `Nat.bits` of booleans.

#### Divisibility by the sum of the digits

Since $10 \equiv 1 \pmod 9$, a number is congruent to the sum of its decimal digits modulo $9$. This is `Nat.modEq_nine_digits_sum`, and the general form is `Nat.modEq_digits_sum`: if $b' \equiv 1 \pmod b$, then $n \equiv s_{b'}(n) \pmod b$, where $s_{b'}(n)$ is the sum of the digits in base $b'$. *Proof.* Reduce the base modulo $b$: by `Nat.ofDigits_modEq`, $\mathrm{ofDigits}_{b'}(L) \equiv \mathrm{ofDigits}_{b' \bmod b}(L) \pmod b$, because $\mathrm{ofDigits}$ is a polynomial in the base. With $b' \bmod b = 1$ the right side is the sum of the list, by `Nat.ofDigits_one`. Apply this to $L = \mathrm{digits}_{b'}(n)$ and use `Nat.ofDigits_digits`. $\square$

The module `Mathlib.Data.Nat.Digits.Div` gives the tests of school arithmetic: `Nat.three_dvd_iff` and `Nat.nine_dvd_iff` by the sum of the digits, and `Nat.eleven_dvd_iff` by the alternating sum of the digits, since $10 \equiv -1 \pmod{11}$. The alternating form uses the base $-1$ in $\mathbb{Z}$, with `Nat.ofDigits_neg_one`. A consequence is `Nat.eleven_dvd_of_palindrome`: a palindrome with an even number of digits is divisible by $11$. The general tool is `Nat.dvd_iff_dvd_ofDigits`, which replaces the base $b'$ by any integer $c$ with $b \mid b' - c$.

#### Logarithms

The module `Mathlib.Data.Nat.Log` defines two logarithms with values in $\mathbb{N}$. The floor logarithm `Nat.log b n` is the largest $k$ with $b^k \leq n$, and the ceiling logarithm `Nat.clog b n` is the least $k$ with $n \leq b^k$. Both have the junk value $0$ when $b \leq 1$, by `Nat.log_of_left_le_one` and `Nat.clog_of_left_le_one`. Also `Nat.log b 0 = 0` by `Nat.log_zero_right`.

The two functions are characterized by Galois connections with the power map $k \mapsto b^k$. For $1 < b$ and $n \neq 0$, `Nat.le_log_iff_pow_le` says
$$k \leq \lfloor \log_b n \rfloor \iff b^k \leq n,$$
and for $1 < b$, `Nat.clog_le_iff_le_pow` says $\lceil \log_b n \rceil \leq k \iff n \leq b^k$. *Proof of the first.* The power map is strictly increasing for $b > 1$, and $b^k > n$ for large $k$. So the set $\{k : b^k \leq n\}$ is a nonempty initial segment of $\mathbb{N}$, since $b^0 = 1 \leq n$. Its largest element is $\lfloor \log_b n \rfloor$, and $k$ is in the set if and only if $k$ is at most this largest element. $\square$ The hypothesis $n \neq 0$ is necessary: $\lfloor \log_b 0 \rfloor = 0$, but $b^0 = 1 > 0$.

Most lemmas are consequences of the Galois connections. The main ones are these.

| Lean name | Statement |
|---|---|
| `Nat.pow_log_le_self` | $b^{\lfloor \log_b n \rfloor} \leq n$ for $n \neq 0$ |
| `Nat.lt_pow_succ_log_self` | $n < b^{\lfloor \log_b n \rfloor + 1}$ for $1 < b$ |
| `Nat.log_eq_iff` | $\lfloor \log_b n \rfloor = m \iff b^m \leq n < b^{m + 1}$, under a side condition |
| `Nat.log_pow` | $\lfloor \log_b b^k \rfloor = k$ for $1 < b$ |
| `Nat.log_mul_base` | $\lfloor \log_b (n b) \rfloor = \lfloor \log_b n \rfloor + 1$ for $1 < b$, $n \neq 0$ |
| `Nat.log_div_base` | $\lfloor \log_b \lfloor n / b \rfloor \rfloor = \lfloor \log_b n \rfloor - 1$ |
| `Nat.le_pow_clog` | $n \leq b^{\lceil \log_b n \rceil}$ for $1 < b$ |
| `Nat.log_le_clog` | $\lfloor \log_b n \rfloor \leq \lceil \log_b n \rceil$ |
| `Nat.log_monotone` | $n \mapsto \lfloor \log_b n \rfloor$ is monotone |
| `Nat.log_anti_left` | for a fixed $n$, the logarithm decreases as the base increases |

The base $2$ has a computed form in core Lean, and `Nat.log2_eq_log_two` identifies it with `Nat.log 2`. The lemma `Nat.log_two_bit` says that appending a bit to a nonzero number adds $1$ to the logarithm in base $2$.

#### Square roots and $n$-th roots

The integer square root `Nat.sqrt n` is the largest $m$ with $m^2 \leq n$; it is defined in core Lean by an iteration of Newton's method, and the module `Mathlib.Data.Nat.Sqrt` proves its properties. The characterization is the Galois connection `Nat.le_sqrt`:
$$m \leq \lfloor \sqrt{n} \rfloor \iff m \cdot m \leq n,$$
and its dual `Nat.sqrt_lt`: $\lfloor \sqrt{m} \rfloor < n \iff m < n \cdot n$. Each lemma with `m * m` has a form with `m ^ 2` and a prime in the name, such as `Nat.le_sqrt'` and `Nat.sqrt_lt'`.

From the characterization come the usual facts. The value at a square is `Nat.sqrt_eq`: $\lfloor \sqrt{n^2} \rfloor = n$. More generally, `Nat.sqrt_add_eq` says $\lfloor \sqrt{n^2 + a} \rfloor = n$ for $a \leq 2n$. *Proof.* By `Nat.le_sqrt`, $n \leq \lfloor \sqrt{n^2 + a} \rfloor$ since $n^2 \leq n^2 + a$. By `Nat.sqrt_lt`, $\lfloor \sqrt{n^2 + a} \rfloor < n + 1$ since $n^2 + a \leq n^2 + 2n < (n + 1)^2$. $\square$ The lemma `Nat.exists_mul_self` says that $n$ is a perfect square if and only if $\lfloor \sqrt{n} \rfloor^2 = n$, which gives a decision procedure, and `Nat.not_exists_sq` says that a number strictly between $m^2$ and $(m + 1)^2$ is not a square. The other lemmas are bounds: `Nat.sqrt_le_self`, `Nat.sqrt_lt_self` for $n > 1$, `Nat.sqrt_le_sqrt` for monotonicity, and `Nat.sqrt_le_add`, $n \leq s^2 + 2s$ with $s = \lfloor \sqrt{n} \rfloor$.

The module `Mathlib.Data.Nat.NthRoot.Defs` defines `Nat.nthRoot n a`, the floor of $a^{1/n}$. It is computed by Newton's method with integer division, so it is fast for large $a$. The degenerate values are part of the definition: the root of degree $1$ is $a$, and the root of degree $0$ is $1$. The module has only the definition; the lemmas that characterize it are in the files on real powers.

#### Common errors

1. `Nat.digits b n` lists the digits from the least significant one. The usual written form of $n$ is the reverse of the list. The leading digit is the last entry of the list.
2. The lemmas on `Nat.log` need $1 < b$ and often $n \neq 0$, because of the junk values $\lfloor \log_b n \rfloor = 0$ for $b \leq 1$ and for $n = 0$. A simp call that does not close a goal on `Nat.log` usually lacks one of these hypotheses.
3. `Nat.sqrt` and `Nat.log` round down, and `Nat.clog` rounds up. To prove $\lfloor \log_b n \rfloor = k$, prove the two inequalities $b^k \leq n < b^{k + 1}$ and use `Nat.log_eq_of_pow_le_of_lt_pow`; to prove $\lfloor \sqrt{n} \rfloor = m$, use `Nat.le_sqrt` and `Nat.sqrt_lt` in the same way.

### Exercises

1. (A) Compute `Nat.digits 2 13` and `Nat.ofDigits 2 [1, 0, 1, 1]` by hand, and check the second value against the first list.
2. (A) Prove that $n \equiv s_{10}(n) \pmod 3$ with `Nat.modEq_digits_sum`, and deduce `Nat.three_dvd_iff`.
3. (B) Prove that a palindrome with an even number of decimal digits is divisible by $11$. *Hint.* Show that its alternating digit sum is $0$.
4. (B) Prove $\lceil \log_b n \rceil \leq \lfloor \log_b n \rfloor + 1$ for $1 < b$, from the two Galois connections.
5. (B) Prove that $\lfloor \sqrt{n (n + 1)} \rfloor = n$ with `Nat.sqrt_add_eq`.
6. (C) Prove `Nat.sum_sum_digits_eq`: the sum of the digit sums of the numbers $0, \ldots, b^l - 1$ is $l \, b^{l - 1} \binom{b}{2}$. *Hint.* Use the bijection `Nat.bijOn_ofDigits` and count how often each digit appears at each place.

### Reference

<?reference?>
