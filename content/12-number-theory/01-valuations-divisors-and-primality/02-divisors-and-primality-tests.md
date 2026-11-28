---
title: Divisors and primality tests
kind: theory
modules:
  - Mathlib.NumberTheory.Divisors
  - Mathlib.NumberTheory.Fermat
  - Mathlib.NumberTheory.FermatPsp
  - Mathlib.NumberTheory.CarmichaelNumber
  - Mathlib.NumberTheory.LucasPrimality
  - Mathlib.NumberTheory.LucasLehmer
  - Mathlib.NumberTheory.Basic
  - Mathlib.NumberTheory.Wilson
  - Mathlib.NumberTheory.PowModTotient
  - Mathlib.NumberTheory.TsumDivisorsAntidiagonal
explains:
  E3: [Nat.divisors, Nat.Perfect, Nat.fermatNumber, Nat.FermatPsp, Nat.IsCarmichael, lucas_primality, lucas_lehmer_sufficiency]
  E2: [Nat.properDivisors, Nat.mem_divisors, Nat.perfect_iff_sum_divisors_eq_two_mul, Nat.sum_divisors_prime_pow, Nat.prod_fermatNumber, Nat.coprime_fermatNumber_fermatNumber, Nat.pepin_primality, Nat.ProbablePrime, Nat.exists_infinite_pseudoprimes, Nat.isCarmichael_iff_korselt, Nat.isCarmichael_561, Nat.prime_of_pow_sub_one_prime, LucasLehmer.LucasLehmerTest, lucas_lehmer_necessity]
  E1: auto
families: []
requires: [V02.C02, V02.C03, V02.C06, V05.C04, V06.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Divisors and primality tests

### Overview

This section studies two old questions. The first is about perfect numbers: the Euclid-Euler theorem finds the even ones, and it leads to the Mersenne numbers $2^p - 1$. The second is how to prove that a large number is prime. Fermat's little theorem (Volume 2, Chapter 3) gives a necessary condition, $a^{n-1} \equiv 1 \pmod n$, but pseudoprimes and Carmichael numbers show that it is not sufficient. Lucas's test adds one condition and gives a proof. Pepin's test and the Lucas-Lehmer test apply this idea to the Fermat and the Mersenne numbers.

### Definitions

**Definition (Divisors).** For $n \geq 1$, the divisors of $n$ are the $d \geq 1$ with $d \mid n$. The proper divisors are the divisors $d < n$. The number $n$ is perfect if the sum of its proper divisors is $n$, that is, if $\sigma(n) = 2n$, where $\sigma(n)$ is the sum of all divisors.

::: mathlib
`Nat.divisors` · `Mathlib.NumberTheory.Divisors`

The divisors as a `Finset ℕ`. Membership is `Nat.mem_divisors`: `d ∈ n.divisors ↔ d ∣ n ∧ n ≠ 0`. The junk value is `Nat.divisors 0 = ∅`. The proper divisors are `Nat.properDivisors`.

<?decl Nat.divisors?>
:::

::: mathlib
`Nat.Perfect` · `Mathlib.NumberTheory.Divisors`

The predicate `∑ i ∈ n.properDivisors, i = n ∧ 0 < n`. The form with all divisors is `Nat.perfect_iff_sum_divisors_eq_two_mul`. The index of this edition has no declaration for the Euclid-Euler theorem.

<?decl Nat.Perfect?>
:::

**Definition (Fermat and Mersenne numbers).** The Fermat numbers are $F_n = 2^{2^n} + 1$, and the Mersenne numbers are $M_p = 2^p - 1$.

**Definition (Probable primes, pseudoprimes, Carmichael numbers).** A number $n$ is a probable prime to the base $b$ if $n \mid b^{n-1} - 1$. A Fermat pseudoprime to the base $b$ is a composite $n > 1$ that is a probable prime to the base $b$. A Carmichael number is a composite $n > 2$ that is a probable prime to every base $b$ prime to $n$.

::: mathlib
`Nat.FermatPsp` · `Mathlib.NumberTheory.FermatPsp`

The predicate `ProbablePrime n b ∧ ¬n.Prime ∧ 1 < n`, where `Nat.ProbablePrime n b` is `n ∣ b ^ (n - 1) - 1`. Most theorems ask `1 ≤ b`. The predicate `Nat.IsCarmichael n` is `2 < n ∧ ¬n.Prime ∧ ∀ b, b.Coprime n → ProbablePrime n b`.

<?decl Nat.FermatPsp?>
:::

### Theorems and proofs

**Theorem (The divisors of a prime power).** For a prime $p$, the divisors of $p^k$ are $1, p, \dots, p^k$, and $\sigma(p^k) = (p^{k+1} - 1)/(p - 1)$.

*Proof.* By the uniqueness of the factorization, a divisor of $p^k$ has no prime factor other than $p$, so it is $p^i$ with $i \leq k$. The sum is a geometric sum. $\square$

In Mathlib, `Nat.sum_divisors_prime_pow` gives `∑ x ∈ (p ^ k).divisors, f x = ∑ x ∈ Finset.range (k + 1), f (p ^ x)` for any `f`.

**Theorem (Euclid-Euler).** An even number $n$ is perfect if and only if $n = 2^{k-1}(2^k - 1)$ with $2^k - 1$ prime.

*Proof.* First, for $a \geq 0$ and odd $m$, $\sigma(2^a m) = (2^{a+1} - 1)\sigma(m)$. Each divisor $d$ of $2^a m$ is $2^i e$ with $i = v_2(d) \leq a$ and $e$ odd, so $e \mid m$, and $(i, e)$ is unique. So $\sigma(2^a m) = \sum_{i \leq a} 2^i \sum_{e \mid m} e$.

If $q = 2^k - 1$ is prime, then $k \geq 2$, and $\sigma(2^{k-1} q) = (2^k - 1)(q + 1) = 2^k q$, so $n$ is perfect.

Conversely, let $n = 2^{k-1} m$ with $k \geq 2$ and $m$ odd be perfect. Then $(2^k - 1)\sigma(m) = 2^k m$. Since $2^k - 1$ is odd, it is prime to $2^k$, so $m = (2^k - 1)c$ and $\sigma(m) = 2^k c$. If $c > 1$, then $1$, $c$ and $m$ are three distinct divisors of $m$, so $\sigma(m) \geq 1 + c + m = 1 + 2^k c$, which is false. So $c = 1$ and $\sigma(m) = m + 1$. Then $1$ and $m$ are the only divisors of $m$, and $m = 2^k - 1$ is prime. $\square$

If $2^k - 1$ is prime, then $k$ is prime: for $k = ab$ with $1 < a < k$, $2^a - 1$ divides $2^k - 1$. In the same way, if $2^k + 1$ is prime, then $k$ is a power of $2$: an odd factor $a > 1$ of $k = ab$ gives the factor $2^b + 1$ of $2^k + 1$. In Mathlib these are `Nat.prime_of_pow_sub_one_prime` and `Nat.pow_of_pow_add_prime` in `Mathlib.NumberTheory.Fermat`.

**Theorem (Products of Fermat numbers).** $F_0 F_1 \cdots F_{n-1} = F_n - 2$, and distinct Fermat numbers are coprime.

*Proof.* By induction on $n$. For $n = 0$ the empty product is $1 = 3 - 2$. If the formula holds for $n$, then
$$F_0 \cdots F_n = (F_n - 2) F_n = (2^{2^n} - 1)(2^{2^n} + 1) = 2^{2^{n+1}} - 1 = F_{n+1} - 2.$$
For $m < n$, a common divisor $d$ of $F_m$ and $F_n$ divides the product and $F_n$, so $d \mid 2$. Since $F_n$ is odd, $d = 1$. $\square$

So the prime factors of the $F_n$ are distinct, and there are infinitely many primes.

::: mathlib
`Nat.fermatNumber` · `Mathlib.NumberTheory.Fermat`

The function `n ↦ 2 ^ 2 ^ n + 1`. The product formula is `Nat.prod_fermatNumber`, with the subtraction in `ℕ`, and coprimality is `Nat.coprime_fermatNumber_fermatNumber`.

<?decl Nat.fermatNumber?>
:::

**Theorem (Lucas's test).** Let $p \geq 2$ and $a \in \mathbb{Z}/p$. If $a^{p-1} = 1$ and $a^{(p-1)/q} \neq 1$ for each prime $q \mid p - 1$, then $p$ is prime.

*Proof.* Since $a^{p-1} = 1$, $a$ is a unit. Let $d$ be its order in $(\mathbb{Z}/p)^\times$ (Volume 5, Chapter 4). Then $d \mid p - 1$. If $d < p - 1$, a prime $q$ divides $(p - 1)/d$, so $d \mid (p-1)/q$ and $a^{(p-1)/q} = 1$, which is false. So $d = p - 1$, and the group $(\mathbb{Z}/p)^\times$ has at least $p - 1$ elements. Its order is $\varphi(p)$ (Volume 2, Chapter 6), so $\varphi(p) = p - 1$. Then each of $1, \dots, p - 1$ is prime to $p$, and $p$ is prime. $\square$

The converse holds too: for a prime $p$, a primitive root $a$ (Volume 6, Chapter 5) satisfies the conditions.

::: mathlib
`lucas_primality` · `Mathlib.NumberTheory.LucasPrimality`

The test, for `p : ℕ` and `a : ZMod p`. The converse is `reverse_lucas_primality` and the equivalence is `lucas_primality_iff`.

<?decl lucas_primality?>
:::

**Theorem (Pepin's test, one direction).** If $3^{(F_n - 1)/2} \equiv -1 \pmod{F_n}$, then $F_n$ is prime.

*Proof.* Apply Lucas's test with $a = 3$. Then $a^{F_n - 1} = (-1)^2 = 1$. The only prime factor of $F_n - 1 = 2^{2^n}$ is $2$, and $a^{(F_n - 1)/2} = -1 \neq 1$ because $F_n > 2$. $\square$

The converse (for $n \geq 1$) follows from quadratic reciprocity and Euler's criterion in Chapter 3, since $F_n \equiv 2 \pmod 3$.

In Mathlib this direction is `Nat.pepin_primality`, with `3 ^ 2 ^ (2 ^ n - 1) = -1` in `ZMod (fermatNumber n)`, and `Nat.fermat_primeFactors_one_lt` says that each prime factor of $F_n$ for $n > 1$ is $k \cdot 2^{n+2} + 1$.

**Theorem (Korselt's criterion).** A composite $n > 2$ is a Carmichael number if and only if $n$ is squarefree and $p - 1 \mid n - 1$ for each prime $p \mid n$.

*Proof.* Assume the condition and let $b$ be prime to $n$. For $p \mid n$, Fermat gives $b^{p-1} \equiv 1 \pmod p$, so $b^{n-1} \equiv 1 \pmod p$. Since $n$ is the product of its distinct primes, the Chinese remainder theorem gives $b^{n-1} \equiv 1 \pmod n$.

Conversely, let $n$ be a Carmichael number and $p^e \parallel n$. Let $g$ be a primitive root modulo $p$. By the Chinese remainder theorem there is $b$ with $b \equiv g \pmod {p^e}$ and $b \equiv 1 \pmod{n/p^e}$; it is prime to $n$. Then $g^{n-1} \equiv 1 \pmod p$, so $p - 1 \mid n - 1$. If $e \geq 2$, take instead $b \equiv 1 + p \pmod{p^e}$ and $b \equiv 1 \pmod{n/p^e}$. By the binomial theorem, $(1+p)^{n-1} \equiv 1 + (n-1)p \equiv 1 - p \pmod{p^2}$, since $p \mid n$. This is not $1$ modulo $p^2$, a contradiction. So $n$ is squarefree. $\square$

::: mathlib
`Nat.isCarmichael_iff_korselt` · `Mathlib.NumberTheory.CarmichaelNumber`

The criterion, with `2 < n ∧ ¬n.Prime ∧ Squarefree n ∧ ∀ p, p.Prime → p ∣ n → p - 1 ∣ n - 1` on the right.

<?decl Nat.isCarmichael_iff_korselt?>
:::

**Theorem (Lucas-Lehmer).** Let $p > 1$, put $s_0 = 4$ and $s_{i+1} = s_i^2 - 2$. If $M_p \mid s_{p-2}$, then $M_p$ is prime. For an odd prime $p$, the converse holds.

*Proof of sufficiency.* Put $\omega = 2 + \sqrt 3$ and $\bar\omega = 2 - \sqrt 3$, so $\omega\bar\omega = 1$. By induction, $s_i = \omega^{2^i} + \bar\omega^{2^i}$: indeed $s_i^2 - 2 = \omega^{2^{i+1}} + 2(\omega\bar\omega)^{2^i} + \bar\omega^{2^{i+1}} - 2$. Assume $M_p$ is composite and let $q$ be its smallest prime factor, so $q^2 \leq M_p$, and $q$ is odd. Work in the ring $X = \{a + b\alpha : a, b \in \mathbb{Z}/q\}$ with $\alpha^2 = 3$. From $q \mid s_{p-2}$, $\omega^{2^{p-2}} = -\bar\omega^{2^{p-2}}$ in $X$. Multiply by $\omega^{2^{p-2}}$: $\omega^{2^{p-1}} = -1$. Since $-1 \neq 1$ in $X$, the order of the unit $\omega$ is $2^p$. The ring $X$ has $q^2$ elements, and $0$ is not a unit, so $2^p \leq q^2 - 1 \leq M_p - 1 = 2^p - 2$. This is false. $\square$

The proof of necessity uses Chapter 3 and is not given here.

::: mathlib
`lucas_lehmer_sufficiency` · `Mathlib.NumberTheory.LucasLehmer`

`1 < p → LucasLehmerTest p → (mersenne p).Prime`. Here `LucasLehmer.s` is the sequence in `ℤ`, and `LucasLehmerTest p` says that `sZMod p (p - 2) = 0` in `ZMod (2 ^ p - 1)`. The proof uses the ring `LucasLehmer.X q`. The converse is `lucas_lehmer_necessity`, with `3 ≤ p`.

<?decl lucas_lehmer_sufficiency?>
:::

### Examples

**Example (A perfect number).** For $k = 3$, $n = 4 \cdot 7 = 28$, and $1 + 2 + 4 + 7 + 14 = 28$.

**Example (The fifth Fermat number).** Fermat's numbers $F_0, \dots, F_4 = 3, 5, 17, 257, 65537$ are prime. For $F_5$, a prime factor has the form $k \cdot 128 + 1$. The first primes of this form are $257 = F_3$, which is prime to $F_5$, and $641 = 5 \cdot 128 + 1$. Indeed $641 \mid F_5$: from $641 = 5 \cdot 2^7 + 1 = 5^4 + 2^4$, $5 \cdot 2^7 \equiv -1$, so $5^4 2^{28} \equiv 1$, and $5^4 \equiv -2^4$ gives $-2^{32} \equiv 1 \pmod{641}$.

**Example (Lucas-Lehmer for $p = 7$).** Modulo $M_7 = 127$: $s_0 = 4$, $s_1 = 14$, $s_2 = 194 \equiv 67$, $s_3 \equiv 67^2 - 2 = 4487 \equiv 42$, $s_4 \equiv 42^2 - 2 = 1762 \equiv 111$, $s_5 \equiv 111^2 - 2 = 12319 = 97 \cdot 127 \equiv 0$. So $127$ is prime.

**Counterexample (Fermat's test is not a proof).** $341 = 11 \cdot 31$ is composite, but $2^{10} = 1024 = 3 \cdot 341 + 1$, so $2^{340} = (2^{10})^{34} \equiv 1 \pmod{341}$. So $341$ is a pseudoprime to the base $2$. The base $3$ detects it: $3^{15} \equiv -1 \pmod{31}$, so $3$ has order $30$ modulo $31$ and $3^{340} \equiv 3^{10} \equiv 25 \pmod{31}$. No base detects $561 = 3 \cdot 11 \cdot 17$: it is squarefree, and $2$, $10$ and $16$ divide $560$, so it is a Carmichael number by Korselt.

### The library around it

`Mathlib.NumberTheory.Divisors` also has `Nat.divisorsAntidiagonal`, the pairs $(a, b)$ with $ab = n$, for Chapter 2. `Nat.exists_infinite_pseudoprimes` gives arbitrarily large pseudoprimes to each base $b \geq 1$.

The small module `Mathlib.NumberTheory.Basic` has one lemma, `dvd_sub_pow_of_dvd_sub`: in a commutative ring, if $p \mid a - b$ then $p^{k+1} \mid a^{p^k} - b^{p^k}$ for each $k$.

`Mathlib.NumberTheory.Wilson` gives Wilson's theorem and its converse. `ZMod.wilsons_lemma` says that $(p-1)! = -1$ in `ZMod p` for a prime $p$, and `ZMod.prod_Ico_one_prime` says the same with the product $\prod_{1 \leq x < p} x$. The converse `Nat.prime_of_fac_equiv_neg_one` gives a primality test, and `Nat.prime_iff_fac_equiv_neg_one` combines the two directions for $n \neq 1$. The test is exact but slow, because $(n-1)!$ has about $n \log n$ digits. For odd $p$, `ZMod.factorial_eq_neg_one_pow_mul_half_factorial_sq` writes $(p-1)!$ as $(-1)^{(p-1)/2}$ times the square of $((p-1)/2)!$, and `ZMod.half_factorial_sq_eq_neg_one` concludes that $((p-1)/2)!^2 = -1$ when $p \bmod 4 \neq 3$. This gives an explicit square root of $-1$ modulo such a prime, which is the first step of the two squares theorem of Section 4.2.

`Mathlib.NumberTheory.PowModTotient` states Euler's theorem in the form that a computation needs, with `%` on natural numbers. `Nat.pow_totient_mod_eq_one` says that $x^{\varphi(n)} \bmod n = 1$ when $1 < n$ and $x$ is coprime to $n$. `Nat.pow_totient_mod` reduces the exponent: $x^k \bmod n = x^{k \bmod \varphi(n)} \bmod n$. `Nat.pow_add_totient_mod_eq` and `Nat.pow_add_mul_totient_mod_eq` add $\varphi(n)$ or a multiple of it to the exponent. All four lemmas need the coprimality hypothesis: for $x = 2$ and $n = 4$ the power $2^{\varphi(4)} = 4$ is $0$ modulo $4$.

`Mathlib.NumberTheory.TsumDivisorsAntidiagonal` connects divisor sums with power series, in the form that the $q$-expansions of Eisenstein series use. The equivalence `sigmaAntidiagonalEquivProd` identifies the pairs $(n, (a, b))$ with $ab = n$ with the pairs $(a, b)$ of positive integers, and `divisorsAntidiagonalFactors` turns a divisor pair of $n$ into a pair in `ℕ+ × ℕ+`. For $\|r\| < 1$ in a complete normed field, `tsum_prod_pow_eq_tsum_sigma` says that $\sum_{d \geq 1} \sum_{c \geq 1} c^k r^{dc} = \sum_{e \geq 1} \sigma_k(e) r^e$, and `tsum_pow_div_one_sub_eq_tsum_sigma` gives the Lambert series form $\sum_{n \geq 1} n^k r^n / (1 - r^n) = \sum_{e \geq 1} \sigma_k(e) r^e$. The summability lemmas `summable_prod_mul_pow` and `summable_norm_pow_mul_geometric_div_one_sub` justify the rearrangements, and `tendsto_zero_geometric_tsum_pnat` says that $\sum_{n \geq 1} r^{nm}$ tends to $0$ as $m \to \infty$.

Common errors of a learner:

- `Nat.divisors 0 = ∅`, so `Nat.mem_divisors` has the condition `n ≠ 0`.
- `ProbablePrime n b` with `b = 0` or `b = 1` is true for trivial reasons; `Nat.fermatPsp_base_one` says that every composite `n > 1` is a pseudoprime to the base `1`.
- Lucas's test needs every prime factor of $p - 1$.

### Exercises

1. (A) Find the divisors of $496$ and show that $496$ is perfect.
2. (A) Show that $2^a - 1 \mid 2^{ab} - 1$ and that $2^b + 1 \mid 2^{ab} + 1$ for odd $a$.
3. (A) Show that $1105 = 5 \cdot 13 \cdot 17$ is a Carmichael number.
4. (B) Run the Lucas-Lehmer test for $p = 5$ and $p = 11$. Hint: $M_{11} = 2047 = 23 \cdot 89$, so the second test fails although $11$ is prime.
5. (B) Prove $3^8 \equiv -1 \pmod{17}$ and conclude with Pepin's test that $F_2$ is prime.
6. (B) Prove with Lucas's test and $a = 2$ that $211$ is prime. Hint: $210 = 2 \cdot 3 \cdot 5 \cdot 7$; check that $2^{105}, 2^{70}, 2^{42}, 2^{30} \not\equiv 1 \pmod{211}$.
7. (B) Show that a prime factor $q$ of $F_n$ satisfies $q \equiv 1 \pmod{2^{n+1}}$. Hint: the order of $2$ modulo $q$ is $2^{n+1}$.
8. (C) Show that a Carmichael number has at least three prime factors. Hint: for $n = pq$ with $p < q$, $q - 1 \mid n - 1$ gives $q - 1 \mid p - 1$.

### Notes and history

Euclid proved the sufficient direction of the Euclid-Euler theorem in the *Elements*, Book IX; Euler proved the converse. Fermat claimed that all $F_n$ are prime, and Euler found the factor $641$ of $F_5$ in 1732. Pepin published his test in 1877. Lehmer gave the final form of the Mersenne test of Lucas in 1930. Korselt gave his criterion in 1899, and Carmichael found $561$ in 1910.

### Reference

<?reference?>
