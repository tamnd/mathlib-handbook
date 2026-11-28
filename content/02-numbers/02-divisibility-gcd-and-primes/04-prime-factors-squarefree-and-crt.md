---
title: Prime factors, squarefree numbers and the Chinese remainder theorem
kind: api
modules:
  - Mathlib.Data.Nat.PrimeFin
  - Mathlib.Data.Nat.Squarefree
  - Mathlib.Data.Nat.ChineseRemainder
  - Mathlib.Data.Nat.MaxPrimeFac
  - Mathlib.Data.Nat.GCD.BigOperators
  - Mathlib.Data.Nat.GCD.Prime
  - Mathlib.Data.Nat.Prime.Factorial
  - Mathlib.Data.Nat.Prime.Int
  - Mathlib.Data.Nat.Prime.Nth
  - Mathlib.Data.Nat.Prime.Pow
explains:
  E2: [Nat.primeFactors_mul, Nat.disjoint_primeFactors, Nat.squarefree_iff_factorization_le_one, Nat.sq_mul_squarefree_of_pos, Nat.Prime.dvd_factorial, Nat.chineseRemainderOfList, Nat.maxPrimeFac_mul, Nat.Coprime.prod_right]
  E1: auto
families: []
requires: [V02.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Prime factors, squarefree numbers and the Chinese remainder theorem

### Overview

The fundamental theorem of arithmetic gives each $n \geq 1$ a list of prime factors with repetitions, and the previous section turns it into the function $p \mapsto v_p(n)$. Many statements need less: only the set of primes that divide $n$. This set is `Nat.primeFactors n`, a `Finset ℕ`. The modules of this section give its API, the squarefree numbers, whose prime factors appear once, the largest prime factor, and the Chinese remainder theorem for a finite family of coprime moduli.

The other modules are small and fill gaps. They give coprimality with products, primes and the lcm, primes and factorials, primes in `ℕ` against primes in `ℤ`, the first values of the enumeration of the primes, and the least prime factor of a power. The section uses the primes and the gcd of this chapter and the congruences of Chapter 3.

### The library around it

#### The finite set of prime factors

The module `Mathlib.Data.Nat.PrimeFin` defines `Nat.primeFactors n` as the finite set of the elements of `n.primeFactorsList`, so `Nat.toFinset_factors` holds by definition. The membership lemma is `Nat.mem_primeFactors`:
$$p \in \mathrm{primeFactors}(n) \iff p \text{ is prime} \wedge p \mid n \wedge n \ne 0.$$
The condition $n \ne 0$ is a junk value: $0$ has no prime factors (`Nat.primeFactors_zero`), although each prime divides $0$. The lemma `Nat.mem_primeFactors_of_ne_zero` drops the condition when $n \ne 0$ is known. The set is empty exactly for $n = 0$ and $n = 1$ (`Nat.primeFactors_eq_empty`), and nonempty exactly for $n > 1$ (`Nat.nonempty_primeFactors`).

The set behaves well under the operations:

| Lean name | Statement |
|---|---|
| `Nat.primeFactors_mul` | $\mathrm{pf}(a b) = \mathrm{pf}(a) \cup \mathrm{pf}(b)$ for $a, b \ne 0$ |
| `Nat.primeFactors_pow` | $\mathrm{pf}(n^k) = \mathrm{pf}(n)$ for $k \ne 0$ |
| `Nat.primeFactors_gcd` | $\mathrm{pf}(\gcd(a, b)) = \mathrm{pf}(a) \cap \mathrm{pf}(b)$ for $a, b \ne 0$ |
| `Nat.Prime.primeFactors` | $\mathrm{pf}(p) = \{p\}$ |
| `Nat.primeFactors_prime_pow` | $\mathrm{pf}(p^k) = \{p\}$ for $k \ne 0$ |
| `Nat.primeFactors_mono` | $m \mid n$ and $n \ne 0$ give $\mathrm{pf}(m) \subseteq \mathrm{pf}(n)$ |
| `Nat.disjoint_primeFactors` | $\mathrm{pf}(a) \cap \mathrm{pf}(b) = \emptyset \iff \gcd(a, b) = 1$ for $a, b \ne 0$ |

**Proof of `Nat.primeFactors_mul`.** For a prime $p$ and $a, b \ne 0$, Euclid's lemma gives $p \mid a b \iff p \mid a \vee p \mid b$, and $a b \ne 0$. So $p$ is in the left side if and only if it is in the right side. $\square$

**Proof sketch of `Nat.disjoint_primeFactors`.** If $\gcd(a, b) > 1$, then it has a prime factor, which divides $a$ and $b$. Conversely, a common prime factor divides the gcd, so the gcd is not $1$. $\square$

The module also restates the infinitude of the primes as `Nat.infinite_setOfPred_prime` and as the instance `Nat.Primes.infinite` on the subtype `Nat.Primes`, with `Nat.Primes.countable`.

#### Squarefree numbers

A number $n$ is squarefree if $d^2 \mid n$ implies that $d$ is a unit, which in `ℕ` means $d = 1$. This is the general predicate `Squarefree` of a monoid. The module `Mathlib.Data.Nat.Squarefree` gives the characterizations in `ℕ`:

| Lean name | Statement |
|---|---|
| `Nat.squarefree_iff_prime_squarefree` | $n$ is squarefree iff $p^2 \nmid n$ for each prime $p$ |
| `Nat.squarefree_iff_factorization_le_one` | for $n \ne 0$: squarefree iff $v_p(n) \leq 1$ for each $p$ |
| `Nat.squarefree_iff_nodup_primeFactorsList` | for $n \ne 0$: squarefree iff the list of prime factors has no repetition |
| `Nat.prod_primeFactors_of_squarefree` | a squarefree $n$ is the product of its prime factors |
| `Nat.squarefree_mul_iff` | $m n$ is squarefree iff $m, n$ are coprime and both are squarefree |
| `Nat.squarefree_pow_iff` | for $n \ne 1$ and $k \ne 0$: $n^k$ is squarefree iff $n$ is and $k = 1$ |
| `Nat.squarefree_and_prime_pow_iff_prime` | a squarefree prime power is a prime |

The proof of the factorization form is short. If $v_p(n) \geq 2$ for some $p$, then $p^2 \mid n$. Conversely, if $d^2 \mid n$ with $d > 1$, then a prime factor $p$ of $d$ gives $p^2 \mid n$, so $v_p(n) \geq 2$.

Each positive number is a square times a squarefree number, by `Nat.sq_mul_squarefree_of_pos`: for $n > 0$ there are $a, b > 0$ with $b^2 a = n$ and $a$ squarefree.

*Proof sketch.* Let $a = \prod_{v_p(n) \text{ odd}} p$ and $b = \prod_p p^{\lfloor v_p(n)/2 \rfloor}$. Then $v_p(b^2 a) = 2 \lfloor v_p(n)/2 \rfloor + (v_p(n) \bmod 2) = v_p(n)$, and $a$ is squarefree because its exponents are at most $1$. $\square$

The predicate is decidable by the instance `Nat.instDecidablePredSquarefree`. The decision procedure uses `Nat.minSqFac`, which returns the least prime $p$ with $p^2 \mid n$ as `Option.some p`, or `Option.none` for a squarefree $n$ (`Nat.squarefree_iff_minSqFac`). The lemma `Nat.sum_divisors_filter_squarefree` rewrites a sum over the squarefree divisors of $n$ as a sum over the subsets of the prime factors, the first step of the theory of the Möbius function.

#### The largest prime factor

The module `Mathlib.Data.Nat.MaxPrimeFac` defines `Nat.maxPrimeFac n`, the largest prime factor of $n$ for $n > 1$. The junk values are `Nat.maxPrimeFac_zero` and `Nat.maxPrimeFac_one`, with the values $0$ and $1$. The lemma `Nat.prime_maxPrimeFac_of_one_lt` says that it is prime for $n > 1$, `Nat.isGreatest_maxPrimeFac` says that it is the greatest element of the set of prime divisors, and `Nat.maxPrimeFac_le_iff` gives its universal property. The lemma `Nat.maxPrimeFac_mul` says $P(m n) = \max(P(m), P(n))$ for $m, n \ne 0$. It follows from `Nat.primeFactors_mul`: the largest element of a union is the larger of the two largest elements.

#### Coprimality with products, the lcm and factorials

The module `Mathlib.Data.Nat.GCD.BigOperators` extends coprimality to products. The lemma `Nat.Coprime.prod_right` says that $x$ is coprime to $\prod_{i \in t} s_i$ if it is coprime to each $s_i$. The proof is an induction on the finite set, with the step $\gcd(x, a) = \gcd(x, b) = 1 \Rightarrow \gcd(x, a b) = 1$. The forms with an equivalence are `Nat.coprime_prod_right_iff` and `Nat.coprime_prod_left_iff`, and the same statements exist for lists, multisets and products over a `Fintype`, as in `Nat.coprime_list_prod_right_iff` and `Nat.coprime_fintype_prod_left_iff`.

The module `Mathlib.Data.Nat.GCD.Prime` says that a prime divides $\mathrm{lcm}(a, b)$ if and only if it divides $a$ or $b$ (`Nat.Prime.dvd_lcm`). The module `Mathlib.Data.Nat.Prime.Factorial` gives `Nat.Prime.dvd_factorial`: $p \mid n! \iff p \leq n$. One direction is `Nat.dvd_factorial`. For the other, if $p \mid n! = 1 \cdot 2 \cdots n$, then Euclid's lemma gives $p \mid m$ for some $1 \leq m \leq n$, so $p \leq m \leq n$. The same module has `Nat.coprime_factorial_iff`: $m \ne 1$ is coprime to $n!$ if and only if $n$ is less than the least prime factor of $m$.

#### Primes in ℤ, powers and the first primes

The module `Mathlib.Data.Nat.Prime.Int` connects the two notions of prime. The predicate `Nat.Prime p` is irreducibility in `ℕ`, and `Prime (p : ℤ)` is the general prime element of a monoid with zero. The lemma `Nat.prime_iff_prime_int` says that they agree. The same module has `Int.prime_two` and `Int.prime_three`, and `Nat.Prime.pow_inj'`, which says that $p^m = q^n$ with primes $p, q$ and $m, n \ne 0$ gives $p = q$ and $m = n$.

The module `Mathlib.Data.Nat.Prime.Pow` has `Nat.pow_minFac`: the least prime factor of $n^k$ is the least prime factor of $n$, for $k \ne 0$. The module `Mathlib.Data.Nat.Prime.Nth` computes the first values of the enumeration `Nat.nth Nat.Prime` of the primes, counted from $0$: `Nat.nth_prime_zero_eq_two` gives $2$, and `Nat.nth_prime_four_eq_eleven` gives $11$.

#### The Chinese remainder theorem for many moduli

Chapter 3 proves the Chinese remainder theorem for two coprime moduli, with `Nat.chineseRemainder`. The module `Mathlib.Data.Nat.ChineseRemainder` extends it to a finite family. Let $s_i$ be pairwise coprime moduli and $a_i$ residues, for $i$ in a list $l$. Then `Nat.chineseRemainderOfList a s l co` is a number $k$ with $k \equiv a_i \pmod{s_i}$ for each $i$, as a subtype. The forms for a multiset and a finite set are `Nat.chineseRemainderOfMultiset` and `Nat.chineseRemainderOfFinset`.

*Proof sketch.* Induction on the list. The empty list gives $k = 0$ (`Nat.chineseRemainderOfList_nil`). For $i :: l$, the modulus $s_i$ is coprime to $\prod_{j \in l} s_j$ by `Nat.Coprime.prod_right`. So the theorem for two moduli combines $a_i \bmod s_i$ with the solution for $l$ modulo the product. $\square$

The solution is unique modulo the product, by `Nat.chineseRemainderOfList_modEq_unique`, and it is less than the product when each $s_i \ne 0$, by `Nat.chineseRemainderOfList_lt_prod`. The uniqueness rests on `Nat.modEq_list_map_prod_iff`: for pairwise coprime moduli, $a \equiv b$ modulo the product if and only if $a \equiv b$ modulo each $s_i$.

#### Common errors

1. The membership $p \in$ `n.primeFactors` contains the condition $n \ne 0$. A proof of $p \mid 0$ does not give $p \in$ `Nat.primeFactors 0`, which is empty.
2. The lemmas `Nat.primeFactors_mul` and `Nat.primeFactors_gcd` need both arguments nonzero. For coprime arguments, `Nat.Coprime.primeFactors_mul` needs no such hypothesis.
3. The enumeration `Nat.nth Nat.Prime` starts at index $0$, so `Nat.nth Nat.Prime 1` is $3$, not $2$.

### Exercises

1. (A) Compute `Nat.primeFactors 360` and `Nat.maxPrimeFac 360`, and justify the results with `Nat.mem_primeFactors` and `Nat.maxPrimeFac_le_iff`.
2. (A) Prove that $\mathrm{pf}(\mathrm{lcm}(a, b)) = \mathrm{pf}(a) \cup \mathrm{pf}(b)$ for $a, b \ne 0$, with `Nat.Prime.dvd_lcm`.
3. (B) Prove that the decomposition $n = b^2 a$ with $a$ squarefree is unique for $n \ne 0$.
4. (B) Find the least $k$ with $k \equiv 2 \pmod 3$, $k \equiv 3 \pmod 5$ and $k \equiv 2 \pmod 7$, and check it against `Nat.chineseRemainderOfList`.
5. (B) Prove that $n!$ and $n! + 1$ are coprime, and deduce with `Nat.Prime.dvd_factorial` that each prime factor of $n! + 1$ is greater than $n$.
6. (C) Prove that a squarefree $n$ has exactly $2^{\omega(n)}$ divisors, where $\omega(n)$ is the number of prime factors, with `Nat.prod_primeFactors_invOn_squarefree`.

### Reference

<?reference?>
