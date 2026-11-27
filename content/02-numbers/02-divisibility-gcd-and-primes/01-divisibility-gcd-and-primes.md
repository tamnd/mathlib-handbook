---
title: Divisibility, gcd and primes
kind: theory
modules:
  - Mathlib.Data.Nat.Prime.Defs
  - Mathlib.Data.Nat.Prime.Basic
  - Mathlib.Data.Nat.Prime.Infinite
  - Mathlib.Data.Int.GCD
explains:
  E3: [Nat.Prime, Nat.exists_infinite_primes]
  E2: [Nat.Prime.two_le, Nat.Prime.dvd_mul, Nat.minFac_prime, Nat.exists_prime_and_dvd, Nat.gcd_eq_gcd_ab]
  E1: auto
families: []
requires: [V02.C01]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V02/C02/Examples.lean
  - MathlibHandbook/V02/C02/Exercises.lean
  - MathlibHandbook/V02/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Divisibility, gcd and primes

### Overview

The relation $a \mid b$ says that $b = a c$ for some $c$. In Lean it is the class `Dvd`, and it has the same definition in each monoid, so the lemmas about divisibility hold for `ℕ`, `ℤ` and the polynomials at the same time. The greatest common divisor `Nat.gcd` is in the core of Lean. Mathlib defines the primes, proves the theorem of Euclid that there are infinitely many, and gives the coefficients of Bézout's identity. This section shows these results and the tactic `norm_num`, which decides if a small number is prime.

### Definitions

**Definition (Divisibility).** For $a, b \in \mathbb{N}$, the relation $a \mid b$ holds if there is $c \in \mathbb{N}$ with $b = a c$. Lean writes it `a ∣ b`, with the symbol `\mid`, not the vertical bar of the keyboard.

**Definition (Prime).** A natural number $p$ is prime if $p \geq 2$ and the only divisors of $p$ are $1$ and $p$. Mathlib defines `Nat.Prime p` as `Irreducible p` in the monoid `ℕ`, and the lemma `Nat.prime_def_lt` gives the usual form.

**Definition (Least factor).** For $n \in \mathbb{N}$, `Nat.minFac n` is the least divisor of $n$ that is at least $2$. Its value at $1$ is the junk value $1$.

**Definition (Bézout coefficients).** For $a, b \in \mathbb{N}$, `Nat.gcdA a b` and `Nat.gcdB a b` are the integers that the extended Euclidean algorithm gives.

### Theorems and proofs

**Theorem (Least factor is prime).** If $n \neq 1$, then the least factor of $n$ is prime.

*Proof.* Let $p$ be the least divisor of $n$ with $p \geq 2$. Such a divisor exists, because $n \geq 2$ divides itself, and each number divides $0$. If $d \mid p$ with $d \geq 2$, then $d \mid n$ and $d \leq p$. So $d = p$ by the choice of $p$, and $p$ is prime. $\square$

**Theorem (Euclid).** For each $n \in \mathbb{N}$, there is a prime $p \geq n$.

*Proof.* Let $m = n! + 1$, and let $p$ be the least factor of $m$. Then $p$ is prime, since $m \neq 1$. If $p < n$, then $p \mid n!$, so $p \mid 1$, which is false. So $p \geq n$. $\square$

**Theorem (Euclid's lemma).** If $p$ is prime and $p \mid a b$, then $p \mid a$ or $p \mid b$.

*Proof.* Suppose that $p \nmid a$. Then $\gcd(p, a) = 1$, because the only divisors of $p$ are $1$ and $p$. Bézout's identity gives integers $x$ and $y$ with $p x + a y = 1$. So $b = p b x + a b y$, and $p$ divides both terms. Thus $p \mid b$. $\square$

### Mathlib boxes

::: mathlib
`Nat.Prime` · `Mathlib.Data.Nat.Prime.Defs`

The definition is `Irreducible p`, so the general lemmas about irreducible elements apply. The instance `Nat.decidablePrime` makes `decide` work on small numbers, but `norm_num` is faster.

<?decl Nat.Prime?>
:::

::: mathlib
`Nat.exists_infinite_primes` · `Mathlib.Data.Nat.Prime.Infinite`

The statement is `∀ n, ∃ p, n ≤ p ∧ p.Prime`. The proof is the proof of Euclid with `Nat.minFac` and the factorial.

<?decl Nat.exists_infinite_primes?>
:::

::: mathlib
`Nat.gcd_eq_gcd_ab` · `Mathlib.Data.Int.GCD`

The identity is in `ℤ`, because one of the coefficients is negative in most cases. The lemma `Int.gcd_eq_gcd_ab` is the form for two integers.

<?decl Nat.gcd_eq_gcd_ab?>
:::

### Examples

**Example (Small primes).** The tactic `norm_num` proves that $37$ is prime and that $91 = 7 \cdot 13$ is not.

<?lean MathlibHandbook/V02/C02/Examples.lean#prime_norm_num?>

**Example (A prime is at least 2).**

<?lean MathlibHandbook/V02/C02/Examples.lean#two_le?>

**Example (Euclid's lemma).** The lemma `Nat.Prime.dvd_mul` is an equivalence, so the proof takes its direction `mp`.

<?lean MathlibHandbook/V02/C02/Examples.lean#dvd_mul?>

**Example (Infinitely many primes).**

<?lean MathlibHandbook/V02/C02/Examples.lean#infinite?>

**Example (The least factor).**

<?lean MathlibHandbook/V02/C02/Examples.lean#minFac?>

**Example (Bézout's identity).**

<?lean MathlibHandbook/V02/C02/Examples.lean#bezout?>

### The library around it

The basic facts about primes are in `Mathlib.Data.Nat.Prime.Defs` and `Mathlib.Data.Nat.Prime.Basic`: for example `Nat.prime_two`, `Nat.minFac_dvd`, `Nat.minFac_le`, `Nat.Prime.coprime_iff_not_dvd` and `Nat.coprime_primes`. The type `Nat.Primes` is the subtype of the primes. The list of the prime factors of $n$ is `Nat.primeFactorsList n`, and `Nat.prod_primeFactorsList` says that their product is $n$. The finite set of the prime factors is `Nat.primeFactors n`, and the multiplicity of each prime is `Nat.factorization n`, which is a finitely supported function. Coprimality is `Nat.Coprime`, from the core of Lean. For divisibility in a general ring, and for the unique factorization of a ring, see the volumes on algebra and on number theory.

### Exercises

1. (A) Give the value of `Nat.minFac 1` and of `Nat.minFac 0` in Mathlib.
2. (A) Explain why `Nat.gcd_eq_gcd_ab` is a statement in `ℤ` and not in `ℕ`.
3. (B) Show that if $p$ is prime and $p \mid a^n$, then $p \mid a$, with induction on $n$.
4. (B) Show that there are infinitely many primes of the form $4k + 3$.
5. (L) Prove that a prime that divides $n^2$ divides $n$. The solution is `prime_dvd_of_dvd_sq`.
6. (L) Prove that for each $n$ there is a prime $p > n$. The solution is `exists_prime_gt`.
7. (L) Prove that $221$ is not prime. The solution is `not_prime_221`.
8. (L) Prove that each $n \neq 1$ has a prime divisor. The solution is `exists_prime_dvd`.

### Notes and history

The proof that there are infinitely many primes is Proposition 20 of Book IX of Euclid's Elements. Bézout stated his identity for polynomials in 1779, and Bachet de Méziriac gave the form for integers in 1624. The definition of a prime as an irreducible element lets Mathlib use one theory of factorization for `ℕ`, `ℤ` and the rings of polynomials.

### Reference

<?reference?>
