---
title: Primes and unique factorization
kind: theory
modules:
  - Mathlib.Data.Nat.Prime.Defs
  - Mathlib.Data.Nat.Prime.Basic
  - Mathlib.Data.Nat.Prime.Infinite
  - Mathlib.Data.Nat.Factors
  - Mathlib.Data.Int.Associated
  - Mathlib.Data.Int.NatPrime
explains:
  E3: [Nat.Prime, Nat.exists_infinite_primes, Nat.primeFactorsList]
  E2: [Nat.Prime.two_le, Nat.Prime.dvd_mul, Nat.minFac, Nat.minFac_prime, Nat.exists_prime_and_dvd, Nat.prime_def_lt, Nat.minFac_sq_le_self, Nat.Prime.coprime_iff_not_dvd, Nat.Prime.dvd_of_dvd_pow, Nat.not_bddAbove_setOfPred_prime, Nat.prod_primeFactorsList, Nat.primeFactorsList_unique]
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

## Primes and unique factorization

### Overview

A prime is a number $p \geq 2$ with no divisors other than $1$ and $p$. Each number $n \geq 2$ has a prime divisor, and the least divisor $\geq 2$ is one. A prime that divides a product divides one of the factors (Euclid's lemma). There are infinitely many primes. From these facts it proves the fundamental theorem of arithmetic: each $n \geq 1$ is a product of primes, and the primes are unique up to their order. Mathlib computes with `Nat.minFac` and `Nat.primeFactorsList`.

### Definitions

**Definition (Prime).** A number $p \in \mathbb{N}$ is prime if $p \geq 2$ and the only divisors of $p$ in $\mathbb{N}$ are $1$ and $p$. A number $n \geq 2$ that is not prime is composite.

The numbers $0$ and $1$ are neither prime nor composite. With $1$ prime, $6 = 2 \cdot 3 = 1 \cdot 2 \cdot 3$ would be two factorizations.

::: mathlib
`Nat.Prime` · `Mathlib.Data.Nat.Prime.Defs`

The definition is `Irreducible p` in the monoid `ℕ`. The lemma `Nat.prime_def_lt` gives the school form `2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1`, and `Nat.Prime.two_le` gives the bound. The extension of `norm_num` tests small numbers.

<?decl Nat.Prime?>
:::

**Definition (Least factor).** For $n \in \mathbb{N}$ with $n \neq 1$, the least factor of $n$ is the least $m \geq 2$ with $m \mid n$.

The definition makes sense because $n$ itself is such a divisor for $n \geq 2$, and each number divides $0$, so the least factor of $0$ is $2$.

::: mathlib
`Nat.minFac` · `Mathlib.Data.Nat.Prime.Defs`

Its value at $1$ is the junk value $1$, and its value at $0$ is $2$. The definition tests $2$ and then the odd numbers up to $\sqrt{n}$, so it computes. The lemmas `Nat.minFac_dvd` and `Nat.minFac_le_of_dvd` say that it is a divisor and that it is the least one.

<?decl Nat.minFac?>
:::

**Definition (Prime factorization).** A prime factorization of $n \geq 1$ is a finite list $(p_1, \dots, p_r)$ of primes with $p_1 p_2 \cdots p_r = n$. The empty list, with the empty product $1$, is the factorization of $1$.

::: mathlib
`Nat.primeFactorsList` · `Mathlib.Data.Nat.Factors`

The function gives the prime factors of `n` in increasing order, with repetitions: `Nat.primeFactorsList 12 = [2, 2, 3]`. It is defined by recursion with `Nat.minFac`, and its value at $0$ and at $1$ is the empty list. The exponents are `Nat.factorization`.

<?decl Nat.primeFactorsList?>
:::

### Theorems and proofs

**Theorem (The least factor is prime).** If $n \neq 1$, then the least factor $p$ of $n$ is prime. So each $n \neq 1$ has a prime divisor.

*Proof.* The number $p$ satisfies $p \geq 2$. Let $d \mid p$ with $d \neq 1$. Then $d \neq 0$, since $p \neq 0$, so $d \geq 2$. Also $d \mid n$, by transitivity. By the choice of $p$, $p \leq d$, and $d \leq p$ because $d \mid p$. So $d = p$, and $p$ is prime. $\square$

::: mathlib
`Nat.minFac_prime` · `Mathlib.Data.Nat.Prime.Defs`

The hypothesis is `n ≠ 1`, and it is necessary, since `Nat.minFac 1 = 1` is not prime. The existence form is `Nat.exists_prime_and_dvd`, with the same hypothesis.

<?decl Nat.minFac_prime?>
:::

**Theorem (The trial bound).** If $n \geq 2$ is composite, then its least factor $p$ satisfies $p^2 \leq n$. So $n \geq 2$ is prime if no $m$ with $2 \leq m$ and $m^2 \leq n$ divides $n$.

*Proof.* Write $n = pm$. Since $n$ is not prime, $p \neq n$, so $m \neq 1$. Also $m \neq 0$. So $m \geq 2$, and $m \mid n$, so $p \leq m$ by the choice of $p$. Then $p^2 \leq pm = n$. For the second claim, if $n$ is composite, then its least factor is a divisor $m$ with $2 \leq m$ and $m^2 \leq n$. $\square$

::: mathlib
`Nat.minFac_sq_le_self` · `Mathlib.Data.Nat.Prime.Defs`

The hypotheses are `0 < n` and `¬ n.Prime`. The test form is `Nat.prime_def_le_sqrt`, with the integer square root `Nat.sqrt`.

<?decl Nat.minFac_sq_le_self?>
:::

**Theorem (Euclid's lemma).** Let $p$ be prime and $a, b \in \mathbb{N}$. If $p \mid ab$, then $p \mid a$ or $p \mid b$. More generally, if $p$ divides a product $a_1 \cdots a_k$, then $p$ divides some $a_i$.

*Proof.* The number $\gcd(p, a)$ divides $p$, so it is $1$ or $p$. If it is $p$, then $p \mid a$. If it is $1$, then $p$ and $a$ are coprime, and Gauss's lemma of the previous section, applied to $p \mid ba$, gives $p \mid b$. The general form follows by induction on $k$. For $k = 0$ the product is $1$, and $p \nmid 1$ since $p \geq 2$, so there is nothing to prove. For $k + 1$, apply the first form to $(a_1 \cdots a_k) \cdot a_{k+1}$. $\square$

::: mathlib
`Nat.Prime.dvd_mul` · `Mathlib.Data.Nat.Prime.Defs`

The statement is an equivalence, `p ∣ m * n ↔ p ∣ m ∨ p ∣ n`. The step in the proof is `Nat.Prime.coprime_iff_not_dvd`. The lemma `Nat.Prime.prime` gives the general `Prime p` of a monoid, with its lemmas for products of lists. The form for powers is `Nat.Prime.dvd_of_dvd_pow`.

<?decl Nat.Prime.dvd_mul?>
:::

**Theorem (Euclid: infinitely many primes).** For each $n \in \mathbb{N}$ there is a prime $p > n$.

*Proof.* Let $m = n! + 1$. Then $m \geq 2$, so $m$ has a prime divisor $p$ by the first theorem. Suppose $p \leq n$. Since $1 \leq p \leq n$, $p \mid n!$ by the theorem on factorials of Chapter 1. Then $p$ divides $m - n! = 1$, which is false, because $p \geq 2$. So $p > n$. $\square$

::: mathlib
`Nat.exists_infinite_primes` · `Mathlib.Data.Nat.Prime.Infinite`

The statement is `∀ n, ∃ p, n ≤ p ∧ p.Prime`, with `≤` in place of `<`; apply it to `n + 1` to get a prime above `n`. Mathlib uses the proof above. The form `Nat.not_bddAbove_setOfPred_prime` says that the set of primes has no upper bound.

<?decl Nat.exists_infinite_primes?>
:::

**Theorem (Fundamental theorem of arithmetic).** Each $n \geq 1$ has a prime factorization. Two prime factorizations of $n$ contain the same primes with the same multiplicities, so they differ only in the order of the factors.

*Proof.* Existence, by strong induction on $n$. For $n = 1$, take the empty list. For $n \geq 2$, let $p$ be the least factor of $n$. It is prime, and $n = pm$ with $1 \leq m < n$, since $p \geq 2$. By the hypothesis, $m$ has a factorization $(p_1, \dots, p_r)$. Then $(p, p_1, \dots, p_r)$ is a factorization of $n$.

Uniqueness, by induction on the length $r$ of the first list. Suppose $p_1 \cdots p_r = q_1 \cdots q_s$, with all $p_i$ and $q_j$ prime. If $r = 0$, the product is $1$. A nonempty product of primes is at least $2$, so $s = 0$ and the lists are equal. If $r \geq 1$, then $p_1$ divides $q_1 \cdots q_s$, so $s \geq 1$, and the general form of Euclid's lemma gives $p_1 \mid q_j$ for some $j$. The only divisors of $q_j$ are $1$ and $q_j$, and $p_1 \neq 1$, so $p_1 = q_j$. Cancel this factor on both sides, which is possible because $p_1 \neq 0$. The result is an equality of a product of $r - 1$ primes with the product of the $q_i$ with $i \neq j$. By the hypothesis, these two lists are the same up to order. Add back $p_1 = q_j$. $\square$

::: mathlib
`Nat.primeFactorsList_unique` · `Mathlib.Data.Nat.Factors`

The statement: if the product of the list `l` is `n` and each member of `l` is prime, then `l` is a permutation of `Nat.primeFactorsList n`, written `l.Perm n.primeFactorsList`. This is the uniqueness part. The existence part is `Nat.prod_primeFactorsList : n ≠ 0 → n.primeFactorsList.prod = n`, together with `Nat.prime_of_mem_primeFactorsList`.

<?decl Nat.primeFactorsList_unique?>
:::

### Examples

**Example (Testing primes).** The number $37$ is prime: $37 < 7^2$, so by the trial bound it suffices to test $2, 3, 5$. The number $91$ is $7 \cdot 13$. For $221 < 15^2$, test the primes up to $13$: $221 = 13 \cdot 17$. In Lean, `norm_num` decides the first two facts.

<?lean MathlibHandbook/V02/C02/Examples.lean#prime_norm_num?>

The least factor of $91$ is $7$, and it is prime. The second part uses `Nat.minFac_prime`, with the hypothesis $91 \neq 1$ proved by `norm_num`.

<?lean MathlibHandbook/V02/C02/Examples.lean#minFac?>

**Example (The bound and Euclid's lemma).** For a prime `p`, the bound `2 ≤ p` is one projection, and Euclid's lemma is one direction of an equivalence.

<?lean MathlibHandbook/V02/C02/Examples.lean#two_le?>

<?lean MathlibHandbook/V02/C02/Examples.lean#dvd_mul?>

**Example (A factorization).** Factor $360$ with the least factor at each step: $360 = 2 \cdot 180 = 2 \cdot 2 \cdot 90 = 2 \cdot 2 \cdot 2 \cdot 45 = 2^3 \cdot 3 \cdot 15 = 2^3 \cdot 3^2 \cdot 5$. So `Nat.primeFactorsList 360 = [2, 2, 2, 3, 3, 5]`, `Nat.primeFactors 360 = {2, 3, 5}`, and the factorization gives the exponents $3, 2, 1$.

**Example (Euclid's numbers).** The number $m$ of the proof need not be prime; only its prime factors are new. With the product of the first primes in place of $n!$: $2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 + 1 = 2311$ is prime, but $2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 \cdot 13 + 1 = 30031 = 59 \cdot 509$.

<?lean MathlibHandbook/V02/C02/Examples.lean#infinite?>

**Counterexample (Unique factorization can fail).** Let $H = \{1, 5, 9, 13, 17, \dots\}$ be the numbers $4k + 1$. The product of two of them is again in $H$. Call $h \in H$ irreducible in $H$ if $h > 1$ and $h$ is not a product of two elements of $H$ that are greater than $1$. The numbers $9$, $21$ and $49$ are irreducible in $H$, because their divisors in $\mathbb{N}$ other than $1$ and themselves are $3$ and $7$, which are not in $H$. But $441 = 9 \cdot 49 = 21 \cdot 21$. Uniqueness fails because Euclid's lemma fails in $H$: $21 \mid 9 \cdot 49$, and $21$ divides neither factor.

### The library around it

The file `Mathlib.Data.Nat.Prime.Defs` also has `Nat.prime_two`, `Nat.Prime.one_lt` and `Nat.irreducible_iff_nat_prime`, and `Mathlib.Data.Nat.Prime.Basic` has `Nat.coprime_primes`. The subtype of the primes is `Nat.Primes`. The file `Mathlib.Data.Nat.Factors` has lemmas such as `Nat.mem_primeFactorsList` and `Nat.perm_primeFactorsList_mul`. Factorization in a general monoid, with `UniqueFactorizationMonoid`, belongs to the volume on rings.

Two modules pass from `ℕ` to `ℤ`. `Mathlib.Data.Int.Associated` has one lemma, `Int.natAbs_eq_iff_associated`: two integers have the same absolute value if and only if they are associated, that is, $a = \pm b$. `Mathlib.Data.Int.NatPrime` has three lemmas on a natural prime $p$ and integers. `Int.Prime.dvd_natAbs_of_coe_dvd_sq` states that $p \mid k^2$ gives $p \mid \lvert k \rvert$. `Int.not_prime_of_int_mul` states that $c = a b$ with $\lvert a \rvert \neq 1$ and $\lvert b \rvert \neq 1$ is not prime. `Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul` states that $p^k \mid m$, $p^l \mid n$ and $p^{k+l+1} \mid m n$ give $p^{k+1} \mid m$ or $p^{l+1} \mid n$.

### Exercises

1. (A) Find the primes up to $50$ with the sieve of Eratosthenes, and explain with the trial bound why it suffices to cross out the multiples of $2$, $3$, $5$ and $7$. *Hint.* $7^2 = 49 \leq 50 < 121$.
2. (A) Give `Nat.minFac 0`, `Nat.minFac 1` and `Nat.primeFactorsList 1`, and explain why `Nat.minFac_prime` needs `n ≠ 1`. *Hint.* The definition section gives the values.
3. (B) Prove that if $p$ is prime and $p \mid a^n$, then $p \mid a$. *Hint.* Induction on $n$ with Euclid's lemma.
4. (B) Prove that there are infinitely many primes of the form $4k + 3$. *Hint.* For primes $p_1, \dots, p_r$ of this form, a prime divisor of $4p_1 \cdots p_r - 1$ of the form $4k + 3$ exists, because a product of numbers $4k + 1$ is again of this form.
5. (C) Prove that for $n \geq 2$ the interval $n! + 2, \dots, n! + n$ contains no prime, and conclude that the gaps between consecutive primes are not bounded. *Hint.* $k \mid n! + k$ for $2 \leq k \leq n$.
6. (L) Prove that a prime that divides $n^2$ divides $n$. The solution is `prime_dvd_of_dvd_sq`.
7. (L) Prove that for each $n$ there is a prime $p > n$. The solution is `exists_prime_gt`.
8. (L) Prove that $221$ is not prime. The solution is `not_prime_221`.
9. (L) Prove that each $n \neq 1$ has a prime divisor. The solution is `exists_prime_dvd`.

### Notes and history

The infinitude of primes is Proposition 20 of Book IX of Euclid's *Elements*, and Euclid's lemma is Proposition 30 of Book VII. The *Elements* has no full statement of the uniqueness of the factorization. Gauss stated and proved the fundamental theorem of arithmetic in the *Disquisitiones Arithmeticae* (1801). The example of the numbers $4k + 1$ is due to Hilbert.

### Reference

<?reference?>
