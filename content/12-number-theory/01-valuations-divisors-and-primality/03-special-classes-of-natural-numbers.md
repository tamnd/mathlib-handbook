---
title: Special classes of natural numbers
kind: api
modules:
  - Mathlib.NumberTheory.FactorisationProperties
  - Mathlib.NumberTheory.AlmostPrime
  - Mathlib.NumberTheory.FrobeniusNumber
  - Mathlib.NumberTheory.ADEInequality
  - Mathlib.NumberTheory.MaricaSchoenheim
explains:
  E2: [Nat.deficient_or_perfect_or_abundant, Nat.Prime.deficient_pow, Nat.Abundant.of_dvd, Nat.weird_seventy, Nat.IsAlmostPrime.mul, frobeniusNumber_pair, ADEInequality.classification, Nat.grahamConjecture_of_squarefree]
  E1: auto
families: []
requires: [V02.C02, V03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Special classes of natural numbers

### Overview

Section 2 defined the proper divisors of a number and the perfect numbers. This section describes five small modules that define further classes of natural numbers by their divisors, their prime factors or their additive structure. The abundant, deficient, pseudoperfect and weird numbers compare a number with the sum of its proper divisors. The almost primes count the prime factors with multiplicity. The Frobenius number of a set of generators is the largest number that is not a sum of the generators. Two more modules solve a small Diophantine inequality and a combinatorial problem on the greatest common divisor.

Each module is short and self-contained. The results are elementary, and most proofs fit in a few lines. The modules are good first examples of how Mathlib states a property of natural numbers: a decidable predicate `ℕ → Prop`, a few lemmas on its behaviour under products and divisibility, and a few concrete examples that the kernel checks with `decide`.

### The library around it

#### Abundant, deficient and weird numbers

Let $s(n) = \sum_{d \mid n, d < n} d$ be the sum of the proper divisors of $n$. The module `Mathlib.NumberTheory.FactorisationProperties` compares $s(n)$ with $n$.

| Lean name | Statement |
|---|---|
| `Nat.Abundant` | $n < s(n)$ |
| `Nat.Deficient` | $s(n) < n$ |
| `Nat.Pseudoperfect` | $n > 0$ and some subset of the proper divisors has sum $n$ |
| `Nat.Weird` | $n$ is abundant and not pseudoperfect |
| `Nat.abundancyIndex` | the rational number $\sigma(n)/n$, with $\sigma(n) = s(n) + n$ |

A perfect number, `Nat.Perfect` of Section 2, has $s(n) = n$ and $n > 0$. Each predicate is decidable, with the instances `Nat.instDecidableAbundant`, `Nat.instDecidableDeficient`, `Nat.instDecidablePseudoperfect` and `Nat.instDecidableWeird`. So `decide` proves the examples `Nat.abundant_twelve`, `Nat.deficient_three` and `Nat.weird_seventy`.

**Trichotomy.** Each $n \neq 0$ is exactly one of deficient, perfect and abundant. This is `Nat.deficient_or_perfect_or_abundant`, with the three exclusive forms `Nat.abundant_iff_not_perfect_and_not_deficient`, `Nat.deficient_iff_not_abundant_and_not_perfect` and `Nat.perfect_iff_not_abundant_and_not_deficient`. The proof is the trichotomy of the order on $\mathbb{N}$, applied to $s(n)$ and $n$. The number $0$ is in no class: `Nat.not_abundant_zero`, `Nat.not_deficient_zero`, `Nat.not_weird_zero`.

**Prime powers are deficient.** For a prime $p$ and $m \geq 0$, the proper divisors of $p^m$ are $1, p, \ldots, p^{m-1}$, so
$$s(p^m) = \frac{p^m - 1}{p - 1} \leq p^m - 1 < p^m.$$
This is `Nat.Prime.deficient_pow`, with the special cases `Nat.Prime.deficient` and `IsPrimePow.deficient`. A prime is also not abundant, not perfect, not pseudoperfect and not weird: `Nat.Prime.not_abundant`, `Nat.Prime.not_perfect`, `Nat.Prime.not_pseudoperfect`, `Nat.Prime.not_weird`.

**Abundance goes up along divisibility.** The abundancy index has the form
$$\frac{\sigma(n)}{n} = \sum_{d \mid n} \frac{d}{n} = \sum_{e \mid n} \frac{1}{e},$$
since $d \mapsto n/d$ is a bijection of the divisors. If $m \mid n$ and $n \neq 0$, each divisor of $m$ divides $n$, so $\sigma(m)/m \leq \sigma(n)/n$. This is `Nat.abundancyIndex_le_of_dvd`. A number is abundant if and only if its abundancy index is larger than $2$, by `Nat.abundant_iff_two_lt_abundancyIndex`. So a nonzero multiple of an abundant number is abundant: `Nat.Abundant.of_dvd` and `Nat.Abundant.mul_left`. The form with the sum of all divisors is `Nat.abundant_iff_sum_divisors`.

The infinite families follow. The even multiples of $12$ give `Nat.infinite_even_abundant`, and the odd multiples of $945 = 3^3 \cdot 5 \cdot 7$, the smallest odd abundant number, give `Nat.infinite_odd_abundant`. The powers of $2$ give `Nat.infinite_even_deficient`, and the odd primes give `Nat.infinite_odd_deficient` and `Nat.infinite_deficient`.

**Pseudoperfect and weird numbers.** A perfect number is pseudoperfect, since the set of all its proper divisors has sum $n$: `Nat.Perfect.pseudoperfect`. The negation of the definition is `Nat.not_pseudoperfect_iff_forall`. The number $70$ is weird. Its proper divisors are $1, 2, 5, 7, 10, 14, 35$, with sum $74 > 70$, so $70$ is abundant. A subset with sum $70$ would leave out a subset with sum $4$, and no subset of these divisors has sum $4$. The lemma `Nat.Weird.pos` says that a weird number is positive.

#### Almost primes

The module `Mathlib.NumberTheory.AlmostPrime` uses $\Omega(n)$, the number of prime factors of $n$ counted with multiplicity, which is `ArithmeticFunction.cardFactors` of Chapter 2. The number $n$ is $k$-almost prime, `Nat.IsAlmostPrime k n`, if $n \neq 0$ and $\Omega(n) = k$. The weaker predicate `Nat.IsAtMostAlmostPrime k n` asks $\Omega(n) \leq k$. A semiprime, `Nat.IsSemiprime n`, is a $2$-almost prime. It is an abbreviation, so each lemma on `Nat.IsAlmostPrime 2` applies to it.

The first values are the expected ones: `Nat.isAlmostPrime_zero_iff` says that only $1$ is $0$-almost prime, and `Nat.isAlmostPrime_one_iff` says that the $1$-almost primes are the primes. Since $\Omega(mn) = \Omega(m) + \Omega(n)$ for $m, n \neq 0$, the classes multiply: if $m$ is $k$-almost prime and $n$ is $l$-almost prime, then $mn$ is $(k + l)$-almost prime. This is `Nat.IsAlmostPrime.mul`, with the version `Nat.IsAtMostAlmostPrime.mul`. The products $pq$ and $p^2$ of primes are semiprimes, by `Nat.Prime.mul_isAlmostPrime_two` and `Nat.Prime.sq_isAlmostPrime_two`. The two predicates are decidable, so `decide` proves small cases.

#### The Frobenius number

Let $S \subseteq \mathbb{N}$. The numbers that are sums of elements of $S$, with repetitions, form the additive submonoid `AddSubmonoid.closure S`. A number $n$ is the Frobenius number of $S$, `FrobeniusNumber n S`, if $n$ is the largest number outside this submonoid. The lemma `frobeniusNumber_iff` unfolds the definition: $n$ is not in the closure, and each $k > n$ is in it.

**Theorem (two generators).** Let $m, n > 1$ be coprime. Then the Frobenius number of $\{m, n\}$ is $mn - m - n$.

*Proof.* Suppose $am + bn = mn - m - n$ with $a, b \geq 0$. Then $(a + 1)m + (b + 1)n = mn$. So $m \mid (b + 1)n$, hence $m \mid b + 1$ since $\gcd(m, n) = 1$, and in the same way $n \mid a + 1$. Then $(a + 1)m + (b + 1)n \geq nm + mn > mn$, a contradiction. Now let $k > mn - m - n$. Since $n$ is a unit modulo $m$, there is $b$ with $0 \leq b < m$ and $bn \equiv k \pmod m$. Then $k - bn$ is divisible by $m$, and $k - bn \geq k - (m - 1)n > -m$. So $k - bn = am$ with $a \geq 0$. $\square$

This is `frobeniusNumber_pair`. For a general set the module uses the greatest common divisor of a set, `Nat.setGcd`, with the API `Nat.dvd_setGcd_iff`, `Nat.setGcd_dvd_of_mem`, `Nat.setGcd_mono` and `Nat.setGcd_eq_zero_iff`. The key fact is `Nat.exists_mem_closure_of_ge`: each large multiple of $\gcd(S)$ is a sum of elements of $S$. Its proof uses that each ideal of the semiring $\mathbb{N}$ is finitely generated, the instance `Nat.instIsNoetherian`, and that each additive submonoid of $\mathbb{N}$ is finitely generated, `Nat.addSubmonoid_fg`. The final result is `exists_frobeniusNumber_iff`: a Frobenius number of $S$ exists if and only if $\gcd(S) = 1$ and $1 \notin S$.

#### The ADE inequality

The module `Mathlib.NumberTheory.ADEInequality` finds all positive integers $p, q, r$ with
$$\frac1p + \frac1q + \frac1r > 1.$$
The triples are unordered, so the library uses a multiset `Multiset ℕ+` and the sum `ADEInequality.sumInv`, with `ADEInequality.sumInv_pqr` for the sum of $\{p, q, r\}$. The solutions are the families `ADEInequality.A' q r` $= \{1, q, r\}$ and `ADEInequality.D' r` $= \{2, 2, r\}$, and the three triples `ADEInequality.E6` $= \{2, 3, 3\}$, `ADEInequality.E7` $= \{2, 3, 4\}$ and `ADEInequality.E8` $= \{2, 3, 5\}$. The names come from the Dynkin diagrams of types A, D and E, which this inequality classifies. The predicate `ADEInequality.Admissible` says that a multiset is one of these.

**Theorem.** `ADEInequality.classification`: $\frac1p + \frac1q + \frac1r > 1$ if and only if $\{p, q, r\}$ is admissible.

*Proof.* Each admissible triple satisfies the inequality by a direct computation: `ADEInequality.Admissible.one_lt_sumInv`. For the converse, sort the triple, $p \leq q \leq r$. If $p \geq 3$, the sum is at most $1$, so $p \leq 2$ (`ADEInequality.lt_three`). If $p = 1$, the triple is $\{1, q, r\}$. If $p = 2$ and $q \geq 4$, the sum is at most $\frac12 + \frac14 + \frac14 = 1$, so $q \leq 3$ (`ADEInequality.lt_four`). If $q = 2$, the triple is $\{2, 2, r\}$. If $q = 3$, then $\frac1r > \frac16$, so $r < 6$ (`ADEInequality.lt_six`), and $r \in \{3, 4, 5\}$. $\square$

#### Graham's problem for squarefree numbers

The module `Mathlib.NumberTheory.MaricaSchoenheim` states a problem of Graham as the predicate `Nat.GrahamConjecture n f`: for each strictly increasing sequence $f(0) < \cdots < f(n - 1)$ of positive integers, there are $i, j$ with $f(i)/\gcd(f(i), f(j)) \geq n$. The module proves the case where each $f(i)$ is squarefree, `Nat.grahamConjecture_of_squarefree`.

*Proof sketch.* A squarefree number is the product of a finite set of primes, and distinct numbers give distinct sets $S_i$. Then $f(i)/\gcd(f(i), f(j))$ is the product of the primes in $S_i \setminus S_j$. The Marica and Schoenheim inequality, `Finset.card_le_card_diffs`, says that a family of $n$ distinct finite sets has at least $n$ distinct differences $S_i \setminus S_j$. So the quotients take at least $n$ distinct positive values, and one of them is at least $n$. $\square$

#### Common errors

1. `Nat.Abundant n` compares $n$ with the sum of the proper divisors, not of all divisors. The form with all divisors is `Nat.abundant_iff_sum_divisors`, with the factor $2$.
2. `Nat.IsAlmostPrime k n` counts prime factors with multiplicity. So $12 = 2^2 \cdot 3$ is $3$-almost prime, not $2$-almost prime.
3. `FrobeniusNumber n S` is a proposition, not a function of $S$. To use the value $mn - m - n$, apply `frobeniusNumber_pair` and then `frobeniusNumber_iff`.

### Exercises

1. (A) Show that $945$ is abundant and that no odd number below $945$ is abundant.
2. (A) Show that $p^2 q$ is $3$-almost prime for primes $p$ and $q$, with `Nat.IsAlmostPrime.mul`.
3. (A) Compute the Frobenius number of $\{4, 7\}$ and write $18$, $19$ and $20$ as sums of $4$ and $7$.
4. (B) Show that $\sigma(n)/n$ can be arbitrarily large. Hint: use $n = k!$ and the harmonic series.
5. (B) Show that the set $\{6, 10, 15\}$ has a Frobenius number, although no two of its elements are coprime.
6. (C) Show that a pseudoperfect number times a positive integer is pseudoperfect, and deduce that each multiple of $6$ is pseudoperfect.

### Reference

<?reference?>
