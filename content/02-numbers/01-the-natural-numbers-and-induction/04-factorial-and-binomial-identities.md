---
title: Further results on factorials and binomial coefficients
kind: api
modules:
  - Mathlib.Data.Nat.Factorial.BigOperators
  - Mathlib.Data.Nat.Factorial.Cast
  - Mathlib.Data.Nat.Factorial.NatCast
  - Mathlib.Data.Nat.Factorial.DoubleFactorial
  - Mathlib.Data.Nat.Factorial.SuperFactorial
  - Mathlib.Data.Nat.Choose.Cast
  - Mathlib.Data.Nat.Choose.Bounds
  - Mathlib.Data.Nat.Choose.Vandermonde
  - Mathlib.Data.Nat.Choose.Central
  - Mathlib.Data.Nat.Choose.Dvd
  - Mathlib.Data.Nat.Choose.Consecutive
  - Mathlib.Data.Nat.Choose.Factorization
  - Mathlib.Data.Nat.Choose.Lucas
  - Mathlib.Data.Nat.Choose.Multinomial
explains:
  E2: [Nat.doubleFactorial_two_mul, Nat.add_choose_eq, Nat.succ_mul_centralBinom_succ, Nat.centralBinom_le_four_pow, Nat.Prime.dvd_choose_self, Choose.choose_modEq_choose_mod_mul_choose_div_nat, Nat.multinomial_spec]
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

## Further results on factorials and binomial coefficients

### Overview

The section on factorials and binomial coefficients defines $n!$ and $\binom{n}{k}$ by recursion and proves the factorial formula and the binomial theorem. The modules of this section continue that work. They write factorials as finite products, cast them to other semirings, define the double factorial and the superfactorial, and give bounds and identities for $\binom{n}{k}$: the identity of Vandermonde, the central binomial coefficient $\binom{2n}{n}$, the divisibility of $\binom{n}{k}$ by a prime, the exponent of a prime in $\binom{n}{k}$, the theorem of Lucas, and the multinomial coefficients.

A reader needs these results in combinatorics and in elementary number theory. The bounds on $\binom{2n}{n}$ and the exponents of primes in it are the main steps of the proof of Bertrand's postulate. The divisibility $p \mid \binom{p}{k}$ gives the Frobenius identity $(x + y)^p = x^p + y^p$ in characteristic $p$. The results about primes use the chapter on divisibility and primes, and the theorem of Lucas uses the congruences of Chapter 3.

### The library around it

#### Factorials as products

The module `Mathlib.Data.Nat.Factorial.BigOperators` connects the recursive definitions with finite products. The lemma `Nat.factorial_eq_prod_range_add_one` says $n! = \prod_{i < n} (i + 1)$, and `Finset.prod_range_add_one_eq_factorial` is the same equation read from right to left. The falling and rising factorials have the same form: `Nat.descFactorial_eq_prod_range` says $n (n - 1) \cdots (n - k + 1) = \prod_{i < k} (n - i)$, and `Nat.ascFactorial_eq_prod_range` says $n (n + 1) \cdots (n + k - 1) = \prod_{i < k} (n + i)$. For a function $f$ on a finite set $s$, `Nat.prod_factorial_dvd_factorial_sum` says that $\prod_{i \in s} f(i)!$ divides $(\sum_{i \in s} f(i))!$. This divisibility makes the multinomial coefficient below a natural number. The lemma `Nat.factorial_coe_dvd_prod` says that $k!$ divides the product of $k$ consecutive integers $n (n + 1) \cdots (n + k - 1)$, for each $n \in \mathbb{Z}$. The other lemmas of the module are `Nat.monotone_factorial` and `Nat.Prime.dvd_ascFactorial_iff`: a prime divides a product of consecutive numbers if and only if it divides one of the factors.

#### Casts of factorials

A cast of a factorial to a semiring is the product of the casts of the factors, by the cast lemmas of Chapter 5. The falling factorial is harder, because subtraction in $\mathbb{N}$ is truncated. The module `Mathlib.Data.Nat.Factorial.Cast` proves the case $k = 2$: `Nat.cast_descFactorial_two` says $\uparrow(a (a - 1)) = a (a - 1)$ in each ring, with the subtraction of the ring on the right. The proof is short: for $a \geq 1$ the two subtractions agree, and for $a = 0$ both sides are $0$.

The module `Mathlib.Data.Nat.Factorial.NatCast` asks when the cast of $n!$ is a unit. In a ring of characteristic $p$, with $p$ prime, `IsUnit.natCast_factorial_iff_of_charP` says that $n!$ is a unit if and only if $n < p$. The lemma `IsUnit.natCast_factorial_of_algebra` gives the unit property in each algebra over a field of characteristic zero, and `IsUnit.natCast_factorial_of_le` passes it from $n!$ to $m!$ for $m \leq n$. When $n!$ is a unit, `Nat.castChoose_eq` gives the factorial formula $\binom{m}{k} = m! \, (k!)^{-1} ((m - k)!)^{-1}$ in the ring, with `Ring.inverse`.

The module `Mathlib.Data.Nat.Choose.Cast` gives the factorial formula in a division semiring of characteristic zero. The lemma `Nat.cast_choose` says $\binom{b}{a} = b! / (a! \, (b - a)!)$ for $a \leq b$, `Nat.cast_add_choose` says $\binom{a + b}{a} = (a + b)! / (a! \, b!)$, and `Nat.cast_choose_two` says $\binom{a}{2} = a (a - 1) / 2$ in a division ring where $2 \neq 0$.

#### Double factorials and superfactorials

The double factorial $n!!$ is the product $n (n - 2) (n - 4) \cdots$, down to $1$ or $2$. The definition `Nat.doubleFactorial` in `Mathlib.Data.Nat.Factorial.DoubleFactorial` is the recursion $0!! = 1$, $1!! = 1$ and $(k + 2)!! = (k + 2) \cdot k!!$, and a postfix notation for it is available after `open Nat`. The recursion is `Nat.doubleFactorial_add_two`. The main identities are these.

| Lean name | Statement |
|---|---|
| `Nat.doubleFactorial_two_mul` | $(2n)!! = 2^n \, n!$ |
| `Nat.factorial_eq_mul_doubleFactorial` | $(n + 1)! = (n + 1)!! \cdot n!!$ |
| `Nat.doubleFactorial_eq_prod_even` | $(2n)!! = \prod_{i < n} 2 (i + 1)$ |
| `Nat.doubleFactorial_eq_prod_odd` | $(2n + 1)!! = \prod_{i < n} (2 (i + 1) + 1)$ |
| `Nat.doubleFactorial_le_factorial` | $n!! \leq n!$ |
| `Nat.doubleFactorial_pos` | $0 < n!!$ |

*Proof of the first identity.* Induction on $n$. For $n = 0$ both sides are $1$. For the step, $(2n + 2)!! = (2n + 2) \cdot (2n)!! = 2 (n + 1) \cdot 2^n n! = 2^{n + 1} (n + 1)!$. $\square$

The superfactorial $\mathrm{sf}(n) = 1! \cdot 2! \cdots n!$ is `Nat.superFactorial` in `Mathlib.Data.Nat.Factorial.SuperFactorial`, with the scoped notation `sf n`. Its recursion is `Nat.superFactorial_succ`, and `Nat.prod_Icc_factorial` and `Nat.prod_range_succ_factorial` write it as a product. The lemma `Nat.superFactorial_two_mul` expresses $\mathrm{sf}(2n)$ with the factorials of odd numbers.

#### Bounds and Vandermonde's identity

The module `Mathlib.Data.Nat.Choose.Bounds` gives upper and lower bounds. The simplest are `Nat.choose_le_two_pow`, $\binom{n}{k} \leq 2^n$, which follows from $\sum_k \binom{n}{k} = 2^n$, and `Nat.choose_le_pow`, $\binom{n}{k} \leq n^k$. The sharper `Nat.choose_le_descFactorial` says $\binom{n}{k} \leq n (n - 1) \cdots (n - k + 1)$. Two bounds take values in an ordered field: `Nat.choose_le_pow_div` says $\binom{n}{r} \leq n^r / r!$, and `Nat.pow_le_choose` says $(n + 1 - r)^r / r! \leq \binom{n}{r}$. Each bound with `_lt_` in the name is the strict form, under a hypothesis such as $2 \leq k$.

The module `Mathlib.Data.Nat.Choose.Vandermonde` proves Vandermonde's identity, `Nat.add_choose_eq`:
$$\binom{m + n}{k} = \sum_{i + j = k} \binom{m}{i} \binom{n}{j}.$$
The sum runs over the antidiagonal `Finset.antidiagonal k` of pairs $(i, j)$ with $i + j = k$. *Proof sketch.* Compare the coefficients of $X^k$ in $(1 + X)^{m + n} = (1 + X)^m (1 + X)^n$. The binomial theorem gives $\binom{m + n}{k}$ on the left. The product of the two expansions gives the sum of $\binom{m}{i} \binom{n}{j}$ over $i + j = k$ on the right. $\square$ With $m = n = k$ and the symmetry $\binom{n}{j} = \binom{n}{n - j}$, it gives `Nat.sum_range_choose_sq`: $\sum_{i \leq n} \binom{n}{i}^2 = \binom{2n}{n}$.

#### The central binomial coefficient

The module `Mathlib.Data.Nat.Choose.Central` defines `Nat.centralBinom n` as $\binom{2n}{n}$; the equation is `Nat.centralBinom_eq_two_mul_choose`. It is the largest coefficient in row $2n$ of Pascal's triangle (`Nat.choose_le_centralBinom`). The recursion is `Nat.succ_mul_centralBinom_succ`:
$$(n + 1) \binom{2n + 2}{n + 1} = 2 (2n + 1) \binom{2n}{n}.$$
*Proof.* Both sides are $(2n + 2)! / ((n + 1)! \, n!)$. Indeed $\binom{2n + 2}{n + 1} = \frac{(2n + 2)(2n + 1)}{(n + 1)^2} \binom{2n}{n}$, and $(2n + 2) / (n + 1) = 2$. $\square$

The bounds of exponential size are the input to Bertrand's postulate. By `Nat.centralBinom_le_four_pow`, $\binom{2n}{n} \leq 4^n$, because $\binom{2n}{n}$ is one term of $\sum_k \binom{2n}{k} = 4^n$. In the other direction, `Nat.four_pow_le_two_mul_add_one_mul_centralBinom` says $4^n \leq (2n + 1) \binom{2n}{n}$, because $\binom{2n}{n}$ is the largest of the $2n + 1$ terms of the same sum. The lemma `Nat.four_pow_lt_mul_centralBinom` sharpens this to $4^n < n \binom{2n}{n}$ for $n \geq 4$. The module also proves `Nat.succ_dvd_centralBinom`, $n + 1 \mid \binom{2n}{n}$, so the Catalan number $\binom{2n}{n} / (n + 1)$ is a natural number, and `Nat.two_dvd_centralBinom_of_one_le`.

#### Primes that divide binomial coefficients

The module `Mathlib.Data.Nat.Choose.Dvd` has four results. The first is `Nat.Prime.dvd_choose_self`: for a prime $p$ and $0 < k < p$, $p \mid \binom{p}{k}$. *Proof.* By the factorial formula, $\binom{p}{k} \, k! \, (p - k)! = p!$, so $p$ divides the left side. The prime $p$ does not divide $k!$ or $(p - k)!$, because all their factors are smaller than $p$. By Euclid's lemma, $p \mid \binom{p}{k}$. $\square$ The same argument gives `Nat.Prime.dvd_choose_add` and `Nat.Prime.dvd_choose`, and `Nat.Prime.coprime_choose_of_lt` says that $p$ is coprime to $\binom{b}{a}$ when $b < p$. The module `Mathlib.Data.Nat.Choose.Consecutive` gives a test for a prime $p > n$: `Nat.Prime.dvd_choose_iff` says $p \mid \binom{k}{n}$ if and only if $p$ divides one of $k, k - 1, \ldots, k - n + 1$.

#### The exponent of a prime

The module `Mathlib.Data.Nat.Choose.Factorization` computes `(n.choose k).factorization p`, the exponent of $p$ in $\binom{n}{k}$. The function `Nat.factorization` is the subject of the section on factorizations in Chapter 2. Legendre's formula `Nat.factorization_factorial` says that the exponent of $p$ in $n!$ is $\sum_{i \geq 1} \lfloor n / p^i \rfloor$, with the sum cut at any $b$ with $\log_p n < b$. The form `Nat.sub_one_mul_factorization_factorial` says $(p - 1) \, v_p(n!) = n - s_p(n)$, where $s_p(n)$ is the sum of the digits of $n$ in base $p$.

Kummer's theorem `Nat.factorization_choose` says that the exponent of $p$ in $\binom{n}{k}$ is the number of $i \geq 1$ with $p^i \leq (k \bmod p^i) + ((n - k) \bmod p^i)$, that is, the number of carries in the addition of $k$ and $n - k$ in base $p$. From it come the bounds that the proof of Bertrand's postulate uses.

| Lean name | Statement |
|---|---|
| `Nat.factorization_choose_le_log` | $v_p \binom{n}{k} \leq \log_p n$ |
| `Nat.pow_factorization_choose_le` | $p^{v_p \binom{n}{k}} \leq n$ for $n > 0$ |
| `Nat.factorization_choose_le_one` | $v_p \binom{n}{k} \leq 1$ if $n < p^2$ |
| `Nat.factorization_choose_eq_zero_of_lt` | $v_p \binom{n}{k} = 0$ if $n < p$ |
| `Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul` | $v_p \binom{2n}{n} = 0$ if $2 < n$, $p \leq n$ and $2n < 3p$ |
| `Nat.prod_pow_factorization_centralBinom` | $\binom{2n}{n} = \prod_{p \leq 2n} p^{v_p \binom{2n}{n}}$ |

#### The theorem of Lucas

The module `Mathlib.Data.Nat.Choose.Lucas` proves the theorem of Lucas. The names are in the namespace `Choose`, and the prime is an instance argument `[Fact (Nat.Prime p)]`. The basic step is `Choose.choose_modEq_choose_mod_mul_choose_div_nat`:
$$\binom{n}{k} \equiv \binom{n \bmod p}{k \bmod p} \binom{\lfloor n / p \rfloor}{\lfloor k / p \rfloor} \pmod p.$$
*Proof sketch.* In $(\mathbb{Z}/p)[X]$, the Frobenius identity gives $(1 + X)^p = 1 + X^p$. Write $n = p q + r$ with $r < p$. Then $(1 + X)^n = (1 + X^p)^q (1 + X)^r$. The coefficient of $X^k$ on the right comes from the single pair $X^{p j} X^{i}$ with $i = k \bmod p$ and $j = \lfloor k / p \rfloor$, because $i \leq r < p$ forces this choice. $\square$ An induction on the number of digits gives `Choose.lucas_theorem_nat`: when $n, k < p^a$, $\binom{n}{k}$ is congruent to the product of $\binom{n_i}{k_i}$ over the base $p$ digits $n_i$, $k_i$. Each result has a form in `Int.ModEq` with the same name without `_nat`. The module also computes the gcd of the coefficients $\binom{n}{1}, \ldots, \binom{n}{n - 1}$: it is the prime $p$ when $n$ is a power of $p$ (`Choose.gcd_choose_eq_minFac_of_isPrimePow`), and $1$ otherwise (`Choose.gcd_choose_eq_one_of_not_isPrimePow`).

#### Multinomial coefficients

The module `Mathlib.Data.Nat.Choose.Multinomial` defines `Nat.multinomial s f`, for a finite set $s$ and $f : \alpha \to \mathbb{N}$, as
$$\binom{\sum_{i \in s} f(i)}{(f(i))_{i \in s}} = \frac{(\sum_{i \in s} f(i))!}{\prod_{i \in s} f(i)!}.$$
It counts the words with $f(i)$ letters $i$ for each $i \in s$. The division is exact by `Nat.prod_factorial_dvd_factorial_sum`, and `Nat.multinomial_spec` states the formula without division: $\prod_{i \in s} f(i)! \cdot \mathrm{multinomial}(s, f) = (\sum_{i \in s} f(i))!$. The recursion `Nat.multinomial_insert` peels off one letter: for $a \notin s$, the coefficient for $\{a\} \cup s$ is $\binom{f(a) + \sum_{i \in s} f(i)}{f(a)}$ times the coefficient for $s$. For two letters, `Nat.binomial_eq_choose` gives back $\binom{f(a) + f(b)}{f(a)}$.

The same coefficient has other forms: `Finsupp.multinomial` for a finitely supported function, `Multiset.multinomial` and `List.multinomial` for a collection of numbers, and `Multiset.countPerms m`, the number of lists with the multiset $m$ of entries. The multinomial theorem `Finset.sum_pow_eq_sum_piAntidiag` expands $(\sum_{i \in s} x_i)^n$ in a commutative semiring as the sum over the $k : s \to \mathbb{N}$ with $\sum k_i = n$ of $\mathrm{multinomial}(s, k) \prod_{i} x_i^{k_i}$. The form `Finset.sum_pow` sums over `Finset.sym s n` with `Multiset.countPerms`, and the forms with `_of_commute` need only that the $x_i$ commute in pairs.

#### Common errors

1. `Nat.centralBinom n` is $\binom{2n}{n}$, not $\binom{n}{n / 2}$. The lemma `Nat.centralBinom_eq_two_mul_choose` unfolds it.
2. The lemmas of Lucas are in the namespace `Choose`, not `Nat`, and they take the prime as an instance `[Fact (Nat.Prime p)]`. Provide it with `haveI := Fact.mk hp` before the call.
3. The natural number formula $\binom{n}{k} = n! / (k! (n - k)!)$ uses division in $\mathbb{N}$. To compute in a field, use `Nat.cast_choose`, which needs $k \leq n$ and characteristic zero; the cast of a truncated subtraction is not the subtraction of the field.

### Exercises

1. (A) Prove $(2n + 1)!! \cdot 2^n \, n! = (2n + 1)!$ from `Nat.doubleFactorial_two_mul` and `Nat.factorial_eq_mul_doubleFactorial`.
2. (A) Use `Nat.Prime.dvd_choose_self` and the binomial theorem to show $(x + y)^p \equiv x^p + y^p \pmod p$ for integers $x$, $y$ and a prime $p$.
3. (B) Prove $\sum_{i \leq n} \binom{n}{i}^2 = \binom{2n}{n}$ from Vandermonde's identity, and compare your proof with `Nat.sum_range_choose_sq`.
4. (A) Show that $\binom{2n}{n} = 2 \binom{2n - 1}{n - 1}$ for $n \geq 1$, and deduce `Nat.two_dvd_centralBinom_of_one_le`.
5. (B) Use the theorem of Lucas to find the number of odd entries in row $n$ of Pascal's triangle, in terms of the binary digits of $n$.
6. (C) Prove Legendre's formula $v_p(n!) = \sum_{i \geq 1} \lfloor n / p^i \rfloor$ by counting, for each $i$, the multiples of $p^i$ in $\{1, \ldots, n\}$.

### Reference

<?reference?>
