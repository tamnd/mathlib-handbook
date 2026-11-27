---
title: Elementary results on primes
kind: theory
modules:
  - Mathlib.NumberTheory.SumPrimeReciprocals
  - Mathlib.NumberTheory.PrimesCongruentOne
  - Mathlib.NumberTheory.Primorial
  - Mathlib.NumberTheory.Bertrand
explains:
  E3: [Nat.Primes.not_summable_one_div, primorial_le_four_pow, Nat.bertrand, Nat.exists_prime_gt_modEq_one]
  E2: [not_summable_one_div_on_primes, one_half_le_sum_primes_ge_one_div, Nat.roughNumbersUpTo_card_le', Nat.Primes.summable_rpow, primorial, primorial_add_le, Nat.Prime.dvd_primorial_iff, bertrand_main_inequality, centralBinom_le_of_no_bertrand_prime, Nat.exists_prime_lt_and_le_two_mul, Nat.infinite_setOfPred_prime_modEq_one, Nat.frequently_atTop_modEq_one]
  E1: auto
families: [primorial_*, Nat.Primes.*]
requires: [V12.C01, V02.C02, V05.C04, V15.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Elementary results on primes

### Overview

Euclid's theorem says that there are infinitely many primes (Volume 2, Chapter 2). This section proves four sharper results by elementary means, as Mathlib proves them. The sum $\sum 1/p$ over the primes diverges, so the primes are not too sparse. The product of the primes up to $n$ is at most $4^n$, so they are not too dense. Bertrand's postulate puts a prime between $n$ and $2n$. And for each $k \ge 1$ there are infinitely many primes $p \equiv 1 \pmod k$, a first case of Dirichlet's theorem of Section 3.

The proofs use counting, binomial coefficients and the $p$-adic valuation of Chapter 1.

### Definitions

**Definition (Primorial).** For $n \ge 0$, the primorial $n\#$ is the product of the primes $p \le n$. So $1\# = 1$, $2\# = 2$, $6\# = 30$ and $10\# = 210$.

::: mathlib
`primorial` · `Mathlib.NumberTheory.Primorial`

`primorial n = ∏ p ∈ Finset.range (n + 1) with p.Prime, p`, with the notation `n#` under `open Nat`. The lemma `Nat.Prime.dvd_primorial_iff` says `p ∣ primorial n ↔ p ≤ n` for a prime `p`.

<?decl primorial?>
:::

**Definition (Rough numbers).** For $k \ge 0$, an integer $n \ge 1$ is $k$-rough if every prime factor of $n$ is at least $k$, and $k$-smooth if every prime factor is less than $k$.

::: mathlib
`Nat.roughNumbersUpTo` · `Mathlib.NumberTheory.SmoothNumbers`

`Nat.smoothNumbers k` is the set of `n ≠ 0` with all prime factors `< k`, and `Nat.roughNumbersUpTo N k` is the finite set of `n ≤ N`, `n ≠ 0`, that are not `k`-smooth. Despite its name, this is the set of the numbers up to $N$ with at least one prime factor $\ge k$.

<?decl Nat.roughNumbersUpTo?>
:::

### Theorems and proofs

**Theorem (Euler).** $\sum_p 1/p$ diverges.

*Proof (Erdős).* Suppose the series converges. Then there is $k$ with $\sum_{p \ge k}1/p < \frac12$. Let $r$ be the number of primes less than $k$ and $N = 4^{r+1}$. Split the integers $1 \le n \le N$ into two classes.

Class 1: $n$ has a prime factor $p \ge k$. For a fixed $p$ there are at most $N/p$ multiples of $p$ up to $N$, so class 1 has at most $N\sum_{p\ge k}1/p < N/2$ elements.

Class 2: all prime factors of $n$ are less than $k$. Write $n = ab^2$ with $a$ squarefree. Then $a$ is a product of a subset of the $r$ primes below $k$, so there are at most $2^r$ choices for $a$, and $b \le \sqrt N = 2^{r+1}$. So class 2 has at most $2^r \cdot 2^{r+1} = N/2$ elements.

The two classes contain all $N$ integers, but have fewer than $N$ elements together. This is a contradiction. $\square$

::: mathlib
`Nat.Primes.not_summable_one_div` · `Mathlib.NumberTheory.SumPrimeReciprocals`

`¬Summable fun p : Nat.Primes ↦ 1 / (p : ℝ)`. The same statement for a function on `ℕ` with an indicator is `not_summable_one_div_on_primes`. The proof is the one above: `Nat.roughNumbersUpTo_card_le'` bounds class 1, and `one_half_le_sum_primes_ge_one_div` is the contradiction in the form $\sum_{k \le p \le 4^{r+1}}1/p \ge \frac12$. The general criterion `Nat.Primes.summable_rpow` says that $\sum_p p^r$ converges if and only if $r < -1$.

<?decl Nat.Primes.not_summable_one_div?>
:::

**Theorem (Primorial bound).** $n\# \le 4^n$ for all $n \ge 0$.

*Proof.* Strong induction on $n$. For $n \le 2$ check directly: $1 \le 1$, $1 \le 4$, $2 \le 16$. Let $n \ge 3$. If $n$ is even, $n$ is not prime, so $n\# = (n - 1)\# \le 4^{n-1}$. Let $n = 2m + 1$ be odd with $m \ge 1$. Each prime $p$ with $m + 2 \le p \le 2m + 1$ divides $(2m + 1)!$ but not $m!\,(m + 1)!$, so it divides $\binom{2m+1}{m}$. These primes are distinct, so their product divides $\binom{2m+1}{m}$. The two binomial coefficients $\binom{2m+1}{m}$ and $\binom{2m+1}{m+1}$ are equal and occur in $\sum_k\binom{2m+1}{k} = 2^{2m+1}$, so $\binom{2m+1}{m} \le 4^m$. Then
$$(2m + 1)\# = (m + 1)\# \cdot \prod_{m + 2 \le p \le 2m + 1}p \le 4^{m+1}\cdot 4^m = 4^{2m+1}. \qquad \square$$

::: mathlib
`primorial_le_four_pow` · `Mathlib.NumberTheory.Primorial`

`primorial n ≤ 4 ^ n`, with the step `primorial_add_le`: for `n ≤ m`, `primorial (m + n) ≤ primorial m * (m + n).choose m`.

<?decl primorial_le_four_pow?>
:::

**Lemma (Valuations of the central binomial coefficient).** Let $n \ge 1$, $N = \binom{2n}{n}$ and $p$ a prime. Then

1. $p^{v_p(N)} \le 2n$;
2. $v_p(N) \le 1$ if $p > \sqrt{2n}$;
3. $v_p(N) = 0$ if $n \ge 3$ and $\frac{2n}{3} < p \le n$.

*Proof.* Legendre's formula of Chapter 1 gives $v_p(N) = \sum_{k\ge1}\left(\lfloor 2n/p^k\rfloor - 2\lfloor n/p^k\rfloor\right)$. Each term is $0$ or $1$, since $\lfloor 2x\rfloor - 2\lfloor x\rfloor \in \{0, 1\}$, and it is $0$ when $p^k > 2n$. So $v_p(N)$ is at most the number of $k \ge 1$ with $p^k \le 2n$, which gives (1), and (2) since then only $k = 1$ counts. For (3), $p > \frac{2n}{3} \ge 2$, so $p \ge 3$ and $p^2 \ge 3p > 2n$; hence only $k = 1$ counts, and $\lfloor 2n/p\rfloor - 2\lfloor n/p\rfloor = 2 - 2 = 0$ since $1 \le n/p < \frac32$ and $2 \le 2n/p < 3$. $\square$

**Theorem (Bertrand's postulate).** For each $n \ge 1$ there is a prime $p$ with $n < p \le 2n$.

*Proof.* Let $N = \binom{2n}{n}$. It is the largest of the $2n + 1$ terms of $\sum_k\binom{2n}{k} = 4^n$, so $N \ge \frac{4^n}{2n + 1}$, and $N \ge \frac{4^n}{2n}$ for $n \ge 1$ after merging the two terms $\binom{2n}{0} + \binom{2n}{2n} = 2 \le N$.

Suppose that no prime lies in $(n, 2n]$. Every prime factor of $N$ is at most $2n$, so by the lemma, part (3), it is at most $\frac{2n}{3}$. Split the prime factors at $\sqrt{2n}$. There are at most $\sqrt{2n}$ primes $p \le \sqrt{2n}$, each with $p^{v_p(N)} \le 2n$ by (1). The primes in $(\sqrt{2n}, \frac{2n}{3}]$ occur with exponent at most $1$ by (2), and their product is at most $\lfloor 2n/3\rfloor\# \le 4^{2n/3}$ by the primorial bound. So
$$\frac{4^n}{2n} \le N \le (2n)^{\sqrt{2n}}\,4^{2n/3}, \qquad\text{that is,}\qquad 4^{n} \le 2n\,(2n)^{\sqrt{2n}}\,4^{2n/3}.$$
This inequality is false for $n \ge 512$. Indeed, take logarithms: it says $\frac{n}{3}\log 4 \le (\sqrt{2n} + 1)\log(2n)$, and for $n = 512$ the left side is $236.6$ and the right side $33 \log 1024 = 228.7$; the left side grows faster than the right side for larger $n$, since its derivative $\frac{\log 4}{3} = 0.462$ exceeds that of the right side, $\frac{\log(2n)}{\sqrt{2n}} + \frac{\sqrt{2n} + 1}{n} < 0.22 + 0.07$ for $n \ge 512$.

For $1 \le n < 512$, each interval $(n, 2n]$ contains one of the primes $2, 3, 5, 7, 13, 23, 43, 83, 163, 317, 631$, since each of them is less than twice the previous one. $\square$

::: mathlib
`Nat.bertrand` · `Mathlib.NumberTheory.Bertrand`

`∀ n ≠ 0, ∃ p, p.Prime ∧ n < p ∧ p ≤ 2 * n`, also under the name `Nat.exists_prime_lt_and_le_two_mul`. The proof follows the one above. The bound by the prime factors is `centralBinom_le_of_no_bertrand_prime`, and the analytic inequality is `bertrand_main_inequality` for `512 ≤ n`, in the form $n\,(2n)^{\lfloor\sqrt{2n}\rfloor}\,4^{\lfloor 2n/3\rfloor} \le 4^n$, which is slightly sharper than the inequality above. The small cases use the list of primes above with `Nat.exists_prime_lt_and_le_two_mul_succ`.

<?decl Nat.bertrand?>
:::

**Theorem (Primes $\equiv 1 \bmod k$).** For each $k \ge 1$ and each $n$ there is a prime $p > n$ with $p \equiv 1 \pmod k$.

*Proof.* Let $\Phi_k \in \mathbb{Z}[X]$ be the $k$-th cyclotomic polynomial, so that $X^k - 1 = \prod_{d \mid k}\Phi_d$, with $\Phi_k$ monic of degree $\varphi(k) \ge 1$. Choose an integer $b$ divisible by $k \cdot n!$ and so large that $|\Phi_k(b)| > 1$, which is possible since $\Phi_k$ is not constant. Let $p$ be a prime factor of $\Phi_k(b)$. Since $\Phi_k(0) = \pm 1$ and $p \mid b$ would give $\Phi_k(b) \equiv \Phi_k(0) = \pm1 \pmod p$, $p \nmid b$; so $p > n$ and $p \nmid k$.

The order of $b$ modulo $p$ is $k$. First $b^k \equiv 1$, since $\Phi_k(b) \mid b^k - 1$. Suppose the order is $d < k$, with $d \mid k$. Then $b$ is a root of $X^d - 1 = \prod_{e \mid d}\Phi_e$ modulo $p$, so of $\Phi_e$ for some $e \mid d$, and also of $\Phi_k$. Both factors occur in $X^k - 1$, so $b$ is a double root of $X^k - 1$ in $\mathbb{F}_p$. But the derivative $kX^{k-1}$ does not vanish at $b \ne 0$ since $p \nmid k$, so $X^k - 1$ has no double root. So the order is $k$, and $k \mid p - 1$ by Lagrange's theorem in $\mathbb{F}_p^\times$ (Volume 5, Chapter 4). $\square$

::: mathlib
`Nat.exists_prime_gt_modEq_one` · `Mathlib.NumberTheory.PrimesCongruentOne`

`k ≠ 0 → ∃ p, p.Prime ∧ n < p ∧ p ≡ 1 [MOD k]`, with `Nat.frequently_atTop_modEq_one` and `Nat.infinite_setOfPred_prime_modEq_one` as corollaries. The proof uses `Polynomial.cyclotomic` and `Polynomial.orderOf_root_cyclotomic_dvd`, which says that the order of a root of $\Phi_k$ in $(\mathbb{Z}/p)^\times$ divides $k$.

<?decl Nat.exists_prime_gt_modEq_one?>
:::

### Examples

**Example (Erdős's count for $k = 5$).** The primes below $5$ are $2$ and $3$, so $r = 2$ and $N = 64$. The integers up to $64$ whose prime factors are only $2$ and $3$ are $1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 32, 36, 48, 54, 64$, which is $17 \le 32 = N/2$. So more than half of the integers up to $64$ have a prime factor $\ge 5$, and these $47$ integers are counted by $\sum_{5 \le p \le 64}\lfloor 64/p\rfloor \ge 47$, which forces $\sum_{5 \le p \le 64}1/p \ge \frac{47}{64} > \frac12$.

**Example (Bertrand for $n = 10$ and $n = 100$).** The interval $(10, 20]$ contains $11, 13, 17, 19$. For $n = 100$, the central binomial coefficient $\binom{200}{100} \approx 9.05 \cdot 10^{58}$ has the prime factors $101, 103, \dots, 199$ with exponent $1$, and no prime factor in $(66, 100]$, as part (3) of the lemma predicts: for example $v_{67}\binom{200}{100} = \lfloor 200/67\rfloor - 2\lfloor 100/67\rfloor = 2 - 2 = 0$.

**Counterexample (Primes $\equiv 1 \bmod k$ do not settle other classes).** The argument with $\Phi_k$ gives primes $\equiv 1 \pmod k$ only. Euclid-style arguments with a polynomial are known for some other classes, such as $3 \bmod 4$ in Exercise 4, but not for a class such as $2 \bmod 5$. For that class the proof needs the L-series of Section 3.

### The library around it

`Mathlib.NumberTheory.SumPrimeReciprocals` also has the general transfer lemmas `Nat.Primes.summable_iff_summable_ite` and `Nat.Primes.tsum_eq_tsum_ite` between sums over the subtype `Nat.Primes` and sums over `ℕ`. The central binomial coefficient is `Nat.centralBinom n`, with the bound `Nat.four_pow_le_two_mul_self_mul_centralBinom`. Section 2 refines the primorial bound into the estimate $\theta(x) \le x\log 4$ of Chebyshev.

Common errors of a learner:

- `Nat.bertrand` requires `n ≠ 0`; for `n = 0` the interval `(0, 0]` is empty.
- `p ≡ 1 [MOD k]` is `Nat.ModEq k p 1`, a statement on `ℕ`. To pass to `ZMod k`, use `(ZMod.natCast_eq_natCast_iff _ _ _).symm`.

### Exercises

1. (A) Check the primorial bound for $n = 10$ and $n = 30$, and show that $n\# < 4^n$ for $n \ge 1$.
2. (A) Deduce from Bertrand's postulate that $p_{k+1} < 2p_k$ for the $k$-th prime $p_k$.
3. (A) Use Bertrand's postulate to show that $1 + \frac12 + \cdots + \frac1n$ is not an integer for $n \ge 2$.
4. (B) Prove directly that there are infinitely many primes $p \equiv 3 \pmod 4$ and infinitely many primes $p \equiv 5 \pmod 6$.
5. (B) Prove that there are infinitely many primes $p \equiv 1 \pmod 4$, from the fact that a prime factor of $n^2 + 1$ is $2$ or $\equiv 1 \pmod 4$.
6. (B) Show that $\sum_{p \le x}1/p \ge \log\log x - 1$ for $x \ge 3$, from $\prod_{p \le x}(1 - 1/p)^{-1} \ge \sum_{n \le x}1/n \ge \log x$.
7. (C) Show that for $n \ge 2$ the number $n!$ is never a perfect power $m^k$ with $k \ge 2$. Hint: Bertrand's postulate gives a prime $p$ with $n/2 < p \le n$.

### Notes and history

Euler proved the divergence of $\sum 1/p$ in 1737 with the product formula for $\zeta$. The short counting proof is due to Erdős, from 1938. Bertrand conjectured the postulate in 1845 and checked it up to $3 \cdot 10^6$; Chebyshev proved it in 1852. The proof of this section, through the central binomial coefficient, is the one of Erdős from 1932, with Ramanujan's earlier proof as a model. A reference is Aigner and Ziegler, *Proofs from THE BOOK*, Chapters 1 and 2.

### Reference

<?reference?>
