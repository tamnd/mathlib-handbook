---
title: Möbius inversion
kind: theory
modules:
  - Mathlib.NumberTheory.ArithmeticFunction.Moebius
  - Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
  - Mathlib.NumberTheory.ArithmeticFunction.Liouville
  - Mathlib.NumberTheory.ArithmeticFunction.Carmichael
explains:
  E3: [ArithmeticFunction.moebius, ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq, ArithmeticFunction.vonMangoldt, ArithmeticFunction.liouville, ArithmeticFunction.carmichael]
  E2: [ArithmeticFunction.moebius_apply_prime_pow, ArithmeticFunction.moebius_apply_of_squarefree, ArithmeticFunction.moebius_ne_zero_iff_squarefree, ArithmeticFunction.isMultiplicative_moebius, ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.coe_zeta_mul_moebius, ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq, ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub, ArithmeticFunction.vonMangoldt_apply, ArithmeticFunction.vonMangoldt_sum, ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.moebius_mul_log_eq_vonMangoldt, ArithmeticFunction.liouville_apply, ArithmeticFunction.isMultiplicative_liouville, ArithmeticFunction.carmichael_eq_exponent, ArithmeticFunction.pow_carmichael, ArithmeticFunction.carmichael_dvd_totient, ArithmeticFunction.carmichael_mul, ArithmeticFunction.carmichael_two_pow_of_ne_two, ArithmeticFunction.carmichael_pow_of_prime_ne_two]
  E1: auto
families: []
requires: [V12.C01, V02.C06, V03.C06, V05.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Möbius inversion

### Overview

Section 1 showed that the arithmetic functions form a ring under Dirichlet convolution and that $\zeta$ is a unit of it, since $\zeta(1) = 1$. This section finds the inverse: it is the Möbius function $\mu$. The equation $\mu * \zeta = \varepsilon$ gives the Möbius inversion formula: if $g(n) = \sum_{d \mid n} f(d)$ for all $n$, then $f(n) = \sum_{d \mid n} \mu(d)\, g(n/d)$. The section applies it to Euler's function, to the von Mangoldt function $\Lambda$, which Chapter 7 uses to count primes, and to the Liouville function. It ends with the Carmichael function $\lambda(n)$, the exponent of the group $(\mathbb{Z}/n)^\times$, which sharpens Euler's theorem $a^{\varphi(n)} \equiv 1 \pmod n$.

### Definitions

**Definition (The Möbius function).** For $n \geq 1$, put $\mu(n) = (-1)^r$ if $n$ is a product of $r$ distinct primes, and $\mu(n) = 0$ if $p^2 \mid n$ for some prime $p$.

So $\mu(1) = 1$, $\mu(p) = -1$, $\mu(p^e) = 0$ for $e \geq 2$, and $\mu$ is multiplicative: for coprime $m$ and $n$, $mn$ is squarefree exactly when $m$ and $n$ are, and then the prime factors of $mn$ are those of $m$ together with those of $n$.

::: mathlib
`ArithmeticFunction.moebius` · `Mathlib.NumberTheory.ArithmeticFunction.Moebius`

`μ : ArithmeticFunction ℤ`, with notation `μ` after `open scoped ArithmeticFunction.Moebius`. It is defined as `if Squarefree n then (-1) ^ cardFactors n else 0`. The basic facts are `moebius_apply_prime_pow`, `moebius_apply_of_squarefree`, `moebius_ne_zero_iff_squarefree` and `isMultiplicative_moebius`. In another ring it is used through the cast `(μ : ArithmeticFunction R)`.

<?decl ArithmeticFunction.moebius?>
:::

**Definition (von Mangoldt and logarithm).** The von Mangoldt function is $\Lambda(n) = \log p$ if $n = p^k$ is a power of a prime $p$ with $k \geq 1$, and $\Lambda(n) = 0$ otherwise. The function $\log$ is $n \mapsto \log n$.

::: mathlib
`ArithmeticFunction.vonMangoldt` · `Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt`

`Λ : ArithmeticFunction ℝ`, with `vonMangoldt_apply : Λ n = if IsPrimePow n then Real.log n.minFac else 0`. The prime of a prime power is its smallest prime factor `n.minFac`. The function $\log$ is `ArithmeticFunction.log`, also with values in `ℝ`.

<?decl ArithmeticFunction.vonMangoldt?>
:::

**Definition (Liouville function).** $\lambda(n) = (-1)^{\Omega(n)}$, where $\Omega(n)$ counts the prime factors with multiplicity. It is completely multiplicative, because $\Omega$ is additive.

::: mathlib
`ArithmeticFunction.liouville` · `Mathlib.NumberTheory.ArithmeticFunction.Liouville`

`ArithmeticFunction ℤ`, with `liouville_apply : n ≠ 0 → liouville n = (-1) ^ cardFactors n`. Complete multiplicativity is `liouville_apply_mul`, and `isMultiplicative_liouville` gives the predicate of Section 1.

<?decl ArithmeticFunction.liouville?>
:::

**Definition (Carmichael function).** For $n \geq 1$, $\lambda_C(n)$ is the exponent of the group $(\mathbb{Z}/n)^\times$: the smallest $m \geq 1$ with $a^m \equiv 1 \pmod n$ for all $a$ prime to $n$.

The subscript separates it from the Liouville function; both have the letter $\lambda$ in the literature.

::: mathlib
`ArithmeticFunction.carmichael` · `Mathlib.NumberTheory.ArithmeticFunction.Carmichael`

`ArithmeticFunction ℕ`, with `carmichael_eq_exponent : n ≠ 0 → carmichael n = Monoid.exponent (ZMod n)ˣ`. The scoped notation `λ` opens with `open scoped ArithmeticFunction.carmichael`.

<?decl ArithmeticFunction.carmichael?>
:::

### Theorems and proofs

**Theorem ($\mu$ inverts $\zeta$).** $\mu * \zeta = \varepsilon$, that is, $\sum_{d \mid n} \mu(d) = 0$ for $n > 1$.

*Proof.* The function $\mu * \zeta$ is multiplicative by Section 1, so it is enough to check prime powers. For $e \geq 1$, $\sum_{j=0}^{e} \mu(p^j) = \mu(1) + \mu(p) = 1 - 1 = 0$, and $(\mu * \zeta)(1) = 1$. So $\mu * \zeta$ agrees with $\varepsilon$ on prime powers, and both are multiplicative. $\square$

A direct proof: if $n$ has $r \geq 1$ distinct prime factors, the squarefree divisors of $n$ with $k$ prime factors are $\binom{r}{k}$ in number, so the sum is $\sum_{k=0}^{r} (-1)^k \binom{r}{k} = (1 - 1)^r = 0$.

::: mathlib
`ArithmeticFunction.moebius_mul_coe_zeta` · `Mathlib.NumberTheory.ArithmeticFunction.Moebius`

`μ * ↑ζ = 1` in `ArithmeticFunction ℤ`, and `coe_zeta_mul_moebius` is the other order. The unit `ArithmeticFunction.zetaUnit` packages $\zeta$ with its inverse.

<?decl ArithmeticFunction.moebius_mul_coe_zeta?>
:::

**Theorem (Möbius inversion).** Let $f, g$ be functions on the positive integers with values in an abelian group. Then
$$g(n) = \sum_{d \mid n} f(d) \text{ for all } n \geq 1 \iff f(n) = \sum_{d \mid n} \mu(d)\, g(n/d) \text{ for all } n \geq 1.$$

*Proof.* For values in a commutative ring, the left side says $g = \zeta * f$ and the right side says $f = \mu * g$. If $g = \zeta * f$, then $\mu * g = (\mu * \zeta) * f = f$. If $f = \mu * g$, then $\zeta * f = (\zeta * \mu) * g = g$. For an abelian group $A$, the same computation works with $\mathbb{Z}$ acting on $A$: the sums are finite, and the associativity of the proof in Section 1 uses only the sum over the triples $abc = n$. $\square$

::: mathlib
`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` · `Mathlib.NumberTheory.ArithmeticFunction.Moebius`

The theorem for `f g : ℕ → R` in a ring, with both sides for `n > 0`, and the right side as `∑ x ∈ n.divisorsAntidiagonal, μ x.1 * g x.2 = f n`. The functions are plain functions, not `ArithmeticFunction R`, so the value at `0` plays no role. The version for an additive group is `sum_eq_iff_sum_smul_moebius_eq`, and the multiplicative version `prod_eq_iff_prod_pow_moebius_eq` has products and powers $g(n/d)^{\mu(d)}$.

<?decl ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq?>
:::

**Theorem (Euler's function).** $\varphi = \mu * \mathrm{id}$, that is, $\varphi(n) = \sum_{d \mid n} \mu(d)\, n/d$. Consequently
$$\varphi(n) = n \prod_{p \mid n} \left(1 - \frac1p\right).$$

*Proof.* First, $\sum_{d \mid n} \varphi(d) = n$. For $1 \leq k \leq n$, put $d = n / \gcd(k, n)$. The $k$ with $n/\gcd(k, n) = d$ are $k = (n/d) j$ with $1 \leq j \leq d$ and $\gcd(j, d) = 1$, so there are $\varphi(d)$ of them. Summing over $d \mid n$ counts each $k$ once. Möbius inversion with $f = \varphi$ and $g = \mathrm{id}$ gives $\varphi = \mu * \mathrm{id}$. So $\varphi$ is multiplicative, and $\varphi(p^e) = p^e - p^{e-1} = p^e(1 - 1/p)$. $\square$

In Mathlib the identity $\sum_{d \mid n} \varphi(d) = n$ is `Nat.sum_totient` in `Mathlib.Data.Nat.Totient`. The index of this edition has no declaration for $\varphi = \mu * \mathrm{id}$ in the form of an equation of arithmetic functions; the inversion theorem above derives it in one step. The product formula is a case of `IsMultiplicative.prodPrimeFactors_one_sub`: $\prod_{p \mid n} (1 - f(p)) = \sum_{d \mid n} \mu(d) f(d)$ for multiplicative $f$.

**Theorem (von Mangoldt).** $\sum_{d \mid n} \Lambda(d) = \log n$, that is, $\Lambda * \zeta = \log$. Consequently $\Lambda = \mu * \log$, and $\Lambda(n) = -\sum_{d \mid n} \mu(d) \log d$.

*Proof.* Let $n = p_1^{e_1} \cdots p_r^{e_r}$. The divisors $d$ with $\Lambda(d) \neq 0$ are the prime powers $p_i^j$ with $1 \leq j \leq e_i$. So the sum is $\sum_i e_i \log p_i = \log n$. Möbius inversion gives $\Lambda = \mu * \log$. For the last form, $\sum_{d \mid n} \mu(d) \log(n/d) = \log n \sum_{d \mid n} \mu(d) - \sum_{d \mid n} \mu(d) \log d$, and the first sum is $0$ for $n > 1$; for $n = 1$ both sides are $0$. $\square$

::: mathlib
`ArithmeticFunction.vonMangoldt_sum` · `Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt`

`∑ i ∈ n.divisors, Λ i = Real.log n`. In the ring of arithmetic functions it is `vonMangoldt_mul_zeta : Λ * ↑ζ = log`, and the inverted form is `moebius_mul_log_eq_vonMangoldt : ↑μ * log = Λ`. The value at `0` is consistent: `Real.log 0 = 0` in Mathlib.

<?decl ArithmeticFunction.vonMangoldt_sum?>
:::

**Theorem (Liouville).** $\sum_{d \mid n} \lambda(d)$ is $1$ if $n$ is a square and $0$ otherwise.

*Proof.* The sum is $(\lambda * \zeta)(n)$, a multiplicative function. On $p^e$ it is $\sum_{j=0}^{e} (-1)^j$, which is $1$ for even $e$ and $0$ for odd $e$. The function that is $1$ on squares and $0$ elsewhere is multiplicative and has the same values on prime powers. $\square$

**Theorem (Carmichael function).** For $n \geq 1$ and $a$ prime to $n$, $a^{\lambda_C(n)} \equiv 1 \pmod n$, and $\lambda_C(n) \mid \varphi(n)$. For coprime $m$ and $n$, $\lambda_C(mn) = \operatorname{lcm}(\lambda_C(m), \lambda_C(n))$. For $k \geq 3$, $\lambda_C(2^k) = 2^{k-2}$, while $\lambda_C(2) = 1$ and $\lambda_C(4) = 2$. For an odd prime $p$, $\lambda_C(p^k) = \varphi(p^k)$.

*Proof.* The first claim is the definition of the exponent. The exponent of a finite group divides its order (Volume 5, Chapter 4), and the order of $(\mathbb{Z}/n)^\times$ is $\varphi(n)$. For coprime $m, n$, the Chinese remainder theorem gives $(\mathbb{Z}/mn)^\times \cong (\mathbb{Z}/m)^\times \times (\mathbb{Z}/n)^\times$, and $a^e = 1$ on a product exactly when $e$ is a multiple of both exponents.

For $2^k$ with $k \geq 3$, use the form for $p = 2$ of the lifting the exponent lemma (Chapter 1, Section 1). For odd $a \neq 1$ and even $N$, $v_2(a^N - 1) = v_2(a - 1) + v_2(a + 1) + v_2(N) - 1$. One of $a - 1$ and $a + 1$ is divisible by $4$, so for $N = 2^{k-2}$, $v_2(a^N - 1) \geq 1 + 2 + (k - 2) - 1 = k$. So $\lambda_C(2^k) \mid 2^{k-2}$. For $a = 5$ and $N = 2^{k-3}$ with $k \geq 4$: $v_2(5^N - 1) = 2 + 1 + (k-3) - 1 = k - 1 < k$. So $5^{2^{k-3}} \not\equiv 1 \pmod{2^k}$, and $\lambda_C(2^k) = 2^{k-2}$. For $k = 3$, $3^1 \not\equiv 1 \pmod 8$, so $\lambda_C(8) = 2$.

For odd $p$ the group $(\mathbb{Z}/p^k)^\times$ is cyclic, so its exponent is its order. This section does not prove the cyclicity; for $k = 1$ it is the theorem on primitive roots of Volume 6, Chapter 5. $\square$

::: mathlib
`ArithmeticFunction.pow_carmichael` · `Mathlib.NumberTheory.ArithmeticFunction.Carmichael`

`a ^ carmichael n = 1` for `a : (ZMod n)ˣ`. The other facts are `carmichael_dvd_totient`, `carmichael_mul` (with `Nat.lcm`), `carmichael_two_pow_of_ne_two : n ≠ 2 → carmichael (2 ^ n) = 2 ^ (n - 2)`, and `carmichael_pow_of_prime_ne_two`. In the statement for $2^n$, the case $n = 0$ is $\lambda_C(1) = 1 = 2^{0 - 2}$, because the subtraction `0 - 2` is `0` in `ℕ`, and $n = 1$ gives $2^0 = 1$ in the same way.

<?decl ArithmeticFunction.pow_carmichael?>
:::

### Examples

**Example (Inversion of $\varphi$).** For $n = 12$, $\varphi(12) = 12 - 6 - 4 + 2 = 4$, from $\mu(1) = 1$, $\mu(2) = \mu(3) = -1$, $\mu(6) = 1$ and $\mu(4) = \mu(12) = 0$. The product formula gives $12 \cdot \tfrac12 \cdot \tfrac23 = 4$, and the units are $1, 5, 7, 11$.

**Example (Von Mangoldt at $12$).** The divisors of $12$ that are prime powers are $2, 3, 4$, so $\sum_{d \mid 12} \Lambda(d) = \log 2 + \log 3 + \log 2 = \log 12$.

**Example (Carmichael's function and Korselt).** $\lambda_C(561) = \operatorname{lcm}(2, 10, 16) = 80$, while $\varphi(561) = 320$. So $a^{80} \equiv 1 \pmod{561}$ for every $a$ prime to $561$, and $80 \mid 560$; this is another form of Korselt's criterion of Chapter 1, Section 2: a squarefree composite $n$ is a Carmichael number exactly when $\lambda_C(n) \mid n - 1$.

**Counterexample (The group $(\mathbb{Z}/8)^\times$ is not cyclic).** $\varphi(8) = 4$, but $1^2 \equiv 3^2 \equiv 5^2 \equiv 7^2 \equiv 1 \pmod 8$, so $\lambda_C(8) = 2 < \varphi(8)$. The formula $\lambda_C(p^k) = \varphi(p^k)$ needs $p$ odd.

### The library around it

The file `Moebius.lean` has the three inversion theorems for sums, for additive groups and for products, and also versions with the suffix `_on` for a set of indices closed under divisors, such as `sum_eq_iff_sum_mul_moebius_eq_on`. `VonMangoldt.lean` has `vonMangoldt_apply_prime`, `vonMangoldt_apply_pow`, `vonMangoldt_nonneg` and `vonMangoldt_le_log`, which Chapter 7 uses for the Chebyshev functions. 

Common errors of a learner:

- `μ` has values in `ℤ`, `Λ` in `ℝ`, `ζ` in `ℕ`. An equation that mixes them needs casts, and the theorems have them already in place: `↑μ * log = Λ`.
- The sum in `sum_eq_iff_sum_mul_moebius_eq` is over `n.divisorsAntidiagonal`, so the term is `μ x.1 * g x.2` and not `μ d * g (n / d)` with `d ∈ n.divisors`. The theorem `Nat.sum_divisorsAntidiagonal` passes between the two forms.
- The name `carmichael` is the function $\lambda_C$; the predicate of Carmichael numbers is `Nat.IsCarmichael`.

### Exercises

1. (A) Compute $\mu(n)$ for $n = 1, \dots, 12$ and check $\sum_{d \mid 12} \mu(d) = 0$.
2. (A) Compute $\lambda_C(n)$ and $\varphi(n)$ for $n = 15, 16, 24, 1105$.
3. (A) Show that $\sum_{d \mid n} \mu(d)^2 = 2^{\omega(n)}$.
4. (B) Show that $\sum_{d \mid n} \mu(d)\,\tau(n/d) = 1$ and $\sum_{d \mid n} \mu(d)\,\sigma(n/d) = n$.
5. (B) The number of monic irreducible polynomials of degree $n$ over $\mathbb{F}_q$ is $N_n$, and $\sum_{d \mid n} d N_d = q^n$. Find $N_n$, and compute $N_4$ for $q = 2$. Hint: the answer is $3$.
6. (B) Show that the number of $k \leq x$ that are squarefree is $\sum_{d \leq \sqrt x} \mu(d) \lfloor x/d^2 \rfloor$. Hint: $\sum_{d^2 \mid k} \mu(d)$ is $1$ for squarefree $k$ and $0$ otherwise.
7. (C) Show that $\lambda_C(n) \mid n - 1$ for a composite squarefree $n$ if and only if $n$ is a Carmichael number, and find $\lambda_C(1729)$.
8. (C) Prove the Selberg identity $\sum_{d \mid n} \mu(d) \log^2(n/d) = \Lambda(n)\log n + (\Lambda * \Lambda)(n)$. Hint: differentiate $\log = \Lambda * \zeta$ with the derivation $f \mapsto f \log$.

### Notes and history

Möbius introduced the function $\mu$ and the inversion formula in 1832. Von Mangoldt introduced $\Lambda$ in his work on the explicit formula of Riemann in 1895. Carmichael introduced $\lambda_C$ in 1910, in the same work where he gave the Carmichael numbers. Selberg used the identity of Exercise 8 in his elementary proof of the prime number theorem of 1949. A standard reference is Apostol, *Introduction to Analytic Number Theory*, Chapter 2.

### Reference

<?reference?>
