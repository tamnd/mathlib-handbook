---
title: The factorization of a natural number
kind: api
modules:
  - Mathlib.Data.Nat.Factorization.Defs
  - Mathlib.Data.Nat.Factorization.Basic
  - Mathlib.Data.Nat.Factorization.Divisors
  - Mathlib.Data.Nat.Factorization.Induction
  - Mathlib.Data.Nat.Factorization.LCM
  - Mathlib.Data.Nat.Factorization.PrimePow
  - Mathlib.Data.Nat.Factorization.Root
  - Mathlib.Data.Nat.Multiplicity
  - Mathlib.Data.Nat.PadicValNat
  - Mathlib.Data.Nat.MaxPowDiv
explains:
  E2: [Nat.factorization_mul, Nat.factorization_le_iff_dvd, Nat.factorization_gcd, Nat.ordProj_mul_ordCompl_eq_self, Nat.multiplicative_factorization, Nat.Prime.emultiplicity_factorial, Nat.pow_dvd_iff_dvd_floorRoot]
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

## The factorization of a natural number

### Overview

The fundamental theorem of arithmetic of the previous section says that each $n \geq 1$ is a product $\prod_p p^{v_p(n)}$ over the primes, with unique exponents. The previous section states it with the list `Nat.primeFactorsList`. For most proofs a function is more useful than a list: the function $p \mapsto v_p(n)$. Mathlib calls it `Nat.factorization`, and it is a finitely supported function `ℕ →₀ ℕ`. With it, multiplication of numbers becomes addition of functions, divisibility becomes the pointwise order, and the gcd and the lcm become the pointwise minimum and maximum.

The modules of this section develop this dictionary. They also give the $p$-adic valuation `padicValNat`, an algorithm `Nat.maxPowDvdDiv` that computes it, Legendre's formula for the valuation of $n!$, and the induction principles on prime powers and coprime products. The section uses the primes and the fundamental theorem of the previous section, and the factorial of Chapter 1.

### The library around it

#### The function `Nat.factorization`

The module `Mathlib.Data.Nat.Factorization.Defs` defines `n.factorization` as the count function of the multiset of prime factors, so `n.factorization p` is the number of times that $p$ occurs in `n.primeFactorsList` (`Nat.primeFactorsList_count_eq`). Its support is the finite set `n.primeFactors`, by `Nat.support_factorization`. The junk values are simple: `Nat.factorization_zero` and `Nat.factorization_one` say that $0$ and $1$ have the zero function, and `Nat.factorization_eq_zero_of_not_prime` says that the value at a number that is not prime is $0$. The simp normal form of the exponent of $p$ in $n$ is `n.factorization p`, not the count in the list.

The value at a prime is the multiplicity: `Nat.factorization_def` says `n.factorization p = multiplicity p n` for a prime $p$, where `multiplicity p n` is the largest $k$ with $p^k \mid n$. The main results translate arithmetic into operations on functions:

| Lean name | Statement |
|---|---|
| `Nat.factorization_mul` | $v(a b) = v(a) + v(b)$ for $a, b \ne 0$ |
| `Nat.factorization_pow` | $v(n^k) = k \cdot v(n)$ |
| `Nat.Prime.factorization` | $v(p)$ is the function with value $1$ at $p$ and $0$ elsewhere |
| `Nat.factorization_le_iff_dvd` | $v(d) \leq v(n) \iff d \mid n$ for $d, n \ne 0$ |
| `Nat.factorization_div` | $v(n / d) = v(n) - v(d)$ for $d \mid n$ |
| `Nat.factorization_gcd` | $v(\gcd(a, b)) = v(a) \sqcap v(b)$ for $a, b \ne 0$ |
| `Nat.factorization_lcm` | $v(\mathrm{lcm}(a, b)) = v(a) \sqcup v(b)$ for $a, b \ne 0$ |
| `Nat.factorization_prod_pow_eq_self` | a function supported on primes is the factorization of $\prod_p p^{f(p)}$ |
| `Nat.prod_factorization_pow_eq_self` | $\prod_p p^{v_p(n)} = n$ for $n \ne 0$ |

**Proof sketch of `Nat.factorization_mul`.** The prime factors of $a b$, as a multiset, are the sum of the prime factors of $a$ and of $b$: the product of the two lists is $a b$ and all its elements are prime, so by uniqueness it is the list of $a b$ up to order. The count function of a sum of multisets is the sum of the count functions. $\square$

**Proof sketch of `Nat.factorization_le_iff_dvd`.** If $d \mid n$, write $n = d e$ with $e \ne 0$. Then $v(n) = v(d) + v(e) \geq v(d)$. Conversely, if $v(d) \leq v(n)$, let $e = \prod_p p^{v_p(n) - v_p(d)}$. Then $v(d e) = v(d) + (v(n) - v(d)) = v(n)$, and the factorization is injective on nonzero numbers (`Nat.factorization_inj`), so $d e = n$. $\square$

The gcd formula follows from the order statement. The number $g = \prod_p p^{\min(v_p(a), v_p(b))}$ divides $a$ and $b$ by `Nat.factorization_le_iff_dvd`, and each common divisor $d$ has $v(d) \leq v(a) \sqcap v(b) = v(g)$, so $d \mid g$. The equivalence `Nat.factorizationEquiv` makes the dictionary complete: it identifies `ℕ+` with the finitely supported functions whose support consists of primes.

#### The parts at one prime

For a prime $p$, the number $n$ splits as the $p$-part $p^{v_p(n)}$ times the part prime to $p$. The module `Mathlib.Data.Nat.Factorization.Defs` gives the notations `ordProj[p] n` for $p^{v_p(n)}$ and `ordCompl[p] n` for $n / p^{v_p(n)}$. The module `Mathlib.Data.Nat.Factorization.Basic` has their API, and the names of its lemmas contain the words *ordProj* and *ordCompl*. The lemma `Nat.ordProj_mul_ordCompl_eq_self` says that the product of the two parts is $n$. Its proof is one line: the $p$-part divides $n$ by `Nat.ordProj_dvd`, and $a \cdot (n / a) = n$ for each divisor $a$ of $n$. Other lemmas are `Nat.coprime_ordCompl` and `Nat.not_dvd_ordCompl`, which say that $p$ does not divide the second part, and `Nat.ordProj_mul` and `Nat.ordCompl_mul`, which say that each part is multiplicative.

The same module connects the factorization with divisibility by prime powers. The lemma `Nat.Prime.pow_dvd_iff_le_factorization` says $p^k \mid n \iff k \leq v_p(n)$ for $n \ne 0$, and `Nat.factorization_eq_card_pow_dvd` counts $v_p(n)$ as the number of $i \geq 1$ with $p^i \mid n$. The lemma `Nat.exists_eq_two_pow_mul_odd` writes each $n \ne 0$ as $2^k m$ with $m$ odd. The lemma `Nat.exists_eq_pow_of_pow_eq_pow` solves $a^m = b^n$: then $a$ and $b$ are powers of one number $c$.

The module `Mathlib.Data.Nat.Factorization.Divisors` describes the divisors of $n \ne 0$ as the images of the functions below $v(n)$: `Nat.divisors_eq_image_Iic_factorization_prod_pow` says that `n.divisors` is the image of the interval $[0, v(n)]$ of finitely supported functions under $f \mapsto \prod_p p^{f(p)}$. The proper divisors come from the functions strictly below $v(n)$.

#### Prime powers, lcm splitting and roots

The module `Mathlib.Data.Nat.Factorization.PrimePow` characterizes the prime powers `IsPrimePow n`. Here $n$ is a prime power if and only if it has exactly one prime factor (`isPrimePow_iff_card_primeFactors_eq_one`), if and only if its factorization is a single point (`isPrimePow_iff_factorization_eq_single`), if and only if exactly one prime divides it (`isPrimePow_iff_unique_prime_dvd`). The equivalence `Nat.Primes.prodNatEquiv` identifies the pairs $(p, k)$ with the prime powers $p^{k + 1}$.

The module `Mathlib.Data.Nat.Factorization.LCM` splits the lcm into coprime parts. The number `Nat.factorizationLCMLeft a b` collects the prime powers $p^{v_p(a)}$ with $v_p(b) \leq v_p(a)$, and `Nat.factorizationLCMRight a b` collects $p^{v_p(b)}$ with $v_p(a) < v_p(b)$. They divide $a$ and $b$, they are coprime (`Nat.coprime_factorizationLCMLeft_factorizationLCMRight`), and their product is $\mathrm{lcm}(a, b)$ (`Nat.factorizationLCMLeft_mul_factorizationLCMRight`). So a statement about $\mathrm{lcm}(a, b)$ reduces to a statement about two coprime factors.

The module `Mathlib.Data.Nat.Factorization.Root` defines roots for divisibility. The number `Nat.floorRoot n a` has the exponents $\lfloor v_p(a) / n \rfloor$, and `Nat.ceilRoot n a` has the exponents $\lceil v_p(a) / n \rceil$. They are not the real $n$-th root rounded: the floor root of $2^3 \cdot 3^2 \cdot 5$ for $n = 2$ is $2 \cdot 3$. They are the adjoints of $x \mapsto x^n$ for the order of divisibility:
$$a^n \mid b \iff a \mid \mathrm{floorRoot}_n(b), \qquad a \mid b^n \iff \mathrm{ceilRoot}_n(a) \mid b \quad (n \ne 0).$$
These are `Nat.pow_dvd_iff_dvd_floorRoot` and `Nat.dvd_pow_iff_ceilRoot_dvd`. For the first, compare exponents: $n \, v_p(a) \leq v_p(b) \iff v_p(a) \leq \lfloor v_p(b)/n \rfloor$ for each prime $p$.

#### Induction on the factorization

The module `Mathlib.Data.Nat.Factorization.Induction` gives induction principles. The principle `induction_on_primes` proves a property for each $n$ from the cases $0$ and $1$ and the step $a \mapsto p a$ for a prime $p$. The recursors `Nat.recOnPrimePow` (step $a \mapsto p^k a$ with $p \nmid a$), `Nat.recOnPrimeCoprime` and `Nat.recOnPosPrimePosCoprime` (prime powers and coprime products) and `Nat.recOnMul` (primes and arbitrary products) give other forms. The main application is `Nat.multiplicative_factorization`: if $f(x y) = f(x) f(y)$ for coprime $x, y$ and $f(1) = 1$, then
$$f(n) = \prod_p f(p^{v_p(n)}) \qquad (n \ne 0).$$
*Proof sketch.* Induction with `Nat.recOnPosPrimePosCoprime`: a prime power is its own product, and for coprime $a, b$ the factorization of $a b$ is the sum of two functions with disjoint supports, so the product splits as $f(a) f(b)$. $\square$

#### Valuations and Legendre's formula

The module `Mathlib.Data.Nat.MaxPowDiv` computes the valuation. The function `Nat.maxPowDvdDiv p n` returns the pair $(k, m)$ with $n = p^k m$ and $p \nmid m$, by repeated division, for $p > 1$ and $n \ne 0$; else it returns $(0, n)$. The second part is `Nat.divMaxPow`. The module `Mathlib.Data.Nat.PadicValNat` defines `padicValNat p n` as the first part, and `Nat.padicValNat_def` proves that it is `multiplicity p n`. So `padicValNat` is a computable form of the multiplicity, and `decide` or `rfl` can evaluate it. The lemmas `Nat.pow_dvd_iff_le_multiplicity` and `Nat.pow_multiplicity_mul_divMaxPow` state the defining properties.

The module `Mathlib.Data.Nat.Multiplicity` uses the multiplicity with values in `ℕ∞`, `emultiplicity`, which is $\top$ for $n = 0$. Its main result is Legendre's formula, `Nat.Prime.emultiplicity_factorial`: for a prime $p$ and $b > \log_p n$,
$$v_p(n!) = \sum_{i = 1}^{b - 1} \left\lfloor \frac{n}{p^i} \right\rfloor.$$
*Proof sketch.* The number $v_p(n!)$ is $\sum_{m = 1}^{n} v_p(m)$, and $v_p(m)$ is the number of $i \geq 1$ with $p^i \mid m$. Swap the two sums: for fixed $i$, the number of $m \leq n$ with $p^i \mid m$ is $\lfloor n / p^i \rfloor$. The terms with $p^i > n$ are $0$. $\square$

The module also has the form with digits, `Nat.Prime.sub_one_mul_multiplicity_factorial`, which says $(p - 1) v_p(n!) = n - s_p(n)$ for the sum $s_p(n)$ of the digits of $n$ in base $p$. Kummer's theorem `Nat.Prime.emultiplicity_choose` says that $v_p\binom{n}{k}$ is the number of carries when $k$ and $n - k$ are added in base $p$, and `Nat.Prime.dvd_choose_pow_iff` says that $p \mid \binom{p^n}{k}$ if and only if $k \ne 0$ and $k \ne p^n$.

#### Common errors

1. Most results need nonzero arguments. The factorization of $0$ is the zero function, so `Nat.factorization_mul` fails for $a = 0$, and `Nat.factorization_le_iff_dvd` fails for $n = 0$ because each $d$ divides $0$.
2. The value `n.factorization p` at a number $p$ that is not prime is $0$, not the multiplicity of $p$. For a composite $p$, use `multiplicity p n` or `padicValNat p n`.
3. The two multiplicities differ at $0$: `emultiplicity p 0` is $\top$ in `ℕ∞`, and `multiplicity p 0` is the junk value $0$ in `ℕ`. The lemmas of `Mathlib.Data.Nat.Multiplicity` use the first.

### Exercises

1. (A) Compute `Nat.factorization 360` as a function, and check the result with `Nat.prod_factorization_pow_eq_self`.
2. (A) Use `Nat.factorization_gcd` and `Nat.factorization_lcm` to prove $\gcd(a, b) \cdot \mathrm{lcm}(a, b) = a b$ for $a, b \ne 0$.
3. (B) Prove that $n$ is a perfect square if and only if each $v_p(n)$ is even, and compare with `Nat.isSquare_iff_even_factorization`.
4. (B) Use Legendre's formula to compute $v_2(100!)$ and $v_5(100!)$, and deduce the number of zeros at the end of $100!$.
5. (B) Prove that the divisor count $d(n)$ is multiplicative, and deduce $d(n) = \prod_p (v_p(n) + 1)$ with `Nat.multiplicative_factorization`.
6. (C) Prove Kummer's theorem for $n = p^m$: $v_p\binom{p^m}{k} = m - v_p(k)$ for $1 \leq k \leq p^m$, and compare with `Nat.Prime.emultiplicity_choose_prime_pow`.

### Reference

<?reference?>
