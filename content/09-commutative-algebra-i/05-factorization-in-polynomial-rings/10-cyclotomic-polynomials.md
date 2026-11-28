---
title: Cyclotomic polynomials
kind: api
modules:
  - Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
  - Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
  - Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
  - Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
  - Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
explains:
  E2: [Polynomial.cyclotomic, Polynomial.prod_cyclotomic_eq_X_pow_sub_one, Polynomial.map_cyclotomic_int, Polynomial.natDegree_cyclotomic, Polynomial.isRoot_cyclotomic_iff, Polynomial.cyclotomic_eq_minpoly, Polynomial.cyclotomic_expand_eq_cyclotomic_mul, Polynomial.cyclotomic_mul_prime_pow_eq]
  E1: auto
families: []
requires: [V06.C04, V06.C05, V06.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cyclotomic polynomials

### Overview

The $n$-th cyclotomic polynomial $\Phi_n$ is the monic polynomial whose roots in $\mathbb{C}$ are the primitive $n$-th roots of unity, each with multiplicity one:
$$\Phi_n = \prod_{\zeta \text{ primitive of order } n} (X - \zeta).$$
Its coefficients are integers, its degree is $\varphi(n)$, and the product of the $\Phi_d$ over the divisors $d$ of $n$ is $X^n - 1$. For example, $\Phi_1 = X - 1$, $\Phi_2 = X + 1$, $\Phi_3 = X^2 + X + 1$ and $\Phi_6 = X^2 - X + 1$. The polynomial $\Phi_n$ is irreducible over $\mathbb{Q}$, so it is the minimal polynomial of $e^{2 \pi i / n}$, and the field $\mathbb{Q}(e^{2 \pi i / n})$ has degree $\varphi(n)$ over $\mathbb{Q}$.

The library defines $\Phi_n$ over $\mathbb{Z}$ and maps it to every ring, so that $\Phi_n$ exists over $\mathbb{Z}/p$ and over any other ring. This section is a guide to the five modules on cyclotomic polynomials: the definition and the product formula, the values at real points, the behavior under $X \mapsto X^p$ and in characteristic $p$, the factorization over finite fields, and the roots and irreducibility over $\mathbb{Q}$. Section 2 used $\Phi_p$ as an example for the criterion of Eisenstein. A proof about $\Phi_n$ over a ring $R$ often starts over $\mathbb{Z}$ or $\mathbb{Q}$, where the polynomial is irreducible and its roots are known, and then moves the result to $R$ with `Polynomial.map_cyclotomic`.

### The library around it

**Two definitions.** The module `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic` first defines `Polynomial.cyclotomic' n R` for a domain $R$. It is the product of $X - \mu$ over the primitive $n$-th roots of unity $\mu$ in $R$. This polynomial is correct only when $R$ has enough roots of unity. If $\zeta$ is a primitive $n$-th root of unity in $R$, then `Polynomial.prod_cyclotomic'_eq_X_pow_sub_one` gives the product formula. The main definition is `Polynomial.cyclotomic n R`, for any ring $R$. It is the polynomial over $\mathbb{Z}$ whose image in $\mathbb{C}[X]$ is `Polynomial.cyclotomic' n ℂ`, mapped to $R$. The specification over $\mathbb{Z}$ is `Polynomial.int_cyclotomic_spec`, and its uniqueness is `Polynomial.int_cyclotomic_unique`. The definition commutes with ring homomorphisms:
$$\operatorname{map} f\, (\Phi_n \text{ over } R) = \Phi_n \text{ over } S,$$
which is `Polynomial.map_cyclotomic` for $f : R \to S$, and `Polynomial.map_cyclotomic_int` for the map from $\mathbb{Z}$.

**Basic properties.** The polynomial is monic, `Polynomial.cyclotomic.monic`, primitive, `Polynomial.cyclotomic.isPrimitive`, and nonzero over a nontrivial ring, `Polynomial.cyclotomic_ne_zero`. Its degree is the totient, `Polynomial.natDegree_cyclotomic` and `Polynomial.degree_cyclotomic`. The small cases are `Polynomial.cyclotomic_zero`, `Polynomial.cyclotomic_one`, `Polynomial.cyclotomic_two`, `Polynomial.cyclotomic_three` and `Polynomial.cyclotomic_six`. For a prime power the formula is a geometric sum,
$$\Phi_{p^{k+1}} = \sum_{i=0}^{p-1} X^{i p^k},$$
which is `Polynomial.cyclotomic_prime_pow_eq_geom_sum`. The product formula holds over every commutative ring:
$$\prod_{d \mid n} \Phi_d = X^n - 1 \quad (n > 0),$$
which is `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`. From it, `Polynomial.cyclotomic_eq_X_pow_sub_one_div` computes $\Phi_n$ by division by the $\Phi_d$ for the proper divisors $d$, and `Polynomial.cyclotomic.dvd_X_pow_sub_one` says that $\Phi_n$ divides $X^n - 1$. Möbius inversion of the product formula gives `Polynomial.cyclotomic_eq_prod_X_pow_sub_one_pow_moebius`, an equation in the field of rational functions. Over a field where $n$ is invertible, $\Phi_n$ is separable, `Polynomial.separable_cyclotomic`, and squarefree, `Polynomial.squarefree_cyclotomic`.

**Roots.** The module `Mathlib.RingTheory.Polynomial.Cyclotomic.Roots` describes the roots. In a domain in which $n$ is nonzero,
$$\Phi_n(\mu) = 0 \iff \mu \text{ is a primitive } n\text{-th root of unity},$$
which is `Polynomial.isRoot_cyclotomic_iff`. The multiset of roots is the set of primitive roots, `Polynomial.cyclotomic.roots_eq_primitiveRoots_val`, and it has no repeated elements, `Polynomial.roots_cyclotomic_nodup`. Over a field of characteristic $0$, the polynomial $\Phi_n$ over $\mathbb{Z}$ is the minimal polynomial over $\mathbb{Z}$ of a primitive $n$-th root of unity $\mu$, `Polynomial.cyclotomic_eq_minpoly`, and the same holds over $\mathbb{Q}$, `Polynomial.cyclotomic_eq_minpoly_rat`. As a result $\Phi_n$ is irreducible over $\mathbb{Z}$, `Polynomial.cyclotomic.irreducible`, and over $\mathbb{Q}$. The proof of these statements uses the theorem that $\mu^p$ has the same minimal polynomial as $\mu$ for a prime $p \nmid n$, which needs reduction modulo $p$. Distinct cyclotomic polynomials over $\mathbb{Q}$ are coprime, `Polynomial.cyclotomic.isCoprime_rat`, and in characteristic $0$ the map $n \mapsto \Phi_n$ is injective, `Polynomial.cyclotomic_injective`.

**Expansion and characteristic $p$.** The module `Mathlib.RingTheory.Polynomial.Cyclotomic.Expand` compares $\Phi_n(X^p)$ with $\Phi_{np}$. For a prime $p$,
$$\Phi_n(X^p) = \Phi_{np} \Phi_n \text{ if } p \nmid n, \qquad \Phi_n(X^p) = \Phi_{np} \text{ if } p \mid n,$$
which are `Polynomial.cyclotomic_expand_eq_cyclotomic_mul` and `Polynomial.cyclotomic_expand_eq_cyclotomic`. In characteristic $p$ the Frobenius gives $\Phi_n(X^p) = \Phi_n^p$, and so
$$\Phi_{p^k m} = \Phi_m^{\,p^k - p^{k-1}} \quad (p \nmid m,\ k > 0),$$
which is `Polynomial.cyclotomic_mul_prime_pow_eq`, with the case $k = 1$ as `Polynomial.cyclotomic_mul_prime_eq_pow_of_not_dvd`. So the roots of $\Phi_{p^k m}$ in a domain of characteristic $p$ are the primitive $m$-th roots of unity, `Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP`.

**Factorization over finite fields.** The module `Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization` lets $K$ be a finite field with $q = p^f$ elements and $p \nmid n$. Then every irreducible factor of $\Phi_n$ over $K$ has degree equal to the order of $q$ in $(\mathbb{Z}/n)^\times$, `Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible`. The number of distinct factors is $\varphi(n)$ divided by this order, `Polynomial.normalizedFactors_cyclotomic_card`. Conversely, a factor of this degree is irreducible, `Polynomial.irreducible_of_dvd_cyclotomic_of_natDegree`.

**Values.** The module `Mathlib.RingTheory.Polynomial.Cyclotomic.Eval` evaluates $\Phi_n$ at real points. At $1$ the value is $p$ when $n$ is a power of the prime $p$, `Polynomial.eval_one_cyclotomic_prime_pow`, and it is $1$ when $n$ is not a prime power, `Polynomial.eval_one_cyclotomic_not_prime_pow`. For $n > 2$ the value is positive at every real point, `Polynomial.cyclotomic_pos`. For $q > 1$ and $n \ge 2$ there are bounds
$$(q - 1)^{\varphi(n)} < \Phi_n(q) < (q + 1)^{\varphi(n)},$$
which are `Polynomial.sub_one_pow_totient_lt_cyclotomic_eval` and `Polynomial.cyclotomic_eval_lt_add_one_pow_totient`. These bounds are the key step in the proof of Wedderburn's little theorem that a finite division ring is commutative. A related fact from Basic is `Polynomial.orderOf_root_cyclotomic_dvd`: if $a$ is a root of $\Phi_n$ modulo $p$, then the order of $a$ modulo $p$ divides $n$. It is a step toward the theorem that there are infinitely many primes $p \equiv 1 \pmod n$.

#### Common errors

1. `Polynomial.cyclotomic' n R` and `Polynomial.cyclotomic n R` are different. The first is the product over the primitive roots that exist in $R$, and it is wrong when $R$ has too few roots of unity. The second is always correct, and most theorems are about it.
2. Many statements need $n \neq 0$ in $R$, written `[NeZero (n : R)]`. In characteristic $p$ with $p \mid n$, the roots of $\Phi_n$ are not primitive $n$-th roots of unity, because none exist.
3. `Polynomial.cyclotomic.irreducible` is stated over $\mathbb{Z}$ and needs $0 < n$. Over $\mathbb{Z}/p$ the polynomial $\Phi_n$ is usually reducible, as the module on finite fields shows.

### Exercises

1. (A) Compute $\Phi_{12}$ from the product formula $\prod_{d \mid 12} \Phi_d = X^{12} - 1$, and check the degree with `Polynomial.natDegree_cyclotomic`.
2. (A) Use `Polynomial.cyclotomic_prime_pow_eq_geom_sum` to write $\Phi_8$ and $\Phi_9$, and evaluate both at $1$.
3. (B) Use `Polynomial.cyclotomic_expand_eq_cyclotomic_mul` to prove that $\Phi_{2n}(X) = \Phi_n(-X)$ for odd $n > 1$.
4. (B) Prove that $\Phi_5$ is irreducible over $\mathbb{F}_2$ and that it is a product of linear factors over $\mathbb{F}_{11}$, using `Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible`.
5. (C) Let $p$ be a prime and $a$ an integer with $\Phi_n(a) \equiv 0 \pmod p$ and $p \nmid n$. Start from `Polynomial.orderOf_root_cyclotomic_dvd`, prove that the order of $a$ modulo $p$ is exactly $n$, and deduce that $p \equiv 1 \pmod n$.
6. (C) Let $D$ be a finite division ring with center $F$ of size $q$, and let $n = \dim_F D$. Use the class equation and `Polynomial.sub_one_pow_totient_lt_cyclotomic_eval` to prove that $n = 1$.

### Reference

<?reference?>
