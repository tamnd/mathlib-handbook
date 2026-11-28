---
title: Multiplicity and the radical of an element
kind: api
modules:
  - Mathlib.RingTheory.Multiplicity
  - Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
  - Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
  - Mathlib.RingTheory.Radical.Basic
  - Mathlib.RingTheory.Radical.NatInt
explains:
  E2: [pow_dvd_iff_le_emultiplicity, emultiplicity_mul, emultiplicity_add_eq_min, UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors, UniqueFactorizationMonoid.dvd_iff_multiplicity_le, IsRelPrime.moebius_mul, UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd, UniqueFactorizationMonoid.squarefree_radical]
  E1: auto
families: []
requires: [V06.C06, V09.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Multiplicity and the radical of an element

### Overview

The multiplicity of $a$ in $b$ is the largest $n$ such that $a^n$ divides $b$. For integers it is the exponent of a prime in a factorization, and it is the source of the $p$-adic valuation. The radical of $b$ is the product of the distinct prime factors of $b$, each taken once. For example, the multiplicity of $2$ in $72 = 2^3 \cdot 3^2$ is $3$, and the radical of $72$ is $6$.

The library defines multiplicity in an arbitrary monoid, where the largest $n$ need not exist. It then proves the usual rules for prime elements, and it connects multiplicity with the multiset of normalized factors in a unique factorization monoid. The same factorization gives the radical of an element and the Möbius function of a unique factorization monoid. This section is a guide to these modules. It uses the normalized factors of Section 5.

### The library around it

**Two versions of multiplicity.** The module `Mathlib.RingTheory.Multiplicity` defines `emultiplicity a b`, a value in `ℕ∞`. It is the supremum of the $n$ with $a^n \mid b$, and it is $\top$ when every power of $a$ divides $b$. For example, the multiplicity of $1$ in any element is $\top$, and so is the multiplicity of any element in $0$. The predicate `FiniteMultiplicity a b` says that some power of $a$ does not divide $b$, and `finiteMultiplicity_iff_emultiplicity_ne_top` says that this is the same as `emultiplicity a b ≠ ⊤`. The function `multiplicity a b` is a natural number. It equals `emultiplicity a b` when the multiplicity is finite, `FiniteMultiplicity.emultiplicity_eq_multiplicity`, and it is $0$ otherwise, `multiplicity_eq_zero_of_not_finiteMultiplicity`. Use `emultiplicity` for statements that must hold in all cases, and use `multiplicity` when the finiteness is known and natural number arithmetic is more convenient.

The basic tool is the characterization by divisibility:
$$a^k \mid b \iff k \le \operatorname{emult}(a, b),$$
which is `pow_dvd_iff_le_emultiplicity`. Its finite version is `FiniteMultiplicity.pow_dvd_iff_le_multiplicity`. To compute a multiplicity, show that $a^k$ divides $b$ and that $a^{k+1}$ does not: `emultiplicity_eq_coe` states this as an equivalence, and `multiplicity_eq_of_dvd_of_not_dvd` gives the result for `multiplicity`. The value is positive exactly when $a \mid b$, `dvd_iff_multiplicity_pos`, and it is zero exactly when $a \nmid b$, `multiplicity_eq_zero`. Multiplicity cannot decrease under a monoid homomorphism, `le_emultiplicity_map`, and it is unchanged under an isomorphism, `emultiplicity_map_eq`.

**Finiteness.** In a monoid with zero where divisibility is well founded, `WfDvdMonoid`, the multiplicity of a non-unit in a nonzero element is finite, `FiniteMultiplicity.of_not_isUnit`, and in particular for a prime, `FiniteMultiplicity.of_prime_left`. For the integers the condition is explicit, `Int.finiteMultiplicity_iff`: the multiplicity of $a$ in $b$ is finite exactly when $|a| \neq 1$ and $b \neq 0$. The module `Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity` also proves `WfDvdMonoid.max_power_factor`: a nonzero $a_0$ and an irreducible $x$ give a decomposition $a_0 = x^n a$ with $x \nmid a$.

**Rules for a prime.** Let $p$ be prime in a cancellative commutative monoid with zero. Then multiplicity is additive on products:
$$\operatorname{emult}(p, a b) = \operatorname{emult}(p, a) + \operatorname{emult}(p, b),$$
which is `emultiplicity_mul`. The version `multiplicity_mul` needs the finiteness of the multiplicity in $a b$ as a hypothesis. Consequences are `emultiplicity_pow` and `multiplicity_pow`, $\operatorname{emult}(p, a^k) = k \operatorname{emult}(p, a)$, and `multiplicity_pow_self_of_prime`. For an irreducible element the multiplicity in itself is $1$, `Irreducible.multiplicity_self`. In a ring there is also a rule for sums. If the multiplicities of $p$ in $a$ and in $b$ differ, then
$$\operatorname{emult}(p, a + b) = \min(\operatorname{emult}(p, a), \operatorname{emult}(p, b)),$$
which is `emultiplicity_add_eq_min`. This rule does not need $p$ to be prime. The one-sided versions are `emultiplicity_add_of_gt` and `emultiplicity_sub_of_gt`. These are the rules of a valuation, and the $p$-adic valuations of the integers and of the rational numbers are built from them.

**Multiplicity and factorization.** In a unique factorization monoid with a normalization, the multiplicity of an irreducible $a$ in $b \neq 0$ is the number of times that the normalized form of $a$ occurs in the normalized factors of $b$:
$$\operatorname{emult}(a, b) = \operatorname{count}(\operatorname{normalize} a, \operatorname{normalizedFactors} b),$$
which is `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`. The version for `multiplicity` is `UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors`, and `UniqueFactorizationMonoid.le_emultiplicity_iff_replicate_le_normalizedFactors` compares a lower bound for the multiplicity with a sub-multiset of the factors. Divisibility is then a comparison of multiplicities at each prime:
$$a \mid b \iff \operatorname{mult}(p, a) \le \operatorname{mult}(p, b) \text{ for every prime } p,$$
for $a, b \neq 0$, which is `UniqueFactorizationMonoid.dvd_iff_multiplicity_le`. For natural numbers and integers the two notions agree through the cast: `Int.natCast_multiplicity` and `Int.multiplicity_natAbs`.

**The Möbius function.** The module `Mathlib.RingTheory.UniqueFactorizationDomain.Moebius` defines `UniqueFactorizationMonoid.moebius`, a function to $\mathbb{Z}$ on any unique factorization monoid. It is $0$ on elements that are not squarefree, `UniqueFactorizationMonoid.moebius_of_not_squarefree`, and on a squarefree $a$ it is $(-1)^k$ where $k$ is the number of prime factors, `Squarefree.moebius_eq`. It is multiplicative on relatively prime elements, `IsRelPrime.moebius_mul`, it takes the same value on associated elements, `Associated.moebius_eq`, and it is $-1$ on an irreducible element, `Irreducible.moebius_eq`. On the natural numbers it is the Möbius function of number theory, `Nat.moebius_eq`.

**The radical.** The module `Mathlib.RingTheory.Radical.Basic` defines `UniqueFactorizationMonoid.primeFactors a`, the finite set of normalized prime factors of $a$, and `UniqueFactorizationMonoid.radical a`, their product. The radical divides the element, `UniqueFactorizationMonoid.radical_dvd_self`, it is squarefree, `UniqueFactorizationMonoid.squarefree_radical`, and it has the same prime factors, `UniqueFactorizationMonoid.primeFactors_radical`. It does not change under powers, `UniqueFactorizationMonoid.radical_pow`, and it is multiplicative on relatively prime elements, `UniqueFactorizationMonoid.radical_mul`. The main property connects the radical with the radical of an ideal in Chapter 1: for $a \neq 0$,
$$(\exists n,\ a \mid b^n) \iff \operatorname{rad}(a) \mid b,$$
which is `UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd`. Hence the ideal $(\operatorname{rad} a)$ is the radical of the ideal $(a)$ in a principal ideal domain. In a Euclidean domain the quotient $a / \operatorname{rad}(a)$ has a name, `EuclideanDomain.divRadical`, with `EuclideanDomain.radical_mul_divRadical`. This quotient is used in the theorem of Mason and Stothers for polynomials. The module `Mathlib.RingTheory.Radical.NatInt` gives the forms for $\mathbb{N}$ and $\mathbb{Z}$: `Nat.radical_eq_prod_primeFactors` writes the radical as the product over `Nat.primeFactors`, `Nat.dvd_radical_pow_self` says that $n \mid \operatorname{rad}(n)^n$, and `Int.radical_natAbs_eq_radical` reduces the integer case to the natural numbers.

#### Common errors

1. The multiplicity of $1$ in any element and of any element in $0$ is infinite. So `multiplicity 1 b` and `multiplicity a 0` are $0$, by the convention for the infinite case, and not the values that an informal argument expects. Prove `FiniteMultiplicity` first, or work with `emultiplicity`.
2. The additivity `multiplicity_mul` has the hypothesis `FiniteMultiplicity p (a * b)`. Without it, the equation can fail: for $a = 0$ and $b = p$ the left side is $0$, by the convention for the infinite case, and the right side is $0 + 1 = 1$. The `emultiplicity` version needs no such hypothesis.
3. The radical and the prime factors depend on a `NormalizationMonoid` instance. In $\mathbb{Z}$ the radical of $-12$ is $6$, not $-6$, because the factors are normalized to be positive.

### Exercises

1. (A) Compute `emultiplicity 3 162` and `UniqueFactorizationMonoid.radical 162` in $\mathbb{N}$, and state the lemmas of this section that justify each step.
2. (A) Prove from `pow_dvd_iff_le_emultiplicity` that $\operatorname{emult}(a, b) \le \operatorname{emult}(a, b c)$ for all $a, b, c$ in a commutative monoid.
3. (B) Let $p$ be a prime number and $n \ge 1$. Prove that the multiplicity of $p$ in $n!$ is $\sum_{k \ge 1} \lfloor n / p^k \rfloor$, using `emultiplicity_mul` and induction on $n$.
4. (B) Use `emultiplicity_mul` and `emultiplicity_pow` to prove that $\sqrt{2}$ is irrational: in an equation $a^2 = 2 b^2$ with $a, b \neq 0$, compare the multiplicities of $2$ on the two sides.
5. (B) Prove that an element $a \neq 0$ of a unique factorization monoid is squarefree exactly when it is associated to its radical.
6. (C) Let $K$ be a field and $f \in K[X]$ nonzero. Describe `UniqueFactorizationMonoid.radical f` in terms of the roots of $f$ in an algebraic closure when $K$ has characteristic $0$, and prove that $f$ divides $\operatorname{rad}(f)^{\deg f}$.

### Reference

<?reference?>
