---
title: Unique factorization and principal ideal domains
kind: api
modules:
  - Mathlib.RingTheory.UniqueFactorizationDomain.Defs
  - Mathlib.RingTheory.UniqueFactorizationDomain.Basic
  - Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
  - Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet
  - Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
  - Mathlib.RingTheory.UniqueFactorizationDomain.Finite
  - Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
  - Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
  - Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
  - Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky
  - Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup
  - Mathlib.RingTheory.UniqueFactorizationDomain.Localization
  - Mathlib.RingTheory.UniqueFactorizationDomain.Nat
  - Mathlib.RingTheory.Prime
  - Mathlib.RingTheory.PrincipalIdealDomain
  - Mathlib.RingTheory.PrincipalIdealDomainOfPrime
explains:
  E2: [UniqueFactorizationMonoid.iff_exists_prime_factors, UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors, UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime, IsPrincipalIdealRing.of_prime, Ideal.irreducible_iff_isMaximal_span_singleton_of_not_isField, exists_gcd_eq_mul_add_mul, mul_eq_mul_prime_pow]
  E1: auto
families: []
requires: [V06.C06, V09.C01, V09.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Unique factorization and principal ideal domains

### Overview

Sections 1 to 3 use the class `UniqueFactorizationMonoid` and the class `IsPrincipalIdealRing` as known objects. This section is a guide to the modules that define them and hold their general theory. Volume 6, Chapter 6 introduces the definitions and proves that a principal ideal domain has unique factorization. The modules here go further: they give the factorization of an element as a multiset, the count of a prime in it, the gcd that the factorization defines, the criterion of Kaplansky with prime ideals, and the theory of Bezout rings.

The library works in a commutative monoid with zero, not only in a domain. So most of the lemmas below apply to $\mathbb{N}$, to the associates of a ring and to the nonzero elements of a domain with no change.

### The library around it

**The definitions.** The module `Mathlib.RingTheory.UniqueFactorizationDomain.Defs` defines `WfDvdMonoid α`: strict divisibility is well founded, so every nonzero nonunit has an irreducible factor, `WfDvdMonoid.exists_irreducible_factor`, and is a product of irreducible elements, `WfDvdMonoid.exists_factors`. The class `UniqueFactorizationMonoid α` asks in addition that every irreducible element is prime, `UniqueFactorizationMonoid.irreducible_iff_prime`. The induction principle `UniqueFactorizationMonoid.induction_on_prime` proves a property for all elements from $0$, the units, and the step from $a$ to $p a$ for a prime $p$. The library gives the class from a decomposition into primes:
$$\text{UFM} \iff \text{every } a \neq 0 \text{ is associated to a product of primes},$$
which is `UniqueFactorizationMonoid.iff_exists_prime_factors` in `Mathlib.RingTheory.UniqueFactorizationDomain.Basic`, for a cancellative monoid. The proof in the backward direction shows that strict divisibility is well founded, by induction on the number of prime factors, and that an irreducible element $q$ is prime: $q$ is associated to a product of primes, and since $q$ is irreducible, that product has one factor. The other main criterion is `ufm_of_decomposition_of_wfDvdMonoid`: a well founded monoid with the decomposition property of gcd monoids has unique factorization.

**The multiset of factors.** The function `UniqueFactorizationMonoid.factors a` chooses a multiset of irreducible factors of $a$, with `UniqueFactorizationMonoid.factors_prod` for the product up to a unit, and `UniqueFactorizationMonoid.factors_unique` for the uniqueness up to associates. In a monoid with a normalization, the better choice is `UniqueFactorizationMonoid.normalizedFactors a` of `Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors`, whose elements are normalized. For $\mathbb{N}$ it is the list of prime factors, `Nat.factors_eq`. It is a homomorphism of monoids on the nonzero elements, `UniqueFactorizationMonoid.normalizedFactors_mul` and `UniqueFactorizationMonoid.normalizedFactors_pow`, and it turns divisibility into inclusion of multisets:
$$x \mid y \iff \operatorname{nf}(x) \le \operatorname{nf}(y) \qquad (x, y \neq 0),$$
which is `UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors`. For the proof, if $y = x z$ then $\operatorname{nf}(y) = \operatorname{nf}(x) + \operatorname{nf}(z)$. Conversely, if $\operatorname{nf}(x) \le \operatorname{nf}(y)$, write $\operatorname{nf}(y) = \operatorname{nf}(x) + t$; then $y$ is associated to $x$ times the product of $t$. Two nonzero elements are associated exactly when they have the same normalized factors, `UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors`. The module `Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp` packs the multiset into a finitely supported function `factorization a : α →₀ ℕ`, with `factorization_mul`, `factorization_pow` and `factorization_eq_count`. The module `Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet` works with the associates instead: `Associates.FactorSet α` is a multiset of irreducible associates with a top element for $0$, `Associates.factors` gives the factor set of an associate, and `Associates.count p` counts the prime $p$ in it. The counts add on products, `Associates.count_mul`, and $p^k \mid m$ exactly when $k$ is at most the count, `Associates.prime_pow_dvd_iff_le`. The associates of a unique factorization monoid form a lattice, `Associates.instLattice`.

**Consequences.** A unique factorization monoid with a normalization is a normalized gcd monoid, `UniqueFactorizationMonoid.toNormalizedGCDMonoid` in `Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid`: the gcd takes the minimum of the multisets of factors. A function that is multiplicative on coprime elements is determined by its values on prime powers, `UniqueFactorizationMonoid.multiplicative_of_coprime` in `Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative`, and `UniqueFactorizationMonoid.induction_on_prime_power` and `UniqueFactorizationMonoid.induction_on_coprime` are the induction principles behind it. When the group of units is finite, an element has finitely many divisors, `UniqueFactorizationMonoid.fintypeSubtypeDvd` in `Mathlib.RingTheory.UniqueFactorizationDomain.Finite`. The module `Mathlib.RingTheory.UniqueFactorizationDomain.Nat` gives the instance `Nat.instUniqueFactorizationMonoid`. The module `Mathlib.RingTheory.UniqueFactorizationDomain.Localization` has no live declarations of its own. The module `Mathlib.RingTheory.Prime` holds two lemmas on products with a prime power: if $x y = a p^n$ with $p$ prime in a cancellative monoid, then $x = b p^i$ and $y = c p^j$ with $i + j = n$ and $a = b c$, `mul_eq_mul_prime_pow`. It also has `Prime.neg` and `Prime.abs`.

**Ideals and unique factorization.** The criterion of Kaplansky is in `Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky`:
$$R \text{ is a UFD} \iff \text{every nonzero prime ideal of } R \text{ contains a prime element},$$
which is `UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime`, for a domain $R$. One direction is `Ideal.IsPrime.exists_mem_prime_of_ne_bot`: a nonzero element of a prime ideal is a product of primes, and one of the factors lies in the ideal. The module `Mathlib.RingTheory.UniqueFactorizationDomain.Ideal` translates well founded divisibility into a condition on principal ideals, `Ideal.setOfPred_isPrincipal_wellFoundedOn_gt` and `WfDvdMonoid.of_setOfPred_isPrincipal_wellFoundedOn_gt`: there is no infinite strictly ascending chain of principal ideals. The module `Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup` proves that the class group of a gcd domain is trivial, the instance `IsGCDMonoid.subsingleton_classGroup`, because an invertible ideal of a gcd domain is principal, `IsGCDMonoid.isPrincipal_of_exists_mul_ne_zero_isPrincipal`.

**Principal ideal rings.** The module `Mathlib.RingTheory.PrincipalIdealDomain` gives the generator of a principal submodule, `Submodule.IsPrincipal.generator`, with `Submodule.IsPrincipal.generator_mem` and `Submodule.IsPrincipal.mem_iff_generator_dvd`. A principal ideal ring is Noetherian, `PrincipalIdealRing.isNoetherianRing`, and a principal ideal domain has unique factorization, `PrincipalIdealRing.to_uniqueFactorizationMonoid`. In a principal ideal domain that is not a field, the irreducible elements are exactly the generators of maximal ideals,
$$p \text{ irreducible} \iff (p) \text{ maximal},$$
which is `Ideal.irreducible_iff_isMaximal_span_singleton_of_not_isField`. If $p$ is irreducible and $(p) \subseteq (q)$, then $q$ is a unit or an associate of $p$, so $(q) = R$ or $(q) = (p)$. The field case is excluded because $0$ is not irreducible but $(0)$ is maximal in a field. Fields and Euclidean domains are principal ideal rings by instances, `DivisionSemiring.isPrincipalIdealRing` and `EuclideanDomain.instIsPrincipalIdealRing`, and the class passes to quotients, `IsPrincipalIdealRing.of_surjective`, and to finite products, `isPrincipalIdealRing_prod_iff`.

**Bezout rings.** A ring is Bezout, `IsBezout`, when every finitely generated ideal is principal, or equivalently every ideal $(x, y)$. The gcd of a Bezout ring is a generator of $(x, y)$, `IsBezout.gcd`, so Bezout's identity holds:
$$\gcd(a, b) = a x + b y \text{ for some } x, y,$$
which is `exists_gcd_eq_mul_add_mul`, with `span_gcd` for the equality of ideals. A Bezout domain is a gcd domain, the instance `IsBezout.instIsGCDMonoidOfIsCancelMulZero`. Coprimality and divisibility behave as in $\mathbb{Z}$: `isRelPrime_iff_isCoprime`, `Irreducible.coprime_iff_not_dvd` and `Prime.coprime_iff_not_dvd`. A Noetherian Bezout ring is a principal ideal ring, `IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout`.

**Principal ideals from prime ideals.** The module `Mathlib.RingTheory.PrincipalIdealDomainOfPrime` proves that a commutative ring in which every prime ideal is principal is a principal ideal ring, `IsPrincipalIdealRing.of_prime`, and that it is enough to check the nonzero primes, `IsPrincipalIdealRing.of_prime_ne_bot`. The proof is the same as for Cohen's theorem of Chapter 3: the principal ideals form an Oka family, `Ideal.isOka_isPrincipal`. If some ideal is not principal, Zorn's lemma gives an ideal maximal among the non-principal ideals, `Ideal.exists_maximal_not_isPrincipal`, and the Oka property makes it prime.

#### Common errors

1. `UniqueFactorizationMonoid.factors` and `UniqueFactorizationMonoid.normalizedFactors` are different functions. The first makes an arbitrary choice; the second needs a `NormalizationMonoid` and is the one with good equalities. In $\mathbb{Z}$, the factors of $-6$ can contain $-2$, and the normalized factors are $\{2, 3\}$.
2. The class is `UniqueFactorizationMonoid` for rings too: there is no class with the word "domain". A unique factorization domain is a ring with `IsDomain R` and `UniqueFactorizationMonoid R`.
3. `Submodule.IsPrincipal.generator` is a choice of generator, unique only up to a unit. Use `Submodule.IsPrincipal.associated_generator_span_self` to compare it with a known generator.

### Exercises

1. (A) Use `UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors` to show that in a unique factorization domain the gcd of $a$ and $b$ has the minimum of the two multisets of factors as its normalized factors.
2. (A) Prove that $\mathbb{Z}[i]$ is a principal ideal domain, and deduce from `Ideal.irreducible_iff_isMaximal_span_singleton_of_not_isField` that $(1 + i)$ is maximal.
3. (B) Prove that $\mathbb{Z}[\sqrt{-5}]$ is not a unique factorization domain by finding a nonzero prime ideal that contains no prime element.
4. (B) Show that a Bezout domain that satisfies the ascending chain condition on principal ideals is a principal ideal domain.
5. (B) Let $f : \mathbb{N} \to \mathbb{N}$ be multiplicative on coprime numbers. Use `UniqueFactorizationMonoid.multiplicative_of_coprime` to prove that $f$ is determined by its values on prime powers, and compute the number of divisors of $n$ in this way.
6. (C) Prove the criterion of Kaplansky: a domain in which every nonzero prime ideal contains a prime element is a unique factorization domain. Consider the multiplicative set generated by the units and the primes, and an ideal maximal among those disjoint from it.

### Reference

<?reference?>
