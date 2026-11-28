---
title: Coprime elements, Bezout rings and finite domains
kind: api
modules:
  - Mathlib.RingTheory.Coprime.Basic
  - Mathlib.RingTheory.Coprime.Lemmas
  - Mathlib.RingTheory.Coprime.Ideal
  - Mathlib.RingTheory.Bezout
  - Mathlib.RingTheory.EuclideanDomain
  - Mathlib.RingTheory.Int.Basic
  - Mathlib.RingTheory.ChainOfDivisors
  - Mathlib.RingTheory.IntegralDomain
  - Mathlib.RingTheory.Fintype
explains:
  E2: [IsCoprime.mul_dvd, IsCoprime.dvd_of_dvd_mul_left, IsCoprime.pow, exists_sum_eq_one_iff_pairwise_coprime, IsBezout.iff_span_pair_isPrincipal, EuclideanDomain.span_gcd, Finite.isField_of_domain, sum_hom_units_eq_zero]
  E1: auto
families: []
requires: [V06.C03, V06.C06, V09.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Coprime elements, Bezout rings and finite domains

### Overview

In the integers, two numbers $a$ and $b$ are coprime when $\gcd(a, b) = 1$, and Bezout's identity gives $u a + v b = 1$. In an arbitrary commutative ring these two conditions differ. Mathlib takes the identity as the definition: `IsCoprime a b` means that there are $u, v$ with $u a + v b = 1$, that is, that the ideals $(a)$ and $(b)$ are comaximal. This is the condition that the Chinese remainder theorem of Section 1.3 needs. The weaker condition that each common divisor is a unit is `IsRelPrime`. The two agree in a Bezout ring, a ring in which each finitely generated ideal is principal.

This section goes through the API of `IsCoprime`, its versions for finite products, the Bezout rings, the links to the gcd of a Euclidean domain and of $\mathbb Z$, and the order isomorphisms between chains of divisors. It ends with the facts about finite domains: a finite domain is a field, and each finite subgroup of the units of a domain is cyclic. Section 5.4 treats the gcd monoids and the Euclidean algorithm. This section uses the gcd only as a tool.

### The library around it

#### The definition and its algebra

The module `Mathlib.RingTheory.Coprime.Basic` defines `IsCoprime` in a commutative semiring. The definition has no hypothesis on $R$, so the API works in $\mathbb N$, in polynomial rings and in quotients. Its basic facts follow from the identity by multiplication.

| Lean name | Statement |
|---|---|
| `IsCoprime.symm` | if $x$ and $y$ are coprime, then $y$ and $x$ are coprime |
| `isCoprime_one_left` | $1$ is coprime to each $x$ |
| `isCoprime_self` | $x$ is coprime to $x$ if and only if $x$ is a unit |
| `IsCoprime.isUnit_of_dvd` | if $x$ and $y$ are coprime and $x \mid y$, then $x$ is a unit |
| `IsCoprime.mul_dvd` | if $x$ and $y$ are coprime, $x \mid z$ and $y \mid z$, then $x y \mid z$ |
| `IsCoprime.dvd_of_dvd_mul_left` | if $x$ and $y$ are coprime and $x \mid y z$, then $x \mid z$ |
| `IsCoprime.mul_right` | if $x$ is coprime to $y$ and to $z$, then $x$ is coprime to $y z$ |
| `IsCoprime.of_isCoprime_of_dvd_left` | a divisor of a coprime element is coprime |
| `IsCoprime.map` | a ring homomorphism keeps coprimality |
| `IsCoprime.isRelPrime` | coprime elements are relatively prime |

Each proof is one line of algebra. For `IsCoprime.mul_dvd`, write $u x + v y = 1$, $z = x a$ and $z = y b$. Then $z = u x z + v y z = x y (u b) + x y (v a)$, so $x y \mid z$. For `IsCoprime.dvd_of_dvd_mul_left`, write $z = u x z + v y z$. Both terms are divisible by $x$ when $x \mid y z$. For `IsCoprime.mul_right`, multiply the two identities: $(u x + v y)(u' x + v' z) = 1$ expands to $x \cdot (\dots) + (v v') y z = 1$.

In a ring, a large family of lemmas says that coprimality does not change under an elementary operation. `IsCoprime.add_mul_left_left` gives `IsCoprime (x + y * z) y` from `IsCoprime x y`, and `IsCoprime.add_mul_left_left_iff` is the equivalence. The names follow a fixed pattern: the part add_mul or mul_add gives the shape of the new argument, the first left or right gives the side of the product, and the last left or right gives which argument changes. The family has versions with sub and with neg, such as `IsCoprime.neg_left`, and `IsCoprime.abs_left` and its relatives for an ordered ring. These lemmas are the ring form of the step $\gcd(a + b c, b) = \gcd(a, b)$ of the Euclidean algorithm.

The module `Mathlib.RingTheory.Coprime.Lemmas` adds powers and finite products. `IsCoprime.pow` gives that $x^m$ and $y^n$ are coprime when $x$ and $y$ are. The proof raises $u x + v y = 1$ to the power $m + n - 1$ and sorts the terms of the binomial expansion: each term is divisible by $x^m$ or by $y^n$. The product lemmas `IsCoprime.prod_left` and `IsCoprime.prod_right` follow from `IsCoprime.mul_right` by induction on the finset, and `Finset.prod_dvd_of_coprime` says that a pairwise coprime family of divisors of $z$ has its product dividing $z$. The lemma `exists_sum_eq_one_iff_pairwise_coprime` gives the identity behind the Chinese remainder theorem: for a nonempty finset $t$, the elements $s_i$ are pairwise coprime if and only if $\sum_{i \in t} \mu_i \prod_{j \ne i} s_j = 1$ for some $\mu$. One direction is the product lemma applied to $s_i$ and $\prod_{j \ne i} s_j$. The module also compares with the natural numbers: `Nat.isCoprime_iff_coprime` says that `IsCoprime (m : ℤ) n` holds if and only if $\gcd(m, n) = 1$ in $\mathbb N$, and `Int.isCoprime_iff_gcd_eq_one` gives the form with the gcd of integers. The parallel lemmas for `IsRelPrime`, such as `IsRelPrime.pow`, need only a `DecompositionMonoid`.

The module `Mathlib.RingTheory.Coprime.Ideal` has one result, `Ideal.iSup_iInf_eq_top_iff_pairwise`. It is the form of the identity above for ideals: $\sum_{i \in t} \bigcap_{j \ne i} I_j = R$ if and only if the $I_i$ are pairwise coprime. For principal ideals, `Ideal.isCoprime_span_singleton_iff` translates between the two notions of coprimality.

#### Bezout rings

The class `IsBezout R` says that each finitely generated ideal is principal. A principal ideal ring is Bezout (`IsBezout.of_isPrincipalIdealRing`), and the ring of entire functions and the ring of all algebraic integers are Bezout domains that are not Noetherian. The module `Mathlib.RingTheory.Bezout` has the reduction to two generators, `IsBezout.iff_span_pair_isPrincipal`. One direction is clear. For the other, induct on a finite generating set: if $(x_1, \dots, x_n) = (d)$, then $(x_1, \dots, x_n, x_{n+1}) = (d, x_{n+1})$, which is principal by hypothesis. The lemma `Function.Surjective.isBezout` says that a quotient of a Bezout ring is Bezout.

`IsBezout.tfae` says that for a Bezout domain four conditions are equivalent: Noetherian, principal ideal ring, unique factorization domain, and the ascending chain condition on principal ideals (`WfDvdMonoid`). The key step is that ascending chains of principal ideals control all finitely generated ideals, because each of them is principal. In a Bezout ring `IsBezout.gcd x y` is a generator of $(x, y)$, and `isRelPrime_iff_isCoprime` shows that the two notions of coprimality agree.

#### Euclidean domains and the integers

The module `Mathlib.RingTheory.EuclideanDomain` connects the gcd of the Euclidean algorithm with coprimality. `EuclideanDomain.span_gcd` says $(\gcd(x, y)) = (x, y)$. The proof: $\gcd(x, y) = a x + b y$ by the extended algorithm, so the left side is contained in the right side, and $\gcd(x, y)$ divides $x$ and $y$, so the right side is contained in the left side. From it follow `EuclideanDomain.gcd_isUnit_iff`, which says that $\gcd(x, y)$ is a unit if and only if $x$ and $y$ are coprime, and `EuclideanDomain.dvd_or_coprime`: an irreducible $x$ divides $y$ or is coprime to $y$. The definition `EuclideanDomain.gcdMonoid` makes a Euclidean domain a `GCDMonoid`, and `isCoprime_div_gcd_div_gcd` says that $p / \gcd(p, q)$ and $q / \gcd(p, q)$ are coprime for $q \ne 0$.

The module `Mathlib.RingTheory.Int.Basic` specializes to $\mathbb Z$. `Int.prime_iff_natAbs_prime` says that an integer $k$ is prime if and only if $|k|$ is a prime number. `Int.span_natAbs` says that $(|a|) = (a)$. `Int.Prime.dvd_mul` is Euclid's lemma with the absolute value. `Int.sq_of_isCoprime` says that if $a$ and $b$ are coprime and $a b = c^2$, then $a = \pm d^2$ for some $d$. It is the step in the parametrization of Pythagorean triples.

#### Chains of divisors

The module `Mathlib.RingTheory.ChainOfDivisors` works in the monoid `Associates M`, where divisibility is a partial order. `DivisorChain.exists_chain_of_prime_pow` says that the divisors of $p^n$ for a prime $p$ form a chain $1 < p < p^2 < \dots < p^n$, and `DivisorChain.isPrimePow_of_has_chain` is the converse in a unique factorization monoid: an element whose divisors form a chain of length $n$ is a prime power. `Associates.isAtom_iff` says that the atoms of this order are the irreducible elements. The definition `mkFactorOrderIsoOfFactorDvdEquiv` turns a bijection of divisors that keeps divisibility into an order isomorphism, and `emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso` says that such an isomorphism keeps multiplicities of prime factors. Dedekind domains use these results to compare the factorization of an ideal with the factorization of a polynomial.

#### Finite domains

The module `Mathlib.RingTheory.IntegralDomain` proves `Finite.isField_of_domain`: a finite domain is a field. The proof is two lines. For $a \ne 0$, multiplication by $a$ is injective because $R$ is a domain, so it is bijective because $R$ is finite (`mul_right_bijective_of_finite₀`), and $1$ is in its image. The definitions `Fintype.fieldOfDomain` and `Fintype.divisionRingOfIsDomain` give the structure as data. The noncommutative form is Wedderburn's theorem, which is in another volume.

The second main result is that each finite subgroup of the units of a domain is cyclic. The instances are `isCyclic_subgroup_units` and `instIsCyclicUnitsOfFinite`, and `isCyclic_of_injective_ringHom` gives the form for a group with an injective homomorphism to $R$. The proof counts roots: the polynomial $X^d - 1$ has at most $d$ roots in a domain, so the group has at most $d$ elements of order dividing $d$, which forces it to be cyclic. In particular the unit group of a finite field is cyclic. The lemma `sum_hom_units_eq_zero` says that for a nontrivial homomorphism $f : G \to R$ from a finite group, $\sum_{g} f(g) = 0$. Proof: take $h$ with $f(h) \ne 1$. Then $f(h) \sum_g f(g) = \sum_g f(h g) = \sum_g f(g)$, so $(f(h) - 1) \sum_g f(g) = 0$, and $f(h) - 1 \ne 0$. The lemma `exists_eq_pow_of_mul_eq_pow_of_coprime` says that if $a$ and $b$ are coprime and $a b = c^n$ in a gcd monoid with trivial units, then $a$ is an $n$-th power.

The module `Mathlib.RingTheory.Fintype` has small facts. `card_units_lt` says that a finite nontrivial monoid with zero has fewer units than elements, because $0$ is not a unit. `orderOf_lt_card` and `ZMod.orderOf_lt` follow. `Finset.univ_of_card_le_two` lists the elements of a ring with at most two elements.

#### Common errors

1. `IsCoprime` is the Bezout identity, not the gcd condition. In $k[X, Y]$ the elements $X$ and $Y$ have only units as common divisors, so `IsRelPrime X Y` holds, but `IsCoprime X Y` is false because $(X, Y) \ne (1)$. Use `IsRelPrime` for the gcd condition in a unique factorization domain that is not a principal ideal domain.
2. In $\mathbb N$ the identity has no subtraction, so `IsCoprime (2 : ℕ) 3` is false: $u \cdot 2 + v \cdot 3 = 1$ has no solution in natural numbers. Cast to $\mathbb Z$ and use `Nat.isCoprime_iff_coprime`, or work with the coprimality of natural numbers.
3. The names of the elementary operation family are easy to swap. Read `IsCoprime.add_mul_left_left` as: the left argument changes to $x + y z$, with $y$ on the left of the product. Check the statement before it is used.

### Exercises

1. (A) Prove `IsCoprime.mul_dvd` from the definition in Lean with `obtain ⟨u, v, h⟩ := hxy`, and compare with `Finset.prod_dvd_of_coprime`.
2. (A) Show that $X$ and $X + 1$ are coprime in $R[X]$ for each commutative ring $R$, and that $X$ and $2$ are not coprime in $\mathbb Z[X]$.
3. (B) Prove that the ring of integers $\mathbb Z[\sqrt{-5}]$ is not Bezout. Use `IsBezout.iff_span_pair_isPrincipal` with the ideal $(2, 1 + \sqrt{-5})$.
4. (B) Use `Finite.isField_of_domain` to prove that each prime ideal of a finite commutative ring is maximal.
5. (B) Use `sum_hom_units_eq_zero` to prove that $\sum_{x \in \mathbb F_q} x^k = 0$ for $0 < k < q - 1$, where $\mathbb F_q$ is a field with $q$ elements.
6. (C) Prove that a Bezout domain is integrally closed. Use `IsBezout.toGCDDomain` and the fact that a gcd domain is integrally closed.

### Reference

<?reference?>
