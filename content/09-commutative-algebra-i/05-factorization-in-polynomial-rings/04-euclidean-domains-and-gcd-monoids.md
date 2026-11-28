---
title: Euclidean domains and gcd monoids
kind: api
modules:
  - Mathlib.Algebra.EuclideanDomain.Defs
  - Mathlib.Algebra.EuclideanDomain.Basic
  - Mathlib.Algebra.EuclideanDomain.Field
  - Mathlib.Algebra.EuclideanDomain.Int
  - Mathlib.Algebra.GCDMonoid.Basic
  - Mathlib.Algebra.GCDMonoid.Multiset
  - Mathlib.Algebra.GCDMonoid.Finset
  - Mathlib.Algebra.GCDMonoid.FinsetLemmas
  - Mathlib.Algebra.GCDMonoid.Nat
  - Mathlib.Algebra.GCDMonoid.PUnit
  - Mathlib.Algebra.GCDMonoid.IntegrallyClosed
explains:
  E2: [EuclideanDomain.gcd_eq_gcd_ab, EuclideanDomain.GCD.induction, EuclideanDomain.gcd_mul_lcm, gcd_greatest, extract_gcd, exists_associated_pow_of_mul_eq_pow, Finset.associated_lcm_prod, IsLocalization.surj_of_gcd_domain]
  E1: auto
families: []
requires: [V06.C06, V09.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Euclidean domains and gcd monoids

### Overview

Volume 6, Chapter 6 proves that a Euclidean domain is a principal ideal domain and that a principal ideal domain has unique factorization. Section 1 of this chapter uses a greatest common divisor in $R$ to define the content of a polynomial. This section describes the two parts of the library that carry these notions: the class `EuclideanDomain` with its extended Euclidean algorithm, and the classes of gcd monoids with their normalization functions.

The two parts are independent. A Euclidean domain has its own function `EuclideanDomain.gcd`, defined by the algorithm. A gcd monoid is a commutative monoid with zero with a function `gcd` that satisfies the universal property of a greatest common divisor. The two functions agree only up to a unit, and the reader must know which one a lemma uses.

### The library around it

#### The class of Euclidean domains

The class `EuclideanDomain R` extends `CommRing R` and `Nontrivial R`. It holds two functions, `EuclideanDomain.quotient` and `EuclideanDomain.remainder`, and a relation `EuclideanDomain.r` on $R$. The axioms are the following.

1. $b \cdot q(a, b) + r(a, b) = a$ for all $a, b$, with $q(a, 0) = 0$.
2. The relation `EuclideanDomain.r` is well founded (`EuclideanDomain.r_wellFounded`).
3. For $b \ne 0$ the remainder is smaller than $b$: `EuclideanDomain.remainder_lt`.
4. For $b \ne 0$ the product $ab$ is never smaller than $a$: `EuclideanDomain.mul_left_not_lt`.

The relation replaces the usual size function $R \to \mathbb{N}$. A function to $\mathbb{N}$ gives a well founded relation, but a relation can be well founded with values in any well ordered set. So the class covers the transfinite Euclidean domains as well as the classical ones. The library gives the instances `Div R` and `Mod R`, so that `a / b` and `a % b` are the quotient and the remainder. The basic identity is `EuclideanDomain.div_add_mod`: $b (a / b) + a \% b = a$. The conventions at zero are `EuclideanDomain.div_zero` ($a / 0 = 0$) and `EuclideanDomain.mod_zero` ($a \% 0 = a$). The class gives the instance `EuclideanDomain.instIsDomain`, so a Euclidean domain is a domain.

The module `Mathlib.Algebra.EuclideanDomain.Basic` proves the arithmetic of exact division. Most of its lemmas have a hypothesis of divisibility, since $a / b$ is the true quotient only when $b \mid a$. Examples are `EuclideanDomain.mul_div_cancel'` ($b \ne 0$ and $b \mid a$ give $b (a / b) = a$), `EuclideanDomain.div_add_div_of_dvd` and `EuclideanDomain.div_pow`. The lemma `EuclideanDomain.mod_eq_zero` says $a \% b = 0 \iff b \mid a$. The definition `RingEquiv.euclideanDomain` moves the structure along a ring isomorphism.

#### The Euclidean algorithm

The function `EuclideanDomain.gcd` follows the recursion $\gcd(0, b) = b$ and $\gcd(a, b) = \gcd(b \% a, a)$ for $a \ne 0$. The second equation is `EuclideanDomain.gcd_val`. The recursion terminates because $b \% a$ is smaller than $a$ for the well founded relation. Proofs about the function follow the same recursion with `EuclideanDomain.GCD.induction`: to prove $P(a, b)$ for all $a, b$, prove $P(0, x)$ for all $x$, and prove $P(a, b)$ from $P(b \% a, a)$ when $a \ne 0$.

The extended algorithm `EuclideanDomain.xgcd` returns the pair (`EuclideanDomain.gcdA a b`, `EuclideanDomain.gcdB a b`) of Bezout coefficients. The main result is `EuclideanDomain.gcd_eq_gcd_ab`:
$$\gcd(a, b) = a \cdot \operatorname{gcdA}(a, b) + b \cdot \operatorname{gcdB}(a, b).$$
*Proof sketch.* The algorithm keeps triples $(r, s, t)$ with $r = as + bt$. It starts with $(a, 1, 0)$ and $(b, 0, 1)$. Each step replaces the pair of triples $(r, s, t)$, $(r', s', t')$ by $(r' \% r, s' - q s, t' - q t)$ and $(r, s, t)$, with $q = r' / r$. The identity $r' \% r = r' - q r$ keeps the invariant. When the first entry is $0$, the second triple holds the gcd. $\square$

The lcm is `EuclideanDomain.lcm a b`, equal to $ab / \gcd(a, b)$. The result `EuclideanDomain.gcd_mul_lcm` says $\gcd(a, b) \cdot \operatorname{lcm}(a, b) = ab$. *Proof.* The gcd divides $a$, so $ab / \gcd(a, b) = (a / \gcd(a, b)) \cdot b$ by `EuclideanDomain.mul_div_assoc`, and `EuclideanDomain.mul_div_cancel'` cancels the gcd. For $\gcd(a, b) = 0$ both sides are $0$, since then $a = b = 0$. $\square$ The usual lemmas `EuclideanDomain.gcd_dvd`, `EuclideanDomain.dvd_gcd`, `EuclideanDomain.dvd_lcm_left` and `EuclideanDomain.lcm_dvd` give the universal properties. The functions need `DecidableEq R`, since the recursion tests $a = 0$.

#### Instances

The module `Mathlib.Algebra.EuclideanDomain.Int` holds the instance `Int.euclideanDomain`. Its quotient and remainder are the integer division `a / b` and the remainder `a % b` of the Lean core, and the remainder is never negative. The relation `EuclideanDomain.r` compares absolute values. The module `Mathlib.Algebra.EuclideanDomain.Field` holds `Field.toEuclideanDomain`: in a field, $a / b$ is the field quotient and the remainder is $0$ for $b \ne 0$ (`Field.mod_eq`). The gcd in a field is trivial: `Field.gcd_eq` says that $\gcd(a, b)$ is $b$ for $a = 0$ and $a$ otherwise. The instance for $K[X]$ is in the polynomial library of Chapter 8, and the gcd monoid structure of a Euclidean domain, `EuclideanDomain.gcdMonoid`, is in `Mathlib.RingTheory.EuclideanDomain`.

#### Normalization monoids

In $\mathbb{Z}$ the gcd is made unique by the choice of the nonnegative associate. The class `NormalizationMonoid α` abstracts this choice. It holds a function `NormalizationMonoid.normUnit : α → αˣ` with $\operatorname{normUnit}(0) = 1$, $\operatorname{normUnit}(1) = 1$, and $\operatorname{normUnit}(a u) = u^{-1} \operatorname{normUnit}(a)$ for $a \ne 0$ and $u$ a unit. The normal form is `normalize x`, equal to $x \cdot \operatorname{normUnit}(x)$ by `normalize_apply`.

| Lean name | Statement |
|---|---|
| `normalize_idem` | $\operatorname{normalize}(\operatorname{normalize} x) = \operatorname{normalize} x$ |
| `normalize_eq_normalize_iff_associated` | $\operatorname{normalize} a = \operatorname{normalize} b \iff a \sim b$ |
| `associated_normalize` | $x \sim \operatorname{normalize} x$ |
| `normalize_eq_zero` | $\operatorname{normalize} x = 0 \iff x = 0$ |
| `normalize_eq_one` | $\operatorname{normalize} x = 1 \iff x$ is a unit |
| `prime_normalize_iff` | $\operatorname{normalize} x$ is prime $\iff x$ is prime |

In a general normalization monoid, `normalize` need not be multiplicative. The class `StrongNormalizationMonoid` adds this property, and then `normalize_mul` holds and `normalizeHom` is the monoid homomorphism. A normalization gives a section of the quotient map to `Associates α`: `Associates.out` picks the normalized representative, and `Associates.mk_out` says that it lies in the class. A monoid with only one unit has a unique normalization, the identity: this is the instance `instStrongNormalizationMonoid`, and `associatesEquivOfUniqueUnits` identifies the monoid with its monoid of associates.

#### Gcd monoids

The class `GCDMonoid α` holds two functions `GCDMonoid.gcd` and `GCDMonoid.lcm` with the axioms $\gcd(a, b) \mid a$, $\gcd(a, b) \mid b$, $c \mid a \wedge c \mid b \Rightarrow c \mid \gcd(a, b)$, $\operatorname{lcm}(0, a) = \operatorname{lcm}(a, 0) = 0$, and `GCDMonoid.gcd_mul_lcm`, which says that $\gcd(a, b) \operatorname{lcm}(a, b)$ is associated to $ab$. It also requires the monoid to be cancellative. The functions are exported, so a user writes `gcd a b`. The predicate `IsGCDMonoid α` says that some gcd monoid structure exists, and the instance `instDecompositionMonoidOfIsGCDMonoid` gives the decomposition property that Gauss's lemma needs.

The class `NormalizedGCDMonoid α` extends both `NormalizationMonoid α` and `GCDMonoid α` and requires the gcd and the lcm to be normalized (`normalize_gcd`, `normalize_lcm`). Only then are the identities exact equalities, not associations: `gcd_comm`, `gcd_assoc`, `gcd_one_left`, `lcm_comm`. In a normalized gcd monoid, $\gcd(0, a) = \operatorname{normalize} a$ (`gcd_zero_left`). The class `StrongNormalizedGCDMonoid` also asks for a multiplicative `normalize`, and then `gcd_mul_left` is the equality $\gcd(ab, ac) = \operatorname{normalize}(a) \gcd(b, c)$.

The result `gcd_greatest` characterizes the gcd. If $d \mid a$, $d \mid b$ and every common divisor of $a$ and $b$ divides $d$, then $\gcd(a, b) = \operatorname{normalize} d$. *Proof.* The hypotheses give $d \mid \gcd(a, b)$, and the axiom gives $\gcd(a, b) \mid d$. So the two are associated, and they have the same normal form. The gcd is normalized, so it equals $\operatorname{normalize} d$. $\square$

Two results drive many proofs in number theory. The first is `extract_gcd`: for all $x, y$ there are $x', y'$ with $x = \gcd(x, y) x'$, $y = \gcd(x, y) y'$ and $\gcd(x', y')$ a unit. The second is `exists_associated_pow_of_mul_eq_pow`: if $\gcd(a, b)$ is a unit and $ab = c^k$, then $a$ is associated to a $k$th power $d^k$. *Proof sketch.* The element $c$ divides $ab$. In a gcd monoid this gives a factorization $c = d_1 d_2$ with $d_1 \mid a$ and $d_2 \mid b$. Then $d_1^k d_2^k = ab$. The coprimality of $a$ and $b$ gives $d_1^k \mid a$, by `pow_dvd_of_mul_eq_pow`, and in the same way $d_2^k \mid b$. The two divisibilities and $d_1^k d_2^k = ab$ force $d_1^k \sim a$ in the cancellative monoid. $\square$ The lemma `gcd_isUnit_iff_isRelPrime` links the unit condition to `IsRelPrime`, and `Irreducible.gcd_eq_one_iff` says $\gcd(x, y) = 1 \iff x \nmid y$ for an irreducible $x$.

A gcd monoid can be built from less data. The constructors `gcdMonoidOfGCD` and `normalizedGCDMonoidOfGCD` take only a gcd function with its three properties and define the lcm. The constructors `gcdMonoidOfLCM` and `normalizedGCDMonoidOfLCM` do the same from an lcm. The constructors `gcdMonoidOfExistsGCD` and `gcdMonoidOfExistsLCM` take only a proof of existence and choose the function. The instance `Associates.instGCDMonoid` makes `Associates α` a gcd monoid.

#### Instances on the integers and on small types

The module `Mathlib.Algebra.GCDMonoid.Nat` holds `instStrongNormalizedGCDMonoidNat` and `Int.instStrongNormalizedGCDMonoid`. On $\mathbb{N}$ the only unit is $1$, so `normalize` is the identity, and `gcd_eq_nat_gcd` and `lcm_eq_nat_lcm` identify the monoid functions with the gcd and the lcm of the natural numbers from the Lean core. On $\mathbb{Z}$ the normalization chooses the nonnegative associate: `Int.normUnit_eq` gives $\operatorname{normUnit}(z) = 1$ for $z \ge 0$ and $-1$ otherwise, and `Int.abs_eq_normalize` says $|z| = \operatorname{normalize} z$. The gcd of the Lean core on $\mathbb{Z}$ takes values in $\mathbb{N}$, and `Int.coe_gcd` says that its cast is the monoid gcd. The lemma `Int.associated_iff` says that $a \sim b$ in $\mathbb{Z}$ if and only if $a = \pm b$, and `associatesIntEquivNat` identifies the associates of $\mathbb{Z}$ with $\mathbb{N}$. The module `Mathlib.Algebra.GCDMonoid.PUnit` gives the trivial structure on the type with one element, with `PUnit.gcd_eq`.

#### Gcd and lcm of a finite family

The module `Mathlib.Algebra.GCDMonoid.Multiset` defines `Multiset.gcd` and `Multiset.lcm` in a normalized gcd monoid, as folds of `gcd` and `lcm` with the start values $0$ and $1$. The module `Mathlib.Algebra.GCDMonoid.Finset` defines `Finset.gcd s f` and `Finset.lcm s f` for a function $f$ on a finite set $s$. The bridge is `Finset.gcd_def`: `s.gcd f` is the gcd of the multiset of values. The universal properties are `Multiset.dvd_gcd`, `Multiset.lcm_dvd`, `Finset.dvd_gcd_iff` and `Finset.lcm_dvd_iff`. The empty gcd is $0$ (`Finset.gcd_empty`) and the empty lcm is $1$ (`Finset.lcm_empty`), which are the top and the bottom of the divisibility order. The gcd of a single value is its normal form (`Finset.gcd_singleton`). The lemma `Finset.gcd_eq_zero_iff` says that the gcd is $0$ exactly when all the values are $0$, and `Finset.extract_gcd` writes each value as the gcd times a cofactor, with cofactors of gcd $1$. The lemma `Finset.gcd_eq_of_dvd_sub` says that $\gcd(a, \gcd_s f) = \gcd(a, \gcd_s g)$ when $a$ divides each $f(x) - g(x)$.

The module `Mathlib.Algebra.GCDMonoid.FinsetLemmas` compares the lcm and the product. The lcm divides the product (`Finset.lcm_dvd_prod`). The result `Finset.associated_lcm_prod` says that the lcm is associated to the product when the values are pairwise relatively prime. *Proof.* Induction on $s$. For $s = \{b\} \cup t$, the value $f(b)$ is relatively prime to each $f(x)$ with $x \in t$, so it is relatively prime to their product, and by induction to $\operatorname{lcm}_t f$. For two relatively prime elements, the gcd is a unit, so `GCDMonoid.gcd_mul_lcm` makes the lcm associated to the product. $\square$ For $\mathbb{N}$ the equality form is `Finset.lcm_eq_prod`. The lemma `Finset.Rat.den_sum_dvd_lcm_den` says that the denominator of a finite sum of rationals divides the lcm of the denominators.

#### Gcd domains are integrally closed

The module `Mathlib.Algebra.GCDMonoid.IntegrallyClosed` proves the instance `GCDMonoid.toIsIntegrallyClosed`: a domain with a gcd monoid structure is integrally closed. The key lemma is `IsLocalization.surj_of_gcd_domain`: each element $z$ of a localization $A$ of $R$ is a fraction $a / b$ with $\gcd(a, b)$ a unit. *Proof.* Write $z = x / y$ and apply `extract_gcd` to $x$ and $y$. The common factor $\gcd(x, y)$ cancels from the fraction. $\square$ The integral closure argument then follows the rational root test: if $a / b$ is a root of a monic polynomial of degree $n$, then $b \mid a^n$, and the coprimality forces $b$ to be a unit.

#### Common errors

1. `EuclideanDomain.gcd` and the monoid `gcd` are different functions. In $\mathbb{Z}$ the first can be negative, the second is never negative, and a lemma about one does not rewrite the other. Use the associations between them, or work in one structure only.
2. The equalities `gcd_comm` and `gcd_assoc` need `NormalizedGCDMonoid`. In a plain `GCDMonoid` the gcd is only defined up to a unit, and the corresponding results are `gcd_comm'` and `gcd_assoc'`, which state an association.
3. `Finset.gcd` of an empty set is $0$, not $1$. A proof by induction on a finite set must use this base case, and `Finset.gcd_eq_zero_iff` holds for the empty set with no hypothesis.

### Exercises

1. (A) Run the extended Euclidean algorithm by hand on $a = 240$ and $b = 46$ in $\mathbb{Z}$ and find integers $s, t$ with $240 s + 46 t = \gcd(240, 46)$.
2. (A) Show from the axioms of `NormalizationMonoid` that $\operatorname{normalize}(u) = 1$ for each unit $u$.
3. (A) Show that in a field with decidable equality the monoid gcd of two nonzero elements is $1$, and compare with `Field.gcd_eq`.
4. (B) Prove `Finset.associated_lcm_prod` for a set of two elements directly from `GCDMonoid.gcd_mul_lcm`.
5. (B) Let $a, b \in \mathbb{Z}$ be relatively prime with $ab = c^2$. Use `exists_associated_pow_of_mul_eq_pow` to show that $a = \pm d^2$ for some $d$, and give an example where the sign is $-1$.
6. (C) Let $R$ be a gcd domain in which each nonzero nonunit is a finite product of irreducible elements. Show that each irreducible element is prime, with `Irreducible.gcd_eq_one_iff`, and deduce that $R$ is a unique factorization domain.

### Reference

<?reference?>
