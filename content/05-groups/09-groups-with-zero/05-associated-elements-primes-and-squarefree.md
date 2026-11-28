---
title: Associated elements, primes and squarefree elements
kind: api
modules:
  - Mathlib.Algebra.GroupWithZero.Associated
  - Mathlib.Algebra.GroupWithZero.Divisibility
  - Mathlib.Algebra.GroupWithZero.Submonoid.Primal
  - Mathlib.Algebra.Prime.Defs
  - Mathlib.Algebra.Prime.Lemmas
  - Mathlib.Algebra.IsPrimePow
  - Mathlib.Algebra.Squarefree.Basic
explains:
  E2: [Associated, Associates, dvd_dvd_iff_associated, Associates.mk_eq_mk_iff_associated, Prime, Prime.irreducible, Irreducible.prime, prime_mul_iff, Squarefree, squarefree_mul_iff]
  E1: auto
families: []
requires: [V02.C02, V05.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Associated elements, primes and squarefree elements

### Overview

In the integers, $6$ and $-6$ have the same divisors and the same multiples. For questions of divisibility they are the same element. In a general commutative monoid with zero, two elements that differ by a unit factor play the same role. Mathlib calls them *associated*. The quotient by this relation is a monoid in which the only unit is $1$, and in it divisibility becomes a partial order.

The modules of this section give the divisibility theory of a commutative monoid with zero: the relation `Associated` and the quotient `Associates`, the prime elements `Prime` and their relation to the irreducible elements, the prime powers `IsPrimePow`, and the squarefree elements `Squarefree`. Volume 2 proves these facts for the natural numbers with `Nat.Prime`. This section gives the general forms, which Volume 6 and the volumes on commutative algebra use for rings and their factorization theory. The basic relation $a \mid b$ and the class `DecompositionMonoid` come from Chapter 1, Section 11.

### The library around it

#### Divisibility in a monoid with zero

The module `Mathlib.Algebra.GroupWithZero.Divisibility` gives the facts about divisibility that involve $0$. Each element divides $0$ (`dvd_zero`), and $0$ divides only $0$ (`zero_dvd_iff`). If $a \neq 0$ and multiplication by $a$ cancels, then $a b \mid a c$ if and only if $b \mid c$ (`mul_dvd_mul_iff_left`, with `mul_dvd_mul_iff_right` for the right factor). In a group with zero divisibility is almost trivial: $m \mid n$ if and only if $m = 0$ implies $n = 0$ (`GroupWithZero.dvd_iff`).

The relation `DvdNotUnit a b` says that $a \neq 0$ and $b = a x$ for a non-unit $x$. It is the strict divisibility of the theory of factorization: a strictly decreasing chain of divisors is a chain for `DvdNotUnit`. In a cancellative monoid, `dvd_and_not_dvd_iff` says that $a \mid b$ and $b \nmid a$ hold exactly when `DvdNotUnit a b` holds. For a non-unit $a \neq 0$, the powers of $a$ are strictly ordered by divisibility: $a^n \mid a^m$ if and only if $n \le m$ (`pow_dvd_pow_iff`).

When the units of $M$ are trivial and $M$ is cancellative, divisibility is antisymmetric (`dvd_antisymm`), and the instance `instIsPartialOrderDvd` makes it a partial order. The natural numbers are the main example. The relative primality `IsRelPrime` meets $0$ in `isRelPrime_zero_left`: $0$ and $x$ are relatively prime if and only if $x$ is a unit.

#### Associated elements

The definition is `Associated x y`, which says that $x u = y$ for a unit $u$ of $M$. It is an equivalence relation: `Associated.refl`, `Associated.symm` and `Associated.trans`, bundled as the setoid `Associated.setoid`. Associated elements divide each other (`Associated.dvd_dvd`). The converse needs cancellation.

**Theorem (`dvd_dvd_iff_associated`).** In a monoid with zero with left cancellation, $a \mid b$ and $b \mid a$ hold if and only if $a$ and $b$ are associated.

*Proof sketch (commutative case).* Write $b = a c$ and $a = b d$. Then $a = a (c d)$. If $a = 0$, then $b = 0$ and the two are associated by $u = 1$. If $a \neq 0$, cancellation gives $c d = 1$, so $c$ is a unit and $b = a c$. $\square$

The relation respects the structure. It is a congruence for the product (`Associated.mul_mul`, `Associated.pow_pow`), and a monoid homomorphism maps associated elements to associated elements (`Associated.map`). The lemmas that transfer a property along it have names such as `Associated.prime_iff`.

| Lean name | Statement |
|---|---|
| `associated_one_iff_isUnit` | $a \sim 1$ if and only if $a$ is a unit |
| `associated_zero_iff_eq_zero` | $a \sim 0$ if and only if $a = 0$ |
| `Associated.dvd_iff_dvd_left` | if $a \sim b$, then $a \mid c \iff b \mid c$ |
| `Associated.prime_iff` | if $p \sim q$, then $p$ is prime if and only if $q$ is prime |
| `Associated.irreducible_iff` | if $p \sim q$, then $p$ is irreducible if and only if $q$ is irreducible |
| `associated_iff_eq` | if the units are trivial, then $x \sim y \iff x = y$ |

In a cancellative monoid, a common factor $a \neq 0$ can be removed: `Associated.of_mul_left` gives $b \sim d$ from $a b \sim c d$ and $a \sim c$.

#### The monoid of associates

The type `Associates M` is the quotient of $M$ by `Associated.setoid`, and `Associates.mk` is the quotient map. The basic lemma `Associates.mk_eq_mk_iff_associated` says that $[a] = [b]$ if and only if $a \sim b$. For a commutative monoid $M$, the product of classes is well defined because the relation is a congruence, and `Associates.mk_mul_mk` gives $[x][y] = [xy]$. The instance `Associates.instCommMonoidWithZero` makes the quotient a commutative monoid with zero when $M$ is one.

The main property of the quotient is that its units are trivial: `Associates.uniqueUnits` and `Associates.isUnit_iff_eq_one`. A unit class $[u]$ is the class of $1$, because $u \sim 1$. Divisibility passes to the quotient (`Associates.mk_dvd_mk`), and so do primes and irreducible elements (`Associates.prime_mk`, `Associates.irreducible_mk`). If $M$ is cancellative, so is the quotient (`Associates.instIsCancelMulZero`). The class map is a monoid homomorphism `Associates.mkMonoidHom`. A homomorphism $f \colon M \to N$ induces `Associates.map f`, and an isomorphism induces the isomorphism `Associates.congr`.

For the integers, the class of $n$ is $\{n, -n\}$, so `Associates ℤ` is in bijection with the natural numbers. The theory of factorization in Volume 9 works in `Associates M`, because there a factorization is unique and not only unique up to units.

#### Prime and irreducible elements

The definition `Prime p` says three things: $p \neq 0$, $p$ is not a unit, and $p \mid a b$ implies $p \mid a$ or $p \mid b$. The first lemmas unpack it: `Prime.ne_zero`, `Prime.not_isUnit`, `Prime.ne_one`, `Prime.dvd_or_dvd` and `Prime.dvd_mul`. An induction on $n$ gives `Prime.dvd_of_dvd_pow`: if $p \mid a^n$, then $p \mid a$. The elements $0$ and $1$ are not prime (`not_prime_zero`, `not_prime_one`).

An irreducible element is a non-unit $p$ such that $p = a b$ forces $a$ or $b$ to be a unit. The class `Irreducible` comes from the monoid library. The two notions are related in both directions.

**Theorem (`Prime.irreducible`).** In a cancellative commutative monoid with zero, each prime is irreducible.

*Proof.* Let $p = a b$. Then $p \mid a b$, so $p \mid a$ or $p \mid b$. Say $a = p c$. Then $p = p c b$, and $p \neq 0$, so cancellation gives $c b = 1$. Thus $b$ is a unit. The other case is the same. $\square$

The converse fails in general: in $\mathbb{Z}[\sqrt{-5}]$ the element $2$ is irreducible, but it divides $(1 + \sqrt{-5})(1 - \sqrt{-5}) = 6$ and neither factor. The converse holds when the irreducible element is *primal*. An element $a$ is primal (`IsPrimal`) if $a \mid b c$ implies $a = b' c'$ with $b' \mid b$ and $c' \mid c$. The lemma `Irreducible.prime_of_isPrimal` gives the step: in $a = b' c'$ one factor is a unit, so $a$ divides $b$ or $c$. A `DecompositionMonoid` is a monoid in which each element is primal. In it `Irreducible.prime` holds, and `irreducible_iff_prime` states the equivalence. Each GCD monoid, and so each unique factorization domain, is a decomposition monoid.

The primal elements of a cancellative commutative monoid with zero form a submonoid, `Submonoid.isPrimal`. The proof is `IsPrimal.mul`, with `isPrimal_zero` and the fact that units are primal.

The module `Mathlib.Algebra.Prime.Lemmas` gives the behaviour of primes under products and maps.

| Lean name | Statement |
|---|---|
| `prime_units_mul` | $u p$ is prime if and only if $p$ is prime, for a unit $u$ |
| `MulEquiv.prime_iff` | an isomorphism preserves and reflects primes |
| `comap_prime` | if $g \circ f = \mathrm{id}$ and $f(p)$ is prime, then $p$ is prime |
| `Prime.pow_dvd_of_dvd_mul_left` | if $p \nmid a$ and $p^n \mid a b$, then $p^n \mid b$ |
| `not_prime_pow` | $a^n$ is not prime for $n \neq 1$, in a cancellative monoid |
| `Prime.not_isSquare` | a prime is not a square |
| `pow_inj_of_not_isUnit` | $q^m = q^n \iff m = n$ for a non-unit $q \neq 0$ |

The module `Mathlib.Algebra.GroupWithZero.Associated` adds the results that need both notions. In a cancellative monoid, a product is prime exactly when one factor is prime and the other is a unit.

**Theorem (`prime_mul_iff`).** In a cancellative commutative monoid with zero, $x y$ is prime if and only if $x$ is prime and $y$ is a unit, or $x$ is a unit and $y$ is prime.

*Proof sketch.* A prime is irreducible, so one factor is a unit, and the other factor is associated to $x y$, so it is prime by `Associated.prime_iff`. The converse is `prime_units_mul` and its mirror. $\square$

The same idea gives `prime_pow_iff`: $p^n$ is prime if and only if $p$ is prime and $n = 1$. Two primes that divide each other are associated (`Prime.associated_of_dvd`), and when the units are trivial they are equal (`prime_dvd_prime_iff_eq`). The divisors of a prime power are the associates of the smaller powers: `dvd_prime_pow` says that $q \mid p^n$ if and only if $q \sim p^i$ for some $i \le n$.

#### Prime powers

The predicate `IsPrimePow n` says that $n = p^k$ for a prime $p$ and $k > 0$ (`isPrimePow_def`). The form `isPrimePow_iff_pow_succ` writes $k$ as $k + 1$ for any $k$, which is often easier to use. A prime is a prime power (`Prime.isPrimePow`), a positive power of a prime power is a prime power (`IsPrimePow.pow`), and a prime power is not a unit (`IsPrimePow.not_isUnit`).

For the natural numbers, `isPrimePow_nat_iff` uses `Nat.Prime` in place of `Prime`. The divisors of a prime power that differ from $1$ are prime powers (`IsPrimePow.dvd`), and each prime power is at least $2$ (`IsPrimePow.two_le`). The bounded forms `isPrimePow_nat_iff_bounded` and `isPrimePow_nat_iff_bounded_log` bound $p$ and $k$ by $n$ and $\log_2 n$. They give the instance `instDecidableIsPrimePowNat`, so the tactic *decide* can test whether a small number is a prime power.

#### Squarefree elements

The definition `Squarefree r` says that $x x \mid r$ implies that $x$ is a unit. So $1$ is squarefree (`squarefree_one`), each unit is squarefree (`IsUnit.squarefree`), and $0$ is not squarefree in a nontrivial monoid (`not_squarefree_zero`), because $x x \mid 0$ for each $x$, and some $x$ is not a unit. An irreducible element is squarefree (`Irreducible.squarefree`), and so is a prime of a cancellative monoid (`Prime.squarefree`). A divisor of a squarefree element is squarefree (`Squarefree.squarefree_of_dvd`), so both factors of a squarefree product are squarefree (`Squarefree.of_mul_left`, `Squarefree.of_mul_right`).

**Theorem (`squarefree_mul_iff`).** In a cancellative decomposition monoid, $x y$ is squarefree if and only if $x$ and $y$ are relatively prime and both are squarefree.

*Proof sketch.* If $x y$ is squarefree and $d$ divides $x$ and $y$, then $d d \mid x y$, so $d$ is a unit: this is `IsRelPrime.of_squarefree_mul`. For the converse, let $d d \mid x y$. Since $d$ is primal, $d = d_1 d_2$ with $d_1 \mid x$ and $d_2 \mid y$, and the relative primality and the squarefree hypotheses force $d_1$ and $d_2$ to be units. $\square$

The module also relates squarefree elements to radical elements and to factorizations.

1. In a decomposition monoid a squarefree element is radical (`Squarefree.isRadical`): if $x \mid y^n$, then $x \mid y$. For $x \neq 0$ the converse holds in a cancellative monoid (`isRadical_iff_squarefree_of_ne_zero`).
2. If divisibility is well founded, then a nonzero $x$ is squarefree if and only if no square of an irreducible element divides it (`squarefree_iff_no_irreducibles`).
3. In a unique factorization monoid, each $x$ is $e^2 d$ with $d$ squarefree (`exists_sq_mul_squarefree`), and a nonzero $x$ is squarefree if and only if its normalized factors have no repetition (`UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors`).
4. In terms of multiplicity, `squarefree_iff_emultiplicity_le_one` says that each non-unit divides $r$ at most once.

For the integers, `Int.squarefree_natCast` and `Int.squarefree_natAbs` move the question to the natural numbers, where Volume 2 decides it with the factorization.

#### Common errors

1. `Prime` is the general notion of a commutative monoid with zero, and `Nat.Prime` is a separate definition for the natural numbers. The bridge `Nat.prime_iff` turns one into the other. The lemmas of this section need the general form.
2. `Associated x y` asks for $x u = y$ with the unit on the right. In a commutative monoid the side does not matter, but a rewrite with `associated_mul_unit_left` and `associated_unit_mul_left` needs the correct form.
3. `Prime.irreducible` and `prime_mul_iff` need `IsCancelMulZero`. In a ring with zero divisors a prime need not be irreducible: in $\mathbb{Z}/6$ the element $2$ is prime, but $2 = 2 \cdot 4$ and neither $2$ nor $4$ is a unit.

### Exercises

1. (A) Show that $6$ and $-6$ are associated in $\mathbb{Z}$, and that `Associates.mk 6 = Associates.mk (-6)` with `Associates.mk_eq_mk_iff_associated`.
2. (A) Prove from the definition that $0$ is not squarefree in a nontrivial monoid with zero, and that a unit is squarefree.
3. (B) Prove `Associated.prime_iff`: if $p \sim q$ and $p$ is prime, then $q$ is prime.
4. (B) Show that in a cancellative commutative monoid with zero, $p^2$ is not prime for a prime $p$, with `prime_pow_iff`.
5. (B) Prove that $2$ is prime in $\mathbb{Z}/6$ and that it is not irreducible there. Explain which hypothesis of `Prime.irreducible` fails.
6. (C) Prove that in a decomposition monoid each irreducible element is prime, starting from `Irreducible.prime_of_isPrimal`.

### Reference

<?reference?>
