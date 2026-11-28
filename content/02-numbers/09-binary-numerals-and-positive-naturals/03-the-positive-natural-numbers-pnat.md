---
title: The positive natural numbers ℕ+
kind: api
modules:
  - Mathlib.Data.PNat.Defs
  - Mathlib.Data.PNat.Basic
  - Mathlib.Data.PNat.Notation
  - Mathlib.Data.PNat.Equiv
  - Mathlib.Data.PNat.Find
  - Mathlib.Data.PNat.Interval
  - Mathlib.Data.PNat.Order
  - Mathlib.Data.PNat.Factors
  - Mathlib.Data.PNat.Prime
  - Mathlib.Data.PNat.Xgcd
explains:
  E2: [PNat.coe_inj, PNat.add_coe, PNat.mul_coe, PNat.sub_coe, PNat.recOn, PNat.find_spec, PNat.gcd_coe, PNat.prod_factorMultiset, PNat.factorMultiset_le_iff, PNat.gcd_props]
  E1: auto
families: []
requires: [V01.C02, V01.C05, V02.C01, V02.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The positive natural numbers ℕ+

### Overview

Many statements are about positive numbers only: the denominator of a fraction, the order of an element of a group, the period of a sequence, the modulus of a congruence. With the type `ℕ`, each such statement carries a hypothesis $0 < n$. The type `ℕ+` puts this hypothesis into the type. It is the subtype $\{n : \mathbb{N} \mid 0 < n\}$, with the name `PNat` and the notation `ℕ+`. A term of `ℕ+` is a pair of a natural number and a proof that it is positive.

The structure on `ℕ+` comes from `ℕ` through the coercion `PNat.val`. Addition, multiplication, the order and divisibility in `ℕ+` are the restrictions of the same operations on `ℕ`. The main lemmas say that the coercion is injective and that it respects these operations. Subtraction and division do not restrict, because a difference or a quotient of positive numbers can be zero. For them `ℕ+` has special definitions, and these are the first source of errors.

The modules are `Mathlib.Data.PNat.Notation` (the type and the coercion), `Mathlib.Data.PNat.Defs` (the conversions from `ℕ`, the order, division with remainder), `Mathlib.Data.PNat.Basic` (the algebraic structure and the induction principles), `Mathlib.Data.PNat.Equiv` (the bijection with `ℕ`), `Mathlib.Data.PNat.Find` (the least positive number with a property), `Mathlib.Data.PNat.Interval` (finite intervals), `Mathlib.Data.PNat.Prime` (gcd, lcm, primes and coprimality), `Mathlib.Data.PNat.Factors` (the multiset of prime factors) and `Mathlib.Data.PNat.Xgcd` (an extended Euclidean algorithm that stays in `ℕ`). The module `Mathlib.Data.PNat.Order` has no declarations of its own. The subtypes of Chapter 2 of Volume 1 and the divisibility of Chapter 2 of this volume are the background.

### The library around it

#### The type and the coercion to `ℕ`

The type `PNat` is defined in `Mathlib.Data.PNat.Notation` as a subtype of `ℕ`, and `PNat.val` is the projection. The instance `coePNatNat` makes `PNat.val` the coercion, so `(n : ℕ)` for `n : ℕ+` is the underlying number. The equality of `ℕ+` is decidable (`instDecidableEqPNat`).

The basic facts are `PNat.pos`, which says that $0 < \uparrow n$, and `PNat.ne_zero`, which says that $\uparrow n \ne 0$. The coercion is injective: `PNat.coe_injective` is the statement as a function, `PNat.coe_inj` is the equivalence $\uparrow m = \uparrow n \leftrightarrow m = n$, and `PNat.eq` is the implication from right to left. The order is the order of `ℕ` (`instLinearOrderPNat`), and `PNat.coe_le_coe` and `PNat.coe_lt_coe` transfer it. A term with an explicit proof, $\langle n, h \rangle$, has the coercion `PNat.mk_coe`, and the order of two such terms is `PNat.mk_le_mk`.

A numeral such as $5$ is a term of `ℕ+` through the instance `instOfNatPNatOfNeZeroNat`, which needs a proof that the numeral is not zero. The instance search finds this proof for each literal except $0$. The lemma `PNat.val_ofNat` gives the coercion of a numeral, and `PNat.one_coe` is the case of $1$. The element $1$ is the least element, so `ℕ+` is an order with a bottom (`PNat.instOrderBot`, `PNat.bot_eq_one`).

#### The conversions from `ℕ`

There are three ways to make a term of `ℕ+` from a natural number.

| Function | Value | Use |
|---|---|---|
| `Nat.toPNat` | $n$, with a proof of $0 < n$ as an argument | when the proof is available |
| `Nat.succPNat` | $n + 1$ | to send `ℕ` onto `ℕ+` with a shift |
| `Nat.toPNat'` | $n$ if $0 < n$, and $1$ if $n = 0$ | a total function with a junk value |

The function `Nat.toPNat'` uses the method of junk values of Chapter 5 of Volume 1: its value at $0$ is $1$ (`Nat.toPNat'_zero`), and `Nat.toPNat'_coe` gives the coercion of the result. In the other direction, `PNat.natPred` sends $n$ to $n - 1$. The lemmas `Nat.succPNat_coe`, `PNat.succPNat_natPred` and `Nat.natPred_succPNat` say that `Nat.succPNat` and `PNat.natPred` are inverse bijections. The module `Mathlib.Data.PNat.Equiv` packs them as the equivalence `Equiv.pnatEquivNat`, and `Mathlib.Data.PNat.Basic` gives the order isomorphism `OrderIso.pnatIsoNat`.

To change a variable of `ℕ` into a variable of `ℕ+`, use the tactic *lift* with the instance `Nat.canLiftPNat`. For `n : ℕ` and a hypothesis `hn : 0 < n`, the command *lift n to ℕ+ using hn* replaces $n$ by the coercion of a new variable of type `ℕ+`. The instance `Int.canLiftPNat` does the same for an integer that is positive.

#### Arithmetic and the algebraic structure

Addition and multiplication restrict from `ℕ`, and the coercion respects them:

$$\uparrow(m + n) = \uparrow m + \uparrow n, \qquad \uparrow(m n) = \uparrow m \cdot \uparrow n, \qquad \uparrow(m^k) = (\uparrow m)^k.$$

These are `PNat.add_coe`, `PNat.mul_coe` and `PNat.pow_coe`. The coercion is a monoid homomorphism `PNat.coeMonoidHom` and an additive homomorphism `PNat.coeAddHom` without zero, because `ℕ+` has no zero. The instances are `instCommMonoidPNat`, `instAddCommSemigroupPNat`, `instDistribPNat` and the order instance `instIsOrderedCancelMonoidPNat`. The type `ℕ+` is not a semiring, because it has no $0$. So a lemma about semirings does not apply to `ℕ+`, and the usual method is to go to `ℕ` with the coercion.

Subtraction on `ℕ+` is truncated at $1$: the value of $a - b$ is $\uparrow a - \uparrow b$ if $b < a$ and $1$ in the other case. This is `PNat.sub_coe`. The lemmas `PNat.add_sub_of_lt` and `PNat.sub_add_of_lt` give the usual identities when $b < a$, and `PNat.add_sub` gives $(a + b) - b = a$ in all cases.

Division with remainder has a special form. For $m, k$ in `ℕ+`, the functions `PNat.mod` and `PNat.div` give a remainder $r$ in $\{1, \dots, k\}$ and a quotient $q$ in `ℕ` with $r + k q = m$ (`PNat.mod_add_div`). The remainder is $k$, not $0$, when $k$ divides $m$ (`PNat.mod_coe`, `PNat.div_coe`), and `PNat.dvd_iff'` says that $k \mid m$ exactly when the remainder is $k$. For a divisor $k$ of $m$, the function `PNat.divExact` gives the quotient as a term of `ℕ+`, with `PNat.mul_div_exact`.

Divisibility restricts from `ℕ` (`PNat.dvd_iff`). Since all the elements are positive, divisibility is a partial order: `PNat.le_of_dvd` gives $m \le n$ from $m \mid n$, and `PNat.dvd_antisymm` gives $m = n$ from $m \mid n$ and $n \mid m$. The only divisor of $1$ is $1$ (`PNat.dvd_one_iff`).

#### Induction and the least element

The order on `ℕ+` is well founded (`instWellFoundedLTPNat`), and the module `Mathlib.Data.PNat.Basic` gives three induction principles. The function `PNat.recOn` is induction from $1$: from a value at $1$ and a step from $n$ to $n + 1$, it gives a value at each $n$, with the equations `PNat.recOn_one` and `PNat.recOn_succ`. The function `PNat.strongInductionOn` is strong induction, and `PNat.caseStrongInductionOn` combines a case at $1$ with a strong step. The lemma `PNat.exists_eq_succ_of_ne_one` is the case analysis: each $n \ne 1$ is $k + 1$ for some $k$ in `ℕ+`.

The module `Mathlib.Data.PNat.Find` gives the least positive number with a decidable property $p$, if one exists. For a proof $h$ of $\exists n, p(n)$, the term `PNat.find h` is this number. The lemma `PNat.find_spec` says that $p$ holds at it, and `PNat.find_min` and `PNat.find_min'` say that it is the least such number. The characterizations `PNat.find_eq_iff`, `PNat.find_le_iff` and `PNat.lt_find_iff` change a statement about `PNat.find h` into a statement about $p$, and `PNat.find_eq_one` covers the case where $p$ holds at $1$.

#### Intervals

The instance `PNat.instLocallyFiniteOrder` makes the intervals of `ℕ+` finite sets. The lemmas `PNat.Icc_eq_finset_subtype` and `PNat.map_subtype_embedding_Icc` connect an interval of `ℕ+` with the same interval of `ℕ`, and the lemmas for the other three kinds of interval have the same form. The numbers of elements are `PNat.card_Icc` ($b + 1 - a$), `PNat.card_Ico` and `PNat.card_Ioc` ($b - a$) and `PNat.card_Ioo` ($b - a - 1$), all computed in `ℕ` with truncated subtraction.

#### Gcd, lcm, primes and coprimality

The functions `PNat.gcd` and `PNat.lcm` take values in `ℕ+`, since the gcd and the lcm of positive numbers are positive. The lemmas `PNat.gcd_coe` and `PNat.lcm_coe` say that they are the gcd and the lcm in `ℕ`. The usual properties are `PNat.gcd_dvd_left`, `PNat.gcd_dvd_right`, `PNat.dvd_gcd`, `PNat.dvd_lcm_left`, `PNat.lcm_dvd` and `PNat.gcd_mul_lcm`, which says that $\gcd(m, n) \cdot \mathrm{lcm}(m, n) = m n$.

The predicate `PNat.Prime` is the primality of the coercion in the sense of `Nat.Prime`. The lemmas `PNat.Prime.one_lt`, `PNat.dvd_prime` and `PNat.exists_prime_and_dvd` are the forms for `ℕ+` of the lemmas for `ℕ`, and `PNat.prime_two`, `PNat.prime_three` and `PNat.prime_five` are the small cases. The predicate `PNat.Coprime` is the statement $\gcd(m, n) = 1$, and `PNat.coprime_coe` says that it agrees with the coprimality of the coercions. The lemmas `PNat.Coprime.mul`, `PNat.Coprime.mul_right` and `PNat.Coprime.gcd_mul` are the usual rules.

#### The multiset of prime factors

The module `Mathlib.Data.PNat.Factors` gives a form of the fundamental theorem of arithmetic with a clean bijection. The type `PrimeMultiset` is the type of finite multisets of primes. The function `PrimeMultiset.prod` takes the product, which is in `ℕ+`, and `PNat.factorMultiset` takes the multiset of prime factors of a positive number. Each function is the inverse of the other: `PNat.prod_factorMultiset` says that $n$ is the product of its prime factors, and `PrimeMultiset.factorMultiset_prod` says that the prime factors of a product of primes are those primes. The equivalence is `PNat.factorMultisetEquiv`. The number $1$ goes to the empty multiset, and there is no number $0$ to exclude, which is the reason to state the theorem on `ℕ+`.

The bijection changes the multiplicative structure into the additive structure of multisets. Products go to sums (`PNat.factorMultiset_mul`), powers to multiples (`PNat.factorMultiset_pow`), divisibility to the order of multisets (`PNat.factorMultiset_le_iff`), the gcd to the infimum (`PNat.factorMultiset_gcd`) and the lcm to the supremum (`PNat.factorMultiset_lcm`). The lemma `PNat.count_factorMultiset` says that $p^k \mid m$ exactly when $p$ has multiplicity at least $k$ in the multiset of $m$. The lemma `PNat.coeNat_factorMultiset` connects the multiset with the list `Nat.primeFactorsList` of Chapter 2 of this volume.

#### The extended Euclidean algorithm in `ℕ`

The usual extended Euclidean algorithm gives integers $x, y$ with $a x + b y = \gcd(a, b)$, and one of them is negative. The module `Mathlib.Data.PNat.Xgcd` gives a form that stays in `ℕ`. For positive $a$ and $b$ with $d = \gcd(a, b)$, it computes numbers $w, z$ in `ℕ+` and $x, y$ in `ℕ` with

$$a = (w + x) d, \qquad b = (y + z) d, \qquad w z = x y + 1.$$

The values are `PNat.gcdW`, `PNat.gcdX`, `PNat.gcdY`, `PNat.gcdZ` and `PNat.gcdD`, and `PNat.gcd_eq` says that `PNat.gcdD` is `PNat.gcd`. The lemma `PNat.gcd_props` states all the identities together, and `PNat.gcd_rel_left` and `PNat.gcd_rel_right` give the Bezout forms $z a = x b + d$ and $w b = y a + d$. The quotients $a / d = w + x$ and $b / d = y + z$ are `PNat.gcdA'` and `PNat.gcdB'`, and the identity $w z = x y + 1$ shows that they are coprime. The algorithm itself works on the record type `PNat.XgcdType`, with the step `PNat.XgcdType.step` and the loop `PNat.XgcdType.reduce`. These are internal, and the lemmas about `PNat.gcdD` and its companions are the interface.

#### Common errors

1. The wrong subtraction or remainder. In `ℕ+`, the value of $3 - 5$ is $1$ and the remainder of $6$ by $3$ is $3$. A proof that uses the rules of `ℕ` without a check of these cases fails. Prefer to go to `ℕ` with `PNat.sub_coe` or `PNat.mod_coe`, where the cases are explicit.
2. Lemmas about semirings do not apply. The type `ℕ+` has no $0$, so it is not a semiring, and a rewrite with a lemma that needs a zero or a semiring fails to find an instance. Lemmas about monoids and about distributive structures, such as `mul_add`, apply. For other statements, rewrite with `PNat.coe_inj` and the lemmas `PNat.add_coe` and `PNat.mul_coe`, and prove the statement in `ℕ`.
3. A hypothesis $0 < n$ that is not used. To work in `ℕ+` with a natural number $n$, do not use `Nat.toPNat'`, whose value at $0$ is a junk value. Use the tactic *lift* with the hypothesis, and the proof keeps the information that $n$ is positive.

### Exercises

1. (A) For $m, n$ in `ℕ+`, prove that $m < m + n$ with `PNat.coe_lt_coe` and `PNat.add_coe`. Then find the lemma of the library that states it.
2. (A) Compute the values of $7 - 3$, $3 - 7$, the remainder of $12$ by $4$ and the remainder of $13$ by $4$ in `ℕ+`. Use `PNat.sub_coe` and `PNat.mod_coe`.
3. (B) Prove that `Nat.succPNat` and `PNat.natPred` are inverse bijections, and that they respect the order. Compare with `Equiv.pnatEquivNat` and `OrderIso.pnatIsoNat`.
4. (B) Let $p$ be the property "$n^2 > 20$" on `ℕ+`. Prove that $p$ holds at some $n$, and find the value of `PNat.find` with `PNat.find_eq_iff`.
5. (B) Use `PNat.factorMultiset_le_iff` and `PNat.factorMultiset_gcd` to prove that $k \mid \gcd(m, n)$ exactly when $k \mid m$ and $k \mid n$, without the lemma `PNat.dvd_gcd`.
6. (C) From the identities $a = (w + x) d$, $b = (y + z) d$ and $w z = x y + 1$ of `PNat.gcd_props`, prove that $z a = x b + d$, and deduce that each common divisor of $a$ and $b$ divides $d$.

### Reference

<?reference?>
