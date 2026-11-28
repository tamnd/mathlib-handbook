---
title: The characteristic of algebras, quotients and products
kind: api
modules:
  - Mathlib.Algebra.CharP.Basic
  - Mathlib.Algebra.CharP.Algebra
  - Mathlib.Algebra.CharP.Subring
  - Mathlib.Algebra.CharP.IntermediateField
  - Mathlib.Algebra.CharP.Pi
  - Mathlib.Algebra.CharP.Synonym
  - Mathlib.Algebra.CharP.LinearMaps
  - Mathlib.Algebra.CharP.Quotient
  - Mathlib.Algebra.CharP.CharAndCard
  - Mathlib.Algebra.CharP.LocalRing
  - Mathlib.Algebra.CharP.MixedCharZero
  - Mathlib.Algebra.CharP.Invertible
  - Mathlib.Algebra.CharP.Two
  - Mathlib.Algebra.CharZero.AddMonoidHom
  - Mathlib.Algebra.CharZero.Infinite
  - Mathlib.Algebra.CharZero.Quotient
explains:
  E2: [CharP.natCast_eq_natCast, RingHom.charP_iff, Prod.charP, CharP.quotient_iff, charP_of_card_eq_prime, charP_zero_or_prime_power, split_by_characteristic, CharP.isUnit_natCast_iff, CharTwo.add_sq]
  E1: auto
families: []
requires: [V06.C01, V06.C02, V06.C03, V02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The characteristic of algebras, quotients and products

### Overview

Section 1 defined the characteristic of a ring with the class `CharP R p` and proved its main properties. In practice the characteristic of a ring is rarely computed from the definition. It comes from a ring that is already known: the ring is a subring, a quotient, a product, an algebra over a field, or a ring of linear maps. The modules of this section supply these transfers as lemmas and instances, so that instance search finds `CharP` on most constructions with no work from the user.

The section also collects three further groups of results. The first group relates the characteristic to the cardinality of a finite ring and to the units of the form $n \cdot 1$. The second group splits the commutative rings into the cases of equal characteristic $p$, equal characteristic zero and mixed characteristic, which is the first step of many proofs in commutative algebra. The third group is the arithmetic of characteristic $2$, where $-1 = 1$ and squaring is additive.

### The library around it

#### Casts of natural numbers and integers

The basic computation in characteristic $p$ is the reduction of the casts. In `Mathlib.Algebra.CharP.Basic` the lemma `CharP.natCast_eq_natCast` says that for $a, b \in \mathbb{N}$,
$$(a : R) = (b : R) \iff a \equiv b \pmod p,$$
under the hypothesis `IsRightCancelAdd R`, which holds in every ring. The proof: if $a \le b$, then $b = a + (b - a)$, so $(a : R) = (b : R)$ if and only if $(b - a : R) = 0$ after cancellation of $a$, and by the definition of `CharP` this holds if and only if $p \mid b - a$. The forms `CharP.natCast_eq_natCast_mod` and `CharP.intCast_eq_intCast_mod` replace a cast by the cast of the remainder, and `CharP.intCast_eq_intCast` is the form for integers with `Int.ModEq`. The lemma `CharP.natCast_injOn_Iio` says that the cast is injective on $\{0, \dots, p - 1\}$.

For a prime $p$ the characteristic is determined by one equation: `CharP.charP_iff_prime_eq_zero` says that in a nontrivial semiring `CharP R p ↔ (p : R) = 0`, and `CharP.ringChar_of_prime_eq_zero` gives `ringChar R = p` from the same equation. The reason is that the characteristic divides $p$ and is not $1$. A domain has characteristic zero exactly when no prime is zero in it: this is `CharZero.charZero_iff_forall_prime_ne_zero`. The lemmas `Ring.two_ne_zero` and `Ring.neg_one_ne_one_of_char_ne_two` give $2 \ne 0$ and $-1 \ne 1$ from `ringChar R ≠ 2`.

#### Transfer along homomorphisms and algebras

An injective ring homomorphism $f : R \to A$ preserves and reflects the characteristic, since $f(n \cdot 1) = n \cdot 1$ and $f$ has zero kernel. This is `RingHom.charP_iff`: for injective $f$, `CharP R p ↔ CharP A p`. The two directions are `charP_of_injective_ringHom` and `RingHom.charP`, and `charZero_of_injective_ringHom` and `RingHom.expChar_iff` are the forms for `CharZero` and `ExpChar`. With no injectivity there is still a relation: `CharP.dvd_of_ringHom` says that the characteristic of $A$ divides that of $R$.

For algebras the lemmas take the injectivity of `algebraMap R A` as hypothesis, as in `charP_of_injective_algebraMap`, or the class `FaithfulSMul R A`, as in `charP_of_injective_algebraMap'`. A ring homomorphism out of a division ring is injective, so `RingHom.charP_iff_charP` needs no hypothesis, and for an algebra $L$ over a field $K$ the lemma `Algebra.charP_iff` gives `CharP K p ↔ CharP L p` and `Algebra.ringChar_eq` gives `ringChar K = ringChar L`. A nontrivial $\mathbb{Q}$-algebra has characteristic zero (`algebraRat.charZero`). The field of fractions of a domain has the characteristic of the domain, by the instances `IsFractionRing.charP` and `IsFractionRing.charZero`, and the free algebra over $R$ has the characteristic of $R$ (`FreeAlgebra.charP`).

#### Subrings, products and type synonyms

A subsemiring contains $1$ and is closed under addition, so it has the characteristic of the ambient ring. The instance `instCharPSubtypeMem` covers each class of subobjects with `SubsemiringClass`, and `SubsemiringClass.charP_iff` states the equivalence. The center of a ring is a subring, so it has the characteristic of the ring. The instances `Subfield.charP` and `IntermediateField.charP` treat subfields and intermediate fields; for an intermediate field $L$ of $E / F$, both the characteristic of $F$ (`IntermediateField.charP`) and that of $E$ (`IntermediateField.charP'`) pass to $L$.

For products the characteristic is a least common multiple. The instance `Prod.charP` gives `CharP (R × S) p` when both factors have characteristic $p$. The proof: $(n, n) = 0$ in $R \times S$ if and only if $p \mid n$ in both coordinates. The general instance `Nat.lcm.charP` gives the characteristic $\operatorname{lcm}(p, q)$ when the factors have characteristics $p$ and $q$. One factor of characteristic zero is enough for `CharZero (R × S)`, by `Prod.charZero_of_left` and `Prod.charZero_of_right`. For a nonempty family of rings with the same characteristic, `Pi.instCharP` gives the characteristic of the product $\prod_i R_i$, and `CharZero.pi` says that one factor of characteristic zero makes the product of characteristic zero. The ring `Fin n` of residues has characteristic $n$ (`Fin.charP`), and the opposite ring and `ULift` keep the characteristic (`MulOpposite.charP`, `ULift.charP`). The order synonyms `Rᵒᵈ` and `Lex R` have the characteristic of `R` (`OrderDual.instCharP`, `Lex.instCharP`, `OrderDual.ringChar_eq`).

The ring of linear maps $M \to M$ of an $R$-module has the characteristic of $R$ when $M$ has an element with zero annihilator, by `Module.charP_end`. For a division ring $D$ this gives the instance on the linear maps of $D$ over its center.

#### Quotients

Let $I$ be an ideal of a commutative ring $R$ of characteristic $n$. The quotient $R/I$ can have a smaller characteristic, since more natural numbers can lie in $I$. The lemma `CharP.quotient_iff` says
$$\operatorname{CharP}(R/I, n) \iff \text{for all } x \in \mathbb{N},\ (x : R) \in I \implies (x : R) = 0.$$
The proof is direct: $(x : R/I) = 0$ means $(x : R) \in I$, and $(x : R) = 0$ means $n \mid x$. The form `CharP.quotient_iff_le_ker_natCast` states the condition with the kernel of `Nat.castRingHom R`. For a prime $p$ that is not a unit in $R$, `CharP.quotient` gives the characteristic $p$ to $R / (p)$. In the other direction, `Ideal.natCast_mem_of_charP_quotient` says that $p \in I$ when $R/I$ has characteristic $p$, and `CharP.ker_intAlgebraMap_eq_span` says that the kernel of $\mathbb{Z} \to R$ is the ideal $(p)$.

The module `Mathlib.Algebra.CharZero.Quotient` studies the circle-like quotient $R / p\mathbb{Z}$ of a division ring of characteristic zero. The lemma `QuotientAddGroup.zmultiples_nsmul_eq_nsmul_iff` says that for $n \ne 0$ the equation $n \psi = n \theta$ holds in $R / p\mathbb{Z}$ if and only if $\psi = \theta + k (p/n)$ for some integer $k$. For $R = \mathbb{R}$ and $p = 2\pi$ this describes the angles $\theta$ with $n\theta$ given. The integer form is `QuotientAddGroup.zmultiples_zsmul_eq_zsmul_iff`.

#### Finite rings and local rings

A finite ring has a nonzero characteristic, and the characteristic is related to the cardinality. The lemma `charP_of_card_eq_prime` says that a ring with $p$ elements, $p$ prime, has characteristic $p$. The proof: the characteristic is the order of $1$ in the additive group, and by Lagrange's theorem it divides $p$; it is not $1$ because the ring has more than one element. For a domain with $p^f$ elements, `charP_of_card_eq_prime_pow` gives the characteristic $p$. In a finite commutative ring the same primes divide the characteristic and the cardinality (`prime_dvd_char_iff_dvd_card`), and $(p : R)$ is a unit if and only if $p$ does not divide the characteristic (`isUnit_iff_not_dvd_char`).

A local ring has characteristic zero or a prime power: this is `charP_zero_or_prime_power`. The proof writes the characteristic $q$ as $q = p^k m$ with $p \nmid m$ and $k \ge 1$ if $q \ne 0$ and not $1$. If $m > 1$, the elements $p^k$ and $m$ of $R$ are both nonzero, and their product is $0$. In a local ring one of two elements whose sum is a unit is a unit, and the Bézout relation $a p^k + b m = 1$ makes one of $p^k$ and $m$ a unit, which contradicts the product being $0$.

#### Equal and mixed characteristic

A commutative ring $R$ of characteristic zero can have quotients of characteristic $p$, as $\mathbb{Z} \to \mathbb{Z}/p$ shows. The class `MixedCharZero R p` records this: $R$ has characteristic zero and some proper ideal $I$ has `CharP (R ⧸ I) p`. The lemma `MixedCharZero.reduce_to_maximal_ideal` says that the ideal can be taken maximal when $p$ is prime. A ring of characteristic zero with no such quotient is of equal characteristic zero, and `EqualCharZero.nonempty_algebraRat_iff` says that this is the case if and only if $R$ is a $\mathbb{Q}$-algebra. The theorem `split_by_characteristic` puts the cases together: to prove a statement $P$ about $R$, it suffices to prove $P$ when $R$ has characteristic $p \ne 0$, when $R$ is a $\mathbb{Q}$-algebra, and when $R$ has mixed characteristic $(0, p)$ for a prime $p$. The variants `split_by_characteristic_domain` and `split_by_characteristic_localRing` restrict the first case to a prime $p$ and to a prime power $p$.

#### Invertible natural numbers

The natural number $n$ is a unit in a ring of prime characteristic $p$ exactly when $p \nmid n$. This is `CharP.isUnit_natCast_iff`, with the forms `CharP.isUnit_intCast_iff` and `CharP.isUnit_ofNat_iff`. The proof of the backward direction: if $p \nmid n$, then $\gcd(n, p) = 1$, and the Bézout coefficient $a$ with $a n \equiv 1 \pmod p$ gives $a \cdot n = 1$ in $R$. The lemmas `CharP.natCast_gcdA_mul_intCast_eq_gcd` and `invOf_eq_of_coprime` make the inverse explicit with `Nat.gcdA`. The definitions `invertibleOfCoprime` and `invertibleOfCharPNotDvd` build the data `Invertible (n : R)`, and in characteristic zero the instances `invertibleTwo`, `invertibleThree` and `invertibleOfPos` provide it for each positive $n$. When $2$ is invertible, each element is even, $a = a/2 + a/2$, and `Even.all` and `Odd.all` say so.

#### Characteristic two

The module `Mathlib.Algebra.CharP.Two` has the namespace `CharTwo`. In characteristic $2$ the equalities $2 = 0$ (`CharTwo.two_eq_zero`), $x + x = 0$ (`CharTwo.add_self_eq_zero`), $-x = x$ (`CharTwo.neg_eq`) and $x - y = x + y$ (`CharTwo.sub_eq_add`) hold. In a commutative semiring the square is additive:
$$(x + y)^2 = x^2 + 2xy + y^2 = x^2 + y^2,$$
which is `CharTwo.add_sq`. The lemma `CharTwo.sum_sq` extends it to finite sums, and `CharTwo.list_sum_sq` and `CharTwo.multiset_sum_sq` to lists and multisets. With no zero divisors, squaring is injective (`CharTwo.sq_injective`), because $x^2 = y^2$ gives $(x + y)^2 = 0$. The cast of an integer is $0$ or $1$ by parity (`CharTwo.intCast_eq_ite`). The lemma `neg_one_eq_one_iff` characterizes the characteristic $2$ in a nontrivial ring by the equation $-1 = 1$.

#### Two small facts on characteristic zero

A monoid with one of characteristic zero is infinite, by the instance `CharZero.infinite`, since $n \mapsto n \cdot 1$ is injective. The lemma `CharZero.of_addMonoidHom` transfers `CharZero` along an injective additive map that sends $1$ to $1$.

#### Common errors

1. `CharP.natCast_eq_natCast` has the hypothesis `IsRightCancelAdd R`. In a ring instance search provides it, but in a semiring with no cancellation of addition the lemma does not apply.
2. `CharP.quotient` needs a prime $p$ that is not a unit of $R$. If $p$ is a unit, the ideal $(p)$ is the whole ring, and the quotient is the zero ring, which has characteristic $1$.
3. `charP_of_card_eq_prime_pow` needs a domain. The ring $\mathbb{Z}/4$ has $2^2$ elements and characteristic $4$.

### Exercises

1. (A) Use `Prod.charP` and `Nat.lcm.charP` to find the characteristic of $\mathbb{Z}/4 \times \mathbb{Z}/6$.
2. (A) Prove `CharTwo.add_sq` from the binomial expansion and `CharTwo.two_eq_zero`, and deduce that $x \mapsto x^2$ is a ring homomorphism of a commutative ring of characteristic $2$.
3. (A) Show with `CharP.quotient_iff` that $\mathbb{Z}[i] / (3)$ has characteristic $3$.
4. (B) Show that a ring with $p$ elements, $p$ prime, is isomorphic to $\mathbb{Z}/p$. Hint: use `charP_of_card_eq_prime` and the map $\mathbb{Z}/p \to R$.
5. (B) Show that $\mathbb{Z}_{(p)}$, the integers localized at a prime $p$, has mixed characteristic $(0, p)$, and that $\mathbb{Z}/6$ is not a local ring with the help of `charP_zero_or_prime_power`.
6. (C) Let $R$ be a commutative ring of characteristic zero in which every nonzero integer is a unit. Construct a $\mathbb{Q}$-algebra structure on $R$, and compare with `EqualCharZero.nonempty_algebraRat_iff`.

### Reference

<?reference?>
