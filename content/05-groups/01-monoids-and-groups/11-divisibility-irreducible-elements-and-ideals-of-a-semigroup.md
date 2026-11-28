---
title: Divisibility, irreducible elements and ideals of a semigroup
kind: api
modules:
  - Mathlib.Algebra.Divisibility.Basic
  - Mathlib.Algebra.Divisibility.Finite
  - Mathlib.Algebra.Divisibility.Hom
  - Mathlib.Algebra.Divisibility.Prod
  - Mathlib.Algebra.Divisibility.Units
  - Mathlib.Algebra.Group.Irreducible.Defs
  - Mathlib.Algebra.Group.Irreducible.Lemmas
  - Mathlib.Algebra.Group.Ideal
explains:
  E2: [dvd_trans, mul_dvd_mul, isUnit_iff_dvd_one, IsRelPrime.dvd_of_dvd_mul_left_of_isPrimal, irreducible_mul_iff, not_irreducible_pow, Irreducible.not_isSquare, SemigroupIdeal.coe_closure']
  E1: auto
families: []
requires: [V01.C04, V02.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Divisibility, irreducible elements and ideals of a semigroup

### Overview

Divisibility makes sense in each semigroup: $a$ divides $b$ if $b = a c$ for some $c$. Volume 2 studies it for the natural numbers and the integers, with primes and greatest common divisors. The modules of this section give the general relation, before any zero or addition enters. They hold the preorder of divisibility, its interaction with units and homomorphisms, the relatively prime pairs, and the irreducible elements of a monoid. The last module defines the ideals of a semigroup: the subsets that absorb products from the left.

The results here need only a semigroup or a monoid. The facts that involve $0$, the associated elements and the prime elements are in Chapter 9, and the factorization theory of rings is in later volumes. The reader needs the units of Chapter 1, Section 5.

### The library around it

#### The relation of divisibility

**Definition (Divisibility).** Let $\alpha$ be a semigroup. Then $a \mid b$ if there is a $c$ with $b = a c$.

The instance `semigroupDvd` gives the notation `a ∣ b`, with the symbol typed as `\mid`. The lemma `dvd_def` unfolds it, `Dvd.intro` proves it from a witness, and `exists_eq_mul_right_of_dvd` and `Dvd.elim` extract the witness. The factor $c$ is on the right. In a commutative semigroup, `Dvd.intro_left` and `dvd_iff_exists_eq_mul_left` give the form $b = c a$.

**Theorem (Divisibility is a preorder).** In a semigroup, $a \mid b$ and $b \mid c$ give $a \mid c$. In a monoid, $a \mid a$.

*Proof.* If $b = a d$ and $c = b e$, then $c = a (d e)$ by associativity. In a monoid, $a = a \cdot 1$. $\square$

The lemmas are `dvd_trans` and `dvd_refl`, with the dot forms `Dvd.dvd.trans` and `dvd_rfl`. The instance `instIsPreorderDvd` records the preorder. It is not a partial order: in $\mathbb{Z}$, $2 \mid -2$ and $-2 \mid 2$. The quotient that makes it a partial order is the monoid of associated classes of Chapter 9.

The relation is compatible with products. The lemmas `dvd_mul_right` and `dvd_mul_left` state $a \mid a b$ and $a \mid b a$, the second one in a commutative semigroup. The lemma `mul_dvd_mul_left` states that $b \mid c$ gives $a b \mid a c$.

**Theorem (Products of divisors).** In a commutative semigroup, $a \mid b$ and $c \mid d$ give $a c \mid b d$.

*Proof.* Write $b = a x$ and $d = c y$. Then $b d = (a c)(x y)$ by commutativity. $\square$

The lemma is `mul_dvd_mul`. For powers, `pow_dvd_pow` states $a^m \mid a^n$ for $m \leq n$, and `pow_dvd_pow_of_dvd` states that $a \mid b$ gives $a^n \mid b^n$. The lemma `dvd_pow` states that $a \mid b$ gives $a \mid b^n$ for $n \neq 0$.

In a semigroup that is not commutative there is also a right divisibility, `RightDvd a b`, with the notation `a ∣ᵣ b`, which states $b = c a$. The lemma `rightDvd_iff_dvd` states that the two relations agree in a commutative semigroup, and `op_dvd_op_iff` exchanges them through the opposite monoid.

A homomorphism preserves divisibility, by `map_dvd`, and an isomorphism also reflects it, by `map_dvd_iff`. In a product, divisibility holds in each component: `prod_dvd_iff` for a binary product and `pi_dvd_iff` for a product of a family. On a finite semigroup with decidable equality divisibility is decidable, by the instance `instDecidableDvdOfFintypeOfDecidableEq`.

#### Units and relatively prime elements

A unit divides each element, by `IsUnit.dvd`, and a unit factor does not change divisibility, by `IsUnit.dvd_mul_right` and `IsUnit.mul_right_dvd`. The forms for an element of `αˣ` are `Units.dvd_mul_right` and `Units.coe_dvd`.

**Theorem (Units divide one).** In a commutative monoid, $x$ is a unit if and only if $x \mid 1$.

*Proof.* If $x y = 1$, then $x \mid 1$ with witness $y$. If $1 = x y$, then $y x = 1$ too by commutativity, so $x$ is a unit. $\square$

The lemma is `isUnit_iff_dvd_one`. The related lemma `isUnit_of_dvd_unit` states that a divisor of a unit is a unit, and `dvd_pow_self_iff` states $x \mid x^n$ exactly when $n \neq 0$ or $x$ is a unit.

**Definition (Relatively prime, primal).** In a monoid, $x$ and $y$ are *relatively prime* if each common divisor of $x$ and $y$ is a unit. In a semigroup, $a$ is *primal* if $a \mid b c$ gives $a = a_1 a_2$ with $a_1 \mid b$ and $a_2 \mid c$.

The predicates are `IsRelPrime x y` and `IsPrimal a`. A semigroup in which each element is primal is a `DecompositionMonoid`, by `decompositionMonoid_iff`. The integers are an example. Then `exists_dvd_and_dvd_of_dvd_mul` splits each divisor of a product.

**Theorem (Divisor of a product).** Let $\alpha$ be a commutative monoid. Let $x$ be primal, let $x$ and $y$ be relatively prime, and let $x \mid y z$. Then $x \mid z$.

*Proof.* As $x$ is primal, $x = a_1 a_2$ with $a_1 \mid y$ and $a_2 \mid z$. Then $a_1 \mid x$ and $a_1 \mid y$, so $a_1$ is a unit. So $x \mid a_2$ up to a unit factor, and $a_2 \mid z$. $\square$

The lemma is `IsRelPrime.dvd_of_dvd_mul_left_of_isPrimal`, and `IsRelPrime.dvd_of_dvd_mul_left` is the form in a `DecompositionMonoid`. The family `IsRelPrime.*` has the closure under products, `IsRelPrime.mul_left` and `IsRelPrime.mul_right`, with the forms `IsRelPrime.mul_left_iff` and `IsRelPrime.mul_right_iff`, and the passage to divisors, `IsRelPrime.of_dvd_left`. The lemma `IsRelPrime.mul_dvd` states that two relatively prime divisors of $z$ have a product that divides $z$. The lemma `isRelPrime_self` states that $x$ is relatively prime to itself exactly when $x$ is a unit.

#### Irreducible elements

**Definition (Irreducible element).** Let $M$ be a monoid. An element $p$ is *irreducible* if $p$ is not a unit and each factorization $p = a b$ has a unit factor.

The predicate is the structure `Irreducible p`, and `irreducible_iff` unfolds it. The fields are `Irreducible.not_isUnit` and `Irreducible.isUnit_or_isUnit`. The lemma `irreducible_or_factor` states that a non-unit is irreducible or a product of two non-units. The additive form is `AddIrreducible`.

**Theorem (Irreducible products).** In a monoid, $x y$ is irreducible if and only if $x$ is irreducible and $y$ is a unit, or $y$ is irreducible and $x$ is a unit.

*Proof.* If $x y$ is irreducible, then $x$ or $y$ is a unit. If $y$ is a unit, then the factorizations of $x$ and of $x y$ correspond by the factor $y$, so $x$ is irreducible. The other case is the same. The converse uses the same correspondence. $\square$

The lemma is `irreducible_mul_iff`. The lemmas `irreducible_mul_isUnit` and `irreducible_units_mul` are the special cases with a unit factor.

**Theorem (Powers and squares).** For $n \neq 1$, the power $x^n$ is not irreducible. A square is not irreducible.

*Proof.* For $n = 0$, $x^0 = 1$ is a unit. For $n \geq 2$, $x^n = x \cdot x^{n-1}$, so $x$ or $x^{n-1}$ is a unit. In both cases $x$ is a unit, and then $x^n$ is a unit, a contradiction. A square $r r$ is the case $n = 2$. $\square$

The lemmas are `not_irreducible_pow` and `Irreducible.not_isSquare`, with the dual form `IsSquare.not_irreducible`. An isomorphism preserves irreducibility, by `MulEquiv.irreducible_iff`. The prime elements and the relation between primes and irreducibles need a zero, and Chapter 9 treats them.

#### Ideals of a semigroup

**Definition (Left ideal).** Let $M$ have a product. A *left ideal* of $M$ is a subset $I$ such that $x y \in I$ for each $x \in M$ and $y \in I$.

The type is `SemigroupIdeal M`. It is an abbreviation for the sub-actions of $M$ on itself, so the lattice and the membership come from there. The closure property is `SemigroupIdeal.mul_mem`. The ideal generated by a set $s$ is `SemigroupIdeal.closure s`, with the universal property `SemigroupIdeal.closure_le`.

**Theorem (Generated ideal).** In a monoid, the ideal generated by $s$ is the set of products $y z$ with $y \in M$ and $z \in s$.

*Proof.* This set contains $s$, since $z = 1 \cdot z$. It absorbs products: $x (y z) = (x y) z$. Each ideal that contains $s$ contains these products. $\square$

The lemma is `SemigroupIdeal.coe_closure'`, and it uses the pointwise product of sets of Chapter 14. In a semigroup without identity, `SemigroupIdeal.coe_closure` adds $s$ itself to the set. A finitely generated ideal is `SemigroupIdeal.FG`, characterized by `SemigroupIdeal.fg_iff`.

#### Common errors

1. A learner types the vertical bar of the keyboard for divisibility. The symbol is `∣`, typed as `\mid`; the plain bar is not divisibility.
2. A learner applies `dvd_mul_left` in a monoid that is not commutative. The lemma needs `CommSemigroup`. The lemma `dvd_mul_right` works in each semigroup, because the witness is on the right.
3. A learner applies `dvd_antisymm` in a general monoid. Divisibility is only a preorder; in $\mathbb{Z}$, $2$ and $-2$ divide each other. The lemma needs a cancellative commutative monoid with zero whose only unit is $1$.

### Exercises

1. (A) Prove that $a \mid b$ gives $a^n \mid b^n$ in a commutative monoid, and find the name of the lemma.
2. (A) Show that $2$ is irreducible in the monoid $(\mathbb{N}, \times)$, and that $4$ is not, with `not_irreducible_pow`.
3. (B) Show that in a group each element divides each other element, and deduce that a group has no irreducible element.
4. (B) In the monoid $\{1, 2, 4, 6, 8, \dots\}$ under multiplication, show that $2$ is irreducible but not primal. Hint: $2 \mid 6 \cdot 10$.
5. (B) Prove that the left ideals of the monoid $(\mathbb{N}, +)$ are the empty set and the sets $\{n, n + 1, \dots\}$.
6. (C) Let $\alpha$ be a commutative `DecompositionMonoid`. Prove that if $x$ and $y$ are each relatively prime to $z$, then $x y$ is relatively prime to $z$. Compare your proof with the statement of `IsRelPrime.mul_left`.

### Reference

<?reference?>
