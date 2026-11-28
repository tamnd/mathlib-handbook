---
title: Units, invertible elements and commuting elements
kind: api
modules:
  - Mathlib.Algebra.Group.Units.Basic
  - Mathlib.Algebra.Group.Units.Opposite
  - Mathlib.Algebra.Group.Invertible.Defs
  - Mathlib.Algebra.Group.Invertible.Basic
  - Mathlib.Algebra.Group.Commute.Basic
  - Mathlib.Algebra.Group.Commute.Units
  - Mathlib.Algebra.Group.Commute.Hom
  - Mathlib.Algebra.Group.Semiconj.Defs
  - Mathlib.Algebra.Group.Semiconj.Basic
  - Mathlib.Algebra.Group.Semiconj.Units
explains:
  E2: [Commute.isUnit_mul_iff, isUnit_pow_iff, Units.ofPowEqOne, nonempty_invertible_iff_isUnit, invOf_mul, SemiconjBy.mul_right, Commute.inv_right]
  E1: auto
families: []
requires: [V01.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Units, invertible elements and commuting elements

### Overview

Section 2 of this chapter defines the group $M^\times$ of units of a monoid $M$ and the predicate `IsUnit`. This section gives the library that a reader uses to compute with units. It has three parts. The first part is the cancellation and division lemmas for units and for elements that are units. The second part is the class `Invertible a`, which carries a chosen inverse of one element. The third part is the theory of commuting and semiconjugate elements: the relation $a x = y a$, its behaviour under products, inverses and powers, and its images under homomorphisms.

The three parts meet in one result. In a monoid a product $a b$ can be a unit when $a$ and $b$ are not units. When $a$ and $b$ commute this cannot happen: $a b$ is a unit exactly when $a$ and $b$ are units. So a power $a^n$ with $n \neq 0$ is a unit exactly when $a$ is a unit, and an element with $a^n = 1$ is a unit.

### The library around it

#### Units and the lemmas on IsUnit

The module `Mathlib.Algebra.Group.Units.Basic` gives the identities that hold in a group for all elements, but in a monoid only for units. There are two forms. The first form takes a unit `u : Mˣ` and states the identity for its value `↑u`: `Units.mul_left_inj` is $b u = c u \iff b = c$, `Units.mul_inv_eq_one` is $a u^{-1} = 1 \iff a = u$, and `Units.mul_inv_eq_iff_eq_mul` is $a u^{-1} = c \iff a = c u$. The second form takes an element `a : M` with a proof `h : IsUnit a`, and is used with dot notation: `h.mul_left_inj`, `h.mul_right_cancel`, `h.mul_eq_one_iff_eq_inv`. The lemmas of the second form that contain $a^{-1}$ or $a / b$ need a `DivisionMonoid`, so that the inverse $a^{-1}$ makes sense for all $a$; a group with zero is the main example.

| Lean name | Statement |
|---|---|
| `IsUnit.mul_right_inj` | for a unit $a$: $a b = a c \iff b = c$ |
| `IsUnit.mul_eq_right` | for a unit $b$: $a b = b \iff a = 1$ |
| `IsUnit.mul_inv_cancel_right` | for a unit $b$: $a b b^{-1} = a$ |
| `IsUnit.div_mul_cancel` | for a unit $b$: $(a / b) b = a$ |
| `IsUnit.div_eq_iff` | for a unit $b$: $a / b = c \iff a = c b$ |
| `IsUnit.div_eq_div_iff` | in a commutative division monoid, for units $b, d$: $a / b = c / d \iff a d = c b$ |

The lemma `IsUnit.isUnit_iff_mulLeft_bijective` states that $a$ is a unit exactly when the left multiplication $x \mapsto a x$ is a bijection of $M$, and `IsUnit.isUnit_iff_mulRight_bijective` is the right form. The division by a unit `divp x u` has the notation `x /ₚ u` and is $x u^{-1}$; the lemmas `divp_eq_iff_mul_eq` and `divp_mul_divp` compute with it. In a monoid with only one unit and with `IsDedekindFiniteMonoid`, the lemma `mul_eq_one` states $a b = 1 \iff a = 1 \land b = 1$. The natural numbers are the main example. The instance `instCanLiftUnitsValIsUnit` lets the tactic `lift` turn an element `a` with `IsUnit a` into a unit.

The module `Mathlib.Algebra.Group.Units.Opposite` relates units and the opposite monoid of the next sections. The equivalence `Units.opEquiv` is a group isomorphism $(M^{\mathrm{op}})^\times \cong (M^\times)^{\mathrm{op}}$, and `isUnit_op` states that $\mathrm{op}(m)$ is a unit exactly when $m$ is a unit.

#### Commuting elements and units

**Theorem (Units and commuting products).** Let $M$ be a monoid and let $a, b \in M$ with $a b = b a$. Then $a b$ is a unit if and only if $a$ and $b$ are units.

*Proof.* A product of units is a unit, with inverse $b^{-1} a^{-1}$. For the converse, let $c$ be the inverse of $a b$, so $a b c = 1$ and $c a b = 1$. Then $a (b c) = 1$. Also $(c b) a = c (b a) = c (a b) = 1$. So $a$ has a left inverse $c b$ and a right inverse $b c$, and by the lemma on left and right inverses of Section 1 these are equal, so $a$ is a unit. For $b$: $b (a c) = (b a) c = (a b) c = 1$ and $(c a) b = 1$, so $b$ is a unit in the same way. $\square$

The lemma is `Commute.isUnit_mul_iff`, used as `h.isUnit_mul_iff` for `h : Commute a b`. Without the hypothesis the result fails: in the monoid of maps $\mathbb{N} \to \mathbb{N}$, the shift $s(n) = n + 1$ and a left inverse $t$ of it give $t \circ s = \mathrm{id}$, but neither map is a bijection.

**Theorem (Powers that are units).** Let $n \neq 0$. Then $a^n$ is a unit if and only if $a$ is a unit.

*Proof.* Write $a^n = a \cdot a^{n - 1}$. The two factors commute, so by the theorem above $a^n$ is a unit exactly when $a$ and $a^{n-1}$ are units. If $a$ is a unit, so is each power. $\square$

The lemma is `isUnit_pow_iff`, and `isUnit_pow_succ_iff` is the form with $n + 1$. When $a$ is not a unit, `isUnit_pow_iff_of_not_isUnit` states that $a^n$ is a unit only for $n = 0$. If $a^n = 1$ with $n \neq 0$, then `IsUnit.of_pow_eq_one` gives that $a$ is a unit, and `Units.ofPowEqOne a n ha hn` is the unit itself. Its inverse is $a^{n - 1}$, by `Units.val_inv_ofPowEqOne`. The definitions `Units.leftOfMul` and `Units.rightOfMul` extract the units $a$ and $b$ from a unit $u = a b$ with commuting factors.

The module `Mathlib.Algebra.Group.Commute.Units` also moves commutation through the coercion of units. The lemma `Commute.units_val_iff` states that two units commute in $M^\times$ exactly when their values commute in $M$. The lemmas `Commute.units_inv_right` and `Commute.units_zpow_right` give that an element that commutes with a unit $u$ commutes with $u^{-1}$ and with each $u^m$, $m \in \mathbb{Z}$. The lemma `Units.commute_iff_mul_inv_cancel` states that $u$ commutes with $a$ exactly when $u a u^{-1} = a$.

#### Commuting elements in a group

The module `Mathlib.Algebra.Group.Commute.Basic` gives the lemmas on `Commute` that need inverses. In a group, if $a$ commutes with $b$, then $a$ commutes with $b^{-1}$: from $a b = b a$, multiply by $b^{-1}$ on both sides to get $b^{-1} a = a b^{-1}$. The lemma is `Commute.inv_right`, with the forms `Commute.inv_left`, `Commute.inv_inv` and the equivalences `Commute.inv_right_iff`. The integer powers follow: `Commute.zpow_right`, `Commute.zpow_left` and `Commute.zpow_zpow` state that $a^m$ and $b^n$ commute for all $m, n \in \mathbb{Z}$, and `Commute.self_zpow` is the case $b = a$. Conjugation preserves commutation, by `Commute.conj_iff`. The lemmas `Commute.div_mul_div_comm` and `Commute.mul_div_mul_comm` are the identities $(a / b)(c / d) = (a c)/(b d)$ of a commutative group, with only the commutations that the proof uses as hypotheses. The lemma `Commute.function_commute_mul_left` turns `Commute a b` into the commutation of the two maps $x \mapsto a x$ and $x \mapsto b x$ in the sense of Volume 1.

#### Semiconjugate elements

**Definition (Semiconjugate elements).** Let $M$ be a semigroup and let $a, x, y \in M$. The element $a$ *semiconjugates* $x$ to $y$ if $a x = y a$.

The predicate is `SemiconjBy a x y`, and `Commute a b` is `SemiconjBy a b b`. In a group, $a$ semiconjugates $x$ to $y$ exactly when $y = a x a^{-1}$, and `SemiconjBy.conj_mk` states that $a$ semiconjugates $x$ to $a x a^{-1}$. The lemmas follow two patterns. The lemmas with `_right` act on the pair $x, y$: `SemiconjBy.mul_right` states that if $a$ semiconjugates $x$ to $y$ and $x'$ to $y'$, then $a$ semiconjugates $x x'$ to $y y'$. The proof is one line: $a x x' = y a x' = y y' a$. Then `SemiconjBy.pow_right`, `SemiconjBy.inv_right` and `SemiconjBy.zpow_right` follow. The lemmas with `_left` act on $a$: `SemiconjBy.mul_left` states that if $a$ semiconjugates $y$ to $z$ and $b$ semiconjugates $x$ to $y$, then $a b$ semiconjugates $x$ to $z$. The lemma `SemiconjBy.inv_symm_left` states that $a^{-1}$ semiconjugates $y$ back to $x$. The module `Mathlib.Algebra.Group.Semiconj.Units` gives the forms for units, such as `SemiconjBy.units_inv_symm_left` and `Units.mk_semiconjBy`, and the identity `Units.conj_pow`: $(u x u^{-1})^n = u x^n u^{-1}$. In a cancellative commutative monoid, `semiconjBy_iff_eq` states that $a$ semiconjugates $x$ to $y$ only when $x = y$.

The module `Mathlib.Algebra.Group.Commute.Hom` states that a multiplicative map preserves the two relations: `Commute.map` and `SemiconjBy.map`. For an injective map the converse holds, by `commute_map_iff` and `semiconjBy_map_iff`.

#### Invertible elements

The class `Invertible a` of `Mathlib.Algebra.Group.Invertible.Defs` holds an element `⅟a` with $⅟a \cdot a = 1$ and $a \cdot ⅟a = 1$. It is data, not a proposition, so a type class can carry the inverse of one element, such as the inverse of $2$ in a ring where $2$ is invertible. In a monoid two such inverses are equal, so the type `Invertible a` has at most one element, by the instance `Invertible.subsingleton`. The lemmas carry `invOf` in their names: `invOf_mul_self`, `mul_invOf_self`, `invOf_eq_right_inv`, `invOf_invOf`, and `invOf_mul`, which states $⅟(a b) = ⅟b \cdot ⅟a$. Its proof is the uniqueness of inverses: $(a b)(⅟b \cdot ⅟a) = 1$, so $⅟b \cdot ⅟a$ is the inverse of $a b$. In a group `invOf_eq_group_inv` identifies `⅟a` with $a^{-1}$.

The module `Mathlib.Algebra.Group.Invertible.Basic` connects the class with units. The definition `unitOfInvertible a` is the unit with value $a$, and `IsUnit.invertible` chooses an instance from a proof of `IsUnit a`. The lemma `nonempty_invertible_iff_isUnit` states that `Invertible a` has an element exactly when $a$ is a unit; the proof uses these two maps. A monoid homomorphism carries an inverse to an inverse: `Invertible.map` is the instance on $f(a)$, and `map_invOf` states $f(⅟a) = ⅟f(a)$. The instance `invertiblePow` and the lemma `invOf_pow` treat powers, and `invertibleOfPowEqOne` builds an inverse from $a^n = 1$.

#### Common errors

1. A learner uses `IsUnit.mul_iff` in a monoid that is not commutative and is not Dedekind finite. The lemma needs `IsDedekindFiniteMonoid`; for two commuting elements of any monoid use `Commute.isUnit_mul_iff`.
2. A learner writes `SemiconjBy a x y` for $x a = a y$. The definition is $a x = y a$: the semiconjugating element is first and stands on the left of $x$.
3. A learner states a lemma with `[Invertible a]` and then also assumes `IsUnit a`. The class already gives a unit, by `isUnit_of_invertible`; two hypotheses of this kind make the lemma hard to apply.

### Exercises

1. (A) Let $M$ be a monoid and let $u \in M^\times$. Prove that $x \mapsto u x u^{-1}$ is a monoid homomorphism $M \to M$, and that `Units.conj_pow` is the statement that it preserves powers.
2. (A) Let $a$ commute with $b$ in a group. Prove that $a^{-1}$ commutes with $b^{-1}$ in two ways: by `Commute.inv_inv`, and by two applications of `Commute.inv_right` and `Commute.inv_left`.
3. (B) Let $M$ be a monoid and let $a^n = 1$ with $n \neq 0$. Prove that $a^{-1} = a^{n-1}$ in $M^\times$, and compute the inverse of the rotation $r$ in the dihedral group $D_5$.
4. (B) Give two maps $f, g : \mathbb{N} \to \mathbb{N}$ with $g \circ f = \mathrm{id}$ and $f \circ g \neq \mathrm{id}$. Deduce that the monoid of maps $\mathbb{N} \to \mathbb{N}$ is not Dedekind finite, and that the hypothesis of `Commute.isUnit_mul_iff` is needed.
5. (B) Let $a$ semiconjugate $x$ to $y$ in a group. Prove that $x$ and $y$ have the same order, with `SemiconjBy.pow_right` and the fact that $a x^n a^{-1} = y^n$.
6. (C) Let $M$ be a finite monoid. Prove that $M$ is Dedekind finite: if $a b = 1$, then $x \mapsto b x$ is injective, so it is a bijection, and $b$ is a unit.

### Reference

<?reference?>
