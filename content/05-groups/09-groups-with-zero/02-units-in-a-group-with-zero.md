---
title: Units, division and the ring inverse
kind: api
modules:
  - Mathlib.Algebra.GroupWithZero.Units.Basic
  - Mathlib.Algebra.GroupWithZero.Units.Lemmas
  - Mathlib.Algebra.GroupWithZero.Units.Equiv
  - Mathlib.Algebra.GroupWithZero.Units.Fintype
  - Mathlib.Algebra.GroupWithZero.Equiv
explains:
  E2: [Units.mk0, isUnit_iff_ne_zero, Ring.inverse, Ring.inverse_mul_cancel, div_eq_iff, div_eq_div_iff, unitsEquivNeZero, Fintype.card_units, map_inv₀, groupWithZeroOfIsUnitOrEqZero]
  E1: auto
families: []
requires: [V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Units, division and the ring inverse

### Overview

Chapter 1 defined the group of units $M^\times$ of a monoid $M$. In a group with zero $G_0$, the units are exactly the nonzero elements, so $G_0^\times$ is $G_0 \setminus \{0\}$ with the same product. This fact connects the two worlds. A statement about the group $G_0^\times$ gives a statement about the nonzero elements of $G_0$, and the lemmas of group theory apply to them. In a monoid with zero that is not a group with zero, such as $\mathbb{Z}$ or a ring of matrices, there is still an inverse function: the ring inverse sends a unit to its inverse and each other element to $0$.

This section gives the API for these ideas. It covers the map from nonzero elements to units, the division lemmas of a group with zero, the ring inverse `Ring.inverse`, homomorphisms that preserve the inverse, the permutations $x \mapsto ax$ for $a \neq 0$, and the count of units in a finite group with zero. It builds on the previous section, where the classes and the zero product lemmas are.

### The library around it

#### Nonzero elements are units

The module `Mathlib.Algebra.GroupWithZero.Units.Basic` starts from one function. For $a \in G_0$ and a proof $h$ of $a \neq 0$, `Units.mk0 a h` is the unit with value $a$ and inverse $a^{-1}$. Its simp lemma `Units.val_mk0` says that its value is $a$. The lemma `Units.mk0_mul` gives the product, `Units.mk0_one` gives the unit $1$, and `Units.mk0_inj` says that $\mathrm{mk0}\ a = \mathrm{mk0}\ b$ exactly when $a = b$.

**Proposition (`isUnit_iff_ne_zero`).** In a group with zero, $a$ is a unit if and only if $a \neq 0$.

*Proof.* If $a \neq 0$, then $a a^{-1} = 1 = a^{-1} a$, so $a$ is a unit. Conversely, assume $a = 0$ is a unit with inverse $u$. Then $1 = 0 \cdot u = 0$, and this contradicts $0 \neq 1$. $\square$

The forward direction has two short names. `Ne.isUnit` turns $h : a \neq 0$ into `IsUnit a`, and dot notation applies it to the proof $h$. The form `IsUnit.mk0` takes the element as an explicit argument. The converse holds in each nontrivial monoid with zero: `IsUnit.ne_zero` and `Units.ne_zero` say that a unit is not $0$, and `not_isUnit_zero` says that $0$ is not a unit. In a trivial monoid $0 = 1$ is a unit, and `isUnit_zero_iff` gives $\mathrm{IsUnit}\ 0 \iff 0 = 1$. Units are not zero divisors: `Units.mul_left_eq_zero` gives $a u = 0 \iff a = 0$, and `IsUnit.mul_right_eq_zero` is the form with `IsUnit`.

The module `Mathlib.Algebra.GroupWithZero.Units.Equiv` packages the bijection.

**Proposition (`unitsEquivNeZero`).** For a group with zero $G_0$, the map $u \mapsto u$ is a bijection from $G_0^\times$ onto the subtype $\{a \in G_0 : a \neq 0\}$.

*Proof.* The map is injective, because a unit is determined by its value (`Units.ext` of Chapter 1). It lands in the nonzero elements by `Units.ne_zero`. It is surjective, because a nonzero $a$ is the value of `Units.mk0 a h`. $\square$

For quantifiers, `Units.exists_iff_ne_zero` turns $\exists u \in G_0^\times,\ p(u)$ into $\exists x \neq 0,\ p(x)$, and `Units.exists0` goes the other way.

Conversely, a monoid with zero in which each element is a unit or $0$ is a group with zero. The definition `groupWithZeroOfIsUnitOrEqZero` builds the structure, with the inverse of a nonzero $a$ chosen from the proof that $a$ is a unit. The commutative form is `commGroupWithZeroOfIsUnitOrEqZero`. Both need a nontrivial monoid.

#### Division in a group with zero

A group with zero has the division $a / b = a b^{-1}$, so each division lemma of a group has a form for a group with zero, with a hypothesis that a denominator is not $0$. The names follow the group names, often with the subscript $0$.

| Lean name | Statement |
|---|---|
| `div_self` | $a \neq 0 \Rightarrow a / a = 1$ |
| `div_mul_cancel₀` | $b \neq 0 \Rightarrow (a / b) b = a$ |
| `mul_div_cancel_of_imp` | $(b = 0 \Rightarrow a = 0) \Rightarrow a b / b = a$ |
| `div_eq_iff` | $b \neq 0 \Rightarrow (a / b = c \iff a = c b)$ |
| `div_eq_one_iff_eq` | $b \neq 0 \Rightarrow (a / b = 1 \iff a = b)$ |
| `div_eq_zero_iff` | $a / b = 0 \iff a = 0 \lor b = 0$ |
| `div_ne_zero` | $a \neq 0$ and $b \neq 0$ give $a / b \neq 0$ |
| `div_div_cancel₀` | $a \neq 0 \Rightarrow a / (a / b) = b$ |
| `mul_div_mul_right` | $c \neq 0 \Rightarrow a c / (b c) = a / b$ |
| `mul_eq_one_iff_eq_inv₀` | $b \neq 0 \Rightarrow (a b = 1 \iff a = b^{-1})$ |

The lemma `div_eq_zero_iff` has no hypothesis. It holds because $0^{-1} = 0$: if $b = 0$, then $a / b = a \cdot 0 = 0$. But `div_self` needs its hypothesis: $0 / 0 = 0 \neq 1$.

**Proposition (`div_eq_div_iff`).** In a commutative group with zero, let $b \neq 0$ and $d \neq 0$. Then $a / b = c / d$ if and only if $a d = c b$.

*Proof.* Multiply both sides of $a b^{-1} = c d^{-1}$ by $b d$. Commutativity gives $a d = c b$, because $b b^{-1} = 1$ and $d d^{-1} = 1$. The steps reverse, because multiplication by the nonzero element $b d$ is injective. $\square$

This is the rule for equal fractions. Without commutativity, `Commute.div_eq_div_iff` gives the same result when $b$ and $d$ commute. The integer powers have the same pattern: `zpow_sub₀` gives $a^{m - n} = a^m / a^n$ for $a \neq 0$, `zpow_ne_zero` gives $a^n \neq 0$ from $a \neq 0$, and `pow_sub₀` gives $a^{m - n} = a^m (a^n)^{-1}$ for natural $n \le m$.

#### The ring inverse

A ring that is not a field has no total inverse with good properties. Mathlib defines one anyway, for each monoid with zero $M_0$:
$$\mathrm{inverse}(x) = \begin{cases} x^{-1} & \text{if } x \text{ is a unit,} \\ 0 & \text{otherwise.} \end{cases}$$
This is `Ring.inverse`. The name says ring, but the definition needs only `MonoidWithZero`. It is noncomputable, because it decides with classical logic whether $x$ is a unit. Its lemmas split by this case.

| Lean name | Statement |
|---|---|
| `Ring.inverse_unit` | for a unit $u$, the inverse of $u$ is $u^{-1}$ |
| `Ring.inverse_non_unit` | for a non-unit $x$, the inverse of $x$ is $0$ |
| `Ring.inverse_mul_cancel` | for a unit $x$, $\mathrm{inverse}(x)\, x = 1$ |
| `Ring.mul_inverse_cancel` | for a unit $x$, $x\, \mathrm{inverse}(x) = 1$ |
| `Ring.inverse_zero` | the inverse of $0$ is $0$ |
| `Ring.inverse_one` | the inverse of $1$ is $1$ |
| `Ring.inverse_mul` | if $a$ or $b$ is a unit, $\mathrm{inverse}(ab) = \mathrm{inverse}(b)\,\mathrm{inverse}(a)$ |
| `Ring.inverse_inverse` | for a unit $a$, the inverse of the inverse is $a$ |
| `Ring.isUnit_iff_inverse_mul_cancel` | $x$ is a unit if and only if $\mathrm{inverse}(x)\, x = 1$ |
| `Ring.inverse_eq_inv` | in a group with zero, the inverse is $a^{-1}$ |

**Proposition (`Ring.inverse_mul_cancel`).** If $x$ is a unit of $M_0$, then $\mathrm{inverse}(x)\, x = 1$.

*Proof.* Since $x$ is a unit, the definition takes the first case, and $\mathrm{inverse}(x) = u^{-1}$ for the unit $u$ with value $x$. Then $u^{-1} u = 1$. $\square$

The lemma `Ring.inverse_eq_inv` says that in a group with zero the ring inverse is the inverse of the structure. So `Ring.inverse` is a common extension of the inverse in a group with zero and of the inverse of units. The inverse of a square matrix uses it, through the inverse of the determinant. The module `Mathlib.Algebra.GroupWithZero.Commute` adds the forms `Ring.mul_inverse_rev`, $\mathrm{inverse}(ab) = \mathrm{inverse}(b)\,\mathrm{inverse}(a)$ with no hypothesis, and `Ring.inverse_pow`. In a commutative monoid with zero, `MonoidWithZero.inverse` bundles the ring inverse as a homomorphism of monoids with zero. In a commutative group with zero, `invMonoidWithZeroHom` bundles $a \mapsto a^{-1}$.

#### Homomorphisms and the inverse

A homomorphism of monoids with zero $f : G_0 \to G_0'$ between groups with zero respects the inverse and the division.

**Proposition (`map_inv₀`).** Let $f$ be a homomorphism of monoids with zero between groups with zero. Then $f(a^{-1}) = f(a)^{-1}$ for each $a$.

*Proof.* If $a = 0$, both sides are $0$, since $f(0) = 0$ and $0^{-1} = 0$. If $a \neq 0$, then $f(a) f(a^{-1}) = f(a a^{-1}) = f(1) = 1$, so $f(a^{-1})$ is the inverse of $f(a)$. $\square$

The lemmas `map_div₀` and `map_zpow₀` follow. When the target is nontrivial, `map_ne_zero` and `map_eq_zero` say that $f(a) = 0$ exactly when $a = 0$: a nonzero $a$ is a unit, and $f$ sends a unit to a unit. These lemmas do not make $f$ injective: the map that sends each nonzero element to $1$ and $0$ to $0$ is a homomorphism. A homomorphism $f$ is *local* when $f(a)$ is a unit only if $a$ is a unit. The instance `instIsLocalHomOfMonoidWithZeroHomClassOfNontrivial` says that each homomorphism of monoids with zero from a group with zero to a nontrivial monoid with zero is local. The lemma `map_ringInverse` says that a local homomorphism commutes with the ring inverse.

The module `Mathlib.Algebra.GroupWithZero.Equiv` gives the coercion from an isomorphism of monoids to a homomorphism of monoids with zero. An isomorphism $f : G \simeq^* H$ of monoids with zero sends $0$ to $0$, because $0$ is the unique absorbing element. The function `MulEquiv.toMonoidWithZeroHom` and the instance `MulEquivClass.toMonoidWithZeroHomClass` record this, and `MulEquiv.toMonoidWithZeroHom_injective` says that the coercion is injective.

#### Permutations by a nonzero element

For $a \neq 0$, the map $x \mapsto a x$ is a bijection of $G_0$, with inverse $x \mapsto a^{-1} x$. The permutation is `Equiv.mulLeft₀ a h`. The forms `Equiv.mulRight₀`, `Equiv.divLeft₀` and `Equiv.divRight₀` give $x \mapsto x a$, $x \mapsto a / x$ and $x \mapsto x / a$. The map $x \mapsto a / x$ is its own inverse. The lemmas `mulLeft_bijective₀` and `mulRight_bijective₀` state the bijectivity. These permutations are useful for sums: a sum over $G_0$ does not change when the variable is multiplied by a nonzero constant.

#### Finite groups with zero

The module `Mathlib.Algebra.GroupWithZero.Units.Fintype` counts units.

**Proposition (`Fintype.card_units`).** For a finite group with zero $G_0$, $|G_0^\times| = |G_0| - 1$.

*Proof.* The bijection `unitsEquivNeZero` identifies $G_0^\times$ with the nonzero elements, and there are $|G_0| - 1$ of them. $\square$

The form with addition is `Fintype.card_eq_card_units_add_one`, $|G_0| = |G_0^\times| + 1$, and it avoids the truncated subtraction of $\mathbb{N}$. The forms `Nat.card_units` and `Nat.card_eq_card_units_add_one` use `Nat.card`. For a prime $p$, the field $\mathbb{Z}/p$ gives $|(\mathbb{Z}/p)^\times| = p - 1$, and the theorem of Lagrange then gives the theorem of Fermat, $a^{p-1} = 1$ for $a \neq 0$. The module also proves `Fintype.card_units_int`, $|\mathbb{Z}^\times| = 2$, with `UnitsInt.univ` listing the units $1$ and $-1$.

#### Common errors

1. `div_self` needs $a \neq 0$, but `div_eq_zero_iff` and `mul_div_cancel_of_imp` need no hypothesis or a weaker one. Read the hypotheses before a rewrite fails.
2. `Ring.inverse` is not the inverse of a field written in another way. In a ring it sends each non-unit to $0$, so $\mathrm{inverse}(x)\, x = 1$ holds only for units. In a group with zero, rewrite with `Ring.inverse_eq_inv` first.
3. `Fintype.card_units` is stated with truncated subtraction. Prefer `Fintype.card_eq_card_units_add_one` when the proof does arithmetic on the cardinality.

### Exercises

1. (A) Prove that in a group with zero, $a / b = 0$ implies $a = 0$ or $b = 0$, and give the Lean name of the result.
2. (A) Compute `Ring.inverse` on each element of $\mathbb{Z}/6$.
3. (B) Prove `map_div₀` from `map_inv₀` and the definition of the division.
4. (B) Let $G_0$ be a finite commutative group with zero and $a \neq 0$. Show that $\prod_{x \neq 0} a x = a^{|G_0| - 1} \prod_{x \neq 0} x$, and deduce $a^{|G_0| - 1} = 1$.
5. (B) Let $G_0$ be a group with zero. Show that the map $G_0 \to \{0, 1\}$ that sends each nonzero element to $1$ is a homomorphism of monoids with zero, and check `map_eq_zero` and `map_inv₀` for it.
6. (C) Let $M$ be a finite commutative monoid with zero in which each nonzero element is cancellable, and $M$ is nontrivial. Build a `CommGroupWithZero` structure on $M$ with `commGroupWithZeroOfIsUnitOrEqZero`.

### Reference

<?reference?>
