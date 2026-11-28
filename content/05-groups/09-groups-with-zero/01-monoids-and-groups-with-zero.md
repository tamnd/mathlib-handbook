---
title: Monoids and groups with zero
kind: api
modules:
  - Mathlib.Algebra.GroupWithZero.Defs
  - Mathlib.Algebra.GroupWithZero.Basic
  - Mathlib.Algebra.GroupWithZero.Commute
  - Mathlib.Algebra.GroupWithZero.Semiconj
  - Mathlib.Algebra.GroupWithZero.NeZero
  - Mathlib.Algebra.GroupWithZero.Nat
  - Mathlib.Algebra.NeZero
  - Mathlib.Algebra.GroupWithZero.Center
  - Mathlib.Algebra.GroupWithZero.Conj
  - Mathlib.Algebra.GroupWithZero.Idempotent
  - Mathlib.Algebra.GroupWithZero.Torsion
  - Mathlib.Algebra.GroupWithZero.Invertible
explains:
  E2: [MonoidWithZero, GroupWithZero, NoZeroDivisors, mul_eq_zero, mul_left_cancel₀, inv_eq_zero, zero_pow_eq, zpow_add₀, IsIdempotentElem.iff_eq_zero_or_one]
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

## Monoids and groups with zero

### Overview

A field is not a group under multiplication, because $0$ has no inverse. But a field is almost a group: the nonzero elements form a group, and $0$ absorbs each product. Mathlib calls such a structure a *group with zero*. The same shape occurs without addition: the nonnegative reals under multiplication, the value monoid $\{0\} \cup \Gamma$ of a valuation, and the group $\mathbb{Z}$ with a zero adjoined. A *monoid with zero* is weaker: it is a monoid with an element $0$ such that $0 \cdot a = a \cdot 0 = 0$. Each ring is a monoid with zero, and so is $\mathbb{N}$ under multiplication.

This section gives the classes of Mathlib for these structures and their first lemmas: the zero product property, cancellation of nonzero factors, powers of $0$, and the convention $0^{-1} = 0$. It also covers the class NeZero, which records that a given element is not zero, and the forms of the lemmas on commuting elements, centers and conjugates that hold in a group with zero. Chapter 1 gave the same lemmas for groups. The difference is a hypothesis $a \neq 0$ in each statement, and a subscript $0$ in many names. The next section treats the units of a monoid with zero and the division lemmas of a group with zero.

### The library around it

#### The classes

The module `Mathlib.Algebra.GroupWithZero.Defs` gives the chain of classes. Each class adds one axiom to the classes of Chapter 1.

| Lean name | Structure |
|---|---|
| `MulZeroClass` | a product and a $0$ with $0 \cdot a = 0$ and $a \cdot 0 = 0$ |
| `MulZeroOneClass` | a `MulOneClass` that is also a `MulZeroClass` |
| `SemigroupWithZero` | a semigroup with an absorbing $0$ |
| `MonoidWithZero` | a monoid with an absorbing $0$ |
| `CommMonoidWithZero` | a commutative monoid with an absorbing $0$ |
| `GroupWithZero` | a nontrivial monoid with zero, with $0^{-1} = 0$ and $a a^{-1} = 1$ for $a \neq 0$ |
| `CommGroupWithZero` | a commutative group with zero |

The two absorption laws are the fields `MulZeroClass.zero_mul` and `MulZeroClass.mul_zero`. Their short forms $0 \cdot a = 0$ and $a \cdot 0 = 0$ are simp lemmas of the core library. A `GroupWithZero` extends `DivInvMonoid`, so it has a division with $a / b = a b^{-1}$ and integer powers. It also extends `Nontrivial`, so $0 \neq 1$. The instance `GroupWithZero.toDivisionMonoid` makes each group with zero a `DivisionMonoid`, so the lemmas of Chapter 1 on inverses, such as `mul_inv_rev` and `inv_inv`, apply with no hypothesis.

The value $0^{-1} = 0$ is a convention, as $1/0 = 0$ in Volume 1. It makes the inverse a total function, and it makes many identities true with no side condition: $(ab)^{-1} = b^{-1}a^{-1}$ and $(a^{-1})^{-1} = a$ hold for all $a, b$. The lemma `inv_zero` states the convention, and `div_zero` and `zero_div` give $a / 0 = 0$ and $0 / a = 0$.

**Proposition (`inv_eq_zero`).** In a group with zero, $a^{-1} = 0$ if and only if $a = 0$.

*Proof.* If $a = 0$, then $a^{-1} = 0$ by the convention. If $a \neq 0$ and $a^{-1} = 0$, then $1 = a a^{-1} = a \cdot 0 = 0$, and this contradicts $0 \neq 1$. $\square$

The lemma `inv_ne_zero` is the form $a \neq 0 \Rightarrow a^{-1} \neq 0$. The pair `mul_inv_cancel₀` and `inv_mul_cancel₀` give $a a^{-1} = 1$ and $a^{-1} a = 1$ for $a \neq 0$. The subscript $0$ marks the form for a group with zero, and separates it from `mul_inv_cancel` of Chapter 1, which holds in a group.

#### Zero divisors and cancellation

A zero divisor is a nonzero $a$ with $ab = 0$ for some nonzero $b$. The class `NoZeroDivisors` says that $ab = 0$ implies $a = 0$ or $b = 0$. The simp lemma `mul_eq_zero` states the property as an equivalence, $ab = 0 \iff a = 0 \lor b = 0$. Its relatives follow the same naming pattern.

| Lean name | Statement |
|---|---|
| `mul_eq_zero` | $ab = 0 \iff a = 0 \lor b = 0$ |
| `zero_eq_mul` | $0 = ab \iff a = 0 \lor b = 0$ |
| `mul_ne_zero` | $a \neq 0$ and $b \neq 0$ give $ab \neq 0$ |
| `mul_ne_zero_iff` | $ab \neq 0 \iff a \neq 0 \land b \neq 0$ |
| `mul_self_eq_zero` | $a a = 0 \iff a = 0$ |
| `mul_eq_zero_comm` | $ab = 0 \iff ba = 0$ |
| `left_ne_zero_of_mul` | $ab \neq 0$ gives $a \neq 0$, with no class on zero divisors |

Cancellation needs a different class. The class `IsLeftCancelMulZero` says that $a \neq 0$ and $ab = ac$ give $b = c$, and `IsRightCancelMulZero` is the mirror form. The class `IsCancelMulZero` asks for both. The lemmas are `mul_left_cancel₀` and `mul_right_cancel₀`, with the equivalence forms `mul_right_inj'` and `mul_left_inj'`, and `mul_eq_mul_left_iff` states $ab = ac \iff b = c \lor a = 0$. The two notions agree in a ring, where $ab = ac$ is $a(b - c) = 0$. In a monoid with zero, a cancellation class gives `NoZeroDivisors` by the instance `IsLeftCancelMulZero.to_noZeroDivisors`, but the converse can fail. The class `MulDivCancelClass` says that $ab / b = a$ for $b \neq 0$, and gives `mul_div_cancel_right₀`.

**Proposition (`mul_left_cancel₀`).** In a group with zero, $a \neq 0$ and $ab = ac$ give $b = c$.

*Proof.* Multiply on the left by $a^{-1}$: $b = a^{-1}(ab) = a^{-1}(ac) = c$. $\square$

So each group with zero is cancellative, by the instance `instIsCancelMulZero`, and has no zero divisors, by `GroupWithZero.noZeroDivisors`. The module `Mathlib.Algebra.GroupWithZero.Nat` gives the instances for $\mathbb{N}$: `Nat.instCommMonoidWithZero`, `Nat.instIsCancelMulZero` and `Nat.instMulDivCancelClass`.

#### Powers of zero, nilpotents and reduced monoids

The powers of $0$ follow from $0^0 = 1$ and $0^{n+1} = 0^n \cdot 0 = 0$.

**Proposition (`zero_pow_eq`).** In a monoid with zero, $0^n = 1$ if $n = 0$ and $0^n = 0$ otherwise.

The lemma `zero_pow` gives $0^n = 0$ for $n \neq 0$, and `zero_pow_eq_zero` gives $0^n = 0 \iff n \neq 0$ in a nontrivial monoid with zero. An element $x$ is nilpotent, `IsNilpotent x`, when $x^n = 0$ for some $n$. A monoid with zero is reduced, `IsReduced`, when its only nilpotent is $0$. A monoid with no zero divisors is reduced, by the instance `isReduced_of_noZeroDivisors`. In a reduced monoid, `pow_eq_zero_iff` gives $a^n = 0 \iff a = 0$ for $n \neq 0$, and `pow_ne_zero` gives $a^n \neq 0$ from $a \neq 0$. The lemmas `IsNilpotent.zero`, `isNilpotent_iff_eq_zero` and `not_isNilpotent_one` complete the family. The ring $\mathbb{Z}/4$ is not reduced: $2^2 = 0$.

A monoid with zero in which $0 = 1$ has one element, because $a = a \cdot 1 = a \cdot 0 = 0$. The lemma `subsingleton_iff_zero_eq_one` states this, and `uniqueOfZeroEqOne` gives the `Unique` structure.

#### Integer powers

In a group with zero, the integer power gives $a^n$ for $n \in \mathbb{Z}$, with $a^{-n} = (a^n)^{-1}$. The law of exponents needs a hypothesis. Take $a = 0$, $m = 1$ and $n = -1$. Then $0^{m+n} = 0^0 = 1$, but $0^1 \cdot 0^{-1} = 0 \cdot 0 = 0$.

**Proposition (`zpow_add₀`).** In a group with zero, $a \neq 0$ gives $a^{m+n} = a^m a^n$ for all $m, n \in \mathbb{Z}$.

*Proof sketch.* The nonzero elements form a group, and the map $n \mapsto a^n$ agrees with the integer power in that group. So the law follows from `zpow_add` of Chapter 1. $\square$

The lemma `zpow_add'` weakens the hypothesis to $a \neq 0$, or $m + n \neq 0$, or $m = n = 0$. The forms `zpow_add_one₀`, `zpow_sub_one₀` and `zpow_one_add₀` treat one step. For $a = 0$, `zero_zpow` gives $0^n = 0$ for $n \neq 0$, and `zero_zpow_eq` gives the case split.

#### The class NeZero

The class NeZero, from the core library, holds for an element when it is not zero. A lemma can then take the fact as an instance argument, so that the elaborator finds it. The module `Mathlib.Algebra.NeZero` gives the lemmas `one_ne_zero`, `zero_ne_one`, `two_ne_zero`, `three_ne_zero` and `four_ne_zero`. Each needs an instance of NeZero for the numeral in the type. The primed forms such as `two_ne_zero'` take the type as an explicit argument. The lemma `NeZero.of_pos` gives the instance from $0 < x$, and `not_neZero` says that the class fails exactly for $0$.

In a nontrivial monoid with zero, the instance `NeZero.one` gives $1 \neq 0$. The instances `NeZero.mul` and `NeZero.pow` carry the fact to products and powers, with no zero divisors or a reduced monoid. The lemma `domain_nontrivial` says that a map $f$ with $f(0) = 0$ and $f(1) = 1$ into a nontrivial monoid with zero has a nontrivial domain.

#### Commuting elements, conjugates and the center

The lemmas on `Commute` and `SemiconjBy` from Chapter 1 hold in a group with zero, with the same names and a subscript $0$. The element $0$ commutes with each element, by `Commute.zero_left` and `Commute.zero_right`, and `SemiconjBy.zero_left` and `SemiconjBy.zero_right` are the semiconjugate forms. If $a$ commutes with $b$, then $a$ commutes with $b^{-1}$, by `Commute.inv_right₀`, and with each power $b^m$, $m \in \mathbb{Z}$, by `Commute.zpow_right₀`. The forms `Commute.inv_left_iff₀`, `Commute.div_left` and `Commute.zpow_zpow₀` follow the pattern. For semiconjugates, `SemiconjBy.inv_right₀` carries $a x = y a$ to $a x^{-1} = y^{-1} a$, and `SemiconjBy.inv_symm_left₀` gives $a^{-1} y = x a^{-1}$. The proof of `Commute.inv_right₀` needs no case on $b$: for $b = 0$ both sides are $0$, and for $b \neq 0$ the group proof applies.

In a group with zero, two elements are conjugate when $c a c^{-1} = b$ for a nonzero $c$. This is `GroupWithZero.isConj_iff₀`. The lemma `GroupWithZero.conj_pow₀` gives $(a^{-1} d a)^s = a^{-1} d^s a$ for $a \neq 0$. For centers, `Set.zero_mem_center` puts $0$ in the center, `Set.inv_mem_centralizer₀` says that a centralizer is closed under the inverse, and `Set.center_units_eq` says that, in a group with zero, a unit is central in the group of units exactly when its value is central.

#### Idempotents, invertible elements and torsion

An element $p$ is idempotent when $p^2 = p$. The element $0$ is idempotent, by `IsIdempotentElem.zero`.

**Proposition (`IsIdempotentElem.iff_eq_zero_or_one`).** In a monoid with zero with left cancellation, $p$ is idempotent if and only if $p = 0$ or $p = 1$.

*Proof.* If $p \neq 0$ and $p p = p = p \cdot 1$, then left cancellation gives $p = 1$. Conversely $0$ and $1$ are idempotent. $\square$

The class `Invertible a` carries a chosen inverse of $a$. In a group with zero, `invertibleOfNonzero` builds it from $a \neq 0$, and `invOf_eq_inv` says that it equals $a^{-1}$. In a nontrivial monoid with zero, `Invertible.ne_zero` gives $a \neq 0$. The lemmas `mul_inv_cancel_of_invertible` and `div_self_of_invertible` are the cancellation laws with the hypothesis in the class.

The module `Mathlib.Algebra.GroupWithZero.Torsion` treats roots. The lemma `HasUniqueRoots.mk'` says that a reduced commutative monoid with zero has unique roots when $x^n = y^n$ gives $x = y$ for nonzero $x$, $y$ and $n \neq 0$. The instance `UniqueFactorizationMonoid.instHasUniqueRoots` applies this to a unique factorization monoid whose group of units is torsion free.

#### Common errors

1. The law $a^{m+n} = a^m a^n$ for integer powers fails at $a = 0$. Use `zpow_add₀` with a proof of $a \neq 0$, or `zpow_add'`. The lemma `zpow_add` of Chapter 1 needs a group and does not apply.
2. A lemma of a group, such as `mul_inv_cancel`, does not apply to a field. Use the subscript form `mul_inv_cancel₀`. The name pattern with the subscript $0$ finds the right form in most cases.
3. `NoZeroDivisors` does not give cancellation in a general monoid with zero. Ask for `IsCancelMulZero` when the proof cancels a factor. In a ring the two classes agree.

### Exercises

1. (A) Prove that in a monoid with zero, $0$ is a unit if and only if $0 = 1$.
2. (A) Prove that a group with zero has no zero divisors, from the axioms of `GroupWithZero` only.
3. (A) Use `mul_eq_zero` to find the solutions of $x^2 = x$ in a field, and compare the answer with `IsIdempotentElem.iff_eq_zero_or_one`.
4. (B) Give a commutative monoid with zero that has no zero divisors and is not cancellative. Hint: adjoin a zero to a commutative monoid that is not cancellative.
5. (B) Show that the set $\{0\} \cup \{2^k : k \in \mathbb{Z}\}$ of rational numbers is a group with zero under multiplication.
6. (C) Prove that a finite monoid with zero that is nontrivial and cancellative is a group with zero.

### Reference

<?reference?>
