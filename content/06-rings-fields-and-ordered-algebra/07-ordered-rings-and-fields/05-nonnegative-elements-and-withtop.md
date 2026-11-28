---
title: Nonnegative elements, order synonyms and adjoined infinities
kind: api
modules:
  - Mathlib.Algebra.Order.Nonneg.Basic
  - Mathlib.Algebra.Order.Nonneg.Ring
  - Mathlib.Algebra.Order.Nonneg.Field
  - Mathlib.Algebra.Order.Nonneg.Lattice
  - Mathlib.Algebra.Order.Nonneg.Module
  - Mathlib.Algebra.Order.Positive.Ring
  - Mathlib.Algebra.Order.Positive.Field
  - Mathlib.Algebra.Order.Ring.Synonym
  - Mathlib.Algebra.Order.Ring.WithTop
  - Mathlib.Algebra.Order.Ring.Opposite
  - Mathlib.Algebra.Order.Ring.Prod
explains:
  E2: [Nonneg, Nonneg.toNonneg, Nonneg.mk_sub_mk, Nonneg.semifield, Nonneg.unitsEquivPos, Nonneg.coeRingHom, WithTop.mul_eq_top_iff, WithTop.top_mul, WithTop.instIsOrderedRing, RingHom.withTopMap]
  E1: auto
families: []
requires: [V06.C01, V06.C03, V04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Nonnegative elements, order synonyms and adjoined infinities

### Overview

Many types of analysis are built from an ordered ring by a standard construction. The nonnegative reals $[0, \infty)$ are the nonnegative part of $\mathbb{R}$. The extended nonnegative reals $[0, \infty]$ add a top element to them. The positive reals form a group under multiplication. This section gives the general constructions behind these types: the subtype of nonnegative elements, the subtype of positive elements, the types `WithTop α` and `WithBot α` with their multiplication, and the ring structures on the order synonyms, the opposite ring and the product.

The section needs the ordered rings and fields of Sections 1 and 2 and the lattices of Volume 4. Volume 15 uses these constructions for the types `NNReal` and `ENNReal`, which are defined from them.

### The library around it

#### The nonnegative elements

For a type `α` with zero and an order, `Nonneg α` is an abbreviation for the subtype `{x : α // 0 ≤ x}`. The instances transfer the structure of $\alpha$ to it.

| Instance | Condition on `α` | Structure of `{x // 0 ≤ x}` |
| --- | --- | --- |
| `Nonneg.addCommMonoid` | ordered additive monoid | additive monoid |
| `Nonneg.semiring` | ordered semiring | semiring |
| `Nonneg.commSemiring` | ordered commutative semiring | commutative semiring |
| `Nonneg.isOrderedRing` | ordered semiring | ordered semiring |
| `Nonneg.canonicallyOrderedAdd` | ordered ring | canonically ordered addition |
| `Nonneg.semifield` | linearly ordered field | semifield |
| `Nonneg.linearOrderedCommGroupWithZero` | linearly ordered field | linearly ordered group with zero |
| `Nonneg.conditionallyCompleteLinearOrderBot` | conditionally complete linear order | the same, with a bottom |

The coercion to `α` is a ring map, `Nonneg.coeRingHom`, and the lemmas `Nonneg.coe_add`, `Nonneg.coe_mul`, `Nonneg.coe_pow` and `Nonneg.coe_natCast` move it through the operations. The nonnegative elements of a ring do not form a ring, since they have no negatives. Instead, the order on them is canonical, by `Nonneg.canonicallyOrderedAdd`: $x \le y$ exactly when $y = x + z$ for a nonnegative $z$, namely $z = y - x$.

The map `Nonneg.toNonneg` sends $a$ to $\max(a, 0)$. It is the left adjoint of the coercion: `Nonneg.toNonneg_le` says $\max(a, 0) \le b \iff a \le b$ for a nonnegative $b$. The truncated subtraction `Nonneg.sub` uses it: `Nonneg.mk_sub_mk` says $x - y = \max(x - y, 0)$. This is the subtraction of $[0, \infty)$, and for a linearly ordered ring the type satisfies `Nonneg.orderedSub`.

In a linearly ordered field the nonnegative elements form a semifield, by `Nonneg.semifield`, with `Nonneg.coe_inv` and `Nonneg.coe_div` for the inverse and the quotient. The units of $[0, \infty)$ are the positive elements: `Nonneg.unitsEquivPos` is the multiplicative equivalence $\{x \ge 0\}^\times \cong \{x > 0\}$. The module `Mathlib.Algebra.Order.Nonneg.Module` makes a module over $R$ into a module over the nonnegative part of $R$, by `Nonneg.instModule`, and `Nonneg.mk_smul` says that the action is the action of the underlying element. This is the structure that convex cones use: a cone is closed under the action of the nonnegative scalars.

#### The positive elements

The subtype `{x : R // 0 < x}` of a strictly ordered semiring is closed under addition and multiplication, but it has no $0$. The module `Mathlib.Algebra.Order.Positive.Ring` gives it the structure of an additive semigroup, `Positive.addCommSemigroup`, and of an ordered cancellative monoid under multiplication, `Positive.isOrderedCancelMonoid`. The coercion lemmas are `Positive.coe_add`, `Positive.val_mul` and `Positive.val_pow`. In a linearly ordered field the positive elements form a commutative group under multiplication, by `Positive.instCommGroupSubtypeLtOfNat`, with `Positive.coe_inv` and `Positive.coe_zpow`.

#### Adjoining an infinity

`WithTop α` adds a top element $\top$ to $\alpha$. When $\alpha$ has a multiplication with zero, the multiplication extends with the convention $0 \cdot \top = 0$:
$$\top \cdot b = \top \text{ for } b \neq 0, \qquad \top \cdot 0 = 0.$$
The lemmas `WithTop.top_mul` and `WithTop.mul_top` give the first rule, `WithTop.top_mul_top` gives $\top \cdot \top = \top$, and `WithTop.mul_eq_top_iff` says that $a b = \top$ exactly when one factor is $\top$ and the other is not $0$. The convention $0 \cdot \infty = 0$ is the one of measure theory: the integral of the zero function on a set of infinite measure is $0$. The multiplication needs `DecidableEq α`, since the definition asks whether a factor is $0$.

The operations behave as expected under the coercion, by `WithTop.coe_mul` and `WithTop.coe_pow`. A finite product is finite, by `WithTop.mul_lt_top`, and `WithTop.pow_eq_top_iff` says $x^n = \top \iff x = \top \wedge n \neq 0$. The lemma `WithTop.untopD_zero_mul` says that the map sending $\top$ to $0$ is multiplicative.

Distributivity is the delicate point. In $[0, \infty]$, $\top \cdot (a + b) = \top \cdot a + \top \cdot b$ needs a case analysis on $a, b = 0$, and it fails if $a + b = 0$ is possible with $a, b \neq 0$. So the instance `WithTop.instCommSemiring` needs that $0$ is the only additive unit, through `Subsingleton (AddUnits α)`, and no zero divisors. The order instance `WithTop.instIsOrderedRing` needs a canonically ordered semiring, such as $\mathbb{N}$ or $[0, \infty)$. A ring map $f : R \to S$ that is injective extends to `RingHom.withTopMap f`, with $\top \mapsto \top$; injectivity is needed so that no nonzero element goes to $0$.

The type `WithBot α` has the same API with $\bot$, as `WithBot.bot_mul`, `WithBot.mul_eq_bot_iff` and `WithBot.instIsOrderedRing`. The degree of a polynomial takes values in `WithBot ℕ`, with $\deg 0 = \bot$, and the rule $\deg(pq) = \deg p + \deg q$ of Chapter 5 is an addition in this type.

#### Order synonyms, opposites and products

The module `Mathlib.Algebra.Order.Ring.Synonym` gives the order dual $R^{\mathrm{od}}$ and the type `Lex R` the ring structure of $R$, by instances such as `OrderDual.instRing`, `OrderDual.instCommRing`, `Lex.instRing` and `Lex.instIsDomain`, with the cast lemmas `toDual_natCast`, `toDual_intCast`, `toLex_natCast` and `toLex_intCast`. These types change only the order. The order dual of an ordered ring is not an ordered ring, because $1 \le 0$ in it. The instances are there so that `Lex (R × S)` and other synonyms can carry a ring structure and an order at the same time.

The opposite ring keeps the order: `MulOpposite.instIsOrderedRing` says that $R^{\mathrm{mop}}$ is an ordered ring when $R$ is, and `AddOpposite.instIsOrderedRing` is the additive form. The product $R \times S$ with the coordinatewise order is an ordered ring by `instIsOrderedRingProd`. It is not a strict ordered ring, since $(1, 0)$ and $(0, 1)$ are positive with product $0$.

#### Common errors

1. The nonnegative elements of a ring are a semiring, not a ring. Subtraction in `{x // 0 ≤ x}` is truncated, by `Nonneg.mk_sub_mk`, so $(2 - 3) + 3 = 3$ and not $2$.
2. In `WithTop α`, $0 \cdot \top = 0$. A proof that uses $\top \cdot b = \top$ must exclude $b = 0$; `WithTop.top_mul` has the hypothesis $b \neq 0$.
3. The order dual of an ordered ring has the same ring structure, but it is not an ordered ring. Lemmas about ordered rings do not apply to $R^{\mathrm{od}}$.

### Exercises

1. (A) Compute $\langle 2, h_2 \rangle - \langle 5, h_5 \rangle$ in `{x : ℚ // 0 ≤ x}` with `Nonneg.mk_sub_mk`.
2. (A) Show that `{x : ℚ // 0 < x}` has no zero element, so that it is not a monoid with zero.
3. (B) Prove `Nonneg.toNonneg_le` from the definition $\max(a, 0)$.
4. (B) Check distributivity $\top(a + b) = \top a + \top b$ in `WithTop ℕ` by the cases $a = 0$, $b = 0$ and $a, b \neq 0$.
5. (B) Show that in `WithTop ℤ` the rule $\top \cdot (a + b) = \top a + \top b$ fails for $a = 1$ and $b = -1$.
6. (C) Prove the associativity $(a b) c = a (b c)$ in `WithTop ℕ` for the cases where one of $a, b, c$ is $\top$, and find the place where the proof needs `NoZeroDivisors ℕ`.

### Reference

<?reference?>
