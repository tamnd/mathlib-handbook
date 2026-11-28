---
title: Linearly ordered groups with zero
kind: api
modules:
  - Mathlib.Algebra.Order.GroupWithZero.Canonical
  - Mathlib.Algebra.Order.GroupWithZero.WithZero
  - Mathlib.Algebra.Order.GroupWithZero.Lex
  - Mathlib.Algebra.Order.GroupWithZero.Range
  - Mathlib.Algebra.Order.GroupWithZero.Associated
explains:
  E2: [LinearOrderedCommMonoidWithZero, LinearOrderedCommGroupWithZero, WithZero.instLinearOrderedCommGroupWithZero, WithZero.exp_le_exp, WithZero.lt_mul_exp_iff_le, OrderIso.withZeroUnits, LinearOrderedCommGroupWithZero.inl, MonoidWithZeroHom.ValueGroup₀.embedding_strictMono, Associates.instCanonicallyOrderedMul, Associates.dvdNotUnit_iff_lt]
  E1: auto
families: []
requires: [V06.C01, V06.C03, V06.C06, V04, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Linearly ordered groups with zero

### Overview

A valuation on a field $K$ is a map $v : K \to \Gamma \cup \{0\}$, where $\Gamma$ is a linearly ordered commutative group, written multiplicatively, and $0$ is a new element below all of $\Gamma$. The $p$-adic valuation of $\mathbb{Q}$ sends $p^n a/b$ to $p^{-n}$ in $\mathbb{Z}$ written multiplicatively, with an adjoined $0$. Mathlib uses the class `LinearOrderedCommGroupWithZero` for the targets of valuations. The class is satisfied by $\Gamma \cup \{0\}$, but also by the nonnegative reals, which are not of this form as a type.

This section gives the class and its monoid form, the standard examples, the exponential notation for $\mathbb{Z}$ with a zero, the lexicographic product, the value group of a map, and the divisibility order on associated elements. The section needs the ordered rings of Section 1, the groups with zero of Chapter 3, the associated elements of Chapter 6, the linear orders of Volume 4 and the ordered groups of Volume 5. Volume 10 uses the class for valuations and discrete valuation rings.

### The library around it

#### The two classes

The class `LinearOrderedCommMonoidWithZero α` is a commutative monoid with zero and a linear order in which multiplication by a positive element is strictly monotone, and $0$ is the bottom element. In Lean it extends `CommMonoidWithZero α`, `LinearOrder α`, `PosMulStrictMono α`, `OrderBot α` and `IsBotZeroClass α`. The class `LinearOrderedCommGroupWithZero α` adds the inverses of the nonzero elements, through `CommGroupWithZero α`. The first consequences are instances.

- `LinearOrderedCommMonoidWithZero.toMulPosStrictMono` and `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid` give the right form and the monotonicity of multiplication by every element.
- `LinearOrderedCommMonoidWithZero.toOrderBot` gives $\bot = 0$, so every element is at least $0$.
- `LinearOrderedCommGroupWithZero.mul_inv_cancel` gives $a a^{-1} = 1$ for $a \neq 0$.

The lemmas of the previous section apply, since the class contains `PosMulStrictMono`. Two lemmas are special to the group case: `mul_inv_lt_of_lt_mul₀` says that $a < b c$ gives $a c^{-1} < b$, and `inv_mul_lt_of_lt_mul₀` is the form with the inverse on the left. These hold without a hypothesis $c \neq 0$: if $c = 0$, the hypothesis $a < 0$ is false.

A linearly ordered group with zero is the same thing as a linearly ordered group with a bottom element adjoined. The order isomorphism `OrderIso.withZeroUnits : WithZero αˣ ≃o α` says that $\alpha$ is the group of units with $0$ added. The units are densely ordered exactly when $\alpha$ is, by `denselyOrdered_units_iff`.

#### Examples

For a linearly ordered commutative group $\Gamma$, the type `WithZero Γ` is a linearly ordered group with zero, by `WithZero.instLinearOrderedCommGroupWithZero`. The order is the order of $\Gamma$ with $0$ below it: `WithZero.zero_lt_coe`, `WithZero.coe_le_coe` and `WithZero.not_coe_le_zero`. The monotonicity classes come from the instances `instPosMulMonoWithZeroOfMulLeftMono` and `instPosMulStrictMonoWithZeroOfMulLeftStrictMono` of the module `Mathlib.Algebra.Order.GroupWithZero.WithZero`. The nonnegative reals form a linearly ordered group with zero by `Nonneg.linearOrderedCommGroupWithZero` of Section 5.

The most used example is `WithZero (Multiplicative ℤ)`, with the notation `ℤᵐ⁰`, the target of discrete valuations. The instance is `WithZero.instLinearOrderedCommGroupWithZeroMultiplicativeInt`. An integer $n$ gives the element `WithZero.exp n`, and the product is the sum of the exponents. The map `WithZero.log` goes back on nonzero elements, by `WithZero.log_exp` and `WithZero.exp_log`. The order is the order of the exponents: `WithZero.exp_le_exp` says $\exp a \le \exp b \iff a \le b$, and `WithZero.exp_lt_exp` is the strict form. The discreteness of $\mathbb{Z}$ shows in `WithZero.lt_mul_exp_iff_le`: for $y \neq 0$, $x < y \cdot \exp 1 \iff x \le y$. And `WithZero.exists_exp_neg_natCast_lt` says that each nonzero $x$ is greater than $\exp(-k)$ for some natural number $k$. The order isomorphisms `WithZero.expOrderIso` and `WithZero.logOrderIso` identify an ordered additive group $G$ with the units of `WithZero (Multiplicative G)`.

There is also a dual construction. For a linearly ordered additive group with a top element, such as the additive valuations with $v(0) = \infty$, the type `Multiplicative αᵒᵈ` is a linearly ordered group with zero, by `instLinearOrderedCommGroupWithZeroMultiplicativeOrderDualOfLinearOrderedAddCommGroupWithTop`. This is the translation between additive and multiplicative valuations: the order is reversed, and $\infty$ becomes $0$.

#### Maps and value groups

The map `WithZero.map' f` extends a monoid map $f : \alpha \to \beta$ to `WithZero α → WithZero β`, and `WithZero.map'_mono` and `WithZero.map'_strictMono` say that it is monotone or strictly monotone when $f$ is. A map of monoids with zero $f : A \to B$ into a linearly ordered group with zero has a value group: `MonoidWithZeroHom.valueGroup f` is the subgroup of $B^\times$ generated by the nonzero values, and `MonoidWithZeroHom.ValueGroup₀ f` adds a zero to it. The module `Mathlib.Algebra.Order.GroupWithZero.Range` gives it the order: it is a linearly ordered group with zero by `MonoidWithZeroHom.ValueGroup₀.instLinearOrderedCommGroupWithZero`, and the inclusion into $B$ is strictly monotone, by `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono`. For a valuation, the value group is the subgroup of the target that the valuation reaches.

#### The lexicographic product

The product $\alpha \times \beta$ of two linearly ordered groups with zero is not linearly ordered in the product order, and $(0, 1)$ would be a zero divisor. The module `Mathlib.Algebra.Order.GroupWithZero.Lex` uses instead `WithZero (Lex (αˣ × βˣ))`: the lexicographic product of the unit groups, with one zero. The inclusions `LinearOrderedCommGroupWithZero.inl` and `LinearOrderedCommGroupWithZero.inr` are monotone maps of monoids with zero, and the first coordinate gives a projection `LinearOrderedCommGroupWithZero.fst`. There is no monotone projection to the second factor, since the order on the second coordinate only matters when the first coordinates are equal. The lemma `LinearOrderedCommGroupWithZero.inl_mul_inr_eq_coe_toLex` says that $\operatorname{inl}(m) \cdot \operatorname{inr}(n)$ is the pair $(m, n)$ for $m, n \neq 0$. Products of this kind are the targets of valuations of rank $2$.

#### The divisibility order on associated elements

For a commutative monoid with zero $M$, the type `Associates M` of classes of associated elements is ordered by divisibility: $[a] \le [b] \iff a \mid b$. The instance `Associates.instCanonicallyOrderedMul` says that this order is canonical: $[a] \le [b]$ exactly when $[b] = [a] \cdot [c]$ for some $c$. The instance `Associates.instIsOrderedMonoid` says that multiplication is monotone. The top element is the class of $0$, by `Associates.le_zero` and `Associates.instOrderTop`, since every element divides $0$. The bottom element is the class of $1$, and `Associates.le_one_iff` says that only $[1]$ is below it.

In a cancellative monoid, the strict order is the strict divisibility: `Associates.dvdNotUnit_iff_lt` says that $[a] < [b]$ exactly when $a \mid b$ and the quotient is not a unit. A prime class $p$ satisfies `Associates.Prime.le_or_le`: $p \le a b$ gives $p \le a$ or $p \le b$, and `Associates.one_or_eq_of_le_of_prime` says that the only classes below a prime $p$ are $1$ and $p$. These lemmas are the order form of the factorization theory of Chapter 6.

#### Common errors

1. `LinearOrderedCommGroupWithZero` is not an ordered field and not an ordered ring. It has no addition. The lemmas for ordered fields do not apply, but the lemmas with the suffix `₀` of the previous section do.
2. In `ℤᵐ⁰`, the element `WithZero.exp 1` is greater than $1$, and the uniformizer of a discrete valuation has the value `WithZero.exp (-1)`, which is less than $1$. Check the sign of the exponent, since the additive valuation and the multiplicative one have opposite orders.
3. In `Associates M`, the class of $0$ is the top element, not the bottom one. The order is divisibility, and every element divides $0$.

### Exercises

1. (A) In `ℤᵐ⁰`, compute `WithZero.exp 2 * WithZero.exp (-5)`, and order the elements $0$, $\exp(-1)$, $1$ and $\exp 3$.
2. (A) Show that in `Associates ℤ`, $[4] < [12]$, and that $[3]$ and $[4]$ are not comparable.
3. (B) Prove `mul_inv_lt_of_lt_mul₀` in a linearly ordered group with zero, with the case $c = 0$ separate.
4. (B) Prove `WithZero.lt_mul_exp_iff_le` from the fact that there is no integer strictly between $n$ and $n + 1$.
5. (B) Show that the product order on $\alpha \times \beta$ is not linear for $\alpha = \beta = $ `ℤᵐ⁰`, and that $(0, 1)$ is a zero divisor in it.
6. (C) Let $v$ be the $p$-adic valuation on $\mathbb{Q}$ with values in `ℤᵐ⁰`. Find its value group, and show that the inclusion into `ℤᵐ⁰` is an isomorphism.

### Reference

<?reference?>
