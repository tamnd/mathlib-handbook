---
title: Interval arithmetic and the unit interval
kind: api
modules:
  - Mathlib.Algebra.Order.Interval.Basic
  - Mathlib.Algebra.Order.Interval.Set.Instances
explains:
  E2: [NonemptyInterval.length, Interval.length, NonemptyInterval.length_add, NonemptyInterval.length_sub, Interval.length_add_le, NonemptyInterval.fst_sub, NonemptyInterval.mul_eq_one_iff, Set.Icc.instCommMonoidWithZero, Set.Icc.mul_le_left, Set.Ioc.instCancelCommMonoid]
  E1: auto
families: []
requires: [V04.C07, V04.C08, V01.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Interval arithmetic and the unit interval

### Overview

The previous section adds sets that happen to be intervals. This section treats intervals as elements of a type, with their own addition and multiplication. A closed interval $[a, b]$ is a pair of ends with $a \le b$, and interval arithmetic computes with these pairs: $[a, b] + [c, d] = [a + c, b + d]$. The result of a computation is an interval that contains each possible exact value. The library makes the intervals of an ordered monoid into a monoid, and the intervals of a canonically ordered semiring into a semiring.

The second part of the section treats the intervals $[0, 1]$, $[0, 1)$, $(0, 1]$ and $(0, 1)$ of an ordered semiring. Each one is closed under multiplication, so each one is a monoid or a semigroup with the multiplication of the semiring. The interval $[0, 1]$ of $\mathbb{R}$ is the unit interval of topology and probability, and these instances give it its algebra.

### The library around it

#### Intervals as elements

The type `NonemptyInterval α` has as elements the pairs $(a, b)$ of elements of $\alpha$ with $a \le b$. The ends are the two components of the pair, written $s_1$ and $s_2$ here. Each element has a coercion to the set $[a, b]$. The type `Interval α` adds one more element, $\bot$, the empty interval. These types and their order, which is inclusion, are in `Mathlib.Order.Interval.Basic`. The constructor `NonemptyInterval.pure` gives the interval $[a, a]$ of one point.

#### Operations on intervals

The file `Mathlib.Algebra.Order.Interval.Basic` defines the operations by their ends. If multiplication is monotone on both sides, then the product of $s$ and $t$ is the interval from $s_1 t_1$ to $s_2 t_2$. The lemmas `NonemptyInterval.fst_mul` and `NonemptyInterval.snd_mul` state the two ends. The lemma `NonemptyInterval.coe_mul_interval` states that the set of the product is the pointwise product of the two sets, so the definition agrees with the previous section. The lemma `NonemptyInterval.pure_mul_pure` states that the product of two points is the point of the product. The additive forms are `NonemptyInterval.fst_add` and the lemmas with the same pattern.

The negative of $s$ is the interval from $-s_2$ to $-s_1$, as `NonemptyInterval.fst_neg` and `NonemptyInterval.snd_neg` state. For a subtraction, the ends cross: `NonemptyInterval.fst_sub` states that the left end of $s - t$ is $s_1 - t_2$, and `NonemptyInterval.snd_sub` states that the right end is $s_2 - t_1$. This needs only `OrderedSub`, so it holds for the truncated subtraction of $\mathbb{N}$. The lemma `NonemptyInterval.sub_mem_sub` states that $a \in s$ and $b \in t$ give $a - b \in s - t$. This is the property that makes interval arithmetic correct: the result contains each exact value.

On `Interval α`, the empty interval absorbs each operation. The lemmas `Interval.bot_add`, `Interval.mul_bot` and `Interval.bot_pow` state this, with $n \ne 0$ for the power.

#### The algebraic structure

The intervals of an ordered commutative monoid form a commutative monoid, by the instances `NonemptyInterval.commMonoid` and `Interval.commMonoid`. They do not form a group, even when $\alpha$ is a group. The difference $s - s$ is the interval from $s_1 - s_2$ to $s_2 - s_1$, which is not $0$ unless $s$ is a point. The lemma `NonemptyInterval.mul_eq_one_iff` states the exact fact: $s t = 1$ holds only when $s$ and $t$ are points $a$ and $b$ with $a b = 1$. The library gives the weaker structure `NonemptyInterval.subtractionCommMonoid`, in which the negation is an involution and reverses sums, but $s - s = 0$ fails. The multiplicative form is `NonemptyInterval.divisionCommMonoid`.

For a commutative semiring with a canonical order, such as $\mathbb{N}$ or $\mathbb{R}_{\ge 0}$, the intervals form a commutative semiring, by the instance `NonemptyInterval.instCommSemiringOfCanonicallyOrderedAdd`. The distributive law holds because all the elements are nonnegative, so multiplication is monotone and the ends of a product are the products of the ends. On $\mathbb{R}$ the product of intervals is not defined by this file, because multiplication by a negative number reverses the order.

#### Length of an interval

In an ordered additive group, `NonemptyInterval.length` is $s_2 - s_1$, and `Interval.length` is the same with the value $0$ at $\bot$, as `Interval.length_bot` states. The lemma `NonemptyInterval.length_nonneg` states that the length is nonnegative, and `NonemptyInterval.length_pure` states that a point has length $0$. The extension of the *positivity* tactic in the same file proves the inequality $0 \le$ length when it appears in a goal.

Lengths add: `NonemptyInterval.length_add` states that $s + t$ has length $s_2 - s_1 + t_2 - t_1$, the sum of the two lengths. The lemma `NonemptyInterval.length_sub` states that $s - t$ also has the sum of the two lengths as its length, and not the difference. This is the usual loss of precision of interval arithmetic: each operation adds the errors. The lemma `NonemptyInterval.length_sum` gives the length of a finite sum. On `Interval α` the equation becomes an inequality, `Interval.length_add_le`, because $\bot + t = \bot$ has length $0$ while $t$ can have a positive length.

#### The unit interval and its neighbours

The file `Mathlib.Algebra.Order.Interval.Set.Instances` gives algebraic structures to four intervals of an ordered semiring $R$, as subtypes of $R$.

The interval $[0, 1]$ contains $0$ and $1$, and the product of two of its elements is again in it: if $0 \le x \le 1$ and $0 \le y \le 1$, then $0 \le x y \le x \cdot 1 = x \le 1$. So it is a monoid with zero, and the instance `Set.Icc.instCommMonoidWithZero` gives the commutative form. The coercion to $R$ keeps the operations, by `Set.Icc.coe_mul` and `Set.Icc.coe_pow`, and `Set.Icc.coeMonoidWithZeroHom` bundles it as a map of monoids with zero. The inequality in the argument above is `Set.Icc.mul_le_left`, which states $x y \le x$, and `Set.Icc.mul_le_right` states $x y \le y$. The instance `Set.Icc.instIsOrderedMonoid` gives an ordered monoid. In a ring, `Set.Icc.mem_iff_one_sub_mem` states that $t$ is in $[0, 1]$ if and only if $1 - t$ is, and `Set.Icc.one_sub_mem` is one direction. This symmetry is used for convex combinations $t x + (1 - t) y$.

The interval $[0, 1)$ does not contain $1$, so it is only a semigroup with zero, by `Set.Ico.instSemigroupWithZero`, and `Set.Ico.coeMulHom` is the coercion as a map of semigroups. The interval $(0, 1]$ does not contain $0$ but contains $1$. In a strict ordered semiring it is a monoid, and with cancellation in $R$ it is a cancellative commutative monoid, by `Set.Ioc.instCancelCommMonoid`. The interval $(0, 1)$ is a commutative semigroup, by `Set.Ioo.instCommSemigroup`, and `Set.Ioo.one_sub_mem` states that $1 - t$ is in $(0, 1)$ when $t$ is. In the last two cases the multiplication is strictly monotone, by instances such as `Set.Ioc.instMulLeftStrictMono`, because the elements are positive.

#### Common errors

1. The intervals of an ordered group do not form a group, so lemmas such as `sub_self` do not apply. For $s - s$, compute the ends with `NonemptyInterval.fst_sub` and `NonemptyInterval.snd_sub`.
2. The product of intervals needs multiplication that is monotone on both sides. For intervals in $\mathbb{R}$ that contain negative numbers, use the pointwise product of sets of the previous section, which is defined for each type with a multiplication.
3. An element of $[0, 1]$ in the sense of `Set.Icc.instCommMonoidWithZero` is a subtype element, not a real number. Use the coercion lemmas such as `Set.Icc.coe_mul` to move a product to $R$ before an inequality in $R$ is applied.

### Exercises

1. (A) Compute $[1, 3] - [2, 5]$ in `NonemptyInterval ℤ` and its length, and check `NonemptyInterval.length_sub` on this example.
2. (A) Show that the left end of $s^{-1}$ is $s_2^{-1}$ in an ordered commutative group, and explain why the ends are exchanged.
3. (B) Prove `NonemptyInterval.mul_eq_one_iff` for ordered commutative groups. Use the lengths in the additive form.
4. (B) Prove `Set.Icc.mul_le_left`, and deduce that the powers $x^n$ of an element of $[0, 1]$ form an antitone sequence.
5. (B) Show that $[0, 1)$ has no identity element for its multiplication in $\mathbb{R}$, so that it is not a monoid.
6. (C) Prove the distributive law $s (t + u) = s t + s u$ for intervals in $\mathbb{N}$, and find intervals in $\mathbb{Z}$ for which the formula of the ends of a product gives an interval that does not contain each product.

### Reference

<?reference?>
