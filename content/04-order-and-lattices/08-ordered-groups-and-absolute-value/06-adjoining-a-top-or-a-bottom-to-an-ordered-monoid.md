---
title: Adjoining a top or a bottom to an ordered monoid
kind: api
modules:
  - Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
  - Mathlib.Algebra.Order.Monoid.WithTop
  - Mathlib.Algebra.Order.AddGroupWithTop
  - Mathlib.Algebra.Order.WithTop.Untop0
  - Mathlib.Algebra.Order.Sub.WithTop
  - Mathlib.Algebra.Order.Monoid.ToMulBot
  - Mathlib.Algebra.Order.SuccPred.WithBot
explains:
  E2: [WithTop.add_top, WithTop.add_eq_top, WithTop.coe_add, WithTop.add_le_add_iff_left, WithTop.addLECancellable_iff_ne_top, LinearOrderedAddCommMonoidWithTop, LinearOrderedAddCommGroupWithTop, WithTop.untop₀, WithTop.instOrderedSub, WithZero.toMulBot]
  E1: auto
families: []
requires: [V04.C01, V04.C03, V01.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Adjoining a top or a bottom to an ordered monoid

### Overview

Many types of analysis and algebra are an ordered monoid with one more element. The extended nonnegative reals `ENNReal` are `WithTop` of the nonnegative reals, the extended reals `EReal` are `WithBot (WithTop ℝ)`, and the degree of a polynomial takes values in `WithBot ℕ`, with $\bot$ as the degree of $0$. In each case the new element absorbs the addition: $a + \infty = \infty$, and $\bot + a = \bot$.

This section describes how the library extends the addition, the order and the subtraction of $\alpha$ to `WithTop α` and `WithBot α`. It also describes the classes of linearly ordered monoids and groups with a top element, the map that forgets the top element, and two smaller files. The order on `WithTop α` itself, with each element of $\alpha$ below $\top$, is in Chapter 1.

### The library around it

#### Addition with an absorbing element

The file `Mathlib.Algebra.Order.Monoid.Unbundled.WithTop` defines the addition of `WithTop α` by $\top + x = x + \top = \top$ and by the addition of $\alpha$ on the other elements. The lemmas `WithTop.add_top` and `WithTop.top_add` state the first rule, and `WithTop.coe_add` states that the coercion from $\alpha$ keeps addition. The lemma `WithTop.add_eq_top` states $x + y = \top \leftrightarrow x = \top \lor y = \top$, and `WithTop.add_ne_top` and `WithTop.add_lt_top` are its negative forms. The instances such as `WithTop.addMonoid` and `WithTop.addCommMonoid` carry the algebraic structure across, and `WithTop.addHom` is the coercion as a monoid map.

The covariant classes of Section 3 also carry across. The instances `WithTop.addLeftMono` and `WithTop.addRightMono` give monotone addition, and `WithTop.instIsOrderedAddMonoid` in `Mathlib.Algebra.Order.Monoid.WithTop` gives an ordered monoid. If $\alpha$ is canonically ordered, then so is `WithTop α`, by `WithTop.canonicallyOrderedAdd`. So `ENNReal`, which is `WithTop` of a canonically ordered type, is canonically ordered.

The reflection classes do not carry across, because $\top$ does not cancel: $1 + \top = 2 + \top$ but $1 \ne 2$. The library gives the reflection with a hypothesis $x \ne \top$. The lemma `WithTop.add_le_add_iff_left` states $x + y \le x + z \leftrightarrow y \le z$ for $x \ne \top$, and `WithTop.le_of_add_le_add_left` is one direction. The lemma `WithTop.addLECancellable_iff_ne_top` states the fact exactly: an element of `WithTop α` cancels if and only if it is not $\top$. The strict reflection class does carry across, as the instance `WithTop.addLeftReflectLT` shows, because $x + y < x + z$ is false when $x = \top$.

The file has the same lemmas for `WithBot α` with $\bot$ in place of $\top$, such as `WithBot.add_bot` and `WithBot.bot_add`. Maps also extend: `AddMonoidHom.withTopMap` extends a monoid map $f$ by $f(\top) = \top$, and `AddEquiv.withTopCongr` does the same for an isomorphism. The lemmas with numerals, such as `WithTop.coe_eq_zero` and `WithTop.natCast_lt_top`, move between $\alpha$ and `WithTop α`.

#### Classes for linear orders with a top element

Some types have a top element without the form `WithTop α`. The class `LinearOrderedAddCommMonoidWithTop` in `Mathlib.Algebra.Order.AddGroupWithTop` asks for a linearly ordered commutative monoid with a top element $\top$ such that $\top + x = \top$, as `LinearOrderedAddCommMonoidWithTop.top_add'` states. The instance `WithTop.linearOrderedAddCommMonoidWithTop` gives it for each linearly ordered cancellative monoid. The additive valuations of the library, `AddValuation`, take their values in a type of this class.

The class `LinearOrderedAddCommGroupWithTop` adds a negation with $-\top = \top$ and $x + (-x) = 0$ for $x \ne \top$. These are the lemmas `LinearOrderedAddCommGroupWithTop.neg_top` and `LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top`. For a linearly ordered additive group $G$, the type `WithTop G` has this class by the instance `WithTop.LinearOrderedAddCommGroup.instLinearOrderedAddCommGroupWithTopOfIsOrderedAddMonoid`. In this class the subtraction satisfies $a - \top = \top$, as `LinearOrderedAddCommGroupWithTop.sub_top` states, and most group lemmas hold with a hypothesis $x \ne \top$. Examples are `LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_iff_ne_top` and `LinearOrderedAddCommGroupWithTop.sub_lt_sub_iff_left_of_ne_top`.

#### Truncated subtraction with a top element

A type `WithTop α` has a second subtraction when $\alpha$ has a bottom element, in `Mathlib.Algebra.Order.Sub.WithTop`. It is defined by $\top - a = \top$ for $a$ in $\alpha$, by $x - \top = \bot$, and by the subtraction of $\alpha$ on the other elements. The lemmas `WithTop.top_sub_coe`, `WithTop.sub_top` and `WithTop.coe_sub` state these rules. If $\alpha$ has a truncated subtraction, then so does `WithTop α`, by the instance `WithTop.instOrderedSub`. On `ENNReal` this gives $\infty - \infty = 0$. The check of the axiom $x - y \le z \leftrightarrow x \le z + y$ for $y = \top$ is short: the left side is $\bot \le z$, which is true, and the right side is $x \le \top$, which is also true. The lemma `WithTop.sub_eq_top_iff` states $a - b = \top \leftrightarrow a = \top \land b \ne \top$.

The two subtractions differ at $a - \top$: it is $\bot$ in `WithTop.instSub` and $\top$ in a `LinearOrderedAddCommGroupWithTop`. The type `WithTop ℤ` has only the second, because $\mathbb{Z}$ has no bottom element.

#### Removing the top element

The function `WithTop.untop₀` in `Mathlib.Algebra.Order.WithTop.Untop0` sends an element of `WithTop α` to $\alpha$, with $\top$ sent to $0$. The lemma `WithTop.untop₀_top` states this value, and `WithTop.coe_untop₀_of_ne_top` states that the function inverts the coercion away from $\top$. The lemma `WithTop.untop₀_add` states $(a + b)$ maps to the sum of the images when $a \ne \top$ and $b \ne \top$. The hypotheses are necessary: for $a = \top$ and $b = 1$ the left side is $0$ and the right side is $1$. The lemma `WithTop.untop₀_mul` needs no hypothesis, because both sides are $0$ when a factor is $\top$ and the other factor is not $0$. In an ordered group, `WithTop.untop₀_le_untop₀_iff` compares the images of two finite elements.

#### Two smaller files

The file `Mathlib.Algebra.Order.Monoid.ToMulBot` gives an isomorphism between two ways to write an ordered group with a bottom element. The term `WithZero.toMulBot` is a multiplicative isomorphism from `WithZero (Multiplicative α)` to `Multiplicative (WithBot α)`, and `WithZero.toMulBot_le` states that it keeps the order. The first form is the usual one for the values of a valuation, and the second form is additive.

The file `Mathlib.Algebra.Order.SuccPred.WithBot` computes the successor in `WithBot α` for a type with `SuccAddOrder`, where the successor of $x$ is $x + 1$. The lemma `WithBot.succ_natCast` states that the successor of $n$ is $n + 1$, and `WithBot.one_le_iff_pos` states $1 \le a \leftrightarrow 0 < a$ in `WithBot α`. For the degree of a polynomial, the second lemma turns a strict inequality with $0$ into an inequality with $1$.

#### Common errors

1. The lemma `add_le_add_iff_left` asks for a reflection class that `ENNReal` and `WithTop ℕ` do not have. Use `WithTop.add_le_add_iff_left` with a proof of $x \ne \top$, or the `AddLECancellable` forms of Section 5.
2. The two subtractions on types with a top element give different values at $a - \top$. Do not move a computation from `ENNReal` to `WithTop ℤ` by analogy.
3. The function `WithTop.untop₀` sends $\top$ to $0$, so a statement about `WithTop.untop₀ a` says little when $a = \top$. Prove $a \ne \top$ first, then rewrite with `WithTop.coe_untop₀_of_ne_top`.

### Exercises

1. (A) Prove `WithTop.add_eq_top` by cases on $x$ and $y$.
2. (A) Find $x$, $y$ and $z$ in `WithTop ℕ` with $x + y \le x + z$ and $z < y$.
3. (B) Prove the converse direction of `WithTop.addLECancellable_iff_ne_top`: if $x \ne \top$, then $x$ cancels.
4. (B) Check the axiom of `OrderedSub` for `WithTop α` in the four cases where each of $x$ and $y$ is $\top$ or an element of $\alpha$.
5. (B) Show that $x \mapsto x + 1$ is strictly monotone on `WithTop ℤ`, but that $x \mapsto x + \top$ is not injective. Explain why `WithTop.add_le_add_iff_left` needs the hypothesis $x \ne \top$.
6. (C) Prove `WithTop.untop₀_mul` for a type with `MulZeroClass` and decidable equality.

### Reference

<?reference?>
