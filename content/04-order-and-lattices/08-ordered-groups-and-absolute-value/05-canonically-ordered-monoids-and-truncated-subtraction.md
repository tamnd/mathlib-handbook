---
title: Canonically ordered monoids and truncated subtraction
kind: api
modules:
  - Mathlib.Algebra.Order.Monoid.Canonical.Defs
  - Mathlib.Algebra.Order.Monoid.Canonical.Basic
  - Mathlib.Algebra.Order.Sub.Defs
  - Mathlib.Algebra.Order.Sub.Basic
  - Mathlib.Algebra.Order.Sub.Unbundled.Basic
  - Mathlib.Algebra.Order.Sub.Unbundled.Hom
  - Mathlib.Algebra.Order.Sub.Prod
  - Mathlib.Algebra.Order.IsBotOne
  - Mathlib.Algebra.Order.Group.Ideal
  - Mathlib.Algebra.Order.Monoid.Associated
explains:
  E2: [CanonicallyOrderedAdd, le_iff_exists_add, IsBotZeroClass, OrderedSub, tsub_le_iff_right, tsub_eq_zero_iff_le, add_tsub_cancel_of_le, tsub_tsub_eq_min, SemigroupIdeal.fg_of_wellQuasiOrderedLE, Associates.mk_le_mk_iff_dvd]
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

## Canonically ordered monoids and truncated subtraction

### Overview

On the natural numbers, $a \le b$ holds exactly when $b = a + c$ for some $c$. The order comes from the addition, and $0$ is the least element. The same is true for the nonnegative reals $\mathbb{R}_{\ge 0}$, for the extended nonnegative reals $[0, \infty]$, for multisets and for finitely supported functions to $\mathbb{N}$. Mathlib calls such a monoid *canonically ordered*.

These monoids are not groups, and so $b - a$ cannot be an inverse. They have a subtraction all the same: $b - a$ is the least $c$ with $b \le c + a$. On $\mathbb{N}$ this gives $3 - 5 = 0$. This *truncated subtraction* has its own class and its own lemma names, with the prefix *tsub*. This section describes the class of canonical orders, the class of truncated subtraction and the main lemmas, and three related files: the bottom element $1$, the ideals of a canonically ordered monoid and the order of divisibility.

### The library around it

#### Canonically ordered monoids

The class `CanonicallyOrderedAdd α` asks for a type with an addition and an order. It extends `ExistsAddOfLE α`, which gives a $c$ with $b = a + c$ when $a \le b$, and adds the two axioms $a \le a + b$ and $a \le b + a$. The lemmas `le_self_add` and `le_add_self` state these axioms, and `le_iff_exists_add` states that $a \le b \leftrightarrow \exists c, b = a + c$. The class is a mixin, so a canonically ordered commutative monoid is written with three classes:

```lean
variable {α : Type*} [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
```

From these classes the library derives the instance `CanonicallyOrderedAdd.toIsOrderedAddMonoid`, so all the lemmas of Section 1 apply. The multiplicative class is `CanonicallyOrderedMul`, with the lemmas `le_self_mul` and `le_iff_exists_mul`. The lemma `lt_iff_exists_add` gives $a < b \leftrightarrow \exists c > 0, b = a + c$ when addition is strictly monotone, and `exists_pos_add_of_lt` gives the witness of a strict inequality.

In a canonically ordered monoid each element is at least $0$, because $0 \le 0 + b = b$. The file `Mathlib.Algebra.Order.IsBotOne` gives this fact a class of its own. The class `IsBotZeroClass α` states that $0$ is the least element, and the instance `instIsBotZeroClass` gives it for each canonically ordered monoid. The lemmas `zero_le`, `nonpos_iff_eq_zero` and `pos_iff_ne_zero` need only this class. The multiplicative class is `IsBotOneClass`, with `le_one_iff_eq_one` and `one_lt_iff_ne_one`, and `bot_eq_one` identifies the bottom of an `OrderBot` with $1$. A canonically ordered monoid has exactly one unit, the identity, as the instance `CanonicallyOrderedCommMonoid.toUniqueAddUnits` records.

The file `Mathlib.Algebra.Order.Monoid.Canonical.Basic` has lemmas that split a quantifier over an interval. For example, `exists_le_add_iff_le_left` states that an element $a \le b + c$ with a property $P$ exists if and only if one exists below $b$, or $P(b + d)$ holds for some $d \le c$. The lemma `Set.range_add_eq_image_Ici` states that the range of $x \mapsto f(x + k)$ is the image of the interval $[k, \infty)$ under $f$.

#### Truncated subtraction

The class `OrderedSub α` asks for an order, an addition and a subtraction with one axiom:
$$a - b \le c \leftrightarrow a \le c + b.$$
This is a Galois connection between $x \mapsto x - b$ and $x \mapsto x + b$, in the sense of Chapter 6. It fixes $a - b$ as the least $c$ with $a \le c + b$. The lemma `tsub_le_iff_right` is the axiom, and `tsub_le_iff_left` is the form with $b + c$. An ordered additive group has the instance `AddGroup.toOrderedSub` of the previous section, so each *tsub* lemma also holds for groups. The instances `Prod.orderedSub` and `Pi.orderedSub` give the class on products.

Several lemmas follow from the axiom alone, in `Mathlib.Algebra.Order.Sub.Defs`. The lemma `le_add_tsub` gives $a \le b + (a - b)$, and `tsub_le_tsub` gives $a - d \le b - c$ from $a \le b$ and $c \le d$. The lemma `tsub_tsub` states $b - a - c = b - (a + c)$. For the proof of `tsub_tsub`, both sides are the least $x$ with $b \le (x + c) + a$, by two uses of the axiom.

In a canonically ordered monoid, `Mathlib.Algebra.Order.Sub.Basic` gives the lemmas that use $0$. The lemma `tsub_eq_zero_iff_le` states $a - b = 0 \leftrightarrow a \le b$. Its proof is short: by the axiom, $a - b \le 0$ is equivalent to $a \le 0 + b = b$, and $a - b \le 0$ is equivalent to $a - b = 0$ because $0$ is the least element. The lemmas `tsub_self`, `tsub_le_self` and `tsub_pos_iff_lt` are other examples. In a linear order, `tsub_add_eq_max` gives $a - b + b = \max(a, b)$, and `tsub_tsub_eq_min` gives $a - (a - b) = \min(a, b)$. For the second, if $a \le b$ then $a - b = 0$ and the result is $a$. If $b \le a$ then $a = (a - b) + b$, so $a - (a - b) = b$ by cancellation. On a linear canonical order with `AddRightReflectLE`, the definition `CanonicallyOrderedAdd.toSub` and the lemma `CanonicallyOrderedAdd.toOrderedSub` construct a truncated subtraction.

#### Cancellation of a truncated difference

The equation $(b - a) + a = b$ is false on $\mathbb{N}$ when $b < a$. The file `Mathlib.Algebra.Order.Sub.Unbundled.Basic` has the forms with the hypothesis $a \le b$. The lemma `add_tsub_cancel_of_le` states $a + (b - a) = b$, and `tsub_add_cancel_of_le` states $b - a + a = b$. They need `ExistsAddOfLE` but no cancellation. The lemma `le_add_tsub` gives $b \le a + (b - a)$. For the converse, the hypothesis gives $b = a + c$, so $b - a \le c$ by the axiom, and $a + (b - a) \le a + c = b$.

The other direction, $(a + b) - b = a$, needs cancellation and not an order hypothesis. The lemma `add_tsub_cancel_right` asks for `AddLeftReflectLE`. On $[0, \infty]$ it fails, because $(1 + \infty) - \infty = 0$. For this case the library has forms with `AddLECancellable` hypotheses on single elements, as `AddLECancellable.add_tsub_cancel_right` and `AddLECancellable.tsub_tsub_cancel_of_le`. With these forms, a proof about $[0, \infty]$ needs only the finiteness of the elements that are cancelled.

The file `Mathlib.Algebra.Order.Sub.Unbundled.Hom` treats maps. The lemma `OrderIso.map_tsub` states that an order isomorphism that keeps addition also keeps truncated subtraction, and `map_tsub_of_le` does the same for an additive map that keeps the order, when $a \le b$. The lemma `le_mul_tsub` states $a b - a c \le a (b - c)$.

#### Ideals and divisibility

The file `Mathlib.Algebra.Order.Group.Ideal` gives a finiteness result. In a canonically ordered commutative monoid whose order is a well quasi-order, `SemigroupIdeal.fg_of_wellQuasiOrderedLE` states that each semigroup ideal is finitely generated, and `SemigroupIdeal.instWellFoundedGT` states that ascending chains of ideals stop. The proof uses the minimal elements of the ideal. An ideal $I$ is upward closed for the canonical order, because $a \in I$ gives $a c \in I$. In a well quasi-order, a set has finitely many minimal elements, and each element of $I$ is above one of them.

The file `Mathlib.Algebra.Order.Monoid.Associated` orders the associates of a commutative monoid by divisibility. The lemma `Associates.mk_le_mk_iff_dvd` states that the class of $x$ is below the class of $y$ if and only if $x \mid y$. The class of $1$ is the bottom, by `Associates.instOrderBot`, and `Associates.isUnit_iff_eq_bot` states that the units are exactly the bottom. The lemmas `Associates.le_mul_right` and `Associates.le_mul_left` are the axioms of a canonical order in this setting.

#### Common errors

1. On $\mathbb{N}$, the expression $a - b + b$ is not $a$. A rewrite with `tsub_add_cancel_of_le` needs a proof of $b \le a$. When the order of $a$ and $b$ is not known, use `tsub_add_eq_max`.
2. The lemma `add_tsub_cancel_right` does not apply to $[0, \infty]$, because addition there does not reflect the order. Use the `AddLECancellable` forms with a proof that the element is finite.
3. The truncated subtraction of $\mathbb{N}$ does not distribute as in a ring. The equation $a - (b - c) = a - b + c$ is false for $a = 1$, $b = 2$ and $c = 1$. Move the computation to $\mathbb{Z}$ with a cast, or use lemmas such as `tsub_tsub` that hold for truncated subtraction.

### Exercises

1. (A) Prove `tsub_eq_zero_iff_le` from `tsub_le_iff_right` and `nonpos_iff_eq_zero`.
2. (A) Show that the integers with the usual order are not canonically ordered, and find the axiom of `CanonicallyOrderedAdd` that fails.
3. (B) Prove `tsub_tsub` in a type with `OrderedSub`, without the lemma itself.
4. (B) Prove `tsub_add_eq_max` in a linear canonically ordered monoid with truncated subtraction.
5. (B) Show that `add_tsub_cancel_right` fails on $[0, \infty]$, and prove $(a + b) - b = a$ when $b \ne \infty$.
6. (C) Prove `SemigroupIdeal.fg_of_wellQuasiOrderedLE` for $\mathbb{N} \times \mathbb{N}$ with the product order, by an argument with the minimal elements of the ideal.

### Reference

<?reference?>
