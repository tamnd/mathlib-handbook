---
title: Covariant classes and unbundled ordered monoids
kind: api
modules:
  - Mathlib.Algebra.Order.Monoid.Unbundled.Defs
  - Mathlib.Algebra.Order.Monoid.Unbundled.Basic
  - Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
  - Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
  - Mathlib.Algebra.Order.ZeroLEOne
  - Mathlib.Algebra.Order.Monoid.NatCast
  - Mathlib.Algebra.Order.Monoid.Basic
explains:
  E2: [CovariantClass, ContravariantClass, MulLeftMono, MulLeftReflectLE, mul_le_mul', Group.covariant_iff_contravariant, covariant_le_iff_contravariant_lt, MulLECancellable, le_iff_exists_one_le_mul, min_add_max]
  E1: auto
families: []
requires: [V04.C01, V04.C02, V01.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Covariant classes and unbundled ordered monoids

### Overview

The first section of this chapter defines an ordered monoid by the mixin `IsOrderedMonoid`: a commutative monoid, a preorder and the axiom that multiplication keeps the order. Many lemmas about inequalities need much less. The rule $b \le c \Rightarrow a b \le a c$ makes sense for any type with a multiplication and an order. It does not need an identity, associativity or commutativity. Mathlib states most inequality lemmas with this rule alone, as a hypothesis of its own. Such a lemma is *unbundled*: it asks for each property separately, and so it applies to $\mathbb{N}$, to the ordinals, to the extended reals and to ordered fields with the same proof.

The modules of this section hold the classes for these rules and the large library of lemmas that use them. The rules come in sixteen classes: left or right, multiplication or addition, monotone or strictly monotone or order reflecting. The section explains how to read the class names and the lemma names, so that a reader can guess the name of a lemma and the hypotheses it needs.

### The library around it

#### Covariant and contravariant classes

The base module `Mathlib.Algebra.Order.Monoid.Unbundled.Defs` starts from an action $\mu : M \to N \to N$ and a relation $r$ on $N$. The predicate `Covariant M N μ r` says that each map $\mu(m, \cdot)$ keeps $r$: from $r(a, b)$ follows $r(\mu(m, a), \mu(m, b))$. The predicate `Contravariant M N μ r` says that each map reflects $r$: from $r(\mu(m, a), \mu(m, b))$ follows $r(a, b)$. The classes `CovariantClass` and `ContravariantClass` make these predicates instances. The lemma `act_rel_act_of_rel` applies a covariant class, `rel_of_act_rel_act` applies a contravariant class, and `rel_iff_cov` combines the two into an equivalence.

A reader rarely writes `CovariantClass` directly. The module defines short names for the cases that occur, with $M = N$, the operation $\cdot$ or $+$, and the relation $\le$ or $<$.

| Lean name | Meaning |
|---|---|
| `MulLeftMono M` | $b \le c \Rightarrow a b \le a c$ |
| `MulRightMono M` | $b \le c \Rightarrow b a \le c a$ |
| `MulLeftStrictMono M` | $b < c \Rightarrow a b < a c$ |
| `MulRightStrictMono M` | $b < c \Rightarrow b a < c a$ |
| `MulLeftReflectLE M` | $a b \le a c \Rightarrow b \le c$ |
| `MulRightReflectLE M` | $b a \le c a \Rightarrow b \le c$ |
| `MulLeftReflectLT M` | $a b < a c \Rightarrow b < c$ |
| `MulRightReflectLT M` | $b a < c a \Rightarrow b < c$ |

The additive forms are `AddLeftMono`, `AddRightMono`, `AddLeftStrictMono`, `AddRightStrictMono`, `AddLeftReflectLE`, `AddRightReflectLE`, `AddLeftReflectLT` and `AddRightReflectLT`. The six *Mono* and *ReflectLT* names are abbreviations of `CovariantClass` or `ContravariantClass`. The two *ReflectLE* names for each operation are separate classes, such as `MulLeftReflectLE`, with a field such as `MulLeftReflectLE.le_of_mul_le_mul_left'`. "Right" means that the fixed factor is on the right: in `MulRightMono` the map $x \mapsto x a$ is monotone. In Lean the right forms use `Function.swap` of the operation.

The module also proves the links between the classes. Each link is an instance or a short lemma.

1. For a commutative operation the left and right forms agree: `covariant_swap_mul_of_covariant_mul` and `contravariant_swap_mul_of_contravariant_mul` are instances, and `mulRightMono_of_mulLeftMono` is the lemma form.
2. In a group, covariance and contravariance agree: `Group.covariant_iff_contravariant`. The instance `Group.mulLeftReflectLE_of_mulLeftMono` uses it.
3. In a linear order, monotone for $\le$ is the same as reflecting $<$, and the converse: `covariant_le_iff_contravariant_lt` and `covariant_lt_iff_contravariant_le`.
4. In a partial order, strict monotonicity gives monotonicity: `mulLeftMono_of_mulLeftStrictMono`. With cancellation the converse holds: `IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono`.

**Proposition.** Let $G$ be a group with a relation $r$. Then left multiplication keeps $r$ if and only if it reflects $r$.

*Proof.* Suppose left multiplication keeps $r$ and $r(a b, a c)$ holds. Multiply on the left by $a^{-1}$. Covariance gives $r(a^{-1} a b, a^{-1} a c)$, and this is $r(b, c)$. Conversely, suppose left multiplication reflects $r$ and $r(b, c)$ holds. Write $b = a^{-1}(a b)$ and $c = a^{-1}(a c)$. Then $r(a^{-1}(a b), a^{-1}(a c))$ holds, and reflection by the factor $a^{-1}$ gives $r(a b, a c)$. $\square$

**Proposition.** In a linear order, $b \le c \Rightarrow a b \le a c$ holds for all $a, b, c$ if and only if $a b < a c \Rightarrow b < c$ holds for all $a, b, c$.

*Proof.* Suppose the first rule and $a b < a c$. If $c \le b$, then $a c \le a b$, which contradicts $a b < a c$. So $b < c$ by linearity. Conversely, suppose the second rule and $b \le c$. If $a c < a b$, then $c < b$, which contradicts $b \le c$. So $a b \le a c$ by linearity. $\square$

The proposition is `covariant_le_iff_contravariant_lt`. It explains why a lemma for a linear order often asks for `MulLeftMono` and then uses the strict reflection rule for free, through the instance `contravariant_lt_of_covariant_le`.

#### The lemmas of the unbundled library

The module `Mathlib.Algebra.Order.Monoid.Unbundled.Basic` holds about four hundred lemmas. Each one names its rule as a hypothesis. The names follow a fixed pattern: the statement is read from left to right, and *of* separates the conclusion from the hypotheses.

| Lean name | Statement | Hypotheses |
|---|---|---|
| `mul_le_mul'` | $a \le b$, $c \le d \Rightarrow a c \le b d$ | `MulLeftMono`, `MulRightMono` |
| `mul_le_mul_iff_left` | $a b \le a c \iff b \le c$ | `MulLeftMono`, `MulLeftReflectLE` |
| `mul_lt_mul_of_lt_of_le` | $a < b$, $c \le d \Rightarrow a c < b d$ | `MulLeftMono`, `MulRightStrictMono` |
| `le_mul_of_one_le_right'` | $1 \le b \Rightarrow a \le a b$ | `MulLeftMono` |
| `one_le_mul` | $1 \le a$, $1 \le b \Rightarrow 1 \le a b$ | `MulLeftMono` |
| `mul_eq_one_iff_of_one_le` | $1 \le a$, $1 \le b \Rightarrow (a b = 1 \iff a = 1 \wedge b = 1)$ | `MulLeftMono`, `MulRightMono` |
| `le_of_mul_le_mul_left'` | $a b \le a c \Rightarrow b \le c$ | `MulLeftReflectLE` |

The additive names replace *mul* by *add*, *one* by *zero*, *one_le* by *nonneg* and *one_lt* by *pos*: `add_nonneg`, `add_eq_zero_iff_of_nonneg`, `le_add_of_nonneg_right`, `add_le_add_iff_left`. A prime on a multiplicative name, as in `mul_le_mul'`, marks the form for an ordered monoid. The unprimed name `mul_le_mul` is the form for an ordered semiring, with nonnegativity hypotheses, in another volume. The additive name has no prime, because no clash exists.

When a statement has two forms, one with the left rule and one with the right rule, the library uses the namespaces *Left* and *Right*. For instance `Left.one_le_mul` and `Right.one_le_mul` differ only in the class they assume, and `Left.mul_lt_mul` and `Right.mul_lt_mul` both prove $a < b$, $c < d \Rightarrow a c < b d$ from different strict rules.

**Proof of `mul_le_mul'`.** From $a \le b$ and the right rule, $a c \le b c$. From $c \le d$ and the left rule, $b c \le b d$. Transitivity gives $a c \le b d$. $\square$

The same module transfers monotonicity through the operations. The lemmas `Monotone.mul'`, `Monotone.const_mul'`, `Monotone.mul_const'`, `StrictMono.mul'` and their forms for `Antitone`, `MonotoneOn` and `StrictAntiOn` say that a product of monotone functions is monotone. The additive forms are `Monotone.add`, `Monotone.const_add` and `StrictMono.add_monotone`. For a linear order, `cmp_mul_left'` says that $\operatorname{cmp}(a b, a c) = \operatorname{cmp}(b, c)$, and `OrderEmbedding.mulLeft` in `Mathlib.Algebra.Order.Monoid.Basic` packs $x \mapsto m x$ as an order embedding.

The predicate `MulLECancellable a` says that $a$ cancels in inequalities: $a b \le a c \Rightarrow b \le c$ for this one element $a$. It is weaker than `MulLeftReflectLE`, which asks the property for every $a$. The additive form `AddLECancellable` is the main tool for truncated subtraction in a later section, where only some elements cancel. The lemmas `MulLECancellable.mul`, `MulLECancellable.mul_le_mul_iff_left` and `MulLECancellable.inj_right` give its closure under products and its use. The instance `Contravariant.MulLECancellable` gives the predicate for each element when the reflection class holds.

#### Differences as witnesses

In a group, $a \le b$ is the same as $1 \le a^{-1} b$. In $\mathbb{N}$ there is no inverse, but $a \le b$ still means that $b = a + c$ for some $c$. The class `ExistsMulOfLE` in `Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE` records this: from $a \le b$ follows $b = a c$ for some $c$. Its additive form is `ExistsAddOfLE`. Each group is an instance, by `Group.existsMulOfLE`, and so are $\mathbb{N}$ and the nonnegative reals.

**Proposition.** Suppose `ExistsMulOfLE`, `MulLeftMono` and `MulLeftReflectLE`. Then $a \le b$ if and only if $b = a c$ for some $c \ge 1$.

*Proof.* If $a \le b$, write $b = a c$. Then $a \cdot 1 = a \le a c$, and reflection gives $1 \le c$. Conversely, from $1 \le c$ the left rule gives $a = a \cdot 1 \le a c = b$. $\square$

This is `le_iff_exists_one_le_mul`. The additive form `le_iff_exists_nonneg_add` and the strict form `lt_iff_exists_pos_add` follow in the same way. With a dense linear order, the module also proves the approximation rule `le_of_forall_pos_le_add`: if $a \le b + \varepsilon$ for each $\varepsilon > 0$, then $a \le b$. Its multiplicative form is `le_of_forall_one_lt_le_mul`.

#### Minimum and maximum

The module `Mathlib.Algebra.Order.Monoid.Unbundled.MinMax` treats a linear order. Translation commutes with the minimum and the maximum: `min_add_add_left` states $\min(a + b, a + c) = a + \min(b, c)$, and `max_add_add_left` is the form for the maximum. The identity `min_add_max` states $\min(a, b) + \max(a, b) = a + b$, with the proof that the pair $(\min(a, b), \max(a, b))$ is $(a, b)$ or $(b, a)$. The more general `fn_min_add_fn_max` states $f(\min(a, b)) + f(\max(a, b)) = f(a) + f(b)$ for any function $f$. The lemma `le_or_le_of_add_le_add` says that $a + b \le c + d$ forces $a \le c$ or $b \le d$.

#### The order of the numerals

The class `ZeroLEOneClass` in `Mathlib.Algebra.Order.ZeroLEOne` has the single field `ZeroLEOneClass.zero_le_one`. It gives `zero_le_one` and, with `NeZero 1`, the strict forms `zero_lt_one` and `one_pos`. Its instances cover `ℕ`, `ℤ`, `ℚ`, products and functions. The module `Mathlib.Algebra.Order.Monoid.NatCast` combines it with `AddLeftMono` to order the small numerals: `zero_le_two`, `zero_lt_two`, `one_lt_two`, `three_pos`, `four_pos`, and `lt_add_one`, which states $a < a + 1$. The primed forms such as `zero_lt_two'` take the type as an explicit argument, for use when Lean cannot infer it.

#### Transfer along injective maps

The module `Mathlib.Algebra.Order.Monoid.Basic` transfers the ordered structure along a map. If $f : \beta \to \alpha$ is injective, keeps the operations and the order is pulled back from $\alpha$, then `Function.Injective.isOrderedMonoid` gives the class `IsOrderedMonoid β`. The cancellative form is `Function.Injective.isOrderedCancelMonoid`. The lemma `StrictMono.isOrderedMonoid` does the same for a strictly monotone map out of a linear order. These lemmas build the ordered structure on subtypes and on type copies without new proofs.

#### Common errors

1. The names `add_le_add_left` and `add_le_add_right` refer to the side of the *added* term in the conclusion, not to the class. In this version of Mathlib, `add_le_add_left` proves $b + a \le c + a$ and needs `AddRightMono`. Read the statement of the lemma before use.
2. A lemma that asks for `AddLeftReflectLE` fails for $\mathbb{N} \cup \{\infty\}$, where $\infty + 1 = \infty + 2$. Check that the type has the reflection class before using `le_of_add_le_add_left`, or use `AddLECancellable` for the elements that do cancel.
3. The multiplicative monoid lemmas end with a prime, as `mul_le_mul'` and `le_mul_of_one_le_right'`. The unprimed names belong to ordered semirings and ask for nonnegative factors.

### Exercises

1. (A) Prove `mul_le_mul'` from `mul_le_mul_left` and `mul_le_mul_right`, and state its additive form.
2. (A) Show that $\mathbb{N}$ has `AddLeftReflectLE` but that `WithTop ℕ` does not.
3. (B) In a linear order with `MulLeftMono`, prove that $a b < a c$ gives $b < c$, without the lemma `covariant_le_iff_contravariant_lt`.
4. (B) Prove `min_add_max` from the case split $a \le b$ or $b \le a$, and then prove `fn_min_add_fn_max` in the same way.
5. (B) Show that `MulLECancellable a` and `MulLECancellable b` give `MulLECancellable (a * b)` in a semigroup.
6. (C) Let $\alpha$ be a dense linear order with `ExistsAddOfLE`. Prove that if $a \le b + \varepsilon$ for each $\varepsilon > 0$, then $a \le b$.

### Reference

<?reference?>
