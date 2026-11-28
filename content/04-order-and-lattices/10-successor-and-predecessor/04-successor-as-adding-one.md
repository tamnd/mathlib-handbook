---
title: Successor as adding one
kind: api
modules:
  - Mathlib.Algebra.Order.SuccPred
  - Mathlib.Algebra.Order.SuccPred.TypeTags
  - Mathlib.Algebra.Order.Interval.Set.SuccPred
  - Mathlib.Algebra.Order.Interval.Finset.SuccPred
  - Mathlib.Algebra.Order.Monoid.LocallyFiniteOrder
explains:
  E2: [SuccAddOrder, PredSubOrder, Order.succ_eq_add_one, Order.add_one_le_iff, Order.lt_add_one_iff, monotone_of_le_add_one, Order.succ_iterate, Set.Ico_add_one_right_eq_Icc, Finset.insert_Icc_right_eq_Icc_add_one, LocallyFiniteOrder.orderAddMonoidEquiv]
  E1: auto
families: []
requires: [V04.C01, V04.C02, V04.C07, V04.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Successor as adding one

### Overview

On $\mathbb{N}$, $\mathbb{Z}$, the positive naturals, the extended naturals and the ordinals, the successor of $x$ is $x + 1$. The earlier sections of this chapter work with `Order.succ`, which has a good theory but does not appear in the usual statements. A proof about $\mathbb{N}$ writes $n + 1$, and the lemma $a < b + 1 \leftrightarrow a \le b$ should apply to it directly. This section describes the classes that state $\operatorname{succ}(x) = x + 1$ and $\operatorname{pred}(x) = x - 1$, and the lemmas that they give for inequalities, monotone functions, limits and intervals.

The last part of the section treats a result of a different kind. A linearly ordered additive group in which each interval $[a, b]$ is finite is either trivial or isomorphic to $\mathbb{Z}$ as an ordered group. In such a group the successor of $x$ is $x + g$ for the least positive element $g$.

### The library around it

#### The two classes

The class `SuccAddOrder α` in `Mathlib.Algebra.Order.SuccPred` asks for a `SuccOrder` on $\alpha$, with an addition and a $1$, such that the successor of each $x$ is $x + 1$. The field `SuccAddOrder.succ_eq_add_one` states this, and `Order.succ_eq_add_one` is the form for use. The dual class `PredSubOrder α` asks that the predecessor be $x - 1$, as `Order.pred_eq_sub_one` states. The instances `Nat.instSuccAddOrder`, `Int.instSuccAddOrder`, `PNat.instSuccAddOrder` and `Ordinal.instSuccAddOrder` give the first class, and `Nat.instPredSubOrder` and `Int.instPredSubOrder` give the second. On $\mathbb{N}$ the predecessor of $0$ is $0$, and the truncated subtraction of Chapter 8 also gives $0 - 1 = 0$, so the two agree.

The classes are data, not a condition. A `SuccAddOrder` instance contains a `SuccOrder` instance, so the general lemmas of the first section apply. The point of the class is that the successor and $x + 1$ are equal by a lemma that the simplifier can use, so a statement can be written with $x + 1$ only.

#### Inequalities with $x + 1$

Each lemma of the first section about `Order.succ` has a form with $x + 1$. The lemma `Order.add_one_le_iff` states $x + 1 \le y \leftrightarrow x < y$ when $\alpha$ has no maximal element, and `Order.add_one_le_iff_of_not_isMax` asks only that $x$ is not maximal. The lemma `Order.lt_add_one_iff` states $x < y + 1 \leftrightarrow x \le y$ in a linear order. The forms in one direction, `Order.add_one_le_of_lt` and `Order.le_of_lt_add_one`, need no condition on maximal elements. For the covering relation, `Order.covBy_add_one` states that $x + 1$ covers $x$, and `Order.covBy_iff_add_one_eq` states that $y$ covers $x$ exactly when $y = x + 1$. The forms for the predecessor are `Order.le_sub_one_iff`, `Order.sub_one_lt_iff` and `Order.sub_one_covBy`.

The iterates are sums. The lemma `Order.succ_iterate` states that the $n$-th iterate of the successor sends $x$ to $x + n$, for an additive monoid with one, and `Order.pred_iterate` states the same for $x - n$ in an additive group with one.

In a linear order where $0$ is the least element, the elements below $1$ and $2$ are known. The lemma `Order.lt_one_iff` states $x < 1 \leftrightarrow x = 0$, and `Order.le_one_iff` states $x \le 1 \leftrightarrow x = 0 \lor x = 1$. The lemma `Order.one_le_iff_pos` states $1 \le x \leftrightarrow 0 < x$. These lemmas need the class `IsBotZeroClass` of Chapter 8 or a similar condition. They hold for $\mathbb{N}$ and the ordinals with one proof.

#### Monotonicity from one step

A function on $\mathbb{N}$ is monotone if $f(n) \le f(n + 1)$ for each $n$. The lemma `monotone_of_le_add_one` states this for each type with `SuccAddOrder` and `IsSuccArchimedean`, the class of the second section: if $f(a) \le f(a + 1)$ for each $a$ that is not maximal, then $f$ is monotone. The proof uses the archimedean property. If $a \le b$, then $b$ is an iterate of the successor applied to $a$, and an induction on the number of steps gives $f(a) \le f(b)$. The forms `strictMono_of_lt_add_one`, `antitone_of_add_one_le` and `strictAnti_of_add_one_lt` treat the other cases, and `monotoneOn_of_le_add_one` gives the form on an order-connected set. For the predecessor, `monotone_of_sub_one_le` uses $f(a - 1) \le f(a)$.

#### Limits

The third section defines the limit elements, those that are not successors. With `SuccAddOrder`, a limit is not of the form $a + 1$, as `Order.not_isSuccLimit_add_one` states. The lemma `Order.IsSuccLimit.add_one_lt` states that if $x$ is a limit and $y < x$, then $y + 1 < x$, and `Order.IsSuccLimit.add_natCast_lt` gives $y + n < x$ for each natural number $n$. When $0$ is the least element, `Order.IsSuccLimit.natCast_lt` states that each natural number is below a limit. For the ordinals, these lemmas give $n < \omega$ and $\alpha + n < \lambda$ for each limit ordinal $\lambda$ above $\alpha$.

#### Intervals with $x + 1$

The files `Mathlib.Algebra.Order.Interval.Set.SuccPred` and `Mathlib.Algebra.Order.Interval.Finset.SuccPred` move between the kinds of intervals of Chapter 7 with $x + 1$ and $x - 1$. In a linear order with no maximal element, `Set.Ico_add_one_right_eq_Icc` states $[a, b + 1) = [a, b]$, and `Set.Icc_add_one_left_eq_Ioc` states $[a + 1, b] = (a, b]$. The lemma `Set.Iio_add_one_eq_Iic` states $(-\infty, b + 1) = (-\infty, b]$. Each lemma has a form with the suffix *of_not_isMax* that asks only that one element is not maximal, and a form with $x - 1$ for the predecessor, such as `Set.Ioc_sub_one_left_eq_Icc`.

The lemmas with insert are the step of an induction on an interval. The lemma `Finset.insert_Icc_right_eq_Icc_add_one` states that for $a \le b + 1$, adding $b + 1$ to the finite interval $[a, b]$ gives $[a, b + 1]$. With it, a sum over $[a, b + 1]$ in $\mathbb{N}$ splits into the sum over $[a, b]$ and the last term. The lemma `Finset.Ico_add_one_right_eq_Icc` is the finite form of the equation for sets.

#### Discrete ordered groups

The file `Mathlib.Algebra.Order.Monoid.LocallyFiniteOrder` treats the ordered groups with a locally finite order, in which each interval is finite. The lemma `Finset.card_Ico_add_right` states that a translation keeps the size of a finite interval, and `card_Ico_zero_add` states that $|[0, a + b)| = |[0, a)| + |[0, b)|$ for $a, b \ge 0$. For the proof, $[0, a + b)$ is the disjoint union of $[0, b)$ and $[b, a + b)$, and the second set is a translate of $[0, a)$.

So the map $a \mapsto |[0, a)| - |[0, -a)|$ adds, and it is a map of groups from $G$ to $\mathbb{Z}$, the definition `LocallyFiniteOrder.addMonoidHom`. It is strictly monotone, by `LocallyFiniteOrder.orderAddMonoidHom_strictMono`, and bijective when $G$ is nontrivial, by `LocallyFiniteOrder.orderAddMonoidHom_bijective`. The result is `LocallyFiniteOrder.orderAddMonoidEquiv`, an isomorphism of ordered groups from $G$ to $\mathbb{Z}$. The multiplicative form is `LocallyFiniteOrder.orderMonoidEquiv`, with values in `Multiplicative ℤ`. The form `LocallyFiniteOrder.orderMonoidWithZeroEquiv` treats a linearly ordered group with zero whose units are locally finite, which is the form of the value group of a discrete valuation.

The file `Mathlib.Algebra.Order.SuccPred.TypeTags` gives `Multiplicative α` and `Additive α` the successor and predecessor orders of $\alpha$. The lemma `Order.succ_ofAdd` states that the successor commutes with the map into `Multiplicative α`.

#### Common errors

1. The lemma `Order.add_one_le_iff` needs `NoMaxOrder`. On the extended naturals the top element $\top$ satisfies $\top + 1 = \top$, and $\top + 1 \le \top$ holds while $\top < \top$ does not. Use `Order.add_one_le_iff_of_not_isMax` with a proof that $x \ne \top$.
2. On $\mathbb{N}$, the lemma `Set.Ioc_sub_one_left_eq_Icc` needs care at $0$, because $0 - 1 = 0$. Use the form with the suffix *of_not_isMin*, which asks that $a$ is not minimal, that is $a \ne 0$.
3. The lemma `monotone_of_le_add_one` needs `IsSuccArchimedean`. On the ordinals the step condition does not reach the limit ordinals, so a function with $f(\alpha) \le f(\alpha + 1)$ for each $\alpha$ need not be monotone.

### Exercises

1. (A) Prove `Order.lt_add_one_iff` on $\mathbb{N}$ from `Order.succ_eq_add_one` and the lemma `Order.lt_succ_iff` of the first section.
2. (A) Use `Order.le_one_iff` to list the natural numbers $n$ with $n \le 1$, and explain why the same lemma does not apply to $\mathbb{Z}$.
3. (B) Prove `monotone_of_le_add_one` for $\mathbb{N}$ by induction on $b - a$, without the archimedean class.
4. (B) Use `Finset.insert_Icc_right_eq_Icc_add_one` to prove $\sum_{i \in [1, n]} i = n (n + 1)/2$ by induction on $n$.
5. (B) Show that `Order.add_one_le_iff` fails on the extended naturals, and check the form with the hypothesis $x \ne \top$.
6. (C) Prove that a nontrivial linearly ordered additive group with a locally finite order has a least positive element $g$, and that each element is a multiple $n g$ with $n \in \mathbb{Z}$.

### Reference

<?reference?>
