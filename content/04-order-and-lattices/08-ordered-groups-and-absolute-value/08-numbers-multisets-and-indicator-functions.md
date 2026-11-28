---
title: Numbers, multisets and indicator functions
kind: api
modules:
  - Mathlib.Algebra.Order.Group.Int
  - Mathlib.Algebra.Order.Group.Unbundled.Int
  - Mathlib.Algebra.Order.Group.Int.Sum
  - Mathlib.Algebra.Order.Group.Nat
  - Mathlib.Algebra.Order.Monoid.PNat
  - Mathlib.Algebra.Order.Group.Multiset
  - Mathlib.Algebra.Order.Monoid.Multiset
  - Mathlib.Algebra.Order.Group.Finset
  - Mathlib.Algebra.Order.Group.Indicator
  - Mathlib.Algebra.Order.Group.PartialSups
  - Mathlib.Algebra.Order.Disjointed
  - Mathlib.Algebra.Order.SuccPred.PartialSups
explains:
  E2: [Nat.instOrderedSub, Int.abs_eq_natAbs, Int.emod_lt_abs, Finset.sum_range_le_sum, Multiset.instOrderedSub, Multiset.le_card_smul_iff_subset, Finset.sup_add_sup, Set.indicator_le_indicator_of_subset, Set.indicator_le_self, partialSups_add_one_eq_sup_disjointed]
  E1: auto
families: []
requires: [V04.C01, V04.C03, V04.C04, V01.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Numbers, multisets and indicator functions

### Overview

The earlier sections of this chapter state results for each ordered monoid or group. This section collects the files that apply them to particular types and operations. They give the instances for $\mathbb{N}$, $\mathbb{Z}$ and the positive naturals, and the order of multisets. They also prove inequalities for finite suprema, indicator functions, partial suprema and disjointed sequences, in each case when the values lie in an ordered monoid.

Most of these results are short. Their value is in the names. A proof about $\mathbb{N}$ often needs only to know that $\mathbb{N}$ has `OrderedSub`, and a proof about a measure often needs only that an indicator function is below the function.

### The library around it

#### Natural numbers and integers

The file `Mathlib.Algebra.Order.Group.Nat` gives $\mathbb{N}$ its classes: `Nat.instIsOrderedCancelAddMonoid`, the canonical order `Nat.instCanonicallyOrderedAdd`, and the truncated subtraction `Nat.instOrderedSub`. With the last instance, each lemma of Section 5 applies to subtraction on $\mathbb{N}$. For example, `tsub_add_cancel_of_le` gives $n - m + m = n$ for $m \le n$. The same file has `Nat.pow_left_strictMono`, which states that $x \mapsto x^n$ is strictly monotone for $n \ne 0$, and its form for functions `StrictMono.nat_pow`.

The file `Mathlib.Algebra.Order.Group.Int` gives `Int.instIsOrderedAddMonoid`. The file `Mathlib.Algebra.Order.Group.Unbundled.Int` links the absolute value of Section 1 to the functions of $\mathbb{Z}$. The lemma `Int.abs_eq_natAbs` states $|a| = \mathrm{natAbs}(a)$, with the natural number cast to $\mathbb{Z}$, and `Int.natCast_natAbs` is the same equation in the other direction. The lemma `Int.sign_mul_abs` states $\mathrm{sign}(a) \cdot |a| = a$. For division with remainder, `Int.emod_lt_abs` states $a \bmod b < |b|$ for $b \ne 0$, and `Int.emod_abs` states that the remainder does not change when $b$ is replaced by $|b|$. Other lemmas are `Int.abs_le_one_iff`, which lists the three integers with $|a| \le 1$, and `Int.abs_sub_lt_of_lt_lt`, which bounds the difference of two naturals below $m$. The lemma `zpow_abs_eq_one` states $a^{|n|} = 1 \leftrightarrow a^n = 1$ in each group.

The file `Mathlib.Algebra.Order.Group.Int.Sum` bounds the sum of a finite set of integers. If each element of $s$ is at least $c$, then `Finset.sum_range_le_sum` states
$$\sum_{n < |s|} (c + n) \le \sum_{x \in s} x.$$
The reason is that the $k$-th element of $s$ in increasing order is at least $c + k$, because the elements are distinct integers. The dual `Finset.sum_le_sum_Ioc` bounds the sum above when each element is at most $c$.

The file `Mathlib.Algebra.Order.Monoid.PNat` gives `PNat.equivNonZeroDivisorsNat`, an isomorphism of ordered monoids from the positive naturals to the submonoid of nonzero divisors of $\mathbb{N}$.

#### Multisets

A multiset is a canonically ordered additive monoid. The order $s \le t$ states that each element has at most as many copies in $s$ as in $t$, and $s \le t$ holds exactly when $t = s + u$ for some $u$. The instances are `Multiset.instCanonicallyOrderedAdd` and `Multiset.instIsOrderedCancelAddMonoid`. The truncated subtraction removes copies, and `Multiset.instOrderedSub` makes it an `OrderedSub`.

The file `Mathlib.Algebra.Order.Group.Multiset` has the lemmas that combine the order with the multiples $n \cdot t$. The lemma `Multiset.le_card_smul_iff_subset` states that $s \le |s| \cdot t$ if and only if each element of $s$ is in $t$. For the proof, an element of $s$ has at most $|s|$ copies in $s$, and $|s| \cdot t$ has at least $|s|$ copies of each element of $t$. The lemma `Multiset.Nodup.le_nsmul_iff_le` states that, for a multiset $s$ without repeated elements and $n \ne 0$, the inequality $s \le n \cdot t$ is equivalent to $s \le t$. The file also gives maps such as `Multiset.countAddMonoidHom`, the number of copies of an element as an additive map.

#### Finite suprema

The file `Mathlib.Algebra.Order.Group.Finset` moves an addition across a finite supremum. In a linearly ordered group, `Finset.sup'_add` states that the supremum of $f$ over a nonempty finite set, plus $a$, is the supremum of $f + a$. In a canonically ordered monoid, `Finset.sup_add_sup` states
$$\sup_{i \in s} f(i) + \sup_{j \in t} g(j) = \sup_{(i, j) \in s \times t} (f(i) + g(j))$$
for nonempty $s$ and $t$. The proof applies `Finset.sup_add` and `Finset.add_sup` once each and then uses the supremum over a product. Other forms treat powers and multiples, such as `Finset.sup'_pow` and `Finset.nsmul_sup'`.

#### Indicator functions

The indicator function of a set $s$ and a function $f$ is $f$ on $s$ and $0$ outside $s$. The file `Mathlib.Algebra.Order.Group.Indicator` gives its order properties. The lemma `Set.indicator_nonneg` states that the indicator is nonnegative if $f$ is nonnegative on $s$. The lemma `Set.indicator_le_indicator_of_subset` states that for $s \subseteq t$ and $f \ge 0$, the indicator on $s$ is below the indicator on $t$. In a type where $0$ is the least element, `Set.indicator_le_self` states that the indicator is below $f$. These three lemmas carry most estimates in integration, where a function is cut to a set. The multiplicative forms, with $1$ in place of $0$, are the lemmas about `Set.mulIndicator`, such as `Set.one_le_mulIndicator`.

The file also has the lemmas for suprema. The lemma `Set.iSup_indicator` moves an indexed supremum inside the indicator for monotone families of sets and functions, when $\bot = 0$. For the support, `Function.support_sup` states that the support of $f \sqcup g$ is in the union of the supports. In a lattice-ordered group, `Set.abs_indicator_symmDiff` states that the absolute value of the indicator on the symmetric difference $s \mathbin{\triangle} t$ equals the absolute difference of the two indicators.

#### Partial suprema and disjointed sequences

Chapter 4 defines the partial suprema $\mathrm{partialSups}(f)(i) = \bigsqcup_{j \le i} f(j)$, and Chapter 3 defines the disjointed sequence of $f$, whose term at $i$ is $f(i)$ minus the earlier terms. The disjointed sequence has the same partial suprema as $f$, and its terms are pairwise disjoint. This is the usual step that turns a countable union into a disjoint union in measure theory. The files `Mathlib.Algebra.Order.SuccPred.PartialSups` and `Mathlib.Algebra.Order.Disjointed` give their recursion when the index type has an addition and the successor is $i + 1$, as in $\mathbb{N}$. The lemma `partialSups_add_one` states that $\mathrm{partialSups}(f)(i + 1) = \mathrm{partialSups}(f)(i) \sqcup f(i + 1)$. In a generalized Boolean algebra, `disjointed_add_one` states that $\mathrm{disjointed}(f)(i + 1)$ is $f(i + 1)$ minus the partial supremum at $i$, and `partialSups_add_one_eq_sup_disjointed` states that $\mathrm{partialSups}(f)(i + 1)$ is the supremum of $\mathrm{partialSups}(f)(i)$ and $\mathrm{disjointed}(f)(i + 1)$. The recursion `Nat.disjointedRec` proves a property of each term of a disjointed sequence from the same property of $f(n)$. The file `Mathlib.Algebra.Order.Group.PartialSups` states that addition of a constant commutes with partial suprema, as `partialSups_add_const`.

#### Common errors

1. On $\mathbb{N}$, the lemma `sub_add_cancel` does not apply, because $\mathbb{N}$ is not a group. Use `tsub_add_cancel_of_le` with a proof of $m \le n$.
2. The lemma `Set.indicator_le_self` needs $0$ to be the least element. On a type with negative values, use `Set.indicator_le_indicator_of_subset` with $t$ the whole type, which needs $f \ge 0$.
3. The lemma `Int.emod_lt_abs` bounds $a \bmod b$ by $|b|$ and not by $b$. For negative $b$, the remainder is still nonnegative.

### Exercises

1. (A) Prove $n - m + m = \max(n, m)$ on $\mathbb{N}$ from the lemmas of Section 5 and `Nat.instOrderedSub`.
2. (A) Prove `Int.sign_mul_abs` by cases on the sign of $a$.
3. (B) Prove `Multiset.le_card_smul_iff_subset`, with the function `Multiset.count`.
4. (B) Prove `Finset.sum_range_le_sum` by induction on the size of $s$, and deduce that a set of $n$ positive integers has sum at least $n(n + 1)/2$.
5. (B) Show that `Set.indicator_le_self` fails on $\mathbb{Z}$, and give the correct form with a hypothesis on $f$.
6. (C) Prove `partialSups_add_one_eq_sup_disjointed` for $\mathbb{N}$ and sets, from `partialSups_add_one` and `disjointed_add_one`.

### Reference

<?reference?>
