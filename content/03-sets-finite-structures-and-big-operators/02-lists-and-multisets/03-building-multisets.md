---
title: "Building multisets: insertion, sums, differences and counts"
kind: api
modules:
  - Mathlib.Data.Multiset.ZeroCons
  - Mathlib.Data.Multiset.Basic
  - Mathlib.Data.Multiset.AddSub
  - Mathlib.Data.Multiset.Count
  - Mathlib.Data.Multiset.Replicate
  - Mathlib.Data.Multiset.Range
  - Mathlib.Data.Multiset.Pairwise
  - Mathlib.Data.Multiset.OrderedMonoid
explains:
  E2: [Multiset.induction_on, Multiset.cons_eq_cons, Multiset.exists_cons_of_mem, Multiset.strongInductionOn, Multiset.le_iff_exists_add, Multiset.sub_le_iff_le_add, Multiset.cons_erase, Multiset.le_iff_count, Multiset.le_count_iff_replicate_le, Multiset.range_succ]
  E1: auto
families: []
requires: [V01.C02, V03.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Building multisets: insertion, sums, differences and counts

### Overview

Section 1 of this chapter defines a multiset as a list up to permutation and gives its card and its counts. This section gives the ways to build multisets and to take them apart. The empty multiset is $0$, and `a ::ₘ s` adds one copy of $a$ to $s$. Every multiset is built from $0$ by insertion, so induction on multisets has the same two cases as induction on lists. The sum $s + t$ adds the counts, the difference $s - t$ subtracts them with truncation at $0$, and the order $s \le t$ compares them.

The section also gives the multiset `Multiset.replicate n a` with $n$ copies of $a$, the multiset `Multiset.range n` $= \{0, 1, \dots, n-1\}$, the predicate `Multiset.Pairwise`, and the strong induction on multisets. All rules here hold with no condition on $\alpha$, except that the difference, the count and the erasure need decidable equality.

### The library around it

#### Zero, insertion and induction

The module `Mathlib.Data.Multiset.ZeroCons` defines `0 : Multiset α`, the image of the empty list, and `Multiset.cons a s`, written `a ::ₘ s`, the image of `a :: l`. The singleton $\{a\}$ is `a ::ₘ 0`, and `{a, b}` is `a ::ₘ {b}`. The order of insertion does not matter: `Multiset.cons_swap` gives `a ::ₘ b ::ₘ s = b ::ₘ a ::ₘ s`. The membership rule `Multiset.mem_cons` gives $x \in a ::_m s$ if and only if $x = a$ or $x \in s$.

Since each list is built from the empty list, each multiset is built from $0$:

$$P(0),\quad (\forall a\, s,\ P(s) \to P(a ::_m s)) \implies \forall s,\ P(s).$$

This is `Multiset.induction_on`, and `Multiset.induction` is the same rule with the multiset as the last argument. Use it with `induction s using Multiset.induction_on with ...` in tactic mode. The recursor `Multiset.rec` makes a function by the same two cases, but it needs a proof that the step does not depend on the order of insertion.

Two insertions are equal only in two ways:

$$a ::_m s = b ::_m t \iff (a = b \text{ and } s = t) \text{ or } (a \ne b \text{ and } \exists u,\ s = b ::_m u,\ t = a ::_m u).$$

This is `Multiset.cons_eq_cons`. The second case appears because the copy of $a$ on the left can match a copy in $t$. A member can always be taken out: if $a \in s$, then $s = a ::_m t$ for some $t$ (`Multiset.exists_cons_of_mem`). The rules for the card give `Multiset.card_cons`, `Multiset.card_zero`, and the descriptions of small multisets `Multiset.card_eq_one`, `Multiset.card_eq_two` and `Multiset.card_eq_three`. For example, `Multiset.card_eq_two` gives $|s| = 2 \iff \exists x\, y,\ s = \{x, y\}$.

The module also gives the relation `Multiset.Rel r s t`: there is a bijection between the elements of $s$ and $t$ that relates each element to its image by $r$. The rule `Multiset.rel_eq` says that for equality it is equality of multisets, and `Multiset.card_eq_card_of_rel` gives equal cards.

#### The order on multisets

The order $s \le t$ says that $s$ is a sub multiset of $t$, the image of the sublist order up to permutation. Insertion is monotone and cancellable: `Multiset.cons_le_cons_iff` gives $a ::_m s \le a ::_m t \iff s \le t$. The bottom is $0$ (`Multiset.instOrderBot`, `Multiset.le_zero`), and the strict order has a description by insertion: $s < t$ if and only if $a ::_m s \le t$ for some $a$ (`Multiset.lt_iff_cons_le`).

The order is well founded, because the card goes down along it. The module `Mathlib.Data.Multiset.Basic` gives the strong induction: `Multiset.strongInductionOn s H` builds a value at $s$ from the values at all $t < s$, and `Multiset.strongInductionOn_eq` unfolds one step. The form `Multiset.strongDownwardInduction` goes up instead of down, for multisets with card at most $n$. The same module gives `Multiset.toList`, a list in the class of a multiset chosen by the axiom of choice, with `Multiset.coe_toList` saying that its class is the multiset, and `Multiset.choose`, the unique element with a property.

#### Sums and differences

The module `Mathlib.Data.Multiset.AddSub` gives the sum $s + t$, the image of the concatenation of lists, and the difference $s - t$, which removes from $s$ one copy of each element of $t$. The module proves that the sum is associative, commutative and cancellative (`Multiset.add_comm`, `Multiset.add_right_inj`), and the module `Mathlib.Algebra.Order.Monoid.Multiset` adds the instances of an ordered cancellative monoid. The order is the order of the monoid:

$$s \le t \iff \exists u,\ t = s + u.$$

This is `Multiset.le_iff_exists_add`. The difference is the truncated subtraction of this order, so it satisfies the Galois rule of an ordered monoid with truncated subtraction:

$$s - t \le u \iff s \le u + t.$$

This is `Multiset.sub_le_iff_le_add`, and the difference of an inequality cancels: `Multiset.sub_add_cancel` gives $s - t + t = s$ when $t \le s$. The card of a difference is the difference of the cards for $t \le s$ (`Multiset.card_sub`), and `Multiset.mem_sub` says that $a \in s - t$ if and only if $a$ has more copies in $s$ than in $t$.

The erasure `Multiset.erase s a` removes one copy of $a$. It is $s - \{a\}$ (`Multiset.sub_singleton`). If $a \in s$, then inserting $a$ again gives $s$:

$$a \in s \implies a ::_m \operatorname{erase}(s, a) = s.$$

This is `Multiset.cons_erase`, and `Multiset.card_erase_of_mem` gives the card $|s| - 1$. If $a \notin s$, the erasure does nothing (`Multiset.erase_of_notMem`). The rule `Multiset.add_singleton_eq_iff` says that $s + \{a\} = t$ if and only if $a \in t$ and $s = \operatorname{erase}(t, a)$.

#### Counts and the extensionality rule

The module `Mathlib.Data.Multiset.Count` gives the count `Multiset.countP p s` of the elements with property $p$, and the count `Multiset.count a s` of the copies of $a$. Each operation of the last subsection has a rule for the counts: `Multiset.count_cons`, `Multiset.count_sub` and `Multiset.count_erase_self`. The count determines the multiset, and it also determines the order:

$$s = t \iff \forall a,\ \operatorname{count}(a, s) = \operatorname{count}(a, t), \qquad s \le t \iff \forall a,\ \operatorname{count}(a, s) \le \operatorname{count}(a, t).$$

These are `Multiset.ext` and `Multiset.le_iff_count`. A proof of an identity of multisets often goes by `Multiset.ext'`: take an arbitrary $a$ and compute the counts on the two sides with the simplifier, which knows the count rules of each operation. The rule `Multiset.card_eq_countP_add_countP` splits the card into the counts of $p$ and of its negation, and `Multiset.countP_eq_card` says that the count of $p$ is the card if and only if each element has property $p$.

#### Replicate, range and pairwise relations

The multiset `Multiset.replicate n a` has $n$ copies of $a$. Its count is $n$ at $a$ and $0$ elsewhere (`Multiset.count_replicate`), and the module `Mathlib.Data.Multiset.Replicate` gives the rules `Multiset.card_replicate`, `Multiset.mem_replicate` and `Multiset.replicate_add`. The count of $a$ in $s$ is at least $n$ if and only if $s$ contains $n$ copies of $a$:

$$n \le \operatorname{count}(a, s) \iff \operatorname{replicate}(n, a) \le s.$$

This is `Multiset.le_count_iff_replicate_le`. The sub multisets of a replicate are replicates (`Multiset.le_replicate_iff`). The module also gives two forms of the predicate Nodup: `Multiset.nodup_iff_ne_cons_cons` says that $s$ has no duplicate if and only if $s$ is never of the form $a ::_m a ::_m t$, and `Multiset.nodup_iff_pairwise` says that $s$ has no duplicate if and only if its elements are pairwise distinct.

The predicate `Multiset.Pairwise r s` says that some list in the class of $s$ is pairwise related by $r$. For a symmetric relation, `Multiset.Pairwise.forall` turns it into the statement for each two distinct elements of $s$.

The multiset `Multiset.range n` is $\{0, 1, \dots, n - 1\}$, the image of the list $[0, 1, \dots, n - 1]$. The module `Mathlib.Data.Multiset.Range` gives the membership rule `Multiset.mem_range` ($m \in \operatorname{range}(n) \iff m < n$), the card `Multiset.card_range`, and `Multiset.nodup_range`. The step rule

$$\operatorname{range}(n + 1) = n ::_m \operatorname{range}(n)$$

is `Multiset.range_succ`. The finset `Finset.range n` of Chapter 3 is built from it, and `Multiset.range_succ` gives the step of the sums $\sum_{i < n+1} f(i)$ of Chapter 6. The module `Mathlib.Data.Multiset.OrderedMonoid` is deprecated and only imports `Mathlib.Algebra.Order.Monoid.Multiset`.

#### Common errors

1. A learner proves `a ::ₘ s = b ::ₘ t → s = t` with no condition. It fails when $a \ne b$, for example $1 ::_m \{2\} = 2 ::_m \{1\}$. Use `Multiset.cons_eq_cons` and handle both cases.
2. A learner expects $s - t + t = s$ for all multisets. It needs $t \le s$; for $s = 0$ and $t = \{a\}$ the left side is $\{a\}$.
3. A learner tries `induction s` on a multiset and gets a goal about the quotient. Use `induction s using Multiset.induction_on`.

### Exercises

1. (A) Compute $\{1, 1, 2, 3\} - \{1, 2, 2\}$ and $\{1, 1, 2, 3\} + \{1, 2, 2\}$, and check the counts.
2. (A) Prove $\operatorname{card}(\operatorname{replicate}(n, a) + \operatorname{replicate}(m, a)) = n + m$.
3. (B) Prove `Multiset.le_iff_exists_add` in the direction from right to left with `Multiset.le_iff_count`.
4. (B) Prove by `Multiset.induction_on` that $\operatorname{count}(a, s) \le |s|$.
5. (B) Use `Multiset.ext'` to prove $(s - t) + (s \cap t) = s$ for multisets, where $\operatorname{count}(a, s \cap t) = \min(\operatorname{count}(a, s), \operatorname{count}(a, t))$.
6. (C) Use `Multiset.strongInductionOn` to prove that each nonzero multiset of natural numbers has a member that is at least each other member.

### Reference

<?reference?>
