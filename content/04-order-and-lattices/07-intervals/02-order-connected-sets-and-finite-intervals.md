---
title: Order-connected sets, unordered intervals and finite intervals
kind: theory
modules:
  - Mathlib.Order.Interval.Set.OrdConnected
  - Mathlib.Order.Interval.Set.UnorderedInterval
  - Mathlib.Order.Interval.Finset.Defs
  - Mathlib.Order.Interval.Finset.Nat
explains:
  E3: [Set.OrdConnected, LocallyFiniteOrder]
  E2: [Set.ordConnected_iff, Set.OrdConnected.inter, Set.OrdConnected.preimage_mono, Set.uIcc, Set.mem_uIcc, Set.uIcc_comm, Set.ordConnected_iff_uIcc_subset, Finset.Icc, Finset.mem_Icc, Finset.coe_Icc, Nat.card_Icc, Nat.card_Ico]
  E1: auto
families: []
requires: [V04.C01, V01.C02]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C07/Examples.lean
  - MathlibHandbook/V04/C07/Exercises.lean
  - MathlibHandbook/V04/C07/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Order-connected sets, unordered intervals and finite intervals

### Overview

A set is *order-connected* if, with two of its elements, it contains all the elements between them. Each interval has this property, and in $\mathbb{R}$ the converse holds: an order-connected set of reals is an interval. The proof uses the completeness of $\mathbb{R}$, and the rationals show that completeness is necessary.

In $\mathbb{N}$ and in $\mathbb{Z}$ each bounded interval is finite. Mathlib has the class `LocallyFiniteOrder` for such orders and the finite intervals `Finset.Icc a b`. The section proves that the interval $[a, b]$ of $\mathbb{N}$ has $b + 1 - a$ elements, with the truncated subtraction. It also defines the unordered interval $[[a, b]]$, which does not depend on the order of the ends.

### Definitions

**Definition (Order-connected set).** Let $\alpha$ be a preorder. A set $s \subseteq \alpha$ is *order-connected* if for all $x, y \in s$, the interval $[x, y]$ is contained in $s$.

*Remarks.* Only the pairs with $x \le y$ matter, because $[x, y] = \emptyset$ otherwise. Some books call such a set *convex*. Mathlib uses the name `OrdConnected`, because "convex" has another meaning in a vector space.

The condition is for each pair: the set $\{0\} \cup [1, 2]$ in $\mathbb{R}$ contains $0$ and $1$, but not $\frac12 \in [0, 1]$.

::: mathlib
`Set.OrdConnected` · `Mathlib.Order.Interval.Set.Defs`

`Set.OrdConnected s` is a class with one field, `out'`, which states `∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → Set.Icc x y ⊆ s`. It is a class so that instance search can prove it: the instances `Set.ordConnected_Icc`, `Set.ordConnected_Ioi` and the others cover each interval. The accessor `Set.OrdConnected.out` gives the condition back.

<?decl Set.OrdConnected?>
:::

::: mathlib
`Set.ordConnected_iff` · `Mathlib.Order.Interval.Set.OrdConnected`

The lemma states the definition as an equivalence, with the hypothesis `x ≤ y` made explicit. A proof starts with `rw [Set.ordConnected_iff]`.

<?decl Set.ordConnected_iff?>
:::

**Definition (Unordered interval).** Let $\alpha$ be a lattice and let $a, b \in \alpha$. The unordered interval is $[[a, b]] = [a \sqcap b, a \sqcup b]$.

In a linear order, $a \sqcap b = \min(a, b)$ and $a \sqcup b = \max(a, b)$, so $[[a, b]]$ is the closed interval between $a$ and $b$, whichever of them is larger. In $\mathbb{R}$, $[[3, 1]] = [1, 3]$.

::: mathlib
`Set.uIcc` · `Mathlib.Order.Interval.Set.UnorderedInterval`

The definition is `Set.Icc (a ⊓ b) (a ⊔ b)` in a `Lattice`, with the notation `[[a, b]]` after `open Interval`. Analysis uses it when the order of the ends is not known, as in `intermediate_value_uIcc`.

<?decl Set.uIcc?>
:::

**Definition (Locally finite order).** A preorder $\alpha$ is *locally finite* if each closed interval $[a, b]$ is a finite set.

The other bounded intervals $[a, b)$, $(a, b]$, $(a, b)$ are subsets of $[a, b]$, so they are finite too. The rays need not be finite: in $\mathbb{N}$, the ray $[0, \infty)$ is all of $\mathbb{N}$.

::: mathlib
`LocallyFiniteOrder` · `Mathlib.Order.Interval.Finset.Defs`

The class holds data: functions `finsetIcc`, `finsetIco`, `finsetIoc` and `finsetIoo` that give the intervals as values of type `Finset α`, with fields for their membership. So Lean can compute: on `ℕ`, `decide` lists the elements of an interval. The instances include `Nat.instLocallyFiniteOrder` and `Int.instLocallyFiniteOrder`. The theorem `Set.finite_Icc` gives the propositional form.

<?decl LocallyFiniteOrder?>
:::

::: mathlib
`Finset.Icc` · `Mathlib.Order.Interval.Finset.Defs`

The function `Finset.Icc a b` is `LocallyFiniteOrder.finsetIcc a b`. The membership lemma is `Finset.mem_Icc`, and `Finset.coe_Icc` states that its coercion to a set is `Set.Icc a b`.

<?decl Finset.Icc?>
:::

### Theorems and proofs

**Theorem (Intervals are order-connected).** In a preorder, each of the nine kinds of intervals is order-connected.

*Proof.* Take $[a, b]$. Let $x, y \in [a, b]$ and let $z \in [x, y]$. Then $a \le x \le z$ gives $a \le z$, and $z \le y \le b$ gives $z \le b$. So $z \in [a, b]$. For $(a, b)$, the same argument works with $a < x \le z$, which gives $a < z$ by mixed transitivity, and $z \le y < b$, which gives $z < b$. The half-open intervals mix the two arguments. For a ray such as $[a, \infty)$, only the left inequality appears, and for $\operatorname{univ}$ there is nothing to prove. $\square$

**Theorem (Stability).** Let $\alpha$ and $\beta$ be preorders.

1. The intersection of a family of order-connected subsets of $\alpha$ is order-connected.
2. If $f : \beta \to \alpha$ is monotone and $s \subseteq \alpha$ is order-connected, then $f^{-1}(s)$ is order-connected.

*Proof.* 1. Let $(s_i)_{i \in I}$ be the family and let $x, y \in \bigcap_i s_i$. For each $i$, the elements $x$ and $y$ are in $s_i$, so $[x, y] \subseteq s_i$. Thus $[x, y] \subseteq \bigcap_i s_i$.

2. Let $x, y \in f^{-1}(s)$ and let $x \le z \le y$. Then $f(x), f(y) \in s$, and monotonicity gives $f(x) \le f(z) \le f(y)$. So $f(z) \in [f(x), f(y)] \subseteq s$, that is, $z \in f^{-1}(s)$. $\square$

The union of two order-connected sets need not be order-connected: $[0, 1] \cup [2, 3]$ is not. The image under a monotone map need not be order-connected either: the inclusion $\mathbb{Z} \to \mathbb{R}$ is monotone, $\mathbb{Z}$ is order-connected in itself, and its image is not order-connected in $\mathbb{R}$.

The next theorem is the converse of the first one for the real numbers. It uses the supremum and the infimum of Chapter 5.

**Theorem (Order-connected sets of reals).** Let $s \subseteq \mathbb{R}$ be nonempty and order-connected. Put $m = \inf s$ if $s$ is bounded below and $m = -\infty$ otherwise, and $M = \sup s$ if $s$ is bounded above and $M = +\infty$ otherwise. Then $(m, M) \subseteq s \subseteq [m, M]$, where the brackets at an infinite end mean the ray. So $s$ is an interval with the ends $m$ and $M$, and it is one of $(m, M)$, $[m, M)$, $(m, M]$, $[m, M]$.

*Proof.* The plan has two steps. The inclusion $s \subseteq [m, M]$ follows from the definitions of $m$ and $M$. The inclusion $(m, M) \subseteq s$ uses the order-connectedness.

*Step 1.* Let $x \in s$. If $s$ is bounded below, then $m = \inf s$ is a lower bound of $s$, so $m \le x$. If $s$ is not bounded below, then $m = -\infty$ and there is no condition. In the same way $x \le M$. So $s \subseteq [m, M]$.

*Step 2.* Let $m < x < M$. First, there is $a \in s$ with $a \le x$. Indeed, if $s$ is bounded below, then $x > \inf s$, so $x$ is not a lower bound of $s$, because $\inf s$ is the greatest lower bound. Thus some $a \in s$ has $a < x$. If $s$ is not bounded below, then $x$ is not a lower bound of $s$, and again some $a \in s$ has $a < x$. In the same way there is $b \in s$ with $x < b$. Now $a, b \in s$ and $a \le x \le b$, so $x \in [a, b] \subseteq s$. Thus $(m, M) \subseteq s$.

*Conclusion.* The set $s$ lies between $(m, M)$ and $[m, M]$. The two sets differ by at most the two ends $m$ and $M$, when they are finite. So $s$ is $(m, M)$ with $m$ added or not, and with $M$ added or not. These are the four forms of the statement. If $m = M$, then $s \subseteq [m, m] = \{m\}$ and $s$ is nonempty, so $s = \{m\} = [m, m]$, which is one of the four forms. $\square$

The proof used the existence of $\inf s$ and $\sup s$ for a bounded nonempty set. This is the completeness of $\mathbb{R}$, and it is necessary, as a counterexample below shows.

**Theorem (Unordered intervals).** Let $\alpha$ be a lattice.

1. $[[a, b]] = [[b, a]]$.
2. If $a \le b$, then $[[a, b]] = [a, b]$.
3. If $\alpha$ is a linear order, then $x \in [[a, b]]$ if and only if $a \le x \le b$ or $b \le x \le a$.
4. If $\alpha$ is a linear order, then $s$ is order-connected if and only if $[[x, y]] \subseteq s$ for all $x, y \in s$.

*Proof.* 1. The operations are commutative: $a \sqcap b = b \sqcap a$ and $a \sqcup b = b \sqcup a$. So the two intervals have the same ends.

2. If $a \le b$, then $a \sqcap b = a$ and $a \sqcup b = b$ (Chapter 3), so $[[a, b]] = [a, b]$.

3. By totality, $a \le b$ or $b \le a$. If $a \le b$, then $[[a, b]] = [a, b]$ by part 2, and $x \in [a, b]$ means $a \le x \le b$. In this case the condition $b \le x \le a$ gives $b \le a$, so $a = b = x$, and then $a \le x \le b$ holds as well. So the disjunction is equivalent to $a \le x \le b$. The case $b \le a$ is the same, with parts 1 and 2.

4. Suppose $s$ is order-connected and $x, y \in s$. If $x \le y$, then $[[x, y]] = [x, y] \subseteq s$. If $y \le x$, then $[[x, y]] = [y, x] \subseteq s$. Conversely, suppose $[[x, y]] \subseteq s$ for all $x, y \in s$, and let $x \le y$ in $s$. Then $[x, y] = [[x, y]] \subseteq s$. $\square$

The last result counts the elements of an interval of natural numbers. In $\mathbb{N}$ the subtraction is truncated: $m - n = 0$ when $m \le n$. With this convention the formula needs no case split.

**Theorem (Number of elements).** For $a, b \in \mathbb{N}$, the interval $[a, b]$ has $b + 1 - a$ elements, and $[a, b)$ has $b - a$ elements.

*Proof.* Suppose first that $a \le b$. Let $n = b - a$, so $b = a + n$. The map $\varphi : \{0, 1, \dots, n\} \to [a, b]$, $\varphi(k) = a + k$, is well defined, since $a \le a + k \le a + n = b$. It is injective, since $a + k = a + l$ gives $k = l$. It is surjective: for $x \in [a, b]$, the number $k = x - a$ satisfies $0 \le k \le n$ and $a + k = x$, because $a \le x$. So $[a, b]$ has as many elements as $\{0, \dots, n\}$, that is, $n + 1$. Since $a \le b$, $n + 1 = (b - a) + 1 = b + 1 - a$.

Suppose now that $b < a$. Then $[a, b]$ is empty by the previous section, so it has $0$ elements. Since $b + 1 \le a$, the truncated difference $b + 1 - a$ is $0$ too.

For $[a, b)$: if $a < b$, then $[a, b) = [a, b - 1]$, because $x < b$ is the same as $x \le b - 1$ in $\mathbb{N}$ when $b \ge 1$. The first part gives $(b - 1) + 1 - a = b - a$ elements. If $b \le a$, then $[a, b)$ is empty and $b - a = 0$. $\square$

::: mathlib
`Nat.card_Icc` · `Mathlib.Order.Interval.Finset.Nat`

The statement is `(Finset.Icc a b).card = b + 1 - a` with the subtraction of `ℕ`. The Lean proof avoids the bijection of the text: the instance builds the interval as a list of length `b + 1 - a`. The partners are `Nat.card_Ico : (Finset.Ico a b).card = b - a`, `Nat.card_Ioc` and `Nat.card_Ioo`. On `ℤ`, `Int.card_Icc` states `(Finset.Icc a b).card = (b + 1 - a).toNat`.

<?decl Nat.card_Icc?>
:::

::: mathlib
`Set.mem_uIcc` · `Mathlib.Order.Interval.Set.UnorderedInterval`

This is part 3 of the theorem, in a `LinearOrder`. The parts 1 and 2 are `Set.uIcc_comm` and `Set.uIcc_of_le`, and part 4 is `Set.ordConnected_iff_uIcc_subset`. The lemma `Set.Icc_subset_uIcc` states `Set.Icc a b ⊆ Set.uIcc a b` with no hypothesis.

<?decl Set.mem_uIcc?>
:::

::: mathlib
`Set.OrdConnected.preimage_mono` · `Mathlib.Order.Interval.Set.OrdConnected`

This is part 2 of the theorem on stability. Part 1 is `Set.ordConnected_iInter`, and `Set.OrdConnected.inter` for two sets. In topology, `isPreconnected_iff_ordConnected` states that in a densely ordered, conditionally complete linear order, a set is connected if and only if it is order-connected.

<?decl Set.OrdConnected.preimage_mono?>
:::

### Examples

**Example (A finite interval).** In $\mathbb{N}$ the interval $[1, 4]$ is the finite set $\{1, 2, 3, 4\}$. The tactic `decide` computes it, because the instance of `LocallyFiniteOrder` on `ℕ` is a list.

<?lean MathlibHandbook/V04/C07/Examples.lean#finset?>

**Example (Counting).** The interval $[3, 10]$ of $\mathbb{N}$ has $10 + 1 - 3 = 8$ elements, and $[3, 10)$ has $10 - 3 = 7$. The interval $[10, 3]$ is empty, and $3 + 1 - 10 = 0$ in $\mathbb{N}$. In $\mathbb{Z}$, $[-3, 5]$ has $5 + 1 - (-3) = 9$ elements.

**Example (Order-connected sets).** In $\mathbb{R}$, the set $\{x \mid x^2 < 4\}$ is order-connected and equal to $(-2, 2)$, with $m = -2$ and $M = 2$, and neither end is in the set. The set $\{x \mid x \ne 0\}$ is not order-connected: it contains $-1$ and $1$ and not $0$.

**Counterexample (Completeness is necessary).** In $\mathbb{Q}$, let $s = \{x \in \mathbb{Q} \mid x^2 < 2\}$. The set $s$ is order-connected. Let $x, z \in s$ and $x \le y \le z$. If $y \ge 0$, then $0 \le y \le z$ gives $y^2 \le z^2 < 2$. If $y < 0$, then $x \le y < 0$ gives $0 < -y \le -x$, so $y^2 \le x^2 < 2$. In both cases $y \in s$. But $s$ is not an interval of $\mathbb{Q}$ with ends in $\mathbb{Q}$. The set is bounded, since $x^2 < 2$ gives $|x| < 2$, so an interval equal to $s$ would have two rational ends $a$ and $b$. It contains $0$ and $1$, so it is not a singleton, and $a < b$. In $\mathbb{R}$, the supremum of an interval of $\mathbb{Q}$ with the right end $b$ is $b$, because $\mathbb{Q}$ is dense in $\mathbb{R}$. The supremum of $s$ in $\mathbb{R}$ is $\sqrt 2$, for the same reason. So $b = \sqrt 2$, and this contradicts the irrationality of $\sqrt 2$. The proof of the theorem fails at the existence of $\sup s$ in $\mathbb{Q}$.

**Counterexample (An order that is not locally finite).** The interval $[0, 1]$ of $\mathbb{Q}$ contains the distinct numbers $1/n$ for $n \ge 1$. So `ℚ` has no instance of `LocallyFiniteOrder`, and `Finset.Icc (0 : ℚ) 1` does not typecheck.

**Example (The unordered interval).** In $\mathbb{R}$, $[[5, 2]] = [2, 5] = [[2, 5]]$, while $[5, 2]$ is empty. In the subsets of $\{1, 2\}$, $[[\{1\}, \{2\}]] = [\emptyset, \{1, 2\}]$, and $\emptyset$ is in it but not between $\{1\}$ and $\{2\}$ in either order. So part 3 of the theorem fails without a linear order.

### The library around it

The file `Mathlib.Order.Interval.Set.OrdConnected` has the instances for the intervals and the closure lemmas, such as `Set.OrdConnected.preimage_anti` and `Set.OrdConnected.dual`. The file `Mathlib.Order.Interval.Set.UnorderedInterval` has the `Set.uIcc` lemmas, named like those of `Set.Icc` with a `u`, and the half-open `Set.uIoc` of the interval integral. Each lemma on `Set.Icc` has a twin on `Finset.Icc` in `Mathlib.Order.Interval.Finset.Basic`, and the cardinals are in a file for each type, such as `Mathlib.Order.Interval.Finset.Nat`.

### Exercises

1. (A) Compute the number of elements of $[7, 20)$ and of $(7, 20]$ in $\mathbb{N}$, and of $[-10, 10]$ in $\mathbb{Z}$. *Hint:* use the formulas of `Nat.card_Ico`, `Nat.card_Ioc` and `Int.card_Icc`.
2. (A) Show that the union of two order-connected sets need not be order-connected, and that the union of two order-connected sets with a common point is order-connected in a linear order. *Hint:* for the second claim, take $x \in s$, $y \in t$ and the common point $c$, and compare $c$ with $x$ and $y$.
3. (A) Show that $\{x \in \mathbb{R} \mid |x - 1| \le 3\}$ is order-connected, and identify it as an interval.
4. (B) Let $f : \mathbb{R} \to \mathbb{R}$ be antitone and let $s$ be order-connected. Show that $f^{-1}(s)$ is order-connected.
5. (B) Show that $(a, b)$ has $b - a - 1$ elements in $\mathbb{N}$, with the truncated subtraction. Check the formula for $a = b$ and for $b = a + 1$.
6. (B) Show that a finite nonempty order-connected subset of $\mathbb{Z}$ is of the form $[a, b]$. *Hint:* a finite nonempty set of integers has a least and a greatest element.
7. (B) Let $\alpha$ be a lattice. Show that $[a, b] \subseteq [[a, b]]$ for all $a, b$, and that the inclusion is strict in $\mathbb{R}$ when $b < a$.
8. (C) Show that the theorem on order-connected sets of reals holds in each conditionally complete linear order, and find where the proof uses that $\mathbb{R}$ has no least and no greatest element. *Hint:* in $[0, 1]$, the whole space is bounded, so the case $m = -\infty$ does not arise.
9. (C) Show that $\mathbb{Z} \times \mathbb{Z}$ with the product order is locally finite, and count the elements of $[(0, 0), (m, n)]$ for $m, n \in \mathbb{N}$. Show that $\mathbb{N}$ with the order of divisibility is not locally finite on all of $\mathbb{N}$. *Hint:* in the order of divisibility, each $n$ divides $0$.

### Notes and history

The term *convex subset* of an ordered set is in Birkhoff, *Lattice theory*. The intervals as the connected subsets of $\mathbb{R}$ are the base of the intermediate value theorem (Rudin, *Principles*, Theorems 2.47 and 4.23).

In Mathlib, Yury Kudryashov wrote the file on order-connected sets in 2020, and Zhouhang Zhou the file of unordered intervals. Yaël Dillies introduced `LocallyFiniteOrder` and the finite intervals in 2021.

### Reference

<?reference?>
