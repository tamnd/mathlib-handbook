---
title: Map, filter, sum and dedup of multisets
kind: theory
modules:
  - Mathlib.Data.Multiset.MapFold
  - Mathlib.Data.Multiset.Filter
  - Mathlib.Data.Multiset.Dedup
  - Mathlib.Algebra.BigOperators.Group.Multiset.Defs
explains:
  E3: [Multiset.map, Multiset.sum, Multiset.dedup]
  E2: [Multiset.prod, Multiset.sum_cons, Multiset.card_map, Multiset.count_map, Multiset.filter, Multiset.count_filter, Multiset.filter_add_not, Multiset.Nodup, Multiset.nodup_iff_count_le_one, Multiset.count_dedup, Multiset.nodup_dedup]
  E1: auto
families: []
requires: [V01.C02, V03.C01]
reads_with: ["MIL", "TPIL"]
lean:
  - MathlibHandbook/V03/C02/Examples.lean
  - MathlibHandbook/V03/C02/Exercises.lean
  - MathlibHandbook/V03/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Map, filter, sum and dedup of multisets

### Overview

The previous section made the type of multisets and its first functions: the card, the count and the sum of two multisets. This section gives the operations that the rest of the volume builds on. The map $f(m)$ applies a function to each element and keeps the repetitions. The filter keeps the elements that satisfy a predicate. The sum $\sum m$ and the product $\prod m$ add or multiply all the elements. The dedup removes the repetitions, and the predicate Nodup says that there is no repetition to remove.

Each operation is first defined on lists and then passed to multisets, by the theorem of the previous section on functions that respect permutations. For the sum and the product this step needs a commutative operation, and this is the deep reason why the big operators $\sum$ and $\prod$ of Chapter 6 need a commutative monoid. The section ends with the bridge to the next chapter: a finset is a multiset with no repetition, the card of a finset is the card of its multiset, and the sum $\sum_{i \in s} f(i)$ over a finset is the sum of the multiset $f(s)$. The main theorems are the formula for the count in an image, $\#_b f(m) = |\{a \in m \mid f(a) = b\}|$, and the formula $|m| = \sum_a \#_a m$ for the card in terms of the counts.

### Definitions

In this section $m, s, t$ are multisets of $\alpha$, $f : \alpha \to \beta$ is a function, and $p$ is a predicate on $\alpha$ that a program can decide.

**Definition (Map).** The map of $m = \langle [a_1, \ldots, a_n] \rangle$ is $f(m) = \langle [f(a_1), \ldots, f(a_n)] \rangle$.

**Definition (Filter).** The filter of $m = \langle [a_1, \ldots, a_n] \rangle$ by $p$ is the class of the list of the $a_i$ with $p(a_i)$ true, in the same order. It is written $\{a \in m \mid p(a)\}$ or $m.\mathrm{filter}\ p$.

**Definition (Sum and product).** Let $M$ be a commutative monoid. The sum of $m = \langle [a_1, \ldots, a_n] \rangle$, a multiset of $M$, is $a_1 + (a_2 + (\cdots + (a_n + 0)))$, and $\sum 0 = 0$. The product is the same with $\cdot$ and $1$.

**Definition (Nodup and dedup).** A list is Nodup when no element occurs twice: $[\,]$ is Nodup, and $a :: l$ is Nodup when $a$ does not occur in $l$ and $l$ is Nodup. A multiset is Nodup when one of its lists, and so each of its lists, is Nodup. The dedup of $m$ is the multiset with one copy of each element of $m$: on lists, $\mathrm{dedup}(a :: l)$ is $\mathrm{dedup}(l)$ if $a$ occurs in $l$, and $a :: \mathrm{dedup}(l)$ otherwise.

*Remarks.* The map of a multiset is not the image of a set. The map keeps the card: $f(\{1, 2\}) = \{1, 1\}$ for the constant function $1$. The image of the set $\{1, 2\}$ is $\{1\}$. The image of a finset in Chapter 3 is the dedup of the map. The filter and the dedup need a decision procedure, for $p$ and for the equality of $\alpha$, because a program must look at each element and decide.

::: mathlib
`Multiset.map` · `Mathlib.Data.Multiset.MapFold`

`Multiset.map f m` is defined with `Quot.liftOn` from `List.map` and the proof that `List.map` respects permutations. It needs no hypothesis on `f` or on `α`. The basic lemmas are `Multiset.map_cons`, `Multiset.map_add`, `Multiset.map_map` (the composition) and `Multiset.map_id`, and the membership lemma `Multiset.mem_map` has the same form as `Set.mem_image`.

<?decl Multiset.map?>
:::

::: mathlib
`Multiset.filter` · `Mathlib.Data.Multiset.Filter`

The predicate is an explicit argument and its decision procedure is an instance argument `[DecidablePred p]`. The membership lemma is `Multiset.mem_filter`: `a ∈ filter p s ↔ a ∈ s ∧ p a`.

<?decl Multiset.filter?>
:::

::: mathlib
`Multiset.sum` · `Mathlib.Algebra.BigOperators.Group.Multiset.Defs`

`Multiset.sum` is defined from `Multiset.prod` by `to_additive`, and `Multiset.prod` is the fold `foldr (· * ·) 1`. The class is `AddCommMonoid M` for the sum and `CommMonoid M` for the product.

<?decl Multiset.sum?>
:::

::: mathlib
`Multiset.Nodup` · `Mathlib.Data.Multiset.Defs`

The predicate "no repetition", lifted from `List.Nodup`. The lemma `Multiset.nodup_cons` says that `(a ::ₘ s).Nodup ↔ a ∉ s ∧ s.Nodup`.

<?decl Multiset.Nodup?>
:::

::: mathlib
`Multiset.dedup` · `Mathlib.Data.Multiset.Dedup`

The dedup needs `DecidableEq α`. Its basic lemmas are `Multiset.mem_dedup` (the same elements), `Multiset.dedup_le` (a submultiset), `Multiset.nodup_dedup` and `Multiset.dedup_eq_self`.

<?decl Multiset.dedup?>
:::

### Theorems and proofs

**Theorem (Map is well defined, and keeps the card).** If $l_1 \sim l_2$ then $f(l_1) \sim f(l_2)$. For each multiset $m$, $|f(m)| = |m|$, $f(s + t) = f(s) + f(t)$ and $g(f(m)) = (g \circ f)(m)$.

*Proof.* Use induction on the proof of $l_1 \sim l_2$. The rule $[\,] \sim [\,]$ maps to itself. The cons rule $a :: l_1 \sim a :: l_2$ maps to $f(a) :: f(l_1) \sim f(a) :: f(l_2)$, which follows from the induction hypothesis by the cons rule. The swap $a :: b :: l \sim b :: a :: l$ maps to the swap $f(a) :: f(b) :: f(l) \sim f(b) :: f(a) :: f(l)$. Transitivity maps to transitivity.

The other statements are statements about lists, proved by induction on the list. For the card, $|f(a :: l)| = |f(a) :: f(l)| = |f(l)| + 1 = |l| + 1$. For the sum, the map of a concatenation is the concatenation of the maps. For the composition, $g(f(a :: l)) = g(f(a)) :: g(f(l))$. $\square$

::: mathlib
`Multiset.card_map` · `Mathlib.Data.Multiset.MapFold`

The map keeps the card, with no hypothesis on `f`. It is a `simp` lemma. Compare `Finset.card_image_of_injective` of Chapter 3, which needs an injective function, because the image of a finset removes the repetitions.

<?decl Multiset.card_map?>
:::

**Theorem (The count in a map).** Let $\beta$ have decidable equality. For each $b \in \beta$, $$\#_b f(m) = \bigl|\{a \in m \mid f(a) = b\}\bigr|.$$

*Proof.* Use induction on $m$. For $m = 0$ both sides are $0$. Let $m = a ::_m m'$, and assume the formula for $m'$. Then $f(m) = f(a) ::_m f(m')$, so $\#_b f(m) = \#_b f(m') + [f(a) = b]$. On the right side, the filter of $a ::_m m'$ is $a ::_m$ (the filter of $m'$) when $f(a) = b$, and the filter of $m'$ otherwise. So its card is the card of the filter of $m'$ plus $[f(a) = b]$. By the induction hypothesis the two sides are equal. $\square$

So the count of $b$ in the map is the size of the fiber of $f$ over $b$, counted with the multiplicities of $m$.

::: mathlib
`Multiset.count_map` · `Mathlib.Data.Multiset.Filter`

The count in a map is the card of a filter. Note the form of the predicate in Mathlib: `fun a ↦ b = f a`, with `b` on the left.

<?decl Multiset.count_map?>
:::

**Theorem (Filter).** For each $a$, $\#_a \{x \in m \mid p(x)\}$ is $\#_a m$ if $p(a)$ holds, and $0$ otherwise. For each $m$, $$\{x \in m \mid p(x)\} + \{x \in m \mid \lnot p(x)\} = m, \qquad \bigl|\{x \in m \mid p(x)\}\bigr| + \bigl|\{x \in m \mid \lnot p(x)\}\bigr| = |m|.$$

*Proof.* The filter is well defined, because a swap of two adjacent elements of a list gives a swap, or no change, in the filtered list. For the count, use induction on $m$. Adding a copy of $x$ to $m$ adds a copy of $x$ to the filter exactly when $p(x)$. So the count of $a$ in the filter grows by $[x = a]$ when $p(x)$ holds and does not grow otherwise. If $p(a)$ holds, the step $x = a$ satisfies $p$, and the count follows $\#_a m$. If $p(a)$ fails, the steps with $x = a$ never add to the filter, and the count stays $0$.

For the sum, compare the counts. If $p(a)$ holds, the counts of $a$ on the left are $\#_a m$ and $0$, and if $p(a)$ fails, they are $0$ and $\#_a m$. In both cases the sum is $\#_a m$. A multiset is determined by its counts, by the previous section, so the equality holds. The card formula follows from the additivity of the card. $\square$

::: mathlib
`Multiset.count_filter` · `Mathlib.Data.Multiset.Filter`

The count in a filter, with an `if` in the statement. After a `rw` with it, `split_ifs` or `simp [h]` removes the `if`.

<?decl Multiset.count_filter?>
:::

**Theorem (The sum is well defined and additive).** Let $M$ be a commutative monoid, written additively. If $l_1 \sim l_2$ then the sums of $l_1$ and $l_2$ are equal. For multisets $s, t$ of $M$ and $a \in M$, $$\textstyle\sum (a ::_m s) = a + \sum s, \qquad \sum (s + t) = \sum s + \sum t.$$ For functions $f, g : \alpha \to M$ and a multiset $m$ of $\alpha$, $\sum (f + g)(m) = \sum f(m) + \sum g(m)$.

*Proof.* Use induction on the proof of $l_1 \sim l_2$. Only the swap rule needs a computation. The sum of $a :: b :: l$ is $a + (b + x)$ with $x$ the sum of $l$, and the sum of $b :: a :: l$ is $b + (a + x)$. By associativity and commutativity, $$a + (b + x) = (a + b) + x = (b + a) + x = b + (a + x).$$ The other rules are direct. The rule for cons is the definition of the sum of a list.

For the sum of $s + t$, use induction on $s$. For $s = 0$ both sides are $\sum t$. For $s = a ::_m s'$, $(a ::_m s') + t = a ::_m (s' + t)$, so the left side is $a + \sum(s' + t) = a + \sum s' + \sum t$ by the induction hypothesis, and this is $\sum s + \sum t$.

For the last formula, use induction on $m$. The step from $m'$ to $a ::_m m'$ adds $f(a) + g(a)$ to the left side and $f(a)$ and $g(a)$ to the two sums on the right side. By commutativity and associativity the two sides stay equal. $\square$

The swap step is the only place where commutativity enters.

::: mathlib
`Multiset.sum_cons` · `Mathlib.Algebra.BigOperators.Group.Multiset.Defs`

The sum of `a ::ₘ s` is `a + s.sum`. It is the step of an induction with `Multiset.induction_on`. The value on `n` copies of `a` is `n • a`, by `Multiset.sum_replicate`. The additivity is `Multiset.sum_add`, and the sum of a pointwise sum is `Multiset.sum_map_add`.

<?decl Multiset.sum_cons?>
:::

**Theorem (Nodup and the counts).** Let $\alpha$ have decidable equality. A multiset $m$ is Nodup if and only if $\#_a m \le 1$ for each $a$. The dedup has the count $\#_a \mathrm{dedup}(m) = 1$ if $a \in m$, and $0$ otherwise. So $\mathrm{dedup}(m)$ is Nodup, it has the same elements as $m$, and $\mathrm{dedup}(m) = m$ if and only if $m$ is Nodup.

*Proof.* For the first statement, use induction on a list $l$ of $m$. The empty list is Nodup and has all counts $0$. For $a :: l$: if it is Nodup then $a \notin l$ and $l$ is Nodup, so $\#_a l = 0$ and $\#_a (a :: l) = 1$, and for $b \ne a$, $\#_b(a :: l) = \#_b l \le 1$ by the induction hypothesis. Conversely, if all counts of $a :: l$ are at most $1$, then $\#_a l = \#_a(a :: l) - 1 \le 0$, so $a \notin l$. The counts of $l$ are at most those of $a :: l$, so $l$ is Nodup by the induction hypothesis, and $a :: l$ is Nodup.

For the count of the dedup, use induction on the list with the recursive definition. For $a :: l$ with $a$ in $l$, the dedup is $\mathrm{dedup}(l)$. Since $a$ occurs in $l$, an element $b$ is in $l$ if and only if it is in $a :: l$, so the formula passes from $l$ to $a :: l$. For $a :: l$ with $a$ not in $l$, the dedup is $a :: \mathrm{dedup}(l)$. Its count of $a$ is $1 + 0 = 1$, since $a \notin l$, and its count of $b \ne a$ is the count in $\mathrm{dedup}(l)$. Again the formula passes to $a :: l$.

The counts of the dedup are at most $1$, so it is Nodup. It has the same elements, because a count is positive exactly when the element is in the multiset. If $m$ is Nodup, its counts are $0$ or $1$, and $1$ exactly for the elements of $m$, so they agree with the counts of the dedup, and $\mathrm{dedup}(m) = m$. Conversely, if $\mathrm{dedup}(m) = m$, then $m$ is Nodup since the dedup is. $\square$

::: mathlib
`Multiset.nodup_iff_count_le_one` · `Mathlib.Data.Multiset.Count`

Nodup in terms of the counts. It needs `DecidableEq α`, because the count needs it; `Multiset.Nodup` itself does not.

<?decl Multiset.nodup_iff_count_le_one?>
:::

::: mathlib
`Multiset.nodup_dedup` · `Mathlib.Data.Multiset.Dedup`

The dedup has no repetition. With this proof, `⟨m.dedup, m.nodup_dedup⟩` is a finset, and this finset is `Multiset.toFinset m` of the next chapter.

<?decl Multiset.nodup_dedup?>
:::

**Theorem (The card is the sum of the counts).** Let $\alpha$ have decidable equality, and let $a_1, \ldots, a_k$ be the elements of $\mathrm{dedup}(m)$. Then $$|m| = \sum_{j=1}^{k} \#_{a_j} m.$$

*Proof.* Use induction on $m$. For $m = 0$ there is no element and both sides are $0$. Let $m = a ::_m m'$, and assume the formula for $m'$. If $a \in m'$, the dedup of $m$ has the same elements as the dedup of $m'$. The count of $a$ grows by $1$ and the other counts do not change, so the right side grows by $1$, as does $|m|$. If $a \notin m'$, the dedup of $m$ has the elements of the dedup of $m'$ and the new element $a$, with $\#_a m = 1$. The old counts do not change. So the right side grows by $1$ again. $\square$

This is the simplest double count. Count the elements of $m$ one by one, or group them by their value and count each group. Mathlib states it as `Multiset.toFinset_sum_count_eq`.

### Examples

**Example (Remove the repetitions).** The dedup of $\{1, 1, 2\}$ is $\{1, 2\}$. Its counts are $1$ for $1$ and $2$ and $0$ for each other number, as the formula of the dedup says.

<?lean MathlibHandbook/V03/C02/Examples.lean#dedup?>

**Example (The sum of a multiset).** The sum of $\{1, 2, 3\}$ is $6$, in each order of the elements.

<?lean MathlibHandbook/V03/C02/Examples.lean#sum?>

**Example (The prime factors of 360).** The multiset of the prime factors of $360 = 2^3 \cdot 3^2 \cdot 5$ is $m = \{2, 2, 2, 3, 3, 5\}$. Its card is $6$, the number of prime factors with multiplicity. Its product is $360$, and its sum is $2 + 2 + 2 + 3 + 3 + 5 = 17$. Its dedup is $\{2, 3, 5\}$, with card $3$, the number of distinct prime factors, and the counts $3, 2, 1$ add up to $6 = |m|$.

**Example (A map and its counts).** Let $m = \{0, 1, 2, \ldots, 9\}$, the multiset `Multiset.range 10`, and $f(n) = n \bmod 3$. Then $$f(m) = \{0, 1, 2, 0, 1, 2, 0, 1, 2, 0\}.$$ Its card is $10 = |m|$. The count of $0$ is $4$, the size of the fiber $\{0, 3, 6, 9\}$; the counts of $1$ and $2$ are $3$, for the fibers $\{1, 4, 7\}$ and $\{2, 5, 8\}$.

**Example (A filter in two parts).** Let $m = \{1, 2, 2, 3, 4, 4, 4\}$ and $p$ the predicate "even". The filter by $p$ is $\{2, 2, 4, 4, 4\}$ and the filter by $\lnot p$ is $\{1, 3\}$. Their sum is $m$, and the cards are $5 + 2 = 7$. The sum of the elements splits the same way: $\sum m = 20 = 16 + 4$.

**Counterexample (A map that creates repetitions).** The map of a Nodup multiset by an injective function is Nodup, by `Multiset.Nodup.map`. The hypothesis is needed. The multiset $\{0, 1\}$ is Nodup, and the map by $n \mapsto \lfloor n / 2 \rfloor$ is $\{0, 0\}$, which is not. So the image of a finset under a function that is not injective must remove the repetitions, and its card can be smaller. This is the reason for the hypothesis of `Finset.card_image_of_injective` in Chapter 3.

### Common errors

A learner often expects `Multiset.map` to remove repetitions, as the image of a set does. It does not; the card does not change. A second error is to forget the decision procedure: `Multiset.filter (fun x => x ∈ S)` for a set `S` with no decidable membership fails to elaborate, and the fix is a decidable predicate or `open Classical`. A third error is to use `Multiset.prod` over a type of matrices or permutations, with the error that no `CommMonoid` instance exists; the fix there is `List.prod` with a chosen order.

### The library around it

The operations come with the same families of lemmas: a `cons` lemma (`Multiset.map_cons`, `Multiset.filter_cons_of_pos`, `Multiset.sum_cons`), an `add` lemma (`Multiset.map_add`, `Multiset.filter_add`, `Multiset.sum_add`, `Multiset.prod_add`), a `mem` lemma (`Multiset.mem_map`, `Multiset.mem_filter`, `Multiset.mem_dedup`) and a `card` or `count` lemma (`Multiset.card_map`, `Multiset.count_map`, `Multiset.count_filter`, `Multiset.count_dedup`). The sums of pointwise operations are `Multiset.sum_map_add`, `Multiset.prod_map_mul` and `Multiset.sum_map_mul_left`. The lemmas `Multiset.filter_le` and `Multiset.dedup_le` say that a filter and a dedup are submultisets. The bridge to finsets is the structure `Finset.mk` with its fields `Finset.val` and `Finset.nodup`, the function `Multiset.toFinset`, and the lemmas `Finset.card_def` and `Finset.sum_eq_multiset_sum`. The table at the end lists the declarations of the section.

### Exercises

1. (A) Compute $f(m)$, its card and its sum for $m = \{-2, -1, 0, 1, 2\}$ and $f(x) = x^2$. Then compute the dedup of $f(m)$.
2. (A) Compute the filter of $\{1, 2, 3, 4, 5, 6\}$ by "divisible by $2$ or by $3$", and check the formula of the two filters.
3. (A) Give the multiset of the prime factors of $720$, its card, its sum and its dedup.
4. (B) Show that $\{x \in m \mid p(x)\}$ filtered again by $q$ is the filter of $m$ by "$p$ and $q$".
5. (B) Show that $\sum c \cdot f(m) = c \cdot \sum f(m)$ in a semiring, by induction on $m$.
6. (B) Show that the map of a Nodup multiset by an injective function is Nodup. Hint: use the count in a map.
7. (B) Let $M$ be a commutative monoid and $m$ a multiset of $M$ with dedup $\{a_1, \ldots, a_k\}$. Show that $\prod m = \prod_j a_j^{\#_{a_j} m}$.
8. (C) Let $m$ be a multiset of natural numbers with $|m| = n$ and $\sum m = s$. Show that some element of $m$ is at least $s / n$ when $n > 0$. This is a form of the pigeonhole principle.

### Notes and history

Map, filter and fold are the basic operations of functional programming on lists, from Lisp (McCarthy, 1960). The passage of a fold to multisets under a commutativity condition is the universal property of the free commutative monoid: the multisets of $\alpha$ form the free commutative monoid on $\alpha$, and each function $\alpha \to M$ to a commutative monoid extends in one way to a morphism of monoids, the sum of the map.

In Mathlib the operations on multisets come from the Lean 3 library of Mario Carneiro (2017). The file `Mathlib/Data/Multiset/Basic.lean` was later split into `MapFold`, `Filter`, `Dedup` and other files, and the sums and products moved to `Mathlib/Algebra/BigOperators/Group/Multiset`.

### Reference

<?reference?>
