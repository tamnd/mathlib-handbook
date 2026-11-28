---
title: Folds, suprema, maxima and sorting of finsets
kind: api
modules:
  - Mathlib.Data.Finset.Fold
  - Mathlib.Data.Finset.Lattice.Fold
  - Mathlib.Data.Finset.Lattice.Lemmas
  - Mathlib.Data.Finset.Lattice.Pi
  - Mathlib.Data.Finset.Lattice.Prod
  - Mathlib.Data.Finset.Lattice.Union
  - Mathlib.Data.Finset.Max
  - Mathlib.Data.Finset.Order
  - Mathlib.Data.Finset.DenselyOrdered
  - Mathlib.Data.Finset.Sort
explains:
  E2: [Finset.fold_insert, Finset.sup_le_iff, Finset.sup_union, Finset.apply_sup_eq_sup_comp, Finset.exists_max_image, Finset.induction_on_max, Finset.min'_lt_max'_of_card, Finset.exists_le, Finset.exists_between, Finset.orderEmbOfFin_unique]
  E1: auto
families: []
requires: [V03.C01, V03.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Folds, suprema, maxima and sorting of finsets

### Overview

A finset has no order on its elements, so an operation that runs through the elements one by one must give the same result in each order. A commutative and associative operation has this property. The fold `Finset.fold` applies such an operation to the values of a function on a finset. The sum and the product of Chapter 6 are folds of this kind, and so are the supremum and the infimum of a function on a finset in a lattice.

The modules of this section give the folds, the lattice folds `Finset.sup` and `Finset.inf` with their forms `Finset.sup'` and `Finset.inf'` for a nonempty finset, the maximum and the minimum `Finset.max'` and `Finset.min'` in a linear order, and the sorted list `Finset.sort` of a finset. They also give the first facts about directed orders and dense orders that a finset needs: a finset has an upper bound in a directed order, and two finsets with $s < t$ pointwise have an element between them in a dense order. Sections 4 and 5 gave the union and the intersection. This section adds the rules that connect them with insert and singletons, in `Mathlib.Data.Finset.Lattice.Lemmas`.

### The library around it

#### The fold of a commutative operation

Let `op : β → β → β` be commutative and associative. The fold asks for these two laws as instances of the classes of commutativity and associativity of the core library. For $b \in \beta$, $f : \alpha \to \beta$ and a finset $s$, `Finset.fold op b f s` is $f(a_1) \ast f(a_2) \ast \cdots \ast f(a_n) \ast b$ for any list $a_1, \ldots, a_n$ of the elements of $s$, where $\ast$ is `op`. The value $b$ is the start value, and `Finset.fold_empty` gives $b$ for the empty finset. The fold goes through the multiset of $s$, where the commutativity and the associativity make the result independent of the order.

**Theorem.** If $a \notin s$, then `fold op b f (insert a s) = op (f a) (fold op b f s)` (`Finset.fold_insert`).

*Proof.* For $a \notin s$, the multiset of $\{a\} \cup s$ is $a$ added to the multiset of $s$. The fold of a multiset with $a$ added at the front is `op (f a)` applied to the fold of the rest, by the definition of the fold on lists. $\square$

The hypothesis $a \notin s$ is needed. If $a \in s$, then $\{a\} \cup s = s$, and the right side has the factor $f(a)$ twice. For an idempotent operation, such as $\max$ or $\sqcup$, the hypothesis is not needed, and the rule is `Finset.fold_insert_idem`. The other rules are the rules of a sum: `Finset.fold_image` for an image along a map that is injective on $s$, `Finset.fold_op_distrib` for the fold of a pointwise operation, `Finset.fold_hom` for a map $m$ with $m(x \ast y) = m(x) \ast' m(y)$, and `Finset.fold_union_inter` for a union and an intersection. For the operations $\max$ and $\min$ of a linear order, `Finset.le_fold_max` and its relatives give the order rules: $c \le \mathrm{fold}\ \max\ b\ f\ s \iff c \le b \lor \exists x \in s,\ c \le f(x)$.

#### Suprema and infima over a finset

For a join semilattice $\alpha$ with a bottom $\bot$ and $f : \beta \to \alpha$, `s.sup f` is $\bigsqcup_{b \in s} f(b)$. It is the fold of $\sqcup$ with the start value $\bot$, and `Finset.sup_def` writes it through the multiset. The infimum `s.inf f` is the dual, for a meet semilattice with a top $\top$. Each rule for `sup` has a twin for `inf`, with the order reversed, and the twins have the same pattern of names.

**Theorem (Universal property).** $\bigsqcup_{b \in s} f(b) \le a \iff \forall b \in s,\ f(b) \le a$ (`Finset.sup_le_iff`).

*Proof.* Use induction on $s$. For $s = \emptyset$, the left side is $\bot \le a$, which is true, and the right side is true with no condition. For $\{c\} \cup s$ with $c \notin s$, the supremum is $f(c) \sqcup \bigsqcup_{b \in s} f(b)$, by `Finset.sup_insert`. In a semilattice, $x \sqcup y \le a \iff x \le a \land y \le a$. The hypothesis of induction gives the condition on $s$. $\square$

The two halves are `Finset.le_sup`, $f(b) \le \bigsqcup_s f$ for $b \in s$, and `Finset.sup_le`. Most rules follow from the universal property. For example:

**Theorem.** $\bigsqcup_{s_1 \cup s_2} f = \bigsqcup_{s_1} f \sqcup \bigsqcup_{s_2} f$ (`Finset.sup_union`).

*Proof.* Both sides are upper bounds of the values $f(b)$ with $b \in s_1 \cup s_2$, and each is below every such upper bound, by `Finset.sup_le_iff` and the rule for $\sqcup$. In a partial order, two least upper bounds are equal. $\square$

| Lean name | Statement |
|---|---|
| `Finset.sup_empty` | $\bigsqcup_{\emptyset} f = \bot$ |
| `Finset.sup_insert` | $\bigsqcup_{\{b\} \cup s} f = f(b) \sqcup \bigsqcup_s f$ |
| `Finset.sup_image` | $\bigsqcup_{g(s)} f = \bigsqcup_s f \circ g$, with no injectivity |
| `Finset.sup_biUnion` | the supremum over a union of finsets, as a double supremum |
| `Finset.sup_comm` | the exchange of two suprema |
| `Finset.sup_product_left` | the supremum over $s \times t$ as a double supremum |
| `Finset.sup_inf_distrib_left` | $a \sqcap \bigsqcup_s f = \bigsqcup_s (a \sqcap f)$ in a distributive lattice |
| `Finset.sup_eq_iSup` | in a complete lattice, `s.sup f` is the indexed supremum $\bigsqcup_{a \in s} f(a)$ |
| `Finset.sup_set_eq_biUnion` | for sets, the supremum is the union $\bigcup_{x \in s} f(x)$ |
| `Finset.sup_eq_biUnion` | for finsets, the supremum is `Finset.biUnion` |

The image rule `Finset.sup_image` needs no injectivity, because $\sqcup$ is idempotent. A sum over an image needs it. A map $g$ of semilattices that keeps $\sqcup$ and $\bot$ commutes with the supremum.

**Theorem.** If $g(x \sqcup y) = g(x) \sqcup g(y)$ and $g(\bot) = \bot$, then $g(\bigsqcup_s f) = \bigsqcup_s g \circ f$ (`Finset.apply_sup_eq_sup_comp`).

*Proof.* Use induction on $s$. The empty case is $g(\bot) = \bot$. The insert case is $g(f(b) \sqcup \bigsqcup_s f) = g(f(b)) \sqcup g(\bigsqcup_s f)$, and the hypothesis of induction rewrites the second term. $\square$

In a linear order the supremum is attained. `Finset.exists_mem_eq_sup` gives $i \in s$ with $\bigsqcup_s f = f(i)$ for a nonempty $s$, and `Finset.lt_sup_iff` gives $a < \bigsqcup_s f \iff \exists b \in s,\ a < f(b)$. The lemma `Finset.sup_induction` proves that a property closed under $\sqcup$ and true at $\bot$ and at each $f(b)$ holds at the supremum. The modules `Mathlib.Data.Finset.Lattice.Prod`, `Mathlib.Data.Finset.Lattice.Union` and `Mathlib.Data.Finset.Lattice.Pi` add three groups: the suprema over a product, as `Finset.sup_prodMap`; the suprema over a `Finset.biUnion`; and the distributive law `Finset.inf_sup`, which writes an infimum of suprema as a supremum over the choice functions in `s.pi t`.

#### The forms for a nonempty finset

A semilattice with no bottom, such as $\mathbb{Z}$, has no value for the supremum over the empty finset. The form `s.sup' H f` takes a proof `H : s.Nonempty` and needs no $\bot$. Its rules are the rules of `sup` with a prime: `Finset.le_sup'`, `Finset.sup'_le`, `Finset.sup'_induction` and `Finset.exists_mem_eq_sup'`. The rule `Finset.coe_sup'` computes it as a supremum in `WithBot α`, and `Finset.sup'_eq_sup` says that it agrees with `sup` when $\alpha$ has a bottom. The infimum `Finset.inf'` is the dual.

#### Maxima and minima

For a finset $s$ of a linear order, `Finset.max s : WithBot α` is the largest element of $s$, with the value $\bot$ for the empty finset (`Finset.max_eq_bot`). The form `s.max' H` takes a proof `H : s.Nonempty` and has a value in $\alpha$. It is `s.sup' H id`, by `Finset.max'_eq_sup'`. The membership and the bounds are `Finset.max'_mem`, `Finset.le_max'` and `Finset.max'_le`, and `Finset.isGreatest_max'` states them together. The minimum `Finset.min'` is the dual, and `Finset.coe_max'` connects the two forms.

**Theorem.** Each function $f : \beta \to \alpha$ to a linear order attains its maximum on a nonempty finset: there is $x \in s$ with $f(x') \le f(x)$ for each $x' \in s$ (`Finset.exists_max_image`).

*Proof.* Use induction on the nonempty finset. For $\{a\}$, take $x = a$. For $\{a\} \cup s$ with $s$ nonempty, let $x_0 \in s$ be the point given by the hypothesis of induction. If $f(a) \le f(x_0)$, take $x = x_0$; else take $x = a$. In both cases $f(x)$ is at least $f(a)$ and at least each $f(x')$ with $x' \in s$, because the order is linear. $\square$

The maximum gives a second form of induction. A finset is built from $\emptyset$ by adding, in each step, an element above all the elements already present.

**Theorem.** Let $P$ hold at $\emptyset$, and let $P(s)$ imply $P(\{a\} \cup s)$ when $x < a$ for each $x \in s$. Then $P$ holds for each finset (`Finset.induction_on_max`).

*Proof.* Use strong induction on the card. A nonempty $s$ is $\{a\} \cup s'$ with $a = \max' s$ and $s' = s \setminus \{a\}$. Each $x \in s'$ is at most $a$ and different from $a$, so $x < a$. The card of $s'$ is smaller, so $P(s')$ holds, and the step gives $P(s)$. $\square$

The forms `Finset.induction_on_min`, `Finset.induction_on_max_value` and `Finset.induction_on_min_value` add the least element, or the element with the largest or least value of a function. The rule `Finset.max'_insert` computes $\max'(\{a\} \cup s) = \max(a, \max' s)$. Two more results count.

**Theorem.** If $|s| > 1$, then $\min' s < \max' s$ (`Finset.min'_lt_max'_of_card`).

*Proof.* A finset with two or more elements has two elements $a \ne b$. Then $\min' s \le \min(a, b) < \max(a, b) \le \max' s$. $\square$

`Finset.card_le_of_interleaved` says that if between any two consecutive elements of $s$ there is an element of $t$, then $|s| \le |t| + 1$. `Finset.exists_next_right` gives the next element of $s$ above a point $x$, when one exists.

#### Directed and dense orders

The module `Mathlib.Data.Finset.Order` gives the upper bounds of finsets in a directed order.

**Theorem.** In a nonempty directed preorder, each finset $s$ has an upper bound $M$ with $i \le M$ for each $i \in s$ (`Finset.exists_le`).

*Proof.* Use induction on $s$. The empty finset has each point as an upper bound, and the order is nonempty. For $\{a\} \cup s$, let $M$ bound $s$. The order is directed, so some $M'$ is above $a$ and above $M$, and $M'$ bounds $\{a\} \cup s$ by transitivity. $\square$

The form `Directed.finset_le` gives the same for a directed family of values. The module `Mathlib.Data.Finset.DenselyOrdered` gives the separation of finsets in a dense linear order.

**Theorem.** In a dense linear order, let $s$ and $t$ be nonempty finsets with $x < y$ for each $x \in s$ and $y \in t$. Then there is $b$ with $x < b < y$ for each $x \in s$ and $y \in t$ (`Finset.exists_between`).

*Proof.* Let $m = \max' s$ and $n = \min' t$. Then $m < n$, because $m \in s$ and $n \in t$. Density gives $b$ with $m < b < n$. Each $x \in s$ is at most $m$, and each $y \in t$ is at least $n$. $\square$

The form `Set.Finite.exists_between` states it for finite sets.

#### Sorting

For a relation $r$ that is decidable, transitive, antisymmetric and total, `Finset.sort s r` is the list of the elements of $s$ in the order $r$. The default relation is $\le$. Its multiset is the multiset of $s$, by `Finset.sort_eq`, so `Finset.mem_sort` and `Finset.length_sort` give the elements and the length, and `Finset.sort_nodup` says that it has no repeated element. In a linear order, `Finset.sortedLT_sort` says that the list for $\le$ is strictly increasing. The first and the last entries are the minimum and the maximum, by `Finset.min'_eq_sorted_zero` and `Finset.max'_eq_sorted_last`. For example, `Finset.sort_range` gives the list $[0, 1, \ldots, n - 1]$ for `Finset.range n`.

The sorted list gives the order embedding `Finset.orderEmbOfFin s h : Fin k ↪o α` for `h : s.card = k`. It sends $i$ to the $i$-th element of $s$ in increasing order, its range is $s$ by `Finset.range_orderEmbOfFin`, and `Finset.orderIsoOfFin` is the same map as an order isomorphism onto the subtype of $s$. It is the only map with these properties.

**Theorem.** Let $|s| = k$, and let $f : \mathrm{Fin}\ k \to \alpha$ be strictly increasing with values in $s$. Then $f$ is `s.orderEmbOfFin h` (`Finset.orderEmbOfFin_unique`).

*Proof.* A strictly increasing map is injective. So $f$ has $k$ distinct values in $s$, and its range is all of $s$. Two strictly increasing maps from $\mathrm{Fin}\ k$ onto the same finite set of a linear order are equal: by induction on $i$, the $i$-th value of each is the least element of $s$ above the earlier values. $\square$

The forms `Finset.orderEmbOfFin_zero` and `Finset.orderEmbOfFin_last` give the first and the last values, and `Finset.orderEmbOfCardLe` embeds `Fin k` for each $k \le |s|$. For a whole finite type with a linear order, `Fintype.orderIsoFinOfCardEq` gives the order isomorphism with `Fin (Fintype.card α)`.

#### Common errors

1. `Finset.sup` needs `OrderBot`, so it does not apply to $\mathbb{Z}$ or $\mathbb{R}$. Use `Finset.sup'` with a proof of nonemptiness, or `Finset.max'` for the largest element of the finset itself.
2. `Finset.max s` has values in `WithBot α`, so `Finset.max s = a` asks for a coercion of `a`. A proof that compares the maximum with an element of $\alpha$ is easier with `Finset.max'`.
3. `Finset.fold_insert` needs $a \notin s$, unlike `Finset.sup_insert`. A rewrite that works for `sup` can fail for a general fold. For an idempotent operation use `Finset.fold_insert_idem`.

### Exercises

1. (A) Compute `(Finset.range 5).sup (fun n ↦ n * (4 - n))` in $\mathbb{N}$, and find a point where the supremum is attained.
2. (A) Prove $\bigsqcup_{s} f \le \bigsqcup_{t} f$ for $s \subseteq t$ from `Finset.sup_le_iff` and `Finset.le_sup`.
3. (B) For finsets $s_i$ of $\alpha$, prove that $\bigsqcup_{i \in I} s_i$ in the lattice of finsets is the union $\bigcup_{i \in I} s_i$, and compare with `Finset.sup_eq_biUnion`.
4. (B) Prove that a nonempty finset of a linear order with $|s| = n$ sorts to a list whose entry $i$ is less than its entry $j$ for $i < j < n$, and deduce `Finset.min'_lt_max'_of_card` again.
5. (B) Prove `Finset.exists_max_image` from `Finset.exists_mem_eq_sup'` and `Finset.le_sup'`.
6. (C) Prove the distributive law $\bigsqcap_{i \in I} \bigsqcup_{j \in J_i} a_{ij} = \bigsqcup_{g} \bigsqcap_{i \in I} a_{i\, g(i)}$ in a finite distributive lattice, where $g$ runs over the choice functions with $g(i) \in J_i$.

### Reference

<?reference?>
