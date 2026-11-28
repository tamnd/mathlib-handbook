---
title: Unions, components and the type of intervals
kind: api
modules:
  - Mathlib.Order.Interval.Set.Disjoint
  - Mathlib.Order.Interval.Set.Union
  - Mathlib.Order.Interval.Set.OrdConnectedComponent
  - Mathlib.Order.Interval.Set.OrdConnectedLinear
  - Mathlib.Order.Interval.Set.Infinite
  - Mathlib.Order.Interval.Set.SuccOrder
  - Mathlib.Order.Interval.Set.SuccPred
  - Mathlib.Order.Interval.Set.Final
  - Mathlib.Order.Interval.Set.Limit
  - Mathlib.Order.Interval.Basic
  - Mathlib.Order.Interval.Lex
explains:
  E2: [Set.Ico_disjoint_Ico, IsLUB.iUnion_Iio_eq, Ioc_subset_biUnion_Ioc, Set.mem_ordConnectedComponent, Set.ordConnected_iff_disjoint_Ioo_empty, Set.Ioo_infinite, Interval.coe_inf, NonemptyInterval.toLex_le_toLex, Set.Ici.isSuccLimit_coe]
  E1: auto
families: []
requires: [V04.C01, V04.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Unions, components and the type of intervals

### Overview

Section 1 proves the rules for one or two intervals. This section is a guide to the files that treat many intervals at the same time: when two intervals are disjoint, when a family of intervals covers a ray, and how a set of a linear order breaks into maximal order connected pieces. It also describes the files on the size of an interval in a dense order, on the intervals of a successor order, and on the subtypes `Set.Ici a` and `Set.Iic a` as orders of their own.

The last part of the section is about intervals as elements of a type. The type `NonemptyInterval α` has one element for each nonempty closed interval of α, and the type `Interval α` adds the empty interval. These types are lattices under inclusion, and they are the start of interval arithmetic in Mathlib. A second order on them, the lexicographic order, makes them a linear order when α is linear.

### The library around it

**Disjoint intervals.** In a linear order, two half-open intervals are disjoint when the smaller right end is at most the larger left end.

$$[a_1, a_2) \cap [b_1, b_2) = \emptyset \iff \min(a_2, b_2) \le \max(a_1, b_1) \qquad (\texttt{Set.Ico\_disjoint\_Ico}).$$

The file `Mathlib.Order.Interval.Set.Disjoint` states this with `Disjoint`, which for sets means an empty intersection. It also has `Set.Ioc_disjoint_Ioc` and simpler rules for rays, such as `Set.Iic_disjoint_Ioi` (with $a \le b$) and `Set.Ici_disjoint_Iic`.

**Unions of rays.** If $a$ is the least upper bound of the range of a family $f$, then a point is below $a$ exactly when it is below some $f(x)$.

$$\operatorname{IsLUB}(\operatorname{range} f, a) \implies \bigcup_x \operatorname{Iio}(f(x)) = \operatorname{Iio}(a) \qquad (\texttt{IsLUB.iUnion\_Iio\_eq}).$$

*Proof.* If $y < f(x)$, then $y < a$ because $f(x) \le a$. Conversely, let $y < a$. If $f(x) \le y$ for each $x$, then $y$ is an upper bound of the range, so $a \le y$, a contradiction. Thus $y < f(x)$ for some $x$, since the order is linear. $\square$

The form with `iSup` in a complete linear order is `iUnion_Iio_eq_Iio_iSup`. The lemma `iUnion_Iio_eq_univ_iff` says that the rays cover the whole order exactly when the range is not bounded above. The same file has the unions over a bounded set, such as `IsGLB.biUnion_Ioi_eq`, and the union of all closed intervals with a fixed left end, `Set.iUnion_Icc_right`, which is the ray `Set.Ici a`.

**Chains of intervals.** For a monotone sequence of points $a_0 \le a_1 \le \dots$, the consecutive half-open intervals cover the long interval. Mathlib states only the inclusion, and it needs no monotonicity.

$$(a_0, a_N] \subseteq \bigcup_{i < N} (a_i, a_{i+1}] \qquad (\texttt{Ioc\_subset\_biUnion\_Ioc}).$$

The proof is by induction on $N$: a point of $(a_0, a_{N+1}]$ is either in $(a_0, a_N]$ or in $(a_N, a_{N+1}]$, in a linear order. The file `Mathlib.Order.Interval.Set.Union` also has `Ico_subset_biUnion_Ico`. The lemma `Ioc_subset_biUnion_Ioc` is used in measure theory, in the file `Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real`, to cover an interval by small intervals.

**Order connected components.** In a linear order, the component of a point $x$ in a set $s$ is the set of points $y$ such that the whole interval between $x$ and $y$ is in $s$.

$$y \in \operatorname{ordConnectedComponent}(s, x) \iff [\![x, y]\!] \subseteq s \qquad (\texttt{Set.mem\_ordConnectedComponent}).$$

Here $[\![x, y]\!]$ is `Set.uIcc x y` of Section 2. The file `Mathlib.Order.Interval.Set.OrdConnectedComponent` proves that the component is order connected, that it is a subset of $s$ (`Set.ordConnectedComponent_subset`), that it contains $x$ when $x \in s$, and that two points of $s$ have the same component when one is in the component of the other. So the components divide $s$ into disjoint pieces, which are the largest order connected subsets of $s$. The definition `Set.ordConnectedSection` chooses one point from each component. The file then builds the sets `Set.ordT5Nhd` for two separated sets, and topology uses them to prove that each linear order with the order topology is completely normal.

**Order connected sets in a locally finite order.** In a linear order that is locally finite, a set is order connected exactly when it has no gaps of one or more points between its elements.

$$I \text{ ord. connected} \iff \forall x, y \in I,\ (x, y) \cap I = \emptyset \to (x, y) = \emptyset \qquad (\texttt{Set.ordConnected\_iff\_disjoint\_Ioo\_empty}).$$

The file `Mathlib.Order.Interval.Set.OrdConnectedLinear` also proves that a nonempty bounded order connected set in a conditionally complete linear order that is locally finite is the closed interval `Set.Icc (sInf I) (sSup I)`. For $\mathbb{N}$ and $\mathbb{Z}$ the file also states the condition with $y \le x + 1$ for consecutive elements of $I$.

**Infinite intervals.** In a dense order, each nonempty open interval is infinite.

$$a < b \implies (a, b) \text{ infinite} \qquad (\texttt{Set.Ioo\_infinite}).$$

The file `Mathlib.Order.Interval.Set.Infinite` proves this in two steps. As a subtype, $(a, b)$ is nonempty and has no maximal element, because for each $x$ with $a < x < b$ density gives a point between $x$ and $b$. A nonempty order with no maximal element contains a strictly increasing sequence, so it is infinite. It also gives `Set.Icc_infinite` and the other bounded kinds, and the rays: `Set.Ioi_infinite` needs `NoMaxOrder` and `Set.Iio_infinite` needs `NoMinOrder`. The instances `NoMaxOrder.infinite` and `NoMinOrder.infinite` say that a nonempty order without a maximum or without a minimum is an infinite type. Compare `not_lt_of_denselyOrdered_of_locallyFinite`, which is the same fact from the side of locally finite orders.

**Successor orders and rays as orders.** The file `Mathlib.Order.Interval.Set.SuccPred` has the rules for sets that convert half-open and closed intervals with `Order.succ` and `Order.pred`, such as `Set.Ico_succ_right_eq_Icc` and `Set.Ico_succ_left_eq_Ioo`. They are the set forms of the finset rules in `Mathlib.Order.Interval.Finset.SuccPred`. A ray is an order of its own, and the file `Mathlib.Order.Interval.Set.SuccOrder` gives `Set.Iic b` a successor function: for an element $i$ that is not maximal in the ray, `Set.Iic.coe_succ_of_not_isMax` says that its successor in the ray is its successor in the whole order. The file `Mathlib.Order.Interval.Set.Limit` proves that a limit of `Set.Ici j` is a limit of the whole order.

$$\operatorname{IsSuccLimit}(m) \implies \operatorname{IsSuccLimit}(m.\mathrm{val}) \qquad (\texttt{Set.Ici.isSuccLimit\_coe}).$$

The file `Mathlib.Order.Interval.Set.Final` has one instance for category theory: the inclusion of `Set.Ici j` into a linear order is a final functor, so a colimit over the order can be computed over the ray.

**The type of nonempty intervals.** The file `Mathlib.Order.Interval.Basic` defines `NonemptyInterval α` as a structure with two fields `fst` and `snd` and a proof of `fst ≤ snd`. Each element has a coercion to `Set α`, which is `Set.Icc fst snd`. The order on the type is inclusion: $s \le t$ when $t_1 \le s_1$ and $s_2 \le t_2$, so the left ends are compared in the reverse direction. The map `NonemptyInterval.toDualProd` makes this precise: it embeds the type into `αᵒᵈ × α`. The definition `NonemptyInterval.pure a` is the interval $[a, a]$, whose coercion is $\{a\}$, and `NonemptyInterval.map` applies a monotone map to both ends. In a lattice, the supremum of two intervals is the smallest interval that contains both, with ends $s_1 \sqcap t_1$ and $s_2 \sqcup t_2$.

**The type of intervals.** The empty set is an interval too, so the file defines `Interval α` as `WithBot (NonemptyInterval α)`, with ⊥ for the empty interval. The coercion sends ⊥ to ∅. When α is a lattice in which `≤` is decidable, `Interval α` is a lattice, and the infimum is the intersection.

$$\uparrow(s \sqcap t) = \uparrow s \cap \uparrow t \qquad (\texttt{Interval.coe\_inf}).$$

The supremum is the smallest interval that contains both, which is in general larger than the union. In a complete lattice, `Interval α` is a complete lattice. The files in `Mathlib.Algebra.Order.Interval` use these types to define the sum and product of intervals.

**The lexicographic order on intervals.** The order of inclusion is not linear: $[0, 1]$ and $[2, 3]$ are not comparable. The file `Mathlib.Order.Interval.Lex` defines a second order on `Lex (NonemptyInterval α)`, which compares the left ends first, in the reverse direction, and then the right ends.

$$\operatorname{toLex} x \le \operatorname{toLex} y \iff y_1 < x_1 \lor (x_1 = y_1 \land x_2 \le y_2) \qquad (\texttt{NonemptyInterval.toLex\_le\_toLex}).$$

This order is linear when α is linear, and it extends inclusion: `NonemptyInterval.toLex_mono` says that $x \le y$ implies $\operatorname{toLex} x \le \operatorname{toLex} y$. The docstring of the file sorts the intervals of $\{1, 2, 3\}$ in this order as $[3,3], [2,2], [2,3], [1,1], [1,2], [1,3]$.

#### Common errors

1. Using `Set.Ico_disjoint_Ico` in a partial order. It needs a linear order, because the statement uses `min` and `max`. In a partial order, use `Set.Ico_disjoint_Ico_same` or a direct proof.
2. Treating `Interval α` as `Set α`. An element of `Interval α` is a pair of endpoints or ⊥, and two elements are equal only when their endpoints are equal. Use the coercion, and the lemma `Interval.coe_inf`, to move to sets.
3. Expecting `Ioc_subset_biUnion_Ioc` to give an equality. The union can be larger than $(a_0, a_N]$ when the sequence is not monotone.

### Exercises

1. (A) Use `Set.Ico_disjoint_Ico` to decide whether $[0, 3)$ and $[3, 5)$ are disjoint in $\mathbb{Z}$, and whether $[0, 4)$ and $[3, 5)$ are.
2. (A) Find the order connected components of $\{0, 1, 2, 5, 6, 9\}$ in $\mathbb{Z}$.
3. (B) Prove `IsLUB.iUnion_Iio_eq` for a linear order, following the proof in the text.
4. (B) Show with `Set.Ioo_infinite` that the rational interval $(0, 1)$ is infinite, and explain why the same statement fails in $\mathbb{Z}$.
5. (B) Compute the infimum and the supremum of $[0, 2]$ and $[1, 5]$ in `Interval ℤ`, and check `Interval.coe_inf` for them.
6. (C) Prove that the lexicographic order on `NonemptyInterval ℕ` is total, and show that $[1, 2]$ and $[2, 3]$ are comparable in it but not under inclusion.

### Reference

<?reference?>
