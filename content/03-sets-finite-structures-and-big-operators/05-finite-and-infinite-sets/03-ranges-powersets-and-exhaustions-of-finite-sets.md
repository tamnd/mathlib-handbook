---
title: "More finite sets: ranges, power sets, exhaustions and subsets of a given size"
kind: api
modules:
  - Mathlib.Data.Set.Finite.Range
  - Mathlib.Data.Set.Finite.Lemmas
  - Mathlib.Data.Set.Finite.Powerset
  - Mathlib.Data.Set.Finite.List
  - Mathlib.Data.Set.Finite.Monad
  - Mathlib.Data.Set.Card.Arithmetic
  - Mathlib.Data.Set.FiniteExhaustion
  - Mathlib.Data.Set.PowersetCard
explains:
  E2: [Set.finite_range, Set.Finite.exists_subset_finite_image_eq, Set.exists_max_image, Set.Finite.induction_to, Set.Finite.powerset, List.finite_length_le, Set.ncard_iUnion_le_of_fintype, Set.exists_union_disjoint_ncard_eq_of_even, Set.nonempty_finiteExhaustion_iff, Set.powersetCard.card]
  E1: auto
families: []
requires: [V03.C03, V03.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## More finite sets: ranges, power sets, exhaustions and subsets of a given size

### Overview

Section 1 of this chapter gives the predicate `Set.Finite` and its closure rules, and Section 2 gives the infinite sets. The modules of this section add the results that a proof needs next. The range of a map from a finite type is finite. A function on a finite nonempty set attains a maximum. A property can be proved on a finite set by adding one element at a time. The subsets of a finite set and the lists of bounded length over a finite type form finite sets. The count of a finite union is at most the sum of the counts. A countable set is an increasing union of finite sets. And the subsets of a given size of a type form a set whose card is a binomial coefficient.

The section uses the finsets of Chapter 3, the finite types of Chapter 4 and the counts `Set.ncard` and `Set.encard` of Section 1. Each result has a short proof from those tools, and the text gives the idea of the proof.

### The library around it

#### Ranges and images

The module `Mathlib.Data.Set.Finite.Range` holds the finiteness of ranges. If the index type $\iota$ is finite, then the range of each map $f : \iota \to \alpha$ is finite: this is `Set.finite_range`, with the instance form `Finite.Set.finite_range` for the subtype. The proof: the map $\iota \to \operatorname{range} f$ is surjective, and the image of a finite type by a surjective map is finite. The instance `Set.fintypeRange` gives a `Fintype` structure when $\alpha$ has decidable equality. The dependent form `Set.Finite.dependent_image` allows a map $F(x, h)$ that also uses the proof $h : x \in s$.

The converse direction is a choice of preimages. If a finite set $u$ lies in the image $f(s)$, then $u$ is the image of a finite subset of $s$:

$$u \text{ finite},\ u \subseteq f(s) \implies \exists\, t \subseteq s,\ t \text{ finite},\ f(t) = u.$$

This is `Set.Finite.exists_subset_finite_image_eq`. For a proof, choose one preimage in $s$ for each point of $u$, and let $t$ be the set of the chosen points. The last result of the module, `Function.Injective.range_eq_range_iff_subset`, says that for an injective map $f$ on a finite type, $\operatorname{range} f = \operatorname{range} g$ if and only if $\operatorname{range} f \subseteq \operatorname{range} g$.

#### Extrema and induction on a finite set

The module `Mathlib.Data.Set.Finite.Lemmas` has two kinds of results. The first kind is about extrema. A function $f$ into a linear order attains its maximum and its minimum on a finite nonempty set $s$:

$$\exists\, a \in s,\ \forall b \in s,\ f(b) \le f(a).$$

This is `Set.exists_max_image`, and `Set.exists_min_image` is the dual. The proof converts $s$ to a finset with `Set.Finite.toFinset` and uses the maximum of a nonempty finset. The forms `Set.exists_upper_bound_image` and `Set.exists_lower_bound_image` drop the condition that $s$ is nonempty, but then the point $a$ need not lie in $s$, and the type must be nonempty.

The second kind is about induction and parameters. `Set.Finite.induction_to` proves a property $C$ of a finite set $S$ from a start $C(S_0)$ with $S_0 \subseteq S$ and a step: for each $s \subsetneq S$ with $C(s)$ there is $a \in S \setminus s$ with $C(s \cup \{a\})$. The proof is an induction on the card of $S \setminus s$, which drops by one at each step. `Set.Finite.induction_to_univ` is the case $S = $ `Set.univ` on a finite type. The rules `Set.Finite.fin_embedding` and `Set.Finite.fin_param` say that a finite set is the range of an injective map from `Fin n`, so its elements can be listed as $a_0, \dots, a_{n-1}$ with no repeat. The rule `Set.sUnion_finite_eq_univ` says that the union of all finite sets is the whole type, because each point lies in a singleton.

#### Power sets, lists and the monad of sets

The power set of a finite set is finite: `Set.Finite.powerset` gives $\mathcal{P}(s)$ finite, and `Set.Finite.finite_subsets` gives the same for $\{b \mid b \subseteq a\}$. The proof maps each subset of the finset of $s$ to a set, and the image of the finite power set of a finset is finite.

The module `Mathlib.Data.Set.Finite.List` counts lists. Over a finite type $\alpha$, the lists of length $n$, of length at most $n$ and of length less than $n$ form finite sets: `List.finite_length_eq`, `List.finite_length_le` and `List.finite_length_lt`. The first one has a direct proof: a list of length $n$ is a function `Fin n → α`, and there are $|\alpha|^n$ of them. The second one is the union over $k \le n$ of the first one, a finite union of finite sets.

The type `Set` is a monad: `pure a` is $\{a\}$, and `s >>= f` is $\bigcup_{a \in s} f(a)$. The module `Mathlib.Data.Set.Finite.Monad` says that these operations keep finiteness. `Finite.Set.finite_pure` gives the finiteness of `pure a`, `Set.Finite.bind` gives that of a union over a finite set of finite sets, and `Set.Finite.seq` gives that of the set of all values $f(x)$ with $f$ in a finite set of maps and $x$ in a finite set. The instances `Set.fintypePure`, `Set.fintypeBind'` and `Set.fintypeSeq` give the same results as `Fintype` structures.

#### Counts of unions and halves of a set

The module `Mathlib.Data.Set.Card.Arithmetic` gives the inequalities and equalities of counts for unions. For a finite type of indices,

$$\operatorname{ncard}\Big(\bigcup_i s_i\Big) \le \sum_i \operatorname{ncard}(s_i),$$

with equality when the sets are finite and pairwise disjoint. These are `Set.ncard_iUnion_le_of_fintype` and `Set.ncard_iUnion_of_finite`. The table gives the other forms. The forms with a finite set of indices use the sum `finsum`, written `∑ᶠ`, which does not need a finset.

| Lean name | Statement |
|---|---|
| `Set.encard_iUnion_le_of_fintype` | $\operatorname{encard}(\bigcup_i s_i) \le \sum_i \operatorname{encard}(s_i)$ for a finite type of indices |
| `Set.encard_iUnion_of_finite` | equality for pairwise disjoint sets, with `∑ᶠ` |
| `Finset.set_ncard_biUnion_le` | $\operatorname{ncard}(\bigcup_{i \in t} s_i) \le \sum_{i \in t} \operatorname{ncard}(s_i)$ for a finset $t$ |
| `Set.Finite.ncard_biUnion` | equality for a finite set of indices, finite sets and pairwise disjoint sets |
| `finsum_one` | $\sum^{f}_{i \in s} 1 = \operatorname{ncard}(s)$ |

The inequality for `Set.encard` holds with no finiteness condition on the sets, because `Set.encard` takes the value $\infty$ on an infinite set. The inequality for `Set.ncard` needs care: `Set.ncard` is $0$ on an infinite set, so if one $s_i$ is infinite the left side is $0$ and the inequality holds for a trivial reason.

The second group of results splits a set into two halves of the same size. A finite set splits into two disjoint parts of equal card if and only if its card is even:

$$\operatorname{ncard}(s) \text{ even} \implies \exists\, t, u,\ t \cup u = s,\ t \cap u = \varnothing,\ \operatorname{ncard}(t) = \operatorname{ncard}(u).$$

This is `Set.exists_union_disjoint_ncard_eq_of_even`, and `Finset.exists_disjoint_union_of_even_card_iff` is the form for finsets with both directions. For a proof, list the elements of $s$ as $a_1, \dots, a_{2k}$ and take the first $k$ for $t$. For an infinite set the same split exists with equal cardinals (`Set.Infinite.exists_union_disjoint_cardinal_eq_of_infinite`), and this uses the cardinal arithmetic $\kappa + \kappa = \kappa$ of the volume on set theory.

#### Finite exhaustions

A *finite exhaustion* of a set $s$ is an increasing sequence of finite sets $K_0 \subseteq K_1 \subseteq \cdots$ whose union is $s$. The structure `Set.FiniteExhaustion s` holds the sequence and the three facts, and the rules `Set.FiniteExhaustion.finite`, `Set.FiniteExhaustion.subset_succ` and `Set.FiniteExhaustion.iUnion_eq` recover them. An exhaustion acts as a monotone function `ℕ → Set α` (`Set.FiniteExhaustion.mono`). A set has a finite exhaustion exactly when it is countable:

$$\operatorname{Nonempty}(\operatorname{FiniteExhaustion}(s)) \iff s \text{ countable}.$$

This is `Set.nonempty_finiteExhaustion_iff`. In one direction, a countable union of finite sets is countable. In the other direction, enumerate $s$ as $a_0, a_1, \dots$ and let $K_n = \{a_0, \dots, a_n\}$; the definition `Set.Countable.finiteExhaustion` makes this choice. The product of two exhaustions is an exhaustion of the product set (`Set.FiniteExhaustion.prod`). The countable sets are the subject of Chapter 8.

#### Subsets of a given size

The module `Mathlib.Data.Set.PowersetCard` gives the set `Set.powersetCard α n` of all finsets of $\alpha$ with $n$ elements, as a type with good structure. For a finite type, it is the finset `Finset.powersetCard n Finset.univ` of Chapter 3, seen as a set (`Set.powersetCard.coe_finset`), and its card is the binomial coefficient:

$$\#\{s \subseteq \alpha : |s| = n\} = \binom{|\alpha|}{n}.$$

This is `Set.powersetCard.card`, stated with `Nat.card`, so it holds with no `Fintype` instance. If $\alpha$ is infinite, both sides are $0$ for a reason of junk values, since `Nat.card` of an infinite type is $0$. The elements of the type `Set.powersetCard α n` act as sets (`Set.powersetCard.instSetLikeElemFinset`), and the module gives constructions on them.

1. `Set.powersetCard.ofCard` makes an element from a finset with a proof of its card, and `Set.powersetCard.prodEquiv` says that each finset is a pair of its size $n$ and an element of `Set.powersetCard α n`.
2. `Set.powersetCard.ofSingleton` is the bijection between $\alpha$ and the subsets of size $1$.
3. `Set.powersetCard.compl` sends a subset of size $n$ to its complement, of size $m$ with $m + n = |\alpha|$. This bijection gives $\binom{N}{n} = \binom{N}{N - n}$.
4. `Set.powersetCard.map` takes the image by an embedding, and `Set.powersetCard.ofFinEmb` takes the range of an embedding `Fin n ↪ β`. The second map is surjective (`Set.powersetCard.ofFinEmb_surjective`).

The type is nonempty if and only if $n \le |\alpha|$ (`Set.powersetCard.nonempty_iff`, with the card in `ℕ∞`), and it is infinite when $\alpha$ is infinite and $n \ne 0$ (`Set.powersetCard.instInfinite`). Two distinct subsets of the same size $n$ differ in a point of the first that is not in the second (`Set.powersetCard.exists_mem_notMem_iff_ne`).

#### Common errors

1. A learner applies `Set.exists_upper_bound_image` and expects the point $a$ to lie in $s$. Only `Set.exists_max_image` gives $a \in s$, and it needs $s$ to be nonempty.
2. A learner proves $\operatorname{ncard}(\bigcup_i s_i) \le \sum_i \operatorname{ncard}(s_i)$ and concludes that the union is finite. The inequality also holds when one $s_i$ is infinite, because then both counts can be $0$. Prove finiteness first, or use `Set.encard`.
3. A learner uses `Set.powersetCard.card` on an infinite type and gets $0 = 0$. The statement is true but carries no information there. For an infinite type, use `Set.powersetCard.instInfinite`.

### Exercises

1. (A) Use `Set.finite_range` to show that the set $\{n^2 \bmod 7 \mid n \in \mathbb{N}\}$ is finite, and compute it.
2. (A) List the elements of `Set.powersetCard (Fin 4) 2` and check `Set.powersetCard.card` on it.
3. (B) Prove `Set.exists_max_image` by induction on a finite set with `Set.Finite.induction_on`.
4. (B) Give a finite exhaustion of the set $\mathbb{Z}$, and of the set of rational numbers in $[0, 1]$.
5. (B) Show that $\operatorname{ncard}(s \cup t) \le \operatorname{ncard}(s) + \operatorname{ncard}(t)$ from `Set.ncard_iUnion_le_of_fintype` with an index in `Bool`, and give an example where the left side is $0$ and the right side is not.
6. (C) Use `Set.powersetCard.compl` to give a bijective proof of $\binom{N}{n} = \binom{N}{N - n}$.

### Reference

<?reference?>
