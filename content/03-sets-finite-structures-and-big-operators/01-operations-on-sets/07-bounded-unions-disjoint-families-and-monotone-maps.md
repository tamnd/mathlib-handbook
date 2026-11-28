---
title: Bounded unions, disjoint families and monotone maps on sets
kind: api
modules:
  - Mathlib.Data.Set.Lattice.Bounded
  - Mathlib.Data.Set.Lattice.Order
  - Mathlib.Data.Set.Lattice.Disjoint
  - Mathlib.Data.Set.Pairwise.Lattice
  - Mathlib.Data.Set.Pairwise.List
  - Mathlib.Data.Set.Pairwise.Chain
  - Mathlib.Data.Set.Accumulate
  - Mathlib.Data.Set.Dissipate
  - Mathlib.Data.Set.MemPartition
  - Mathlib.Data.Set.Constructions
  - Mathlib.Data.Set.Equitable
  - Mathlib.Data.Set.Order
  - Mathlib.Data.Set.Monotone
explains:
  E2: [Set.biUnion_insert, Set.sInter_eq_empty_iff, Set.nonempty_iInter, Monotone.iUnion_nat_add, Set.unionEqSigmaOfDisjoint, Set.biUnion_sdiff_biUnion_eq, memPartition_succ, FiniteInter.finiteInterClosure_min, Set.equitableOn_iff_exists_eq_eq_add_one, Set.monotoneOn_insert_iff]
  E1: auto
families: []
requires: [V01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bounded unions, disjoint families and monotone maps on sets

### Overview

Section 2 of this chapter gives the indexed union $\bigcup_i s_i$ and the indexed intersection $\bigcap_i s_i$. In practice the index often runs over a set: $\bigcup_{i \in t} s_i$, written `⋃ i ∈ t, s i`, is a *bounded union*. The union of a set of sets, $\bigcup_0 S$, written `⋃₀ S`, is a bounded union over $S$ itself. The modules of this section hold the rules for these forms, the rules for sequences of sets indexed by $\mathbb{N}$, and the rules for families of disjoint sets.

The section also gives four small constructions: the partition of a type made by the first $n$ sets of a sequence, the closure of a family of sets under finite intersections, the functions that are almost constant on a set, and the rules for monotone functions on a set.

### The library around it

#### Bounded unions and unions of sets of sets

The module `Mathlib.Data.Set.Lattice.Bounded` holds about 200 results. A bounded union unfolds to two nested unions, `⋃ i, ⋃ (h : i ∈ t), s i`, and the membership rule `Set.mem_biUnion` gives a point in some $s_i$ with $i \in t$. The rules over the shape of the index set are the most used:

$$\bigcup_{x \in \{a\} \cup t} s_x = s_a \cup \bigcup_{x \in t} s_x, \qquad \bigcup_{x \in \{a, b\}} s_x = s_a \cup s_b.$$

These are `Set.biUnion_insert` and `Set.biUnion_pair`, with `Set.biUnion_empty`, `Set.biUnion_singleton`, `Set.biUnion_union` and `Set.biUnion_univ` for the other shapes, and the forms `Set.biInter_insert`, `Set.biInter_pair` and so on for intersections. An induction on a finite index set uses them. The rules `Set.sUnion_eq_biUnion` and `Set.sInter_eq_biInter` convert `⋃₀` and `⋂₀` to bounded forms, and `Set.sUnion_insert` and `Set.sInter_insert` give the insertion rules for them directly.

The emptiness of an intersection has two useful forms:

$$\bigcap_i s_i \ne \varnothing \iff \exists x,\ \forall i,\ x \in s_i, \qquad \bigcap_0 C = \varnothing \iff \forall a,\ \exists b \in C,\ a \notin b.$$

These are `Set.nonempty_iInter` and `Set.sInter_eq_empty_iff`. The De Morgan laws for a set of sets are `Set.compl_sUnion` and `Set.compl_sInter`, and `Set.sInter_eq_compl_sUnion_compl` writes one through the other. The union of sets of sets and the power set form a Galois connection: $\bigcup_0 S \subseteq t$ if and only if $S \subseteq \mathcal{P}(t)$ (`Set.sUnion_powerset_gc`). The module also turns unions into ranges: `Set.iUnion_eq_range_sigma` writes $\bigcup_i s_i$ as the range of the second projection on the sigma type $\Sigma i, s_i$.

#### Sequences of sets

The module `Mathlib.Data.Set.Lattice.Order` holds the rules for families indexed by $\mathbb{N}$ and by an order. The first term can be split off: $s_0 \cup \bigcup_i s_{i+1} = \bigcup_i s_i$ (`Set.union_iUnion_nat_succ`), and the dual rule `Set.inter_iInter_nat_succ` does the same for intersections. A shift of the index does not change the union of an increasing sequence:

$$f \text{ monotone} \implies \bigcup_n f(n + k) = \bigcup_n f(n).$$

This is `Monotone.iUnion_nat_add`, and `Antitone.iInter_nat_add` is the dual. The rule `Set.iUnion_ge_eq_iUnion_nat_add` rewrites the tail $\bigcup_{i \ge n} u_i$ as $\bigcup_i u_{i+n}$. The lower limit of a sequence of sets, $\bigcup_n \bigcap_{i \ge n} f(i)$, also does not change under a shift (`Set.iUnion_iInter_ge_nat_add`). For a complete lattice, the intervals of an infimum and a supremum are intersections: `Set.Iic_iInf` gives $(-\infty, \inf_i f(i)] = \bigcap_i (-\infty, f(i)]$, and `Set.Ici_iSup` is the dual. The rule `Set.nonempty_iInter_Iic_iff` says that the intervals $(-\infty, f(i)]$ have a common point if and only if the range of $f$ is bounded below.

The modules `Mathlib.Data.Set.Accumulate`, `Mathlib.Data.Set.Dissipate` and `Mathlib.Data.Set.Pairwise.Chain` are deprecated and only import `Mathlib.Order.SetAccumulate`, `Mathlib.Order.SetDissipate` and `Mathlib.Order.Preorder.PairwiseChain`, which hold the partial unions $\bigcup_{i \le n} s_i$, the partial intersections $\bigcap_{i \le n} s_i$ and the chains of sets.

#### Disjoint families

A union of pairwise disjoint sets is a disjoint union in the sense of types. The module `Mathlib.Data.Set.Lattice.Disjoint` gives the map `Set.sigmaToiUnion t` from the sigma type $\Sigma i, t_i$ to the union, and `Set.sigmaToiUnion_bijective` says that it is bijective when the sets are pairwise disjoint. The equivalence

$$\bigcup_i t_i \simeq \Sigma i,\ t_i$$

for a pairwise disjoint family is `Set.unionEqSigmaOfDisjoint`. A count of a disjoint union as a sum of counts goes through it. The module also gives the disjointness of a union: $\bigcup_i s_i$ is disjoint from $t$ if and only if each $s_i$ is disjoint from $t$ (`Set.disjoint_iUnion_left`, with `Set.disjoint_iUnion_right` and the forms for `⋃₀`).

The module `Mathlib.Data.Set.Pairwise.Lattice` connects disjoint families and bounded unions. For a family $f$ pairwise disjoint on $s \cup t$,

$$\bigcup_{i \in s} f(i) \setminus \bigcup_{i \in t} f(i) = \bigcup_{i \in s \setminus t} f(i).$$

This is `Set.biUnion_sdiff_biUnion_eq`. Without disjointness only the inclusion $\subseteq$ holds. If the sets are pairwise disjoint and nonempty, then the map $s \mapsto \bigcup_{i \in s} f(i)$ is injective (`Pairwise.biUnion_injective`). For a directed family of sets, a relation holds pairwise on the union if and only if it holds pairwise on each set (`Set.pairwise_iUnion`), and `Set.pairwiseDisjoint_iUnion` is the same for disjointness. The module `Mathlib.Data.Set.Pairwise.List` has two results: for a list with no duplicates, a symmetric relation holds pairwise on the set of its elements if and only if it holds pairwise along the list (`List.Nodup.pairwise_coe`).

#### The partition made by a sequence of sets

Let $f : \mathbb{N} \to \operatorname{Set} \alpha$. The module `Mathlib.Data.Set.MemPartition` defines `memPartition f n`, the partition of $\alpha$ made by the sets $f(0), \dots, f(n-1)$: two points are in the same part when they lie in the same sets $f(i)$ for $i < n$. The definition is recursive. The partition for $0$ is $\{\alpha\}$ (`memPartition_zero`), and the next step cuts each part by $f(n)$:

$$\operatorname{memPartition}(f, n + 1) = \{u \cap f(n) \mid u \in P_n\} \cup \{u \setminus f(n) \mid u \in P_n\}.$$

This is `memPartition_succ`, with $P_n = \operatorname{memPartition}(f, n)$. The main results say that it is a partition: the parts are disjoint (`disjoint_memPartition`), their union is the whole type (`sUnion_memPartition`), and there are finitely many parts (`finite_memPartition`). The part that holds a point $a$ is `memPartitionSet f n a`, with `mem_memPartitionSet` and `memPartitionSet_eq_iff`.

#### Families closed under finite intersections

The module `Mathlib.Data.Set.Constructions` defines the class `FiniteInter S` for a family $S$ of sets of $\alpha$: the whole type is in $S$ (`FiniteInter.univ_mem`) and $S$ is closed under binary intersection (`FiniteInter.inter_mem`). The closure `FiniteInter.finiteInterClosure S` is the least such family that contains $S$. The rule `FiniteInter.finiteInterClosure_finiteInter` says that it is closed, and `FiniteInter.finiteInterClosure_min` says that it is the least:

$$S \subseteq T,\ \operatorname{FiniteInter}(T) \implies \operatorname{finiteInterClosure}(S) \subseteq T.$$

The rule `FiniteInter.finiteInterClosure_insert` describes the closure after one set is added.

#### Equitable functions

A function $f : \alpha \to \beta$ is *equitable* on $s$ when its values on $s$ differ by at most one: $f(a_1) \le f(a_2) + 1$ for all $a_1, a_2 \in s$. This is `Set.EquitableOn s f`. For values in $\mathbb{N}$ it has the form

$$\operatorname{EquitableOn}(s, f) \iff \exists b,\ \forall a \in s,\ f(a) = b \text{ or } f(a) = b + 1.$$

This is `Set.equitableOn_iff_exists_eq_eq_add_one`. For a finset, `Finset.equitableOn_iff` says that $b$ can be the integer part of the mean $\left(\sum_{i \in s} f(i)\right) / |s|$. The negation `Set.not_equitableOn` gives two points with $f(b) + 1 < f(a)$. An *equipartition* is a partition in which the sizes of the parts are equitable.

#### Monotone functions on a set

The modules `Mathlib.Data.Set.Order` and `Mathlib.Data.Set.Monotone` connect `MonotoneOn f s` and the global form. The rule `Set.monotoneOn_iff_monotone` says that $f$ is monotone on $s$ if and only if its restriction to the subtype is monotone, and `Set.strictMonoOn_iff_strictMono` does the same for the strict form. Monotonicity grows one point at a time by `Set.monotoneOn_insert_iff`: $f$ is monotone on $s \cup \{a\}$ if and only if it is monotone on $s$ and $f(b) \le f(a)$ for $b \le a$ in $s$ and $f(a) \le f(b)$ for $a \le b$ in $s$.

The other results are of three kinds. Rules for sets as values: `Monotone.inter` and `Monotone.union` say that the intersection and the union of two monotone families of sets are monotone, and `Set.monotone_ofPred` makes a monotone family from a predicate. Rules for congruence and restriction: `MonotoneOn.mono`, `MonotoneOn.congr` and `Monotone.domRestrict`. And inverse rules: `Function.monotoneOn_of_rightInvOn_of_mapsTo` says that a right inverse on a set of a monotone function to a linear order is monotone. The rule `Set.not_monotoneOn_not_antitoneOn_iff_exists_le_le` says that a function between linear orders is neither monotone nor antitone on $s$ if and only if it goes up and down on three points $a \le b \le c$ of $s$.

#### Common errors

1. A learner uses `Set.mem_iUnion` on `⋃ i ∈ t, s i` and gets a goal with a union over a proof. A bounded union has two levels. Use `Set.mem_iUnion₂` or `Set.mem_biUnion`, or `simp only [Set.mem_iUnion]` twice.
2. A learner applies `Set.biUnion_sdiff_biUnion_eq` with a family that is disjoint only on $s$. The rule needs disjointness on $s \cup t$.
3. A learner applies `Monotone.iUnion_nat_add` to an arbitrary sequence. For a sequence that is not increasing, the union of a shifted sequence can be smaller. Use `Set.iUnion_ge_eq_iUnion_nat_add` for the tail.

### Exercises

1. (A) Use `Set.biUnion_insert` and `Set.biUnion_singleton` to compute $\bigcup_{x \in \{1, 2, 3\}} \{x, 2x\}$ in $\mathbb{N}$.
2. (A) Give a sequence of sets $s_n \subseteq \mathbb{N}$ with $\bigcup_n s_{n+1} \ne \bigcup_n s_n$.
3. (A) Find all the parts of `memPartition f 2` for $f(0) = \{0, 1\}$ and $f(1) = \{1, 2\}$ in `Fin 4`.
4. (B) Prove `Set.sInter_eq_empty_iff` from the definition of `⋂₀`.
5. (B) Show that $f(n) = \lfloor n / 3 \rfloor$ is not equitable on $\{0, \dots, 6\}$ but is equitable on $\{0, \dots, 5\}$, with `Set.equitableOn_iff_exists_eq_eq_add_one`.
6. (C) Show with `Set.unionEqSigmaOfDisjoint` that if the sets $t_0, \dots, t_{k-1}$ are pairwise disjoint and finite, then the count of their union is the sum of their counts.

### Reference

<?reference?>
