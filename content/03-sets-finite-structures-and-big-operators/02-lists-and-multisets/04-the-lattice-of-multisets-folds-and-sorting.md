---
title: The lattice of multisets, folds, sorting and the multiset order
kind: api
modules:
  - Mathlib.Data.Multiset.UnionInter
  - Mathlib.Data.Multiset.FinsetOps
  - Mathlib.Data.Multiset.Lattice
  - Mathlib.Data.Multiset.Fold
  - Mathlib.Data.Multiset.Find
  - Mathlib.Data.Multiset.Sort
  - Mathlib.Data.Multiset.Functor
  - Mathlib.Data.Multiset.Interval
  - Mathlib.Data.Multiset.DershowitzManna
explains:
  E2: [Multiset.count_union, Multiset.union_add_inter, Multiset.add_eq_union_iff_disjoint, Multiset.ndinsert, Multiset.ndunion_eq_union, Multiset.sup_le, Multiset.fold_cons_left, Multiset.sort_eq, Multiset.card_Icc, Multiset.wellFounded_isDershowitzMannaLT]
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

## The lattice of multisets, folds, sorting and the multiset order

### Overview

The order $s \le t$ on multisets of Section 3 is a lattice: the union $s \cup t$ takes the maximum of the counts, and the intersection $s \cap t$ takes the minimum. These two operations are different from the sum $s + t$, which adds the counts. The finsets of Chapter 3 need a third kind of operation, which does not add a copy of an element that is already present. The modules of this section give the three kinds and the rules between them.

The section then gives the ways to compute with a multiset: the fold of a commutative and associative operation, the supremum and infimum of a multiset in a lattice, the search for an element with a property, the sorted list of a multiset, and the monad structure. It ends with two orders on multisets: the intervals $[s, t]$ of the inclusion order and the Dershowitz and Manna order, a well founded order that proves the termination of programs.

### The library around it

#### Union and intersection

The module `Mathlib.Data.Multiset.UnionInter` defines $s \cup t$ as $(s - t) + t$ (`Multiset.union_def`) and $s \cap t$ as the image of the list intersection. With decidable equality on $\alpha$ they make `Multiset α` a distributive lattice (`Multiset.instDistribLattice`), in which the sup is the union and the inf is the intersection (`Multiset.sup_eq_union`, `Multiset.inf_eq_inter`). The counts are the maximum and the minimum:

$$\operatorname{count}(a, s \cup t) = \max(\operatorname{count}(a, s), \operatorname{count}(a, t)), \qquad \operatorname{count}(a, s \cap t) = \min(\dots).$$

These are `Multiset.count_union` and `Multiset.count_inter`. Since $\max(x, y) + \min(x, y) = x + y$, the count gives

$$(s \cup t) + (s \cap t) = s + t,$$

which is `Multiset.union_add_inter`. In the same way $(s - t) + (s \cap t) = s$ (`Multiset.sub_add_inter`), and the sum distributes over both operations: `Multiset.union_add_distrib` and `Multiset.inter_add_distrib`. The membership rules are as for sets: `Multiset.mem_union` and `Multiset.mem_inter`.

Two multisets are disjoint when no element is in both. This is the `Disjoint` of the lattice, and `Multiset.disjoint_left` gives the form with members. The sum and the union agree exactly on disjoint multisets:

$$s + t = s \cup t \iff \operatorname{Disjoint}(s, t).$$

This is `Multiset.add_eq_union_iff_disjoint`. A sum has no duplicate if and only if both parts have none and they are disjoint (`Multiset.nodup_add`). The intersection is zero exactly for disjoint multisets (`Multiset.inter_eq_zero_iff_disjoint`).

#### Operations for finsets

The module `Mathlib.Data.Multiset.FinsetOps` gives three operations that keep the predicate Nodup. They are the operations behind the insertion, the union and the intersection of finsets.

1. `Multiset.ndinsert a s` adds $a$ only if $a \notin s$. The rules `Multiset.ndinsert_of_mem` and `Multiset.ndinsert_of_notMem` give the two cases, `Multiset.mem_ndinsert` gives the members, and `Multiset.Nodup.ndinsert` gives that the result has no duplicate.
2. `Multiset.ndunion s t` adds to $t$ the elements of $s$ that are not in $t$, one at a time (`Multiset.cons_ndunion`).
3. `Multiset.ndinter s t` keeps the elements of $s$ that are in $t$.

On a multiset with no duplicate these are the lattice operations:

$$s \text{ Nodup} \implies \operatorname{ndunion}(s, t) = s \cup t, \qquad \operatorname{ndinter}(s, t) = s \cap t.$$

These are `Multiset.ndunion_eq_union` and `Multiset.ndinter_eq_inter`. In general they differ: $\operatorname{ndunion}(\{a\}, \{a, a\}) = \{a, a\}$, but $\{a\} \cup \{a, a\} = \{a, a\}$ and $\operatorname{ndinter}(\{a, a\}, \{a\}) = \{a, a\}$ while $\{a, a\} \cap \{a\} = \{a\}$. The card of `Multiset.ndinsert a s` is $|s| + 1$ only when $a \notin s$ (`Multiset.length_ndinsert_of_notMem`). The finset operations of Chapter 3 are defined with these and inherit their rules.

#### Folds and lattice operations

A function on lists that does not see the order passes to multisets. The fold of an operation $\ast$ that is commutative and associative is such a function. The module `Mathlib.Data.Multiset.Fold` defines `Multiset.fold`, which combines $b$ with all elements of $s$. Its rules are the rules of a monoid homomorphism:

$$\operatorname{fold}(b, a ::_m s) = a \ast \operatorname{fold}(b, s), \qquad \operatorname{fold}(b_1 \ast b_2, s_1 + s_2) = \operatorname{fold}(b_1, s_1) \ast \operatorname{fold}(b_2, s_2).$$

These are `Multiset.fold_cons_left` and `Multiset.fold_add`. The rule `Multiset.fold_hom` moves a homomorphism through a fold, and `Multiset.fold_dedup_idem` says that for an idempotent operation the fold does not see duplicates. The sum and the product of a multiset in Section 2 are folds of `+` and `*`.

The module `Mathlib.Data.Multiset.Lattice` gives the fold of $\sqcup$ with start $\bot$, `Multiset.sup s`, and the dual `Multiset.inf s`. Their main rule is the universal property:

$$\sup s \le a \iff \forall b \in s,\ b \le a.$$

This is `Multiset.sup_le`, with `Multiset.le_sup` for each member and `Multiset.le_inf` for the dual. The rules `Multiset.sup_cons`, `Multiset.sup_add` and `Multiset.sup_union` give the sup of a built multiset, and `Multiset.sup_dedup` says that duplicates do not matter. The finset forms `Finset.sup` and `Finset.inf` of Chapter 3 rest on these.

#### Search, sorting and the monad

The module `Mathlib.Data.Multiset.Find` gives `Multiset.find?`, which returns the element of $s$ with a property $p$ when at most one element of $s$ has it. The extra hypothesis is necessary: without it the result would depend on the order of the list. The rule `Multiset.find?_eq_some_iff` says that the result is `some a` if and only if $a \in s$ and $p(a)$, and `Multiset.find?_eq_choose` connects it to `Multiset.choose` of Section 3.

The module `Mathlib.Data.Multiset.Sort` gives `Multiset.sort s r`, the list of the elements of $s$ in the order of a total, transitive and antisymmetric relation $r$. With `≤` on a linear order the relation can be left out. The rules say that it is a list in the class of $s$ and that it is sorted:

$$\operatorname{sort}(s) \text{ as a multiset} = s, \qquad \operatorname{sort}(s) \text{ is pairwise } r.$$

These are `Multiset.sort_eq` and `Multiset.pairwise_sort`, with `Multiset.length_sort` for the length and `Multiset.mem_sort` for the members. The rule `Multiset.sort_range` says that the sorted list of `Multiset.range n` is the list $[0, \dots, n - 1]$. Sorting gives a canonical list for a multiset, so it is the way to print or compute with a multiset in a fixed order.

The module `Mathlib.Data.Multiset.Functor` gives the instance `Multiset.instMonad`: `pure a` is $\{a\}$, the map is `Multiset.map`, and `>>=` is `Multiset.bind` (`Multiset.bind_def`). The traversal `Multiset.traverse` works only for a commutative applicative functor, because the result must not depend on the order of the elements.

#### Intervals of multisets

The module `Mathlib.Data.Multiset.Interval` makes `Multiset α` a locally finite order (`Multiset.instLocallyFiniteOrder`): each interval $[s, t]$ is a finite set of multisets. The construction goes through the finitely supported functions, by the equivalence that sends a multiset to its counts (`Multiset.Icc_eq`). The card of an interval is a product over the elements:

$$|[s, t]| = \prod_{i \in \operatorname{supp}(s) \cup \operatorname{supp}(t)} (\operatorname{count}(i, t) + 1 - \operatorname{count}(i, s)).$$

This is `Multiset.card_Icc`. For each element $i$, a multiset $u$ in the interval has between $\operatorname{count}(i, s)$ and $\operatorname{count}(i, t)$ copies of $i$, and the choices for different $i$ are independent. The rules `Multiset.card_Ico`, `Multiset.card_Ioc`, `Multiset.card_Ioo` and `Multiset.card_Iic` subtract one or two from this.

#### The Dershowitz and Manna order

Let $\alpha$ be a preorder. The relation `Multiset.IsDershowitzMannaLT M N` holds when $N$ comes from $M$ by the replacement of a multiset $Y$ by a nonzero multiset $Z$ with each element of $Y$ below some element of $Z$:

$$M = X + Y,\quad N = X + Z,\quad Z \ne 0,\quad \forall y \in Y,\ \exists z \in Z,\ y < z.$$

So $M < N$ when $M$ comes from $N$ by the removal of at least one element and the addition of any number of smaller elements. The main theorem says that this order is well founded when the order on $\alpha$ is:

$$\operatorname{WellFoundedLT}(\alpha) \implies \operatorname{WellFounded}(\operatorname{IsDershowitzMannaLT}).$$

This is `Multiset.wellFounded_isDershowitzMannaLT`, and the instance `Multiset.instWellFoundedIsDershowitzMannaLT` makes it available to the termination proofs of recursive definitions. The rule `Multiset.IsDershowitzMannaLT.trans` gives transitivity. A termination proof assigns to each state a multiset of natural numbers and shows that each step goes down in this order; for example, a step that replaces one number $n$ by any finite number of numbers less than $n$.

#### Common errors

1. A learner proves $s + t = s \cup t$ for all multisets. It holds only for disjoint multisets: $\{a\} + \{a\} = \{a, a\}$ but $\{a\} \cup \{a\} = \{a\}$. Use `Multiset.add_eq_union_iff_disjoint`.
2. A learner uses `Multiset.ndinsert` and `Multiset.cons` as the same operation. The insertion `a ::ₘ s` adds a copy even when $a \in s$. Only `Multiset.ndinsert` skips it.
3. A learner tries `Multiset.fold` with subtraction and gets an error that no instance is found. The fold needs an operation that is commutative and associative, given as two instance arguments for commutativity and associativity.

### Exercises

1. (A) Compute $\{1, 1, 2\} \cup \{1, 3\}$, $\{1, 1, 2\} \cap \{1, 3\}$ and $\{1, 1, 2\} + \{1, 3\}$, and check `Multiset.union_add_inter`.
2. (A) Compute `Multiset.sort {3, 1, 2, 1}` for the order `≤` on $\mathbb{N}$.
3. (B) Prove `Multiset.union_add_inter` with `Multiset.ext'`, `Multiset.count_union` and `Multiset.count_inter`.
4. (B) Use `Multiset.card_Icc` to count the multisets $u$ with $\{1\} \le u \le \{1, 1, 2, 2, 2\}$.
5. (B) Show that $\{3\}$ is above $\{2, 2, 2, 1\}$ in the Dershowitz and Manna order on $\mathbb{N}$, and give $X$, $Y$ and $Z$.
6. (C) Use `Multiset.wellFounded_isDershowitzMannaLT` to prove that the process "remove one number $n > 0$ from a multiset of natural numbers and add $n$ copies of $n - 1$" stops.

### Reference

<?reference?>
