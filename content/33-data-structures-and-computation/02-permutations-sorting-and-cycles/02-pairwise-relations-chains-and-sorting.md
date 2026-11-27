---
title: Pairwise relations, chains and sorting
kind: theory
modules:
  - Mathlib.Data.List.Pairwise
  - Mathlib.Data.List.Triplewise
  - Mathlib.Data.List.Chain
  - Mathlib.Data.List.ChainOfFn
  - Mathlib.Data.List.Destutter
  - Mathlib.Data.List.Sort
  - Mathlib.Data.List.MinMax
explains:
  E3: [List.Triplewise, List.triplewise_iff_getElem, List.destutter, List.isChain_destutter, List.destutter_eq_self_iff, List.SortedLE, List.sortedLE_iff_pairwise, List.sortedLE_iff_isChain, List.orderedInsert, List.insertionSort, List.perm_insertionSort, List.sortedLE_insertionSort, List.Pairwise.orderedInsert, List.sortedLE_mergeSort, List.mergeSort_eq_insertionSort, List.sublist_of_subperm_of_sortedLE, List.argmax, List.argmax_eq_some_iff, List.maximum, List.maximum_eq_coe_iff, List.Perm.maximum_eq]
  E2: [List.Pairwise.rel_get_of_lt, List.pairwise_iff_forall_infix, List.tfae_iff_pairwise, List.tfae_of_cycle, List.pairwise_of_reflexive_of_forall_ne, List.Pairwise.set_pairwise, List.triplewise_cons, List.isChain_iff_forall₂, List.IsChain.sublist, List.isChain_reverse, List.IsChain.iterate, List.isChain_cons_eq_iff_eq_replicate, List.relationReflTransGen_of_exists_isChain, List.chains, WellFounded.list_chain', List.isChain_ofFn, List.destutter', List.destutter_sublist, List.destutter_idem, List.Pairwise.destutter_eq_dedup, List.SortedLT, List.sortedLT_iff_nodup_and_sortedLE, List.sortedLE_iff_monotone_get, List.sortedLE_reverse, List.sortedLT_range, List.decidableSortedLE, List.perm_orderedInsert, List.orderedInsert_eq_take_drop, List.pairwise_insertionSort, List.length_insertionSort, List.sublist_insertionSort, List.Pairwise.insertionSort_eq, List.Pairwise.merge, List.pairwise_mergeSort', List.mergeSort_eq_self, List.Subset.antisymm_of_sortedLT, List.sublist_of_subperm_of_pairwise, List.argmin, List.minimum, List.argmax_mem, List.le_of_mem_argmax, List.argmax_cons, List.maximum_cons, List.maximum_nil, List.maximum_mem]
  E1: auto
families: []
requires: [V04.C01, V04.C02, V03.C02, V33.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Pairwise relations, chains and sorting

### Overview

A sorted list is a list in which each entry is at most each later entry. There are two ways to say this. The pairwise form asks the relation for each pair of positions $i < j$; the chain form asks it only for neighbours. For a transitive relation the two forms agree, and the chain form is easier to check while the pairwise form is easier to use. This section studies the predicates `Pairwise`, `Triplewise` and `IsChain`, the operation `destutter` that makes a chain out of a list, the predicates `SortedLE` and `SortedLT`, insertion sort and merge sort with the proofs that they give sorted permutations, the uniqueness of the sorted permutation of a list, and the functions `argmax`, `argmin`, `maximum` and `minimum`.

`Pairwise`, `IsChain` and `mergeSort` are in the core library. Mathlib adds the sorted predicates, insertion sort, the comparison of the two sorts and most of the lemmas below. The former predicates `Chain` and `Sorted` are replaced by `IsChain` and by `SortedLE` and its relatives.

### Definitions

**Definition (Pairwise).** `Pairwise R l` is the inductive predicate with two rules: `Pairwise R []`, and if $R(a, b)$ for each $b \in l$ and `Pairwise R l`, then `Pairwise R (a :: l)`. So $R$ holds between each entry and each later entry.

**Definition (Triplewise).** `Triplewise p l` holds if $p(l_i, l_j, l_k)$ for all positions $i < j < k$. Its rules are `Triplewise p []` and: if `Pairwise (p a) l` and `Triplewise p l`, then `Triplewise p (a :: l)` (`triplewise_cons`).

**Definition (Chain).** `IsChain R l` holds if $R(l_i, l_{i+1})$ for each pair of neighbours. Its rules are: `IsChain R []`, `IsChain R [a]`, and if $R(a, b)$ and `IsChain R (b :: l)` then `IsChain R (a :: b :: l)`.

**Definition (Destutter).** `destutter' R a l` walks along $l$ and keeps the last kept entry $a$ in mind: on `b :: l` it keeps $b$ if $R(a, b)$, and then continues with $b$; otherwise it drops $b$ and continues with $a$. `destutter R (a :: l) = destutter' R a l`. For $R = (\neq)$ it removes the repeated neighbours.

**Definition (Sorted).** For a preorder, `l.SortedLE` means that `l.get : Fin |l| → α` is monotone, and `l.SortedLT` means that it is strictly monotone. `SortedGE` and `SortedGT` are the duals.

**Definition (Insertion sort).** For a decidable relation $\preceq$, `orderedInsert a [] = [a]` and `orderedInsert a (b :: l)` is `a :: b :: l` if $a \preceq b$, and `b :: orderedInsert a l` otherwise. `insertionSort` is `foldr orderedInsert []`: it inserts the entries from the last to the first into the sorted list built so far.

**Definition (Merge sort).** In the core library, `mergeSort` is a specification marked `noncomputable`, and the compiler runs a faster version proved equal to it. `merge` takes two lists and repeatedly moves the smaller head to the output: `merge (x :: xs) (y :: ys)` is `x :: merge xs (y :: ys)` if $x \preceq y$, and `y :: merge (x :: xs) ys` otherwise. `mergeSort` cuts a list of length $n \ge 2$ into the first $\lfloor (n + 1)/2 \rfloor$ entries and the rest, sorts both parts, and merges them.

**Definition (Maximum and argmax).** `argmax f l` is `none` for $[\,]$, and otherwise `some m` for the first entry $m$ of $l$ at which $f$ takes its largest value. `argmin` is dual. `maximum l` is `argmax id l` read in `WithBot α`: it is $\bot$ for $[\,]$. `minimum l` is in `WithTop α`.

### Theorems and proofs

**Theorem (Pairwise by positions).** `Pairwise R l` holds if and only if $R(l_i, l_j)$ for all positions $i < j$.

*Proof.* Induction on $l$. For $[\,]$ there are no positions. For $a :: l$, the pairs $i < j$ are of two kinds. If $i = 0$, then $l_i = a$ and $l_j$ ranges over the members of $l$; this is the first condition of the rule. If $i > 0$, the pair is a pair $i - 1 < j - 1$ of positions of $l$, and the hypothesis turns these conditions into `Pairwise R l`. $\square$

**Theorem (Chains and pairwise relations).** `Pairwise R l` implies `IsChain R l`. If $R$ is transitive, the converse holds.

*Proof.* The first claim is clear from the positions: neighbours are positions $i < i + 1$. For the converse, use induction on $l$, and show the stronger claim that `IsChain R (a :: l)` gives $R(a, b)$ for each $b \in l$. If $l = b :: l'$, then $R(a, b)$, and by the hypothesis applied to `b :: l'`, $R(b, c)$ for each $c \in l'$; transitivity gives $R(a, c)$. With the hypothesis for `Pairwise R (b :: l')`, the rule gives `Pairwise R (a :: b :: l')`. $\square$

So, for a preorder, `SortedLE l` is equivalent to `Pairwise (· ≤ ·) l` and to `IsChain (· ≤ ·) l` (`sortedLE_iff_pairwise`, `sortedLE_iff_isChain`). The first equivalence is the theorem by positions, since a map on `Fin n` is monotone if and only if $l_i \le l_j$ for $i < j$, and $l_i \le l_i$ by reflexivity.

**Proposition (Destutter).** `destutter R l` is a chain for $R$ and a sublist of $l$, and `destutter R l = l` if and only if `IsChain R l`.

*Proof.* Show for `destutter' R a l` that it starts with $a$, is a chain, and is a sublist of $a :: l$; induction on $l$ for all $a$. For $[\,]$ the result is $[a]$. On $b :: l$, if $R(a, b)$ the result is $a :: \operatorname{destutter'} R\, b\, l$, which starts with $a$ followed by $b$; the hypothesis gives a chain from $b$, and $R(a, b)$ extends it. Otherwise the result is `destutter' R a l`, a chain by the hypothesis, and a sublist of $a :: l$, hence of $a :: b :: l$. If $l$ is a chain from $a$, then each test $R(a, b)$ succeeds, and no entry is dropped. Conversely, if the result is $l$ itself, then $l$ is a chain by the first part. $\square$

**Theorem (Insertion sort).** `insertionSort r l` is a permutation of $l$. If $\preceq$ is total and transitive, it is pairwise sorted for $\preceq$. For a linear order and $\preceq \;=\; \le$, it is `SortedLE`.

*Proof.* First, `orderedInsert a l ∼ a :: l`, by induction on $l$: on $b :: l$, either the result is $a :: b :: l$, or it is $b :: \operatorname{orderedInsert} a\, l \sim b :: a :: l \sim a :: b :: l$ by the hypothesis and a swap. By induction on $l$, `insertionSort (a :: l) = orderedInsert a (insertionSort l) ∼ a :: insertionSort l ∼ a :: l`.

Second, if `Pairwise (≼) l` then `Pairwise (≼) (orderedInsert a l)`. Induction on $l$. For $[\,]$ the result is $[a]$. On $b :: l$ with `Pairwise (≼) (b :: l)`: if $a \preceq b$, then the result is $a :: b :: l$, and $a \preceq c$ for each $c \in l$, because $b \preceq c$ and $\preceq$ is transitive. If not $a \preceq b$, then $b \preceq a$ by totality. The result is $b :: \operatorname{orderedInsert} a\, l$. Its tail is sorted by the hypothesis, and its members are $a$ and the members of $l$, so $b$ is below each of them. Now induction on $l$ gives that `insertionSort l` is pairwise sorted, and for $\le$ the previous theorem turns this into `SortedLE`. $\square$

**Theorem (Uniqueness of the sorted permutation).** Let $\preceq$ be antisymmetric. If $l_1 \sim l_2$ and both are pairwise sorted for $\preceq$, then $l_1 = l_2$.

*Proof.* Induction on $l_1$ for all $l_2$. If $l_1 = [\,]$, then $l_2 = [\,]$. Let $l_1 = a :: t_1$. Then $l_2$ is not empty; write $l_2 = b :: t_2$. Suppose $a \neq b$. Since $a \in l_2$, $a \in t_2$, so $b \preceq a$ because $l_2$ is sorted. Since $b \in l_1$, $b \in t_1$, so $a \preceq b$ because $l_1$ is sorted. Antisymmetry gives $a = b$, a contradiction. So $a = b$. Cancel $a$ in $a :: t_1 \sim a :: t_2$: $t_1 \sim t_2$. Both tails are sorted, and the hypothesis gives $t_1 = t_2$. $\square$

In Mathlib this theorem is `Perm.eq_of_pairwise'` and, for $\le$, `Perm.eq_of_sortedLE`, both in `Mathlib.Data.List.Sort`; the index of this edition has no record for these two names, so they appear only here. The index has the consequence `sublist_of_subperm_of_sortedLE`: a sorted list contained as a multiset in a sorted list is a sublist of it.

**Theorem (Merge sort).** For a linear order, `mergeSort l (· ≤ ·)` is `SortedLE`. If $\preceq$ is total, transitive and antisymmetric, merge sort and insertion sort give the same list (`mergeSort_eq_insertionSort`).

*Proof.* Two facts on `merge` come from the core library: `merge l l'` is a permutation of $l \mathbin{+\!\!+} l'$, and if $l$ and $l'$ are pairwise sorted, so is `merge l l'` (`Pairwise.merge`). The first holds since each step moves one head to the output. For the second, the output is built by putting the smaller head $x$ in front of the merge of the rest, and $x$ is below all the other entries: below the rest of its own list by the hypothesis, and below the other head, hence below the other list by transitivity. Now use strong induction on $|l|$. Lists of length $0$ and $1$ are sorted and unchanged. For $|l| \ge 2$, both parts are shorter, so both sorted parts are sorted permutations of the parts, and the merge is a sorted permutation of $l$. Then `mergeSort l` and `insertionSort l` are two sorted permutations of $l$, and the uniqueness theorem gives their equality. $\square$

**Proposition (Argmax and maximum).** For a linear order on $\beta$, `argmax f l = some m` if and only if $m \in l$, $f(a) \le f(m)$ for each $a \in l$, and $m$ comes first among the entries with this value. For a linear order on $\alpha$, `maximum l = m` (in `WithBot α`) if and only if $m \in l$ and $a \le m$ for each $a \in l$; so $l_1 \sim l_2$ gives `maximum l₁ = maximum l₂`.

*Proof.* `argmax f l` is a left fold that keeps a candidate $c$ and replaces it by the next entry $b$ only if $f(c) < f(b)$. By induction on the fold, the candidate after a prefix is the first entry of the prefix with the largest value: a strict increase moves to the new entry, and a tie keeps the older one. For `maximum`, take $f = \mathrm{id}$; the order on $\alpha$ is linear, so the largest value is attained at one value $m$, the greatest member. This description depends only on the members, so permutations have the same maximum. $\square$

### Examples

**Example (Insertion sort of [3, 1, 2]).** `insertionSort [3, 1, 2]` is `orderedInsert 3 (orderedInsert 1 (orderedInsert 2 []))`. Step 1: `orderedInsert 2 [] = [2]`. Step 2: $1 \le 2$, so `orderedInsert 1 [2] = [1, 2]`. Step 3: $3 \le 1$ fails, so the result is $1 :: \operatorname{orderedInsert} 3\, [2]$; $3 \le 2$ fails, so it is $1 :: 2 :: \operatorname{orderedInsert} 3\, [\,] = [1, 2, 3]$. Merge sort cuts $[3, 1, 2]$ into $[3, 1]$ and $[2]$, sorts $[3, 1]$ by the merge of $[3]$ and $[1]$ into $[1, 3]$, and merges $[1, 3]$ with $[2]$: $1 \le 2$ gives $1$, then $3 \le 2$ fails and gives $2$, then $3$. The result is $[1, 2, 3]$, as the uniqueness theorem predicts.

**Counterexample (A chain that is not pairwise).** For $R = (\neq)$ on $\mathbb{N}$, $[1, 2, 1]$ is a chain, since $1 \neq 2$ and $2 \neq 1$, but it is not pairwise, since its first and last entries are equal. The relation $\neq$ is not transitive.

**Counterexample (Sorting without antisymmetry).** Order pairs $(k, x)$ by $k$ only. This preorder is total and transitive, but not antisymmetric. The lists $[(1, a), (1, b)]$ and $[(1, b), (1, a)]$ are both sorted and are permutations of each other, but they are different. So `mergeSort_eq_insertionSort` needs `Std.Antisymm`.

**Example (Destutter and argmax).** `destutter (· ≠ ·) [1, 1, 2, 2, 2, 3, 1] = [1, 2, 3, 1]`: the repeated neighbours go, and the last $1$ stays, because it differs from its kept neighbour $3$. `destutter (· < ·) [1, 3, 2, 4, 5] = [1, 3, 4, 5]`: the $2$ is dropped, because $3 < 2$ fails. For $f(x) = x \bmod 3$, `argmax f [4, 5, 2, 8] = some 5`: the values are $1, 2, 2, 2$, the candidate moves from $4$ to $5$, and the ties keep $5$. `maximum [3, 1, 4, 1, 5] = 5`, and `maximum [] = ⊥`.

```lean
example : List.insertionSort (· ≤ ·) [3, 1, 2] = [1, 2, 3] := rfl
example : List.destutter (· ≠ ·) [1, 1, 2, 2, 2, 3, 1] = [1, 2, 3, 1] := by decide
```

### The library around it

::: mathlib
`List.tfae_of_cycle` · `Mathlib.Data.List.Pairwise`

`Pairwise.rel_get_of_lt`, `pairwise_iff_forall_infix`, `pairwise_of_reflexive_of_forall_ne`, `Pairwise.set_pairwise`, `tfae_iff_pairwise` and `tfae_of_cycle`, which proves `TFAE` from a cycle of implications. `Mathlib.Data.List.Triplewise` has `triplewise_cons` and `triplewise_iff_getElem`.

<?decl List.tfae_of_cycle?>
:::

::: mathlib
`List.relationReflTransGen_of_exists_isChain` · `Mathlib.Data.List.Chain`

`isChain_iff_forall₂`, `IsChain.sublist` for transitive relations, `isChain_reverse`, `IsChain.iterate`, `isChain_cons_eq_iff_eq_replicate`, and `relationReflTransGen_of_exists_isChain`: a chain joins its head to its last entry in the reflexive transitive closure. `List.chains` and `WellFounded.list_chain'` give a well-founded order on decreasing chains. `Mathlib.Data.List.ChainOfFn` has `isChain_ofFn`.

<?decl List.relationReflTransGen_of_exists_isChain?>
:::

::: mathlib
`List.destutter_eq_self_iff` · `Mathlib.Data.List.Destutter`

`destutter'`, `destutter`, `isChain_destutter`, `destutter_sublist`, `destutter_idem`, `destutter_eq_self_iff` and `Pairwise.destutter_eq_dedup`.

<?decl List.destutter_eq_self_iff?>
:::

::: mathlib
`List.mergeSort_eq_insertionSort` · `Mathlib.Data.List.Sort`

`SortedLE`, `SortedLT`, `sortedLE_iff_pairwise`, `sortedLE_iff_isChain`, `sortedLE_iff_monotone_get`, `sortedLT_iff_nodup_and_sortedLE`, `sortedLE_reverse`, `sortedLT_range`, `decidableSortedLE`; `orderedInsert`, `perm_orderedInsert`, `orderedInsert_eq_take_drop`, `insertionSort`, `perm_insertionSort`, `pairwise_insertionSort`, `sortedLE_insertionSort`, `Pairwise.insertionSort_eq`; `Pairwise.merge`, `pairwise_mergeSort'`, `sortedLE_mergeSort`, `mergeSort_eq_self` and `mergeSort_eq_insertionSort`; `sublist_of_subperm_of_sortedLE` and `Subset.antisymm_of_sortedLT`.

<?decl List.mergeSort_eq_insertionSort?>
:::

::: mathlib
`List.Perm.maximum_eq` · `Mathlib.Data.List.MinMax`

`argmax`, `argmin`, `argmax_cons`, `argmax_mem`, `le_of_mem_argmax`, `argmax_eq_some_iff`, `maximum`, `minimum`, `maximum_nil`, `maximum_cons`, `maximum_mem`, `maximum_eq_coe_iff` and `Perm.maximum_eq`.

<?decl List.Perm.maximum_eq?>
:::

Common errors of a learner: The first error is to look for `List.Sorted` or `List.Chain`; these names are gone, and `SortedLE`, `SortedLT` and `IsChain` replace them. The second error is to use the chain form for a relation that is not transitive, such as $\neq$. The third error is to expect `maximum []` to be a number; it is $\bot$ in `WithBot α`, and `maximum_of_length_pos` gives a value in $\alpha$ for a list that is not empty. The fourth error is to sort by a key with a relation that is not antisymmetric and to expect the two sorts to agree.

### Exercises

1. (A) Sort $[4, 2, 5, 1]$ by insertion, step by step, and by merge sort. Hint: insertion starts from the last entry.
2. (A) Compute `destutter (· ≠ ·) [2, 2, 1, 1, 2]` and `destutter (· ≤ ·) [3, 1, 4, 1, 5]`. Hint: compare each entry with the last kept entry.
3. (A) Compute `argmin (fun x => x % 4) [7, 4, 9, 8]` and `minimum [7, 4, 9, 8]`. Hint: the first entry with the least value wins.
4. (B) Prove that `orderedInsert a l` has length $|l| + 1$ and that `insertionSort l = l` for a pairwise sorted list $l$. Hint: if $l$ is sorted and $a \preceq b$ for each $b$, the insertion of $a$ in front stops at once.
5. (B) Prove that `SortedLT l` holds if and only if $l$ has no duplicates and `SortedLE l`. Hint: use the pairwise form and $a < b \iff a \le b \wedge a \neq b$.
6. (B) Prove that `Triplewise p l` holds if and only if $p(l_i, l_j, l_k)$ for all $i < j < k$. Hint: induction on $l$ with `triplewise_cons`, as for `Pairwise`.
7. (C) Show that insertion sort makes at most $n(n - 1)/2$ comparisons on a list of length $n$, and exactly that many on $[1, 2, \dots, n]$ with the relation $\ge$. Hint: the insertion into a list of length $k$ makes at most $k$ comparisons.

### Notes and history

Merge sort is due to John von Neumann (1945). Knuth's *The Art of Computer Programming*, Volume 3, treats both, and proves that a sort by comparisons needs about $n \log_2 n$ comparisons in the worst case; the index of this edition has no declaration for this lower bound. Quicksort, due to Hoare (1961), is not in the library of lists. The uniqueness of the sorted permutation is the reason why the two sorts give the same result, and Mathlib uses it to compare `mergeSort` and `insertionSort`.

The Mathlib files are by these authors, read from their headers: `Pairwise` by Mario Carneiro; `Triplewise` by Joseph Myers and Yaël Dillies; `Chain` by Mario Carneiro, Kenny Lau and Yury Kudryashov; `ChainOfFn` by Joseph Myers; `Destutter` by Eric Rodriguez and Eric Wieser; `Sort` by Jeremy Avigad and Wrenna Robson; `MinMax` by Minchao Wu, Chris Hughes and Mantas Bakšys.

### Reference

<?reference?>
